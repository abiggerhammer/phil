{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Assurance
import Phil.Core.Decision
  ( AssumptionRef (..)
  , DecisionCertificate (..)
  )
import Phil.Core.Discharge
  ( ExportBinding (..)
  , ObligationDisposition (..)
  , ResolvedObligation (..)
  , RuntimeBinding (..)
  , StaticDischarge (..)
  )
import Phil.Core.Syntax
  ( Obligation (..)
  , ObligationId (..)
  , Proposition (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Verification
  ( VerificationObligationGraph (..)
  , buildVerificationRevisionGraph
  , buildVerificationRevisionGraphWithSupport
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "handoff preserves runtime disposition and canonical proposition" runtimeDispositionPreserved
    , test "generated prerequisite revision records exact parent lineage" prerequisiteLineagePreserved
    , test "certificate prerequisite becomes explicit parent-to-child support" certificatePrerequisiteSupportPreserved
    , test "revision graph consumes explicit certificate support direction" certificatePrerequisiteGraphPreserved
    , test "revision graph does not reinterpret generation lineage as support" lineageIsNotGraphSupport
    , test "later sibling certificate can depend on earlier sibling revision" siblingPrerequisiteSupportPreserved
    , test "unknown certificate prerequisite fails closed" unknownPrerequisiteRejected
    , test "handoff preserves explicit export disposition" exportDispositionPreserved
    ]
  if and results then pure () else exitFailure

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed

runtimeDispositionPreserved :: Bool
runtimeDispositionPreserved =
  case handoffResolvedObligation handoffConfig runtimeResolved of
    Right (parent : _) ->
      handoffDisposition parent == RuntimeBound runtimeBinding
        && handoffCanonicalProposition parent == equalRef
        && revisionGeneratedFrom (handoffRevision parent) == []
        && null (handoffSupportDependencies parent)
    _ -> False

prerequisiteLineagePreserved :: Bool
prerequisiteLineagePreserved =
  case handoffResolvedObligation handoffConfig runtimeResolved of
    Right (parent : child : _) ->
      revisionGeneratedFrom (handoffRevision child)
        == [revisionId (handoffRevision parent)]
        && handoffCanonicalProposition child == Truth
        && handoffDisposition child == StaticallyDischarged StaticByDefinition
        && null (handoffSupportDependencies child)
    _ -> False

certificatePrerequisiteSupportPreserved :: Bool
certificatePrerequisiteSupportPreserved =
  case handoffResolvedObligation handoffConfig certificateResolved of
    Right entries@(parent : child : _) ->
      let parentRevision = revisionId (handoffRevision parent)
          childRevision = revisionId (handoffRevision child)
          supportEdges = handoffSupportEdges entries
      in handoffSupportDependencies parent == [DependsOnObligation childRevision]
          && revisionGeneratedFrom (handoffRevision parent) == []
          && revisionGeneratedFrom (handoffRevision child) == [parentRevision]
          && length supportEdges == 1
          && (parentRevision, childRevision) `elem` supportEdges
          && not ((childRevision, parentRevision) `elem` supportEdges)
    _ -> False

certificatePrerequisiteGraphPreserved :: Bool
certificatePrerequisiteGraphPreserved =
  case handoffResolvedObligation handoffConfig certificateResolved of
    Right entries ->
      let revisions = map handoffRevision entries
          supportEdges = handoffSupportEdges entries
      in case buildVerificationRevisionGraphWithSupport
          revisions supportEdges mempty of
          Right graph -> verificationGraphDependencies graph == supportEdges
          Left _ -> False
    Left _ -> False

lineageIsNotGraphSupport :: Bool
lineageIsNotGraphSupport =
  case handoffResolvedObligation handoffConfig certificateResolved of
    Right entries ->
      case buildVerificationRevisionGraph (map handoffRevision entries) mempty of
        Right graph -> null (verificationGraphDependencies graph)
        Left _ -> False
    Left _ -> False

siblingPrerequisiteSupportPreserved :: Bool
siblingPrerequisiteSupportPreserved =
  case handoffResolvedObligation handoffConfig siblingResolved of
    Right entries@(_parent : firstChild : secondChild : _) ->
      let firstRevision = revisionId (handoffRevision firstChild)
          secondRevision = revisionId (handoffRevision secondChild)
      in handoffSupportDependencies secondChild == [DependsOnObligation firstRevision]
          && (secondRevision, firstRevision) `elem` handoffSupportEdges entries
    _ -> False

unknownPrerequisiteRejected :: Bool
unknownPrerequisiteRejected =
  case handoffResolvedObligation handoffConfig unknownPrerequisiteResolved of
    Left (UnknownPrerequisiteSupport consumer prerequisite) ->
      consumer == obligationId unknownParentObligation
        && prerequisite == missingPrerequisiteId
    Right _ -> False

exportDispositionPreserved :: Bool
exportDispositionPreserved =
  case handoffResolvedObligation handoffConfig exportedResolved of
    Right [entry] ->
      handoffDisposition entry == Exported exportBinding
        && handoffCanonicalProposition entry == Falsehood
        && null (handoffSupportDependencies entry)
    _ -> False

handoffConfig :: HandoffConfig
handoffConfig = HandoffConfig
  { handoffRevisionKind = const "Test"
  , handoffRepresentation = const "Core"
  , handoffSubjectIds = const ["subject"]
  , handoffContextIds = const ["context"]
  , handoffAcceptanceRule = const (AcceptEntry KernelChecked (EvidenceRole "establishes"))
  }

runtimeResolved :: ResolvedObligation
runtimeResolved = ResolvedObligation
  { resolvedObligation = parentObligation
  , resolvedCanonicalProposition = equalRef
  , resolvedPrerequisites = [childResolved]
  , resolvedDisposition = RuntimeBound runtimeBinding
  }

certificateResolved :: ResolvedObligation
certificateResolved = ResolvedObligation
  { resolvedObligation = certificateParentObligation
  , resolvedCanonicalProposition = Truth
  , resolvedPrerequisites = [childResolved]
  , resolvedDisposition = prerequisiteCertificateDisposition childObligation
  }

siblingResolved :: ResolvedObligation
siblingResolved = ResolvedObligation
  { resolvedObligation = siblingParentObligation
  , resolvedCanonicalProposition = Truth
  , resolvedPrerequisites = [childResolved, siblingConsumerResolved]
  , resolvedDisposition = StaticallyDischarged StaticByDefinition
  }

siblingConsumerResolved :: ResolvedObligation
siblingConsumerResolved = ResolvedObligation
  { resolvedObligation = siblingConsumerObligation
  , resolvedCanonicalProposition = Truth
  , resolvedPrerequisites = []
  , resolvedDisposition = prerequisiteCertificateDisposition childObligation
  }

unknownPrerequisiteResolved :: ResolvedObligation
unknownPrerequisiteResolved = ResolvedObligation
  { resolvedObligation = unknownParentObligation
  , resolvedCanonicalProposition = Truth
  , resolvedPrerequisites = []
  , resolvedDisposition = StaticallyDischarged StaticByCertificate
      { staticCertificateProducer = "test-producer"
      , staticCertificateChecker = "test-checker"
      , staticCertificate = CertificateAssumption
          (PrerequisiteFact missingPrerequisiteId)
          Truth
      }
  }

prerequisiteCertificateDisposition :: Obligation -> ObligationDisposition
prerequisiteCertificateDisposition prerequisite =
  StaticallyDischarged StaticByCertificate
    { staticCertificateProducer = "test-producer"
    , staticCertificateChecker = "test-checker"
    , staticCertificate = CertificateAssumption
        (PrerequisiteFact (obligationId prerequisite))
        Truth
    }

childResolved :: ResolvedObligation
childResolved = ResolvedObligation
  { resolvedObligation = childObligation
  , resolvedCanonicalProposition = Truth
  , resolvedPrerequisites = []
  , resolvedDisposition = StaticallyDischarged StaticByDefinition
  }

exportedResolved :: ResolvedObligation
exportedResolved = ResolvedObligation
  { resolvedObligation = exportObligation
  , resolvedCanonicalProposition = Falsehood
  , resolvedPrerequisites = []
  , resolvedDisposition = Exported exportBinding
  }

parentObligation :: Obligation
parentObligation = Obligation
  { obligationId = ObligationId "test.handoff.parent"
  , obligationProposition = Truth
  , obligationOrigin = "test"
  , obligationScope = "test.scope"
  , obligationRequiredPoint = "parent.required"
  }

certificateParentObligation :: Obligation
certificateParentObligation = Obligation
  { obligationId = ObligationId "test.handoff.certificate-parent"
  , obligationProposition = Truth
  , obligationOrigin = "test"
  , obligationScope = "test.scope"
  , obligationRequiredPoint = "certificate-parent.required"
  }

siblingParentObligation :: Obligation
siblingParentObligation = Obligation
  { obligationId = ObligationId "test.handoff.sibling-parent"
  , obligationProposition = Truth
  , obligationOrigin = "test"
  , obligationScope = "test.scope"
  , obligationRequiredPoint = "sibling-parent.required"
  }

siblingConsumerObligation :: Obligation
siblingConsumerObligation = Obligation
  { obligationId = ObligationId "test.handoff.sibling-consumer"
  , obligationProposition = Truth
  , obligationOrigin = "test"
  , obligationScope = "test.scope"
  , obligationRequiredPoint = "sibling-consumer.required"
  }

unknownParentObligation :: Obligation
unknownParentObligation = Obligation
  { obligationId = ObligationId "test.handoff.unknown-parent"
  , obligationProposition = Truth
  , obligationOrigin = "test"
  , obligationScope = "test.scope"
  , obligationRequiredPoint = "unknown-parent.required"
  }

missingPrerequisiteId :: ObligationId
missingPrerequisiteId = ObligationId "test.handoff.missing-prerequisite"

childObligation :: Obligation
childObligation = Obligation
  { obligationId = ObligationId "test.handoff.child"
  , obligationProposition = Truth
  , obligationOrigin = "test"
  , obligationScope = "test.scope"
  , obligationRequiredPoint = "child.required"
  }

exportObligation :: Obligation
exportObligation = Obligation
  { obligationId = ObligationId "test.handoff.export"
  , obligationProposition = Falsehood
  , obligationOrigin = "test"
  , obligationScope = "test.scope"
  , obligationRequiredPoint = "export.required"
  }

runtimeBinding :: RuntimeBinding
runtimeBinding = RuntimeBinding
  { runtimeObligationId = obligationId parentObligation
  , runtimeProposition = equalRef
  , runtimeRequiredPoint = obligationRequiredPoint parentObligation
  , runtimeValidator = "test-validator"
  , runtimeSuccessEvidence = TyProof equalRef
  , runtimeFailureClass = "ValidationFailure"
  , runtimeResourceContract = "no ownership change"
  , runtimeCostRef = "test.runtime.cost"
  }

exportBinding :: ExportBinding
exportBinding = ExportBinding
  { exportObligationId = obligationId exportObligation
  , exportProposition = Falsehood
  , exportRequiredPoint = obligationRequiredPoint exportObligation
  , exportBoundary = "parent.component"
  }

equalRef :: Proposition
equalRef = Equal (RefNat 1) (RefNat 1)
