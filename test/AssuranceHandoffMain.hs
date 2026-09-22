{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
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
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "handoff preserves runtime disposition and canonical proposition" runtimeDispositionPreserved
    , test "generated prerequisite revision records exact parent lineage" prerequisiteLineagePreserved
    , test "certificate prerequisite becomes explicit parent-to-child support" certificatePrerequisiteSupportPreserved
    , test "later sibling certificate can depend on earlier sibling revision" siblingPrerequisiteSupportPreserved
    , test "unknown certificate prerequisite fails closed" unknownPrerequisiteRejected
    , test "handoff preserves explicit export disposition" exportDispositionPreserved
    ]
  if and results then pure () else exitFailure

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
      in handoffSupportDependencies parent == [DependsOnObligation childRevision]
          && revisionGeneratedFrom (handoffRevision parent) == []
          && revisionGeneratedFrom (handoffRevision child) == [parentRevision]
          && handoffSupportEdges entries == Set.singleton (parentRevision, childRevision)
          && not (Set.member (childRevision, parentRevision) (handoffSupportEdges entries))
    _ -> False

siblingPrerequisiteSupportPreserved :: Bool
siblingPrerequisiteSupportPreserved =
  case handoffResolvedObligation handoffConfig siblingResolved of
    Right entries@(_parent : firstChild : secondChild : _) ->
      let firstRevision = revisionId (handoffRevision firstChild)
          secondRevision = revisionId (handoffRevision secondChild)
      in handoffSupportDependencies secondChild == [DependsOnObligation firstRevision]
          && Set.member (secondRevision, firstRevision) (handoffSupportEdges entries)
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

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
