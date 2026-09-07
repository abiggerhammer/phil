{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance
  ( AcceptanceRule (..)
  , AssuranceKind (..)
  , Digest (..)
  , EvidenceEntry (..)
  , EvidenceEntryId (..)
  , EvidenceResult (..)
  , EvidenceRole (..)
  , RevisionId (..)
  , ValidityScope (..)
  , deriveEvidenceEntryDigest
  , digestText
  )
import Phil.Core.Static
  ( ArchitectureInstanceDescriptor (..)
  , ArchitectureInstanceIdentity
  , ArchitectureRealizationDescriptor (..)
  , ArchitectureRealizationIdentity
  , DeclarationDescriptor (..)
  , DeclarationIdentity
  , DeclarationKey (..)
  , DeclarationPresentation (..)
  , InstanceKey (..)
  , SemanticForm (..)
  , deriveArchitectureInstanceIdentity
  , deriveArchitectureRealizationIdentity
  , deriveDeclarationIdentity
  )
import Phil.Core.Syntax
  ( Obligation (..)
  , ObligationId (..)
  , Proposition (..)
  , RefTerm (..)
  )
import Phil.Verification
  ( ApplicationAssurancePolicy (..)
  , AssurancePolicyRevision (..)
  , VerificationDisposition (..)
  , VerificationGraphError
  , VerificationObligationGraph (..)
  , VerificationObligationInput (..)
  , buildVerificationObligationGraph
  )
import Phil.Verification.Bundle
  ( IntrinsicVerificationResult (..)
  , VerificationBundle (..)
  , VerificationBundleError (..)
  , buildVerificationBundle
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  graph <- graphOrFail baseInputs
  reorderedGraph <- graphOrFail (reverse baseInputs)
  base <- bundleOrFail $ buildVerificationBundle
    sourceRevision
    [declarationMain, declarationAux]
    [instanceMain, instanceAux]
    [realizationMain]
    graph
    policyA
    [evidenceRoot, evidenceDep]
  reordered <- bundleOrFail $ buildVerificationBundle
    sourceRevision
    [declarationAux, declarationMain, declarationMain]
    [instanceAux, instanceMain]
    [realizationMain]
    reorderedGraph
    policyA
    [evidenceDep, evidenceRoot, evidenceRoot]
  changedSource <- bundleOrFail $ buildVerificationBundle
    (digestText "ver012.source.semantic.v2")
    [declarationMain, declarationAux]
    [instanceMain, instanceAux]
    [realizationMain]
    graph
    policyA
    [evidenceRoot, evidenceDep]
  changedDeclaration <- bundleOrFail $ buildVerificationBundle
    sourceRevision
    [declarationChanged, declarationAux]
    [instanceChanged, instanceAux]
    [realizationChangedDeclaration]
    graph
    policyA
    [evidenceRoot, evidenceDep]
  changedRealization <- bundleOrFail $ buildVerificationBundle
    sourceRevision
    [declarationMain, declarationAux]
    [instanceMain, instanceAux]
    [realizationChangedTarget]
    graph
    policyA
    [evidenceRoot, evidenceDep]
  changedPolicy <- bundleOrFail $ buildVerificationBundle
    sourceRevision
    [declarationMain, declarationAux]
    [instanceMain, instanceAux]
    [realizationMain]
    graph
    policyB
    [evidenceRoot, evidenceDep]
  changedEvidence <- bundleOrFail $ buildVerificationBundle
    sourceRevision
    [declarationMain, declarationAux]
    [instanceMain, instanceAux]
    [realizationMain]
    graph
    policyA
    [rekeyEvidenceProducer evidenceRoot, evidenceDep]
  let checks =
        [ ("canonical bundle is independent of traversal and duplicate input order",
            base == reordered)
        , ("bundle exposes explicit intrinsic acceptance rather than Haskell reachability",
            verificationBundleIntrinsicResult base == IntrinsicVerificationAccepted)
        , ("bundle exposes exact canonical obligation graph and dependency target",
            verificationBundleObligationGraph base == graph
              && Set.size (verificationGraphDependencies graph) == 1)
        , ("source semantic revision changes independent verification target",
            verificationBundleRevision changedSource /= verificationBundleRevision base)
        , ("declaration and architecture revision changes rekey target",
            verificationBundleRevision changedDeclaration /= verificationBundleRevision base)
        , ("realization revision changes rekey target",
            verificationBundleRevision changedRealization /= verificationBundleRevision base)
        , ("assurance policy identity changes rekey target",
            verificationBundleRevision changedPolicy /= verificationBundleRevision base)
        , ("accepted evidence replacement changes bundle lineage without source or graph identity",
            verificationBundleRevision changedEvidence /= verificationBundleRevision base
              && verificationBundleSourceRevision changedEvidence
                == verificationBundleSourceRevision base
              && verificationGraphRevision
                  (verificationBundleObligationGraph changedEvidence)
                == verificationGraphRevision
                  (verificationBundleObligationGraph base))
        , ("presentation-only declaration renaming does not change canonical target",
            declarationMain == declarationPresentationVariant)
        , ("rejected evidence cannot enter independent verification target",
            testRejectedEvidence graph)
        , ("stale evidence digest cannot enter independent verification target",
            testStaleEvidenceDigest graph)
        , ("evidence for unknown obligation cannot enter independent verification target",
            testUnknownEvidenceTarget graph)
        ]
  mapM_ report checks
  unless (and (map snd checks)) exitFailure
  where
    report (label, True) = putStrLn ("PASS: VER-012 " ++ label)
    report (label, False) = putStrLn ("FAIL: VER-012 " ++ label)

graphOrFail
  :: [VerificationObligationInput]
  -> IO VerificationObligationGraph
graphOrFail inputs =
  case buildVerificationObligationGraph inputs (Set.singleton rootId) of
    Left errorValue -> failCase ("could not build graph: " ++ show errorValue)
    Right graph -> pure graph

bundleOrFail
  :: Either VerificationBundleError VerificationBundle
  -> IO VerificationBundle
bundleOrFail result = case result of
  Left errorValue -> failCase ("could not build bundle: " ++ show errorValue)
  Right bundle -> pure bundle

failCase :: String -> IO a
failCase message = putStrLn ("FAIL: VER-012 " ++ message) >> exitFailure

sourceRevision :: Digest
sourceRevision = digestText "ver012.source.semantic.v1"

policyA :: ApplicationAssurancePolicy
policyA = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision = AssurancePolicyRevision "policy.ver012.v1"
  , applicationAssurancePolicyPermittedDispositions =
      Set.fromList [StaticallyDischarged, RuntimeBound]
  }

policyB :: ApplicationAssurancePolicy
policyB = policyA
  { applicationAssurancePolicyRevision = AssurancePolicyRevision "policy.ver012.v2" }

rootId :: ObligationId
rootId = ObligationId "ver012.root"

depId :: ObligationId
depId = ObligationId "ver012.dep"

rootObligation :: Obligation
rootObligation = Obligation
  { obligationId = rootId
  , obligationProposition = LessEqual (RefNat 1) (RefNat 2)
  , obligationOrigin = "checked.callable:ver012.root"
  , obligationScope = "application:ver012"
  , obligationRequiredPoint = "before:ver012.root"
  }

depObligation :: Obligation
depObligation = Obligation
  { obligationId = depId
  , obligationProposition = Equal (RefNat 3) (RefNat 3)
  , obligationOrigin = "checked.callable:ver012.dep"
  , obligationScope = "application:ver012"
  , obligationRequiredPoint = "before:ver012.dep"
  }

rootInput :: VerificationObligationInput
rootInput = VerificationObligationInput
  { verificationInputObligation = rootObligation
  , verificationInputKind = "semantic"
  , verificationInputRepresentation = "phil-core/proposition-v1"
  , verificationInputSubjectIds = ["subject:root"]
  , verificationInputContextIds = ["context:ver012"]
  , verificationInputAcceptanceRule =
      AcceptEntry CertificateChecked (EvidenceRole "static-proof")
  , verificationInputDependencies = Set.singleton depId
  }

depInput :: VerificationObligationInput
depInput = VerificationObligationInput
  { verificationInputObligation = depObligation
  , verificationInputKind = "semantic-prerequisite"
  , verificationInputRepresentation = "phil-core/proposition-v1"
  , verificationInputSubjectIds = ["subject:dep"]
  , verificationInputContextIds = ["context:ver012"]
  , verificationInputAcceptanceRule =
      AcceptEntry KernelChecked (EvidenceRole "semantic")
  , verificationInputDependencies = Set.empty
  }

baseInputs :: [VerificationObligationInput]
baseInputs = [rootInput, depInput]

declarationMain :: DeclarationIdentity
declarationMain = deriveDeclarationIdentity baseDeclaration

declarationPresentationVariant :: DeclarationIdentity
declarationPresentationVariant = deriveDeclarationIdentity baseDeclaration
  { declarationPresentation = DeclarationPresentation "renamed" ["Elsewhere", "Module"] }

declarationChanged :: DeclarationIdentity
declarationChanged = deriveDeclarationIdentity baseDeclaration
  { declarationDefinitionSemantics = SemanticAtom "definition-v2" }

declarationAux :: DeclarationIdentity
declarationAux = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation "aux" ["Ver012"]
  , declarationKey = DeclarationKey "declaration.ver012.aux"
  , declarationInterfaceSemantics = SemanticAtom "interface-aux"
  , declarationDefinitionSemantics = SemanticAtom "definition-aux"
  }

baseDeclaration :: DeclarationDescriptor
baseDeclaration = DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation "main" ["Ver012"]
  , declarationKey = DeclarationKey "declaration.ver012.main"
  , declarationInterfaceSemantics = SemanticAtom "interface-v1"
  , declarationDefinitionSemantics = SemanticAtom "definition-v1"
  }

instanceMain :: ArchitectureInstanceIdentity
instanceMain = deriveArchitectureInstanceIdentity (instanceDescriptor declarationMain)

instanceChanged :: ArchitectureInstanceIdentity
instanceChanged = deriveArchitectureInstanceIdentity (instanceDescriptor declarationChanged)

instanceAux :: ArchitectureInstanceIdentity
instanceAux = deriveArchitectureInstanceIdentity ArchitectureInstanceDescriptor
  { architectureInstanceKey = InstanceKey "instance.ver012.aux"
  , architectureParentInstanceKey = Nothing
  , architectureDeclarationIdentity = declarationAux
  , architectureStaticBindings = Map.empty
  }

instanceDescriptor :: DeclarationIdentity -> ArchitectureInstanceDescriptor
instanceDescriptor declaration = ArchitectureInstanceDescriptor
  { architectureInstanceKey = InstanceKey "instance.ver012.main"
  , architectureParentInstanceKey = Nothing
  , architectureDeclarationIdentity = declaration
  , architectureStaticBindings = Map.fromList [("T", SemanticAtom "Blob")]
  }

realizationMain :: ArchitectureRealizationIdentity
realizationMain = realizationFor instanceMain "native-v1"

realizationChangedTarget :: ArchitectureRealizationIdentity
realizationChangedTarget = realizationFor instanceMain "wasm-v1"

realizationChangedDeclaration :: ArchitectureRealizationIdentity
realizationChangedDeclaration = realizationFor instanceChanged "native-v1"

realizationFor :: ArchitectureInstanceIdentity -> Text -> ArchitectureRealizationIdentity
realizationFor instanceIdentity target = deriveArchitectureRealizationIdentity
  ArchitectureRealizationDescriptor
    { realizationInstanceIdentity = instanceIdentity
    , realizationSemantics = SemanticAtom target
    }

evidenceRoot :: EvidenceEntry
evidenceRoot = mkEvidence "root" rootRevisionId "producer.ver012.root"

evidenceDep :: EvidenceEntry
evidenceDep = mkEvidence "dep" depRevisionId "producer.ver012.dep"

rootRevisionId :: RevisionId
rootRevisionId = revisionFor rootId

depRevisionId :: RevisionId
depRevisionId = revisionFor depId

revisionFor :: ObligationId -> RevisionId
revisionFor targetId =
  case buildVerificationObligationGraph baseInputs (Set.singleton rootId) of
    Left errorValue -> error ("VER-012 fixture graph failure: " ++ show errorValue)
    Right graph -> case
        [ revision
        | (revision, node) <- Map.toAscList (verificationGraphNodes graph)
        , revisionObligationId node == targetId
        ] of
      [revision] -> revision
      _ -> error "VER-012 fixture could not resolve obligation revision"

mkEvidence :: Text -> RevisionId -> Text -> EvidenceEntry
mkEvidence suffix revision producer = provisional
  { evidenceEntryDigest = deriveEvidenceEntryDigest provisional }
  where
    provisional = EvidenceEntry
      { evidenceEntryId = EvidenceEntryId ("evidence.ver012." <> suffix)
      , evidenceEntryDigest = Digest ""
      , evidenceObligationRevision = revision
      , evidenceAssuranceKind = CertificateChecked
      , evidenceRole = EvidenceRole "static-proof"
      , evidenceProducer = producer
      , evidenceChecker = "checker.ver012.competent"
      , evidenceArtifact = Nothing
      , evidenceInputDigests = []
      , evidenceAssumptions = []
      , evidenceDependsOn = []
      , evidenceValidityScope = ValidityScope Map.empty
      , evidenceResult = EvidenceAccepted
      , evidenceJustifies = ["VER-012 canonical bundle fixture"]
      , evidenceRuntimeMechanism = Nothing
      , evidenceRuntimeResidue = []
      , evidenceCostRefs = []
      }

rekeyEvidenceProducer :: EvidenceEntry -> EvidenceEntry
rekeyEvidenceProducer entry = changed
  { evidenceEntryDigest = deriveEvidenceEntryDigest changed }
  where
    changed = entry { evidenceProducer = "producer.ver012.alternative" }

testRejectedEvidence :: VerificationObligationGraph -> Bool
testRejectedEvidence graph =
  let rejected = evidenceRoot { evidenceResult = EvidenceRejected "fixture rejection" }
  in case buildVerificationBundle
      sourceRevision
      [declarationMain]
      [instanceMain]
      [realizationMain]
      graph
      policyA
      [rejected] of
    Left (VerificationEvidenceRejected entryId _) ->
      entryId == evidenceEntryId rejected
    _ -> False

testStaleEvidenceDigest :: VerificationObligationGraph -> Bool
testStaleEvidenceDigest graph =
  let stale = evidenceRoot { evidenceEntryDigest = Digest "stale" }
  in case buildVerificationBundle
      sourceRevision
      [declarationMain]
      [instanceMain]
      [realizationMain]
      graph
      policyA
      [stale] of
    Left (VerificationEvidenceDigestMismatch entryId _ actual) ->
      entryId == evidenceEntryId stale && actual == Digest "stale"
    _ -> False

testUnknownEvidenceTarget :: VerificationObligationGraph -> Bool
testUnknownEvidenceTarget graph =
  let unknown = (mkEvidence "unknown" (RevisionId "rev.ver012.unknown") "producer.ver012.unknown")
  in case buildVerificationBundle
      sourceRevision
      [declarationMain]
      [instanceMain]
      [realizationMain]
      graph
      policyA
      [unknown] of
    Left (VerificationEvidenceUnknownObligation entryId revision) ->
      entryId == evidenceEntryId unknown
        && revision == RevisionId "rev.ver012.unknown"
    _ -> False
