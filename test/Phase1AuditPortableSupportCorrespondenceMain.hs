{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.List (sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Assurance.Types
import Phil.Handoff.Phase1AssuranceInputs
import Phil.Verification
  ( ApplicationAssurancePolicy (..)
  , AssurancePolicyRevision (..)
  , VerificationDisposition (..)
  )
import Phil.Verification.ManifestClosure (ManifestClosureSelection (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ runTest "portable assurance input preserves typed support edges exactly"
        typedSupportRoundTripPreserves
    , runTest "precise evidence support remains selection-bound"
        missingSelectedEvidenceSupportRejects
    , runTest "support-edge constructor mutation is content-bound"
        supportConstructorMutationRejects
    , runTest "obligation support remains deferred and distinct from evidence selection"
        obligationSupportRemainsTyped
    ]
  if and results then pure () else exitFailure

typedSupportRoundTripPreserves :: Either String ()
typedSupportRoundTripPreserves = do
  inputs <- deriveTypedSupportInputs
  decoded <- decodeInputs (renderPhase1AssuranceInputs inputs)
  if decoded /= inputs
    then Left "render/decode changed the selected assurance inputs"
    else case Map.lookup primaryEvidenceId
        (ledgerEvidence (phase1AssuranceLedger decoded)) of
      Nothing -> Left "decoded ledger lost the primary evidence entry"
      Just entry
        | evidenceDependsOn entry == expectedTypedDependencies -> Right ()
        | otherwise -> Left
            ("decoded support differs: " <> show (evidenceDependsOn entry))

missingSelectedEvidenceSupportRejects :: Either String ()
missingSelectedEvidenceSupportRejects =
  case derivePhase1AssuranceInputs staticPolicy typedSupportLedger primaryOnlySelection of
    Left _ -> Right ()
    Right _ -> Left "unselected DependsOnEvidence target was accepted"

supportConstructorMutationRejects :: Either String ()
supportConstructorMutationRejects = do
  inputs <- deriveTypedSupportInputs
  let source = renderPhase1AssuranceInputs inputs
      mutated = Text.replace
        "evidence-dependency-evidence"
        "evidence-dependency-obligation"
        source
  case decodePhase1AssuranceInputs mutated of
    Left _ -> Right ()
    Right _ -> Left "changing a precise evidence edge into an obligation edge was accepted"

obligationSupportRemainsTyped :: Either String ()
obligationSupportRemainsTyped = do
  inputs <- deriveInputs obligationOnlyLedger primaryOnlySelection
  decoded <- decodeInputs (renderPhase1AssuranceInputs inputs)
  case Map.lookup primaryEvidenceId
      (ledgerEvidence (phase1AssuranceLedger decoded)) of
    Nothing -> Left "decoded ledger lost obligation-supported evidence"
    Just entry
      | evidenceDependsOn entry == [DependsOnObligation prerequisiteRevision] -> Right ()
      | otherwise -> Left
          ("obligation support changed representation: " <> show (evidenceDependsOn entry))

deriveTypedSupportInputs :: Either String Phase1AssuranceInputs
deriveTypedSupportInputs = deriveInputs typedSupportLedger typedSupportSelection

deriveInputs
  :: AssuranceLedger
  -> ManifestClosureSelection
  -> Either String Phase1AssuranceInputs
deriveInputs ledger selection =
  case derivePhase1AssuranceInputs staticPolicy ledger selection of
    Left errorValue -> Left ("derivation failed: " <> show errorValue)
    Right inputs -> Right inputs

decodeInputs :: Text.Text -> Either String Phase1AssuranceInputs
decodeInputs source =
  case decodePhase1AssuranceInputs source of
    Left errorValue -> Left ("decode failed: " <> show errorValue)
    Right inputs -> Right inputs

staticPolicy :: ApplicationAssurancePolicy
staticPolicy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision = AssurancePolicyRevision "policy.portable-support"
  , applicationAssurancePolicyPermittedDispositions =
      Set.singleton StaticallyDischarged
  }

typedSupportLedger :: AssuranceLedger
typedSupportLedger = emptyLedger
  { ledgerEvidence = Map.fromList
      [ (helperEvidenceId, helperEvidence)
      , (primaryEvidenceId, primaryEvidence)
      ]
  }

obligationOnlyLedger :: AssuranceLedger
obligationOnlyLedger = emptyLedger
  { ledgerEvidence = Map.singleton primaryEvidenceId obligationOnlyEvidence
  }

typedSupportSelection :: ManifestClosureSelection
typedSupportSelection = emptySelection
  { manifestClosureEvidence = Set.fromList [helperEvidenceId, primaryEvidenceId]
  }

primaryOnlySelection :: ManifestClosureSelection
primaryOnlySelection = emptySelection
  { manifestClosureEvidence = Set.singleton primaryEvidenceId
  }

emptySelection :: ManifestClosureSelection
emptySelection = ManifestClosureSelection
  { manifestClosureEvidence = Set.empty
  , manifestClosureAssumptions = Set.empty
  , manifestClosureExports = Map.empty
  , manifestClosureUses = Set.empty
  }

helperEvidenceId :: EvidenceEntryId
helperEvidenceId = EvidenceEntryId "evidence.portable.helper"

primaryEvidenceId :: EvidenceEntryId
primaryEvidenceId = EvidenceEntryId "evidence.portable.primary"

helperRevision :: RevisionId
helperRevision = RevisionId "revision.portable.helper"

primaryRevision :: RevisionId
primaryRevision = RevisionId "revision.portable.primary"

prerequisiteRevision :: RevisionId
prerequisiteRevision = RevisionId "revision.portable.prerequisite"

expectedTypedDependencies :: [EvidenceDependency]
expectedTypedDependencies = sort
  [ DependsOnEvidence helperEvidenceId
  , DependsOnObligation prerequisiteRevision
  ]

helperEvidence :: EvidenceEntry
helperEvidence = mkEvidence helperEvidenceId helperRevision []

primaryEvidence :: EvidenceEntry
primaryEvidence = mkEvidence primaryEvidenceId primaryRevision expectedTypedDependencies

obligationOnlyEvidence :: EvidenceEntry
obligationOnlyEvidence =
  mkEvidence primaryEvidenceId primaryRevision
    [DependsOnObligation prerequisiteRevision]

mkEvidence
  :: EvidenceEntryId
  -> RevisionId
  -> [EvidenceDependency]
  -> EvidenceEntry
mkEvidence entryId revision dependencies =
  provisional
    { evidenceEntryDigest = deriveEvidenceEntryDigest provisional }
  where
    provisional = EvidenceEntry
      { evidenceEntryId = entryId
      , evidenceEntryDigest = Digest ""
      , evidenceObligationRevision = revision
      , evidenceAssuranceKind = KernelChecked
      , evidenceRole = EvidenceRole "portable-support"
      , evidenceProducer = "audit-correspondence"
      , evidenceChecker = "audit-correspondence"
      , evidenceArtifact = Nothing
      , evidenceInputDigests = []
      , evidenceAssumptions = []
      , evidenceDependsOn = sort dependencies
      , evidenceValidityScope = ValidityScope Map.empty
      , evidenceResult = EvidenceAccepted
      , evidenceJustifies = []
      , evidenceRuntimeMechanism = Nothing
      , evidenceRuntimeResidue = []
      , evidenceCostRefs = []
      }

runTest :: String -> Either String () -> IO Bool
runTest label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False
