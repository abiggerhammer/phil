module Main (main) where

import ProviderEvidenceQualificationKernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "evidence prefix accepts all exact reflected facts"
        (assertCompetenceAccepted
          (decideProviderEvidenceCompetenceByFacts
            True True True True True True))
    , test "unqualified operation rejects first"
        (assertOperationNotQualified
          (decideProviderEvidenceCompetenceByFacts
            False True True True True True))
    , test "operation mismatch rejects after qualification"
        (assertOperationMismatch
          (decideProviderEvidenceCompetenceByFacts
            True False True True True True))
    , test "family mismatch has certified precedence"
        (assertFamilyMismatch
          (decideProviderEvidenceCompetenceByFacts
            True True False True True True))
    , test "parameter mismatch has certified precedence"
        (assertParametersMismatch
          (decideProviderEvidenceCompetenceByFacts
            True True True False True True))
    , test "stable-subject mismatch has certified precedence"
        (assertStableSubjectMismatch
          (decideProviderEvidenceCompetenceByFacts
            True True True True False True))
    , test "validity mismatch has certified precedence"
        (assertValidityMismatch
          (decideProviderEvidenceCompetenceByFacts
            True True True True True False))
    , test "direct stable mapping accepts exact stable observation and subject"
        (assertMappingAccepted
          (decideDirectEvidenceSubjectMappingByFacts True True))
    , test "direct mapping rejects a non-stable exact observation"
        (assertDirectMappingRejected
          (decideDirectEvidenceSubjectMappingByFacts False True))
    , test "direct mapping rejects a mismatched stable subject"
        (assertDirectMappingRejected
          (decideDirectEvidenceSubjectMappingByFacts True False))
    , test "checked mapping accepts exact observation and stable subject"
        (assertMappingAccepted
          (decideCheckedEvidenceSubjectMappingByFacts True True))
    , test "checked mapping reports observation mismatch first"
        (assertCheckedObservationMismatch
          (decideCheckedEvidenceSubjectMappingByFacts False False))
    , test "checked mapping reports subject mismatch after observation"
        (assertCheckedSubjectMismatch
          (decideCheckedEvidenceSubjectMappingByFacts True False))
    , test "runtime coincidence never establishes subject competence"
        (assertRuntimeCoincidenceRejected
          decideRuntimeCoincidenceSubjectMapping)
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

assertCompetenceAccepted :: ProviderEvidenceCompetenceDecision -> Either String ()
assertCompetenceAccepted decision = case decision of
  ProviderEvidenceCompetenceAccepted -> Right ()
  _ -> Left "expected ProviderEvidenceCompetenceAccepted"

assertOperationNotQualified :: ProviderEvidenceCompetenceDecision -> Either String ()
assertOperationNotQualified decision = case decision of
  ProviderEvidenceOperationNotQualified -> Right ()
  _ -> Left "expected ProviderEvidenceOperationNotQualified"

assertOperationMismatch :: ProviderEvidenceCompetenceDecision -> Either String ()
assertOperationMismatch decision = case decision of
  ProviderEvidenceOperationMismatch -> Right ()
  _ -> Left "expected ProviderEvidenceOperationMismatch"

assertFamilyMismatch :: ProviderEvidenceCompetenceDecision -> Either String ()
assertFamilyMismatch decision = case decision of
  ProviderEvidenceFamilyMismatch -> Right ()
  _ -> Left "expected ProviderEvidenceFamilyMismatch"

assertParametersMismatch :: ProviderEvidenceCompetenceDecision -> Either String ()
assertParametersMismatch decision = case decision of
  ProviderEvidenceParametersMismatch -> Right ()
  _ -> Left "expected ProviderEvidenceParametersMismatch"

assertStableSubjectMismatch :: ProviderEvidenceCompetenceDecision -> Either String ()
assertStableSubjectMismatch decision = case decision of
  ProviderEvidenceStableSubjectMismatch -> Right ()
  _ -> Left "expected ProviderEvidenceStableSubjectMismatch"

assertValidityMismatch :: ProviderEvidenceCompetenceDecision -> Either String ()
assertValidityMismatch decision = case decision of
  ProviderEvidenceValidityMismatch -> Right ()
  _ -> Left "expected ProviderEvidenceValidityMismatch"

assertMappingAccepted :: ProviderEvidenceMappingDecision -> Either String ()
assertMappingAccepted decision = case decision of
  ProviderEvidenceMappingAccepted -> Right ()
  _ -> Left "expected ProviderEvidenceMappingAccepted"

assertDirectMappingRejected :: ProviderEvidenceMappingDecision -> Either String ()
assertDirectMappingRejected decision = case decision of
  ProviderEvidenceDirectMappingRejected -> Right ()
  _ -> Left "expected ProviderEvidenceDirectMappingRejected"

assertCheckedObservationMismatch :: ProviderEvidenceMappingDecision -> Either String ()
assertCheckedObservationMismatch decision = case decision of
  ProviderEvidenceCheckedObservationMismatch -> Right ()
  _ -> Left "expected ProviderEvidenceCheckedObservationMismatch"

assertCheckedSubjectMismatch :: ProviderEvidenceMappingDecision -> Either String ()
assertCheckedSubjectMismatch decision = case decision of
  ProviderEvidenceCheckedSubjectMismatch -> Right ()
  _ -> Left "expected ProviderEvidenceCheckedSubjectMismatch"

assertRuntimeCoincidenceRejected :: ProviderEvidenceMappingDecision -> Either String ()
assertRuntimeCoincidenceRejected decision = case decision of
  ProviderEvidenceRuntimeCoincidenceRejected -> Right ()
  _ -> Left "expected ProviderEvidenceRuntimeCoincidenceRejected"
