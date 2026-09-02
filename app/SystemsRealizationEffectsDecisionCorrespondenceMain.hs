module Main where

import qualified SystemsRealizationEffectsKernel as Kernel
import System.Exit (exitFailure)

assert :: String -> Bool -> IO ()
assert label condition =
  if condition
    then putStrLn ("PASS: " <> label)
    else do
      putStrLn ("FAIL: " <> label)
      exitFailure

strengtheningTag :: Kernel.TargetStrengtheningDecision -> String
strengtheningTag decision = case decision of
  Kernel.TargetStrengtheningAcceptedDecision -> "accepted"
  Kernel.TargetStrengtheningCoverageDecision -> "coverage"
  Kernel.TargetStrengtheningIntroducerDecision -> "introducer"
  Kernel.TargetStrengtheningSourceAssuranceDecision -> "source-assurance"
  Kernel.TargetStrengtheningDerivedRequiredDecision -> "derived-required"
  Kernel.TargetStrengtheningDerivedRevisionDecision -> "derived-revision"
  Kernel.TargetStrengtheningDerivedIntroducerDecision -> "derived-introducer"
  Kernel.TargetStrengtheningDerivedSubjectDecision -> "derived-subject"
  Kernel.TargetStrengtheningDerivedStatementDecision -> "derived-statement"
  Kernel.TargetStrengtheningDerivedAcceptanceDecision -> "derived-acceptance"

stagingTag :: Kernel.StagingEffectDecision -> String
stagingTag decision = case decision of
  Kernel.StagingEffectAcceptedDecision -> "accepted"
  Kernel.StagingEffectCoverageDecision -> "coverage"
  Kernel.StagingEffectRequirementDecision -> "requirement"
  Kernel.StagingEffectEffectDecision -> "effect"
  Kernel.StagingEffectAuthorityDecision -> "authority"
  Kernel.StagingEffectFailureDecision -> "failure"
  Kernel.StagingEffectTransferDecision -> "transfer"
  Kernel.StagingEffectCostDecision -> "cost"
  Kernel.StagingEffectBytesDecision -> "bytes"
  Kernel.StagingEffectFrequencyDecision -> "frequency"

nextStageTag :: Kernel.NextStageExportDecision -> String
nextStageTag decision = case decision of
  Kernel.NextStageExportAcceptedDecision -> "accepted"
  Kernel.NextStageExportCoverageDecision -> "coverage"
  Kernel.NextStageExportRevisionDecision -> "revision"
  Kernel.NextStageExportSourceDecision -> "source"
  Kernel.NextStageExportFactDecision -> "fact"
  Kernel.NextStageExportFolkloreDecision -> "folklore"
  Kernel.NextStageExportAcceptanceDecision -> "acceptance"
  Kernel.NextStageExportScopeDecision -> "scope"

realizationTag :: Kernel.SystemsRealizationEffectsDecision -> String
realizationTag decision = case decision of
  Kernel.SystemsRealizationEffectsAcceptedDecision -> "accepted"
  Kernel.SystemsRealizationEffectsStageClosureDecision -> "stage-closure"
  Kernel.SystemsRealizationEffectsStrengtheningDecision -> "strengthening"
  Kernel.SystemsRealizationEffectsStagingDecision -> "staging"
  Kernel.SystemsRealizationEffectsNextStageDecision -> "next-stage"

checkStrengthening
  :: String -> String
  -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
  -> IO ()
checkStrengthening label expected a b c d e f g h i =
  assert label
    (strengtheningTag (Kernel.decideTargetStrengtheningByFacts a b c d e f g h i)
      == expected)

checkStaging
  :: String -> String
  -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
  -> IO ()
checkStaging label expected a b c d e f g h i =
  assert label
    (stagingTag (Kernel.decideStagingEffectByFacts a b c d e f g h i)
      == expected)

checkNextStage
  :: String -> String
  -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
  -> IO ()
checkNextStage label expected a b c d e f g =
  assert label
    (nextStageTag (Kernel.decideNextStageExportByFacts a b c d e f g)
      == expected)

checkRealization :: String -> String -> Bool -> Bool -> Bool -> Bool -> IO ()
checkRealization label expected a b c d =
  assert label
    (realizationTag (Kernel.decideSystemsRealizationEffectsByFacts a b c d)
      == expected)

main :: IO ()
main = do
  checkStrengthening "SYS-014 accepts exact target strengthening" "accepted"
    True True True True True True True True True
  checkStrengthening "SYS-014 requires exact target-precondition coverage" "coverage"
    False True True True True True True True True
  checkStrengthening "SYS-014 requires nonempty introducer identity" "introducer"
    True False True True True True True True True
  checkStrengthening "SYS-014 forbids unknown source assurance" "source-assurance"
    True True False True True True True True True
  checkStrengthening "SYS-014 requires derived obligation when source assurance is absent" "derived-required"
    True True True False True True True True True
  checkStrengthening "SYS-014 requires derived revision identity" "derived-revision"
    True True True True False True True True True
  checkStrengthening "SYS-014 requires exact derived introducer" "derived-introducer"
    True True True True True False True True True
  checkStrengthening "SYS-014 requires derived semantic subject" "derived-subject"
    True True True True True True False True True
  checkStrengthening "SYS-014 requires derived proposition/refinement statement" "derived-statement"
    True True True True True True True False True
  checkStrengthening "SYS-014 requires derived acceptance rule" "derived-acceptance"
    True True True True True True True True False

  checkStaging "SYS-017 accepts complete staging consequences" "accepted"
    True True True True True True True True True
  checkStaging "SYS-017 requires exact event coverage" "coverage"
    False True True True True True True True True
  checkStaging "SYS-017 requires staging requirement identity" "requirement"
    True False True True True True True True True
  checkStaging "SYS-017 requires realization effect" "effect"
    True True False True True True True True True
  checkStaging "SYS-017 requires authority account" "authority"
    True True True False True True True True True
  checkStaging "SYS-017 requires explicit failure account" "failure"
    True True True True False True True True True
  checkStaging "SYS-017 requires semantic subject transfer" "transfer"
    True True True True True False True True True
  checkStaging "SYS-017 requires target-required cost identity" "cost"
    True True True True True True False True True
  checkStaging "SYS-017 requires bytes-copied accounting" "bytes"
    True True True True True True True False True
  checkStaging "SYS-017 requires frequency accounting" "frequency"
    True True True True True True True True False

  checkNextStage "SYS-019 accepts exact competence-boundary export" "accepted"
    True True True True True True True
  checkNextStage "SYS-019 requires exact requirement coverage" "coverage"
    False True True True True True True
  checkNextStage "SYS-019 requires requirement revision" "revision"
    True False True True True True True
  checkNextStage "SYS-019 requires exact source provenance" "source"
    True True False True True True True
  checkNextStage "SYS-019 requires exact fact or contract" "fact"
    True True True False True True True
  checkNextStage "SYS-019 rejects folklore-only requirements" "folklore"
    True True True True False True True
  checkNextStage "SYS-019 requires acceptance rule" "acceptance"
    True True True True True False True
  checkNextStage "SYS-019 requires validity scope" "scope"
    True True True True True True False

  checkRealization "SYS-REALIZE cumulative acceptance" "accepted"
    True True True True
  checkRealization "SYS-REALIZE requires bound Stage Closure predecessor" "stage-closure"
    False True True True
  checkRealization "SYS-REALIZE requires target strengthening" "strengthening"
    True False True True
  checkRealization "SYS-REALIZE requires staging effects" "staging"
    True True False True
  checkRealization "SYS-REALIZE requires next-stage export" "next-stage"
    True True True False
