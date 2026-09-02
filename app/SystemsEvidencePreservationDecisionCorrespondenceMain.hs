module Main where

import System.Exit (exitFailure)
import SystemsEvidencePreservationKernel

assert :: String -> Bool -> IO ()
assert label condition =
  if condition
    then putStrLn ("PASS: " <> label)
    else do
      putStrLn ("FAIL: " <> label)
      exitFailure

erasureTag :: EvidenceErasureDecision -> String
erasureTag decision = case decision of
  EvidenceErasureAcceptedDecision -> "accepted"
  EvidenceErasureAssuranceUseDecision -> "assurance-use"
  EvidenceErasureSourceSubjectDecision -> "source-subject"
  EvidenceErasureDischargeSubjectDecision -> "discharge-subject"
  EvidenceErasureRepresentationDecision -> "representation"
  EvidenceErasureLastUseDecision -> "last-use"
  EvidenceErasureConsumerClosureBasisDecision -> "closure-basis"
  EvidenceErasureSuccessorRevisionDecision -> "successor-revision"
  EvidenceErasureRuntimeResidueRevisionDecision -> "runtime-residue-revision"
  EvidenceErasureCostRevisionDecision -> "cost-revision"
  EvidenceErasureLaterConsumersDecision -> "later-consumers"

assumptionTag :: AssumptionDependencyDecision -> String
assumptionTag decision = case decision of
  AssumptionDependencyAcceptedDecision -> "accepted"
  AssumptionRegistryDecision -> "registry"
  AssumptionAuthorityDecision -> "authority"
  AssumptionValidityScopeDecision -> "validity-scope"
  AssumptionForwardDecision -> "forward"
  AssumptionForwardScopeDecision -> "forward-scope"
  AssumptionReverseDecision -> "reverse"

systemsTag :: SystemsEvidenceDecision -> String
systemsTag decision = case decision of
  SystemsEvidenceAcceptedDecision -> "accepted"
  SystemsEvidenceSubjectTransferDecision -> "subject-transfer"
  SystemsEvidenceErasureDecision -> "erasure"
  SystemsEvidenceAssumptionDecision -> "assumption"

checkErasure :: String -> String -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> IO ()
checkErasure label expected a b c d e f g h i j =
  assert label (erasureTag (decideEvidenceErasureByFacts a b c d e f g h i j) == expected)

checkAssumption :: String -> String -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> IO ()
checkAssumption label expected a b c d e f =
  assert label (assumptionTag (decideAssumptionDependencyByFacts a b c d e f) == expected)

checkSystems :: String -> String -> Bool -> Bool -> Bool -> IO ()
checkSystems label expected a b c =
  assert label (systemsTag (decideSystemsEvidenceByFacts a b c) == expected)

main :: IO ()
main = do
  checkErasure "SYS-EVID erasure accepts exact preserved facts" "accepted"
    True True True True True True True True True True
  checkErasure "SYS-EVID erasure requires accepted Assurance use" "assurance-use"
    False True True True True True True True True True
  checkErasure "SYS-EVID erasure requires exact source subject" "source-subject"
    True False True True True True True True True True
  checkErasure "SYS-EVID erasure requires exact discharge subject" "discharge-subject"
    True True False True True True True True True True
  checkErasure "SYS-EVID erasure requires representation identity" "representation"
    True True True False True True True True True True
  checkErasure "SYS-EVID erasure requires last semantic use" "last-use"
    True True True True False True True True True True
  checkErasure "SYS-EVID erasure requires consumer-closure basis" "closure-basis"
    True True True True True False True True True True
  checkErasure "SYS-EVID erasure requires well-formed successor revision" "successor-revision"
    True True True True True True False True True True
  checkErasure "SYS-EVID erasure requires well-formed runtime-residue revision" "runtime-residue-revision"
    True True True True True True True False True True
  checkErasure "SYS-EVID erasure requires well-formed cost revision" "cost-revision"
    True True True True True True True True False True
  checkErasure "SYS-EVID erasure requires all later consumers closed" "later-consumers"
    True True True True True True True True True False

  checkAssumption "SYS-EVID assumptions accept exact bidirectional dependencies" "accepted"
    True True True True True True
  checkAssumption "SYS-EVID assumptions require exact registry" "registry"
    False True True True True True
  checkAssumption "SYS-EVID assumptions require Certified authority" "authority"
    True False True True True True
  checkAssumption "SYS-EVID assumptions require validity scopes" "validity-scope"
    True True False True True True
  checkAssumption "SYS-EVID assumptions require exact forward dependencies" "forward"
    True True True False True True
  checkAssumption "SYS-EVID assumptions require exact forward scopes" "forward-scope"
    True True True True False True
  checkAssumption "SYS-EVID assumptions require exact reverse dependencies" "reverse"
    True True True True True False

  checkSystems "SYS-EVID cumulative acceptance" "accepted" True True True
  checkSystems "SYS-EVID cumulative subject-transfer predecessor" "subject-transfer" False True True
  checkSystems "SYS-EVID cumulative erasure suffix" "erasure" True False True
  checkSystems "SYS-EVID cumulative assumption suffix" "assumption" True True False
