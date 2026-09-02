module Main where

import System.Exit (exitFailure)
import qualified SystemsEvidencePreservationKernel as Kernel

assert :: String -> Bool -> IO ()
assert label condition =
  if condition
    then putStrLn ("PASS: " <> label)
    else do
      putStrLn ("FAIL: " <> label)
      exitFailure

toKernelBool :: Bool -> Kernel.Bool
toKernelBool value =
  if value then Kernel.True else Kernel.False

erasureTag :: Kernel.EvidenceErasureDecision -> String
erasureTag decision = case decision of
  Kernel.EvidenceErasureAcceptedDecision -> "accepted"
  Kernel.EvidenceErasureAssuranceUseDecision -> "assurance-use"
  Kernel.EvidenceErasureSourceSubjectDecision -> "source-subject"
  Kernel.EvidenceErasureDischargeSubjectDecision -> "discharge-subject"
  Kernel.EvidenceErasureRepresentationDecision -> "representation"
  Kernel.EvidenceErasureLastUseDecision -> "last-use"
  Kernel.EvidenceErasureConsumerClosureBasisDecision -> "closure-basis"
  Kernel.EvidenceErasureSuccessorRevisionDecision -> "successor-revision"
  Kernel.EvidenceErasureRuntimeResidueRevisionDecision -> "runtime-residue-revision"
  Kernel.EvidenceErasureCostRevisionDecision -> "cost-revision"
  Kernel.EvidenceErasureLaterConsumersDecision -> "later-consumers"

assumptionTag :: Kernel.AssumptionDependencyDecision -> String
assumptionTag decision = case decision of
  Kernel.AssumptionDependencyAcceptedDecision -> "accepted"
  Kernel.AssumptionRegistryDecision -> "registry"
  Kernel.AssumptionAuthorityDecision -> "authority"
  Kernel.AssumptionValidityScopeDecision -> "validity-scope"
  Kernel.AssumptionForwardDecision -> "forward"
  Kernel.AssumptionForwardScopeDecision -> "forward-scope"
  Kernel.AssumptionReverseDecision -> "reverse"

systemsTag :: Kernel.SystemsEvidenceDecision -> String
systemsTag decision = case decision of
  Kernel.SystemsEvidenceAcceptedDecision -> "accepted"
  Kernel.SystemsEvidenceSubjectTransferDecision -> "subject-transfer"
  Kernel.SystemsEvidenceErasureDecision -> "erasure"
  Kernel.SystemsEvidenceAssumptionDecision -> "assumption"

checkErasure :: String -> String -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> IO ()
checkErasure label expected a b c d e f g h i j =
  assert label
    (erasureTag
      (Kernel.decideEvidenceErasureByFacts
        (toKernelBool a) (toKernelBool b) (toKernelBool c) (toKernelBool d)
        (toKernelBool e) (toKernelBool f) (toKernelBool g) (toKernelBool h)
        (toKernelBool i) (toKernelBool j)) == expected)

checkAssumption :: String -> String -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> IO ()
checkAssumption label expected a b c d e f =
  assert label
    (assumptionTag
      (Kernel.decideAssumptionDependencyByFacts
        (toKernelBool a) (toKernelBool b) (toKernelBool c)
        (toKernelBool d) (toKernelBool e) (toKernelBool f)) == expected)

checkSystems :: String -> String -> Bool -> Bool -> Bool -> IO ()
checkSystems label expected a b c =
  assert label
    (systemsTag
      (Kernel.decideSystemsEvidenceByFacts
        (toKernelBool a) (toKernelBool b) (toKernelBool c)) == expected)

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
