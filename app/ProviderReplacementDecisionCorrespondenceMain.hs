module Main (main) where

import qualified ProviderReplacementQualificationKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ replacementCase "replacement accepts when every reflected invariant holds"
        allTrue "accepted"
    , replacementCase "prior admission failure wins first"
        (decision False False False False False False False False False False False False)
        "admission-required"
    , replacementCase "replacement admission failure wins before identity checks"
        (decision True False False False False False False False False False False False)
        "admission-required"
    , replacementCase "interface mismatch has certified precedence"
        (decision True True False False False False False False False False False False)
        "interface-mismatch"
    , replacementCase "occurrence mismatch has certified precedence"
        (decision True True True False False False False False False False False False)
        "occurrence-mismatch"
    , replacementCase "instance mismatch has certified precedence"
        (decision True True True True False False False False False False False False)
        "instance-mismatch"
    , replacementCase "same semantic subject rejects"
        (decision True True True True True False False False False False False False)
        "same-subject"
    , replacementCase "unchanged realization rejects"
        (decision True True True True True True False False False False False False)
        "realization-unchanged"
    , replacementCase "inherited claim lineage rejects"
        (decision True True True True True True True False False False False False)
        "claim-inherited"
    , replacementCase "inherited evidence lineage rejects"
        (decision True True True True True True True True False False False False)
        "evidence-inherited"
    , replacementCase "inherited admission lineage rejects"
        (decision True True True True True True True True True False False False)
        "admission-inherited"
    , replacementCase "shared evidence without explicit scope rejects"
        (decision True True True True True True True True True True False False)
        "shared-evidence-unscoped"
    , replacementCase "spurious reuse justification rejects"
        (decision True True True True True True True True True True True False)
        "unexpected-reuse"
    , reuseCase "exact scoped reuse accepts"
        (Kernel.decideProviderReplacementReuseByFacts True True True True)
        "reuse-accepted"
    , reuseCase "reuse reference mismatch rejects first"
        (Kernel.decideProviderReplacementReuseByFacts False False False False)
        "reference-mismatch"
    , reuseCase "reuse prior claim mismatch rejects"
        (Kernel.decideProviderReplacementReuseByFacts True False False False)
        "prior-claim-mismatch"
    , reuseCase "reuse new claim mismatch rejects"
        (Kernel.decideProviderReplacementReuseByFacts True True False False)
        "new-claim-mismatch"
    , reuseCase "reuse without validity scope rejects"
        (Kernel.decideProviderReplacementReuseByFacts True True True False)
        "scope-missing"
    ]
  if and results then pure () else exitFailure

allTrue :: Kernel.ProviderReplacementDecision
allTrue = decision True True True True True True True True True True True True

decision
  :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool
  -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
  -> Kernel.ProviderReplacementDecision
decision = Kernel.decideProviderReplacementByFacts

replacementCase :: String -> Kernel.ProviderReplacementDecision -> String -> IO Bool
replacementCase label actual expected = report label (replacementTag actual == expected)

reuseCase :: String -> Kernel.ProviderReplacementReuseDecision -> String -> IO Bool
reuseCase label actual expected = report label (reuseTag actual == expected)

report :: String -> Bool -> IO Bool
report label ok = do
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> label)
  pure ok

replacementTag :: Kernel.ProviderReplacementDecision -> String
replacementTag result = case result of
  Kernel.ProviderReplacementAccepted -> "accepted"
  Kernel.ProviderReplacementAdmissionRequired -> "admission-required"
  Kernel.ProviderReplacementInterfaceMismatch -> "interface-mismatch"
  Kernel.ProviderReplacementOccurrenceMismatch -> "occurrence-mismatch"
  Kernel.ProviderReplacementInstanceMismatch -> "instance-mismatch"
  Kernel.ProviderReplacementSameSemanticSubject -> "same-subject"
  Kernel.ProviderReplacementRealizationUnchanged -> "realization-unchanged"
  Kernel.ProviderReplacementClaimLineageInherited -> "claim-inherited"
  Kernel.ProviderReplacementEvidenceLineageInherited -> "evidence-inherited"
  Kernel.ProviderReplacementAdmissionLineageInherited -> "admission-inherited"
  Kernel.ProviderReplacementSharedEvidenceWithoutScope -> "shared-evidence-unscoped"
  Kernel.ProviderReplacementUnexpectedEvidenceReuse -> "unexpected-reuse"

reuseTag :: Kernel.ProviderReplacementReuseDecision -> String
reuseTag result = case result of
  Kernel.ProviderReplacementReuseAccepted -> "reuse-accepted"
  Kernel.ProviderReplacementReuseReferenceMismatch -> "reference-mismatch"
  Kernel.ProviderReplacementReusePriorClaimMismatch -> "prior-claim-mismatch"
  Kernel.ProviderReplacementReuseNewClaimMismatch -> "new-claim-mismatch"
  Kernel.ProviderReplacementReuseScopeMissing -> "scope-missing"
