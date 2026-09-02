module Main where

import qualified SystemsStageClosureKernel as Kernel
import System.Exit (exitFailure)

assert :: String -> Bool -> IO ()
assert label condition =
  if condition
    then putStrLn ("PASS: " <> label)
    else do
      putStrLn ("FAIL: " <> label)
      exitFailure

sourceTag :: Kernel.SourceClosureDecision -> String
sourceTag decision = case decision of
  Kernel.SourceClosureAcceptedDecision -> "accepted"
  Kernel.SourceClosureCoverageDecision -> "coverage"
  Kernel.SourceClosureEmptyFactDecision -> "empty-fact"
  Kernel.SourceClosureDispositionDecision -> "disposition"

targetTag :: Kernel.TargetClosureDecision -> String
targetTag decision = case decision of
  Kernel.TargetClosureAcceptedDecision -> "accepted"
  Kernel.TargetClosureCoverageDecision -> "coverage"
  Kernel.TargetClosureEmptyMechanismDecision -> "empty-mechanism"
  Kernel.TargetClosureJustificationDecision -> "justification"

identityTag :: Kernel.StageIdentityDecision -> String
identityTag decision = case decision of
  Kernel.StageIdentityAcceptedDecision -> "accepted"
  Kernel.StageIdentitySubjectDecision -> "subject"
  Kernel.StageIdentityInstanceDecision -> "instance"
  Kernel.StageIdentityRealizationDecision -> "realization"
  Kernel.StageIdentitySystemsDecision -> "systems"
  Kernel.StageIdentityContractDecision -> "contract"
  Kernel.StageIdentityProfileDecision -> "profile"
  Kernel.StageIdentityRecomputedSystemsDecision -> "recomputed-systems"
  Kernel.StageIdentityRecomputedFinalDecision -> "recomputed-final"
  Kernel.StageIdentityStoredSystemsDecision -> "stored-systems"
  Kernel.StageIdentityStoredFinalDecision -> "stored-final"

closureTag :: Kernel.SystemsStageClosureDecision -> String
closureTag decision = case decision of
  Kernel.SystemsStageClosureAcceptedDecision -> "accepted"
  Kernel.SystemsStageClosureFactDecision -> "fact"
  Kernel.SystemsStageClosureProjectionDecision -> "projection"
  Kernel.SystemsStageClosureSourceDecision -> "source"
  Kernel.SystemsStageClosureTargetDecision -> "target"
  Kernel.SystemsStageClosureScopeDecision -> "scope"
  Kernel.SystemsStageClosureIdentityDecision -> "identity"

checkSource :: String -> String -> Bool -> Bool -> Bool -> IO ()
checkSource label expected a b c =
  assert label (sourceTag (Kernel.decideSourceClosureByFacts a b c) == expected)

checkTarget :: String -> String -> Bool -> Bool -> Bool -> IO ()
checkTarget label expected a b c =
  assert label (targetTag (Kernel.decideTargetClosureByFacts a b c) == expected)

checkIdentity
  :: String -> String
  -> Bool -> Bool -> Bool -> Bool -> Bool
  -> Bool -> Bool -> Bool -> Bool -> Bool
  -> IO ()
checkIdentity label expected a b c d e f g h i j =
  assert label
    (identityTag (Kernel.decideStageIdentityByFacts a b c d e f g h i j)
      == expected)

checkClosure
  :: String -> String
  -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
  -> IO ()
checkClosure label expected a b c d e f =
  assert label
    (closureTag (Kernel.decideSystemsStageClosureByFacts a b c d e f)
      == expected)

main :: IO ()
main = do
  checkSource "stage source closure accepts exact facts" "accepted" True True True
  checkSource "stage source closure requires exact coverage" "coverage" False True True
  checkSource "stage source closure rejects empty fact identity" "empty-fact" True False True
  checkSource "stage source closure requires permitted dispositions" "disposition" True True False

  checkTarget "stage target closure accepts exact facts" "accepted" True True True
  checkTarget "stage target closure requires exact coverage" "coverage" False True True
  checkTarget "stage target closure rejects empty mechanism identity" "empty-mechanism" True False True
  checkTarget "stage target closure requires valid justification" "justification" True True False

  checkIdentity "stage identity accepts exact common trunk" "accepted"
    True True True True True True True True True True
  checkIdentity "stage identity requires exact subject" "subject"
    False True True True True True True True True True
  checkIdentity "stage identity requires exact instance" "instance"
    True False True True True True True True True True
  checkIdentity "stage identity requires exact realization" "realization"
    True True False True True True True True True True
  checkIdentity "stage identity requires exact systems revision" "systems"
    True True True False True True True True True True
  checkIdentity "stage identity requires exact coarse contract" "contract"
    True True True True False True True True True True
  checkIdentity "stage identity requires exact verifier profile" "profile"
    True True True True True False True True True True
  checkIdentity "stage identity requires recomputed systems revision" "recomputed-systems"
    True True True True True True False True True True
  checkIdentity "stage identity requires recomputed final revision" "recomputed-final"
    True True True True True True True False True True
  checkIdentity "stage identity requires stored systems revision" "stored-systems"
    True True True True True True True True False True
  checkIdentity "stage identity requires stored final revision" "stored-final"
    True True True True True True True True True False

  checkClosure "cumulative stage closure accepts all Certified relations" "accepted"
    True True True True True True
  checkClosure "cumulative stage closure requires Certified facts" "fact"
    False True True True True True
  checkClosure "cumulative stage closure requires exact fact projection" "projection"
    True False True True True True
  checkClosure "cumulative stage closure requires source closure" "source"
    True True False True True True
  checkClosure "cumulative stage closure requires target closure" "target"
    True True True False True True
  checkClosure "cumulative stage closure requires validity scope" "scope"
    True True True True False True
  checkClosure "cumulative stage closure requires final identity" "identity"
    True True True True True False
