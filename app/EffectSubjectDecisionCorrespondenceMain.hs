module Main (main) where

import Control.Monad (unless)
import EffectSubjectKernel

assert :: String -> Bool -> IO ()
assert label condition = do
  unless condition (error ("FAIL: " ++ label))
  putStrLn ("PASS: " ++ label)

isCorrespondenceAccepted :: EffectSubjectCorrespondenceDecision -> Bool
isCorrespondenceAccepted decision = case decision of
  EffectSubjectCorrespondenceAccepted -> True
  _ -> False

isCorrespondenceSourceEmpty :: EffectSubjectCorrespondenceDecision -> Bool
isCorrespondenceSourceEmpty decision = case decision of
  EffectSubjectCorrespondenceSourceEmpty -> True
  _ -> False

isCorrespondenceTargetEmpty :: EffectSubjectCorrespondenceDecision -> Bool
isCorrespondenceTargetEmpty decision = case decision of
  EffectSubjectCorrespondenceTargetEmpty -> True
  _ -> False

isCorrespondenceRevisionEmpty :: EffectSubjectCorrespondenceDecision -> Bool
isCorrespondenceRevisionEmpty decision = case decision of
  EffectSubjectCorrespondenceRevisionEmpty -> True
  _ -> False

isRetargetAcceptedSame :: EffectSubjectRetargetDecision -> Bool
isRetargetAcceptedSame decision = case decision of
  EffectSubjectRetargetAcceptedSame -> True
  _ -> False

isRetargetAcceptedCorrespondence :: EffectSubjectRetargetDecision -> Bool
isRetargetAcceptedCorrespondence decision = case decision of
  EffectSubjectRetargetAcceptedCorrespondence -> True
  _ -> False

isRetargetOutOfRange :: EffectSubjectRetargetDecision -> Bool
isRetargetOutOfRange decision = case decision of
  EffectSubjectRetargetIndexOutOfRange -> True
  _ -> False

isRetargetRequiresCorrespondence :: EffectSubjectRetargetDecision -> Bool
isRetargetRequiresCorrespondence decision = case decision of
  EffectSubjectRetargetRequiresCorrespondence -> True
  _ -> False

isRetargetSourceMismatch :: EffectSubjectRetargetDecision -> Bool
isRetargetSourceMismatch decision = case decision of
  EffectSubjectRetargetCorrespondenceSourceMismatch -> True
  _ -> False

isRetargetTargetMismatch :: EffectSubjectRetargetDecision -> Bool
isRetargetTargetMismatch decision = case decision of
  EffectSubjectRetargetCorrespondenceTargetMismatch -> True
  _ -> False

main :: IO ()
main = do
  let correspondence = decideEffectSubjectCorrespondence
      retarget = decideEffectSubjectRetarget

  assert "nonempty exact correspondence facts accept"
    (isCorrespondenceAccepted (correspondence True True True))
  assert "source nonemptiness is first correspondence gate"
    (isCorrespondenceSourceEmpty (correspondence False False False))
  assert "target nonemptiness is second correspondence gate"
    (isCorrespondenceTargetEmpty (correspondence True False False))
  assert "relation revision is final correspondence gate"
    (isCorrespondenceRevisionEmpty (correspondence True True False))

  assert "out-of-range rejects before all retarget identity facts"
    (isRetargetOutOfRange (retarget False True True True True))
  assert "same semantic subject accepts without correspondence"
    (isRetargetAcceptedSame (retarget True True False False False))
  assert "same semantic subject ignores irrelevant correspondence facts"
    (isRetargetAcceptedSame (retarget True True True False False))
  assert "changed subject without correspondence rejects"
    (isRetargetRequiresCorrespondence (retarget True False False False False))
  assert "changed subject correspondence must name exact source"
    (isRetargetSourceMismatch (retarget True False True False False))
  assert "changed subject correspondence must name exact target"
    (isRetargetTargetMismatch (retarget True False True True False))
  assert "changed subject with exact correspondence accepts"
    (isRetargetAcceptedCorrespondence (retarget True False True True True))
