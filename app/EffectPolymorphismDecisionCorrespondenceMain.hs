module Main (main) where

import Control.Monad (unless)
import EffectPolymorphismKernel

assert :: String -> Bool -> IO ()
assert label condition = do
  unless condition (error ("FAIL: " ++ label))
  putStrLn ("PASS: " ++ label)

isAccepted :: EffectSetInstantiationDecision -> Bool
isAccepted decision = case decision of
  EffectSetInstantiationAccepted -> True
  _ -> False

isParameterKeyMismatch :: EffectSetInstantiationDecision -> Bool
isParameterKeyMismatch decision = case decision of
  EffectSetInstantiationParameterKeyMismatch -> True
  _ -> False

isKindMismatch :: EffectSetInstantiationDecision -> Bool
isKindMismatch decision = case decision of
  EffectSetInstantiationKindMismatch -> True
  _ -> False

isSemanticFormMalformed :: EffectSetInstantiationDecision -> Bool
isSemanticFormMalformed decision = case decision of
  EffectSetInstantiationSemanticFormMalformed -> True
  _ -> False

isBoundExceeded :: EffectSetInstantiationDecision -> Bool
isBoundExceeded decision = case decision of
  EffectSetInstantiationBoundExceeded -> True
  _ -> False

main :: IO ()
main = do
  let decide = decideEffectSetInstantiation

  assert "parameter identity is first gate"
    (isParameterKeyMismatch (decide False False False False))
  assert "Effects kind is second gate"
    (isKindMismatch (decide True False False False))
  assert "canonical finite-set decode is third gate"
    (isSemanticFormMalformed (decide True True False False))
  assert "subset bound is final rejection gate"
    (isBoundExceeded (decide True True True False))
  assert "exact or narrower canonical Effects set accepts"
    (isAccepted (decide True True True True))
