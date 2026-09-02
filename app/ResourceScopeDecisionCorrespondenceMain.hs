module Main (main) where

import ResourceScopeKernel

assert :: String -> Bool -> IO ()
assert label condition =
  if condition
    then putStrLn ("PASS: " <> label)
    else fail ("FAIL: " <> label)

main :: IO ()
main = do
  assert "RES-SCOPE scoped boundary accepts bound join with closed loans" $
    decideScopedBoundaryByFacts True True == ScopedBoundaryAcceptedDecision
  assert "RES-SCOPE scoped boundary reports Resource Join predecessor failure first" $
    decideScopedBoundaryByFacts False True == ScopedBoundaryResourceJoinDecision
  assert "RES-SCOPE scoped boundary reports lexical loan escape after join acceptance" $
    decideScopedBoundaryByFacts True False == ScopedBoundaryLexicalLoanDecision

  assert "RES-SCOPE affine state accepts explicit carrier" $
    decideAffineProjectionByFact True == AffineProjectionAcceptedDecision
  assert "RES-SCOPE affine state rejects hidden maybe-possession" $
    decideAffineProjectionByFact False == AffineProjectionExplicitCarrierDecision

  assert "RES-SCOPE branch disposition accepts exact continuing/terminal classification" $
    decideBranchDispositionByFacts True True == BranchDispositionAcceptedDecision
  assert "RES-SCOPE branch disposition rejects terminal arm projection" $
    decideBranchDispositionByFacts False True == BranchDispositionTerminalExclusionDecision
  assert "RES-SCOPE branch disposition rejects inexact continuing projection" $
    decideBranchDispositionByFacts True False == BranchDispositionContinuingExactDecision
