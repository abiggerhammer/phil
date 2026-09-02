module Main (main) where

import ResourceScopeKernel

assert :: String -> Bool -> IO ()
assert label condition =
  if condition
    then putStrLn ("PASS: " <> label)
    else fail ("FAIL: " <> label)

isScopedBoundaryAccepted :: ScopedBoundaryDecision -> Bool
isScopedBoundaryAccepted decision = case decision of
  ScopedBoundaryAcceptedDecision -> True
  _ -> False

isScopedBoundaryResourceJoin :: ScopedBoundaryDecision -> Bool
isScopedBoundaryResourceJoin decision = case decision of
  ScopedBoundaryResourceJoinDecision -> True
  _ -> False

isScopedBoundaryLexicalLoan :: ScopedBoundaryDecision -> Bool
isScopedBoundaryLexicalLoan decision = case decision of
  ScopedBoundaryLexicalLoanDecision -> True
  _ -> False

isAffineProjectionAccepted :: AffineProjectionDecision -> Bool
isAffineProjectionAccepted decision = case decision of
  AffineProjectionAcceptedDecision -> True
  _ -> False

isAffineProjectionExplicitCarrier :: AffineProjectionDecision -> Bool
isAffineProjectionExplicitCarrier decision = case decision of
  AffineProjectionExplicitCarrierDecision -> True
  _ -> False

isBranchDispositionAccepted :: BranchDispositionDecision -> Bool
isBranchDispositionAccepted decision = case decision of
  BranchDispositionAcceptedDecision -> True
  _ -> False

isBranchDispositionTerminalExclusion :: BranchDispositionDecision -> Bool
isBranchDispositionTerminalExclusion decision = case decision of
  BranchDispositionTerminalExclusionDecision -> True
  _ -> False

isBranchDispositionContinuingExact :: BranchDispositionDecision -> Bool
isBranchDispositionContinuingExact decision = case decision of
  BranchDispositionContinuingExactDecision -> True
  _ -> False

main :: IO ()
main = do
  assert "RES-SCOPE scoped boundary accepts bound join with closed loans" $
    isScopedBoundaryAccepted (decideScopedBoundaryByFacts True True)
  assert "RES-SCOPE scoped boundary reports Resource Join predecessor failure first" $
    isScopedBoundaryResourceJoin (decideScopedBoundaryByFacts False True)
  assert "RES-SCOPE scoped boundary reports lexical loan escape after join acceptance" $
    isScopedBoundaryLexicalLoan (decideScopedBoundaryByFacts True False)

  assert "RES-SCOPE affine state accepts explicit carrier" $
    isAffineProjectionAccepted (decideAffineProjectionByFact True)
  assert "RES-SCOPE affine state rejects hidden maybe-possession" $
    isAffineProjectionExplicitCarrier (decideAffineProjectionByFact False)

  assert "RES-SCOPE branch disposition accepts exact continuing/terminal classification" $
    isBranchDispositionAccepted (decideBranchDispositionByFacts True True)
  assert "RES-SCOPE branch disposition rejects terminal arm projection" $
    isBranchDispositionTerminalExclusion (decideBranchDispositionByFacts False True)
  assert "RES-SCOPE branch disposition rejects inexact continuing projection" $
    isBranchDispositionContinuingExact (decideBranchDispositionByFacts True False)
