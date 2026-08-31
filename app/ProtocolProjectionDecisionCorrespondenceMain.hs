module Main (main) where

import ProtocolProjectionKernel

assert :: String -> Bool -> IO ()
assert label ok =
  if ok then pure () else error ("protocol projection correspondence failed: " ++ label)

isDeclaredRoleAccepted :: DeclaredProjectionRoleDecision -> Bool
isDeclaredRoleAccepted DeclaredProjectionRoleAccepted = True
isDeclaredRoleAccepted _ = False

isUndeclaredRoleRejected :: DeclaredProjectionRoleDecision -> Bool
isUndeclaredRoleRejected UndeclaredProjectionRoleRejected = True
isUndeclaredRoleRejected _ = False

isProjectionInstanceAccepted :: ProjectionInstanceDecision -> Bool
isProjectionInstanceAccepted ProjectionInstanceAccepted = True
isProjectionInstanceAccepted _ = False

isProjectionInstanceMismatch :: ProjectionInstanceDecision -> Bool
isProjectionInstanceMismatch ProjectionInstanceMismatchDecision = True
isProjectionInstanceMismatch _ = False

isProjectionSessionAccepted :: ProjectionSessionDecision -> Bool
isProjectionSessionAccepted ProjectionSessionAccepted = True
isProjectionSessionAccepted _ = False

isProjectionSessionMismatch :: ProjectionSessionDecision -> Bool
isProjectionSessionMismatch ProjectionSessionMismatchDecision = True
isProjectionSessionMismatch _ = False

projectionPlanExact :: Bool
projectionPlanExact =
  case planProtocolProjection (11 :: Int) (22 :: Int) (33 :: Int) of
    MkProtocolProjectionPlan instanceRevision roleKey localSession ->
      instanceRevision == 11 && roleKey == 22 && localSession == 33

transferPlanExact :: Bool
transferPlanExact =
  case planTransferredProtocolContract (11 :: Int) (22 :: Int) (33 :: Int) of
    MkTransferredProtocolContractPlan instanceRevision roleKey localSession ->
      instanceRevision == 11 && roleKey == 22 && localSession == 33

main :: IO ()
main = do
  assert "declared role accepts"
    (isDeclaredRoleAccepted (decideDeclaredProjectionRoleByFact True))
  assert "undeclared role rejects"
    (isUndeclaredRoleRejected (decideDeclaredProjectionRoleByFact False))
  assert "exact instance accepts"
    (isProjectionInstanceAccepted (decideProjectionInstanceByFact True))
  assert "mismatched instance rejects"
    (isProjectionInstanceMismatch (decideProjectionInstanceByFact False))
  assert "exact session accepts"
    (isProjectionSessionAccepted (decideProjectionSessionByFact True))
  assert "mismatched session rejects"
    (isProjectionSessionMismatch (decideProjectionSessionByFact False))
  assert "projection plan preserves exact coordinates" projectionPlanExact
  assert "transfer plan preserves exact contract" transferPlanExact
