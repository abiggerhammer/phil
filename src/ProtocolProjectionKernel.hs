module ProtocolProjectionKernel where

import qualified Prelude

data DeclaredProjectionRoleDecision =
   DeclaredProjectionRoleAccepted
 | UndeclaredProjectionRoleRejected

decideDeclaredProjectionRoleByFact :: Prelude.Bool ->
                                      DeclaredProjectionRoleDecision
decideDeclaredProjectionRoleByFact roleDeclared =
  case roleDeclared of {
   Prelude.True -> DeclaredProjectionRoleAccepted;
   Prelude.False -> UndeclaredProjectionRoleRejected}

data ProjectionInstanceDecision =
   ProjectionInstanceAccepted
 | ProjectionInstanceMismatchDecision

decideProjectionInstanceByFact :: Prelude.Bool -> ProjectionInstanceDecision
decideProjectionInstanceByFact instanceMatches =
  case instanceMatches of {
   Prelude.True -> ProjectionInstanceAccepted;
   Prelude.False -> ProjectionInstanceMismatchDecision}

data ProjectionSessionDecision =
   ProjectionSessionAccepted
 | ProjectionSessionMismatchDecision

decideProjectionSessionByFact :: Prelude.Bool -> ProjectionSessionDecision
decideProjectionSessionByFact sessionMatches =
  case sessionMatches of {
   Prelude.True -> ProjectionSessionAccepted;
   Prelude.False -> ProjectionSessionMismatchDecision}

data ProtocolProjectionPlan instanceType roleKeyType sessionType =
   MkProtocolProjectionPlan instanceType roleKeyType sessionType

planProtocolProjection :: a1 -> a2 -> a3 -> ProtocolProjectionPlan a1 a2 a3
planProtocolProjection instanceRevision roleKey localSession =
  MkProtocolProjectionPlan instanceRevision roleKey localSession

data TransferredProtocolContractPlan instanceType roleKeyType sessionType =
   MkTransferredProtocolContractPlan instanceType roleKeyType sessionType

planTransferredProtocolContract :: a1 -> a2 -> a3 ->
                                   TransferredProtocolContractPlan a1 
                                   a2 a3
planTransferredProtocolContract instanceRevision roleKey localSession =
  MkTransferredProtocolContractPlan instanceRevision roleKey localSession
