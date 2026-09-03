module Main (main) where

import DataEliminationKernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-ELIM linear field bound accepts" $
        fieldAccepted (decideFieldDispositionByMode Linear (Just FieldBound))
    , test "DATA-ELIM linear field omission rejects" $
        fieldLinearRequired (decideFieldDispositionByMode Linear (Just FieldOmitted))
    , test "DATA-ELIM missing linear disposition rejects" $
        fieldLinearRequired (decideFieldDispositionByMode Linear Nothing)
    , test "DATA-ELIM affine field bound accepts" $
        fieldAccepted (decideFieldDispositionByMode Affine (Just FieldBound))
    , test "DATA-ELIM affine field omission accepts" $
        fieldAccepted (decideFieldDispositionByMode Affine (Just FieldOmitted))
    , test "DATA-ELIM omitted affine disposition accepts" $
        fieldAccepted (decideFieldDispositionByMode Affine Nothing)
    , test "DATA-ELIM unrestricted omission accepts" $
        fieldAccepted (decideFieldDispositionByMode Unrestricted Nothing)
    , test "DATA-ELIM valid distinct plan accepts" $
        planAccepted (decideEliminationPlanByFacts True True)
    , test "DATA-ELIM invalid field disposition rejects plan" $
        planFieldRejected (decideEliminationPlanByFacts False True)
    , test "DATA-ELIM duplicate disposition rejects plan" $
        planDuplicateRejected (decideEliminationPlanByFacts True False)
    , test "DATA-ELIM whole aggregate disposition accepts" $
        aggregateAccepted (decideAggregateDispositionKind WholeAggregateKind)
    , test "DATA-ELIM explicit typed remainder kind accepts" $
        aggregateAccepted (decideAggregateDispositionKind ExplicitTypedRemainderKind)
    , test "DATA-ELIM implicit partial remainder rejects" $
        aggregateImplicitRejected (decideAggregateDispositionKind ImplicitPartialRemainderKind)
    , test "DATA-ELIM exact consuming transfer accepts" $
        consumingAccepted (decideConsumingEliminationByFacts True True True)
    , test "DATA-ELIM unconsumed aggregate rejects" $
        consumingAggregateRejected (decideConsumingEliminationByFacts False True True)
    , test "DATA-ELIM inexact successor restoration rejects" $
        consumingSuccessorRejected (decideConsumingEliminationByFacts True False True)
    , test "DATA-ELIM duplicate successor rejects" $
        consumingDuplicateRejected (decideConsumingEliminationByFacts True True False)
    , test "DATA-ELIM complete borrow lifecycle accepts" $
        borrowAccepted (decideBorrowLifecycleByFacts True True True True True)
    , test "DATA-ELIM undeclared field borrow rejects" $
        borrowFieldRejected (decideBorrowLifecycleByFacts False True True True True)
    , test "DATA-ELIM failed loan start rejects" $
        borrowStartRejected (decideBorrowLifecycleByFacts True False True True True)
    , test "DATA-ELIM movable borrowed owner rejects" $
        borrowMovementRejected (decideBorrowLifecycleByFacts True True False True True)
    , test "DATA-ELIM escaping live borrow rejects" $
        borrowBoundaryRejected (decideBorrowLifecycleByFacts True True True False True)
    , test "DATA-ELIM failed owner-preserving loan end rejects" $
        borrowEndRejected (decideBorrowLifecycleByFacts True True True True False)
    ]
  if and results then pure () else exitFailure

test :: String -> Bool -> IO Bool
test label condition = do
  putStrLn ((if condition then "PASS: " else "FAIL: ") <> label)
  pure condition

fieldAccepted :: FieldDispositionDecision -> Bool
fieldAccepted decision = case decision of
  FieldDispositionAcceptedDecision -> True
  _ -> False

fieldLinearRequired :: FieldDispositionDecision -> Bool
fieldLinearRequired decision = case decision of
  FieldDispositionLinearRequiredDecision -> True
  _ -> False

planAccepted :: EliminationPlanDecision -> Bool
planAccepted decision = case decision of
  EliminationPlanAcceptedDecision -> True
  _ -> False

planFieldRejected :: EliminationPlanDecision -> Bool
planFieldRejected decision = case decision of
  EliminationPlanFieldDispositionDecision -> True
  _ -> False

planDuplicateRejected :: EliminationPlanDecision -> Bool
planDuplicateRejected decision = case decision of
  EliminationPlanDuplicateDispositionDecision -> True
  _ -> False

aggregateAccepted :: AggregateDispositionDecision -> Bool
aggregateAccepted decision = case decision of
  AggregateDispositionAcceptedDecision -> True
  _ -> False

aggregateImplicitRejected :: AggregateDispositionDecision -> Bool
aggregateImplicitRejected decision = case decision of
  AggregateDispositionImplicitRemainderDecision -> True
  _ -> False

consumingAccepted :: ConsumingEliminationDecision -> Bool
consumingAccepted decision = case decision of
  ConsumingEliminationAcceptedDecision -> True
  _ -> False

consumingAggregateRejected :: ConsumingEliminationDecision -> Bool
consumingAggregateRejected decision = case decision of
  ConsumingEliminationAggregateDecision -> True
  _ -> False

consumingSuccessorRejected :: ConsumingEliminationDecision -> Bool
consumingSuccessorRejected decision = case decision of
  ConsumingEliminationSuccessorDecision -> True
  _ -> False

consumingDuplicateRejected :: ConsumingEliminationDecision -> Bool
consumingDuplicateRejected decision = case decision of
  ConsumingEliminationDuplicateSuccessorDecision -> True
  _ -> False

borrowAccepted :: BorrowLifecycleDecision -> Bool
borrowAccepted decision = case decision of
  BorrowLifecycleAcceptedDecision -> True
  _ -> False

borrowFieldRejected :: BorrowLifecycleDecision -> Bool
borrowFieldRejected decision = case decision of
  BorrowLifecycleFieldDecision -> True
  _ -> False

borrowStartRejected :: BorrowLifecycleDecision -> Bool
borrowStartRejected decision = case decision of
  BorrowLifecycleStartDecision -> True
  _ -> False

borrowMovementRejected :: BorrowLifecycleDecision -> Bool
borrowMovementRejected decision = case decision of
  BorrowLifecycleMovementDecision -> True
  _ -> False

borrowBoundaryRejected :: BorrowLifecycleDecision -> Bool
borrowBoundaryRejected decision = case decision of
  BorrowLifecycleBoundaryDecision -> True
  _ -> False

borrowEndRejected :: BorrowLifecycleDecision -> Bool
borrowEndRejected decision = case decision of
  BorrowLifecycleEndDecision -> True
  _ -> False
