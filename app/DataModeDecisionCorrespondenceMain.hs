module Main (main) where

import DataModeKernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-MODE empty record derives unrestricted"
        (sameMode Unrestricted (deriveRecordMode []))
    , test "DATA-MODE record derives strongest affine mode"
        (sameMode Affine (deriveRecordMode [Unrestricted, Affine]))
    , test "DATA-MODE record derives strongest linear mode"
        (sameMode Linear (deriveRecordMode [Affine, Linear]))
    , test "DATA-MODE sum conservatively includes all constructor payloads"
        (sameMode Linear (deriveSumMode [[Unrestricted], [Affine, Linear]]))
    , test "DATA-MODE exact record candidate accepts"
        (isAggregateAccepted
          (decideRecordModeByCandidate [Unrestricted, Affine] Affine))
    , test "DATA-MODE wrong record candidate rejects"
        (isAggregateMismatch
          (decideRecordModeByCandidate [Unrestricted, Affine] Unrestricted))
    , test "DATA-MODE exact sum candidate accepts"
        (isAggregateAccepted
          (decideSumModeByCandidate [[Unrestricted], [Affine]] Affine))
    , test "DATA-MODE resolved generic actual preserves strongest mode"
        (isJustMode Linear
          (resolvedStrongestMode [Just Unrestricted, Just Linear]))
    , test "DATA-MODE unresolved generic actual fails closed"
        (isNothingMode
          (resolvedStrongestMode [Just Unrestricted, Nothing, Just Linear]))
    , test "DATA-MODE omitted nominal declaration keeps derived mode"
        (isNominalAccepted Affine
          (decideNominalModeByFact Affine Nothing False))
    , test "DATA-MODE equal nominal declaration needs no strengthening fact"
        (isNominalAccepted Linear
          (decideNominalModeByFact Linear (Just Linear) False))
    , test "DATA-MODE nominal weakening rejects"
        (isNominalWeakening
          (decideNominalModeByFact Affine (Just Unrestricted) True))
    , test "DATA-MODE strict strengthening without admitted fact rejects"
        (isNominalJustification
          (decideNominalModeByFact Unrestricted (Just Affine) False))
    , test "DATA-MODE justified strict strengthening accepts"
        (isNominalAccepted Linear
          (decideNominalModeByFact Unrestricted (Just Linear) True))
    , test "DATA-MODE unique restricted occurrences accept"
        (isFormationAccepted (decideAggregateFormationByFact True))
    , test "DATA-MODE duplicate restricted occurrence rejects"
        (isFormationDuplicate (decideAggregateFormationByFact False))
    ]
  if and results then pure () else exitFailure

test :: String -> Bool -> IO Bool
test label condition = do
  putStrLn ((if condition then "PASS: " else "FAIL: ") <> label)
  pure condition

sameMode :: Mode -> Mode -> Bool
sameMode left right = case (left, right) of
  (Unrestricted, Unrestricted) -> True
  (Affine, Affine) -> True
  (Linear, Linear) -> True
  _ -> False

isJustMode :: Mode -> Maybe Mode -> Bool
isJustMode expected actual = case actual of
  Just mode -> sameMode expected mode
  Nothing -> False

isNothingMode :: Maybe Mode -> Bool
isNothingMode actual = case actual of
  Nothing -> True
  Just _ -> False

isAggregateAccepted :: AggregateModeDecision -> Bool
isAggregateAccepted decision = case decision of
  AggregateModeAcceptedDecision -> True
  AggregateModeMismatchDecision -> False

isAggregateMismatch :: AggregateModeDecision -> Bool
isAggregateMismatch decision = case decision of
  AggregateModeMismatchDecision -> True
  AggregateModeAcceptedDecision -> False

isNominalAccepted :: Mode -> NominalModeDecision -> Bool
isNominalAccepted expected decision = case decision of
  NominalModeAcceptedDecision actual -> sameMode expected actual
  _ -> False

isNominalWeakening :: NominalModeDecision -> Bool
isNominalWeakening decision = case decision of
  NominalModeWeakeningDecision -> True
  _ -> False

isNominalJustification :: NominalModeDecision -> Bool
isNominalJustification decision = case decision of
  NominalModeJustificationDecision -> True
  _ -> False

isFormationAccepted :: AggregateFormationDecision -> Bool
isFormationAccepted decision = case decision of
  AggregateFormationAcceptedDecision -> True
  AggregateFormationDuplicateRestrictedDecision -> False

isFormationDuplicate :: AggregateFormationDecision -> Bool
isFormationDuplicate decision = case decision of
  AggregateFormationDuplicateRestrictedDecision -> True
  AggregateFormationAcceptedDecision -> False
