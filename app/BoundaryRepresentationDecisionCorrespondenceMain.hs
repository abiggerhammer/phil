module Main (main) where

import BoundaryRepresentationKernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "all exact mapping facts accept"
        (assertMappingAccepted
          (decideBoundaryMappingByFacts True True True True True True))
    , test "representation mismatch rejects first"
        (assertRepresentationMismatch
          (decideBoundaryMappingByFacts False False False False False False))
    , test "grammar mismatch follows representation"
        (assertGrammarMismatch
          (decideBoundaryMappingByFacts True False False False False False))
    , test "value-type mismatch follows grammar"
        (assertValueTypeMismatch
          (decideBoundaryMappingByFacts True True False False False False))
    , test "recognized grammar mismatch follows representation identities"
        (assertRecognizedGrammarMismatch
          (decideBoundaryMappingByFacts True True True False False False))
    , test "recognized value mismatch follows recognized grammar"
        (assertRecognizedValueMismatch
          (decideBoundaryMappingByFacts True True True True False False))
    , test "explicit mapping rejection is last"
        (assertMappingRejected
          (decideBoundaryMappingByFacts True True True True True False))
    , test "correspondence plan preserves exact source and target coordinates"
        assertExactCorrespondencePlan
    , test "receive-only accepts inbound use"
        (assertBoundaryUseAccepted
          (decideBoundaryUse ReceiveOnly InboundUse))
    , test "receive-only rejects outbound encoding"
        (assertReceiveOnlyCannotEncode
          (decideBoundaryUse ReceiveOnly OutboundUse))
    , test "send-only rejects inbound use"
        (assertSendOnlyCannotAcceptInbound
          (decideBoundaryUse SendOnly InboundUse))
    , test "send-only accepts outbound use"
        (assertBoundaryUseAccepted
          (decideBoundaryUse SendOnly OutboundUse))
    , test "bidirectional accepts inbound use"
        (assertBoundaryUseAccepted
          (decideBoundaryUse Bidirectional InboundUse))
    , test "bidirectional accepts outbound use"
        (assertBoundaryUseAccepted
          (decideBoundaryUse Bidirectional OutboundUse))
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

assertMappingAccepted :: BoundaryMappingDecision -> Either String ()
assertMappingAccepted decision = case decision of
  BoundaryMappingDecisionAccepted -> Right ()
  _ -> Left "expected BoundaryMappingDecisionAccepted"

assertRepresentationMismatch :: BoundaryMappingDecision -> Either String ()
assertRepresentationMismatch decision = case decision of
  BoundaryRepresentationMismatchDecision -> Right ()
  _ -> Left "expected BoundaryRepresentationMismatchDecision"

assertGrammarMismatch :: BoundaryMappingDecision -> Either String ()
assertGrammarMismatch decision = case decision of
  BoundaryGrammarMismatchDecision -> Right ()
  _ -> Left "expected BoundaryGrammarMismatchDecision"

assertValueTypeMismatch :: BoundaryMappingDecision -> Either String ()
assertValueTypeMismatch decision = case decision of
  BoundaryValueTypeMismatchDecision -> Right ()
  _ -> Left "expected BoundaryValueTypeMismatchDecision"

assertRecognizedGrammarMismatch :: BoundaryMappingDecision -> Either String ()
assertRecognizedGrammarMismatch decision = case decision of
  RecognizedGrammarMismatchDecision -> Right ()
  _ -> Left "expected RecognizedGrammarMismatchDecision"

assertRecognizedValueMismatch :: BoundaryMappingDecision -> Either String ()
assertRecognizedValueMismatch decision = case decision of
  RecognizedValueMismatchDecision -> Right ()
  _ -> Left "expected RecognizedValueMismatchDecision"

assertMappingRejected :: BoundaryMappingDecision -> Either String ()
assertMappingRejected decision = case decision of
  BoundaryMappingRejectedDecision -> Right ()
  _ -> Left "expected BoundaryMappingRejectedDecision"

assertExactCorrespondencePlan :: Either String ()
assertExactCorrespondencePlan =
  case planBoundaryCorrespondence
        "representation" "grammar" "value-type" "recognized-source" "semantic-target" of
    MkBoundaryCorrespondencePlan representation grammar valueType source target
      | representation == "representation"
      , grammar == "grammar"
      , valueType == "value-type"
      , source == "recognized-source"
      , target == "semantic-target"
      , source /= target -> Right ()
      | otherwise -> Left "correspondence plan changed an exact coordinate"

assertBoundaryUseAccepted :: BoundaryDirectionResult -> Either String ()
assertBoundaryUseAccepted result = case result of
  BoundaryUseAccepted -> Right ()
  _ -> Left "expected BoundaryUseAccepted"

assertReceiveOnlyCannotEncode :: BoundaryDirectionResult -> Either String ()
assertReceiveOnlyCannotEncode result = case result of
  BoundaryUseRejected ReceiveOnlyCannotEncode -> Right ()
  _ -> Left "expected ReceiveOnlyCannotEncode"

assertSendOnlyCannotAcceptInbound :: BoundaryDirectionResult -> Either String ()
assertSendOnlyCannotAcceptInbound result = case result of
  BoundaryUseRejected SendOnlyCannotAcceptInbound -> Right ()
  _ -> Left "expected SendOnlyCannotAcceptInbound"
