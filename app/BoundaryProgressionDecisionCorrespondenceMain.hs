module Main (main) where

import BoundaryProgressionKernel

assert :: String -> Bool -> IO ()
assert label ok =
  if ok then pure () else error ("boundary progression correspondence failed: " ++ label)

isReceiveAccepted :: ReceiveProgressionDecision -> Bool
isReceiveAccepted ReceiveProgressionDecisionAccepted = True
isReceiveAccepted _ = False

isReceiveGrammarMismatch :: ReceiveProgressionDecision -> Bool
isReceiveGrammarMismatch ReceiveMappingGrammarMismatchDecision = True
isReceiveGrammarMismatch _ = False

isReceiveValueMismatch :: ReceiveProgressionDecision -> Bool
isReceiveValueMismatch ReceiveMappingValueMismatchDecision = True
isReceiveValueMismatch _ = False

isUnderlyingReceiveRejected :: ReceiveProgressionDecision -> Bool
isUnderlyingReceiveRejected UnderlyingReceiveRejectedDecision = True
isUnderlyingReceiveRejected _ = False

isInvalidEmission :: CompleteEmissionDecision -> Bool
isInvalidEmission InvalidEmissionExtentDecision = True
isInvalidEmission _ = False

isPartialEmission :: CompleteEmissionDecision -> Bool
isPartialEmission PartialEmissionDecision = True
isPartialEmission _ = False

isCompleteEmission :: CompleteEmissionDecision -> Bool
isCompleteEmission CompleteEmissionDecisionAccepted = True
isCompleteEmission _ = False

isPastFrameEmission :: CompleteEmissionDecision -> Bool
isPastFrameEmission EmissionPastDeclaredFrameDecision = True
isPastFrameEmission _ = False

planExact :: Bool
planExact =
  case planCompleteEmission ("representation" :: String) ("owner" :: String) of
    MkCompleteEmissionPlan representation owner ->
      representation == "representation" && owner == "owner"

isSendAccepted :: SendProgressionDecision -> Bool
isSendAccepted SendProgressionDecisionAccepted = True
isSendAccepted _ = False

isSendRepresentationMismatch :: SendProgressionDecision -> Bool
isSendRepresentationMismatch SendEmissionRepresentationMismatchDecision = True
isSendRepresentationMismatch _ = False

isSendOwnerMismatch :: SendProgressionDecision -> Bool
isSendOwnerMismatch SendEmissionOwnerMismatchDecision = True
isSendOwnerMismatch _ = False

isUnderlyingSendRejected :: SendProgressionDecision -> Bool
isUnderlyingSendRejected UnderlyingSendRejectedDecision = True
isUnderlyingSendRejected _ = False

main :: IO ()
main = do
  assert "receive exact facts accept"
    (isReceiveAccepted (decideReceiveProgressionByFacts True True True))
  assert "receive grammar mismatch first"
    (isReceiveGrammarMismatch (decideReceiveProgressionByFacts False False False))
  assert "receive value mismatch second"
    (isReceiveValueMismatch (decideReceiveProgressionByFacts True False False))
  assert "underlying receive rejection last"
    (isUnderlyingReceiveRejected (decideReceiveProgressionByFacts True True False))

  assert "invalid emission rejects"
    (isInvalidEmission (decideEmissionDisposition InvalidEmissionExtent))
  assert "partial emission rejects"
    (isPartialEmission (decideEmissionDisposition PartialEmission))
  assert "complete emission accepts"
    (isCompleteEmission (decideEmissionDisposition CompleteEmission))
  assert "past declared frame rejects"
    (isPastFrameEmission (decideEmissionDisposition EmissionPastDeclaredFrame))
  assert "completion plan preserves exact identity" planExact

  assert "send exact facts accept"
    (isSendAccepted (decideSendProgressionByFacts True True True))
  assert "send representation mismatch first"
    (isSendRepresentationMismatch (decideSendProgressionByFacts False False False))
  assert "send owner mismatch second"
    (isSendOwnerMismatch (decideSendProgressionByFacts True False False))
  assert "underlying send rejection last"
    (isUnderlyingSendRejected (decideSendProgressionByFacts True True False))
