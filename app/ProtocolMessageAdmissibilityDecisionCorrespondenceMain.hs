module Main (main) where

import ProtocolMessageAdmissibilityKernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ check "exact reflected contract facts accept"
        (isContractAccepted (decideBoundaryMessageContractByFacts True True True True True))
    , check "empty revision wins precedence"
        (isRevisionEmpty (decideBoundaryMessageContractByFacts False False False False False))
    , check "type mismatch is second"
        (isTypeMismatch (decideBoundaryMessageContractByFacts True False False False False))
    , check "semantic mismatch is third"
        (isSemanticsMismatch (decideBoundaryMessageContractByFacts True True False False False))
    , check "shape rejection is fourth"
        (isShapeRejected (decideBoundaryMessageContractByFacts True True True False False))
    , check "hard type rejection is last"
        (isHardTypeRejected (decideBoundaryMessageContractByFacts True True True True False))
    , check "intrinsic concrete fact accepts"
        (isIntrinsicAccepted (decideIntrinsicBoundaryMessageByFact True))
    , check "non-intrinsic concrete fact requires contract"
        (isIntrinsicRequiresContract (decideIntrinsicBoundaryMessageByFact False))
    ]
  if and results then pure () else exitFailure

check :: String -> Bool -> IO Bool
check label ok = do
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> label)
  pure ok

isContractAccepted :: BoundaryMessageContractDecision -> Bool
isContractAccepted value = case value of
  BoundaryMessageContractAcceptedDecision -> True
  _ -> False

isRevisionEmpty :: BoundaryMessageContractDecision -> Bool
isRevisionEmpty value = case value of
  BoundaryMessageRevisionEmptyDecision -> True
  _ -> False

isTypeMismatch :: BoundaryMessageContractDecision -> Bool
isTypeMismatch value = case value of
  BoundaryMessageTypeMismatchDecision -> True
  _ -> False

isSemanticsMismatch :: BoundaryMessageContractDecision -> Bool
isSemanticsMismatch value = case value of
  BoundaryMessageSemanticsMismatchDecision -> True
  _ -> False

isShapeRejected :: BoundaryMessageContractDecision -> Bool
isShapeRejected value = case value of
  BoundaryMessageShapeRejectedDecision -> True
  _ -> False

isHardTypeRejected :: BoundaryMessageContractDecision -> Bool
isHardTypeRejected value = case value of
  BoundaryMessageHardTypeRejectedDecision -> True
  _ -> False

isIntrinsicAccepted :: IntrinsicBoundaryMessageDecision -> Bool
isIntrinsicAccepted value = case value of
  IntrinsicBoundaryMessageAcceptedDecision -> True
  _ -> False

isIntrinsicRequiresContract :: IntrinsicBoundaryMessageDecision -> Bool
isIntrinsicRequiresContract value = case value of
  IntrinsicBoundaryMessageRequiresContractDecision -> True
  _ -> False
