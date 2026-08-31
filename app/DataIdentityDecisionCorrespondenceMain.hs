module Main (main) where

import DataIdentityKernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "resolved nominal identity match accepts" $
        isIdentityAccepted (decideDataIdentityByFact True)
    , test "resolved nominal identity mismatch rejects" $
        isIdentityRejected (decideDataIdentityByFact False)
    , test "explicit operation grant accepts" $
        isOperationAccepted (decideDataOperationByFact True)
    , test "missing operation grant rejects" $
        isOperationRejected (decideDataOperationByFact False)
    , test "identity match cannot manufacture operation" $
        isOperationRejected (decideDataOperationAfterIdentityByFacts True False)
    , test "identity mismatch does not erase explicit operation grant" $
        isOperationAccepted (decideDataOperationAfterIdentityByFacts False True)
    , test "operation decision ignores identity fact when granted" $
        sameOperationClass
          (decideDataOperationAfterIdentityByFacts True True)
          (decideDataOperationAfterIdentityByFacts False True)
    , test "operation decision ignores identity fact when ungranted" $
        sameOperationClass
          (decideDataOperationAfterIdentityByFacts True False)
          (decideDataOperationAfterIdentityByFacts False False)
    ]
  if and results then pure () else exitFailure

isIdentityAccepted :: DataIdentityDecision -> Bool
isIdentityAccepted decision = case decision of
  DataIdentityAccepted -> True
  DataIdentityRejected -> False

isIdentityRejected :: DataIdentityDecision -> Bool
isIdentityRejected = not . isIdentityAccepted

isOperationAccepted :: DataOperationDecision -> Bool
isOperationAccepted decision = case decision of
  DataOperationAccepted -> True
  DataOperationRejected -> False

isOperationRejected :: DataOperationDecision -> Bool
isOperationRejected = not . isOperationAccepted

sameOperationClass :: DataOperationDecision -> DataOperationDecision -> Bool
sameOperationClass left right = case (left, right) of
  (DataOperationAccepted, DataOperationAccepted) -> True
  (DataOperationRejected, DataOperationRejected) -> True
  _ -> False

test :: String -> Bool -> IO Bool
test label ok = do
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> label)
  pure ok
