module Main (main) where

import Phil.Core.BoundaryDirection
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "BND-007 receive-only rejects encoding" $
        expect ReceiveOnly OutboundUse ReceiveOnlyCannotEncode
    , test "BND-007 send-only rejects inbound acceptance" $
        expect SendOnly InboundUse SendOnlyCannotAcceptInbound
    , test "BND-007 receive-only permits inbound use" $
        expectAccept ReceiveOnly InboundUse
    , test "BND-007 send-only permits outbound use" $
        expectAccept SendOnly OutboundUse
    , test "BND-007 bidirectional permits both uses" $
        expectAccept Bidirectional InboundUse >> expectAccept Bidirectional OutboundUse
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

expect :: BoundaryDirection -> BoundaryUse -> BoundaryDirectionError -> Either String ()
expect direction use expected =
  case checkBoundaryUse direction use of
    Left actual | actual == expected -> Right ()
    other -> Left ("unexpected direction result: " <> show other)

expectAccept :: BoundaryDirection -> BoundaryUse -> Either String ()
expectAccept direction use =
  case checkBoundaryUse direction use of
    Right () -> Right ()
    other -> Left ("expected direction to be admitted, got: " <> show other)
