module Main (main) where

import Phil.Core.DataIdentity
  ( DataTypeRef (..)
  , definitionallyEqualDataType
  , resolveDataType
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-010 equal-shaped nominal declarations remain distinct"
        (not (definitionallyEqualDataType uploadId userId))
    , test "DATA-010 a nominal type equals itself"
        (definitionallyEqualDataType uploadId uploadId)
    , test "DATA-010 transparent alias equals its exact target"
        (definitionallyEqualDataType lengthAlias uint64)
    , test "DATA-010 alias chains resolve transitively"
        (definitionallyEqualDataType byteCountAlias uint64)
    , test "DATA-010 alias naming does not create nominal identity"
        (resolveDataType lengthAlias == uint64)
    ]
  if and results then pure () else exitFailure

test :: String -> Bool -> IO Bool
test label ok = do
  putStrLn ((if ok then "PASS: " else "FAIL: ") <> label)
  pure ok

uploadId :: DataTypeRef
uploadId = NominalType "UploadId"

userId :: DataTypeRef
userId = NominalType "UserId"

uint64 :: DataTypeRef
uint64 = NominalType "UInt64"

lengthAlias :: DataTypeRef
lengthAlias = TransparentAlias "Length" uint64

byteCountAlias :: DataTypeRef
byteCountAlias = TransparentAlias "ByteCount" lengthAlias
