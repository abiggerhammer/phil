module Main (main) where

import Phil.Core.DataOperationContract
  ( DataOperation (..)
  , emptyOperationContract
  , grantOperation
  , permitsOperation
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  let automaticOperations =
        [ Equality
        , Ordering
        , Hashing
        , Clone
        , Default
        , Serialization
        , Deserialization
        , MemcpySafety
        , ABICompatibility
        ]
      noAutomaticPrivileges = all (not . permitsOperation emptyOperationContract) automaticOperations
      equalityContract = grantOperation Equality emptyOperationContract
      serializationContract = grantOperation Serialization emptyOperationContract
      explicitEqualityOnly =
        permitsOperation equalityContract Equality
          && not (permitsOperation equalityContract Hashing)
          && not (permitsOperation equalityContract Serialization)
      explicitSerializationOnly =
        permitsOperation serializationContract Serialization
          && not (permitsOperation serializationContract Equality)
          && not (permitsOperation serializationContract ABICompatibility)
      results =
        [ ("DATA-011 shape grants no automatic semantic/representation operations", noAutomaticPrivileges)
        , ("DATA-011 explicit equality contract grants equality only", explicitEqualityOnly)
        , ("DATA-011 explicit serialization contract does not imply equality or ABI", explicitSerializationOnly)
        ]
  mapM_ report results
  if all snd results then pure () else exitFailure

report :: (String, Bool) -> IO ()
report (label, ok) = putStrLn ((if ok then "PASS: " else "FAIL: ") <> label)
