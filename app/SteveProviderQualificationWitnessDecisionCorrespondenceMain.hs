module Main (main) where

import SteveProviderQualificationWitnessKernel
  ( decideSteveProviderQualificationWitnessByFacts
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  let controls =
        [ ("Steve provider witness accepts all eleven exact facts", facts True [])
        , ("Steve provider witness rejects provider admission drift", facts False [0])
        , ("Steve provider witness rejects digest subject drift", facts False [1])
        , ("Steve provider witness rejects digest observation mapping drift", facts False [2])
        , ("Steve provider witness rejects digest borrow drift", facts False [3])
        , ("Steve provider witness rejects Blob outcome-borrow drift", facts False [4])
        , ("Steve provider witness rejects Blob layer drift", facts False [5])
        , ("Steve provider witness rejects no-replace drift", facts False [6])
        , ("Steve provider witness rejects partial-publication drift", facts False [7])
        , ("Steve provider witness rejects authority-disposition drift", facts False [8])
        , ("Steve provider witness rejects obligation-manifest drift", facts False [9])
        , ("Steve provider witness rejects condition-lineage drift", facts False [10])
        ]
  results <- mapM (uncurry test) controls
  if and results then pure () else exitFailure

facts :: Bool -> [Int] -> Bool
facts expectedFalse falseIndexes =
  let value index = index `notElem` falseIndexes
      actual = decideSteveProviderQualificationWitnessByFacts
        (value 0)
        (value 1)
        (value 2)
        (value 3)
        (value 4)
        (value 5)
        (value 6)
        (value 7)
        (value 8)
        (value 9)
        (value 10)
  in if null falseIndexes then actual else actual == expectedFalse

test :: String -> Bool -> IO Bool
test label condition = do
  putStrLn ((if condition then "PASS: " else "FAIL: ") <> label)
  pure condition
