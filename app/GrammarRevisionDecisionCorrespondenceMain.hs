module Main (main) where

import GrammarRevisionKernel (decideGrammarRevisionBindingByFacts)
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ control "grammar revision accepts competent exact payload-independent binding"
        True True True True
    , control "grammar revision rejects missing/duplicate/malformed competence"
        False True True False
    , control "grammar revision rejects incompatible selected revision"
        True False True False
    , control "grammar revision rejects injected payload-rebinding disagreement"
        True True False False
    ]
  if and results then pure () else exitFailure

control :: String -> Bool -> Bool -> Bool -> Bool -> IO Bool
control label competentPresent exactSelectedRevision payloadIndependent expected = do
  let actual = decideGrammarRevisionBindingByFacts
        competentPresent exactSelectedRevision payloadIndependent
  if actual == expected
    then putStrLn ("PASS: " <> label) >> pure True
    else do
      putStrLn
        ("FAIL: " <> label
          <> " -- expected " <> show expected
          <> ", got " <> show actual)
      pure False
