module Main (main) where

import CheckedBindingModeKernel (decideCheckedBindingModeByFacts)
import System.Exit (exitFailure)

main :: IO ()
main = do
  let controls =
        [ ("checked binding mode accepts exact successful facts",
            decideCheckedBindingModeByFacts True True True)
        , ("checked binding mode rejects checked-type drift",
            not (decideCheckedBindingModeByFacts False True True))
        , ("checked binding mode rejects supplied-mode reclassification",
            not (decideCheckedBindingModeByFacts True False True))
        , ("checked binding mode rejects context insertion failure",
            not (decideCheckedBindingModeByFacts True True False))
        ]
  mapM_ report controls
  if all snd controls then pure () else exitFailure

report :: (String, Bool) -> IO ()
report (label, ok) = putStrLn ((if ok then "PASS: " else "FAIL: ") <> label)
