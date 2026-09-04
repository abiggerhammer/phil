module Main (main) where

import qualified StorageRealizationKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  rejects <- mapM rejectOne (zip [0 ..] factLabels)
  accepts <- check
    "storage realization accepts all seven exact facts"
    (decision (replicate 7 True))
  if accepts && and rejects then pure () else exitFailure

check :: String -> Bool -> IO Bool
check label accepted = do
  putStrLn ((if accepted then "PASS: " else "FAIL: ") <> label)
  pure accepted

rejectOne :: (Int, String) -> IO Bool
rejectOne (index, label) =
  check ("storage realization rejects false " <> label)
    (not (decision (rejectAt index (replicate 7 True))))

rejectAt :: Int -> [Bool] -> [Bool]
rejectAt index facts =
  take index facts ++ [False] ++ drop (index + 1) facts

decision :: [Bool] -> Bool
decision
    [ subjectBasisAdmitted
    , exactSubjectPresent
    , semanticRevisionNonzero
    , outcomeRevisionNonzero
    , physicalStrategyNonzero
    , selectedSemanticsNonzero
    , physicalObjectsNonzero
    ] =
  Kernel.decideStorageRealizationValidByFacts
    subjectBasisAdmitted
    exactSubjectPresent
    semanticRevisionNonzero
    outcomeRevisionNonzero
    physicalStrategyNonzero
    selectedSemanticsNonzero
    physicalObjectsNonzero
decision _ = False

factLabels :: [String]
factLabels =
  [ "checked semantic-subject basis"
  , "exact semantic subject presence"
  , "semantic revision identity"
  , "outcome revision identity"
  , "physical strategy identity"
  , "selected realization semantics identity"
  , "physical object identity domain"
  ]
