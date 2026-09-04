module Main (main) where

import qualified ConcurrencyActivationKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "explicit architecture binding accepts" True
        (Kernel.decideActivationBindingExplicitByFacts True)
    , test "ambient binding rejects" False
        (Kernel.decideActivationBindingExplicitByFacts False)
    , test "restricted ownership exact and complete accepts" True
        (restricted True True)
    , test "restricted ownership mismatch rejects" False
        (restricted False True)
    , test "invented restricted owner rejects" False
        (restricted True False)
    , test "direct stateful ownership exact and complete accepts" True
        (direct True True)
    , test "direct stateful ownership mismatch rejects" False
        (direct False True)
    , test "invented direct stateful owner rejects" False
        (direct True False)
    , test "activation context accepts all certified facts" True
        (activation True True True True True True True)
    , test "activation context rejects population failure" False
        (activation False True True True True True True)
    , test "activation context rejects ambient binding" False
        (activation True False True True True True True)
    , test "activation context rejects unknown process binding" False
        (activation True True False True True True True)
    , test "activation context rejects restricted mismatch" False
        (activation True True True False True True True)
    , test "activation context rejects invented restricted owner" False
        (activation True True True True False True True)
    , test "activation context rejects direct stateful mismatch" False
        (activation True True True True True False True)
    , test "activation context rejects invented direct stateful owner" False
        (activation True True True True True True False)
    , test "participant classification accepts exact closure" True
        (participants True True True True)
    , test "participant classification rejects missing or extra role" False
        (participants False True True True)
    , test "participant classification rejects inactive internal target" False
        (participants True False True True)
    , test "participant classification rejects nonstatic internal target" False
        (participants True True False True)
    , test "participant classification rejects empty role" False
        (participants True True True False)
    , test "certified activation accepts both predecessors" True
        (certified True True)
    , test "certified activation rejects activation-context failure" False
        (certified False True)
    , test "certified activation rejects participant failure" False
        (certified True False)
    ]
  if and results then pure () else exitFailure

restricted :: Bool -> Bool -> Bool
restricted = Kernel.decideRestrictedInitialOwnershipByFacts

direct :: Bool -> Bool -> Bool
direct = Kernel.decideDirectStatefulOwnershipByFacts

activation :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
activation = Kernel.decideActivationContextByFacts

participants :: Bool -> Bool -> Bool -> Bool -> Bool
participants = Kernel.decideParticipantClassificationByFacts

certified :: Bool -> Bool -> Bool
certified = Kernel.decideCertifiedConcurrencyActivationByFacts

test :: String -> Bool -> Bool -> IO Bool
test label expected actual
  | expected == actual = putStrLn ("PASS: " <> label) >> pure True
  | otherwise = do
      putStrLn ("FAIL: " <> label <> " -- expected " <> show expected
        <> ", got " <> show actual)
      pure False
