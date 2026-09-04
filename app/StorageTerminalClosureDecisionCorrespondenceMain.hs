module Main (main) where

import qualified StorageTerminalClosureKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "live semantic storage owner always rejects"
        (not Kernel.decideSemanticStorageLiveByFacts)
    , test "released semantic storage owner accepts"
        Kernel.decideSemanticStorageReleasedByFacts
    , test "exact permitted terminal disposition accepts"
        (Kernel.decideSemanticStorageTerminalDispositionByFacts True)
    , test "unpermitted terminal disposition rejects"
        (not (Kernel.decideSemanticStorageTerminalDispositionByFacts False))
    , test "semantic storage closure accepts unique closed owners"
        (Kernel.decideSemanticStorageClosureByFacts True True)
    , test "semantic storage closure rejects duplicate owner keys"
        (not (Kernel.decideSemanticStorageClosureByFacts False True))
    , test "semantic storage closure rejects an open owner"
        (not (Kernel.decideSemanticStorageClosureByFacts True False))
    , test "reclaimed physical storage accepts"
        Kernel.decidePhysicalStorageReclaimedByFacts
    , test "leaked physical storage always rejects realization"
        (not Kernel.decidePhysicalStorageLeakedByFacts)
    , test "exact profile-authorized retention accepts"
        (Kernel.decidePhysicalStorageRetainedByProfileByFacts True True)
    , test "retention rejects when policy does not permit retention"
        (not (Kernel.decidePhysicalStorageRetainedByProfileByFacts False True))
    , test "retention rejects a mismatched profile"
        (not (Kernel.decidePhysicalStorageRetainedByProfileByFacts True False))
    , test "physical reclamation accepts unique accepted states"
        (Kernel.decidePhysicalStorageReclamationByFacts True True)
    , test "physical reclamation rejects duplicate object keys"
        (not (Kernel.decidePhysicalStorageReclamationByFacts False True))
    , test "physical reclamation rejects a bad physical state"
        (not (Kernel.decidePhysicalStorageReclamationByFacts True False))
    , test "memory process closure accepts all semantic predecessors"
        (Kernel.decideCertifiedMemoryProcessClosureByFacts True True True)
    , test "memory process closure rejects stage-identity failure"
        (not (Kernel.decideCertifiedMemoryProcessClosureByFacts False True True))
    , test "memory process closure rejects realization failure"
        (not (Kernel.decideCertifiedMemoryProcessClosureByFacts True False True))
    , test "memory process closure rejects semantic-storage failure"
        (not (Kernel.decideCertifiedMemoryProcessClosureByFacts True True False))
    , test "memory root closure accepts ordinary root and static storage closure"
        (Kernel.decideCertifiedMemoryRootClosureByFacts True True)
    , test "memory root closure rejects ordinary root-terminal failure"
        (not (Kernel.decideCertifiedMemoryRootClosureByFacts False True))
    , test "memory root closure rejects static semantic-storage failure"
        (not (Kernel.decideCertifiedMemoryRootClosureByFacts True False))
    ]
  if and results then pure () else exitFailure

test :: String -> Bool -> IO Bool
test label accepted = do
  putStrLn ((if accepted then "PASS: " else "FAIL: ") <> label)
  pure accepted
