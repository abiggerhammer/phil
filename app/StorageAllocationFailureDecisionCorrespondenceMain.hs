module Main (main) where

import qualified StorageAllocationFailureKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "failure realization accepts valid base and disposition"
        (Kernel.decideStorageFailureRealizationByFacts True True)
    , test "failure realization rejects invalid MEM-001 predecessor"
        (not (Kernel.decideStorageFailureRealizationByFacts False True))
    , test "failure realization rejects invalid failure disposition"
        (not (Kernel.decideStorageFailureRealizationByFacts True False))
    , test "allocation-cannot-fail disposition accepts"
        Kernel.decideStorageFailureCannotFailByFacts
    , test "mapped source failure accepts exact identity and declaration"
        (Kernel.decideStorageFailureMapsToSourceByFacts True True)
    , test "mapped source failure rejects invalid failure identity"
        (not (Kernel.decideStorageFailureMapsToSourceByFacts False True))
    , test "mapped source failure rejects undeclared outcome"
        (not (Kernel.decideStorageFailureMapsToSourceByFacts True False))
    , test "checked capacity evidence accepts nonzero identity"
        (Kernel.decideStorageFailureProvedUnreachableByFacts True)
    , test "checked capacity evidence rejects zero identity"
        (not (Kernel.decideStorageFailureProvedUnreachableByFacts False))
    , test "explicit allocation assumption accepts nonzero identity"
        (Kernel.decideStorageFailureAssumptionByFacts True)
    , test "explicit allocation assumption rejects zero identity"
        (not (Kernel.decideStorageFailureAssumptionByFacts False))
    , test "deployment requirement accepts nonzero identity"
        (Kernel.decideStorageFailureDeploymentRequirementByFacts True)
    , test "deployment requirement rejects zero identity"
        (not (Kernel.decideStorageFailureDeploymentRequirementByFacts False))
    , test "unaccounted allocation failure always rejects"
        (not Kernel.decideStorageFailureUnaccountedByFacts)
    ]
  if and results then pure () else exitFailure

test :: String -> Bool -> IO Bool
test label accepted = do
  putStrLn ((if accepted then "PASS: " else "FAIL: ") <> label)
  pure accepted
