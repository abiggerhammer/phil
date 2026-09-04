module Main (main) where

import qualified DeploymentQualificationKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "qualification accepts all exact Certified facts" (decision allExact)
    , test "qualification rejects invalid topology identity" (rejectAt 0)
    , test "qualification rejects malformed topology links" (rejectAt 1)
    , test "qualification rejects a claim without a selected domain" (rejectAt 2)
    , test "qualification rejects an unsound claim-domain assignment" (rejectAt 3)
    , test "qualification rejects an artifact mismatch" (rejectAt 4)
    , test "qualification rejects a policy mismatch" (rejectAt 5)
    , test "qualification rejects a topology-revision mismatch" (rejectAt 6)
    , test "qualification rejects a covered-claim mismatch" (rejectAt 7)
    , test "qualification rejects an invalid qualification identity" (rejectAt 8)
    , test "qualification rejects a stale qualification" (rejectAt 9)
    , test "qualification rejects incomplete selected-domain evidence" (rejectAt 10)
    , test "qualification rejects an extra domain-evidence binding" (rejectAt 11)
    , test "qualification rejects missing or inexact composition evidence" (rejectAt 12)
    , test "availability accepts a present valid qualification" $
        Kernel.decideDeploymentQualificationAvailableByFacts True True
    , test "availability rejects raw evidence without a qualification" $
        not (Kernel.decideDeploymentQualificationAvailableByFacts False True)
    , test "availability rejects a present invalid qualification" $
        not (Kernel.decideDeploymentQualificationAvailableByFacts True False)
    ]
  if and results then pure () else exitFailure

allExact :: [Bool]
allExact = replicate 13 True

decision :: [Bool] -> Bool
decision
  [ topologyIdentityValid
  , linksWellFormed
  , claimDomainsTotal
  , claimDomainsSound
  , artifactExact
  , policyExact
  , topologyExact
  , claimSetExact
  , identityValid
  , qualificationCurrent
  , everySelectedDomainHasEvidence
  , noExtraDomainBinding
  , compositionEvidenceValid
  ] = Kernel.decideDeploymentQualificationByFacts
        topologyIdentityValid
        linksWellFormed
        claimDomainsTotal
        claimDomainsSound
        artifactExact
        policyExact
        topologyExact
        claimSetExact
        identityValid
        qualificationCurrent
        everySelectedDomainHasEvidence
        noExtraDomainBinding
        compositionEvidenceValid
decision _ = False

rejectAt :: Int -> Bool
rejectAt index =
  not (decision (take index allExact ++ [False] ++ drop (index + 1) allExact))

test :: String -> Bool -> IO Bool
test label result = do
  putStrLn ((if result then "PASS: " else "FAIL: ") <> label)
  pure result
