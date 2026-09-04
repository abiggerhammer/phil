module Main (main) where

import qualified DeploymentAuthorityKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  policyRejects <- rejectionControls "policy" policyDecision policyFacts
  grantRejects <- rejectionControls "grant" grantDecision grantFacts
  issuedRejects <- rejectionControls "issued" issuedDecision issuedFacts
  usableRejects <- rejectionControls "usable" usableDecision usableFacts
  accepts <- sequence
    [ check "policy admissibility accepts all exact facts" (policyDecision (replicate 4 True))
    , check "grant match accepts all exact facts" (grantDecision (replicate 7 True))
    , check "issuance accepts valid qualification, policy, grant, and begin point"
        (issuedDecision (replicate 4 True))
    , check "use accepts valid qualification, policy, grant, and current point"
        (usableDecision (replicate 4 True))
    , check "issuance rejects invalid qualification predecessor"
        (not (issuedDecision [False, True, True, True]))
    , check "use rejects stale/invalid qualification predecessor"
        (not (usableDecision [False, True, True, True]))
    ]
  if and (accepts ++ policyRejects ++ grantRejects ++ issuedRejects ++ usableRejects)
    then pure ()
    else exitFailure

check :: String -> Bool -> IO Bool
check label accepted = do
  putStrLn ((if accepted then "PASS: " else "FAIL: ") <> label)
  pure accepted

rejectionControls :: String -> ([Bool] -> Bool) -> [String] -> IO [Bool]
rejectionControls family decision labels =
  mapM rejectOne (zip [0 ..] labels)
  where
    exact = replicate (length labels) True
    rejectOne (index, label) =
      check (family <> " rejects false " <> label)
        (not (decision (rejectAt index exact)))

rejectAt :: Int -> [Bool] -> [Bool]
rejectAt index facts =
  take index facts ++ [False] ++ drop (index + 1) facts

policyDecision :: [Bool] -> Bool
policyDecision [wellFormed, deploymentPolicyExact, claimPlanned, claimQualified] =
  Kernel.decideDeploymentAuthorityPolicyAdmissibleByFacts
    wellFormed deploymentPolicyExact claimPlanned claimQualified
policyDecision _ = False

grantDecision :: [Bool] -> Bool
grantDecision
    [ policyExact
    , qualificationExact
    , claimExact
    , actionExact
    , resourceExact
    , validityEndExact
    , contentIdentityValid
    ] =
  Kernel.decideDeploymentAuthorityGrantMatchesByFacts
    policyExact qualificationExact claimExact actionExact resourceExact
    validityEndExact contentIdentityValid
grantDecision _ = False

issuedDecision :: [Bool] -> Bool
issuedDecision [qualificationValid, policyAdmissible, grantMatches, beginsNow] =
  Kernel.decideDeploymentAuthorityIssuedByFacts
    qualificationValid policyAdmissible grantMatches beginsNow
issuedDecision _ = False

usableDecision :: [Bool] -> Bool
usableDecision [qualificationValid, policyAdmissible, grantMatches, grantCurrent] =
  Kernel.decideDeploymentAuthorityUsableByFacts
    qualificationValid policyAdmissible grantMatches grantCurrent
usableDecision _ = False

policyFacts :: [String]
policyFacts =
  [ "policy well-formedness"
  , "deployment policy identity"
  , "planned claim"
  , "qualified claim"
  ]

grantFacts :: [String]
grantFacts =
  [ "authority policy revision"
  , "qualification identity"
  , "claim identity"
  , "action identity"
  , "resource identity"
  , "qualification-bounded validity end"
  , "grant content identity"
  ]

issuedFacts :: [String]
issuedFacts =
  [ "qualification validity"
  , "policy admissibility"
  , "grant match"
  , "grant begin observation"
  ]

usableFacts :: [String]
usableFacts =
  [ "qualification validity"
  , "policy admissibility"
  , "grant match"
  , "grant currentness"
  ]
