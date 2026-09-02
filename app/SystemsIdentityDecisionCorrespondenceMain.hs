module Main (main) where

import SystemsIdentityKernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ check "artifact accepted"
        (isArtifactAccepted (decideArtifactIdentityByFacts True True True True True))
    , check "artifact source mismatch"
        (isArtifactSource (decideArtifactIdentityByFacts False True True True True))
    , check "artifact target mismatch"
        (isArtifactTarget (decideArtifactIdentityByFacts True False True True True))
    , check "artifact implementation mismatch"
        (isArtifactImplementation (decideArtifactIdentityByFacts True True False True True))
    , check "artifact declared-root mismatch"
        (isArtifactDeclaredRoot (decideArtifactIdentityByFacts True True True False True))
    , check "artifact manifest-root mismatch"
        (isArtifactManifestRoot (decideArtifactIdentityByFacts True True True True False))
    , check "decision accepted"
        (isDecisionAccepted (decideDecisionBindingByFacts True True True True True))
    , check "decision empty identity"
        (isDecisionNonempty (decideDecisionBindingByFacts False True True True True))
    , check "decision map-key mismatch"
        (isDecisionMapKey (decideDecisionBindingByFacts True False True True True))
    , check "decision digest mismatch"
        (isDecisionDigest (decideDecisionBindingByFacts True True False True True))
    , check "decision source mismatch"
        (isDecisionSource (decideDecisionBindingByFacts True True True False True))
    , check "decision target mismatch"
        (isDecisionTarget (decideDecisionBindingByFacts True True True True False))
    ]
  if and results then pure () else exitFailure

check :: String -> Bool -> IO Bool
check label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed

isArtifactAccepted :: ArtifactIdentityDecision -> Bool
isArtifactAccepted ArtifactIdentityAcceptedDecision = True
isArtifactAccepted _ = False

isArtifactSource :: ArtifactIdentityDecision -> Bool
isArtifactSource ArtifactIdentitySourceDecision = True
isArtifactSource _ = False

isArtifactTarget :: ArtifactIdentityDecision -> Bool
isArtifactTarget ArtifactIdentityTargetDecision = True
isArtifactTarget _ = False

isArtifactImplementation :: ArtifactIdentityDecision -> Bool
isArtifactImplementation ArtifactIdentityImplementationDecision = True
isArtifactImplementation _ = False

isArtifactDeclaredRoot :: ArtifactIdentityDecision -> Bool
isArtifactDeclaredRoot ArtifactIdentityDeclaredRootDecision = True
isArtifactDeclaredRoot _ = False

isArtifactManifestRoot :: ArtifactIdentityDecision -> Bool
isArtifactManifestRoot ArtifactIdentityManifestRootDecision = True
isArtifactManifestRoot _ = False

isDecisionAccepted :: DecisionBindingDecision -> Bool
isDecisionAccepted DecisionBindingAcceptedDecision = True
isDecisionAccepted _ = False

isDecisionNonempty :: DecisionBindingDecision -> Bool
isDecisionNonempty DecisionBindingNonemptyDecision = True
isDecisionNonempty _ = False

isDecisionMapKey :: DecisionBindingDecision -> Bool
isDecisionMapKey DecisionBindingMapKeyDecision = True
isDecisionMapKey _ = False

isDecisionDigest :: DecisionBindingDecision -> Bool
isDecisionDigest DecisionBindingDigestDecision = True
isDecisionDigest _ = False

isDecisionSource :: DecisionBindingDecision -> Bool
isDecisionSource DecisionBindingSourceDecision = True
isDecisionSource _ = False

isDecisionTarget :: DecisionBindingDecision -> Bool
isDecisionTarget DecisionBindingTargetDecision = True
isDecisionTarget _ = False
