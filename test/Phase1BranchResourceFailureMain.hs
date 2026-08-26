{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Examples.Phase1.BranchResourceWitnesses
import Phil.Systems.BranchResourceFailure
import Phil.Systems.IR (ValueId (..))
import Phil.Systems.Phase1Stage (SystemsMechanismKey (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SYS-007 upload branch resource/failure relations accept" uploadAccepted
    , test "SYS-007 Steve branch resource/failure relations accept" steveAccepted
    , test "SYS-007 missing reachable outcome rejects" missingOutcomeRejected
    , test "SYS-007 missing owner fate rejects" missingOwnerFateRejected
    , test "SYS-007 required release missing rejects" missingReleaseRejected
    , test "SYS-007 released owner cannot masquerade as terminal return" releasedOwnerReturnRejected
    , test "SYS-007 fatal source outcome cannot become continuation" fatalContinuationRejected
    , test "SYS-007 continuing owner cannot survive a terminal arm implicitly" continuingOwnerOnTerminalRejected
    , test "SYS-007 borrowed view is not an owning residue" borrowedViewNotOwnerRejected
    , test "SYS-007 semantic outcome reference is mandatory" emptySemanticOutcomeRejected
    , test "SYS-007 site key and exact mechanism must agree" mechanismKeyMismatchRejected
    , test "SYS-007 branch resource stage identity is deterministic" deterministicIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

uploadAccepted :: Either String ()
uploadAccepted = uploadBundle >>= mapLeft show . verifyBranchResourceStageBundle

steveAccepted :: Either String ()
steveAccepted = steveBundle >>= mapLeft show . verifyBranchResourceStageBundle

missingOutcomeRejected :: Either String ()
missingOutcomeRejected = do
  bundle <- uploadBundle
  site <- lookupSite uploadReceiveSite bundle
  let changed = site { branchSiteOutcomes = Map.delete "failure" (branchSiteOutcomes site) }
      mutated = replaceSite uploadReceiveSite changed bundle
  case verifyBranchResourceStageBundle mutated of
    Left (BranchResourceOutcomeDomainMismatch mechanism expected actual) -> do
      assert (mechanism == uploadReceiveSite) "wrong missing-outcome mechanism"
      assert (expected == Set.fromList ["success", "failure"]) "wrong target outcome domain"
      assert (actual == Set.singleton "success") "wrong mutated outcome domain"
    other -> Left ("missing branch outcome was accepted: " <> show other)

missingOwnerFateRejected :: Either String ()
missingOwnerFateRejected = do
  bundle <- uploadBundle
  site <- lookupSite uploadDigestSite bundle
  failure <- lookupOutcome "failure" site
  let failure' = failure { branchOutcomeOwnerFates = Map.empty }
      changed = site
        { branchSiteOutcomes = Map.insert "failure" failure' (branchSiteOutcomes site) }
      mutated = replaceSite uploadDigestSite changed bundle
  case verifyBranchResourceStageBundle mutated of
    Left (BranchResourceOwnerFateDomainMismatch mechanism label expected actual) -> do
      assert (mechanism == uploadDigestSite) "wrong owner-fate mechanism"
      assert (label == "failure") "wrong owner-fate label"
      assert (expected == Set.singleton (ValueId "server.payload")) "wrong tracked owner set"
      assert (Set.null actual) "owner fate was not actually removed"
    other -> Left ("missing owner fate was accepted: " <> show other)

missingReleaseRejected :: Either String ()
missingReleaseRejected = do
  bundle <- uploadBundle
  site <- lookupSite uploadReceiveSite bundle
  success <- lookupOutcome "success" site
  let success' = success
        { branchOutcomeOwnerFates = Map.singleton (ValueId "server.payload") OwnerReleased }
      changed = site
        { branchSiteOutcomes = Map.insert "success" success' (branchSiteOutcomes site) }
      mutated = replaceSite uploadReceiveSite changed bundle
  case verifyBranchResourceStageBundle mutated of
    Left (BranchResourceOwnerReleaseMissing mechanism label owner) -> do
      assert (mechanism == uploadReceiveSite) "wrong missing-release mechanism"
      assert (label == "success") "wrong missing-release label"
      assert (owner == ValueId "server.payload") "wrong missing-release owner"
    other -> Left ("invented owner release was accepted: " <> show other)

releasedOwnerReturnRejected :: Either String ()
releasedOwnerReturnRejected = do
  bundle <- uploadBundle
  site <- lookupSite uploadDigestSite bundle
  failure <- lookupOutcome "failure" site
  let failure' = failure
        { branchOutcomeOwnerFates = Map.singleton
            (ValueId "server.payload") OwnerReturnedAtTerminal }
      changed = site
        { branchSiteOutcomes = Map.insert "failure" failure' (branchSiteOutcomes site) }
      mutated = replaceSite uploadDigestSite changed bundle
  case verifyBranchResourceStageBundle mutated of
    Left (BranchResourceOwnerReleasedUnexpectedly mechanism label owner) -> do
      assert (mechanism == uploadDigestSite) "wrong release-vs-return mechanism"
      assert (label == "failure") "wrong release-vs-return label"
      assert (owner == ValueId "server.payload") "wrong released owner"
    other -> Left ("released owner was accepted as terminal return: " <> show other)

fatalContinuationRejected :: Either String ()
fatalContinuationRejected = do
  bundle <- uploadBundle
  site <- lookupSite uploadReceiveSite bundle
  failure <- lookupOutcome "failure" site
  let failure' = failure { branchOutcomeControlClass = BranchContinues }
      changed = site
        { branchSiteOutcomes = Map.insert "failure" failure' (branchSiteOutcomes site) }
      mutated = replaceSite uploadReceiveSite changed bundle
  case verifyBranchResourceStageBundle mutated of
    Left (BranchResourceControlClassMismatch mechanism label BranchContinues (BranchFatal "EarlyEOF")) -> do
      assert (mechanism == uploadReceiveSite) "wrong fatal-continuation mechanism"
      assert (label == "failure") "wrong fatal-continuation label"
    other -> Left ("fatal branch was accepted as continuing: " <> show other)

continuingOwnerOnTerminalRejected :: Either String ()
continuingOwnerOnTerminalRejected = do
  bundle <- steveBundle
  site <- lookupSite steveBlobInstallSite bundle
  installed <- lookupOutcome "installed" site
  let installed' = installed
        { branchOutcomeOwnerFates = Map.singleton
            (ValueId "put.candidate") OwnerContinues }
      changed = site
        { branchSiteOutcomes = Map.insert "installed" installed' (branchSiteOutcomes site) }
      mutated = replaceSite steveBlobInstallSite changed bundle
  case verifyBranchResourceStageBundle mutated of
    Left (BranchResourceOwnerContinuesOnTerminal mechanism label owner (BranchEnds "success")) -> do
      assert (mechanism == steveBlobInstallSite) "wrong terminal-owner mechanism"
      assert (label == "installed") "wrong terminal-owner label"
      assert (owner == ValueId "put.candidate") "wrong terminal owner"
    other -> Left ("terminal arm retained an implicit continuing owner: " <> show other)

borrowedViewNotOwnerRejected :: Either String ()
borrowedViewNotOwnerRejected = do
  bundle <- steveBundle
  site <- lookupSite steveDigestComputeSite bundle
  computed <- lookupOutcome "computed" site
  let view = ValueId "put.digest-view"
      computed' = computed
        { branchOutcomeOwnerFates = Map.singleton view OwnerContinues }
      changed = site
        { branchSiteTrackedOwners = Set.singleton view
        , branchSiteOutcomes = Map.singleton "computed" computed'
        }
      mutated = replaceSite steveDigestComputeSite changed bundle
  case verifyBranchResourceStageBundle mutated of
    Left (BranchResourceTrackedValueNotOwning mechanism owner _) -> do
      assert (mechanism == steveDigestComputeSite) "wrong borrowed-view mechanism"
      assert (owner == view) "wrong borrowed view"
    other -> Left ("borrowed view was accepted as branch owner: " <> show other)

emptySemanticOutcomeRejected :: Either String ()
emptySemanticOutcomeRejected = do
  bundle <- steveBundle
  site <- lookupSite steveDigestComputeSite bundle
  computed <- lookupOutcome "computed" site
  let computed' = computed { branchOutcomeSemanticRef = "" }
      changed = site { branchSiteOutcomes = Map.singleton "computed" computed' }
      mutated = replaceSite steveDigestComputeSite changed bundle
  case verifyBranchResourceStageBundle mutated of
    Left (BranchResourceEmptySemanticOutcome mechanism label) -> do
      assert (mechanism == steveDigestComputeSite) "wrong empty-semantic mechanism"
      assert (label == "computed") "wrong empty-semantic label"
    other -> Left ("empty semantic outcome reference was accepted: " <> show other)

mechanismKeyMismatchRejected :: Either String ()
mechanismKeyMismatchRejected = do
  bundle <- steveBundle
  site <- lookupSite steveDigestComputeSite bundle
  let wrong = SystemsMechanismKey "StevePut:put.entry:term.runtime-choice.NotDigest"
      changed = site { branchSiteMechanism = wrong }
      mutated = replaceSite steveDigestComputeSite changed bundle
  case verifyBranchResourceStageBundle mutated of
    Left (BranchResourceSiteMapKeyMismatch expected actual) -> do
      assert (expected == steveDigestComputeSite) "wrong mechanism map key"
      assert (actual == wrong) "wrong substituted mechanism"
    other -> Left ("mechanism key mismatch was accepted: " <> show other)

deterministicIdentity :: Either String ()
deterministicIdentity = do
  bundle <- steveBundle
  let reversed = Map.fromList (reverse (Map.toAscList (branchResourceStageSites bundle)))
      rebuilt = makeBranchResourceStageBundle (branchResourceStageBase bundle) reversed
  assert
    (branchResourceStageRevision rebuilt == branchResourceStageRevision bundle)
    "branch resource stage revision changed with map order"
  mapLeft show $ verifyBranchResourceStageBundle rebuilt

replaceSite
  :: SystemsMechanismKey
  -> BranchSiteContract
  -> BranchResourceStageBundle
  -> BranchResourceStageBundle
replaceSite key site bundle = makeBranchResourceStageBundle
  (branchResourceStageBase bundle)
  (Map.insert key site (branchResourceStageSites bundle))

lookupSite
  :: SystemsMechanismKey
  -> BranchResourceStageBundle
  -> Either String BranchSiteContract
lookupSite key bundle = maybe
  (Left ("missing branch site: " <> show key))
  Right
  (Map.lookup key (branchResourceStageSites bundle))

lookupOutcome :: String -> BranchSiteContract -> Either String BranchOutcomeContract
lookupOutcome label site = maybe
  (Left ("missing branch outcome: " <> label))
  Right
  (Map.lookup (Text.pack label) (branchSiteOutcomes site))

uploadBundle :: Either String BranchResourceStageBundle
uploadBundle = uploadBranchResourceStageBundle

steveBundle :: Either String BranchResourceStageBundle
steveBundle = steveBranchResourceStageBundle

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
