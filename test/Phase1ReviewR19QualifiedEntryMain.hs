{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.ProviderQualification
  ( CheckedProviderOperationQualification (..)
  , CheckedProviderSemanticQualification (..)
  , ProviderImplementationEntryKey
  , ProviderOperationKey (..)
  )
import Phil.Examples.Phase1.AuthorityEffectWitnesses
  ( steveAuthorityEffectStageBundle
  , uploadAuthorityEffectStageBundle
  )
import Phil.Examples.Phase1.ProviderCallWitnesses
  ( steveProviderCallExpectations
  , uploadProviderCallExpectations
  )
import Phil.Systems.AuthorityEffectCorrespondence
import Phil.Systems.Phase1Stage (SystemsMechanismKey)
import Phil.Systems.ProviderCallCorrespondence
import System.Exit (exitFailure)

data EntryFixture = EntryFixture
  { fixtureBundle :: AuthorityEffectStageBundle
  , fixtureSite :: SystemsMechanismKey
  , fixtureOccurrence :: Text
  , fixtureOperation :: ProviderOperationKey
  , fixtureOriginalEntry :: ProviderImplementationEntryKey
  , fixtureDonorEntry :: ProviderImplementationEntryKey
  }

data EntryMutation
  = ChangeLinkOnly
  | ChangeSelectionOnly
  | ChangeSelectionAndLinks
  deriving (Eq)

type StageVerifier = AuthorityEffectStageBundle
  -> Either AuthorityEffectStageVerificationError ()

main :: IO ()
main = do
  results <- sequence
    [ test "R19 genuine Steve qualification accepts at the strong gate" steveAccepted
    , test "R19 opaque Upload control still accepts at the strong gate" uploadAccepted
    , test "R19 one-sided link change rejects at the provider base" (oneSidedRejects ChangeLinkOnly)
    , test "R19 one-sided selection change rejects at the provider base" (oneSidedRejects ChangeSelectionOnly)
    , test "R19 complete provider gate alone does not bind semantic entries" providerGateControl
    , test "R19 coordinated compute/check entry rebinding rejects at the strong gate"
        (qualifiedRejects strongVerifier computeFixture)
    , test "R19 coordinated compute/check entry rebinding also rejects at the relative authority gate"
        (qualifiedRejects verifyAuthorityEffectStageBundle computeFixture)
    , test "R19 reverse digest entry rebinding rejects"
        (qualifiedRejects strongVerifier checkFixture)
    , test "R19 blob read/install entry rebinding rejects"
        (qualifiedRejects strongVerifier blobFixture)
    , test "R19 selected but unused operation still requires its qualified entry" unusedOperationRejects
    , test "R19 restoring the genuine mapping restores exact identity and acceptance" restorationAccepted
    ]
  if and results then pure () else exitFailure

strongVerifier :: StageVerifier
strongVerifier = verifyAuthorityEffectStageBundleAgainst steveProviderCallExpectations

steveAccepted :: Either String ()
steveAccepted = steveAuthorityEffectStageBundle >>= mapLeft show . strongVerifier

uploadAccepted :: Either String ()
uploadAccepted = uploadAuthorityEffectStageBundle >>= mapLeft show
  . verifyAuthorityEffectStageBundleAgainst uploadProviderCallExpectations

computeFixture, checkFixture, blobFixture :: Either String EntryFixture
computeFixture = makeFixture (ProviderOperationKey "digest.compute") (ProviderOperationKey "digest.check")
checkFixture = makeFixture (ProviderOperationKey "digest.check") (ProviderOperationKey "digest.compute")
blobFixture = makeFixture (ProviderOperationKey "blob.read") (ProviderOperationKey "blob.install-if-absent")

-- Both original and donor entries come from a freshly materialized genuine
-- qualification. Never manufacture or edit a Checked qualification record.
makeFixture :: ProviderOperationKey -> ProviderOperationKey -> Either String EntryFixture
makeFixture operation donorOperation = do
  bundle <- steveAuthorityEffectStageBundle
  mapLeft show $ strongVerifier bundle
  (site, expectation) <- case
      [ (key, value)
      | (key, value) <- Map.toAscList steveProviderCallExpectations
      , expectedProviderOperation value == operation
      ] of
    [value] -> Right value
    _ -> Left "fixture needs exactly one independently expected site for this operation"
  let occurrence = expectedProviderOccurrence expectation
      base = authorityEffectStageBase bundle
  selection <- lookupRequired "selected provider" occurrence (providerCallStageSelections base)
  let entries = selectedProviderOperationEntries selection
  original <- lookupRequired "original implementation entry" operation entries
  donor <- lookupRequired "donor implementation entry" donorOperation entries
  surface <- lookupRequired "genuine provider surface" occurrence (authorityEffectStageSurfaces bundle)
  case surface of
    QualifiedProviderSemanticSurface semantic _ _ -> do
      let qualified = checkedProviderOperations semantic
      assert (entries == Map.map checkedProviderImplementationEntry qualified)
        "selected map does not equal the genuine qualified entry map"
      assert (all (\(key, checked) -> key == checkedProviderOperationKey checked)
        (Map.toAscList qualified)) "qualification operation key mismatch in fixture"
    _ -> Left "fixture unexpectedly has an opaque provider surface"
  assert (original /= donor) "donor must differ from the operation's genuine entry"
  link <- lookupRequired "original call link" site (providerCallStageLinks base)
  case providerCallBindingBasis link of
    ExactProviderCallBinding actualOccurrence _ _ actualOperation actualEntry ->
      assert (actualOccurrence == occurrence && actualOperation == operation && actualEntry == original)
        "original link does not match the independent expectation and genuine entry"
    _ -> Left "fixture unexpectedly has a runtime-symbol-only link"
  Right EntryFixture
    { fixtureBundle = bundle
    , fixtureSite = site
    , fixtureOccurrence = occurrence
    , fixtureOperation = operation
    , fixtureOriginalEntry = original
    , fixtureDonorEntry = donor
    }

oneSidedRejects :: EntryMutation -> Either String ()
oneSidedRejects mode = do
  fixture <- computeFixture
  mutated <- checkedMutation fixture mode
  let (expectedEntry, actualEntry) = case mode of
        ChangeLinkOnly -> (fixtureOriginalEntry fixture, fixtureDonorEntry fixture)
        ChangeSelectionOnly -> (fixtureDonorEntry fixture, fixtureOriginalEntry fixture)
        ChangeSelectionAndLinks -> (fixtureDonorEntry fixture, fixtureDonorEntry fixture)
  case strongVerifier mutated of
    Left (AuthorityEffectBaseStageError
      (ProviderCallImplementationEntryMismatch site expected actual)) ->
        assert (site == fixtureSite fixture && expected == expectedEntry && actual == actualEntry)
          "wrong one-sided implementation-entry mismatch diagnostic"
    other -> Left ("one-sided entry mismatch did not reject at the provider base: " <> show other)

providerGateControl :: Either String ()
providerGateControl = do
  fixture <- computeFixture
  mutated <- checkedMutation fixture ChangeSelectionAndLinks
  mapLeft show $ verifyProviderCallStageBundleCompleteAgainst
    steveProviderCallExpectations (authorityEffectStageBase mutated)

qualifiedRejects :: StageVerifier -> Either String EntryFixture -> Either String ()
qualifiedRejects verifier fixtureResult = do
  fixture <- fixtureResult
  mutated <- checkedMutation fixture ChangeSelectionAndLinks
  -- Inventory, operation meaning, and candidate link/selection agreement all
  -- pass. The authority/effect gate must find the semantic-entry mismatch.
  mapLeft show $ verifyProviderCallStageBundleCompleteAgainst
    steveProviderCallExpectations (authorityEffectStageBase mutated)
  expectQualifiedMismatch fixture (verifier mutated)

unusedOperationRejects :: Either String ()
unusedOperationRejects = do
  fixture <- computeFixture
  let original = fixtureBundle fixture
      base = authorityEffectStageBase original
      site = fixtureSite fixture
      subsetBase = makeProviderCallStageBundle
        (providerCallStageBase base)
        (providerCallStageSelections base)
        (Set.delete site (providerCallStageCallSites base))
        (Map.delete site (providerCallStageLinks base))
      subset = makeAuthorityEffectStageBundle subsetBase
        (authorityEffectStageSurfaces original)
        (Map.delete site (authorityEffectStageUses original))
      mutated = setEntry fixture ChangeSelectionOnly (fixtureDonorEntry fixture) subset
  assert (not (any (matchesOperation fixture) (Map.elems (providerCallStageLinks subsetBase))))
    "unused-operation fixture still has a represented call"
  -- This is deliberately a relative subset, not an independent-completeness
  -- claim. Its unused selected operation still carries genuine qualification.
  mapLeft show $ verifyAuthorityEffectStageBundle subset
  assertFresh mutated
  assert (setEntry fixture ChangeSelectionAndLinks (fixtureOriginalEntry fixture) mutated == subset)
    "unused-operation mutation changed something other than the selected entry"
  mapLeft show $ verifyProviderCallStageBundle (authorityEffectStageBase mutated)
  expectQualifiedMismatch fixture (verifyAuthorityEffectStageBundle mutated)

restorationAccepted :: Either String ()
restorationAccepted = do
  fixture <- computeFixture
  mutated <- checkedMutation fixture ChangeSelectionAndLinks
  let restored = setEntry fixture ChangeSelectionAndLinks (fixtureOriginalEntry fixture) mutated
  assert (restored == fixtureBundle fixture) "restoration did not recover exact original stage identity"
  mapLeft show $ strongVerifier restored

expectQualifiedMismatch
  :: EntryFixture -> Either AuthorityEffectStageVerificationError () -> Either String ()
expectQualifiedMismatch fixture result = case result of
  Left (AuthorityEffectOperationEntryMismatch occurrence operation) ->
    assert (occurrence == fixtureOccurrence fixture && operation == fixtureOperation fixture)
      "wrong qualified-entry mismatch location"
  other -> Left ("qualified-entry mismatch escaped the semantic gate: " <> show other)

checkedMutation :: EntryFixture -> EntryMutation -> Either String AuthorityEffectStageBundle
checkedMutation fixture mode = do
  let original = fixtureBundle fixture
      mutated = setEntry fixture mode (fixtureDonorEntry fixture) original
      originalBase = authorityEffectStageBase original
      mutatedBase = authorityEffectStageBase mutated
      requiredSites = Map.keysSet steveProviderCallExpectations
  assertFresh mutated
  assert (mutated /= original) "entry mutation was a no-op"
  assert (providerCallStageRevision mutatedBase /= providerCallStageRevision originalBase
    && authorityEffectStageRevision mutated /= authorityEffectStageRevision original)
    "changed candidate entries did not change both canonical stage revisions"
  assert (providerCallStageCallSites originalBase == requiredSites
    && providerCallStageCallSites mutatedBase == requiredSites
    && Map.keysSet (providerCallStageLinks mutatedBase) == requiredSites)
    "entry mutation changed the independent call inventory"
  assert (providerCallStageBase mutatedBase == providerCallStageBase originalBase)
    "entry mutation changed the underlying Subject/Systems stage"
  assert (authorityEffectStageSurfaces mutated == authorityEffectStageSurfaces original
    && authorityEffectStageUses mutated == authorityEffectStageUses original)
    "entry mutation changed genuine qualification, authority surfaces, or use summaries"
  -- Restoring only the entry fields must recover the entire original bundle.
  -- This checks preservation of admissions, claim inputs, operation keys,
  -- runtime symbols/signatures, and all other candidate data in one equality.
  assert (setEntry fixture ChangeSelectionAndLinks (fixtureOriginalEntry fixture) mutated == original)
    "entry mutation changed fields outside the selected/link implementation entries"
  Right mutated

assertFresh :: AuthorityEffectStageBundle -> Either String ()
assertFresh bundle = do
  let base = authorityEffectStageBase bundle
  assert (providerCallStageRevision base == deriveProviderCallStageRevision base)
    "provider-stage revision is stale"
  assert (authorityEffectStageRevision bundle == deriveAuthorityEffectStageRevision bundle)
    "authority/effect-stage revision is stale"

setEntry
  :: EntryFixture -> EntryMutation -> ProviderImplementationEntryKey
  -> AuthorityEffectStageBundle -> AuthorityEffectStageBundle
setEntry fixture mode replacement bundle = makeAuthorityEffectStageBundle
  (makeProviderCallStageBundle (providerCallStageBase base) selections
    (providerCallStageCallSites base) links)
  (authorityEffectStageSurfaces bundle)
  (authorityEffectStageUses bundle)
  where
    base = authorityEffectStageBase bundle
    selections
      | mode == ChangeLinkOnly = providerCallStageSelections base
      | otherwise = Map.adjust changeSelection (fixtureOccurrence fixture)
          (providerCallStageSelections base)
    links
      | mode == ChangeSelectionOnly = providerCallStageLinks base
      | otherwise = Map.map changeLink (providerCallStageLinks base)
    changeSelection selection = selection
      { selectedProviderOperationEntries = Map.insert (fixtureOperation fixture) replacement
          (selectedProviderOperationEntries selection) }
    changeLink link = case providerCallBindingBasis link of
      ExactProviderCallBinding occurrence admission interface operation _
        | matchesOperation fixture link -> link
            { providerCallBindingBasis = ExactProviderCallBinding
                occurrence admission interface operation replacement }
      _ -> link

matchesOperation :: EntryFixture -> ProviderCallLink -> Bool
matchesOperation fixture link = case providerCallBindingBasis link of
  ExactProviderCallBinding occurrence _ _ operation _ ->
    occurrence == fixtureOccurrence fixture && operation == fixtureOperation fixture
  _ -> False

lookupRequired :: Ord k => String -> k -> Map.Map k a -> Either String a
lookupRequired label key = maybe (Left ("missing " <> label)) Right . Map.lookup key

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False
