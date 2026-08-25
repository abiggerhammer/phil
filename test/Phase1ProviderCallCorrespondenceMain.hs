{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.ProviderQualification
  ( ProviderImplementationEntryKey (..)
  , ProviderOperationKey (..)
  )
import Phil.Core.ProviderQualificationIdentity
  ( CheckedProviderQualificationAdmissionIdentity (..)
  , ProviderQualificationAdmissionDecision (..)
  , ProviderQualificationSubject (..)
  )
import Phil.Core.Static (InterfaceRevision (..))
import Phil.Examples.Phase1.ProviderCallWitnesses
import Phil.Systems.Phase1Stage (SystemsMechanismKey (..))
import Phil.Systems.ProviderCallCorrespondence
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SYS-005 upload provider call accepts exact admission" uploadAccepted
    , test "SYS-005 Steve provider calls accept exact admissions" steveAccepted
    , test "SYS-005 upload bridge is an admitted opaque boundary" uploadBridgeIsExact
    , test "SYS-005 matching symbol cannot rescue wrong admission" wrongAdmissionRejected
    , test "SYS-005 runtime symbol alone cannot establish operation mapping" symbolOnlyRejected
    , test "SYS-005 wrong semantic operation rejects with same symbol" wrongOperationRejected
    , test "SYS-005 wrong implementation entry rejects with same symbol" wrongEntryRejected
    , test "SYS-005 wrong provider interface rejects" wrongInterfaceRejected
    , test "SYS-005 harmless runtime symbol rename preserves validity" symbolRenameAccepted
    , test "SYS-005 missing provider call link rejects closure" missingLinkRejected
    , test "SYS-005 unknown provider occurrence rejects" unknownSelectionRejected
    , test "SYS-005 rejected selected admission cannot justify call" rejectedSelectionRejected
    , test "SYS-005 provider call stage identity is deterministic" deterministicIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

uploadAccepted :: Either String ()
uploadAccepted = uploadBundle >>= mapLeft show . verifyProviderCallStageBundle

steveAccepted :: Either String ()
steveAccepted = steveBundle >>= mapLeft show . verifyProviderCallStageBundle

uploadBridgeIsExact :: Either String ()
uploadBridgeIsExact = do
  bundle <- uploadBundle
  selection <- singleSelection bundle
  case selectedProviderSubject selection of
    OpaqueProviderBoundary boundary ->
      assert (boundary == "phase0.upload.storage.runtime-boundary")
        "upload storage bridge names wrong opaque boundary"
    other -> Left ("upload storage bridge used wrong qualification subject: " <> show other)
  case checkedQualificationAdmissionDecision
      (selectedProviderCheckedAdmission selection) of
    QualificationAdmitted -> Right ()
    other -> Left ("upload storage bridge was not admitted: " <> show other)

wrongAdmissionRejected :: Either String ()
wrongAdmissionRejected = do
  bundle <- steveBundle
  link <- lookupLink digestComputeSite bundle
  (occurrence, _admission, interface, operation, entry) <- exactBasis link
  selection <- lookupSelection occurrence bundle
  other <- otherSelection occurrence bundle
  let wrongAdmission = checkedQualificationAdmissionRevision
        (selectedProviderCheckedAdmission other)
      badLink = link
        { providerCallBindingBasis = ExactProviderCallBinding
            occurrence wrongAdmission interface operation entry }
      mutated = replaceLink bundle digestComputeSite badLink
      expected = checkedQualificationAdmissionRevision
        (selectedProviderCheckedAdmission selection)
  case verifyProviderCallStageBundle mutated of
    Left (ProviderCallAdmissionMismatch site expectedRevision actualRevision) -> do
      assert (site == digestComputeSite) "wrong call site in admission mismatch"
      assert (expectedRevision == expected) "wrong expected admission revision"
      assert (actualRevision == wrongAdmission) "wrong supplied admission revision"
      assert (providerCallRuntimeSymbol badLink == providerCallRuntimeSymbol link)
        "fixture accidentally changed runtime symbol"
    otherResult -> Left ("wrong admission with matching symbol was accepted: " <> show otherResult)

symbolOnlyRejected :: Either String ()
symbolOnlyRejected = do
  bundle <- steveBundle
  link <- lookupLink digestComputeSite bundle
  let badLink = link
        { providerCallBindingBasis = RuntimeSymbolOnlyProviderCall
            (providerCallRuntimeSymbol link)
            (providerCallRuntimeSignature link) }
      mutated = replaceLink bundle digestComputeSite badLink
  case verifyProviderCallStageBundle mutated of
    Left (ProviderCallRuntimeSymbolInferenceRejected site symbol signature) -> do
      assert (site == digestComputeSite) "wrong symbol-only call site"
      assert (symbol == providerCallRuntimeSymbol link) "wrong symbol-only symbol"
      assert (signature == providerCallRuntimeSignature link) "wrong symbol-only signature"
    other -> Left ("runtime symbol-only provider mapping was accepted: " <> show other)

wrongOperationRejected :: Either String ()
wrongOperationRejected = do
  bundle <- steveBundle
  link <- lookupLink digestComputeSite bundle
  (occurrence, admission, interface, _operation, entry) <- exactBasis link
  let wrongOperation = ProviderOperationKey "blob.read"
      badLink = link
        { providerCallBindingBasis = ExactProviderCallBinding
            occurrence admission interface wrongOperation entry }
      mutated = replaceLink bundle digestComputeSite badLink
  case verifyProviderCallStageBundle mutated of
    Left (ProviderCallOperationNotSelected site actual) -> do
      assert (site == digestComputeSite) "wrong site in operation rejection"
      assert (actual == wrongOperation) "wrong rejected semantic operation"
      assert (providerCallRuntimeSymbol badLink == providerCallRuntimeSymbol link)
        "fixture accidentally changed runtime symbol"
    other -> Left ("wrong semantic operation was accepted: " <> show other)

wrongEntryRejected :: Either String ()
wrongEntryRejected = do
  bundle <- steveBundle
  link <- lookupLink digestComputeSite bundle
  (occurrence, admission, interface, operation, _entry) <- exactBasis link
  let wrongEntry = ProviderImplementationEntryKey "steve.blob.impl.read"
      badLink = link
        { providerCallBindingBasis = ExactProviderCallBinding
            occurrence admission interface operation wrongEntry }
      mutated = replaceLink bundle digestComputeSite badLink
  case verifyProviderCallStageBundle mutated of
    Left (ProviderCallImplementationEntryMismatch site _ actual) -> do
      assert (site == digestComputeSite) "wrong site in entry rejection"
      assert (actual == wrongEntry) "wrong rejected implementation entry"
    other -> Left ("wrong implementation entry was accepted: " <> show other)

wrongInterfaceRejected :: Either String ()
wrongInterfaceRejected = do
  bundle <- steveBundle
  link <- lookupLink digestComputeSite bundle
  (occurrence, admission, _interface, operation, entry) <- exactBasis link
  let wrongInterface = InterfaceRevision "steve.provider.blob.v1"
      badLink = link
        { providerCallBindingBasis = ExactProviderCallBinding
            occurrence admission wrongInterface operation entry }
      mutated = replaceLink bundle digestComputeSite badLink
  case verifyProviderCallStageBundle mutated of
    Left (ProviderCallInterfaceMismatch site _ actual) -> do
      assert (site == digestComputeSite) "wrong site in interface rejection"
      assert (actual == wrongInterface) "wrong rejected provider interface"
    other -> Left ("wrong provider interface was accepted: " <> show other)

symbolRenameAccepted :: Either String ()
symbolRenameAccepted = do
  bundle <- steveBundle
  link <- lookupLink digestComputeSite bundle
  let renamed = link
        { providerCallRuntimeSymbol = "backend_renamed_sha256_symbol" }
      mutated = replaceLink bundle digestComputeSite renamed
  mapLeft show $ verifyProviderCallStageBundle mutated

missingLinkRejected :: Either String ()
missingLinkRejected = do
  bundle <- steveBundle
  let links = Map.delete digestComputeSite (providerCallStageLinks bundle)
      mutated = makeProviderCallStageBundle
        (providerCallStageBase bundle)
        (providerCallStageSelections bundle)
        (providerCallStageCallSites bundle)
        links
  case verifyProviderCallStageBundle mutated of
    Left (ProviderCallLinkDomainMismatch expected actual) -> do
      assert (expected == providerCallStageCallSites bundle) "wrong expected call-site domain"
      assert (actual == Map.keysSet links) "wrong actual link domain"
    other -> Left ("missing provider call link was accepted: " <> show other)

unknownSelectionRejected :: Either String ()
unknownSelectionRejected = do
  bundle <- steveBundle
  link <- lookupLink digestComputeSite bundle
  (_occurrence, admission, interface, operation, entry) <- exactBasis link
  let badOccurrence = "steve.not-selected-provider"
      badLink = link
        { providerCallBindingBasis = ExactProviderCallBinding
            badOccurrence admission interface operation entry }
      mutated = replaceLink bundle digestComputeSite badLink
  case verifyProviderCallStageBundle mutated of
    Left (ProviderCallUnknownSelection site occurrence) -> do
      assert (site == digestComputeSite) "wrong site in unknown-selection rejection"
      assert (occurrence == badOccurrence) "wrong unknown provider occurrence"
    other -> Left ("unknown provider occurrence was accepted: " <> show other)

rejectedSelectionRejected :: Either String ()
rejectedSelectionRejected = do
  bundle <- steveBundle
  link <- lookupLink digestComputeSite bundle
  (occurrence, _admission, _interface, _operation, _entry) <- exactBasis link
  selection <- lookupSelection occurrence bundle
  let checked = selectedProviderCheckedAdmission selection
      rejectedChecked = checked
        { checkedQualificationAdmissionDecision =
            QualificationRejected (Set.singleton "fixture-rejection") }
      rejectedSelection = selection
        { selectedProviderCheckedAdmission = rejectedChecked }
      selections = Map.insert occurrence rejectedSelection
        (providerCallStageSelections bundle)
      mutated = makeProviderCallStageBundle
        (providerCallStageBase bundle)
        selections
        (providerCallStageCallSites bundle)
        (providerCallStageLinks bundle)
  case verifyProviderCallStageBundle mutated of
    Left (ProviderSelectionAdmissionRejected actual) ->
      assert (actual == occurrence) "wrong rejected selection occurrence"
    other -> Left ("rejected provider admission was accepted: " <> show other)

deterministicIdentity :: Either String ()
deterministicIdentity = do
  bundle <- steveBundle
  let selections = Map.fromList
        (reverse (Map.toAscList (providerCallStageSelections bundle)))
      links = Map.fromList
        (reverse (Map.toAscList (providerCallStageLinks bundle)))
      rebuilt = makeProviderCallStageBundle
        (providerCallStageBase bundle)
        selections
        (providerCallStageCallSites bundle)
        links
  assert (providerCallStageRevision rebuilt == providerCallStageRevision bundle)
    "provider-call stage revision changed with map enumeration order"
  mapLeft show $ verifyProviderCallStageBundle rebuilt

replaceLink
  :: ProviderCallStageBundle
  -> SystemsMechanismKey
  -> ProviderCallLink
  -> ProviderCallStageBundle
replaceLink bundle key link = makeProviderCallStageBundle
  (providerCallStageBase bundle)
  (providerCallStageSelections bundle)
  (providerCallStageCallSites bundle)
  (Map.insert key link (providerCallStageLinks bundle))

lookupLink
  :: SystemsMechanismKey
  -> ProviderCallStageBundle
  -> Either String ProviderCallLink
lookupLink key bundle = maybe
  (Left ("missing provider call link: " <> show key))
  Right
  (Map.lookup key (providerCallStageLinks bundle))

lookupSelection
  :: String
  -> ProviderCallStageBundle
  -> Either String SelectedProviderAdmission
lookupSelection occurrence bundle = maybe
  (Left ("missing provider selection: " <> occurrence))
  Right
  (Map.lookup (fromString occurrence) (providerCallStageSelections bundle))

otherSelection
  :: String
  -> ProviderCallStageBundle
  -> Either String SelectedProviderAdmission
otherSelection occurrence bundle = case
  [ selection
  | (key, selection) <- Map.toAscList (providerCallStageSelections bundle)
  , key /= fromString occurrence
  ] of
    selection : _ -> Right selection
    [] -> Left "no alternate provider selection in fixture"

singleSelection :: ProviderCallStageBundle -> Either String SelectedProviderAdmission
singleSelection bundle = case Map.elems (providerCallStageSelections bundle) of
  [selection] -> Right selection
  other -> Left ("expected one provider selection, got " <> show (length other))

exactBasis
  :: ProviderCallLink
  -> Either String (String, QualificationAdmissionRevision, InterfaceRevision, ProviderOperationKey, ProviderImplementationEntryKey)
exactBasis link = case providerCallBindingBasis link of
  ExactProviderCallBinding occurrence admission interface operation entry ->
    Right (toString occurrence, admission, interface, operation, entry)
  other -> Left ("expected exact provider binding, got " <> show other)

uploadBundle :: Either String ProviderCallStageBundle
uploadBundle = uploadProviderCallStageBundle

steveBundle :: Either String ProviderCallStageBundle
steveBundle = steveProviderCallStageBundle

digestComputeSite :: SystemsMechanismKey
digestComputeSite = SystemsMechanismKey
  "StevePut:put.entry:term.runtime-choice.DigestProvider.compute"

fromString :: String -> Data.Text.Text
fromString = Data.Text.pack

toString :: Data.Text.Text -> String
toString = Data.Text.unpack

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
