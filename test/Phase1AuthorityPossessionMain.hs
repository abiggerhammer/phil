{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.Authority
import Phil.Core.Syntax (Mode (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "AUTH-001 exact possessed capability authorizes operation" exactPossessionAccepts
    , test "AUTH-001 missing capability occurrence rejects" missingOccurrenceRejects
    , test "AUTH-001 wrong authority contract rejects" wrongContractRejects
    , test "AUTH-001 wrong authority subject rejects" wrongSubjectRejects
    , test "AUTH-001 undeclared authority operation rejects" undeclaredOperationRejects
    , test "AUTH-002 unrestricted authority may be copied" unrestrictedCopyAccepts
    , test "AUTH-002 affine authority may not be copied" affineCopyRejects
    , test "AUTH-002 linear authority may not be copied" linearCopyRejects
    , test "AUTH-002 affine authority may be dropped" affineDropAccepts
    , test "AUTH-002 linear authority may not be dropped" linearDropRejects
    , test "AUTH-005 import does not grant authority" importedDeclarationRejects
    , test "AUTH-005 effect permission does not grant authority" effectPermissionRejects
    , test "AUTH-005 runtime handle does not grant authority" runtimeHandleRejects
    , test "AUTH-005 backend symbol does not grant authority" backendSymbolRejects
    , test "AUTH-005 ambient registry entry does not grant authority" ambientRegistryRejects
    , test "AUTH-005 runtime identity cannot repair wrong semantic subject" runtimeCoincidenceCannotRepairSubject
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactPossessionAccepts :: Either String ()
exactPossessionAccepts = do
  checked <- mapLeft show $ checkAuthorityExercise readRequirement
    (PossessedCapability linearReadOccurrence)
    baseState
  assert
    (authorityCapabilityOccurrence (checkedAuthorityCapability checked) == linearReadOccurrence)
    "accepted exercise changed capability occurrence"

missingOccurrenceRejects :: Either String ()
missingOccurrenceRejects =
  case checkAuthorityExercise readRequirement
      (PossessedCapability missingOccurrence)
      baseState of
    Left (UnknownCapabilityOccurrence key) ->
      assert (key == missingOccurrence) "wrong missing occurrence diagnostic"
    other -> Left ("missing capability occurrence did not reject: " <> show other)

wrongContractRejects :: Either String ()
wrongContractRejects =
  case checkAuthorityExercise wrongContractRequirement
      (PossessedCapability linearReadOccurrence)
      baseState of
    Left (AuthorityContractMismatch expected actual) -> do
      assert (expected == adminContract) "wrong expected authority contract"
      assert (actual == storageContract) "wrong actual authority contract"
    other -> Left ("wrong authority contract did not reject: " <> show other)

wrongSubjectRejects :: Either String ()
wrongSubjectRejects =
  case checkAuthorityExercise wrongSubjectRequirement
      (PossessedCapability linearReadOccurrence)
      baseState of
    Left (AuthoritySubjectMismatch expected actual) -> do
      assert (expected == blobTwo) "wrong expected authority subject"
      assert (actual == blobOne) "wrong actual authority subject"
    other -> Left ("wrong authority subject did not reject: " <> show other)

undeclaredOperationRejects :: Either String ()
undeclaredOperationRejects =
  case checkAuthorityExercise deleteRequirement
      (PossessedCapability linearReadOccurrence)
      baseState of
    Left (AuthorityOperationNotPermitted operation) ->
      assert (operation == deleteOperation) "wrong undeclared operation diagnostic"
    other -> Left ("undeclared authority operation did not reject: " <> show other)

unrestrictedCopyAccepts :: Either String ()
unrestrictedCopyAccepts = do
  next <- mapLeft show $ copyAuthorityCapability unrestrictedReadOccurrence copiedOccurrence baseState
  copied <- maybe
    (Left "unrestricted copy did not create target occurrence")
    Right
    (lookupAuthorityCapability copiedOccurrence next)
  original <- maybe
    (Left "unrestricted copy consumed predecessor")
    Right
    (lookupAuthorityCapability unrestrictedReadOccurrence next)
  assert (authorityCapabilityContract copied == authorityCapabilityContract original)
    "copy changed authority contract"
  assert (authorityCapabilitySubject copied == authorityCapabilitySubject original)
    "copy changed authority subject"
  assert (authorityCapabilityOperations copied == authorityCapabilityOperations original)
    "copy changed authority operation set"

affineCopyRejects :: Either String ()
affineCopyRejects =
  case copyAuthorityCapability affineReadOccurrence copiedOccurrence baseState of
    Left (RestrictedCapabilityCopy key Affine) ->
      assert (key == affineReadOccurrence) "wrong affine copy predecessor"
    other -> Left ("affine authority copy did not reject: " <> show other)

linearCopyRejects :: Either String ()
linearCopyRejects =
  case copyAuthorityCapability linearReadOccurrence copiedOccurrence baseState of
    Left (RestrictedCapabilityCopy key Linear) ->
      assert (key == linearReadOccurrence) "wrong linear copy predecessor"
    other -> Left ("linear authority copy did not reject: " <> show other)

affineDropAccepts :: Either String ()
affineDropAccepts = do
  next <- mapLeft show $ dropAuthorityCapability affineReadOccurrence baseState
  assert
    (lookupAuthorityCapability affineReadOccurrence next == Nothing)
    "affine authority remained after legal drop"

linearDropRejects :: Either String ()
linearDropRejects =
  case dropAuthorityCapability linearReadOccurrence baseState of
    Left (LinearCapabilityDrop key) ->
      assert (key == linearReadOccurrence) "wrong linear drop occurrence"
    other -> Left ("linear authority drop did not reject: " <> show other)

importedDeclarationRejects :: Either String ()
importedDeclarationRejects =
  expectNonPossession (ImportedAuthorityDeclaration storageContract)

effectPermissionRejects :: Either String ()
effectPermissionRejects =
  expectNonPossession (EffectPermissionOnly "read")

runtimeHandleRejects :: Either String ()
runtimeHandleRejects =
  expectNonPossession (RuntimeAuthorityHandle "fd:7")

backendSymbolRejects :: Either String ()
backendSymbolRejects =
  expectNonPossession (BackendAuthoritySymbol "phil_storage_read")

ambientRegistryRejects :: Either String ()
ambientRegistryRejects =
  expectNonPossession (AmbientAuthorityRegistryEntry "default-storage-provider")

runtimeCoincidenceCannotRepairSubject :: Either String ()
runtimeCoincidenceCannotRepairSubject = do
  expectNonPossession (RuntimeAuthorityHandle "fd:7")
  wrongSubjectRejects

expectNonPossession :: AuthorityExerciseSource -> Either String ()
expectNonPossession source =
  case checkAuthorityExercise readRequirement source baseState of
    Left (AuthoritySourceIsNotPossession actual) ->
      assert (actual == source) "non-possession diagnostic changed source"
    other -> Left ("non-possession source was treated as authority: " <> show other)

storageContract, adminContract :: AuthorityContractKey
storageContract = AuthorityContractKey "authority.storage.read.v1"
adminContract = AuthorityContractKey "authority.storage.admin.v1"

blobOne, blobTwo :: AuthoritySubjectKey
blobOne = AuthoritySubjectKey "blob.001"
blobTwo = AuthoritySubjectKey "blob.002"

readOperation, deleteOperation :: AuthorityOperationKey
readOperation = AuthorityOperationKey "read"
deleteOperation = AuthorityOperationKey "delete"

readRequirement, wrongContractRequirement, wrongSubjectRequirement,
  deleteRequirement :: AuthorityRequirement
readRequirement = AuthorityRequirement storageContract blobOne readOperation
wrongContractRequirement = AuthorityRequirement adminContract blobOne readOperation
wrongSubjectRequirement = AuthorityRequirement storageContract blobTwo readOperation
deleteRequirement = AuthorityRequirement storageContract blobOne deleteOperation

linearReadOccurrence, affineReadOccurrence, unrestrictedReadOccurrence,
  copiedOccurrence, missingOccurrence :: CapabilityOccurrenceKey
linearReadOccurrence = CapabilityOccurrenceKey "cap.linear.read.001"
affineReadOccurrence = CapabilityOccurrenceKey "cap.affine.read.001"
unrestrictedReadOccurrence = CapabilityOccurrenceKey "cap.unrestricted.read.001"
copiedOccurrence = CapabilityOccurrenceKey "cap.copy.001"
missingOccurrence = CapabilityOccurrenceKey "cap.missing"

linearCapability, affineCapability, unrestrictedCapability :: AuthorityCapability
linearCapability = capability linearReadOccurrence Linear
affineCapability = capability affineReadOccurrence Affine
unrestrictedCapability = capability unrestrictedReadOccurrence Unrestricted

capability :: CapabilityOccurrenceKey -> Mode -> AuthorityCapability
capability occurrence mode = AuthorityCapability
  { authorityCapabilityOccurrence = occurrence
  , authorityCapabilityContract = storageContract
  , authorityCapabilitySubject = blobOne
  , authorityCapabilityMode = mode
  , authorityCapabilityOperations = Set.singleton readOperation
  }

baseState :: AuthorityState
baseState = foldInsert [linearCapability, affineCapability, unrestrictedCapability]

foldInsert :: [AuthorityCapability] -> AuthorityState
foldInsert = foldl insertOne emptyAuthorityState
  where
    insertOne state capabilityValue =
      case insertAuthorityCapability capabilityValue state of
        Right next -> next
        Left err -> error (show err)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
