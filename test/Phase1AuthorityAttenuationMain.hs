{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.Authority
import Phil.Core.AuthorityAttenuation
import Phil.Core.Syntax (Mode (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "AUTH-003 explicit attenuation accepts narrower authority" explicitAttenuationAccepts
    , test "AUTH-003 explicit attenuation rejects widening" explicitAttenuationRejectsWidening
    , test "AUTH-003 attenuation preserves exact subject" attenuationRejectsSubjectChange
    , test "AUTH-003 attenuation witness is bound to source contract" witnessSourceMismatchRejects
    , test "AUTH-003 attenuation witness is bound to target contract" witnessTargetMismatchRejects
    , test "AUTH-003 attenuation witness is bound to subject" witnessSubjectMismatchRejects
    , test "AUTH-003 attenuation witness is bound to visible operation set" witnessOperationMismatchRejects
    , test "AUTH-003 generic binding accepts checked narrowing" genericBindingAcceptsCheckedNarrowing
    , test "AUTH-003 generic binding rejects silent widening" genericBindingRejectsWidening
    , test "AUTH-003 callable substitution rejects silent widening" callableSubstitutionRejectsWidening
    , test "AUTH-003 provider replacement rejects silent widening" providerReplacementRejectsWidening
    , test "AUTH-003 contract change without attenuation rejects" contractChangeRequiresWitness
    , test "AUTH-003 same contract cannot silently change authority surface" sameContractSurfaceChangeRejects
    , test "AUTH-003 join keeps authority common to every branch" joinKeepsCommonAuthority
    , test "AUTH-003 join never unions branch-local authority" joinDoesNotUnionAuthority
    , test "AUTH-003 join rejects subject mismatch" joinRejectsSubjectMismatch
    , test "AUTH-003 join rejects implicit contract change" joinRejectsContractChange
    , test "AUTH-003 capability projection preserves semantic surface" capabilityProjectionIsExact
    , test "AUTH-003 set ordering is nonsemantic" operationOrderingIsCanonical
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

explicitAttenuationAccepts :: Either String ()
explicitAttenuationAccepts = do
  checked <- mapLeft show $ checkExplicitAuthorityAttenuation broadSurface readSurface readWitness
  assert (checkedAuthorityAttenuationSource checked == broadSurface)
    "checked attenuation changed source surface"
  assert (checkedAuthorityAttenuationTarget checked == readSurface)
    "checked attenuation changed target surface"

explicitAttenuationRejectsWidening :: Either String ()
explicitAttenuationRejectsWidening =
  case checkExplicitAuthorityAttenuation readSurface broadSurface reverseWitness of
    Left (AuthorityAttenuationWouldWiden excess) ->
      assert (excess == Set.fromList [writeOperation, deleteOperation])
        "widening diagnostic reported wrong excess authority"
    other -> Left ("widening attenuation did not reject: " <> show other)

attenuationRejectsSubjectChange :: Either String ()
attenuationRejectsSubjectChange =
  case checkExplicitAuthorityAttenuation broadSurface otherSubjectReadSurface otherSubjectWitness of
    Left (AuthorityAttenuationSubjectMismatch expected actual) -> do
      assert (expected == blobSubject) "wrong source subject in mismatch"
      assert (actual == otherBlobSubject) "wrong target subject in mismatch"
    other -> Left ("subject-changing attenuation did not reject: " <> show other)

witnessSourceMismatchRejects :: Either String ()
witnessSourceMismatchRejects =
  let bad = readWitness { authorityAttenuationSourceContract = readContract }
  in case checkExplicitAuthorityAttenuation broadSurface readSurface bad of
    Left (AuthorityAttenuationWitnessSourceMismatch expected actual) -> do
      assert (expected == broadContract) "wrong expected witness source contract"
      assert (actual == readContract) "wrong actual witness source contract"
    other -> Left ("wrong witness source contract was accepted: " <> show other)

witnessTargetMismatchRejects :: Either String ()
witnessTargetMismatchRejects =
  let bad = readWitness { authorityAttenuationTargetContract = broadContract }
  in case checkExplicitAuthorityAttenuation broadSurface readSurface bad of
    Left (AuthorityAttenuationWitnessTargetMismatch expected actual) -> do
      assert (expected == readContract) "wrong expected witness target contract"
      assert (actual == broadContract) "wrong actual witness target contract"
    other -> Left ("wrong witness target contract was accepted: " <> show other)

witnessSubjectMismatchRejects :: Either String ()
witnessSubjectMismatchRejects =
  let bad = readWitness { authorityAttenuationSubject = otherBlobSubject }
  in case checkExplicitAuthorityAttenuation broadSurface readSurface bad of
    Left (AuthorityAttenuationWitnessSubjectMismatch expected actual) -> do
      assert (expected == blobSubject) "wrong expected witness subject"
      assert (actual == otherBlobSubject) "wrong actual witness subject"
    other -> Left ("wrong witness subject was accepted: " <> show other)

witnessOperationMismatchRejects :: Either String ()
witnessOperationMismatchRejects =
  let bad = readWitness
        { authorityAttenuationVisibleOperations = Set.fromList [readOperation, writeOperation] }
  in case checkExplicitAuthorityAttenuation broadSurface readSurface bad of
    Left (AuthorityAttenuationWitnessOperationsMismatch expected actual) -> do
      assert (expected == Set.singleton readOperation) "wrong expected visible operations"
      assert (actual == Set.fromList [readOperation, writeOperation])
        "wrong witness visible operations"
    other -> Left ("wrong witness operation set was accepted: " <> show other)

genericBindingAcceptsCheckedNarrowing :: Either String ()
genericBindingAcceptsCheckedNarrowing = do
  checked <- mapLeft show $ checkAuthorityBoundary
    AuthorityGenericBinding broadSurface readSurface (Just readWitness)
  case checkedAuthorityBoundaryAttenuation checked of
    Just attenuation -> assert
      (checkedAuthorityAttenuationTarget attenuation == readSurface)
      "generic binding lost checked attenuation"
    Nothing -> Left "generic binding accepted narrowing without recording attenuation"

genericBindingRejectsWidening :: Either String ()
genericBindingRejectsWidening =
  case checkAuthorityBoundary AuthorityGenericBinding readSurface broadSurface (Just reverseWitness) of
    Left (AuthorityAttenuationWouldWiden excess) ->
      assert (excess == Set.fromList [writeOperation, deleteOperation])
        "generic widening diagnostic reported wrong excess"
    other -> Left ("generic binding silently widened authority: " <> show other)

callableSubstitutionRejectsWidening :: Either String ()
callableSubstitutionRejectsWidening =
  case checkAuthorityBoundary AuthorityCallableSubstitution readSurface broadSurface Nothing of
    Left (AuthorityAttenuationWouldWiden _) -> Right ()
    other -> Left ("callable substitution silently widened authority: " <> show other)

providerReplacementRejectsWidening :: Either String ()
providerReplacementRejectsWidening =
  case checkAuthorityBoundary AuthorityProviderReplacement readSurface broadSurface Nothing of
    Left (AuthorityAttenuationWouldWiden _) -> Right ()
    other -> Left ("provider replacement silently widened authority: " <> show other)

contractChangeRequiresWitness :: Either String ()
contractChangeRequiresWitness =
  case checkAuthorityBoundary AuthorityArchitectureBoundary broadSurface readSurface Nothing of
    Left (AuthorityBoundaryContractChangeWithoutAttenuation kind sourceContract targetContract) -> do
      assert (kind == AuthorityArchitectureBoundary) "wrong boundary kind"
      assert (sourceContract == broadContract) "wrong source contract"
      assert (targetContract == readContract) "wrong target contract"
    other -> Left ("contract change without attenuation witness was accepted: " <> show other)

sameContractSurfaceChangeRejects :: Either String ()
sameContractSurfaceChangeRejects =
  let malformedNarrow = broadSurface
        { authoritySurfaceOperations = Set.singleton readOperation }
  in case checkAuthorityBoundary AuthorityGenericBinding broadSurface malformedNarrow Nothing of
    Left (AuthorityBoundarySameContractSurfaceMismatch kind expected actual) -> do
      assert (kind == AuthorityGenericBinding) "wrong same-contract boundary kind"
      assert (expected == broadOperations) "wrong same-contract source operations"
      assert (actual == Set.singleton readOperation) "wrong same-contract target operations"
    other -> Left ("same contract silently changed authority surface: " <> show other)

joinKeepsCommonAuthority :: Either String ()
joinKeepsCommonAuthority = do
  let left = broadSameContractSurface
      right = readWriteSameContractSurface
      joined = readSameContractSurface
  result <- mapLeft show $ checkAuthorityJoin [left, right] joined
  assert (result == joined) "join changed the declared common authority surface"

joinDoesNotUnionAuthority :: Either String ()
joinDoesNotUnionAuthority =
  let readOnly = readSameContractSurface
      writeOnly = writeSameContractSurface
      attemptedUnion = readWriteSameContractSurface
  in case checkAuthorityJoin [readOnly, writeOnly] attemptedUnion of
    Left (AuthorityJoinWouldWiden excess) ->
      assert (excess == Set.fromList [readOperation, writeOperation])
        "join-union diagnostic reported wrong authority"
    other -> Left ("join synthesized branch-local authority union: " <> show other)

joinRejectsSubjectMismatch :: Either String ()
joinRejectsSubjectMismatch =
  case checkAuthorityJoin [readSameContractSurface, otherSubjectSameContractSurface]
      readSameContractSurface of
    Left (AuthorityJoinSubjectMismatch expected actual) -> do
      assert (expected == blobSubject) "wrong joined subject"
      assert (actual == otherBlobSubject) "wrong branch subject"
    other -> Left ("join accepted mismatched semantic subjects: " <> show other)

joinRejectsContractChange :: Either String ()
joinRejectsContractChange =
  case checkAuthorityJoin [broadSurface, readSurface] readSurface of
    Left (AuthorityJoinContractChangeWithoutAttenuation source target) -> do
      assert (source == broadContract) "wrong branch contract in join mismatch"
      assert (target == readContract) "wrong joined contract in join mismatch"
    other -> Left ("join silently changed authority contract: " <> show other)

capabilityProjectionIsExact :: Either String ()
capabilityProjectionIsExact =
  let capability = AuthorityCapability
        { authorityCapabilityOccurrence = CapabilityOccurrenceKey "cap.storage.001"
        , authorityCapabilityContract = broadContract
        , authorityCapabilitySubject = blobSubject
        , authorityCapabilityMode = Linear
        , authorityCapabilityOperations = broadOperations
        }
  in assert (authoritySurfaceFromCapability capability == broadSurface)
      "capability projection changed semantic authority surface"

operationOrderingIsCanonical :: Either String ()
operationOrderingIsCanonical =
  let reorderedBroad = broadSurface
        { authoritySurfaceOperations = Set.fromList [deleteOperation, readOperation, writeOperation] }
      reorderedWitness = readWitness
        { authorityAttenuationVisibleOperations = Set.fromList [readOperation] }
  in case ( checkExplicitAuthorityAttenuation broadSurface readSurface readWitness
          , checkExplicitAuthorityAttenuation reorderedBroad readSurface reorderedWitness
          ) of
      (Right left, Right right) ->
        assert (left == right) "operation enumeration order changed attenuation semantics"
      other -> Left ("canonical attenuation comparison failed: " <> show other)

broadContract, readContract, commonContract :: AuthorityContractKey
broadContract = AuthorityContractKey "storage.read-write-delete.v1"
readContract = AuthorityContractKey "storage.read-only.v1"
commonContract = AuthorityContractKey "storage.branch-common.v1"

blobSubject, otherBlobSubject :: AuthoritySubjectKey
blobSubject = AuthoritySubjectKey "blob-store.primary"
otherBlobSubject = AuthoritySubjectKey "blob-store.secondary"

readOperation, writeOperation, deleteOperation :: AuthorityOperationKey
readOperation = AuthorityOperationKey "read"
writeOperation = AuthorityOperationKey "write"
deleteOperation = AuthorityOperationKey "delete"

broadOperations :: Set.Set AuthorityOperationKey
broadOperations = Set.fromList [readOperation, writeOperation, deleteOperation]

broadSurface, readSurface, otherSubjectReadSurface :: AuthoritySurface
broadSurface = AuthoritySurface broadContract blobSubject broadOperations
readSurface = AuthoritySurface readContract blobSubject (Set.singleton readOperation)
otherSubjectReadSurface = AuthoritySurface
  readContract otherBlobSubject (Set.singleton readOperation)

readWitness, reverseWitness, otherSubjectWitness :: AuthorityAttenuationWitness
readWitness = AuthorityAttenuationWitness
  broadContract readContract blobSubject (Set.singleton readOperation)
reverseWitness = AuthorityAttenuationWitness
  readContract broadContract blobSubject broadOperations
otherSubjectWitness = AuthorityAttenuationWitness
  broadContract readContract otherBlobSubject (Set.singleton readOperation)

broadSameContractSurface, readWriteSameContractSurface, readSameContractSurface,
  writeSameContractSurface, otherSubjectSameContractSurface :: AuthoritySurface
broadSameContractSurface = AuthoritySurface commonContract blobSubject broadOperations
readWriteSameContractSurface = AuthoritySurface commonContract blobSubject
  (Set.fromList [readOperation, writeOperation])
readSameContractSurface = AuthoritySurface commonContract blobSubject
  (Set.singleton readOperation)
writeSameContractSurface = AuthoritySurface commonContract blobSubject
  (Set.singleton writeOperation)
otherSubjectSameContractSurface = AuthoritySurface commonContract otherBlobSubject
  (Set.singleton readOperation)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
