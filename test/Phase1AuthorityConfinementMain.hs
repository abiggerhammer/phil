{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.Authority
import Phil.Core.AuthorityAttenuation
import Phil.Core.AuthorityConfinement
import Phil.Core.Callable (CallableOccurrenceKey (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "AUTH-004 broader captured authority may expose narrower behavior" narrowBehaviorAccepts
    , test "AUTH-004 false negative-authority claim sees hidden captured authority" falseNegativeClaimRejects
    , test "AUTH-004 genuinely absent authority can be proved absent" absentAuthorityClaimAccepts
    , test "AUTH-004 exercising hidden authority exceeds public confinement" hiddenExerciseRejects
    , test "AUTH-004 exercising unreachable authority rejects" unreachableExerciseRejects
    , test "AUTH-004 public mediated authority must be reachable" unsupportedPublicAuthorityRejects
    , test "AUTH-004 captured callable authority participates in reachability" capturedCallableAuthorityCounts
    , test "AUTH-004 negative claims are subject specific" subjectSpecificNegativeClaim
    , test "AUTH-004 duplicate reachable grants canonicalize" duplicateReachabilityCanonicalizes
    , test "AUTH-004 grant ordering is nonsemantic" grantOrderingIsNonsemantic
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

narrowBehaviorAccepts :: Either String ()
narrowBehaviorAccepts = do
  checked <- mapLeft show $ checkClosureAuthorityConfinement baselineSpec
  assert (checkedClosureReachableAuthority checked == broadReachableUses)
    "checked reachability lost captured delete authority"
  assert (checkedClosurePublicMediatedAuthority checked == readPublicUses)
    "checked public authority changed"
  assert (checkedClosureExercisedAuthority checked == readPublicUses)
    "checked exercised authority changed"

falseNegativeClaimRejects :: Either String ()
falseNegativeClaimRejects = do
  checked <- mapLeft show $ checkClosureAuthorityConfinement baselineSpec
  case checkNegativeAuthorityClaim checked deletePrimaryClaim of
    Left (NegativeAuthorityClaimFalse claim origins) -> do
      assert (claim == deletePrimaryClaim) "negative claim diagnostic changed claim"
      assert (origins == Set.singleton (CapturedCapabilityOrigin storageCapabilityOccurrence))
        "negative claim did not identify captured capability origin"
    other -> Left ("false delete-absence claim did not reject: " <> show other)

absentAuthorityClaimAccepts :: Either String ()
absentAuthorityClaimAccepts = do
  checked <- mapLeft show $ checkClosureAuthorityConfinement baselineSpec
  proof <- mapLeft show $ checkNegativeAuthorityClaim checked writePrimaryClaim
  assert (checkedNegativeAuthorityClaim proof == writePrimaryClaim)
    "accepted negative claim changed identity"
  assert (checkedNegativeAuthorityReachableSet proof == broadReachableUses)
    "negative claim proof lost reachable authority set"

hiddenExerciseRejects :: Either String ()
hiddenExerciseRejects =
  let spec = baselineSpec
        { closureExercisedAuthority = Set.fromList [readPrimaryUse, deletePrimaryUse] }
  in case checkClosureAuthorityConfinement spec of
      Left (ClosureExercisedAuthorityExceedsPublic excess) ->
        assert (excess == Set.singleton deletePrimaryUse)
          "hidden-authority exercise reported wrong excess"
      other -> Left ("hidden delete exercise did not reject: " <> show other)

unreachableExerciseRejects :: Either String ()
unreachableExerciseRejects =
  let spec = baselineSpec
        { closureExercisedAuthority = Set.fromList [readPrimaryUse, writePrimaryUse] }
  in case checkClosureAuthorityConfinement spec of
      Left (ClosureExercisedAuthorityNotReachable excess) ->
        assert (excess == Set.singleton writePrimaryUse)
          "unreachable exercise reported wrong authority"
      other -> Left ("unreachable write exercise did not reject: " <> show other)

unsupportedPublicAuthorityRejects :: Either String ()
unsupportedPublicAuthorityRejects =
  let spec = baselineSpec
        { closurePublicMediatedAuthority = Set.fromList [readPrimaryUse, writePrimaryUse]
        , closureExercisedAuthority = Set.singleton readPrimaryUse
        }
  in case checkClosureAuthorityConfinement spec of
      Left (ClosurePublicAuthorityNotReachable excess) ->
        assert (excess == Set.singleton writePrimaryUse)
          "unsupported public authority reported wrong excess"
      other -> Left ("unreachable public write authority did not reject: " <> show other)

capturedCallableAuthorityCounts :: Either String ()
capturedCallableAuthorityCounts = do
  let spec = ClosureAuthorityConfinementSpec
        { closureReachableAuthority =
            [ ReachableAuthorityGrant
                (CapturedCapabilityOrigin storageCapabilityOccurrence)
                readOnlySurface
            , ReachableAuthorityGrant
                (CapturedCallableOrigin deleteCallableOccurrence)
                deleteOnlySurface
            ]
        , closurePublicMediatedAuthority = readPublicUses
        , closureExercisedAuthority = readPublicUses
        }
  checked <- mapLeft show $ checkClosureAuthorityConfinement spec
  case checkNegativeAuthorityClaim checked deletePrimaryClaim of
    Left (NegativeAuthorityClaimFalse _ origins) ->
      assert (origins == Set.singleton (CapturedCallableOrigin deleteCallableOccurrence))
        "captured callable authority was not retained in negative analysis"
    other -> Left ("captured callable delete authority was ignored: " <> show other)

subjectSpecificNegativeClaim :: Either String ()
subjectSpecificNegativeClaim = do
  let spec = ClosureAuthorityConfinementSpec
        { closureReachableAuthority =
            [ ReachableAuthorityGrant
                (CapturedCapabilityOrigin storageCapabilityOccurrence)
                readOnlySurface
            , ReachableAuthorityGrant
                (CapturedCapabilityOrigin secondaryDeleteCapabilityOccurrence)
                secondaryDeleteSurface
            ]
        , closurePublicMediatedAuthority = readPublicUses
        , closureExercisedAuthority = readPublicUses
        }
  checked <- mapLeft show $ checkClosureAuthorityConfinement spec
  _ <- mapLeft show $ checkNegativeAuthorityClaim checked deletePrimaryClaim
  case checkNegativeAuthorityClaim checked deleteSecondaryClaim of
    Left (NegativeAuthorityClaimFalse _ origins) ->
      assert (origins == Set.singleton
        (CapturedCapabilityOrigin secondaryDeleteCapabilityOccurrence))
        "secondary-subject negative claim reported wrong origin"
    other -> Left ("secondary delete authority was not detected: " <> show other)

duplicateReachabilityCanonicalizes :: Either String ()
duplicateReachabilityCanonicalizes = do
  let duplicateSpec = baselineSpec
        { closureReachableAuthority = broadCapturedGrants <> broadCapturedGrants }
  left <- mapLeft show $ checkClosureAuthorityConfinement baselineSpec
  right <- mapLeft show $ checkClosureAuthorityConfinement duplicateSpec
  assert (checkedClosureReachableAuthority left == checkedClosureReachableAuthority right)
    "duplicate reachability changed semantic reachable set"

grantOrderingIsNonsemantic :: Either String ()
grantOrderingIsNonsemantic = do
  let callableGrant = ReachableAuthorityGrant
        (CapturedCallableOrigin deleteCallableOccurrence)
        deleteOnlySurface
      capabilityGrant = ReachableAuthorityGrant
        (CapturedCapabilityOrigin storageCapabilityOccurrence)
        readOnlySurface
      leftSpec = ClosureAuthorityConfinementSpec
        [capabilityGrant, callableGrant]
        readPublicUses
        readPublicUses
      rightSpec = ClosureAuthorityConfinementSpec
        [callableGrant, capabilityGrant]
        readPublicUses
        readPublicUses
  left <- mapLeft show $ checkClosureAuthorityConfinement leftSpec
  right <- mapLeft show $ checkClosureAuthorityConfinement rightSpec
  assert (checkedClosureReachableAuthority left == checkedClosureReachableAuthority right)
    "grant order changed reachable authority semantics"
  case ( checkNegativeAuthorityClaim left deletePrimaryClaim
       , checkNegativeAuthorityClaim right deletePrimaryClaim
       ) of
    (Left (NegativeAuthorityClaimFalse _ leftOrigins),
     Left (NegativeAuthorityClaimFalse _ rightOrigins)) ->
      assert (leftOrigins == rightOrigins)
        "grant order changed negative-authority origins"
    other -> Left ("canonical negative analysis failed: " <> show other)

storageCapabilityOccurrence, secondaryDeleteCapabilityOccurrence :: CapabilityOccurrenceKey
storageCapabilityOccurrence = CapabilityOccurrenceKey "cap.storage.primary"
secondaryDeleteCapabilityOccurrence = CapabilityOccurrenceKey "cap.storage.secondary-delete"

deleteCallableOccurrence :: CallableOccurrenceKey
deleteCallableOccurrence = CallableOccurrenceKey "callable.delete-helper.001"

broadContract, readContract, deleteContract :: AuthorityContractKey
broadContract = AuthorityContractKey "storage.read-delete.v1"
readContract = AuthorityContractKey "storage.read-only.v1"
deleteContract = AuthorityContractKey "storage.delete-only.v1"

primarySubject, secondarySubject :: AuthoritySubjectKey
primarySubject = AuthoritySubjectKey "store.primary"
secondarySubject = AuthoritySubjectKey "store.secondary"

readOperation, writeOperation, deleteOperation :: AuthorityOperationKey
readOperation = AuthorityOperationKey "read"
writeOperation = AuthorityOperationKey "write"
deleteOperation = AuthorityOperationKey "delete"

broadSurface, readOnlySurface, deleteOnlySurface, secondaryDeleteSurface :: AuthoritySurface
broadSurface = AuthoritySurface broadContract primarySubject
  (Set.fromList [readOperation, deleteOperation])
readOnlySurface = AuthoritySurface readContract primarySubject (Set.singleton readOperation)
deleteOnlySurface = AuthoritySurface deleteContract primarySubject (Set.singleton deleteOperation)
secondaryDeleteSurface = AuthoritySurface deleteContract secondarySubject
  (Set.singleton deleteOperation)

readPrimaryUse, writePrimaryUse, deletePrimaryUse :: AuthorityUse
readPrimaryUse = AuthorityUse primarySubject readOperation
writePrimaryUse = AuthorityUse primarySubject writeOperation
deletePrimaryUse = AuthorityUse primarySubject deleteOperation

readPublicUses, broadReachableUses :: Set.Set AuthorityUse
readPublicUses = Set.singleton readPrimaryUse
broadReachableUses = Set.fromList [readPrimaryUse, deletePrimaryUse]

broadCapturedGrants :: [ReachableAuthorityGrant]
broadCapturedGrants =
  [ ReachableAuthorityGrant
      (CapturedCapabilityOrigin storageCapabilityOccurrence)
      broadSurface
  ]

baselineSpec :: ClosureAuthorityConfinementSpec
baselineSpec = ClosureAuthorityConfinementSpec
  { closureReachableAuthority = broadCapturedGrants
  , closurePublicMediatedAuthority = readPublicUses
  , closureExercisedAuthority = readPublicUses
  }

deletePrimaryClaim, writePrimaryClaim, deleteSecondaryClaim :: NegativeAuthorityClaim
deletePrimaryClaim = NegativeAuthorityClaim primarySubject deleteOperation
writePrimaryClaim = NegativeAuthorityClaim primarySubject writeOperation
deleteSecondaryClaim = NegativeAuthorityClaim secondarySubject deleteOperation

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
