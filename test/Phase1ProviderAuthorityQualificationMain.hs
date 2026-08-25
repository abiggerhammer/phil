{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Authority
import Phil.Core.AuthorityAttenuation
import Phil.Core.AuthorityConfinement
import Phil.Core.ProviderAuthorityQualification
import Phil.Core.ProviderQualification
import Phil.Core.Static (DefinitionRevision (..), InterfaceRevision (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "PROV-009 pure Phil rich internals accept with checked static confinement"
        pureStaticConfinementAccepts
    , test "PROV-009 provider public surface cannot omit statically exposed authority"
        staticPublicEscapeRejects
    , test "PROV-009 provider internal inventory cannot omit statically reachable authority"
        staticReachabilityUnderreportRejects
    , test "PROV-009 every extra internal authority grant needs an exact disposition"
        missingExtraDispositionRejects
    , test "PROV-009 dispositions cannot be invented for non-extra authority"
        unexpectedDispositionRejects
    , test "PROV-009 static confinement must actually cover the extra authority"
        unavailableStaticConfinementRejects
    , test "AUTH-006 foreign authority accepts with explicit external confinement evidence"
        foreignExternalConfinementAccepts
    , test "AUTH-006 foreign authority may remain an explicit assumption"
        foreignAssumptionAccepts
    , test "AUTH-006 foreign authority may remain an explicit TCB boundary"
        foreignTcbBoundaryAccepts
    , test "AUTH-006 ABI shape cannot establish a complete foreign authority inventory"
        foreignAbiInventoryRejects
    , test "AUTH-006 opaque foreign code cannot claim pure-Phil inventory checking"
        foreignPureInventoryRejects
    , test "AUTH-006 ABI absence is not per-grant confinement evidence"
        foreignAbiDispositionRejects
    , test "AUTH-006 opaque foreign authority cannot use static Phil confinement"
        foreignStaticDispositionRejects
    , test "PROV-009 semantic authority qualification is bound to exact provider revisions"
        semanticRevisionMismatchRejects
    , test "PROV-009 subject-specific authority grants remain distinct"
        subjectSpecificAuthorityIsDistinct
    , test "PROV-009 disposition map ordering is nonsemantic"
        dispositionOrderingIsCanonical
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

pureStaticConfinementAccepts :: Either String ()
pureStaticConfinementAccepts = do
  closure <- checkedReadOnlyClosure
  let spec = pureSpec closure
  checked <- mapLeft show $ checkProviderAuthorityQualification
    (Just checkedSemanticProvider)
    spec
  assert (checkedProviderAuthorityExtra checked == Set.singleton deleteUse)
    "wrong extra internal authority set"
  assert (checkedProviderAuthorityStaticReachable checked == readDeleteUses)
    "static reachability was not retained"

staticPublicEscapeRejects :: Either String ()
staticPublicEscapeRejects = do
  closure <- checkedReadOnlyClosure
  let spec = (pureSpec closure)
        { providerAuthorityClientVisible = Set.empty
        , providerAuthorityExtraDispositions = Map.fromList
            [ (readUse, ExtraAuthorityStaticallyConfined)
            , (deleteUse, ExtraAuthorityStaticallyConfined)
            ]
        }
  case checkProviderAuthorityQualification (Just checkedSemanticProvider) spec of
    Left (ProviderAuthorityStaticPublicEscape excess) ->
      assert (excess == Set.singleton readUse) "wrong static public escape set"
    other -> Left ("statically exposed authority was omitted from provider surface: " <> show other)

staticReachabilityUnderreportRejects :: Either String ()
staticReachabilityUnderreportRejects = do
  closure <- checkedReadOnlyClosure
  let spec = (pureSpec closure)
        { providerAuthorityInternal = Set.singleton readUse
        , providerAuthorityExtraDispositions = Map.empty
        }
  case checkProviderAuthorityQualification (Just checkedSemanticProvider) spec of
    Left (ProviderAuthorityStaticReachabilityUnderreported missing) ->
      assert (missing == Set.singleton deleteUse) "wrong underreported authority set"
    other -> Left ("statically reachable authority was silently omitted: " <> show other)

missingExtraDispositionRejects :: Either String ()
missingExtraDispositionRejects = do
  closure <- checkedReadOnlyClosure
  let spec = (pureSpec closure) { providerAuthorityExtraDispositions = Map.empty }
  case checkProviderAuthorityQualification (Just checkedSemanticProvider) spec of
    Left (ProviderAuthorityMissingExtraDispositions missing) ->
      assert (missing == Set.singleton deleteUse) "wrong missing disposition set"
    other -> Left ("extra authority without disposition was accepted: " <> show other)

unexpectedDispositionRejects :: Either String ()
unexpectedDispositionRejects = do
  closure <- checkedReadOnlyClosure
  let spec = (pureSpec closure)
        { providerAuthorityExtraDispositions = Map.fromList
            [ (deleteUse, ExtraAuthorityStaticallyConfined)
            , (readUse, ExtraAuthorityStaticallyConfined)
            ]
        }
  case checkProviderAuthorityQualification (Just checkedSemanticProvider) spec of
    Left (ProviderAuthorityUnexpectedExtraDispositions unexpected) ->
      assert (unexpected == Set.singleton readUse) "wrong unexpected disposition set"
    other -> Left ("disposition for non-extra authority was accepted: " <> show other)

unavailableStaticConfinementRejects :: Either String ()
unavailableStaticConfinementRejects = do
  closure <- checkedReadOnlyClosure
  let spec = (pureSpec closure)
        { providerAuthorityInternal = Set.insert networkUse readDeleteUses
        , providerAuthorityExtraDispositions = Map.fromList
            [ (deleteUse, ExtraAuthorityStaticallyConfined)
            , (networkUse, ExtraAuthorityStaticallyConfined)
            ]
        }
  case checkProviderAuthorityQualification (Just checkedSemanticProvider) spec of
    Left (ProviderAuthorityStaticConfinementUnavailable authority) ->
      assert (authority == networkUse) "wrong unsupported static confinement authority"
    other -> Left ("authority absent from static confinement was accepted: " <> show other)

foreignExternalConfinementAccepts :: Either String ()
foreignExternalConfinementAccepts = do
  let spec = foreignSpec
        (ForeignAuthorityInventoryByEvidence foreignInventoryEvidence)
        (Map.singleton deleteUse (ExtraAuthorityExternallyConfined sandboxEvidence))
  checked <- mapLeft show $ checkProviderAuthorityQualification Nothing spec
  assert (checkedProviderAuthorityExtra checked == Set.singleton deleteUse)
    "foreign extra authority set changed"

foreignAssumptionAccepts :: Either String ()
foreignAssumptionAccepts = do
  let spec = foreignSpec
        (ForeignAuthorityInventoryAssumption ambientInventoryAssumption)
        (Map.singleton deleteUse (ExtraAuthorityAssumptionDependent deleteAssumption))
  _ <- mapLeft show $ checkProviderAuthorityQualification Nothing spec
  Right ()

foreignTcbBoundaryAccepts :: Either String ()
foreignTcbBoundaryAccepts = do
  let spec = foreignSpec
        (ForeignAuthorityInventoryTcbBoundary runtimeTcb)
        (Map.singleton deleteUse (ExtraAuthorityTcbBoundary runtimeTcb))
  _ <- mapLeft show $ checkProviderAuthorityQualification Nothing spec
  Right ()

foreignAbiInventoryRejects :: Either String ()
foreignAbiInventoryRejects =
  let spec = ProviderAuthorityQualificationSpec
        { providerAuthoritySubject = foreignSubject
        , providerAuthorityInventoryBasis = ForeignAuthorityInventoryFromAbiShape foreignAbi
        , providerAuthorityClientVisible = Set.empty
        , providerAuthorityInternal = Set.empty
        , providerAuthorityPurePhilConfinements = []
        , providerAuthorityExtraDispositions = Map.empty
        }
  in case checkProviderAuthorityQualification Nothing spec of
      Left (ProviderAuthorityAbiInventoryIsNotEvidence abi) ->
        assert (abi == foreignAbi) "wrong ABI inventory diagnostic"
      other -> Left ("empty foreign authority inventory was trusted from ABI shape: " <> show other)

foreignPureInventoryRejects :: Either String ()
foreignPureInventoryRejects =
  let spec = foreignSpec
        (CheckedPurePhilAuthorityInventory pureInventoryRevision)
        (Map.singleton deleteUse (ExtraAuthorityExternallyConfined sandboxEvidence))
  in case checkProviderAuthorityQualification Nothing spec of
      Left (ProviderAuthorityForeignInventoryRequiresEvidenceOrBoundary basis) ->
        assert (basis == CheckedPurePhilAuthorityInventory pureInventoryRevision)
          "wrong foreign inventory-basis diagnostic"
      other -> Left ("opaque foreign code accepted pure-Phil inventory basis: " <> show other)

foreignAbiDispositionRejects :: Either String ()
foreignAbiDispositionRejects =
  let spec = foreignSpec
        (ForeignAuthorityInventoryByEvidence foreignInventoryEvidence)
        (Map.singleton deleteUse (ExtraAuthorityAssertedAbsentFromAbi foreignAbi))
  in case checkProviderAuthorityQualification Nothing spec of
      Left (ProviderAuthorityAbiAbsenceIsNotConfinement authority abi) -> do
        assert (authority == deleteUse) "wrong ABI-absence authority"
        assert (abi == foreignAbi) "wrong ABI-absence shape"
      other -> Left ("ABI omission was accepted as confinement evidence: " <> show other)

foreignStaticDispositionRejects :: Either String ()
foreignStaticDispositionRejects =
  let spec = foreignSpec
        (ForeignAuthorityInventoryByEvidence foreignInventoryEvidence)
        (Map.singleton deleteUse ExtraAuthorityStaticallyConfined)
  in case checkProviderAuthorityQualification Nothing spec of
      Left (ProviderAuthorityStaticConfinementInvalidForOpaque authority) ->
        assert (authority == deleteUse) "wrong opaque static-confinement authority"
      other -> Left ("opaque foreign authority used static Phil confinement: " <> show other)

semanticRevisionMismatchRejects :: Either String ()
semanticRevisionMismatchRejects = do
  closure <- checkedReadOnlyClosure
  let wrongSubject = SemanticProviderAuthoritySubject
        (InterfaceRevision "provider.blob.v2")
        (DefinitionRevision "provider.blob.impl.v1")
      spec = (pureSpec closure) { providerAuthoritySubject = wrongSubject }
  case checkProviderAuthorityQualification (Just checkedSemanticProvider) spec of
    Left (ProviderAuthoritySemanticSubjectRevisionMismatch subject expectedInterface expectedDefinition) -> do
      assert (subject == wrongSubject) "wrong mismatched semantic subject"
      assert (expectedInterface == InterfaceRevision "provider.blob.v1")
        "wrong expected provider interface"
      assert (expectedDefinition == DefinitionRevision "provider.blob.impl.v1")
        "wrong expected provider implementation"
    other -> Left ("authority qualification ignored provider revision mismatch: " <> show other)

subjectSpecificAuthorityIsDistinct :: Either String ()
subjectSpecificAuthorityIsDistinct = do
  closure <- checkedReadOnlyClosure
  let otherDelete = AuthorityUse secondarySubject deleteOperation
      spec = (pureSpec closure)
        { providerAuthorityInternal = Set.insert otherDelete readDeleteUses
        , providerAuthorityExtraDispositions = Map.fromList
            [ (deleteUse, ExtraAuthorityStaticallyConfined)
            , (otherDelete, ExtraAuthorityExternallyConfined sandboxEvidence)
            ]
        }
  checked <- mapLeft show $ checkProviderAuthorityQualification
    (Just checkedSemanticProvider) spec
  assert (checkedProviderAuthorityExtra checked == Set.fromList [deleteUse, otherDelete])
    "authority subjects collapsed during qualification"

dispositionOrderingIsCanonical :: Either String ()
dispositionOrderingIsCanonical = do
  closure <- checkedReadOnlyClosure
  let extraNetwork = networkUse
      internal = Set.insert extraNetwork readDeleteUses
      left = Map.fromList
        [ (deleteUse, ExtraAuthorityStaticallyConfined)
        , (extraNetwork, ExtraAuthorityExternallyConfined sandboxEvidence)
        ]
      right = Map.fromList
        [ (extraNetwork, ExtraAuthorityExternallyConfined sandboxEvidence)
        , (deleteUse, ExtraAuthorityStaticallyConfined)
        ]
      base = (pureSpec closure) { providerAuthorityInternal = internal }
  checkedLeft <- mapLeft show $ checkProviderAuthorityQualification
    (Just checkedSemanticProvider) (base { providerAuthorityExtraDispositions = left })
  checkedRight <- mapLeft show $ checkProviderAuthorityQualification
    (Just checkedSemanticProvider) (base { providerAuthorityExtraDispositions = right })
  assert (checkedLeft == checkedRight) "disposition insertion order changed qualification"

checkedReadOnlyClosure :: Either String CheckedClosureAuthorityConfinement
checkedReadOnlyClosure = mapLeft show $ checkClosureAuthorityConfinement
  ClosureAuthorityConfinementSpec
    { closureReachableAuthority =
        [ ReachableAuthorityGrant
            (OtherAuthorityReachabilityOrigin "provider.internal.storage")
            broadStorageSurface
        ]
    , closurePublicMediatedAuthority = Set.singleton readUse
    , closureExercisedAuthority = Set.singleton readUse
    }

pureSpec :: CheckedClosureAuthorityConfinement -> ProviderAuthorityQualificationSpec
pureSpec closure = ProviderAuthorityQualificationSpec
  { providerAuthoritySubject = semanticProviderAuthoritySubject checkedSemanticProvider
  , providerAuthorityInventoryBasis = CheckedPurePhilAuthorityInventory pureInventoryRevision
  , providerAuthorityClientVisible = Set.singleton readUse
  , providerAuthorityInternal = readDeleteUses
  , providerAuthorityPurePhilConfinements = [closure]
  , providerAuthorityExtraDispositions =
      Map.singleton deleteUse ExtraAuthorityStaticallyConfined
  }

foreignSpec
  :: ProviderAuthorityInventoryBasis
  -> Map.Map AuthorityUse ProviderExtraAuthorityDisposition
  -> ProviderAuthorityQualificationSpec
foreignSpec inventoryBasis dispositions = ProviderAuthorityQualificationSpec
  { providerAuthoritySubject = foreignSubject
  , providerAuthorityInventoryBasis = inventoryBasis
  , providerAuthorityClientVisible = Set.singleton readUse
  , providerAuthorityInternal = readDeleteUses
  , providerAuthorityPurePhilConfinements = []
  , providerAuthorityExtraDispositions = dispositions
  }

checkedSemanticProvider :: CheckedProviderSemanticQualification
checkedSemanticProvider = CheckedProviderSemanticQualification
  { checkedProviderContractRevision = InterfaceRevision "provider.blob.v1"
  , checkedProviderImplementationRevision = DefinitionRevision "provider.blob.impl.v1"
  , checkedProviderOperations = Map.empty
  }

foreignSubject :: ProviderAuthoritySubject
foreignSubject = OpaqueForeignProviderAuthoritySubject
  (InterfaceRevision "provider.blob.v1")
  (OpaqueProviderBoundaryKey "artifact.libblob.sha256:abc123")

pureInventoryRevision :: ProviderAuthorityInventoryRevision
pureInventoryRevision = ProviderAuthorityInventoryRevision "authority-inventory.blob.impl.v1"

foreignInventoryEvidence, sandboxEvidence :: ProviderAuthorityConfinementEvidenceKey
foreignInventoryEvidence = ProviderAuthorityConfinementEvidenceKey "evidence.foreign-authority-inventory.v1"
sandboxEvidence = ProviderAuthorityConfinementEvidenceKey "evidence.sandbox-no-delete-escape.v1"

ambientInventoryAssumption, deleteAssumption :: ProviderAuthorityAssumptionKey
ambientInventoryAssumption = ProviderAuthorityAssumptionKey "assume.runtime-authority-inventory-complete.v1"
deleteAssumption = ProviderAuthorityAssumptionKey "assume.delete-authority-confined.v1"

runtimeTcb :: ProviderAuthorityTcbBoundaryKey
runtimeTcb = ProviderAuthorityTcbBoundaryKey "tcb.runtime.provider-sandbox.v1"

foreignAbi :: ProviderAuthorityAbiShapeKey
foreignAbi = ProviderAuthorityAbiShapeKey "abi.blob-provider.v1"

primarySubject, secondarySubject :: AuthoritySubjectKey
primarySubject = AuthoritySubjectKey "blob-store.primary"
secondarySubject = AuthoritySubjectKey "blob-store.secondary"

readOperation, deleteOperation, networkOperation :: AuthorityOperationKey
readOperation = AuthorityOperationKey "read"
deleteOperation = AuthorityOperationKey "delete"
networkOperation = AuthorityOperationKey "network-connect"

readUse, deleteUse, networkUse :: AuthorityUse
readUse = AuthorityUse primarySubject readOperation
deleteUse = AuthorityUse primarySubject deleteOperation
networkUse = AuthorityUse primarySubject networkOperation

readDeleteUses :: Set.Set AuthorityUse
readDeleteUses = Set.fromList [readUse, deleteUse]

broadStorageSurface :: AuthoritySurface
broadStorageSurface = AuthoritySurface
  { authoritySurfaceContract = AuthorityContractKey "storage.read-delete.v1"
  , authoritySurfaceSubject = primarySubject
  , authoritySurfaceOperations = Set.fromList [readOperation, deleteOperation]
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
