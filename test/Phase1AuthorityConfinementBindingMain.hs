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
    [ test "AUTH-004 binding accepts confined closure" closureBindingAccepts
    , test "AUTH-004 binding rejects unreachable public authority" closureBindingRejectsUnreachablePublic
    , test "AUTH-004 binding accepts genuinely absent authority" negativeBindingAcceptsAbsent
    , test "AUTH-004 binding rejects reachable negative claim" negativeBindingRejectsReachable
    , test "PROV-009 binding accepts semantic static confinement" providerSemanticBindingAccepts
    , test "PROV-009 binding rejects semantic revision mismatch" providerRevisionBindingRejects
    , test "AUTH-006 binding accepts explicit foreign confinement evidence" providerForeignBindingAccepts
    , test "AUTH-006 binding rejects ABI inventory inference" providerAbiBindingRejects
    , test "PROV-009 binding requires exact extra-authority dispositions" providerDispositionDomainBindingRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

closureBindingAccepts :: Either String ()
closureBindingAccepts = do
  checked <- mapLeft show $ checkClosureAuthorityConfinement baselineClosureSpec
  assert (checkedClosureReachableAuthority checked == readDeleteUses)
    "bound closure lost reachable authority"

closureBindingRejectsUnreachablePublic :: Either String ()
closureBindingRejectsUnreachablePublic =
  let spec = baselineClosureSpec
        { closurePublicMediatedAuthority = Set.fromList [readUse, writeUse] }
  in case checkClosureAuthorityConfinement spec of
      Left (ClosurePublicAuthorityNotReachable excess) ->
        assert (excess == Set.singleton writeUse) "wrong unreachable public authority"
      other -> Left ("unreachable public authority did not reject: " <> show other)

negativeBindingAcceptsAbsent :: Either String ()
negativeBindingAcceptsAbsent = do
  checked <- mapLeft show $ checkClosureAuthorityConfinement baselineClosureSpec
  proof <- mapLeft show $ checkNegativeAuthorityClaim checked writeClaim
  assert (checkedNegativeAuthorityClaim proof == writeClaim)
    "accepted negative claim changed identity"

negativeBindingRejectsReachable :: Either String ()
negativeBindingRejectsReachable = do
  checked <- mapLeft show $ checkClosureAuthorityConfinement baselineClosureSpec
  case checkNegativeAuthorityClaim checked deleteClaim of
    Left (NegativeAuthorityClaimFalse claim origins) -> do
      assert (claim == deleteClaim) "negative-claim diagnostic changed identity"
      assert (origins == Set.singleton storageOrigin)
        "negative-claim diagnostic lost exact reachability origin"
    other -> Left ("reachable negative claim did not reject: " <> show other)

providerSemanticBindingAccepts :: Either String ()
providerSemanticBindingAccepts = do
  closure <- checkedClosure
  checked <- mapLeft show $ checkProviderAuthorityQualification
    (Just checkedSemanticProvider)
    (pureProviderSpec closure)
  assert (checkedProviderAuthorityExtra checked == Set.singleton deleteUse)
    "bound provider changed exact extra-authority set"

providerRevisionBindingRejects :: Either String ()
providerRevisionBindingRejects = do
  closure <- checkedClosure
  let wrongSubject = SemanticProviderAuthoritySubject
        (InterfaceRevision "provider.binding.v2")
        (DefinitionRevision "provider.binding.impl.v1")
      spec = (pureProviderSpec closure) { providerAuthoritySubject = wrongSubject }
  case checkProviderAuthorityQualification (Just checkedSemanticProvider) spec of
    Left (ProviderAuthoritySemanticSubjectRevisionMismatch subject _ _) ->
      assert (subject == wrongSubject) "wrong semantic revision mismatch subject"
    other -> Left ("semantic revision mismatch did not reject: " <> show other)

providerForeignBindingAccepts :: Either String ()
providerForeignBindingAccepts = do
  checked <- mapLeft show $ checkProviderAuthorityQualification Nothing foreignProviderSpec
  assert (checkedProviderAuthorityExtra checked == Set.singleton deleteUse)
    "bound foreign provider changed extra-authority set"

providerAbiBindingRejects :: Either String ()
providerAbiBindingRejects =
  let spec = foreignProviderSpec
        { providerAuthorityInventoryBasis = ForeignAuthorityInventoryFromAbiShape foreignAbi }
  in case checkProviderAuthorityQualification Nothing spec of
      Left (ProviderAuthorityAbiInventoryIsNotEvidence abi) ->
        assert (abi == foreignAbi) "wrong ABI-inventory diagnostic"
      other -> Left ("ABI inventory inference did not reject: " <> show other)

providerDispositionDomainBindingRejects :: Either String ()
providerDispositionDomainBindingRejects = do
  closure <- checkedClosure
  let spec = (pureProviderSpec closure) { providerAuthorityExtraDispositions = Map.empty }
  case checkProviderAuthorityQualification (Just checkedSemanticProvider) spec of
    Left (ProviderAuthorityMissingExtraDispositions missing) ->
      assert (missing == Set.singleton deleteUse) "wrong missing-disposition set"
    other -> Left ("missing extra-authority disposition did not reject: " <> show other)

checkedClosure :: Either String CheckedClosureAuthorityConfinement
checkedClosure = mapLeft show $ checkClosureAuthorityConfinement baselineClosureSpec

baselineClosureSpec :: ClosureAuthorityConfinementSpec
baselineClosureSpec = ClosureAuthorityConfinementSpec
  { closureReachableAuthority =
      [ ReachableAuthorityGrant storageOrigin broadSurface ]
  , closurePublicMediatedAuthority = Set.singleton readUse
  , closureExercisedAuthority = Set.singleton readUse
  }

pureProviderSpec :: CheckedClosureAuthorityConfinement -> ProviderAuthorityQualificationSpec
pureProviderSpec closure = ProviderAuthorityQualificationSpec
  { providerAuthoritySubject = semanticProviderAuthoritySubject checkedSemanticProvider
  , providerAuthorityInventoryBasis = CheckedPurePhilAuthorityInventory pureInventoryRevision
  , providerAuthorityClientVisible = Set.singleton readUse
  , providerAuthorityInternal = readDeleteUses
  , providerAuthorityPurePhilConfinements = [closure]
  , providerAuthorityExtraDispositions = Map.singleton deleteUse ExtraAuthorityStaticallyConfined
  }

foreignProviderSpec :: ProviderAuthorityQualificationSpec
foreignProviderSpec = ProviderAuthorityQualificationSpec
  { providerAuthoritySubject = OpaqueForeignProviderAuthoritySubject
      (InterfaceRevision "provider.binding.v1")
      foreignBoundary
  , providerAuthorityInventoryBasis = ForeignAuthorityInventoryByEvidence foreignEvidence
  , providerAuthorityClientVisible = Set.singleton readUse
  , providerAuthorityInternal = readDeleteUses
  , providerAuthorityPurePhilConfinements = []
  , providerAuthorityExtraDispositions =
      Map.singleton deleteUse (ExtraAuthorityExternallyConfined foreignEvidence)
  }

checkedSemanticProvider :: CheckedProviderSemanticQualification
checkedSemanticProvider = CheckedProviderSemanticQualification
  { checkedProviderContractRevision = InterfaceRevision "provider.binding.v1"
  , checkedProviderImplementationRevision = DefinitionRevision "provider.binding.impl.v1"
  , checkedProviderOperations = Map.empty
  }

storageOrigin :: AuthorityReachabilityOrigin
storageOrigin = OtherAuthorityReachabilityOrigin "binding.storage"

primarySubject :: AuthoritySubjectKey
primarySubject = AuthoritySubjectKey "binding.store.primary"

readOperation, writeOperation, deleteOperation :: AuthorityOperationKey
readOperation = AuthorityOperationKey "read"
writeOperation = AuthorityOperationKey "write"
deleteOperation = AuthorityOperationKey "delete"

readUse, writeUse, deleteUse :: AuthorityUse
readUse = AuthorityUse primarySubject readOperation
writeUse = AuthorityUse primarySubject writeOperation
deleteUse = AuthorityUse primarySubject deleteOperation

readDeleteUses :: Set.Set AuthorityUse
readDeleteUses = Set.fromList [readUse, deleteUse]

broadSurface :: AuthoritySurface
broadSurface = AuthoritySurface
  (AuthorityContractKey "binding.storage.read-delete.v1")
  primarySubject
  (Set.fromList [readOperation, deleteOperation])

deleteClaim, writeClaim :: NegativeAuthorityClaim
deleteClaim = NegativeAuthorityClaim primarySubject deleteOperation
writeClaim = NegativeAuthorityClaim primarySubject writeOperation

pureInventoryRevision :: ProviderAuthorityInventoryRevision
pureInventoryRevision = ProviderAuthorityInventoryRevision "binding.authority-inventory.v1"

foreignBoundary :: OpaqueProviderBoundaryKey
foreignBoundary = OpaqueProviderBoundaryKey "binding.foreign-provider.v1"

foreignEvidence :: ProviderAuthorityConfinementEvidenceKey
foreignEvidence = ProviderAuthorityConfinementEvidenceKey "binding.foreign-authority-evidence.v1"

foreignAbi :: ProviderAuthorityAbiShapeKey
foreignAbi = ProviderAuthorityAbiShapeKey "binding.foreign-abi.v1"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
