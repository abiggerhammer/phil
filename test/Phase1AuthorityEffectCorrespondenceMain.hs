{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Authority
  ( AuthorityOperationKey (..)
  , AuthoritySubjectKey (..)
  )
import Phil.Core.AuthorityConfinement (AuthorityUse (..))
import Phil.Core.Callable (SemanticEffect (..))
import Phil.Core.ProviderAuthorityQualification
  ( ProviderAuthorityAssumptionKey (..)
  , ProviderExtraAuthorityDisposition (..)
  )
import Phil.Core.ProviderQualification (ProviderOperationKey (..))
import Phil.Examples.Phase1.AuthorityEffectWitnesses
import Phil.Systems.AuthorityEffectCorrespondence
import Phil.Systems.Phase1Stage (SystemsMechanismKey (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SYS-006 upload authority/effect relation accepts" uploadAccepted
    , test "SYS-006 Steve authority/effect relations accept" steveAccepted
    , test "SYS-006 source-observable effect widening rejects" observableEffectWideningRejected
    , test "SYS-006 internal target effect with refinement accepts" internalEffectWithRefinementAccepted
    , test "SYS-006 internal target effect without refinement rejects" internalEffectWithoutRefinementRejected
    , test "SYS-006 provider operation cannot exercise another operation's authority" wrongOperationAuthorityRejected
    , test "SYS-006 qualified-but-unassigned internal authority is hidden" hiddenInternalAuthorityRejected
    , test "SYS-006 surface cannot widen admitted public authority" publicSurfaceEscapeRejected
    , test "SYS-006 opaque provider surface requires evidence" opaqueSurfaceEvidenceRequired
    , test "SYS-006 authority/effect stage identity is deterministic" deterministicIdentity
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

uploadAccepted :: Either String ()
uploadAccepted = uploadBundle >>= mapLeft show . verifyAuthorityEffectStageBundle

steveAccepted :: Either String ()
steveAccepted = steveBundle >>= mapLeft show . verifyAuthorityEffectStageBundle

observableEffectWideningRejected :: Either String ()
observableEffectWideningRejected = do
  bundle <- steveBundle
  use <- lookupUse digestCompute bundle
  let widened = ProviderEffectUse
        (SemanticEffect "network.exfiltrate") SourceObservableEffect
        (Just (RealizationEffectRevision "target.network.v1"))
      changedUse = use
        { systemsProviderUseEffects = Set.insert widened (systemsProviderUseEffects use) }
      mutated = rebuild bundle
        (authorityEffectStageSurfaces bundle)
        (Map.insert digestCompute changedUse (authorityEffectStageUses bundle))
  case verifyAuthorityEffectStageBundle mutated of
    Left (AuthorityEffectObservableRealizationWidening mechanism effect) -> do
      assert (mechanism == digestCompute) "wrong widening mechanism"
      assert (effect == SemanticEffect "network.exfiltrate") "wrong widened effect"
    other -> Left ("source-observable effect widening was accepted: " <> show other)

internalEffectWithRefinementAccepted :: Either String ()
internalEffectWithRefinementAccepted = do
  bundle <- steveBundle
  use <- lookupUse digestCompute bundle
  let internal = ProviderEffectUse
        (SemanticEffect "target.hash.dispatch") InternalRealizationEffect
        (Just (RealizationEffectRevision "realization.effect.hash-dispatch.v1"))
      changedUse = use
        { systemsProviderUseEffects = Set.insert internal (systemsProviderUseEffects use) }
      mutated = rebuild bundle
        (authorityEffectStageSurfaces bundle)
        (Map.insert digestCompute changedUse (authorityEffectStageUses bundle))
  mapLeft show $ verifyAuthorityEffectStageBundle mutated

internalEffectWithoutRefinementRejected :: Either String ()
internalEffectWithoutRefinementRejected = do
  bundle <- steveBundle
  use <- lookupUse digestCompute bundle
  let internal = ProviderEffectUse
        (SemanticEffect "target.hash.dispatch") InternalRealizationEffect Nothing
      changedUse = use
        { systemsProviderUseEffects = Set.insert internal (systemsProviderUseEffects use) }
      mutated = rebuild bundle
        (authorityEffectStageSurfaces bundle)
        (Map.insert digestCompute changedUse (authorityEffectStageUses bundle))
  case verifyAuthorityEffectStageBundle mutated of
    Left (AuthorityEffectMissingRealizationRefinement mechanism effect) -> do
      assert (mechanism == digestCompute) "wrong missing-refinement mechanism"
      assert (effect == SemanticEffect "target.hash.dispatch") "wrong missing-refinement effect"
    other -> Left ("unrefined internal effect was accepted: " <> show other)

wrongOperationAuthorityRejected :: Either String ()
wrongOperationAuthorityRejected = do
  bundle <- steveBundle
  use <- lookupUse blobInstall bundle
  let changedUse = use
        { systemsProviderUseAuthority = Set.insert
            (PublicProviderAuthority blobReadAuthority)
            (systemsProviderUseAuthority use) }
      mutated = rebuild bundle
        (authorityEffectStageSurfaces bundle)
        (Map.insert blobInstall changedUse (authorityEffectStageUses bundle))
  case verifyAuthorityEffectStageBundle mutated of
    Left (AuthorityEffectHiddenPublicAuthority mechanism authority) -> do
      assert (mechanism == blobInstall) "wrong operation-authority mechanism"
      assert (authority == blobReadAuthority) "wrong hidden public authority"
    other -> Left ("cross-operation authority was accepted: " <> show other)

hiddenInternalAuthorityRejected :: Either String ()
hiddenInternalAuthorityRejected = do
  bundle <- steveBundle
  use <- lookupUse blobInstall bundle
  let disposition = ExtraAuthorityAssumptionDependent
        (ProviderAuthorityAssumptionKey "assumption:steve.blob.backing-authority-confined.v1")
      changedUse = use
        { systemsProviderUseAuthority = Set.insert
            (QualifiedInternalProviderAuthority blobDeleteAuthority disposition)
            (systemsProviderUseAuthority use) }
      mutated = rebuild bundle
        (authorityEffectStageSurfaces bundle)
        (Map.insert blobInstall changedUse (authorityEffectStageUses bundle))
  case verifyAuthorityEffectStageBundle mutated of
    Left (AuthorityEffectHiddenInternalAuthority mechanism authority) -> do
      assert (mechanism == blobInstall) "wrong hidden-internal mechanism"
      assert (authority == blobDeleteAuthority) "wrong hidden internal authority"
    other -> Left ("unassigned internal authority was accepted: " <> show other)

publicSurfaceEscapeRejected :: Either String ()
publicSurfaceEscapeRejected = do
  bundle <- steveBundle
  surface <- maybe (Left "missing BlobProvider surface") Right
    (Map.lookup "steve.blob-provider" (authorityEffectStageSurfaces bundle))
  changedSurface <- case surface of
    QualifiedProviderSemanticSurface semantic authority assignments -> do
      assignment <- maybe (Left "missing blob.read authority assignment") Right
        (Map.lookup blobReadOperation assignments)
      let widened = assignment
            { operationPublicAuthority = Set.insert blobDeleteAuthority
                (operationPublicAuthority assignment) }
      Right (QualifiedProviderSemanticSurface semantic authority
        (Map.insert blobReadOperation widened assignments))
    _ -> Left "BlobProvider unexpectedly opaque"
  let mutated = rebuild bundle
        (Map.insert "steve.blob-provider" changedSurface (authorityEffectStageSurfaces bundle))
        (authorityEffectStageUses bundle)
  case verifyAuthorityEffectStageBundle mutated of
    Left (AuthorityEffectPublicAuthorityEscape occurrence escaped) -> do
      assert (occurrence == "steve.blob-provider") "wrong authority-escape provider"
      assert (escaped == Set.singleton blobDeleteAuthority) "wrong escaped authority set"
    other -> Left ("widened public authority surface was accepted: " <> show other)

opaqueSurfaceEvidenceRequired :: Either String ()
opaqueSurfaceEvidenceRequired = do
  bundle <- uploadBundle
  surface <- maybe (Left "missing upload storage surface") Right
    (Map.lookup "upload.storage-provider" (authorityEffectStageSurfaces bundle))
  changedSurface <- case surface of
    OpaqueProviderSemanticSurface _ operations ->
      Right (OpaqueProviderSemanticSurface "" operations)
    _ -> Left "upload storage surface unexpectedly qualified"
  let mutated = rebuild bundle
        (Map.insert "upload.storage-provider" changedSurface (authorityEffectStageSurfaces bundle))
        (authorityEffectStageUses bundle)
  case verifyAuthorityEffectStageBundle mutated of
    Left (AuthorityEffectOpaqueSurfaceMissingEvidence occurrence) ->
      assert (occurrence == "upload.storage-provider") "wrong opaque provider diagnostic"
    other -> Left ("opaque surface without evidence was accepted: " <> show other)

deterministicIdentity :: Either String ()
deterministicIdentity = do
  bundle <- steveBundle
  let reversedSurfaces = Map.fromList
        (reverse (Map.toAscList (authorityEffectStageSurfaces bundle)))
      reversedUses = Map.fromList
        (reverse (Map.toAscList (authorityEffectStageUses bundle)))
      rebuilt = rebuild bundle reversedSurfaces reversedUses
  assert
    (authorityEffectStageRevision rebuilt == authorityEffectStageRevision bundle)
    "authority/effect stage revision changed with map order"
  mapLeft show $ verifyAuthorityEffectStageBundle rebuilt

rebuild
  :: AuthorityEffectStageBundle
  -> Map.Map Text ProviderSemanticSurfaceBasis
  -> Map.Map SystemsMechanismKey SystemsProviderUse
  -> AuthorityEffectStageBundle
rebuild bundle surfaces uses = makeAuthorityEffectStageBundle
  (authorityEffectStageBase bundle) surfaces uses

lookupUse
  :: SystemsMechanismKey
  -> AuthorityEffectStageBundle
  -> Either String SystemsProviderUse
lookupUse key bundle = maybe
  (Left ("missing Systems provider use: " <> show key))
  Right
  (Map.lookup key (authorityEffectStageUses bundle))

uploadBundle :: Either String AuthorityEffectStageBundle
uploadBundle = uploadAuthorityEffectStageBundle

steveBundle :: Either String AuthorityEffectStageBundle
steveBundle = steveAuthorityEffectStageBundle

digestCompute, blobInstall :: SystemsMechanismKey
digestCompute = SystemsMechanismKey
  "StevePut:put.entry:term.runtime-choice.DigestProvider.compute"
blobInstall = SystemsMechanismKey
  "StevePut:put.install:term.runtime-choice.BlobProvider.install-if-absent"

blobReadOperation :: ProviderOperationKey
blobReadOperation = ProviderOperationKey "blob.read"

blobReadAuthority, blobDeleteAuthority :: AuthorityUse
blobReadAuthority = AuthorityUse
  (AuthoritySubjectKey "steve.blob.namespace") (AuthorityOperationKey "read")
blobDeleteAuthority = AuthorityUse
  (AuthoritySubjectKey "steve.blob.namespace") (AuthorityOperationKey "delete")

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
