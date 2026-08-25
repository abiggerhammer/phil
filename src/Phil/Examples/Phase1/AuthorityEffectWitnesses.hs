{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.AuthorityEffectWitnesses
  ( uploadAuthorityEffectStageBundle
  , steveAuthorityEffectStageBundle
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Authority
  ( AuthorityOperationKey (..)
  , AuthoritySubjectKey (..)
  )
import Phil.Core.AuthorityConfinement (AuthorityUse (..))
import Phil.Core.Callable (SemanticEffect (..))
import Phil.Core.ProviderQualification
  ( CheckedProviderSemanticQualification (..)
  , ProviderOperationKey (..)
  )
import Phil.Examples.Phase1.ProviderCallWitnesses
  ( steveProviderCallStageBundle
  , uploadProviderCallStageBundle
  )
import Phil.Examples.Steve.ProviderQualifications
  ( SteveProviderQualificationArtifact (..)
  , SteveProviderQualificationError (..)
  , SteveProviderQualifications (..)
  , materializeSteveProviderQualifications
  )
import Phil.Systems.AuthorityEffectCorrespondence
import Phil.Systems.Phase1Stage (SystemsMechanismKey (..))

uploadAuthorityEffectStageBundle :: Either String AuthorityEffectStageBundle
uploadAuthorityEffectStageBundle = do
  base <- uploadProviderCallStageBundle
  let surface = OpaqueProviderSemanticSurface
        "evidence.upload.storage.runtime"
        (Map.singleton uploadStoreOperation OpaqueProviderOperationSurface
          { opaqueOperationEffectBound = Set.singleton (SemanticEffect "upload.store")
          , opaqueOperationPublicAuthority = Set.singleton uploadStoreAuthority
          })
      use = SystemsProviderUse
        { systemsProviderUseMechanism = uploadStoreMechanism
        , systemsProviderUseEffects = Set.singleton
            (ProviderEffectUse (SemanticEffect "upload.store") SourceObservableEffect Nothing)
        , systemsProviderUseAuthority = Set.singleton
            (PublicProviderAuthority uploadStoreAuthority)
        }
  pure (makeAuthorityEffectStageBundle
    base
    (Map.singleton "upload.storage-provider" surface)
    (Map.singleton uploadStoreMechanism use))

steveAuthorityEffectStageBundle :: Either String AuthorityEffectStageBundle
steveAuthorityEffectStageBundle = do
  base <- steveProviderCallStageBundle
  qualifications <- mapLeft (Text.unpack . unSteveProviderQualificationError)
    materializeSteveProviderQualifications
  let digestArtifact = steveDigestProviderQualification qualifications
      blobArtifact = steveBlobProviderQualification qualifications
      digestSurface = QualifiedProviderSemanticSurface
        (steveProviderCheckedSemantic digestArtifact)
        (steveProviderCheckedAuthority digestArtifact)
        (Map.fromSet (const emptyAuthorityAssignment)
          (Map.keysSet (checkedProviderOperations
            (steveProviderCheckedSemantic digestArtifact))))
      blobSurface = QualifiedProviderSemanticSurface
        (steveProviderCheckedSemantic blobArtifact)
        (steveProviderCheckedAuthority blobArtifact)
        (Map.fromList
          [ (blobReadOperation, ProviderOperationAuthorityAssignment
              (Set.singleton blobReadAuthority) Map.empty)
          , (blobInstallOperation, ProviderOperationAuthorityAssignment
              (Set.singleton blobInstallAuthority) Map.empty)
          ])
      surfaces = Map.fromList
        [ ("steve.digest-provider", digestSurface)
        , ("steve.blob-provider", blobSurface)
        ]
      uses = Map.fromList
        [ (steveDigestComputeMechanism,
            semanticProviderUse steveDigestComputeMechanism "digest.sha256.compute" Set.empty)
        , (steveBlobInstallMechanism,
            semanticProviderUse steveBlobInstallMechanism "blob.install-if-absent"
              (Set.singleton (PublicProviderAuthority blobInstallAuthority)))
        , (steveBlobReadMechanism,
            semanticProviderUse steveBlobReadMechanism "blob.read"
              (Set.singleton (PublicProviderAuthority blobReadAuthority)))
        , (steveDigestCheckMechanism,
            semanticProviderUse steveDigestCheckMechanism "digest.sha256.check" Set.empty)
        ]
  pure (makeAuthorityEffectStageBundle base surfaces uses)

semanticProviderUse
  :: SystemsMechanismKey
  -> Text
  -> Set.Set ProviderAuthorityExercise
  -> SystemsProviderUse
semanticProviderUse mechanism effect authority = SystemsProviderUse
  { systemsProviderUseMechanism = mechanism
  , systemsProviderUseEffects = Set.singleton
      (ProviderEffectUse (SemanticEffect effect) SourceObservableEffect Nothing)
  , systemsProviderUseAuthority = authority
  }

emptyAuthorityAssignment :: ProviderOperationAuthorityAssignment
emptyAuthorityAssignment = ProviderOperationAuthorityAssignment Set.empty Map.empty

uploadStoreOperation, blobReadOperation, blobInstallOperation :: ProviderOperationKey
uploadStoreOperation = ProviderOperationKey "upload.store"
blobReadOperation = ProviderOperationKey "blob.read"
blobInstallOperation = ProviderOperationKey "blob.install-if-absent"

uploadStoreAuthority, blobReadAuthority, blobInstallAuthority :: AuthorityUse
uploadStoreAuthority = AuthorityUse
  (AuthoritySubjectKey "upload.storage") (AuthorityOperationKey "store")
blobReadAuthority = AuthorityUse
  (AuthoritySubjectKey "steve.blob.namespace") (AuthorityOperationKey "read")
blobInstallAuthority = AuthorityUse
  (AuthoritySubjectKey "steve.blob.namespace") (AuthorityOperationKey "install-if-absent")

uploadStoreMechanism :: SystemsMechanismKey
uploadStoreMechanism = SystemsMechanismKey "UploadServer:server.store:term.store"

steveDigestComputeMechanism, steveBlobInstallMechanism :: SystemsMechanismKey
steveBlobReadMechanism, steveDigestCheckMechanism :: SystemsMechanismKey
steveDigestComputeMechanism = SystemsMechanismKey
  "StevePut:put.entry:term.runtime-choice.DigestProvider.compute"
steveBlobInstallMechanism = SystemsMechanismKey
  "StevePut:put.install:term.runtime-choice.BlobProvider.install-if-absent"
steveBlobReadMechanism = SystemsMechanismKey
  "SteveGet:get.entry:term.runtime-choice.BlobProvider.read"
steveDigestCheckMechanism = SystemsMechanismKey
  "SteveGet:get.check:term.runtime-choice.DigestProvider.check"

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
