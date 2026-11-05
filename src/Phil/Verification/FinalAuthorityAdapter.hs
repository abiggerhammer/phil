{-# LANGUAGE OverloadedStrings #-}

module Phil.Verification.FinalAuthorityAdapter
  ( ExpectedSourceManifestAssociation (..)
  , NativeFinalAuthority
  , nativeFinalSourceIdentity
  , nativeFinalManifestId
  , nativeFinalRawSystemsDigest
  , nativeFinalLoweringRoot
  , nativeFinalSubjectRevision
  , nativeFinalInstanceRevision
  , nativeFinalRealizationRevision
  , nativeFinalSystemsRevision
  , nativeFinalCommonContractRevision
  , nativeFinalClosedContractRevision
  , nativeFinalVerifierProfile
  , NativeFinalAuthorityError (..)
  , bindNativeFinalAuthority
  ) where

import Phil.Assurance.Types
  ( AssuranceManifest (..)
  , Digest
  )
import Phil.Core.Generic
  ( GenericApplicationIdentity
  , GenericDischargeLineage (..)
  )
import Phil.Core.Static (InstanceRevision, RealizationRevision)
import Phil.Systems.IR
  ( loweringLedgerRoot
  , systemsArtifactDigest
  , systemsArtifactLoweringLedger
  )
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  , Phase1StageContractRevision
  , SystemsArtifactRevision
  )
import Phil.Systems.StageClosure
  ( ClosedStageContractRevision
  , StageClosureBundle (..)
  , concreteSubjectStage
  )
import Phil.Systems.SubjectCorrespondence
  ( SubjectStageBundle (..)
  , SubjectStageRevision
  )
import Phil.Verification.ArtifactClosure
  ( CertifiedApplicationArtifact
  , certifiedApplicationSourceAssurance
  , certifiedApplicationStageClosure
  )
import Phil.Verification.CertifiedRelease
  ( CertifiedReleaseArtifact
  , certifiedReleaseManifest
  , certifiedReleaseStageClosure
  )
import Phil.Verification.GenericAssurance
  ( genericApplicationAssuranceLineage
  )

-- | Independently supplied association. It is intentionally an ordinary input,
-- not a certificate: its producer must establish the relationship between an
-- accepted generic application and the assurance manifest, because the native
-- AssuranceManifest has no field containing a GenericApplicationIdentity.
data ExpectedSourceManifestAssociation = ExpectedSourceManifestAssociation
  { expectedSourceApplicationIdentity :: GenericApplicationIdentity
  , expectedSourceManifestId :: Digest
  }
  deriving (Eq, Show)

data NativeFinalAuthority = NativeFinalAuthority
  GenericApplicationIdentity
  Digest
  Digest
  Digest
  SubjectStageRevision
  InstanceRevision
  RealizationRevision
  SystemsArtifactRevision
  Phase1StageContractRevision
  ClosedStageContractRevision
  String
  deriving (Eq, Show)

nativeFinalSourceIdentity :: NativeFinalAuthority -> GenericApplicationIdentity
nativeFinalSourceIdentity (NativeFinalAuthority source _ _ _ _ _ _ _ _ _ _) = source

nativeFinalManifestId :: NativeFinalAuthority -> Digest
nativeFinalManifestId (NativeFinalAuthority _ manifest _ _ _ _ _ _ _ _ _) = manifest

nativeFinalRawSystemsDigest :: NativeFinalAuthority -> Digest
nativeFinalRawSystemsDigest (NativeFinalAuthority _ _ raw _ _ _ _ _ _ _ _) = raw

nativeFinalLoweringRoot :: NativeFinalAuthority -> Digest
nativeFinalLoweringRoot (NativeFinalAuthority _ _ _ root _ _ _ _ _ _ _) = root

nativeFinalSubjectRevision :: NativeFinalAuthority -> SubjectStageRevision
nativeFinalSubjectRevision (NativeFinalAuthority _ _ _ _ subject _ _ _ _ _ _) = subject

nativeFinalInstanceRevision :: NativeFinalAuthority -> InstanceRevision
nativeFinalInstanceRevision (NativeFinalAuthority _ _ _ _ _ instanceRevision _ _ _ _ _) = instanceRevision

nativeFinalRealizationRevision :: NativeFinalAuthority -> RealizationRevision
nativeFinalRealizationRevision (NativeFinalAuthority _ _ _ _ _ _ realization _ _ _ _) = realization

nativeFinalSystemsRevision :: NativeFinalAuthority -> SystemsArtifactRevision
nativeFinalSystemsRevision (NativeFinalAuthority _ _ _ _ _ _ _ systems _ _ _) = systems

nativeFinalCommonContractRevision :: NativeFinalAuthority -> Phase1StageContractRevision
nativeFinalCommonContractRevision (NativeFinalAuthority _ _ _ _ _ _ _ _ contract _ _) = contract

nativeFinalClosedContractRevision :: NativeFinalAuthority -> ClosedStageContractRevision
nativeFinalClosedContractRevision (NativeFinalAuthority _ _ _ _ _ _ _ _ _ closed _) = closed

nativeFinalVerifierProfile :: NativeFinalAuthority -> String
nativeFinalVerifierProfile (NativeFinalAuthority _ _ _ _ _ _ _ _ _ _ profile) = profile

data NativeFinalAuthorityError
  = NativeFinalSourceMismatch GenericApplicationIdentity GenericApplicationIdentity
  | NativeFinalManifestMismatch Digest Digest
  | NativeFinalStageMismatch
  | NativeFinalRawSystemsMismatch Digest Digest
  | NativeFinalLoweringRootMismatch Digest Digest
  deriving (Eq, Show)

-- | Bind two independently accepted, opaque producer results. The exact
-- StageClosure object must be identical, not only its advertised revision.
-- The external source/manifest association remains an explicit premise.
bindNativeFinalAuthority
  :: ExpectedSourceManifestAssociation
  -> CertifiedApplicationArtifact
  -> CertifiedReleaseArtifact
  -> Either NativeFinalAuthorityError NativeFinalAuthority
bindNativeFinalAuthority association sourceArtifact release = do
  let acceptedSource = certifiedApplicationSourceAssurance sourceArtifact
      sourceId = genericDischargeApplicationIdentity
        (genericApplicationAssuranceLineage acceptedSource)
      expectedSource = expectedSourceApplicationIdentity association
      manifest = certifiedReleaseManifest release
      actualManifestId = manifestId manifest
      expectedManifestId = expectedSourceManifestId association
      sourceStage = certifiedApplicationStageClosure sourceArtifact
      releaseStage = certifiedReleaseStageClosure release
  if sourceId == expectedSource
    then Right ()
    else Left (NativeFinalSourceMismatch expectedSource sourceId)
  if actualManifestId == expectedManifestId
    then Right ()
    else Left (NativeFinalManifestMismatch expectedManifestId actualManifestId)
  if sourceStage == releaseStage
    then Right ()
    else Left NativeFinalStageMismatch
  let subject = concreteSubjectStage (stageClosureConcrete releaseStage)
      common = subjectStageBase subject
      systemsArtifact = phase1StageSystemsArtifact common
      raw = systemsArtifactDigest systemsArtifact
      root = loweringLedgerRoot (systemsArtifactLoweringLedger systemsArtifact)
  if manifestImplementationDigest manifest == raw
    then Right ()
    else Left (NativeFinalRawSystemsMismatch raw (manifestImplementationDigest manifest))
  if manifestLoweringLedgerRoot manifest == root
    then Right ()
    else Left (NativeFinalLoweringRootMismatch root (manifestLoweringLedgerRoot manifest))
  Right (NativeFinalAuthority
    sourceId actualManifestId raw root
    (subjectStageRevision subject)
    (phase1StageInstanceRevision common)
    (phase1StageRealizationRevision common)
    (phase1StageSystemsArtifactRevision common)
    (phase1StageContractRevision common)
    (stageClosureContractRevision releaseStage)
    (show (phase1StageVerifierProfileRevision common)))
