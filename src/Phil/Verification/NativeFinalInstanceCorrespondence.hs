{-# LANGUAGE OverloadedStrings #-}

-- | A narrow, native, producer-to-consumer final-authority witness.  No Rocq
-- nat encoding or claim of FinalArtifactCertified is exported here.
module Phil.Verification.NativeFinalInstanceCorrespondence
  ( NativeFinalInstanceCorrespondence
  , nativeCorrespondenceArchitectureInstance
  , nativeCorrespondenceAuthority
  , NativeFinalInstanceCorrespondenceError (..)
  , closeNativeFinalInstanceCorrespondence
  ) where

import Phil.Assurance.Types (AssuranceLedger, VerificationContext)
import Phil.Core.Static
  ( ArchitectureInstanceDescriptor
  , ArchitectureInstanceIdentity
  , deriveArchitectureInstanceIdentity
  )
import Phil.Verification (ApplicationAssurancePolicy)
import Phil.Verification.ArtifactClosure (CertifiedApplicationArtifact)
import Phil.Verification.Bundle (VerificationBundle)
import Phil.Verification.CertifiedRelease (CertifiedReleaseArtifact)
import Phil.Verification.FinalAuthorityAdapter (NativeFinalAuthority)
import Phil.Verification.GenericAssurance (GenericApplicationAssurance)
import Phil.Verification.ManifestClosure (ManifestClosureSelection)
import Phil.Verification.SourceManifestBinding
  ( SourceManifestBindingError
  , bindProducedFinalAuthority
  , closeSourceManifestBindingForInstance
  )

-- | Retains the canonical architecture-instance identity from the checked
-- actuals/instance/bundle producer *separately* from StageClosure's
-- InstanceRevision (available through 'nativeCorrespondenceAuthority').
-- They are different native domains; relating them remains a named premise.
-- The constructor is deliberately private.
data NativeFinalInstanceCorrespondence = NativeFinalInstanceCorrespondence
  ArchitectureInstanceIdentity
  NativeFinalAuthority
  deriving (Eq, Show)

nativeCorrespondenceArchitectureInstance
  :: NativeFinalInstanceCorrespondence -> ArchitectureInstanceIdentity
nativeCorrespondenceArchitectureInstance
  (NativeFinalInstanceCorrespondence instanceIdentity _) = instanceIdentity

nativeCorrespondenceAuthority
  :: NativeFinalInstanceCorrespondence -> NativeFinalAuthority
nativeCorrespondenceAuthority
  (NativeFinalInstanceCorrespondence _ authority) = authority

data NativeFinalInstanceCorrespondenceError
  = NativeFinalInstanceSourceRejected SourceManifestBindingError
  | NativeFinalInstanceReleaseRejected SourceManifestBindingError
  deriving (Eq, Show)

-- | Compose, without substituting identity domains:
--   (1) accepted GenericApplicationAssurance and exact semantic actuals;
--   (2) canonical architecture descriptor and instance stored in the bundle;
--   (3) the *actual* INT-002 manifest producer;
--   (4) independently accepted VER-010 source artifact and INT-005 release;
--   (5) full manifest and retained StageClosure equality, including the
--       actual raw Systems digest and lowering root, checked by the adapter.
--
-- The downstream native stage's InstanceRevision is NOT asserted equal to the
-- architecture occurrence's InstanceRevision merely because both mention an
-- instance: no such competent bridge is established by this interface.
closeNativeFinalInstanceCorrespondence
  :: GenericApplicationAssurance
  -> ArchitectureInstanceDescriptor
  -> VerificationBundle
  -> ApplicationAssurancePolicy
  -> VerificationContext
  -> AssuranceLedger
  -> ManifestClosureSelection
  -> CertifiedApplicationArtifact
  -> CertifiedReleaseArtifact
  -> Either NativeFinalInstanceCorrespondenceError NativeFinalInstanceCorrespondence
closeNativeFinalInstanceCorrespondence
  source descriptor bundle policy context ledger selection sourceArtifact release = do
    produced <- either (Left . NativeFinalInstanceSourceRejected) Right
      (closeSourceManifestBindingForInstance
        source descriptor bundle policy context ledger selection)
    authority <- either (Left . NativeFinalInstanceReleaseRejected) Right
      (bindProducedFinalAuthority produced sourceArtifact release)
    pure (NativeFinalInstanceCorrespondence
      (deriveArchitectureInstanceIdentity descriptor) authority)
