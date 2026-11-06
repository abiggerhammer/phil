{-# LANGUAGE OverloadedStrings #-}

-- | A narrow, native, producer-to-consumer final-authority witness.  No Rocq
-- nat encoding or claim of FinalArtifactCertified is exported here.
module Phil.Verification.NativeFinalInstanceCorrespondence
  ( NativeFinalInstanceCorrespondence
  , nativeCorrespondenceArchitectureInstance
  , nativeCorrespondenceAuthority
  , NativeStageRevisionEquality
  , nativeStageRevisionEqualityOccurrence
  , nativeStageRevisionEqualityStageRevision
  , NativeStageRevisionEqualityError (..)
  , checkNativeStageRevisionEquality
  , NativeFinalInstanceCorrespondenceError (..)
  , closeNativeFinalInstanceCorrespondence
  ) where

import Phil.Assurance.Types (AssuranceLedger, VerificationContext)
import Phil.Core.Static
  ( ArchitectureInstanceDescriptor
  , ArchitectureInstanceIdentity (..)
  , InstanceRevision
  , deriveArchitectureInstanceIdentity
  )
import Phil.Verification (ApplicationAssurancePolicy)
import Phil.Verification.ArtifactClosure
  ( CertifiedApplicationArtifact
  , certifiedApplicationSourceAssurance
  )
import Phil.Verification.Bundle (VerificationBundle)
import Phil.Verification.CertifiedRelease (CertifiedReleaseArtifact)
import Phil.Verification.FinalAuthorityAdapter
  ( NativeFinalAuthority
  , nativeFinalInstanceRevision
  )
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

-- | Equality of the architecture occurrence's canonical revision with the
-- retained concrete stage's InstanceRevision. The constructor is private.
-- Crucially, this is a necessary consistency check, NOT evidence that the
-- stage was produced by that occurrence: StageClosure stores no InstanceKey.
data NativeStageRevisionEquality = NativeStageRevisionEquality
  ArchitectureInstanceIdentity InstanceRevision
  deriving (Eq, Show)

nativeStageRevisionEqualityOccurrence
  :: NativeStageRevisionEquality -> ArchitectureInstanceIdentity
nativeStageRevisionEqualityOccurrence
  (NativeStageRevisionEquality occurrence _) = occurrence

nativeStageRevisionEqualityStageRevision
  :: NativeStageRevisionEquality -> InstanceRevision
nativeStageRevisionEqualityStageRevision
  (NativeStageRevisionEquality _ revision) = revision

data NativeStageRevisionEqualityError
  = NativeStageRevisionDifferent InstanceRevision InstanceRevision
  deriving (Eq, Show)

-- | A second, fail-closed gate on an already accepted native witness. It does
-- not retrofit a stage-origin proof into the upstream certified producers.
-- Same revision with a different occurrence key remains insufficient.
checkNativeStageRevisionEquality
  :: NativeFinalInstanceCorrespondence
  -> Either NativeStageRevisionEqualityError NativeStageRevisionEquality
checkNativeStageRevisionEquality witness =
  let occurrence = nativeCorrespondenceArchitectureInstance witness
      expected = identityInstanceRevision occurrence
      actual = nativeFinalInstanceRevision (nativeCorrespondenceAuthority witness)
  in if expected == actual
      then Right (NativeStageRevisionEquality occurrence actual)
      else Left (NativeStageRevisionDifferent expected actual)

data NativeFinalInstanceCorrespondenceError
  = NativeFinalInstanceSourceAssuranceMismatch
  | NativeFinalInstanceSourceRejected SourceManifestBindingError
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
    -- The producer must use the EXACT accepted source-assurance object,
    -- not merely a second assurance with the same application identity.
    -- This check is necessary, not stage-origin or model-proof authority.
    if source == certifiedApplicationSourceAssurance sourceArtifact
      then Right ()
      else Left NativeFinalInstanceSourceAssuranceMismatch
    produced <- either (Left . NativeFinalInstanceSourceRejected) Right
      (closeSourceManifestBindingForInstance
        source descriptor bundle policy context ledger selection)
    authority <- either (Left . NativeFinalInstanceReleaseRejected) Right
      (bindProducedFinalAuthority produced sourceArtifact release)
    pure (NativeFinalInstanceCorrespondence
      (deriveArchitectureInstanceIdentity descriptor) authority)
