{-# LANGUAGE OverloadedStrings #-}

module Phil.Verification.SourceManifestBinding
  ( CertifiedSourceManifestBinding
  , sourceManifestBindingManifest
  , SourceManifestBindingError (..)
  , closeSourceManifestBinding
  , bindProducedFinalAuthority
  ) where

import qualified Data.Set as Set
import Phil.Assurance.Types
  ( AssuranceLedger
  , AssuranceManifest (..)
  , VerificationContext
  )
import Phil.Core.Generic
  ( GenericApplicationIdentity (..)
  , GenericDischargeLineage (..)
  )
import Phil.Core.Static
  ( DeclarationIdentity (..)
  )
import Phil.Verification
  ( ApplicationAssurancePolicy
  )
import Phil.Verification.ArtifactClosure
  ( CertifiedApplicationArtifact
  )
import Phil.Verification.Bundle
  ( VerificationBundle (..)
  )
import Phil.Verification.CertifiedRelease
  ( CertifiedReleaseArtifact
  , certifiedReleaseManifest
  )
import Phil.Verification.FinalAuthorityAdapter
  ( ExpectedSourceManifestAssociation (..)
  , NativeFinalAuthority
  , NativeFinalAuthorityError
  , bindNativeFinalAuthority
  )
import Phil.Verification.GenericAssurance
  ( GenericApplicationAssurance
  , genericApplicationAssuranceLineage
  )
import Phil.Verification.ManifestClosure
  ( ManifestClosureError
  , ManifestClosureSelection
  , closeVerificationBundle
  )

-- | A manifest obtained by the ordinary checked VER-012 -> INT-002 closure,
-- with the accepted generic application's declaration identity checked against
-- that exact verification bundle. The constructor and association are private.
-- This does not prove generic actuals map to architecture instance bindings.
data CertifiedSourceManifestBinding = CertifiedSourceManifestBinding
  GenericApplicationIdentity
  AssuranceManifest
  deriving (Eq, Show)

sourceManifestBindingManifest :: CertifiedSourceManifestBinding -> AssuranceManifest
sourceManifestBindingManifest (CertifiedSourceManifestBinding _ manifest) = manifest

data SourceManifestBindingError
  = SourceManifestDeclarationNotInVerificationBundle DeclarationIdentity
  | SourceManifestClosureRejected ManifestClosureError
  | SourceManifestReleaseManifestMismatch
  | SourceManifestNativeBindingRejected NativeFinalAuthorityError
  deriving (Eq, Show)

-- | Reuse the accepted source and the actual manifest closure producer. The
-- source declaration must occur in the same bundle from which the manifest is
-- closed; the policy, context, ledger and selection are checked by INT-002.
closeSourceManifestBinding
  :: GenericApplicationAssurance
  -> VerificationBundle
  -> ApplicationAssurancePolicy
  -> VerificationContext
  -> AssuranceLedger
  -> ManifestClosureSelection
  -> Either SourceManifestBindingError CertifiedSourceManifestBinding
closeSourceManifestBinding source bundle policy context ledger selection = do
  let lineage = genericApplicationAssuranceLineage source
      application = genericDischargeApplicationIdentity lineage
      declaration = DeclarationIdentity
        { identityDeclarationKey = genericApplicationDeclarationKey application
        , identityInterfaceRevision = genericApplicationInterfaceRevision application
        , identityDefinitionRevision = genericDischargeDefinitionRevision lineage
        }
  if Set.member declaration (verificationBundleDeclarations bundle)
    then Right ()
    else Left (SourceManifestDeclarationNotInVerificationBundle declaration)
  manifest <- either (Left . SourceManifestClosureRejected) Right
    (closeVerificationBundle bundle policy context ledger selection)
  pure (CertifiedSourceManifestBinding application manifest)

-- | The final adapter must consume the same produced manifest, not a second
-- independently supplied manifest with a caller-selected identity pair.
bindProducedFinalAuthority
  :: CertifiedSourceManifestBinding
  -> CertifiedApplicationArtifact
  -> CertifiedReleaseArtifact
  -> Either SourceManifestBindingError NativeFinalAuthority
bindProducedFinalAuthority (CertifiedSourceManifestBinding sourceId manifest) sourceArtifact release = do
  if certifiedReleaseManifest release == manifest
    then Right ()
    else Left SourceManifestReleaseManifestMismatch
  either (Left . SourceManifestNativeBindingRejected) Right $
    bindNativeFinalAuthority
      (ExpectedSourceManifestAssociation sourceId (manifestId manifest))
      sourceArtifact
      release
