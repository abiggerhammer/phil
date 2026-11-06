{-# LANGUAGE OverloadedStrings #-}

module Phil.Verification.SourceManifestBinding
  ( CertifiedSourceManifestBinding
  , sourceManifestBindingManifest
  , SourceManifestBindingError (..)
  , closeSourceManifestBinding
  , closeSourceManifestBindingForInstance
  , bindProducedFinalAuthority
  ) where

import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Phil.Assurance.Types
  ( AssuranceLedger
  , AssuranceManifest (..)
  , VerificationContext
  )
import Phil.Core.Generic
  ( GenericApplicationIdentity (..)
  , GenericStaticParameterKey (..)
  , GenericDischargeLineage (..)
  )
import Phil.Core.Static
  ( DeclarationIdentity (..)
  , ArchitectureInstanceDescriptor (..)
  , deriveArchitectureInstanceIdentity
  )
import Phil.Verification
  ( ApplicationAssurancePolicy
  )
import Phil.Verification.ArtifactClosure
  ( CertifiedApplicationArtifact
  , certifiedApplicationSourceAssurance
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
-- that exact verification bundle. The private constructor also retains the
-- COMPLETE accepted source assurance for the independently accepted consumer.
-- This does not prove generic actuals map to architecture instance bindings.
data CertifiedSourceManifestBinding = CertifiedSourceManifestBinding
  GenericApplicationAssurance
  AssuranceManifest
  deriving (Eq, Show)

sourceManifestBindingManifest :: CertifiedSourceManifestBinding -> AssuranceManifest
sourceManifestBindingManifest (CertifiedSourceManifestBinding _ manifest) = manifest

data SourceManifestBindingError
  = SourceManifestDeclarationNotInVerificationBundle DeclarationIdentity
  | SourceManifestInstanceDeclarationMismatch DeclarationIdentity DeclarationIdentity
  | SourceManifestStaticArgumentsMismatch
  | SourceManifestInstanceNotInVerificationBundle
  | SourceManifestClosureRejected ManifestClosureError
  | SourceManifestSourceAssuranceMismatch
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
  pure (CertifiedSourceManifestBinding source manifest)

-- | Stronger closeout of one exact generic application against an actual
-- architecture instance descriptor. The descriptor is checked against the
-- bundle's stored canonical instance identity, rather than trusted by name.
-- The static-argument map must equal the instance bindings in full: no
-- omissions, additional parameters, or silently ignored source arguments.
closeSourceManifestBindingForInstance
  :: GenericApplicationAssurance
  -> ArchitectureInstanceDescriptor
  -> VerificationBundle
  -> ApplicationAssurancePolicy
  -> VerificationContext
  -> AssuranceLedger
  -> ManifestClosureSelection
  -> Either SourceManifestBindingError CertifiedSourceManifestBinding
closeSourceManifestBindingForInstance source descriptor bundle policy context ledger selection = do
  let lineage = genericApplicationAssuranceLineage source
      application = genericDischargeApplicationIdentity lineage
      declaration = DeclarationIdentity
        { identityDeclarationKey = genericApplicationDeclarationKey application
        , identityInterfaceRevision = genericApplicationInterfaceRevision application
        , identityDefinitionRevision = genericDischargeDefinitionRevision lineage
        }
      descriptorDeclaration = architectureDeclarationIdentity descriptor
      sourceBindings = Map.fromList
        [ (unGenericStaticParameterKey key, value)
        | (key, value) <- Map.toAscList (genericApplicationSemanticArguments application)
        ]
      instanceIdentity = deriveArchitectureInstanceIdentity descriptor
  if declaration == descriptorDeclaration
    then Right ()
    else Left (SourceManifestInstanceDeclarationMismatch declaration descriptorDeclaration)
  if sourceBindings == architectureStaticBindings descriptor
    then Right ()
    else Left SourceManifestStaticArgumentsMismatch
  if Set.member instanceIdentity (verificationBundleArchitectureInstances bundle)
    then Right ()
    else Left SourceManifestInstanceNotInVerificationBundle
  closeSourceManifestBinding source bundle policy context ledger selection

-- | The final adapter must consume the same produced manifest, not a second
-- independently supplied manifest with a caller-selected identity pair.
bindProducedFinalAuthority
  :: CertifiedSourceManifestBinding
  -> CertifiedApplicationArtifact
  -> CertifiedReleaseArtifact
  -> Either SourceManifestBindingError NativeFinalAuthority
bindProducedFinalAuthority (CertifiedSourceManifestBinding producedSource manifest) sourceArtifact release = do
  -- Retain the complete checked source proof, not only the same
  -- application identity. The exported low-level binder must fail closed
  -- independently of the high-level final-instance wrapper.
  if producedSource == certifiedApplicationSourceAssurance sourceArtifact
    then Right ()
    else Left SourceManifestSourceAssuranceMismatch
  if certifiedReleaseManifest release == manifest
    then Right ()
    else Left SourceManifestReleaseManifestMismatch
  let sourceId = genericDischargeApplicationIdentity
        (genericApplicationAssuranceLineage producedSource)
  either (Left . SourceManifestNativeBindingRejected) Right $
    bindNativeFinalAuthority
      (ExpectedSourceManifestAssociation sourceId (manifestId manifest))
      sourceArtifact
      release
