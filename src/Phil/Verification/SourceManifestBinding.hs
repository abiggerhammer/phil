{-# LANGUAGE OverloadedStrings #-}

module Phil.Verification.SourceManifestBinding
  ( CertifiedSourceManifestBinding
  , sourceManifestBindingManifest
  , sourceManifestBindingSourceAssurance
  , sourceManifestBindingArchitectureInstance
  , sourceManifestBindingArchitectureDescriptor
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
  , ArchitectureInstanceIdentity
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
-- Declaration-only closure has no checked architecture-instance binding;
-- only the checked actuals/descriptor/bundle producer can attach the COMPLETE
-- descriptor, including semantic bindings and declaration lineage. An identity
-- projection would discard those inputs before faithful representation.
-- Even the retained descriptor does NOT establish stage-production lineage.
data CertifiedSourceManifestBinding = CertifiedSourceManifestBinding
  GenericApplicationAssurance
  AssuranceManifest
  (Maybe ArchitectureInstanceDescriptor)
  deriving (Eq, Show)

sourceManifestBindingManifest :: CertifiedSourceManifestBinding -> AssuranceManifest
sourceManifestBindingManifest (CertifiedSourceManifestBinding _ manifest _) = manifest

-- | The complete accepted source-assurance object attached to the checked
-- manifest producer; identity alone would lose checked body evidence.
-- This projection does not certify any concrete stage-production origin.
sourceManifestBindingSourceAssurance
  :: CertifiedSourceManifestBinding -> GenericApplicationAssurance
sourceManifestBindingSourceAssurance (CertifiedSourceManifestBinding source _ _) = source

-- | Derived identity of the retained, checked canonical descriptor. The
-- token cannot carry an arbitrary independently supplied identity.
sourceManifestBindingArchitectureInstance
  :: CertifiedSourceManifestBinding -> Maybe ArchitectureInstanceIdentity
sourceManifestBindingArchitectureInstance =
  fmap deriveArchitectureInstanceIdentity . sourceManifestBindingArchitectureDescriptor

-- | Complete checked descriptor, preserving declaration and semantic actuals
-- for later competent representation. Its presence is producer-gated, not
-- proof that this occurrence produced the downstream StageClosure.
sourceManifestBindingArchitectureDescriptor
  :: CertifiedSourceManifestBinding -> Maybe ArchitectureInstanceDescriptor
sourceManifestBindingArchitectureDescriptor
  (CertifiedSourceManifestBinding _ _ descriptor) = descriptor

data SourceManifestBindingError
  = SourceManifestDeclarationNotInVerificationBundle DeclarationIdentity
  | SourceManifestInstanceDeclarationMismatch DeclarationIdentity DeclarationIdentity
  | SourceManifestStaticArgumentsMismatch
  | SourceManifestInstanceNotInVerificationBundle
  | SourceManifestClosureRejected ManifestClosureError
  | SourceManifestSourceAssuranceMismatch
  | SourceManifestInstanceNotBound
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
  pure (CertifiedSourceManifestBinding source manifest Nothing)

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
  baseBinding <- closeSourceManifestBinding source bundle policy context ledger selection
  pure (CertifiedSourceManifestBinding
    source (sourceManifestBindingManifest baseBinding) (Just descriptor))

-- | The final adapter consumes only a *checked-instance* source manifest,
-- not the weaker declaration-only closure. This is a necessary producer gate,
-- not independent occurrence-to-concrete-stage provenance.
-- The manifest must be the exact produced manifest, never a caller-chosen pair.
bindProducedFinalAuthority
  :: CertifiedSourceManifestBinding
  -> CertifiedApplicationArtifact
  -> CertifiedReleaseArtifact
  -> Either SourceManifestBindingError NativeFinalAuthority
bindProducedFinalAuthority (CertifiedSourceManifestBinding producedSource manifest maybeInstance) sourceArtifact release = do
  case maybeInstance of
    Nothing -> Left SourceManifestInstanceNotBound
    Just _ -> Right ()
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
