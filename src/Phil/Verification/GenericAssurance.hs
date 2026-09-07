{-# LANGUAGE OverloadedStrings #-}

module Phil.Verification.GenericAssurance
  ( GenericPublicRequirementRevision (..)
  , deriveGenericPublicRequirementRevision
  , ReusableGenericBodyAssurance
  , reusableGenericBodyAssuranceId
  , reusableGenericBodyDeclarationKey
  , reusableGenericBodyInterfaceRevision
  , reusableGenericBodyDefinitionRevision
  , reusableGenericBodyRequirementRevisions
  , reusableGenericBodyEvidenceArtifact
  , GenericBodyAssuranceError (..)
  , prepareReusableGenericBodyAssurance
  , GenericApplicationAssurance
  , genericApplicationAssuranceBody
  , genericApplicationAssuranceLineage
  , GenericAssuranceReuseError (..)
  , composeGenericApplicationAssurance
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
  ( ArtifactIdentity (..)
  , ArtifactRef (..)
  , Digest (..)
  , digestText
  , renderPropositionCanonical
  )
import Phil.Core.Generic
  ( GenericApplicationIdentity (..)
  , GenericDischargeLineage (..)
  , GenericRequirement (..)
  , GenericStaticParameterKey (..)
  , GenericStructuralRequirements
  , GenericValueParameterKey (..)
  , StructuralPermission (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , DefinitionRevision (..)
  , InterfaceRevision (..)
  )

-- | Content-bound revision of one public requirement in the exact generic
-- declaration/interface contract where it is published.  The same proposition
-- or provider constraint published by a different generic/interface therefore
-- has a different revision.
newtype GenericPublicRequirementRevision = GenericPublicRequirementRevision
  { unGenericPublicRequirementRevision :: Digest
  }
  deriving (Eq, Ord, Show)

-- | Derive an exact public-requirement revision without depending on source
-- formatting, container traversal, proof-search order, or backend realization.
deriveGenericPublicRequirementRevision
  :: DeclarationKey
  -> InterfaceRevision
  -> GenericRequirement
  -> GenericPublicRequirementRevision
deriveGenericPublicRequirementRevision declarationKey interfaceRevision requirement =
  GenericPublicRequirementRevision (digestText (Text.intercalate "\n"
    [ "phil.generic.public-requirement.v1"
    , "declaration=" <> unDeclarationKey declarationKey
    , "interface=" <> unInterfaceRevision interfaceRevision
    , "requirement=" <> renderGenericRequirement requirement
    ]))

-- | One reusable conditional assurance artifact for a generic body.  Its
-- identity deliberately excludes ordinary application actuals, per-application
-- discharge evidence, architecture occurrence, monomorphization identity, and
-- backend realization.  Those belong to application lineage or later stages.
data ReusableGenericBodyAssurance = ReusableGenericBodyAssurance
  Digest
  DeclarationKey
  InterfaceRevision
  DefinitionRevision
  (Map GenericRequirement GenericPublicRequirementRevision)
  ArtifactIdentity
  deriving (Eq, Ord, Show)

reusableGenericBodyAssuranceId :: ReusableGenericBodyAssurance -> Digest
reusableGenericBodyAssuranceId
  (ReusableGenericBodyAssurance assuranceId _ _ _ _ _) = assuranceId

reusableGenericBodyDeclarationKey :: ReusableGenericBodyAssurance -> DeclarationKey
reusableGenericBodyDeclarationKey
  (ReusableGenericBodyAssurance _ declarationKey _ _ _ _) = declarationKey

reusableGenericBodyInterfaceRevision :: ReusableGenericBodyAssurance -> InterfaceRevision
reusableGenericBodyInterfaceRevision
  (ReusableGenericBodyAssurance _ _ interfaceRevision _ _ _) = interfaceRevision

reusableGenericBodyDefinitionRevision :: ReusableGenericBodyAssurance -> DefinitionRevision
reusableGenericBodyDefinitionRevision
  (ReusableGenericBodyAssurance _ _ _ definitionRevision _ _) = definitionRevision

reusableGenericBodyRequirementRevisions
  :: ReusableGenericBodyAssurance
  -> Map GenericRequirement GenericPublicRequirementRevision
reusableGenericBodyRequirementRevisions
  (ReusableGenericBodyAssurance _ _ _ _ revisions _) = revisions

reusableGenericBodyEvidenceArtifact :: ReusableGenericBodyAssurance -> ArtifactIdentity
reusableGenericBodyEvidenceArtifact
  (ReusableGenericBodyAssurance _ _ _ _ _ artifact) = artifact

data GenericBodyAssuranceError
  = GenericBodyAssuranceEmptyDeclarationKey
  | GenericBodyAssuranceEmptyInterfaceRevision
  | GenericBodyAssuranceEmptyDefinitionRevision
  | GenericBodyAssuranceEmptyArtifactReference
  | GenericBodyAssuranceEmptyArtifactDigest
  deriving (Eq, Ord, Show)

-- | Prepare a reusable body-assurance artifact from exact generic semantic
-- identity, exact public requirements, and an ADR-010 content-bound artifact.
-- Application identities and their requirement discharge are intentionally not
-- inputs, so ordinary applications cannot duplicate or rekey the body proof.
prepareReusableGenericBodyAssurance
  :: DeclarationKey
  -> InterfaceRevision
  -> DefinitionRevision
  -> Set GenericRequirement
  -> ArtifactIdentity
  -> Either GenericBodyAssuranceError ReusableGenericBodyAssurance
prepareReusableGenericBodyAssurance declarationKey interfaceRevision definitionRevision requirements artifact
  | blank (unDeclarationKey declarationKey) = Left GenericBodyAssuranceEmptyDeclarationKey
  | blank (unInterfaceRevision interfaceRevision) = Left GenericBodyAssuranceEmptyInterfaceRevision
  | blank (unDefinitionRevision definitionRevision) = Left GenericBodyAssuranceEmptyDefinitionRevision
  | blank (unArtifactRef (artifactReference artifact)) = Left GenericBodyAssuranceEmptyArtifactReference
  | blank (unDigest (artifactDigest artifact)) = Left GenericBodyAssuranceEmptyArtifactDigest
  | otherwise = Right
      (ReusableGenericBodyAssurance
        assuranceId
        declarationKey
        interfaceRevision
        definitionRevision
        requirementRevisions
        artifact)
  where
    requirementRevisions = Map.fromSet
      (deriveGenericPublicRequirementRevision declarationKey interfaceRevision)
      requirements
    assuranceId = digestText (Text.intercalate "\n"
      [ "phil.generic.body-assurance.v1"
      , "declaration=" <> unDeclarationKey declarationKey
      , "interface=" <> unInterfaceRevision interfaceRevision
      , "definition=" <> unDefinitionRevision definitionRevision
      , "requirements=" <> Text.intercalate ","
          [ unDigest (unGenericPublicRequirementRevision revision)
          | revision <- Map.elems requirementRevisions
          ]
      , "artifact-ref=" <> unArtifactRef (artifactReference artifact)
      , "artifact-digest=" <> unDigest (artifactDigest artifact)
      ])
    blank = Text.null . Text.strip

-- | One exact ordinary generic application composed with the shared body
-- assurance artifact and its own checked discharge lineage.  There is no
-- backend/monomorphization field by design: realization cannot multiply
-- source-level generic-body assurance claims.
data GenericApplicationAssurance = GenericApplicationAssurance
  ReusableGenericBodyAssurance
  GenericDischargeLineage
  deriving (Eq, Ord, Show)

genericApplicationAssuranceBody
  :: GenericApplicationAssurance
  -> ReusableGenericBodyAssurance
genericApplicationAssuranceBody (GenericApplicationAssurance body _) = body

genericApplicationAssuranceLineage
  :: GenericApplicationAssurance
  -> GenericDischargeLineage
genericApplicationAssuranceLineage (GenericApplicationAssurance _ lineage) = lineage

data GenericAssuranceReuseError
  = GenericAssuranceDeclarationMismatch DeclarationKey DeclarationKey
  | GenericAssuranceInterfaceMismatch InterfaceRevision InterfaceRevision
  | GenericAssuranceDefinitionMismatch DefinitionRevision DefinitionRevision
  | GenericAssurancePublicRequirementRevisionMismatch
      (Map GenericRequirement GenericPublicRequirementRevision)
      (Map GenericRequirement GenericPublicRequirementRevision)
  | GenericAssuranceDispositionDomainMismatch
      (Set GenericRequirement)
      (Set GenericRequirement)
  deriving (Eq, Ord, Show)

-- | Compose one application with a reusable conditional body artifact.  The
-- body artifact remains reusable only when its generic definition and public
-- requirement revisions are exact.  The application's own checked disposition
-- map must close exactly that public requirement domain.  Distinct applications
-- may therefore share the body artifact while retaining distinct lineage.
composeGenericApplicationAssurance
  :: ReusableGenericBodyAssurance
  -> Set GenericRequirement
  -> GenericDischargeLineage
  -> Either GenericAssuranceReuseError GenericApplicationAssurance
composeGenericApplicationAssurance body currentRequirements lineage
  | applicationDeclaration /= bodyDeclaration =
      Left (GenericAssuranceDeclarationMismatch bodyDeclaration applicationDeclaration)
  | applicationInterface /= bodyInterface =
      Left (GenericAssuranceInterfaceMismatch bodyInterface applicationInterface)
  | lineageDefinition /= bodyDefinition =
      Left (GenericAssuranceDefinitionMismatch bodyDefinition lineageDefinition)
  | currentRequirementRevisions /= bodyRequirementRevisions =
      Left
        (GenericAssurancePublicRequirementRevisionMismatch
          bodyRequirementRevisions
          currentRequirementRevisions)
  | dispositionDomain /= expectedDomain =
      Left
        (GenericAssuranceDispositionDomainMismatch
          expectedDomain
          dispositionDomain)
  | otherwise = Right (GenericApplicationAssurance body lineage)
  where
    application = genericDischargeApplicationIdentity lineage
    applicationDeclaration = genericApplicationDeclarationKey application
    applicationInterface = genericApplicationInterfaceRevision application
    lineageDefinition = genericDischargeDefinitionRevision lineage
    bodyDeclaration = reusableGenericBodyDeclarationKey body
    bodyInterface = reusableGenericBodyInterfaceRevision body
    bodyDefinition = reusableGenericBodyDefinitionRevision body
    bodyRequirementRevisions = reusableGenericBodyRequirementRevisions body
    currentRequirementRevisions = Map.fromSet
      (deriveGenericPublicRequirementRevision bodyDeclaration bodyInterface)
      currentRequirements
    expectedDomain = Map.keysSet bodyRequirementRevisions
    dispositionDomain = Map.keysSet (genericDischargeDispositions lineage)

renderGenericRequirement :: GenericRequirement -> Text
renderGenericRequirement requirement = case requirement of
  GenericStructuralRequirement key permission -> Text.intercalate ":"
    [ "structural"
    , unGenericValueParameterKey key
    , renderStructuralPermission permission
    ]
  GenericProviderContractRequirement key requiredInterface -> Text.intercalate ":"
    [ "provider"
    , unGenericStaticParameterKey key
    , unInterfaceRevision requiredInterface
    ]
  GenericPropositionRequirement proposition ->
    "proposition:" <> renderPropositionCanonical proposition

renderStructuralPermission :: StructuralPermission -> Text
renderStructuralPermission permission = case permission of
  WeakeningPermission -> "weakening"
  ContractionPermission -> "contraction"
