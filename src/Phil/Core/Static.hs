{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Static
  ( ClaimDefinition (..)
  , ClaimDecl (..)
  , StaticContext (..)
  , StaticError (..)
  , SemanticForm (..)
  , DeclarationKey (..)
  , InterfaceRevision (..)
  , DefinitionRevision (..)
  , InstanceKey (..)
  , InstanceRevision (..)
  , RealizationRevision (..)
  , DeclarationPresentation (..)
  , DeclarationDescriptor (..)
  , DeclarationIdentity (..)
  , ArchitectureInstanceDescriptor (..)
  , ArchitectureInstanceIdentity (..)
  , ArchitectureRealizationDescriptor (..)
  , ArchitectureRealizationIdentity (..)
  , canonicalSemanticForm
  , deriveDeclarationIdentity
  , deriveArchitectureInstanceIdentity
  , deriveArchitectureRealizationIdentity
  , emptyStaticContext
  , declareTransparentClaim
  , declareOpaqueClaim
  , lookupClaim
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.SortCheck (SortError, validateRefSort)
import Phil.Core.Syntax
  ( Name
  , Proposition
  , RefSort
  )

data ClaimDefinition
  = TransparentClaim Proposition
  | OpaqueClaim
  deriving (Eq, Ord, Show)

data ClaimDecl = ClaimDecl
  { claimParameters :: [(Name, RefSort)]
  , claimDefinition :: ClaimDefinition
  }
  deriving (Eq, Ord, Show)

newtype StaticContext = StaticContext
  { staticClaims :: Map.Map Text ClaimDecl
  }
  deriving (Eq, Show)

data StaticError
  = DuplicateClaim Text
  | DuplicateClaimParameter Text Name
  | InvalidClaimParameterSort Text Name RefSort SortError
  deriving (Eq, Show)

-- | A target-independent canonical semantic value used when deriving exact
-- Phase 1 declaration, instance, and realization revisions.  The constructors
-- distinguish ordered data, set-like data, and named fields so that callers do
-- not have to rely on source text, source order, or container iteration order.
data SemanticForm
  = SemanticAtom Text
  | SemanticOrdered [SemanticForm]
  | SemanticUnordered (Set.Set SemanticForm)
  | SemanticRecord (Map.Map Text SemanticForm)
  deriving (Eq, Ord, Show)

newtype DeclarationKey = DeclarationKey { unDeclarationKey :: Text }
  deriving (Eq, Ord, Show)

newtype InterfaceRevision = InterfaceRevision { unInterfaceRevision :: Text }
  deriving (Eq, Ord, Show)

newtype DefinitionRevision = DefinitionRevision { unDefinitionRevision :: Text }
  deriving (Eq, Ord, Show)

newtype InstanceKey = InstanceKey { unInstanceKey :: Text }
  deriving (Eq, Ord, Show)

newtype InstanceRevision = InstanceRevision { unInstanceRevision :: Text }
  deriving (Eq, Ord, Show)

newtype RealizationRevision = RealizationRevision { unRealizationRevision :: Text }
  deriving (Eq, Ord, Show)

-- | Human-facing location data.  It is deliberately carried next to, rather
-- than inside, semantic identity inputs.  Renaming or moving a declaration can
-- therefore preserve identity when elaborated semantics and stable lineage are
-- unchanged.
data DeclarationPresentation = DeclarationPresentation
  { declarationDisplayName :: Text
  , declarationModulePath :: [Text]
  }
  deriving (Eq, Ord, Show)

-- | Minimal checked declaration descriptor for the first Phase 1 identity
-- slice.  The exact source syntax and full architecture graph vocabulary stay
-- deferred; the checked semantic forms are the identity-bearing inputs.
data DeclarationDescriptor = DeclarationDescriptor
  { declarationPresentation :: DeclarationPresentation
  , declarationKey :: DeclarationKey
  , declarationInterfaceSemantics :: SemanticForm
  , declarationDefinitionSemantics :: SemanticForm
  }
  deriving (Eq, Ord, Show)

data DeclarationIdentity = DeclarationIdentity
  { identityDeclarationKey :: DeclarationKey
  , identityInterfaceRevision :: InterfaceRevision
  , identityDefinitionRevision :: DefinitionRevision
  }
  deriving (Eq, Ord, Show)

-- | One exact architecture occurrence.  Parent occurrence identity is stable
-- lineage, not the complete parent revision, so an unrelated sibling edit does
-- not recursively rekey an unaffected child.  Broader evidence may still name
-- the containing architecture revision in its validity context.
data ArchitectureInstanceDescriptor = ArchitectureInstanceDescriptor
  { architectureInstanceKey :: InstanceKey
  , architectureParentInstanceKey :: Maybe InstanceKey
  , architectureDeclarationIdentity :: DeclarationIdentity
  , architectureStaticBindings :: Map.Map Text SemanticForm
  }
  deriving (Eq, Ord, Show)

data ArchitectureInstanceIdentity = ArchitectureInstanceIdentity
  { identityInstanceKey :: InstanceKey
  , identityInstanceRevision :: InstanceRevision
  }
  deriving (Eq, Ord, Show)

-- | Concrete realization choices are deliberately downstream of the abstract
-- architecture occurrence.  Replacing one qualified implementation may change
-- this identity without changing the ArchitectureInstance identity.
data ArchitectureRealizationDescriptor = ArchitectureRealizationDescriptor
  { realizationInstanceIdentity :: ArchitectureInstanceIdentity
  , realizationSemantics :: SemanticForm
  }
  deriving (Eq, Ord, Show)

newtype ArchitectureRealizationIdentity = ArchitectureRealizationIdentity
  { identityRealizationRevision :: RealizationRevision
  }
  deriving (Eq, Ord, Show)

canonicalSemanticForm :: SemanticForm -> Text
canonicalSemanticForm semantic = case semantic of
  SemanticAtom value -> "atom(" <> canonicalAtom value <> ")"
  SemanticOrdered values ->
    "ordered[" <> Text.intercalate "," (map canonicalSemanticForm values) <> "]"
  SemanticUnordered values ->
    "unordered["
      <> Text.intercalate "," (map canonicalSemanticForm (Set.toAscList values))
      <> "]"
  SemanticRecord fields ->
    "record{"
      <> Text.intercalate ","
          [ canonicalAtom field <> "=" <> canonicalSemanticForm value
          | (field, value) <- Map.toAscList fields
          ]
      <> "}"
  where
    canonicalAtom value = Text.pack (show (Text.length value)) <> ":" <> value

deriveDeclarationIdentity :: DeclarationDescriptor -> DeclarationIdentity
deriveDeclarationIdentity descriptor = DeclarationIdentity
  { identityDeclarationKey = declarationKey descriptor
  , identityInterfaceRevision = interfaceRevision
  , identityDefinitionRevision = definitionRevision
  }
  where
    interfaceRevision = InterfaceRevision
      ("phil.interface.canonical.v1:"
        <> canonicalSemanticForm (declarationInterfaceSemantics descriptor))
    definitionRevision = DefinitionRevision
      ("phil.definition.canonical.v1:"
        <> canonicalSemanticForm (SemanticRecord (Map.fromList
          [ ("interface_revision", SemanticAtom (unInterfaceRevision interfaceRevision))
          , ("definition", declarationDefinitionSemantics descriptor)
          ])))

deriveArchitectureInstanceIdentity
  :: ArchitectureInstanceDescriptor
  -> ArchitectureInstanceIdentity
deriveArchitectureInstanceIdentity descriptor = ArchitectureInstanceIdentity
  { identityInstanceKey = architectureInstanceKey descriptor
  , identityInstanceRevision = InstanceRevision
      ("phil.instance.canonical.v1:"
        <> canonicalSemanticForm (SemanticRecord (Map.fromList
          [ ("instance_key", SemanticAtom (unInstanceKey (architectureInstanceKey descriptor)))
          , ("parent_instance_key", maybe (SemanticAtom "")
              (SemanticAtom . unInstanceKey) (architectureParentInstanceKey descriptor))
          , ("declaration_key", SemanticAtom
              (unDeclarationKey (identityDeclarationKey declarationIdentity)))
          , ("interface_revision", SemanticAtom
              (unInterfaceRevision (identityInterfaceRevision declarationIdentity)))
          , ("definition_revision", SemanticAtom
              (unDefinitionRevision (identityDefinitionRevision declarationIdentity)))
          , ("bindings", SemanticRecord (architectureStaticBindings descriptor))
          ])))
  }
  where
    declarationIdentity = architectureDeclarationIdentity descriptor

deriveArchitectureRealizationIdentity
  :: ArchitectureRealizationDescriptor
  -> ArchitectureRealizationIdentity
deriveArchitectureRealizationIdentity descriptor = ArchitectureRealizationIdentity
  { identityRealizationRevision = RealizationRevision
      ("phil.realization.canonical.v1:"
        <> canonicalSemanticForm (SemanticRecord (Map.fromList
          [ ("instance_key", SemanticAtom
              (unInstanceKey (identityInstanceKey instanceIdentity)))
          , ("instance_revision", SemanticAtom
              (unInstanceRevision (identityInstanceRevision instanceIdentity)))
          , ("realization", realizationSemantics descriptor)
          ])))
  }
  where
    instanceIdentity = realizationInstanceIdentity descriptor

emptyStaticContext :: StaticContext
emptyStaticContext = StaticContext Map.empty

declareTransparentClaim
  :: Text
  -> [(Name, RefSort)]
  -> Proposition
  -> StaticContext
  -> Either StaticError StaticContext
declareTransparentClaim name parameters body =
  declareClaim name parameters (TransparentClaim body)

declareOpaqueClaim
  :: Text
  -> [(Name, RefSort)]
  -> StaticContext
  -> Either StaticError StaticContext
declareOpaqueClaim name parameters =
  declareClaim name parameters OpaqueClaim

lookupClaim :: Text -> StaticContext -> Maybe ClaimDecl
lookupClaim name = Map.lookup name . staticClaims

declareClaim
  :: Text
  -> [(Name, RefSort)]
  -> ClaimDefinition
  -> StaticContext
  -> Either StaticError StaticContext
declareClaim name parameters definition context
  | Map.member name (staticClaims context) = Left (DuplicateClaim name)
  | otherwise = do
      ensureUniqueParameters Set.empty parameters
      mapM_ validateParameter parameters
      Right context
        { staticClaims = Map.insert name (ClaimDecl parameters definition) (staticClaims context)
        }
  where
    ensureUniqueParameters _ [] = Right ()
    ensureUniqueParameters seen ((parameter, _) : rest)
      | Set.member parameter seen = Left (DuplicateClaimParameter name parameter)
      | otherwise = ensureUniqueParameters (Set.insert parameter seen) rest

    validateParameter (parameter, sort) =
      case validateRefSort sort of
        Right () -> Right ()
        Left err -> Left (InvalidClaimParameterSort name parameter sort err)
