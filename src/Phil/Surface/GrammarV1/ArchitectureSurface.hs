module Phil.Surface.GrammarV1.ArchitectureSurface
  ( GrammarV1CheckedArchitectureRoleTarget (..)
  , GrammarV1CheckedArchitectureItem (..)
  , GrammarV1CheckedArchitectureSurface (..)
  , grammarV1CheckedArchitectureSurface
  ) where

import qualified Data.Text as Text
import Data.Text (Text)
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual
  )
import Phil.Core.Static
  ( DeclarationKey
  , DefinitionRevision
  , StaticContext
  )
import Phil.Core.Syntax
  ( Proposition
  , RefTerm
  , Ty
  )
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.BoundRefExpression
  ( grammarV1BoundRefExpression
  )
import Phil.Surface.GrammarV1.CheckedProposition
  ( grammarV1CheckedProposition
  )
import Phil.Surface.GrammarV1.CheckedType
  ( grammarV1CheckedType
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1BareStaticReferenceActual
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ArchitectureDecl (..)
  , GrammarV1ArchitectureItem (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1RoleTarget (..)
  , GrammarV1StaticArgument (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Preserve explicit internal-versus-external protocol participation without
-- resolving an internal participant or inventing an external transport/boundary.
data GrammarV1CheckedArchitectureRoleTarget
  = GrammarV1CheckedInternalRoleTarget Text
  | GrammarV1CheckedExternalRoleTarget
  deriving (Eq, Show)

-- | Checked bounded meaning of one closed architecture item. Static references
-- remain unresolved identity-bearing references. Qualified names remain exact
-- lookup identities. Proposition/type payloads are checked through their
-- competent existing bridges. Grant values use only the existing bounded RefTerm
-- expression fragment; acceptance here does not establish authority possession
-- or authorize a grant transition.
data GrammarV1CheckedArchitectureItem
  = GrammarV1CheckedArchitectureInstance Text GenericStaticActual
  | GrammarV1CheckedArchitectureRef Text Text
  | GrammarV1CheckedArchitectureProcess Text Text
  | GrammarV1CheckedArchitectureProtocol Text GenericStaticActual
  | GrammarV1CheckedArchitectureRole Text GrammarV1CheckedArchitectureRoleTarget
  | GrammarV1CheckedArchitectureBind Text Text
  | GrammarV1CheckedArchitectureBoundary Text Text
  | GrammarV1CheckedArchitectureObservable Text
  | GrammarV1CheckedArchitectureAssume Proposition Text [FocusStep]
  | GrammarV1CheckedArchitectureConstraint Proposition [FocusStep]
  | GrammarV1CheckedArchitectureEntry Text Ty [FocusStep]
  | GrammarV1CheckedArchitectureAuthority Text Ty Text [FocusStep]
  | GrammarV1CheckedArchitectureGrant Text RefTerm
  | GrammarV1CheckedArchitectureExportObligation Text Text
  deriving (Eq, Show)

-- | One closed source architecture before occurrence creation, graph checking,
-- assumption admission, authority possession, process activation, or realization.
-- Stable declaration/definition lineage is caller supplied and never derived from
-- the source display name.
data GrammarV1CheckedArchitectureSurface = GrammarV1CheckedArchitectureSurface
  { checkedArchitectureDeclarationKey :: DeclarationKey
  , checkedArchitectureDefinitionRevision :: DefinitionRevision
  , checkedArchitectureDisplayName :: Text
  , checkedArchitectureItems :: [GrammarV1CheckedArchitectureItem]
  }
  deriving (Eq, Show)

-- | Route the bounded closed architecture declaration surface through existing
-- checked type/proposition/reference-expression bridges while preserving source
-- item order. Generic parameters and requirements remain outside this slice.
-- Bare/qualified unspecialized instance and protocol references are preserved as
-- unresolved static actuals; specialized applications remain fail-closed until
-- canonical static-argument semantics exist.
--
-- This function does not create InstanceKey/ProcessKey identity, resolve refs,
-- instantiate children/protocols, validate role bindings, establish wiring or
-- boundary correspondence, admit assumptions, enforce constraints, establish
-- entry ownership, construct possessed capabilities, authorize grants, discharge
-- exported obligations, establish observability, or choose a realization.
grammarV1CheckedArchitectureSurface
  :: StaticContext
  -> DeclarationKey
  -> DefinitionRevision
  -> GrammarV1ArchitectureDecl
  -> Maybe (Either FocusingError GrammarV1CheckedArchitectureSurface)
grammarV1CheckedArchitectureSurface
    staticContext declarationKey definitionRevision source
  | not (null (grammarV1ArchitectureGenericParams source)) = Nothing
  | not (null (grammarV1ArchitectureRequirements source)) = Nothing
  | otherwise = do
      checkedItems <- collect (map checkItem (grammarV1ArchitectureItems source))
      pure $ fmap
        (\items -> GrammarV1CheckedArchitectureSurface
          { checkedArchitectureDeclarationKey = declarationKey
          , checkedArchitectureDefinitionRevision = definitionRevision
          , checkedArchitectureDisplayName = locatedValue (grammarV1ArchitectureName source)
          , checkedArchitectureItems = items
          })
        checkedItems
  where
    checkItem (Located _ item) = case item of
      GrammarV1ArchitectureInstance sourceName sourceTarget -> do
        target <- grammarV1BareStaticReferenceActual
          (GrammarV1StaticReferenceArgument (locatedValue sourceTarget))
        pure (Right
          (GrammarV1CheckedArchitectureInstance (locatedValue sourceName) target))
      GrammarV1ArchitectureRef sourceName sourceTarget -> do
        target <- qualifiedNameText (locatedValue sourceTarget)
        pure (Right
          (GrammarV1CheckedArchitectureRef (locatedValue sourceName) target))
      GrammarV1ArchitectureProcess sourceName sourceTarget -> do
        target <- qualifiedNameText (locatedValue sourceTarget)
        pure (Right
          (GrammarV1CheckedArchitectureProcess (locatedValue sourceName) target))
      GrammarV1ArchitectureProtocol sourceName sourceTarget -> do
        target <- grammarV1BareStaticReferenceActual
          (GrammarV1StaticReferenceArgument (locatedValue sourceTarget))
        pure (Right
          (GrammarV1CheckedArchitectureProtocol (locatedValue sourceName) target))
      GrammarV1ArchitectureRole sourceRole sourceTarget -> do
        role <- qualifiedNameText (locatedValue sourceRole)
        target <- checkedRoleTarget (locatedValue sourceTarget)
        pure (Right (GrammarV1CheckedArchitectureRole role target))
      GrammarV1ArchitectureBind sourceName sourceTarget -> do
        name <- qualifiedNameText (locatedValue sourceName)
        target <- qualifiedNameText (locatedValue sourceTarget)
        pure (Right (GrammarV1CheckedArchitectureBind name target))
      GrammarV1ArchitectureBoundary sourceName sourceTarget -> do
        name <- qualifiedNameText (locatedValue sourceName)
        target <- qualifiedNameText (locatedValue sourceTarget)
        pure (Right (GrammarV1CheckedArchitectureBoundary name target))
      GrammarV1ArchitectureObservable sourceTarget -> do
        target <- qualifiedNameText (locatedValue sourceTarget)
        pure (Right (GrammarV1CheckedArchitectureObservable target))
      GrammarV1ArchitectureAssume sourceProposition sourceScope -> do
        checked <- grammarV1CheckedProposition
          staticContext emptySurfaceState (locatedValue sourceProposition)
        scope <- qualifiedNameText (locatedValue sourceScope)
        pure $ fmap
          (\(proposition, steps) ->
            GrammarV1CheckedArchitectureAssume proposition scope steps)
          checked
      GrammarV1ArchitectureConstraint sourceProposition -> do
        checked <- grammarV1CheckedProposition
          staticContext emptySurfaceState (locatedValue sourceProposition)
        pure $ fmap
          (\(proposition, steps) ->
            GrammarV1CheckedArchitectureConstraint proposition steps)
          checked
      GrammarV1ArchitectureEntry sourceName sourceType -> do
        checked <- grammarV1CheckedType
          staticContext emptySurfaceState (locatedValue sourceType)
        pure $ fmap
          (\(ty, steps) ->
            GrammarV1CheckedArchitectureEntry (locatedValue sourceName) ty steps)
          checked
      GrammarV1ArchitectureAuthority sourceName sourceType sourceOrigin -> do
        checked <- grammarV1CheckedType
          staticContext emptySurfaceState (locatedValue sourceType)
        origin <- qualifiedNameText (locatedValue sourceOrigin)
        pure $ fmap
          (\(ty, steps) ->
            GrammarV1CheckedArchitectureAuthority
              (locatedValue sourceName) ty origin steps)
          checked
      GrammarV1ArchitectureGrant sourceTarget sourceValue -> do
        target <- qualifiedNameText (locatedValue sourceTarget)
        value <- grammarV1BoundRefExpression emptySurfaceState sourceValue
        pure (Right (GrammarV1CheckedArchitectureGrant target value))
      GrammarV1ArchitectureExportObligation sourceObligation sourceTarget -> do
        obligation <- qualifiedNameText (locatedValue sourceObligation)
        target <- qualifiedNameText (locatedValue sourceTarget)
        pure (Right
          (GrammarV1CheckedArchitectureExportObligation obligation target))

checkedRoleTarget
  :: GrammarV1RoleTarget
  -> Maybe GrammarV1CheckedArchitectureRoleTarget
checkedRoleTarget source = case source of
  GrammarV1InternalRoleTarget target ->
    GrammarV1CheckedInternalRoleTarget
      <$> qualifiedNameText (locatedValue target)
  GrammarV1ExternalRoleTarget -> Just GrammarV1CheckedExternalRoleTarget

qualifiedNameText :: GrammarV1QualifiedName -> Maybe Text
qualifiedNameText source =
  case grammarV1QualifiedNameParts source of
    [] -> Nothing
    parts -> Just (Text.intercalate (Text.singleton '.') parts)

collect :: [Maybe (Either e a)] -> Maybe (Either e [a])
collect [] = Just (Right [])
collect (candidate : rest) = do
  value <- candidate
  case value of
    Left err -> pure (Left err)
    Right accepted -> do
      remaining <- collect rest
      pure ((accepted :) <$> remaining)
