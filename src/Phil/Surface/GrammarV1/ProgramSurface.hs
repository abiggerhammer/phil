module Phil.Surface.GrammarV1.ProgramSurface
  ( GrammarV1CheckedProgramItem (..)
  , GrammarV1CheckedProgramSurface (..)
  , grammarV1CheckedProgramSurface
  ) where

import qualified Data.Text as Text
import Data.Text (Text)
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual
  , GenericStaticKind (..)
  )
import Phil.Core.Static
  ( DeclarationKey
  , DefinitionRevision
  , StaticContext
  )
import Phil.Core.Syntax
  ( Proposition
  , Ty
  )
import Phil.Surface.Check.Support (emptySurfaceState)
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
  ( GrammarV1ProgramDecl (..)
  , GrammarV1ProgramItem (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1StaticArgument (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Checked semantic surface of one closed program-root item. Entries carry
-- checked type meaning but not ownership/mode admission. Assumptions carry an
-- exactly checked proposition plus unresolved scope spelling; this does not admit
-- the proposition as evidence. Exported obligations and observables preserve only
-- their exact unresolved qualified lookup spellings at this boundary.
data GrammarV1CheckedProgramItem
  = GrammarV1CheckedProgramEntry Text Ty [FocusStep]
  | GrammarV1CheckedProgramAssume Proposition Text [FocusStep]
  | GrammarV1CheckedProgramExportObligation Text Text
  | GrammarV1CheckedProgramObservable Text
  deriving (Eq, Show)

-- | One checked closed Grammar-v1 program root before architecture instantiation
-- or assurance discharge. Stable declaration/definition lineage is supplied by
-- the authority above Grammar v1; source display spelling never constructs it.
-- The program target remains an unresolved architecture-category static
-- reference, preserving the exact source lookup spelling without claiming that a
-- corresponding architecture exists or that instantiation has occurred.
data GrammarV1CheckedProgramSurface = GrammarV1CheckedProgramSurface
  { checkedProgramDeclarationKey :: DeclarationKey
  , checkedProgramDefinitionRevision :: DefinitionRevision
  , checkedProgramDisplayName :: Text
  , checkedProgramTargetKind :: GenericStaticKind
  , checkedProgramTargetReference :: GenericStaticActual
  , checkedProgramItems :: [GrammarV1CheckedProgramItem]
  }
  deriving (Eq, Show)

-- | Route the bounded closed program-root surface through already-established
-- type/proposition checkers. Entry types and assumption propositions are checked
-- under an empty top-level term scope in source order; the first Core focusing
-- rejection remains an explicit Left. A bare/qualified unspecialized target is
-- preserved as one unresolved architecture reference. Specialized architecture
-- targets remain fail-closed until generic static-argument elaboration is
-- competent.
--
-- This bridge does not instantiate the architecture, create InstanceKey or
-- InstanceRevision, establish entry ownership/modes, admit assumptions, close or
-- export obligations, establish observability, bind runtime resources, or select
-- a target realization.
grammarV1CheckedProgramSurface
  :: StaticContext
  -> DeclarationKey
  -> DefinitionRevision
  -> GrammarV1ProgramDecl
  -> Maybe (Either FocusingError GrammarV1CheckedProgramSurface)
grammarV1CheckedProgramSurface
    staticContext declarationKey definitionRevision source = do
  targetReference <- grammarV1BareStaticReferenceActual
    (GrammarV1StaticReferenceArgument
      (locatedValue (grammarV1ProgramTarget source)))
  checkedItems <- collect (map checkItem (grammarV1ProgramItems source))
  pure $ fmap
    (\items -> GrammarV1CheckedProgramSurface
      { checkedProgramDeclarationKey = declarationKey
      , checkedProgramDefinitionRevision = definitionRevision
      , checkedProgramDisplayName = locatedValue (grammarV1ProgramName source)
      , checkedProgramTargetKind = GenericArchitectureDependencyKind
      , checkedProgramTargetReference = targetReference
      , checkedProgramItems = items
      })
    checkedItems
  where
    checkItem (Located _ item) = case item of
      GrammarV1ProgramEntry sourceName sourceType -> do
        checked <- grammarV1CheckedType
          staticContext
          emptySurfaceState
          (locatedValue sourceType)
        pure $ fmap
          (\(ty, steps) ->
            GrammarV1CheckedProgramEntry (locatedValue sourceName) ty steps)
          checked
      GrammarV1ProgramAssume sourceProposition sourceScope -> do
        checked <- grammarV1CheckedProposition
          staticContext
          emptySurfaceState
          (locatedValue sourceProposition)
        scope <- qualifiedNameText (locatedValue sourceScope)
        pure $ fmap
          (\(proposition, steps) ->
            GrammarV1CheckedProgramAssume proposition scope steps)
          checked
      GrammarV1ProgramExportObligation sourceObligation sourceTarget -> do
        obligation <- qualifiedNameText (locatedValue sourceObligation)
        target <- qualifiedNameText (locatedValue sourceTarget)
        pure (Right (GrammarV1CheckedProgramExportObligation obligation target))
      GrammarV1ProgramObservable sourceTarget -> do
        target <- qualifiedNameText (locatedValue sourceTarget)
        pure (Right (GrammarV1CheckedProgramObservable target))

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
