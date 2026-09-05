module Phil.Surface.GrammarV1.SemanticComponentHeader
  ( GrammarV1CheckedSemanticComponentHeader (..)
  , GrammarV1SemanticComponentHeaderError (..)
  , grammarV1CheckedSemanticComponentHeader
  ) where

import Data.Text (Text)
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static
  ( DeclarationKey
  , DefinitionRevision
  , StaticContext
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Ty
  )
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceCheckError
  , SurfaceShape (..)
  , SurfaceState
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError
  , GrammarV1LexicalScope
  , GrammarV1ResolvedBinder
  , grammarV1ComponentParameterScope
  )
import Phil.Surface.GrammarV1.Elaborate (grammarV1PrimitiveType)
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference
  , GrammarV1LexicalReferenceError
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ComponentDecl (..)
  , GrammarV1TermParam (..)
  , GrammarV1Type
  )
import Phil.Surface.GrammarV1.SemanticBindingState
  ( grammarV1InsertSemanticBinding
  )
import Phil.Surface.GrammarV1.SemanticCheckedType
  ( GrammarV1CheckedSemanticType (..)
  , GrammarV1SemanticCheckedTypeError (..)
  , grammarV1CheckedSemanticType
  )
import Phil.Surface.GrammarV1.SemanticRefinementType
  ( GrammarV1SemanticRefinementTypeError
  )
import Phil.Surface.Syntax (Located (..))

-- | A checked component header whose runtime term parameters have exact SURF-009
-- semantic identity. Omitted versus explicitly empty parameter syntax remains
-- visible in the parameter carrier, while every present parameter is retained as
-- its resolved binder plus checked type. The temporary SurfaceState is keyed only
-- by generated Core names. The retained lexical scope is the post-provides scope:
-- any refinement binder inside the provides type has closed, but its declaration-
-- wide ordinal remains consumed for later component-body binders.
data GrammarV1CheckedSemanticComponentHeader = GrammarV1CheckedSemanticComponentHeader
  { checkedSemanticComponentDeclarationKey :: DeclarationKey
  , checkedSemanticComponentDefinitionRevision :: DefinitionRevision
  , checkedSemanticComponentDisplayName :: Text
  , checkedSemanticComponentParameters :: Maybe [(GrammarV1ResolvedBinder, Ty)]
  , checkedSemanticComponentProvidesType :: Maybe Ty
  , checkedSemanticComponentProvidesReferences :: Maybe [GrammarV1CheckedLexicalReference]
  , checkedSemanticComponentState :: SurfaceState
  , checkedSemanticComponentLexicalScope :: GrammarV1LexicalScope
  }
  deriving (Eq, Show)

data GrammarV1SemanticComponentHeaderError
  = GrammarV1SemanticComponentBinderScopeError GrammarV1BinderScopeError
  | GrammarV1SemanticComponentBindingInsertError SurfaceCheckError
  | GrammarV1SemanticComponentProvidesReferenceError GrammarV1LexicalReferenceError
  | GrammarV1SemanticComponentProvidesRewriteNonCompetent (Located GrammarV1Type)
  | GrammarV1SemanticComponentProvidesFocusingError FocusingError
  | GrammarV1SemanticComponentProvidesRefinementError
      GrammarV1SemanticRefinementTypeError
  deriving (Eq, Show)

-- | Migrate the bounded closed-component header route onto resolver-issued
-- runtime binder identity without changing the older SURF-008 component API.
-- Generic parameters and generic requirements stay outside this bounded slice.
-- Present term parameters retain the existing primitive unrestricted competence,
-- but are inserted under generated semantic names obtained from BinderScope.
--
-- A present `provides` type now delegates to SemanticCheckedType. Ordinary
-- dependent provides retain exact reference evidence and semantic-name rewriting;
-- a top-level primitive-base refinement additionally allocates its local binder in
-- a child lexical scope and returns the enclosing scope with that ordinal consumed.
-- Absence of a provides clause leaves the parameter lexical scope unchanged and
-- remains distinct from an empty reference set on a present closed type.
grammarV1CheckedSemanticComponentHeader
  :: StaticContext
  -> DeclarationKey
  -> DefinitionRevision
  -> GrammarV1ComponentDecl
  -> Maybe
      (Either
        GrammarV1SemanticComponentHeaderError
        (GrammarV1CheckedSemanticComponentHeader, [FocusStep]))
grammarV1CheckedSemanticComponentHeader
    staticContext declarationKey definitionRevision source
  | not (null (grammarV1ComponentGenericParams source)) = Nothing
  | not (null (grammarV1ComponentRequirements source)) = Nothing
  | otherwise =
      case grammarV1ComponentParameterScope declarationKey source of
        Left scopeError ->
          Just (Left (GrammarV1SemanticComponentBinderScopeError scopeError))
        Right (maybeBinders, lexicalScope) -> do
          built <- buildSemanticParameters
            maybeBinders
            (grammarV1ComponentTermParams source)
          case built of
            Left buildError -> Just (Left buildError)
            Right (parameters, semanticState) ->
              case grammarV1ComponentProvides source of
                Nothing -> Just
                  (Right
                    ( buildHeader
                        parameters
                        Nothing
                        Nothing
                        semanticState
                        lexicalScope
                    , []
                    ))
                Just providesSource -> do
                  checkedProvides <- grammarV1CheckedSemanticType
                    staticContext
                    lexicalScope
                    semanticState
                    providesSource
                  pure $ case checkedProvides of
                    Left typeError -> Left (mapProvidesTypeError typeError)
                    Right (semanticProvides, nextLexicalScope) ->
                      Right
                        ( buildHeader
                            parameters
                            (Just (checkedSemanticTypeValue semanticProvides))
                            (Just (checkedSemanticTypeReferences semanticProvides))
                            semanticState
                            nextLexicalScope
                        , checkedSemanticTypeFocusSteps semanticProvides
                        )
  where
    buildHeader parameters providesType providesReferences semanticState lexicalScope =
      GrammarV1CheckedSemanticComponentHeader
        { checkedSemanticComponentDeclarationKey = declarationKey
        , checkedSemanticComponentDefinitionRevision = definitionRevision
        , checkedSemanticComponentDisplayName =
            locatedValue (grammarV1ComponentName source)
        , checkedSemanticComponentParameters = parameters
        , checkedSemanticComponentProvidesType = providesType
        , checkedSemanticComponentProvidesReferences = providesReferences
        , checkedSemanticComponentState = semanticState
        , checkedSemanticComponentLexicalScope = lexicalScope
        }

buildSemanticParameters
  :: Maybe [GrammarV1ResolvedBinder]
  -> Maybe [Located GrammarV1TermParam]
  -> Maybe
      (Either
        GrammarV1SemanticComponentHeaderError
        (Maybe [(GrammarV1ResolvedBinder, Ty)], SurfaceState))
buildSemanticParameters maybeBinders maybeParameters =
  case (maybeBinders, maybeParameters) of
    (Nothing, Nothing) -> Just (Right (Nothing, emptySurfaceState))
    (Just binders, Just parameters) -> do
      built <- buildPresentParameters binders parameters
      pure (fmap (\(checked, state) -> (Just checked, state)) built)
    _ -> Nothing

buildPresentParameters
  :: [GrammarV1ResolvedBinder]
  -> [Located GrammarV1TermParam]
  -> Maybe
      (Either
        GrammarV1SemanticComponentHeaderError
        ([(GrammarV1ResolvedBinder, Ty)], SurfaceState))
buildPresentParameters = go [] emptySurfaceState
  where
    go reversed state [] [] = Just (Right (reverse reversed, state))
    go reversed state (binder : binders) (Located _ parameter : parameters) = do
      ty <- grammarV1PrimitiveType
        (locatedValue (grammarV1TermParamType parameter))
      case grammarV1InsertSemanticBinding
          binder
          (BindingMeta Unrestricted ty PlainShape)
          state of
        Left insertError ->
          Just (Left (GrammarV1SemanticComponentBindingInsertError insertError))
        Right nextState ->
          go ((binder, ty) : reversed) nextState binders parameters
    go _ _ _ _ = Nothing

mapProvidesTypeError
  :: GrammarV1SemanticCheckedTypeError
  -> GrammarV1SemanticComponentHeaderError
mapProvidesTypeError typeError = case typeError of
  GrammarV1SemanticCheckedTypeReferenceError referenceError ->
    GrammarV1SemanticComponentProvidesReferenceError referenceError
  GrammarV1SemanticCheckedTypeRewriteNonCompetent source ->
    GrammarV1SemanticComponentProvidesRewriteNonCompetent source
  GrammarV1SemanticCheckedTypeFocusingError focusingError ->
    GrammarV1SemanticComponentProvidesFocusingError focusingError
  GrammarV1SemanticCheckedTypeRefinementError refinementError ->
    GrammarV1SemanticComponentProvidesRefinementError refinementError
