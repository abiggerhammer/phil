module Phil.Surface.GrammarV1.SemanticComponentHeader
  ( GrammarV1CheckedSemanticComponentHeader (..)
  , GrammarV1SemanticComponentHeaderError (..)
  , grammarV1CheckedSemanticComponentHeader
  ) where

import qualified Data.Set as Set
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
  , GrammarV1ResolvedBinder
  , grammarV1ComponentParameterScope
  )
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedType)
import Phil.Surface.GrammarV1.Elaborate (grammarV1PrimitiveType)
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference
  , GrammarV1LexicalReferenceError
  , grammarV1CheckedTypeReferences
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ComponentDecl (..)
  , GrammarV1TermParam (..)
  , GrammarV1Type
  )
import Phil.Surface.GrammarV1.SemanticBindingState
  ( grammarV1InsertSemanticBinding
  , grammarV1RewriteTypeReferences
  )
import Phil.Surface.Syntax (Located (..))

-- | A checked component header whose runtime term parameters have exact SURF-009
-- semantic identity. Omitted versus explicitly empty parameter syntax remains
-- visible in the parameter carrier, while every present parameter is retained as
-- its resolved binder plus checked type. The temporary SurfaceState is keyed only
-- by generated Core names and is retained for composition with later body slices.
data GrammarV1CheckedSemanticComponentHeader = GrammarV1CheckedSemanticComponentHeader
  { checkedSemanticComponentDeclarationKey :: DeclarationKey
  , checkedSemanticComponentDefinitionRevision :: DefinitionRevision
  , checkedSemanticComponentDisplayName :: Text
  , checkedSemanticComponentParameters :: Maybe [(GrammarV1ResolvedBinder, Ty)]
  , checkedSemanticComponentProvidesType :: Maybe Ty
  , checkedSemanticComponentProvidesReferences :: Maybe [GrammarV1CheckedLexicalReference]
  , checkedSemanticComponentState :: SurfaceState
  }
  deriving (Eq, Show)

data GrammarV1SemanticComponentHeaderError
  = GrammarV1SemanticComponentBinderScopeError GrammarV1BinderScopeError
  | GrammarV1SemanticComponentBindingInsertError SurfaceCheckError
  | GrammarV1SemanticComponentProvidesReferenceError GrammarV1LexicalReferenceError
  | GrammarV1SemanticComponentProvidesRewriteNonCompetent (Located GrammarV1Type)
  | GrammarV1SemanticComponentProvidesFocusingError FocusingError
  deriving (Eq, Show)

-- | Migrate the bounded closed-component header route onto resolver-issued
-- runtime binder identity without changing the older SURF-008 component API.
-- Generic parameters and generic requirements stay outside this bounded slice.
-- Present term parameters retain the existing primitive unrestricted competence,
-- but are inserted under generated semantic names obtained from BinderScope.
--
-- A present `provides` type is reference-checked in the exact component lexical
-- scope, rewritten only at certified local occurrences, and delegated to the
-- ordinary checked type authority over that semantic state. This permits exact
-- dependent headers such as `component C(n : U8) provides Bytes[toNat(n)]` while
-- preventing display spelling from becoming Core identity. Absence of a provides
-- clause remains distinct from an empty reference set on a present closed type.
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
                    ( buildHeader parameters Nothing Nothing semanticState
                    , []
                    ))
                Just providesSource -> do
                  checkedReferences <- grammarV1CheckedTypeReferences
                    Set.empty
                    lexicalScope
                    providesSource
                  case checkedReferences of
                    Left referenceError ->
                      Just
                        (Left
                          (GrammarV1SemanticComponentProvidesReferenceError
                            referenceError))
                    Right references ->
                      case grammarV1RewriteTypeReferences references providesSource of
                        Nothing ->
                          Just
                            (Left
                              (GrammarV1SemanticComponentProvidesRewriteNonCompetent
                                providesSource))
                        Just rewrittenProvides -> do
                          checkedProvides <- grammarV1CheckedType
                            staticContext
                            semanticState
                            (locatedValue rewrittenProvides)
                          pure $ case checkedProvides of
                            Left focusingError ->
                              Left
                                (GrammarV1SemanticComponentProvidesFocusingError
                                  focusingError)
                            Right (providesType, focusSteps) ->
                              Right
                                ( buildHeader
                                    parameters
                                    (Just providesType)
                                    (Just references)
                                    semanticState
                                , focusSteps
                                )
  where
    buildHeader parameters providesType providesReferences semanticState =
      GrammarV1CheckedSemanticComponentHeader
        { checkedSemanticComponentDeclarationKey = declarationKey
        , checkedSemanticComponentDefinitionRevision = definitionRevision
        , checkedSemanticComponentDisplayName =
            locatedValue (grammarV1ComponentName source)
        , checkedSemanticComponentParameters = parameters
        , checkedSemanticComponentProvidesType = providesType
        , checkedSemanticComponentProvidesReferences = providesReferences
        , checkedSemanticComponentState = semanticState
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
