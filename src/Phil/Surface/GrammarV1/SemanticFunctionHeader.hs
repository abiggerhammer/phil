module Phil.Surface.GrammarV1.SemanticFunctionHeader
  ( GrammarV1CheckedSemanticFunctionHeader (..)
  , GrammarV1SemanticFunctionHeaderError (..)
  , grammarV1CheckedSemanticFunctionHeader
  ) where

import qualified Data.Set as Set
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Generic.StaticActual (GenericStaticActual)
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
  , GrammarV1ResolvedBinder (..)
  , grammarV1FunctionParameterScope
  )
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedType)
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1BareStaticReferenceActual
  , grammarV1PrimitiveType
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference
  , GrammarV1LexicalReferenceError
  , grammarV1CheckedTypeReferences
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1FunctionDecl (..)
  , GrammarV1StaticArgument (..)
  , GrammarV1TermParam (..)
  , GrammarV1Type (..)
  )
import Phil.Surface.GrammarV1.SemanticBindingState
  ( grammarV1InsertSemanticBinding
  , grammarV1RewriteTypeReferences
  )
import Phil.Surface.Syntax (Located (..))

-- | A checked closed function header whose runtime term parameters have exact
-- SURF-009 binder identity. Display spelling remains attached to each resolved
-- binder for diagnostics, while the retained SurfaceState and checked dependent
-- result type use only generated semantic Core names.
data GrammarV1CheckedSemanticFunctionHeader = GrammarV1CheckedSemanticFunctionHeader
  { checkedSemanticFunctionDeclarationKey :: DeclarationKey
  , checkedSemanticFunctionDefinitionRevision :: DefinitionRevision
  , checkedSemanticFunctionRecursive :: Bool
  , checkedSemanticFunctionDisplayName :: String
  , checkedSemanticFunctionParameters :: [(GrammarV1ResolvedBinder, Ty)]
  , checkedSemanticFunctionResultType :: Ty
  , checkedSemanticFunctionResultReferences :: [GrammarV1CheckedLexicalReference]
  , checkedSemanticFunctionSatisfiesReference :: GenericStaticActual
  , checkedSemanticFunctionState :: SurfaceState
  }
  deriving (Eq, Show)

data GrammarV1SemanticFunctionHeaderError
  = GrammarV1SemanticFunctionBinderScopeError GrammarV1BinderScopeError
  | GrammarV1SemanticFunctionBindingInsertError SurfaceCheckError
  | GrammarV1SemanticFunctionResultReferenceError GrammarV1LexicalReferenceError
  | GrammarV1SemanticFunctionResultRewriteNonCompetent (Located GrammarV1Type)
  | GrammarV1SemanticFunctionResultFocusingError FocusingError
  deriving (Eq, Show)

-- | Migrate the bounded closed-function header path onto resolver-issued runtime
-- binder identity without changing the older SURF-008 header API yet. Generic
-- parameters and generic requirements remain outside this bounded route. Runtime
-- parameters retain the same primitive unrestricted competence as the existing
-- closed-header bridge, but their SurfaceState entries are inserted under the
-- generated Core names from BinderScope rather than source spelling.
--
-- The explicit result type is reference-checked against that exact lexical scope,
-- rewritten only at certified local occurrences, and then delegated to the
-- ordinary checked type bridge over the semantic-name state. This admits dependent
-- results such as Bytes[toNat(x)] without making x's display spelling semantic.
-- Static/global names remain untouched. Specialized satisfies references and
-- structurally unsupported parameter/result forms remain source non-competence.
grammarV1CheckedSemanticFunctionHeader
  :: StaticContext
  -> DeclarationKey
  -> DefinitionRevision
  -> GrammarV1FunctionDecl
  -> Maybe
      (Either
        GrammarV1SemanticFunctionHeaderError
        (GrammarV1CheckedSemanticFunctionHeader, [FocusStep]))
grammarV1CheckedSemanticFunctionHeader
    staticContext declarationKey definitionRevision source
  | not (null (grammarV1FunctionGenericParams source)) = Nothing
  | not (null (grammarV1FunctionRequirements source)) = Nothing
  | otherwise = do
      resultSource <- grammarV1FunctionResultType source
      satisfiesReference <- unresolvedCallableReference
        (locatedValue (grammarV1FunctionSatisfies source))
      case grammarV1FunctionParameterScope declarationKey source of
        Left scopeError ->
          pure (Left (GrammarV1SemanticFunctionBinderScopeError scopeError))
        Right (binders, lexicalScope) -> do
          built <- buildSemanticParameters
            binders
            (grammarV1FunctionTermParams source)
          case built of
            Left buildError -> pure (Left buildError)
            Right (parameters, semanticState) -> do
              checkedReferences <- grammarV1CheckedTypeReferences
                Set.empty
                lexicalScope
                resultSource
              case checkedReferences of
                Left referenceError ->
                  pure
                    (Left
                      (GrammarV1SemanticFunctionResultReferenceError
                        referenceError))
                Right references ->
                  case grammarV1RewriteTypeReferences references resultSource of
                    Nothing ->
                      pure
                        (Left
                          (GrammarV1SemanticFunctionResultRewriteNonCompetent
                            resultSource))
                    Just rewrittenResult -> do
                      checkedResult <- grammarV1CheckedType
                        staticContext
                        semanticState
                        (locatedValue rewrittenResult)
                      pure $ case checkedResult of
                        Left focusingError ->
                          Left
                            (GrammarV1SemanticFunctionResultFocusingError
                              focusingError)
                        Right (resultType, focusSteps) ->
                          Right
                            ( GrammarV1CheckedSemanticFunctionHeader
                                { checkedSemanticFunctionDeclarationKey = declarationKey
                                , checkedSemanticFunctionDefinitionRevision = definitionRevision
                                , checkedSemanticFunctionRecursive = grammarV1FunctionRecursive source
                                , checkedSemanticFunctionDisplayName =
                                    show (locatedValue (grammarV1FunctionName source))
                                , checkedSemanticFunctionParameters = parameters
                                , checkedSemanticFunctionResultType = resultType
                                , checkedSemanticFunctionResultReferences = references
                                , checkedSemanticFunctionSatisfiesReference = satisfiesReference
                                , checkedSemanticFunctionState = semanticState
                                }
                            , focusSteps
                            )

buildSemanticParameters
  :: [GrammarV1ResolvedBinder]
  -> [Located GrammarV1TermParam]
  -> Maybe
      (Either
        GrammarV1SemanticFunctionHeaderError
        ([(GrammarV1ResolvedBinder, Ty)], SurfaceState))
buildSemanticParameters = go [] emptySurfaceState
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
          Just (Left (GrammarV1SemanticFunctionBindingInsertError insertError))
        Right nextState ->
          go ((binder, ty) : reversed) nextState binders parameters
    go _ _ _ _ = Nothing

unresolvedCallableReference :: GrammarV1Type -> Maybe GenericStaticActual
unresolvedCallableReference sourceType = case sourceType of
  GrammarV1NamedType reference ->
    grammarV1BareStaticReferenceActual
      (GrammarV1StaticReferenceArgument reference)
  _ -> Nothing
