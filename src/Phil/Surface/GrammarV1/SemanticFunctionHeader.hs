module Phil.Surface.GrammarV1.SemanticFunctionHeader
  ( GrammarV1CheckedSemanticFunctionHeader (..)
  , GrammarV1SemanticFunctionHeaderError (..)
  , grammarV1CheckedSemanticFunctionHeader
  ) where

import Data.Text (Text)
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
  , GrammarV1LexicalScope
  , GrammarV1ResolvedBinder (..)
  , grammarV1FunctionParameterScope
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1BareStaticReferenceActual
  , grammarV1PrimitiveType
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference
  , GrammarV1LexicalReferenceError
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1FunctionDecl (..)
  , GrammarV1StaticArgument (..)
  , GrammarV1TermParam (..)
  , GrammarV1Type (..)
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

-- | A checked closed function header whose runtime term parameters have exact
-- SURF-009 binder identity. Display spelling remains attached to each resolved
-- binder for diagnostics, while the retained SurfaceState and checked dependent
-- result type use only generated semantic Core names. The lexical scope retained
-- here is the post-result scope: a result refinement binder has already closed,
-- but its declaration-wide ordinal remains consumed for later body binders.
data GrammarV1CheckedSemanticFunctionHeader = GrammarV1CheckedSemanticFunctionHeader
  { checkedSemanticFunctionDeclarationKey :: DeclarationKey
  , checkedSemanticFunctionDefinitionRevision :: DefinitionRevision
  , checkedSemanticFunctionRecursive :: Bool
  , checkedSemanticFunctionDisplayName :: Text
  , checkedSemanticFunctionParameters :: [(GrammarV1ResolvedBinder, Ty)]
  , checkedSemanticFunctionResultType :: Ty
  , checkedSemanticFunctionResultReferences :: [GrammarV1CheckedLexicalReference]
  , checkedSemanticFunctionSatisfiesReference :: GenericStaticActual
  , checkedSemanticFunctionState :: SurfaceState
  , checkedSemanticFunctionLexicalScope :: GrammarV1LexicalScope
  }
  deriving (Eq, Show)

data GrammarV1SemanticFunctionHeaderError
  = GrammarV1SemanticFunctionBinderScopeError GrammarV1BinderScopeError
  | GrammarV1SemanticFunctionBindingInsertError SurfaceCheckError
  | GrammarV1SemanticFunctionResultReferenceError GrammarV1LexicalReferenceError
  | GrammarV1SemanticFunctionResultRewriteNonCompetent (Located GrammarV1Type)
  | GrammarV1SemanticFunctionResultFocusingError FocusingError
  | GrammarV1SemanticFunctionResultRefinementError
      GrammarV1SemanticRefinementTypeError
  deriving (Eq, Show)

-- | Migrate the bounded closed-function header path onto resolver-issued runtime
-- binder identity without changing the older SURF-008 header API yet. Generic
-- parameters and generic requirements remain outside this bounded route. Runtime
-- parameters retain the same primitive unrestricted competence as the existing
-- closed-header bridge, but their SurfaceState entries are inserted under the
-- generated Core names from BinderScope rather than source spelling.
--
-- Result checking now delegates to SemanticCheckedType. Ordinary dependent types
-- still use exact reference evidence and semantic-name rewriting; a top-level
-- primitive-base refinement additionally allocates its local binder in a child
-- lexical scope, rewrites its predicate to generated names, and returns the outer
-- scope with the declaration-wide ordinal advanced. Static/global names remain
-- untouched. Specialized satisfies references and structurally unsupported
-- parameter/result forms remain source non-competence.
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
              checkedResult <- grammarV1CheckedSemanticType
                staticContext
                lexicalScope
                semanticState
                resultSource
              pure $ case checkedResult of
                Left typeError -> Left (mapResultTypeError typeError)
                Right (semanticResult, nextLexicalScope) ->
                  Right
                    ( GrammarV1CheckedSemanticFunctionHeader
                        { checkedSemanticFunctionDeclarationKey = declarationKey
                        , checkedSemanticFunctionDefinitionRevision = definitionRevision
                        , checkedSemanticFunctionRecursive = grammarV1FunctionRecursive source
                        , checkedSemanticFunctionDisplayName =
                            locatedValue (grammarV1FunctionName source)
                        , checkedSemanticFunctionParameters = parameters
                        , checkedSemanticFunctionResultType =
                            checkedSemanticTypeValue semanticResult
                        , checkedSemanticFunctionResultReferences =
                            checkedSemanticTypeReferences semanticResult
                        , checkedSemanticFunctionSatisfiesReference = satisfiesReference
                        , checkedSemanticFunctionState = semanticState
                        , checkedSemanticFunctionLexicalScope = nextLexicalScope
                        }
                    , checkedSemanticTypeFocusSteps semanticResult
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

mapResultTypeError
  :: GrammarV1SemanticCheckedTypeError
  -> GrammarV1SemanticFunctionHeaderError
mapResultTypeError typeError = case typeError of
  GrammarV1SemanticCheckedTypeReferenceError referenceError ->
    GrammarV1SemanticFunctionResultReferenceError referenceError
  GrammarV1SemanticCheckedTypeRewriteNonCompetent source ->
    GrammarV1SemanticFunctionResultRewriteNonCompetent source
  GrammarV1SemanticCheckedTypeFocusingError focusingError ->
    GrammarV1SemanticFunctionResultFocusingError focusingError
  GrammarV1SemanticCheckedTypeRefinementError refinementError ->
    GrammarV1SemanticFunctionResultRefinementError refinementError

unresolvedCallableReference :: GrammarV1Type -> Maybe GenericStaticActual
unresolvedCallableReference sourceType = case sourceType of
  GrammarV1NamedType reference ->
    grammarV1BareStaticReferenceActual
      (GrammarV1StaticReferenceArgument reference)
  _ -> Nothing
