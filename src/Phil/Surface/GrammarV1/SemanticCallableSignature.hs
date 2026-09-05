module Phil.Surface.GrammarV1.SemanticCallableSignature
  ( GrammarV1SemanticCallableScope (..)
  , GrammarV1CheckedSemanticCallableSignature (..)
  , GrammarV1SemanticCallableSignatureError (..)
  , grammarV1SemanticCallableParameterScope
  , grammarV1CheckedSemanticCallableSignature
  ) where

import Data.Text (Text)
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static
  ( DeclarationKey
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
  , grammarV1CallableParameterBinderScope
  )
import Phil.Surface.GrammarV1.Elaborate (grammarV1PrimitiveType)
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference
  , GrammarV1LexicalReferenceError
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableContractDecl (..)
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

-- | Exact semantic parameter environment for one bounded callable contract.
-- This is deliberately independent of result-type success so sibling callable
-- proposition/effect/failure categories can consume the same resolver-issued
-- binder state without an unrelated result-type rejection poisoning them.
data GrammarV1SemanticCallableScope = GrammarV1SemanticCallableScope
  { semanticCallableScopeParameters :: [(GrammarV1ResolvedBinder, Ty)]
  , semanticCallableScopeLexicalScope :: GrammarV1LexicalScope
  , semanticCallableScopeState :: SurfaceState
  }
  deriving (Eq, Show)

-- | A callable contract signature whose runtime term parameters carry exact
-- SURF-009 semantic identity. The source display name remains diagnostic, while
-- the retained parameter state and dependent result type use generated Core names.
-- The retained lexical scope is post-result: a result refinement binder has
-- closed, but its declaration-wide ordinal remains consumed for later outcome or
-- body binders.
data GrammarV1CheckedSemanticCallableSignature = GrammarV1CheckedSemanticCallableSignature
  { checkedSemanticCallableDeclarationKey :: DeclarationKey
  , checkedSemanticCallableDisplayName :: Text
  , checkedSemanticCallableParameters :: [(GrammarV1ResolvedBinder, Ty)]
  , checkedSemanticCallableResultType :: Ty
  , checkedSemanticCallableResultReferences :: [GrammarV1CheckedLexicalReference]
  , checkedSemanticCallableResultRefinementBinder :: Maybe GrammarV1ResolvedBinder
  , checkedSemanticCallableState :: SurfaceState
  , checkedSemanticCallableLexicalScope :: GrammarV1LexicalScope
  }
  deriving (Eq, Show)

data GrammarV1SemanticCallableSignatureError
  = GrammarV1SemanticCallableBinderScopeError GrammarV1BinderScopeError
  | GrammarV1SemanticCallableBindingInsertError SurfaceCheckError
  | GrammarV1SemanticCallableResultReferenceError GrammarV1LexicalReferenceError
  | GrammarV1SemanticCallableResultRewriteNonCompetent (Located GrammarV1Type)
  | GrammarV1SemanticCallableResultFocusingError FocusingError
  | GrammarV1SemanticCallableResultRefinementError
      GrammarV1SemanticRefinementTypeError
  deriving (Eq, Show)

-- | Build only the callable term-parameter semantic environment. Generic
-- parameters and requirements remain outside the bounded route. The returned
-- lexical scope and SurfaceState originate from one exact BinderScope allocation;
-- callers must consume them rather than rebuilding semantic identity from source
-- spelling. Result-type and clause semantics are intentionally not checked here.
grammarV1SemanticCallableParameterScope
  :: DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        GrammarV1SemanticCallableSignatureError
        GrammarV1SemanticCallableScope)
grammarV1SemanticCallableParameterScope declarationKey source
  | not (null (grammarV1CallableGenericParams source)) = Nothing
  | not (null (grammarV1CallableRequirements source)) = Nothing
  | otherwise =
      case grammarV1CallableParameterBinderScope declarationKey source of
        Left scopeError ->
          Just (Left (GrammarV1SemanticCallableBinderScopeError scopeError))
        Right (binders, lexicalScope) -> do
          built <- buildSemanticParameters binders (grammarV1CallableTermParams source)
          pure $ do
            (parameters, semanticState) <- built
            Right GrammarV1SemanticCallableScope
              { semanticCallableScopeParameters = parameters
              , semanticCallableScopeLexicalScope = lexicalScope
              , semanticCallableScopeState = semanticState
              }

-- | Migrate the bounded callable-signature route onto resolver-issued term-binder
-- identity without changing the older SURF-008 callable API. Generic parameters
-- and requirements remain outside this bounded route. Primitive unrestricted term
-- parameters are inserted into a fresh SurfaceState under their generated Core
-- names rather than source spelling.
--
-- Result checking delegates to SemanticCheckedType. Ordinary dependent types keep
-- exact lexical-reference evidence and semantic-name rewriting. A top-level
-- primitive-base refinement additionally consumes one declaration-wide binder
-- ordinal in a child scope, rewrites its predicate to generated names, and returns
-- the enclosing callable scope with that ordinal still consumed. Independent
-- clause-checking APIs may still consume only the parameter scope; whole-callable
-- composition must consume the post-result scope retained here.
grammarV1CheckedSemanticCallableSignature
  :: StaticContext
  -> DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        GrammarV1SemanticCallableSignatureError
        (GrammarV1CheckedSemanticCallableSignature, [FocusStep]))
grammarV1CheckedSemanticCallableSignature staticContext declarationKey source = do
  scoped <- grammarV1SemanticCallableParameterScope declarationKey source
  case scoped of
    Left scopeError -> Just (Left scopeError)
    Right semanticScope -> do
      let resultSource = grammarV1CallableResultType source
          lexicalScope = semanticCallableScopeLexicalScope semanticScope
          semanticState = semanticCallableScopeState semanticScope
      checkedResult <- grammarV1CheckedSemanticType
        staticContext
        lexicalScope
        semanticState
        resultSource
      pure $ case checkedResult of
        Left typeError -> Left (mapResultTypeError typeError)
        Right (semanticResult, nextLexicalScope) ->
          Right
            ( GrammarV1CheckedSemanticCallableSignature
                { checkedSemanticCallableDeclarationKey = declarationKey
                , checkedSemanticCallableDisplayName =
                    locatedValue (grammarV1CallableName source)
                , checkedSemanticCallableParameters =
                    semanticCallableScopeParameters semanticScope
                , checkedSemanticCallableResultType =
                    checkedSemanticTypeValue semanticResult
                , checkedSemanticCallableResultReferences =
                    checkedSemanticTypeReferences semanticResult
                , checkedSemanticCallableResultRefinementBinder =
                    checkedSemanticTypeRefinementBinder semanticResult
                , checkedSemanticCallableState = semanticState
                , checkedSemanticCallableLexicalScope = nextLexicalScope
                }
            , checkedSemanticTypeFocusSteps semanticResult
            )

buildSemanticParameters
  :: [GrammarV1ResolvedBinder]
  -> [Located GrammarV1TermParam]
  -> Maybe
      (Either
        GrammarV1SemanticCallableSignatureError
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
          Just (Left (GrammarV1SemanticCallableBindingInsertError insertError))
        Right nextState ->
          go ((binder, ty) : reversed) nextState binders parameters
    go _ _ _ _ = Nothing

mapResultTypeError
  :: GrammarV1SemanticCheckedTypeError
  -> GrammarV1SemanticCallableSignatureError
mapResultTypeError typeError = case typeError of
  GrammarV1SemanticCheckedTypeReferenceError referenceError ->
    GrammarV1SemanticCallableResultReferenceError referenceError
  GrammarV1SemanticCheckedTypeRewriteNonCompetent source ->
    GrammarV1SemanticCallableResultRewriteNonCompetent source
  GrammarV1SemanticCheckedTypeFocusingError focusingError ->
    GrammarV1SemanticCallableResultFocusingError focusingError
  GrammarV1SemanticCheckedTypeRefinementError refinementError ->
    GrammarV1SemanticCallableResultRefinementError refinementError
