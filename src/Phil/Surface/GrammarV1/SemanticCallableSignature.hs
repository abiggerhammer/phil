module Phil.Surface.GrammarV1.SemanticCallableSignature
  ( GrammarV1CheckedSemanticCallableSignature (..)
  , GrammarV1SemanticCallableSignatureError (..)
  , grammarV1CheckedSemanticCallableSignature
  ) where

import qualified Data.Set as Set
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
  , GrammarV1ResolvedBinder
  , grammarV1CallableParameterBinderScope
  )
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedType)
import Phil.Surface.GrammarV1.Elaborate (grammarV1PrimitiveType)
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference
  , GrammarV1LexicalReferenceError
  , grammarV1CheckedTypeReferences
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableContractDecl (..)
  , GrammarV1TermParam (..)
  , GrammarV1Type
  )
import Phil.Surface.GrammarV1.SemanticBindingState
  ( grammarV1InsertSemanticBinding
  , grammarV1RewriteTypeReferences
  )
import Phil.Surface.Syntax (Located (..))

-- | A callable contract signature whose runtime term parameters carry exact
-- SURF-009 semantic identity. The source display name remains diagnostic, while
-- the retained parameter state and dependent result type use generated Core names.
data GrammarV1CheckedSemanticCallableSignature = GrammarV1CheckedSemanticCallableSignature
  { checkedSemanticCallableDeclarationKey :: DeclarationKey
  , checkedSemanticCallableDisplayName :: Text
  , checkedSemanticCallableParameters :: [(GrammarV1ResolvedBinder, Ty)]
  , checkedSemanticCallableResultType :: Ty
  , checkedSemanticCallableResultReferences :: [GrammarV1CheckedLexicalReference]
  , checkedSemanticCallableState :: SurfaceState
  }
  deriving (Eq, Show)

data GrammarV1SemanticCallableSignatureError
  = GrammarV1SemanticCallableBinderScopeError GrammarV1BinderScopeError
  | GrammarV1SemanticCallableBindingInsertError SurfaceCheckError
  | GrammarV1SemanticCallableResultReferenceError GrammarV1LexicalReferenceError
  | GrammarV1SemanticCallableResultRewriteNonCompetent (Located GrammarV1Type)
  | GrammarV1SemanticCallableResultFocusingError FocusingError
  deriving (Eq, Show)

-- | Migrate the bounded callable-signature route onto resolver-issued term-binder
-- identity without changing the older SURF-008 callable API. Generic parameters
-- and requirements remain outside this bounded route. Primitive unrestricted term
-- parameters are inserted into a fresh SurfaceState under their generated Core
-- names rather than source spelling.
--
-- The result type is reference-checked against the exact callable lexical scope,
-- rewritten only at certified local occurrences, and delegated to the ordinary
-- checked type authority. Callable proposition/effect/failure clauses remain owned
-- by their existing projections; this slice establishes the semantic parameter
-- state that those later composition paths can consume.
grammarV1CheckedSemanticCallableSignature
  :: StaticContext
  -> DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        GrammarV1SemanticCallableSignatureError
        (GrammarV1CheckedSemanticCallableSignature, [FocusStep]))
grammarV1CheckedSemanticCallableSignature staticContext declarationKey source
  | not (null (grammarV1CallableGenericParams source)) = Nothing
  | not (null (grammarV1CallableRequirements source)) = Nothing
  | otherwise =
      case grammarV1CallableParameterBinderScope declarationKey source of
        Left scopeError ->
          Just (Left (GrammarV1SemanticCallableBinderScopeError scopeError))
        Right (binders, lexicalScope) -> do
          built <- buildSemanticParameters binders (grammarV1CallableTermParams source)
          case built of
            Left buildError -> Just (Left buildError)
            Right (parameters, semanticState) -> do
              let resultSource = grammarV1CallableResultType source
              checkedReferences <- grammarV1CheckedTypeReferences
                Set.empty
                lexicalScope
                resultSource
              case checkedReferences of
                Left referenceError ->
                  Just
                    (Left
                      (GrammarV1SemanticCallableResultReferenceError
                        referenceError))
                Right references ->
                  case grammarV1RewriteTypeReferences references resultSource of
                    Nothing ->
                      Just
                        (Left
                          (GrammarV1SemanticCallableResultRewriteNonCompetent
                            resultSource))
                    Just rewrittenResult -> do
                      checkedResult <- grammarV1CheckedType
                        staticContext
                        semanticState
                        (locatedValue rewrittenResult)
                      pure $ case checkedResult of
                        Left focusingError ->
                          Left
                            (GrammarV1SemanticCallableResultFocusingError
                              focusingError)
                        Right (resultType, focusSteps) ->
                          Right
                            ( GrammarV1CheckedSemanticCallableSignature
                                { checkedSemanticCallableDeclarationKey = declarationKey
                                , checkedSemanticCallableDisplayName =
                                    locatedValue (grammarV1CallableName source)
                                , checkedSemanticCallableParameters = parameters
                                , checkedSemanticCallableResultType = resultType
                                , checkedSemanticCallableResultReferences = references
                                , checkedSemanticCallableState = semanticState
                                }
                            , focusSteps
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
