module Phil.Surface.GrammarV1.SemanticCheckedType
  ( GrammarV1CheckedSemanticType (..)
  , GrammarV1SemanticCheckedTypeError (..)
  , grammarV1CheckedSemanticType
  ) where

import qualified Data.Set as Set
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax (Ty)
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1LexicalScope
  , GrammarV1ResolvedBinder
  )
import Phil.Surface.GrammarV1.CheckedType
  ( grammarV1CheckedType
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference
  , GrammarV1LexicalReferenceError
  , grammarV1CheckedTypeReferences
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Type (..)
  )
import Phil.Surface.GrammarV1.SemanticBindingState
  ( grammarV1RewriteTypeReferences
  )
import Phil.Surface.GrammarV1.SemanticRefinementType
  ( GrammarV1CheckedSemanticRefinementType (..)
  , GrammarV1SemanticRefinementTypeError
  , grammarV1CheckedSemanticRefinementType
  )
import Phil.Surface.Syntax (Located (..))

-- | One checked type on the semantic-binder path. Ordinary types retain exact
-- lexical reference evidence and do not advance binder scope. A top-level
-- primitive-base refinement additionally retains its resolver-issued local binder
-- and returns the declaration-wide scope after that child binder has closed.
data GrammarV1CheckedSemanticType = GrammarV1CheckedSemanticType
  { checkedSemanticTypeValue :: Ty
  , checkedSemanticTypeReferences :: [GrammarV1CheckedLexicalReference]
  , checkedSemanticTypeRefinementBinder :: Maybe GrammarV1ResolvedBinder
  , checkedSemanticTypeFocusSteps :: [FocusStep]
  }
  deriving (Eq, Show)

data GrammarV1SemanticCheckedTypeError
  = GrammarV1SemanticCheckedTypeReferenceError GrammarV1LexicalReferenceError
  | GrammarV1SemanticCheckedTypeRewriteNonCompetent (Located GrammarV1Type)
  | GrammarV1SemanticCheckedTypeFocusingError FocusingError
  | GrammarV1SemanticCheckedTypeRefinementError GrammarV1SemanticRefinementTypeError
  deriving (Eq, Show)

-- | Compose ordinary exact-reference type checking with the semantic refinement
-- binder authority. This is intentionally bounded to a top-level refinement: a
-- refinement nested inside another aggregate type remains outside competence until
-- a recursive semantic type traversal owns its exact source-order binder stream.
grammarV1CheckedSemanticType
  :: StaticContext
  -> GrammarV1LexicalScope
  -> SurfaceState
  -> Located GrammarV1Type
  -> Maybe
      (Either
        GrammarV1SemanticCheckedTypeError
        (GrammarV1CheckedSemanticType, GrammarV1LexicalScope))
grammarV1CheckedSemanticType staticContext lexicalScope state source =
  case locatedValue source of
    GrammarV1RefinementType _ _ _ -> do
      checked <- grammarV1CheckedSemanticRefinementType
        staticContext lexicalScope state (locatedValue source)
      pure $ do
        (refinement, nextScope) <- mapLeft
          GrammarV1SemanticCheckedTypeRefinementError
          checked
        Right
          ( GrammarV1CheckedSemanticType
              { checkedSemanticTypeValue = checkedSemanticRefinementType refinement
              , checkedSemanticTypeReferences = checkedSemanticRefinementReferences refinement
              , checkedSemanticTypeRefinementBinder =
                  Just (checkedSemanticRefinementBinder refinement)
              , checkedSemanticTypeFocusSteps =
                  checkedSemanticRefinementFocusSteps refinement
              }
          , nextScope
          )
    _ -> do
      checkedReferences <- grammarV1CheckedTypeReferences
        Set.empty lexicalScope source
      case checkedReferences of
        Left referenceError ->
          pure (Left (GrammarV1SemanticCheckedTypeReferenceError referenceError))
        Right references ->
          case grammarV1RewriteTypeReferences references source of
            Nothing ->
              pure (Left (GrammarV1SemanticCheckedTypeRewriteNonCompetent source))
            Just rewritten -> do
              checked <- grammarV1CheckedType
                staticContext state (locatedValue rewritten)
              pure $ case checked of
                Left focusingError ->
                  Left (GrammarV1SemanticCheckedTypeFocusingError focusingError)
                Right (ty, steps) ->
                  Right
                    ( GrammarV1CheckedSemanticType
                        { checkedSemanticTypeValue = ty
                        , checkedSemanticTypeReferences = references
                        , checkedSemanticTypeRefinementBinder = Nothing
                        , checkedSemanticTypeFocusSteps = steps
                        }
                    , lexicalScope
                    )

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
