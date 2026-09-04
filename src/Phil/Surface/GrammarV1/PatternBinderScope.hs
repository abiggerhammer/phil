module Phil.Surface.GrammarV1.PatternBinderScope
  ( grammarV1BindPattern
  ) where

import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind
  , GrammarV1BinderScopeError
  , GrammarV1LexicalScope
  , GrammarV1ResolvedBinder
  , grammarV1BindLocal
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1FieldPattern (..)
  , GrammarV1Pattern (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Allocate semantic identities for every binder introduced by one source
-- pattern, in exact source preorder. This operation owns lexical identity only;
-- it does not infer or validate the value/type shape being destructured.
--
-- A bare record field is the shorthand binder for that field name. An explicit
-- `field = pattern` binds only the nested pattern; the field label is structural
-- syntax and does not itself become a local name.
grammarV1BindPattern
  :: GrammarV1BinderKind
  -> Located GrammarV1Pattern
  -> GrammarV1LexicalScope
  -> Either
      GrammarV1BinderScopeError
      ([GrammarV1ResolvedBinder], GrammarV1LexicalScope)
grammarV1BindPattern binderKind (Located _ patternValue) scope =
  case patternValue of
    GrammarV1IdentifierPattern sourceName -> do
      (resolvedBinder, nextScope) <- grammarV1BindLocal binderKind sourceName scope
      Right ([resolvedBinder], nextScope)
    GrammarV1TuplePattern patterns ->
      bindPatterns patterns scope
    GrammarV1RecordPattern _ fields ->
      bindFields fields scope
  where
    bindPatterns [] currentScope = Right ([], currentScope)
    bindPatterns (patternItem : rest) currentScope = do
      (firstBinders, afterFirst) <- grammarV1BindPattern binderKind patternItem currentScope
      (restBinders, afterRest) <- bindPatterns rest afterFirst
      Right (firstBinders <> restBinders, afterRest)

    bindFields [] currentScope = Right ([], currentScope)
    bindFields (Located _ field : rest) currentScope = do
      (firstBinders, afterFirst) <- bindField field currentScope
      (restBinders, afterRest) <- bindFields rest afterFirst
      Right (firstBinders <> restBinders, afterRest)

    bindField field currentScope =
      case grammarV1FieldPatternValue field of
        Nothing -> do
          (resolvedBinder, nextScope) <- grammarV1BindLocal
            binderKind
            (grammarV1FieldPatternName field)
            currentScope
          Right ([resolvedBinder], nextScope)
        Just nestedPattern ->
          grammarV1BindPattern binderKind nestedPattern currentScope
