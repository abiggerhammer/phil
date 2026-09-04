module Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep (..)
  , GrammarV1CheckedLetScopeTrace (..)
  , GrammarV1LetPatternScopeError (..)
  , grammarV1CheckedFunctionLetPatternScope
  , grammarV1CheckedClosureLetPatternScope
  ) where

import Phil.Core.Static (DeclarationKey)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (GrammarV1LetPatternBinder)
  , GrammarV1BinderScopeError
  , GrammarV1LexicalScope
  , GrammarV1ResolvedBinder
  , grammarV1ClosureParameterScope
  , grammarV1FunctionParameterScope
  )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence
  , grammarV1CheckedLocalValueOccurrenceInScope
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1Closure (..)
  , GrammarV1Expression
  , GrammarV1FunctionDecl (..)
  , GrammarV1Statement (..)
  )
import Phil.Surface.GrammarV1.PatternBinderScope (grammarV1BindPattern)
import Phil.Surface.Syntax (Located (..))

-- | Exact lexical-scope trace for the bounded sequential-let fragment. A let
-- step records the initializer occurrence resolved in the pre-binding scope and
-- the exact semantic binders allocated afterward. Ordinary value statements
-- record the local occurrence visible at that source point.
data GrammarV1CheckedLetScopeStep
  = GrammarV1CheckedLetBindingStep
      (Located GrammarV1Statement)
      GrammarV1CheckedLocalValueOccurrence
      [GrammarV1ResolvedBinder]
  | GrammarV1CheckedLetOccurrenceStep
      (Located GrammarV1Statement)
      GrammarV1CheckedLocalValueOccurrence
  deriving (Eq, Show)

data GrammarV1CheckedLetScopeTrace = GrammarV1CheckedLetScopeTrace
  { grammarV1CheckedLetParameterBinders :: [GrammarV1ResolvedBinder]
  , grammarV1CheckedLetScopeSteps :: [GrammarV1CheckedLetScopeStep]
  }
  deriving (Eq, Show)

newtype GrammarV1LetPatternScopeError = GrammarV1LetPatternBinderError
  { grammarV1LetPatternBinderError :: GrammarV1BinderScopeError
  }
  deriving (Eq, Show)

-- | Check lexical availability for the bounded function-body fragment containing
-- sequential lets whose initializers are already-available simple local values.
-- The initializer is resolved before the pattern is bound, so a let cannot make
-- its own binders visible to its initializer. Pattern/value shape compatibility is
-- deliberately not established here; this slice owns lexical identity/scope only.
grammarV1CheckedFunctionLetPatternScope
  :: DeclarationKey
  -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1LetPatternScopeError GrammarV1CheckedLetScopeTrace)
grammarV1CheckedFunctionLetPatternScope declarationKey functionDecl =
  case grammarV1FunctionParameterScope declarationKey functionDecl of
    Left scopeError -> Just (Left (GrammarV1LetPatternBinderError scopeError))
    Right (parameterBinders, scope) ->
      fmap
        (fmap (GrammarV1CheckedLetScopeTrace parameterBinders))
        (checkedBlock scope (grammarV1FunctionBody functionDecl))

-- | The same bounded sequential-let scope trace for a closure. The caller's exact
-- outer scope remains active; closure parameters are allocated in the child frame
-- before the body is traversed. Capture admissibility remains separately owned.
grammarV1CheckedClosureLetPatternScope
  :: GrammarV1LexicalScope
  -> GrammarV1Closure
  -> Maybe (Either GrammarV1LetPatternScopeError GrammarV1CheckedLetScopeTrace)
grammarV1CheckedClosureLetPatternScope outerScope closure =
  case grammarV1ClosureParameterScope outerScope closure of
    Left scopeError -> Just (Left (GrammarV1LetPatternBinderError scopeError))
    Right (parameterBinders, scope) ->
      fmap
        (fmap (GrammarV1CheckedLetScopeTrace parameterBinders))
        (checkedBlock scope (grammarV1ClosureBody closure))

checkedBlock
  :: GrammarV1LexicalScope
  -> Located GrammarV1Block
  -> Maybe (Either GrammarV1LetPatternScopeError [GrammarV1CheckedLetScopeStep])
checkedBlock scope (Located _ (GrammarV1Block statements)) =
  checkedStatements scope statements

checkedStatements
  :: GrammarV1LexicalScope
  -> [Located GrammarV1Statement]
  -> Maybe (Either GrammarV1LetPatternScopeError [GrammarV1CheckedLetScopeStep])
checkedStatements _ [] = Just (Right [])
checkedStatements scope (source@(Located _ statement) : rest) =
  case statement of
    GrammarV1LetStatement patternValue initializer -> do
      initializerOccurrence <- grammarV1CheckedLocalValueOccurrenceInScope scope initializer
      case grammarV1BindPattern GrammarV1LetPatternBinder patternValue scope of
        Left scopeError -> Just (Left (GrammarV1LetPatternBinderError scopeError))
        Right (binders, nextScope) -> do
          remainder <- checkedStatements nextScope rest
          Just $ fmap
            (GrammarV1CheckedLetBindingStep source initializerOccurrence binders :)
            remainder
    GrammarV1ReturnStatement expression ->
      checkedOccurrenceStatement scope source expression rest
    GrammarV1ExpressionStatement expression ->
      checkedOccurrenceStatement scope source expression rest

checkedOccurrenceStatement
  :: GrammarV1LexicalScope
  -> Located GrammarV1Statement
  -> Located GrammarV1Expression
  -> [Located GrammarV1Statement]
  -> Maybe (Either GrammarV1LetPatternScopeError [GrammarV1CheckedLetScopeStep])
checkedOccurrenceStatement scope source expression rest = do
  occurrence <- grammarV1CheckedLocalValueOccurrenceInScope scope expression
  remainder <- checkedStatements scope rest
  Just $ fmap (GrammarV1CheckedLetOccurrenceStep source occurrence :) remainder
