module Phil.Surface.GrammarV1.CaseArmScope
  ( GrammarV1CaseExpressionKind (..)
  , GrammarV1CheckedCaseArm (..)
  , GrammarV1CheckedCaseExpression (..)
  , GrammarV1CaseArmScopeError (..)
  , grammarV1CheckedCaseExpressionInScope
  ) where

import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (GrammarV1MatchArmBinder)
  , GrammarV1BinderScopeError
  , GrammarV1LexicalScope
  , GrammarV1ResolvedBinder
  , grammarV1BindLocal
  , grammarV1EnterLexicalScope
  , grammarV1LeaveLexicalScope
  )
import Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep
  , GrammarV1LetPatternScopeError
  , grammarV1CheckedLetPatternBlockInScope
  )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence
  , grammarV1CheckedLocalValueOccurrenceInScope
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1CaseBinders (..)
  , GrammarV1CasePattern (..)
  , GrammarV1Expression (..)
  , GrammarV1FieldBinder (..)
  , GrammarV1MatchArm (..)
  , GrammarV1MatchArmBody (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | The three Grammar-v1 expressions that share one exact match-arm/case-pattern
-- syntax and therefore one lexical binder rule.
data GrammarV1CaseExpressionKind
  = GrammarV1MatchCaseExpression
  | GrammarV1DecideCaseExpression
  | GrammarV1OfferCaseExpression
  deriving (Eq, Ord, Show)

-- | One checked sibling arm. Its case binders and body-local let trace are kept
-- explicit, while the child lexical frame itself is discarded before the next
-- sibling is checked.
data GrammarV1CheckedCaseArm = GrammarV1CheckedCaseArm
  { grammarV1CheckedCaseArmSource :: Located GrammarV1MatchArm
  , grammarV1CheckedCaseArmBinders :: [GrammarV1ResolvedBinder]
  , grammarV1CheckedCaseArmBodySteps :: [GrammarV1CheckedLetScopeStep]
  }
  deriving (Eq, Show)

-- | Bounded lexical result for match/decide/offer. The scrutinee is resolved in
-- the parent scope before any arm binder exists; each arm then receives a fresh
-- child scope. The declaration-wide ordinal is threaded across sibling exits so
-- equal display spellings in different arms remain distinct semantic occurrences.
data GrammarV1CheckedCaseExpression = GrammarV1CheckedCaseExpression
  { grammarV1CheckedCaseExpressionKind :: GrammarV1CaseExpressionKind
  , grammarV1CheckedCaseScrutinee :: GrammarV1CheckedLocalValueOccurrence
  , grammarV1CheckedCaseArms :: [GrammarV1CheckedCaseArm]
  }
  deriving (Eq, Show)

data GrammarV1CaseArmScopeError
  = GrammarV1CaseArmBinderError GrammarV1BinderScopeError
  | GrammarV1CaseArmBodyError GrammarV1LetPatternScopeError
  deriving (Eq, Show)

-- | Check one bounded match/decide/offer expression from an exact lexical scope.
-- Match expressions with a join clause remain outside this slice because join
-- state introduces its own SURF-009 binder family. The scrutinee and admitted arm
-- bodies use the already-established simple-local/let competence boundary.
grammarV1CheckedCaseExpressionInScope
  :: GrammarV1LexicalScope
  -> Located GrammarV1Expression
  -> Maybe
      (Either
        GrammarV1CaseArmScopeError
        (GrammarV1CheckedCaseExpression, GrammarV1LexicalScope))
grammarV1CheckedCaseExpressionInScope scope (Located _ expression) =
  case expression of
    GrammarV1MatchExpression scrutinee Nothing arms ->
      checkedCaseExpression GrammarV1MatchCaseExpression scope scrutinee arms
    GrammarV1MatchExpression _ (Just _) _ -> Nothing
    GrammarV1DecideExpression scrutinee arms ->
      checkedCaseExpression GrammarV1DecideCaseExpression scope scrutinee arms
    GrammarV1OfferExpression scrutinee arms ->
      checkedCaseExpression GrammarV1OfferCaseExpression scope scrutinee arms
    _ -> Nothing

checkedCaseExpression
  :: GrammarV1CaseExpressionKind
  -> GrammarV1LexicalScope
  -> Located GrammarV1Expression
  -> [Located GrammarV1MatchArm]
  -> Maybe
      (Either
        GrammarV1CaseArmScopeError
        (GrammarV1CheckedCaseExpression, GrammarV1LexicalScope))
checkedCaseExpression kind scope scrutinee arms = do
  checkedScrutinee <- grammarV1CheckedLocalValueOccurrenceInScope scope scrutinee
  checkedArmsResult <- checkedArms scope arms
  Just $ fmap
    (\(checkedArmList, finalScope) ->
      ( GrammarV1CheckedCaseExpression
          { grammarV1CheckedCaseExpressionKind = kind
          , grammarV1CheckedCaseScrutinee = checkedScrutinee
          , grammarV1CheckedCaseArms = checkedArmList
          }
      , finalScope
      ))
    checkedArmsResult

checkedArms
  :: GrammarV1LexicalScope
  -> [Located GrammarV1MatchArm]
  -> Maybe
      (Either
        GrammarV1CaseArmScopeError
        ([GrammarV1CheckedCaseArm], GrammarV1LexicalScope))
checkedArms scope [] = Just (Right ([], scope))
checkedArms scope (arm : rest) = do
  firstResult <- checkedArm scope arm
  case firstResult of
    Left scopeError -> Just (Left scopeError)
    Right (firstArm, afterFirst) -> do
      remainder <- checkedArms afterFirst rest
      Just $ fmap
        (\(restArms, finalScope) -> (firstArm : restArms, finalScope))
        remainder

checkedArm
  :: GrammarV1LexicalScope
  -> Located GrammarV1MatchArm
  -> Maybe
      (Either
        GrammarV1CaseArmScopeError
        (GrammarV1CheckedCaseArm, GrammarV1LexicalScope))
checkedArm parentScope source@(Located _ arm) =
  let childScope = grammarV1EnterLexicalScope parentScope
  in case bindCasePattern (grammarV1MatchArmPattern arm) childScope of
      Left scopeError -> Just (Left (GrammarV1CaseArmBinderError scopeError))
      Right (binders, boundScope) -> do
        bodyResult <- grammarV1CheckedLetPatternBlockInScope
          boundScope
          (armBodyBlock (grammarV1MatchArmBody arm))
        case bodyResult of
          Left bodyError -> Just (Left (GrammarV1CaseArmBodyError bodyError))
          Right (bodySteps, finalChildScope) ->
            case grammarV1LeaveLexicalScope finalChildScope of
              Left scopeError -> Just (Left (GrammarV1CaseArmBinderError scopeError))
              Right nextParentScope -> Just (Right
                ( GrammarV1CheckedCaseArm
                    { grammarV1CheckedCaseArmSource = source
                    , grammarV1CheckedCaseArmBinders = binders
                    , grammarV1CheckedCaseArmBodySteps = bodySteps
                    }
                , nextParentScope
                ))

armBodyBlock :: GrammarV1MatchArmBody -> Located GrammarV1Block
armBodyBlock body = case body of
  GrammarV1MatchArmBlock block -> block
  GrammarV1MatchArmStatement statement ->
    Located (locatedSpan statement) (GrammarV1Block [statement])

bindCasePattern
  :: Located GrammarV1CasePattern
  -> GrammarV1LexicalScope
  -> Either
      GrammarV1BinderScopeError
      ([GrammarV1ResolvedBinder], GrammarV1LexicalScope)
bindCasePattern (Located _ casePattern) scope =
  case grammarV1CasePatternBinders casePattern of
    Nothing -> Right ([], scope)
    Just (GrammarV1TupleCaseBinders names) -> bindNames names scope
    Just (GrammarV1RecordCaseBinders fields) ->
      bindNames (map caseFieldBinderName fields) scope
  where
    bindNames [] currentScope = Right ([], currentScope)
    bindNames (sourceName : rest) currentScope = do
      (firstBinder, afterFirst) <- grammarV1BindLocal
        GrammarV1MatchArmBinder
        sourceName
        currentScope
      (restBinders, afterRest) <- bindNames rest afterFirst
      Right (firstBinder : restBinders, afterRest)

caseFieldBinderName :: Located GrammarV1FieldBinder -> Located Text
caseFieldBinderName (Located _ fieldBinder) =
  fromMaybe
    (grammarV1FieldBinderField fieldBinder)
    (grammarV1FieldBinderAlias fieldBinder)
