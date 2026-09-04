module Phil.Surface.GrammarV1.SemanticCallablePropositions
  ( GrammarV1CheckedSemanticCallableProposition (..)
  , GrammarV1SemanticCallablePropositionError (..)
  , grammarV1CheckedSemanticCallableRequires
  , grammarV1CheckedSemanticCallableEnsures
  , grammarV1CheckedSemanticCallableObligations
  , grammarV1CheckedSemanticCallableAssumptions
  ) where

import qualified Data.Set as Set
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static
  ( DeclarationKey
  , StaticContext
  )
import Phil.Core.Syntax (Proposition)
import Phil.Surface.GrammarV1.CheckedProposition
  ( grammarV1CheckedProposition
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference
  , GrammarV1LexicalReferenceError
  , grammarV1CheckedPropositionReferences
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableClause (..)
  , GrammarV1CallableContractDecl (..)
  , GrammarV1Proposition
  )
import Phil.Surface.GrammarV1.SemanticBindingState
  ( grammarV1RewritePropositionReferences
  )
import Phil.Surface.GrammarV1.SemanticCallableSignature
  ( GrammarV1SemanticCallableScope (..)
  , GrammarV1SemanticCallableSignatureError
  , grammarV1SemanticCallableParameterScope
  )
import Phil.Surface.Syntax (Located (..))

-- | One callable clause proposition after exact lexical parameter occurrences
-- have been rewritten to generated Core names and delegated to the ordinary
-- proposition/focusing authority. Category ownership remains with the caller;
-- this record preserves only the exact source, resolver evidence, Core meaning,
-- and focusing trace for one proposition in source order.
data GrammarV1CheckedSemanticCallableProposition =
  GrammarV1CheckedSemanticCallableProposition
    { checkedSemanticCallablePropositionSource :: Located GrammarV1Proposition
    , checkedSemanticCallablePropositionReferences :: [GrammarV1CheckedLexicalReference]
    , checkedSemanticCallablePropositionCore :: Proposition
    , checkedSemanticCallablePropositionFocusSteps :: [FocusStep]
    }
  deriving (Eq, Show)

data GrammarV1SemanticCallablePropositionError
  = GrammarV1SemanticCallablePropositionScopeError
      GrammarV1SemanticCallableSignatureError
  | GrammarV1SemanticCallablePropositionReferenceError
      (Located GrammarV1Proposition)
      GrammarV1LexicalReferenceError
  | GrammarV1SemanticCallablePropositionRewriteNonCompetent
      (Located GrammarV1Proposition)
  | GrammarV1SemanticCallablePropositionCheckNonCompetent
      (Located GrammarV1Proposition)
  | GrammarV1SemanticCallablePropositionFocusingError
      (Located GrammarV1Proposition)
      FocusingError
  deriving (Eq, Show)

-- | Check callable preconditions in source order under the exact semantic
-- parameter environment. Preconditions remain categorically distinct from every
-- other callable proposition family.
grammarV1CheckedSemanticCallableRequires
  :: StaticContext
  -> DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        GrammarV1SemanticCallablePropositionError
        [GrammarV1CheckedSemanticCallableProposition])
grammarV1CheckedSemanticCallableRequires =
  checkedSemanticCategory select
  where
    select clause = case clause of
      GrammarV1CallableRequires proposition -> Just proposition
      _ -> Nothing

-- | Check callable postconditions independently of the callable result-type
-- checker. A bad result type therefore cannot poison a semantically competent
-- ensures category, matching the pre-existing category independence contract.
grammarV1CheckedSemanticCallableEnsures
  :: StaticContext
  -> DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        GrammarV1SemanticCallablePropositionError
        [GrammarV1CheckedSemanticCallableProposition])
grammarV1CheckedSemanticCallableEnsures =
  checkedSemanticCategory select
  where
    select clause = case clause of
      GrammarV1CallableEnsures proposition -> Just proposition
      _ -> Nothing

-- | Check residual obligations without reclassifying or discharging them.
grammarV1CheckedSemanticCallableObligations
  :: StaticContext
  -> DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        GrammarV1SemanticCallablePropositionError
        [GrammarV1CheckedSemanticCallableProposition])
grammarV1CheckedSemanticCallableObligations =
  checkedSemanticCategory select
  where
    select clause = case clause of
      GrammarV1CallableObligation proposition -> Just proposition
      _ -> Nothing

-- | Check assumptions under the identical resolver-issued parameter environment
-- while preserving assumption category and source order.
grammarV1CheckedSemanticCallableAssumptions
  :: StaticContext
  -> DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        GrammarV1SemanticCallablePropositionError
        [GrammarV1CheckedSemanticCallableProposition])
grammarV1CheckedSemanticCallableAssumptions =
  checkedSemanticCategory select
  where
    select clause = case clause of
      GrammarV1CallableAssumes proposition -> Just proposition
      _ -> Nothing

checkedSemanticCategory
  :: (GrammarV1CallableClause -> Maybe (Located GrammarV1Proposition))
  -> StaticContext
  -> DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        GrammarV1SemanticCallablePropositionError
        [GrammarV1CheckedSemanticCallableProposition])
checkedSemanticCategory select staticContext declarationKey source = do
  scoped <- grammarV1SemanticCallableParameterScope declarationKey source
  pure $ do
    semanticScope <- mapLeft
      GrammarV1SemanticCallablePropositionScopeError
      scoped
    mapM
      (checkOne staticContext semanticScope)
      [ proposition
      | Located _ clause <- grammarV1CallableClauses source
      , Just proposition <- [select clause]
      ]

checkOne
  :: StaticContext
  -> GrammarV1SemanticCallableScope
  -> Located GrammarV1Proposition
  -> Either
      GrammarV1SemanticCallablePropositionError
      GrammarV1CheckedSemanticCallableProposition
checkOne staticContext semanticScope source = do
  references <- case grammarV1CheckedPropositionReferences
      Set.empty
      (semanticCallableScopeLexicalScope semanticScope)
      source of
    Nothing ->
      Left (GrammarV1SemanticCallablePropositionCheckNonCompetent source)
    Just checked -> mapLeft
      (GrammarV1SemanticCallablePropositionReferenceError source)
      checked
  rewritten <- maybe
    (Left (GrammarV1SemanticCallablePropositionRewriteNonCompetent source))
    Right
    (grammarV1RewritePropositionReferences references source)
  checked <- maybe
    (Left (GrammarV1SemanticCallablePropositionCheckNonCompetent source))
    Right
    ( grammarV1CheckedProposition
        staticContext
        (semanticCallableScopeState semanticScope)
        (locatedValue rewritten)
    )
  (proposition, focusSteps) <- mapLeft
    (GrammarV1SemanticCallablePropositionFocusingError source)
    checked
  Right GrammarV1CheckedSemanticCallableProposition
    { checkedSemanticCallablePropositionSource = source
    , checkedSemanticCallablePropositionReferences = references
    , checkedSemanticCallablePropositionCore = proposition
    , checkedSemanticCallablePropositionFocusSteps = focusSteps
    }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
