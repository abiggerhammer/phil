module Phil.Surface.GrammarV1.SemanticCallableOutcomePropositions
  ( GrammarV1SemanticCallableOutcomePropositionError (..)
  , grammarV1CheckedSemanticCallableOutcomeEnsures
  , grammarV1CheckedSemanticCallableOutcomeObligations
  ) where

import qualified Data.Set as Set
import Phil.Core.Focusing (FocusingError)
import Phil.Core.Static
  ( DeclarationKey
  , StaticContext
  )
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.BinderScope (GrammarV1LexicalScope)
import Phil.Surface.GrammarV1.CheckedProposition
  ( grammarV1CheckedProposition
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1LexicalReferenceError
  , grammarV1CheckedPropositionReferences
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableContractDecl
  , GrammarV1OutcomeKind
  , GrammarV1OutcomeResidue (..)
  , GrammarV1OutcomeResidueClause (..)
  , GrammarV1Proposition
  )
import Phil.Surface.GrammarV1.SemanticBindingState
  ( grammarV1RewritePropositionReferences
  )
import Phil.Surface.GrammarV1.SemanticCallableOutcomeState
  ( GrammarV1SemanticCallableOutcomeResidueScope (..)
  , GrammarV1SemanticCallableOutcomeStateError
  , GrammarV1SemanticCallableOutcomeStateScope (..)
  , grammarV1SemanticCallableOutcomeScopes
  )
import Phil.Surface.GrammarV1.SemanticCallablePropositions
  ( GrammarV1CheckedSemanticCallableProposition (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Explicit semantic failures for outcome-local proposition checking. Repeated
-- state clauses remain an ambiguity rather than one branch being selected
-- arbitrarily; lexical evidence, rewrite competence, and Core focusing failures
-- remain distinct after that scope decision.
data GrammarV1SemanticCallableOutcomePropositionError
  = GrammarV1SemanticCallableOutcomePropositionScopeError
      GrammarV1SemanticCallableOutcomeStateError
  | GrammarV1SemanticCallableOutcomeAmbiguousStateScope
      (Located GrammarV1OutcomeResidue)
  | GrammarV1SemanticCallableOutcomePropositionReferenceError
      (Located GrammarV1Proposition)
      GrammarV1LexicalReferenceError
  | GrammarV1SemanticCallableOutcomePropositionRewriteNonCompetent
      (Located GrammarV1Proposition)
  | GrammarV1SemanticCallableOutcomePropositionCheckNonCompetent
      (Located GrammarV1Proposition)
  | GrammarV1SemanticCallableOutcomePropositionFocusingError
      (Located GrammarV1Proposition)
      FocusingError
  deriving (Eq, Show)

-- | Check outcome-local postconditions under the exact callable parameter scope
-- plus the one explicit semantic state telescope for that residue, when present.
-- Source order and outcome category are preserved exactly.
grammarV1CheckedSemanticCallableOutcomeEnsures
  :: StaticContext
  -> DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        GrammarV1SemanticCallableOutcomePropositionError
        [(GrammarV1OutcomeKind, [GrammarV1CheckedSemanticCallableProposition])])
grammarV1CheckedSemanticCallableOutcomeEnsures =
  checkedCategory select
  where
    select clause = case clause of
      GrammarV1OutcomeEnsures proposition -> Just proposition
      _ -> Nothing

-- | Check outcome-local residual obligations through the same exact branch scope
-- without reclassifying them as postconditions or discharged facts.
grammarV1CheckedSemanticCallableOutcomeObligations
  :: StaticContext
  -> DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        GrammarV1SemanticCallableOutcomePropositionError
        [(GrammarV1OutcomeKind, [GrammarV1CheckedSemanticCallableProposition])])
grammarV1CheckedSemanticCallableOutcomeObligations =
  checkedCategory select
  where
    select clause = case clause of
      GrammarV1OutcomeObligation proposition -> Just proposition
      _ -> Nothing

checkedCategory
  :: (GrammarV1OutcomeResidueClause -> Maybe (Located GrammarV1Proposition))
  -> StaticContext
  -> DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        GrammarV1SemanticCallableOutcomePropositionError
        [(GrammarV1OutcomeKind, [GrammarV1CheckedSemanticCallableProposition])])
checkedCategory select staticContext declarationKey source = do
  scoped <- grammarV1SemanticCallableOutcomeScopes declarationKey source
  pure $ do
    residueScopes <- mapLeft
      GrammarV1SemanticCallableOutcomePropositionScopeError
      scoped
    mapM (checkResidue staticContext select) residueScopes

checkResidue
  :: StaticContext
  -> (GrammarV1OutcomeResidueClause -> Maybe (Located GrammarV1Proposition))
  -> GrammarV1SemanticCallableOutcomeResidueScope
  -> Either
      GrammarV1SemanticCallableOutcomePropositionError
      (GrammarV1OutcomeKind, [GrammarV1CheckedSemanticCallableProposition])
checkResidue staticContext select residueScope = do
  (lexicalScope, state) <- case semanticCallableOutcomeResidueStateScopes residueScope of
    [] -> Right
      ( semanticCallableOutcomeResidueBaseLexicalScope residueScope
      , semanticCallableOutcomeResidueBaseState residueScope
      )
    [stateScope] -> Right
      ( semanticCallableOutcomeStateLexicalScope stateScope
      , semanticCallableOutcomeStateSurfaceState stateScope
      )
    _ -> Left
      (GrammarV1SemanticCallableOutcomeAmbiguousStateScope
        (semanticCallableOutcomeResidueSource residueScope))
  checked <- mapM
    (checkOne staticContext lexicalScope state)
    [ proposition
    | Located _ clause <- grammarV1OutcomeResidueClauses residue
    , Just proposition <- [select clause]
    ]
  Right
    ( semanticCallableOutcomeResidueKind residueScope
    , checked
    )
  where
    Located _ residue = semanticCallableOutcomeResidueSource residueScope

checkOne
  :: StaticContext
  -> GrammarV1LexicalScope
  -> SurfaceState
  -> Located GrammarV1Proposition
  -> Either
      GrammarV1SemanticCallableOutcomePropositionError
      GrammarV1CheckedSemanticCallableProposition
checkOne staticContext lexicalScope state source = do
  references <- case grammarV1CheckedPropositionReferences
      Set.empty
      lexicalScope
      source of
    Nothing ->
      Left
        (GrammarV1SemanticCallableOutcomePropositionCheckNonCompetent source)
    Just checked -> mapLeft
      (GrammarV1SemanticCallableOutcomePropositionReferenceError source)
      checked
  rewritten <- maybe
    (Left
      (GrammarV1SemanticCallableOutcomePropositionRewriteNonCompetent source))
    Right
    (grammarV1RewritePropositionReferences references source)
  checked <- maybe
    (Left
      (GrammarV1SemanticCallableOutcomePropositionCheckNonCompetent source))
    Right
    (grammarV1CheckedProposition staticContext state (locatedValue rewritten))
  (proposition, focusSteps) <- mapLeft
    (GrammarV1SemanticCallableOutcomePropositionFocusingError source)
    checked
  Right GrammarV1CheckedSemanticCallableProposition
    { checkedSemanticCallablePropositionSource = source
    , checkedSemanticCallablePropositionReferences = references
    , checkedSemanticCallablePropositionCore = proposition
    , checkedSemanticCallablePropositionFocusSteps = focusSteps
    }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
