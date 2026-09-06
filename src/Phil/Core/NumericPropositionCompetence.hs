module Phil.Core.NumericPropositionCompetence
  ( NumericPropositionCompetence (..)
  , NumericPropositionCompetenceError (..)
  , classifyNumericPropositionCompetence
  , proposeNumericDecisionCertificate
  ) where

import qualified Data.Set as Set
import Phil.Core.Checker (CheckState)
import Phil.Core.Decision
  ( DecisionCertificate
  , SolverAssumption
  , proposeDecisionCertificate
  )
import Phil.Core.SortCheck
  ( SortError
  , checkPropositionSorts
  , sortOfRefTerm
  )
import Phil.Core.Syntax
  ( Proposition (..)
  , RefSort (..)
  , RefTerm
  )

-- | The built-in numeric decision competence is intentionally smaller than the
-- runtime scalar surface. Nat and UInt have an exact linear decision procedure;
-- opaque numeric domains (including EXEC-018 F32/F64 semantic sorts) require an
-- explicitly declared evidence/checker path instead of inheriting runtime
-- arithmetic support as theorem-proving authority.
data NumericPropositionCompetence
  = NumericPropositionCompetent [RefSort]
  | NumericPropositionRequiresExplicitEvidence [RefSort]
  | NumericPropositionNotNumeric
  deriving (Eq, Show)

data NumericPropositionCompetenceError
  = NumericPropositionSortError SortError
  deriving (Eq, Show)

classifyNumericPropositionCompetence
  :: CheckState
  -> Proposition
  -> Either NumericPropositionCompetenceError NumericPropositionCompetence
classifyNumericPropositionCompetence state proposition = do
  mapLeft NumericPropositionSortError (checkPropositionSorts state proposition)
  sorts <- numericSorts state proposition
  let distinct = Set.toAscList (Set.fromList sorts)
  pure $ case distinct of
    [] -> NumericPropositionNotNumeric
    values
      | all builtInNumericSort values -> NumericPropositionCompetent values
      | otherwise -> NumericPropositionRequiresExplicitEvidence values

-- | Invoke the built-in producer only when the proposition lies wholly inside
-- its declared Nat/UInt competence. Unsupported numeric propositions remain
-- unresolved; callers may later provide exact evidence to the ordinary checked
-- certificate/evidence boundary, but this function never invents an assumption,
-- runtime guard, or truth value for them.
proposeNumericDecisionCertificate
  :: CheckState
  -> [SolverAssumption]
  -> Proposition
  -> Either
      NumericPropositionCompetenceError
      (NumericPropositionCompetence, Maybe DecisionCertificate)
proposeNumericDecisionCertificate state assumptions proposition = do
  competence <- classifyNumericPropositionCompetence state proposition
  let certificate = case competence of
        NumericPropositionCompetent _ ->
          proposeDecisionCertificate state assumptions proposition
        NumericPropositionRequiresExplicitEvidence _ -> Nothing
        NumericPropositionNotNumeric -> Nothing
  pure (competence, certificate)

numericSorts
  :: CheckState
  -> Proposition
  -> Either NumericPropositionCompetenceError [RefSort]
numericSorts state = go
  where
    go proposition = case proposition of
      Equal left right -> relation left right
      NotEqual left right -> relation left right
      LessThan left right -> relation left right
      LessEqual left right -> relation left right
      Conjunction left right -> (<>) <$> go left <*> go right
      Disjunction left right -> (<>) <$> go left <*> go right
      Negation inner -> go inner
      Truth -> pure []
      Falsehood -> pure []
      Member _ _ -> pure []
      Disjoint _ _ -> pure []
      Atom _ _ -> pure []

    relation left right = do
      leftSort <- termSort left
      rightSort <- termSort right
      pure (numericCandidate leftSort <> numericCandidate rightSort)

    termSort term =
      mapLeft NumericPropositionSortError (sortOfRefTerm state term)

numericCandidate :: RefSort -> [RefSort]
numericCandidate sort = case sort of
  SortNat -> [sort]
  SortUInt _ -> [sort]
  SortOpaque _ -> [sort]
  _ -> []

builtInNumericSort :: RefSort -> Bool
builtInNumericSort sort = case sort of
  SortNat -> True
  SortUInt _ -> True
  _ -> False

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
