module Phil.Surface.GrammarV1.CallableCost
  ( GrammarV1CallableCostClause (..)
  , grammarV1CallableCostClauses
  ) where

import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableClause (..)
  , GrammarV1CallableContractDecl (..)
  , GrammarV1Expression
  )
import Phil.Surface.Syntax (Located (..))

-- | One exact caller-visible Grammar-v1 cost clause at the SURF-008
-- correspondence boundary.
--
-- ADR-015 keeps callable cost separate from effects and points to the separately
-- governed ADR-011 cost/resource model. The source expression is therefore
-- preserved as the exact semantic handoff selected by the programmer. This
-- bridge does not reinterpret an integer literal as cycles, bytes, allocations,
-- time, memory, or any other target metric, and it does not manufacture a
-- Systems CostClass/CostShape or physical charge identity from source spelling.
-- The competent cost-model/resolution layer must consume this exact Located
-- expression and attach whatever stable model identity and quantitative meaning
-- the applicable cost contract establishes.
newtype GrammarV1CallableCostClause = GrammarV1CallableCostClause
  { grammarV1CallableCostExpression :: Located GrammarV1Expression
  }
  deriving (Eq, Show)

-- | Preserve every callable cost clause in exact source order. Clause
-- multiplicity and duplicate expressions remain visible; this layer has no
-- authority to combine independent cost contracts or pick one as dominant.
-- Exact absence is the empty list. Other callable clauses are ignored rather
-- than being reclassified as cost.
grammarV1CallableCostClauses
  :: GrammarV1CallableContractDecl
  -> [GrammarV1CallableCostClause]
grammarV1CallableCostClauses source =
  [ GrammarV1CallableCostClause expression
  | Located _ (GrammarV1CallableCost expression) <- grammarV1CallableClauses source
  ]
