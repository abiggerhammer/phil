module Phil.Surface.GrammarV1.CheckedProposition
  ( grammarV1CheckedProposition
  ) where

import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  , canonicalizeProposition
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax (Proposition)
import Phil.Surface.Check.Types
  ( SurfaceState
  , stateCore
  )
import Phil.Surface.GrammarV1.BoundProposition
  ( grammarV1BoundProposition
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1Proposition)

-- | Compose the complete already-supported binding-aware Grammar-v1
-- proposition tree with Core's established focusing authority. Structural
-- source non-competence remains Nothing. Once a Core proposition exists, claim
-- existence/arity/sorts, transparent expansion, UInt-to-Nat focusing,
-- proposition sort checking, recursive-claim rejection, and normalization are
-- owned exactly once by canonicalizeProposition over the supplied StaticContext
-- and the live Core CheckState. This bridge adds no leaf-local retry, claim
-- table, coercion, proof, evidence, assumption, or fallback interpretation.
grammarV1CheckedProposition
  :: StaticContext
  -> SurfaceState
  -> GrammarV1Proposition
  -> Maybe (Either FocusingError (Proposition, [FocusStep]))
grammarV1CheckedProposition staticContext state source = do
  proposition <- grammarV1BoundProposition state source
  pure (canonicalizeProposition staticContext (stateCore state) proposition)
