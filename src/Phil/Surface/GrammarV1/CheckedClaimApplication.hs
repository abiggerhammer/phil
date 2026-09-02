module Phil.Surface.GrammarV1.CheckedClaimApplication
  ( grammarV1CheckedClaimApplication
  ) where

import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  , canonicalizeProposition
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax (Proposition)
import Phil.Surface.Check.Types (SurfaceState (..))
import Phil.Surface.GrammarV1.BoundClaimApplication
  ( grammarV1BoundClaimApplication
  )
import Phil.Surface.GrammarV1.Parser (GrammarV1Proposition)

-- | Compose the already-verified structural claim-application bridge with the
-- Core checker that owns claim existence, arity, argument sorts, transparent
-- expansion, recursion rejection, and expected-Nat coercion. Source forms that
-- are still outside the structural bridge remain Nothing. Once an Atom has been
-- constructed, every semantic acceptance or rejection is delegated exactly to
-- canonicalizeProposition; this module does not maintain a second claim table,
-- retry arguments under another sort, or invent evidence/definitions.
grammarV1CheckedClaimApplication
  :: StaticContext
  -> SurfaceState
  -> GrammarV1Proposition
  -> Maybe (Either FocusingError (Proposition, [FocusStep]))
grammarV1CheckedClaimApplication staticContext state source = do
  structural <- grammarV1BoundClaimApplication state source
  pure (canonicalizeProposition staticContext (stateCore state) structural)
