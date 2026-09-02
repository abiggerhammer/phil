module Phil.Surface.GrammarV1.BoundClaimApplication
  ( grammarV1BoundClaimApplication
  ) where

import qualified Data.Text as Text
import Phil.Core.Syntax (Proposition (..))
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.BoundRefExpression
  ( grammarV1BoundRefExpression
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Proposition (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1StaticReference (..)
  )

-- | Preserve an unspecialized claim identity, including exact qualification,
-- while delegating every argument to the verified binding-aware refinement-
-- expression bridge. Claim existence, arity, and argument sorts remain the
-- competent semantic checker's responsibility exactly as before; this bridge
-- only preserves already-supported argument structure. Unknown/consumed names,
-- qualified or specialized term names, ordinary calls, projections, symbolic
-- multiplication, and specialized claim references remain fail-closed.
grammarV1BoundClaimApplication
  :: SurfaceState
  -> GrammarV1Proposition
  -> Maybe Proposition
grammarV1BoundClaimApplication state source = case source of
  GrammarV1ClaimApplicationProposition reference arguments
    | null (grammarV1StaticReferenceArguments reference) -> do
        claim <- case grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) of
          [] -> Nothing
          parts -> Just (Text.intercalate (Text.singleton '.') parts)
        terms <- mapM (grammarV1BoundRefExpression state) arguments
        Just (Atom claim terms)
  _ -> Nothing
