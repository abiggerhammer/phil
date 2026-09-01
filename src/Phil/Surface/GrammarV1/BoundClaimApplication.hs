module Phil.Surface.GrammarV1.BoundClaimApplication
  ( grammarV1BoundClaimApplication
  ) where

import Control.Applicative ((<|>))
import qualified Data.Text as Text
import Phil.Core.Syntax (Proposition (..), RefTerm)
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.BoundRef (grammarV1BoundRefTerm)
import Phil.Surface.GrammarV1.Elaborate (grammarV1IntrinsicRefLiteral)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Proposition (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1StaticReference (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Preserve a bare, unspecialized claim identity while admitting only argument
-- terms whose meaning is already verified: intrinsic scalar literals or simple
-- live surface bindings. Claim existence, arity, and argument sorts remain the
-- competent semantic checker's responsibility exactly as for the intrinsic
-- claim bridge. Unknown/consumed names, qualified or specialized term names,
-- calls, projections, arithmetic, and specialized claim references fail closed.
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
        terms <- mapM verifiedTerm arguments
        Just (Atom claim terms)
  _ -> Nothing
  where
    verifiedTerm :: Located a -> Maybe RefTerm
    verifiedTerm _ = Nothing
