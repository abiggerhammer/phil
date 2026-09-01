module Phil.Surface.GrammarV1.BoundRef
  ( grammarV1BoundRefTerm
  ) where

import qualified Data.Map.Strict as Map
import Phil.Core.Syntax (Name (..), RefTerm (..))
import Phil.Surface.Check.Types (SurfaceState (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Expression (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1StaticReference (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Resolve only a simple Grammar-v1 term name that is already present in the
-- competent live surface binding environment. This bridge deliberately does not
-- guess qualification, static specialization, calls, projections, or unknown
-- identities merely to obtain a Core RefVar.
grammarV1BoundRefTerm
  :: SurfaceState
  -> Located GrammarV1Expression
  -> Maybe RefTerm
grammarV1BoundRefTerm state (Located _ expression) = case expression of
  GrammarV1NameExpression reference arguments
    | null arguments
    , null (grammarV1StaticReferenceArguments reference) ->
        case grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) of
          [name]
            | Map.member name (stateBindings state) ->
                Just (RefVar (Name name))
          _ -> Nothing
  _ -> Nothing
