module Phil.Surface.GrammarV1.CallableAuthority
  ( grammarV1CallableAuthorityRequirement
  , grammarV1CallableAuthoritySet
  , grammarV1CallableAuthorityBounds
  ) where

import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.CallableRefinement
  ( CallableAuthorityRequirement (..)
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableClause (..)
  , GrammarV1CallableContractDecl (..)
  , GrammarV1QualifiedName (..)
  , GrammarV1StaticReference (..)
  , GrammarV1Type (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Preserve the first exact Grammar-v1 callable-authority identity fragment as
-- Core's Text-backed CallableAuthorityRequirement. Only unspecialized named
-- types are competent here: a static specialization or a structured type carries
-- semantic structure that must not be flattened into a textual authority label.
grammarV1CallableAuthorityRequirement
  :: GrammarV1Type
  -> Maybe CallableAuthorityRequirement
grammarV1CallableAuthorityRequirement source = case source of
  GrammarV1NamedType reference
    | null (grammarV1StaticReferenceArguments reference) ->
        case grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) of
          [] -> Nothing
          parts -> Just
            (CallableAuthorityRequirement
              (Text.intercalate (Text.singleton '.') parts))
  _ -> Nothing

-- | Route one Grammar-v1 authority type set into Core's finite caller-authority
-- surface. Source order and duplicate spellings intentionally normalize through
-- the existing semantic Set carrier. One non-competent type rejects the whole
-- set rather than being dropped or approximated.
grammarV1CallableAuthoritySet
  :: [Located GrammarV1Type]
  -> Maybe (Set.Set CallableAuthorityRequirement)
grammarV1CallableAuthoritySet source =
  Set.fromList <$> mapM
    (grammarV1CallableAuthorityRequirement . locatedValue)
    source

-- | Preserve each callable authority clause as a separate Core authority set in
-- source order. This projection does not invent a declaration-level cardinality
-- rule or silently union repeated clauses. Exact absence is Just [].
grammarV1CallableAuthorityBounds
  :: GrammarV1CallableContractDecl
  -> Maybe [Set.Set CallableAuthorityRequirement]
grammarV1CallableAuthorityBounds source =
  mapM grammarV1CallableAuthoritySet
    [ authorityTypes
    | Located _ (GrammarV1CallableAuthority authorityTypes) <- grammarV1CallableClauses source
    ]
