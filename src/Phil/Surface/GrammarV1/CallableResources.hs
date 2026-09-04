module Phil.Surface.GrammarV1.CallableResources
  ( GrammarV1CallableResourceDisposition (..)
  , GrammarV1CallableResourceClause (..)
  , grammarV1CallableResourceClauses
  ) where

import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableClause (..)
  , GrammarV1CallableContractDecl (..)
  , GrammarV1QualifiedName
  )
import Phil.Surface.Syntax (Located (..))

-- | The caller-visible resource disposition selected by one Grammar-v1
-- callable clause. Consume and borrow are kept as distinct semantic categories;
-- this surface does not treat either as an effect, authority requirement, or
-- structural-mode inference.
data GrammarV1CallableResourceDisposition
  = GrammarV1CallableConsumesResource
  | GrammarV1CallableBorrowsResource
  deriving (Eq, Ord, Show)

-- | One exact parsed callable resource clause at the SURF-008 correspondence
-- boundary. Clause boundaries, source order, designator order, duplicate
-- designators, qualification, and every designator's Located source occurrence
-- are preserved unchanged.
--
-- The qualified names are deliberately not converted into runtime ownership or
-- loan identities here. A competent binder/name-resolution layer must attach
-- exact term/resource occurrence evidence to these exact Located designators;
-- source spelling is not occurrence identity. Resource availability, mode,
-- consume legality, loan lifetime, subject continuity, and outcome residue are
-- likewise later semantic checks. SURF-009 therefore remains authoritative for
-- binder identity and scope.
data GrammarV1CallableResourceClause = GrammarV1CallableResourceClause
  { grammarV1CallableResourceDisposition
      :: GrammarV1CallableResourceDisposition
  , grammarV1CallableResourceDesignators
      :: [Located GrammarV1QualifiedName]
  }
  deriving (Eq, Show)

-- | Preserve every caller-visible consumes/borrows clause in exact source order.
-- Other callable clauses are intentionally ignored rather than reclassified.
-- Exact absence is the empty list. Because this function performs no name
-- resolution, generic/static context cannot alter the selected resource
-- disposition or manufacture a term occurrence.
grammarV1CallableResourceClauses
  :: GrammarV1CallableContractDecl
  -> [GrammarV1CallableResourceClause]
grammarV1CallableResourceClauses source =
  foldr collect [] (grammarV1CallableClauses source)
  where
    collect (Located _ clause) rest = case clause of
      GrammarV1CallableConsumes designators ->
        GrammarV1CallableResourceClause
          { grammarV1CallableResourceDisposition =
              GrammarV1CallableConsumesResource
          , grammarV1CallableResourceDesignators = designators
          } : rest
      GrammarV1CallableBorrows designators ->
        GrammarV1CallableResourceClause
          { grammarV1CallableResourceDisposition =
              GrammarV1CallableBorrowsResource
          , grammarV1CallableResourceDesignators = designators
          } : rest
      _ -> rest
