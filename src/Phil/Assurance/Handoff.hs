module Phil.Assurance.Handoff
  ( HandoffConfig (..)
  , LedgerHandoff (..)
  , handoffResolvedObligation
  ) where

import Data.Text (Text)
import Phil.Assurance.Types
  ( AcceptanceRule
  , ObligationRevision (..)
  , RevisionId
  , revisionFromCoreObligation
  )
import Phil.Core.Discharge
  ( ObligationDisposition
  , ResolvedObligation (..)
  )
import Phil.Core.Syntax
  ( Obligation
  , Proposition
  )

-- | Architecture-owned metadata required to turn a checker result into an
-- immutable assurance-ledger revision.  The Core checker deliberately does
-- not know acceptance policy, subject/context naming, or representation
-- lineage metadata, so the handoff requires those explicitly instead of
-- guessing them.
data HandoffConfig = HandoffConfig
  { handoffRevisionKind :: Obligation -> Text
  , handoffRepresentation :: Obligation -> Text
  , handoffSubjectIds :: Obligation -> [Text]
  , handoffContextIds :: Obligation -> [Text]
  , handoffAcceptanceRule :: Obligation -> AcceptanceRule
  }

-- | Lossless checker-to-ledger handoff node.  The exact Core disposition is
-- retained rather than prematurely reclassified as final ledger evidence.
-- Runtime implementation artifacts, exported destination obligations, and
-- evidence artifact identities are attached only at the assurance layer.
data LedgerHandoff = LedgerHandoff
  { handoffRevision :: ObligationRevision
  , handoffCanonicalProposition :: Proposition
  , handoffDisposition :: ObligationDisposition
  }
  deriving (Eq, Show)

-- | Flatten a resolved obligation and its generated prerequisites into
-- immutable revision/disposition nodes.  Child prerequisite revisions record
-- the parent revision in generated_from; the parent does not depend on the
-- child's identity for its own logical revision ID.
handoffResolvedObligation
  :: HandoffConfig
  -> ResolvedObligation
  -> [LedgerHandoff]
handoffResolvedObligation config = go []
  where
    go :: [RevisionId] -> ResolvedObligation -> [LedgerHandoff]
    go generatedFrom resolved =
      let obligation = resolvedObligation resolved
          revision = revisionFromCoreObligation
            obligation
            (handoffRevisionKind config obligation)
            (handoffRepresentation config obligation)
            (handoffSubjectIds config obligation)
            (handoffContextIds config obligation)
            (handoffAcceptanceRule config obligation)
            generatedFrom
          current = LedgerHandoff
            { handoffRevision = revision
            , handoffCanonicalProposition = resolvedCanonicalProposition resolved
            , handoffDisposition = resolvedDisposition resolved
            }
          children = concatMap
            (go [revisionId revision])
            (resolvedPrerequisites resolved)
      in current : children
