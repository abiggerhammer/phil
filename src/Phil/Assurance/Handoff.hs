module Phil.Assurance.Handoff
  ( HandoffConfig (..)
  , HandoffError (..)
  , LedgerHandoff (..)
  , handoffResolvedObligation
  , handoffResolvedObligationWithEvidence
  , handoffSupportEdges
  , bindHandoffCertificateEvidence
  ) where

import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance.Types
  ( AcceptanceRule
  , EvidenceDependency (..)
  , EvidenceEntry (..)
  , EvidenceEntryId
  , ObligationRevision (..)
  , RevisionId
  , deriveEvidenceEntryDigest
  , revisionFromCoreObligation
  )
import Phil.Core.Decision
  ( AssumptionRef (..)
  , DecisionCertificate (..)
  , LinearBasis (..)
  , LinearCertificate (..)
  )
import Phil.Core.Discharge
  ( ObligationDisposition (..)
  , ResolvedObligation (..)
  , StaticDischarge (..)
  )
import Phil.Core.Syntax
  ( Name
  , Obligation (..)
  , ObligationId
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

-- | Fail closed when a checker-to-ledger handoff loses support identity or an
-- evidence entry is rebound to the wrong obligation/disposition.
data HandoffError
  = UnknownPrerequisiteSupport ObligationId ObligationId
  | UnknownEvidenceFactSupport ObligationId Name Int
  | HandoffEvidenceRevisionMismatch RevisionId RevisionId
  | HandoffEvidenceNotCertificate RevisionId
  deriving (Eq, Show)

-- | Lossless checker-to-ledger handoff node.  The exact Core disposition is
-- retained rather than prematurely reclassified as final ledger evidence.
-- Runtime implementation artifacts, exported destination obligations, and
-- evidence artifact identities are attached only at the assurance layer.
--
-- 'handoffSupportDependencies' records semantic support used by a retained
-- certificate.  It is deliberately separate from 'revisionGeneratedFrom':
-- generation provenance is child -> parent, while a prerequisite dependency
-- is evidence for parent/consumer -> child/prerequisite.
data LedgerHandoff = LedgerHandoff
  { handoffRevision :: ObligationRevision
  , handoffCanonicalProposition :: Proposition
  , handoffDisposition :: ObligationDisposition
  , handoffSupportDependencies :: [EvidenceDependency]
  }
  deriving (Eq, Show)

-- | Handoff without an external evidence-identity environment.  Certificates
-- that retain an 'EvidenceFact' fail closed here rather than silently losing
-- that support edge.  Call 'handoffResolvedObligationWithEvidence' when Core
-- evidence facts have immutable assurance-ledger identities.
handoffResolvedObligation
  :: HandoffConfig
  -> ResolvedObligation
  -> Either HandoffError [LedgerHandoff]
handoffResolvedObligation config =
  handoffResolvedObligationWithEvidence config Map.empty

-- | Flatten a resolved obligation and its generated prerequisites into
-- immutable revision/disposition nodes, then bind every support reference
-- retained by a decision certificate to an immutable assurance identity.
--
-- 'PrerequisiteFact' references resolve against the complete flattened
-- obligation tree and become 'DependsOnObligation'. 'EvidenceFact' references
-- resolve against the supplied @(binding name, fact index)@ map and become
-- 'DependsOnEvidence'. Missing identities fail closed.
--
-- Child prerequisite revisions continue to record the parent revision in
-- 'revisionGeneratedFrom'.  That lineage remains provenance only; it is never
-- reversed or repurposed as semantic support.
--
-- Resolution processes sibling prerequisites left-to-right, so a later child
-- certificate may depend on an earlier sibling.  The second pass therefore
-- resolves support against the complete flattened tree, not just direct
-- children of the current node.
handoffResolvedObligationWithEvidence
  :: HandoffConfig
  -> Map.Map (Name, Int) EvidenceEntryId
  -> ResolvedObligation
  -> Either HandoffError [LedgerHandoff]
handoffResolvedObligationWithEvidence config evidenceIds root =
  traverse attachSupport flattened
  where
    flattened = flatten [] root

    revisionByObligation = Map.fromList
      [ (revisionObligationId revision, revisionId revision)
      | entry <- flattened
      , let revision = handoffRevision entry
      ]

    attachSupport entry =
      let revision = handoffRevision entry
          consumer = revisionObligationId revision
          disposition = handoffDisposition entry
          prerequisites = dispositionPrerequisites disposition
          evidenceFacts = dispositionEvidenceFacts disposition
          missing = prerequisites `Set.difference` Map.keysSet revisionByObligation
      in case Set.lookupMin missing of
          Just prerequisite -> Left (UnknownPrerequisiteSupport consumer prerequisite)
          Nothing ->
            case traverse resolveEvidenceFact (Set.toAscList evidenceFacts) of
              Left (name, index) ->
                Left (UnknownEvidenceFactSupport consumer name index)
              Right evidenceDependencies -> Right entry
                { handoffSupportDependencies = Set.toAscList . Set.fromList $
                    evidenceDependencies
                      <> [ DependsOnObligation (revisionByObligation Map.! prerequisite)
                         | prerequisite <- Set.toAscList prerequisites
                         ]
                }

    resolveEvidenceFact ref =
      case Map.lookup ref evidenceIds of
        Just evidenceId -> Right (DependsOnEvidence evidenceId)
        Nothing -> Left ref

    flatten :: [RevisionId] -> ResolvedObligation -> [LedgerHandoff]
    flatten generatedFrom resolved =
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
            , handoffSupportDependencies = []
            }
          children = concatMap
            (flatten [revisionId revision])
            (resolvedPrerequisites resolved)
      in current : children

-- | Project only the semantic obligation-support relation in graph direction:
-- @(consumer, prerequisite)@.  Precise evidence-entry dependencies remain in
-- the evidence layer and do not become revision-graph edges. Generation
-- lineage is also intentionally ignored here.
handoffSupportEdges :: [LedgerHandoff] -> Set (RevisionId, RevisionId)
handoffSupportEdges entries = Set.fromList
  [ (revisionId (handoffRevision entry), prerequisite)
  | entry <- entries
  , DependsOnObligation prerequisite <- handoffSupportDependencies entry
  ]

-- | Finalize certificate evidence with the exact support recorded by the
-- checker handoff. Existing precise evidence-entry dependencies are retained,
-- including dependencies outside Core's local fact namespace; exact mapped
-- 'EvidenceFact' dependencies are unioned with them. Existing whole-obligation
-- dependencies are replaced by the authoritative handoff relation, so stale
-- caller-supplied obligation edges cannot masquerade as prerequisite support.
-- The evidence digest is then rebound to the resulting dependency set.
bindHandoffCertificateEvidence
  :: LedgerHandoff
  -> EvidenceEntry
  -> Either HandoffError EvidenceEntry
bindHandoffCertificateEvidence handoff evidence
  | actualRevision /= expectedRevision =
      Left (HandoffEvidenceRevisionMismatch expectedRevision actualRevision)
  | otherwise =
      case handoffDisposition handoff of
        StaticallyDischarged StaticByCertificate {} -> Right finalized
        _ -> Left (HandoffEvidenceNotCertificate expectedRevision)
  where
    expectedRevision = revisionId (handoffRevision handoff)
    actualRevision = evidenceObligationRevision evidence
    preciseEvidenceDependencies =
      [ dependency
      | dependency@(DependsOnEvidence _) <- evidenceDependsOn evidence
      ]
    rebound = evidence
      { evidenceDependsOn = Set.toAscList . Set.fromList $
          preciseEvidenceDependencies <> handoffSupportDependencies handoff
      }
    finalized = rebound
      { evidenceEntryDigest = deriveEvidenceEntryDigest rebound
      }

dispositionPrerequisites :: ObligationDisposition -> Set ObligationId
dispositionPrerequisites disposition =
  case disposition of
    StaticallyDischarged StaticByCertificate { staticCertificate = certificate } ->
      certificatePrerequisites certificate
    _ -> Set.empty

dispositionEvidenceFacts :: ObligationDisposition -> Set (Name, Int)
dispositionEvidenceFacts disposition =
  case disposition of
    StaticallyDischarged StaticByCertificate { staticCertificate = certificate } ->
      certificateEvidenceFacts certificate
    _ -> Set.empty

certificatePrerequisites :: DecisionCertificate -> Set ObligationId
certificatePrerequisites certificate =
  case certificate of
    CertificateTruth -> Set.empty
    CertificateAssumption assumption _ -> assumptionPrerequisites assumption
    CertificateLinear linear -> linearPrerequisites linear
    CertificateConjunction left right ->
      certificatePrerequisites left `Set.union` certificatePrerequisites right
    CertificateDisjunctionLeft left -> certificatePrerequisites left
    CertificateDisjunctionRight right -> certificatePrerequisites right
    CertificateNotEqualLeft linear -> linearPrerequisites linear
    CertificateNotEqualRight linear -> linearPrerequisites linear

certificateEvidenceFacts :: DecisionCertificate -> Set (Name, Int)
certificateEvidenceFacts certificate =
  case certificate of
    CertificateTruth -> Set.empty
    CertificateAssumption assumption _ -> assumptionEvidenceFacts assumption
    CertificateLinear linear -> linearEvidenceFacts linear
    CertificateConjunction left right ->
      certificateEvidenceFacts left `Set.union` certificateEvidenceFacts right
    CertificateDisjunctionLeft left -> certificateEvidenceFacts left
    CertificateDisjunctionRight right -> certificateEvidenceFacts right
    CertificateNotEqualLeft linear -> linearEvidenceFacts linear
    CertificateNotEqualRight linear -> linearEvidenceFacts linear

linearPrerequisites :: LinearCertificate -> Set ObligationId
linearPrerequisites linear = Set.unions
  [ basisPrerequisites basis
  | (basis, _) <- linearTerms linear
  ]

linearEvidenceFacts :: LinearCertificate -> Set (Name, Int)
linearEvidenceFacts linear = Set.unions
  [ basisEvidenceFacts basis
  | (basis, _) <- linearTerms linear
  ]

basisPrerequisites :: LinearBasis -> Set ObligationId
basisPrerequisites basis =
  case basis of
    BasisAssumption assumption _ -> assumptionPrerequisites assumption
    BasisNatLower _ -> Set.empty
    BasisUIntLower _ _ -> Set.empty
    BasisUIntUpper _ _ -> Set.empty

basisEvidenceFacts :: LinearBasis -> Set (Name, Int)
basisEvidenceFacts basis =
  case basis of
    BasisAssumption assumption _ -> assumptionEvidenceFacts assumption
    BasisNatLower _ -> Set.empty
    BasisUIntLower _ _ -> Set.empty
    BasisUIntUpper _ _ -> Set.empty

assumptionPrerequisites :: AssumptionRef -> Set ObligationId
assumptionPrerequisites assumption =
  case assumption of
    PrerequisiteFact obligationId -> Set.singleton obligationId
    EvidenceFact _ _ -> Set.empty

assumptionEvidenceFacts :: AssumptionRef -> Set (Name, Int)
assumptionEvidenceFacts assumption =
  case assumption of
    EvidenceFact name index -> Set.singleton (name, index)
    PrerequisiteFact _ -> Set.empty
