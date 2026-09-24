module Phil.Assurance.Handoff
  ( HandoffConfig (..)
  , HandoffError (..)
  , LedgerHandoff (..)
  , DirectEvidenceAuthorityBinding (..)
  , handoffResolvedObligation
  , handoffResolvedObligationWithEvidence
  , attachDirectNamedEvidenceAuthority
  , handoffSupportEdges
  , bindHandoffCertificateEvidence
  , bindHandoffDirectEvidence
  ) where

import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance.Types
  ( AcceptanceRule
  , AssuranceLedger (..)
  , EvidenceDependency (..)
  , EvidenceEntry (..)
  , EvidenceEntryId
  , ObligationRevision (..)
  , RevisionId
  , deriveEvidenceEntryDigest
  , renderPropositionCanonical
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

-- | Architecture-owned immutable identity for one direct named-evidence use.
-- The map carrying this value is keyed by the exact checking-event obligation
-- and selected Core name, so later reuse of the display name cannot silently
-- substitute another proof record.
newtype DirectEvidenceAuthorityBinding = DirectEvidenceAuthorityBinding
  { directAuthorityEvidenceEntryId :: EvidenceEntryId
  }
  deriving (Eq, Show)

-- | Fail closed when a checker-to-ledger handoff loses support identity or an
-- evidence entry is rebound to the wrong obligation/disposition.
data HandoffError
  = UnknownPrerequisiteSupport ObligationId ObligationId
  | UnknownEvidenceFactSupport ObligationId Name Int
  | MissingDirectEvidenceAuthority ObligationId Name
  | MissingDirectAuthorityEvidenceEntry ObligationId Name EvidenceEntryId
  | MissingDirectAuthorityEvidenceRevision ObligationId Name EvidenceEntryId RevisionId
  | DirectEvidenceAuthorityPropositionMismatch ObligationId Name Text Text
  | DirectEvidenceAuthoritySubjectMismatch ObligationId Name [Text] [Text]
  | DirectEvidenceAuthorityScopeMismatch ObligationId Name Text Text
  | HandoffEvidenceRevisionMismatch RevisionId RevisionId
  | HandoffEvidenceNotCertificate RevisionId
  | HandoffEvidenceNotDirect RevisionId
  | HandoffDirectEvidenceSupportMissing RevisionId Name
  deriving (Eq, Show)

-- | Lossless checker-to-ledger handoff node.  The exact Core disposition is
-- retained rather than prematurely reclassified as final ledger evidence.
-- Runtime implementation artifacts, exported destination obligations, and
-- evidence artifact identities are attached only at the assurance layer.
--
-- 'handoffSupportDependencies' records semantic support required by the
-- resolver for the original goal, together with any additional support named
-- by a retained certificate or a validated direct named-evidence selection.
-- It is deliberately separate from 'revisionGeneratedFrom': generation
-- provenance is child -> parent, while a prerequisite dependency is
-- parent/consumer -> child/prerequisite.
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
-- immutable revision/disposition nodes, retaining every direct prerequisite
-- on which the resolver made the original goal conditional.  Then bind every
-- additional support reference retained by a decision certificate to an
-- immutable assurance identity.
--
-- Direct resolved prerequisites are semantic support even when arithmetic
-- normalization yields an empty certificate or the parent closes by
-- definition.  'PrerequisiteFact' references still resolve against the
-- complete flattened obligation tree and become 'DependsOnObligation'; this
-- additionally handles certificate references to earlier sibling support.
-- 'EvidenceFact' references resolve against the supplied @(binding name, fact
-- index)@ map and become 'DependsOnEvidence'. Missing certificate identities
-- fail closed.
--
-- Direct 'StaticByEvidence' support is intentionally not inferred from a name
-- here. Use 'attachDirectNamedEvidenceAuthority' after the architecture has
-- bound the exact checking event and name to an immutable evidence record.
--
-- Child prerequisite revisions continue to record the parent revision in
-- 'revisionGeneratedFrom'.  That lineage remains provenance only; it is never
-- reversed or repurposed as semantic support.
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
          certificatePrerequisiteIds = dispositionPrerequisites disposition
          evidenceFacts = dispositionEvidenceFacts disposition
          missing = certificatePrerequisiteIds `Set.difference` Map.keysSet revisionByObligation
          resolvedDependencies = handoffSupportDependencies entry
      in case Set.lookupMin missing of
          Just prerequisite -> Left (UnknownPrerequisiteSupport consumer prerequisite)
          Nothing ->
            case traverse resolveEvidenceFact (Set.toAscList evidenceFacts) of
              Left (name, index) ->
                Left (UnknownEvidenceFactSupport consumer name index)
              Right evidenceDependencies -> Right entry
                { handoffSupportDependencies = Set.toAscList . Set.fromList $
                    resolvedDependencies
                      <> evidenceDependencies
                      <> [ DependsOnObligation (revisionByObligation Map.! prerequisite)
                         | prerequisite <- Set.toAscList certificatePrerequisiteIds
                         ]
                }

    resolveEvidenceFact ref =
      case Map.lookup ref evidenceIds of
        Just evidenceId -> Right (DependsOnEvidence evidenceId)
        Nothing -> Left ref

    flatten :: [RevisionId] -> ResolvedObligation -> [LedgerHandoff]
    flatten generatedFrom resolved =
      let revision = revisionFor generatedFrom resolved
          currentRevision = revisionId revision
          prerequisiteDependencies =
            [ DependsOnObligation
                (revisionId (revisionFor [currentRevision] prerequisite))
            | prerequisite <- resolvedPrerequisites resolved
            ]
          current = LedgerHandoff
            { handoffRevision = revision
            , handoffCanonicalProposition = resolvedCanonicalProposition resolved
            , handoffDisposition = resolvedDisposition resolved
            , handoffSupportDependencies = prerequisiteDependencies
            }
          children = concatMap
            (flatten [currentRevision])
            (resolvedPrerequisites resolved)
      in current : children

    revisionFor :: [RevisionId] -> ResolvedObligation -> ObligationRevision
    revisionFor generatedFrom resolved =
      let obligation = resolvedObligation resolved
      in revisionFromCoreObligation
          obligation
          (handoffRevisionKind config obligation)
          (handoffRepresentation config obligation)
          (handoffSubjectIds config obligation)
          (handoffContextIds config obligation)
          (handoffAcceptanceRule config obligation)
          generatedFrom

-- | Bind each direct 'StaticByEvidence' selection to an immutable assurance
-- record using the exact checking-event obligation and selected name.  The
-- source evidence revision must carry the exact checker proposition, semantic
-- subjects, and scope for that event.  This preserves direct valid evidence
-- while preventing later name reuse from standing in for the selected proof.
attachDirectNamedEvidenceAuthority
  :: HandoffConfig
  -> Map.Map (ObligationId, Name) DirectEvidenceAuthorityBinding
  -> AssuranceLedger
  -> ResolvedObligation
  -> [LedgerHandoff]
  -> Either HandoffError [LedgerHandoff]
attachDirectNamedEvidenceAuthority config authorities ledger root entries = do
  supportPairs <- mapM validateDirectUse (directEvidenceUses root)
  let supportByConsumer = Map.fromList supportPairs
  Right (map (attachSupport supportByConsumer) entries)
  where
    validateDirectUse (consumer, evidenceName, proposition, obligation) = do
      authority <-
        case Map.lookup (consumer, evidenceName) authorities of
          Just binding -> Right binding
          Nothing -> Left (MissingDirectEvidenceAuthority consumer evidenceName)
      let evidenceId = directAuthorityEvidenceEntryId authority
      evidence <-
        case Map.lookup evidenceId (ledgerEvidence ledger) of
          Just entry -> Right entry
          Nothing -> Left
            (MissingDirectAuthorityEvidenceEntry consumer evidenceName evidenceId)
      revision <-
        case Map.lookup (evidenceObligationRevision evidence) (ledgerRevisions ledger) of
          Just entry -> Right entry
          Nothing -> Left
            (MissingDirectAuthorityEvidenceRevision
              consumer evidenceName evidenceId (evidenceObligationRevision evidence))
      let expectedStatement = renderPropositionCanonical proposition
          actualStatement = revisionStatement revision
      if actualStatement == expectedStatement
        then Right ()
        else Left
          (DirectEvidenceAuthorityPropositionMismatch
            consumer evidenceName expectedStatement actualStatement)
      let expectedSubjects = sort (handoffSubjectIds config obligation)
          actualSubjects = sort (revisionSubjectIds revision)
      if actualSubjects == expectedSubjects
        then Right ()
        else Left
          (DirectEvidenceAuthoritySubjectMismatch
            consumer evidenceName expectedSubjects actualSubjects)
      let expectedScope = obligationScope obligation
          actualScope = revisionScope revision
      if actualScope == expectedScope
        then Right ()
        else Left
          (DirectEvidenceAuthorityScopeMismatch
            consumer evidenceName expectedScope actualScope)
      Right (consumer, evidenceId)

    attachSupport support entry =
      case Map.lookup (revisionObligationId (handoffRevision entry)) support of
        Nothing -> entry
        Just evidenceId -> entry
          { handoffSupportDependencies = Set.toAscList . Set.fromList $
              DependsOnEvidence evidenceId : handoffSupportDependencies entry
          }

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

-- | Finalize a direct named-evidence disposition with the exact immutable
-- support established by 'attachDirectNamedEvidenceAuthority'.  A raw
-- 'StaticByEvidence' handoff that has only a display name is rejected: final
-- closure must not infer authority from spelling alone.
bindHandoffDirectEvidence
  :: LedgerHandoff
  -> EvidenceEntry
  -> Either HandoffError EvidenceEntry
bindHandoffDirectEvidence handoff evidence
  | actualRevision /= expectedRevision =
      Left (HandoffEvidenceRevisionMismatch expectedRevision actualRevision)
  | otherwise =
      case handoffDisposition handoff of
        StaticallyDischarged (StaticByEvidence evidenceName)
          | hasDirectSupport -> Right finalized
          | otherwise -> Left
              (HandoffDirectEvidenceSupportMissing expectedRevision evidenceName)
        _ -> Left (HandoffEvidenceNotDirect expectedRevision)
  where
    expectedRevision = revisionId (handoffRevision handoff)
    actualRevision = evidenceObligationRevision evidence
    hasDirectSupport = any isEvidenceDependency (handoffSupportDependencies handoff)
    isEvidenceDependency dependency = case dependency of
      DependsOnEvidence _ -> True
      DependsOnObligation _ -> False
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

directEvidenceUses
  :: ResolvedObligation
  -> [(ObligationId, Name, Proposition, Obligation)]
directEvidenceUses resolved =
  current <> concatMap directEvidenceUses (resolvedPrerequisites resolved)
  where
    obligation = resolvedObligation resolved
    current = case resolvedDisposition resolved of
      StaticallyDischarged (StaticByEvidence evidenceName) ->
        [ ( obligationId obligation
          , evidenceName
          , resolvedCanonicalProposition resolved
          , obligation
          )
        ]
      _ -> []

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
