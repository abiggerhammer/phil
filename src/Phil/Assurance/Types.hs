{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.Types
  ( Digest (..)
  , RevisionId (..)
  , EvidenceEntryId (..)
  , AssumptionId (..)
  , ArtifactRef (..)
  , ExportId (..)
  , AssuranceUseId (..)
  , AssuranceKind (..)
  , EvidenceRole (..)
  , AcceptanceRule (..)
  , ValidityScope (..)
  , ArtifactIdentity (..)
  , ObligationRevision (..)
  , EvidenceDependency (..)
  , EvidenceResult (..)
  , RuntimeMechanism (..)
  , EvidenceEntry (..)
  , Assumption (..)
  , ExportEntry (..)
  , AssuranceUse (..)
  , AssuranceLedger (..)
  , AssuranceManifest (..)
  , VerificationContext (..)
  , emptyLedger
  , emptyManifest
  , emptyVerificationContext
  , digestText
  , renderPropositionCanonical
  , deriveRevisionId
  , revisionFromCoreObligation
  , deriveEvidenceEntryId
  , deriveAssumptionId
  , deriveExportId
  , deriveManifestId
  ) where

import qualified Crypto.Hash.SHA256 as SHA256
import Data.Bits (shiftR, (.&.))
import qualified Data.ByteString as ByteString
import Data.List (sort)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Data.Word (Word8)
import Phil.Core.Syntax
  ( Name (..)
  , Obligation (..)
  , ObligationId (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  )

newtype Digest = Digest { unDigest :: Text }
  deriving (Eq, Ord, Show)

newtype RevisionId = RevisionId { unRevisionId :: Text }
  deriving (Eq, Ord, Show)

newtype EvidenceEntryId = EvidenceEntryId { unEvidenceEntryId :: Text }
  deriving (Eq, Ord, Show)

newtype AssumptionId = AssumptionId { unAssumptionId :: Text }
  deriving (Eq, Ord, Show)

newtype ArtifactRef = ArtifactRef { unArtifactRef :: Text }
  deriving (Eq, Ord, Show)

newtype ExportId = ExportId { unExportId :: Text }
  deriving (Eq, Ord, Show)

newtype AssuranceUseId = AssuranceUseId { unAssuranceUseId :: Text }
  deriving (Eq, Ord, Show)

data AssuranceKind
  = KernelChecked
  | ProofAssistantTheorem
  | CertificateChecked
  | TranslationValidated
  | DifferentialTested
  | PropertyTested
  | RuntimeEnforced
  | Assumed
  deriving (Eq, Ord, Show)

newtype EvidenceRole = EvidenceRole { unEvidenceRole :: Text }
  deriving (Eq, Ord, Show)

data AcceptanceRule
  = AcceptEntry AssuranceKind EvidenceRole
  | AcceptAll [AcceptanceRule]
  | AcceptAny [AcceptanceRule]
  deriving (Eq, Ord, Show)

newtype ValidityScope = ValidityScope
  { validityDimensions :: Map Text Text
  }
  deriving (Eq, Ord, Show)

data ArtifactIdentity = ArtifactIdentity
  { artifactReference :: ArtifactRef
  , artifactDigest :: Digest
  }
  deriving (Eq, Ord, Show)

data ObligationRevision = ObligationRevision
  { revisionObligationId :: ObligationId
  , revisionId :: RevisionId
  , revisionStatement :: Text
  , revisionStatementDigest :: Digest
  , revisionKind :: Text
  , revisionOrigin :: Text
  , revisionScope :: Text
  , revisionRequiredAt :: Text
  , revisionRepresentation :: Text
  , revisionSubjectIds :: [Text]
  , revisionContextIds :: [Text]
  , revisionAcceptanceRule :: AcceptanceRule
  , revisionGeneratedFrom :: [RevisionId]
  }
  deriving (Eq, Ord, Show)

data EvidenceDependency
  = DependsOnEvidence EvidenceEntryId
  | DependsOnObligation RevisionId
  deriving (Eq, Ord, Show)

data EvidenceResult
  = EvidenceAccepted
  | EvidenceRejected Text
  deriving (Eq, Ord, Show)

data RuntimeMechanism = RuntimeMechanism
  { runtimeMechanismName :: Text
  , runtimeExecutionPoint :: Text
  , runtimeSuccessEvidenceType :: Text
  , runtimeFailureContract :: Text
  , runtimeImplementation :: Maybe ArtifactIdentity
  }
  deriving (Eq, Ord, Show)

data EvidenceEntry = EvidenceEntry
  { evidenceEntryId :: EvidenceEntryId
  , evidenceObligationRevision :: RevisionId
  , evidenceAssuranceKind :: AssuranceKind
  , evidenceRole :: EvidenceRole
  , evidenceProducer :: Text
  , evidenceChecker :: Text
  , evidenceArtifact :: Maybe ArtifactIdentity
  , evidenceInputDigests :: [Digest]
  , evidenceAssumptions :: [AssumptionId]
  , evidenceDependsOn :: [EvidenceDependency]
  , evidenceValidityScope :: ValidityScope
  , evidenceResult :: EvidenceResult
  , evidenceJustifies :: [Text]
  , evidenceRuntimeMechanism :: Maybe RuntimeMechanism
  , evidenceRuntimeResidue :: [Text]
  , evidenceCostRefs :: [Text]
  }
  deriving (Eq, Ord, Show)

data Assumption = Assumption
  { assumptionId :: AssumptionId
  , assumptionStatement :: Text
  , assumptionScope :: Text
  , assumptionOwnerBoundary :: Text
  , assumptionRationale :: Text
  , assumptionValidityScope :: ValidityScope
  }
  deriving (Eq, Ord, Show)

data ExportEntry = ExportEntry
  { exportId :: ExportId
  , exportObligationRevision :: RevisionId
  , exportDestinationBoundary :: Text
  , exportDerivedObligationId :: ObligationId
  , exportValidityScope :: ValidityScope
  }
  deriving (Eq, Ord, Show)

data AssuranceUse
  = ErasureUse
      { assuranceUseId :: AssuranceUseId
      , useObligationRevision :: RevisionId
      , useEvidenceEntries :: [EvidenceEntryId]
      }
  | RetainedRuntimeUse
      { assuranceUseId :: AssuranceUseId
      , useObligationRevision :: RevisionId
      , useRuntimeEvidence :: EvidenceEntryId
      , useCostRef :: Text
      }
  deriving (Eq, Ord, Show)

data AssuranceLedger = AssuranceLedger
  { ledgerRevisions :: Map RevisionId ObligationRevision
  , ledgerEvidence :: Map EvidenceEntryId EvidenceEntry
  , ledgerAssumptions :: Map AssumptionId Assumption
  , ledgerExports :: Map ExportId ExportEntry
  , ledgerUses :: Map AssuranceUseId AssuranceUse
  }
  deriving (Eq, Show)

data AssuranceManifest = AssuranceManifest
  { manifestId :: Digest
  , manifestArchitectureDigest :: Digest
  , manifestPhilCoreDigest :: Digest
  , manifestImplementationDigest :: Digest
  , manifestTarget :: Text
  , manifestCompilationProfile :: Text
  , manifestObligationRevisions :: Set RevisionId
  , manifestCertificationScope :: Set RevisionId
  , manifestEvidenceEntries :: Set EvidenceEntryId
  , manifestAssumptionNodes :: Set AssumptionId
  , manifestExports :: Set ExportId
  , manifestAssuranceUses :: Set AssuranceUseId
  , manifestLoweringLedgerRoot :: Digest
  , manifestValidityContext :: Map Text Text
  }
  deriving (Eq, Show)

data VerificationContext = VerificationContext
  { verificationArchitectureDigest :: Digest
  , verificationPhilCoreDigest :: Digest
  , verificationImplementationDigest :: Digest
  , verificationTarget :: Text
  , verificationCompilationProfile :: Text
  , verificationExpectedObligations :: Set RevisionId
  , verificationPermittedAssumptions :: Set AssumptionId
  , verificationPermittedExportBoundaries :: Set Text
  , verificationAvailableArtifacts :: Map ArtifactRef Digest
  , verificationLoweringLedgerRoot :: Digest
  , verificationKnownCostRefs :: Set Text
  , verificationValidityContext :: Map Text Text
  }
  deriving (Eq, Show)

emptyLedger :: AssuranceLedger
emptyLedger = AssuranceLedger
  { ledgerRevisions = Map.empty
  , ledgerEvidence = Map.empty
  , ledgerAssumptions = Map.empty
  , ledgerExports = Map.empty
  , ledgerUses = Map.empty
  }

emptyManifest :: AssuranceManifest
emptyManifest = AssuranceManifest
  { manifestId = Digest ""
  , manifestArchitectureDigest = Digest ""
  , manifestPhilCoreDigest = Digest ""
  , manifestImplementationDigest = Digest ""
  , manifestTarget = ""
  , manifestCompilationProfile = ""
  , manifestObligationRevisions = Set.empty
  , manifestCertificationScope = Set.empty
  , manifestEvidenceEntries = Set.empty
  , manifestAssumptionNodes = Set.empty
  , manifestExports = Set.empty
  , manifestAssuranceUses = Set.empty
  , manifestLoweringLedgerRoot = Digest ""
  , manifestValidityContext = Map.empty
  }

emptyVerificationContext :: VerificationContext
emptyVerificationContext = VerificationContext
  { verificationArchitectureDigest = Digest ""
  , verificationPhilCoreDigest = Digest ""
  , verificationImplementationDigest = Digest ""
  , verificationTarget = ""
  , verificationCompilationProfile = ""
  , verificationExpectedObligations = Set.empty
  , verificationPermittedAssumptions = Set.empty
  , verificationPermittedExportBoundaries = Set.empty
  , verificationAvailableArtifacts = Map.empty
  , verificationLoweringLedgerRoot = Digest ""
  , verificationKnownCostRefs = Set.empty
  , verificationValidityContext = Map.empty
  }

digestText :: Text -> Digest
digestText value = Digest . Text.pack . concatMap hexByte . ByteString.unpack $
  SHA256.hash (Text.encodeUtf8 value)
  where
    hexByte :: Word8 -> String
    hexByte byte = [hexDigit (byte `shiftR` 4), hexDigit (byte .&. 0x0f)]

    hexDigit :: Word8 -> Char
    hexDigit nibble
      | nibble < 10 = toEnum (fromEnum '0' + fromIntegral nibble)
      | otherwise = toEnum (fromEnum 'a' + fromIntegral nibble - 10)

renderPropositionCanonical :: Proposition -> Text
renderPropositionCanonical proposition = case proposition of
  Truth -> "true"
  Falsehood -> "false"
  Equal left right -> binary "eq" left right
  NotEqual left right -> binary "neq" left right
  LessThan left right -> binary "lt" left right
  LessEqual left right -> binary "le" left right
  Member value collection -> binary "member" value collection
  Disjoint left right -> binary "disjoint" left right
  Conjunction left right ->
    "and(" <> renderPropositionCanonical left <> "," <> renderPropositionCanonical right <> ")"
  Disjunction left right ->
    "or(" <> renderPropositionCanonical left <> "," <> renderPropositionCanonical right <> ")"
  Negation inner -> "not(" <> renderPropositionCanonical inner <> ")"
  Atom claim arguments ->
    "atom(" <> atomText claim <> "," <> listText (map renderRefTerm arguments) <> ")"
  where
    binary tag left right =
      tag <> "(" <> renderRefTerm left <> "," <> renderRefTerm right <> ")"

renderRefTerm :: RefTerm -> Text
renderRefTerm term = case term of
  RefVar (Name name) -> "var(" <> atomText name <> ")"
  RefNat value -> "nat(" <> Text.pack (show value) <> ")"
  RefUInt width value ->
    "uint(" <> Text.pack (show width) <> "," <> Text.pack (show value) <> ")"
  RefBool value -> if value then "bool(true)" else "bool(false)"
  RefField base field sort ->
    "field(" <> renderRefTerm base <> "," <> atomText field <> "," <> renderSort sort <> ")"
  RefLen value -> "len(" <> renderRefTerm value <> ")"
  RefToNat value -> "toNat(" <> renderRefTerm value <> ")"
  RefAdd left right -> "add(" <> renderRefTerm left <> "," <> renderRefTerm right <> ")"
  RefSub left right -> "sub(" <> renderRefTerm left <> "," <> renderRefTerm right <> ")"
  RefScale coefficient value ->
    "scale(" <> Text.pack (show coefficient) <> "," <> renderRefTerm value <> ")"
  RefOpaque sort value ->
    "opaque(" <> renderSort sort <> "," <> atomText value <> ")"

renderSort :: RefSort -> Text
renderSort sort = case sort of
  SortBool -> "Bool"
  SortNat -> "Nat"
  SortUInt width -> "UInt(" <> Text.pack (show width) <> ")"
  SortEnum name -> "Enum(" <> atomText name <> ")"
  SortFiniteSeq inner -> "Seq(" <> renderSort inner <> ")"
  SortFiniteSet inner -> "Set(" <> renderSort inner <> ")"
  SortStableId kind -> "StableId(" <> atomText kind <> ")"
  SortOpaque name -> "OpaqueSort(" <> atomText name <> ")"

atomText :: Text -> Text
atomText value = Text.pack (show (Text.length value)) <> ":" <> value

listText :: [Text] -> Text
listText values = "[" <> Text.intercalate "," values <> "]"

canonicalFields :: [(Text, Text)] -> Text
canonicalFields fields = Text.intercalate "|"
  [ atomText key <> "=" <> atomText value
  | (key, value) <- fields
  ]

renderAcceptanceRule :: AcceptanceRule -> Text
renderAcceptanceRule rule = case rule of
  AcceptEntry kind (EvidenceRole role) ->
    "entry(" <> Text.pack (show kind) <> "," <> atomText role <> ")"
  AcceptAll rules -> "all" <> listText (map renderAcceptanceRule rules)
  AcceptAny rules -> "any" <> listText (map renderAcceptanceRule rules)

renderValidityScope :: ValidityScope -> Text
renderValidityScope (ValidityScope dimensions) = canonicalFields (Map.toAscList dimensions)

deriveRevisionId :: ObligationRevision -> RevisionId
deriveRevisionId revision = RevisionId ("rev.sha256." <> unDigest (digestText payload))
  where
    payload = canonicalFields
      [ ("obligation", unObligationId (revisionObligationId revision))
      , ("statement_digest", unDigest (revisionStatementDigest revision))
      , ("kind", revisionKind revision)
      , ("origin", revisionOrigin revision)
      , ("scope", revisionScope revision)
      , ("required_at", revisionRequiredAt revision)
      , ("representation", revisionRepresentation revision)
      , ("subjects", listText (sort (revisionSubjectIds revision)))
      , ("contexts", listText (sort (revisionContextIds revision)))
      , ("acceptance", renderAcceptanceRule (revisionAcceptanceRule revision))
      ]

revisionFromCoreObligation
  :: Obligation
  -> Text
  -> Text
  -> [Text]
  -> [Text]
  -> AcceptanceRule
  -> [RevisionId]
  -> ObligationRevision
revisionFromCoreObligation obligation kind representation subjects contexts acceptance generatedFrom =
  let statement = renderPropositionCanonical (obligationProposition obligation)
      statementDigest = digestText statement
      provisional = ObligationRevision
        { revisionObligationId = obligationId obligation
        , revisionId = RevisionId ""
        , revisionStatement = statement
        , revisionStatementDigest = statementDigest
        , revisionKind = kind
        , revisionOrigin = obligationOrigin obligation
        , revisionScope = obligationScope obligation
        , revisionRequiredAt = obligationRequiredPoint obligation
        , revisionRepresentation = representation
        , revisionSubjectIds = subjects
        , revisionContextIds = contexts
        , revisionAcceptanceRule = acceptance
        , revisionGeneratedFrom = generatedFrom
        }
  in provisional { revisionId = deriveRevisionId provisional }

deriveEvidenceEntryId :: EvidenceEntry -> EvidenceEntryId
deriveEvidenceEntryId entry = EvidenceEntryId ("evidence.sha256." <> unDigest (digestText payload))
  where
    payload = canonicalFields
      [ ("revision", unRevisionId (evidenceObligationRevision entry))
      , ("kind", Text.pack (show (evidenceAssuranceKind entry)))
      , ("role", unEvidenceRole (evidenceRole entry))
      , ("producer", evidenceProducer entry)
      , ("checker", evidenceChecker entry)
      , ("artifact", maybe "" renderArtifact (evidenceArtifact entry))
      , ("inputs", listText (sort (map unDigest (evidenceInputDigests entry))))
      , ("assumptions", listText (sort (map unAssumptionId (evidenceAssumptions entry))))
      , ("depends", listText (sort (map renderDependency (evidenceDependsOn entry))))
      , ("validity", renderValidityScope (evidenceValidityScope entry))
      , ("result", renderResult (evidenceResult entry))
      , ("justifies", listText (sort (evidenceJustifies entry)))
      , ("runtime", maybe "" renderRuntime (evidenceRuntimeMechanism entry))
      , ("residue", listText (sort (evidenceRuntimeResidue entry)))
      , ("cost", listText (sort (evidenceCostRefs entry)))
      ]

    renderArtifact artifact =
      unArtifactRef (artifactReference artifact) <> "@" <> unDigest (artifactDigest artifact)

    renderDependency dependency = case dependency of
      DependsOnEvidence entryId -> "evidence:" <> unEvidenceEntryId entryId
      DependsOnObligation revision -> "obligation:" <> unRevisionId revision

    renderResult result = case result of
      EvidenceAccepted -> "accepted"
      EvidenceRejected reason -> "rejected:" <> reason

    renderRuntime runtime = canonicalFields
      [ ("name", runtimeMechanismName runtime)
      , ("point", runtimeExecutionPoint runtime)
      , ("success", runtimeSuccessEvidenceType runtime)
      , ("failure", runtimeFailureContract runtime)
      , ("implementation", maybe "" renderArtifact (runtimeImplementation runtime))
      ]

deriveAssumptionId :: Assumption -> AssumptionId
deriveAssumptionId assumption = AssumptionId ("assumption.sha256." <> unDigest (digestText payload))
  where
    payload = canonicalFields
      [ ("statement", assumptionStatement assumption)
      , ("scope", assumptionScope assumption)
      , ("owner", assumptionOwnerBoundary assumption)
      , ("rationale", assumptionRationale assumption)
      , ("validity", renderValidityScope (assumptionValidityScope assumption))
      ]

deriveExportId :: ExportEntry -> ExportId
deriveExportId export = ExportId ("export.sha256." <> unDigest (digestText payload))
  where
    payload = canonicalFields
      [ ("revision", unRevisionId (exportObligationRevision export))
      , ("destination", exportDestinationBoundary export)
      , ("derived", unObligationId (exportDerivedObligationId export))
      , ("validity", renderValidityScope (exportValidityScope export))
      ]

deriveManifestId :: AssuranceManifest -> Digest
deriveManifestId manifest = digestText (canonicalFields
  [ ("architecture", unDigest (manifestArchitectureDigest manifest))
  , ("core", unDigest (manifestPhilCoreDigest manifest))
  , ("implementation", unDigest (manifestImplementationDigest manifest))
  , ("target", manifestTarget manifest)
  , ("profile", manifestCompilationProfile manifest)
  , ("obligations", renderSet unRevisionId (manifestObligationRevisions manifest))
  , ("scope", renderSet unRevisionId (manifestCertificationScope manifest))
  , ("evidence", renderSet unEvidenceEntryId (manifestEvidenceEntries manifest))
  , ("assumptions", renderSet unAssumptionId (manifestAssumptionNodes manifest))
  , ("exports", renderSet unExportId (manifestExports manifest))
  , ("uses", renderSet unAssuranceUseId (manifestAssuranceUses manifest))
  , ("lowering", unDigest (manifestLoweringLedgerRoot manifest))
  , ("validity", canonicalFields (Map.toAscList (manifestValidityContext manifest)))
  ])
  where
    renderSet render = listText . sort . map render . Set.toList
