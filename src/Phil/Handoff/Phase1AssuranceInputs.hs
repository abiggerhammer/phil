{-# LANGUAGE OverloadedStrings #-}

module Phil.Handoff.Phase1AssuranceInputs
  ( Phase1AssuranceInputs (..)
  , Phase1AssuranceInputsError (..)
  , phase1AssuranceInputsFormatV1
  , derivePhase1AssuranceInputs
  , renderPhase1AssuranceInputs
  , decodePhase1AssuranceInputs
  , requiredAssuranceDispositions
  ) where

import Control.Monad (foldM)
import qualified Data.ByteString as ByteString
import Data.Char (isDigit)
import Data.List (sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Data.Word (Word8)
import Numeric (readHex, showHex)
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))
import Phil.Verification
  ( ApplicationAssurancePolicy (..)
  , AssurancePolicyRevision (..)
  , VerificationDisposition (..)
  )
import Phil.Verification.ManifestClosure
  ( ManifestClosureSelection (..)
  )

data Phase1AssuranceInputs = Phase1AssuranceInputs
  { phase1AssurancePolicy :: ApplicationAssurancePolicy
  , phase1AssuranceRequiredDispositions :: Set.Set VerificationDisposition
  , phase1AssuranceLedger :: AssuranceLedger
  , phase1AssuranceSelection :: ManifestClosureSelection
  }
  deriving (Eq, Show)

newtype Phase1AssuranceInputsError = Phase1AssuranceInputsError Text
  deriving (Eq, Show)

phase1AssuranceInputsFormatV1 :: Text
phase1AssuranceInputsFormatV1 = "PHIL-PHASE1-ASSURANCE-INPUTS-V1"

derivePhase1AssuranceInputs
  :: ApplicationAssurancePolicy
  -> AssuranceLedger
  -> ManifestClosureSelection
  -> Either Phase1AssuranceInputsError Phase1AssuranceInputs
derivePhase1AssuranceInputs policy ledger selection = do
  evidence <- selectMap "evidence" (ledgerEvidence ledger)
    (manifestClosureEvidence selection)
  assumptions <- selectMap "assumption" (ledgerAssumptions ledger)
    (manifestClosureAssumptions selection)
  exports <- selectMap "export" (ledgerExports ledger)
    (Map.keysSet (manifestClosureExports selection))
  uses <- selectMap "use" (ledgerUses ledger)
    (manifestClosureUses selection)
  mapM_ validateEvidence (Map.elems evidence)
  mapM_ validateAssumption (Map.elems assumptions)
  mapM_ validateExport (Map.elems exports)
  mapM_ validateUse (Map.elems uses)
  validateEvidenceAssumptions evidence assumptions
  validateEvidenceDependencies evidence
  validateUses uses evidence
  let selectedLedger = emptyLedger
        { ledgerEvidence = evidence
        , ledgerAssumptions = assumptions
        , ledgerExports = exports
        , ledgerUses = uses
        }
      required = requiredAssuranceDispositions
        evidence assumptions (manifestClosureExports selection)
      permitted = applicationAssurancePolicyPermittedDispositions policy
  if required `Set.isSubsetOf` permitted
    then Right Phase1AssuranceInputs
      { phase1AssurancePolicy = policy
      , phase1AssuranceRequiredDispositions = required
      , phase1AssuranceLedger = selectedLedger
      , phase1AssuranceSelection = selection
      }
    else Left (failure "required disposition is not permitted by policy")
  where
    selectMap label source keys = fmap Map.fromList $ mapM select
      (Set.toAscList keys)
      where
        select key = case Map.lookup key source of
          Nothing -> Left (failure
            (label <> " selection is missing from ledger: " <> Text.pack (show key)))
          Just value -> Right (key, value)

requiredAssuranceDispositions
  :: Map.Map EvidenceEntryId EvidenceEntry
  -> Map.Map AssumptionId Assumption
  -> Map.Map ExportId VerificationDisposition
  -> Set.Set VerificationDisposition
requiredAssuranceDispositions evidence assumptions exports =
  Set.fromList
    (concatMap evidenceDispositions (Map.elems evidence)
      <> [AssumptionDependent | not (Map.null assumptions)]
      <> Map.elems exports)
  where
    evidenceDispositions entry =
      primaryDisposition (evidenceAssuranceKind entry)
        : [AssumptionDependent | not (null (evidenceAssumptions entry))]

primaryDisposition :: AssuranceKind -> VerificationDisposition
primaryDisposition kind = case kind of
  KernelChecked -> StaticallyDischarged
  ProofAssistantTheorem -> ExternallyDischarged
  CertificateChecked -> ExternallyDischarged
  TranslationValidated -> ExternallyDischarged
  DifferentialTested -> ExternallyDischarged
  PropertyTested -> ExternallyDischarged
  RuntimeEnforced -> RuntimeBound
  Assumed -> AssumptionDependent

renderPhase1AssuranceInputs :: Phase1AssuranceInputs -> Text
renderPhase1AssuranceInputs inputs = Text.unlines $
  [ phase1AssuranceInputsFormatV1
  , row ["policy", hexText (unAssurancePolicyRevision
      (applicationAssurancePolicyRevision policy))]
  ]
  <> [ row ["permit", dispositionToken disposition]
     | disposition <- Set.toAscList
         (applicationAssurancePolicyPermittedDispositions policy)
     ]
  <> [ row ["require", dispositionToken disposition]
     | disposition <- Set.toAscList
         (phase1AssuranceRequiredDispositions inputs)
     ]
  <> concatMap renderEvidence (Map.elems (ledgerEvidence ledger))
  <> concatMap renderAssumption (Map.elems (ledgerAssumptions ledger))
  <> concatMap renderExport
      [ (exportValue, disposition)
      | (exportKey, disposition) <-
          Map.toAscList (manifestClosureExports selection)
      , Just exportValue <- [Map.lookup exportKey (ledgerExports ledger)]
      ]
  <> map renderUse (Map.elems (ledgerUses ledger))
  where
    policy = phase1AssurancePolicy inputs
    ledger = phase1AssuranceLedger inputs
    selection = phase1AssuranceSelection inputs

renderEvidence :: EvidenceEntry -> [Text]
renderEvidence entry =
  [ row
      [ "evidence"
      , hexEvidenceId (evidenceEntryId entry)
      , digestToken (evidenceEntryDigest entry)
      , hexRevisionId (evidenceObligationRevision entry)
      , assuranceKindToken (evidenceAssuranceKind entry)
      , hexText (unEvidenceRole (evidenceRole entry))
      , hexText (evidenceProducer entry)
      , hexText (evidenceChecker entry)
      ]
  ]
  <> maybe [] (\artifact -> [row
      [ "evidence-artifact"
      , hexEvidenceId (evidenceEntryId entry)
      , hexText (unArtifactRef (artifactReference artifact))
      , digestToken (artifactDigest artifact)
      ]]) (evidenceArtifact entry)
  <> [ row ["evidence-input", hexEvidenceId (evidenceEntryId entry), digestToken digest]
     | digest <- sort (evidenceInputDigests entry)
     ]
  <> [ row ["evidence-assumption", hexEvidenceId (evidenceEntryId entry), hexAssumptionId key]
     | key <- sort (evidenceAssumptions entry)
     ]
  <> [ renderDependency (evidenceEntryId entry) dependency
     | dependency <- sort (evidenceDependsOn entry)
     ]
  <> [ row
        [ "evidence-validity"
        , hexEvidenceId (evidenceEntryId entry)
        , hexText key
        , hexText value
        ]
     | (key, value) <- Map.toAscList
         (validityDimensions (evidenceValidityScope entry))
     ]
  <> [ row ["evidence-justify", hexEvidenceId (evidenceEntryId entry), hexText value]
     | value <- sort (evidenceJustifies entry)
     ]
  <> maybe [] (renderRuntime (evidenceEntryId entry))
       (evidenceRuntimeMechanism entry)
  <> [ row ["evidence-residue", hexEvidenceId (evidenceEntryId entry), hexText value]
     | value <- sort (evidenceRuntimeResidue entry)
     ]
  <> [ row ["evidence-cost", hexEvidenceId (evidenceEntryId entry), hexText value]
     | value <- sort (evidenceCostRefs entry)
     ]

renderDependency :: EvidenceEntryId -> EvidenceDependency -> Text
renderDependency entryId dependency = case dependency of
  DependsOnEvidence dependencyId -> row
    [ "evidence-dependency-evidence"
    , hexEvidenceId entryId
    , hexEvidenceId dependencyId
    ]
  DependsOnObligation revision -> row
    [ "evidence-dependency-obligation"
    , hexEvidenceId entryId
    , hexRevisionId revision
    ]

renderRuntime :: EvidenceEntryId -> RuntimeMechanism -> [Text]
renderRuntime entryId runtime =
  [ row
      [ "evidence-runtime"
      , hexEvidenceId entryId
      , hexText (runtimeMechanismName runtime)
      , hexText (runtimeExecutionPoint runtime)
      , hexText (runtimeSuccessEvidenceType runtime)
      , hexText (runtimeFailureContract runtime)
      ]
  ]
  <> maybe [] (\artifact -> [row
      [ "evidence-runtime-artifact"
      , hexEvidenceId entryId
      , hexText (unArtifactRef (artifactReference artifact))
      , digestToken (artifactDigest artifact)
      ]]) (runtimeImplementation runtime)

renderAssumption :: Assumption -> [Text]
renderAssumption assumption =
  [ row
      [ "assumption"
      , hexAssumptionId (assumptionId assumption)
      , digestToken (assumptionDigest assumption)
      , hexText (assumptionStatement assumption)
      , hexText (assumptionScope assumption)
      , hexText (assumptionOwnerBoundary assumption)
      , hexText (assumptionRationale assumption)
      ]
  ]
  <> [ row
        [ "assumption-validity"
        , hexAssumptionId (assumptionId assumption)
        , hexText key
        , hexText value
        ]
     | (key, value) <- Map.toAscList
         (validityDimensions (assumptionValidityScope assumption))
     ]

renderExport :: (ExportEntry, VerificationDisposition) -> [Text]
renderExport (exportValue, disposition) =
  [ row
      [ "export"
      , hexExportId (exportId exportValue)
      , digestToken (exportDigest exportValue)
      , hexRevisionId (exportObligationRevision exportValue)
      , hexText (exportDestinationBoundary exportValue)
      , hexText (unObligationId (exportDerivedObligationId exportValue))
      , dispositionToken disposition
      ]
  ]
  <> [ row
        [ "export-validity"
        , hexExportId (exportId exportValue)
        , hexText key
        , hexText value
        ]
     | (key, value) <- Map.toAscList
         (validityDimensions (exportValidityScope exportValue))
     ]

renderUse :: AssuranceUse -> Text
renderUse useValue = case useValue of
  ErasureUse useId useDigest revision entries -> row
    [ "use-erasure"
    , hexUseId useId
    , digestToken useDigest
    , hexRevisionId revision
    , Text.intercalate "," (map hexEvidenceId (sort entries))
    ]
  RetainedRuntimeUse useId useDigest revision evidenceId costRef -> row
    [ "use-runtime"
    , hexUseId useId
    , digestToken useDigest
    , hexRevisionId revision
    , hexEvidenceId evidenceId
    , hexText costRef
    ]

data DecodeState = DecodeState
  { decodePolicyRevision :: Maybe AssurancePolicyRevision
  , decodePermitted :: Set.Set VerificationDisposition
  , decodeRequired :: Set.Set VerificationDisposition
  , decodeEvidence :: Map.Map EvidenceEntryId EvidenceEntry
  , decodeAssumptions :: Map.Map AssumptionId Assumption
  , decodeExports :: Map.Map ExportId (ExportEntry, VerificationDisposition)
  , decodeUses :: Map.Map AssuranceUseId AssuranceUse
  }

emptyDecodeState :: DecodeState
emptyDecodeState = DecodeState Nothing Set.empty Set.empty Map.empty Map.empty Map.empty Map.empty

decodePhase1AssuranceInputs
  :: Text
  -> Either Phase1AssuranceInputsError Phase1AssuranceInputs
decodePhase1AssuranceInputs input =
  case Text.lines input of
    [] -> Left (failure "empty assurance-input file")
    header : rows
      | Text.strip header /= phase1AssuranceInputsFormatV1 ->
          Left (failure ("unexpected assurance-input header: " <> header))
      | otherwise -> do
          state <- foldM decodeRow emptyDecodeState (zip [2 :: Int ..] rows)
          revision <- maybe
            (Left (failure "missing assurance policy"))
            Right
            (decodePolicyRevision state)
          let policy = ApplicationAssurancePolicy revision (decodePermitted state)
              ledger = emptyLedger
                { ledgerEvidence = decodeEvidence state
                , ledgerAssumptions = decodeAssumptions state
                , ledgerExports = Map.map fst (decodeExports state)
                , ledgerUses = decodeUses state
                }
              selection = ManifestClosureSelection
                { manifestClosureEvidence = Map.keysSet (decodeEvidence state)
                , manifestClosureAssumptions = Map.keysSet (decodeAssumptions state)
                , manifestClosureExports = Map.map snd (decodeExports state)
                , manifestClosureUses = Map.keysSet (decodeUses state)
                }
          derived <- derivePhase1AssuranceInputs policy ledger selection
          if phase1AssuranceRequiredDispositions derived == decodeRequired state
            then Right derived
            else Left (failure "persisted required dispositions do not match selected assurance inputs")

decodeRow :: DecodeState -> (Int, Text) -> Either Phase1AssuranceInputsError DecodeState
decodeRow state (lineNumber, rawLine)
  | Text.null (Text.strip rawLine) = Right state
  | "#" `Text.isPrefixOf` Text.strip rawLine = Right state
  | otherwise =
      case Text.splitOn "\t" rawLine of
        ["policy", rawRevision] -> do
          revision <- AssurancePolicyRevision <$> decodeHex lineNumber rawRevision
          case decodePolicyRevision state of
            Nothing -> Right state { decodePolicyRevision = Just revision }
            Just _ -> Left (lineFailure lineNumber "duplicate policy row")
        ["permit", rawDisposition] -> do
          disposition <- parseDisposition lineNumber rawDisposition
          if Set.member disposition (decodePermitted state)
            then Left (lineFailure lineNumber "duplicate permitted disposition")
            else Right state
              { decodePermitted = Set.insert disposition (decodePermitted state) }
        ["require", rawDisposition] -> do
          disposition <- parseDisposition lineNumber rawDisposition
          if Set.member disposition (decodeRequired state)
            then Left (lineFailure lineNumber "duplicate required disposition")
            else Right state
              { decodeRequired = Set.insert disposition (decodeRequired state) }
        ["evidence", rawId, rawDigest, rawRevision, rawKind, rawRole, rawProducer, rawChecker] -> do
          entryId <- EvidenceEntryId <$> decodeHex lineNumber rawId
          digest <- parseDigest lineNumber rawDigest
          revision <- RevisionId <$> decodeHex lineNumber rawRevision
          kind <- parseAssuranceKind lineNumber rawKind
          roleValue <- EvidenceRole <$> decodeHex lineNumber rawRole
          producer <- decodeHex lineNumber rawProducer
          checker <- decodeHex lineNumber rawChecker
          if Map.member entryId (decodeEvidence state)
            then Left (lineFailure lineNumber "duplicate evidence entry")
            else Right state
              { decodeEvidence = Map.insert entryId
                  EvidenceEntry
                    { evidenceEntryId = entryId
                    , evidenceEntryDigest = digest
                    , evidenceObligationRevision = revision
                    , evidenceAssuranceKind = kind
                    , evidenceRole = roleValue
                    , evidenceProducer = producer
                    , evidenceChecker = checker
                    , evidenceArtifact = Nothing
                    , evidenceInputDigests = []
                    , evidenceAssumptions = []
                    , evidenceDependsOn = []
                    , evidenceValidityScope = ValidityScope Map.empty
                    , evidenceResult = EvidenceAccepted
                    , evidenceJustifies = []
                    , evidenceRuntimeMechanism = Nothing
                    , evidenceRuntimeResidue = []
                    , evidenceCostRefs = []
                    }
                  (decodeEvidence state)
              }
        ["evidence-artifact", rawId, rawRef, rawDigest] -> do
          artifact <- ArtifactIdentity
            <$> (ArtifactRef <$> decodeHex lineNumber rawRef)
            <*> parseDigest lineNumber rawDigest
          updateEvidence lineNumber rawId state $ \entry ->
            if evidenceArtifact entry == Nothing
              then Right entry { evidenceArtifact = Just artifact }
              else Left (lineFailure lineNumber "duplicate evidence artifact")
        ["evidence-input", rawId, rawDigest] -> do
          digest <- parseDigest lineNumber rawDigest
          updateEvidence lineNumber rawId state $ \entry ->
            Right entry { evidenceInputDigests = digest : evidenceInputDigests entry }
        ["evidence-assumption", rawId, rawAssumption] -> do
          assumptionKey <- AssumptionId <$> decodeHex lineNumber rawAssumption
          updateEvidence lineNumber rawId state $ \entry ->
            Right entry { evidenceAssumptions = assumptionKey : evidenceAssumptions entry }
        ["evidence-dependency-evidence", rawId, rawDependency] -> do
          dependency <- DependsOnEvidence . EvidenceEntryId <$> decodeHex lineNumber rawDependency
          updateEvidence lineNumber rawId state $ \entry ->
            Right entry { evidenceDependsOn = dependency : evidenceDependsOn entry }
        ["evidence-dependency-obligation", rawId, rawDependency] -> do
          dependency <- DependsOnObligation . RevisionId <$> decodeHex lineNumber rawDependency
          updateEvidence lineNumber rawId state $ \entry ->
            Right entry { evidenceDependsOn = dependency : evidenceDependsOn entry }
        ["evidence-validity", rawId, rawKey, rawValue] -> do
          key <- decodeHex lineNumber rawKey
          value <- decodeHex lineNumber rawValue
          updateEvidence lineNumber rawId state $ \entry ->
            insertEvidenceValidity lineNumber key value entry
        ["evidence-justify", rawId, rawValue] -> do
          value <- decodeHex lineNumber rawValue
          updateEvidence lineNumber rawId state $ \entry ->
            Right entry { evidenceJustifies = value : evidenceJustifies entry }
        ["evidence-runtime", rawId, rawName, rawPoint, rawSuccess, rawFailure] -> do
          runtime <- RuntimeMechanism
            <$> decodeHex lineNumber rawName
            <*> decodeHex lineNumber rawPoint
            <*> decodeHex lineNumber rawSuccess
            <*> decodeHex lineNumber rawFailure
            <*> pure Nothing
          updateEvidence lineNumber rawId state $ \entry ->
            if evidenceRuntimeMechanism entry == Nothing
              then Right entry { evidenceRuntimeMechanism = Just runtime }
              else Left (lineFailure lineNumber "duplicate runtime mechanism")
        ["evidence-runtime-artifact", rawId, rawRef, rawDigest] -> do
          artifact <- ArtifactIdentity
            <$> (ArtifactRef <$> decodeHex lineNumber rawRef)
            <*> parseDigest lineNumber rawDigest
          updateEvidence lineNumber rawId state $ \entry ->
            case evidenceRuntimeMechanism entry of
              Nothing -> Left (lineFailure lineNumber "runtime artifact precedes runtime mechanism")
              Just runtime
                | runtimeImplementation runtime == Nothing ->
                    Right entry
                      { evidenceRuntimeMechanism = Just runtime
                          { runtimeImplementation = Just artifact }
                      }
                | otherwise ->
                    Left (lineFailure lineNumber "duplicate runtime artifact")
        ["evidence-residue", rawId, rawValue] -> do
          value <- decodeHex lineNumber rawValue
          updateEvidence lineNumber rawId state $ \entry ->
            Right entry { evidenceRuntimeResidue = value : evidenceRuntimeResidue entry }
        ["evidence-cost", rawId, rawValue] -> do
          value <- decodeHex lineNumber rawValue
          updateEvidence lineNumber rawId state $ \entry ->
            Right entry { evidenceCostRefs = value : evidenceCostRefs entry }
        ["assumption", rawId, rawDigest, rawStatement, rawScope, rawOwner, rawRationale] -> do
          assumptionKey <- AssumptionId <$> decodeHex lineNumber rawId
          digest <- parseDigest lineNumber rawDigest
          statement <- decodeHex lineNumber rawStatement
          scope <- decodeHex lineNumber rawScope
          owner <- decodeHex lineNumber rawOwner
          rationale <- decodeHex lineNumber rawRationale
          if Map.member assumptionKey (decodeAssumptions state)
            then Left (lineFailure lineNumber "duplicate assumption")
            else Right state
              { decodeAssumptions = Map.insert assumptionKey
                  Assumption
                    { assumptionId = assumptionKey
                    , assumptionDigest = digest
                    , assumptionStatement = statement
                    , assumptionScope = scope
                    , assumptionOwnerBoundary = owner
                    , assumptionRationale = rationale
                    , assumptionValidityScope = ValidityScope Map.empty
                    }
                  (decodeAssumptions state)
              }
        ["assumption-validity", rawId, rawKey, rawValue] -> do
          assumptionKey <- AssumptionId <$> decodeHex lineNumber rawId
          key <- decodeHex lineNumber rawKey
          value <- decodeHex lineNumber rawValue
          assumption <- lookupMap lineNumber "assumption" assumptionKey
            (decodeAssumptions state)
          let ValidityScope dimensions = assumptionValidityScope assumption
          if Map.member key dimensions
            then Left (lineFailure lineNumber "duplicate assumption validity dimension")
            else Right state
              { decodeAssumptions = Map.insert assumptionKey
                  assumption
                    { assumptionValidityScope =
                        ValidityScope (Map.insert key value dimensions)
                    }
                  (decodeAssumptions state)
              }
        ["export", rawId, rawDigest, rawRevision, rawDestination, rawDerived, rawDisposition] -> do
          exportKey <- ExportId <$> decodeHex lineNumber rawId
          digest <- parseDigest lineNumber rawDigest
          revision <- RevisionId <$> decodeHex lineNumber rawRevision
          destination <- decodeHex lineNumber rawDestination
          derived <- ObligationId <$> decodeHex lineNumber rawDerived
          disposition <- parseDisposition lineNumber rawDisposition
          if disposition `notElem` [Exported, DeploymentExported]
            then Left (lineFailure lineNumber "invalid export disposition")
            else if Map.member exportKey (decodeExports state)
              then Left (lineFailure lineNumber "duplicate export")
              else Right state
                { decodeExports = Map.insert exportKey
                    ( ExportEntry
                        { exportId = exportKey
                        , exportDigest = digest
                        , exportObligationRevision = revision
                        , exportDestinationBoundary = destination
                        , exportDerivedObligationId = derived
                        , exportValidityScope = ValidityScope Map.empty
                        }
                    , disposition
                    )
                    (decodeExports state)
                }
        ["export-validity", rawId, rawKey, rawValue] -> do
          exportKey <- ExportId <$> decodeHex lineNumber rawId
          key <- decodeHex lineNumber rawKey
          value <- decodeHex lineNumber rawValue
          (exportValue, disposition) <- lookupMap lineNumber "export" exportKey
            (decodeExports state)
          let ValidityScope dimensions = exportValidityScope exportValue
          if Map.member key dimensions
            then Left (lineFailure lineNumber "duplicate export validity dimension")
            else Right state
              { decodeExports = Map.insert exportKey
                  ( exportValue
                      { exportValidityScope =
                          ValidityScope (Map.insert key value dimensions)
                      }
                  , disposition
                  )
                  (decodeExports state)
              }
        ["use-erasure", rawId, rawDigest, rawRevision, rawEntries] -> do
          useId <- AssuranceUseId <$> decodeHex lineNumber rawId
          digest <- parseDigest lineNumber rawDigest
          revision <- RevisionId <$> decodeHex lineNumber rawRevision
          entries <- mapM (fmap EvidenceEntryId . decodeHex lineNumber)
            (splitList rawEntries)
          insertUse lineNumber useId
            (ErasureUse useId digest revision entries) state
        ["use-runtime", rawId, rawDigest, rawRevision, rawEvidence, rawCost] -> do
          useId <- AssuranceUseId <$> decodeHex lineNumber rawId
          digest <- parseDigest lineNumber rawDigest
          revision <- RevisionId <$> decodeHex lineNumber rawRevision
          evidenceId <- EvidenceEntryId <$> decodeHex lineNumber rawEvidence
          costRef <- decodeHex lineNumber rawCost
          insertUse lineNumber useId
            (RetainedRuntimeUse useId digest revision evidenceId costRef) state
        _ -> Left (lineFailure lineNumber ("malformed row: " <> rawLine))

updateEvidence
  :: Int
  -> Text
  -> DecodeState
  -> (EvidenceEntry -> Either Phase1AssuranceInputsError EvidenceEntry)
  -> Either Phase1AssuranceInputsError DecodeState
updateEvidence lineNumber rawId state update = do
  entryId <- EvidenceEntryId <$> decodeHex lineNumber rawId
  entry <- lookupMap lineNumber "evidence" entryId (decodeEvidence state)
  updated <- update entry
  Right state
    { decodeEvidence = Map.insert entryId updated (decodeEvidence state) }

insertEvidenceValidity
  :: Int -> Text -> Text -> EvidenceEntry
  -> Either Phase1AssuranceInputsError EvidenceEntry
insertEvidenceValidity lineNumber key value entry =
  let ValidityScope dimensions = evidenceValidityScope entry
  in if Map.member key dimensions
      then Left (lineFailure lineNumber "duplicate evidence validity dimension")
      else Right entry
        { evidenceValidityScope = ValidityScope (Map.insert key value dimensions) }

insertUse
  :: Int -> AssuranceUseId -> AssuranceUse -> DecodeState
  -> Either Phase1AssuranceInputsError DecodeState
insertUse lineNumber useId useValue state
  | Map.member useId (decodeUses state) =
      Left (lineFailure lineNumber "duplicate assurance use")
  | otherwise = Right state
      { decodeUses = Map.insert useId useValue (decodeUses state) }

validateEvidence :: EvidenceEntry -> Either Phase1AssuranceInputsError ()
validateEvidence entry
  | evidenceResult entry /= EvidenceAccepted =
      Left (failure "selected evidence is not accepted")
  | deriveEvidenceEntryDigest normalized /= evidenceEntryDigest entry =
      Left (failure
        ("evidence digest mismatch: " <> unEvidenceEntryId (evidenceEntryId entry)))
  | otherwise = Right ()
  where
    normalized = entry
      { evidenceInputDigests = sort (evidenceInputDigests entry)
      , evidenceAssumptions = sort (evidenceAssumptions entry)
      , evidenceDependsOn = sort (evidenceDependsOn entry)
      , evidenceJustifies = sort (evidenceJustifies entry)
      , evidenceRuntimeResidue = sort (evidenceRuntimeResidue entry)
      , evidenceCostRefs = sort (evidenceCostRefs entry)
      }

validateAssumption :: Assumption -> Either Phase1AssuranceInputsError ()
validateAssumption value
  | deriveAssumptionDigest value == assumptionDigest value = Right ()
  | otherwise = Left (failure
      ("assumption digest mismatch: " <> unAssumptionId (assumptionId value)))

validateExport :: ExportEntry -> Either Phase1AssuranceInputsError ()
validateExport value
  | deriveExportDigest value == exportDigest value = Right ()
  | otherwise = Left (failure
      ("export digest mismatch: " <> unExportId (exportId value)))

validateUse :: AssuranceUse -> Either Phase1AssuranceInputsError ()
validateUse value
  | deriveAssuranceUseDigest value == assuranceUseDigest value = Right ()
  | otherwise = Left (failure
      ("assurance-use digest mismatch: " <> unAssuranceUseId (assuranceUseId value)))

validateEvidenceAssumptions
  :: Map.Map EvidenceEntryId EvidenceEntry
  -> Map.Map AssumptionId Assumption
  -> Either Phase1AssuranceInputsError ()
validateEvidenceAssumptions evidence assumptions =
  mapM_ checkEntry (Map.elems evidence)
  where
    known = Map.keysSet assumptions
    checkEntry entry =
      case Set.lookupMin
          (Set.fromList (evidenceAssumptions entry) `Set.difference` known) of
        Nothing -> Right ()
        Just missing -> Left (failure
          ("evidence references missing selected assumption: "
            <> unAssumptionId missing))

validateEvidenceDependencies
  :: Map.Map EvidenceEntryId EvidenceEntry
  -> Either Phase1AssuranceInputsError ()
validateEvidenceDependencies evidence =
  mapM_ checkEntry (Map.elems evidence)
  where
    known = Map.keysSet evidence
    checkEntry entry = mapM_ checkDependency (evidenceDependsOn entry)
    checkDependency dependency = case dependency of
      DependsOnEvidence key
        | Set.member key known -> Right ()
        | otherwise -> Left (failure
            ("evidence dependency is not selected: " <> unEvidenceEntryId key))
      DependsOnObligation _ -> Right ()

validateUses
  :: Map.Map AssuranceUseId AssuranceUse
  -> Map.Map EvidenceEntryId EvidenceEntry
  -> Either Phase1AssuranceInputsError ()
validateUses uses evidence = mapM_ checkUse (Map.elems uses)
  where
    known = Map.keysSet evidence
    require key
      | Set.member key known = Right ()
      | otherwise = Left (failure
          ("assurance use references unselected evidence: " <> unEvidenceEntryId key))
    checkUse useValue = case useValue of
      ErasureUse _ _ _ entries -> mapM_ require entries
      RetainedRuntimeUse _ _ _ entry _ -> require entry

row :: [Text] -> Text
row = Text.intercalate "\t"

hexText :: Text -> Text
hexText = Text.concatMap hexByte . TextEncoding.decodeLatin1 . TextEncoding.encodeUtf8
  where
    hexByte character =
      let value = fromIntegral (fromEnum character) :: Word8
      in Text.pack (case showHex value "" of
          [digit] -> ['0', digit]
          digits -> digits)

decodeHex :: Int -> Text -> Either Phase1AssuranceInputsError Text
decodeHex lineNumber raw
  | odd (Text.length raw) = Left (lineFailure lineNumber "odd-length hex text")
  | Text.any (not . lowerHex) raw = Left (lineFailure lineNumber "invalid hex text")
  | otherwise =
      case TextEncoding.decodeUtf8' (ByteString.pack bytes) of
        Left _ -> Left (lineFailure lineNumber "hex text is not valid UTF-8")
        Right value -> Right value
  where
    chunks [] = []
    chunks (a:b:rest) = [a,b] : chunks rest
    chunks _ = []
    bytes =
      [ fromIntegral value
      | pair <- chunks (Text.unpack raw)
      , let parsed = readHex pair
      , (value, "") <- take 1 parsed
      ]
    lowerHex character =
      isDigit character || (character >= 'a' && character <= 'f')

digestToken :: Digest -> Text
digestToken (Digest value) = "sha256:" <> value

parseDigest :: Int -> Text -> Either Phase1AssuranceInputsError Digest
parseDigest lineNumber raw =
  case Text.stripPrefix "sha256:" raw of
    Just value
      | Text.length value == 64
      , Text.all lowerHex value -> Right (Digest value)
    _ -> Left (lineFailure lineNumber "malformed SHA-256 digest")
  where
    lowerHex character =
      isDigit character || (character >= 'a' && character <= 'f')

hexEvidenceId :: EvidenceEntryId -> Text
hexEvidenceId = hexText . unEvidenceEntryId

hexAssumptionId :: AssumptionId -> Text
hexAssumptionId = hexText . unAssumptionId

hexExportId :: ExportId -> Text
hexExportId = hexText . unExportId

hexUseId :: AssuranceUseId -> Text
hexUseId = hexText . unAssuranceUseId

hexRevisionId :: RevisionId -> Text
hexRevisionId = hexText . unRevisionId

splitList :: Text -> [Text]
splitList raw
  | Text.null raw = []
  | otherwise = Text.splitOn "," raw

assuranceKindToken :: AssuranceKind -> Text
assuranceKindToken kind = case kind of
  KernelChecked -> "kernel"
  ProofAssistantTheorem -> "proof-assistant"
  CertificateChecked -> "certificate"
  TranslationValidated -> "translation"
  DifferentialTested -> "differential"
  PropertyTested -> "property"
  RuntimeEnforced -> "runtime"
  Assumed -> "assumed"

parseAssuranceKind :: Int -> Text -> Either Phase1AssuranceInputsError AssuranceKind
parseAssuranceKind lineNumber raw = case raw of
  "kernel" -> Right KernelChecked
  "proof-assistant" -> Right ProofAssistantTheorem
  "certificate" -> Right CertificateChecked
  "translation" -> Right TranslationValidated
  "differential" -> Right DifferentialTested
  "property" -> Right PropertyTested
  "runtime" -> Right RuntimeEnforced
  "assumed" -> Right Assumed
  _ -> Left (lineFailure lineNumber ("unknown assurance kind: " <> raw))

dispositionToken :: VerificationDisposition -> Text
dispositionToken disposition = case disposition of
  StaticallyDischarged -> "static"
  RuntimeBound -> "runtime"
  ExternallyDischarged -> "external"
  AssumptionDependent -> "assumption"
  Exported -> "exported"
  DeploymentExported -> "deployment-exported"
  Unresolved -> "unresolved"

parseDisposition :: Int -> Text -> Either Phase1AssuranceInputsError VerificationDisposition
parseDisposition lineNumber raw = case raw of
  "static" -> Right StaticallyDischarged
  "runtime" -> Right RuntimeBound
  "external" -> Right ExternallyDischarged
  "assumption" -> Right AssumptionDependent
  "exported" -> Right Exported
  "deployment-exported" -> Right DeploymentExported
  "unresolved" -> Right Unresolved
  _ -> Left (lineFailure lineNumber ("unknown verification disposition: " <> raw))

lookupMap
  :: (Ord key, Show key)
  => Int -> Text -> key -> Map.Map key value
  -> Either Phase1AssuranceInputsError value
lookupMap lineNumber label key values =
  maybe
    (Left (lineFailure lineNumber
      (label <> " row references missing identity: " <> Text.pack (show key))))
    Right
    (Map.lookup key values)

failure :: Text -> Phase1AssuranceInputsError
failure = Phase1AssuranceInputsError

lineFailure :: Int -> Text -> Phase1AssuranceInputsError
lineFailure lineNumber detail =
  failure ("line " <> Text.pack (show lineNumber) <> ": " <> detail)
