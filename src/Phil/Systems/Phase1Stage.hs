{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.Phase1Stage
  ( SystemsArtifactRevision (..)
  , Phase1StageContractRevision (..)
  , SourceFactKey (..)
  , SystemsMechanismKey (..)
  , Phase1FactDisposition (..)
  , SystemsJustification (..)
  , Phase1StageBundle (..)
  , Phase1StageVerificationError (..)
  , deriveSystemsArtifactRevision
  , derivePhase1StageContractRevision
  , collectSourceFacts
  , collectSystemsMechanisms
  , makePhase1StageBundle
  , verifyPhase1StageBundle
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (Digest (..))
import Phil.Core.Static
  ( InstanceRevision (..)
  , RealizationRevision (..)
  , SemanticForm (..)
  , canonicalSemanticForm
  )
import Phil.Systems.IR

newtype SystemsArtifactRevision = SystemsArtifactRevision
  { unSystemsArtifactRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype Phase1StageContractRevision = Phase1StageContractRevision
  { unPhase1StageContractRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype SourceFactKey = SourceFactKey
  { unSourceFactKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype SystemsMechanismKey = SystemsMechanismKey
  { unSystemsMechanismKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Bounded Phase-1 fact disposition vocabulary for SYS-001.  Later SYS slices
-- may refine the target relation, but a source responsibility may never simply
-- disappear.
data Phase1FactDisposition
  = Phase1FactRealized (Set SystemsMechanismKey)
  | Phase1FactPreserved (Set SystemsMechanismKey)
  | Phase1FactExported Text
  | Phase1FactAssumptionDependent (Set Text) Phase1FactDisposition
  deriving (Eq, Ord, Show)

-- | Reverse accounting for one semantically significant Systems mechanism.
-- A mechanism must be justified by at least one source fact or one exact
-- realization choice.  Merely existing in the target graph is insufficient.
data SystemsJustification = SystemsJustification
  { systemsJustificationSourceFacts :: Set SourceFactKey
  , systemsJustificationRealizationRefs :: Set Text
  , systemsJustificationQualificationRefs :: Set Text
  , systemsJustificationAssumptionRefs :: Set Text
  }
  deriving (Eq, Ord, Show)

-- | Generic StageContract accounting envelope.  It deliberately has no witness
-- tag: framed upload and Steve are ordinary values supplied to the same verifier.
data Phase1StageBundle = Phase1StageBundle
  { phase1StageInstanceRevision :: InstanceRevision
  , phase1StageRealizationRevision :: RealizationRevision
  , phase1StageSystemsArtifact :: SystemsArtifact
  , phase1StageSystemsArtifactRevision :: SystemsArtifactRevision
  , phase1StageContractRevision :: Phase1StageContractRevision
  , phase1StageVerifierProfileRevision :: Text
  , phase1StageSourceFacts :: Set SourceFactKey
  , phase1StageFactDispositions :: Map SourceFactKey Phase1FactDisposition
  , phase1StageSystemsMechanisms :: Set SystemsMechanismKey
  , phase1StageSystemsJustifications :: Map SystemsMechanismKey SystemsJustification
  }
  deriving (Eq, Show)

data Phase1StageVerificationError
  = Phase1SystemsArtifactRevisionMismatch SystemsArtifactRevision SystemsArtifactRevision
  | Phase1StageContractRevisionMismatch Phase1StageContractRevision Phase1StageContractRevision
  | Phase1LegacyTargetDigestMismatch Digest Digest
  | Phase1StageSourceFactSetMismatch (Set SourceFactKey) (Set SourceFactKey)
  | Phase1StageDispositionDomainMismatch (Set SourceFactKey) (Set SourceFactKey)
  | Phase1StageMechanismSetMismatch (Set SystemsMechanismKey) (Set SystemsMechanismKey)
  | Phase1StageJustificationDomainMismatch (Set SystemsMechanismKey) (Set SystemsMechanismKey)
  | Phase1StageDispositionUnknownMechanisms SourceFactKey (Set SystemsMechanismKey)
  | Phase1StageEmptyAssumptionDependency SourceFactKey
  | Phase1StageJustificationUnknownSourceFacts SystemsMechanismKey (Set SourceFactKey)
  | Phase1StageMechanismUnjustified SystemsMechanismKey
  | Phase1StageEmptyVerifierProfile
  deriving (Eq, Show)

deriveSystemsArtifactRevision :: SystemsArtifact -> SystemsArtifactRevision
deriveSystemsArtifactRevision artifact =
  SystemsArtifactRevision (unDigest (systemsArtifactDigest artifact))

derivePhase1StageContractRevision :: Phase1StageBundle -> Phase1StageContractRevision
derivePhase1StageContractRevision bundle =
  Phase1StageContractRevision
    ("phil.phase1.stage.canonical.v1:"
      <> canonicalSemanticForm (SemanticRecord (Map.fromList
        [ ("instance", SemanticAtom (instanceText (phase1StageInstanceRevision bundle)))
        , ("realization", SemanticAtom (realizationText (phase1StageRealizationRevision bundle)))
        , ("systems", SemanticAtom
            (unSystemsArtifactRevision (phase1StageSystemsArtifactRevision bundle)))
        , ("verifier_profile", SemanticAtom (phase1StageVerifierProfileRevision bundle))
        , ("source_facts", semanticSourceFactSet (phase1StageSourceFacts bundle))
        , ("dispositions", SemanticRecord
            (Map.fromList
              [ (unSourceFactKey key, semanticDisposition value)
              | (key, value) <- Map.toAscList (phase1StageFactDispositions bundle)
              ]))
        , ("systems_mechanisms", semanticMechanismSet
            (phase1StageSystemsMechanisms bundle))
        , ("justifications", SemanticRecord
            (Map.fromList
              [ (unSystemsMechanismKey key, semanticJustification value)
              | (key, value) <- Map.toAscList (phase1StageSystemsJustifications bundle)
              ]))
        ])))

collectSourceFacts :: SystemsArtifact -> Set SourceFactKey
collectSourceFacts artifact = Set.fromList
  [ SourceFactKey (factTransferId fact)
  | fact <- stageFacts (systemsArtifactStageContract artifact)
  ]

-- | SYS-001 conservatively treats every logical operation and terminator in the
-- Systems graph as semantically significant.  Later schemas can classify some
-- objects as incidental only at an explicit competence boundary.
collectSystemsMechanisms :: SystemsArtifact -> Set SystemsMechanismKey
collectSystemsMechanisms artifact = Set.fromList
  (concatMap functionMechanisms (Map.toAscList functions))
  where
    functions = systemsProgramFunctions (systemsArtifactProgram artifact)

    functionMechanisms (functionKey, function) = concatMap
      (blockMechanisms functionKey)
      (Map.toAscList (systemsFunctionBlocks function))

    blockMechanisms functionKey (blockKey, blockValue) =
      [ mechanism functionKey blockKey ("op." <> Text.pack (show index) <> "." <> operationKind op)
      | (index, op) <- zip [(0 :: Int) ..] (systemsBlockOps blockValue)
      ]
      <> [mechanism functionKey blockKey ("term." <> terminatorKind (systemsBlockTerminator blockValue))]

    mechanism functionKey blockKey suffix = SystemsMechanismKey
      (functionKey <> ":" <> unBlockId blockKey <> ":" <> suffix)

makePhase1StageBundle
  :: InstanceRevision
  -> RealizationRevision
  -> Text
  -> SystemsArtifact
  -> Map SourceFactKey Phase1FactDisposition
  -> Map SystemsMechanismKey SystemsJustification
  -> Phase1StageBundle
makePhase1StageBundle instanceRevision realizationRevision verifierProfile artifact dispositions justifications =
  provisional
    { phase1StageContractRevision = derivePhase1StageContractRevision provisional }
  where
    provisional = Phase1StageBundle
      { phase1StageInstanceRevision = instanceRevision
      , phase1StageRealizationRevision = realizationRevision
      , phase1StageSystemsArtifact = artifact
      , phase1StageSystemsArtifactRevision = deriveSystemsArtifactRevision artifact
      , phase1StageContractRevision = Phase1StageContractRevision "pending"
      , phase1StageVerifierProfileRevision = verifierProfile
      , phase1StageSourceFacts = collectSourceFacts artifact
      , phase1StageFactDispositions = dispositions
      , phase1StageSystemsMechanisms = collectSystemsMechanisms artifact
      , phase1StageSystemsJustifications = justifications
      }

verifyPhase1StageBundle
  :: Phase1StageBundle
  -> Either Phase1StageVerificationError ()
verifyPhase1StageBundle bundle = do
  let artifact = phase1StageSystemsArtifact bundle
      expectedSystemsRevision = deriveSystemsArtifactRevision artifact
      actualSystemsRevision = phase1StageSystemsArtifactRevision bundle
      expectedStageRevision = derivePhase1StageContractRevision bundle
      actualStageRevision = phase1StageContractRevision bundle
      expectedLegacyTarget = systemsProgramDigest (systemsArtifactProgram artifact)
      actualLegacyTarget = stageTargetArtifactDigest (systemsArtifactStageContract artifact)
      expectedSourceFacts = collectSourceFacts artifact
      actualSourceFacts = phase1StageSourceFacts bundle
      dispositionDomain = Map.keysSet (phase1StageFactDispositions bundle)
      expectedMechanisms = collectSystemsMechanisms artifact
      actualMechanisms = phase1StageSystemsMechanisms bundle
      justificationDomain = Map.keysSet (phase1StageSystemsJustifications bundle)

  if Text.null (phase1StageVerifierProfileRevision bundle)
    then Left Phase1StageEmptyVerifierProfile
    else Right ()
  requireEqual Phase1SystemsArtifactRevisionMismatch expectedSystemsRevision actualSystemsRevision
  requireEqual Phase1StageContractRevisionMismatch expectedStageRevision actualStageRevision
  requireEqual Phase1LegacyTargetDigestMismatch expectedLegacyTarget actualLegacyTarget
  requireEqual Phase1StageSourceFactSetMismatch expectedSourceFacts actualSourceFacts
  requireEqual Phase1StageDispositionDomainMismatch actualSourceFacts dispositionDomain
  requireEqual Phase1StageMechanismSetMismatch expectedMechanisms actualMechanisms
  requireEqual Phase1StageJustificationDomainMismatch actualMechanisms justificationDomain

  mapM_ (checkDisposition actualMechanisms)
    (Map.toAscList (phase1StageFactDispositions bundle))
  mapM_ (checkJustification actualSourceFacts)
    (Map.toAscList (phase1StageSystemsJustifications bundle))

checkDisposition
  :: Set SystemsMechanismKey
  -> (SourceFactKey, Phase1FactDisposition)
  -> Either Phase1StageVerificationError ()
checkDisposition mechanisms (fact, disposition) = go disposition
  where
    go value = case value of
      Phase1FactRealized refs -> requireRefs refs
      Phase1FactPreserved refs -> requireRefs refs
      Phase1FactExported _ -> Right ()
      Phase1FactAssumptionDependent assumptions inner
        | Set.null assumptions -> Left (Phase1StageEmptyAssumptionDependency fact)
        | otherwise -> go inner

    requireRefs refs =
      let unknown = Set.difference refs mechanisms
      in if Set.null unknown
          then Right ()
          else Left (Phase1StageDispositionUnknownMechanisms fact unknown)

checkJustification
  :: Set SourceFactKey
  -> (SystemsMechanismKey, SystemsJustification)
  -> Either Phase1StageVerificationError ()
checkJustification sourceFacts (mechanismKey, justification) = do
  let citedFacts = systemsJustificationSourceFacts justification
      unknown = Set.difference citedFacts sourceFacts
      hasReason = not (Set.null citedFacts)
        || not (Set.null (systemsJustificationRealizationRefs justification))
        || not (Set.null (systemsJustificationQualificationRefs justification))
  if not (Set.null unknown)
    then Left (Phase1StageJustificationUnknownSourceFacts mechanismKey unknown)
    else if not hasReason
      then Left (Phase1StageMechanismUnjustified mechanismKey)
      else Right ()

semanticDisposition :: Phase1FactDisposition -> SemanticForm
semanticDisposition disposition = case disposition of
  Phase1FactRealized refs -> tagged "realized" (semanticMechanismSet refs)
  Phase1FactPreserved refs -> tagged "preserved" (semanticMechanismSet refs)
  Phase1FactExported ref -> tagged "exported" (SemanticAtom ref)
  Phase1FactAssumptionDependent assumptions inner -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "assumption-dependent")
    , ("assumptions", semanticTextSet assumptions)
    , ("inner", semanticDisposition inner)
    ])

semanticJustification :: SystemsJustification -> SemanticForm
semanticJustification justification = SemanticRecord (Map.fromList
  [ ("source_facts", semanticSourceFactSet (systemsJustificationSourceFacts justification))
  , ("realization_refs", semanticTextSet (systemsJustificationRealizationRefs justification))
  , ("qualification_refs", semanticTextSet (systemsJustificationQualificationRefs justification))
  , ("assumptions", semanticTextSet (systemsJustificationAssumptionRefs justification))
  ])

semanticSourceFactSet :: Set SourceFactKey -> SemanticForm
semanticSourceFactSet = SemanticUnordered . Set.map (SemanticAtom . unSourceFactKey)

semanticMechanismSet :: Set SystemsMechanismKey -> SemanticForm
semanticMechanismSet = SemanticUnordered . Set.map (SemanticAtom . unSystemsMechanismKey)

semanticTextSet :: Set Text -> SemanticForm
semanticTextSet = SemanticUnordered . Set.map SemanticAtom

tagged :: Text -> SemanticForm -> SemanticForm
tagged name value = SemanticRecord (Map.fromList
  [ ("kind", SemanticAtom name)
  , ("value", value)
  ])

operationKind :: SystemsOp -> Text
operationKind operation = case operation of
  OpReceiveFrame {} -> "receive-frame"
  OpBorrowView {} -> "borrow-view"
  OpCommitIngress {} -> "commit-ingress"
  OpDestroyPending {} -> "destroy-pending"
  OpReleaseOwner {} -> "release-owner"
  OpCleanupPartial {} -> "cleanup-partial"
  OpRuntimeCall { runtimeCallName = name } -> "runtime-call." <> name
  OpSessionSelect { sessionSelectLabel = label } -> "session-select." <> label
  OpCopy {} -> "copy"
  OpEraseFact {} -> "erase-fact"
  OpDiagnostic { diagnosticName = name } -> "diagnostic." <> name
  OpScalarLiteral {} -> "scalar-literal"
  OpTraceEvent event -> "trace." <> event

terminatorKind :: SystemsTerminator -> Text
terminatorKind terminator = case terminator of
  TermJump {} -> "jump"
  TermBranch {} -> "branch"
  TermRecognize {} -> "recognize"
  TermRuntimeCheck {} -> "runtime-check"
  TermReceiveExact {} -> "receive-exact"
  TermSendExact {} -> "send-exact"
  TermStore {} -> "store"
  TermSessionOffer {} -> "session-offer"
  TermRuntimeChoice { runtimeChoiceName = name } -> "runtime-choice." <> name
  TermReturnScalar {} -> "return-scalar"
  TermEnd reason -> "end." <> reason
  TermFatal reason -> "fatal." <> reason

instanceText :: InstanceRevision -> Text
instanceText (InstanceRevision value) = value

realizationText :: RealizationRevision -> Text
realizationText (RealizationRevision value) = value

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)
