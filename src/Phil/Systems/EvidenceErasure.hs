{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.EvidenceErasure
  ( EvidenceErasureStageRevision (..)
  , ErasureJustificationKey (..)
  , ErasedRepresentationKey (..)
  , SemanticUseKey (..)
  , SuccessorInvariantRevision (..)
  , NoLaterConsumerRevision (..)
  , RuntimeResidueChangeRevision (..)
  , ErasureCostChangeRevision (..)
  , LaterConsumerBasis (..)
  , LaterSemanticConsumer (..)
  , ErasureJustification (..)
  , EvidenceErasureStageBundle (..)
  , EvidenceErasureVerificationError (..)
  , deriveEvidenceErasureStageRevision
  , makeEvidenceErasureStageBundle
  , verifyEvidenceErasureStageBundle
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Static
  ( SemanticForm (..)
  , canonicalSemanticForm
  )
import Phil.Systems.EvidenceSubjectTransfer
  ( EvidenceTransferStageBundle (..)
  , EvidenceTransferStageRevision (..)
  , EvidenceTransferVerificationError
  , verifyEvidenceTransferStageBundle
  )
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  , SourceFactKey (..)
  )
import Phil.Systems.SubjectCorrespondence
  ( SourceSubjectKey (..)
  , SubjectCorrespondence (..)
  , SubjectStageBundle (..)
  )
import qualified SystemsEvidencePreservationKernel as Kernel

newtype EvidenceErasureStageRevision = EvidenceErasureStageRevision
  { unEvidenceErasureStageRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype ErasureJustificationKey = ErasureJustificationKey
  { unErasureJustificationKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype ErasedRepresentationKey = ErasedRepresentationKey
  { unErasedRepresentationKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype SemanticUseKey = SemanticUseKey
  { unSemanticUseKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype SuccessorInvariantRevision = SuccessorInvariantRevision
  { unSuccessorInvariantRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype NoLaterConsumerRevision = NoLaterConsumerRevision
  { unNoLaterConsumerRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype RuntimeResidueChangeRevision = RuntimeResidueChangeRevision
  { unRuntimeResidueChangeRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype ErasureCostChangeRevision = ErasureCostChangeRevision
  { unErasureCostChangeRevision :: Text
  }
  deriving (Eq, Ord, Show)

-- | A semantic consumer after the claimed erasure either still requires the
-- erased representation (which makes the erasure invalid) or consumes the
-- exact successor invariant/control fact named by the erasure justification.
data LaterConsumerBasis
  = ConsumerNeedsErasedRepresentation
  | ConsumerUsesSuccessorInvariant SuccessorInvariantRevision
  deriving (Eq, Ord, Show)

data LaterSemanticConsumer = LaterSemanticConsumer
  { laterConsumerKey :: SemanticUseKey
  , laterConsumerSubject :: SourceSubjectKey
  , laterConsumerSourceFact :: SourceFactKey
  , laterConsumerBasis :: LaterConsumerBasis
  }
  deriving (Eq, Ord, Show)

-- | SYS-012 makes representation erasure an explicit semantic act.  The source
-- fact is also the exact evidence reference carried by the selected semantic
-- subject in this bounded slice.  Discharge evidence is therefore checked
-- against that exact subject rather than accepted by textual similarity.
data ErasureJustification = ErasureJustification
  { erasureJustificationKey :: ErasureJustificationKey
  , erasureSourceFact :: SourceFactKey
  , erasureSubject :: SourceSubjectKey
  , erasureRepresentation :: ErasedRepresentationKey
  , erasureDischargeEvidenceRefs :: Set Text
  , erasureLastSemanticUse :: SemanticUseKey
  , erasureSuccessorInvariant :: Maybe SuccessorInvariantRevision
  , erasureNoLaterConsumerBasis :: NoLaterConsumerRevision
  , erasureRuntimeResidueChange :: Maybe RuntimeResidueChangeRevision
  , erasureCostChange :: Maybe ErasureCostChangeRevision
  }
  deriving (Eq, Ord, Show)

data EvidenceErasureStageBundle = EvidenceErasureStageBundle
  { evidenceErasureStageBase :: EvidenceTransferStageBundle
  , evidenceErasureStageRevision :: EvidenceErasureStageRevision
  , evidenceErasureStageJustifications :: Map ErasureJustificationKey ErasureJustification
  , evidenceErasureStageLaterConsumers :: Map SemanticUseKey LaterSemanticConsumer
  }
  deriving (Eq, Show)

data EvidenceErasureVerificationError
  = EvidenceErasureBaseError EvidenceTransferVerificationError
  | EvidenceErasureStageRevisionMismatch
      EvidenceErasureStageRevision EvidenceErasureStageRevision
  | ErasureJustificationMapKeyMismatch
      ErasureJustificationKey ErasureJustificationKey
  | ErasureJustificationEmptyKey
  | ErasureUnknownSourceFact ErasureJustificationKey SourceFactKey
  | ErasureUnknownSubject ErasureJustificationKey SourceSubjectKey
  | ErasureSourceFactNotEvidenceForSubject
      ErasureJustificationKey SourceSubjectKey SourceFactKey
  | ErasureDuplicateSourceFact SourceFactKey (Set ErasureJustificationKey)
  | ErasureEmptyRepresentation ErasureJustificationKey
  | ErasureEmptyDischargeEvidence ErasureJustificationKey
  | ErasureDischargeEvidenceNotForSubject
      ErasureJustificationKey SourceSubjectKey Text
  | ErasureEmptyLastSemanticUse ErasureJustificationKey
  | ErasureEmptyNoLaterConsumerBasis ErasureJustificationKey
  | ErasureEmptySuccessorInvariant ErasureJustificationKey
  | ErasureEmptyRuntimeResidueChange ErasureJustificationKey
  | ErasureEmptyCostChange ErasureJustificationKey
  | LaterConsumerMapKeyMismatch SemanticUseKey SemanticUseKey
  | LaterConsumerEmptyKey
  | LaterConsumerUnknownSourceFact SemanticUseKey SourceFactKey
  | LaterConsumerUnknownSubject SemanticUseKey SourceSubjectKey
  | LaterConsumerFactNotEvidenceForSubject
      SemanticUseKey SourceSubjectKey SourceFactKey
  | LaterConsumerWithoutErasureJustification
      SemanticUseKey SourceFactKey SourceSubjectKey
  | LaterConsumerEqualsLastSemanticUse ErasureJustificationKey SemanticUseKey
  | ErasureLiveConsumerStillNeedsRepresentation
      ErasureJustificationKey SemanticUseKey
  | ErasureLiveConsumerMissingSuccessorInvariant
      ErasureJustificationKey SemanticUseKey SuccessorInvariantRevision
  | ErasureLiveConsumerSuccessorMismatch
      ErasureJustificationKey
      SemanticUseKey
      SuccessorInvariantRevision
      SuccessorInvariantRevision
  deriving (Eq, Show)

deriveEvidenceErasureStageRevision
  :: EvidenceErasureStageBundle
  -> EvidenceErasureStageRevision
deriveEvidenceErasureStageRevision bundle = EvidenceErasureStageRevision
  ("phil.phase1.stage.evidence-erasure.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("base_stage", SemanticAtom (baseRevisionText (evidenceErasureStageBase bundle)))
      , ("justifications", SemanticRecord (Map.fromList
          [ (unErasureJustificationKey key, semanticJustification value)
          | (key, value) <- Map.toAscList (evidenceErasureStageJustifications bundle)
          ]))
      , ("later_consumers", SemanticRecord (Map.fromList
          [ (unSemanticUseKey key, semanticConsumer value)
          | (key, value) <- Map.toAscList (evidenceErasureStageLaterConsumers bundle)
          ]))
      ])))

makeEvidenceErasureStageBundle
  :: EvidenceTransferStageBundle
  -> Map ErasureJustificationKey ErasureJustification
  -> Map SemanticUseKey LaterSemanticConsumer
  -> EvidenceErasureStageBundle
makeEvidenceErasureStageBundle base justifications laterConsumers = provisional
  { evidenceErasureStageRevision = deriveEvidenceErasureStageRevision provisional }
  where
    provisional = EvidenceErasureStageBundle
      { evidenceErasureStageBase = base
      , evidenceErasureStageRevision = EvidenceErasureStageRevision "pending"
      , evidenceErasureStageJustifications = justifications
      , evidenceErasureStageLaterConsumers = laterConsumers
      }

verifyEvidenceErasureStageBundle
  :: EvidenceErasureStageBundle
  -> Either EvidenceErasureVerificationError ()
verifyEvidenceErasureStageBundle bundle = do
  mapLeft EvidenceErasureBaseError $
    verifyEvidenceTransferStageBundle (evidenceErasureStageBase bundle)
  requireEqual EvidenceErasureStageRevisionMismatch
    (deriveEvidenceErasureStageRevision bundle)
    (evidenceErasureStageRevision bundle)
  mapM_ (checkJustification bundle)
    (Map.toAscList (evidenceErasureStageJustifications bundle))
  checkUniqueSourceFacts bundle
  mapM_ (checkConsumer bundle)
    (Map.toAscList (evidenceErasureStageLaterConsumers bundle))
  mapM_ (checkConsumerClosure bundle)
    (Map.elems (evidenceErasureStageLaterConsumers bundle))

checkJustification
  :: EvidenceErasureStageBundle
  -> (ErasureJustificationKey, ErasureJustification)
  -> Either EvidenceErasureVerificationError ()
checkJustification bundle (key, justification) = do
  requireEqual ErasureJustificationMapKeyMismatch
    key (erasureJustificationKey justification)
  if Text.null (unErasureJustificationKey key)
    then Left ErasureJustificationEmptyKey
    else Right ()
  let fact = erasureSourceFact justification
      subject = erasureSubject justification
  if Set.member fact (baseSourceFacts bundle)
    then Right ()
    else Left (ErasureUnknownSourceFact key fact)
  correspondence <- maybe
    (Left (ErasureUnknownSubject key subject))
    Right
    (Map.lookup subject (baseCorrespondences bundle))
  let sourceSubjectExact =
        Set.member (unSourceFactKey fact) (subjectCorrespondenceEvidenceRefs correspondence)
  case Kernel.decideEvidenceErasureByFacts
      Kernel.True (toKernelBool sourceSubjectExact) Kernel.True Kernel.True
      Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True of
    Kernel.EvidenceErasureAcceptedDecision -> Right ()
    Kernel.EvidenceErasureSourceSubjectDecision ->
      Left (ErasureSourceFactNotEvidenceForSubject key subject fact)
    _ -> kernelInvariant "erasure-source-subject"
  case erasureRepresentation justification of
    ErasedRepresentationKey value ->
      case Kernel.decideEvidenceErasureByFacts
          Kernel.True Kernel.True Kernel.True (toKernelBool (not (Text.null value)))
          Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True of
        Kernel.EvidenceErasureAcceptedDecision -> Right ()
        Kernel.EvidenceErasureRepresentationDecision ->
          Left (ErasureEmptyRepresentation key)
        _ -> kernelInvariant "erasure-representation"
  let discharge = erasureDischargeEvidenceRefs justification
  if Set.null discharge
    then Left (ErasureEmptyDischargeEvidence key)
    else Right ()
  let dischargeResult = mapM_ (requireDischargeEvidence key subject correspondence)
        (Set.toAscList discharge)
  case Kernel.decideEvidenceErasureByFacts
      Kernel.True Kernel.True (toKernelBool (isRight dischargeResult)) Kernel.True
      Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True of
    Kernel.EvidenceErasureAcceptedDecision -> dischargeResult
    Kernel.EvidenceErasureDischargeSubjectDecision -> dischargeResult
    _ -> kernelInvariant "erasure-discharge-subject"
  case erasureLastSemanticUse justification of
    SemanticUseKey value ->
      case Kernel.decideEvidenceErasureByFacts
          Kernel.True Kernel.True Kernel.True Kernel.True
          (toKernelBool (not (Text.null value))) Kernel.True Kernel.True Kernel.True
          Kernel.True Kernel.True of
        Kernel.EvidenceErasureAcceptedDecision -> Right ()
        Kernel.EvidenceErasureLastUseDecision -> Left (ErasureEmptyLastSemanticUse key)
        _ -> kernelInvariant "erasure-last-use"
  case erasureNoLaterConsumerBasis justification of
    NoLaterConsumerRevision value ->
      case Kernel.decideEvidenceErasureByFacts
          Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True
          (toKernelBool (not (Text.null value))) Kernel.True Kernel.True Kernel.True
          Kernel.True of
        Kernel.EvidenceErasureAcceptedDecision -> Right ()
        Kernel.EvidenceErasureConsumerClosureBasisDecision ->
          Left (ErasureEmptyNoLaterConsumerBasis key)
        _ -> kernelInvariant "erasure-consumer-closure-basis"
  let successorWellFormed = optionalRevisionWellFormed
        unSuccessorInvariantRevision (erasureSuccessorInvariant justification)
  case Kernel.decideEvidenceErasureByFacts
      Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True
      (toKernelBool successorWellFormed) Kernel.True Kernel.True Kernel.True of
    Kernel.EvidenceErasureAcceptedDecision -> Right ()
    Kernel.EvidenceErasureSuccessorRevisionDecision ->
      Left (ErasureEmptySuccessorInvariant key)
    _ -> kernelInvariant "erasure-successor-revision"
  let runtimeWellFormed = optionalRevisionWellFormed
        unRuntimeResidueChangeRevision (erasureRuntimeResidueChange justification)
  case Kernel.decideEvidenceErasureByFacts
      Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True
      Kernel.True (toKernelBool runtimeWellFormed) Kernel.True Kernel.True of
    Kernel.EvidenceErasureAcceptedDecision -> Right ()
    Kernel.EvidenceErasureRuntimeResidueRevisionDecision ->
      Left (ErasureEmptyRuntimeResidueChange key)
    _ -> kernelInvariant "erasure-runtime-residue-revision"
  let costWellFormed = optionalRevisionWellFormed
        unErasureCostChangeRevision (erasureCostChange justification)
  case Kernel.decideEvidenceErasureByFacts
      Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True
      Kernel.True Kernel.True (toKernelBool costWellFormed) Kernel.True of
    Kernel.EvidenceErasureAcceptedDecision -> Right ()
    Kernel.EvidenceErasureCostRevisionDecision -> Left (ErasureEmptyCostChange key)
    _ -> kernelInvariant "erasure-cost-revision"

checkUniqueSourceFacts
  :: EvidenceErasureStageBundle
  -> Either EvidenceErasureVerificationError ()
checkUniqueSourceFacts bundle =
  mapM_ checkGroup (Map.toAscList grouped)
  where
    grouped = Map.fromListWith Set.union
      [ (erasureSourceFact justification, Set.singleton key)
      | (key, justification) <- Map.toAscList (evidenceErasureStageJustifications bundle)
      ]
    checkGroup (fact, keys)
      | Set.size keys <= 1 = Right ()
      | otherwise = Left (ErasureDuplicateSourceFact fact keys)

checkConsumer
  :: EvidenceErasureStageBundle
  -> (SemanticUseKey, LaterSemanticConsumer)
  -> Either EvidenceErasureVerificationError ()
checkConsumer bundle (key, consumer) = do
  requireEqual LaterConsumerMapKeyMismatch key (laterConsumerKey consumer)
  if Text.null (unSemanticUseKey key)
    then Left LaterConsumerEmptyKey
    else Right ()
  let fact = laterConsumerSourceFact consumer
      subject = laterConsumerSubject consumer
  if Set.member fact (baseSourceFacts bundle)
    then Right ()
    else Left (LaterConsumerUnknownSourceFact key fact)
  correspondence <- maybe
    (Left (LaterConsumerUnknownSubject key subject))
    Right
    (Map.lookup subject (baseCorrespondences bundle))
  if Set.member (unSourceFactKey fact) (subjectCorrespondenceEvidenceRefs correspondence)
    then Right ()
    else Left (LaterConsumerFactNotEvidenceForSubject key subject fact)
  let basisResult = case laterConsumerBasis consumer of
        ConsumerNeedsErasedRepresentation -> Right ()
        ConsumerUsesSuccessorInvariant (SuccessorInvariantRevision value)
          | Text.null value -> Left
              (ErasureLiveConsumerMissingSuccessorInvariant
                (ErasureJustificationKey "") key (SuccessorInvariantRevision value))
          | otherwise -> Right ()
  case Kernel.decideEvidenceErasureByFacts
      Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True
      Kernel.True Kernel.True Kernel.True (toKernelBool (isRight basisResult)) of
    Kernel.EvidenceErasureAcceptedDecision -> basisResult
    Kernel.EvidenceErasureLaterConsumersDecision -> basisResult
    _ -> kernelInvariant "erasure-consumer-basis"

checkConsumerClosure
  :: EvidenceErasureStageBundle
  -> LaterSemanticConsumer
  -> Either EvidenceErasureVerificationError ()
checkConsumerClosure bundle consumer =
  case Kernel.decideEvidenceErasureByFacts
      Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True Kernel.True
      Kernel.True Kernel.True Kernel.True (toKernelBool (isRight nativeResult)) of
    Kernel.EvidenceErasureAcceptedDecision -> nativeResult
    Kernel.EvidenceErasureLaterConsumersDecision -> nativeResult
    _ -> kernelInvariant "erasure-later-consumers"
  where
    nativeResult = nativeCheckConsumerClosure bundle consumer

nativeCheckConsumerClosure
  :: EvidenceErasureStageBundle
  -> LaterSemanticConsumer
  -> Either EvidenceErasureVerificationError ()
nativeCheckConsumerClosure bundle consumer = do
  let fact = laterConsumerSourceFact consumer
      subject = laterConsumerSubject consumer
      matching =
        [ justification
        | justification <- Map.elems (evidenceErasureStageJustifications bundle)
        , erasureSourceFact justification == fact
        , erasureSubject justification == subject
        ]
  justification <- case matching of
    [value] -> Right value
    _ -> Left (LaterConsumerWithoutErasureJustification
      (laterConsumerKey consumer) fact subject)
  let erasureKey = erasureJustificationKey justification
      consumerKey = laterConsumerKey consumer
  if consumerKey == erasureLastSemanticUse justification
    then Left (LaterConsumerEqualsLastSemanticUse erasureKey consumerKey)
    else Right ()
  case laterConsumerBasis consumer of
    ConsumerNeedsErasedRepresentation ->
      Left (ErasureLiveConsumerStillNeedsRepresentation erasureKey consumerKey)
    ConsumerUsesSuccessorInvariant actual ->
      case erasureSuccessorInvariant justification of
        Nothing -> Left
          (ErasureLiveConsumerMissingSuccessorInvariant erasureKey consumerKey actual)
        Just expected
          | expected == actual -> Right ()
          | otherwise -> Left
              (ErasureLiveConsumerSuccessorMismatch
                erasureKey consumerKey expected actual)

requireDischargeEvidence
  :: ErasureJustificationKey
  -> SourceSubjectKey
  -> SubjectCorrespondence
  -> Text
  -> Either EvidenceErasureVerificationError ()
requireDischargeEvidence key subject correspondence evidenceRef
  | Set.member evidenceRef (subjectCorrespondenceEvidenceRefs correspondence) = Right ()
  | otherwise = Left (ErasureDischargeEvidenceNotForSubject key subject evidenceRef)

optionalRevisionWellFormed :: (a -> Text) -> Maybe a -> Bool
optionalRevisionWellFormed _ Nothing = True
optionalRevisionWellFormed render (Just value) = not (Text.null (render value))

baseSubjectStage :: EvidenceErasureStageBundle -> SubjectStageBundle
baseSubjectStage = evidenceTransferStageBase . evidenceErasureStageBase

basePhase1Stage :: EvidenceErasureStageBundle -> Phase1StageBundle
basePhase1Stage = subjectStageBase . baseSubjectStage

baseSourceFacts :: EvidenceErasureStageBundle -> Set SourceFactKey
baseSourceFacts = phase1StageSourceFacts . basePhase1Stage

baseCorrespondences
  :: EvidenceErasureStageBundle
  -> Map SourceSubjectKey SubjectCorrespondence
baseCorrespondences = subjectStageCorrespondences . baseSubjectStage

semanticJustification :: ErasureJustification -> SemanticForm
semanticJustification justification = SemanticRecord (Map.fromList
  [ ("key", SemanticAtom
      (unErasureJustificationKey (erasureJustificationKey justification)))
  , ("source_fact", SemanticAtom
      (unSourceFactKey (erasureSourceFact justification)))
  , ("subject", SemanticAtom
      (unSourceSubjectKey (erasureSubject justification)))
  , ("representation", SemanticAtom
      (unErasedRepresentationKey (erasureRepresentation justification)))
  , ("discharge_evidence", SemanticUnordered
      (Set.map SemanticAtom (erasureDischargeEvidenceRefs justification)))
  , ("last_semantic_use", SemanticAtom
      (unSemanticUseKey (erasureLastSemanticUse justification)))
  , ("successor_invariant", SemanticAtom
      (maybe "none" unSuccessorInvariantRevision
        (erasureSuccessorInvariant justification)))
  , ("no_later_consumer_basis", SemanticAtom
      (unNoLaterConsumerRevision (erasureNoLaterConsumerBasis justification)))
  , ("runtime_residue_change", SemanticAtom
      (maybe "none" unRuntimeResidueChangeRevision
        (erasureRuntimeResidueChange justification)))
  , ("cost_change", SemanticAtom
      (maybe "none" unErasureCostChangeRevision (erasureCostChange justification)))
  ])

semanticConsumer :: LaterSemanticConsumer -> SemanticForm
semanticConsumer consumer = SemanticRecord (Map.fromList
  [ ("key", SemanticAtom (unSemanticUseKey (laterConsumerKey consumer)))
  , ("subject", SemanticAtom
      (unSourceSubjectKey (laterConsumerSubject consumer)))
  , ("source_fact", SemanticAtom
      (unSourceFactKey (laterConsumerSourceFact consumer)))
  , ("basis", semanticConsumerBasis (laterConsumerBasis consumer))
  ])

semanticConsumerBasis :: LaterConsumerBasis -> SemanticForm
semanticConsumerBasis basis = case basis of
  ConsumerNeedsErasedRepresentation -> SemanticAtom "erased-representation"
  ConsumerUsesSuccessorInvariant revision -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "successor-invariant")
    , ("revision", SemanticAtom (unSuccessorInvariantRevision revision))
    ])

baseRevisionText :: EvidenceTransferStageBundle -> Text
baseRevisionText = unEvidenceTransferStageRevision . evidenceTransferStageRevision

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

toKernelBool :: Bool -> Kernel.Bool
toKernelBool value = if value then Kernel.True else Kernel.False

isRight :: Either a b -> Bool
isRight value = case value of
  Right _ -> True
  Left _ -> False

kernelInvariant :: String -> Either e a
kernelInvariant label =
  error ("SystemsEvidencePreservationKernel mismatch: " <> label)
