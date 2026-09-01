{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.EvidenceSubjectTransfer
  ( EvidenceTransferStageRevision (..)
  , SubjectTransferRelationKey (..)
  , CopyRelationRevision (..)
  , ByteEqualityRevision (..)
  , EvidenceTransferLawRevision (..)
  , SubjectTransferBasis (..)
  , SubjectTransferRelation (..)
  , EvidenceRebindingKey (..)
  , EvidenceRebindingClaim (..)
  , EvidenceTransferStageBundle (..)
  , EvidenceTransferVerificationError (..)
  , deriveEvidenceTransferStageRevision
  , makeEvidenceTransferStageBundle
  , verifyEvidenceTransferStageBundle
  ) where

import qualified BoundarySubjectKernel as Kernel
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
import Phil.Systems.SubjectCorrespondence
  ( SourceSubjectKey (..)
  , SubjectCorrespondence (..)
  , SubjectStageBundle (..)
  , SubjectStageRevision (..)
  , SubjectStageVerificationError
  , SubjectValidityScopeRevision (..)
  , verifySubjectStageBundle
  )

newtype EvidenceTransferStageRevision = EvidenceTransferStageRevision
  { unEvidenceTransferStageRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype SubjectTransferRelationKey = SubjectTransferRelationKey
  { unSubjectTransferRelationKey :: Text
  }
  deriving (Eq, Ord, Show)

newtype CopyRelationRevision = CopyRelationRevision
  { unCopyRelationRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype ByteEqualityRevision = ByteEqualityRevision
  { unByteEqualityRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype EvidenceTransferLawRevision = EvidenceTransferLawRevision
  { unEvidenceTransferLawRevision :: Text
  }
  deriving (Eq, Ord, Show)

-- | Runtime coincidence is represented only so the verifier can reject the
-- exact invalid inference mechanically. A checked transfer binds the concrete
-- copy relation, exact byte-equality relation, and the proposition-specific
-- law that says which evidence may move to the new stable subject.
data SubjectTransferBasis
  = CheckedSubjectCopy
      CopyRelationRevision
      ByteEqualityRevision
      EvidenceTransferLawRevision
  | RuntimeSubjectCoincidence Text
  deriving (Eq, Ord, Show)

data SubjectTransferRelation = SubjectTransferRelation
  { subjectTransferRelationKey :: SubjectTransferRelationKey
  , subjectTransferSource :: SourceSubjectKey
  , subjectTransferTarget :: SourceSubjectKey
  , subjectTransferBasis :: SubjectTransferBasis
  , subjectTransferAllowedEvidence :: Set Text
  , subjectTransferValidityScope :: SubjectValidityScopeRevision
  }
  deriving (Eq, Ord, Show)

newtype EvidenceRebindingKey = EvidenceRebindingKey
  { unEvidenceRebindingKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Rebinding is an explicit semantic act. A claim with no relation is not a
-- deferred proof obligation: it is the SYS-011 invalid case and is rejected.
data EvidenceRebindingClaim = EvidenceRebindingClaim
  { evidenceRebindingKey :: EvidenceRebindingKey
  , evidenceRebindingSource :: SourceSubjectKey
  , evidenceRebindingTarget :: SourceSubjectKey
  , evidenceRebindingEvidenceRefs :: Set Text
  , evidenceRebindingRelation :: Maybe SubjectTransferRelationKey
  }
  deriving (Eq, Ord, Show)

data EvidenceTransferStageBundle = EvidenceTransferStageBundle
  { evidenceTransferStageBase :: SubjectStageBundle
  , evidenceTransferStageRevision :: EvidenceTransferStageRevision
  , evidenceTransferStageRelations :: Map SubjectTransferRelationKey SubjectTransferRelation
  , evidenceTransferStageRebindings :: Map EvidenceRebindingKey EvidenceRebindingClaim
  }
  deriving (Eq, Show)

data EvidenceTransferVerificationError
  = EvidenceTransferBaseError SubjectStageVerificationError
  | EvidenceTransferStageRevisionMismatch
      EvidenceTransferStageRevision EvidenceTransferStageRevision
  | SubjectTransferMapKeyMismatch
      SubjectTransferRelationKey SubjectTransferRelationKey
  | SubjectTransferSourceEqualsTarget
      SubjectTransferRelationKey SourceSubjectKey
  | SubjectTransferUnknownSource
      SubjectTransferRelationKey SourceSubjectKey
  | SubjectTransferUnknownTarget
      SubjectTransferRelationKey SourceSubjectKey
  | SubjectTransferEmptyAllowedEvidence SubjectTransferRelationKey
  | SubjectTransferEmptyCopyRevision SubjectTransferRelationKey
  | SubjectTransferEmptyByteEqualityRevision SubjectTransferRelationKey
  | SubjectTransferEmptyLawRevision SubjectTransferRelationKey
  | SubjectTransferEmptyValidityScope SubjectTransferRelationKey
  | SubjectTransferRuntimeCoincidenceRejected SubjectTransferRelationKey Text
  | EvidenceRebindingMapKeyMismatch EvidenceRebindingKey EvidenceRebindingKey
  | EvidenceRebindingSourceEqualsTarget EvidenceRebindingKey SourceSubjectKey
  | EvidenceRebindingUnknownSource EvidenceRebindingKey SourceSubjectKey
  | EvidenceRebindingUnknownTarget EvidenceRebindingKey SourceSubjectKey
  | EvidenceRebindingEmptyEvidenceSet EvidenceRebindingKey
  | EvidenceRebindingSourceEvidenceMissing EvidenceRebindingKey Text
  | EvidenceRebindingMissingRelation EvidenceRebindingKey
  | EvidenceRebindingUnknownRelation
      EvidenceRebindingKey SubjectTransferRelationKey
  | EvidenceRebindingRelationEndpointMismatch
      EvidenceRebindingKey
      SubjectTransferRelationKey
      SourceSubjectKey
      SourceSubjectKey
  | EvidenceRebindingEvidenceNotTransferable
      EvidenceRebindingKey SubjectTransferRelationKey Text
  deriving (Eq, Show)

deriveEvidenceTransferStageRevision
  :: EvidenceTransferStageBundle
  -> EvidenceTransferStageRevision
deriveEvidenceTransferStageRevision bundle = EvidenceTransferStageRevision
  ("phil.phase1.stage.evidence-subject-transfer.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("base_stage", SemanticAtom (baseRevisionText (evidenceTransferStageBase bundle)))
      , ("relations", SemanticRecord (Map.fromList
          [ (unSubjectTransferRelationKey key, semanticRelation relation)
          | (key, relation) <- Map.toAscList (evidenceTransferStageRelations bundle)
          ]))
      , ("rebindings", SemanticRecord (Map.fromList
          [ (unEvidenceRebindingKey key, semanticRebinding claim)
          | (key, claim) <- Map.toAscList (evidenceTransferStageRebindings bundle)
          ]))
      ])))

makeEvidenceTransferStageBundle
  :: SubjectStageBundle
  -> Map SubjectTransferRelationKey SubjectTransferRelation
  -> Map EvidenceRebindingKey EvidenceRebindingClaim
  -> EvidenceTransferStageBundle
makeEvidenceTransferStageBundle base relations rebindings = provisional
  { evidenceTransferStageRevision = deriveEvidenceTransferStageRevision provisional }
  where
    provisional = EvidenceTransferStageBundle
      { evidenceTransferStageBase = base
      , evidenceTransferStageRevision = EvidenceTransferStageRevision "pending"
      , evidenceTransferStageRelations = relations
      , evidenceTransferStageRebindings = rebindings
      }

verifyEvidenceTransferStageBundle
  :: EvidenceTransferStageBundle
  -> Either EvidenceTransferVerificationError ()
verifyEvidenceTransferStageBundle bundle = do
  mapLeft EvidenceTransferBaseError $
    verifySubjectStageBundle (evidenceTransferStageBase bundle)
  requireEqual EvidenceTransferStageRevisionMismatch
    (deriveEvidenceTransferStageRevision bundle)
    (evidenceTransferStageRevision bundle)
  mapM_ (checkRelation bundle)
    (Map.toAscList (evidenceTransferStageRelations bundle))
  mapM_ (checkRebinding bundle)
    (Map.toAscList (evidenceTransferStageRebindings bundle))

checkRelation
  :: EvidenceTransferStageBundle
  -> (SubjectTransferRelationKey, SubjectTransferRelation)
  -> Either EvidenceTransferVerificationError ()
checkRelation bundle (key, relation) = do
  requireEqual SubjectTransferMapKeyMismatch
    key (subjectTransferRelationKey relation)
  let source = subjectTransferSource relation
      target = subjectTransferTarget relation
      correspondences = subjectStageCorrespondences (evidenceTransferStageBase bundle)
  if source == target
    then Left (SubjectTransferSourceEqualsTarget key source)
    else Right ()
  if Map.member source correspondences
    then Right ()
    else Left (SubjectTransferUnknownSource key source)
  if Map.member target correspondences
    then Right ()
    else Left (SubjectTransferUnknownTarget key target)
  if Set.null (subjectTransferAllowedEvidence relation)
    then Left (SubjectTransferEmptyAllowedEvidence key)
    else Right ()
  checkRelationAdmissionPreflight key relation

-- | Relation preflight uses the certified decision for every fact already
-- available at relation-validation time. The proposition-specific evidence
-- gate is neutralized here and checked with the concrete evidence reference in
-- 'requireTransferableEvidence'.
checkRelationAdmissionPreflight
  :: SubjectTransferRelationKey
  -> SubjectTransferRelation
  -> Either EvidenceTransferVerificationError ()
checkRelationAdmissionPreflight key relation =
  case subjectTransferBasis relation of
    CheckedSubjectCopy
        (CopyRelationRevision copyRevision)
        (ByteEqualityRevision equalityRevision)
        (EvidenceTransferLawRevision lawRevision) ->
      mapRelationDecision key relation Nothing $
        Kernel.decideBoundarySubjectTransferByFacts
          True
          True
          (not (Text.null copyRevision))
          (not (Text.null equalityRevision))
          (not (Text.null lawRevision))
          True
          (validityScopePresent relation)
    RuntimeSubjectCoincidence reason ->
      mapRelationDecision key relation (Just reason) $
        Kernel.decideBoundarySubjectTransferByFacts
          False False False False False True (validityScopePresent relation)

checkRebinding
  :: EvidenceTransferStageBundle
  -> (EvidenceRebindingKey, EvidenceRebindingClaim)
  -> Either EvidenceTransferVerificationError ()
checkRebinding bundle (key, claim) = do
  requireEqual EvidenceRebindingMapKeyMismatch key (evidenceRebindingKey claim)
  let source = evidenceRebindingSource claim
      target = evidenceRebindingTarget claim
      correspondences = subjectStageCorrespondences (evidenceTransferStageBase bundle)
  if source == target
    then Left (EvidenceRebindingSourceEqualsTarget key source)
    else Right ()
  sourceCorrespondence <- maybe
    (Left (EvidenceRebindingUnknownSource key source))
    Right
    (Map.lookup source correspondences)
  if Map.member target correspondences
    then Right ()
    else Left (EvidenceRebindingUnknownTarget key target)
  let evidenceRefs = evidenceRebindingEvidenceRefs claim
  if Set.null evidenceRefs
    then Left (EvidenceRebindingEmptyEvidenceSet key)
    else Right ()
  mapM_ (requireSourceEvidence key sourceCorrespondence)
    (Set.toAscList evidenceRefs)
  relationKey <- maybe
    (Left (EvidenceRebindingMissingRelation key))
    Right
    (evidenceRebindingRelation claim)
  relation <- maybe
    (Left (EvidenceRebindingUnknownRelation key relationKey))
    Right
    (Map.lookup relationKey (evidenceTransferStageRelations bundle))
  if subjectTransferSource relation == source
      && subjectTransferTarget relation == target
    then Right ()
    else Left (EvidenceRebindingRelationEndpointMismatch
      key relationKey (subjectTransferSource relation) (subjectTransferTarget relation))
  mapM_ (requireTransferableEvidence key relationKey relation)
    (Set.toAscList evidenceRefs)

requireSourceEvidence
  :: EvidenceRebindingKey
  -> SubjectCorrespondence
  -> Text
  -> Either EvidenceTransferVerificationError ()
requireSourceEvidence key correspondence evidenceRef
  | Set.member evidenceRef (subjectCorrespondenceEvidenceRefs correspondence) = Right ()
  | otherwise = Left (EvidenceRebindingSourceEvidenceMissing key evidenceRef)

requireTransferableEvidence
  :: EvidenceRebindingKey
  -> SubjectTransferRelationKey
  -> SubjectTransferRelation
  -> Text
  -> Either EvidenceTransferVerificationError ()
requireTransferableEvidence key relationKey relation evidenceRef =
  case subjectTransferBasis relation of
    CheckedSubjectCopy
        (CopyRelationRevision copyRevision)
        (ByteEqualityRevision equalityRevision)
        (EvidenceTransferLawRevision lawRevision) ->
      mapEvidenceDecision key relationKey relation evidenceRef Nothing $
        Kernel.decideBoundarySubjectTransferByFacts
          True
          True
          (not (Text.null copyRevision))
          (not (Text.null equalityRevision))
          (not (Text.null lawRevision))
          (Set.member evidenceRef (subjectTransferAllowedEvidence relation))
          (validityScopePresent relation)
    RuntimeSubjectCoincidence reason ->
      mapEvidenceDecision key relationKey relation evidenceRef (Just reason) $
        Kernel.decideBoundarySubjectTransferByFacts
          False False False False False
          (Set.member evidenceRef (subjectTransferAllowedEvidence relation))
          (validityScopePresent relation)

mapRelationDecision
  :: SubjectTransferRelationKey
  -> SubjectTransferRelation
  -> Maybe Text
  -> Kernel.BoundarySubjectTransferDecision
  -> Either EvidenceTransferVerificationError ()
mapRelationDecision relationKey _ runtimeReason decision = case decision of
  Kernel.BoundarySubjectTransferAcceptedDecision -> Right ()
  Kernel.BoundarySubjectRuntimeCoincidenceDecision ->
    Left (SubjectTransferRuntimeCoincidenceRejected relationKey
      (maybe "runtime subject coincidence" id runtimeReason))
  Kernel.BoundarySubjectCopyRevisionDecision ->
    Left (SubjectTransferEmptyCopyRevision relationKey)
  Kernel.BoundarySubjectByteEqualityDecision ->
    Left (SubjectTransferEmptyByteEqualityRevision relationKey)
  Kernel.BoundarySubjectTransferLawDecision ->
    Left (SubjectTransferEmptyLawRevision relationKey)
  Kernel.BoundarySubjectValidityScopeDecision ->
    Left (SubjectTransferEmptyValidityScope relationKey)
  Kernel.BoundarySubjectTransportKindDecision ->
    Left (SubjectTransferEmptyCopyRevision relationKey)
  Kernel.BoundarySubjectEvidenceReferenceDecision ->
    Left (SubjectTransferEmptyAllowedEvidence relationKey)

mapEvidenceDecision
  :: EvidenceRebindingKey
  -> SubjectTransferRelationKey
  -> SubjectTransferRelation
  -> Text
  -> Maybe Text
  -> Kernel.BoundarySubjectTransferDecision
  -> Either EvidenceTransferVerificationError ()
mapEvidenceDecision key relationKey _ evidenceRef runtimeReason decision = case decision of
  Kernel.BoundarySubjectTransferAcceptedDecision -> Right ()
  Kernel.BoundarySubjectRuntimeCoincidenceDecision ->
    Left (SubjectTransferRuntimeCoincidenceRejected relationKey
      (maybe "runtime subject coincidence" id runtimeReason))
  Kernel.BoundarySubjectCopyRevisionDecision ->
    Left (SubjectTransferEmptyCopyRevision relationKey)
  Kernel.BoundarySubjectByteEqualityDecision ->
    Left (SubjectTransferEmptyByteEqualityRevision relationKey)
  Kernel.BoundarySubjectTransferLawDecision ->
    Left (SubjectTransferEmptyLawRevision relationKey)
  Kernel.BoundarySubjectEvidenceReferenceDecision ->
    Left (EvidenceRebindingEvidenceNotTransferable key relationKey evidenceRef)
  Kernel.BoundarySubjectValidityScopeDecision ->
    Left (SubjectTransferEmptyValidityScope relationKey)
  Kernel.BoundarySubjectTransportKindDecision ->
    Left (SubjectTransferEmptyCopyRevision relationKey)

validityScopePresent :: SubjectTransferRelation -> Bool
validityScopePresent relation = case subjectTransferValidityScope relation of
  SubjectValidityScopeRevision scope -> not (Text.null scope)

semanticRelation :: SubjectTransferRelation -> SemanticForm
semanticRelation relation = SemanticRecord (Map.fromList
  [ ("key", SemanticAtom
      (unSubjectTransferRelationKey (subjectTransferRelationKey relation)))
  , ("source", SemanticAtom
      (unSourceSubjectKey (subjectTransferSource relation)))
  , ("target", SemanticAtom
      (unSourceSubjectKey (subjectTransferTarget relation)))
  , ("basis", semanticBasis (subjectTransferBasis relation))
  , ("allowed_evidence", SemanticUnordered
      (Set.map SemanticAtom (subjectTransferAllowedEvidence relation)))
  , ("validity_scope", SemanticAtom
      (validityText (subjectTransferValidityScope relation)))
  ])

semanticBasis :: SubjectTransferBasis -> SemanticForm
semanticBasis basis = case basis of
  CheckedSubjectCopy copyRevision equalityRevision lawRevision ->
    SemanticRecord (Map.fromList
      [ ("kind", SemanticAtom "checked-subject-copy")
      , ("copy_revision", SemanticAtom (copyRevisionText copyRevision))
      , ("byte_equality_revision", SemanticAtom
          (byteEqualityRevisionText equalityRevision))
      , ("evidence_transfer_law_revision", SemanticAtom
          (transferLawRevisionText lawRevision))
      ])
  RuntimeSubjectCoincidence reason -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "runtime-subject-coincidence")
    , ("reason", SemanticAtom reason)
    ])

semanticRebinding :: EvidenceRebindingClaim -> SemanticForm
semanticRebinding claim = SemanticRecord (Map.fromList
  [ ("key", SemanticAtom (unEvidenceRebindingKey (evidenceRebindingKey claim)))
  , ("source", SemanticAtom (unSourceSubjectKey (evidenceRebindingSource claim)))
  , ("target", SemanticAtom (unSourceSubjectKey (evidenceRebindingTarget claim)))
  , ("evidence", SemanticUnordered
      (Set.map SemanticAtom (evidenceRebindingEvidenceRefs claim)))
  , ("relation", SemanticAtom (maybe "none" unSubjectTransferRelationKey
      (evidenceRebindingRelation claim)))
  ])

baseRevisionText :: SubjectStageBundle -> Text
baseRevisionText = unSubjectStageRevision . subjectStageRevision

copyRevisionText :: CopyRelationRevision -> Text
copyRevisionText (CopyRelationRevision value) = value

byteEqualityRevisionText :: ByteEqualityRevision -> Text
byteEqualityRevisionText (ByteEqualityRevision value) = value

transferLawRevisionText :: EvidenceTransferLawRevision -> Text
transferLawRevisionText (EvidenceTransferLawRevision value) = value

validityText :: SubjectValidityScopeRevision -> Text
validityText (SubjectValidityScopeRevision value) = value

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
