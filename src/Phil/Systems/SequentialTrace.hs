{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.SequentialTrace
  ( SequentialEventKey (..)
  , SequentialCommutation (..)
  , SequentialTraceRefinement (..)
  , CheckedSequentialTraceRefinement (..)
  , SequentialTraceRefinementError (..)
  , renderSequentialTraceRelation
  , renderSequentialCommutationRelation
  , checkSequentialTraceRefinement
  ) where

import Data.List (findIndex, nub, sort)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (Digest)
import Phil.Systems.IR (StageContract (..))

-- | Exact semantic identity of one bounded source execution event.  The key is
-- supplied by the competent source/event projector; display spelling, target
-- instruction identity, and host execution identity are deliberately absent.
newtype SequentialEventKey = SequentialEventKey
  { unSequentialEventKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Exact evidence that two semantic events may commute without changing the
-- source projection.  Commutation is symmetric; the evidence identifier is part
-- of the StageContract relation and must be nonempty.
data SequentialCommutation = SequentialCommutation
  { sequentialCommutationLeft :: SequentialEventKey
  , sequentialCommutationRight :: SequentialEventKey
  , sequentialCommutationEvidence :: Text
  }
  deriving (Eq, Ord, Show)

-- | Ordered source/target trace relation tied to one exact StageContract and its
-- source/target artifact digests.  StageContract.trace_relation itself remains a
-- set-like collection of relation facts; order lives inside this checked witness.
data SequentialTraceRefinement = SequentialTraceRefinement
  { sequentialTraceStageContractId :: Text
  , sequentialTraceSourceDigest :: Digest
  , sequentialTraceTargetDigest :: Digest
  , sequentialTraceSourceOrder :: [SequentialEventKey]
  , sequentialTraceTargetProjection :: [SequentialEventKey]
  , sequentialTraceCommutations :: Set.Set SequentialCommutation
  }
  deriving (Eq, Show)

data CheckedSequentialTraceRefinement = CheckedSequentialTraceRefinement
  { checkedSequentialTraceSourceOrder :: [SequentialEventKey]
  , checkedSequentialTraceTargetProjection :: [SequentialEventKey]
  , checkedSequentialTraceUsedCommutations :: Set.Set SequentialCommutation
  }
  deriving (Eq, Show)

data SequentialTraceRefinementError
  = SequentialStageContractIdMismatch Text Text
  | SequentialSourceDigestMismatch Digest Digest
  | SequentialTargetDigestMismatch Digest Digest
  | SequentialDuplicateSourceEvent SequentialEventKey
  | SequentialDuplicateTargetEvent SequentialEventKey
  | SequentialTraceEventSetMismatch
      [SequentialEventKey]
      [SequentialEventKey]
  | SequentialMissingTraceRelation Text
  | SequentialEmptyCommutationEvidence SequentialEventKey SequentialEventKey
  | SequentialMissingCommutationRelation SequentialCommutation
  | SequentialOrderViolation SequentialEventKey SequentialEventKey
  deriving (Eq, Show)

renderSequentialTraceRelation :: SequentialTraceRefinement -> Text
renderSequentialTraceRelation refinement = Text.intercalate "|"
  [ "phil.exec.trace.v1"
  , "source=" <> renderKeys (sequentialTraceSourceOrder refinement)
  , "target=" <> renderKeys (sequentialTraceTargetProjection refinement)
  ]

renderSequentialCommutationRelation :: SequentialCommutation -> Text
renderSequentialCommutationRelation commutation = Text.intercalate "|"
  [ "phil.exec.commute.v1"
  , "left=" <> unSequentialEventKey left
  , "right=" <> unSequentialEventKey right
  , "evidence=" <> sequentialCommutationEvidence commutation
  ]
  where
    (left, right) = normalizedPair
      (sequentialCommutationLeft commutation)
      (sequentialCommutationRight commutation)

checkSequentialTraceRefinement
  :: StageContract
  -> SequentialTraceRefinement
  -> Either SequentialTraceRefinementError CheckedSequentialTraceRefinement
checkSequentialTraceRefinement contract refinement = do
  if sequentialTraceStageContractId refinement == stageContractId contract
    then Right ()
    else Left (SequentialStageContractIdMismatch
      (stageContractId contract)
      (sequentialTraceStageContractId refinement))
  if sequentialTraceSourceDigest refinement == stageSourceArtifactDigest contract
    then Right ()
    else Left (SequentialSourceDigestMismatch
      (stageSourceArtifactDigest contract)
      (sequentialTraceSourceDigest refinement))
  if sequentialTraceTargetDigest refinement == stageTargetArtifactDigest contract
    then Right ()
    else Left (SequentialTargetDigestMismatch
      (stageTargetArtifactDigest contract)
      (sequentialTraceTargetDigest refinement))
  ensureUnique SequentialDuplicateSourceEvent (sequentialTraceSourceOrder refinement)
  ensureUnique SequentialDuplicateTargetEvent (sequentialTraceTargetProjection refinement)
  let source = sequentialTraceSourceOrder refinement
      target = sequentialTraceTargetProjection refinement
  if sort source == sort target
    then Right ()
    else Left (SequentialTraceEventSetMismatch source target)
  let traceRelation = renderSequentialTraceRelation refinement
  if traceRelation `elem` stageTraceRelation contract
    then Right ()
    else Left (SequentialMissingTraceRelation traceRelation)
  mapM_ (validateCommutationRelation contract)
    (Set.toAscList (sequentialTraceCommutations refinement))
  used <- reorderToSource
    (sequentialTraceCommutations refinement)
    source
    target
    Set.empty
  Right CheckedSequentialTraceRefinement
    { checkedSequentialTraceSourceOrder = source
    , checkedSequentialTraceTargetProjection = target
    , checkedSequentialTraceUsedCommutations = used
    }

validateCommutationRelation
  :: StageContract
  -> SequentialCommutation
  -> Either SequentialTraceRefinementError ()
validateCommutationRelation contract commutation
  | Text.null (sequentialCommutationEvidence commutation) =
      Left (SequentialEmptyCommutationEvidence
        (sequentialCommutationLeft commutation)
        (sequentialCommutationRight commutation))
  | renderSequentialCommutationRelation commutation `elem` stageTraceRelation contract =
      Right ()
  | otherwise = Left (SequentialMissingCommutationRelation commutation)

reorderToSource
  :: Set.Set SequentialCommutation
  -> [SequentialEventKey]
  -> [SequentialEventKey]
  -> Set.Set SequentialCommutation
  -> Either SequentialTraceRefinementError (Set.Set SequentialCommutation)
reorderToSource _ [] [] used = Right used
reorderToSource commutations (expected : sourceRest) target used = do
  index <- maybe
    (Left (SequentialTraceEventSetMismatch (expected : sourceRest) target))
    Right
    (findIndex (== expected) target)
  let (before, suffix) = splitAt index target
  case suffix of
    [] -> Left (SequentialTraceEventSetMismatch (expected : sourceRest) target)
    _ : after -> do
      usedHere <- foldl
        (checkCrossing commutations expected)
        (Right used)
        before
      reorderToSource commutations sourceRest (before <> after) usedHere
reorderToSource _ source target _ = Left (SequentialTraceEventSetMismatch source target)

checkCrossing
  :: Set.Set SequentialCommutation
  -> SequentialEventKey
  -> Either SequentialTraceRefinementError (Set.Set SequentialCommutation)
  -> SequentialEventKey
  -> Either SequentialTraceRefinementError (Set.Set SequentialCommutation)
checkCrossing commutations expected accumulated preceding = do
  used <- accumulated
  case matchingCommutation commutations expected preceding of
    Nothing -> Left (SequentialOrderViolation expected preceding)
    Just commutation -> Right (Set.insert commutation used)

matchingCommutation
  :: Set.Set SequentialCommutation
  -> SequentialEventKey
  -> SequentialEventKey
  -> Maybe SequentialCommutation
matchingCommutation commutations first second =
  let pair = normalizedPair first second
  in findMatching pair (Set.toAscList commutations)
  where
    findMatching _ [] = Nothing
    findMatching pair (commutation : rest)
      | normalizedPair
          (sequentialCommutationLeft commutation)
          (sequentialCommutationRight commutation) == pair = Just commutation
      | otherwise = findMatching pair rest

normalizedPair
  :: SequentialEventKey
  -> SequentialEventKey
  -> (SequentialEventKey, SequentialEventKey)
normalizedPair first second
  | first <= second = (first, second)
  | otherwise = (second, first)

ensureUnique
  :: (SequentialEventKey -> SequentialTraceRefinementError)
  -> [SequentialEventKey]
  -> Either SequentialTraceRefinementError ()
ensureUnique constructor values =
  case firstDuplicate values of
    Nothing -> Right ()
    Just duplicate -> Left (constructor duplicate)

firstDuplicate :: [SequentialEventKey] -> Maybe SequentialEventKey
firstDuplicate values = go [] values
  where
    go _ [] = Nothing
    go seen (value : rest)
      | value `elem` seen = Just value
      | otherwise = go (value : seen) rest

renderKeys :: [SequentialEventKey] -> Text
renderKeys = Text.intercalate "," . map unSequentialEventKey
