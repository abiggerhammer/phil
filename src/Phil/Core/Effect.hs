{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Effect
  ( SemanticEffectSubjectKey (..)
  , SemanticEffectRelationRevision (..)
  , SemanticEffectSubjectCorrespondence
  , CheckedSemanticEffect (..)
  , SemanticEffectCheckError (..)
  , checkedSemanticEffect
  , checkedSemanticEffectSubjectCorrespondence
  , retargetCheckedSemanticEffectSubject
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Callable (SemanticEffect (..))
import Phil.Core.Static
  ( SemanticForm (..)
  , canonicalSemanticForm
  )

-- | Exact semantic subject identity carried by one effect argument.  This is an
-- opaque-to-the-source semantic key supplied by the competent resolver/checker;
-- display spelling, pointer/handle identity, target symbols, and source offsets
-- are deliberately absent from the type.
newtype SemanticEffectSubjectKey = SemanticEffectSubjectKey
  { unSemanticEffectSubjectKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Identity of an already-accepted semantic equality/succession/
-- correspondence relation used to justify changing an effect subject.
newtype SemanticEffectRelationRevision = SemanticEffectRelationRevision
  { unSemanticEffectRelationRevision :: Text
  }
  deriving (Eq, Ord, Show)

-- | Opaque checked permission to retarget one exact subject to another.  The
-- constructor is intentionally not exported: callers can only obtain a value by
-- presenting nonempty exact source/target keys plus the revision of a relation
-- that a competent outer layer has already accepted.
data SemanticEffectSubjectCorrespondence = SemanticEffectSubjectCorrespondence
  SemanticEffectSubjectKey
  SemanticEffectSubjectKey
  SemanticEffectRelationRevision
  deriving (Eq, Ord, Show)

-- | Structured view retained alongside the established Text-backed
-- 'SemanticEffect'.  Existing CALL-EFFECT finite-set machinery continues to use
-- the Core carrier unchanged; this structure supplies the identity discipline
-- required by EFF-001/002.
data CheckedSemanticEffect = CheckedSemanticEffect
  { checkedSemanticEffectLabel :: [Text]
  , checkedSemanticEffectSubjects :: [SemanticEffectSubjectKey]
  , checkedSemanticEffectCore :: SemanticEffect
  }
  deriving (Eq, Ord, Show)

data SemanticEffectCheckError
  = EmptySemanticEffectLabel
  | EmptySemanticEffectLabelPart Int
  | EmptySemanticEffectSubjectKey Int
  | EmptySemanticEffectRelationRevision
  | SemanticEffectSubjectIndexOutOfRange Int
  | SemanticEffectSubjectRetargetRequiresCorrespondence
      SemanticEffectSubjectKey
      SemanticEffectSubjectKey
  | SemanticEffectSubjectCorrespondenceSourceMismatch
      SemanticEffectSubjectKey
      SemanticEffectSubjectKey
  | SemanticEffectSubjectCorrespondenceTargetMismatch
      SemanticEffectSubjectKey
      SemanticEffectSubjectKey
  deriving (Eq, Ord, Show)

-- | Construct one checked semantic effect from its exact label and semantic
-- subjects.  The zero-subject case preserves the historic CALL-EFFECT identity
-- byte-for-byte; argument-bearing effects use a versioned canonical encoding so
-- equal labels over distinct semantic subjects remain distinct.
checkedSemanticEffect
  :: [Text]
  -> [SemanticEffectSubjectKey]
  -> Either SemanticEffectCheckError CheckedSemanticEffect
checkedSemanticEffect labelParts subjects = do
  validateLabel labelParts
  validateSubjects subjects
  pure CheckedSemanticEffect
    { checkedSemanticEffectLabel = labelParts
    , checkedSemanticEffectSubjects = subjects
    , checkedSemanticEffectCore = semanticEffectCore labelParts subjects
    }

-- | Package an exact already-accepted subject relation for later retargeting.
-- This function validates only representation integrity; the caller remains
-- responsible for invoking it only after the competent equality/succession/
-- correspondence checker has accepted the named relation revision.
checkedSemanticEffectSubjectCorrespondence
  :: SemanticEffectSubjectKey
  -> SemanticEffectSubjectKey
  -> SemanticEffectRelationRevision
  -> Either SemanticEffectCheckError SemanticEffectSubjectCorrespondence
checkedSemanticEffectSubjectCorrespondence source target revision = do
  validateSubjectAt 0 source
  validateSubjectAt 1 target
  case revision of
    SemanticEffectRelationRevision value
      | Text.null value -> Left EmptySemanticEffectRelationRevision
      | otherwise -> Right
          (SemanticEffectSubjectCorrespondence source target revision)

-- | Retarget one subject occurrence.  Exact identity is substitutable without
-- extra evidence.  A distinct target is rejected unless an exact checked
-- correspondence names the current subject as source and requested subject as
-- target; runtime/representation coincidence has no route through this API.
retargetCheckedSemanticEffectSubject
  :: Int
  -> SemanticEffectSubjectKey
  -> Maybe SemanticEffectSubjectCorrespondence
  -> CheckedSemanticEffect
  -> Either SemanticEffectCheckError CheckedSemanticEffect
retargetCheckedSemanticEffectSubject index target correspondence checked = do
  source <- maybe
    (Left (SemanticEffectSubjectIndexOutOfRange index))
    Right
    (atMay index (checkedSemanticEffectSubjects checked))
  if source == target
    then pure checked
    else do
      case correspondence of
        Nothing -> Left
          (SemanticEffectSubjectRetargetRequiresCorrespondence source target)
        Just (SemanticEffectSubjectCorrespondence relationSource relationTarget _revision)
          | relationSource /= source -> Left
              (SemanticEffectSubjectCorrespondenceSourceMismatch source relationSource)
          | relationTarget /= target -> Left
              (SemanticEffectSubjectCorrespondenceTargetMismatch target relationTarget)
          | otherwise -> checkedSemanticEffect
              (checkedSemanticEffectLabel checked)
              (replaceAt index target (checkedSemanticEffectSubjects checked))

semanticEffectCore :: [Text] -> [SemanticEffectSubjectKey] -> SemanticEffect
semanticEffectCore labelParts [] =
  SemanticEffect (Text.intercalate "." labelParts)
semanticEffectCore labelParts subjects =
  SemanticEffect
    ( "phil.effect.subject.v1:"
      <> canonicalSemanticForm
        (SemanticRecord (Map.fromList
          [ ("label", SemanticOrdered (map SemanticAtom labelParts))
          , ("subjects", SemanticOrdered (map subjectForm subjects))
          ]))
    )
  where
    subjectForm (SemanticEffectSubjectKey key) = SemanticAtom key

validateLabel :: [Text] -> Either SemanticEffectCheckError ()
validateLabel [] = Left EmptySemanticEffectLabel
validateLabel parts = go 0 parts
  where
    go _ [] = Right ()
    go index (part : rest)
      | Text.null part = Left (EmptySemanticEffectLabelPart index)
      | otherwise = go (index + 1) rest

validateSubjects :: [SemanticEffectSubjectKey] -> Either SemanticEffectCheckError ()
validateSubjects = go 0
  where
    go _ [] = Right ()
    go index (subject : rest) = do
      validateSubjectAt index subject
      go (index + 1) rest

validateSubjectAt
  :: Int
  -> SemanticEffectSubjectKey
  -> Either SemanticEffectCheckError ()
validateSubjectAt index (SemanticEffectSubjectKey key)
  | Text.null key = Left (EmptySemanticEffectSubjectKey index)
  | otherwise = Right ()

atMay :: Int -> [a] -> Maybe a
atMay index values
  | index < 0 = Nothing
  | otherwise = go index values
  where
    go _ [] = Nothing
    go 0 (value : _) = Just value
    go remaining (_ : rest) = go (remaining - 1) rest

replaceAt :: Int -> a -> [a] -> [a]
replaceAt index replacement values = go index values
  where
    go _ [] = []
    go 0 (_ : rest) = replacement : rest
    go remaining (value : rest) = value : go (remaining - 1) rest
