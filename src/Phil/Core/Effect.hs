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
import qualified EffectSubjectKernel as Kernel
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
-- Concrete Text nonemptiness is reflected into the Rocq-extracted decision
-- kernel; truth/competence of the named relation remains an outer authority.
checkedSemanticEffectSubjectCorrespondence
  :: SemanticEffectSubjectKey
  -> SemanticEffectSubjectKey
  -> SemanticEffectRelationRevision
  -> Either SemanticEffectCheckError SemanticEffectSubjectCorrespondence
checkedSemanticEffectSubjectCorrespondence source target revision =
  case Kernel.decideEffectSubjectCorrespondence
      (subjectKeyNonempty source)
      (subjectKeyNonempty target)
      (relationRevisionNonempty revision) of
    Kernel.EffectSubjectCorrespondenceAccepted -> Right
      (SemanticEffectSubjectCorrespondence source target revision)
    Kernel.EffectSubjectCorrespondenceSourceEmpty ->
      Left (EmptySemanticEffectSubjectKey 0)
    Kernel.EffectSubjectCorrespondenceTargetEmpty ->
      Left (EmptySemanticEffectSubjectKey 1)
    Kernel.EffectSubjectCorrespondenceRevisionEmpty ->
      Left EmptySemanticEffectRelationRevision

-- | Retarget one subject occurrence.  Native indexing/equality reflects only
-- primitive facts into the Rocq-extracted decision kernel.  The kernel owns the
-- semantic branch order: exact identity needs no evidence; a distinct subject
-- requires exact source/target correspondence; representation coincidence has
-- no decision input.
retargetCheckedSemanticEffectSubject
  :: Int
  -> SemanticEffectSubjectKey
  -> Maybe SemanticEffectSubjectCorrespondence
  -> CheckedSemanticEffect
  -> Either SemanticEffectCheckError CheckedSemanticEffect
retargetCheckedSemanticEffectSubject index target correspondence checked =
  case atMay index (checkedSemanticEffectSubjects checked) of
    Nothing ->
      case Kernel.decideEffectSubjectRetarget
          False False (correspondencePresent correspondence) False False of
        Kernel.EffectSubjectRetargetIndexOutOfRange ->
          Left (SemanticEffectSubjectIndexOutOfRange index)
        _ -> Left (SemanticEffectSubjectIndexOutOfRange index)
    Just source ->
      let sameSubject = source == target
          (relationSource, relationTarget, sourceMatches, targetMatches) =
            correspondenceFacts source target correspondence
      in case Kernel.decideEffectSubjectRetarget
          True
          sameSubject
          (correspondencePresent correspondence)
          sourceMatches
          targetMatches of
        Kernel.EffectSubjectRetargetAcceptedSame -> Right checked
        Kernel.EffectSubjectRetargetAcceptedCorrespondence ->
          checkedSemanticEffect
            (checkedSemanticEffectLabel checked)
            (replaceAt index target (checkedSemanticEffectSubjects checked))
        Kernel.EffectSubjectRetargetIndexOutOfRange ->
          Left (SemanticEffectSubjectIndexOutOfRange index)
        Kernel.EffectSubjectRetargetRequiresCorrespondence -> Left
          (SemanticEffectSubjectRetargetRequiresCorrespondence source target)
        Kernel.EffectSubjectRetargetCorrespondenceSourceMismatch -> Left
          (SemanticEffectSubjectCorrespondenceSourceMismatch source relationSource)
        Kernel.EffectSubjectRetargetCorrespondenceTargetMismatch -> Left
          (SemanticEffectSubjectCorrespondenceTargetMismatch target relationTarget)

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
validateSubjectAt index subject
  | subjectKeyNonempty subject = Right ()
  | otherwise = Left (EmptySemanticEffectSubjectKey index)

subjectKeyNonempty :: SemanticEffectSubjectKey -> Bool
subjectKeyNonempty (SemanticEffectSubjectKey key) = not (Text.null key)

relationRevisionNonempty :: SemanticEffectRelationRevision -> Bool
relationRevisionNonempty (SemanticEffectRelationRevision value) =
  not (Text.null value)

correspondencePresent :: Maybe SemanticEffectSubjectCorrespondence -> Bool
correspondencePresent maybeCorrespondence = case maybeCorrespondence of
  Nothing -> False
  Just _ -> True

correspondenceFacts
  :: SemanticEffectSubjectKey
  -> SemanticEffectSubjectKey
  -> Maybe SemanticEffectSubjectCorrespondence
  -> ( SemanticEffectSubjectKey
     , SemanticEffectSubjectKey
     , Bool
     , Bool
     )
correspondenceFacts source target maybeCorrespondence =
  case maybeCorrespondence of
    Nothing -> (source, target, False, False)
    Just (SemanticEffectSubjectCorrespondence relationSource relationTarget _revision) ->
      ( relationSource
      , relationTarget
      , relationSource == source
      , relationTarget == target
      )

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
