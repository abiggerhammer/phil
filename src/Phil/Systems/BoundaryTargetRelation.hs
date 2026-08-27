{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.BoundaryTargetRelation
  ( ZeroCopyTargetRelation (..)
  , BoundaryTargetRealization (..)
  , BoundaryTargetRelationError (..)
  , verifyBoundaryTargetRealization
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.BoundaryMapping
  ( BoundaryRepresentationId (..)
  , ValueTypeRevision (..)
  )
import Phil.Core.Syntax (GrammarId (..))
import Phil.Systems.TargetStrengthening
  ( TargetStrengtheningStageBundle (..)
  , TargetStrengtheningStageRevision
  , TargetStrengtheningVerificationError
  , verifyTargetStrengtheningStageBundle
  )

data ZeroCopyTargetRelation = ZeroCopyTargetRelation
  { zeroCopyTargetStageRevision :: TargetStrengtheningStageRevision
  , zeroCopyBoundaryRepresentation :: BoundaryRepresentationId
  , zeroCopyGrammarRevision :: GrammarId
  , zeroCopyValueTypeRevision :: ValueTypeRevision
  , zeroCopySourceSemanticLayout :: Text
  , zeroCopyConcreteMemoryLayout :: Text
  , zeroCopyEndianAlignmentPaddingTagging :: Text
  , zeroCopyLifetimeRules :: Text
  , zeroCopyOwnershipRules :: Text
  , zeroCopyDeviceStorageConstraints :: Text
  , zeroCopyTargetAssumptionsCarriers :: Text
  }
  deriving (Eq, Show)

data BoundaryTargetRealization
  = CheckedZeroCopy ZeroCopyTargetRelation
  | PointerReinterpretation Text
  deriving (Eq, Show)

data BoundaryTargetRelationError
  = BoundaryTargetBaseStageError TargetStrengtheningVerificationError
  | BoundaryTargetStageRevisionMismatch
      TargetStrengtheningStageRevision TargetStrengtheningStageRevision
  | BoundaryTargetMissingFact Text
  | BoundaryTargetPointerReinterpretationRejected Text
  deriving (Eq, Show)

verifyBoundaryTargetRealization
  :: TargetStrengtheningStageBundle
  -> BoundaryTargetRealization
  -> Either BoundaryTargetRelationError ()
verifyBoundaryTargetRealization base realization = do
  mapLeft BoundaryTargetBaseStageError (verifyTargetStrengtheningStageBundle base)
  case realization of
    PointerReinterpretation detail ->
      Left (BoundaryTargetPointerReinterpretationRejected detail)
    CheckedZeroCopy relation -> do
      requireEqual BoundaryTargetStageRevisionMismatch
        (targetStrengtheningStageRevision base)
        (zeroCopyTargetStageRevision relation)
      requireRevisionFacts relation
      mapM_ requireFact
        [ ("source semantic constructors/fields", zeroCopySourceSemanticLayout relation)
        , ("concrete memory layout", zeroCopyConcreteMemoryLayout relation)
        , ("endian/alignment/padding/tagging", zeroCopyEndianAlignmentPaddingTagging relation)
        , ("lifetime rules", zeroCopyLifetimeRules relation)
        , ("ownership/borrowing rules", zeroCopyOwnershipRules relation)
        , ("device/storage-domain constraints", zeroCopyDeviceStorageConstraints relation)
        , ("target assumptions/carriers", zeroCopyTargetAssumptionsCarriers relation)
        ]

requireRevisionFacts
  :: ZeroCopyTargetRelation
  -> Either BoundaryTargetRelationError ()
requireRevisionFacts relation = do
  let BoundaryRepresentationId representation = zeroCopyBoundaryRepresentation relation
      GrammarId grammar = zeroCopyGrammarRevision relation
      ValueTypeRevision valueType = zeroCopyValueTypeRevision relation
  requireFact ("boundary representation revision", representation)
  requireFact ("grammar revision", grammar)
  requireFact ("semantic value type revision", valueType)

requireFact :: (Text, Text) -> Either BoundaryTargetRelationError ()
requireFact (label, value)
  | Text.null (Text.strip value) = Left (BoundaryTargetMissingFact label)
  | otherwise = Right ()

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
