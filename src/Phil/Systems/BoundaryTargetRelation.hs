{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.BoundaryTargetRelation
  ( ZeroCopyTargetRelation (..)
  , BoundaryTargetRealization (..)
  , BoundaryTargetRelationError (..)
  , verifyBoundaryTargetRealization
  ) where

import qualified BoundarySubjectKernel as Kernel
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
      case Kernel.decideZeroCopyRealizationByFacts
        False False False False False False False False False False False False of
        Kernel.ZeroCopyPointerReinterpretationDecision ->
          Left (BoundaryTargetPointerReinterpretationRejected detail)
        _ -> Left (BoundaryTargetPointerReinterpretationRejected detail)
    CheckedZeroCopy relation ->
      mapZeroCopyDecision base relation (checkedZeroCopyDecision base relation)

checkedZeroCopyDecision
  :: TargetStrengtheningStageBundle
  -> ZeroCopyTargetRelation
  -> Kernel.ZeroCopyRealizationDecision
checkedZeroCopyDecision base relation =
  Kernel.decideZeroCopyRealizationByFacts
    True
    (targetStrengtheningStageRevision base == zeroCopyTargetStageRevision relation)
    (factPresent representation)
    (factPresent grammar)
    (factPresent valueType)
    (factPresent (zeroCopySourceSemanticLayout relation))
    (factPresent (zeroCopyConcreteMemoryLayout relation))
    (factPresent (zeroCopyEndianAlignmentPaddingTagging relation))
    (factPresent (zeroCopyLifetimeRules relation))
    (factPresent (zeroCopyOwnershipRules relation))
    (factPresent (zeroCopyDeviceStorageConstraints relation))
    (factPresent (zeroCopyTargetAssumptionsCarriers relation))
  where
    BoundaryRepresentationId representation = zeroCopyBoundaryRepresentation relation
    GrammarId grammar = zeroCopyGrammarRevision relation
    ValueTypeRevision valueType = zeroCopyValueTypeRevision relation

mapZeroCopyDecision
  :: TargetStrengtheningStageBundle
  -> ZeroCopyTargetRelation
  -> Kernel.ZeroCopyRealizationDecision
  -> Either BoundaryTargetRelationError ()
mapZeroCopyDecision base relation decision = case decision of
  Kernel.ZeroCopyRealizationAcceptedDecision -> Right ()
  Kernel.ZeroCopyStageRevisionDecision ->
    Left (BoundaryTargetStageRevisionMismatch
      (targetStrengtheningStageRevision base)
      (zeroCopyTargetStageRevision relation))
  Kernel.ZeroCopyBoundaryRepresentationDecision ->
    Left (BoundaryTargetMissingFact "boundary representation revision")
  Kernel.ZeroCopyGrammarDecision ->
    Left (BoundaryTargetMissingFact "grammar revision")
  Kernel.ZeroCopyValueTypeDecision ->
    Left (BoundaryTargetMissingFact "semantic value type revision")
  Kernel.ZeroCopySourceSemanticLayoutDecision ->
    Left (BoundaryTargetMissingFact "source semantic constructors/fields")
  Kernel.ZeroCopyConcreteMemoryLayoutDecision ->
    Left (BoundaryTargetMissingFact "concrete memory layout")
  Kernel.ZeroCopyEndianAlignmentPaddingTaggingDecision ->
    Left (BoundaryTargetMissingFact "endian/alignment/padding/tagging")
  Kernel.ZeroCopyLifetimeRulesDecision ->
    Left (BoundaryTargetMissingFact "lifetime rules")
  Kernel.ZeroCopyOwnershipRulesDecision ->
    Left (BoundaryTargetMissingFact "ownership/borrowing rules")
  Kernel.ZeroCopyDeviceStorageConstraintsDecision ->
    Left (BoundaryTargetMissingFact "device/storage-domain constraints")
  Kernel.ZeroCopyTargetAssumptionsCarriersDecision ->
    Left (BoundaryTargetMissingFact "target assumptions/carriers")
  Kernel.ZeroCopyPointerReinterpretationDecision ->
    Left (BoundaryTargetMissingFact "checked zero-copy realization")

factPresent :: Text -> Bool
factPresent = not . Text.null . Text.strip

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
