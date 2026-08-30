{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.BoundaryMapping
  ( BoundaryRepresentationId (..)
  , ValueTypeRevision (..)
  , BoundaryRepresentation (..)
  , BoundaryMappingRequest (..)
  , CorrespondenceEvidence (..)
  , BoundaryMappingDisposition (..)
  , BoundaryMappingError (..)
  , mapRecognizedBoundary
  , mapRecognizedBoundaryWithDisposition
  ) where

import qualified BoundaryRepresentationKernel as Kernel
import Data.Text (Text)
import Phil.Core.Recognition
  ( ParsedWitness
  , parsedGrammarId
  , parsedValueName
  )
import Phil.Core.Syntax (GrammarId, Name)

newtype BoundaryRepresentationId = BoundaryRepresentationId Text
  deriving (Eq, Ord, Show)

newtype ValueTypeRevision = ValueTypeRevision Text
  deriving (Eq, Ord, Show)

data BoundaryRepresentation = BoundaryRepresentation
  { representationId :: BoundaryRepresentationId
  , representationGrammar :: GrammarId
  , representationValueType :: ValueTypeRevision
  }
  deriving (Eq, Show)

data BoundaryMappingRequest = BoundaryMappingRequest
  { requestedRepresentation :: BoundaryRepresentationId
  , requestedGrammar :: GrammarId
  , requestedValueType :: ValueTypeRevision
  , requestedGrammarValue :: Name
  , requestedSemanticValue :: Name
  }
  deriving (Eq, Show)

data CorrespondenceEvidence = CorrespondenceEvidence
  { correspondenceRepresentation :: BoundaryRepresentationId
  , correspondenceGrammar :: GrammarId
  , correspondenceValueType :: ValueTypeRevision
  , correspondenceGrammarValue :: Name
  , correspondenceSemanticValue :: Name
  }
  deriving (Eq, Show)

data BoundaryMappingDisposition
  = MappingAccepted
  | MappingRejected Text
  deriving (Eq, Show)

data BoundaryMappingError
  = BoundaryRepresentationMismatch BoundaryRepresentationId BoundaryRepresentationId
  | BoundaryGrammarMismatch GrammarId GrammarId
  | BoundaryValueTypeMismatch ValueTypeRevision ValueTypeRevision
  | RecognizedGrammarMismatch GrammarId GrammarId
  | RecognizedValueMismatch Name Name
  | BoundaryMappingFailure BoundaryRepresentationId Name Text
  deriving (Eq, Show)

mapRecognizedBoundary
  :: BoundaryRepresentation
  -> ParsedWitness
  -> BoundaryMappingRequest
  -> Either BoundaryMappingError CorrespondenceEvidence
mapRecognizedBoundary representation parsed request =
  mapRecognizedBoundaryWithDisposition representation parsed request MappingAccepted

mapRecognizedBoundaryWithDisposition
  :: BoundaryRepresentation
  -> ParsedWitness
  -> BoundaryMappingRequest
  -> BoundaryMappingDisposition
  -> Either BoundaryMappingError CorrespondenceEvidence
mapRecognizedBoundaryWithDisposition representation parsed request disposition =
  case Kernel.decideBoundaryMappingByFacts
      (requestedRepresentation request == representationId representation)
      (requestedGrammar request == representationGrammar representation)
      (requestedValueType request == representationValueType representation)
      (parsedGrammarId parsed == representationGrammar representation)
      (parsedValueName parsed == requestedGrammarValue request)
      (disposition == MappingAccepted) of
    Kernel.BoundaryRepresentationMismatchDecision ->
      Left (BoundaryRepresentationMismatch
        (representationId representation)
        (requestedRepresentation request))
    Kernel.BoundaryGrammarMismatchDecision ->
      Left (BoundaryGrammarMismatch
        (representationGrammar representation)
        (requestedGrammar request))
    Kernel.BoundaryValueTypeMismatchDecision ->
      Left (BoundaryValueTypeMismatch
        (representationValueType representation)
        (requestedValueType request))
    Kernel.RecognizedGrammarMismatchDecision ->
      Left (RecognizedGrammarMismatch
        (representationGrammar representation)
        (parsedGrammarId parsed))
    Kernel.RecognizedValueMismatchDecision ->
      Left (RecognizedValueMismatch
        (parsedValueName parsed)
        (requestedGrammarValue request))
    Kernel.BoundaryMappingRejectedDecision ->
      case disposition of
        MappingRejected detail ->
          Left (BoundaryMappingFailure
            (representationId representation)
            (requestedGrammarValue request)
            detail)
        MappingAccepted ->
          Left (BoundaryMappingFailure
            (representationId representation)
            (requestedGrammarValue request)
            "certified boundary mapping bridge mismatch")
    Kernel.BoundaryMappingDecisionAccepted ->
      case Kernel.planBoundaryCorrespondence
          (representationId representation)
          (representationGrammar representation)
          (representationValueType representation)
          (requestedGrammarValue request)
          (requestedSemanticValue request) of
        Kernel.MkBoundaryCorrespondencePlan
            plannedRepresentation
            plannedGrammar
            plannedValueType
            plannedGrammarValue
            plannedSemanticValue ->
          Right CorrespondenceEvidence
            { correspondenceRepresentation = plannedRepresentation
            , correspondenceGrammar = plannedGrammar
            , correspondenceValueType = plannedValueType
            , correspondenceGrammarValue = plannedGrammarValue
            , correspondenceSemanticValue = plannedSemanticValue
            }
