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
mapRecognizedBoundaryWithDisposition representation parsed request disposition
  | requestedRepresentation request /= representationId representation =
      Left (BoundaryRepresentationMismatch (representationId representation) (requestedRepresentation request))
  | requestedGrammar request /= representationGrammar representation =
      Left (BoundaryGrammarMismatch (representationGrammar representation) (requestedGrammar request))
  | requestedValueType request /= representationValueType representation =
      Left (BoundaryValueTypeMismatch (representationValueType representation) (requestedValueType request))
  | parsedGrammarId parsed /= representationGrammar representation =
      Left (RecognizedGrammarMismatch (representationGrammar representation) (parsedGrammarId parsed))
  | parsedValueName parsed /= requestedGrammarValue request =
      Left (RecognizedValueMismatch (parsedValueName parsed) (requestedGrammarValue request))
  | MappingRejected detail <- disposition =
      Left (BoundaryMappingFailure
        (representationId representation)
        (requestedGrammarValue request)
        detail)
  | otherwise = Right CorrespondenceEvidence
      { correspondenceRepresentation = representationId representation
      , correspondenceGrammar = representationGrammar representation
      , correspondenceValueType = representationValueType representation
      , correspondenceGrammarValue = requestedGrammarValue request
      , correspondenceSemanticValue = requestedSemanticValue request
      }
