module Phil.Core.BoundarySerialization
  ( SerializationBasis (..)
  , SerializationCorrespondence (..)
  , BoundarySerializationError (..)
  , checkBoundarySerialization
  ) where

import Phil.Core.BoundaryMapping (BoundaryRepresentationId)
import Phil.Core.Syntax (Name)

data SerializationBasis
  = CheckedWireCorrespondence
  | RawMemoryLayout
  | MatchingCStructShape
  deriving (Eq, Show)

data SerializationCorrespondence = SerializationCorrespondence
  { serializationRepresentation :: BoundaryRepresentationId
  , serializationSubject :: Name
  , serializationBasis :: SerializationBasis
  }
  deriving (Eq, Show)

data BoundarySerializationError
  = UncheckedSerializationBasis SerializationBasis
  | SerializationRepresentationMismatch BoundaryRepresentationId BoundaryRepresentationId
  | SerializationSubjectMismatch Name Name
  deriving (Eq, Show)

checkBoundarySerialization
  :: BoundaryRepresentationId
  -> Name
  -> SerializationCorrespondence
  -> Either BoundarySerializationError ()
checkBoundarySerialization expectedRepresentation expectedSubject correspondence
  | serializationBasis correspondence /= CheckedWireCorrespondence =
      Left (UncheckedSerializationBasis (serializationBasis correspondence))
  | serializationRepresentation correspondence /= expectedRepresentation =
      Left (SerializationRepresentationMismatch expectedRepresentation (serializationRepresentation correspondence))
  | serializationSubject correspondence /= expectedSubject =
      Left (SerializationSubjectMismatch expectedSubject (serializationSubject correspondence))
  | otherwise = Right ()
