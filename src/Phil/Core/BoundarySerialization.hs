module Phil.Core.BoundarySerialization
  ( SerializationBasis (..)
  , SerializationCorrespondence (..)
  , BoundarySerializationError (..)
  , checkBoundarySerialization
  ) where

import qualified BoundaryEncodingKernel as Kernel
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
checkBoundarySerialization expectedRepresentation expectedSubject correspondence =
  case Kernel.decideBoundarySerializationByFacts
    (toKernelBasis (serializationBasis correspondence))
    (serializationRepresentation correspondence == expectedRepresentation)
    (serializationSubject correspondence == expectedSubject) of
    Kernel.RawMemoryLayoutRejectedDecision ->
      Left (UncheckedSerializationBasis RawMemoryLayout)
    Kernel.MatchingCStructShapeRejectedDecision ->
      Left (UncheckedSerializationBasis MatchingCStructShape)
    Kernel.SerializationRepresentationMismatchDecision ->
      Left (SerializationRepresentationMismatch
        expectedRepresentation
        (serializationRepresentation correspondence))
    Kernel.SerializationSubjectMismatchDecision ->
      Left (SerializationSubjectMismatch
        expectedSubject
        (serializationSubject correspondence))
    Kernel.BoundarySerializationDecisionAccepted -> Right ()


toKernelBasis :: SerializationBasis -> Kernel.SerializationBasis
toKernelBasis CheckedWireCorrespondence = Kernel.CheckedWireCorrespondence
toKernelBasis RawMemoryLayout = Kernel.RawMemoryLayout
toKernelBasis MatchingCStructShape = Kernel.MatchingCStructShape
