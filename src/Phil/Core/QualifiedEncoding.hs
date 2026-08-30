module Phil.Core.QualifiedEncoding
  ( EncodingAdmission (..)
  , QualifiedEncoder (..)
  , GeneratedEncodingEvidence (..)
  , QualifiedEncodingError (..)
  , establishGeneratedEncoding
  ) where

import qualified BoundaryEncodingKernel as Kernel
import Phil.Core.BoundaryMapping (BoundaryRepresentationId)
import Phil.Core.Syntax (Name)

data EncodingAdmission
  = EncodingAdmitted
  | EncodingNotAdmitted
  deriving (Eq, Show)

data QualifiedEncoder = QualifiedEncoder
  { encoderImplementation :: Name
  , encoderRepresentation :: BoundaryRepresentationId
  , encoderAdmission :: EncodingAdmission
  }
  deriving (Eq, Show)

data GeneratedEncodingEvidence = GeneratedEncodingEvidence
  { generatedByImplementation :: Name
  , generatedRepresentation :: BoundaryRepresentationId
  , generatedOutputOwner :: Name
  }
  deriving (Eq, Show)

data QualifiedEncodingError
  = EncoderNotAdmitted Name
  | EncodingRepresentationMismatch BoundaryRepresentationId BoundaryRepresentationId
  | EncodingOutputOwnerMismatch Name Name
  deriving (Eq, Show)

establishGeneratedEncoding
  :: QualifiedEncoder
  -> BoundaryRepresentationId
  -> Name
  -> Name
  -> Either QualifiedEncodingError GeneratedEncodingEvidence
establishGeneratedEncoding encoder requestedRepresentation expectedOwner actualOwner =
  case Kernel.decideQualifiedEncodingByFacts
    (encoderAdmission encoder == EncodingAdmitted)
    (encoderRepresentation encoder == requestedRepresentation)
    (expectedOwner == actualOwner) of
    Kernel.QualifiedEncoderNotAdmittedDecision ->
      Left (EncoderNotAdmitted (encoderImplementation encoder))
    Kernel.QualifiedEncodingRepresentationMismatchDecision ->
      Left (EncodingRepresentationMismatch
        (encoderRepresentation encoder)
        requestedRepresentation)
    Kernel.QualifiedEncodingOutputOwnerMismatchDecision ->
      Left (EncodingOutputOwnerMismatch expectedOwner actualOwner)
    Kernel.QualifiedEncodingDecisionAccepted ->
      case Kernel.planGeneratedEncoding
        (encoderImplementation encoder)
        requestedRepresentation
        actualOwner of
        Kernel.MkGeneratedEncodingPlan implementation representation owner ->
          Right GeneratedEncodingEvidence
            { generatedByImplementation = implementation
            , generatedRepresentation = representation
            , generatedOutputOwner = owner
            }
