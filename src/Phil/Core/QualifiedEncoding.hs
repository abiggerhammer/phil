module Phil.Core.QualifiedEncoding
  ( EncodingAdmission (..)
  , QualifiedEncoder (..)
  , GeneratedEncodingEvidence (..)
  , QualifiedEncodingError (..)
  , establishGeneratedEncoding
  ) where

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
establishGeneratedEncoding encoder requestedRepresentation expectedOwner actualOwner
  | encoderAdmission encoder /= EncodingAdmitted =
      Left (EncoderNotAdmitted (encoderImplementation encoder))
  | encoderRepresentation encoder /= requestedRepresentation =
      Left (EncodingRepresentationMismatch (encoderRepresentation encoder) requestedRepresentation)
  | expectedOwner /= actualOwner =
      Left (EncodingOutputOwnerMismatch expectedOwner actualOwner)
  | otherwise =
      Right GeneratedEncodingEvidence
        { generatedByImplementation = encoderImplementation encoder
        , generatedRepresentation = requestedRepresentation
        , generatedOutputOwner = actualOwner
        }
