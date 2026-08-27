module Phil.Core.EncodingCanonicality
  ( EncodingCanonicality (..)
  , EncodingForm (..)
  , CanonicalityError (..)
  , checkEncodingCanonicality
  ) where

import Phil.Core.BoundaryMapping (BoundaryRepresentationId)
import Phil.Core.QualifiedEncoding
  ( GeneratedEncodingEvidence
  , generatedOutputOwner
  , generatedRepresentation
  )
import Phil.Core.Syntax (Name)

data EncodingCanonicality
  = CanonicalityNotRequired
  | CanonicalEncodingRequired
  deriving (Eq, Show)

data EncodingForm
  = CanonicalGrammarMember
  | NonCanonicalLegalGrammarMember
  deriving (Eq, Show)

data CanonicalityError
  = NonCanonicalEncodingRejected BoundaryRepresentationId Name
  deriving (Eq, Show)

checkEncodingCanonicality
  :: EncodingCanonicality
  -> EncodingForm
  -> GeneratedEncodingEvidence
  -> Either CanonicalityError GeneratedEncodingEvidence
checkEncodingCanonicality requirement encodingForm evidence =
  case (requirement, encodingForm) of
    (CanonicalEncodingRequired, NonCanonicalLegalGrammarMember) ->
      Left (NonCanonicalEncodingRejected
        (generatedRepresentation evidence)
        (generatedOutputOwner evidence))
    _ -> Right evidence
