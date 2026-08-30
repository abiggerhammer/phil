module Phil.Core.EncodingCanonicality
  ( EncodingCanonicality (..)
  , EncodingForm (..)
  , CanonicalityError (..)
  , checkEncodingCanonicality
  ) where

import qualified BoundaryEncodingKernel as Kernel
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
  case Kernel.decideEncodingCanonicality
    (toKernelRequirement requirement)
    (toKernelForm encodingForm) of
    Kernel.EncodingCanonicalityAccepted -> Right evidence
    Kernel.NonCanonicalEncodingRejectedDecision ->
      Left (NonCanonicalEncodingRejected
        (generatedRepresentation evidence)
        (generatedOutputOwner evidence))


toKernelRequirement :: EncodingCanonicality -> Kernel.EncodingCanonicality
toKernelRequirement CanonicalityNotRequired = Kernel.CanonicalityNotRequired
toKernelRequirement CanonicalEncodingRequired = Kernel.CanonicalEncodingRequired


toKernelForm :: EncodingForm -> Kernel.EncodingForm
toKernelForm CanonicalGrammarMember = Kernel.CanonicalGrammarMember
toKernelForm NonCanonicalLegalGrammarMember = Kernel.NonCanonicalLegalGrammarMember
