module Phil.Core.BoundaryProgression
  ( EmissionExtent (..)
  , CompleteEmissionEvidence
  , completeEmissionRepresentation
  , completeEmissionOwner
  , BoundaryProgressionError (..)
  , establishCompleteEmission
  , commitMappedReceive
  , commitQualifiedSend
  ) where

import qualified BoundaryProgressionKernel as Kernel
import Phil.Core.BoundaryMapping
  ( BoundaryRepresentationId
  , CorrespondenceEvidence
  , correspondenceGrammar
  , correspondenceGrammarValue
  )
import Phil.Core.Context (ResourceContext)
import Phil.Core.QualifiedEncoding
  ( GeneratedEncodingEvidence
  , generatedOutputOwner
  , generatedRepresentation
  )
import Phil.Core.Recognition
  ( CommitReceiveStep
  , ParsedWitness
  , RecognitionError
  , commitReceive
  , parsedGrammarId
  , parsedValueName
  )
import Phil.Core.Session
  ( SessionError
  , SessionStep
  , sendEndpoint
  )
import Phil.Core.Syntax (Name)

data EmissionExtent = EmissionExtent
  { intendedEmissionBytes :: Int
  , emittedBytes :: Int
  }
  deriving (Eq, Show)

data CompleteEmissionEvidence = CompleteEmissionEvidence
  BoundaryRepresentationId Name
  deriving (Eq, Show)

completeEmissionRepresentation :: CompleteEmissionEvidence -> BoundaryRepresentationId
completeEmissionRepresentation (CompleteEmissionEvidence representation _) = representation

completeEmissionOwner :: CompleteEmissionEvidence -> Name
completeEmissionOwner (CompleteEmissionEvidence _ owner) = owner

data BoundaryProgressionError
  = ReceiveMappingGrammarMismatch
  | ReceiveMappingValueMismatch
  | UnderlyingReceiveProgressionError RecognitionError
  | InvalidEmissionExtent EmissionExtent
  | PartialTransportEmission EmissionExtent
  | EmissionPastDeclaredFrame EmissionExtent
  | SendEmissionRepresentationMismatch BoundaryRepresentationId BoundaryRepresentationId
  | SendEmissionOwnerMismatch Name Name
  | UnderlyingSendProgressionError SessionError
  deriving (Eq, Show)

establishCompleteEmission
  :: GeneratedEncodingEvidence
  -> EmissionExtent
  -> Either BoundaryProgressionError CompleteEmissionEvidence
establishCompleteEmission generated extent =
  case Kernel.decideEmissionDisposition (classifyEmissionExtent extent) of
    Kernel.InvalidEmissionExtentDecision ->
      Left (InvalidEmissionExtent extent)
    Kernel.PartialEmissionDecision ->
      Left (PartialTransportEmission extent)
    Kernel.EmissionPastDeclaredFrameDecision ->
      Left (EmissionPastDeclaredFrame extent)
    Kernel.CompleteEmissionDecisionAccepted ->
      case Kernel.planCompleteEmission
        (generatedRepresentation generated)
        (generatedOutputOwner generated) of
        Kernel.MkCompleteEmissionPlan representation owner ->
          Right (CompleteEmissionEvidence representation owner)

commitMappedReceive
  :: Name
  -> Name
  -> ParsedWitness
  -> CorrespondenceEvidence
  -> ResourceContext
  -> Either BoundaryProgressionError CommitReceiveStep
commitMappedReceive pending successor parsed correspondence context =
  case Kernel.decideReceiveProgressionByFacts
    (parsedGrammarId parsed == correspondenceGrammar correspondence)
    (parsedValueName parsed == correspondenceGrammarValue correspondence)
    underlyingAccepted of
    Kernel.ReceiveMappingGrammarMismatchDecision ->
      Left ReceiveMappingGrammarMismatch
    Kernel.ReceiveMappingValueMismatchDecision ->
      Left ReceiveMappingValueMismatch
    Kernel.UnderlyingReceiveRejectedDecision ->
      mapLeft UnderlyingReceiveProgressionError underlying
    Kernel.ReceiveProgressionDecisionAccepted ->
      mapLeft UnderlyingReceiveProgressionError underlying
  where
    underlying = commitReceive pending successor parsed context
    underlyingAccepted = either (const False) (const True) underlying

commitQualifiedSend
  :: Name
  -> Name
  -> GeneratedEncodingEvidence
  -> CompleteEmissionEvidence
  -> ResourceContext
  -> Either BoundaryProgressionError SessionStep
commitQualifiedSend endpoint successor generated emission context =
  case Kernel.decideSendProgressionByFacts
    (generatedRepresentation generated == completeEmissionRepresentation emission)
    (generatedOutputOwner generated == completeEmissionOwner emission)
    underlyingAccepted of
    Kernel.SendEmissionRepresentationMismatchDecision ->
      Left (SendEmissionRepresentationMismatch
        (generatedRepresentation generated)
        (completeEmissionRepresentation emission))
    Kernel.SendEmissionOwnerMismatchDecision ->
      Left (SendEmissionOwnerMismatch
        (generatedOutputOwner generated)
        (completeEmissionOwner emission))
    Kernel.UnderlyingSendRejectedDecision ->
      mapLeft UnderlyingSendProgressionError underlying
    Kernel.SendProgressionDecisionAccepted ->
      mapLeft UnderlyingSendProgressionError underlying
  where
    underlying = sendEndpoint endpoint successor context
    underlyingAccepted = either (const False) (const True) underlying

classifyEmissionExtent :: EmissionExtent -> Kernel.EmissionDisposition
classifyEmissionExtent extent
  | intendedEmissionBytes extent < 0 || emittedBytes extent < 0 =
      Kernel.InvalidEmissionExtent
  | emittedBytes extent < intendedEmissionBytes extent =
      Kernel.PartialEmission
  | emittedBytes extent > intendedEmissionBytes extent =
      Kernel.EmissionPastDeclaredFrame
  | otherwise = Kernel.CompleteEmission

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
