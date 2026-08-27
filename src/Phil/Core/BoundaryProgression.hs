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
establishCompleteEmission generated extent
  | intendedEmissionBytes extent < 0 || emittedBytes extent < 0 =
      Left (InvalidEmissionExtent extent)
  | emittedBytes extent < intendedEmissionBytes extent =
      Left (PartialTransportEmission extent)
  | emittedBytes extent > intendedEmissionBytes extent =
      Left (EmissionPastDeclaredFrame extent)
  | otherwise = Right (CompleteEmissionEvidence
      (generatedRepresentation generated)
      (generatedOutputOwner generated))

commitMappedReceive
  :: Name
  -> Name
  -> ParsedWitness
  -> CorrespondenceEvidence
  -> ResourceContext
  -> Either BoundaryProgressionError CommitReceiveStep
commitMappedReceive pending successor parsed correspondence context
  | parsedGrammarId parsed /= correspondenceGrammar correspondence =
      Left ReceiveMappingGrammarMismatch
  | parsedValueName parsed /= correspondenceGrammarValue correspondence =
      Left ReceiveMappingValueMismatch
  | otherwise = mapLeft UnderlyingReceiveProgressionError
      (commitReceive pending successor parsed context)

commitQualifiedSend
  :: Name
  -> Name
  -> GeneratedEncodingEvidence
  -> CompleteEmissionEvidence
  -> ResourceContext
  -> Either BoundaryProgressionError SessionStep
commitQualifiedSend endpoint successor generated emission context
  | generatedRepresentation generated /= completeEmissionRepresentation emission =
      Left (SendEmissionRepresentationMismatch
        (generatedRepresentation generated)
        (completeEmissionRepresentation emission))
  | generatedOutputOwner generated /= completeEmissionOwner emission =
      Left (SendEmissionOwnerMismatch
        (generatedOutputOwner generated)
        (completeEmissionOwner emission))
  | otherwise = mapLeft UnderlyingSendProgressionError
      (sendEndpoint endpoint successor context)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
