module Phil.Core.BoundaryRecognition
  ( RecognitionExtent (..)
  , CompleteRecognitionError (..)
  , recognizeCompleteFrame
  ) where

import Phil.Core.Context (ResourceContext)
import Phil.Core.Recognition
  ( ParsedWitness
  , PendingRawView
  , RecognitionError
  , trustedRecognitionSuccess
  )
import Phil.Core.Syntax (Name)

data RecognitionExtent = RecognitionExtent
  { declaredFrameBytes :: Int
  , consumedFrameBytes :: Int
  }
  deriving (Eq, Show)

data CompleteRecognitionError
  = InvalidRecognitionExtent RecognitionExtent
  | TrailingBytesInsideFrame RecognitionExtent
  | RecognitionConsumedPastFrame RecognitionExtent
  | UnderlyingRecognitionError RecognitionError
  deriving (Eq, Show)

recognizeCompleteFrame
  :: PendingRawView
  -> Name
  -> RecognitionExtent
  -> ResourceContext
  -> Either CompleteRecognitionError ParsedWitness
recognizeCompleteFrame raw valueName extent context
  | declaredFrameBytes extent < 0 || consumedFrameBytes extent < 0 =
      Left (InvalidRecognitionExtent extent)
  | consumedFrameBytes extent < declaredFrameBytes extent =
      Left (TrailingBytesInsideFrame extent)
  | consumedFrameBytes extent > declaredFrameBytes extent =
      Left (RecognitionConsumedPastFrame extent)
  | otherwise =
      mapLeft UnderlyingRecognitionError
        (trustedRecognitionSuccess raw valueName context)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
