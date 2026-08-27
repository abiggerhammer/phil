module Phil.Core.BoundaryRecognition
  ( RecognitionExtent (..)
  , CompleteRecognitionError (..)
  , recognizeCompleteFrame
  , rejectMalformedCompleteFrame
  ) where

import Data.Text (Text)
import Phil.Core.Context (ResourceContext)
import Phil.Core.Recognition
  ( ParsedWitness
  , PendingRawView
  , RecognitionError
  , RecognitionFailure
  , trustedRecognitionFailure
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
recognizeCompleteFrame raw valueName extent context = do
  checkCompleteExtent extent
  mapLeft UnderlyingRecognitionError
    (trustedRecognitionSuccess raw valueName context)

rejectMalformedCompleteFrame
  :: PendingRawView
  -> Text
  -> RecognitionExtent
  -> ResourceContext
  -> Either CompleteRecognitionError RecognitionFailure
rejectMalformedCompleteFrame raw detail extent context = do
  checkCompleteExtent extent
  mapLeft UnderlyingRecognitionError
    (trustedRecognitionFailure raw detail context)

checkCompleteExtent
  :: RecognitionExtent
  -> Either CompleteRecognitionError ()
checkCompleteExtent extent
  | declaredFrameBytes extent < 0 || consumedFrameBytes extent < 0 =
      Left (InvalidRecognitionExtent extent)
  | consumedFrameBytes extent < declaredFrameBytes extent =
      Left (TrailingBytesInsideFrame extent)
  | consumedFrameBytes extent > declaredFrameBytes extent =
      Left (RecognitionConsumedPastFrame extent)
  | otherwise = Right ()

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
