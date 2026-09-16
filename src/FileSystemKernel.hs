module FileSystemKernel where

import qualified Prelude

data FileSystemObservedReadKind =
   ObservedReadSuccess
 | ObservedReadTooLarge
 | ObservedReadNotFound
 | ObservedReadPortableNegative

data FileSystemReadDecision =
   FileSystemReadAccepted
 | FileSystemReadPathOccurrenceMismatch
 | FileSystemReadNegativeLimit
 | FileSystemReadAuthorityRejected
 | FileSystemReadSuccessMissingBinding
 | FileSystemReadSuccessContentMismatch
 | FileSystemReadSuccessExceedsLimit
 | FileSystemReadTooLargeMismatch
 | FileSystemReadNotFoundMismatch

decideFileSystemReadByFacts :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
                               -> FileSystemObservedReadKind -> Prelude.Bool
                               -> Prelude.Bool -> Prelude.Bool ->
                               FileSystemReadDecision
decideFileSystemReadByFacts pathOccurrenceMatches limitNonnegative authorityAccepted observedKind bindingPresent contentMatches withinLimit =
  case pathOccurrenceMatches of {
   Prelude.True ->
    case limitNonnegative of {
     Prelude.True ->
      case authorityAccepted of {
       Prelude.True ->
        case observedKind of {
         ObservedReadSuccess ->
          case bindingPresent of {
           Prelude.True ->
            case contentMatches of {
             Prelude.True ->
              case withinLimit of {
               Prelude.True -> FileSystemReadAccepted;
               Prelude.False -> FileSystemReadSuccessExceedsLimit};
             Prelude.False -> FileSystemReadSuccessContentMismatch};
           Prelude.False -> FileSystemReadSuccessMissingBinding};
         ObservedReadTooLarge ->
          case bindingPresent of {
           Prelude.True ->
            case withinLimit of {
             Prelude.True -> FileSystemReadTooLargeMismatch;
             Prelude.False -> FileSystemReadAccepted};
           Prelude.False -> FileSystemReadTooLargeMismatch};
         ObservedReadNotFound ->
          case bindingPresent of {
           Prelude.True -> FileSystemReadNotFoundMismatch;
           Prelude.False -> FileSystemReadAccepted};
         ObservedReadPortableNegative -> FileSystemReadAccepted};
       Prelude.False -> FileSystemReadAuthorityRejected};
     Prelude.False -> FileSystemReadNegativeLimit};
   Prelude.False -> FileSystemReadPathOccurrenceMismatch}

data FileSystemReplaceDecision =
   FileSystemReplaceAccepted
 | FileSystemReplacePathOccurrenceMismatch
 | FileSystemReplaceAuthorityRejected

decideFileSystemReplaceByFacts :: Prelude.Bool -> Prelude.Bool ->
                                  FileSystemReplaceDecision
decideFileSystemReplaceByFacts pathOccurrenceMatches authorityAccepted =
  case pathOccurrenceMatches of {
   Prelude.True ->
    case authorityAccepted of {
     Prelude.True -> FileSystemReplaceAccepted;
     Prelude.False -> FileSystemReplaceAuthorityRejected};
   Prelude.False -> FileSystemReplacePathOccurrenceMismatch}

replaceShouldInstallBinding :: Prelude.Bool -> Prelude.Bool
replaceShouldInstallBinding observedSuccess =
  observedSuccess

