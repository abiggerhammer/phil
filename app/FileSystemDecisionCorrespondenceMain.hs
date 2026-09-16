module Main (main) where

import qualified FileSystemKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  let checks =
        [ ("read path mismatch rejects first", isReadPathMismatch $ readDecision False False False Kernel.ObservedReadSuccess False False False)
        , ("negative limit rejects before authority", isReadNegativeLimit $ readDecision True False False Kernel.ObservedReadSuccess False False False)
        , ("read authority rejection precedes outcome", isReadAuthorityRejected $ readDecision True True False Kernel.ObservedReadSuccess False False False)
        , ("successful read requires binding", isReadSuccessMissingBinding $ readDecision True True True Kernel.ObservedReadSuccess False True True)
        , ("successful read checks content before bound", isReadSuccessContentMismatch $ readDecision True True True Kernel.ObservedReadSuccess True False False)
        , ("oversized successful read rejects", isReadSuccessExceedsLimit $ readDecision True True True Kernel.ObservedReadSuccess True True False)
        , ("bounded exact read accepts", isReadAccepted $ readDecision True True True Kernel.ObservedReadSuccess True True True)
        , ("TooLarge requires binding", isReadTooLargeMismatch $ readDecision True True True Kernel.ObservedReadTooLarge False False False)
        , ("TooLarge rejects within-limit binding", isReadTooLargeMismatch $ readDecision True True True Kernel.ObservedReadTooLarge True False True)
        , ("TooLarge accepts oversized binding", isReadAccepted $ readDecision True True True Kernel.ObservedReadTooLarge True False False)
        , ("NotFound accepts absent binding", isReadAccepted $ readDecision True True True Kernel.ObservedReadNotFound False False False)
        , ("NotFound rejects present binding", isReadNotFoundMismatch $ readDecision True True True Kernel.ObservedReadNotFound True False False)
        , ("portable negative accepts after preconditions", isReadAccepted $ readDecision True True True Kernel.ObservedReadPortableNegative True False False)
        , ("replace path mismatch rejects first", isReplacePathMismatch $ Kernel.decideFileSystemReplaceByFacts False False)
        , ("replace authority rejection follows path", isReplaceAuthorityRejected $ Kernel.decideFileSystemReplaceByFacts True False)
        , ("authorized matching replace accepts", isReplaceAccepted $ Kernel.decideFileSystemReplaceByFacts True True)
        , ("successful replace installs binding", Kernel.replaceShouldInstallBinding True)
        , ("failed replace preserves prior state", not (Kernel.replaceShouldInstallBinding False))
        ]
  mapM_ report checks
  if all snd checks then pure () else exitFailure
  where
    report (label, True) = putStrLn ("PASS: FileSystem kernel " <> label)
    report (label, False) = putStrLn ("FAIL: FileSystem kernel " <> label)

readDecision
  :: Bool
  -> Bool
  -> Bool
  -> Kernel.FileSystemObservedReadKind
  -> Bool
  -> Bool
  -> Bool
  -> Kernel.FileSystemReadDecision
readDecision = Kernel.decideFileSystemReadByFacts

isReadAccepted :: Kernel.FileSystemReadDecision -> Bool
isReadAccepted decision = case decision of
  Kernel.FileSystemReadAccepted -> True
  _ -> False

isReadPathMismatch :: Kernel.FileSystemReadDecision -> Bool
isReadPathMismatch decision = case decision of
  Kernel.FileSystemReadPathOccurrenceMismatch -> True
  _ -> False

isReadNegativeLimit :: Kernel.FileSystemReadDecision -> Bool
isReadNegativeLimit decision = case decision of
  Kernel.FileSystemReadNegativeLimit -> True
  _ -> False

isReadAuthorityRejected :: Kernel.FileSystemReadDecision -> Bool
isReadAuthorityRejected decision = case decision of
  Kernel.FileSystemReadAuthorityRejected -> True
  _ -> False

isReadSuccessMissingBinding :: Kernel.FileSystemReadDecision -> Bool
isReadSuccessMissingBinding decision = case decision of
  Kernel.FileSystemReadSuccessMissingBinding -> True
  _ -> False

isReadSuccessContentMismatch :: Kernel.FileSystemReadDecision -> Bool
isReadSuccessContentMismatch decision = case decision of
  Kernel.FileSystemReadSuccessContentMismatch -> True
  _ -> False

isReadSuccessExceedsLimit :: Kernel.FileSystemReadDecision -> Bool
isReadSuccessExceedsLimit decision = case decision of
  Kernel.FileSystemReadSuccessExceedsLimit -> True
  _ -> False

isReadTooLargeMismatch :: Kernel.FileSystemReadDecision -> Bool
isReadTooLargeMismatch decision = case decision of
  Kernel.FileSystemReadTooLargeMismatch -> True
  _ -> False

isReadNotFoundMismatch :: Kernel.FileSystemReadDecision -> Bool
isReadNotFoundMismatch decision = case decision of
  Kernel.FileSystemReadNotFoundMismatch -> True
  _ -> False

isReplaceAccepted :: Kernel.FileSystemReplaceDecision -> Bool
isReplaceAccepted decision = case decision of
  Kernel.FileSystemReplaceAccepted -> True
  _ -> False

isReplacePathMismatch :: Kernel.FileSystemReplaceDecision -> Bool
isReplacePathMismatch decision = case decision of
  Kernel.FileSystemReplacePathOccurrenceMismatch -> True
  _ -> False

isReplaceAuthorityRejected :: Kernel.FileSystemReplaceDecision -> Bool
isReplaceAuthorityRejected decision = case decision of
  Kernel.FileSystemReplaceAuthorityRejected -> True
  _ -> False
