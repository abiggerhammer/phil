{-# LANGUAGE OverloadedStrings #-}

module Phil.IO.Console
  ( ConsoleOccurrenceKey (..)
  , ConsoleProviderKind (..)
  , ConsoleProviderOccurrence
  , consoleProviderOccurrenceKey
  , consoleProviderKind
  , consoleProviderInterface
  , ConsoleEnvironment (..)
  , standardConsoleEnvironment
  , consoleInputOccurrence
  , consoleOutputOccurrence
  , ConsoleOperation (..)
  , ConsoleOperationContract (..)
  , consoleOperationContract
  , consoleOperationEffect
  , defaultConsoleAuthorityMode
  , makeConsoleAuthorityCapability
  , defaultConsoleAuthorityCapability
  , ConsoleFailure (..)
  , ConsoleReadOutcome (..)
  , CheckedConsoleRead (..)
  , checkConsoleReadLine
  , ConsoleWriteOutcome (..)
  , CheckedConsoleWrite (..)
  , checkConsoleWrite
  , ConsoleFlushOutcome (..)
  , CheckedConsoleFlush (..)
  , checkConsoleFlush
  , ConsoleCheckError (..)
  ) where

import qualified ConsoleImplementationKernel as Kernel
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Numeric.Natural (Natural)
import Phil.Core.Authority
  ( AuthorityCapability (..)
  , AuthorityCheckError
  , AuthorityContractKey (..)
  , AuthorityExerciseSource
  , AuthorityOperationKey (..)
  , AuthorityRequirement (..)
  , AuthorityState
  , AuthoritySubjectKey (..)
  , CapabilityOccurrenceKey
  , CheckedAuthorityExercise
  , checkAuthorityExercise
  )
import Phil.Core.Callable (SemanticEffect (..))
import Phil.Core.Static (InterfaceRevision (..))
import Phil.Core.Syntax (Mode (..))

newtype ConsoleOccurrenceKey = ConsoleOccurrenceKey
  { unConsoleOccurrenceKey :: Text
  }
  deriving (Eq, Ord, Show)

data ConsoleProviderKind
  = ConsoleInputProvider
  | ConsoleOutputProvider
  deriving (Eq, Ord, Show)

-- | One exact console-provider occurrence.  The constructor stays private so
-- the provider kind and interface revision cannot disagree.
data ConsoleProviderOccurrence = ConsoleProviderOccurrence
  { consoleProviderOccurrenceKey :: ConsoleOccurrenceKey
  , consoleProviderKind :: ConsoleProviderKind
  , consoleProviderInterface :: InterfaceRevision
  }
  deriving (Eq, Ord, Show)

-- | The standard environment names three ordinary provider occurrences.  This
-- value grants no authority by itself; callers must still possess an exact
-- authority capability for the selected occurrence and operation.
data ConsoleEnvironment = ConsoleEnvironment
  { consoleEnvironmentStdin :: ConsoleProviderOccurrence
  , consoleEnvironmentStdout :: ConsoleProviderOccurrence
  , consoleEnvironmentStderr :: ConsoleProviderOccurrence
  }
  deriving (Eq, Ord, Show)

standardConsoleEnvironment :: ConsoleEnvironment
standardConsoleEnvironment = ConsoleEnvironment
  { consoleEnvironmentStdin =
      checkedOccurrence ConsoleInputProvider (ConsoleOccurrenceKey "standard.stdin")
  , consoleEnvironmentStdout =
      checkedOccurrence ConsoleOutputProvider (ConsoleOccurrenceKey "standard.stdout")
  , consoleEnvironmentStderr =
      checkedOccurrence ConsoleOutputProvider (ConsoleOccurrenceKey "standard.stderr")
  }

consoleInputOccurrence
  :: Text
  -> Either ConsoleCheckError ConsoleProviderOccurrence
consoleInputOccurrence = makeOccurrence ConsoleInputProvider

consoleOutputOccurrence
  :: Text
  -> Either ConsoleCheckError ConsoleProviderOccurrence
consoleOutputOccurrence = makeOccurrence ConsoleOutputProvider

makeOccurrence
  :: ConsoleProviderKind
  -> Text
  -> Either ConsoleCheckError ConsoleProviderOccurrence
makeOccurrence kind raw
  | Text.null raw = Left EmptyConsoleOccurrenceKey
  | otherwise =
      case Kernel.decideConsoleOccurrenceByFacts (Text.null raw) of
        Kernel.ConsoleOccurrenceAccepted ->
          Right (checkedOccurrence kind (ConsoleOccurrenceKey raw))
        Kernel.ConsoleOccurrenceEmpty ->
          Left (ConsoleOccurrenceKernelDisagreement kind raw)

checkedOccurrence :: ConsoleProviderKind -> ConsoleOccurrenceKey -> ConsoleProviderOccurrence
checkedOccurrence kind key = ConsoleProviderOccurrence
  { consoleProviderOccurrenceKey = key
  , consoleProviderKind = kind
  , consoleProviderInterface = case kind of
      ConsoleInputProvider -> InterfaceRevision "phil.console.input.interface.v1"
      ConsoleOutputProvider -> InterfaceRevision "phil.console.output.interface.v1"
  }

data ConsoleOperation
  = ConsoleReadLineOp
  | ConsoleWriteOp
  | ConsoleFlushOp
  deriving (Eq, Ord, Show)

data ConsoleOperationContract = ConsoleOperationContract
  { consoleContractOccurrence :: ConsoleProviderOccurrence
  , consoleContractOperation :: ConsoleOperation
  , consoleContractEffect :: SemanticEffect
  , consoleContractAuthority :: AuthorityRequirement
  }
  deriving (Eq, Ord, Show)

consoleOperationContract
  :: ConsoleProviderOccurrence
  -> ConsoleOperation
  -> Either ConsoleCheckError ConsoleOperationContract
consoleOperationContract occurrence operation = do
  checkOperationKind occurrence operation
  Right ConsoleOperationContract
    { consoleContractOccurrence = occurrence
    , consoleContractOperation = operation
    , consoleContractEffect = consoleOperationEffect occurrence operation
    , consoleContractAuthority = AuthorityRequirement
        { requiredAuthorityContract = authorityContractFor occurrence
        , requiredAuthoritySubject = authoritySubjectFor occurrence
        , requiredAuthorityOperation = authorityOperationFor operation
        }
    }

-- | Console effects are indexed by the exact semantic occurrence.  Equal
-- operation names on stdout and stderr therefore remain distinct effects.
consoleOperationEffect :: ConsoleProviderOccurrence -> ConsoleOperation -> SemanticEffect
consoleOperationEffect occurrence operation = SemanticEffect
  ("phil.console.effect.v1:"
    <> canonicalAtom (unConsoleOccurrenceKey (consoleProviderOccurrenceKey occurrence))
    <> ":"
    <> operationName operation)

-- | Restricted ownership is the default.  Input is linear because concurrent
-- stream owners change input-consumption meaning; output is affine unless the
-- architecture explicitly grants an unrestricted authority capability.
defaultConsoleAuthorityMode :: ConsoleProviderOccurrence -> Mode
defaultConsoleAuthorityMode occurrence = case consoleProviderKind occurrence of
  ConsoleInputProvider -> Linear
  ConsoleOutputProvider -> Affine

makeConsoleAuthorityCapability
  :: CapabilityOccurrenceKey
  -> Mode
  -> ConsoleProviderOccurrence
  -> Set ConsoleOperation
  -> Either ConsoleCheckError AuthorityCapability
makeConsoleAuthorityCapability capabilityKey mode occurrence operations = do
  mapM_ (checkOperationKind occurrence) (Set.toAscList operations)
  Right AuthorityCapability
    { authorityCapabilityOccurrence = capabilityKey
    , authorityCapabilityContract = authorityContractFor occurrence
    , authorityCapabilitySubject = authoritySubjectFor occurrence
    , authorityCapabilityMode = mode
    , authorityCapabilityOperations = Set.map authorityOperationFor operations
    }

defaultConsoleAuthorityCapability
  :: CapabilityOccurrenceKey
  -> ConsoleProviderOccurrence
  -> Either ConsoleCheckError AuthorityCapability
defaultConsoleAuthorityCapability capabilityKey occurrence =
  makeConsoleAuthorityCapability
    capabilityKey
    (defaultConsoleAuthorityMode occurrence)
    occurrence
    (operationsForKind (consoleProviderKind occurrence))

operationsForKind :: ConsoleProviderKind -> Set ConsoleOperation
operationsForKind kind = case kind of
  ConsoleInputProvider -> Set.singleton ConsoleReadLineOp
  ConsoleOutputProvider -> Set.fromList [ConsoleWriteOp, ConsoleFlushOp]

authorityContractFor :: ConsoleProviderOccurrence -> AuthorityContractKey
authorityContractFor occurrence = case consoleProviderKind occurrence of
  ConsoleInputProvider -> AuthorityContractKey "phil.console.input.authority.v1"
  ConsoleOutputProvider -> AuthorityContractKey "phil.console.output.authority.v1"

authoritySubjectFor :: ConsoleProviderOccurrence -> AuthoritySubjectKey
authoritySubjectFor occurrence = AuthoritySubjectKey
  ("phil.console.subject.v1:"
    <> canonicalAtom (unConsoleOccurrenceKey (consoleProviderOccurrenceKey occurrence)))

authorityOperationFor :: ConsoleOperation -> AuthorityOperationKey
authorityOperationFor = AuthorityOperationKey . operationName

operationName :: ConsoleOperation -> Text
operationName operation = case operation of
  ConsoleReadLineOp -> "read_line"
  ConsoleWriteOp -> "write"
  ConsoleFlushOp -> "flush"

checkOperationKind
  :: ConsoleProviderOccurrence
  -> ConsoleOperation
  -> Either ConsoleCheckError ()
checkOperationKind occurrence operation =
  case (consoleProviderKind occurrence, operation) of
    (ConsoleInputProvider, ConsoleReadLineOp) -> requireKernelOperation
    (ConsoleOutputProvider, ConsoleWriteOp) -> requireKernelOperation
    (ConsoleOutputProvider, ConsoleFlushOp) -> requireKernelOperation
    _ -> Left (ConsoleOperationKindMismatch
      (consoleProviderOccurrenceKey occurrence)
      (consoleProviderKind occurrence)
      operation)
  where
    requireKernelOperation =
      case Kernel.decideConsoleOperationByFacts
          (kernelOperationAllowed occurrence operation) of
        Kernel.ConsoleOperationAccepted -> Right ()
        Kernel.ConsoleOperationKindMismatch ->
          Left (ConsoleOperationKernelDisagreement
            (consoleProviderOccurrenceKey occurrence)
            (consoleProviderKind occurrence)
            operation)

kernelOperationAllowed
  :: ConsoleProviderOccurrence
  -> ConsoleOperation
  -> Bool
kernelOperationAllowed occurrence operation =
  case (consoleProviderKind occurrence, operation) of
    (ConsoleInputProvider, ConsoleReadLineOp) -> True
    (ConsoleOutputProvider, ConsoleWriteOp) -> True
    (ConsoleOutputProvider, ConsoleFlushOp) -> True
    _ -> False

data ConsoleFailure
  = ConsoleDenied
  | ConsoleTooLarge
  | ConsoleExhausted
  | ConsoleInvalid
  | ConsoleUnsupported
  | ConsoleUnavailable
  | ConsoleOther Text
  deriving (Eq, Ord, Show)

data ConsoleReadOutcome
  = ConsoleLine Text
  | ConsoleEndOfInput
  | ConsoleReadFailed ConsoleFailure
  deriving (Eq, Ord, Show)

data CheckedConsoleRead = CheckedConsoleRead
  { checkedConsoleReadOccurrence :: ConsoleProviderOccurrence
  , checkedConsoleReadLimit :: Natural
  , checkedConsoleReadEffect :: SemanticEffect
  , checkedConsoleReadAuthority :: CheckedAuthorityExercise
  , checkedConsoleReadOutcome :: ConsoleReadOutcome
  }
  deriving (Eq, Ord, Show)

checkConsoleReadLine
  :: ConsoleProviderOccurrence
  -> Natural
  -> AuthorityExerciseSource
  -> AuthorityState
  -> ConsoleReadOutcome
  -> Either ConsoleCheckError CheckedConsoleRead
checkConsoleReadLine occurrence limit source authorityState outcome = do
  contract <- consoleOperationContract occurrence ConsoleReadLineOp
  checkedAuthority <- mapLeft ConsoleAuthorityError $
    checkAuthorityExercise (consoleContractAuthority contract) source authorityState
  lineWithinLimit <- case outcome of
    ConsoleLine line ->
      let actual = fromIntegral (Text.length line)
      in if actual <= limit
          then Right True
          else Left (ConsoleReadLineExceedsLimit limit actual)
    ConsoleEndOfInput -> Right True
    ConsoleReadFailed _ -> Right True
  let observedKind = case outcome of
        ConsoleLine _ -> Kernel.ObservedConsoleLine
        ConsoleEndOfInput -> Kernel.ObservedConsoleEndOfInput
        ConsoleReadFailed _ -> Kernel.ObservedConsoleReadFailure
  case Kernel.decideConsoleReadByFacts
      (kernelOperationAllowed occurrence ConsoleReadLineOp)
      True
      observedKind
      lineWithinLimit of
    Kernel.ConsoleReadAccepted -> Right ()
    _ -> Left (ConsoleReadKernelDisagreement
      (consoleProviderOccurrenceKey occurrence))
  Right CheckedConsoleRead
    { checkedConsoleReadOccurrence = occurrence
    , checkedConsoleReadLimit = limit
    , checkedConsoleReadEffect = consoleContractEffect contract
    , checkedConsoleReadAuthority = checkedAuthority
    , checkedConsoleReadOutcome = outcome
    }

data ConsoleWriteOutcome
  = ConsoleWriteSucceeded
  | ConsoleWriteFailed ConsoleFailure Natural
  deriving (Eq, Ord, Show)

data CheckedConsoleWrite = CheckedConsoleWrite
  { checkedConsoleWriteOccurrence :: ConsoleProviderOccurrence
  , checkedConsoleWriteEffect :: SemanticEffect
  , checkedConsoleWriteAuthority :: CheckedAuthorityExercise
  , checkedConsoleWriteRequestedText :: Text
  , checkedConsoleWriteOutcome :: ConsoleWriteOutcome
  , checkedConsoleWriteObservablePrefixLength :: Natural
  , checkedConsoleWriteObservablePrefix :: Text
  }
  deriving (Eq, Ord, Show)

checkConsoleWrite
  :: ConsoleProviderOccurrence
  -> AuthorityExerciseSource
  -> AuthorityState
  -> Text
  -> ConsoleWriteOutcome
  -> Either ConsoleCheckError CheckedConsoleWrite
checkConsoleWrite occurrence source authorityState requested outcome = do
  contract <- consoleOperationContract occurrence ConsoleWriteOp
  checkedAuthority <- mapLeft ConsoleAuthorityError $
    checkAuthorityExercise (consoleContractAuthority contract) source authorityState
  let requestedLength = fromIntegral (Text.length requested)
  let observedSuccess = case outcome of
        ConsoleWriteSucceeded -> True
        ConsoleWriteFailed _ _ -> False
  (observableLength, progressWithinRequest) <- case outcome of
    ConsoleWriteSucceeded -> Right (requestedLength, True)
    ConsoleWriteFailed _ prefixLength
      | prefixLength <= requestedLength -> Right (prefixLength, True)
      | otherwise -> Left (ConsoleWriteProgressOutOfRange requestedLength prefixLength)
  let kernelUsesFullRequest =
        Kernel.consoleWriteUsesFullRequested observedSuccess
      nativeUsesFullRequest = case outcome of
        ConsoleWriteSucceeded -> True
        ConsoleWriteFailed _ _ -> False
  if kernelUsesFullRequest == nativeUsesFullRequest
    then Right ()
    else Left (ConsoleWriteKernelDisagreement
      (consoleProviderOccurrenceKey occurrence))
  case Kernel.decideConsoleWriteByFacts
      (kernelOperationAllowed occurrence ConsoleWriteOp)
      True
      observedSuccess
      progressWithinRequest of
    Kernel.ConsoleWriteAccepted -> Right ()
    _ -> Left (ConsoleWriteKernelDisagreement
      (consoleProviderOccurrenceKey occurrence))
  let observablePrefix = Text.take (fromIntegral observableLength) requested
  Right CheckedConsoleWrite
    { checkedConsoleWriteOccurrence = occurrence
    , checkedConsoleWriteEffect = consoleContractEffect contract
    , checkedConsoleWriteAuthority = checkedAuthority
    , checkedConsoleWriteRequestedText = requested
    , checkedConsoleWriteOutcome = outcome
    , checkedConsoleWriteObservablePrefixLength = observableLength
    , checkedConsoleWriteObservablePrefix = observablePrefix
    }

data ConsoleFlushOutcome
  = ConsoleFlushSucceeded
  | ConsoleFlushFailed ConsoleFailure
  deriving (Eq, Ord, Show)

data CheckedConsoleFlush = CheckedConsoleFlush
  { checkedConsoleFlushOccurrence :: ConsoleProviderOccurrence
  , checkedConsoleFlushEffect :: SemanticEffect
  , checkedConsoleFlushAuthority :: CheckedAuthorityExercise
  , checkedConsoleFlushOutcome :: ConsoleFlushOutcome
  }
  deriving (Eq, Ord, Show)

checkConsoleFlush
  :: ConsoleProviderOccurrence
  -> AuthorityExerciseSource
  -> AuthorityState
  -> ConsoleFlushOutcome
  -> Either ConsoleCheckError CheckedConsoleFlush
checkConsoleFlush occurrence source authorityState outcome = do
  contract <- consoleOperationContract occurrence ConsoleFlushOp
  checkedAuthority <- mapLeft ConsoleAuthorityError $
    checkAuthorityExercise (consoleContractAuthority contract) source authorityState
  case Kernel.decideConsoleFlushByFacts
      (kernelOperationAllowed occurrence ConsoleFlushOp)
      True of
    Kernel.ConsoleFlushAccepted -> Right ()
    _ -> Left (ConsoleFlushKernelDisagreement
      (consoleProviderOccurrenceKey occurrence))
  Right CheckedConsoleFlush
    { checkedConsoleFlushOccurrence = occurrence
    , checkedConsoleFlushEffect = consoleContractEffect contract
    , checkedConsoleFlushAuthority = checkedAuthority
    , checkedConsoleFlushOutcome = outcome
    }

data ConsoleCheckError
  = EmptyConsoleOccurrenceKey
  | ConsoleOperationKindMismatch ConsoleOccurrenceKey ConsoleProviderKind ConsoleOperation
  | ConsoleAuthorityError AuthorityCheckError
  | ConsoleReadLineExceedsLimit Natural Natural
  | ConsoleWriteProgressOutOfRange Natural Natural
  | ConsoleOccurrenceKernelDisagreement ConsoleProviderKind Text
  | ConsoleOperationKernelDisagreement ConsoleOccurrenceKey ConsoleProviderKind ConsoleOperation
  | ConsoleReadKernelDisagreement ConsoleOccurrenceKey
  | ConsoleWriteKernelDisagreement ConsoleOccurrenceKey
  | ConsoleFlushKernelDisagreement ConsoleOccurrenceKey
  deriving (Eq, Ord, Show)

canonicalAtom :: Text -> Text
canonicalAtom value = Text.pack (show (Text.length value)) <> ":" <> value

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
