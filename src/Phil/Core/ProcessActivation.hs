{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProcessActivation
  ( ActivationOccurrenceKey (..)
  , ActivationBindingOrigin (..)
  , ActivationBinding (..)
  , ProcessActivationContract (..)
  , ProcessActivationError (..)
  , activateProcessContexts
  ) where

import Data.List (foldl')
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.CheckedBindingMode
  ( BindingOrigin (EntryValueBinding)
  , CheckedBindingModeError
  , CheckedTypeMode (..)
  , insertCheckedBinding
  )
import Phil.Core.Context
  ( CheckError
  , ResourceContext
  , emptyContext
  , startSharedLoan
  )
import Phil.Core.Process
  ( ProcessKey
  , ProcessNetwork (..)
  , ProcessNetworkError
  , activateRootProcesses
  )
import Phil.Core.Syntax (Mode (..), Name)

newtype ActivationOccurrenceKey = ActivationOccurrenceKey
  { unActivationOccurrenceKey :: Text
  }
  deriving (Eq, Ord, Show)

data ActivationBindingOrigin
  = TargetParameterOrigin Text
  | RootEntryOrigin Text
  | ProtocolEndpointOrigin Text
  | ExplicitAuthorityOrigin Text
  | InitializationTransitionOrigin Text
  | AmbientActivationOrigin Text
  deriving (Eq, Ord, Show)

data ActivationBinding = ActivationBinding
  { activationOccurrenceKey :: ActivationOccurrenceKey
  , activationLocalName :: Name
  , activationCheckedTypeMode :: CheckedTypeMode
  , activationBindingOrigin :: ActivationBindingOrigin
  , activationStartsSharedLoan :: Bool
  }
  deriving (Eq, Show)

data ProcessActivationContract = ProcessActivationContract
  { activationContractProcess :: ProcessKey
  , activationContractBindings :: [ActivationBinding]
  }
  deriving (Eq, Show)

data ProcessActivationError
  = DuplicateActivationContract ProcessKey
  | UnknownActivationProcess ProcessKey
  | MissingActivationContract ProcessKey
  | AmbientActivationBinding ProcessKey Name Text
  | DuplicateRestrictedActivationOccurrence
      ActivationOccurrenceKey
      ProcessKey
      Name
      ProcessKey
      Name
  | ActivationBindingModeError ProcessKey CheckedBindingModeError
  | ActivationResourceError ProcessKey CheckError
  | ProcessNetworkActivationError ProcessNetworkError
  deriving (Eq, Show)

-- | Close every initial process context from explicit architecture-owned
-- activation inputs, prove global restricted ownership is a partition, and
-- only then perform the exactly-once root activation transition.
activateProcessContexts
  :: ProcessNetwork
  -> [ProcessActivationContract]
  -> Either ProcessActivationError (ProcessNetwork, Map.Map ProcessKey ResourceContext)
activateProcessContexts network contracts = do
  contractMap <- normalizeActivationContracts network contracts
  (contexts, _) <-
    Map.foldlWithKey' buildProcessContext
      (Right (Map.empty, Map.empty))
      contractMap
  activated <- mapLeft ProcessNetworkActivationError (activateRootProcesses network)
  pure (activated, contexts)

normalizeActivationContracts
  :: ProcessNetwork
  -> [ProcessActivationContract]
  -> Either ProcessActivationError (Map.Map ProcessKey ProcessActivationContract)
normalizeActivationContracts network contracts = do
  normalized <- foldl' insertContract (Right Map.empty) contracts
  case Set.lookupMin missingProcesses of
    Just processKey -> Left (MissingActivationContract processKey)
    Nothing -> Right normalized
  where
    populationKeys = Map.keysSet (processNetworkPopulation network)
    missingProcesses = populationKeys `Set.difference` Map.keysSet normalized

    insertContract accumulated contract = do
      current <- accumulated
      let processKey = activationContractProcess contract
      if not (Map.member processKey (processNetworkPopulation network))
        then Left (UnknownActivationProcess processKey)
        else if Map.member processKey current
          then Left (DuplicateActivationContract processKey)
          else Right (Map.insert processKey contract current)

buildProcessContext
  :: Either
      ProcessActivationError
      ( Map.Map ProcessKey ResourceContext
      , Map.Map ActivationOccurrenceKey (ProcessKey, Name)
      )
  -> ProcessKey
  -> ProcessActivationContract
  -> Either
      ProcessActivationError
      ( Map.Map ProcessKey ResourceContext
      , Map.Map ActivationOccurrenceKey (ProcessKey, Name)
      )
buildProcessContext accumulated processKey contract = do
  (contexts, restrictedOwners) <- accumulated
  (context, nextOwners) <-
    foldl' (insertActivationBinding processKey)
      (Right (emptyContext, restrictedOwners))
      (activationContractBindings contract)
  pure (Map.insert processKey context contexts, nextOwners)

insertActivationBinding
  :: ProcessKey
  -> Either
      ProcessActivationError
      (ResourceContext, Map.Map ActivationOccurrenceKey (ProcessKey, Name))
  -> ActivationBinding
  -> Either
      ProcessActivationError
      (ResourceContext, Map.Map ActivationOccurrenceKey (ProcessKey, Name))
insertActivationBinding processKey accumulated binding = do
  (context, restrictedOwners) <- accumulated
  ensureExplicitOrigin processKey binding
  nextOwners <- reserveRestrictedOwner processKey binding restrictedOwners
  nextContext <- mapLeft (ActivationBindingModeError processKey) $
    insertCheckedBinding
      EntryValueBinding
      checked
      (checkedBindingMode checked)
      (activationLocalName binding)
      (checkedBindingType checked)
      context
  loanContext <-
    if activationStartsSharedLoan binding
      then mapLeft (ActivationResourceError processKey) $
        startSharedLoan (activationLocalName binding) nextContext
      else Right nextContext
  pure (loanContext, nextOwners)
  where
    checked = activationCheckedTypeMode binding

ensureExplicitOrigin
  :: ProcessKey
  -> ActivationBinding
  -> Either ProcessActivationError ()
ensureExplicitOrigin processKey binding =
  case activationBindingOrigin binding of
    AmbientActivationOrigin detail ->
      Left (AmbientActivationBinding processKey (activationLocalName binding) detail)
    _ -> Right ()

reserveRestrictedOwner
  :: ProcessKey
  -> ActivationBinding
  -> Map.Map ActivationOccurrenceKey (ProcessKey, Name)
  -> Either ProcessActivationError (Map.Map ActivationOccurrenceKey (ProcessKey, Name))
reserveRestrictedOwner processKey binding owners =
  case checkedBindingMode (activationCheckedTypeMode binding) of
    Unrestricted -> Right owners
    Affine -> reserve
    Linear -> reserve
  where
    occurrenceKey = activationOccurrenceKey binding
    localName = activationLocalName binding
    reserve =
      case Map.lookup occurrenceKey owners of
        Just (firstProcess, firstName) ->
          Left (DuplicateRestrictedActivationOccurrence
            occurrenceKey firstProcess firstName processKey localName)
        Nothing -> Right (Map.insert occurrenceKey (processKey, localName) owners)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
