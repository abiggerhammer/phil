{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.ProcessActivation
  ( ActivationOccurrenceKey (..)
  , ActivationBindingOrigin (..)
  , ActivationBinding (..)
  , ProcessActivationContract (..)
  , RestrictedOwnerIndex
  , ProcessActivationState (..)
  , ProcessActivationError (..)
  , activateProcessState
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

type RestrictedOwnerIndex =
  Map.Map ActivationOccurrenceKey (ProcessKey, Name)

data ProcessActivationState = ProcessActivationState
  { activationProcessContexts :: Map.Map ProcessKey ResourceContext
  , activationRestrictedOwners :: RestrictedOwnerIndex
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
-- activation inputs, retain the exact global restricted-owner partition, and
-- only then perform the exactly-once root activation transition.
activateProcessState
  :: ProcessNetwork
  -> [ProcessActivationContract]
  -> Either ProcessActivationError (ProcessNetwork, ProcessActivationState)
activateProcessState network contracts = do
  contractMap <- normalizeActivationContracts network contracts
  (contexts, restrictedOwners) <-
    Map.foldlWithKey' buildProcessContext
      (Right (Map.empty, Map.empty))
      contractMap
  activated <- mapLeft ProcessNetworkActivationError (activateRootProcesses network)
  pure
    ( activated
    , ProcessActivationState
        { activationProcessContexts = contexts
        , activationRestrictedOwners = restrictedOwners
        }
    )

-- | Backwards-compatible CONC-003 view for callers that only need the checked
-- per-process resource contexts. CONC-005 and later ownership-sensitive slices
-- should use 'activateProcessState' so exact occurrence identity is retained.
activateProcessContexts
  :: ProcessNetwork
  -> [ProcessActivationContract]
  -> Either ProcessActivationError (ProcessNetwork, Map.Map ProcessKey ResourceContext)
activateProcessContexts network contracts = do
  (activated, state) <- activateProcessState network contracts
  pure (activated, activationProcessContexts state)

normalizeActivationContracts
  :: ProcessNetwork
  -> [ProcessActivationContract]
  -> Either ProcessActivationError (Map.Map ProcessKey ProcessActivationContract)
normalizeActivationContracts network contracts = do
  normalized <- foldl' insertContract (Right Map.empty) contracts
  let missingProcesses = populationKeys `Set.difference` Map.keysSet normalized
  case Set.lookupMin missingProcesses of
    Just processKey -> Left (MissingActivationContract processKey)
    Nothing -> Right normalized
  where
    populationKeys = Map.keysSet (processNetworkPopulation network)

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
      (Map.Map ProcessKey ResourceContext, RestrictedOwnerIndex)
  -> ProcessKey
  -> ProcessActivationContract
  -> Either
      ProcessActivationError
      (Map.Map ProcessKey ResourceContext, RestrictedOwnerIndex)
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
      (ResourceContext, RestrictedOwnerIndex)
  -> ActivationBinding
  -> Either
      ProcessActivationError
      (ResourceContext, RestrictedOwnerIndex)
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
  -> RestrictedOwnerIndex
  -> Either ProcessActivationError RestrictedOwnerIndex
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
