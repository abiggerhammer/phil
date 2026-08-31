{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Protocol
  ( ProtocolInstanceRevision (..)
  , ProtocolRoleKey (..)
  , ProtocolEndpointBinding (..)
  , ProtocolEndpointContract (..)
  , ProtocolContext (..)
  , ProtocolActionRequest (..)
  , CheckedProtocolStep (..)
  , ProtocolCheckError (..)
  , emptyProtocolContext
  , insertProtocolEndpoint
  , lookupProtocolEndpoint
  , protocolEndpointContract
  , checkProtocolEndpointSubstitution
  , checkProtocolEndpointJoin
  , checkProtocolAction
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified ProtocolIdentityKernel as Kernel
import qualified ProtocolProgressionGuardKernel as ProgressionKernel
import Phil.Core.Context
  ( CheckError
  , ResourceContext (..)
  , emptyContext
  , insertBinding
  )
import Phil.Core.Session
  ( SessionError
  , SessionStep (..)
  , closeEndpoint
  , offerEndpoint
  , receiveEndpoint
  , selectEndpoint
  , sendEndpoint
  )
import Phil.Core.Syntax
  ( Mode (Linear)
  , Name
  , Outcome
  , Session
  , Ty (..)
  )

-- | Exact static identity of one instantiated protocol contract.  This is
-- deliberately distinct from the local session shape: equal local sessions do
-- not imply equal protocol instances.
newtype ProtocolInstanceRevision = ProtocolInstanceRevision
  { unProtocolInstanceRevision :: Text
  }
  deriving (Eq, Ord, Show)

-- | Exact role identity inside one protocol instance.
newtype ProtocolRoleKey = ProtocolRoleKey
  { unProtocolRoleKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Provenance carried beside one live linear endpoint occurrence.  Phase 0's
-- TyEndpoint retains the local session calculus; Phase 1 adds the exact protocol
-- instance and role needed to prevent instance/role confusion.
data ProtocolEndpointBinding = ProtocolEndpointBinding
  { protocolEndpointName :: Name
  , protocolEndpointInstance :: ProtocolInstanceRevision
  , protocolEndpointRole :: ProtocolRoleKey
  , protocolEndpointSession :: Session
  }
  deriving (Eq, Ord, Show)

-- | The exact static contract of an endpoint occurrence, excluding the local
-- occurrence name. Different branch-local names may inhabit the same contract,
-- but equal Session syntax alone never establishes contract equality.
data ProtocolEndpointContract = ProtocolEndpointContract
  { protocolContractInstance :: ProtocolInstanceRevision
  , protocolContractRole :: ProtocolRoleKey
  , protocolContractSession :: Session
  }
  deriving (Eq, Ord, Show)

-- | Checked protocol metadata plus the ordinary structural resource context.
-- Both representations name the same live endpoint session and are checked for
-- agreement before any communication action is admitted.
data ProtocolContext = ProtocolContext
  { protocolResources :: ResourceContext
  , protocolEndpoints :: Map Name ProtocolEndpointBinding
  }
  deriving (Eq, Show)

-- | A communication request carries the exact protocol instance and role under
-- which the operation is being type-checked.  The current local state is taken
-- from the live endpoint binding and must admit the requested Session action.
data ProtocolActionRequest
  = ProtocolSendRequest
      Name Name ProtocolInstanceRevision ProtocolRoleKey
  | ProtocolReceiveRequest
      Name Name ProtocolInstanceRevision ProtocolRoleKey
  | ProtocolSelectRequest
      Name Name ProtocolInstanceRevision ProtocolRoleKey Text
  | ProtocolOfferRequest
      Name Name ProtocolInstanceRevision ProtocolRoleKey Text
  | ProtocolCloseRequest
      Name ProtocolInstanceRevision ProtocolRoleKey Outcome
  deriving (Eq, Show)

-- | Successful checking preserves the exact protocol instance/role on the
-- successor occurrence while delegating state progression and linear resource
-- consumption to the existing Session checker.
data CheckedProtocolStep = CheckedProtocolStep
  { checkedProtocolPredecessor :: ProtocolEndpointBinding
  , checkedProtocolSuccessor :: Maybe ProtocolEndpointBinding
  , checkedProtocolSessionStep :: SessionStep
  , checkedProtocolContext :: ProtocolContext
  }
  deriving (Eq, Show)

data ProtocolCheckError
  = ProtocolResourceError CheckError
  | DuplicateProtocolEndpoint Name
  | ProtocolEndpointUnknown Name
  | ProtocolEndpointMapKeyMismatch Name Name
  | ProtocolEmptyInstanceRevision Name
  | ProtocolEmptyRoleKey Name
  | ProtocolInstanceMismatch
      Name ProtocolInstanceRevision ProtocolInstanceRevision
  | ProtocolRoleMismatch Name ProtocolRoleKey ProtocolRoleKey
  | ProtocolEndpointResourceMissing Name
  | ProtocolEndpointResourceTypeMismatch Name Ty
  | ProtocolEndpointSessionMismatch Name Session Session
  | ProtocolEndpointMetadataConflict Name
  | ProtocolEndpointContractInstanceMismatch
      ProtocolInstanceRevision ProtocolInstanceRevision
  | ProtocolEndpointContractRoleMismatch ProtocolRoleKey ProtocolRoleKey
  | ProtocolEndpointContractSessionMismatch Session Session
  | ProtocolEndpointJoinEmpty
  | ProtocolSessionError SessionError
  deriving (Eq, Show)

emptyProtocolContext :: ProtocolContext
emptyProtocolContext = ProtocolContext
  { protocolResources = emptyContext
  , protocolEndpoints = Map.empty
  }

insertProtocolEndpoint
  :: Name
  -> ProtocolInstanceRevision
  -> ProtocolRoleKey
  -> Session
  -> ProtocolContext
  -> Either ProtocolCheckError ProtocolContext
insertProtocolEndpoint name instanceRevision role session context
  | Map.member name (protocolEndpoints context) =
      Left (DuplicateProtocolEndpoint name)
  | Text.null (unProtocolInstanceRevision instanceRevision) =
      Left (ProtocolEmptyInstanceRevision name)
  | Text.null (unProtocolRoleKey role) =
      Left (ProtocolEmptyRoleKey name)
  | otherwise = do
      resources <- mapLeft ProtocolResourceError $
        insertBinding Linear name (TyEndpoint session) (protocolResources context)
      let binding = ProtocolEndpointBinding
            { protocolEndpointName = name
            , protocolEndpointInstance = instanceRevision
            , protocolEndpointRole = role
            , protocolEndpointSession = session
            }
      Right context
        { protocolResources = resources
        , protocolEndpoints = Map.insert name binding (protocolEndpoints context)
        }

lookupProtocolEndpoint :: Name -> ProtocolContext -> Maybe ProtocolEndpointBinding
lookupProtocolEndpoint name = Map.lookup name . protocolEndpoints

protocolEndpointContract :: ProtocolEndpointBinding -> ProtocolEndpointContract
protocolEndpointContract binding =
  case Kernel.planProtocolContract
      (protocolEndpointInstance binding)
      (protocolEndpointRole binding)
      (protocolEndpointSession binding) of
    Kernel.MkProtocolContractPlan instanceRevision role localSession ->
      ProtocolEndpointContract
        { protocolContractInstance = instanceRevision
        , protocolContractRole = role
        , protocolContractSession = localSession
        }

-- | Check whether one endpoint occurrence may inhabit a position expecting the
-- other's exact endpoint contract. Occurrence names are intentionally ignored;
-- protocol instance, role, and local state are all identity-bearing.
checkProtocolEndpointSubstitution
  :: ProtocolEndpointBinding
  -> ProtocolEndpointBinding
  -> Either ProtocolCheckError ()
checkProtocolEndpointSubstitution expected actual =
  checkEndpointContract
    (protocolEndpointContract expected)
    (protocolEndpointContract actual)

-- | Join branch-local endpoint occurrences into one post-join endpoint contract.
-- Different occurrence names are allowed, but every branch must agree on exact
-- protocol instance, role, and local session state.
checkProtocolEndpointJoin
  :: [ProtocolEndpointBinding]
  -> Either ProtocolCheckError ProtocolEndpointContract
checkProtocolEndpointJoin [] = Left ProtocolEndpointJoinEmpty
checkProtocolEndpointJoin (firstBinding : rest) = do
  let expected = protocolEndpointContract firstBinding
  mapM_ (checkEndpointContract expected . protocolEndpointContract) rest
  Right expected

checkProtocolAction
  :: ProtocolActionRequest
  -> ProtocolContext
  -> Either ProtocolCheckError CheckedProtocolStep
checkProtocolAction request context = do
  let endpoint = requestEndpoint request
      expectedInstance = requestInstance request
      expectedRole = requestRole request
  binding <- maybe
    (Left (ProtocolEndpointUnknown endpoint))
    Right
    (lookupProtocolEndpoint endpoint context)
  if protocolEndpointName binding /= endpoint
    then Left (ProtocolEndpointMapKeyMismatch endpoint (protocolEndpointName binding))
    else Right ()

  let actualInstance = protocolEndpointInstance binding
      actualRole = protocolEndpointRole binding
      instanceMatches = expectedInstance == actualInstance
      roleMatches = expectedRole == actualRole

  case Kernel.decideProtocolActionByFacts
      instanceMatches
      roleMatches
      True of
    Kernel.ProtocolActionAccepted -> Right ()
    Kernel.ProtocolActionInstanceMismatchDecision ->
      Left (ProtocolInstanceMismatch endpoint expectedInstance actualInstance)
    Kernel.ProtocolActionRoleMismatchDecision ->
      Left (ProtocolRoleMismatch endpoint expectedRole actualRole)
    Kernel.ProtocolActionLocalStateRejectedDecision ->
      Left (ProtocolInstanceMismatch endpoint expectedInstance actualInstance)

  checkResourceAgreement binding (protocolResources context)

  let sessionResult = runSessionAction request (protocolResources context)
      localStateAllows = case sessionResult of
        Right _ -> True
        Left _ -> False

  sessionStep <- case
      Kernel.decideProtocolActionByFacts True True localStateAllows of
    Kernel.ProtocolActionAccepted ->
      case sessionResult of
        Right step -> Right step
        Left sessionError -> Left (ProtocolSessionError sessionError)
    Kernel.ProtocolActionLocalStateRejectedDecision ->
      case sessionResult of
        Left sessionError -> Left (ProtocolSessionError sessionError)
        Right _ ->
          Left (ProtocolEndpointSessionMismatch
            endpoint
            (protocolEndpointSession binding)
            (protocolEndpointSession binding))
    Kernel.ProtocolActionInstanceMismatchDecision ->
      Left (ProtocolInstanceMismatch endpoint expectedInstance actualInstance)
    Kernel.ProtocolActionRoleMismatchDecision ->
      Left (ProtocolRoleMismatch endpoint expectedRole actualRole)

  (successor, nextContext) <- advanceMetadata endpoint binding sessionStep context
  Right CheckedProtocolStep
    { checkedProtocolPredecessor = binding
    , checkedProtocolSuccessor = successor
    , checkedProtocolSessionStep = sessionStep
    , checkedProtocolContext = nextContext
    }

requestEndpoint :: ProtocolActionRequest -> Name
requestEndpoint request = case request of
  ProtocolSendRequest endpoint _ _ _ -> endpoint
  ProtocolReceiveRequest endpoint _ _ _ -> endpoint
  ProtocolSelectRequest endpoint _ _ _ _ -> endpoint
  ProtocolOfferRequest endpoint _ _ _ _ -> endpoint
  ProtocolCloseRequest endpoint _ _ _ -> endpoint

requestInstance :: ProtocolActionRequest -> ProtocolInstanceRevision
requestInstance request = case request of
  ProtocolSendRequest _ _ instanceRevision _ -> instanceRevision
  ProtocolReceiveRequest _ _ instanceRevision _ -> instanceRevision
  ProtocolSelectRequest _ _ instanceRevision _ _ -> instanceRevision
  ProtocolOfferRequest _ _ instanceRevision _ _ -> instanceRevision
  ProtocolCloseRequest _ instanceRevision _ _ -> instanceRevision

requestRole :: ProtocolActionRequest -> ProtocolRoleKey
requestRole request = case request of
  ProtocolSendRequest _ _ _ role -> role
  ProtocolReceiveRequest _ _ _ role -> role
  ProtocolSelectRequest _ _ _ role _ -> role
  ProtocolOfferRequest _ _ _ role _ -> role
  ProtocolCloseRequest _ _ role _ -> role

runSessionAction
  :: ProtocolActionRequest
  -> ResourceContext
  -> Either SessionError SessionStep
runSessionAction request resources = case request of
  ProtocolSendRequest endpoint successor _ _ ->
    sendEndpoint endpoint successor resources
  ProtocolReceiveRequest endpoint successor _ _ ->
    receiveEndpoint endpoint successor resources
  ProtocolSelectRequest endpoint successor _ _ label ->
    selectEndpoint endpoint successor label resources
  ProtocolOfferRequest endpoint successor _ _ label ->
    offerEndpoint endpoint successor label resources
  ProtocolCloseRequest endpoint _ _ outcome ->
    closeEndpoint endpoint outcome resources

checkResourceAgreement
  :: ProtocolEndpointBinding
  -> ResourceContext
  -> Either ProtocolCheckError ()
checkResourceAgreement binding resources =
  case Map.lookup name (linearBindings resources) of
    Nothing -> Left (ProtocolEndpointResourceMissing name)
    Just (TyEndpoint actualSession)
      | actualSession == expectedSession -> Right ()
      | otherwise -> Left
          (ProtocolEndpointSessionMismatch name expectedSession actualSession)
    Just other -> Left (ProtocolEndpointResourceTypeMismatch name other)
  where
    name = protocolEndpointName binding
    expectedSession = protocolEndpointSession binding

advanceMetadata
  :: Name
  -> ProtocolEndpointBinding
  -> SessionStep
  -> ProtocolContext
  -> Either ProtocolCheckError
      (Maybe ProtocolEndpointBinding, ProtocolContext)
advanceMetadata predecessor binding sessionStep context =
  let endpoints = protocolEndpoints context
      predecessorLive = Map.member predecessor endpoints
      remaining = Map.delete predecessor endpoints
      resources = stepContext sessionStep
  in case stepSuccessor sessionStep of
      Nothing ->
        case ProgressionKernel.decideProtocolCloseByFact predecessorLive of
          ProgressionKernel.ProtocolCloseAccepted -> Right
            ( Nothing
            , ProtocolContext
                { protocolResources = resources
                , protocolEndpoints = remaining
                }
            )
          ProgressionKernel.ProtocolClosePredecessorMissingDecision ->
            Left (ProtocolEndpointUnknown predecessor)
      Just (successorName, successorSession) ->
        let namesDistinct = successorName /= predecessor
            successorFresh = not (Map.member successorName endpoints)
        in case ProgressionKernel.decideProtocolContinuationByFacts
            predecessorLive namesDistinct successorFresh of
          ProgressionKernel.ProtocolContinuationAccepted ->
            case ProgressionKernel.planProtocolSuccessorContract
                (protocolEndpointInstance binding)
                (protocolEndpointRole binding)
                successorSession of
              ProgressionKernel.MkProtocolSuccessorContractPlan
                  instanceRevision role nextSession ->
                let successorBinding = ProtocolEndpointBinding
                      { protocolEndpointName = successorName
                      , protocolEndpointInstance = instanceRevision
                      , protocolEndpointRole = role
                      , protocolEndpointSession = nextSession
                      }
                in Right
                  ( Just successorBinding
                  , ProtocolContext
                      { protocolResources = resources
                      , protocolEndpoints = Map.insert successorName successorBinding remaining
                      }
                  )
          ProgressionKernel.ProtocolContinuationPredecessorMissingDecision ->
            Left (ProtocolEndpointUnknown predecessor)
          ProgressionKernel.ProtocolContinuationSameNameDecision ->
            Left (ProtocolEndpointMetadataConflict successorName)
          ProgressionKernel.ProtocolContinuationSuccessorOccupiedDecision ->
            Left (ProtocolEndpointMetadataConflict successorName)

checkEndpointContract
  :: ProtocolEndpointContract
  -> ProtocolEndpointContract
  -> Either ProtocolCheckError ()
checkEndpointContract expected actual =
  case Kernel.decideProtocolContractByFacts
      (protocolContractInstance expected == protocolContractInstance actual)
      (protocolContractRole expected == protocolContractRole actual)
      (protocolContractSession expected == protocolContractSession actual) of
    Kernel.ProtocolContractAccepted -> Right ()
    Kernel.ProtocolContractInstanceMismatchDecision ->
      Left (ProtocolEndpointContractInstanceMismatch
        (protocolContractInstance expected)
        (protocolContractInstance actual))
    Kernel.ProtocolContractRoleMismatchDecision ->
      Left (ProtocolEndpointContractRoleMismatch
        (protocolContractRole expected)
        (protocolContractRole actual))
    Kernel.ProtocolContractSessionMismatchDecision ->
      Left (ProtocolEndpointContractSessionMismatch
        (protocolContractSession expected)
        (protocolContractSession actual))

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
