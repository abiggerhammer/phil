{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ArchitectureComponentActivation
  ( GrammarV1ResolvedComponentActivation (..)
  , GrammarV1ArchitectureComponentActivationError (..)
  , grammarV1ResolvedComponentActivation
  , grammarV1ComponentProtocolContextFromResources
  , grammarV1ComponentProtocolContextFromActivation
  ) where

import Data.List (foldl')
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.CheckedBindingMode
  ( CheckedTypeMode (..)
  )
import Phil.Core.Context
  ( ResourceContext (..)
  )
import Phil.Core.Process
  ( ProcessKey
  )
import Phil.Core.ProcessActivation
  ( ActivationBinding (..)
  , ActivationBindingOrigin (..)
  , ActivationReachability (..)
  , ProcessActivationContract (..)
  , ProcessActivationState (..)
  )
import Phil.Core.Protocol
  ( ProtocolContext (..)
  , ProtocolEndpointBinding (..)
  )
import Phil.Core.Protocol.Family
  ( ProtocolProjectionEvidence (..)
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name
  , Ty (..)
  )
import Phil.Surface.GrammarV1.ArchitectureComponentProvisioning
  ( GrammarV1ComponentProvisioningSource (..)
  , GrammarV1ProvisionedComponentParameter (..)
  , GrammarV1ResolvedComponentProvisioning (..)
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..)
  )

-- | Exact runtime handoff derived from the static INT-008 provisioning carrier.
-- The activation contract owns the ordinary structural resource context; the
-- endpoint list carries only the protocol instance/role/session metadata that
-- must be reattached to that same context after activation.
data GrammarV1ResolvedComponentActivation = GrammarV1ResolvedComponentActivation
  { resolvedComponentActivationContract :: ProcessActivationContract
  , resolvedComponentActivationProtocolEndpoints :: [ProtocolEndpointBinding]
  }
  deriving (Eq, Show)

data GrammarV1ArchitectureComponentActivationError
  = GrammarV1ActivationEntryEndpointWithoutProtocol Text
  | GrammarV1ActivationProtocolEndpointModeMismatch Text CheckedTypeMode
  | GrammarV1ActivationProtocolEndpointTypeMismatch Text Ty Ty
  | GrammarV1ActivationDuplicateProtocolEndpoint Name
  | GrammarV1ActivationProcessContextMissing ProcessKey
  | GrammarV1ActivationProtocolEndpointResourceMissing Name
  | GrammarV1ActivationProtocolEndpointResourceTypeMismatch Name Ty Ty
  | GrammarV1ActivationUnexpectedEndpointResource Name
  deriving (Eq, Show)

-- | Turn exact architecture provisioning into one ProcessActivationContract and
-- the endpoint provenance that will inhabit the resulting process resource
-- context. No resource is inserted twice: protocol metadata is deliberately
-- kept separate until the activation context exists.
grammarV1ResolvedComponentActivation
  :: GrammarV1ResolvedComponentProvisioning
  -> Either
      GrammarV1ArchitectureComponentActivationError
      GrammarV1ResolvedComponentActivation
grammarV1ResolvedComponentActivation provisioning = do
  pieces <- mapM activationPiece (resolvedProvisioningParameters provisioning)
  let bindings = map fst pieces
      endpoints = concatMap snd pieces
  normalizedEndpoints <- normalizeEndpoints endpoints
  Right GrammarV1ResolvedComponentActivation
    { resolvedComponentActivationContract = ProcessActivationContract
        { activationContractProcess = resolvedProvisioningProcessKey provisioning
        , activationContractBindings = bindings
        }
    , resolvedComponentActivationProtocolEndpoints = normalizedEndpoints
    }
  where
    activationPiece parameter =
      let binder = provisionedComponentParameterBinder parameter
          localName = grammarV1ResolvedBinderCoreName binder
          displayName = grammarV1ResolvedBinderDisplayName binder
          checked = provisionedComponentParameterCheckedMode parameter
          occurrence = provisionedComponentParameterOccurrence parameter
          mkBinding origin reachability = ActivationBinding
            { activationOccurrenceKey = occurrence
            , activationLocalName = localName
            , activationCheckedTypeMode = checked
            , activationBindingOrigin = origin
            , activationReachability = reachability
            , activationStartsSharedLoan = False
            }
      in case provisionedComponentParameterSource parameter of
          GrammarV1ComponentProvisioningEntry entryName _ ->
            case checkedBindingType checked of
              TyEndpoint _ -> Left
                (GrammarV1ActivationEntryEndpointWithoutProtocol displayName)
              _ -> Right
                ( mkBinding
                    (RootEntryOrigin entryName)
                    (entryReachability checked occurrence)
                , []
                )
          GrammarV1ComponentProvisioningProtocolEndpoint occurrenceName projection -> do
            let expectedType = TyEndpoint (protocolProjectionSession projection)
            if checkedBindingMode checked /= Linear
              then Left
                (GrammarV1ActivationProtocolEndpointModeMismatch displayName checked)
              else Right ()
            if checkedBindingType checked /= expectedType
              then Left
                (GrammarV1ActivationProtocolEndpointTypeMismatch
                  displayName expectedType (checkedBindingType checked))
              else Right ()
            let binding = mkBinding
                  (ProtocolEndpointOrigin occurrenceName)
                  (ProtocolMediatedReachability occurrence)
                endpoint = ProtocolEndpointBinding
                  { protocolEndpointName = localName
                  , protocolEndpointInstance = protocolProjectionInstance projection
                  , protocolEndpointRole = protocolProjectionRole projection
                  , protocolEndpointSession = protocolProjectionSession projection
                  }
            Right (binding, [endpoint])

entryReachability :: CheckedTypeMode -> a -> ActivationReachability
entryReachability checked occurrence =
  case checkedBindingMode checked of
    Unrestricted -> ExtensionalImmutableReachability
    Affine -> DirectStatefulReachability occurrence
    Linear -> DirectStatefulReachability occurrence

normalizeEndpoints
  :: [ProtocolEndpointBinding]
  -> Either GrammarV1ArchitectureComponentActivationError [ProtocolEndpointBinding]
normalizeEndpoints endpoints =
  Map.elems <$> foldl' insertOne (Right Map.empty) endpoints
  where
    insertOne accumulated endpoint = do
      current <- accumulated
      let name = protocolEndpointName endpoint
      if Map.member name current
        then Left (GrammarV1ActivationDuplicateProtocolEndpoint name)
        else Right (Map.insert name endpoint current)

-- | Reattach exact protocol provenance to an already-closed activation resource
-- context. Every endpoint metadata entry must match one linear TyEndpoint with
-- the same local session, and every endpoint-shaped resource must have metadata.
grammarV1ComponentProtocolContextFromResources
  :: GrammarV1ResolvedComponentActivation
  -> ResourceContext
  -> Either GrammarV1ArchitectureComponentActivationError ProtocolContext
grammarV1ComponentProtocolContextFromResources activation resources = do
  let endpoints = resolvedComponentActivationProtocolEndpoints activation
      endpointMap = Map.fromList
        [ (protocolEndpointName endpoint, endpoint)
        | endpoint <- endpoints
        ]
  mapM_ (validateEndpoint resources) endpoints
  let metadataNames = Map.keysSet endpointMap
      resourceNames = endpointResourceNames resources
  case Set.lookupMin (resourceNames `Set.difference` metadataNames) of
    Just unexpected -> Left (GrammarV1ActivationUnexpectedEndpointResource unexpected)
    Nothing -> Right ProtocolContext
      { protocolResources = resources
      , protocolEndpoints = endpointMap
      }

-- | Convenience handoff for the normal INT-008 path after activateProcessState:
-- select the exact process context named by the derived contract, then attach
-- the protocol metadata without rebuilding or reinserting any binding.
grammarV1ComponentProtocolContextFromActivation
  :: GrammarV1ResolvedComponentActivation
  -> ProcessActivationState
  -> Either GrammarV1ArchitectureComponentActivationError ProtocolContext
grammarV1ComponentProtocolContextFromActivation activation state = do
  let processKey = activationContractProcess
        (resolvedComponentActivationContract activation)
  resources <- maybe
    (Left (GrammarV1ActivationProcessContextMissing processKey))
    Right
    (Map.lookup processKey (activationProcessContexts state))
  grammarV1ComponentProtocolContextFromResources activation resources

validateEndpoint
  :: ResourceContext
  -> ProtocolEndpointBinding
  -> Either GrammarV1ArchitectureComponentActivationError ()
validateEndpoint resources endpoint =
  case Map.lookup name (linearBindings resources) of
    Nothing -> Left (GrammarV1ActivationProtocolEndpointResourceMissing name)
    Just actualType
      | actualType == expectedType -> Right ()
      | otherwise -> Left
          (GrammarV1ActivationProtocolEndpointResourceTypeMismatch
            name expectedType actualType)
  where
    name = protocolEndpointName endpoint
    expectedType = TyEndpoint (protocolEndpointSession endpoint)

endpointResourceNames :: ResourceContext -> Set.Set Name
endpointResourceNames resources = Set.unions
  [ names (unrestrictedBindings resources)
  , names (affineBindings resources)
  , names (linearBindings resources)
  ]
  where
    names = Map.keysSet . Map.filter isEndpoint
    isEndpoint ty = case ty of
      TyEndpoint _ -> True
      _ -> False
