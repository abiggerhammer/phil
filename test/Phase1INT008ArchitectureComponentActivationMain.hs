{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Core.CheckedBindingMode
  ( CheckedTypeMode (..)
  )
import Phil.Core.Context
  ( emptyContext
  , insertBinding
  )
import Phil.Core.Process
  ( ProcessKey (..)
  )
import Phil.Core.ProcessActivation
  ( ActivationBinding (..)
  , ActivationBindingOrigin (..)
  , ActivationOccurrenceKey (..)
  , ActivationReachability (..)
  , ProcessActivationContract (..)
  , ProcessActivationState (..)
  )
import Phil.Core.Protocol
  ( ProtocolEndpointBinding (..)
  , ProtocolInstanceRevision (..)
  , ProtocolRoleKey (..)
  , lookupProtocolEndpoint
  , protocolEndpoints
  , protocolResources
  )
import Phil.Core.Protocol.Family
  ( ProtocolProjectionEvidence (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Outcome (..)
  , Session (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.ArchitectureComponentActivation
import Phil.Surface.GrammarV1.ArchitectureComponentProvisioning
  ( GrammarV1ComponentProvisioningSource (..)
  , GrammarV1ProvisionedComponentParameter (..)
  , GrammarV1ResolvedComponentProvisioning (..)
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey (..)
  , GrammarV1BinderKind (..)
  , GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.Syntax
  ( SourcePoint (..)
  , SourceSpan (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "INT-008 exact provisioning derives activation contract and protocol context"
        exactActivationHandoff
    , test "INT-008 endpoint type cannot arrive through an entry without protocol provenance"
        entryEndpointWithoutProtocolRejects
    , test "INT-008 protocol endpoint must remain linear"
        endpointModeMismatchRejects
    , test "INT-008 protocol endpoint must retain exact projected session"
        endpointTypeMismatchRejects
    , test "INT-008 protocol context requires the exact activated process"
        missingProcessContextRejects
    , test "INT-008 protocol metadata must match the activated endpoint resource"
        endpointResourceMismatchRejects
    , test "INT-008 endpoint-shaped activated resources cannot lack protocol metadata"
        unexpectedEndpointResourceRejects
    , test "INT-008 duplicate endpoint metadata names fail closed"
        duplicateEndpointNameRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactActivationHandoff :: Either String ()
exactActivationHandoff = do
  activation <- mapLeft show $ grammarV1ResolvedComponentActivation exactProvisioning
  let contract = resolvedComponentActivationContract activation
  assert (activationContractProcess contract == processKey)
    "activation contract changed exact ProcessKey"
  case activationContractBindings contract of
    [endpointBinding, payloadBinding] -> do
      assert (activationLocalName endpointBinding == endpointName)
        "endpoint activation changed semantic local name"
      assert (activationCheckedTypeMode endpointBinding == CheckedTypeMode endpointType Linear)
        "endpoint activation changed checked type/mode"
      assert (activationOccurrenceKey endpointBinding == endpointOccurrence)
        "endpoint activation changed exact occurrence identity"
      assert (activationBindingOrigin endpointBinding == ProtocolEndpointOrigin "ping")
        "endpoint activation lost protocol occurrence provenance"
      assert (activationReachability endpointBinding == ProtocolMediatedReachability endpointOccurrence)
        "endpoint activation was not protocol-mediated"
      assert (activationLocalName payloadBinding == payloadName)
        "payload activation changed semantic local name"
      assert (activationBindingOrigin payloadBinding == RootEntryOrigin "payload")
        "payload activation lost root-entry provenance"
      assert (activationReachability payloadBinding == ExtensionalImmutableReachability)
        "unrestricted payload activation gained stateful reachability"
    other -> Left ("unexpected activation binding telescope: " <> show other)
  case resolvedComponentActivationProtocolEndpoints activation of
    [endpoint] -> do
      assert (protocolEndpointName endpoint == endpointName)
        "endpoint metadata changed semantic local name"
      assert (protocolEndpointInstance endpoint == protocolInstance)
        "endpoint metadata changed protocol instance"
      assert (protocolEndpointRole endpoint == clientRole)
        "endpoint metadata changed protocol role"
      assert (protocolEndpointSession endpoint == clientSession)
        "endpoint metadata changed local session"
    other -> Left ("unexpected endpoint metadata telescope: " <> show other)
  resources <- exactResources
  let state = ProcessActivationState
        { activationProcessContexts = Map.singleton processKey resources
        , activationRestrictedOwners = Map.singleton endpointOccurrence (processKey, endpointName)
        , activationDirectStatefulReachability = Map.empty
        }
  protocolContext <- mapLeft show $
    grammarV1ComponentProtocolContextFromActivation activation state
  assert (protocolResources protocolContext == resources)
    "protocol handoff rebuilt or changed activation resources"
  assert (Map.keys (protocolEndpoints protocolContext) == [endpointName])
    "protocol handoff changed endpoint metadata domain"
  case lookupProtocolEndpoint endpointName protocolContext of
    Just endpoint -> do
      assert (protocolEndpointInstance endpoint == protocolInstance)
        "protocol context changed exact instance identity"
      assert (protocolEndpointRole endpoint == clientRole)
        "protocol context changed exact role identity"
      assert (protocolEndpointSession endpoint == clientSession)
        "protocol context changed exact local session"
    Nothing -> Left "protocol context lost endpoint metadata"

entryEndpointWithoutProtocolRejects :: Either String ()
entryEndpointWithoutProtocolRejects =
  let bad = exactProvisioning
        { resolvedProvisioningParameters =
            [ endpointParameter
                { provisionedComponentParameterSource =
                    GrammarV1ComponentProvisioningEntry "endpoint" endpointType
                }
            , payloadParameter
            ]
        }
  in case grammarV1ResolvedComponentActivation bad of
      Left (GrammarV1ActivationEntryEndpointWithoutProtocol "endpoint") -> Right ()
      other -> Left ("endpoint entry did not fail closed: " <> show other)

endpointModeMismatchRejects :: Either String ()
endpointModeMismatchRejects =
  let badEndpoint = endpointParameter
        { provisionedComponentParameterCheckedMode =
            CheckedTypeMode endpointType Unrestricted
        }
      bad = exactProvisioning
        { resolvedProvisioningParameters = [badEndpoint, payloadParameter] }
  in case grammarV1ResolvedComponentActivation bad of
      Left (GrammarV1ActivationProtocolEndpointModeMismatch
        "endpoint" (CheckedTypeMode actualType Unrestricted)) ->
          assert (actualType == endpointType)
            "endpoint mode mismatch lost exact endpoint type"
      other -> Left ("non-linear protocol endpoint was accepted: " <> show other)

endpointTypeMismatchRejects :: Either String ()
endpointTypeMismatchRejects =
  let wrongType = TyEndpoint serverSession
      badEndpoint = endpointParameter
        { provisionedComponentParameterCheckedMode =
            CheckedTypeMode wrongType Linear
        }
      bad = exactProvisioning
        { resolvedProvisioningParameters = [badEndpoint, payloadParameter] }
  in case grammarV1ResolvedComponentActivation bad of
      Left (GrammarV1ActivationProtocolEndpointTypeMismatch
        "endpoint" expected actual) -> do
          assert (expected == endpointType)
            "endpoint type mismatch lost projected expected session"
          assert (actual == wrongType)
            "endpoint type mismatch lost actual checked type"
      other -> Left ("wrong endpoint session was accepted: " <> show other)

missingProcessContextRejects :: Either String ()
missingProcessContextRejects = do
  activation <- mapLeft show $ grammarV1ResolvedComponentActivation exactProvisioning
  let state = ProcessActivationState
        { activationProcessContexts = Map.empty
        , activationRestrictedOwners = Map.empty
        , activationDirectStatefulReachability = Map.empty
        }
  case grammarV1ComponentProtocolContextFromActivation activation state of
    Left (GrammarV1ActivationProcessContextMissing actual) ->
      assert (actual == processKey) "missing-context diagnostic changed ProcessKey"
    other -> Left ("missing activated process did not reject: " <> show other)

endpointResourceMismatchRejects :: Either String ()
endpointResourceMismatchRejects = do
  activation <- mapLeft show $ grammarV1ResolvedComponentActivation exactProvisioning
  resources0 <- mapLeft show $ insertBinding Linear endpointName (TyUInt 8) emptyContext
  resources <- mapLeft show $ insertBinding Unrestricted payloadName (TyUInt 8) resources0
  case grammarV1ComponentProtocolContextFromResources activation resources of
    Left (GrammarV1ActivationProtocolEndpointResourceTypeMismatch name expected actual) -> do
      assert (name == endpointName) "resource mismatch named wrong endpoint"
      assert (expected == endpointType) "resource mismatch lost expected endpoint type"
      assert (actual == TyUInt 8) "resource mismatch lost actual resource type"
    other -> Left ("corrupt activated endpoint resource was accepted: " <> show other)

unexpectedEndpointResourceRejects :: Either String ()
unexpectedEndpointResourceRejects = do
  activation <- mapLeft show $ grammarV1ResolvedComponentActivation exactProvisioning
  resources <- exactResources
  polluted <- mapLeft show $ insertBinding Linear ghostEndpoint endpointType resources
  case grammarV1ComponentProtocolContextFromResources activation polluted of
    Left (GrammarV1ActivationUnexpectedEndpointResource actual) ->
      assert (actual == ghostEndpoint)
        "unexpected-endpoint diagnostic changed resource name"
    other -> Left ("endpoint resource without metadata was accepted: " <> show other)

duplicateEndpointNameRejects :: Either String ()
duplicateEndpointNameRejects =
  let secondEndpoint = endpointParameter
        { provisionedComponentParameterBinder =
            parameterBinder 2 endpointName "endpoint2"
        , provisionedComponentParameterOccurrence =
            ActivationOccurrenceKey "architecture.local-ping:ping.Client.second"
        }
      bad = exactProvisioning
        { resolvedProvisioningParameters = [endpointParameter, secondEndpoint] }
  in case grammarV1ResolvedComponentActivation bad of
      Left (GrammarV1ActivationDuplicateProtocolEndpoint actual) ->
        assert (actual == endpointName) "duplicate endpoint diagnostic changed local name"
      other -> Left ("duplicate endpoint metadata name was accepted: " <> show other)

exactResources :: Either String Phil.Core.Context.ResourceContext
exactResources = do
  resources0 <- mapLeft show $ insertBinding Linear endpointName endpointType emptyContext
  mapLeft show $ insertBinding Unrestricted payloadName (TyUInt 8) resources0

exactProvisioning :: GrammarV1ResolvedComponentProvisioning
exactProvisioning = GrammarV1ResolvedComponentProvisioning
  { resolvedProvisioningComponentOccurrence = "client"
  , resolvedProvisioningProcessSite = "client_run"
  , resolvedProvisioningProcessKey = processKey
  , resolvedProvisioningParameters = [endpointParameter, payloadParameter]
  }

endpointParameter :: GrammarV1ProvisionedComponentParameter
endpointParameter = GrammarV1ProvisionedComponentParameter
  { provisionedComponentParameterBinder = parameterBinder 0 endpointName "endpoint"
  , provisionedComponentParameterCheckedMode = CheckedTypeMode endpointType Linear
  , provisionedComponentParameterOccurrence = endpointOccurrence
  , provisionedComponentParameterSource =
      GrammarV1ComponentProvisioningProtocolEndpoint "ping" clientProjection
  }

payloadParameter :: GrammarV1ProvisionedComponentParameter
payloadParameter = GrammarV1ProvisionedComponentParameter
  { provisionedComponentParameterBinder = parameterBinder 1 payloadName "payload"
  , provisionedComponentParameterCheckedMode = CheckedTypeMode (TyUInt 8) Unrestricted
  , provisionedComponentParameterOccurrence = payloadOccurrence
  , provisionedComponentParameterSource =
      GrammarV1ComponentProvisioningEntry "payload" (TyUInt 8)
  }

parameterBinder :: Int -> Name -> String -> GrammarV1ResolvedBinder
parameterBinder ordinal coreName displayName = GrammarV1ResolvedBinder
  { grammarV1ResolvedBinderKey = GrammarV1BinderKey
      { grammarV1BinderDeclarationRoot = DeclarationKey "component.ClientWorker"
      , grammarV1BinderOrdinal = ordinal
      }
  , grammarV1ResolvedBinderCoreName = coreName
  , grammarV1ResolvedBinderKind = GrammarV1ComponentParameterBinder
  , grammarV1ResolvedBinderDisplayName = fromStringText displayName
  , grammarV1ResolvedBinderSourceSpan = dummySpan
  }

fromStringText :: String -> Data.Text.Text
fromStringText = Data.Text.pack

dummySpan :: SourceSpan
dummySpan = SourceSpan dummyPoint dummyPoint

dummyPoint :: SourcePoint
dummyPoint = SourcePoint
  { sourcePointFile = "int008-activation"
  , sourcePointLine = 1
  , sourcePointColumn = 1
  , sourcePointOffset = 0
  }

processKey :: ProcessKey
processKey = ProcessKey "process.local-ping.client"

endpointName, payloadName, ghostEndpoint :: Name
endpointName = Name "component.ClientWorker.param.0"
payloadName = Name "component.ClientWorker.param.1"
ghostEndpoint = Name "ghost.endpoint"

protocolInstance :: ProtocolInstanceRevision
protocolInstance = ProtocolInstanceRevision "protocol.ping.instance.v1"

clientRole :: ProtocolRoleKey
clientRole = ProtocolRoleKey "Client"

clientSession, serverSession :: Session
clientSession = Send (Name "x") (TyUInt 8) (End (Outcome "Done"))
serverSession = Receive (Name "x") (TyUInt 8) (End (Outcome "Done"))

endpointType :: Ty
endpointType = TyEndpoint clientSession

clientProjection :: ProtocolProjectionEvidence
clientProjection = ProtocolProjectionEvidence
  { protocolProjectionInstance = protocolInstance
  , protocolProjectionRole = clientRole
  , protocolProjectionSession = clientSession
  }

endpointOccurrence, payloadOccurrence :: ActivationOccurrenceKey
endpointOccurrence = ActivationOccurrenceKey "architecture.local-ping:ping.Client"
payloadOccurrence = ActivationOccurrenceKey "architecture.local-ping:entry.payload"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
