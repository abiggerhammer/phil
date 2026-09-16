{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.CheckedBindingMode
  ( CheckedTypeMode (..)
  )
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  )
import Phil.Core.Process (ProcessKey (..))
import Phil.Core.ProcessActivation (ActivationOccurrenceKey (..))
import Phil.Core.ProcessRendezvous (ProcessRendezvousSide (..))
import Phil.Core.Protocol
  ( ProtocolRoleKey (..)
  )
import Phil.Core.Protocol.Family
  ( instantiateBinaryProtocol
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , DefinitionRevision (..)
  , InterfaceRevision (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax (Ty (..))
import Phil.Surface.GrammarV1.ArchitectureComponentProvisioning
import Phil.Surface.GrammarV1.ArchitectureSurface
  ( grammarV1CheckedArchitectureSurface
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.ComponentSendClose
  ( GrammarV1CheckedComponentSendClose (..)
  , grammarV1CheckedComponentSendClose
  )
import Phil.Surface.GrammarV1.ComponentSendProvisioning
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolEndpointType
  ( GrammarV1ProtocolEndpointResolution (..)
  )
import Phil.Surface.GrammarV1.ProtocolRoles
  ( grammarV1ClosedBinaryProtocolFamily
  )
import Phil.Surface.GrammarV1.SemanticComponentHeader
  ( grammarV1CheckedSemanticComponentHeaderWithProtocolEndpoints
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "INT-008 source send joins exact architecture provisioning"
        exactSourceSendProvisioning
    , test "INT-008 source send rejects missing provisioned payload binder"
        missingPayloadProvisioningRejects
    , test "INT-008 source send rejects non-protocol endpoint source"
        endpointSourceKindRejects
    , test "INT-008 source send checks payload type against projected message type"
        payloadTypeMismatchRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

data Fixture = Fixture
  { fixturePlan :: GrammarV1CheckedComponentSendClose
  , fixtureProvisioning :: GrammarV1ResolvedComponentProvisioning
  }

exactSourceSendProvisioning :: Either String ()
exactSourceSendProvisioning = do
  fixture <- sourceFixture
  resolved <- mapLeft show $ grammarV1ResolveComponentSendProvisioning
    (fixturePlan fixture)
    (fixtureProvisioning fixture)
  let plan = fixturePlan fixture
      side = resolvedComponentSendRendezvousSide resolved
      payloadParameter = resolvedComponentSendPayloadParameter resolved
  assert
    (rendezvousProcess side == processKey)
    "source-derived rendezvous side changed process identity"
  assert
    (rendezvousEndpoint side
      == grammarV1ResolvedBinderCoreName (checkedComponentSendEndpoint plan))
    "rendezvous predecessor did not use exact source endpoint binder name"
  assert
    (rendezvousSuccessor side
      == grammarV1ResolvedBinderCoreName (checkedComponentSendSuccessor plan))
    "rendezvous successor did not use exact source let binder name"
  assert
    (rendezvousRole side == ProtocolRoleKey "Client")
    "rendezvous side lost exact Client projection role"
  case provisionedComponentParameterSource payloadParameter of
    GrammarV1ComponentProvisioningEntry entryName entryType -> do
      assert (entryName == "payload") "payload provenance changed architecture entry"
      assert (entryType == TyUInt 8) "payload provenance changed entry type"
    other -> Left ("source payload did not retain entry provenance: " <> show other)
  assert
    (resolvedComponentSendPayloadOccurrence resolved
      == ActivationOccurrenceKey
        "phil.architecture.entry.v1:architecture.local-ping.v1:payload")
    "source payload did not retain exact architecture entry occurrence"

missingPayloadProvisioningRejects :: Either String ()
missingPayloadProvisioningRejects = do
  fixture <- sourceFixture
  let provisioning = fixtureProvisioning fixture
      payloadKey = grammarV1ResolvedBinderKey
        (checkedComponentSendPayload (fixturePlan fixture))
      retained =
        [ parameter
        | parameter <- resolvedProvisioningParameters provisioning
        , grammarV1ResolvedBinderKey
            (provisionedComponentParameterBinder parameter) /= payloadKey
        ]
      broken = provisioning { resolvedProvisioningParameters = retained }
  case grammarV1ResolveComponentSendProvisioning (fixturePlan fixture) broken of
    Left (GrammarV1ComponentSendParameterMissing actualKey) ->
      assert (actualKey == payloadKey) "missing-parameter diagnostic changed binder identity"
    other -> Left ("missing provisioned payload did not reject exactly: " <> show other)

endpointSourceKindRejects :: Either String ()
endpointSourceKindRejects = do
  fixture <- sourceFixture
  let provisioning = fixtureProvisioning fixture
      endpointKey = grammarV1ResolvedBinderKey
        (checkedComponentSendEndpoint (fixturePlan fixture))
      rewrite parameter
        | grammarV1ResolvedBinderKey
            (provisionedComponentParameterBinder parameter) == endpointKey =
            parameter
              { provisionedComponentParameterSource =
                  GrammarV1ComponentProvisioningEntry "fake" (TyUInt 8)
              }
        | otherwise = parameter
      broken = provisioning
        { resolvedProvisioningParameters = map rewrite
            (resolvedProvisioningParameters provisioning)
        }
  case grammarV1ResolveComponentSendProvisioning (fixturePlan fixture) broken of
    Left (GrammarV1ComponentSendEndpointNotProtocol
      (GrammarV1ComponentProvisioningEntry "fake" (TyUInt 8))) -> Right ()
    other -> Left ("non-protocol endpoint source did not reject exactly: " <> show other)

payloadTypeMismatchRejects :: Either String ()
payloadTypeMismatchRejects = do
  fixture <- sourceFixture
  let provisioning = fixtureProvisioning fixture
      payloadKey = grammarV1ResolvedBinderKey
        (checkedComponentSendPayload (fixturePlan fixture))
      rewrite parameter
        | grammarV1ResolvedBinderKey
            (provisionedComponentParameterBinder parameter) == payloadKey =
            parameter
              { provisionedComponentParameterCheckedMode =
                  CheckedTypeMode (TyUInt 16) (checkedBindingMode
                    (provisionedComponentParameterCheckedMode parameter))
              }
        | otherwise = parameter
      broken = provisioning
        { resolvedProvisioningParameters = map rewrite
            (resolvedProvisioningParameters provisioning)
        }
  case grammarV1ResolveComponentSendProvisioning (fixturePlan fixture) broken of
    Left (GrammarV1ComponentSendPayloadTypeMismatch (TyUInt 8) (TyUInt 16)) -> Right ()
    other -> Left ("wrong payload type did not reject exactly: " <> show other)

sourceFixture :: Either String Fixture
sourceFixture = do
  (protocol, component, architectureDecl) <- parseFixture
  family <- case grammarV1ClosedBinaryProtocolFamily
      (DeclarationKey "protocol.ping")
      (InterfaceRevision "protocol.ping.v1")
      protocol of
    Just (Right value) -> Right value
    other -> Left ("expected closed Ping protocol family, got " <> show other)
  instanceValue <- mapLeft show $
    instantiateBinaryProtocol strictGenericInstantiationPolicy family [] []
  let endpointResolution = GrammarV1ProtocolEndpointResolution
        { protocolEndpointResolutionSourceReference = ReferencedGenericStaticActual "Ping"
        , protocolEndpointResolutionInstance = instanceValue
        }
      occurrence = GrammarV1ArchitectureProtocolOccurrence
        { architectureProtocolOccurrenceName = "ping"
        , architectureProtocolOccurrenceSourceReference = ReferencedGenericStaticActual "Ping"
        , architectureProtocolOccurrenceInstance = instanceValue
        }
  header <- case grammarV1CheckedSemanticComponentHeaderWithProtocolEndpoints
      emptyStaticContext
      [endpointResolution]
      componentKey
      componentRevision
      component of
    Just (Right (value, [])) -> Right value
    other -> Left ("expected endpoint-aware ClientWorker header, got " <> show other)
  architecture <- case grammarV1CheckedArchitectureSurface
      emptyStaticContext
      architectureKey
      architectureRevision
      architectureDecl of
    Just (Right value) -> Right value
    other -> Left ("expected checked LocalPing architecture, got " <> show other)
  provisioning <- mapLeft show $ grammarV1ResolveArchitectureComponentProvisioning
    architecture
    "client"
    "client_run"
    processKey
    component
    header
    [occurrence]
  plan <- case grammarV1CheckedComponentSendClose componentKey component of
    Just (Right value) -> Right value
    other -> Left ("expected checked source send/close plan, got " <> show other)
  Right Fixture
    { fixturePlan = plan
    , fixtureProvisioning = provisioning
    }

parseFixture
  :: Either String (GrammarV1ProtocolDecl, GrammarV1ComponentDecl, GrammarV1ArchitectureDecl)
parseFixture = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "int008-source-send-provisioning" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ protocolTop, Located _ componentTop, Located _ architectureTop, Located _ programTop] -> do
      protocol <- case locatedValue (grammarV1Declaration protocolTop) of
        GrammarV1ProtocolDeclaration value -> Right value
        other -> Left ("expected Ping protocol declaration, got " <> show other)
      component <- case locatedValue (grammarV1Declaration componentTop) of
        GrammarV1ComponentDeclaration value -> Right value
        other -> Left ("expected ClientWorker component declaration, got " <> show other)
      architecture <- case locatedValue (grammarV1Declaration architectureTop) of
        GrammarV1ArchitectureDeclaration value -> Right value
        other -> Left ("expected LocalPing architecture declaration, got " <> show other)
      case locatedValue (grammarV1Declaration programTop) of
        GrammarV1ProgramDeclaration _ -> Right ()
        other -> Left ("expected program declaration, got " <> show other)
      Right (protocol, component, architecture)
    declarations -> Left
      ("expected protocol/component/architecture/program, got "
        <> show (length declarations) <> " declarations")

source :: Text.Text
source = Text.unlines
  [ "protocol Ping {"
  , "  role Client = send (x : U8) then end Done;"
  , "  role Server = receive (x : U8) then end Done;"
  , "}"
  , "component ClientWorker(endpoint : Client[Ping], payload : U8) {"
  , "  let done = send payload on endpoint;"
  , "  close done;"
  , "}"
  , "architecture LocalPing {"
  , "  instance client = ClientWorker;"
  , "  process client_run = client;"
  , "  protocol ping = Ping;"
  , "  role ping.Client = client;"
  , "  role ping.Server = external;"
  , "  entry payload : U8;"
  , "  bind client.endpoint = ping.Client;"
  , "  bind client.payload = payload;"
  , "}"
  , "program main = instantiate LocalPing;"
  ]

componentKey, architectureKey :: DeclarationKey
componentKey = DeclarationKey "component.ClientWorker"
architectureKey = DeclarationKey "architecture.LocalPing"

componentRevision, architectureRevision :: DefinitionRevision
componentRevision = DefinitionRevision "component.ClientWorker.v1"
architectureRevision = DefinitionRevision "architecture.local-ping.v1"

processKey :: ProcessKey
processKey = ProcessKey "process.local-ping.client"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
