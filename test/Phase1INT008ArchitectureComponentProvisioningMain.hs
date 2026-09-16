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
import Phil.Core.Protocol
  ( ProtocolRoleKey (..)
  )
import Phil.Core.Protocol.Family
  ( ProtocolProjectionEvidence (..)
  , instantiateBinaryProtocol
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , DefinitionRevision (..)
  , InterfaceRevision (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.ArchitectureComponentProvisioning
import Phil.Surface.GrammarV1.ArchitectureSurface
  ( GrammarV1CheckedArchitectureSurface
  , grammarV1CheckedArchitectureSurface
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolEndpointType
  ( GrammarV1ProtocolEndpointResolution (..)
  )
import Phil.Surface.GrammarV1.ProtocolRoles
  ( grammarV1ClosedBinaryProtocolFamily
  )
import Phil.Surface.GrammarV1.SemanticComponentHeader
  ( GrammarV1CheckedSemanticComponentHeader
  , grammarV1CheckedSemanticComponentHeaderWithProtocolEndpoints
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "INT-008 architecture bind provisions exact endpoint and entry"
        exactArchitectureProvisioning
    , test "INT-008 missing component parameter bind fails closed"
        missingBindRejects
    , test "INT-008 wrong protocol role cannot provision endpoint"
        wrongRoleRejects
    , test "INT-008 protocol occurrence resolution cannot cross source identity"
        crossProtocolResolutionRejects
    , test "INT-008 one linear endpoint occurrence cannot provision two parameters"
        duplicatedLinearEndpointRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactArchitectureProvisioning :: Either String ()
exactArchitectureProvisioning = do
  fixture <- checkedFixture exactSource "ClientWorker"
  result <- mapLeft show (resolveFixture fixture)
  case resolvedProvisioningParameters result of
    [endpoint, payload] -> do
      assert
        (grammarV1ResolvedBinderDisplayName
          (provisionedComponentParameterBinder endpoint) == "endpoint")
        "first provisioned parameter was not endpoint"
      assert
        (checkedBindingMode
          (provisionedComponentParameterCheckedMode endpoint) == Linear)
        "endpoint provisioning lost linear mode"
      case provisionedComponentParameterSource endpoint of
        GrammarV1ComponentProvisioningProtocolEndpoint occurrence projection -> do
          assert (occurrence == "ping")
            "endpoint did not retain exact ping occurrence"
          assert (protocolProjectionRole projection == ProtocolRoleKey "Client")
            "endpoint did not retain exact Client role"
        other -> Left ("endpoint had wrong provisioning source: " <> show other)
      assert
        (grammarV1ResolvedBinderDisplayName
          (provisionedComponentParameterBinder payload) == "payload")
        "second provisioned parameter was not payload"
      assert
        (checkedBindingMode
          (provisionedComponentParameterCheckedMode payload) == Unrestricted)
        "payload provisioning changed unrestricted mode"
      case provisionedComponentParameterSource payload of
        GrammarV1ComponentProvisioningEntry entryName entryType -> do
          assert (entryName == "payload") "payload entry identity changed"
          assert (entryType == TyUInt 8) "payload entry type changed"
        other -> Left ("payload had wrong provisioning source: " <> show other)
    other -> Left ("unexpected provisioned parameter telescope: " <> show other)

missingBindRejects :: Either String ()
missingBindRejects = do
  fixture <- checkedFixture missingBindSource "ClientWorker"
  case resolveFixture fixture of
    Left (GrammarV1ProvisioningBindMissing "client.endpoint") -> Right ()
    other -> Left ("missing endpoint bind did not reject exactly: " <> show other)

wrongRoleRejects :: Either String ()
wrongRoleRejects = do
  fixture <- checkedFixture wrongRoleSource "ClientWorker"
  case resolveFixture fixture of
    Left (GrammarV1ProvisioningProtocolEndpointRoleMismatch
      "endpoint" (ProtocolRoleKey "Server") (ProtocolRoleKey "Client")) -> Right ()
    other -> Left ("wrong role bind did not reject exactly: " <> show other)

crossProtocolResolutionRejects :: Either String ()
crossProtocolResolutionRejects = do
  fixture <- checkedFixture exactSource "ClientWorker"
  let wrongOccurrence = (fixtureProtocolOccurrence fixture)
        { architectureProtocolOccurrenceSourceReference =
            ReferencedGenericStaticActual "OtherProtocol"
        }
  case grammarV1ResolveArchitectureComponentProvisioning
      (fixtureArchitecture fixture)
      "client"
      "client_run"
      processKey
      (fixtureComponent fixture)
      (fixtureHeader fixture)
      [wrongOccurrence] of
    Left (GrammarV1ProvisioningProtocolSourceMismatch
      "ping"
      (ReferencedGenericStaticActual "Ping")
      (ReferencedGenericStaticActual "OtherProtocol")) -> Right ()
    other -> Left ("cross-protocol resolution did not reject exactly: " <> show other)

duplicatedLinearEndpointRejects :: Either String ()
duplicatedLinearEndpointRejects = do
  fixture <- checkedFixture duplicateEndpointSource "TwinClient"
  case grammarV1ResolveArchitectureComponentProvisioning
      (fixtureArchitecture fixture)
      "client"
      "client_run"
      processKey
      (fixtureComponent fixture)
      (fixtureHeader fixture)
      [fixtureProtocolOccurrence fixture] of
    Left (GrammarV1ProvisioningDuplicateRestrictedSource _ "first" "second") -> Right ()
    other -> Left ("duplicated linear endpoint did not reject exactly: " <> show other)

data CheckedFixture = CheckedFixture
  { fixtureComponent :: GrammarV1ComponentDecl
  , fixtureArchitecture :: GrammarV1CheckedArchitectureSurface
  , fixtureHeader :: GrammarV1CheckedSemanticComponentHeader
  , fixtureProtocolOccurrence :: GrammarV1ArchitectureProtocolOccurrence
  }

checkedFixture :: Text.Text -> Text.Text -> Either String CheckedFixture
checkedFixture source expectedComponentName = do
  (protocol, component, architectureDecl) <- parseFixture source expectedComponentName
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
      (DeclarationKey ("component." <> expectedComponentName))
      (DefinitionRevision ("component." <> expectedComponentName <> ".v1"))
      component of
    Just (Right (value, [])) -> Right value
    other -> Left ("expected checked endpoint-aware component header, got " <> show other)
  architecture <- case grammarV1CheckedArchitectureSurface
      emptyStaticContext
      (DeclarationKey "architecture.local-ping")
      (DefinitionRevision "architecture.local-ping.v1")
      architectureDecl of
    Just (Right value) -> Right value
    other -> Left ("expected checked LocalPing architecture, got " <> show other)
  Right CheckedFixture
    { fixtureComponent = component
    , fixtureArchitecture = architecture
    , fixtureHeader = header
    , fixtureProtocolOccurrence = occurrence
    }

resolveFixture
  :: CheckedFixture
  -> Either GrammarV1ArchitectureComponentProvisioningError GrammarV1ResolvedComponentProvisioning
resolveFixture fixture =
  grammarV1ResolveArchitectureComponentProvisioning
    (fixtureArchitecture fixture)
    "client"
    "client_run"
    processKey
    (fixtureComponent fixture)
    (fixtureHeader fixture)
    [fixtureProtocolOccurrence fixture]

processKey :: ProcessKey
processKey = ProcessKey "process.local-ping.client"

parseFixture
  :: Text.Text
  -> Text.Text
  -> Either String (GrammarV1ProtocolDecl, GrammarV1ComponentDecl, GrammarV1ArchitectureDecl)
parseFixture source expectedComponentName = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "int008-architecture-provisioning" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ protocolTop, Located _ componentTop, Located _ architectureTop, Located _ programTop] -> do
      protocol <- case locatedValue (grammarV1Declaration protocolTop) of
        GrammarV1ProtocolDeclaration value -> Right value
        other -> Left ("expected Ping protocol declaration, got " <> show other)
      component <- case locatedValue (grammarV1Declaration componentTop) of
        GrammarV1ComponentDeclaration value
          | locatedValue (grammarV1ComponentName value) == expectedComponentName -> Right value
          | otherwise -> Left "component display name changed"
        other -> Left ("expected component declaration, got " <> show other)
      architecture <- case locatedValue (grammarV1Declaration architectureTop) of
        GrammarV1ArchitectureDeclaration value -> Right value
        other -> Left ("expected architecture declaration, got " <> show other)
      case locatedValue (grammarV1Declaration programTop) of
        GrammarV1ProgramDeclaration _ -> Right ()
        other -> Left ("expected program declaration, got " <> show other)
      Right (protocol, component, architecture)
    declarations -> Left
      ("expected protocol/component/architecture/program, got "
        <> show (length declarations) <> " declarations")

protocolSource :: [Text.Text]
protocolSource =
  [ "protocol Ping {"
  , "  role Client = send (x : U8) then end Done;"
  , "  role Server = receive (x : U8) then end Done;"
  , "}"
  ]

exactSource :: Text.Text
exactSource = Text.unlines $
  protocolSource <>
  [ "component ClientWorker(endpoint : Client[Ping], payload : U8) {}"
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

missingBindSource :: Text.Text
missingBindSource = Text.unlines $
  protocolSource <>
  [ "component ClientWorker(endpoint : Client[Ping], payload : U8) {}"
  , "architecture LocalPing {"
  , "  instance client = ClientWorker;"
  , "  process client_run = client;"
  , "  protocol ping = Ping;"
  , "  role ping.Client = client;"
  , "  role ping.Server = external;"
  , "  entry payload : U8;"
  , "  bind client.payload = payload;"
  , "}"
  , "program main = instantiate LocalPing;"
  ]

wrongRoleSource :: Text.Text
wrongRoleSource = Text.unlines $
  protocolSource <>
  [ "component ClientWorker(endpoint : Client[Ping], payload : U8) {}"
  , "architecture LocalPing {"
  , "  instance client = ClientWorker;"
  , "  process client_run = client;"
  , "  protocol ping = Ping;"
  , "  role ping.Client = client;"
  , "  role ping.Server = client;"
  , "  entry payload : U8;"
  , "  bind client.endpoint = ping.Server;"
  , "  bind client.payload = payload;"
  , "}"
  , "program main = instantiate LocalPing;"
  ]

duplicateEndpointSource :: Text.Text
duplicateEndpointSource = Text.unlines $
  protocolSource <>
  [ "component TwinClient(first : Client[Ping], second : Client[Ping]) {}"
  , "architecture LocalPing {"
  , "  instance client = TwinClient;"
  , "  process client_run = client;"
  , "  protocol ping = Ping;"
  , "  role ping.Client = client;"
  , "  role ping.Server = external;"
  , "  bind client.first = ping.Client;"
  , "  bind client.second = ping.Client;"
  , "}"
  , "program main = instantiate LocalPing;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
