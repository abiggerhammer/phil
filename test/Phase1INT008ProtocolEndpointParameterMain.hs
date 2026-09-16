{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  )
import Phil.Core.Protocol
  ( ProtocolRoleKey (..)
  )
import Phil.Core.Protocol.Family
  ( ProtocolFamilyError (..)
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
  , Name (..)
  , Outcome (..)
  , Session (..)
  , Ty (..)
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceState (..)
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolEndpointType
  ( GrammarV1ProtocolEndpointResolution (..)
  , GrammarV1ProtocolEndpointTypeError (..)
  )
import Phil.Surface.GrammarV1.ProtocolRoles
  ( grammarV1ClosedBinaryProtocolFamily
  )
import Phil.Surface.GrammarV1.SemanticComponentHeader
  ( GrammarV1CheckedSemanticComponentHeader (..)
  , GrammarV1SemanticComponentHeaderError (..)
  , grammarV1CheckedSemanticComponentHeader
  , grammarV1CheckedSemanticComponentHeaderWithProtocolEndpoints
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "INT-008 Client[Ping] resolves to exact linear endpoint projection"
        exactPingEndpointParameterResolves
    , test "INT-008 endpoint parameter stays non-competent without architecture resolution"
        unresolvedPingEndpointRemainsNonCompetent
    , test "INT-008 unknown protocol role fails against exact family"
        unknownRoleRejects
    , test "INT-008 duplicate protocol resolution fails closed"
        duplicateResolutionRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactPingEndpointParameterResolves :: Either String ()
exactPingEndpointParameterResolves = do
  (protocol, component) <- pingDeclarations clientWorkerSource
  resolution <- pingResolution protocol
  header <- checkedEndpointHeader [resolution] component
  parameters <- maybe
    (Left "resolved ClientWorker lost its parameter telescope")
    Right
    (checkedSemanticComponentParameters header)
  case parameters of
    [(endpointBinder, endpointType), (payloadBinder, payloadType)] -> do
      let expectedSession = Send (Name "x") (TyUInt 8) (End (Outcome "Done"))
          expectedEndpoint = TyEndpoint expectedSession
          Name endpointSemanticName = grammarV1ResolvedBinderCoreName endpointBinder
          Name payloadSemanticName = grammarV1ResolvedBinderCoreName payloadBinder
          bindings = stateBindings (checkedSemanticComponentState header)
      assert (endpointType == expectedEndpoint)
        ("Client[Ping] did not preserve exact projected session: " <> show endpointType)
      assert (payloadType == TyUInt 8)
        "payload parameter did not remain U8"
      endpointMeta <- maybe
        (Left "endpoint binder missing from semantic SurfaceState")
        Right
        (Map.lookup endpointSemanticName bindings)
      payloadMeta <- maybe
        (Left "payload binder missing from semantic SurfaceState")
        Right
        (Map.lookup payloadSemanticName bindings)
      assert
        (bindingMode endpointMeta == Linear && bindingType endpointMeta == expectedEndpoint)
        "resolved protocol endpoint was not installed as exact linear TyEndpoint"
      assert
        (bindingMode payloadMeta == Unrestricted && bindingType payloadMeta == TyUInt 8)
        "ordinary payload parameter changed mode or type"
      assert
        (grammarV1ResolvedBinderDisplayName endpointBinder == "endpoint")
        "endpoint diagnostic spelling changed"
      assert
        (grammarV1ResolvedBinderDisplayName payloadBinder == "payload")
        "payload diagnostic spelling changed"
    other -> Left ("unexpected resolved ClientWorker parameter shape: " <> show other)

unresolvedPingEndpointRemainsNonCompetent :: Either String ()
unresolvedPingEndpointRemainsNonCompetent = do
  (_, component) <- pingDeclarations clientWorkerSource
  let declarationKey = DeclarationKey "component.ping.client"
      definitionRevision = DefinitionRevision "component.ping.client.v1"
      legacy = grammarV1CheckedSemanticComponentHeader
        emptyStaticContext declarationKey definitionRevision component
      explicitEmpty = grammarV1CheckedSemanticComponentHeaderWithProtocolEndpoints
        emptyStaticContext [] declarationKey definitionRevision component
  assert (legacy == Nothing)
    "legacy primitive-only component header guessed Client[Ping] semantics"
  assert (explicitEmpty == Nothing)
    "endpoint-aware component header guessed a protocol without resolution"

unknownRoleRejects :: Either String ()
unknownRoleRejects = do
  (protocol, component) <- pingDeclarations wrongRoleWorkerSource
  resolution <- pingResolution protocol
  let result = grammarV1CheckedSemanticComponentHeaderWithProtocolEndpoints
        emptyStaticContext
        [resolution]
        (DeclarationKey "component.ping.wrong-role")
        (DefinitionRevision "component.ping.wrong-role.v1")
        component
  case result of
    Just (Left (GrammarV1SemanticComponentProtocolEndpointTypeError
      (GrammarV1ProtocolEndpointProjectionError
        (UnknownProtocolProjectionRole (ProtocolRoleKey "Observer") roles)))) -> do
          assert
            (roles == [ProtocolRoleKey "Client", ProtocolRoleKey "Server"])
            ("unknown-role rejection lost exact declared role set: " <> show roles)
    other -> Left ("unknown protocol role did not reject exactly: " <> show other)

duplicateResolutionRejects :: Either String ()
duplicateResolutionRejects = do
  (protocol, component) <- pingDeclarations clientWorkerSource
  resolution <- pingResolution protocol
  let result = grammarV1CheckedSemanticComponentHeaderWithProtocolEndpoints
        emptyStaticContext
        [resolution, resolution]
        (DeclarationKey "component.ping.duplicate-resolution")
        (DefinitionRevision "component.ping.duplicate-resolution.v1")
        component
  case result of
    Just (Left (GrammarV1SemanticComponentProtocolEndpointTypeError
      (GrammarV1ProtocolEndpointResolutionAmbiguous
        (ReferencedGenericStaticActual "Ping") 2))) -> Right ()
    other -> Left ("duplicate protocol resolution did not fail closed: " <> show other)

checkedEndpointHeader
  :: [GrammarV1ProtocolEndpointResolution]
  -> GrammarV1ComponentDecl
  -> Either String GrammarV1CheckedSemanticComponentHeader
checkedEndpointHeader resolutions component =
  case grammarV1CheckedSemanticComponentHeaderWithProtocolEndpoints
      emptyStaticContext
      resolutions
      (DeclarationKey "component.ping.client")
      (DefinitionRevision "component.ping.client.v1")
      component of
    Just (Right (header, [])) -> Right header
    other -> Left ("expected checked endpoint-aware component header, got " <> show other)

pingResolution
  :: GrammarV1ProtocolDecl
  -> Either String GrammarV1ProtocolEndpointResolution
pingResolution protocol = do
  family <- case grammarV1ClosedBinaryProtocolFamily
      (DeclarationKey "protocol.ping")
      (InterfaceRevision "protocol.ping.v1")
      protocol of
    Just (Right value) -> Right value
    other -> Left ("expected closed Ping protocol family, got " <> show other)
  instanceValue <- mapLeft show $
    instantiateBinaryProtocol strictGenericInstantiationPolicy family [] []
  Right GrammarV1ProtocolEndpointResolution
    { protocolEndpointResolutionSourceReference = ReferencedGenericStaticActual "Ping"
    , protocolEndpointResolutionInstance = instanceValue
    }

pingDeclarations
  :: Text.Text
  -> Either String (GrammarV1ProtocolDecl, GrammarV1ComponentDecl)
pingDeclarations componentSource = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "int008-ping-endpoint" $
      Text.unlines
        [ "protocol Ping {"
        , "  role Client = send (x : U8) then end Done;"
        , "  role Server = receive (x : U8) then end Done;"
        , "}"
        , componentSource
        ]
  case grammarV1TopLevelDecls sourceFile of
    [Located _ protocolTop, Located _ componentTop] -> do
      protocol <- case locatedValue (grammarV1Declaration protocolTop) of
        GrammarV1ProtocolDeclaration value -> Right value
        other -> Left ("expected Ping protocol declaration, got " <> show other)
      component <- case locatedValue (grammarV1Declaration componentTop) of
        GrammarV1ComponentDeclaration value -> Right value
        other -> Left ("expected ClientWorker component declaration, got " <> show other)
      Right (protocol, component)
    declarations -> Left
      ("expected protocol plus component, got " <> show (length declarations) <> " declarations")

clientWorkerSource :: Text.Text
clientWorkerSource =
  "component ClientWorker(endpoint : Client[Ping], payload : U8) {}"

wrongRoleWorkerSource :: Text.Text
wrongRoleWorkerSource =
  "component ObserverWorker(endpoint : Observer[Ping], payload : U8) {}"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
