{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Static (DeclarationKey (..), InterfaceRevision (..))
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (..)
  , GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.ComponentRequestReplyOutput
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolRoles
  ( grammarV1ClosedBinaryProtocolFamily
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "INT-009 request/reply source retains exact client and server binders"
        exactRoundTripShape
    , test "INT-009 client must output the exact received reply binder"
        clientOutputMustUseReply
    , test "INT-009 client receive must use the send successor endpoint"
        clientReceiveMustUseSuccessor
    , test "INT-009 client reply type is String"
        clientReplyTypeMustBeString
    , test "INT-009 server reply send must use the receive successor endpoint"
        serverSendMustUseSuccessor
    , test "INT-009 server reply is an explicit String value"
        serverReplyMustBeStringLiteral
    , test "INT-009 unrelated component stays outside Stage-2 competence"
        unrelatedBodyStaysOutside
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactRoundTripShape :: Either String ()
exactRoundTripShape = do
  (protocol, client, server) <- parseFixture source
  case grammarV1ClosedBinaryProtocolFamily
      protocolKey protocolInterface protocol of
    Just (Right _) -> Right ()
    other -> Left ("request/reply protocol family did not close: " <> show other)
  clientChecked <- requireClient client
  serverChecked <- requireServer server
  assertBinder "payload" GrammarV1ComponentParameterBinder
    (requestReplyClientPayload clientChecked)
  assertBinder "endpoint" GrammarV1ComponentParameterBinder
    (requestReplyClientInitialEndpoint clientChecked)
  assertBinder "awaiting" GrammarV1LetPatternBinder
    (requestReplyClientReplyEndpoint clientChecked)
  assertBinder "done" GrammarV1LetPatternBinder
    (requestReplyClientTerminalEndpoint clientChecked)
  assertBinder "reply" GrammarV1LetPatternBinder
    (requestReplyClientReplyValue clientChecked)
  assertBinder "writeDecision" GrammarV1LetPatternBinder
    (requestReplyClientWriteDecision clientChecked)
  assertBinder "endpoint" GrammarV1ComponentParameterBinder
    (requestReplyServerInitialEndpoint serverChecked)
  assertBinder "replyEndpoint" GrammarV1LetPatternBinder
    (requestReplyServerReplyEndpoint serverChecked)
  assertBinder "request" GrammarV1LetPatternBinder
    (requestReplyServerRequestValue serverChecked)
  assertBinder "done" GrammarV1LetPatternBinder
    (requestReplyServerTerminalEndpoint serverChecked)
  assert (requestReplyServerReplyText serverChecked == "pong")
    "server reply literal changed"
  let clientKeys =
        [ grammarV1ResolvedBinderKey (requestReplyClientPayload clientChecked)
        , grammarV1ResolvedBinderKey (requestReplyClientInitialEndpoint clientChecked)
        , grammarV1ResolvedBinderKey (requestReplyClientReplyEndpoint clientChecked)
        , grammarV1ResolvedBinderKey (requestReplyClientTerminalEndpoint clientChecked)
        , grammarV1ResolvedBinderKey (requestReplyClientReplyValue clientChecked)
        , grammarV1ResolvedBinderKey (requestReplyClientWriteDecision clientChecked)
        ]
  assert (length clientKeys == length (unique clientKeys))
    "client request/reply binders collapsed identities"

clientOutputMustUseReply :: Either String ()
clientOutputMustUseReply = do
  (_, client, _) <- parseFixture $
    Text.replace "console_write(reply)" "console_write(payload)" source
  case grammarV1CheckedRequestReplyClient clientKey client of
    Just (Left (GrammarV1RequestReplyOutputArgumentMismatch expected actual)) -> do
      assert (grammarV1ResolvedBinderDisplayName expected == "reply")
        "output mismatch did not retain reply binder"
      assert (grammarV1ResolvedBinderDisplayName actual == "payload")
        "output mismatch did not retain actual payload binder"
    other -> Left ("client wrote non-reply value without exact rejection: " <> show other)

clientReceiveMustUseSuccessor :: Either String ()
clientReceiveMustUseSuccessor = do
  (_, client, _) <- parseFixture $
    Text.replace "receive String on awaiting" "receive String on endpoint" source
  case grammarV1CheckedRequestReplyClient clientKey client of
    Just (Left (GrammarV1RequestReplyEndpointMismatch role expected actual)) -> do
      assert (role == "send successor -> receive endpoint")
        "client endpoint mismatch named wrong edge"
      assert (grammarV1ResolvedBinderDisplayName expected == "awaiting")
        "client endpoint mismatch lost send successor"
      assert (grammarV1ResolvedBinderDisplayName actual == "endpoint")
        "client endpoint mismatch lost actual endpoint"
    other -> Left ("client reused predecessor endpoint: " <> show other)

clientReplyTypeMustBeString :: Either String ()
clientReplyTypeMustBeString = do
  (_, client, _) <- parseFixture $
    Text.replace "receive String on awaiting" "receive U8 on awaiting" source
  case grammarV1CheckedRequestReplyClient clientKey client of
    Just (Left (GrammarV1RequestReplyReceiveTypeMismatch
      (GrammarV1UnsignedType "String")
      (GrammarV1UnsignedType "U8"))) -> Right ()
    other -> Left ("client wrong reply type did not reject exactly: " <> show other)

serverSendMustUseSuccessor :: Either String ()
serverSendMustUseSuccessor = do
  (_, _, server) <- parseFixture $
    Text.replace "send \"pong\" on replyEndpoint" "send \"pong\" on endpoint" source
  case grammarV1CheckedRequestReplyServer serverKey server of
    Just (Left (GrammarV1RequestReplyEndpointMismatch role expected actual)) -> do
      assert (role == "receive successor -> send endpoint")
        "server endpoint mismatch named wrong edge"
      assert (grammarV1ResolvedBinderDisplayName expected == "replyEndpoint")
        "server endpoint mismatch lost receive successor"
      assert (grammarV1ResolvedBinderDisplayName actual == "endpoint")
        "server endpoint mismatch lost actual predecessor"
    other -> Left ("server reused predecessor endpoint: " <> show other)

serverReplyMustBeStringLiteral :: Either String ()
serverReplyMustBeStringLiteral = do
  (_, _, server) <- parseFixture $
    Text.replace "send \"pong\" on replyEndpoint" "send request on replyEndpoint" source
  case grammarV1CheckedRequestReplyServer serverKey server of
    Just (Left GrammarV1RequestReplyReplyLiteralRequired) -> Right ()
    other -> Left ("server non-String reply entered Stage-2 carrier: " <> show other)

unrelatedBodyStaysOutside :: Either String ()
unrelatedBodyStaysOutside = do
  (_, client, _) <- parseFixture $
    Text.replace clientBody "  payload;\n" source
  case grammarV1CheckedRequestReplyClient clientKey client of
    Nothing -> Right ()
    other -> Left ("unrelated body entered request/reply competence: " <> show other)

requireClient
  :: GrammarV1ComponentDecl
  -> Either String GrammarV1CheckedRequestReplyClient
requireClient component = case grammarV1CheckedRequestReplyClient clientKey component of
  Just (Right value) -> Right value
  other -> Left ("expected checked request/reply client, got " <> show other)

requireServer
  :: GrammarV1ComponentDecl
  -> Either String GrammarV1CheckedRequestReplyServer
requireServer component = case grammarV1CheckedRequestReplyServer serverKey component of
  Just (Right value) -> Right value
  other -> Left ("expected checked request/reply server, got " <> show other)

parseFixture
  :: Text
  -> Either String (GrammarV1ProtocolDecl, GrammarV1ComponentDecl, GrammarV1ComponentDecl)
parseFixture input = do
  parsed <- mapLeft show $
    parseGrammarV1StructuralSource "int009-request-reply-source" input
  case grammarV1TopLevelDecls parsed of
    [ Located _ protocolTop
      , Located _ clientTop
      , Located _ serverTop
      ] -> do
        protocol <- case locatedValue (grammarV1Declaration protocolTop) of
          GrammarV1ProtocolDeclaration value -> Right value
          other -> Left ("expected protocol declaration, got " <> show other)
        client <- componentNamed "ClientWorker" clientTop
        server <- componentNamed "ServerWorker" serverTop
        Right (protocol, client, server)
    declarations -> Left
      ("expected protocol and two components, got "
        <> show (length declarations) <> " declarations")

componentNamed
  :: Text
  -> GrammarV1TopLevelDecl
  -> Either String GrammarV1ComponentDecl
componentNamed expected top = case locatedValue (grammarV1Declaration top) of
  GrammarV1ComponentDeclaration value
    | locatedValue (grammarV1ComponentName value) == expected -> Right value
    | otherwise -> Left ("unexpected component declaration: " <> show value)
  other -> Left ("expected component declaration, got " <> show other)

assertBinder
  :: Text
  -> GrammarV1BinderKind
  -> GrammarV1ResolvedBinder
  -> Either String ()
assertBinder expectedName expectedKind binder = do
  assert (grammarV1ResolvedBinderDisplayName binder == expectedName)
    ("binder display name drifted: " <> show binder)
  assert (grammarV1ResolvedBinderKind binder == expectedKind)
    ("binder kind drifted: " <> show binder)

unique :: Eq a => [a] -> [a]
unique = foldr (\value seen -> if value `elem` seen then seen else value : seen) []

source :: Text
source = Text.unlines
  [ "protocol PingRoundTrip {"
  , "  role Client = send (x : U8) then receive (reply : String) then end Done;"
  , "  role Server = receive (x : U8) then send (reply : String) then end Done;"
  , "}"
  , "component ClientWorker(endpoint : Client[PingRoundTrip], payload : U8) {"
  , clientBody
  , "}"
  , "component ServerWorker(endpoint : Server[PingRoundTrip]) {"
  , "  let (replyEndpoint, request) = receive U8 on endpoint;"
  , "  let done = send \"pong\" on replyEndpoint;"
  , "  close done;"
  , "}"
  ]

clientBody :: Text
clientBody = Text.unlines
  [ "  let awaiting = send payload on endpoint;"
  , "  let (done, reply) = receive String on awaiting;"
  , "  let writeDecision = console_write(reply);"
  , "  close done;"
  ]

protocolKey, clientKey, serverKey :: DeclarationKey
protocolKey = DeclarationKey "protocol.ping-round-trip"
clientKey = DeclarationKey "component.ClientWorker"
serverKey = DeclarationKey "component.ServerWorker"

protocolInterface :: InterfaceRevision
protocolInterface = InterfaceRevision "protocol.ping-round-trip.v1"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
