{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Scalar (ScalarLiteral (..))
import Phil.Core.Static (DeclarationKey (..))
import Phil.Surface.GrammarV1.BoundedPingSourceValues
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "INT-009 bounded Ping derives exact request/reply values from source"
        exactValues
    , test "INT-009 bounded Ping rejects out-of-range request literals"
        requestRangeRejects
    , test "INT-009 bounded Ping output must use the received reply binder"
        outputBinderRejects
    , test "INT-009 bounded Ping reply must come from a source String literal"
        replyLiteralRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactValues :: Either String ()
exactValues = do
  (client, server) <- parseFixture source
  values <- requireValues client server
  assert (boundedPingSourceRequestValue values == ScalarUIntLiteral 8 42)
    "request byte did not come from the explicit send literal"
  assert (boundedPingSourceReplyText values == "pong")
    "reply text did not come from the explicit server send literal"

requestRangeRejects :: Either String ()
requestRangeRejects = do
  (client, server) <- parseFixture $
    Text.replace "send 42 on selected" "send 256 on selected" source
  case grammarV1CheckedBoundedPingSourceValues clientKey client serverKey server of
    Just (Left (GrammarV1BoundedPingSourceValuesRequestOutOfRange 256)) -> Right ()
    other -> Left ("out-of-range request did not reject exactly: " <> show other)

outputBinderRejects :: Either String ()
outputBinderRejects = do
  (client, server) <- parseFixture $
    Text.replace "console_write(reply)" "console_write(selected)" source
  case grammarV1CheckedBoundedPingSourceValues clientKey client serverKey server of
    Just (Left (GrammarV1BoundedPingSourceValuesReferenceMismatch "console_write reply")) -> Right ()
    other -> Left ("wrong output binder did not reject exactly: " <> show other)

replyLiteralRejects :: Either String ()
replyLiteralRejects = do
  (client, server) <- parseFixture $
    Text.replace "send \"pong\" on replyEndpoint" "send request on replyEndpoint" source
  case grammarV1CheckedBoundedPingSourceValues clientKey client serverKey server of
    Just (Left (GrammarV1BoundedPingSourceValuesServerShape "reply must be a String literal")) -> Right ()
    other -> Left ("nonliteral reply did not reject exactly: " <> show other)

requireValues
  :: GrammarV1ComponentDecl
  -> GrammarV1ComponentDecl
  -> Either String GrammarV1BoundedPingSourceValues
requireValues client server =
  case grammarV1CheckedBoundedPingSourceValues clientKey client serverKey server of
    Just (Right values) -> Right values
    other -> Left ("expected bounded Ping source values, got " <> show other)

parseFixture
  :: Text
  -> Either String (GrammarV1ComponentDecl, GrammarV1ComponentDecl)
parseFixture input = do
  parsed <- mapLeft show $
    parseGrammarV1StructuralSource "int009-bounded-ping-source-values" input
  case grammarV1TopLevelDecls parsed of
    [Located _ clientTop, Located _ serverTop] -> do
      client <- component "ClientRound" clientTop
      server <- component "ServerRound" serverTop
      Right (client, server)
    declarations -> Left
      ("expected two round-template components, got "
        <> show (length declarations) <> " declarations")

component
  :: Text
  -> GrammarV1TopLevelDecl
  -> Either String GrammarV1ComponentDecl
component expected top = case locatedValue (grammarV1Declaration top) of
  GrammarV1ComponentDeclaration value
    | locatedValue (grammarV1ComponentName value) == expected -> Right value
    | otherwise -> Left ("unexpected component name: " <> show value)
  other -> Left ("expected component declaration, got " <> show other)

source :: Text
source = Text.unlines
  [ "component ClientRound(endpoint : Client[PingCount], count : U32) {"
  , "  loop state (currentEndpoint = endpoint, remaining : U32 = count) {"
  , "    let selected = select Ping on currentEndpoint;"
  , "    let awaiting = send 42 on selected;"
  , "    let (nextEndpoint, reply) = receive String on awaiting;"
  , "    let writeDecision = console_write(reply);"
  , "    let nextRemaining = remaining - 1;"
  , "    continue (nextEndpoint, nextRemaining);"
  , "  };"
  , "}"
  , "component ServerRound(endpoint : Server[PingCount]) {"
  , "  loop state (currentEndpoint = endpoint) {"
  , "    let (replyEndpoint, request) = receive U8 on currentEndpoint;"
  , "    let nextEndpoint = send \"pong\" on replyEndpoint;"
  , "    continue (nextEndpoint);"
  , "  };"
  , "}"
  ]

clientKey, serverKey :: DeclarationKey
clientKey = DeclarationKey "component.ClientRound"
serverKey = DeclarationKey "component.ServerRound"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
