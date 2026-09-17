{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Protocol.Family (BinaryProtocolFamily)
import Phil.Core.Static
  ( DeclarationKey (..)
  , InterfaceRevision (..)
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (..)
  , GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.BoundedPingLoopSource
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolRoles
  ( grammarV1ClosedBinaryProtocolFamily
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "INT-009 bounded Ping protocol is guarded recursive Ping/Done"
        recursiveProtocolShape
    , test "INT-009 bounded Ping loop carries exact endpoint and count state"
        exactLoopStateSpine
    , test "INT-009 bounded Ping continue must supply both state values"
        continueArityRejects
    , test "INT-009 bounded Ping continue preserves endpoint/count order"
        continueOrderRejects
    , test "INT-009 bounded Ping count state begins at the count parameter"
        countInitializerRejects
    , test "INT-009 bounded Ping Done branch must actually terminate"
        doneBranchMustTerminate
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

recursiveProtocolShape :: Either String ()
recursiveProtocolShape = do
  (protocol, _) <- parseFixture source
  family <- requireFamily protocol
  mapLeft show (grammarV1CheckBoundedPingProtocol family)

exactLoopStateSpine :: Either String ()
exactLoopStateSpine = do
  (_, component) <- parseFixture source
  checked <- requireLoop component
  assertBinder "endpoint" GrammarV1ComponentParameterBinder
    (boundedPingEndpointParameter checked)
  assertBinder "count" GrammarV1ComponentParameterBinder
    (boundedPingCountParameter checked)
  assertBinder "currentEndpoint" GrammarV1LoopStateBinder
    (boundedPingEndpointState checked)
  assertBinder "remaining" GrammarV1LoopStateBinder
    (boundedPingCountState checked)
  let keys =
        [ grammarV1ResolvedBinderKey (boundedPingEndpointParameter checked)
        , grammarV1ResolvedBinderKey (boundedPingCountParameter checked)
        , grammarV1ResolvedBinderKey (boundedPingEndpointState checked)
        , grammarV1ResolvedBinderKey (boundedPingCountState checked)
        ]
  assert (length keys == length (unique keys))
    "bounded Ping parameter/loop-state binder identities collapsed"

continueArityRejects :: Either String ()
continueArityRejects = do
  (_, component) <- parseFixture $
    Text.replace
      "continue (currentEndpoint, remaining);"
      "continue (currentEndpoint);"
      source
  case grammarV1CheckedBoundedPingLoop componentKey component of
    Just (Left (GrammarV1BoundedPingContinueArity 1)) -> Right ()
    other -> Left ("one-actual continue did not reject exactly: " <> show other)

continueOrderRejects :: Either String ()
continueOrderRejects = do
  (_, component) <- parseFixture $
    Text.replace
      "continue (currentEndpoint, remaining);"
      "continue (remaining, currentEndpoint);"
      source
  case grammarV1CheckedBoundedPingLoop componentKey component of
    Just (Left (GrammarV1BoundedPingContinueActualMismatch 0 "remaining")) -> Right ()
    other -> Left ("swapped loop state did not reject exactly: " <> show other)

countInitializerRejects :: Either String ()
countInitializerRejects = do
  (_, component) <- parseFixture $
    Text.replace
      "remaining : U32 = count"
      "remaining : U32 = 0"
      source
  case grammarV1CheckedBoundedPingLoop componentKey component of
    Just (Left (GrammarV1BoundedPingInitializerNotSimple "remaining")) -> Right ()
    other -> Left ("literal count initializer did not reject exact provenance: " <> show other)

doneBranchMustTerminate :: Either String ()
doneBranchMustTerminate = do
  (protocol, _) <- parseFixture $
    Text.replace "Done => end Done" "Done => continue Loop" source
  family <- requireFamily protocol
  case grammarV1CheckBoundedPingProtocol family of
    Left (GrammarV1BoundedPingProtocolShapeMismatch _) -> Right ()
    other -> Left ("nonterminal Done branch entered bounded Ping protocol: " <> show other)

requireLoop
  :: GrammarV1ComponentDecl
  -> Either String GrammarV1CheckedBoundedPingLoop
requireLoop component =
  case grammarV1CheckedBoundedPingLoop componentKey component of
    Just (Right value) -> Right value
    other -> Left ("expected bounded Ping loop source carrier, got " <> show other)

requireFamily :: GrammarV1ProtocolDecl -> Either String BinaryProtocolFamily
requireFamily protocol =
  case grammarV1ClosedBinaryProtocolFamily
      protocolKey protocolInterface protocol of
    Just (Right value) -> Right value
    other -> Left ("expected closed recursive PingCount family, got " <> show other)

parseFixture
  :: Text
  -> Either String (GrammarV1ProtocolDecl, GrammarV1ComponentDecl)
parseFixture input = do
  parsed <- mapLeft show $
    parseGrammarV1StructuralSource "int009-bounded-ping-loop" input
  case grammarV1TopLevelDecls parsed of
    [Located _ protocolTop, Located _ componentTop] -> do
      protocol <- case locatedValue (grammarV1Declaration protocolTop) of
        GrammarV1ProtocolDeclaration value -> Right value
        other -> Left ("expected protocol declaration, got " <> show other)
      component <- case locatedValue (grammarV1Declaration componentTop) of
        GrammarV1ComponentDeclaration value -> Right value
        other -> Left ("expected component declaration, got " <> show other)
      Right (protocol, component)
    declarations -> Left
      ("expected protocol and component, got "
        <> show (length declarations) <> " declarations")

source :: Text
source = Text.unlines
  [ "protocol PingCount {"
  , "  role Client = recursive Loop = select {"
  , "    Ping => send (x : U8) then receive (reply : String) then continue Loop |"
  , "    Done => end Done"
  , "  };"
  , "  role Server = recursive Loop = offer {"
  , "    Ping => receive (x : U8) then send (reply : String) then continue Loop |"
  , "    Done => end Done"
  , "  };"
  , "}"
  , "component ClientCounter(endpoint : Client[PingCount], count : U32) {"
  , "  loop state (currentEndpoint = endpoint, remaining : U32 = count) {"
  , "    continue (currentEndpoint, remaining);"
  , "  };"
  , "}"
  ]

assertBinder
  :: Text
  -> GrammarV1BinderKind
  -> GrammarV1ResolvedBinder
  -> Either String ()
assertBinder expectedName expectedKind binder = do
  assert (grammarV1ResolvedBinderDisplayName binder == expectedName)
    ("binder name drifted: " <> show binder)
  assert (grammarV1ResolvedBinderKind binder == expectedKind)
    ("binder kind drifted: " <> show binder)

unique :: Eq a => [a] -> [a]
unique = foldr (\value seen -> if value `elem` seen then seen else value : seen) []

protocolKey, componentKey :: DeclarationKey
protocolKey = DeclarationKey "protocol.ping-count"
componentKey = DeclarationKey "component.ClientCounter"

protocolInterface :: InterfaceRevision
protocolInterface = InterfaceRevision "protocol.ping-count.v1"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
