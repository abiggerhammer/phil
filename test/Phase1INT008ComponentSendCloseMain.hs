{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Static (DeclarationKey (..))
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey (..)
  , GrammarV1BinderKind (..)
  , GrammarV1BinderScopeError (..)
  , GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.ComponentSendClose
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ComponentDecl
  , GrammarV1Declaration (..)
  , GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..)
  , parseGrammarV1StructuralSource
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "INT-008 source send/close retains exact component parameter and successor binders"
        exactSendCloseBinds
    , test "INT-008 close must consume the exact send successor binder"
        closePredecessorRejects
    , test "INT-008 send payload must resolve to an active local binder"
        missingPayloadRejects
    , test "INT-008 send successor cannot shadow a live component parameter"
        successorShadowingRejects
    , test "INT-008 bounded send/close slice requires one identifier successor"
        tupleSuccessorRejects
    , test "INT-008 unrelated component body stays outside send/close competence"
        unrelatedBodyIsNotCompetent
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactSendCloseBinds :: Either String ()
exactSendCloseBinds = do
  component <- parseComponent exactSource
  checked <- requireChecked component
  let payload = checkedComponentSendPayload checked
      endpoint = checkedComponentSendEndpoint checked
      successor = checkedComponentSendSuccessor checked
  assertBinder endpoint "endpoint" GrammarV1ComponentParameterBinder 0
  assertBinder payload "payload" GrammarV1ComponentParameterBinder 1
  assertBinder successor "done" GrammarV1LetPatternBinder 2
  assert
    (grammarV1ResolvedBinderCoreName endpoint
      /= grammarV1ResolvedBinderCoreName payload)
    "endpoint and payload collapsed to one semantic Core name"
  assert
    (grammarV1ResolvedBinderCoreName successor
      /= grammarV1ResolvedBinderCoreName endpoint)
    "send successor reused the endpoint parameter identity"

closePredecessorRejects :: Either String ()
closePredecessorRejects = do
  component <- parseComponent closeEndpointSource
  case grammarV1CheckedComponentSendClose componentKey component of
    Just (Left (GrammarV1ComponentSendCloseCloseMismatch expected actual)) -> do
      assert (grammarV1ResolvedBinderDisplayName expected == "done")
        "close mismatch lost exact send successor"
      assert (grammarV1ResolvedBinderDisplayName actual == "endpoint")
        "close mismatch lost exact source close operand"
    other -> Left ("closing the predecessor endpoint was not rejected exactly: " <> show other)

missingPayloadRejects :: Either String ()
missingPayloadRejects = do
  component <- parseComponent missingPayloadSource
  case grammarV1CheckedComponentSendClose componentKey component of
    Just (Left (GrammarV1ComponentSendCloseOperandNotLocal "send payload")) -> Right ()
    other -> Left ("unknown send payload did not fail closed: " <> show other)

successorShadowingRejects :: Either String ()
successorShadowingRejects = do
  component <- parseComponent shadowingSource
  case grammarV1CheckedComponentSendClose componentKey component of
    Just (Left (GrammarV1ComponentSendCloseBinderError
      (GrammarV1ActiveShadowing sourceName previous))) -> do
        assert (locatedValue sourceName == "payload")
          "shadowing diagnostic changed successor spelling"
        assert (grammarV1ResolvedBinderDisplayName previous == "payload")
          "shadowing diagnostic lost active component parameter"
    other -> Left ("successor shadowing was not rejected exactly: " <> show other)

tupleSuccessorRejects :: Either String ()
tupleSuccessorRejects = do
  component <- parseComponent tupleSuccessorSource
  case grammarV1CheckedComponentSendClose componentKey component of
    Just (Left GrammarV1ComponentSendCloseSuccessorNotIdentifier) -> Right ()
    other -> Left ("tuple send successor entered the bounded slice: " <> show other)

unrelatedBodyIsNotCompetent :: Either String ()
unrelatedBodyIsNotCompetent = do
  component <- parseComponent unrelatedSource
  case grammarV1CheckedComponentSendClose componentKey component of
    Nothing -> Right ()
    other -> Left ("unrelated body was claimed by send/close slice: " <> show other)

requireChecked
  :: GrammarV1ComponentDecl
  -> Either String GrammarV1CheckedComponentSendClose
requireChecked component =
  case grammarV1CheckedComponentSendClose componentKey component of
    Just (Right checked) -> Right checked
    other -> Left ("expected checked send/close body, got " <> show other)

assertBinder
  :: GrammarV1ResolvedBinder
  -> Text
  -> GrammarV1BinderKind
  -> Int
  -> Either String ()
assertBinder binder expectedName expectedKind expectedOrdinal = do
  assert (grammarV1ResolvedBinderDisplayName binder == expectedName)
    ("binder display spelling changed for " <> Text.unpack expectedName)
  assert (grammarV1ResolvedBinderKind binder == expectedKind)
    ("binder kind changed for " <> Text.unpack expectedName)
  case grammarV1ResolvedBinderKey binder of
    GrammarV1BinderKey declarationKey ordinal -> do
      assert (declarationKey == componentKey)
        ("binder declaration root changed for " <> Text.unpack expectedName)
      assert (ordinal == expectedOrdinal)
        ("binder ordinal changed for " <> Text.unpack expectedName)

parseComponent :: Text -> Either String GrammarV1ComponentDecl
parseComponent source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "int008-component-send-close" source
  case
      [ component
      | Located _ top <- grammarV1TopLevelDecls sourceFile
      , GrammarV1ComponentDeclaration component <-
          [locatedValue (grammarV1Declaration top)]
      ] of
    [component] -> Right component
    components -> Left
      ("expected exactly one component declaration, got " <> show (length components))

componentKey :: DeclarationKey
componentKey = DeclarationKey "component.ClientWorker"

protocolSource :: [Text]
protocolSource =
  [ "protocol Ping {"
  , "  role Client = send (x : U8) then end Done;"
  , "  role Server = receive (x : U8) then end Done;"
  , "}"
  ]

componentSource :: [Text] -> Text
componentSource body = Text.unlines $
  protocolSource <>
  [ "component ClientWorker(endpoint : Client[Ping], payload : U8) {" ] <>
  map ("  " <>) body <>
  [ "}" ]

exactSource :: Text
exactSource = componentSource
  [ "let done = send payload on endpoint;"
  , "close done;"
  ]

closeEndpointSource :: Text
closeEndpointSource = componentSource
  [ "let done = send payload on endpoint;"
  , "close endpoint;"
  ]

missingPayloadSource :: Text
missingPayloadSource = componentSource
  [ "let done = send missing on endpoint;"
  , "close done;"
  ]

shadowingSource :: Text
shadowingSource = componentSource
  [ "let payload = send payload on endpoint;"
  , "close payload;"
  ]

tupleSuccessorSource :: Text
tupleSuccessorSource = componentSource
  [ "let (done, extra) = send payload on endpoint;"
  , "close done;"
  ]

unrelatedSource :: Text
unrelatedSource = componentSource
  [ "payload;" ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
