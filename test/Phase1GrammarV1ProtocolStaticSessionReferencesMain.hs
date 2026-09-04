{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  )
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ProtocolStaticSessionReferences
  ( grammarV1ClosedProtocolRoleSessionReferences
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 closed protocol role session references preserve unresolved static identity"
        closedReferencesPreserved
    , test "SURF-008 protocol display spelling cannot resolve static session identity"
        protocolRenameIsNonsemantic
    , test "SURF-008 static session reference projection preserves duplicate role spelling"
        duplicateRoleSpellingRemainsVisible
    , test "SURF-008 static session references remain unresolved before category checking"
        unresolvedCategoryRemainsUnresolved
    , test "SURF-008 richer static session reference forms remain fail-closed"
        competenceBoundaries
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

closedReferencesPreserved :: Either String ()
closedReferencesPreserved = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol P {"
    , "  role Client = sessions.client.Flow;"
    , "  role Server = sessions.server.Flow;"
    , "}"
    ]
  let expected =
        ( ( ProtocolRoleKey "Client"
          , ReferencedGenericStaticActual "sessions.client.Flow"
          )
        , ( ProtocolRoleKey "Server"
          , ReferencedGenericStaticActual "sessions.server.Flow"
          )
        )
  assert
    (grammarV1ClosedProtocolRoleSessionReferences protocol == Just expected)
    "qualified static session references changed spelling, role order, or unresolved identity"

protocolRenameIsNonsemantic :: Either String ()
protocolRenameIsNonsemantic = do
  first <- onlyProtocol $ Text.unlines
    [ "protocol FirstPresentation {"
    , "  role Client = sessions.Client;"
    , "  role Server = sessions.Server;"
    , "}"
    ]
  renamed <- onlyProtocol $ Text.unlines
    [ "protocol RenamedPresentation {"
    , "  role Client = sessions.Client;"
    , "  role Server = sessions.Server;"
    , "}"
    ]
  assert
    ( grammarV1ClosedProtocolRoleSessionReferences first
        == grammarV1ClosedProtocolRoleSessionReferences renamed
    )
    "protocol declaration display-name change leaked into unresolved role session references"

duplicateRoleSpellingRemainsVisible :: Either String ()
duplicateRoleSpellingRemainsVisible = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol Duplicate {"
    , "  role Same = sessions.Left;"
    , "  role Same = sessions.Right;"
    , "}"
    ]
  let expected =
        ( (ProtocolRoleKey "Same", ReferencedGenericStaticActual "sessions.Left")
        , (ProtocolRoleKey "Same", ReferencedGenericStaticActual "sessions.Right")
        )
  assert
    (grammarV1ClosedProtocolRoleSessionReferences protocol == Just expected)
    "static-session projection normalized or rejected duplicate role spelling before competent role checking"

unresolvedCategoryRemainsUnresolved :: Either String ()
unresolvedCategoryRemainsUnresolved = do
  protocol <- onlyProtocol $ Text.unlines
    [ "protocol Unresolved {"
    , "  role A = maybe.NotASession;"
    , "  role B = maybe.AlsoUnknown;"
    , "}"
    ]
  let expected =
        ( (ProtocolRoleKey "A", ReferencedGenericStaticActual "maybe.NotASession")
        , (ProtocolRoleKey "B", ReferencedGenericStaticActual "maybe.AlsoUnknown")
        )
  assert
    (grammarV1ClosedProtocolRoleSessionReferences protocol == Just expected)
    "unresolved static session projection invented category-resolution authority"

competenceBoundaries :: Either String ()
competenceBoundaries = do
  inline <- onlyProtocol $ Text.unlines
    [ "protocol Inline {"
    , "  role A = send (x : U8) then end Done;"
    , "  role B = receive (y : U8) then end Done;"
    , "}"
    ]
  mixed <- onlyProtocol $ Text.unlines
    [ "protocol Mixed {"
    , "  role A = sessions.A;"
    , "  role B = end Done;"
    , "}"
    ]
  generic <- onlyProtocol $ Text.unlines
    [ "protocol Generic[S : Session] {"
    , "  role A = S;"
    , "  role B = S;"
    , "}"
    ]
  required <- onlyProtocol $ Text.unlines
    [ "protocol Required requires { proposition true; } {"
    , "  role A = sessions.A;"
    , "  role B = sessions.B;"
    , "}"
    ]
  specialized <- onlyProtocol $ Text.unlines
    [ "protocol Specialized {"
    , "  role A = sessions.Flow[U8];"
    , "  role B = sessions.Flow[U8];"
    , "}"
    ]
  mapM_ (\(label, protocol) ->
    assert
      (grammarV1ClosedProtocolRoleSessionReferences protocol == Nothing)
      (label <> " escaped the static-session-reference competence wall"))
    [ ("inline role body", inline)
    , ("mixed inline/reference roles", mixed)
    , ("generic Session binder", generic)
    , ("requirement-bearing protocol", required)
    , ("specialized session reference", specialized)
    ]

onlyProtocol :: Text.Text -> Either String GrammarV1ProtocolDecl
onlyProtocol source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "protocol-static-session-references" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ProtocolDeclaration protocol -> Right protocol
      other -> Left ("expected protocol declaration, got " <> show other)
    declarations -> Left
      ("expected one protocol declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
