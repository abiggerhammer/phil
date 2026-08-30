{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ testIO "SURF-002 external protocol-participant fixture preserves sessions and role targets"
        expectExternalParticipant
    , testIO "SURF-003 external role with extra target rejects at syntax"
        (expectFixtureReject "rejected/24-external-role-extra-target.phil")
    , test "SURF-002 send/receive preserve optional boundary and guard clauses"
        optionalSessionClausesPreserved
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectExternalParticipant :: IO (Either String ())
expectExternalParticipant = do
  parsed <- parseFixture "accepted/28-external-protocol-participant.phil"
  pure $ do
    sourceFile <- mapLeft show parsed
    case grammarV1TopLevelDecls sourceFile of
      [Located _ protocolTop, Located _ componentTop, Located _ architectureTop, Located _ programTop] -> do
        case locatedValue (grammarV1Declaration protocolTop) of
          GrammarV1ProtocolDeclaration protocolDecl -> expectPingProtocol protocolDecl
          other -> Left ("expected Ping protocol first, got " <> show other)
        case locatedValue (grammarV1Declaration componentTop) of
          GrammarV1ComponentDeclaration componentDecl ->
            assert (locatedValue (grammarV1ComponentName componentDecl) == "ClientWorker")
              "component declaration was not ClientWorker"
          other -> Left ("expected ClientWorker component second, got " <> show other)
        case locatedValue (grammarV1Declaration architectureTop) of
          GrammarV1ArchitectureDeclaration architectureDecl ->
            expectExternalArchitecture architectureDecl
          other -> Left ("expected ExternalPeer architecture third, got " <> show other)
        case locatedValue (grammarV1Declaration programTop) of
          GrammarV1ProgramDeclaration programDecl -> do
            assert (locatedValue (grammarV1ProgramName programDecl) == "main")
              "program declaration was not main"
            assert (staticReferenceNamed "ExternalPeer" (grammarV1ProgramTarget programDecl))
              "program target was not ExternalPeer"
          other -> Left ("expected main program fourth, got " <> show other)
      declarations -> Left ("expected four top-level declarations, got " <> show (length declarations))

expectPingProtocol :: GrammarV1ProtocolDecl -> Either String ()
expectPingProtocol protocolDecl = do
  assert (locatedValue (grammarV1ProtocolName protocolDecl) == "Ping")
    "protocol name was not Ping"
  case grammarV1ProtocolRoles protocolDecl of
    [Located _ clientRole, Located _ serverRole] -> do
      assert (locatedValue (grammarV1RoleSessionName clientRole) == "Client")
        "first role was not Client"
      expectSendSession (grammarV1RoleSessionExpression clientRole)
      assert (locatedValue (grammarV1RoleSessionName serverRole) == "Server")
        "second role was not Server"
      expectReceiveSession (grammarV1RoleSessionExpression serverRole)
    roles -> Left ("expected two protocol roles, got " <> show roles)

expectSendSession :: Located GrammarV1SessionExpression -> Either String ()
expectSendSession (Located _ session) = case session of
  GrammarV1SessionSend param Nothing Nothing continuation ->
    checkParamAndEnd "x" param continuation
  other -> Left ("expected send session, got " <> show other)

expectReceiveSession :: Located GrammarV1SessionExpression -> Either String ()
expectReceiveSession (Located _ session) = case session of
  GrammarV1SessionReceive param Nothing Nothing continuation ->
    checkParamAndEnd "x" param continuation
  other -> Left ("expected receive session, got " <> show other)

checkParamAndEnd
  :: Text.Text
  -> Located GrammarV1TermParam
  -> Located GrammarV1SessionExpression
  -> Either String ()
checkParamAndEnd expectedName (Located _ param) (Located _ continuation) = do
  assert (locatedValue (grammarV1TermParamName param) == expectedName)
    "session parameter name was not preserved"
  assert (locatedValue (grammarV1TermParamType param) == GrammarV1UnsignedType "U8")
    "session parameter type was not U8"
  case continuation of
    GrammarV1SessionEnd label ->
      assert (locatedValue label == "Done") "session end label was not Done"
    other -> Left ("expected end Done continuation, got " <> show other)

expectExternalArchitecture :: GrammarV1ArchitectureDecl -> Either String ()
expectExternalArchitecture architectureDecl = do
  assert (locatedValue (grammarV1ArchitectureName architectureDecl) == "ExternalPeer")
    "architecture name was not ExternalPeer"
  case grammarV1ArchitectureItems architectureDecl of
    [ Located _ (GrammarV1ArchitectureInstance instanceName component)
      , Located _ (GrammarV1ArchitectureProcess processName processTarget)
      , Located _ (GrammarV1ArchitectureProtocol protocolName protocolTarget)
      , Located _ (GrammarV1ArchitectureRole clientRole clientTarget)
      , Located _ (GrammarV1ArchitectureRole serverRole serverTarget)
      ] -> do
        assert (locatedValue instanceName == "client") "instance name was not client"
        assert (staticReferenceNamed "ClientWorker" component)
          "client instance target was not ClientWorker"
        assert (locatedValue processName == "client_run") "process name was not client_run"
        assert (qualifiedNameNamed ["client"] processTarget)
          "process target was not client"
        assert (locatedValue protocolName == "ping") "protocol occurrence was not ping"
        assert (staticReferenceNamed "Ping" protocolTarget)
          "protocol target was not Ping"
        assert (qualifiedNameNamed ["ping", "Client"] clientRole)
          "internal role path was not ping.Client"
        expectInternalTarget ["client"] clientTarget
        assert (qualifiedNameNamed ["ping", "Server"] serverRole)
          "external role path was not ping.Server"
        expectExternalTarget serverTarget
    items -> Left ("unexpected architecture items " <> show items)

expectInternalTarget
  :: [Text.Text]
  -> Located GrammarV1RoleTarget
  -> Either String ()
expectInternalTarget expected (Located _ target) = case target of
  GrammarV1InternalRoleTarget name ->
    assert (qualifiedNameNamed expected name) "internal role target was not preserved"
  other -> Left ("expected internal role target, got " <> show other)

expectExternalTarget :: Located GrammarV1RoleTarget -> Either String ()
expectExternalTarget (Located _ target) = case target of
  GrammarV1ExternalRoleTarget -> Right ()
  other -> Left ("expected external role target, got " <> show other)

optionalSessionClausesPreserved :: Either String ()
optionalSessionClausesPreserved = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "session-options" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ProtocolDeclaration protocolDecl ->
        case grammarV1ProtocolRoles protocolDecl of
          [Located _ firstRole, Located _ secondRole] -> do
            expectSendOptions (grammarV1RoleSessionExpression firstRole)
            expectReceiveOptions (grammarV1RoleSessionExpression secondRole)
          roles -> Left ("expected two roles, got " <> show roles)
      other -> Left ("expected protocol declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))
  where
    source = Text.unlines
      [ "protocol P {"
      , "  role A = send (x : U8) using Wire when true then end Done;"
      , "  role B = receive (y : U8) using Wire when false then end Done;"
      , "}"
      ]

expectSendOptions :: Located GrammarV1SessionExpression -> Either String ()
expectSendOptions (Located _ session) = case session of
  GrammarV1SessionSend param (Just wire) (Just guard) continuation -> do
    assert (staticReferenceNamed "Wire" wire) "send using target was not Wire"
    assert (locatedValue guard == GrammarV1TrueProposition)
      "send guard proposition was not true"
    checkParamAndEnd "x" param continuation
  other -> Left ("expected send session with optional clauses, got " <> show other)

expectReceiveOptions :: Located GrammarV1SessionExpression -> Either String ()
expectReceiveOptions (Located _ session) = case session of
  GrammarV1SessionReceive param (Just wire) (Just guard) continuation -> do
    assert (staticReferenceNamed "Wire" wire) "receive using target was not Wire"
    assert (locatedValue guard == GrammarV1FalseProposition)
      "receive guard proposition was not false"
    checkParamAndEnd "y" param continuation
  other -> Left ("expected receive session with optional clauses, got " <> show other)

staticReferenceNamed :: Text.Text -> Located GrammarV1StaticReference -> Bool
staticReferenceNamed expected (Located _ reference) =
  grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected]
    && null (grammarV1StaticReferenceArguments reference)

qualifiedNameNamed :: [Text.Text] -> Located GrammarV1QualifiedName -> Bool
qualifiedNameNamed expected (Located _ name) =
  grammarV1QualifiedNameParts name == expected

expectFixtureReject :: FilePath -> IO (Either String ())
expectFixtureReject relativePath = do
  parsed <- parseFixture relativePath
  pure $ case parsed of
    Left _ -> Right ()
    Right value -> Left ("expected syntax rejection, parsed " <> show value)

parseFixture
  :: FilePath
  -> IO (Either GrammarV1ParseDiagnostic GrammarV1SourceFile)
parseFixture relativePath = do
  let path = "test/fixtures/phase1-surface/" <> relativePath
  source <- TextIO.readFile path
  pure (parseGrammarV1StructuralSource (Text.pack relativePath) source)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
