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
    [ testIO "SURF-002 static process-network fixture preserves architecture and program"
        expectStaticProcessNetwork
    , testIO "SURF-003 process missing target rejects at syntax"
        (expectFixtureReject "rejected/23-process-missing-target.phil")
    , test "SURF-002 architecture ref and bind preserve qualified names"
        architectureRefBindPreserved
    , test "SURF-003 architecture ref and bind reject static arguments"
        architectureRefBindRejectStaticArguments
    , test "SURF-002 unimplemented architecture items remain fail closed"
        (expectReject unimplementedArchitectureItem)
    , test "SURF-002 unimplemented program blocks remain fail closed"
        (expectReject unimplementedProgramBlock)
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectStaticProcessNetwork :: IO (Either String ())
expectStaticProcessNetwork = do
  parsed <- parseFixture "accepted/27-static-process-network.phil"
  pure $ do
    sourceFile <- mapLeft show parsed
    case grammarV1TopLevelDecls sourceFile of
      [Located _ componentTop, Located _ architectureTop, Located _ programTop] -> do
        case locatedValue (grammarV1Declaration componentTop) of
          GrammarV1ComponentDeclaration componentDecl ->
            assert (locatedValue (grammarV1ComponentName componentDecl) == "Worker")
              "component declaration was not Worker"
          other -> Left ("expected Worker component first, got " <> show other)
        case locatedValue (grammarV1Declaration architectureTop) of
          GrammarV1ArchitectureDeclaration architectureDecl -> do
            assert (locatedValue (grammarV1ArchitectureName architectureDecl) == "Pair")
              "architecture declaration was not Pair"
            assert (null (grammarV1ArchitectureGenericParams architectureDecl))
              "Pair unexpectedly acquired generic parameters"
            assert (null (grammarV1ArchitectureRequirements architectureDecl))
              "Pair unexpectedly acquired generic requirements"
            expectArchitectureItems (grammarV1ArchitectureItems architectureDecl)
          other -> Left ("expected Pair architecture second, got " <> show other)
        case locatedValue (grammarV1Declaration programTop) of
          GrammarV1ProgramDeclaration programDecl -> do
            assert (locatedValue (grammarV1ProgramName programDecl) == "main")
              "program declaration was not main"
            assert (staticReferenceNamed "Pair" (grammarV1ProgramTarget programDecl))
              "program target was not the static reference Pair"
          other -> Left ("expected main program third, got " <> show other)
      declarations -> Left ("expected component, architecture, and program; got " <> show (length declarations))

architectureRefBindPreserved :: Either String ()
architectureRefBindPreserved = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "architecture-ref-bind" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ architectureTop, Located _ programTop] -> do
      case locatedValue (grammarV1Declaration architectureTop) of
        GrammarV1ArchitectureDeclaration architectureDecl ->
          case grammarV1ArchitectureItems architectureDecl of
            [ Located _ (GrammarV1ArchitectureRef alias refTarget)
              , Located _ (GrammarV1ArchitectureBind bindSource bindTarget)
              ] -> do
                assert (locatedValue alias == "service")
                  "architecture ref alias was not service"
                assert (qualifiedNameParts refTarget == ["cluster", "worker"])
                  "architecture ref target was not cluster.worker"
                assert (qualifiedNameParts bindSource == ["client", "port"])
                  "architecture bind source was not client.port"
                assert (qualifiedNameParts bindTarget == ["server", "port"])
                  "architecture bind target was not server.port"
            other -> Left ("unexpected ref/bind architecture items " <> show other)
        other -> Left ("expected architecture declaration first, got " <> show other)
      case locatedValue (grammarV1Declaration programTop) of
        GrammarV1ProgramDeclaration programDecl ->
          assert (staticReferenceNamed "Wiring" (grammarV1ProgramTarget programDecl))
            "program target was not Wiring"
        other -> Left ("expected program declaration second, got " <> show other)
    declarations -> Left ("expected architecture and program; got " <> show (length declarations))
  where
    source = Text.unlines
      [ "architecture Wiring {"
      , "  ref service = cluster.worker;"
      , "  bind client.port = server.port;"
      , "}"
      , "program main = instantiate Wiring;"
      ]

architectureRefBindRejectStaticArguments :: Either String ()
architectureRefBindRejectStaticArguments = do
  expectReject "architecture A { ref service = Cluster[U32]; } program main = instantiate A;"
  expectReject "architecture A { bind client[U32] = server.port; } program main = instantiate A;"

expectArchitectureItems
  :: [Located GrammarV1ArchitectureItem]
  -> Either String ()
expectArchitectureItems items = case items of
  [ Located _ (GrammarV1ArchitectureInstance left leftTarget)
    , Located _ (GrammarV1ArchitectureInstance right rightTarget)
    , Located _ (GrammarV1ArchitectureProcess leftRun leftProcessTarget)
    , Located _ (GrammarV1ArchitectureProcess rightRun rightProcessTarget)
    ] -> do
      assert (locatedValue left == "left") "first instance was not left"
      assert (staticReferenceNamed "Worker" leftTarget)
        "left instance target was not Worker"
      assert (locatedValue right == "right") "second instance was not right"
      assert (staticReferenceNamed "Worker" rightTarget)
        "right instance target was not Worker"
      assert (locatedValue leftRun == "left_run") "first process was not left_run"
      assert (qualifiedNameNamed "left" leftProcessTarget)
        "left_run process target was not left"
      assert (locatedValue rightRun == "right_run") "second process was not right_run"
      assert (qualifiedNameNamed "right" rightProcessTarget)
        "right_run process target was not right"
  other -> Left ("expected two instances followed by two processes, got " <> show other)

staticReferenceNamed :: Text.Text -> Located GrammarV1StaticReference -> Bool
staticReferenceNamed expected (Located _ reference) =
  grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected]
    && null (grammarV1StaticReferenceArguments reference)

qualifiedNameNamed :: Text.Text -> Located GrammarV1QualifiedName -> Bool
qualifiedNameNamed expected (Located _ name) =
  grammarV1QualifiedNameParts name == [expected]

qualifiedNameParts :: Located GrammarV1QualifiedName -> [Text.Text]
qualifiedNameParts (Located _ name) =
  grammarV1QualifiedNameParts name

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

expectReject :: Text.Text -> Either String ()
expectReject source = case parseGrammarV1StructuralSource "fail-closed" source of
  Left _ -> Right ()
  Right value -> Left ("expected fail-closed rejection, parsed " <> show value)

unimplementedArchitectureItem :: Text.Text
unimplementedArchitectureItem = Text.unlines
  [ "architecture A {"
  , "  constraint true;"
  , "}"
  , "program main = instantiate A;"
  ]

unimplementedProgramBlock :: Text.Text
unimplementedProgramBlock = Text.unlines
  [ "architecture A {}"
  , "program main = instantiate A {"
  , "  observable x;"
  , "};"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
