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
    [ testIO "SURF-002 static process network fixture preserves architecture occurrences"
        expectStaticProcessNetwork
    , testIO "SURF-003 process missing target rejects at syntax"
        (expectFixtureReject "rejected/23-process-missing-target.phil")
    , test "SURF-002 process target preserves qualified occurrence reference"
        qualifiedProcessTargetPreserved
    , test "SURF-002 program target preserves specialized static reference"
        specializedProgramTargetPreserved
    , test "SURF-002 unsupported architecture item remains fail-closed"
        unsupportedArchitectureItemRejects
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
      [ Located _ componentTop
        , Located _ architectureTop
        , Located _ programTop
        ] -> do
          case locatedValue (grammarV1Declaration componentTop) of
            GrammarV1ComponentDeclaration componentDecl ->
              assert (locatedValue (grammarV1ComponentName componentDecl) == "Worker")
                "component name was not Worker"
            other -> Left ("expected Worker component first, got " <> show other)
          case locatedValue (grammarV1Declaration architectureTop) of
            GrammarV1ArchitectureDeclaration architectureDecl -> do
              assert (locatedValue (grammarV1ArchitectureName architectureDecl) == "Pair")
                "architecture name was not Pair"
              assert (null (grammarV1ArchitectureGenericParams architectureDecl))
                "Pair unexpectedly had generic parameters"
              assert (null (grammarV1ArchitectureRequirements architectureDecl))
                "Pair unexpectedly had generic requirements"
              assertArchitectureItems (grammarV1ArchitectureItems architectureDecl)
          case locatedValue (grammarV1Declaration programTop) of
            GrammarV1ProgramDeclaration programDecl -> do
              assert (locatedValue (grammarV1ProgramName programDecl) == "main")
                "program name was not main"
              assertStaticReference "Pair" [] (grammarV1ProgramTarget programDecl)
          other -> Left ("expected program declaration third, got " <> show other)
      declarations -> Left ("expected component, architecture, program; got " <> show (length declarations))

assertArchitectureItems :: [Located GrammarV1ArchitectureItem] -> Either String ()
assertArchitectureItems items = case items of
  [ Located _ (GrammarV1ArchitectureInstance leftName leftTarget)
    , Located _ (GrammarV1ArchitectureInstance rightName rightTarget)
    , Located _ (GrammarV1ArchitectureProcess leftRun leftOccurrence)
    , Located _ (GrammarV1ArchitectureProcess rightRun rightOccurrence)
    ] -> do
      assert (locatedValue leftName == "left") "first instance name was not left"
      assertStaticReference "Worker" [] leftTarget
      assert (locatedValue rightName == "right") "second instance name was not right"
      assertStaticReference "Worker" [] rightTarget
      assert (locatedValue leftRun == "left_run") "first process name was not left_run"
      assertQualifiedName ["left"] leftOccurrence
      assert (locatedValue rightRun == "right_run") "second process name was not right_run"
      assertQualifiedName ["right"] rightOccurrence
  other -> Left ("unexpected architecture item sequence: " <> show other)

qualifiedProcessTargetPreserved :: Either String ()
qualifiedProcessTargetPreserved = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "qualified-process" source
  architectureDecl <- singleArchitecture sourceFile
  case grammarV1ArchitectureItems architectureDecl of
    [Located _ (GrammarV1ArchitectureProcess name target)] -> do
      assert (locatedValue name == "run") "process name was not run"
      assertQualifiedName ["worker", "endpoint"] target
    other -> Left ("expected one process item, got " <> show other)
  where
    source = "architecture A { process run = worker.endpoint; }"

specializedProgramTargetPreserved :: Either String ()
specializedProgramTargetPreserved = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "specialized-program" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1ProgramDeclaration programDecl ->
        assertStaticReference
          "Pair"
          [GrammarV1StaticTypeArgument (GrammarV1UnsignedType "U32")]
          (grammarV1ProgramTarget programDecl)
      other -> Left ("expected program declaration, got " <> show other)
    declarations -> Left ("expected one program declaration, got " <> show (length declarations))
  where
    source = "program main = instantiate Pair[U32];"

unsupportedArchitectureItemRejects :: Either String ()
unsupportedArchitectureItemRejects =
  expectReject "architecture A { ref x = y; }"

singleArchitecture :: GrammarV1SourceFile -> Either String GrammarV1ArchitectureDecl
singleArchitecture sourceFile = case grammarV1TopLevelDecls sourceFile of
  [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1ArchitectureDeclaration architectureDecl -> Right architectureDecl
    other -> Left ("expected architecture declaration, got " <> show other)
  declarations -> Left ("expected one architecture declaration, got " <> show (length declarations))

assertQualifiedName :: [Text.Text] -> Located GrammarV1QualifiedName -> Either String ()
assertQualifiedName expected (Located _ actual) =
  assert (grammarV1QualifiedNameParts actual == expected) $
    "expected qualified name " <> show expected <> ", got " <> show (grammarV1QualifiedNameParts actual)

assertStaticReference
  :: Text.Text
  -> [GrammarV1StaticArgument]
  -> Located GrammarV1StaticReference
  -> Either String ()
assertStaticReference expectedName expectedArguments (Located _ reference) = do
  assert
    (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expectedName])
    ("static reference name was not " <> Text.unpack expectedName)
  assert
    (grammarV1StaticReferenceArguments reference == expectedArguments)
    "static reference arguments were not preserved"

expectReject :: Text.Text -> Either String ()
expectReject source = case parseGrammarV1StructuralSource "process-network-negative" source of
  Left _ -> Right ()
  Right value -> Left ("expected syntax rejection, parsed " <> show value)

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
