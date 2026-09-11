{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.ReferenceAstArchitectureProgram
  ( GrammarV1ReferenceArchitectureProgramDeclaration
  , grammarV1ProductionArchitectureProgramDeclarations
  , grammarV1ReferenceArchitectureProgramDeclarations
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( grammarV1ReferenceParseSourceTokens
  )
import System.Exit (exitFailure)

corpusRoot :: FilePath
corpusRoot = "test/fixtures/phase1-surface"

data CorpusCase = CorpusCase
  { corpusCaseId :: Text
  , corpusCasePath :: FilePath
  , corpusCaseExpectation :: Text
  }

main :: IO ()
main = do
  input <- TextIO.getContents
  let directCases =
        [ ( "minimal"
          , "architecture A {} program main = instantiate A;"
          , 2
          )
        , ( "rich-all-items"
          , Text.unlines
              [ "architecture Mesh[T: Type] requires { proposition true; } {"
              , "  instance worker = Worker[T];"
              , "  ref alias = cluster.worker;"
              , "  process runner = worker;"
              , "  protocol ping = Ping[T];"
              , "  role ping.Client = runner;"
              , "  role ping.Server = external;"
              , "  bind runner.port = service.port;"
              , "  authority token : Proof[true] originates at root.node;"
              , "  grant trust.token = true;"
              , "  boundary edge.ingress = codec.inbound;"
              , "  entry ingress : Frame[Wire];"
              , "  assume true within trust.zone;"
              , "  export obligation proof.ready to audit.sink;"
              , "  observable metrics.bytes;"
              , "  constraint false;"
              , "}"
              , "program main = instantiate Mesh[U8] {"
              , "  entry input : U8;"
              , "  assume true within program.scope;"
              , "  export obligation proof.ready to audit.sink;"
              , "  observable metrics.bytes;"
              , "};"
              ]
          , 2
          )
        , ( "static-reference"
          , Text.unlines
              [ "architecture Generic[T: Type] {"
              , "  instance worker = Worker[T];"
              , "  protocol wire = Protocol[T];"
              , "}"
              , "program main = instantiate Generic[U8];"
              ]
          , 2
          )
        , ( "unicode"
          , Text.unlines
              [ "architecture Δομή { observable μετρικά.τιμή; }"
              , "program κύριο = instantiate Δομή;"
              ]
          , 2
          )
        , ( "mixed"
          , Text.unlines
              [ "type T = U8;"
              , "architecture First {}"
              , "claim C = true;"
              , "program main = instantiate First;"
              ]
          , 2
          )
        ]
      directResults =
        [ checkSource label source expected
        | (label, source, expected) <- directCases
        ]
      mismatch = checkMismatch
      caseLines = filter (not . Text.null) (Text.lines input)
      parsedCases = traverse parseCaseLine caseLines
  corpusResults <- case parsedCases of
    Left detail -> pure [Left detail]
    Right cases -> mapM runCase cases
  let failures = [detail | Left detail <- directResults <> [mismatch] <> corpusResults]
  mapM_ (putStrLn . ("FAIL: " <>)) failures
  if null failures
    then putStrLn
      ("PASS: certified Grammar-v1 architecture/program declarations agree with production AST across "
        <> show (length directCases) <> " direct controls and parser corpus")
    else exitFailure

checkSource :: String -> Text -> Int -> Either String ()
checkSource label source expectedCount = do
  (referenceValues, productionValues) <- parseValues (Text.pack label) source
  if referenceValues /= productionValues
    then Left
      (label <> " -- certified/production mismatch\nreference: "
        <> show referenceValues <> "\nproduction: " <> show productionValues)
    else if length referenceValues /= expectedCount
      then Left
        (label <> " -- expected " <> show expectedCount
          <> " architecture/program declarations, got " <> show (length referenceValues))
      else Right ()

checkMismatch :: Either String ()
checkMismatch = do
  (referenceValues, _) <- parseValues
    "mismatch-reference"
    (Text.unlines
      [ "architecture A { role p.Server = external; constraint true; }"
      , "program main = instantiate A { observable metrics.good; };"
      ])
  (_, productionValues) <- parseValues
    "mismatch-production"
    (Text.unlines
      [ "architecture A { role p.Server = internal.worker; constraint false; }"
      , "program main = instantiate A { observable metrics.bad; };"
      ])
  if referenceValues /= productionValues
    then Right ()
    else Left "mismatched architecture/program payloads were accepted as equal"

parseValues
  :: Text
  -> Text
  -> Either String
      ( [GrammarV1ReferenceArchitectureProgramDeclaration]
      , [GrammarV1ReferenceArchitectureProgramDeclaration]
      )
parseValues sourceName source = do
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens sourceName source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceValues <- mapLeft show
    (grammarV1ReferenceArchitectureProgramDeclarations tree)
  production <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
  pure
    ( referenceValues
    , grammarV1ProductionArchitectureProgramDeclarations production
    )

parseCaseLine :: Text -> Either String CorpusCase
parseCaseLine line = case Text.splitOn "\t" line of
  [fixtureId, path, expectation]
    | not (Text.null fixtureId)
    , not (Text.null path)
    , expectation == "parse" || expectation == "reject-syntax" ->
        Right CorpusCase
          { corpusCaseId = fixtureId
          , corpusCasePath = Text.unpack path
          , corpusCaseExpectation = expectation
          }
  _ -> Left ("invalid TSV row " <> show line)

runCase :: CorpusCase -> IO (Either String ())
runCase corpusCase
  | corpusCaseExpectation corpusCase == "reject-syntax" = pure (Right ())
  | otherwise = do
      let relativePath = corpusCasePath corpusCase
          path = corpusRoot <> "/" <> relativePath
          label = Text.unpack (corpusCaseId corpusCase) <> " " <> relativePath
          sourceName = Text.pack relativePath
      sourceResult <- try (TextIO.readFile path) :: IO (Either IOException Text)
      pure $ case sourceResult of
        Left exception -> Left
          (label <> " -- unable to read fixture: " <> show exception)
        Right source -> do
          (referenceValues, productionValues) <- parseValues sourceName source
          if referenceValues == productionValues
            then Right ()
            else Left
              (label <> " -- certified/production mismatch\nreference: "
                <> show referenceValues <> "\nproduction: " <> show productionValues)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
