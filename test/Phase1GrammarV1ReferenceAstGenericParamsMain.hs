{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.ReferenceAstGenericParams
  ( GrammarV1ReferenceGenericKindSpine (..)
  , GrammarV1ReferenceGenericParamSpine (..)
  , GrammarV1ReferenceTypeAliasGenericParams (..)
  , grammarV1ProductionTypeAliasGenericParams
  , grammarV1ReferenceTypeAliasGenericParams
  )
import Phil.Surface.GrammarV1.ReferenceAstTypeAlias
  ( GrammarV1ReferenceTypeTag (..)
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
  let directResults =
        [ checkAllKinds
        , checkNoParams
        , checkUnicodeName
        ]
      directFailures = [detail | Left detail <- directResults]
  mapM_ (putStrLn . ("FAIL: " <>)) directFailures
  if null directFailures then pure () else exitFailure

  input <- TextIO.getContents
  case traverse parseCaseLine (filter (not . Text.null) (Text.lines input)) of
    Left detail -> putStrLn ("FAIL: manifest stream -- " <> detail) >> exitFailure
    Right [] -> putStrLn "FAIL: manifest stream -- no corpus cases" >> exitFailure
    Right cases -> do
      results <- traverse runCase cases
      let failures = [detail | Left detail <- results]
      mapM_ (putStrLn . ("FAIL: " <>)) failures
      if null failures
        then putStrLn
          ("PASS: certified Grammar-v1 generic parameters agree with production AST ("
            <> show (length cases) <> " fixtures)")
        else exitFailure

checkAllKinds :: Either String ()
checkAllKinds = do
  let source = Text.unwords
        [ "type Generic["
        , "T : Type,"
        , "N : Nat,"
        , "S : Session,"
        , "M : Message,"
        , "E : Effects,"
        , "P : provider Unit,"
        , "C : callable U8,"
        , "B : boundary Bytes,"
        , "A : architecture Wire"
        , "] = T;"
        ]
      expected =
        [ GrammarV1ReferenceGenericParamSpine "T" GrammarV1ReferenceTypeKind
        , GrammarV1ReferenceGenericParamSpine "N" GrammarV1ReferenceNatKind
        , GrammarV1ReferenceGenericParamSpine "S" GrammarV1ReferenceSessionKind
        , GrammarV1ReferenceGenericParamSpine "M" GrammarV1ReferenceMessageKind
        , GrammarV1ReferenceGenericParamSpine "E" GrammarV1ReferenceEffectsKind
        , GrammarV1ReferenceGenericParamSpine
            "P" (GrammarV1ReferenceProviderKind GrammarV1ReferenceUnitType)
        , GrammarV1ReferenceGenericParamSpine
            "C" (GrammarV1ReferenceCallableKind (GrammarV1ReferencePrimitiveSpelling "U8"))
        , GrammarV1ReferenceGenericParamSpine
            "B" (GrammarV1ReferenceBoundaryKind GrammarV1ReferenceBytesType)
        , GrammarV1ReferenceGenericParamSpine
            "A" (GrammarV1ReferenceArchitectureKind GrammarV1ReferenceNamedType)
        ]
  (reference, production) <- parseGenericParams "all-kinds" source
  if reference /= production
    then mismatch "all kinds" reference production
    else case reference of
      [value]
        | grammarV1ReferenceGenericParamsAliasName value /= "Generic" ->
            Left "all kinds -- alias name changed"
        | grammarV1ReferenceGenericParams value /= expected ->
            Left
              ("all kinds -- generic parameter sequence mismatch\nexpected: "
                <> show expected <> "\nactual:   "
                <> show (grammarV1ReferenceGenericParams value))
        | otherwise -> Right ()
      other -> Left ("all kinds -- expected one type alias, got " <> show (length other))

checkNoParams :: Either String ()
checkNoParams = do
  (reference, production) <- parseGenericParams "no-params" "type Plain = Unit;"
  if reference /= production
    then mismatch "no params" reference production
    else case reference of
      [value]
        | null (grammarV1ReferenceGenericParams value) -> Right ()
        | otherwise -> Left "no params -- certified optional-none became nonempty parameters"
      other -> Left ("no params -- expected one type alias, got " <> show (length other))

checkUnicodeName :: Either String ()
checkUnicodeName = do
  let source = "type Unicode[Té : Type] = Té;"
  (reference, production) <- parseGenericParams "unicode-name" source
  if reference /= production
    then mismatch "unicode name" reference production
    else case reference of
      [value] -> case grammarV1ReferenceGenericParams value of
        [GrammarV1ReferenceGenericParamSpine "Té" GrammarV1ReferenceTypeKind] -> Right ()
        other -> Left ("unicode name -- unexpected parameters " <> show other)
      other -> Left ("unicode name -- expected one type alias, got " <> show (length other))

parseGenericParams
  :: String
  -> Text
  -> Either String
      ( [GrammarV1ReferenceTypeAliasGenericParams]
      , [GrammarV1ReferenceTypeAliasGenericParams]
      )
parseGenericParams label source = do
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens (Text.pack label) source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  reference <- mapLeft show (grammarV1ReferenceTypeAliasGenericParams tree)
  production <- mapLeft show (parseGrammarV1StructuralSource (Text.pack label) source)
  pure (reference, grammarV1ProductionTypeAliasGenericParams production)

mismatch
  :: String
  -> [GrammarV1ReferenceTypeAliasGenericParams]
  -> [GrammarV1ReferenceTypeAliasGenericParams]
  -> Either String a
mismatch label reference production =
  Left
    (label <> " -- certified/production generic parameter mismatch\nreference: "
      <> show reference <> "\nproduction: " <> show production)

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
        Left exception -> Left (label <> " -- unable to read fixture: " <> show exception)
        Right source -> do
          sourceTokens <- mapLeft show (lexGrammarV1SourceTokens sourceName source)
          tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
          reference <- mapLeft show (grammarV1ReferenceTypeAliasGenericParams tree)
          production <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
          let productionParams = grammarV1ProductionTypeAliasGenericParams production
          if reference == productionParams
            then Right ()
            else mismatch label reference productionParams

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
