{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.ReferenceAstTypeAlias
  ( GrammarV1ReferenceTypeAliasSpine (..)
  , GrammarV1ReferenceTypeTag (..)
  , grammarV1ProductionTypeAliasSpines
  , grammarV1ReferenceTypeAliasSpines
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
  let targetCases =
        [ ("type TUnit = Unit;", GrammarV1ReferenceUnitType)
        , ("type TBool = Bool;", GrammarV1ReferenceBoolType)
        , ("type TChar = Char;", GrammarV1ReferencePrimitiveSpelling "Char")
        , ("type TString = String;", GrammarV1ReferencePrimitiveSpelling "String")
        , ("type TU = U32;", GrammarV1ReferencePrimitiveSpelling "U32")
        , ("type TI = I32;", GrammarV1ReferencePrimitiveSpelling "I32")
        , ("type TF32 = F32;", GrammarV1ReferencePrimitiveSpelling "F32")
        , ("type TF64 = F64;", GrammarV1ReferencePrimitiveSpelling "F64")
        , ("type TBytes = Bytes;", GrammarV1ReferenceBytesType)
        , ("type TBytesN = Bytes[4];", GrammarV1ReferenceBytesType)
        , ("type TFrame = Frame[Wire];", GrammarV1ReferenceFrameType)
        , ("type TProof = Proof[true];", GrammarV1ReferenceProofType)
        , ("type TValidated = Validated[Wire, 1, 2];", GrammarV1ReferenceValidatedType)
        , ("type TRefined = {x : U32 | true};", GrammarV1ReferenceRefinementType)
        , ("type TTuple = (U8, U16);", GrammarV1ReferenceTupleType)
        , ("type TNamed = Wire;", GrammarV1ReferenceNamedType)
        ]
      targetResults =
        [ checkTargetTag index source expected
        | (index, (source, expected)) <- zip [(1 :: Int)..] targetCases
        ]
      genericResult = checkGenericCounts
      directFailures = [detail | Left detail <- genericResult : targetResults]
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
          ("PASS: certified Grammar-v1 type-alias/type-constructor spine agrees with production AST ("
            <> show (length cases) <> " fixtures)")
        else exitFailure

checkTargetTag
  :: Int
  -> Text
  -> GrammarV1ReferenceTypeTag
  -> Either String ()
checkTargetTag index source expected = do
  (referenceSpines, productionSpines) <- parseAliasSpines ("target-" <> show index) source
  if referenceSpines /= productionSpines
    then Left
      ("target " <> show index <> " -- certified/production alias spine mismatch\nreference: "
        <> show referenceSpines <> "\nproduction: " <> show productionSpines)
    else case referenceSpines of
      [spine]
        | grammarV1ReferenceTypeAliasTargetTag spine == expected -> Right ()
        | otherwise -> Left
            ("target " <> show index <> " -- expected tag " <> show expected
              <> ", got " <> show (grammarV1ReferenceTypeAliasTargetTag spine))
      other -> Left
        ("target " <> show index <> " -- expected one type alias, got " <> show (length other))

checkGenericCounts :: Either String ()
checkGenericCounts = do
  let source = "type Generic[T : Type, N : Nat] requires { authority U8; } = T;"
  (referenceSpines, productionSpines) <- parseAliasSpines "generic-counts" source
  if referenceSpines /= productionSpines
    then Left
      ("generic counts -- certified/production alias spine mismatch\nreference: "
        <> show referenceSpines <> "\nproduction: " <> show productionSpines)
    else case referenceSpines of
      [spine]
        | grammarV1ReferenceTypeAliasName spine /= "Generic" ->
            Left "generic counts -- alias name changed"
        | grammarV1ReferenceTypeAliasGenericParamCount spine /= 2 ->
            Left "generic counts -- expected two generic parameters"
        | grammarV1ReferenceTypeAliasRequirementCount spine /= 1 ->
            Left "generic counts -- expected one generic requirement"
        | grammarV1ReferenceTypeAliasTargetTag spine /= GrammarV1ReferenceNamedType ->
            Left "generic counts -- generic target should be a named type"
        | otherwise -> Right ()
      other -> Left ("generic counts -- expected one type alias, got " <> show (length other))

parseAliasSpines
  :: String
  -> Text
  -> Either String
      ( [GrammarV1ReferenceTypeAliasSpine]
      , [GrammarV1ReferenceTypeAliasSpine]
      )
parseAliasSpines label source = do
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens (Text.pack label) source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceSpines <- mapLeft show (grammarV1ReferenceTypeAliasSpines tree)
  production <- mapLeft show (parseGrammarV1StructuralSource (Text.pack label) source)
  pure (referenceSpines, grammarV1ProductionTypeAliasSpines production)

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
          referenceSpines <- mapLeft show (grammarV1ReferenceTypeAliasSpines tree)
          production <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
          let productionSpines = grammarV1ProductionTypeAliasSpines production
          if referenceSpines == productionSpines
            then Right ()
            else Left
              (label <> " -- certified/production type-alias spine mismatch\nreference: "
                <> show referenceSpines <> "\nproduction: " <> show productionSpines)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
