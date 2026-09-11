{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.ReferenceAstDeclarationCommon
  ( GrammarV1ReferenceFieldCore (..)
  , GrammarV1ReferenceGenericParamCore (..)
  , GrammarV1ReferenceStructuralModeCore (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstRecordData
  ( GrammarV1ReferenceRecordDataDeclaration (..)
  , GrammarV1ReferenceVariantCore (..)
  , GrammarV1ReferenceVariantPayloadCore (..)
  , grammarV1ProductionRecordDataDeclarations
  , grammarV1ReferenceRecordDataDeclaration
  , grammarV1ReferenceRecordDataDeclarations
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( GrammarV1ReferenceParseTree (..)
  , grammarV1ReferenceParseSourceTokens
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
  let directCases =
        [ ("empty-record", "record Empty {}", checkEmptyRecord)
        , ( "rich-record"
          , Text.unlines
              [ "record Pair[T: Type] mode affine requires {"
              , "  authority T;"
              , "  proposition true;"
              , "  effects E within {};"
              , "} { left: T, right: Bytes[4], }"
              ]
          , checkRichRecord
          )
        , ("simple-data", "data Maybe[T: Type] = None | Some(T);", checkSimpleData)
        , ( "rich-data"
          , Text.unlines
              [ "data Packet mode linear requires { representation true; } ="
              , "  Empty{}"
              , "| Rec{tag: U8, payload: Bytes[4],}"
              , "| Tup(U8, String);"
              ]
          , checkRichData
          )
        , ( "ordered-multiple"
          , Text.unlines ["record R {x: U8}", "data D = A | B{};"]
          , checkOrderedMultiple
          )
        , ( "unicode-identifiers"
          , "record Δοχείο {τιμή: U8}"
          , checkUnicodeRecord
          )
        ]
      directResults =
        [ checkDirect label source predicate
        | (label, source, predicate) <- directCases
        ]
      nonTarget = case grammarV1ReferenceRecordDataDeclaration
        (GrammarV1ReferenceNonterminal "declaration"
          (GrammarV1ReferenceAlternative 2
            (GrammarV1ReferenceLiteral "not-used"))) of
        Right Nothing -> Right ()
        other -> Left ("non-record/data alternative did not stay outside tranche: " <> show other)
      malformed = case grammarV1ReferenceRecordDataDeclaration
        (GrammarV1ReferenceNonterminal "declaration"
          (GrammarV1ReferenceAlternative 15
            (GrammarV1ReferenceLiteral "impossible"))) of
        Left _ -> Right ()
        Right value -> Left ("out-of-range declaration decoded as " <> show value)
      directFailures = [detail | Left detail <- directResults <> [nonTarget, malformed]]
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
          ("PASS: record/data declaration bodies agree with production AST ("
            <> show (length cases) <> " corpus fixtures)")
        else exitFailure

checkDirect
  :: String
  -> Text
  -> ([GrammarV1ReferenceRecordDataDeclaration] -> Either String ())
  -> Either String ()
checkDirect label source predicate = do
  (referenceValues, productionValues) <- parseValues label source
  if referenceValues /= productionValues
    then Left
      (label <> " -- certified/production record-data mismatch\nreference: "
        <> show referenceValues <> "\nproduction: " <> show productionValues)
    else predicate referenceValues

checkEmptyRecord :: [GrammarV1ReferenceRecordDataDeclaration] -> Either String ()
checkEmptyRecord values = case values of
  [GrammarV1ReferenceRecordDeclaration "Empty" [] Nothing [] []] -> Right ()
  _ -> Left ("unexpected empty record projection " <> show values)

checkRichRecord :: [GrammarV1ReferenceRecordDataDeclaration] -> Either String ()
checkRichRecord values = case values of
  [GrammarV1ReferenceRecordDeclaration "Pair" params (Just GrammarV1ReferenceAffineMode) requirements fields]
    | map grammarV1ReferenceGenericParamNameCore params == ["T"]
    , length requirements == 3
    , map grammarV1ReferenceFieldNameCore fields == ["left", "right"] -> Right ()
  _ -> Left ("unexpected rich record projection " <> show values)

checkSimpleData :: [GrammarV1ReferenceRecordDataDeclaration] -> Either String ()
checkSimpleData values = case values of
  [GrammarV1ReferenceDataDeclaration "Maybe" params Nothing [] variants]
    | map grammarV1ReferenceGenericParamNameCore params == ["T"]
    , map grammarV1ReferenceVariantNameCore variants == ["None", "Some"]
    , (case variants of
        [ GrammarV1ReferenceVariantCore "None" Nothing
          , GrammarV1ReferenceVariantCore "Some"
              (Just (GrammarV1ReferenceVariantTupleCore [_]))
          ] -> True
        _ -> False) -> Right ()
  _ -> Left ("unexpected simple data projection " <> show values)

checkRichData :: [GrammarV1ReferenceRecordDataDeclaration] -> Either String ()
checkRichData values = case values of
  [GrammarV1ReferenceDataDeclaration "Packet" [] (Just GrammarV1ReferenceLinearMode) requirements variants]
    | length requirements == 1
    , map grammarV1ReferenceVariantNameCore variants == ["Empty", "Rec", "Tup"]
    , (case variants of
        [ GrammarV1ReferenceVariantCore "Empty"
              (Just (GrammarV1ReferenceVariantRecordCore []))
          , GrammarV1ReferenceVariantCore "Rec"
              (Just (GrammarV1ReferenceVariantRecordCore recordFields))
          , GrammarV1ReferenceVariantCore "Tup"
              (Just (GrammarV1ReferenceVariantTupleCore tupleTypes))
          ] -> map grammarV1ReferenceFieldNameCore recordFields == ["tag", "payload"]
               && length tupleTypes == 2
        _ -> False) -> Right ()
  _ -> Left ("unexpected rich data projection " <> show values)

checkOrderedMultiple :: [GrammarV1ReferenceRecordDataDeclaration] -> Either String ()
checkOrderedMultiple values = case values of
  [GrammarV1ReferenceRecordDeclaration "R" _ _ _ _, GrammarV1ReferenceDataDeclaration "D" _ _ _ _] -> Right ()
  _ -> Left ("record/data source order was not preserved: " <> show values)

checkUnicodeRecord :: [GrammarV1ReferenceRecordDataDeclaration] -> Either String ()
checkUnicodeRecord values = case values of
  [GrammarV1ReferenceRecordDeclaration "Δοχείο" [] Nothing [] fields]
    | map grammarV1ReferenceFieldNameCore fields == ["τιμή"] -> Right ()
  _ -> Left ("unicode record identifiers were not preserved: " <> show values)

parseValues
  :: String
  -> Text
  -> Either String
      ( [GrammarV1ReferenceRecordDataDeclaration]
      , [GrammarV1ReferenceRecordDataDeclaration]
      )
parseValues label source = do
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens (Text.pack label) source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceValues <- mapLeft show (grammarV1ReferenceRecordDataDeclarations tree)
  production <- mapLeft show (parseGrammarV1StructuralSource (Text.pack label) source)
  pure (referenceValues, grammarV1ProductionRecordDataDeclarations production)

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
          sourceTokens <- mapLeft show (lexGrammarV1SourceTokens sourceName source)
          tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
          referenceValues <- mapLeft show (grammarV1ReferenceRecordDataDeclarations tree)
          production <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
          let productionValues = grammarV1ProductionRecordDataDeclarations production
          if referenceValues == productionValues
            then Right ()
            else Left
              (label <> " -- certified/production record-data mismatch\nreference: "
                <> show referenceValues <> "\nproduction: " <> show productionValues)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
