{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1QualifiedName (..)
  , parseGrammarV1StructuralSource
  )
import Phil.Surface.GrammarV1.ReferenceAstRepresentationBridge
  ( grammarV1ProductionSourceFileToImplementationHeader
  , grammarV1ReferenceSourceSpineToImplementationHeader
  )
import Phil.Surface.GrammarV1.ReferenceAstSpine
  ( GrammarV1ReferenceImportSpine (..)
  , GrammarV1ReferenceSourceSpine (..)
  , grammarV1ProductionSourceSpine
  , grammarV1ReferenceSourceSpine
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( grammarV1ReferenceParseSourceTokens
  , kernelStringToText
  )
import qualified SurfaceGrammarAstRepresentationKernel as Representation
import qualified SurfaceGrammarRecognizerKernel as Recognizer
import System.Exit (exitFailure)

corpusRoot :: FilePath
corpusRoot = "test/fixtures/phase1-surface"

data CorpusCase = CorpusCase
  { corpusCaseId :: Text
  , corpusCasePath :: FilePath
  , corpusCaseExpectation :: Text
  }

type SourceHeaderView =
  ( Maybe [Text]
  , [([Text], Maybe [Text])]
  , Int
  )

main :: IO ()
main = do
  let directSources =
        [ ("module/import spine",
            "module alpha.beta; import foo.bar; import baz { one, two }; type X = U32;")
        , ("empty prelude spine", "type Blob = Bytes;")
        ]
      directChecks =
        map (uncurry checkSource) directSources
          <> [checkUtf8RepresentationBinding, checkNegativeCountRejected]
      directFailures = [detail | Left detail <- directChecks]
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
          ("PASS: certified Grammar-v1 source-file AST spine and extracted header representation agree with production ("
            <> show (length cases) <> " fixtures)")
        else exitFailure

checkSource :: String -> Text -> Either String ()
checkSource label source = do
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens (Text.pack label) source)
  referenceTree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceSpine <- mapLeft show (grammarV1ReferenceSourceSpine referenceTree)
  productionAst <- mapLeft show (parseGrammarV1StructuralSource (Text.pack label) source)
  let productionSpine = grammarV1ProductionSourceSpine productionAst
  if referenceSpine /= productionSpine
    then Left
      (label <> " -- source-file spine mismatch\nreference: "
        <> show referenceSpine <> "\nproduction: " <> show productionSpine)
    else do
      referenceHeader <- mapLeft show
        (grammarV1ReferenceSourceSpineToImplementationHeader referenceSpine)
      productionHeader <- mapLeft show
        (grammarV1ProductionSourceFileToImplementationHeader productionAst)
      checkImplementationHeader
        (label <> " -- certified extracted header")
        referenceSpine
        referenceHeader
      checkImplementationHeader
        (label <> " -- production extracted header")
        productionSpine
        productionHeader

checkUtf8RepresentationBinding :: Either String ()
checkUtf8RepresentationBinding = do
  let spine = GrammarV1ReferenceSourceSpine
        { grammarV1ReferenceModuleName =
            Just (GrammarV1QualifiedName ["μ", "naïve"])
        , grammarV1ReferenceImports =
            [ GrammarV1ReferenceImportSpine
                { grammarV1ReferenceImportName =
                    GrammarV1QualifiedName ["λ", "café"]
                , grammarV1ReferenceImportSelection =
                    Just ["π", "東京"]
                }
            ]
        , grammarV1ReferenceTopLevelCount = 2
        }
  header <- mapLeft show
    (grammarV1ReferenceSourceSpineToImplementationHeader spine)
  checkImplementationHeader "explicit UTF-8 representation bridge" spine header

checkNegativeCountRejected :: Either String ()
checkNegativeCountRejected =
  let spine = GrammarV1ReferenceSourceSpine
        { grammarV1ReferenceModuleName = Nothing
        , grammarV1ReferenceImports = []
        , grammarV1ReferenceTopLevelCount = -1
        }
  in case grammarV1ReferenceSourceSpineToImplementationHeader spine of
      Left _ -> Right ()
      Right _ -> Left "negative source-spine top-level count was accepted"

checkImplementationHeader
  :: String
  -> GrammarV1ReferenceSourceSpine
  -> Representation.Phase1SurfaceImplementationSourceHeader
  -> Either String ()
checkImplementationHeader label spine header = do
  actual <- implementationHeaderView header
  let expected = sourceSpineView spine
  if actual == expected
    then Right ()
    else Left
      (label <> " mismatch\nexpected: " <> show expected
        <> "\nactual: " <> show actual)

sourceSpineView :: GrammarV1ReferenceSourceSpine -> SourceHeaderView
sourceSpineView spine =
  ( fmap qualifiedNameParts (grammarV1ReferenceModuleName spine)
  , map importSpineView (grammarV1ReferenceImports spine)
  , grammarV1ReferenceTopLevelCount spine
  )
  where
    qualifiedNameParts (GrammarV1QualifiedName parts) = parts
    importSpineView importSpine =
      ( qualifiedNameParts (grammarV1ReferenceImportName importSpine)
      , grammarV1ReferenceImportSelection importSpine
      )

implementationHeaderView
  :: Representation.Phase1SurfaceImplementationSourceHeader
  -> Either String SourceHeaderView
implementationHeaderView header = do
  moduleName <- traverse decodeRepresentationName
    (Representation.phase1_impl_source_module header)
  imports <- traverse implementationImportView
    (Representation.phase1_impl_source_imports header)
  pure
    ( moduleName
    , imports
    , representationNatToInt
        (Representation.phase1_impl_source_top_level_count header)
    )

implementationImportView
  :: Representation.Phase1SurfaceImplementationImportHeader
  -> Either String ([Text], Maybe [Text])
implementationImportView header = do
  name <- decodeRepresentationName
    (Representation.phase1_impl_import_name header)
  selection <- traverse decodeRepresentationName
    (Representation.phase1_impl_import_selection header)
  pure (name, selection)

decodeRepresentationName
  :: [Representation.String]
  -> Either String [Text]
decodeRepresentationName = traverse decodeRepresentationString

decodeRepresentationString
  :: Representation.String
  -> Either String Text
decodeRepresentationString =
  mapLeft show
    . kernelStringToText
    . representationStringToRecognizer

representationStringToRecognizer
  :: Representation.String
  -> Recognizer.String
representationStringToRecognizer value = case value of
  Representation.EmptyString -> Recognizer.EmptyString
  Representation.String0 ascii rest ->
    Recognizer.String0
      (representationAsciiToRecognizer ascii)
      (representationStringToRecognizer rest)

representationAsciiToRecognizer
  :: Representation.Ascii0
  -> Recognizer.Ascii0
representationAsciiToRecognizer ascii = case ascii of
  Representation.Ascii bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 ->
    Recognizer.Ascii bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7

representationNatToInt :: Representation.Nat -> Int
representationNatToInt value = case value of
  Representation.O -> 0
  Representation.S predecessor -> 1 + representationNatToInt predecessor

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
      sourceResult <- try (TextIO.readFile path) :: IO (Either IOException Text)
      pure $ case sourceResult of
        Left exception -> Left (label <> " -- unable to read fixture: " <> show exception)
        Right source -> checkSource label source

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
