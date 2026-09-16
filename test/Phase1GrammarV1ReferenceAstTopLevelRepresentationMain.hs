{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer
  ( lexGrammarV1SourceTokens
  )
import Phil.Surface.GrammarV1.Parser
  ( parseGrammarV1StructuralSource
  )
import Phil.Surface.GrammarV1.ReferenceAstTopLevel
  ( GrammarV1ReferenceAttributeSpine (..)
  , GrammarV1ReferenceDeclarationTag (..)
  , GrammarV1ReferenceTopLevelSpine (..)
  , grammarV1ProductionTopLevelSpines
  , grammarV1ReferenceTopLevelSpines
  )
import Phil.Surface.GrammarV1.ReferenceAstTopLevelRepresentationBridge
  ( grammarV1ProductionTopLevelSpinesToImplementation
  , grammarV1ReferenceDeclarationTagToImplementation
  , grammarV1ReferenceTopLevelSpineToImplementation
  , grammarV1ReferenceTopLevelSpinesToImplementation
  )
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( grammarV1ReferenceParseSourceTokens
  , kernelStringToText
  )
import qualified SurfaceGrammarAstTopLevelCarrierKernel as Representation
import qualified SurfaceGrammarRecognizerKernel as Recognizer
import System.Exit (exitFailure)

corpusRoot :: FilePath
corpusRoot = "test/fixtures/phase1-surface"

data CorpusCase = CorpusCase
  { corpusCaseId :: Text
  , corpusCasePath :: FilePath
  , corpusCaseExpectation :: Text
  }

type TopLevelView =
  ( [(Text, Text)]
  , GrammarV1ReferenceDeclarationTag
  )

main :: IO ()
main = do
  let directChecks =
        [ declarationTagBridgeCoverage
        , unicodeAttributeBridge
        ]
      directFailures = [detail | Left detail <- directChecks]
  mapM_ (putStrLn . ("FAIL: " <>)) directFailures
  if null directFailures then pure () else exitFailure

  attributeCheck <- compareSource
    "attribute-direct"
    "@owner(\"λ\") @note(\"e\\u{0301}\") type Alias = U32;"
  case attributeCheck of
    Left detail -> putStrLn ("FAIL: " <> detail) >> exitFailure
    Right () -> pure ()

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
          ("PASS: certified Grammar-v1 top-level representation and production AST agree ("
            <> show (length cases) <> " fixtures)")
        else exitFailure

declarationTagBridgeCoverage :: Either String ()
declarationTagBridgeCoverage =
  let tags = [minBound .. maxBound]
      actual =
        map
          (implementationDeclarationTag
            . grammarV1ReferenceDeclarationTagToImplementation)
          tags
  in if actual == tags
      then Right ()
      else Left
        ("declaration-tag implementation bridge mismatch: expected "
          <> show tags <> ", got " <> show actual)

unicodeAttributeBridge :: Either String ()
unicodeAttributeBridge = do
  let spine = GrammarV1ReferenceTopLevelSpine
        { grammarV1ReferenceTopLevelAttributes =
            [ GrammarV1ReferenceAttributeSpine
                { grammarV1ReferenceAttributeName = "μ"
                , grammarV1ReferenceAttributeValue = "東京"
                }
            , GrammarV1ReferenceAttributeSpine
                { grammarV1ReferenceAttributeName = "naïve"
                , grammarV1ReferenceAttributeValue = "café"
                }
            ]
        , grammarV1ReferenceTopLevelDeclarationTag =
            GrammarV1ReferenceProgramDeclaration
        }
  actual <- implementationTopLevelView
    (grammarV1ReferenceTopLevelSpineToImplementation spine)
  let expected = referenceTopLevelView spine
  if actual == expected
    then Right ()
    else Left
      ("explicit UTF-8 top-level representation bridge mismatch: expected "
        <> show expected <> ", got " <> show actual)

compareSource :: Text -> Text -> IO (Either String ())
compareSource sourceName source = pure $ do
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens sourceName source)
  referenceTree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceTopLevels <- mapLeft show (grammarV1ReferenceTopLevelSpines referenceTree)
  production <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
  let productionTopLevels = grammarV1ProductionTopLevelSpines production
  if referenceTopLevels /= productionTopLevels
    then Left
      (Text.unpack sourceName
        <> " -- top-level correspondence mismatch\nreference: "
        <> show referenceTopLevels
        <> "\nproduction: "
        <> show productionTopLevels)
    else do
      referenceImplementation <- traverse implementationTopLevelView
        (grammarV1ReferenceTopLevelSpinesToImplementation referenceTopLevels)
      productionImplementation <- traverse implementationTopLevelView
        (grammarV1ProductionTopLevelSpinesToImplementation production)
      let expected = map referenceTopLevelView referenceTopLevels
      if referenceImplementation /= expected
        then Left
          (Text.unpack sourceName
            <> " -- certified extracted top-level representation mismatch\nexpected: "
            <> show expected <> "\nactual: " <> show referenceImplementation)
        else if productionImplementation /= expected
          then Left
            (Text.unpack sourceName
              <> " -- production extracted top-level representation mismatch\nexpected: "
              <> show expected <> "\nactual: " <> show productionImplementation)
          else Right ()

referenceTopLevelView :: GrammarV1ReferenceTopLevelSpine -> TopLevelView
referenceTopLevelView topLevel =
  ( map attributeView (grammarV1ReferenceTopLevelAttributes topLevel)
  , grammarV1ReferenceTopLevelDeclarationTag topLevel
  )
  where
    attributeView attribute =
      ( grammarV1ReferenceAttributeName attribute
      , grammarV1ReferenceAttributeValue attribute
      )

implementationTopLevelView
  :: Representation.Phase1SurfaceImplementationTopLevel
  -> Either String TopLevelView
implementationTopLevelView topLevel = case topLevel of
  Representation.Build_Phase1SurfaceImplementationTopLevel attributes tag -> do
    attributeViews <- traverse implementationAttributeView attributes
    pure (attributeViews, implementationDeclarationTag tag)

implementationAttributeView
  :: Representation.Phase1SurfaceImplementationAttribute
  -> Either String (Text, Text)
implementationAttributeView attribute = case attribute of
  Representation.Build_Phase1SurfaceImplementationAttribute name value ->
    (,) <$> decodeRepresentationString name <*> decodeRepresentationString value

implementationDeclarationTag
  :: Representation.Phase1SurfaceDeclarationTag
  -> GrammarV1ReferenceDeclarationTag
implementationDeclarationTag tag = case tag of
  Representation.Phase1RecordDeclaration ->
    GrammarV1ReferenceRecordDeclaration
  Representation.Phase1DataDeclaration ->
    GrammarV1ReferenceDataDeclaration
  Representation.Phase1TypeAliasDeclaration ->
    GrammarV1ReferenceTypeAliasDeclaration
  Representation.Phase1ClaimDeclaration ->
    GrammarV1ReferenceClaimDeclaration
  Representation.Phase1CallableContractDeclaration ->
    GrammarV1ReferenceCallableContractDeclaration
  Representation.Phase1FunctionDeclaration ->
    GrammarV1ReferenceFunctionDeclaration
  Representation.Phase1ProviderContractDeclaration ->
    GrammarV1ReferenceProviderContractDeclaration
  Representation.Phase1ProviderImplementationDeclaration ->
    GrammarV1ReferenceProviderImplementationDeclaration
  Representation.Phase1OpaqueProviderImplementationDeclaration ->
    GrammarV1ReferenceOpaqueProviderImplementationDeclaration
  Representation.Phase1ProtocolDeclaration ->
    GrammarV1ReferenceProtocolDeclaration
  Representation.Phase1CapabilityDeclaration ->
    GrammarV1ReferenceCapabilityDeclaration
  Representation.Phase1BoundaryDeclaration ->
    GrammarV1ReferenceBoundaryDeclaration
  Representation.Phase1ArchitectureDeclaration ->
    GrammarV1ReferenceArchitectureDeclaration
  Representation.Phase1ComponentDeclaration ->
    GrammarV1ReferenceComponentDeclaration
  Representation.Phase1ProgramDeclaration ->
    GrammarV1ReferenceProgramDeclaration

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
runCase corpusCase = do
  let relativePath = corpusCasePath corpusCase
      path = corpusRoot <> "/" <> relativePath
      label = Text.unpack (corpusCaseId corpusCase) <> " " <> relativePath
      sourceName = Text.pack relativePath
  sourceResult <- try (TextIO.readFile path) :: IO (Either IOException Text)
  pure $ case sourceResult of
    Left exception -> Left (label <> " -- unable to read fixture: " <> show exception)
    Right source -> case corpusCaseExpectation corpusCase of
      "parse" -> do
        sourceTokens <- mapLeft show (lexGrammarV1SourceTokens sourceName source)
        referenceTree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
        referenceTopLevels <- mapLeft show (grammarV1ReferenceTopLevelSpines referenceTree)
        production <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
        let productionTopLevels = grammarV1ProductionTopLevelSpines production
        if referenceTopLevels /= productionTopLevels
          then Left
            (label <> " -- top-level correspondence mismatch\nreference: "
              <> show referenceTopLevels
              <> "\nproduction: " <> show productionTopLevels)
          else do
            referenceImplementation <- traverse implementationTopLevelView
              (grammarV1ReferenceTopLevelSpinesToImplementation referenceTopLevels)
            productionImplementation <- traverse implementationTopLevelView
              (grammarV1ProductionTopLevelSpinesToImplementation production)
            let expected = map referenceTopLevelView referenceTopLevels
            if referenceImplementation == expected
              && productionImplementation == expected
              then Right ()
              else Left
                (label <> " -- extracted top-level representation mismatch\nexpected: "
                  <> show expected
                  <> "\ncertified: " <> show referenceImplementation
                  <> "\nproduction: " <> show productionImplementation)
      "reject-syntax" ->
        case parseGrammarV1StructuralSource sourceName source of
          Right _ -> Left (label <> " -- syntax-negative fixture parsed in production")
          Left _ -> case lexGrammarV1SourceTokens sourceName source of
            Left _ -> Right ()
            Right sourceTokens -> case grammarV1ReferenceParseSourceTokens sourceTokens of
              Left _ -> Right ()
              Right _ -> Left (label <> " -- syntax-negative fixture produced certified tree")
      other -> Left (label <> " -- unsupported expectation " <> Text.unpack other)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
