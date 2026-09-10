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
  ( GrammarV1ReferenceDeclarationTag (..)
  , grammarV1ProductionTopLevelSpines
  , grammarV1ReferenceDeclarationTag
  , grammarV1ReferenceTopLevelSpines
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
  let directChecks =
        [ declarationAlternativeCoverage
        , mismatchedDeclarationNameRejected
        , outOfRangeDeclarationRejected
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
          ("PASS: certified Grammar-v1 top-level attributes and declaration choices agree with production AST ("
            <> show (length cases) <> " fixtures)")
        else exitFailure

declarationAlternativeCoverage :: Either String ()
declarationAlternativeCoverage = do
  let expected =
        [ (0, "record_decl", GrammarV1ReferenceRecordDeclaration)
        , (1, "data_decl", GrammarV1ReferenceDataDeclaration)
        , (2, "type_alias_decl", GrammarV1ReferenceTypeAliasDeclaration)
        , (3, "claim_decl", GrammarV1ReferenceClaimDeclaration)
        , (4, "callable_contract_decl", GrammarV1ReferenceCallableContractDeclaration)
        , (5, "function_decl", GrammarV1ReferenceFunctionDeclaration)
        , (6, "provider_contract_decl", GrammarV1ReferenceProviderContractDeclaration)
        , (7, "provider_implementation_decl", GrammarV1ReferenceProviderImplementationDeclaration)
        , (8, "opaque_provider_implementation_decl", GrammarV1ReferenceOpaqueProviderImplementationDeclaration)
        , (9, "protocol_decl", GrammarV1ReferenceProtocolDeclaration)
        , (10, "capability_decl", GrammarV1ReferenceCapabilityDeclaration)
        , (11, "boundary_decl", GrammarV1ReferenceBoundaryDeclaration)
        , (12, "architecture_decl", GrammarV1ReferenceArchitectureDeclaration)
        , (13, "component_decl", GrammarV1ReferenceComponentDeclaration)
        , (14, "program_decl", GrammarV1ReferenceProgramDeclaration)
        ]
  actual <- traverse decode expected
  let expectedTags = [tag | (_, _, tag) <- expected]
  if actual == expectedTags
    && actual == [minBound .. maxBound]
    then Right ()
    else Left
      ("declaration alternative coverage mismatch: expected "
        <> show expectedTags <> ", got " <> show actual)
  where
    decode (index, name, _tag) =
      mapLeft show
        (grammarV1ReferenceDeclarationTag
          (syntheticDeclaration index name))

mismatchedDeclarationNameRejected :: Either String ()
mismatchedDeclarationNameRejected =
  case grammarV1ReferenceDeclarationTag (syntheticDeclaration 0 "data_decl") of
    Left _ -> Right ()
    Right tag -> Left
      ("declaration alternative 0 accepted mismatched data_decl as " <> show tag)

outOfRangeDeclarationRejected :: Either String ()
outOfRangeDeclarationRejected =
  case grammarV1ReferenceDeclarationTag (syntheticDeclaration 15 "record_decl") of
    Left _ -> Right ()
    Right tag -> Left
      ("out-of-range declaration alternative accepted as " <> show tag)

syntheticDeclaration :: Integer -> Text -> GrammarV1ReferenceParseTree
syntheticDeclaration index name =
  GrammarV1ReferenceNonterminal "declaration"
    (GrammarV1ReferenceAlternative index
      (GrammarV1ReferenceNonterminal name
        (GrammarV1ReferenceSequence [])))

compareSource :: Text -> Text -> IO (Either String ())
compareSource sourceName source = pure $ do
  sourceTokens <- mapLeft show (lexGrammarV1SourceTokens sourceName source)
  referenceTree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceTopLevels <- mapLeft show (grammarV1ReferenceTopLevelSpines referenceTree)
  production <- mapLeft show (parseGrammarV1StructuralSource sourceName source)
  let productionTopLevels = grammarV1ProductionTopLevelSpines production
  if referenceTopLevels == productionTopLevels
    then Right ()
    else Left
      (Text.unpack sourceName
        <> " -- top-level correspondence mismatch\nreference: "
        <> show referenceTopLevels
        <> "\nproduction: "
        <> show productionTopLevels)

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
        if referenceTopLevels == productionTopLevels
          then Right ()
          else Left
            (label <> " -- top-level correspondence mismatch\nreference: "
              <> show referenceTopLevels
              <> "\nproduction: "
              <> show productionTopLevels)
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
