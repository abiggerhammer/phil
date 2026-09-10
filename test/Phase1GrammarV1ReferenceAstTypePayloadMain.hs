{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.ReferenceAstStaticReference
  ( GrammarV1ReferenceStaticArgumentTag (..)
  , GrammarV1ReferenceStaticReferenceSpine (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstTypeAlias
  ( GrammarV1ReferenceTypeTag (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstTypePayload
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
        [ ( "runtime-bytes"
          , "type Runtime = Bytes;"
          , [GrammarV1ReferencePayloadBytes GrammarV1ReferenceRuntimeBytes]
          )
        , ( "indexed-bytes"
          , "type Fixed = Bytes[16];"
          , [GrammarV1ReferencePayloadBytes GrammarV1ReferenceIndexedBytes]
          )
        , ( "frame-reference"
          , "type Framed = Frame[Wire.Codec[U32, 1 + 2]];"
          , [GrammarV1ReferencePayloadFrame
              (reference ["Wire", "Codec"]
                [ GrammarV1ReferenceStaticTypeArgument
                    (GrammarV1ReferencePrimitiveSpelling "U32")
                , GrammarV1ReferenceStaticValueArgument
                ])]
          )
        , ( "proof-hole"
          , "type Evidence = Proof[true];"
          , [GrammarV1ReferencePayloadProof]
          )
        , ( "validated-reference"
          , "type Checked = Validated[Check[U16], payload, evidence];"
          , [GrammarV1ReferencePayloadValidated
              (reference ["Check"]
                [GrammarV1ReferenceStaticTypeArgument
                  (GrammarV1ReferencePrimitiveSpelling "U16")])]
          )
        , ( "refinement-recursion"
          , "type PositivePair = {pair : (U32, Frame[Codec]) | true};"
          , [GrammarV1ReferencePayloadRefinement
              "pair"
              (GrammarV1ReferencePayloadTuple
                [ GrammarV1ReferencePayloadPrimitive "U32"
                , GrammarV1ReferencePayloadFrame (reference ["Codec"] [])
                ])]
          )
        , ( "nested-tuple"
          , "type Nested = (U8, (Bool, Foo.Bar), Frame[Wire]);"
          , [GrammarV1ReferencePayloadTuple
              [ GrammarV1ReferencePayloadPrimitive "U8"
              , GrammarV1ReferencePayloadTuple
                  [ GrammarV1ReferencePayloadBool
                  , GrammarV1ReferencePayloadNamed (reference ["Foo", "Bar"] [])
                  ]
              , GrammarV1ReferencePayloadFrame (reference ["Wire"] [])
              ]]
          )
        , ( "specialized-named"
          , "type Specialized = Map[U32, Cfg[N]];"
          , [GrammarV1ReferencePayloadNamed
              (reference ["Map"]
                [ GrammarV1ReferenceStaticTypeArgument
                    (GrammarV1ReferencePrimitiveSpelling "U32")
                , GrammarV1ReferenceStaticValueArgument
                ])]
          )
        , ( "unicode-name"
          , "type Unicode = Δ.Τύπος;"
          , [GrammarV1ReferencePayloadNamed (reference ["Δ", "Τύπος"] [])]
          )
        ]
      directResults =
        [ checkDirect label source expected
        | (label, source, expected) <- directCases
        ]
      malformedResult =
        case grammarV1ReferenceTypePayload (GrammarV1ReferenceLiteral "Unit") of
          Left _ -> Right ()
          Right value -> Left
            ("malformed-tree -- non-type root decoded as " <> show value)
      directFailures = [detail | Left detail <- malformedResult : directResults]
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
          ("PASS: certified Grammar-v1 recursive type payloads agree with production AST ("
            <> show (length cases) <> " fixtures)")
        else exitFailure

reference
  :: [Text]
  -> [GrammarV1ReferenceStaticArgumentTag]
  -> GrammarV1ReferenceStaticReferenceSpine
reference name arguments = GrammarV1ReferenceStaticReferenceSpine
  { grammarV1ReferenceStaticReferenceName = name
  , grammarV1ReferenceStaticReferenceArguments = arguments
  }

checkDirect
  :: String
  -> Text
  -> [GrammarV1ReferenceTypePayload]
  -> Either String ()
checkDirect label source expected = do
  (referencePayloads, productionPayloads) <- parsePayloads label source
  if referencePayloads /= productionPayloads
    then Left
      (label <> " -- certified/production type-payload mismatch\nreference: "
        <> show referencePayloads <> "\nproduction: " <> show productionPayloads)
    else if referencePayloads /= expected
      then Left
        (label <> " -- unexpected type-payload projection\nexpected: "
          <> show expected <> "\nactual: " <> show referencePayloads)
      else Right ()

parsePayloads
  :: String
  -> Text
  -> Either String
      ( [GrammarV1ReferenceTypePayload]
      , [GrammarV1ReferenceTypePayload]
      )
parsePayloads label source = do
  sourceTokens <- mapLeft show
    (lexGrammarV1SourceTokens (Text.pack label) source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referencePayloads <- mapLeft show
    (grammarV1ReferenceTypeAliasTypePayloads tree)
  production <- mapLeft show
    (parseGrammarV1StructuralSource (Text.pack label) source)
  pure
    ( referencePayloads
    , grammarV1ProductionTypeAliasTypePayloads production
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
          sourceTokens <- mapLeft show
            (lexGrammarV1SourceTokens sourceName source)
          tree <- mapLeft show
            (grammarV1ReferenceParseSourceTokens sourceTokens)
          referencePayloads <- mapLeft show
            (grammarV1ReferenceTypeAliasTypePayloads tree)
          production <- mapLeft show
            (parseGrammarV1StructuralSource sourceName source)
          let productionPayloads = grammarV1ProductionTypeAliasTypePayloads production
          if referencePayloads == productionPayloads
            then Right ()
            else Left
              (label <> " -- certified/production type-payload mismatch\nreference: "
                <> show referencePayloads <> "\nproduction: " <> show productionPayloads)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
