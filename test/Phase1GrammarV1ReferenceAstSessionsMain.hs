{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.GrammarV1.Lexer (lexGrammarV1SourceTokens)
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.ReferenceAstProposition
  ( GrammarV1ReferencePropositionCore (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstSessions
  ( GrammarV1ReferenceRoleSessionCore (..)
  , GrammarV1ReferenceSessionBranchCore (..)
  , GrammarV1ReferenceSessionCore (..)
  , GrammarV1ReferenceTermParamCore (..)
  , grammarV1ProductionProtocolSessions
  , grammarV1ReferenceProtocolSessions
  , grammarV1ReferenceSessionCore
  )
import Phil.Surface.GrammarV1.ReferenceAstStaticReference
  ( GrammarV1ReferenceStaticArgumentTag (..)
  , GrammarV1ReferenceStaticReferenceSpine (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstTypeAlias
  ( GrammarV1ReferenceTypeTag (..)
  )
import Phil.Surface.GrammarV1.ReferenceAstTypePayload
  ( GrammarV1ReferenceBytesPayload (..)
  , GrammarV1ReferenceTypePayload (..)
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
        [ ( "reference-and-end"
          , "protocol P { role A = Session[U8]; role B = end Done; }"
          , [[ role "A"
                (GrammarV1ReferenceSessionReference
                  (reference ["Session"]
                    [GrammarV1ReferenceStaticTypeArgument
                      (GrammarV1ReferencePrimitiveSpelling "U8")]))
             , role "B" (GrammarV1ReferenceSessionEnd "Done")
             ]]
          )
        , ( "send-receive-boundary-guards"
          , "protocol P { role A = send(x: U8) using Wire when true then receive(y: Bytes[4]) when false then end Done; role B = end Done; }"
          , [[ role "A"
                (GrammarV1ReferenceSessionSend
                  (param "x" (GrammarV1ReferencePayloadPrimitive "U8"))
                  (Just (reference ["Wire"] []))
                  (Just GrammarV1ReferenceTrueProposition)
                  (GrammarV1ReferenceSessionReceive
                    (param "y" (GrammarV1ReferencePayloadBytes GrammarV1ReferenceIndexedBytes))
                    Nothing
                    (Just GrammarV1ReferenceFalseProposition)
                    (GrammarV1ReferenceSessionEnd "Done")))
             , role "B" (GrammarV1ReferenceSessionEnd "Done")
             ]]
          )
        , ( "choice-branch-parameter-presence"
          , Text.unlines
              [ "protocol P {"
              , "  role A = select { Go(x: U8, y: Bool) using Wire when true => continue Loop | Stop() => end Done };"
              , "  role B = offer { Go => end Done | Stop(z: String) => end Done };"
              , "}"
              ]
          , [[ role "A" (GrammarV1ReferenceSessionSelect
                [ branch "Go"
                    (Just
                      [ param "x" (GrammarV1ReferencePayloadPrimitive "U8")
                      , param "y" GrammarV1ReferencePayloadBool
                      ])
                    (Just (reference ["Wire"] []))
                    (Just GrammarV1ReferenceTrueProposition)
                    (GrammarV1ReferenceSessionContinue "Loop")
                , branch "Stop" (Just []) Nothing Nothing
                    (GrammarV1ReferenceSessionEnd "Done")
                ])
             , role "B" (GrammarV1ReferenceSessionOffer
                [ branch "Go" Nothing Nothing Nothing
                    (GrammarV1ReferenceSessionEnd "Done")
                , branch "Stop"
                    (Just [param "z" (GrammarV1ReferencePayloadPrimitive "String")])
                    Nothing
                    Nothing
                    (GrammarV1ReferenceSessionEnd "Done")
                ])
             ]]
          )
        , ( "recursive-continue"
          , "protocol P { role A = recursive Loop = send(x: U8) then continue Loop; role B = end Done; }"
          , [[ role "A"
                (GrammarV1ReferenceSessionRecursive "Loop"
                  (GrammarV1ReferenceSessionSend
                    (param "x" (GrammarV1ReferencePayloadPrimitive "U8"))
                    Nothing
                    Nothing
                    (GrammarV1ReferenceSessionContinue "Loop")))
             , role "B" (GrammarV1ReferenceSessionEnd "Done")
             ]]
          )
        , ( "unicode-session-identifiers"
          , "protocol Π { role Α = send(μήνυμα: U8) then end Τέλος; role Β = end Τέλος; }"
          , [[ role "Α"
                (GrammarV1ReferenceSessionSend
                  (param "μήνυμα" (GrammarV1ReferencePayloadPrimitive "U8"))
                  Nothing
                  Nothing
                  (GrammarV1ReferenceSessionEnd "Τέλος"))
             , role "Β" (GrammarV1ReferenceSessionEnd "Τέλος")
             ]]
          )
        ]
      directResults =
        [ checkDirect label source expected
        | (label, source, expected) <- directCases
        ]
      malformedResult =
        case grammarV1ReferenceSessionCore (GrammarV1ReferenceLiteral "end") of
          Left _ -> Right ()
          Right value -> Left
            ("malformed-tree -- non-session root decoded as " <> show value)
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
          ("PASS: certified Grammar-v1 sessions agree with production AST ("
            <> show (length cases) <> " fixtures)")
        else exitFailure

role :: Text -> GrammarV1ReferenceSessionCore -> GrammarV1ReferenceRoleSessionCore
role name value = GrammarV1ReferenceRoleSessionCore
  { grammarV1ReferenceRoleSessionName = name
  , grammarV1ReferenceRoleSessionValue = value
  }

param :: Text -> GrammarV1ReferenceTypePayload -> GrammarV1ReferenceTermParamCore
param name sourceType = GrammarV1ReferenceTermParamCore
  { grammarV1ReferenceTermParamName = name
  , grammarV1ReferenceTermParamType = sourceType
  }

branch
  :: Text
  -> Maybe [GrammarV1ReferenceTermParamCore]
  -> Maybe GrammarV1ReferenceStaticReferenceSpine
  -> Maybe GrammarV1ReferencePropositionCore
  -> GrammarV1ReferenceSessionCore
  -> GrammarV1ReferenceSessionBranchCore
branch label params boundary guard continuation = GrammarV1ReferenceSessionBranchCore
  { grammarV1ReferenceSessionBranchLabel = label
  , grammarV1ReferenceSessionBranchParams = params
  , grammarV1ReferenceSessionBranchBoundary = boundary
  , grammarV1ReferenceSessionBranchGuard = guard
  , grammarV1ReferenceSessionBranchContinuation = continuation
  }

reference
  :: [Text]
  -> [GrammarV1ReferenceStaticArgumentTag]
  -> GrammarV1ReferenceStaticReferenceSpine
reference parts arguments = GrammarV1ReferenceStaticReferenceSpine
  { grammarV1ReferenceStaticReferenceName = parts
  , grammarV1ReferenceStaticReferenceArguments = arguments
  }

checkDirect
  :: String
  -> Text
  -> [[GrammarV1ReferenceRoleSessionCore]]
  -> Either String ()
checkDirect label source expected = do
  (referenceValues, productionValues) <- parseValues label source
  if referenceValues /= productionValues
    then Left
      (label <> " -- certified/production session mismatch\nreference: "
        <> show referenceValues <> "\nproduction: " <> show productionValues)
    else if referenceValues /= expected
      then Left
        (label <> " -- unexpected session projection\nexpected: "
          <> show expected <> "\nactual: " <> show referenceValues)
      else Right ()

parseValues
  :: String
  -> Text
  -> Either String
      ( [[GrammarV1ReferenceRoleSessionCore]]
      , [[GrammarV1ReferenceRoleSessionCore]]
      )
parseValues label source = do
  sourceTokens <- mapLeft show
    (lexGrammarV1SourceTokens (Text.pack label) source)
  tree <- mapLeft show (grammarV1ReferenceParseSourceTokens sourceTokens)
  referenceValues <- mapLeft show (grammarV1ReferenceProtocolSessions tree)
  production <- mapLeft show
    (parseGrammarV1StructuralSource (Text.pack label) source)
  pure
    ( referenceValues
    , grammarV1ProductionProtocolSessions production
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
          referenceValues <- mapLeft show
            (grammarV1ReferenceProtocolSessions tree)
          production <- mapLeft show
            (parseGrammarV1StructuralSource sourceName source)
          let productionValues = grammarV1ProductionProtocolSessions production
          if referenceValues == productionValues
            then Right ()
            else Left
              (label <> " -- certified/production session mismatch\nreference: "
                <> show referenceValues <> "\nproduction: " <> show productionValues)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform result = case result of
  Left value -> Left (transform value)
  Right value -> Right value
