{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (IOException, try)
import Data.Either (isRight)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Data.Word (Word8)
import Phil.Surface.GrammarV1.Parser (parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.ReferenceKernelBridge
  ( grammarV1ReferenceAcceptsSource
  , textToKernelString
  )
import qualified SurfaceGrammarRecognizerKernel as Kernel
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
  case utf8RepresentationCheck of
    Left detail -> putStrLn ("FAIL: " <> detail) >> exitFailure
    Right () -> pure ()
  input <- TextIO.getContents
  case traverse parseCaseLine (filter (not . Text.null) (Text.lines input)) of
    Left detail -> putStrLn ("FAIL: manifest stream -- " <> detail) >> exitFailure
    Right [] -> putStrLn "FAIL: manifest stream -- no corpus cases" >> exitFailure
    Right cases -> do
      results <- traverse runCase cases
      let failures = [detail | Left detail <- results]
      mapM_ putStrLn ["FAIL: " <> detail | detail <- failures]
      if null failures
        then putStrLn
          ("PASS: extracted Grammar-v1 reference bridge agrees with production corpus ("
            <> show (length cases) <> " fixtures)")
        else exitFailure

utf8RepresentationCheck :: Either String ()
utf8RepresentationCheck = do
  expectBytes "empty Text" [] (textToKernelString "")
  expectBytes "ASCII Text" [0x41, 0x42, 0x43] (textToKernelString "ABC")
  expectBytes
    "multi-byte UTF-8 Text"
    [0x41, 0xc3, 0xa9, 0xce, 0xbb]
    (textToKernelString "Aéλ")

expectBytes :: String -> [Word8] -> Kernel.String -> Either String ()
expectBytes label expected actual =
  let observed = kernelStringBytes actual
  in if observed == expected
      then Right ()
      else Left
        (label <> " -- expected bytes " <> show expected <> ", observed " <> show observed)

kernelStringBytes :: Kernel.String -> [Word8]
kernelStringBytes value = case value of
  Kernel.EmptyString -> []
  Kernel.String0 ascii rest -> kernelAsciiByte ascii : kernelStringBytes rest

kernelAsciiByte :: Kernel.Ascii0 -> Word8
kernelAsciiByte ascii = case ascii of
  Kernel.Ascii bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 ->
    contribution 0x01 bit0
      + contribution 0x02 bit1
      + contribution 0x04 bit2
      + contribution 0x08 bit3
      + contribution 0x10 bit4
      + contribution 0x20 bit5
      + contribution 0x40 bit6
      + contribution 0x80 bit7
  where
    contribution weight present = if present then weight else 0

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
      expected = corpusCaseExpectation corpusCase == "parse"
  sourceResult <- try (TextIO.readFile path) :: IO (Either IOException Text)
  pure $ case sourceResult of
    Left exception -> Left (label <> " -- unable to read fixture: " <> show exception)
    Right source ->
      let productionAccepted = isRight (parseGrammarV1StructuralSource sourceName source)
          referenceResult = grammarV1ReferenceAcceptsSource sourceName source
          referenceAccepted = either (const False) id referenceResult
      in if productionAccepted /= expected
          then Left
            (label <> " -- production parser expectation drift: expected "
              <> show expected <> ", observed " <> show productionAccepted)
          else if referenceAccepted /= expected
            then Left
              (label <> " -- extracted recognizer expectation mismatch: expected "
                <> show expected <> ", observed " <> show referenceAccepted
                <> case referenceResult of
                    Left diagnostic -> "; lexer diagnostic: " <> show diagnostic
                    Right _ -> "")
            else if referenceAccepted /= productionAccepted
              then Left
                (label <> " -- production/reference acceptance disagree: production="
                  <> show productionAccepted <> ", reference=" <> show referenceAccepted)
              else Right ()
