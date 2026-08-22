{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (forM, unless)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Paths_phil_core (getDataFileName)
import Phil.Surface.Parser
  ( ParseDiagnostic
  , parseSurfaceFile
  )
import Phil.Surface.Syntax
  ( Block (..)
  , Component (..)
  , Located (..)
  , SourcePoint (..)
  , SourceSpan (..)
  , SurfaceFile (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ testIO "accepted and rejected Phase 0 witnesses all parse" testWitnessCorpus
    , testPure "source spans preserve file, line, column, and offset" testSourceSpans
    , testPure "parser requires complete input consumption" testTrailingGarbage
    , testPure "unterminated blocks are syntax errors" testUnterminatedBlock
    ]
  unless (and results) exitFailure

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= report label

testPure :: String -> Either String () -> IO Bool
testPure label = report label

report :: String -> Either String () -> IO Bool
report label result =
  case result of
    Right () -> putStrLn ("PASS: " ++ label) >> pure True
    Left message -> putStrLn ("FAIL: " ++ label ++ " -- " ++ message) >> pure False

testWitnessCorpus :: IO (Either String ())
testWitnessCorpus = do
  results <- forM witnessPaths $ \relativePath -> do
    path <- getDataFileName relativePath
    source <- TextIO.readFile path
    pure $ case parseSurfaceFile (Text.pack relativePath) source of
      Right (SurfaceFile [_]) -> Right ()
      Right (SurfaceFile components) ->
        Left (relativePath ++ " parsed with unexpected component count " ++ show (length components))
      Left diagnostic -> Left (relativePath ++ " failed to parse: " ++ showDiagnostic diagnostic)
  pure $ case [message | Left message <- results] of
    [] -> Right ()
    failures -> Left (unlines failures)

witnessPaths :: [FilePath]
witnessPaths =
  [ "examples/upload/client.phil"
  , "examples/upload/server.phil"
  , "examples/rejected/01-reuse-consumed-endpoint.phil"
  , "examples/rejected/02-drop-live-endpoint.phil"
  , "examples/rejected/03-wrong-protocol-order.phil"
  , "examples/rejected/04-nonexhaustive-offer.phil"
  , "examples/rejected/05-raw-field-access.phil"
  , "examples/rejected/06-parsed-used-as-validated.phil"
  , "examples/rejected/07-unrelated-payload-length.phil"
  , "examples/rejected/08-incompatible-branch-join.phil"
  , "examples/rejected/09-continue-after-fatal-recognition-failure.phil"
  , "examples/rejected/10-accept-before-digest-check.phil"
  , "examples/rejected/11-copy-authority-capability.phil"
  , "examples/rejected/12-ignore-cancellation-cleanup.phil"
  , "examples/rejected/13-commit-unrelated-parsed.phil"
  , "examples/rejected/14-copy-owned-payload.phil"
  , "examples/rejected/15-drop-pending-receive.phil"
  , "examples/rejected/16-escape-shared-loan.phil"
  , "examples/rejected/17-use-evidence-wrong-context.phil"
  , "examples/rejected/18-prove-opaque-digest.phil"
  , "examples/rejected/19-label-does-not-transfer-proof.phil"
  , "examples/rejected/20-unchecked-wraparound-proof.phil"
  ]

testSourceSpans :: Either String ()
testSourceSpans =
  case parseSurfaceFile "span-test.phil" "component A {\n  let x = foo()\n}\n" of
    Left diagnostic -> Left ("valid source failed to parse: " ++ showDiagnostic diagnostic)
    Right (SurfaceFile [Located componentSpan component]) ->
      case blockStatements (locatedValue (componentBody component)) of
        [Located statementSpan _]
          | pointMatches (sourceSpanStart componentSpan) "span-test.phil" 1 1 0
              && pointMatches (sourceSpanStart statementSpan) "span-test.phil" 2 3 16 -> Right ()
          | otherwise -> Left
              ("unexpected source spans: component=" ++ show componentSpan
                ++ ", statement=" ++ show statementSpan)
        statements -> Left ("unexpected statement count: " ++ show (length statements))
    Right (SurfaceFile components) ->
      Left ("unexpected component count: " ++ show (length components))

pointMatches :: SourcePoint -> Text.Text -> Int -> Int -> Int -> Bool
pointMatches point file line column offset =
  sourcePointFile point == file
    && sourcePointLine point == line
    && sourcePointColumn point == column
    && sourcePointOffset point == offset

testTrailingGarbage :: Either String ()
testTrailingGarbage =
  case parseSurfaceFile "trailing.phil" "component A {} garbage" of
    Left _ -> Right ()
    Right _ -> Left "parser accepted trailing non-comment input"

testUnterminatedBlock :: Either String ()
testUnterminatedBlock =
  case parseSurfaceFile "unterminated.phil" "component A { let x = foo()" of
    Left _ -> Right ()
    Right _ -> Left "parser accepted an unterminated component block"

showDiagnostic :: ParseDiagnostic -> String
showDiagnostic = show
