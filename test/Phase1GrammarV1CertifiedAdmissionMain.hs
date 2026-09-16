{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ParseDiagnostic (..)
  , parseGrammarV1StructuralSource
  )
import System.Exit (exitFailure)

main :: IO ()
main =
  case parseGrammarV1StructuralSource
      "certified-admission-test"
      "module demo; record R {}" of
    Left GrammarV1CertifiedGrammarDiagnostic ->
      putStrLn "PASS: public Grammar-v1 parser fails closed when certified recognizer rejects"
    Left diagnostic -> do
      putStrLn ("FAIL: expected certified grammar rejection, got " <> show diagnostic)
      exitFailure
    Right parsed -> do
      putStrLn ("FAIL: production parser bypassed rejecting certified recognizer: " <> show parsed)
      exitFailure
