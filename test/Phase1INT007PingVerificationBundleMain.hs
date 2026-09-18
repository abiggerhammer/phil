{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text.IO as TextIO
import Phil.Handoff.Phase1VerificationBundle
import Phil.Handoff.Phase1WholeSourceVerification
import Phil.Verification
  ( VerificationObligationGraph (..)
  )
import Phil.Verification.Bundle
  ( VerificationBundle (..)
  )
import Phil.Verification.GrammarV1WholeSource
import System.Exit (exitFailure)

stages :: [(String, FilePath)]
stages =
  [ ("stage1-one-shot", "handoff/phase1/ping/stage1-verification-v1.tsv")
  , ("stage2-request-reply", "handoff/phase1/ping/stage2-verification-v1.tsv")
  , ("stage3-bounded", "handoff/phase1/ping/stage3-verification-v1.tsv")
  , ("stage4-unbounded", "handoff/phase1/ping/stage4-verification-v1.tsv")
  , ("stage5-interruptible", "handoff/phase1/ping/stage5-verification-v1.tsv")
  ]

main :: IO ()
main = do
  results <- mapM (uncurry checkStage) stages
  if and results then pure () else exitFailure

checkStage :: String -> FilePath -> IO Bool
checkStage label descriptorPath = do
  descriptorSource <- TextIO.readFile descriptorPath
  case decodePhase1WholeSourceVerificationDescriptor descriptorSource of
    Left errorValue -> do
      putStrLn ("FAIL: " <> label <> " descriptor decode -- " <> show errorValue)
      pure False
    Right descriptor -> do
      materialized <-
        materializePhase1WholeSourceVerificationDescriptor "." descriptor
      case materialized of
        Left errorValue -> do
          putStrLn ("FAIL: " <> label <> " descriptor materialization -- "
            <> show errorValue)
          pure False
        Right (spec, expectedSource) ->
          case decodePhase1VerificationBundleSummary expectedSource of
            Left errorValue -> do
              putStrLn ("FAIL: " <> label <> " summary decode -- "
                <> show errorValue)
              pure False
            Right expected ->
              case grammarV1WholeSourceVerificationBundle spec of
                Left errorValue -> do
                  putStrLn ("FAIL: " <> label <> " whole-source bridge -- "
                    <> show errorValue)
                  pure False
                Right bundle -> checkBundle label expected bundle

checkBundle
  :: String
  -> Phase1VerificationBundleSummary
  -> VerificationBundle
  -> IO Bool
checkBundle label expected bundle = do
  let graph = verificationBundleObligationGraph bundle
      graphEmpty =
        Map.null (verificationGraphNodes graph)
          && Set.null (verificationGraphDependencies graph)
          && Set.null (verificationGraphCertificationScope graph)
      evidenceEmpty = Map.null (verificationBundleAcceptedEvidence bundle)
      actual = derivePhase1VerificationBundleSummary bundle
  if not graphEmpty
    then do
      putStrLn ("FAIL: " <> label
        <> " invented residual verification obligations")
      pure False
    else if not evidenceEmpty
      then do
        putStrLn ("FAIL: " <> label <> " invented accepted evidence")
        pure False
      else if actual == expected
        then do
          putStrLn ("PASS: INT-007 " <> label
            <> " whole-source VerificationBundle reconstructs exactly")
          pure True
        else do
          putStrLn ("FAIL: INT-007 " <> label
            <> " VerificationBundle summary drift")
          putStrLn ("ACTUAL " <> label <> " VERIFICATION SUMMARY BEGIN")
          TextIO.putStr (renderPhase1VerificationBundleSummary actual)
          putStrLn ("ACTUAL " <> label <> " VERIFICATION SUMMARY END")
          pure False
