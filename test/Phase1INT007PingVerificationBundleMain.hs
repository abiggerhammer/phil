{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.Static
  ( DeclarationKey (..)
  , DefinitionRevision (..)
  )
import Phil.Handoff.Phase1VerificationBundle
import Phil.Verification
  ( AssurancePolicyRevision (..)
  , VerificationObligationGraph (..)
  )
import Phil.Verification.Bundle
  ( VerificationBundle (..)
  )
import Phil.Verification.GrammarV1WholeSource
import System.Exit (exitFailure)

data PingStage = PingStage
  { pingStageLabel :: String
  , pingStageSourcePath :: FilePath
  , pingStageSupplementalPath :: Maybe FilePath
  , pingStageArchitectureKey :: DeclarationKey
  , pingStageArchitectureRevision :: DefinitionRevision
  , pingStagePolicyRevision :: AssurancePolicyRevision
  , pingStageSummaryPath :: FilePath
  }

stages :: [PingStage]
stages =
  [ stage "stage1-one-shot"
      "handoff/phase1/ping/stage1-one-shot.phil"
      Nothing
      "architecture.LocalPing"
      "architecture.local-ping.v1"
      "phase1.int007.ping.stage1.verification.v1"
  , stage "stage2-request-reply"
      "handoff/phase1/ping/stage2-request-reply.phil"
      Nothing
      "architecture.RoundTrip"
      "architecture.round-trip.v1"
      "phase1.int007.ping.stage2.verification.v1"
  , stage "stage3-bounded"
      "handoff/phase1/ping/stage3-bounded.phil"
      Nothing
      "architecture.BoundedPing"
      "architecture.bounded-ping.v1"
      "phase1.int007.ping.stage3.verification.v1"
  , stage "stage4-unbounded"
      "handoff/phase1/ping/stage4-unbounded.phil"
      Nothing
      "architecture.BarePing"
      "architecture.bare-ping.v1"
      "phase1.int007.ping.stage4.verification.v1"
  , stage "stage5-interruptible"
      "handoff/phase1/ping/stage5-interruptible.phil"
      (Just "handoff/phase1/ping/stage5-cancel-on-signal.phil")
      "architecture.InterruptiblePing"
      "architecture.interruptible-ping.v1"
      "phase1.int007.ping.stage5.verification.v1"
  ]
  where
    stage label sourcePath supplementalPath architectureKey architectureRevision policyRevision =
      PingStage
        { pingStageLabel = label
        , pingStageSourcePath = sourcePath
        , pingStageSupplementalPath = supplementalPath
        , pingStageArchitectureKey = DeclarationKey architectureKey
        , pingStageArchitectureRevision = DefinitionRevision architectureRevision
        , pingStagePolicyRevision = AssurancePolicyRevision policyRevision
        , pingStageSummaryPath =
            "handoff/phase1/ping/" <> label <> "-verification-bundle-v1.tsv"
        }

main :: IO ()
main = do
  results <- mapM checkStage stages
  if and results then pure () else exitFailure

checkStage :: PingStage -> IO Bool
checkStage stage = do
  primary <- TextIO.readFile (pingStageSourcePath stage)
  supplemental <- case pingStageSupplementalPath stage of
    Nothing -> pure []
    Just path -> do
      source <- TextIO.readFile path
      pure [("cancel-on-signal", source)]
  expectedSource <- TextIO.readFile (pingStageSummaryPath stage)
  case decodePhase1VerificationBundleSummary expectedSource of
    Left errorValue -> do
      putStrLn ("FAIL: " <> pingStageLabel stage <> " summary decode -- " <> show errorValue)
      pure False
    Right expected ->
      case grammarV1WholeSourceVerificationBundle
          GrammarV1WholeSourceVerificationSpec
            { wholeSourcePrimaryLabel = fromString (pingStageLabel stage)
            , wholeSourcePrimaryText = primary
            , wholeSourceSupplementalUnits = supplemental
            , wholeSourceArchitectureKey = pingStageArchitectureKey stage
            , wholeSourceArchitectureRevision = pingStageArchitectureRevision stage
            , wholeSourceProgramKey = DeclarationKey "program.main"
            , wholeSourcePolicyRevision = pingStagePolicyRevision stage
            } of
        Left errorValue -> do
          putStrLn ("FAIL: " <> pingStageLabel stage <> " whole-source bridge -- " <> show errorValue)
          pure False
        Right bundle -> do
          let graph = verificationBundleObligationGraph bundle
              graphEmpty =
                Map.null (verificationGraphNodes graph)
                  && Set.null (verificationGraphDependencies graph)
                  && Set.null (verificationGraphCertificationScope graph)
              evidenceEmpty = Map.null (verificationBundleAcceptedEvidence bundle)
              actual = derivePhase1VerificationBundleSummary bundle
          if not graphEmpty
            then do
              putStrLn ("FAIL: " <> pingStageLabel stage
                <> " invented residual verification obligations")
              pure False
            else if not evidenceEmpty
              then do
                putStrLn ("FAIL: " <> pingStageLabel stage
                  <> " invented accepted evidence")
                pure False
              else if actual == expected
                then do
                  putStrLn ("PASS: INT-007 " <> pingStageLabel stage
                    <> " whole-source VerificationBundle reconstructs exactly")
                  pure True
                else do
                  putStrLn ("FAIL: INT-007 " <> pingStageLabel stage
                    <> " VerificationBundle summary drift")
                  putStrLn ("ACTUAL " <> pingStageLabel stage <> " VERIFICATION SUMMARY BEGIN")
                  TextIO.putStr (renderPhase1VerificationBundleSummary actual)
                  putStrLn ("ACTUAL " <> pingStageLabel stage <> " VERIFICATION SUMMARY END")
                  pure False

fromString :: String -> Text.Text
fromString = Text.pack
