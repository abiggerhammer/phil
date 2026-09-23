{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.Checker (emptyCheckState)
import Phil.Core.Decision
  ( CertificateError (..)
  , DecisionCertificate (..)
  , checkDecisionCertificate
  , proposeDecisionCertificate
  )
import Phil.Core.SortCheck (SortError (..))
import Phil.Core.Syntax
  ( Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ runTest "standalone checker rejects a sort-invalid goal before normalization"
        checkerRejectsMalformedOriginal
    , runTest "standalone proposer refuses a sort-invalid goal before normalization"
        proposerRejectsMalformedOriginal
    , runTest "well-sorted zero scaling remains admissible"
        wellSortedZeroScaleStillWorks
    ]
  if and results then pure () else exitFailure

checkerRejectsMalformedOriginal :: Either String ()
checkerRejectsMalformedOriginal =
  case checkDecisionCertificate emptyCheckState [] malformedGoal CertificateTruth of
    Left (CertificateSortError (ExpectedNatOperand term SortBool))
      | term == RefBool True -> Right ()
    other -> Left ("sort-invalid original goal was not rejected: " <> show other)

proposerRejectsMalformedOriginal :: Either String ()
proposerRejectsMalformedOriginal =
  case proposeDecisionCertificate emptyCheckState [] malformedGoal of
    Nothing -> Right ()
    Just certificate -> Left
      ("producer normalized a sort-invalid goal into a certificate: " <> show certificate)

wellSortedZeroScaleStillWorks :: Either String ()
wellSortedZeroScaleStillWorks = do
  case checkDecisionCertificate emptyCheckState [] wellSortedGoal CertificateTruth of
    Left errorValue -> Left ("well-sorted checker control failed: " <> show errorValue)
    Right () -> Right ()
  case proposeDecisionCertificate emptyCheckState [] wellSortedGoal of
    Just CertificateTruth -> Right ()
    other -> Left ("well-sorted producer control changed: " <> show other)

malformedGoal :: Proposition
malformedGoal =
  Equal
    (RefScale 0 (RefBool True))
    (RefNat 0)

wellSortedGoal :: Proposition
wellSortedGoal =
  Equal
    (RefScale 0 (RefNat 7))
    (RefNat 0)

runTest :: String -> Either String () -> IO Bool
runTest label result =
  case result of
    Right () -> putStrLn ("PASS: " <> label) >> pure True
    Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False
