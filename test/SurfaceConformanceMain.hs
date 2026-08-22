{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM, unless)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Paths_phil_core (getDataFileName)
import Phil.Surface.Check
  ( SurfaceCheckError (..)
  , checkSurfaceComponent
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Phase0
  ( FixtureExpectation (..)
  , phase0EnvironmentFor
  , phase0ExpectationFor
  )
import Phil.Surface.Syntax (SurfaceFile (..))
import System.Exit (exitFailure)
import System.Timeout (timeout)

main :: IO ()
main = do
  results <- forM fixturePaths checkFixture
  unless (and results) exitFailure

checkFixture :: FilePath -> IO Bool
checkFixture relativePath = do
  path <- getDataFileName relativePath
  source <- TextIO.readFile path
  case (phase0ExpectationFor relativePath, phase0EnvironmentFor relativePath) of
    (Nothing, _) -> failCase "fixture has no expected disposition"
    (_, Left errorText) -> failCase (Text.unpack errorText)
    (Just expectation, Right environment) ->
      case parseSurfaceFile (Text.pack relativePath) source of
        Left diagnostic -> failCase ("parse failure: " ++ show diagnostic)
        Right (SurfaceFile [component]) -> do
          checked <- timeout fixtureTimeoutMicros $
            evaluate (checkSurfaceComponent environment component)
          case checked of
            Nothing -> failCase "checker did not terminate within the per-fixture limit"
            Just result -> compareResult expectation result
        Right (SurfaceFile components) ->
          failCase ("unexpected component count: " ++ show (length components))
  where
    compareResult expectation result =
      case (expectation, result) of
        (FixtureAccept, Right _) -> passCase
        (FixtureAccept, Left errorValue) ->
          failCase ("expected acceptance, got " ++ show errorValue)
        (FixtureReject expectedClass, Left errorValue)
          | surfaceErrorClass errorValue == expectedClass -> passCase
          | otherwise -> failCase
              ("expected rejection class " ++ show expectedClass
                ++ ", got " ++ show (surfaceErrorClass errorValue)
                ++ ": " ++ Text.unpack (surfaceErrorDetail errorValue))
        (FixtureReject expectedClass, Right _) ->
          failCase ("expected rejection class " ++ show expectedClass ++ ", but checker accepted")

    passCase = putStrLn ("PASS: " ++ relativePath) >> pure True
    failCase message = putStrLn ("FAIL: " ++ relativePath ++ " -- " ++ message) >> pure False

fixtureTimeoutMicros :: Int
fixtureTimeoutMicros = 2000000

fixturePaths :: [FilePath]
fixturePaths =
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
