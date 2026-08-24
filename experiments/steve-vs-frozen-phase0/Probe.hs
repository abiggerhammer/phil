{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.Check (checkSurfaceComponent)
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Phase0 (phase0EnvironmentFor)
import Phil.Surface.Syntax (SurfaceFile (..))
import System.Exit (exitFailure)

fixturePath :: FilePath
fixturePath = "examples/steve/steve.phil"

main :: IO ()
main = do
  source <- TextIO.readFile fixturePath
  case parseSurfaceFile (Text.pack fixturePath) source of
    Left diagnostic -> failCase ("Steve did not parse: " <> show diagnostic)
    Right (SurfaceFile components) -> do
      putStrLn ("PASS: frozen Phase 0 parser accepted Steve (" <> show (length components) <> " components)")
      case phase0EnvironmentFor fixturePath of
        Left detail
          | "no Phase 0 checking environment for " `Text.isPrefixOf` detail -> do
              putStrLn ("EXPECTED STOP: " <> Text.unpack detail)
              putStrLn "CLASSIFICATION: semantic-environment generalization boundary"
          | otherwise -> failCase ("unexpected Phase 0 environment failure: " <> Text.unpack detail)
        Right environment -> do
          putStrLn "UNEXPECTED: frozen Phase 0 supplied a checking environment for Steve"
          mapM_ (checkOne environment) components
          failCase "Steve reached whole-component semantic checking; update the baseline classification"

checkOne environment component =
  case checkSurfaceComponent environment component of
    Left errorValue -> putStrLn ("semantic result: " <> show errorValue)
    Right _ -> putStrLn "semantic result: accepted"

failCase :: String -> IO a
failCase detail = do
  putStrLn ("FAIL: " <> detail)
  exitFailure
