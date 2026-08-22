{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.Context
  ( ResourceContext (linearBindings)
  , consumeLinear
  , emptyContext
  , insertBinding
  )
import Phil.Core.Syntax (Mode (Linear), Name (Name), Ty (TyOpaque))
import Phil.Surface.Parser (ParseDiagnostic (..), parseSurfaceFile)
import Phil.Surface.Syntax
  ( Component (..)
  , Located (..)
  , SourcePoint (..)
  , SurfaceFile (..)
  )
import System.Environment (getArgs)
import System.Exit (exitFailure)

main :: IO ()
main = do
  arguments <- getArgs
  case arguments of
    [] -> bootstrapDemo
    ["parse", path] -> parseFile path
    _ -> do
      putStrLn "usage: phil-core [parse FILE]"
      exitFailure

bootstrapDemo :: IO ()
bootstrapDemo = do
  let endpoint = Name "endpoint"
      endpointTy = TyOpaque "Endpoint[ServerUpload]"
  case insertBinding Linear endpoint endpointTy emptyContext >>= consumeLinear endpoint of
    Left err -> putStrLn ("phil-core bootstrap failed: " ++ show err)
    Right (_, residual) -> do
      putStrLn "phil-core bootstrap: linear endpoint consumed"
      putStrLn ("residual Δ = " ++ show (linearBindings residual))

parseFile :: FilePath -> IO ()
parseFile path = do
  source <- TextIO.readFile path
  case parseSurfaceFile (Text.pack path) source of
    Left diagnostic -> do
      putStrLn (renderDiagnostic diagnostic)
      exitFailure
    Right (SurfaceFile components) -> do
      let names = map (componentName . locatedValue) components
      putStrLn
        ("parsed " ++ show (length components) ++ " component(s): "
          ++ Text.unpack (Text.intercalate ", " names))
      putStrLn "parse-only: no semantic acceptance has been claimed"

renderDiagnostic :: ParseDiagnostic -> String
renderDiagnostic diagnostic =
  let point = parseDiagnosticPoint diagnostic
  in Text.unpack (sourcePointFile point)
      ++ ":" ++ show (sourcePointLine point)
      ++ ":" ++ show (sourcePointColumn point)
      ++ ": " ++ Text.unpack (parseDiagnosticMessage diagnostic)
