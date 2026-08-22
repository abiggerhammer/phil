{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Paths_phil_core (getDataFileName)
import Phil.Core.Static
  ( declareOpaqueClaim
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Name (..)
  , RefSort (..)
  )
import Phil.Surface.Check
  ( RejectionClass (OpaqueProof)
  , SurfaceCheckError (..)
  , checkSurfaceComponent
  , emptySurfaceEnvironment
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax (SurfaceFile (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  path <- getDataFileName fixturePath
  source <- TextIO.readFile path
  case buildEnvironment of
    Left detail -> failCase ("could not build Steve static environment: " <> detail)
    Right environment ->
      case parseSurfaceFile (Text.pack fixturePath) source of
        Left diagnostic -> failCase ("parse failure: " <> show diagnostic)
        Right (SurfaceFile [component]) ->
          case checkSurfaceComponent environment component of
            Left errorValue
              | surfaceErrorClass errorValue == OpaqueProof ->
                  putStrLn
                    "PASS: Steve fixture 02 rejects generic proof of opaque DigestMatches as OpaqueProof"
              | otherwise ->
                  failCase
                    ("expected OpaqueProof, got "
                      <> show (surfaceErrorClass errorValue)
                      <> ": "
                      <> Text.unpack (surfaceErrorDetail errorValue))
            Right _ -> failCase "checker accepted an opaque DigestMatches proof"
        Right (SurfaceFile components) ->
          failCase ("unexpected component count: " <> show (length components))

fixturePath :: FilePath
fixturePath = "examples/steve/rejected/02-prove-opaque-digest.phil"

buildEnvironment =
  case declareOpaqueClaim
      "DigestMatches"
      [ (Name "id", SortOpaque "ContentId[SHA256]")
      , (Name "object", SortStableId "OwnedBytes")
      ]
      emptyStaticContext of
    Left staticError -> Left (show staticError)
    Right staticContext -> Right (emptySurfaceEnvironment staticContext)

failCase :: String -> IO ()
failCase detail = do
  putStrLn ("FAIL: " <> fixturePath <> " -- " <> detail)
  exitFailure
