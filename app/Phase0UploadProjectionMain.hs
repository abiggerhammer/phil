module Main (main) where

import qualified Data.Text.IO as TextIO
import Paths_phil_core (getDataFileName)
import Phil.Compiler.Phase0UploadProjection
import Phil.Systems (systemsArtifactDigest)

main :: IO ()
main = do
  clientPath <- getDataFileName "examples/upload/client.phil"
  serverPath <- getDataFileName "examples/upload/server.phil"
  clientSource <- TextIO.readFile clientPath
  serverSource <- TextIO.readFile serverPath
  case projectPhase0UploadSources clientSource serverSource of
    Left err -> fail (show err)
    Right projection -> do
      putStrLn ("source-pair: " <> show (phase0ProjectionSourceDigest projection))
      putStrLn ("base-systems: " <> show
        (systemsArtifactDigest (phase0ProjectionBaseArtifact projection)))
      putStrLn ("final-systems: " <> show
        (systemsArtifactDigest (phase0ProjectionFinalArtifact projection)))
