module Main (main) where

import qualified Data.Text.IO as TextIO
import Phil.Phase0UploadProjection
import Phil.Systems (systemsArtifactDigest)
import System.Directory (doesFileExist)

main :: IO ()
main = do
  clientPath <- findFixture "examples/upload/client.phil"
  serverPath <- findFixture "examples/upload/server.phil"
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

findFixture :: FilePath -> IO FilePath
findFixture relative = do
  let candidates = [relative, "../" <> relative]
  existing <- filterM doesFileExist candidates
  case existing of
    path : _ -> pure path
    [] -> fail ("could not locate Phase 0 fixture " <> relative)

filterM :: Monad m => (a -> m Bool) -> [a] -> m [a]
filterM _ [] = pure []
filterM predicate (value : rest) = do
  keep <- predicate value
  remaining <- filterM predicate rest
  pure (if keep then value : remaining else remaining)
