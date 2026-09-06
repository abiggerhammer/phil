{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import qualified Data.Text.IO as TextIO
import Phil.Assurance.Rocq
import Phil.Assurance.Types
import Phil.Phase0UploadProjectionProofCertification
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  let proofRoot = "rocq-phase0-source-projection" </> "proof" </> "Phil" </> "Surface"
      output = "phase0-source-projection-certificates"
      proofSourcePath = proofRoot </> "Phase0UploadProjection.v"
      proofObjectPath = proofRoot </> "Phase0UploadProjection.vo"
      proofCertPath = output </> "PHIL-SURF-SYS-UPLOAD-PROJ-001.rocq.cert"
      finalCertPath = output </> "PHIL-LLVM-CERT-018.proof-bound.cert"

  proofSourceBytes <- ByteString.readFile proofSourcePath
  proofObjectBytes <- ByteString.readFile proofObjectPath
  proofBundle <- case packageTrustedRocqProof
      phase0UploadProjectionCertificationSpec
      proofSourceBytes
      proofObjectBytes of
    Left err -> failWith ("Phase 0 source projection Rocq certification failed: " <> show err)
    Right bundle -> pure bundle

  let proofCertificate = rocqBundleCertificate proofBundle
      proofArtifact = rocqBundleCertificateArtifact proofBundle
  ByteString.writeFile proofCertPath
    (TextEncoding.encodeUtf8 (renderRocqProofCertificate proofCertificate))

  projectionImplementationSource <- TextIO.readFile
    "phase0-projection/src/Phil/Phase0UploadProjection.hs"
  clientSource <- TextIO.readFile "examples/upload/client.phil"
  serverSource <- TextIO.readFile "examples/upload/server.phil"

  finalBundle <- case phase0UploadProjectionProofCertification
      proofBundle
      projectionImplementationSource
      clientSource
      serverSource of
    Left err -> failWith ("Phase 0 source-bound certification failed: " <> show err)
    Right bundle -> pure bundle

  let finalArtifact = projectionProofArtifact finalBundle
  ByteString.writeFile finalCertPath
    (TextEncoding.encodeUtf8 (renderPhase0UploadProjectionProofCertification finalBundle))

  putStrLn "certified PHIL-SURF-SYS-UPLOAD-PROJ-001"
  printArtifact proofArtifact
  putStrLn "certified PHIL-LLVM-CERT-018"
  printArtifact finalArtifact

printArtifact :: ArtifactIdentity -> IO ()
printArtifact artifact = do
  putStrLn ("artifact: " <> Text.unpack (unArtifactRef (artifactReference artifact)))
  putStrLn ("sha256: " <> Text.unpack (unDigest (artifactDigest artifact)))

(</>) :: FilePath -> FilePath -> FilePath
left </> right
  | null left = right
  | last left == '/' = left <> right
  | otherwise = left <> "/" <> right

failWith :: String -> IO a
failWith message = do
  hPutStrLn stderr message
  exitFailure
