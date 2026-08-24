{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Phil.Assurance.Rocq
import Phil.Assurance.Types
import Phil.LLVM.StorageFailureDetailProofCertification
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  let root = "rocq-storage-failure-detail-lowering" </> "proof" </> "Phil" </> "LLVM"
      output = "storage-failure-detail-lowering-certificates"
      sourcePath = root </> "StorageFailureDetail.v"
      objectPath = root </> "StorageFailureDetail.vo"
      proofPath = output </> "PHIL-LLVM-STORAGE-FAIL-DETAIL-001.rocq.cert"
      finalPath = output </> "PHIL-LLVM-CERT-016.proof-bound.cert"
  sourceBytes <- ByteString.readFile sourcePath
  objectBytes <- ByteString.readFile objectPath
  case certifyRocqProof llvmStorageFailureDetailCertificationSpec sourceBytes objectBytes of
    Left err -> failWith ("Storage Failure Detail Rocq certification failed: " <> show err)
    Right proofBundle -> do
      let proofCertificate = rocqBundleCertificate proofBundle
          proofArtifact = rocqBundleCertificateArtifact proofBundle
      ByteString.writeFile proofPath
        (TextEncoding.encodeUtf8 (renderRocqProofCertificate proofCertificate))
      case phase0StorageFailureDetailProofCertification proofBundle of
        Left err -> failWith ("Storage Failure Detail proof-bound certification failed: " <> show err)
        Right finalBundle -> do
          let finalArtifact = storageFailureDetailProofArtifact finalBundle
          ByteString.writeFile finalPath
            (TextEncoding.encodeUtf8 (renderStorageFailureDetailProofCertification finalBundle))
          putStrLn "certified PHIL-LLVM-STORAGE-FAIL-DETAIL-001"
          putStrLn ("proof certificate artifact: " <>
            Text.unpack (unArtifactRef (artifactReference proofArtifact)))
          putStrLn ("proof certificate sha256: " <>
            Text.unpack (unDigest (artifactDigest proofArtifact)))
          putStrLn "certified PHIL-LLVM-CERT-016"
          putStrLn ("final certificate artifact: " <>
            Text.unpack (unArtifactRef (artifactReference finalArtifact)))
          putStrLn ("final certificate sha256: " <>
            Text.unpack (unDigest (artifactDigest finalArtifact)))

(</>) :: FilePath -> FilePath -> FilePath
left </> right
  | null left = right
  | last left == '/' = left <> right
  | otherwise = left <> "/" <> right

failWith :: String -> IO a
failWith message = do
  hPutStrLn stderr message
  exitFailure
