{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Phil.Assurance
import Phil.LLVM.LocalRuntimeChoiceProofCertification
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [ systemsSource, systemsObject
      , llvmSource, llvmObject
      , systemsCertificatePath, llvmCertificatePath
      ] -> do
        systemsProof <- certify
          systemsLocalRuntimeChoiceCertificationSpec systemsSource systemsObject
        llvmProof <- certify
          llvmLocalRuntimeChoiceBoundaryCertificationSpec llvmSource llvmObject
        writeProofCertificate systemsCertificatePath systemsProof
        writeProofCertificate llvmCertificatePath llvmProof
    _ -> failWith
      "usage: phil-certify-local-runtime-choice SYS.v SYS.vo LLVM.v LLVM.vo SYS.cert LLVM.cert"

certify
  :: RocqCertificationSpec
  -> FilePath
  -> FilePath
  -> IO RocqCertificationBundle
certify spec sourcePath objectPath = do
  sourceBytes <- ByteString.readFile sourcePath
  objectBytes <- ByteString.readFile objectPath
  case packageTrustedRocqProof spec sourceBytes objectBytes of
    Left err -> failWith ("Rocq certification failed: " <> show err)
    Right bundle -> pure bundle

writeProofCertificate :: FilePath -> RocqCertificationBundle -> IO ()
writeProofCertificate path bundle = do
  let text = renderRocqProofCertificate (rocqBundleCertificate bundle)
      artifact = rocqBundleCertificateArtifact bundle
  ByteString.writeFile path (TextEncoding.encodeUtf8 text)
  putStrLn
    ("proof certificate: " <>
      Text.unpack (unArtifactRef (artifactReference artifact)) <>
      " sha256=" <> Text.unpack (unDigest (artifactDigest artifact)))

failWith :: String -> IO a
failWith message = do
  hPutStrLn stderr message
  exitFailure
