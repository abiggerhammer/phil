{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Phil.Assurance
import Phil.LLVM
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [ systemsSource, systemsObject
      , abiSource, abiObject
      , symbolSource, symbolObject
      , systemsCertificatePath, abiCertificatePath, symbolCertificatePath
      , finalCertificatePath
      ] -> do
        systemsProof <- certify
          systemsRecognizedRecordCertificationSpec systemsSource systemsObject
        abiProof <- certify
          llvmRecognizedRecordABICertificationSpec abiSource abiObject
        symbolProof <- certify
          llvmRuntimeSymbolCertificationSpec symbolSource symbolObject

        writeProofCertificate systemsCertificatePath systemsProof
        writeProofCertificate abiCertificatePath abiProof
        writeProofCertificate symbolCertificatePath symbolProof

        case phase0RecognizedRecordProofCertification systemsProof abiProof symbolProof of
          Left err -> failWith ("recognized-record proof certification failed: " <> show err)
          Right bundle -> do
            let finalText = renderRecognizedRecordProofCertification bundle
                finalArtifact = recognizedRecordProofCertificationArtifact bundle
            ByteString.writeFile finalCertificatePath (TextEncoding.encodeUtf8 finalText)
            putStrLn "certified PHIL-LLVM-CERT-002 with proof-bound semantic authority"
            putStrLn
              ("certificate artifact: " <>
                Text.unpack (unArtifactRef (artifactReference finalArtifact)))
            putStrLn
              ("certificate sha256: " <>
                Text.unpack (unDigest (artifactDigest finalArtifact)))
    _ -> failWith
      "usage: phil-certify-recognized-record SYS.v SYS.vo ABI.v ABI.vo SYMBOL.v SYMBOL.vo SYS.cert ABI.cert SYMBOL.cert CERT002.cert"

certify
  :: RocqCertificationSpec
  -> FilePath
  -> FilePath
  -> IO RocqCertificationBundle
certify spec sourcePath objectPath = do
  sourceBytes <- ByteString.readFile sourcePath
  objectBytes <- ByteString.readFile objectPath
  case certifyRocqProof spec sourceBytes objectBytes of
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
