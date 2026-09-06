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
    [ exactSource, exactObject
      , abiSource, abiObject
      , symbolSource, symbolObject
      , exactCertificatePath, abiCertificatePath, symbolCertificatePath
      , finalCertificatePath
      ] -> do
        exactProof <- certify
          llvmExactReceiveCertificationSpec exactSource exactObject
        abiProof <- certify
          llvmRecognizedRecordABICertificationSpec abiSource abiObject
        symbolProof <- certify
          llvmRuntimeSymbolCertificationSpec symbolSource symbolObject

        writeProofCertificate exactCertificatePath exactProof
        writeProofCertificate abiCertificatePath abiProof
        writeProofCertificate symbolCertificatePath symbolProof

        case phase0ExactReceiveProofCertification exactProof abiProof symbolProof of
          Left err -> failWith ("exact-receive proof certification failed: " <> show err)
          Right bundle -> do
            let finalText = renderExactReceiveProofCertification bundle
                finalArtifact = exactReceiveProofCertificationArtifact bundle
            ByteString.writeFile finalCertificatePath (TextEncoding.encodeUtf8 finalText)
            putStrLn "certified PHIL-LLVM-CERT-003 with proof-bound exact-receive authority"
            putStrLn
              ("certificate artifact: " <>
                Text.unpack (unArtifactRef (artifactReference finalArtifact)))
            putStrLn
              ("certificate sha256: " <>
                Text.unpack (unDigest (artifactDigest finalArtifact)))
    _ -> failWith
      "usage: phil-certify-exact-receive EXACT.v EXACT.vo ABI.v ABI.vo SYMBOL.v SYMBOL.vo EXACT.cert ABI.cert SYMBOL.cert CERT003.cert"

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
