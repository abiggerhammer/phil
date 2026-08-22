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
    [ systemsDigestSource, systemsDigestObject
      , llvmDigestSource, llvmDigestObject
      , systemsRecordSource, systemsRecordObject
      , exactSource, exactObject
      , abiSource, abiObject
      , symbolSource, symbolObject
      , systemsDigestCertificatePath, llvmDigestCertificatePath
      , systemsRecordCertificatePath, exactCertificatePath
      , abiCertificatePath, symbolCertificatePath
      , predecessorCertificatePath, finalCertificatePath
      ] -> do
        systemsDigestProof <- certify
          systemsDigestValidationCertificationSpec systemsDigestSource systemsDigestObject
        llvmDigestProof <- certify
          llvmDigestValidationCertificationSpec llvmDigestSource llvmDigestObject
        systemsRecordProof <- certify
          systemsRecognizedRecordCertificationSpec systemsRecordSource systemsRecordObject
        exactProof <- certify
          llvmExactReceiveCertificationSpec exactSource exactObject
        abiProof <- certify
          llvmRecognizedRecordABICertificationSpec abiSource abiObject
        symbolProof <- certify
          llvmRuntimeSymbolCertificationSpec symbolSource symbolObject

        writeProofCertificate systemsDigestCertificatePath systemsDigestProof
        writeProofCertificate llvmDigestCertificatePath llvmDigestProof
        writeProofCertificate systemsRecordCertificatePath systemsRecordProof
        writeProofCertificate exactCertificatePath exactProof
        writeProofCertificate abiCertificatePath abiProof
        writeProofCertificate symbolCertificatePath symbolProof

        case phase0DigestValidationProofCertification
            systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof of
          Left err -> failWith ("digest-validation proof certification failed: " <> show err)
          Right bundle -> do
            let predecessor = digestValidationProofCertificationPredecessor bundle
                predecessorText = renderExactReceiveProofCertification predecessor
                finalText = renderDigestValidationProofCertification bundle
                finalArtifact = digestValidationProofCertificationArtifact bundle
            ByteString.writeFile predecessorCertificatePath
              (TextEncoding.encodeUtf8 predecessorText)
            ByteString.writeFile finalCertificatePath
              (TextEncoding.encodeUtf8 finalText)
            putStrLn "reproduced proof-bound PHIL-LLVM-CERT-003 predecessor authority"
            putStrLn
              ("predecessor certificate sha256: " <>
                Text.unpack (unDigest (artifactDigest
                  (exactReceiveProofCertificationArtifact predecessor))))
            putStrLn "certified PHIL-LLVM-CERT-004 with proof-bound digest authority"
            putStrLn
              ("certificate artifact: " <>
                Text.unpack (unArtifactRef (artifactReference finalArtifact)))
            putStrLn
              ("certificate sha256: " <>
                Text.unpack (unDigest (artifactDigest finalArtifact)))
    _ -> failWith
      "usage: phil-certify-digest-validation SYS_DIGEST.v SYS_DIGEST.vo LLVM_DIGEST.v LLVM_DIGEST.vo SYS_RECORD.v SYS_RECORD.vo EXACT.v EXACT.vo ABI.v ABI.vo SYMBOL.v SYMBOL.vo SYS_DIGEST.cert LLVM_DIGEST.cert SYS_RECORD.cert EXACT.cert ABI.cert SYMBOL.cert CERT003.cert CERT004.cert"

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
