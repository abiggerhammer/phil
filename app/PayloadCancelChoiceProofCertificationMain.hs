{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Phil.Assurance
import Phil.LLVM
import Phil.LLVM.PayloadCancelChoiceProofCertification
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [ systemsPayloadCancelSource, systemsPayloadCancelObject
      , llvmPayloadCancelSource, llvmPayloadCancelObject
      , systemsFinalSource, systemsFinalObject
      , llvmFinalSource, llvmFinalObject
      , systemsRejectedSource, systemsRejectedObject
      , llvmRejectedSource, llvmRejectedObject
      , systemsAcceptedSource, systemsAcceptedObject
      , llvmAcceptedSource, llvmAcceptedObject
      , systemsStorageSource, systemsStorageObject
      , llvmStorageSource, llvmStorageObject
      , systemsDigestSource, systemsDigestObject
      , llvmDigestSource, llvmDigestObject
      , systemsRecordSource, systemsRecordObject
      , exactSource, exactObject
      , abiSource, abiObject
      , symbolSource, symbolObject
      , systemsPayloadCancelCertificatePath, llvmPayloadCancelCertificatePath
      , systemsFinalCertificatePath, llvmFinalCertificatePath
      , systemsRejectedCertificatePath, llvmRejectedCertificatePath
      , systemsAcceptedCertificatePath, llvmAcceptedCertificatePath
      , systemsStorageCertificatePath, llvmStorageCertificatePath
      , systemsDigestCertificatePath, llvmDigestCertificatePath
      , systemsRecordCertificatePath, exactCertificatePath
      , abiCertificatePath, symbolCertificatePath
      , predecessorCertificatePath, finalCertificatePath
      ] -> do
        systemsPayloadCancelProof <- certify
          systemsPayloadCancelChoiceCertificationSpec
          systemsPayloadCancelSource systemsPayloadCancelObject
        llvmPayloadCancelProof <- certify
          llvmPayloadCancelChoiceCertificationSpec
          llvmPayloadCancelSource llvmPayloadCancelObject
        systemsFinalProof <- certify
          systemsFinalResponseCertificationSpec systemsFinalSource systemsFinalObject
        llvmFinalProof <- certify
          llvmFinalResponseCertificationSpec llvmFinalSource llvmFinalObject
        systemsRejectedProof <- certify
          systemsRejectedResponseCertificationSpec systemsRejectedSource systemsRejectedObject
        llvmRejectedProof <- certify
          llvmRejectedResponseCertificationSpec llvmRejectedSource llvmRejectedObject
        systemsAcceptedProof <- certify
          systemsAcceptedResponseCertificationSpec systemsAcceptedSource systemsAcceptedObject
        llvmAcceptedProof <- certify
          llvmAcceptedResponseCertificationSpec llvmAcceptedSource llvmAcceptedObject
        systemsStorageProof <- certify
          systemsStorageCertificationSpec systemsStorageSource systemsStorageObject
        llvmStorageProof <- certify
          llvmStorageCertificationSpec llvmStorageSource llvmStorageObject
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

        writeProofCertificate systemsPayloadCancelCertificatePath systemsPayloadCancelProof
        writeProofCertificate llvmPayloadCancelCertificatePath llvmPayloadCancelProof
        writeProofCertificate systemsFinalCertificatePath systemsFinalProof
        writeProofCertificate llvmFinalCertificatePath llvmFinalProof
        writeProofCertificate systemsRejectedCertificatePath systemsRejectedProof
        writeProofCertificate llvmRejectedCertificatePath llvmRejectedProof
        writeProofCertificate systemsAcceptedCertificatePath systemsAcceptedProof
        writeProofCertificate llvmAcceptedCertificatePath llvmAcceptedProof
        writeProofCertificate systemsStorageCertificatePath systemsStorageProof
        writeProofCertificate llvmStorageCertificatePath llvmStorageProof
        writeProofCertificate systemsDigestCertificatePath systemsDigestProof
        writeProofCertificate llvmDigestCertificatePath llvmDigestProof
        writeProofCertificate systemsRecordCertificatePath systemsRecordProof
        writeProofCertificate exactCertificatePath exactProof
        writeProofCertificate abiCertificatePath abiProof
        writeProofCertificate symbolCertificatePath symbolProof

        case phase0PayloadCancelChoiceProofCertification
            systemsPayloadCancelProof llvmPayloadCancelProof
            systemsFinalProof llvmFinalProof
            systemsRejectedProof llvmRejectedProof
            systemsAcceptedProof llvmAcceptedProof
            systemsStorageProof llvmStorageProof
            systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof of
          Left err -> failWith ("payload/cancel proof certification failed: " <> show err)
          Right bundle -> do
            let predecessor = payloadCancelChoiceProofCertificationPredecessor bundle
                predecessorText = renderFinalResponseReceiveProofCertification predecessor
                finalText = renderPayloadCancelChoiceProofCertification bundle
                finalArtifact = payloadCancelChoiceProofCertificationArtifact bundle
            ByteString.writeFile predecessorCertificatePath
              (TextEncoding.encodeUtf8 predecessorText)
            ByteString.writeFile finalCertificatePath
              (TextEncoding.encodeUtf8 finalText)
            putStrLn "reproduced proof-bound PHIL-LLVM-CERT-008 predecessor authority"
            putStrLn
              ("predecessor certificate sha256: " <>
                Text.unpack (unDigest (artifactDigest
                  (finalResponseReceiveProofCertificationArtifact predecessor))))
            putStrLn "certified PHIL-LLVM-CERT-009 with proof-bound payload/cancel authority"
            putStrLn
              ("certificate artifact: " <>
                Text.unpack (unArtifactRef (artifactReference finalArtifact)))
            putStrLn
              ("certificate sha256: " <>
                Text.unpack (unDigest (artifactDigest finalArtifact)))
    _ -> failWith
      "usage: phil-certify-payload-cancel-choice SYS_PAYLOAD_CANCEL.v SYS_PAYLOAD_CANCEL.vo LLVM_PAYLOAD_CANCEL.v LLVM_PAYLOAD_CANCEL.vo SYS_FINAL.v SYS_FINAL.vo LLVM_FINAL.v LLVM_FINAL.vo SYS_REJECTED.v SYS_REJECTED.vo LLVM_REJECTED.v LLVM_REJECTED.vo SYS_ACCEPTED.v SYS_ACCEPTED.vo LLVM_ACCEPTED.v LLVM_ACCEPTED.vo SYS_STORAGE.v SYS_STORAGE.vo LLVM_STORAGE.v LLVM_STORAGE.vo SYS_DIGEST.v SYS_DIGEST.vo LLVM_DIGEST.v LLVM_DIGEST.vo SYS_RECORD.v SYS_RECORD.vo EXACT.v EXACT.vo ABI.v ABI.vo SYMBOL.v SYMBOL.vo SYS_PAYLOAD_CANCEL.cert LLVM_PAYLOAD_CANCEL.cert SYS_FINAL.cert LLVM_FINAL.cert SYS_REJECTED.cert LLVM_REJECTED.cert SYS_ACCEPTED.cert LLVM_ACCEPTED.cert SYS_STORAGE.cert LLVM_STORAGE.cert SYS_DIGEST.cert LLVM_DIGEST.cert SYS_RECORD.cert EXACT.cert ABI.cert SYMBOL.cert CERT008.cert CERT009.cert"

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
