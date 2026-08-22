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
    [ systemsAcceptedSource, systemsAcceptedObject
      , llvmAcceptedSource, llvmAcceptedObject
      , systemsStorageSource, systemsStorageObject
      , llvmStorageSource, llvmStorageObject
      , systemsDigestSource, systemsDigestObject
      , llvmDigestSource, llvmDigestObject
      , systemsRecordSource, systemsRecordObject
      , exactSource, exactObject
      , abiSource, abiObject
      , symbolSource, symbolObject
      , systemsAcceptedCertificatePath, llvmAcceptedCertificatePath
      , systemsStorageCertificatePath, llvmStorageCertificatePath
      , systemsDigestCertificatePath, llvmDigestCertificatePath
      , systemsRecordCertificatePath, exactCertificatePath
      , abiCertificatePath, symbolCertificatePath
      , predecessorCertificatePath, finalCertificatePath
      ] -> certifyAcceptedResponse
        systemsAcceptedSource systemsAcceptedObject
        llvmAcceptedSource llvmAcceptedObject
        systemsStorageSource systemsStorageObject
        llvmStorageSource llvmStorageObject
        systemsDigestSource systemsDigestObject
        llvmDigestSource llvmDigestObject
        systemsRecordSource systemsRecordObject
        exactSource exactObject
        abiSource abiObject
        symbolSource symbolObject
        systemsAcceptedCertificatePath llvmAcceptedCertificatePath
        systemsStorageCertificatePath llvmStorageCertificatePath
        systemsDigestCertificatePath llvmDigestCertificatePath
        systemsRecordCertificatePath exactCertificatePath
        abiCertificatePath symbolCertificatePath
        predecessorCertificatePath finalCertificatePath

    [ systemsStorageSource, systemsStorageObject
      , llvmStorageSource, llvmStorageObject
      , systemsDigestSource, systemsDigestObject
      , llvmDigestSource, llvmDigestObject
      , systemsRecordSource, systemsRecordObject
      , exactSource, exactObject
      , abiSource, abiObject
      , symbolSource, symbolObject
      , systemsStorageCertificatePath, llvmStorageCertificatePath
      , systemsDigestCertificatePath, llvmDigestCertificatePath
      , systemsRecordCertificatePath, exactCertificatePath
      , abiCertificatePath, symbolCertificatePath
      , predecessorCertificatePath, finalCertificatePath
      ] -> certifyStorage
        systemsStorageSource systemsStorageObject
        llvmStorageSource llvmStorageObject
        systemsDigestSource systemsDigestObject
        llvmDigestSource llvmDigestObject
        systemsRecordSource systemsRecordObject
        exactSource exactObject
        abiSource abiObject
        symbolSource symbolObject
        systemsStorageCertificatePath llvmStorageCertificatePath
        systemsDigestCertificatePath llvmDigestCertificatePath
        systemsRecordCertificatePath exactCertificatePath
        abiCertificatePath symbolCertificatePath
        predecessorCertificatePath finalCertificatePath

    _ -> failWith $ unlines
      [ "usage (storage): phil-certify-storage SYS_STORAGE.v SYS_STORAGE.vo LLVM_STORAGE.v LLVM_STORAGE.vo SYS_DIGEST.v SYS_DIGEST.vo LLVM_DIGEST.v LLVM_DIGEST.vo SYS_RECORD.v SYS_RECORD.vo EXACT.v EXACT.vo ABI.v ABI.vo SYMBOL.v SYMBOL.vo SYS_STORAGE.cert LLVM_STORAGE.cert SYS_DIGEST.cert LLVM_DIGEST.cert SYS_RECORD.cert EXACT.cert ABI.cert SYMBOL.cert CERT004.cert CERT005.cert"
      , "usage (accepted): phil-certify-storage SYS_ACCEPTED.v SYS_ACCEPTED.vo LLVM_ACCEPTED.v LLVM_ACCEPTED.vo SYS_STORAGE.v SYS_STORAGE.vo LLVM_STORAGE.v LLVM_STORAGE.vo SYS_DIGEST.v SYS_DIGEST.vo LLVM_DIGEST.v LLVM_DIGEST.vo SYS_RECORD.v SYS_RECORD.vo EXACT.v EXACT.vo ABI.v ABI.vo SYMBOL.v SYMBOL.vo SYS_ACCEPTED.cert LLVM_ACCEPTED.cert SYS_STORAGE.cert LLVM_STORAGE.cert SYS_DIGEST.cert LLVM_DIGEST.cert SYS_RECORD.cert EXACT.cert ABI.cert SYMBOL.cert CERT005.cert CERT006.cert"
      ]

certifyStorage
  :: FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> IO ()
certifyStorage
    systemsStorageSource systemsStorageObject
    llvmStorageSource llvmStorageObject
    systemsDigestSource systemsDigestObject
    llvmDigestSource llvmDigestObject
    systemsRecordSource systemsRecordObject
    exactSource exactObject
    abiSource abiObject
    symbolSource symbolObject
    systemsStorageCertificatePath llvmStorageCertificatePath
    systemsDigestCertificatePath llvmDigestCertificatePath
    systemsRecordCertificatePath exactCertificatePath
    abiCertificatePath symbolCertificatePath
    predecessorCertificatePath finalCertificatePath = do
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

  writeProofCertificate systemsStorageCertificatePath systemsStorageProof
  writeProofCertificate llvmStorageCertificatePath llvmStorageProof
  writeProofCertificate systemsDigestCertificatePath systemsDigestProof
  writeProofCertificate llvmDigestCertificatePath llvmDigestProof
  writeProofCertificate systemsRecordCertificatePath systemsRecordProof
  writeProofCertificate exactCertificatePath exactProof
  writeProofCertificate abiCertificatePath abiProof
  writeProofCertificate symbolCertificatePath symbolProof

  case phase0StorageProofCertification
      systemsStorageProof llvmStorageProof
      systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof of
    Left err -> failWith ("storage proof certification failed: " <> show err)
    Right bundle -> do
      let predecessor = storageProofCertificationPredecessor bundle
          predecessorText = renderDigestValidationProofCertification predecessor
          finalText = renderStorageProofCertification bundle
          finalArtifact = storageProofCertificationArtifact bundle
      ByteString.writeFile predecessorCertificatePath
        (TextEncoding.encodeUtf8 predecessorText)
      ByteString.writeFile finalCertificatePath
        (TextEncoding.encodeUtf8 finalText)
      putStrLn "reproduced proof-bound PHIL-LLVM-CERT-004 predecessor authority"
      putStrLn
        ("predecessor certificate sha256: " <>
          Text.unpack (unDigest (artifactDigest
            (digestValidationProofCertificationArtifact predecessor))))
      putStrLn "certified PHIL-LLVM-CERT-005 with proof-bound storage authority"
      putStrLn
        ("certificate artifact: " <>
          Text.unpack (unArtifactRef (artifactReference finalArtifact)))
      putStrLn
        ("certificate sha256: " <>
          Text.unpack (unDigest (artifactDigest finalArtifact)))

certifyAcceptedResponse
  :: FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> FilePath -> FilePath
  -> IO ()
certifyAcceptedResponse
    systemsAcceptedSource systemsAcceptedObject
    llvmAcceptedSource llvmAcceptedObject
    systemsStorageSource systemsStorageObject
    llvmStorageSource llvmStorageObject
    systemsDigestSource systemsDigestObject
    llvmDigestSource llvmDigestObject
    systemsRecordSource systemsRecordObject
    exactSource exactObject
    abiSource abiObject
    symbolSource symbolObject
    systemsAcceptedCertificatePath llvmAcceptedCertificatePath
    systemsStorageCertificatePath llvmStorageCertificatePath
    systemsDigestCertificatePath llvmDigestCertificatePath
    systemsRecordCertificatePath exactCertificatePath
    abiCertificatePath symbolCertificatePath
    predecessorCertificatePath finalCertificatePath = do
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

  case phase0AcceptedResponseProofCertification
      systemsAcceptedProof llvmAcceptedProof
      systemsStorageProof llvmStorageProof
      systemsDigestProof llvmDigestProof systemsRecordProof exactProof abiProof symbolProof of
    Left err -> failWith ("accepted-response proof certification failed: " <> show err)
    Right bundle -> do
      let predecessor = acceptedResponseProofCertificationPredecessor bundle
          predecessorText = renderStorageProofCertification predecessor
          finalText = renderAcceptedResponseProofCertification bundle
          finalArtifact = acceptedResponseProofCertificationArtifact bundle
      ByteString.writeFile predecessorCertificatePath
        (TextEncoding.encodeUtf8 predecessorText)
      ByteString.writeFile finalCertificatePath
        (TextEncoding.encodeUtf8 finalText)
      putStrLn "reproduced proof-bound PHIL-LLVM-CERT-005 predecessor authority"
      putStrLn
        ("predecessor certificate sha256: " <>
          Text.unpack (unDigest (artifactDigest
            (storageProofCertificationArtifact predecessor))))
      putStrLn "certified PHIL-LLVM-CERT-006 with proof-bound accepted-response authority"
      putStrLn
        ("certificate artifact: " <>
          Text.unpack (unArtifactRef (artifactReference finalArtifact)))
      putStrLn
        ("certificate sha256: " <>
          Text.unpack (unDigest (artifactDigest finalArtifact)))

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
