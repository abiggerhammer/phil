{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance.Types
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "Phase 0 certified systems lowering verifies" referencePasses
    , test "live source fact cannot disappear from stage contract" missingFactRejects
    , test "recognition success cannot expose transport before commit" missingCommitRejects
    , test "recognition cannot be reclassified as validation" recognitionClassRejects
    , test "wrong protocol edge rejects despite locally well-formed blocks" wrongDigestEdgeRejects
    , test "systems IR cannot invent a second owner for the same storage" duplicateOwnerRejects
    , test "runtime copy must point to a copy-class lowering decision" hiddenCopyRejects
    , test "runtime-bound validator cannot disappear after certification" missingRuntimeSiteRejects
    , test "certified release cannot retain defensive diagnostic state" certifiedDiagnosticRejects
    , test "erasure operation requires a selected ADR-010 erasure use" unknownErasureUseRejects
    , test "lowering ledger root is content-bound" loweringRootTamperRejects
    , test "lowering decisions carry independently checked digests" decisionDigestTamperRejects
    ]
  if and results then pure () else exitFailure

referencePasses :: Bool
referencePasses =
  verifySystemsArtifact phase0SystemsVerificationContext phase0SystemsArtifact == Right ()

missingFactRejects :: Bool
missingFactRejects =
  let contract = systemsArtifactStageContract phase0SystemsArtifact
      bad = phase0SystemsArtifact
        { systemsArtifactStageContract = contract { stageFacts = drop 1 (stageFacts contract) } }
  in case verifySystemsArtifact phase0SystemsVerificationContext bad of
      Left StageFactSetMismatch {} -> True
      _ -> False

missingCommitRejects :: Bool
missingCommitRejects =
  let bad = adjustBlock "UploadServer" "server.hello.commit"
        (\block -> block
          { systemsBlockOps = filter (not . isHelloCommit) (systemsBlockOps block) })
        phase0SystemsArtifact
  in case verifySystemsArtifact phase0SystemsVerificationContext bad of
      Left RecognitionSuccessMissingCommit {} -> True
      _ -> False
  where
    isHelloCommit OpCommitIngress { commitPending = ValueId "server.pending.hello" } = True
    isHelloCommit _ = False

recognitionClassRejects :: Bool
recognitionClassRejects =
  let bad = adjustBlock "UploadServer" "server.entry" change phase0SystemsArtifact
  in case verifySystemsArtifact phase0SystemsVerificationContext bad of
      Left RuntimeSiteKindMismatch {} -> True
      _ -> False
  where
    change block = case systemsBlockTerminator block of
      term@TermRecognize { recognizeSite = site } ->
        block { systemsBlockTerminator = term
          { recognizeSite = site { runtimeSiteKind = ValidationBoundary "HelloPolicy" } } }
      _ -> block

wrongDigestEdgeRejects :: Bool
wrongDigestEdgeRejects =
  let bad = adjustBlock "UploadServer" "server.digest" change phase0SystemsArtifact
  in case verifySystemsArtifact phase0SystemsVerificationContext bad of
      Left StageRequiredEdgeMissing {} -> True
      _ -> False
  where
    change block = case systemsBlockTerminator block of
      term@TermRuntimeCheck {} ->
        block { systemsBlockTerminator = term { checkSuccess = BlockId "server.accepted" } }
      _ -> block

duplicateOwnerRejects :: Bool
duplicateOwnerRejects =
  let bad = adjustFunction "UploadClient" addDuplicate phase0SystemsArtifact
  in case verifySystemsArtifact phase0SystemsVerificationContext bad of
      Left DuplicateOwningStorage {} -> True
      _ -> False
  where
    addDuplicate function = function
      { systemsFunctionValues = Map.insert duplicateId duplicate (systemsFunctionValues function) }
    duplicateId = ValueId "client.payload.duplicate"
    duplicate = SystemsValue duplicateId (OwnedBuffer "Bytes[payload.length]") (Just "payload.client")

hiddenCopyRejects :: Bool
hiddenCopyRejects =
  let bad0 = adjustFunction "UploadClient" addTarget phase0SystemsArtifact
      bad = adjustBlock "UploadClient" "client.entry" addCopy bad0
  in case verifySystemsArtifact phase0SystemsVerificationContext bad of
      Left CopyWithoutCopyDecision {} -> True
      _ -> False
  where
    targetId = ValueId "client.payload.copy"
    addTarget function = function
      { systemsFunctionValues = Map.insert targetId
          (SystemsValue targetId (OwnedBuffer "Bytes[payload.length]") (Just "payload.client.copy"))
          (systemsFunctionValues function)
      }
    addCopy block = block
      { systemsBlockOps = OpCopy
          (ValueId "client.payload") targetId (DecisionId "lower.runtime.semantic_call")
          : systemsBlockOps block
      }

missingRuntimeSiteRejects :: Bool
missingRuntimeSiteRejects =
  let bad = adjustBlock "UploadServer" "server.hello.commit"
        (\block -> block { systemsBlockTerminator = TermJump (BlockId "server.version.choose") })
        phase0SystemsArtifact
  in case verifySystemsArtifact phase0SystemsVerificationContext bad of
      Left RetainedRuntimeUseMissingSite {} -> True
      _ -> False

certifiedDiagnosticRejects :: Bool
certifiedDiagnosticRejects =
  let bad = adjustBlock "UploadClient" "client.entry"
        (\block -> block
          { systemsBlockOps = OpDiagnostic "session-state" (DecisionId "lower.runtime.semantic_call")
              : systemsBlockOps block })
        phase0SystemsArtifact
  in case verifySystemsArtifact phase0SystemsVerificationContext bad of
      Left DiagnosticInCertifiedRelease {} -> True
      _ -> False

unknownErasureUseRejects :: Bool
unknownErasureUseRejects =
  let bad = adjustBlock "UploadServer" "server.digest" change phase0SystemsArtifact
  in case verifySystemsArtifact phase0SystemsVerificationContext bad of
      Left ErasureOperationMissingUse {} -> True
      _ -> False
  where
    change block = block
      { systemsBlockOps = map rewrite (systemsBlockOps block) }
    rewrite op@OpEraseFact {} = op { erasedByUse = AssuranceUseId "use.systems.missing" }
    rewrite op = op

loweringRootTamperRejects :: Bool
loweringRootTamperRejects =
  let ledger = systemsArtifactLoweringLedger phase0SystemsArtifact
      bad = phase0SystemsArtifact
        { systemsArtifactLoweringLedger = ledger { loweringLedgerRoot = digestText "tampered" } }
  in case verifySystemsArtifact phase0SystemsVerificationContext bad of
      Left LoweringLedgerRootMismatch {} -> True
      _ -> False

decisionDigestTamperRejects :: Bool
decisionDigestTamperRejects =
  let ledger = systemsArtifactLoweringLedger phase0SystemsArtifact
      decisionId = DecisionId "lower.payload.digest_borrow"
      decisions = Map.adjust
        (\decision -> decision { loweringDecisionDigest = digestText "tampered decision" })
        decisionId
        (loweringLedgerDecisions ledger)
      changedLedger = LoweringLedger decisions (deriveLoweringLedgerRoot decisions)
      badArtifact = phase0SystemsArtifact { systemsArtifactLoweringLedger = changedLedger }
      changedManifest0 = (systemsAssuranceManifest phase0SystemsVerificationContext)
        { manifestLoweringLedgerRoot = loweringLedgerRoot changedLedger }
      changedManifest = changedManifest0
        { manifestId = deriveManifestId
            (systemsAssuranceLedger phase0SystemsVerificationContext)
            changedManifest0
        }
      changedAssuranceContext = (systemsAssuranceVerificationContext phase0SystemsVerificationContext)
        { verificationLoweringLedgerRoot = loweringLedgerRoot changedLedger }
      changedContext = phase0SystemsVerificationContext
        { systemsAssuranceManifest = changedManifest
        , systemsAssuranceVerificationContext = changedAssuranceContext
        }
  in case verifySystemsArtifact changedContext badArtifact of
      Left DecisionDigestMismatch {} -> True
      _ -> False

adjustFunction
  :: Text
  -> (SystemsFunction -> SystemsFunction)
  -> SystemsArtifact
  -> SystemsArtifact
adjustFunction functionName modify artifact = artifact
  { systemsArtifactProgram = program
      { systemsProgramFunctions = Map.adjust modify functionName (systemsProgramFunctions program) }
  }
  where
    program = systemsArtifactProgram artifact

adjustBlock
  :: Text
  -> Text
  -> (SystemsBlock -> SystemsBlock)
  -> SystemsArtifact
  -> SystemsArtifact
adjustBlock functionName blockName modify =
  adjustFunction functionName $ \function -> function
    { systemsFunctionBlocks = Map.adjust modify (BlockId blockName) (systemsFunctionBlocks function) }

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
