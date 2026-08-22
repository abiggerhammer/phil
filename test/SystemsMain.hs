{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Assurance hiding (LoweringLedgerRootMismatch)
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "Phase 0 certified systems lowering verifies" referencePasses
    , test "live source fact cannot disappear from stage contract" missingFactRejects
    , test "recognition success cannot expose transport before commit" missingCommitRejects
    , test "recognition cannot be reclassified as validation" recognitionClassRejects
    , test "wrong protocol edge rejects despite locally well-formed blocks" wrongProtocolEdgeRejects
    , test "systems IR cannot invent a second owner for the same storage" duplicateOwnerRejects
    , test "runtime copy must point to a copy-class lowering decision" hiddenCopyRejects
    , test "runtime-bound validator cannot disappear after certification" missingRuntimeSiteRejects
    , test "certified release cannot retain defensive diagnostic state" certifiedDiagnosticRejects
    , test "checked-runtime diagnostics require defensive cost classification" checkedRuntimeDiagnosticClassRejects
    , test "erasure cannot precede transfer of its surviving invariant" erasureWithoutTransferRejects
    , test "erasure operation requires a selected ADR-010 erasure use" unknownErasureUseRejects
    , test "stage source identity is content-bound" sourceIdentityRejects
    , test "systems target identity is content-bound" targetIdentityRejects
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
  in case verifyRebound bad of
      Left StageFactSetMismatch {} -> True
      _ -> False

missingCommitRejects :: Bool
missingCommitRejects =
  let bad0 = adjustBlock "UploadServer" "server.hello.commit"
        (\block -> block
          { systemsBlockOps = filter (not . isHelloCommit) (systemsBlockOps block) })
        phase0SystemsArtifact
      bad = rebindArtifact bad0
  in case verifyRebound bad of
      Left RecognitionSuccessMissingCommit {} -> True
      _ -> False
  where
    isHelloCommit OpCommitIngress { commitPending = ValueId "server.pending.hello" } = True
    isHelloCommit _ = False

recognitionClassRejects :: Bool
recognitionClassRejects =
  let bad0 = adjustBlock "UploadServer" "server.entry" change phase0SystemsArtifact
      bad = rebindArtifact bad0
  in case verifyRebound bad of
      Left RuntimeSiteKindMismatch {} -> True
      _ -> False
  where
    change block = case systemsBlockTerminator block of
      term@TermRecognize { recognizeSite = site } ->
        block { systemsBlockTerminator = term
          { recognizeSite = site { runtimeSiteKind = ValidationBoundary "HelloPolicy" } } }
      _ -> block

wrongProtocolEdgeRejects :: Bool
wrongProtocolEdgeRejects =
  let bad0 = adjustBlock "UploadServer" "server.begin.commit" change phase0SystemsArtifact
      bad = rebindArtifact bad0
  in case verifyRebound bad of
      Left StageRequiredEdgeMissing {} -> True
      _ -> False
  where
    change block = case systemsBlockTerminator block of
      term@TermRuntimeCheck {} ->
        block { systemsBlockTerminator = term { checkSuccess = BlockId "server.accepted" } }
      _ -> block

duplicateOwnerRejects :: Bool
duplicateOwnerRejects =
  let bad0 = adjustFunction "UploadClient" addDuplicate phase0SystemsArtifact
      bad = rebindArtifact bad0
  in case verifyRebound bad of
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
      bad1 = adjustBlock "UploadClient" "client.entry" addCopy bad0
      bad = rebindArtifact bad1
  in case verifyRebound bad of
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
  let bad0 = adjustBlock "UploadServer" "server.hello.commit"
        (\block -> block { systemsBlockTerminator = TermJump (BlockId "server.version.choose") })
        phase0SystemsArtifact
      bad = rebindArtifact bad0
  in case verifyRebound bad of
      Left RetainedRuntimeUseMissingSite {} -> True
      _ -> False

certifiedDiagnosticRejects :: Bool
certifiedDiagnosticRejects =
  let bad0 = adjustBlock "UploadClient" "client.entry"
        (\block -> block
          { systemsBlockOps = OpDiagnostic "session-state" (DecisionId "lower.runtime.semantic_call")
              : systemsBlockOps block })
        phase0SystemsArtifact
      bad = rebindArtifact bad0
  in case verifyRebound bad of
      Left DiagnosticInCertifiedRelease {} -> True
      _ -> False

checkedRuntimeDiagnosticClassRejects :: Bool
checkedRuntimeDiagnosticClassRejects =
  let withDiagnostic = adjustBlock "UploadClient" "client.entry"
        (\block -> block
          { systemsBlockOps = OpDiagnostic "session-state" (DecisionId "lower.runtime.semantic_call")
              : systemsBlockOps block })
        phase0SystemsArtifact
      program = systemsArtifactProgram withDiagnostic
      bad0 = withDiagnostic
        { systemsArtifactProgram = program { systemsProgramProfile = CheckedRuntime } }
      bad = rebindArtifact bad0
  in case verifyRebound bad of
      Left DiagnosticDecisionNotDefensive {} -> True
      _ -> False

erasureWithoutTransferRejects :: Bool
erasureWithoutTransferRejects =
  let ledger = systemsArtifactLoweringLedger phase0SystemsArtifact
      decisionId = DecisionId "lower.erase.digest_proof"
      decisions = Map.adjust removeTransfer decisionId (loweringLedgerDecisions ledger)
      changedLedger = LoweringLedger decisions (deriveLoweringLedgerRoot decisions)
      bad = phase0SystemsArtifact { systemsArtifactLoweringLedger = changedLedger }
  in case verifyRebound bad of
      Left ErasureWithoutFactTransfer {} -> True
      _ -> False
  where
    removeTransfer lowering = resealDecision lowering
      { loweringInvariantsTransferred = [] }

unknownErasureUseRejects :: Bool
unknownErasureUseRejects =
  let bad0 = adjustBlock "UploadServer" "server.hello.commit" change phase0SystemsArtifact
      bad = rebindArtifact bad0
  in case verifyRebound bad of
      Left ErasureOperationMissingUse {} -> True
      _ -> False
  where
    change block = block
      { systemsBlockOps = map rewrite (systemsBlockOps block) }
    rewrite op@OpEraseFact {} = op { erasedByUse = AssuranceUseId "use.systems.missing" }
    rewrite op = op

sourceIdentityRejects :: Bool
sourceIdentityRejects =
  let contract = systemsArtifactStageContract phase0SystemsArtifact
      bad = phase0SystemsArtifact
        { systemsArtifactStageContract = contract
            { stageSourceArtifactDigest = digestText "wrong source artifact" }
        }
  in case verifyRebound bad of
      Left SourceArtifactDigestMismatch {} -> True
      _ -> False

targetIdentityRejects :: Bool
targetIdentityRejects =
  let bad = adjustBlock "UploadClient" "client.entry"
        (\block -> block { systemsBlockOps = OpTraceEvent "identity drift" : systemsBlockOps block })
        phase0SystemsArtifact
  in case verifyRebound bad of
      Left TargetArtifactDigestMismatch {} -> True
      _ -> False

loweringRootTamperRejects :: Bool
loweringRootTamperRejects =
  let ledger = systemsArtifactLoweringLedger phase0SystemsArtifact
      bad = phase0SystemsArtifact
        { systemsArtifactLoweringLedger = ledger { loweringLedgerRoot = digestText "tampered" } }
  in case verifyRebound bad of
      Left LoweringLedgerRootMismatch {} -> True
      _ -> False

decisionDigestTamperRejects :: Bool
decisionDigestTamperRejects =
  let ledger = systemsArtifactLoweringLedger phase0SystemsArtifact
      decisionId = DecisionId "lower.payload.digest_borrow"
      decisions = Map.adjust
        (\lowering -> lowering { loweringDecisionDigest = digestText "tampered decision" })
        decisionId
        (loweringLedgerDecisions ledger)
      changedLedger = LoweringLedger decisions (deriveLoweringLedgerRoot decisions)
      bad = phase0SystemsArtifact { systemsArtifactLoweringLedger = changedLedger }
  in case verifyRebound bad of
      Left DecisionDigestMismatch {} -> True
      _ -> False

verifyRebound :: SystemsArtifact -> Either SystemsVerificationError ()
verifyRebound artifact = verifySystemsArtifact (contextForArtifact artifact) artifact

contextForArtifact :: SystemsArtifact -> SystemsVerificationContext
contextForArtifact artifact = base
  { systemsAssuranceManifest = manifest
  , systemsAssuranceVerificationContext = assuranceContext
  }
  where
    base = phase0SystemsVerificationContext
    ledger = systemsAssuranceLedger base
    loweringRoot = loweringLedgerRoot (systemsArtifactLoweringLedger artifact)
    implementationDigest = systemsArtifactDigest artifact
    manifest0 = (systemsAssuranceManifest base)
      { manifestImplementationDigest = implementationDigest
      , manifestLoweringLedgerRoot = loweringRoot
      }
    manifest = manifest0 { manifestId = deriveManifestId ledger manifest0 }
    assuranceContext = (systemsAssuranceVerificationContext base)
      { verificationImplementationDigest = implementationDigest
      , verificationLoweringLedgerRoot = loweringRoot
      }

rebindArtifact :: SystemsArtifact -> SystemsArtifact
rebindArtifact artifact = artifact
  { systemsArtifactStageContract = contract
  , systemsArtifactLoweringLedger = LoweringLedger decisions (deriveLoweringLedgerRoot decisions)
  }
  where
    program = systemsArtifactProgram artifact
    oldContract = systemsArtifactStageContract artifact
    sourceDigest = stageSourceArtifactDigest oldContract
    targetDigest = systemsProgramDigest program
    contract = oldContract { stageTargetArtifactDigest = targetDigest }
    decisions = Map.map rebindDecision
      (loweringLedgerDecisions (systemsArtifactLoweringLedger artifact))
    rebindDecision lowering = resealDecision lowering
      { loweringSourceArtifactDigest = sourceDigest
      , loweringTargetArtifactDigest = targetDigest
      }

resealDecision :: LoweringDecision -> LoweringDecision
resealDecision lowering = provisional
  { loweringDecisionDigest = deriveLoweringDecisionDigest provisional }
  where
    provisional = lowering { loweringDecisionDigest = Digest "" }

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
