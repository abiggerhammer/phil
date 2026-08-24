{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.ExactSendProofCertification
  ( systemsExactSendCertificationSpec
  , llvmExactSendCertificationSpec
  , ExactSendProofCertificationError (..)
  , ExactSendProofCertificationBundle (..)
  , verifyCurrentExactSendTranslation
  , phase0ExactSendProofCertification
  , verifyPhase0ExactSendProofCertification
  , renderExactSendProofCertification
  ) where

import Control.Monad (forM_, unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Rocq
import Phil.Assurance.Types
import Phil.Assurance.Verify (ManifestError, verifyManifest)
import Phil.Core.Syntax (ObligationId (..), unObligationId)
import Phil.LLVM.ExactSend
import Phil.LLVM.HelloPolicyValidation
import Phil.LLVM.HelloPolicyValidationProofCertification
import Phil.LLVM.IR
import Phil.LLVM.Verify
import Phil.Systems.ClientOutbound
import Phil.Systems.IR
import Phil.Systems.Verify (SystemsVerificationContext (..))

systemsExactSendCertificationSpec :: RocqCertificationSpec
systemsExactSendCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "systems-exact-send"
  , rocqSpecObligation = ObligationId "PHIL-SYS-EXACT-SEND-001"
  , rocqSpecClaim =
      "For the verified current Phase 0 client-outbound Systems successor, the exact client transport remains a TransportHandle and client.payload remains the exact OwnedBuffer owner; the newly explicit digest borrow is non-owning and introduces no copy; owner identity survives the borrow/projection/digest path; exactly one send_exact operation consumes exact client.transport and client.payload at the retained ExactSendBoundary with no result value or recoverable source failure continuation; and no physical send ABI, physical I/O, or outer framing is claimed at Systems level."
  , rocqSpecKind = "Systems exact-send ownership and runtime-site semantics"
  , rocqSpecOrigin =
      "src/Phil/Systems/ClientOutbound.hs; src/Phil/LLVM/ExactSend.hs; proof/Phil/Systems/ExactSend.v"
  , rocqSpecScope = "Phil.Systems current client-outbound successor exact-send slice"
  , rocqSpecRepresentation =
      "normalized exact transport / original payload owner / non-owning borrow / retained ExactSendBoundary model"
  , rocqSpecSubjects =
      [ "client.transport : TransportHandle"
      , "client.payload : OwnedBuffer[Bytes[payload.length]]"
      , "client.payload_view : BorrowedSlice[client.payload]"
      , "send_exact(client.transport, client.payload)"
      , "ExactSendBoundary upload.payload.exact_length.client_send"
      ]
  , rocqSpecTheorems =
      [ "verified_systems_exact_send_reuses_hello_policy_authority"
      , "verified_systems_exact_send_preserves_exact_transport_and_payload_owner"
      , "verified_systems_exact_send_preserves_nonowning_borrow_and_no_copy"
      , "verified_systems_exact_send_preserves_one_exact_site_without_failure_edge"
      , "verified_systems_exact_send_binds_decision_and_claims_no_physical_transport"
      , "systems_exact_send_owner_or_copy_drift_is_rejected"
      , "systems_exact_send_call_or_site_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Systems/ExactSend.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Systems/ExactSend.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-SYS-EXACT-SEND-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-SYS-EXACT-SEND-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from the current ClientOutbound Haskell artifact to exact ValueId/BlockId/RuntimeSiteRef identities, borrow/copy multiplicity, lowering-decision identity, and absence of a recoverable source edge remain explicit trust boundaries. Physical transport implementation and completion semantics are outside this Systems theorem."
  }

llvmExactSendCertificationSpec :: RocqCertificationSpec
llvmExactSendCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "llvm-exact-send"
  , rocqSpecObligation = ObligationId "PHIL-LLVM-EXACT-SEND-001"
  , rocqSpecClaim =
      "For transport-exact-send-v1 over the current client-outbound Systems successor, verified lowering maps source client.payload exactly to the single explicit target owner parameter client.payload.owner, retains the exact ExactSendBoundary, emits exactly one phil_runtime_send_exact(ptr,ptr) with exact client transport and mapped payload identities, introduces no payload copy or recoverable failure edge, preserves proof-bound HelloPolicy/BeginPolicy/version target authority, rejects generic exact-send and ambient transport/payload state, and deliberately makes no physical claim about the newly explicit outbound Hello/Begin semantic operations, which remain generic outside this theorem's competence."
  , rocqSpecKind = "LLVM transport exact-send ABI v1"
  , rocqSpecOrigin =
      "src/Phil/LLVM/ExactSend.hs; docs/phase-0/exact-send-abi-v1.md; proof/Phil/LLVM/ExactSend.v"
  , rocqSpecScope = "Phil.LLVM transport-exact-send-v1 over client-outbound-v1 Systems successor"
  , rocqSpecRepresentation =
      "normalized source-owner to target-owner parameter / exact runtime operation / scoped generic-outbound model"
  , rocqSpecSubjects =
      [ "client.payload -> client.payload.owner"
      , "UploadClient(ptr client.transport, ptr client.payload.owner)"
      , "phil_runtime_send_exact(ptr,ptr)->void"
      , "ExactSendBoundary upload.payload.exact_length.client_send"
      ]
  , rocqSpecTheorems =
      [ "verified_llvm_exact_send_reuses_systems_and_hello_policy_authority"
      , "verified_llvm_exact_send_preserves_source_target_payload_identity"
      , "verified_llvm_exact_send_preserves_one_exact_runtime_operation"
      , "verified_llvm_exact_send_introduces_no_copy_failure_edge_or_ambient_state"
      , "verified_llvm_exact_send_scopes_out_client_outbound_physical_lowering"
      , "verified_llvm_exact_send_keeps_runtime_and_execution_gates_external"
      , "llvm_exact_send_mapping_or_operation_drift_is_rejected"
      , "llvm_exact_send_copy_failure_or_ambient_drift_is_rejected"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/LLVM/ExactSend.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/LLVM/ExactSend.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-LLVM-EXACT-SEND-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-LLVM-EXACT-SEND-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness; reviewed current-Systems/LLVM-to-normalized-proof correspondence; provider whole-send-or-nonreturn semantics; opaque payload-handle implementation/lifetime; physical I/O and OS/socket buffering; target calling convention; LLVM 18; linking; native execution; and outer framing remain explicit trust boundaries. Physical lowering of the newly explicit outbound Hello/Begin semantic operations is explicitly outside this theorem."
  }

data ExactSendProofCertificationError
  = ExactSendProofClientOutboundError ClientOutboundError
  | ExactSendProofLLVMVerificationError LLVMVerificationError
  | ExactSendProofSourceMismatch Text
  | ExactSendProofTargetMismatch Text
  | ExactSendProofWrongProof Text ObligationId ObligationId
  | ExactSendProofManifestError Text ManifestError
  | ExactSendProofFinalManifestError ManifestError
  deriving (Eq, Show)

data ExactSendProofCertificationBundle = ExactSendProofCertificationBundle
  { exactSendProofSystems :: ClientOutboundBundle
  , exactSendProofLLVM :: LLVMArtifact
  , exactSendProofPredecessor :: HelloPolicyValidationProofCertificationBundle
  , exactSendProofArtifact :: ArtifactIdentity
  , exactSendProofRecord :: Text
  , exactSendProofLedger :: AssuranceLedger
  , exactSendProofManifest :: AssuranceManifest
  , exactSendProofContext :: VerificationContext
  }
  deriving (Eq, Show)

verifyCurrentExactSendTranslation
  :: ClientOutboundBundle
  -> LLVMArtifact
  -> Either ExactSendProofCertificationError ()
verifyCurrentExactSendTranslation bundle llvmArtifact = do
  mapLeft ExactSendProofClientOutboundError (verifyClientOutboundBundle bundle)
  site <- verifyCurrentSourceExactSend bundle
  verifyCurrentTargetExactSend bundle site llvmArtifact
  case verifyHelloPolicyValidationLLVMWitness
      (clientOutboundPredecessor bundle) llvmArtifact of
    Left err -> Left (ExactSendProofTargetMismatch (Text.pack (show err)))
    Right () -> pure ()
  mapLeft ExactSendProofLLVMVerificationError $
    verifyLLVMEmissionWith
      lowerSystemsExactSend
      (currentExactSendLLVMVerificationContext bundle)
      (clientOutboundArtifact bundle)
      llvmArtifact

currentExactSendLLVMVerificationContext
  :: ClientOutboundBundle
  -> LLVMVerificationContext
currentExactSendLLVMVerificationContext bundle = LLVMVerificationContext
  { llvmSystemsContext = clientOutboundContext bundle
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion phase0ExactSendLLVMTarget
  , llvmExpectedToolVersion = llvmTargetToolVersion phase0ExactSendLLVMTarget
  , llvmExpectedTargetTriple = llvmTargetTripleName phase0ExactSendLLVMTarget
  , llvmExpectedDataLayout = llvmTargetDataLayout phase0ExactSendLLVMTarget
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest phase0ExactSendLLVMTarget
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile phase0ExactSendLLVMTarget
  , llvmAuthorizedStrengthenings = mempty
  }

verifyCurrentSourceExactSend
  :: ClientOutboundBundle
  -> Either ExactSendProofCertificationError RuntimeSiteRef
verifyCurrentSourceExactSend bundle = do
  let witness = clientOutboundWitness bundle
      artifact = clientOutboundArtifact bundle
      program = systemsArtifactProgram artifact
      functionName = clientOutboundFunction witness
      transport = clientOutboundTransport witness
      payload = clientOutboundPayload witness
      payloadView = clientOutboundPayloadView witness
  client <- maybe
    (Left (ExactSendProofSourceMismatch "UploadClient missing"))
    Right
    (Map.lookup functionName (systemsProgramFunctions program))
  case Map.lookup transport (systemsFunctionValues client) of
    Just SystemsValue { systemsValueRole = TransportHandle } -> pure ()
    _ -> Left (ExactSendProofSourceMismatch "client.transport is not exact TransportHandle")
  case Map.lookup payload (systemsFunctionValues client) of
    Just SystemsValue { systemsValueRole = OwnedBuffer _ } -> pure ()
    _ -> Left (ExactSendProofSourceMismatch "client.payload is not exact OwnedBuffer")
  case Map.lookup payloadView (systemsFunctionValues client) of
    Just SystemsValue { systemsValueRole = BorrowedSlice owner }
      | owner == payload -> pure ()
    _ -> Left (ExactSendProofSourceMismatch "client.payload_view is not a non-owning borrow of client.payload")

  let operations =
        [ operation
        | blockValue <- Map.elems (systemsFunctionBlocks client)
        , operation <- systemsBlockOps blockValue
        ]
      payloadBorrows =
        [ ()
        | OpBorrowView view owner _ <- operations
        , view == payloadView
        , owner == payload
        ]
      payloadCopies =
        [ ()
        | OpCopy source _ _ <- operations
        , source == payload
        ]
  unless (length payloadBorrows == 1 && null payloadCopies) $
    Left (ExactSendProofSourceMismatch "client.payload borrow/copy shape drifted")

  sourceBlock <- maybe
    (Left (ExactSendProofSourceMismatch "client.payload block missing"))
    Right
    (Map.lookup (BlockId "client.payload") (systemsFunctionBlocks client))
  let exactCalls =
        [ (site, decision)
        | OpRuntimeCall name inputs outputs (Just site) decision <- systemsBlockOps sourceBlock
        , name == "send_exact"
        , inputs == [transport, payload]
        , null outputs
        , runtimeSiteKind site == ExactSendBoundary
        ]
      recoverableExactSendTerminators =
        [ ()
        | blockValue <- Map.elems (systemsFunctionBlocks client)
        , TermSendExact sendTransport sendPayload sendSite _ _ <- [systemsBlockTerminator blockValue]
        , sendTransport == transport
        , sendPayload == payload
        , runtimeSiteKind sendSite == ExactSendBoundary
        ]
  (site, decision) <- case exactCalls of
    [one] -> Right one
    _ -> Left (ExactSendProofSourceMismatch "exact send call multiplicity/operands/site drifted")
  unless (null recoverableExactSendTerminators) $
    Left (ExactSendProofSourceMismatch "recoverable exact-send failure edge appeared")
  case Map.lookup decision (loweringLedgerDecisions (systemsArtifactLoweringLedger artifact)) of
    Just lowering
      | loweringTargetArtifactDigest lowering == systemsProgramDigest program -> pure ()
    _ -> Left (ExactSendProofSourceMismatch "exact-send lowering decision is missing or not rebound to current successor")
  pure site

verifyCurrentTargetExactSend
  :: ClientOutboundBundle
  -> RuntimeSiteRef
  -> LLVMArtifact
  -> Either ExactSendProofCertificationError ()
verifyCurrentTargetExactSend bundle site llvmArtifact = do
  let witness = clientOutboundWitness bundle
      moduleValue = llvmArtifactModule llvmArtifact
      functionName = clientOutboundFunction witness
      transport = unValueId (clientOutboundTransport witness)
      payloadTarget = unValueId (clientOutboundPayload witness) <> ".owner"
  client <- maybe
    (Left (ExactSendProofTargetMismatch "UploadClient missing"))
    Right
    (Map.lookup functionName (llvmFunctions moduleValue))
  let expectedParameters =
        [ LLVMParameter transport LLVMPointerParameter
        , LLVMParameter payloadTarget LLVMPointerParameter
        ]
  unless (llvmFunctionParameters client == expectedParameters) $
    Left (ExactSendProofTargetMismatch "UploadClient transport/payload-owner parameter mapping drifted")

  payloadBlock <- maybe
    (Left (ExactSendProofTargetMismatch "client.payload LLVM block missing"))
    Right
    (Map.lookup (LLVMBlockId "client.payload") (llvmFunctionBlocks client))
  let exactOps =
        [ operation
        | operation@(LLVMExactSend opSite opTransport opPayload) <- llvmBlockOps payloadBlock
        , opSite == site
        , opTransport == transport
        , opPayload == payloadTarget
        ]
      genericExactOps =
        [ ()
        | LLVMRuntime opSite name <- llvmBlockOps payloadBlock
        , opSite == site || name == "send_exact"
        ]
      allClientOps = concatMap llvmBlockOps (Map.elems (llvmFunctionBlocks client))
      copyOps = [() | LLVMCall "copy" <- allClientOps]
  unless (exactOps == [LLVMExactSend site transport payloadTarget]
      && null genericExactOps
      && null copyOps) $
    Left (ExactSendProofTargetMismatch "exact runtime operation or no-copy shape drifted")

  entryBlock <- maybe
    (Left (ExactSendProofTargetMismatch "client.entry LLVM block missing"))
    Right
    (Map.lookup (LLVMBlockId (unBlockId (clientOutboundEntryBlock witness)))
      (llvmFunctionBlocks client))
  versionBlock <- maybe
    (Left (ExactSendProofTargetMismatch "client.version LLVM block missing"))
    Right
    (Map.lookup (LLVMBlockId (unBlockId (clientOutboundVersionBlock witness)))
      (llvmFunctionBlocks client))
  let expectedEntryGeneric =
        [ LLVMCall (clientOutboundSupportedVersionsCall witness)
        , LLVMCall (clientOutboundConstructHelloCall witness)
        , LLVMCall (clientOutboundSendHelloCall witness)
        ]
      expectedVersionGeneric =
        [ LLVMPlain "borrowed view; no representation copy"
        , LLVMCall (clientOutboundDigestCall witness)
        , LLVMCall (clientOutboundProjectLengthCall witness)
        , LLVMCall (clientOutboundProjectKindCall witness)
        , LLVMCall (clientOutboundConstructBeginCall witness)
        , LLVMCall (clientOutboundSendBeginCall witness)
        ]
  unless (llvmBlockOps entryBlock == expectedEntryGeneric
      && llvmBlockOps versionBlock == expectedVersionGeneric) $
    Left (ExactSendProofTargetMismatch
      "client-outbound Hello/Begin semantics were unexpectedly physically selected by exact-send target")

  let rendered = llvmArtifactText llvmArtifact
  forM_
    [ "declare void @phil_runtime_send_exact(ptr, ptr)"
    , "call void @phil_runtime_send_exact(ptr %client_transport, ptr %client_payload_owner)"
    ] $ \needle ->
      unless (Text.isInfixOf needle rendered) $
        Left (ExactSendProofTargetMismatch ("missing exact-send target text: " <> needle))
  forM_
    [ "declare i1 @phil_runtime_send_exact()"
    , "@phil_call_send_exact"
    , "current_transport"
    , "current_payload"
    , "pending_send_payload"
    ] $ \needle ->
      unless (not (Text.isInfixOf needle rendered)) $
        Left (ExactSendProofTargetMismatch ("generic/ambient exact-send residue: " <> needle))

phase0ExactSendProofCertification
  :: RocqCertificationBundle
  -> RocqCertificationBundle
  -> HelloPolicyValidationProofCertificationBundle
  -> Either ExactSendProofCertificationError ExactSendProofCertificationBundle
phase0ExactSendProofCertification systemsProof llvmProof predecessor = do
  verifyProof "systems-exact-send" systemsExactSendCertificationSpec systemsProof
  verifyProof "llvm-exact-send" llvmExactSendCertificationSpec llvmProof
  systemsBundle <- mapLeft ExactSendProofClientOutboundError phase0ClientOutboundBundle
  let systemsArtifact = clientOutboundArtifact systemsBundle
      llvmArtifact = lowerSystemsExactSend phase0ExactSendLLVMTarget systemsArtifact
  verifyCurrentExactSendTranslation systemsBundle llvmArtifact

  let proofBundles = [systemsProof, llvmProof]
      proofLedgers = map rocqBundleLedger proofBundles
      semanticRevisions = Map.unions (map ledgerRevisions proofLedgers)
      semanticEvidence = Map.unions (map ledgerEvidence proofLedgers)
      semanticRevisionIds = Map.keysSet semanticRevisions
      semanticEvidenceIds = Map.keysSet semanticEvidence
      proofArtifacts = map rocqBundleCertificateArtifact proofBundles
      proofDigests = map artifactDigest proofArtifacts
      predecessorArtifact = helloPolicyProofArtifact predecessor

      systemsManifest = systemsAssuranceManifest (clientOutboundContext systemsBundle)
      moduleValue = llvmArtifactModule llvmArtifact
      sourceDigest = llvmContractSourceDigest (llvmArtifactContract llvmArtifact)
      targetDigest = llvmContractTargetDigest (llvmArtifactContract llvmArtifact)
      targetTextDigest = digestText (llvmArtifactText llvmArtifact)
      abiDigest = llvmRuntimeABIDigest moduleValue
      systemsLoweringRoot = loweringLedgerRoot (systemsArtifactLoweringLedger systemsArtifact)
      certificationTarget = "preopt-llvm:" <> llvmTargetTriple moduleValue
      sourceCompilationProfile = Text.pack (show (llvmCompilationProfile moduleValue))
      certificationProfile =
        "translation-validation/" <> sourceCompilationProfile <>
        "/transport-exact-send-v1/client-outbound-v1/proof-bound"
      validityContext = Map.fromList
        [ ("source_digest", unDigest sourceDigest)
        , ("source_successor", "client-outbound-v1")
        , ("target_digest", unDigest targetDigest)
        , ("target_text_digest", unDigest targetTextDigest)
        , ("llvm_language", llvmLanguageVersion moduleValue)
        , ("llvm_tool_profile", llvmToolVersion moduleValue)
        , ("target_triple", llvmTargetTriple moduleValue)
        , ("data_layout", llvmDataLayout moduleValue)
        , ("runtime_abi_digest", unDigest abiDigest)
        , ("runtime_abi_profile", llvmRuntimeABIProfile moduleValue)
        , ("systems_compilation_profile", sourceCompilationProfile)
        , ("systems_lowering_ledger_root", unDigest systemsLoweringRoot)
        , ("predecessor_certification", unDigest (artifactDigest predecessorArtifact))
        , ("proof_assistant", "Rocq")
        , ("rocq_version", "9.2.0")
        , ("certificate_profile", "proof-assistant-theorem/v1")
        , ("client_transport", "exact source client.transport -> explicit ptr")
        , ("client_payload_source", "client.payload : OwnedBuffer")
        , ("client_payload_target", "client.payload.owner : explicit ptr parameter")
        , ("client_payload_relation", "client.payload -> client.payload.owner")
        , ("send", "phil_runtime_send_exact(ptr,ptr)->void")
        , ("send_failure", "must not return normally; source has no recoverable failure edge")
        , ("payload_copy", "none introduced by source successor or exact-send translation")
        , ("outbound_record_lowering", "unselected outside exact-send certification scope")
        , ("external_provider_semantics", "whole-send-or-nonreturn runtime gate")
        , ("external_runtime_abi", "provider signature and execution gate")
        , ("external_llvm", "LLVM 18 acceptance/link gate")
        , ("outer_framing", "not defined by transport-exact-send-v1")
        ]
      evidenceScope = ValidityScope $
        Map.insert "target" certificationTarget $
        Map.insert "compilation_profile" certificationProfile validityContext
      revisionStatement =
        "The transport-exact-send-v1 lowering over the current client-outbound-v1 Systems successor may be labeled Certified only when exact successor source/target/text digests, Systems lowering root, target/runtime-ABI/tool identities, the proof-bound PHIL-LLVM-CERT-012 predecessor certificate, PHIL-SYS-EXACT-SEND-001 semantic authority, PHIL-LLVM-EXACT-SEND-001 lowering authority, and the exact successor translation-validation result are content-bound. The translation-only PHIL-LLVM-CERT-013 revision created before client-outbound normalization does not extend to the successor digest and is not imported as evidence. Provider whole-send-or-nonreturn semantics, opaque payload-handle implementation/lifetime, physical I/O, provider ABI conformance, LLVM implementation correctness, linking, native execution, outer framing, and physical lowering of the newly explicit outbound Hello/Begin semantic operations remain explicit external gates or out-of-scope target work."
      provisionalRevision = ObligationRevision
        { revisionObligationId = ObligationId "PHIL-LLVM-CERT-013"
        , revisionId = RevisionId ""
        , revisionStatement = revisionStatement
        , revisionStatementDigest = digestText revisionStatement
        , revisionKind = "LLVMExactSendProofBoundCertification"
        , revisionOrigin =
            "transport exact-send ABI v1 / client-outbound successor / proof-bound PHIL-LLVM-CERT-013"
        , revisionScope = "llvm.phase0.preopt.transport-exact-send.client-outbound.proof-bound"
        , revisionRequiredAt = "certification"
        , revisionRepresentation =
            "current client-outbound SystemsArtifact -> transport-exact-send-v1 canonical pre-optimization LLVMArtifact + exact-send proof authority"
        , revisionSubjectIds =
            [ "systems:" <> unDigest sourceDigest
            , "systems-lowering-root:" <> unDigest systemsLoweringRoot
            , "llvm:" <> unDigest targetDigest
            , "llvm-text:" <> unDigest targetTextDigest
            , "runtime-abi:" <> unDigest abiDigest
            , "predecessor-certification:" <> unDigest (artifactDigest predecessorArtifact)
            ] <> map ("proof-certificate:" <>) (map unDigest proofDigests)
        , revisionContextIds =
            [ "language:" <> llvmLanguageVersion moduleValue
            , "tool-profile:" <> llvmToolVersion moduleValue
            , "target:" <> llvmTargetTriple moduleValue
            , "layout:" <> llvmDataLayout moduleValue
            , "runtime-abi-profile:" <> llvmRuntimeABIProfile moduleValue
            , "compilation-profile:" <> sourceCompilationProfile
            , "source-successor:client-outbound-v1"
            , "rocq:9.2.0"
            ]
        , revisionAcceptanceRule = AcceptEntry TranslationValidated (EvidenceRole "translation_validated")
        , revisionGeneratedFrom = Set.toAscList semanticRevisionIds
        }
      certificationRevision = provisionalRevision
        { revisionId = deriveRevisionId provisionalRevision }
      certificationRevisionId = revisionId certificationRevision
      translationArtifactRecord = Text.unlines
        [ "phil-llvm-phase0-transport-exact-send-translation-validation/v2"
        , "source-successor=client-outbound-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "llvm-language=" <> llvmLanguageVersion moduleValue
        , "llvm-tool-profile=" <> llvmToolVersion moduleValue
        , "target-triple=" <> llvmTargetTriple moduleValue
        , "data-layout=" <> llvmDataLayout moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "translation-validator=Phil.LLVM.ExactSendProofCertification.verifyCurrentExactSendTranslation"
        , "assurance-checker=Phil.Assurance.Verify.verifyManifest"
        ]
      translationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef
            "artifact:phil:llvm:phase0:transport-exact-send:translation-validation:v2"
        , artifactDigest = digestText translationArtifactRecord
        }
      translationEvidenceId = EvidenceEntryId
        "evidence.llvm.phase0.transport-exact-send.client-outbound.proof-bound.translation.validated"
      provisionalEvidence = EvidenceEntry
        { evidenceEntryId = translationEvidenceId
        , evidenceEntryDigest = Digest ""
        , evidenceObligationRevision = certificationRevisionId
        , evidenceAssuranceKind = TranslationValidated
        , evidenceRole = EvidenceRole "translation_validated"
        , evidenceProducer =
            "Phil.LLVM.ExactSendProofCertification.verifyCurrentExactSendTranslation"
        , evidenceChecker = "Phil.Assurance.Verify.verifyManifest"
        , evidenceArtifact = Just translationArtifact
        , evidenceInputDigests =
            [ sourceDigest
            , systemsLoweringRoot
            , targetDigest
            , targetTextDigest
            , abiDigest
            , artifactDigest predecessorArtifact
            ] <> proofDigests
        , evidenceAssumptions = []
        , evidenceDependsOn = map DependsOnObligation (Set.toAscList semanticRevisionIds)
        , evidenceValidityScope = evidenceScope
        , evidenceResult = EvidenceAccepted
        , evidenceJustifies =
            [ "current client-outbound successor retains exact client.transport and original client.payload owner"
            , "the payload digest borrow is non-owning and neither source successor nor exact-send lowering introduces a payload copy"
            , "source client.payload maps exactly to one target parameter client.payload.owner"
            , "the exact ExactSendBoundary is retained"
            , "exactly one phil_runtime_send_exact(ptr,ptr) receives exact transport and mapped payload identities"
            , "no recoverable exact-send failure edge is invented"
            , "proof-bound HelloPolicy predecessor target authority is preserved"
            , "generic exact-send and ambient transport/payload state are absent"
            , "new outbound Hello/Begin semantic operations remain generic and outside this physical certification scope"
            ]
        , evidenceRuntimeMechanism = Nothing
        , evidenceRuntimeResidue = []
        , evidenceCostRefs = []
        }
      translationEvidence = provisionalEvidence
        { evidenceEntryDigest = deriveEvidenceEntryDigest provisionalEvidence }
      certificationRecord = Text.unlines $
        [ "phil-llvm-phase0-transport-exact-send-certification/v2"
        , "obligation=PHIL-LLVM-CERT-013"
        , "revision=" <> unRevisionId certificationRevisionId
        , "source-successor=client-outbound-v1"
        , "source-digest=" <> unDigest sourceDigest
        , "systems-lowering-root=" <> unDigest systemsLoweringRoot
        , "target-digest=" <> unDigest targetDigest
        , "target-text-digest=" <> unDigest targetTextDigest
        , "runtime-abi-profile=" <> llvmRuntimeABIProfile moduleValue
        , "runtime-abi-digest=" <> unDigest abiDigest
        , "translation-artifact=" <> renderArtifact translationArtifact
        , "predecessor-certification=" <> renderArtifact predecessorArtifact
        ] <> map renderProofArtifact proofBundles <>
        [ "historical-translation-only-cert013=pre-client-outbound source digest; not imported"
        , "outbound-record-lowering=unselected outside exact-send certification scope"
        , "external-provider-semantics=whole-send-or-nonreturn gate"
        , "external-runtime-abi=provider signature and execution gate"
        , "external-llvm=LLVM 18 acceptance/link gate"
        , "external-native=native execution gate"
        , "residual-outer-framing=not defined by transport-exact-send-v1"
        ]
      certificationArtifact = ArtifactIdentity
        { artifactReference = ArtifactRef "certificate:phil:llvm:PHIL-LLVM-CERT-013:v1"
        , artifactDigest = digestText certificationRecord
        }
      revisions = Map.insert certificationRevisionId certificationRevision semanticRevisions
      evidence = Map.insert translationEvidenceId translationEvidence semanticEvidence
      obligationIds = Set.insert certificationRevisionId semanticRevisionIds
      evidenceIds = Set.insert translationEvidenceId semanticEvidenceIds
      ledger = emptyLedger
        { ledgerRevisions = revisions
        , ledgerEvidence = evidence
        }
      certificationRoot = digestText $ Text.intercalate "|" $
        [ "phil-llvm-phase0-transport-exact-send-client-outbound-proof-bound-certification-root-v1"
        , unDigest sourceDigest
        , unDigest systemsLoweringRoot
        , unDigest targetDigest
        , unDigest targetTextDigest
        , unDigest abiDigest
        , unDigest (artifactDigest predecessorArtifact)
        ] <> map unDigest proofDigests
      provisionalManifest = emptyManifest
        { manifestArchitectureDigest = manifestArchitectureDigest systemsManifest
        , manifestPhilCoreDigest = manifestPhilCoreDigest systemsManifest
        , manifestImplementationDigest = artifactDigest certificationArtifact
        , manifestTarget = certificationTarget
        , manifestCompilationProfile = certificationProfile
        , manifestObligationRevisions = obligationIds
        , manifestCertificationScope = obligationIds
        , manifestEvidenceEntries = evidenceIds
        , manifestLoweringLedgerRoot = certificationRoot
        , manifestValidityContext = validityContext
        }
      manifest = provisionalManifest
        { manifestId = deriveManifestId ledger provisionalManifest }
      explicitArtifacts = translationArtifact : certificationArtifact : predecessorArtifact : proofArtifacts
      availableArtifacts = Map.fromList
        [ (artifactReference artifact, artifactDigest artifact)
        | artifact <- explicitArtifacts
        ]
      context = emptyVerificationContext
        { verificationArchitectureDigest = manifestArchitectureDigest systemsManifest
        , verificationPhilCoreDigest = manifestPhilCoreDigest systemsManifest
        , verificationImplementationDigest = artifactDigest certificationArtifact
        , verificationTarget = certificationTarget
        , verificationCompilationProfile = certificationProfile
        , verificationExpectedObligations = obligationIds
        , verificationAvailableArtifacts = availableArtifacts
        , verificationLoweringLedgerRoot = certificationRoot
        , verificationValidityContext = validityContext
        }
      result = ExactSendProofCertificationBundle
        { exactSendProofSystems = systemsBundle
        , exactSendProofLLVM = llvmArtifact
        , exactSendProofPredecessor = predecessor
        , exactSendProofArtifact = certificationArtifact
        , exactSendProofRecord = certificationRecord
        , exactSendProofLedger = ledger
        , exactSendProofManifest = manifest
        , exactSendProofContext = context
        }

  mapLeft ExactSendProofFinalManifestError $ verifyManifest context ledger manifest
  pure result

verifyPhase0ExactSendProofCertification
  :: RocqCertificationBundle
  -> RocqCertificationBundle
  -> HelloPolicyValidationProofCertificationBundle
  -> Either ExactSendProofCertificationError ()
verifyPhase0ExactSendProofCertification systemsProof llvmProof predecessor = do
  bundle <- phase0ExactSendProofCertification systemsProof llvmProof predecessor
  mapLeft ExactSendProofFinalManifestError $
    verifyManifest
      (exactSendProofContext bundle)
      (exactSendProofLedger bundle)
      (exactSendProofManifest bundle)

renderExactSendProofCertification :: ExactSendProofCertificationBundle -> Text
renderExactSendProofCertification = exactSendProofRecord

verifyProof
  :: Text
  -> RocqCertificationSpec
  -> RocqCertificationBundle
  -> Either ExactSendProofCertificationError ()
verifyProof label spec bundle = do
  let expected = rocqSpecObligation spec
      actual = rocqCertificateObligation (rocqBundleCertificate bundle)
  unless (actual == expected) $
    Left (ExactSendProofWrongProof label expected actual)
  mapLeft (ExactSendProofManifestError label) $
    verifyManifest
      (rocqBundleVerificationContext bundle)
      (rocqBundleLedger bundle)
      (rocqBundleManifest bundle)

renderArtifact :: ArtifactIdentity -> Text
renderArtifact artifact =
  unArtifactRef (artifactReference artifact) <> ";sha256=" <> unDigest (artifactDigest artifact)

renderProofArtifact :: RocqCertificationBundle -> Text
renderProofArtifact bundle =
  let certificate = rocqBundleCertificate bundle
      artifact = rocqBundleCertificateArtifact bundle
  in "proof=" <> unObligationId (rocqCertificateObligation certificate)
      <> ";artifact=" <> unArtifactRef (artifactReference artifact)
      <> ";sha256=" <> unDigest (artifactDigest artifact)

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
