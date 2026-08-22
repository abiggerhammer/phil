{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance
import Phil.LLVM
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "Phase 0 conservative LLVM emission verifies" referencePasses
    , test "runtime validator results directly guard LLVM branches" runtimeResultGuardsBranch
    , test "declared LLVM entry block is emitted first" entryBlockEmittedFirst
    , test "LLVM artifact text is content-bound" textTamperRejects
    , test "systems source identity is content-bound" sourceDigestRejects
    , test "target triple cannot drift without a new target profile" targetTripleRejects
    , test "runtime-bound checks cannot disappear before LLVM" missingRuntimeRejects
    , test "unwitnessed LLVM control edges reject" unwitnessedEdgeRejects
    , test "nuw cannot be emitted without explicit strengthening authority" unauthorizedNoWrapRejects
    , test "evidence-backed inbounds strengthening is accepted" authorizedInBoundsPasses
    , test "llvm.assume cannot replace a runtime-bound validator" assumeReplacementRejects
    , test "modeled failure cannot become unjustified unreachable" unjustifiedUnreachableRejects
    , test "accidental poison is rejected" poisonRejects
    , test "contract trace relation is preserved" traceRelationRejects
    ]
  if and results then pure () else exitFailure

referencePasses :: Bool
referencePasses =
  verifyLLVMEmission phase0LLVMVerificationContext phase0SystemsArtifact phase0LLVMArtifact == Right ()

runtimeResultGuardsBranch :: Bool
runtimeResultGuardsBranch =
  let rendered = llvmArtifactText phase0LLVMArtifact
  in Text.isInfixOf "%phil_runtime_cond_server_digest = call i1" rendered
      && Text.isInfixOf "br i1 %phil_runtime_cond_server_digest" rendered

entryBlockEmittedFirst :: Bool
entryBlockEmittedFirst =
  Text.isInfixOf "define i32 @UploadServer() {\nserver_entry:" (llvmArtifactText phase0LLVMArtifact)

textTamperRejects :: Bool
textTamperRejects =
  let bad = phase0LLVMArtifact { llvmArtifactText = llvmArtifactText phase0LLVMArtifact <> "\n; tampered" }
  in case verifyLLVMEmission phase0LLVMVerificationContext phase0SystemsArtifact bad of
      Left LLVMArtifactTextMismatch -> True
      _ -> False

sourceDigestRejects :: Bool
sourceDigestRejects =
  let contract = llvmArtifactContract phase0LLVMArtifact
      bad = phase0LLVMArtifact
        { llvmArtifactContract = contract { llvmContractSourceDigest = digestText "wrong systems artifact" } }
  in case verifyLLVMEmission phase0LLVMVerificationContext phase0SystemsArtifact bad of
      Left LLVMSourceDigestMismatch {} -> True
      _ -> False

targetTripleRejects :: Bool
targetTripleRejects =
  let moduleValue = llvmArtifactModule phase0LLVMArtifact
      changed = phase0LLVMArtifact
        { llvmArtifactModule = moduleValue { llvmTargetTriple = "aarch64-unknown-linux-gnu" } }
      bad = rebindLLVMArtifact changed
  in case verifyLLVMEmission phase0LLVMVerificationContext phase0SystemsArtifact bad of
      Left LLVMTargetTripleMismatch {} -> True
      _ -> False

missingRuntimeRejects :: Bool
missingRuntimeRejects =
  let bad = rebindLLVMArtifact $
        adjustLLVMBlock "UploadServer" "server.digest" dropRuntimeBranch phase0LLVMArtifact
  in case verifyLLVMEmission phase0LLVMVerificationContext phase0SystemsArtifact bad of
      Left LLVMRuntimeCoverageMismatch {} -> True
      _ -> False

unwitnessedEdgeRejects :: Bool
unwitnessedEdgeRejects =
  let bad = rebindLLVMArtifact $
        adjustLLVMBlock "UploadServer" "server.digest_mismatch"
          (\blockValue -> blockValue
            { llvmBlockTerminator = LLVMJump (LLVMBlockId "server.accepted") })
          phase0LLVMArtifact
  in case verifyLLVMEmission phase0LLVMVerificationContext phase0SystemsArtifact bad of
      Left LLVMUnwitnessedTargetEdge {} -> True
      _ -> False

unauthorizedNoWrapRejects :: Bool
unauthorizedNoWrapRejects =
  let (_, strengthening) = strengtheningFixture LLVMNoUnsignedWrap "llvm.upload.payload_length.no_unsigned_wrap"
      bad = rebindLLVMArtifact (addStrengthening strengthening phase0LLVMArtifact)
  in case verifyLLVMEmission phase0LLVMVerificationContext phase0SystemsArtifact bad of
      Left LLVMUnauthorizedStrengthening {} -> True
      _ -> False

authorizedInBoundsPasses :: Bool
authorizedInBoundsPasses =
  let (authority, strengthening) = strengtheningFixture LLVMInBounds "llvm.upload.frame_gep.inbounds"
      artifact = rebindLLVMArtifact (addStrengthening strengthening phase0LLVMArtifact)
      context = phase0LLVMVerificationContext
        { llvmAuthorizedStrengthenings = Map.singleton
            (llvmStrengtheningClaim strengthening)
            (Set.singleton authority)
        }
  in verifyLLVMEmission context phase0SystemsArtifact artifact == Right ()

assumeReplacementRejects :: Bool
assumeReplacementRejects =
  let site = phase0RuntimeBranchSite "UploadServer" "server.begin.commit"
      authority = LLVMObligation (runtimeSiteRevision site)
      strengthening = LLVMStrengthening
        { llvmStrengtheningId = LLVMStrengtheningId "test.assume.begin_policy"
        , llvmStrengtheningKind = LLVMAssume
        , llvmStrengtheningClaim = "llvm.upload.begin_policy.established"
        , llvmStrengtheningAuthority = authority
        , llvmStrengtheningFunction = "UploadServer"
        , llvmStrengtheningBlock = LLVMBlockId "server.begin.commit"
        }
      withoutRuntime = adjustLLVMBlock "UploadServer" "server.begin.commit"
        dropRuntimeBranch phase0LLVMArtifact
      artifact = rebindLLVMArtifact (addStrengthening strengthening withoutRuntime)
      context = phase0LLVMVerificationContext
        { llvmAuthorizedStrengthenings = Map.singleton
            (llvmStrengtheningClaim strengthening)
            (Set.singleton authority)
        }
  in case verifyLLVMEmission context phase0SystemsArtifact artifact of
      Left LLVMRuntimeCoverageMismatch {} -> True
      _ -> False

unjustifiedUnreachableRejects :: Bool
unjustifiedUnreachableRejects =
  let bad = rebindLLVMArtifact $
        adjustLLVMBlock "UploadServer" "server.early_eof"
          (\blockValue -> blockValue { llvmBlockTerminator = LLVMUnreachable Nothing })
          phase0LLVMArtifact
  in case verifyLLVMEmission phase0LLVMVerificationContext phase0SystemsArtifact bad of
      Left LLVMUnjustifiedUnreachable {} -> True
      _ -> False

poisonRejects :: Bool
poisonRejects =
  let bad = rebindLLVMArtifact $
        adjustLLVMBlock "UploadClient" "client.entry"
          (\blockValue -> blockValue { llvmBlockOps = LLVMPoison "branch-input" : llvmBlockOps blockValue })
          phase0LLVMArtifact
  in case verifyLLVMEmission phase0LLVMVerificationContext phase0SystemsArtifact bad of
      Left LLVMAccidentalPoison {} -> True
      _ -> False

traceRelationRejects :: Bool
traceRelationRejects =
  let contract = llvmArtifactContract phase0LLVMArtifact
      bad = phase0LLVMArtifact
        { llvmArtifactContract = contract { llvmContractTraceRelation = ["invented trace relation"] } }
  in case verifyLLVMEmission phase0LLVMVerificationContext phase0SystemsArtifact bad of
      Left LLVMTraceRelationMismatch -> True
      _ -> False

strengtheningFixture :: LLVMStrengtheningKind -> Text -> (LLVMAuthority, LLVMStrengthening)
strengtheningFixture kind claim = (authority, strengthening)
  where
    invariantId = case Map.keys (stageInvariants (systemsArtifactStageContract phase0SystemsArtifact)) of
      firstId : _ -> firstId
      [] -> InvariantId "missing-invariant"
    authority = LLVMInvariant invariantId
    strengthening = LLVMStrengthening
      { llvmStrengtheningId = LLVMStrengtheningId ("test." <> Text.replace "." "_" claim)
      , llvmStrengtheningKind = kind
      , llvmStrengtheningClaim = claim
      , llvmStrengtheningAuthority = authority
      , llvmStrengtheningFunction = "UploadServer"
      , llvmStrengtheningBlock = LLVMBlockId "server.entry"
      }

addStrengthening :: LLVMStrengthening -> LLVMArtifact -> LLVMArtifact
addStrengthening strengthening artifact = artifact
  { llvmArtifactModule = moduleValue
      { llvmStrengthenings = Map.insert
          (llvmStrengtheningId strengthening)
          strengthening
          (llvmStrengthenings moduleValue)
      }
  }
  where
    moduleValue = llvmArtifactModule $
      adjustLLVMBlock
        (llvmStrengtheningFunction strengthening)
        (unLLVMBlockId (llvmStrengtheningBlock strengthening))
        (\blockValue -> blockValue
          { llvmBlockOps = LLVMStrengtheningOp
              (llvmStrengtheningId strengthening)
              (llvmStrengtheningClaim strengthening)
              : llvmBlockOps blockValue
          })
        artifact

phase0RuntimeBranchSite :: Text -> Text -> RuntimeSiteRef
phase0RuntimeBranchSite functionName blockName =
  case lookupLLVMBlock functionName blockName phase0LLVMArtifact of
    Just blockValue -> case llvmBlockTerminator blockValue of
      LLVMRuntimeBranch site _ _ _ -> site
      _ -> error "expected Phase 0 LLVM runtime branch"
    Nothing -> error "missing Phase 0 LLVM block"

dropRuntimeBranch :: LLVMBlock -> LLVMBlock
dropRuntimeBranch blockValue = case llvmBlockTerminator blockValue of
  LLVMRuntimeBranch _ _ yes no -> blockValue { llvmBlockTerminator = LLVMBranch yes no }
  _ -> blockValue

lookupLLVMBlock :: Text -> Text -> LLVMArtifact -> Maybe LLVMBlock
lookupLLVMBlock functionName blockName artifact = do
  functionValue <- Map.lookup functionName (llvmFunctions (llvmArtifactModule artifact))
  Map.lookup (LLVMBlockId blockName) (llvmFunctionBlocks functionValue)

rebindLLVMArtifact :: LLVMArtifact -> LLVMArtifact
rebindLLVMArtifact artifact = artifact
  { llvmArtifactText = renderLLVMModule moduleValue
  , llvmArtifactContract = contract { llvmContractTargetDigest = llvmModuleDigest moduleValue }
  }
  where
    moduleValue = llvmArtifactModule artifact
    contract = llvmArtifactContract artifact

adjustLLVMBlock
  :: Text
  -> Text
  -> (LLVMBlock -> LLVMBlock)
  -> LLVMArtifact
  -> LLVMArtifact
adjustLLVMBlock functionName blockName modify artifact = artifact
  { llvmArtifactModule = moduleValue
      { llvmFunctions = Map.adjust adjustFunction functionName (llvmFunctions moduleValue) }
  }
  where
    moduleValue = llvmArtifactModule artifact
    blockId = LLVMBlockId blockName
    adjustFunction functionValue = functionValue
      { llvmFunctionBlocks = Map.adjust modify blockId (llvmFunctionBlocks functionValue) }

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
