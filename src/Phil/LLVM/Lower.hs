{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.Lower
  ( lowerSystemsConservative
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.LLVM.IR
import Phil.Systems.IR

lowerSystemsConservative :: LLVMTargetProfile -> SystemsArtifact -> LLVMArtifact
lowerSystemsConservative target systemsArtifact = artifact
  where
    program = systemsArtifactProgram systemsArtifact
    sourceContract = systemsArtifactStageContract systemsArtifact
    moduleValue = LLVMModule
      { llvmModuleName = systemsProgramName program <> "-preopt"
      , llvmLanguageVersion = llvmTargetLanguageVersion target
      , llvmToolVersion = llvmTargetToolVersion target
      , llvmTargetTriple = llvmTargetTripleName target
      , llvmDataLayout = llvmTargetDataLayout target
      , llvmRuntimeABIDigest = llvmTargetRuntimeABIDigest target
      , llvmRuntimeABIProfile = llvmTargetRuntimeABIProfile target
      , llvmCompilationProfile = systemsProgramProfile program
      , llvmFunctions = Map.fromList
          [ (functionKey, lowerFunction functionValue)
          | (functionKey, functionValue) <- Map.toAscList (systemsProgramFunctions program)
          ]
      , llvmStrengthenings = Map.empty
      }
    contract = LLVMEmissionContract
      { llvmContractSourceDigest = systemsArtifactDigest systemsArtifact
      , llvmContractTargetDigest = llvmModuleDigest moduleValue
      , llvmContractEdgeWitnesses = allEdgeWitnesses program
      , llvmContractTraceRelation = stageTraceRelation sourceContract
      , llvmContractResourceFailureRelation = stageResourceFailureRelation sourceContract
      }
    artifact = LLVMArtifact
      { llvmArtifactModule = moduleValue
      , llvmArtifactText = renderLLVMModule moduleValue
      , llvmArtifactContract = contract
      }

lowerFunction :: SystemsFunction -> LLVMFunction
lowerFunction functionValue = LLVMFunction
  { llvmFunctionName = systemsFunctionName functionValue
  , llvmFunctionEntry = lowerBlockId (systemsFunctionEntry functionValue)
  , llvmFunctionBlocks = Map.fromList
      [ (lowerBlockId blockKey, lowerBlock blockValue)
      | (blockKey, blockValue) <- Map.toAscList (systemsFunctionBlocks functionValue)
      ]
  }

lowerBlock :: SystemsBlock -> LLVMBlock
lowerBlock blockValue = LLVMBlock
  { llvmBlockId = lowerBlockId (systemsBlockId blockValue)
  , llvmBlockOps = concatMap lowerOp (systemsBlockOps blockValue) <> terminatorOps
  , llvmBlockTerminator = loweredTerminator
  }
  where
    (terminatorOps, loweredTerminator) = lowerTerminator (systemsBlockTerminator blockValue)

lowerOp :: SystemsOp -> [LLVMOp]
lowerOp operation = case operation of
  OpReceiveFrame { receiveGrammar = grammar } ->
    [LLVMCall ("receive_frame." <> grammar)]
  OpBorrowView {} -> [LLVMPlain "borrowed view; no representation copy"]
  OpCommitIngress {} -> [LLVMPlain "commit recognized ingress into CFG typestate"]
  OpDestroyPending {} -> [LLVMCleanup "destroy pending ingress/frame"]
  OpReleaseOwner {} -> [LLVMCleanup "release owner"]
  OpCleanupPartial {} -> [LLVMCleanup "cleanup partial owner"]
  OpRuntimeCall { runtimeCallName = name, runtimeCallSite = maybeSite } ->
    case maybeSite of
      Nothing -> [LLVMCall name]
      Just site -> [LLVMRuntime site name]
  OpCopy {} -> [LLVMCall "copy"]
  OpEraseFact {} -> [LLVMMetadata "proof/typestate fact erased before LLVM"]
  OpDiagnostic { diagnosticName = name } -> [LLVMMetadata ("diagnostic " <> name)]
  OpTraceEvent name -> [LLVMMetadata ("trace " <> name)]

lowerTerminator :: SystemsTerminator -> ([LLVMOp], LLVMTerminator)
lowerTerminator terminator = case terminator of
  TermJump target -> ([], LLVMJump (lowerBlockId target))
  TermBranch _ yes no -> ([], LLVMBranch (lowerBlockId yes) (lowerBlockId no))
  TermRecognize { recognizeSite = site, recognizeSuccess = yes, recognizeFailure = no } ->
    ([LLVMRuntime site (siteName site)], LLVMBranch (lowerBlockId yes) (lowerBlockId no))
  TermRuntimeCheck { checkSite = site, checkSuccess = yes, checkFailure = no } ->
    ([LLVMRuntime site (siteName site)], LLVMBranch (lowerBlockId yes) (lowerBlockId no))
  TermReceiveExact { exactSite = site, exactSuccess = yes, exactFailure = no } ->
    ([LLVMRuntime site (siteName site)], LLVMBranch (lowerBlockId yes) (lowerBlockId no))
  TermSendExact { sendExactSite = site, sendExactSuccess = yes, sendExactFailure = no } ->
    ([LLVMRuntime site (siteName site)], LLVMBranch (lowerBlockId yes) (lowerBlockId no))
  TermStore { storeSite = site, storeSuccess = yes, storeFailure = no } ->
    ([LLVMRuntime site (siteName site)], LLVMBranch (lowerBlockId yes) (lowerBlockId no))
  TermEnd outcome -> ([], LLVMReturn outcome)
  TermFatal failure -> ([], LLVMReturn ("fatal:" <> failure))

siteName :: RuntimeSiteRef -> Text
siteName site = Text.pack (show (runtimeSiteKind site))

allEdgeWitnesses :: SystemsProgram -> [LLVMEdgeWitness]
allEdgeWitnesses program =
  [ LLVMEdgeWitness
      { llvmEdgeSourceFunction = systemsFunctionName functionValue
      , llvmEdgeSourceFrom = systemsBlockId blockValue
      , llvmEdgeSourceTo = target
      , llvmEdgeTargetFunction = systemsFunctionName functionValue
      , llvmEdgeTargetPath = [lowerBlockId (systemsBlockId blockValue), lowerBlockId target]
      }
  | functionValue <- Map.elems (systemsProgramFunctions program)
  , blockValue <- Map.elems (systemsFunctionBlocks functionValue)
  , target <- blockSuccessors blockValue
  ]

lowerBlockId :: BlockId -> LLVMBlockId
lowerBlockId = LLVMBlockId . unBlockId
