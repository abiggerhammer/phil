{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Scalar (ScalarLiteral (..), ScalarType (..))
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsStorage)
import Phil.LLVM.Storage
  ( phase0StorageLLVMTarget
  , phase0StorageLLVMVerificationContext
  )
import Phil.LLVM.Verify
  ( LLVMVerificationError (..)
  , verifyLLVMEmissionWith
  )
import Phil.Systems.IR (SystemsArtifact)
import Phil.Systems.Storage
  ( StorageBundle (..)
  , phase0StorageBundle
  )
import System.Exit (exitFailure)

type Lowerer = LLVMTargetProfile -> SystemsArtifact -> LLVMArtifact

main :: IO ()
main = do
  results <- sequence
    [ testCase "R3 unchanged closed-world function coverage passes" unchangedPasses
    , testCase "R3 unadvertised extra target function rejects" unadvertisedExtraRejects
    , testCase "R3 selected lowerer may explicitly admit helper function" admittedExtraPasses
    , testCase "R3 disconnected return block rejects with fresh digest" extraReturnBlockRejects
    , testCase "R3 disconnected ordinary-call block rejects with fresh digest" extraCallBlockRejects
    , testCase "R3 selected scalar helper is a valid U32 positive control" scalarHelperPasses
    , testCase "R3 earlier disconnected U64 return cannot change the U32 interface" (extraScalarBlockRejects earlyExtraBlockId 64)
    , testCase "R3 later disconnected U64 return rejects even without interface drift" (extraScalarBlockRejects lateExtraBlockId 64)
    , testCase "R3 same-width disconnected return also rejects" (extraScalarBlockRejects earlyExtraBlockId 32)
    , testCase "R3 selected lowerer may explicitly admit disconnected helper blocks" admittedBlocksPass
    , testCase "R3 missing reference-admitted disconnected block rejects" missingBlockRejects
    , testCase "R3 equal-sized but renamed block inventory rejects" renamedBlockRejects
    , testCase "R3 helper entry must match the selected lowerer" helperEntryDriftRejects
    , testCase "R3 changed return width in an expected block rejects" returnWidthDriftRejects
    ]
  if and results then pure () else exitFailure

unchangedPasses :: Bool
unchangedPasses = withFixture $ \bundle systemsArtifact llvmArtifact ->
  verifyWith lowerSystemsStorage bundle systemsArtifact llvmArtifact == Right ()

unadvertisedExtraRejects :: Bool
unadvertisedExtraRejects = withFixture $ \bundle systemsArtifact llvmArtifact ->
  let badArtifact = addExplicitHelper llvmArtifact
  in case verifyWith lowerSystemsStorage bundle systemsArtifact badArtifact of
    Left (LLVMFunctionSetMismatch expected actual) ->
      helperFunctionName `notElem` expected
        && helperFunctionName `elem` actual
    _ -> False

admittedExtraPasses :: Bool
admittedExtraPasses = selectedLowererPasses lowerSystemsStorageWithHelper

extraReturnBlockRejects :: Bool
extraReturnBlockRejects = extraSourceBlockRejects extraReturnBlock

extraCallBlockRejects :: Bool
extraCallBlockRejects = extraSourceBlockRejects extraReturnBlock
  { llvmBlockOps = [LLVMCall "review_r3_disconnected_call"] }

-- These blocks add no edge or runtime site. Their only authority would be the
-- candidate's own rebound digest, which must not establish correspondence.
extraSourceBlockRejects :: LLVMBlock -> Bool
extraSourceBlockRejects extraBlock = withFixture $ \bundle systemsArtifact artifact ->
  case Map.lookupMin (llvmFunctions (llvmArtifactModule artifact)) of
    Nothing -> False
    Just (functionName, functionValue) ->
      let badArtifact = changeFunction functionName
            (insertBlock extraBlock) artifact
      in Map.notMember (llvmBlockId extraBlock) (llvmFunctionBlocks functionValue)
          && unchangedBoundaryInventory artifact badArtifact
          && blockMismatchRejects lowerSystemsStorage bundle systemsArtifact
            functionName artifact badArtifact

scalarHelperPasses :: Bool
scalarHelperPasses = withSelected lowerSystemsStorageWithScalarHelper $
  \bundle systemsArtifact artifact ->
    Text.isInfixOf scalarHelperI32Header (llvmArtifactText artifact)
      && verifyWith lowerSystemsStorageWithScalarHelper bundle systemsArtifact artifact
        == Right ()

extraScalarBlockRejects :: LLVMBlockId -> Int -> Bool
extraScalarBlockRejects extraId width = withSelected lowerSystemsStorageWithScalarHelper $
  \bundle systemsArtifact artifact ->
    let extraBlock = scalarBlock extraId "review.r3.extra.value" width
        badArtifact = changeFunction helperFunctionName (insertBlock extraBlock) artifact
        expectedHeader
          | extraId < helperEntry && width == 64 = scalarHelperI64Header
          | otherwise = scalarHelperI32Header
    in Text.isInfixOf scalarHelperI32Header (llvmArtifactText artifact)
        && Text.isInfixOf expectedHeader (llvmArtifactText badArtifact)
        && unchangedBoundaryInventory artifact badArtifact
        && blockMismatchRejects lowerSystemsStorageWithScalarHelper bundle systemsArtifact
          helperFunctionName artifact badArtifact

admittedBlocksPass :: Bool
admittedBlocksPass = selectedLowererPasses lowerSystemsStorageWithHelperBlocks

missingBlockRejects :: Bool
missingBlockRejects = withSelected lowerSystemsStorageWithHelperBlocks $
  \bundle systemsArtifact artifact ->
    let badArtifact = changeFunction helperFunctionName
          (\functionValue -> functionValue
            { llvmFunctionBlocks = Map.delete earlyExtraBlockId (llvmFunctionBlocks functionValue) })
          artifact
    in unchangedBoundaryInventory artifact badArtifact
        && blockMismatchRejects lowerSystemsStorageWithHelperBlocks bundle systemsArtifact
          helperFunctionName artifact badArtifact

renamedBlockRejects :: Bool
renamedBlockRejects = withSelected lowerSystemsStorageWithHelperBlocks $
  \bundle systemsArtifact artifact ->
    let badArtifact = changeFunction helperFunctionName
          (\functionValue -> functionValue
            { llvmFunctionBlocks = Map.insert lateExtraBlockId
                (extraReturnBlock { llvmBlockId = lateExtraBlockId })
                (Map.delete earlyExtraBlockId (llvmFunctionBlocks functionValue)) })
          artifact
        blockCount candidate = Map.size . llvmFunctionBlocks <$>
          Map.lookup helperFunctionName (llvmFunctions (llvmArtifactModule candidate))
    in blockCount artifact == blockCount badArtifact
        && unchangedBoundaryInventory artifact badArtifact
        && blockMismatchRejects lowerSystemsStorageWithHelperBlocks bundle systemsArtifact
          helperFunctionName artifact badArtifact

helperEntryDriftRejects :: Bool
helperEntryDriftRejects = withSelected lowerSystemsStorageWithHelperBlocks $
  \bundle systemsArtifact artifact ->
    let badArtifact = changeFunction helperFunctionName
          (\functionValue -> functionValue { llvmFunctionEntry = earlyExtraBlockId }) artifact
    in freshIdentity badArtifact
        && case verifyWith lowerSystemsStorageWithHelperBlocks bundle systemsArtifact badArtifact of
          Left (LLVMFunctionEntryMismatch functionName expected actual) ->
            functionName == helperFunctionName
              && expected == helperEntry && actual == earlyExtraBlockId
          _ -> False

returnWidthDriftRejects :: Bool
returnWidthDriftRejects = withSelected lowerSystemsStorageWithScalarHelper $
  \bundle systemsArtifact artifact ->
    let expectedTerminator = LLVMReturnScalar helperScalarName (ScalarUInt 32)
        actualTerminator = LLVMReturnScalar helperScalarName (ScalarUInt 64)
        badArtifact = changeFunction helperFunctionName
          (\functionValue -> functionValue
            { llvmFunctionBlocks = Map.adjust
                (\blockValue -> blockValue { llvmBlockTerminator = actualTerminator })
                helperEntry (llvmFunctionBlocks functionValue) }) artifact
    in freshIdentity badArtifact
        && case verifyWith lowerSystemsStorageWithScalarHelper bundle systemsArtifact badArtifact of
          Left (LLVMOrdinaryTerminatorMismatch functionName blockId expected actual) ->
            functionName == helperFunctionName && blockId == helperEntry
              && expected == expectedTerminator && actual == actualTerminator
          _ -> False

blockMismatchRejects
  :: Lowerer -> StorageBundle -> SystemsArtifact -> Text
  -> LLVMArtifact -> LLVMArtifact -> Bool
blockMismatchRejects lowerer bundle systemsArtifact functionName expectedArtifact actualArtifact =
  case ( Map.lookup functionName (llvmFunctions (llvmArtifactModule expectedArtifact))
       , Map.lookup functionName (llvmFunctions (llvmArtifactModule actualArtifact))
       ) of
    (Just expectedFunction, Just actualFunction) ->
      let expectedIds = Map.keys (llvmFunctionBlocks expectedFunction)
          actualIds = Map.keys (llvmFunctionBlocks actualFunction)
      in freshIdentity actualArtifact
          && expectedIds /= actualIds
          && case verifyWith lowerer bundle systemsArtifact actualArtifact of
            Left (LLVMBlockSetMismatch rejectedFunction expected actual) ->
              rejectedFunction == functionName && expected == expectedIds && actual == actualIds
            _ -> False
    _ -> False

-- Preserve the inventories that previously let disconnected blocks slip
-- through; no test is satisfied by a stale rendering or a stale target digest.
unchangedBoundaryInventory :: LLVMArtifact -> LLVMArtifact -> Bool
unchangedBoundaryInventory expected actual =
  let expectedModule = llvmArtifactModule expected
      actualModule = llvmArtifactModule actual
      edges moduleValue =
        [ (functionName, blockId, target)
        | (functionName, functionValue) <- Map.toAscList (llvmFunctions moduleValue)
        , (blockId, blockValue) <- Map.toAscList (llvmFunctionBlocks functionValue)
        , target <- llvmBlockSuccessors blockValue
        ]
  in Map.keys (llvmFunctions expectedModule) == Map.keys (llvmFunctions actualModule)
      && fmap llvmFunctionEntry (llvmFunctions expectedModule)
        == fmap llvmFunctionEntry (llvmFunctions actualModule)
      && fmap llvmFunctionParameters (llvmFunctions expectedModule)
        == fmap llvmFunctionParameters (llvmFunctions actualModule)
      && llvmRuntimeSites expectedModule == llvmRuntimeSites actualModule
      && edges expectedModule == edges actualModule
      && llvmContractEdgeWitnesses (llvmArtifactContract expected)
        == llvmContractEdgeWitnesses (llvmArtifactContract actual)

freshIdentity :: LLVMArtifact -> Bool
freshIdentity artifact =
  llvmArtifactText artifact == renderLLVMModule (llvmArtifactModule artifact)
    && llvmContractTargetDigest (llvmArtifactContract artifact)
      == llvmModuleDigest (llvmArtifactModule artifact)

verifyWith :: Lowerer -> StorageBundle -> SystemsArtifact -> LLVMArtifact
  -> Either LLVMVerificationError ()
verifyWith lowerer bundle =
  verifyLLVMEmissionWith lowerer (phase0StorageLLVMVerificationContext bundle)

selectedLowererPasses :: Lowerer -> Bool
selectedLowererPasses lowerer = withSelected lowerer $ \bundle systemsArtifact artifact ->
  verifyWith lowerer bundle systemsArtifact artifact == Right ()

withFixture :: (StorageBundle -> SystemsArtifact -> LLVMArtifact -> Bool) -> Bool
withFixture = withSelected lowerSystemsStorage

withSelected :: Lowerer -> (StorageBundle -> SystemsArtifact -> LLVMArtifact -> Bool) -> Bool
withSelected lowerer action = case phase0StorageBundle of
  Left _ -> False
  Right bundle ->
    let systemsArtifact = storageArtifact bundle
        artifact = lowerer phase0StorageLLVMTarget systemsArtifact
    in action bundle systemsArtifact artifact

lowerSystemsStorageWithHelper :: Lowerer
lowerSystemsStorageWithHelper target systemsArtifact =
  addExplicitHelper (lowerSystemsStorage target systemsArtifact)

lowerSystemsStorageWithScalarHelper :: Lowerer
lowerSystemsStorageWithScalarHelper target systemsArtifact =
  changeFunction helperFunctionName
    (\functionValue -> functionValue
      { llvmFunctionBlocks = Map.singleton helperEntry
          (scalarBlock helperEntry helperScalarName 32) })
    (lowerSystemsStorageWithHelper target systemsArtifact)

lowerSystemsStorageWithHelperBlocks :: Lowerer
lowerSystemsStorageWithHelperBlocks target systemsArtifact =
  changeFunction helperFunctionName (insertBlock extraReturnBlock)
    (lowerSystemsStorageWithHelper target systemsArtifact)

addExplicitHelper :: LLVMArtifact -> LLVMArtifact
addExplicitHelper artifact = rebindModule changedModule artifact
  where
    moduleValue = llvmArtifactModule artifact
    changedModule = moduleValue
      { llvmFunctions = Map.insert helperFunctionName helperFunction (llvmFunctions moduleValue) }

changeFunction :: Text -> (LLVMFunction -> LLVMFunction) -> LLVMArtifact -> LLVMArtifact
changeFunction functionName change artifact =
  let moduleValue = llvmArtifactModule artifact
  in rebindModule
      (moduleValue { llvmFunctions = Map.adjust change functionName (llvmFunctions moduleValue) })
      artifact

insertBlock :: LLVMBlock -> LLVMFunction -> LLVMFunction
insertBlock blockValue functionValue = functionValue
  { llvmFunctionBlocks = Map.insert (llvmBlockId blockValue) blockValue (llvmFunctionBlocks functionValue) }

helperFunctionName :: Text
helperFunctionName = "review.r3.explicit.helper"

helperEntry :: LLVMBlockId
helperEntry = LLVMBlockId "review.r3.helper.entry"

earlyExtraBlockId, lateExtraBlockId :: LLVMBlockId
earlyExtraBlockId = LLVMBlockId "aaa.review.r3.extra"
lateExtraBlockId = LLVMBlockId "zzz.review.r3.extra"

helperScalarName, scalarHelperI32Header, scalarHelperI64Header :: Text
helperScalarName = "review.r3.helper.value"
scalarHelperI32Header = "define i32 @review_r3_explicit_helper() {"
scalarHelperI64Header = "define i64 @review_r3_explicit_helper() {"

helperFunction :: LLVMFunction
helperFunction = LLVMFunction
  { llvmFunctionName = helperFunctionName
  , llvmFunctionParameters = []
  , llvmFunctionEntry = helperEntry
  , llvmFunctionBlocks = Map.singleton helperEntry helperBlock
  }

helperBlock :: LLVMBlock
helperBlock = LLVMBlock
  { llvmBlockId = helperEntry
  , llvmBlockOps = []
  , llvmBlockTerminator = LLVMReturn "review-r3-explicit-helper"
  }

extraReturnBlock :: LLVMBlock
extraReturnBlock = helperBlock { llvmBlockId = earlyExtraBlockId }

scalarBlock :: LLVMBlockId -> Text -> Int -> LLVMBlock
scalarBlock blockId valueName width = LLVMBlock
  { llvmBlockId = blockId
  , llvmBlockOps = [LLVMScalarLiteral valueName (ScalarUIntLiteral width 7)]
  , llvmBlockTerminator = LLVMReturnScalar valueName (ScalarUInt width)
  }

rebindModule :: LLVMModule -> LLVMArtifact -> LLVMArtifact
rebindModule moduleValue artifact = artifact
  { llvmArtifactModule = moduleValue
  , llvmArtifactText = renderLLVMModule moduleValue
  , llvmArtifactContract = contract
      { llvmContractTargetDigest = llvmModuleDigest moduleValue }
  }
  where
    contract = llvmArtifactContract artifact

testCase :: String -> Bool -> IO Bool
testCase label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
