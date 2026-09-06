{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.Verify
  ( LLVMVerificationContext (..)
  , LLVMVerificationError (..)
  , verifyLLVMEmission
  , verifyLLVMEmissionWith
  ) where

import Control.Monad (forM_, unless, when)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
import Phil.LLVM.IR
import Phil.LLVM.Lower (lowerSystemsConservative)
import Phil.Systems.IR
import Phil.Systems.Verify
  ( SystemsVerificationContext (..)
  , SystemsVerificationError
  , verifySystemsArtifact
  )

data LLVMVerificationContext = LLVMVerificationContext
  { llvmSystemsContext :: SystemsVerificationContext
  , llvmExpectedLanguageVersion :: Text
  , llvmExpectedToolVersion :: Text
  , llvmExpectedTargetTriple :: Text
  , llvmExpectedDataLayout :: Text
  , llvmExpectedRuntimeABIDigest :: Digest
  , llvmExpectedRuntimeABIProfile :: Text
  , llvmAuthorizedStrengthenings :: Map Text (Set LLVMAuthority)
  }
  deriving (Eq, Show)

data LLVMVerificationError
  = LLVMSystemsError SystemsVerificationError
  | LLVMSourceDigestMismatch Digest Digest
  | LLVMTargetDigestMismatch Digest Digest
  | LLVMArtifactTextMismatch
  | LLVMLanguageVersionMismatch Text Text
  | LLVMToolVersionMismatch Text Text
  | LLVMTargetTripleMismatch Text Text
  | LLVMDataLayoutMismatch Text Text
  | LLVMRuntimeABIDigestMismatch Digest Digest
  | LLVMRuntimeABIProfileMismatch Text Text
  | LLVMCompilationProfileMismatch CompilationProfile CompilationProfile
  | LLVMFunctionMapKeyMismatch Text Text
  | LLVMFunctionMissing Text
  | LLVMFunctionEntryMismatch Text LLVMBlockId LLVMBlockId
  | LLVMFunctionParametersMismatch Text [LLVMParameter] [LLVMParameter]
  | LLVMMissingEntryBlock Text LLVMBlockId
  | LLVMBlockMapKeyMismatch Text LLVMBlockId LLVMBlockId
  | LLVMUnknownControlTarget Text LLVMBlockId LLVMBlockId
  | LLVMRuntimeCoverageMismatch [RuntimeSiteRef] [RuntimeSiteRef]
  | LLVMOrdinaryOperationMismatch Text LLVMBlockId [LLVMOp] [LLVMOp]
  | LLVMOrdinaryTerminatorMismatch Text LLVMBlockId LLVMTerminator LLVMTerminator
  | LLVMEdgeWitnessSetMismatch
  | LLVMDuplicateEdgeWitness Text BlockId BlockId
  | LLVMEdgeWitnessPathTooShort Text BlockId BlockId
  | LLVMEdgeWitnessFunctionMissing Text
  | LLVMEdgeWitnessBlockMissing Text LLVMBlockId
  | LLVMEdgeWitnessPathBroken Text LLVMBlockId LLVMBlockId
  | LLVMUnwitnessedTargetEdge Text LLVMBlockId LLVMBlockId
  | LLVMTraceRelationMismatch
  | LLVMResourceFailureRelationMismatch
  | LLVMStrengtheningMapKeyMismatch LLVMStrengtheningId LLVMStrengtheningId
  | LLVMEmptyStrengtheningClaim LLVMStrengtheningId
  | LLVMStrengtheningLocationMissing LLVMStrengtheningId
  | LLVMStrengtheningUseCount LLVMStrengtheningId Int
  | LLVMStrengtheningUseMissing LLVMStrengtheningId
  | LLVMStrengtheningUseLocationMismatch LLVMStrengtheningId Text LLVMBlockId Text LLVMBlockId
  | LLVMStrengtheningKindUseMismatch LLVMStrengtheningId
  | LLVMUnauthorizedStrengthening LLVMStrengtheningId Text LLVMAuthority
  | LLVMStrengtheningAuthorityMissing LLVMStrengtheningId LLVMAuthority
  | LLVMUnjustifiedUnreachable Text LLVMBlockId
  | LLVMAccidentalPoison Text LLVMBlockId
  | LLVMUndefValue Text LLVMBlockId
  | LLVMFreezeValue Text LLVMBlockId
  deriving (Eq, Show)

type LLVMLowerer = LLVMTargetProfile -> SystemsArtifact -> LLVMArtifact

verifyLLVMEmission
  :: LLVMVerificationContext
  -> SystemsArtifact
  -> LLVMArtifact
  -> Either LLVMVerificationError ()
verifyLLVMEmission = verifyLLVMEmissionWith lowerSystemsConservative

verifyLLVMEmissionWith
  :: LLVMLowerer
  -> LLVMVerificationContext
  -> SystemsArtifact
  -> LLVMArtifact
  -> Either LLVMVerificationError ()
verifyLLVMEmissionWith lowerer context systemsArtifact artifact = do
  mapLeft LLVMSystemsError $
    verifySystemsArtifact (llvmSystemsContext context) systemsArtifact
  verifyIdentity context systemsArtifact artifact
  verifyModuleStructure systemsArtifact (llvmArtifactModule artifact)
  verifyRuntimeCoverage systemsArtifact (llvmArtifactModule artifact)
  verifyEdgeWitnesses systemsArtifact artifact
  verifyContractRelations systemsArtifact (llvmArtifactContract artifact)
  verifyDefinedExecutionDiscipline (llvmArtifactModule artifact)
  verifyOrdinaryProjectionWith lowerer context systemsArtifact (llvmArtifactModule artifact)
  verifyStrengthenings context systemsArtifact (llvmArtifactModule artifact)

verifyIdentity
  :: LLVMVerificationContext
  -> SystemsArtifact
  -> LLVMArtifact
  -> Either LLVMVerificationError ()
verifyIdentity context systemsArtifact artifact = do
  let moduleValue = llvmArtifactModule artifact
      contract = llvmArtifactContract artifact
      expectedSource = systemsArtifactDigest systemsArtifact
      expectedTarget = llvmModuleDigest moduleValue
  unless (llvmContractSourceDigest contract == expectedSource) $
    Left (LLVMSourceDigestMismatch expectedSource (llvmContractSourceDigest contract))
  unless (llvmContractTargetDigest contract == expectedTarget) $
    Left (LLVMTargetDigestMismatch expectedTarget (llvmContractTargetDigest contract))
  unless (llvmArtifactText artifact == renderLLVMModule moduleValue) $
    Left LLVMArtifactTextMismatch
  unless (llvmLanguageVersion moduleValue == llvmExpectedLanguageVersion context) $
    Left (LLVMLanguageVersionMismatch (llvmExpectedLanguageVersion context) (llvmLanguageVersion moduleValue))
  unless (llvmToolVersion moduleValue == llvmExpectedToolVersion context) $
    Left (LLVMToolVersionMismatch (llvmExpectedToolVersion context) (llvmToolVersion moduleValue))
  unless (llvmTargetTriple moduleValue == llvmExpectedTargetTriple context) $
    Left (LLVMTargetTripleMismatch (llvmExpectedTargetTriple context) (llvmTargetTriple moduleValue))
  unless (llvmDataLayout moduleValue == llvmExpectedDataLayout context) $
    Left (LLVMDataLayoutMismatch (llvmExpectedDataLayout context) (llvmDataLayout moduleValue))
  unless (llvmRuntimeABIDigest moduleValue == llvmExpectedRuntimeABIDigest context) $
    Left (LLVMRuntimeABIDigestMismatch (llvmExpectedRuntimeABIDigest context) (llvmRuntimeABIDigest moduleValue))
  unless (llvmRuntimeABIProfile moduleValue == llvmExpectedRuntimeABIProfile context) $
    Left (LLVMRuntimeABIProfileMismatch (llvmExpectedRuntimeABIProfile context) (llvmRuntimeABIProfile moduleValue))
  let expectedProfile = systemsProgramProfile (systemsArtifactProgram systemsArtifact)
  unless (llvmCompilationProfile moduleValue == expectedProfile) $
    Left (LLVMCompilationProfileMismatch expectedProfile (llvmCompilationProfile moduleValue))

verifyModuleStructure :: SystemsArtifact -> LLVMModule -> Either LLVMVerificationError ()
verifyModuleStructure systemsArtifact moduleValue = do
  let sourceFunctions = systemsProgramFunctions (systemsArtifactProgram systemsArtifact)
      targetFunctions = llvmFunctions moduleValue
  forM_ (Map.toAscList targetFunctions) $ \(functionKey, functionValue) -> do
    unless (functionKey == llvmFunctionName functionValue) $
      Left (LLVMFunctionMapKeyMismatch functionKey (llvmFunctionName functionValue))
    unless (Map.member (llvmFunctionEntry functionValue) (llvmFunctionBlocks functionValue)) $
      Left (LLVMMissingEntryBlock functionKey (llvmFunctionEntry functionValue))
    forM_ (Map.toAscList (llvmFunctionBlocks functionValue)) $ \(blockKey, blockValue) -> do
      unless (blockKey == llvmBlockId blockValue) $
        Left (LLVMBlockMapKeyMismatch functionKey blockKey (llvmBlockId blockValue))
      forM_ (llvmBlockSuccessors blockValue) $ \target ->
        unless (Map.member target (llvmFunctionBlocks functionValue)) $
          Left (LLVMUnknownControlTarget functionKey blockKey target)
  forM_ (Map.toAscList sourceFunctions) $ \(functionKey, sourceFunction) ->
    case Map.lookup functionKey targetFunctions of
      Nothing -> Left (LLVMFunctionMissing functionKey)
      Just targetFunction -> do
        let expectedEntry = LLVMBlockId (unBlockId (systemsFunctionEntry sourceFunction))
        unless (llvmFunctionEntry targetFunction == expectedEntry) $
          Left (LLVMFunctionEntryMismatch functionKey expectedEntry (llvmFunctionEntry targetFunction))

verifyRuntimeCoverage :: SystemsArtifact -> LLVMModule -> Either LLVMVerificationError ()
verifyRuntimeCoverage systemsArtifact moduleValue =
  let sourceSites = sourceRuntimeSites systemsArtifact
      targetSites = llvmRuntimeSites moduleValue
  in unless (counts sourceSites == counts targetSites) $
      Left (LLVMRuntimeCoverageMismatch sourceSites targetSites)

verifyOrdinaryProjectionWith
  :: LLVMLowerer
  -> LLVMVerificationContext
  -> SystemsArtifact
  -> LLVMModule
  -> Either LLVMVerificationError ()
verifyOrdinaryProjectionWith lowerer context systemsArtifact actualModule = do
  let expectedArtifact = lowerer (targetProfileFromContext context) systemsArtifact
      expectedModule = llvmArtifactModule expectedArtifact
  forM_ (Map.toAscList (llvmFunctions expectedModule)) $ \(functionName, expectedFunction) ->
    case Map.lookup functionName (llvmFunctions actualModule) of
      Nothing -> Left (LLVMFunctionMissing functionName)
      Just actualFunction -> do
        let expectedParameters = llvmFunctionParameters expectedFunction
            actualParameters = llvmFunctionParameters actualFunction
        unless (actualParameters == expectedParameters) $
          Left (LLVMFunctionParametersMismatch
            functionName expectedParameters actualParameters)
        forM_ (Map.toAscList (llvmFunctionBlocks expectedFunction)) $ \(blockId, expectedBlock) ->
          case Map.lookup blockId (llvmFunctionBlocks actualFunction) of
            Nothing -> Left (LLVMEdgeWitnessBlockMissing functionName blockId)
            Just actualBlock -> do
              let expectedOps = ordinaryOps (llvmBlockOps expectedBlock)
                  actualOps = ordinaryOps (llvmBlockOps actualBlock)
              unless (actualOps == expectedOps) $
                Left (LLVMOrdinaryOperationMismatch functionName blockId expectedOps actualOps)
              unless (ordinaryTerminatorCompatible
                        (llvmBlockTerminator expectedBlock)
                        (llvmBlockTerminator actualBlock)) $
                Left (LLVMOrdinaryTerminatorMismatch
                  functionName
                  blockId
                  (llvmBlockTerminator expectedBlock)
                  (llvmBlockTerminator actualBlock))

ordinaryOps :: [LLVMOp] -> [LLVMOp]
ordinaryOps = filter isOrdinary
  where
    isOrdinary operation = case operation of
      LLVMCall _ -> True
      LLVMRuntime _ _ -> True
      LLVMCleanup _ -> True
      LLVMBufferRelease _ -> True
      LLVMPlain _ -> True
      LLVMScalarLiteral _ _ -> True
      LLVMFieldProjection {} -> True
      LLVMOpaqueFieldProjection {} -> True
      LLVMChooseSupportedPayloadBinding {} -> True
      LLVMUnsupportedSelect {} -> True
      LLVMVersionSelect {} -> True
      LLVMVersionChoicePayloadBinding {} -> True
      LLVMBeginPolicyValidationReasonBinding {} -> True
      LLVMBeginPolicyRejectSelect {} -> True
      LLVMBeginPolicyProceedSelect {} -> True
      LLVMBeginPolicyChoiceReasonBinding {} -> True
      LLVMHelloPolicyValidationReasonBinding {} -> True
      LLVMHelloPolicyFailure {} -> True
      LLVMExactSend {} -> True
      LLVMClientSupportedVersions {} -> True
      LLVMClientPayloadLength {} -> True
      LLVMClientPayloadKind {} -> True
      LLVMClientSHA256 {} -> True
      LLVMClientSendHello {} -> True
      LLVMClientSendBegin {} -> True
      LLVMServerReceiveFrame {} -> True
      LLVMServerBorrowFrameView {} -> True
      LLVMServerCommitIngress {} -> True
      LLVMServerFailRecognition {} -> True
      LLVMServerDestroyPending {} -> True
      LLVMStorageFailureEffect {} -> True
      LLVMAcceptedResponse {} -> True
      LLVMRejectedResponse {} -> True
      LLVMPayloadCancelSelect {} -> True
      LLVMFinalResponsePayloadBinding {} -> True
      LLVMRecordUploadId {} -> True
      LLVMStrengtheningOp _ _ -> False
      LLVMPoison _ -> False
      LLVMUndef _ -> False
      LLVMFreeze _ -> False
      LLVMMetadata _ -> False

ordinaryTerminatorCompatible :: LLVMTerminator -> LLVMTerminator -> Bool
ordinaryTerminatorCompatible expected actual = expected == actual

targetProfileFromContext :: LLVMVerificationContext -> LLVMTargetProfile
targetProfileFromContext context = LLVMTargetProfile
  { llvmTargetLanguageVersion = llvmExpectedLanguageVersion context
  , llvmTargetToolVersion = llvmExpectedToolVersion context
  , llvmTargetTripleName = llvmExpectedTargetTriple context
  , llvmTargetDataLayout = llvmExpectedDataLayout context
  , llvmTargetRuntimeABIDigest = llvmExpectedRuntimeABIDigest context
  , llvmTargetRuntimeABIProfile = llvmExpectedRuntimeABIProfile context
  }

verifyEdgeWitnesses
  :: SystemsArtifact
  -> LLVMArtifact
  -> Either LLVMVerificationError ()
verifyEdgeWitnesses systemsArtifact artifact = do
  let contract = llvmArtifactContract artifact
      witnesses = llvmContractEdgeWitnesses contract
      sourceEdges = sourceControlEdges systemsArtifact
      witnessKeys = map witnessSourceKey witnesses
  when (length witnessKeys /= Set.size (Set.fromList witnessKeys)) $
    case firstDuplicate witnessKeys of
      Just (functionName, from, to) -> Left (LLVMDuplicateEdgeWitness functionName from to)
      Nothing -> pure ()
  unless (Set.fromList witnessKeys == Set.fromList sourceEdges) $
    Left LLVMEdgeWitnessSetMismatch
  forM_ witnesses $ verifyWitnessPath (llvmArtifactModule artifact)
  let allowedEdges = Set.fromList (concatMap witnessTargetEdges witnesses)
      actualEdges = Set.fromList (targetControlEdges (llvmArtifactModule artifact))
  forM_ (Set.toAscList (actualEdges `Set.difference` allowedEdges)) $ \(functionName, from, to) ->
    Left (LLVMUnwitnessedTargetEdge functionName from to)

verifyWitnessPath :: LLVMModule -> LLVMEdgeWitness -> Either LLVMVerificationError ()
verifyWitnessPath moduleValue witness = do
  let functionName = llvmEdgeTargetFunction witness
      path = llvmEdgeTargetPath witness
  when (length path < 2) $
    Left (LLVMEdgeWitnessPathTooShort
      (llvmEdgeSourceFunction witness)
      (llvmEdgeSourceFrom witness)
      (llvmEdgeSourceTo witness))
  functionValue <- case Map.lookup functionName (llvmFunctions moduleValue) of
    Nothing -> Left (LLVMEdgeWitnessFunctionMissing functionName)
    Just value -> Right value
  forM_ path $ \blockId ->
    unless (Map.member blockId (llvmFunctionBlocks functionValue)) $
      Left (LLVMEdgeWitnessBlockMissing functionName blockId)
  forM_ (pairs path) $ \(from, to) ->
    case Map.lookup from (llvmFunctionBlocks functionValue) of
      Nothing -> Left (LLVMEdgeWitnessBlockMissing functionName from)
      Just blockValue ->
        unless (to `elem` llvmBlockSuccessors blockValue) $
          Left (LLVMEdgeWitnessPathBroken functionName from to)

verifyContractRelations
  :: SystemsArtifact
  -> LLVMEmissionContract
  -> Either LLVMVerificationError ()
verifyContractRelations systemsArtifact contract = do
  let sourceContract = systemsArtifactStageContract systemsArtifact
  unless (llvmContractTraceRelation contract == stageTraceRelation sourceContract) $
    Left LLVMTraceRelationMismatch
  unless (llvmContractResourceFailureRelation contract == stageResourceFailureRelation sourceContract) $
    Left LLVMResourceFailureRelationMismatch

verifyStrengthenings
  :: LLVMVerificationContext
  -> SystemsArtifact
  -> LLVMModule
  -> Either LLVMVerificationError ()
verifyStrengthenings context systemsArtifact moduleValue = do
  let strengthenings = llvmStrengthenings moduleValue
      useIds = llvmStrengtheningUses moduleValue
  forM_ useIds $ \strengtheningId ->
    unless (Map.member strengtheningId strengthenings) $
      Left (LLVMStrengtheningUseMissing strengtheningId)
  forM_ (Map.toAscList strengthenings) $ \(key, strengthening) -> do
    unless (key == llvmStrengtheningId strengthening) $
      Left (LLVMStrengtheningMapKeyMismatch key (llvmStrengtheningId strengthening))
    when (Text.null (llvmStrengtheningClaim strengthening)) $
      Left (LLVMEmptyStrengtheningClaim key)
    verifyStrengtheningLocation moduleValue strengthening
    let locations = strengtheningUseLocations moduleValue key
    unless (length locations == 1) $
      Left (LLVMStrengtheningUseCount key (length locations))
    case locations of
      [(actualFunction, actualBlock, inTerminator)] -> do
        unless
          ( actualFunction == llvmStrengtheningFunction strengthening
          && actualBlock == llvmStrengtheningBlock strengthening
          ) $
          Left (LLVMStrengtheningUseLocationMismatch
            key
            (llvmStrengtheningFunction strengthening)
            (llvmStrengtheningBlock strengthening)
            actualFunction
            actualBlock)
        unless (kindMatchesLocation inTerminator (llvmStrengtheningKind strengthening)) $
          Left (LLVMStrengtheningKindUseMismatch key)
      _ -> pure ()
    verifyAuthority context systemsArtifact strengthening

verifyStrengtheningLocation :: LLVMModule -> LLVMStrengthening -> Either LLVMVerificationError ()
verifyStrengtheningLocation moduleValue strengthening =
  case Map.lookup (llvmStrengtheningFunction strengthening) (llvmFunctions moduleValue) >>= \functionValue ->
      Map.lookup (llvmStrengtheningBlock strengthening) (llvmFunctionBlocks functionValue) of
    Nothing -> Left (LLVMStrengtheningLocationMissing (llvmStrengtheningId strengthening))
    Just _ -> Right ()

strengtheningUseLocations
  :: LLVMModule
  -> LLVMStrengtheningId
  -> [(Text, LLVMBlockId, Bool)]
strengtheningUseLocations moduleValue strengtheningId =
  concat
    [ blockLocations (llvmFunctionName functionValue) blockValue
    | functionValue <- Map.elems (llvmFunctions moduleValue)
    , blockValue <- Map.elems (llvmFunctionBlocks functionValue)
    ]
  where
    blockLocations functionName blockValue =
      [ (functionName, llvmBlockId blockValue, False)
      | LLVMStrengtheningOp candidate _ <- llvmBlockOps blockValue
      , candidate == strengtheningId
      ] <> case llvmBlockTerminator blockValue of
        LLVMUnreachable (Just candidate) | candidate == strengtheningId ->
          [(functionName, llvmBlockId blockValue, True)]
        _ -> []

kindMatchesLocation :: Bool -> LLVMStrengtheningKind -> Bool
kindMatchesLocation inTerminator kind
  | inTerminator = kind == LLVMUnreachableFact
  | otherwise = kind /= LLVMUnreachableFact

verifyAuthority
  :: LLVMVerificationContext
  -> SystemsArtifact
  -> LLVMStrengthening
  -> Either LLVMVerificationError ()
verifyAuthority context systemsArtifact strengthening = do
  let strengtheningId = llvmStrengtheningId strengthening
      claim = llvmStrengtheningClaim strengthening
      authority = llvmStrengtheningAuthority strengthening
  case Map.lookup claim (llvmAuthorizedStrengthenings context) of
    Just permitted | Set.member authority permitted -> pure ()
    _ -> Left (LLVMUnauthorizedStrengthening strengtheningId claim authority)
  unless (authorityExists context systemsArtifact authority) $
    Left (LLVMStrengtheningAuthorityMissing strengtheningId authority)

authorityExists :: LLVMVerificationContext -> SystemsArtifact -> LLVMAuthority -> Bool
authorityExists context systemsArtifact authority = case authority of
  LLVMInvariant invariantId ->
    Map.member invariantId (stageInvariants (systemsArtifactStageContract systemsArtifact))
  LLVMEvidence evidenceId ->
    Set.member evidenceId (manifestEvidenceEntries manifest)
  LLVMObligation revision ->
    Set.member revision (manifestObligationRevisions manifest)
  where
    manifest = systemsAssuranceManifest (llvmSystemsContext context)

verifyDefinedExecutionDiscipline :: LLVMModule -> Either LLVMVerificationError ()
verifyDefinedExecutionDiscipline moduleValue =
  forM_ (Map.elems (llvmFunctions moduleValue)) $ \functionValue ->
    forM_ (Map.elems (llvmFunctionBlocks functionValue)) $ \blockValue -> do
      forM_ (llvmBlockOps blockValue) $ \operation -> case operation of
        LLVMPoison _ -> Left (LLVMAccidentalPoison (llvmFunctionName functionValue) (llvmBlockId blockValue))
        LLVMUndef _ -> Left (LLVMUndefValue (llvmFunctionName functionValue) (llvmBlockId blockValue))
        LLVMFreeze _ -> Left (LLVMFreezeValue (llvmFunctionName functionValue) (llvmBlockId blockValue))
        _ -> pure ()
      case llvmBlockTerminator blockValue of
        LLVMUnreachable Nothing ->
          Left (LLVMUnjustifiedUnreachable (llvmFunctionName functionValue) (llvmBlockId blockValue))
        _ -> pure ()

sourceRuntimeSites :: SystemsArtifact -> [RuntimeSiteRef]
sourceRuntimeSites systemsArtifact = concatMap runtimeSites
  (Map.elems (systemsProgramFunctions (systemsArtifactProgram systemsArtifact)))

sourceControlEdges :: SystemsArtifact -> [(Text, BlockId, BlockId)]
sourceControlEdges systemsArtifact =
  [ (systemsFunctionName functionValue, systemsBlockId blockValue, target)
  | functionValue <- Map.elems (systemsProgramFunctions (systemsArtifactProgram systemsArtifact))
  , blockValue <- Map.elems (systemsFunctionBlocks functionValue)
  , target <- blockSuccessors blockValue
  ]

targetControlEdges :: LLVMModule -> [(Text, LLVMBlockId, LLVMBlockId)]
targetControlEdges moduleValue =
  [ (llvmFunctionName functionValue, llvmBlockId blockValue, target)
  | functionValue <- Map.elems (llvmFunctions moduleValue)
  , blockValue <- Map.elems (llvmFunctionBlocks functionValue)
  , target <- llvmBlockSuccessors blockValue
  ]

witnessSourceKey :: LLVMEdgeWitness -> (Text, BlockId, BlockId)
witnessSourceKey witness =
  (llvmEdgeSourceFunction witness, llvmEdgeSourceFrom witness, llvmEdgeSourceTo witness)

witnessTargetEdges :: LLVMEdgeWitness -> [(Text, LLVMBlockId, LLVMBlockId)]
witnessTargetEdges witness =
  [ (llvmEdgeTargetFunction witness, from, to)
  | (from, to) <- pairs (llvmEdgeTargetPath witness)
  ]

pairs :: [a] -> [(a, a)]
pairs values = zip values (drop 1 values)

counts :: Ord a => [a] -> Map a Int
counts = Map.fromListWith (+) . map (\value -> (value, 1))

firstDuplicate :: Ord a => [a] -> Maybe a
firstDuplicate = go Set.empty
  where
    go _ [] = Nothing
    go seen (value : rest)
      | Set.member value seen = Just value
      | otherwise = go (Set.insert value seen) rest

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft transform = either (Left . transform) Right