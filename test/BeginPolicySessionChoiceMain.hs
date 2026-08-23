{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.LLVM
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "BeginPolicy session choice candidate verifies" candidateVerifies
    , test "server validation exposes explicit operands and rejected reason" exactServerRuntimeChoice
    , test "server emits semantic reject(reason)/proceed selects" exactServerSelects
    , test "client offers reject(reason)/proceed" exactClientOffer
    , test "legacy client BeginPolicy Bool and receive call are absent" legacyClientChoiceAbsent
    , test "Begin record materialization follows ingress commit" materializationAfterCommit
    , test "version-choice semantics and operands remain valid" versionChoicePreserved
    , test "missing local rejection payload is rejected" missingLocalReasonRejects
    , test "producing architecture policyContext internally is rejected" producedPolicyContextRejects
    , test "version-profile LLVM stays fail-closed before BeginPolicy physical lowering" llvmFailClosed
    ]
  if and results then pure () else exitFailure

candidateVerifies :: Bool
candidateVerifies = case phase0BeginPolicySessionChoiceBundle of
  Right bundle -> verifyBeginPolicySessionChoiceBundle bundle == Right ()
  Left _ -> False

exactServerRuntimeChoice :: Bool
exactServerRuntimeChoice = withBundle $ \bundle ->
  let witness = beginPolicySessionChoiceWitness bundle
      expectedArms = Map.fromList
        [ ( beginPolicyAcceptedArm witness
          , SystemsRuntimeChoiceArm Nothing (beginPolicyServerProceedBlock witness)
          )
        , ( beginPolicyRejectedArm witness
          , SystemsRuntimeChoiceArm
              (Just (beginPolicyServerRejectReason witness))
              (beginPolicyServerRejectBlock witness)
          )
        ]
  in case lookupServerBlock bundle (beginPolicyCommitBlock witness) of
      Just blockValue -> case systemsBlockTerminator blockValue of
        TermRuntimeChoice name inputs (Just site) arms ->
          name == beginPolicyRuntimeChoiceName witness
            && inputs == [beginPolicyPolicyContext witness, beginPolicyBeginRecord witness]
            && runtimeSiteKind site == ValidationBoundary "BeginPolicy"
            && arms == expectedArms
        _ -> False
      Nothing -> False

exactServerSelects :: Bool
exactServerSelects = withBundle $ \bundle ->
  let witness = beginPolicySessionChoiceWitness bundle
  in case lookupServer bundle of
      Nothing -> False
      Just server ->
        hasExactSelect
          server
          (beginPolicyServerRejectBlock witness)
          (beginPolicyServerTransport witness)
          (beginPolicyRejectLabel witness)
          (Just (beginPolicyServerRejectReason witness))
          (beginPolicyLoweringDecision witness)
        && hasExactSelect
          server
          (beginPolicyServerProceedBlock witness)
          (beginPolicyServerTransport witness)
          (beginPolicyProceedLabel witness)
          Nothing
          (beginPolicyLoweringDecision witness)

exactClientOffer :: Bool
exactClientOffer = withBundle $ \bundle ->
  let witness = beginPolicySessionChoiceWitness bundle
      expected = Map.fromList
        [ ( beginPolicyRejectLabel witness
          , SystemsChoiceArm
              (Just (beginPolicyClientRejectReason witness))
              (beginPolicyClientRejectTarget witness)
          )
        , ( beginPolicyProceedLabel witness
          , SystemsChoiceArm Nothing (beginPolicyClientProceedTarget witness)
          )
        ]
  in case lookupClientBlock bundle (beginPolicyClientOfferBlock witness) of
      Just blockValue -> systemsBlockTerminator blockValue
        == TermSessionOffer (beginPolicyClientTransport witness) expected
      Nothing -> False

legacyClientChoiceAbsent :: Bool
legacyClientChoiceAbsent = withBundle $ \bundle ->
  let witness = beginPolicySessionChoiceWitness bundle
  in case lookupClient bundle of
      Nothing -> False
      Just client ->
        Map.notMember
          (beginPolicyClientLegacyDiscriminator witness)
          (systemsFunctionValues client)
        && case Map.lookup
            (beginPolicyClientOfferBlock witness)
            (systemsFunctionBlocks client) of
              Nothing -> False
              Just blockValue -> not (any (isLegacyReceive witness) (systemsBlockOps blockValue))

materializationAfterCommit :: Bool
materializationAfterCommit = withBundle $ \bundle ->
  let witness = beginPolicySessionChoiceWitness bundle
  in case lookupServerBlock bundle (beginPolicyCommitBlock witness) of
      Nothing -> False
      Just blockValue ->
        let operations = systemsBlockOps blockValue
            commits =
              [ index
              | (index, OpCommitIngress { commitPending = pending }) <- zip [0 :: Int ..] operations
              , pending == beginPolicyPendingBegin witness
              ]
            materializations =
              [ index
              | (index, OpRuntimeCall name inputs outputs site decisionId) <- zip [0 :: Int ..] operations
              , name == beginPolicyMaterializeCall witness
              , null inputs
              , outputs == [beginPolicyBeginRecord witness]
              , site == Nothing
              , decisionId == beginPolicyLoweringDecision witness
              ]
        in case (commits, materializations) of
            (commitIndex : _, [materializeIndex]) -> materializeIndex > commitIndex
            _ -> False

versionChoicePreserved :: Bool
versionChoicePreserved = withBundle $ \bundle ->
  case verifyVersionChoiceOperandsWitness
    (beginPolicySessionChoiceArtifact bundle)
    phase0VersionChoiceOperandsWitness of
      Right () -> True
      Left _ -> False

missingLocalReasonRejects :: Bool
missingLocalReasonRejects = withBundle $ \bundle ->
  let witness = beginPolicySessionChoiceWitness bundle
      mutated = mapServerBlock bundle (beginPolicyCommitBlock witness) $ \blockValue ->
        blockValue
          { systemsBlockTerminator = case systemsBlockTerminator blockValue of
              TermRuntimeChoice name inputs site arms ->
                TermRuntimeChoice name inputs site $
                  Map.adjust
                    (\arm -> arm { runtimeChoiceArmPayloadBinding = Nothing })
                    (beginPolicyRejectedArm witness)
                    arms
              other -> other
          }
  in case verifyBeginPolicySessionChoiceWitness mutated witness of
      Left _ -> True
      Right () -> False

producedPolicyContextRejects :: Bool
producedPolicyContextRejects = withBundle $ \bundle ->
  let witness = beginPolicySessionChoiceWitness bundle
      mutated = mapServerBlock bundle (beginPolicyCommitBlock witness) $ \blockValue ->
        blockValue
          { systemsBlockOps = OpRuntimeCall
              { runtimeCallName = "illegal policyContext producer"
              , runtimeCallInputs = []
              , runtimeCallOutputs = [beginPolicyPolicyContext witness]
              , runtimeCallSite = Nothing
              , runtimeCallDecision = beginPolicyLoweringDecision witness
              } : systemsBlockOps blockValue
          }
  in case verifyBeginPolicySessionChoiceWitness mutated witness of
      Left (BeginPolicyInputHasProducer _ _) -> True
      _ -> False

llvmFailClosed :: Bool
llvmFailClosed = withBundle $ \bundle ->
  let witness = beginPolicySessionChoiceWitness bundle
      llvmArtifact = lowerSystemsVersionSessionChoice
        phase0VersionSessionChoiceLLVMTarget
        (beginPolicySessionChoiceArtifact bundle)
      serverChoiceClosed = do
        blockValue <- lookupLLVMServerBlock llvmArtifact (beginPolicyCommitBlock witness)
        pure (llvmBlockTerminator blockValue == LLVMUnreachable Nothing)
      rejectPoison = do
        blockValue <- lookupLLVMServerBlock llvmArtifact (beginPolicyServerRejectBlock witness)
        pure (LLVMPoison "unlowered-session-select:reject" `elem` llvmBlockOps blockValue)
      clientOfferClosed = do
        blockValue <- lookupLLVMClientBlock llvmArtifact (beginPolicyClientOfferBlock witness)
        pure (llvmBlockTerminator blockValue == LLVMUnreachable Nothing)
  in serverChoiceClosed == Just True
      && rejectPoison == Just True
      && clientOfferClosed == Just True

hasExactSelect
  :: SystemsFunction
  -> BlockId
  -> ValueId
  -> Data.Text.Text
  -> Maybe ValueId
  -> DecisionId
  -> Bool
hasExactSelect function blockId transport label payload decisionId =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> False
    Just blockValue -> any exact (systemsBlockOps blockValue)
  where
    exact operation = case operation of
      OpSessionSelect actualTransport actualLabel actualPayload actualDecision ->
        actualTransport == transport
          && actualLabel == label
          && actualPayload == payload
          && actualDecision == decisionId
      _ -> False

isLegacyReceive :: BeginPolicySessionChoiceWitness -> SystemsOp -> Bool
isLegacyReceive witness operation = case operation of
  OpRuntimeCall { runtimeCallName = name } ->
    name == beginPolicyClientLegacyReceiveCall witness
  _ -> False

withBundle :: (BeginPolicySessionChoiceBundle -> Bool) -> Bool
withBundle action = case phase0BeginPolicySessionChoiceBundle of
  Left _ -> False
  Right bundle -> action bundle

lookupServer :: BeginPolicySessionChoiceBundle -> Maybe SystemsFunction
lookupServer bundle =
  let witness = beginPolicySessionChoiceWitness bundle
  in Map.lookup
      (beginPolicyServerFunction witness)
      (systemsProgramFunctions (systemsArtifactProgram (beginPolicySessionChoiceArtifact bundle)))

lookupClient :: BeginPolicySessionChoiceBundle -> Maybe SystemsFunction
lookupClient bundle =
  let witness = beginPolicySessionChoiceWitness bundle
  in Map.lookup
      (beginPolicyClientFunction witness)
      (systemsProgramFunctions (systemsArtifactProgram (beginPolicySessionChoiceArtifact bundle)))

lookupServerBlock :: BeginPolicySessionChoiceBundle -> BlockId -> Maybe SystemsBlock
lookupServerBlock bundle blockId = do
  function <- lookupServer bundle
  Map.lookup blockId (systemsFunctionBlocks function)

lookupClientBlock :: BeginPolicySessionChoiceBundle -> BlockId -> Maybe SystemsBlock
lookupClientBlock bundle blockId = do
  function <- lookupClient bundle
  Map.lookup blockId (systemsFunctionBlocks function)

lookupLLVMServerBlock :: LLVMArtifact -> BlockId -> Maybe LLVMBlock
lookupLLVMServerBlock artifact blockId = do
  function <- Map.lookup "UploadServer" (llvmFunctions (llvmArtifactModule artifact))
  Map.lookup (LLVMBlockId (unBlockId blockId)) (llvmFunctionBlocks function)

lookupLLVMClientBlock :: LLVMArtifact -> BlockId -> Maybe LLVMBlock
lookupLLVMClientBlock artifact blockId = do
  function <- Map.lookup "UploadClient" (llvmFunctions (llvmArtifactModule artifact))
  Map.lookup (LLVMBlockId (unBlockId blockId)) (llvmFunctionBlocks function)

mapServerBlock
  :: BeginPolicySessionChoiceBundle
  -> BlockId
  -> (SystemsBlock -> SystemsBlock)
  -> SystemsArtifact
mapServerBlock bundle blockId transform =
  let artifact = beginPolicySessionChoiceArtifact bundle
      program = systemsArtifactProgram artifact
      functions = systemsProgramFunctions program
      functions' = Map.adjust
        (\function -> function
          { systemsFunctionBlocks = Map.adjust transform blockId (systemsFunctionBlocks function) })
        "UploadServer"
        functions
      program' = program { systemsProgramFunctions = functions' }
  in artifact { systemsArtifactProgram = program' }

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
