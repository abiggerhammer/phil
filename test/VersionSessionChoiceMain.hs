{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.LLVM
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "version session choice candidate verifies" candidateVerifies
    , test "server emits semantic unsupported/version selects" exactServerSelects
    , test "client offers unsupported/version with selected UInt16 payload" exactClientOffer
    , test "legacy client version Bool and receive call are absent" legacyClientChoiceAbsent
    , test "received selected version feeds client refinement" selectedVersionFeedsRefinement
    , test "local choose_supported choice remains local" localChoicePreserved
    , test "payload/cancel and final response semantics remain valid" payloadCancelPreserved
    , test "missing client version payload is rejected" missingVersionPayloadRejects
    , test "version payload cannot be used on unsupported arm" unsupportedArmUseRejects
    , test "generic LLVM remains fail-closed before physical version lowering" llvmFailClosed
    ]
  if and results then pure () else exitFailure

candidateVerifies :: Bool
candidateVerifies = case phase0VersionSessionChoiceBundle of
  Right bundle -> verifyVersionSessionChoiceBundle bundle == Right ()
  Left _ -> False

exactServerSelects :: Bool
exactServerSelects = withBundle $ \bundle ->
  let witness = versionSessionChoiceWitness bundle
  in case lookupServer bundle of
      Nothing -> False
      Just server ->
        hasExactSelect
          server
          (versionChoiceServerUnsupportedBlock witness)
          (versionChoiceServerTransport witness)
          (versionChoiceUnsupportedLabel witness)
          Nothing
          (versionChoiceSelectDecision witness)
        && hasExactSelect
          server
          (versionChoiceServerVersionBlock witness)
          (versionChoiceServerTransport witness)
          (versionChoiceVersionLabel witness)
          (Just (versionChoiceServerSelectedVersion witness))
          (versionChoiceSelectDecision witness)

exactClientOffer :: Bool
exactClientOffer = withBundle $ \bundle ->
  let witness = versionSessionChoiceWitness bundle
      expected = Map.fromList
        [ ( versionChoiceUnsupportedLabel witness
          , SystemsChoiceArm Nothing (versionChoiceClientUnsupportedTarget witness)
          )
        , ( versionChoiceVersionLabel witness
          , SystemsChoiceArm
              (Just (versionChoiceClientSelectedVersion witness))
              (versionChoiceClientVersionTarget witness)
          )
        ]
  in case lookupClientBlock bundle (versionChoiceClientOfferBlock witness) of
      Just blockValue -> systemsBlockTerminator blockValue
        == TermSessionOffer (versionChoiceClientTransport witness) expected
      Nothing -> False

legacyClientChoiceAbsent :: Bool
legacyClientChoiceAbsent = withBundle $ \bundle ->
  let witness = versionSessionChoiceWitness bundle
  in case lookupClient bundle of
      Nothing -> False
      Just client ->
        Map.notMember
          (versionChoiceClientLegacyDiscriminator witness)
          (systemsFunctionValues client)
        && case Map.lookup
            (versionChoiceClientOfferBlock witness)
            (systemsFunctionBlocks client) of
              Nothing -> False
              Just blockValue -> not (any (isLegacyReceive witness) (systemsBlockOps blockValue))

selectedVersionFeedsRefinement :: Bool
selectedVersionFeedsRefinement = withBundle $ \bundle ->
  let witness = versionSessionChoiceWitness bundle
  in case lookupClient bundle of
      Nothing -> False
      Just client ->
        case ( Map.lookup
                (versionChoiceClientSelectedVersion witness)
                (systemsFunctionValues client)
             , Map.lookup
                (versionChoiceClientVersionTarget witness)
                (systemsFunctionBlocks client)
             ) of
          ( Just SystemsValue { systemsValueRole = TypedScalar (ScalarUInt 16) }
            , Just blockValue
            ) -> case systemsBlockTerminator blockValue of
                TermRuntimeCheck inputs _ yes no ->
                  inputs == [versionChoiceClientSelectedVersion witness]
                    && yes == versionChoiceClientVersionSuccess witness
                    && no == versionChoiceClientVersionFailure witness
                _ -> False
          _ -> False

localChoicePreserved :: Bool
localChoicePreserved = withBundle $ \bundle ->
  let witness = phase0LocalRuntimeChoiceWitness
      expected = Map.fromList
        [ ("none", SystemsRuntimeChoiceArm Nothing (localChoiceNoneTarget witness))
        , ("some", SystemsRuntimeChoiceArm
            (Just (localChoiceSelectedVersion witness))
            (localChoiceSomeTarget witness))
        ]
  in case lookupServerBlock bundle (localChoiceBlock witness) of
      Just blockValue -> systemsBlockTerminator blockValue
        == TermRuntimeChoice (localChoiceName witness) [] Nothing expected
      Nothing -> False

payloadCancelPreserved :: Bool
payloadCancelPreserved = withBundle $ \bundle ->
  case verifyPayloadCancelChoiceWitness
    (versionSessionChoiceArtifact bundle)
    phase0PayloadCancelChoiceWitness of
      Right () -> True
      Left _ -> False

missingVersionPayloadRejects :: Bool
missingVersionPayloadRejects = withBundle $ \bundle ->
  let witness = versionSessionChoiceWitness bundle
      mutated = mapClientBlock bundle (versionChoiceClientOfferBlock witness) $ \blockValue ->
        blockValue
          { systemsBlockTerminator = case systemsBlockTerminator blockValue of
              TermSessionOffer transport arms ->
                TermSessionOffer transport $
                  Map.adjust
                    (\arm -> arm { choiceArmPayloadBinding = Nothing })
                    (versionChoiceVersionLabel witness)
                    arms
              other -> other
          }
  in case verifyVersionSessionChoiceWitness mutated witness of
      Left _ -> True
      Right () -> False

unsupportedArmUseRejects :: Bool
unsupportedArmUseRejects = withBundle $ \bundle ->
  let witness = versionSessionChoiceWitness bundle
      mutated = mapClientBlock bundle (versionChoiceClientUnsupportedTarget witness) $ \blockValue ->
        blockValue
          { systemsBlockOps = OpRuntimeCall
              { runtimeCallName = "illegal selected version use"
              , runtimeCallInputs = [versionChoiceClientSelectedVersion witness]
              , runtimeCallOutputs = []
              , runtimeCallSite = Nothing
              , runtimeCallDecision = DecisionId "lower.runtime.semantic_call"
              } : systemsBlockOps blockValue
          }
  in case verifyScalarDataflow mutated of
      Left (ScalarUseBeforeDefinition _ _ _ _ _ _) -> True
      _ -> False

llvmFailClosed :: Bool
llvmFailClosed = withBundle $ \bundle ->
  let witness = versionSessionChoiceWitness bundle
      llvmArtifact = lowerSystemsPayloadCancelChoice
        phase0PayloadCancelChoiceLLVMTarget
        (versionSessionChoiceArtifact bundle)
      versionPoison = do
        blockValue <- lookupLLVMServerBlock llvmArtifact (versionChoiceServerVersionBlock witness)
        pure (LLVMPoison "unlowered-session-select:version" `elem` llvmBlockOps blockValue)
      clientOfferClosed = do
        blockValue <- lookupLLVMClientBlock llvmArtifact (versionChoiceClientOfferBlock witness)
        pure (llvmBlockTerminator blockValue == LLVMUnreachable Nothing)
  in versionPoison == Just True && clientOfferClosed == Just True

hasExactSelect
  :: SystemsFunction
  -> BlockId
  -> ValueId
  -> Text
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

isLegacyReceive :: VersionSessionChoiceWitness -> SystemsOp -> Bool
isLegacyReceive witness operation = case operation of
  OpRuntimeCall { runtimeCallName = name } ->
    name == versionChoiceClientLegacyReceiveCall witness
  _ -> False

withBundle :: (VersionSessionChoiceBundle -> Bool) -> Bool
withBundle action = case phase0VersionSessionChoiceBundle of
  Left _ -> False
  Right bundle -> action bundle

lookupServer :: VersionSessionChoiceBundle -> Maybe SystemsFunction
lookupServer bundle =
  let witness = versionSessionChoiceWitness bundle
  in Map.lookup
      (versionChoiceServerFunction witness)
      (systemsProgramFunctions (systemsArtifactProgram (versionSessionChoiceArtifact bundle)))

lookupClient :: VersionSessionChoiceBundle -> Maybe SystemsFunction
lookupClient bundle =
  let witness = versionSessionChoiceWitness bundle
  in Map.lookup
      (versionChoiceClientFunction witness)
      (systemsProgramFunctions (systemsArtifactProgram (versionSessionChoiceArtifact bundle)))

lookupServerBlock :: VersionSessionChoiceBundle -> BlockId -> Maybe SystemsBlock
lookupServerBlock bundle blockId = do
  function <- lookupServer bundle
  Map.lookup blockId (systemsFunctionBlocks function)

lookupClientBlock :: VersionSessionChoiceBundle -> BlockId -> Maybe SystemsBlock
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

mapClientBlock
  :: VersionSessionChoiceBundle
  -> BlockId
  -> (SystemsBlock -> SystemsBlock)
  -> SystemsArtifact
mapClientBlock bundle blockId transform =
  let artifact = versionSessionChoiceArtifact bundle
      program = systemsArtifactProgram artifact
      functions = systemsProgramFunctions program
      functions' = Map.adjust
        (\function -> function
          { systemsFunctionBlocks = Map.adjust transform blockId (systemsFunctionBlocks function) })
        "UploadClient"
        functions
      program' = program { systemsProgramFunctions = functions' }
  in artifact { systemsArtifactProgram = program' }

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
