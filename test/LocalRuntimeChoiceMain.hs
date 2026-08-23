{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.LLVM
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "local runtime choice candidate verifies" candidateVerifies
    , test "choose_supported has exact none/some branch payload" exactChoice
    , test "version-selection stage invariant transfers to runtime choice" invariantTransferred
    , test "legacy has_version Bool is absent" legacyBoolAbsent
    , test "selected version reaches select version" selectedVersionFlows
    , test "payload/cancel semantic choice remains valid" payloadCancelPreserved
    , test "wrong some payload is rejected" wrongSomePayloadRejects
    , test "some payload cannot be used on none arm" noneArmUseRejects
    , test "some payload binder rejects alternate predecessor" alternateSomePredecessorRejects
    , test "generic LLVM remains fail-closed on local runtime choice" llvmFailClosed
    ]
  if and results then pure () else exitFailure

candidateVerifies :: Bool
candidateVerifies = case phase0LocalRuntimeChoiceBundle of
  Right bundle -> verifyLocalRuntimeChoiceBundle bundle == Right ()
  Left _ -> False

exactChoice :: Bool
exactChoice = withBundle $ \bundle ->
  let witness = localRuntimeChoiceWitness bundle
      expected = Map.fromList
        [ ("none", SystemsRuntimeChoiceArm Nothing (localChoiceNoneTarget witness))
        , ("some", SystemsRuntimeChoiceArm
            (Just (localChoiceSelectedVersion witness))
            (localChoiceSomeTarget witness))
        ]
  in case lookupSystemsBlock bundle (localChoiceBlock witness) of
      Just blockValue -> systemsBlockTerminator blockValue
        == TermRuntimeChoice (localChoiceName witness) [] Nothing expected
      Nothing -> False

invariantTransferred :: Bool
invariantTransferred = withBundle $ \bundle ->
  let witness = localRuntimeChoiceWitness bundle
      expectedArms = Map.fromList
        [ ("none", SystemsRuntimeChoiceArm Nothing (localChoiceNoneTarget witness))
        , ("some", SystemsRuntimeChoiceArm
            (Just (localChoiceSelectedVersion witness))
            (localChoiceSomeTarget witness))
        ]
      contract = systemsArtifactStageContract (localRuntimeChoiceArtifact bundle)
  in case Map.lookup (localChoiceInvariant witness) (stageInvariants contract) of
      Just StageInvariant
        { stageInvariantClaim = InvariantRuntimeChoice functionName blockId name arms
        } -> functionName == localChoiceFunction witness
          && blockId == localChoiceBlock witness
          && name == localChoiceName witness
          && arms == expectedArms
      _ -> False

legacyBoolAbsent :: Bool
legacyBoolAbsent = withBundle $ \bundle ->
  let witness = localRuntimeChoiceWitness bundle
  in case lookupServer bundle of
      Just function -> Map.notMember
        (localChoiceLegacyDiscriminator witness)
        (systemsFunctionValues function)
      Nothing -> False

selectedVersionFlows :: Bool
selectedVersionFlows = withBundle $ \bundle ->
  let witness = localRuntimeChoiceWitness bundle
  in case lookupSystemsBlock bundle (localChoiceVersionSelectBlock witness) of
      Just blockValue -> any (isExactSelect witness) (systemsBlockOps blockValue)
      Nothing -> False

payloadCancelPreserved :: Bool
payloadCancelPreserved = withBundle $ \bundle ->
  case verifyPayloadCancelChoiceWitness
    (localRuntimeChoiceArtifact bundle)
    phase0PayloadCancelChoiceWitness of
      Right () -> True
      Left _ -> False

wrongSomePayloadRejects :: Bool
wrongSomePayloadRejects = withBundle $ \bundle ->
  let witness = localRuntimeChoiceWitness bundle
      mutated = mapSystemsBlock bundle (localChoiceBlock witness) $ \blockValue ->
        blockValue
          { systemsBlockTerminator = case systemsBlockTerminator blockValue of
              TermRuntimeChoice name inputs site arms ->
                TermRuntimeChoice name inputs site $
                  Map.adjust
                    (\arm -> arm { runtimeChoiceArmPayloadBinding = Nothing })
                    "some"
                    arms
              other -> other
          }
  in case verifyLocalRuntimeChoiceWitness mutated witness of
      Left _ -> True
      Right () -> False

noneArmUseRejects :: Bool
noneArmUseRejects = withBundle $ \bundle ->
  let witness = localRuntimeChoiceWitness bundle
      mutated = mapSystemsBlock bundle (localChoiceNoneTarget witness) $ \blockValue ->
        blockValue
          { systemsBlockOps = OpRuntimeCall
              { runtimeCallName = "illegal selected version use"
              , runtimeCallInputs = [localChoiceSelectedVersion witness]
              , runtimeCallOutputs = []
              , runtimeCallSite = Nothing
              , runtimeCallDecision = DecisionId "lower.runtime.semantic_call"
              } : systemsBlockOps blockValue
          }
  in case verifyScalarDataflow mutated of
      Left (ScalarUseBeforeDefinition _ _ _ _ _ _) -> True
      _ -> False

alternateSomePredecessorRejects :: Bool
alternateSomePredecessorRejects = withBundle $ \bundle ->
  let witness = localRuntimeChoiceWitness bundle
      mutated = mapSystemsBlock bundle (localChoiceNoneTarget witness) $ \blockValue ->
        blockValue { systemsBlockTerminator = TermJump (localChoiceSomeTarget witness) }
  in case verifyLocalRuntimeChoiceWitness mutated witness of
      Left (LocalRuntimeChoiceMismatch _) -> True
      _ -> False

llvmFailClosed :: Bool
llvmFailClosed = withBundle $ \bundle ->
  let witness = localRuntimeChoiceWitness bundle
      artifact = lowerSystemsPayloadCancelChoice
        phase0PayloadCancelChoiceLLVMTarget
        (localRuntimeChoiceArtifact bundle)
  in case lookupLLVMBlock artifact (localChoiceBlock witness) of
      Just blockValue -> llvmBlockTerminator blockValue == LLVMUnreachable Nothing
      Nothing -> False

isExactSelect :: LocalRuntimeChoiceWitness -> SystemsOp -> Bool
isExactSelect witness OpRuntimeCall
  { runtimeCallName = "select version"
  , runtimeCallInputs = inputs
  , runtimeCallOutputs = []
  , runtimeCallSite = Nothing
  } = inputs == [localChoiceServerTransport witness, localChoiceSelectedVersion witness]
isExactSelect _ _ = False

withBundle :: (LocalRuntimeChoiceBundle -> Bool) -> Bool
withBundle action = case phase0LocalRuntimeChoiceBundle of
  Left _ -> False
  Right bundle -> action bundle

lookupServer :: LocalRuntimeChoiceBundle -> Maybe SystemsFunction
lookupServer bundle =
  let witness = localRuntimeChoiceWitness bundle
  in Map.lookup
      (localChoiceFunction witness)
      (systemsProgramFunctions (systemsArtifactProgram (localRuntimeChoiceArtifact bundle)))

lookupSystemsBlock :: LocalRuntimeChoiceBundle -> BlockId -> Maybe SystemsBlock
lookupSystemsBlock bundle blockId = do
  function <- lookupServer bundle
  Map.lookup blockId (systemsFunctionBlocks function)

lookupLLVMBlock :: LLVMArtifact -> BlockId -> Maybe LLVMBlock
lookupLLVMBlock artifact blockId = do
  function <- Map.lookup "UploadServer" (llvmFunctions (llvmArtifactModule artifact))
  Map.lookup (LLVMBlockId (unBlockId blockId)) (llvmFunctionBlocks function)

mapSystemsBlock
  :: LocalRuntimeChoiceBundle
  -> BlockId
  -> (SystemsBlock -> SystemsBlock)
  -> SystemsArtifact
mapSystemsBlock bundle blockId transform =
  let artifact = localRuntimeChoiceArtifact bundle
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
