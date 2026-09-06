{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.Core.Scalar (ScalarType (ScalarUInt))
import Phil.LLVM.BeginPolicyChoice
  ( lowerSystemsBeginPolicyChoice
  , phase0BeginPolicyChoiceLLVMTarget
  , phase0BeginPolicyChoiceLLVMVerificationContext
  )
import Phil.LLVM.IR
import Phil.LLVM.Verify
  ( LLVMVerificationError (..)
  , verifyLLVMEmissionWith
  )
import Phil.Systems.BeginPolicySessionChoice
  ( BeginPolicySessionChoiceBundle (..)
  , phase0BeginPolicySessionChoiceBundle
  )
import Phil.Systems.IR (SystemsArtifact)
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ testCase "R2 unchanged parameter correspondence passes" unchangedPasses
    , testCase "R2 parameter omission rejects" (mutationRejects omitOne)
    , testCase "R2 parameter name drift rejects" (mutationRejects driftName)
    , testCase "R2 parameter type drift rejects" (mutationRejects driftType)
    , testCase "R2 parameter order drift rejects" (mutationRejects swapFirstTwo)
    ]
  if and results then pure () else exitFailure

unchangedPasses :: Bool
unchangedPasses = withFixture $ \bundle systemsArtifact llvmArtifact ->
  verifyLLVMEmissionWith
    lowerSystemsBeginPolicyChoice
    (phase0BeginPolicyChoiceLLVMVerificationContext bundle)
    systemsArtifact
    llvmArtifact
    == Right ()

mutationRejects :: ([LLVMParameter] -> Maybe [LLVMParameter]) -> Bool
mutationRejects transform = withFixture $ \bundle systemsArtifact llvmArtifact ->
  case mutateFirstApplicableParameters transform llvmArtifact of
    Nothing -> False
    Just badArtifact ->
      case verifyLLVMEmissionWith
          lowerSystemsBeginPolicyChoice
          (phase0BeginPolicyChoiceLLVMVerificationContext bundle)
          systemsArtifact
          badArtifact of
        Left (LLVMFunctionParametersMismatch _ expected actual) -> expected /= actual
        _ -> False

withFixture
  :: (BeginPolicySessionChoiceBundle -> SystemsArtifact -> LLVMArtifact -> Bool)
  -> Bool
withFixture action = case phase0BeginPolicySessionChoiceBundle of
  Left _ -> False
  Right bundle ->
    let systemsArtifact = beginPolicySessionChoiceArtifact bundle
        llvmArtifact = lowerSystemsBeginPolicyChoice
          phase0BeginPolicyChoiceLLVMTarget
          systemsArtifact
    in action bundle systemsArtifact llvmArtifact

mutateFirstApplicableParameters
  :: ([LLVMParameter] -> Maybe [LLVMParameter])
  -> LLVMArtifact
  -> Maybe LLVMArtifact
mutateFirstApplicableParameters transform artifact =
  go (Map.toAscList (llvmFunctions moduleValue))
  where
    moduleValue = llvmArtifactModule artifact

    go [] = Nothing
    go ((functionName, functionValue) : rest) =
      case transform (llvmFunctionParameters functionValue) of
        Just changed
          | changed /= llvmFunctionParameters functionValue ->
              let changedFunction = functionValue { llvmFunctionParameters = changed }
                  changedModule = moduleValue
                    { llvmFunctions =
                        Map.insert functionName changedFunction (llvmFunctions moduleValue)
                    }
              in Just (rebindModule changedModule artifact)
        _ -> go rest

rebindModule :: LLVMModule -> LLVMArtifact -> LLVMArtifact
rebindModule moduleValue artifact = artifact
  { llvmArtifactModule = moduleValue
  , llvmArtifactText = renderLLVMModule moduleValue
  , llvmArtifactContract = contract
      { llvmContractTargetDigest = llvmModuleDigest moduleValue }
  }
  where
    contract = llvmArtifactContract artifact

omitOne :: [LLVMParameter] -> Maybe [LLVMParameter]
omitOne (_ : rest) = Just rest
omitOne [] = Nothing

driftName :: [LLVMParameter] -> Maybe [LLVMParameter]
driftName (parameter : rest) = Just
  (parameter { llvmParameterName = llvmParameterName parameter <> ".review-r2" } : rest)
driftName [] = Nothing

driftType :: [LLVMParameter] -> Maybe [LLVMParameter]
driftType (parameter : rest) = Just
  (parameter { llvmParameterType = otherType (llvmParameterType parameter) } : rest)
driftType [] = Nothing

otherType :: LLVMParameterType -> LLVMParameterType
otherType parameterType = case parameterType of
  LLVMPointerParameter -> LLVMScalarParameter (ScalarUInt 32)
  LLVMScalarParameter _ -> LLVMPointerParameter

swapFirstTwo :: [LLVMParameter] -> Maybe [LLVMParameter]
swapFirstTwo (first : second : rest) = Just (second : first : rest)
swapFirstTwo _ = Nothing

testCase :: String -> Bool -> IO Bool
testCase label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
