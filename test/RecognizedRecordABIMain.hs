{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Phil.LLVM
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "recognized-record certification closes" certificationPasses
    , test "competing recognized record materialization is rejected" competingMaterializationRejects
    ]
  if and results then pure () else exitFailure

certificationPasses :: Bool
certificationPasses = verifyPhase0RecognizedRecordLLVMCertification == Right ()

competingMaterializationRejects :: Bool
competingMaterializationRejects = case phase0RecognizedRecordBundle of
  Left _ -> False
  Right bundle ->
    let badBundle = addCompetingMaterialization bundle
        badArtifact = lowerSystemsRecognizedRecord
          phase0RecognizedRecordLLVMTarget
          (recognizedRecordArtifact badBundle)
    in case verifyRecognizedRecordTranslation badBundle badArtifact of
      Left (RecognizedRecordSystemsMaterializationSetMismatch _ _ _) -> True
      _ -> False

addCompetingMaterialization
  :: RecognizedRecordBundle
  -> RecognizedRecordBundle
addCompetingMaterialization bundle = bundle
  { recognizedRecordArtifact = artifact
      { systemsArtifactProgram = program
          { systemsProgramFunctions = Map.adjust
              addToFunction
              functionName
              (systemsProgramFunctions program)
          }
      }
  }
  where
    witness = phase0BeginRecordWitness
    artifact = recognizedRecordArtifact bundle
    program = systemsArtifactProgram artifact
    functionName = recognizedRecordFunction witness
    successBlock = recognizedRecordSuccessBlock witness
    extraId = ValueId "server.begin.competing"
    extraValue = SystemsValue
      { systemsValueId = extraId
      , systemsValueRole = RuntimeRecord (recognizedRecordGrammar witness)
      , systemsStorageIdentity = Nothing
      }
    extraOperation = OpRuntimeCall
      { runtimeCallName = "materialize recognized " <> recognizedRecordGrammar witness
      , runtimeCallInputs = []
      , runtimeCallOutputs = [extraId]
      , runtimeCallSite = Nothing
      , runtimeCallDecision = recognizedRecordMaterializationDecision witness
      }
    addToFunction function = function
      { systemsFunctionValues = Map.insert
          extraId
          extraValue
          (systemsFunctionValues function)
      , systemsFunctionBlocks = Map.adjust
          (\blockValue -> blockValue
            { systemsBlockOps = extraOperation : systemsBlockOps blockValue })
          successBlock
          (systemsFunctionBlocks function)
      }

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
