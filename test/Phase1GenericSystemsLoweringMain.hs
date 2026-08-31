{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.Static
import Phil.Examples.Phase1.SystemsWitnesses
  ( steveHostAbiDecisionId
  , stevePhase1StageBundle
  , uploadPhase1StageBundle
  )
import Phil.Systems.GenericLowering
import Phil.Systems.IR
import Phil.Systems.Phase1Stage
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SYS-GENERIC upload is accepted by generic producer/verifier"
        uploadAccepted
    , test "SYS-GENERIC Steve is accepted by generic producer/verifier"
        steveAccepted
    , test "SYS-GENERIC presentation rename is nonsemantic"
        presentationRenameNonsemantic
    , test "SYS-GENERIC one instance admits two legal realizations"
        twoLegalRealizations
    , test "SYS-GENERIC missing operation realization rejects"
        missingOperationRejects
    , test "SYS-GENERIC target-only ABI choice remains explicit"
        steveAbiChoiceExplicit
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

uploadAccepted :: Either String ()
uploadAccepted = do
  mapLeft show (verifyPhase1StageBundle uploadPhase1StageBundle)
  let contract = systemsArtifactStageContract
        (phase1StageSystemsArtifact uploadPhase1StageBundle)
  assert
    ("phil.phase1.generic.core-to-systems.v1:"
      `Text.isPrefixOf` stageContractId contract)
    "upload StageContract did not come from generic Core-to-Systems producer"

steveAccepted :: Either String ()
steveAccepted = do
  bundle <- stevePhase1StageBundle
  mapLeft show (verifyPhase1StageBundle bundle)
  let contract = systemsArtifactStageContract (phase1StageSystemsArtifact bundle)
  assert
    ("phil.phase1.generic.core-to-systems.v1:"
      `Text.isPrefixOf` stageContractId contract)
    "Steve StageContract did not come from generic Core-to-Systems producer"

presentationRenameNonsemantic :: Either String ()
presentationRenameNonsemantic = do
  before <- checkedInstance "Before"
  after <- checkedInstance "After"
  bundleBefore <- mapLeft show (lowerGenericSystems before sampleProgram contextA)
  bundleAfter <- mapLeft show (lowerGenericSystems after sampleProgram contextA)
  assert
    (identityInstanceRevision (checkedArchitectureIdentity before)
      == identityInstanceRevision (checkedArchitectureIdentity after))
    "presentation rename changed ArchitectureInstance revision"
  assert
    (phase1StageSystemsArtifactRevision bundleBefore
      == phase1StageSystemsArtifactRevision bundleAfter)
    "presentation rename changed Systems artifact revision"
  assert
    (phase1StageContractRevision bundleBefore
      == phase1StageContractRevision bundleAfter)
    "presentation rename changed StageContract revision"

twoLegalRealizations :: Either String ()
twoLegalRealizations = do
  checked <- checkedInstance "Sample"
  bundleA <- mapLeft show (lowerGenericSystems checked sampleProgram contextA)
  bundleB <- mapLeft show (lowerGenericSystems checked sampleProgram contextB)
  assert
    (phase1StageInstanceRevision bundleA == phase1StageInstanceRevision bundleB)
    "representation choice changed source ArchitectureInstance revision"
  assert
    (phase1StageRealizationRevision bundleA /= phase1StageRealizationRevision bundleB)
    "different explicit realization choices did not change RealizationRevision"
  assert
    (phase1StageSystemsArtifactRevision bundleA
      /= phase1StageSystemsArtifactRevision bundleB)
    "different runtime realization did not change Systems artifact revision"

missingOperationRejects :: Either String ()
missingOperationRejects = do
  checked <- checkedInstance "Sample"
  let missing = contextA { genericContextOperations = Map.empty }
  case lowerGenericSystems checked sampleProgram missing of
    Left (GenericLoweringMissingOperationRealization "sample.call") -> Right ()
    other -> Left
      ("missing operation realization was not rejected exactly: " <> show other)

steveAbiChoiceExplicit :: Either String ()
steveAbiChoiceExplicit = do
  bundle <- stevePhase1StageBundle
  let ledger = systemsArtifactLoweringLedger (phase1StageSystemsArtifact bundle)
  assert
    (Map.member steveHostAbiDecisionId (loweringLedgerDecisions ledger))
    "Steve target-only host ABI choice disappeared from generic lowering ledger"

sampleProgram :: CoreSystemsProgram
sampleProgram = CoreSystemsProgram
  { coreProgramLabel = "Sample"
  , coreProgramProfile = CheckedRuntime
  , coreProgramFunctions = Map.singleton "sample.function" sampleFunction
  , coreProgramFacts = Set.fromList
      [ "sample.fact.resource"
      , "sample.fact.failure"
      ]
  }

sampleFunction :: CoreSystemsFunction
sampleFunction = CoreSystemsFunction
  { coreFunctionKey = "sample.function"
  , coreFunctionEntry = "entry"
  , coreFunctionValues = Map.fromList
      [ ("input", CoreInputValue "SampleInput")
      , ("output", CoreInputValue "SampleOutput")
      ]
  , coreFunctionBlocks = Map.fromList
      [ ("entry", CoreSystemsBlock
          { coreBlockKey = "entry"
          , coreBlockOperations =
              [CoreSystemsCall "sample.call" ["input"] ["output"]]
          , coreBlockTerminator = CoreSystemsEnd "success"
          })
      ]
  }

contextA :: GenericRealizationContext
contextA = sampleContext
  "context.sample.a"
  "SampleRuntime.call.a"
  "realization:sample.a"

contextB :: GenericRealizationContext
contextB = sampleContext
  "context.sample.b"
  "SampleRuntime.call.b"
  "realization:sample.b"

sampleContext
  :: Text.Text
  -> Text.Text
  -> Text.Text
  -> GenericRealizationContext
sampleContext revision runtimeName realizationRef = GenericRealizationContext
  { genericContextRevision = revision
  , genericContextSemantics = SemanticRecord (Map.fromList
      [ ("target", SemanticAtom "test-host")
      , ("runtime", SemanticAtom runtimeName)
      ])
  , genericContextVerifierProfile = "phase1-stage-verifier.v1"
  , genericContextRealizationRefs = Set.singleton realizationRef
  , genericContextQualificationRefs = Set.empty
  , genericContextAssumptions = Set.empty
  , genericContextOperations = Map.singleton "sample.call"
      RealizedOperation
        { realizedOperationRuntimeName = runtimeName
        , realizedOperationQualificationRefs = Set.empty
        , realizedOperationAssumptions = Set.empty
        , realizedOperationCostClass = SemanticRequired
        , realizedOperationCostShape = emptyCostShape
        , realizedOperationTargetPreconditions = []
        , realizedOperationDerivedObligations = []
        }
  , genericContextTargetChoices = []
  }

checkedInstance :: Text.Text -> Either String CheckedArchitectureInstance
checkedInstance displayName = do
  graph <- mapLeft show $ instantiateArchitecture
    (InstanceKey "instance.sample")
    ArchitectureNodeSpec
      { architectureNodeDeclaration =
          deriveDeclarationIdentity DeclarationDescriptor
            { declarationPresentation =
                DeclarationPresentation displayName ["phase1", "test"]
            , declarationKey = DeclarationKey "decl.sample"
            , declarationInterfaceSemantics =
                SemanticAtom "sample.checked-core.interface"
            , declarationDefinitionSemantics =
                coreSystemsProgramSemanticForm sampleProgram
            }
      , architectureNodeStaticBindings = Map.empty
      , architectureNodeRequirements = []
      , architectureNodeChildren = []
      , architectureNodeReferences = []
      }
  maybe
    (Left "sample root instance missing")
    Right
    (lookupArchitectureInstance (InstanceKey "instance.sample") graph)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
