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
    , test "SYS-GENERIC runtime sites retain exact source facts"
        uploadRuntimeFactsRetained
    , test "SYS-GENERIC Steve is accepted by generic producer/verifier"
        steveAccepted
    , test "SYS-GENERIC presentation rename is nonsemantic"
        presentationRenameNonsemantic
    , test "SYS-GENERIC one instance admits two legal realizations"
        twoLegalRealizations
    , test "SYS-GENERIC missing decision rejects"
        missingDecisionRejects
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

uploadRuntimeFactsRetained :: Either String ()
uploadRuntimeFactsRetained =
  mapM_ assertRuntimeFact
    [ "hello.complete_recognition"
    , "begin.complete_recognition"
    , "hello.policy"
    , "version.client_refinement"
    , "begin.policy"
    , "payload.exact_receive"
    , "payload.exact_send"
    , "digest.matches"
    , "storage.success"
    ]
  where
    contract = systemsArtifactStageContract
      (phase1StageSystemsArtifact uploadPhase1StageBundle)

    assertRuntimeFact factId =
      case
        [ factDisposition transfer
        | transfer <- stageFacts contract
        , factTransferId transfer == factId
        ] of
        [FactRuntimeRetained _] -> Right ()
        other -> Left
          ("source fact is not retained by its exact runtime site: "
            <> Text.unpack factId <> " -> " <> show other)

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
    "different explicit realization choices did not change Systems artifact revision"

missingDecisionRejects :: Either String ()
missingDecisionRejects = do
  checked <- checkedInstance "Sample"
  let missing = contextA { genericContextDecisions = Map.empty }
  case lowerGenericSystems checked sampleProgram missing of
    Left (GenericLoweringMissingDecision "sample.call") -> Right ()
    other -> Left
      ("missing decision was not rejected exactly: " <> show other)

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
  , coreProgramFacts = Map.fromList
      [ ("sample.fact.resource", Nothing)
      , ("sample.fact.failure", Nothing)
      ]
  }

sampleFunction :: CoreSystemsFunction
sampleFunction = CoreSystemsFunction
  { coreFunctionKey = "sample.function"
  , coreFunctionEntry = "entry"
  , coreFunctionValues = Map.fromList
      [ ("input", sampleValue "input" "SampleInput")
      , ("output", sampleValue "output" "SampleOutput")
      ]
  , coreFunctionBlocks = Map.singleton "entry"
      CoreSystemsBlock
        { coreBlockKey = "entry"
        , coreBlockOperations =
            [ CoreRuntimeCall "sample.call" "sample.semantic_call"
                ["input"] ["output"] Nothing
            ]
        , coreBlockTerminator = CoreSystemsEnd "success"
        }
  }

sampleValue :: Text.Text -> Text.Text -> CoreSystemsValue
sampleValue key semanticType = CoreSystemsValue
  { coreValueKey = key
  , coreValueRole = CoreRuntimeInput semanticType
  , coreValueStorageIdentity = Nothing
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
  , genericContextDecisions = Map.singleton "sample.call"
      GenericDecisionSpec
        { genericDecisionId = DecisionId ("lower.sample:" <> runtimeName)
        , genericDecisionSourceRepresentation = "sample semantic call"
        , genericDecisionTargetRepresentation = runtimeName
        , genericDecisionSemanticEntities = ["sample.call"]
        , genericDecisionAction = Retain
        , genericDecisionCostClass = Just SemanticRequired
        , genericDecisionCostShape =
            emptyCostShape { costFrequency = Just "per sample call" }
        , genericDecisionTargetPreconditions = []
        , genericDecisionAssumptions = []
        , genericDecisionDerivedObligations = []
        }
  , genericContextRuntimeSites = Map.empty
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
