{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.LLVM
import Phil.Systems
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "version choice operands Systems candidate verifies" systemsCandidateVerifies
    , test "version choice LLVM translation verifies" translationVerifies
    , test "PHIL-LLVM-CERT-010 translation certification verifies" certificationVerifies
    , test "serverSupported is explicit runtime input with no local producer" explicitServerSupported
    , test "Hello.versions projection feeds explicit choose_supported operands" exactChooserOperands
    , test "LLVM chooser produces selected UInt16 before version select" exactLLVMChooser
    , test "client physical offer binds selected UInt16" exactClientOffer
    , test "wire ABI declarations are exact" exactRenderedABI
    , test "canonical version-choice target contains no unlowered version poison" noVersionPoison
    ]
  if and results then pure () else exitFailure

systemsCandidateVerifies :: Bool
systemsCandidateVerifies = case phase0VersionChoiceOperandsBundle of
  Right bundle -> verifyVersionChoiceOperandsBundle bundle == Right ()
  Left _ -> False

translationVerifies :: Bool
translationVerifies = withBundle $ \bundle ->
  let artifact = lowerSystemsVersionSessionChoice
        phase0VersionSessionChoiceLLVMTarget
        (versionChoiceOperandsArtifact bundle)
  in verifyVersionSessionChoiceTranslation bundle artifact == Right ()

certificationVerifies :: Bool
certificationVerifies =
  verifyPhase0VersionSessionChoiceLLVMCertification == Right ()

explicitServerSupported :: Bool
explicitServerSupported = withBundle $ \bundle ->
  let witness = versionChoiceOperandsWitness bundle
      program = systemsArtifactProgram (versionChoiceOperandsArtifact bundle)
  in case Map.lookup (versionOperandsServerFunction witness) (systemsProgramFunctions program) of
      Nothing -> False
      Just function ->
        case Map.lookup (versionOperandsServerSupported witness) (systemsFunctionValues function) of
          Just SystemsValue { systemsValueRole = RuntimeInput "SupportedVersions" } ->
            not (any (blockProduces (versionOperandsServerSupported witness))
              (Map.elems (systemsFunctionBlocks function)))
          _ -> False

exactChooserOperands :: Bool
exactChooserOperands = withBundle $ \bundle ->
  let witness = versionChoiceOperandsWitness bundle
      localWitness = phase0LocalRuntimeChoiceWitness
      program = systemsArtifactProgram (versionChoiceOperandsArtifact bundle)
  in doBool $ do
      function <- Map.lookup (versionOperandsServerFunction witness) (systemsProgramFunctions program)
      helloBlock <- Map.lookup (versionOperandsHelloCommitBlock witness) (systemsFunctionBlocks function)
      choiceBlock <- Map.lookup (versionOperandsChoiceBlock witness) (systemsFunctionBlocks function)
      let helloOpsOkay = case systemsBlockOps helloBlock of
            OpCommitIngress {} :
              OpRuntimeCall "materialize recognized Hello" [] [helloRecord] Nothing _
              : OpRuntimeCall "project recognized Hello.versions" [projectionInput] [helloVersions] Nothing _
              : _ -> helloRecord == versionOperandsHelloRecord witness
                  && projectionInput == versionOperandsHelloRecord witness
                  && helloVersions == versionOperandsHelloVersions witness
            _ -> False
          expectedArms = Map.fromList
            [ ("none", SystemsRuntimeChoiceArm Nothing (localChoiceNoneTarget localWitness))
            , ("some", SystemsRuntimeChoiceArm
                (Just (localChoiceSelectedVersion localWitness))
                (localChoiceSomeTarget localWitness))
            ]
          choiceOkay = systemsBlockTerminator choiceBlock == TermRuntimeChoice
            (localChoiceName localWitness)
            [versionOperandsServerSupported witness, versionOperandsHelloVersions witness]
            Nothing
            expectedArms
      pure (helloOpsOkay && choiceOkay)

exactLLVMChooser :: Bool
exactLLVMChooser = withLLVM $ \bundle artifact ->
  let operands = versionChoiceOperandsWitness bundle
      versionWitness = phase0VersionSessionChoiceWitness
      moduleValue = llvmArtifactModule artifact
  in doBool $ do
      server <- Map.lookup (versionChoiceServerFunction versionWitness) (llvmFunctions moduleValue)
      choice <- Map.lookup
        (LLVMBlockId (unBlockId (versionOperandsChoiceBlock operands)))
        (llvmFunctionBlocks server)
      versionBlock <- Map.lookup
        (LLVMBlockId (unBlockId (versionChoiceServerVersionBlock versionWitness)))
        (llvmFunctionBlocks server)
      let expectedTerm = LLVMChooseSupported
            (unValueId (versionOperandsServerSupported operands))
            (unValueId (versionOperandsHelloVersions operands))
            (unValueId (versionOperandsSelectedVersion operands))
            (LLVMBlockId (unBlockId (versionChoiceServerVersionBlock versionWitness)))
            (LLVMBlockId (unBlockId (versionChoiceServerUnsupportedBlock versionWitness)))
          expectedBinding = LLVMChooseSupportedPayloadBinding
            (unValueId (versionOperandsSelectedVersion operands))
          expectedSelect = LLVMVersionSelect
            (unValueId (versionChoiceServerTransport versionWitness))
            (unValueId (versionOperandsSelectedVersion operands))
      pure (llvmBlockTerminator choice == expectedTerm
        && expectedBinding `elem` llvmBlockOps versionBlock
        && expectedSelect `elem` llvmBlockOps versionBlock)

exactClientOffer :: Bool
exactClientOffer = withLLVM $ \_ artifact ->
  let witness = phase0VersionSessionChoiceWitness
      moduleValue = llvmArtifactModule artifact
  in doBool $ do
      client <- Map.lookup (versionChoiceClientFunction witness) (llvmFunctions moduleValue)
      offer <- Map.lookup
        (LLVMBlockId (unBlockId (versionChoiceClientOfferBlock witness)))
        (llvmFunctionBlocks client)
      target <- Map.lookup
        (LLVMBlockId (unBlockId (versionChoiceClientVersionTarget witness)))
        (llvmFunctionBlocks client)
      let expectedTerm = LLVMVersionChoiceOffer
            (unValueId (versionChoiceClientTransport witness))
            (unValueId (versionChoiceClientSelectedVersion witness))
            (LLVMBlockId (unBlockId (versionChoiceClientVersionTarget witness)))
            (LLVMBlockId (unBlockId (versionChoiceClientUnsupportedTarget witness)))
        expectedBinding = LLVMVersionChoicePayloadBinding
(unValueId (versionChoiceClientSelectedVersion witness))
        refinementOkay = case llvmBlockTerminator target of
LLVMVersionRefinement _ transport selected yes no ->
  transport == unValueId (versionChoiceClientTransport witness)
    && selected == unValueId (versionChoiceClientSelectedVersion witness)
    && yes == LLVMBlockId (unBlockId (versionChoiceClientVersionSuccess witness))
    && no == LLVMBlockId (unBlockId (versionChoiceClientVersionFailure witness))
_ -> False
      pure (llvmBlockTerminator offer == expectedTerm
        && expectedBinding `elem` llvmBlockOps target
        && refinementOkay)

exactRenderedABI :: Bool
exactRenderedABI = withLLVM $ \_ artifact ->
  let rendered = llvmArtifactText artifact
  in all (`Text.isInfixOf` rendered)
      [ "declare ptr @phil_record_Hello_get_versions(ptr)"
      , "declare i1 @phil_runtime_choose_supported(ptr, ptr, ptr)"
      , "declare void @phil_runtime_select_unsupported(ptr)"
      , "declare void @phil_runtime_select_version(ptr, i16)"
      , "declare i1 @phil_runtime_receive_version_choice(ptr, ptr)"
      , "declare i1 @phil_runtime_refine_selected_version(ptr, i16)"
      ]

noVersionPoison :: Bool
noVersionPoison = withLLVM $ \_ artifact ->
  let rendered = llvmArtifactText artifact
  in not (Text.isInfixOf "unlowered-session-select:version" rendered)
      && not (Text.isInfixOf "unlowered-session-select:unsupported" rendered)

blockProduces :: ValueId -> SystemsBlock -> Bool
blockProduces valueId blockValue =
  any produces (systemsBlockOps blockValue)
  || case systemsBlockTerminator blockValue of
      TermRuntimeChoice { runtimeChoiceArms = arms } ->
        any ((== Just valueId) . runtimeChoiceArmPayloadBinding) (Map.elems arms)
      TermSessionOffer { sessionOfferArms = arms } ->
        any ((== Just valueId) . choiceArmPayloadBinding) (Map.elems arms)
      _ -> False
  where
    produces operation = case operation of
      OpRuntimeCall { runtimeCallOutputs = outputs } -> valueId `elem` outputs
      OpCopy { copyTarget = output } -> output == valueId
      OpScalarLiteral { scalarLiteralOutput = output } -> output == valueId
      _ -> False

withBundle :: (VersionChoiceOperandsBundle -> Bool) -> Bool
withBundle action = case phase0VersionChoiceOperandsBundle of
  Left _ -> False
  Right bundle -> action bundle

withLLVM :: (VersionChoiceOperandsBundle -> LLVMArtifact -> Bool) -> Bool
withLLVM action = case phase0VersionChoiceOperandsBundle of
  Left _ -> False
  Right bundle -> action bundle (lowerSystemsVersionSessionChoice
    phase0VersionSessionChoiceLLVMTarget
    (versionChoiceOperandsArtifact bundle))

doBool :: Maybe Bool -> Bool
doBool = maybe False id

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
