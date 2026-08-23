{-# LANGUAGE OverloadedStrings #-}

module Phil.LLVM.VersionSessionChoiceLoweringProofCheck
  ( VersionSessionChoiceLoweringProofCheckError (..)
  , verifyVersionSessionChoiceLoweringProofWitness
  , verifyVersionSessionChoiceLoweringExactShape
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.LLVM.IR
import Phil.LLVM.VersionSessionChoice
import Phil.Systems.IR
import Phil.Systems.VersionChoiceOperands
import Phil.Systems.VersionSessionChoice

data VersionSessionChoiceLoweringProofCheckError
  = VersionLoweringProofSystemsError VersionChoiceOperandsError
  | VersionLoweringProofLLVMError VersionSessionChoiceLLVMError
  | VersionLoweringProofSystemsFunctionMissing Text
  | VersionLoweringProofSystemsBlockMissing Text BlockId
  | VersionLoweringProofLLVMFunctionMissing Text
  | VersionLoweringProofLLVMBlockMissing Text LLVMBlockId
  | VersionLoweringProofSystemsMaterializeMultiplicity Int
  | VersionLoweringProofSystemsProjectionMultiplicity Int
  | VersionLoweringProofSystemsUnsupportedSelectMultiplicity Int
  | VersionLoweringProofSystemsVersionSelectMultiplicity Int
  | VersionLoweringProofLLVMProjectionMultiplicity Int
  | VersionLoweringProofLLVMUnsupportedSelectMultiplicity Int
  | VersionLoweringProofLLVMVersionBindingMultiplicity Int
  | VersionLoweringProofLLVMVersionSelectMultiplicity Int
  | VersionLoweringProofLLVMClientBindingMultiplicity Int
  | VersionLoweringProofLLVMChooserMismatch LLVMTerminator
  | VersionLoweringProofLLVMClientOfferMismatch LLVMTerminator
  | VersionLoweringProofLLVMClientRefinementMismatch LLVMTerminator
  | VersionLoweringProofRenderedDeclarationMultiplicity Text Int
  deriving (Eq, Show)

verifyVersionSessionChoiceLoweringProofWitness
  :: VersionChoiceOperandsBundle
  -> LLVMArtifact
  -> Either VersionSessionChoiceLoweringProofCheckError ()
verifyVersionSessionChoiceLoweringProofWitness bundle llvmArtifact = do
  mapLeft VersionLoweringProofSystemsError $
    verifyVersionChoiceOperandsBundle bundle
  mapLeft VersionLoweringProofLLVMError $
    verifyVersionSessionChoiceTranslation bundle llvmArtifact
  verifyVersionSessionChoiceLoweringExactShape
    (versionChoiceOperandsArtifact bundle)
    (versionChoiceOperandsWitness bundle)
    llvmArtifact

verifyVersionSessionChoiceLoweringExactShape
  :: SystemsArtifact
  -> VersionChoiceOperandsWitness
  -> LLVMArtifact
  -> Either VersionSessionChoiceLoweringProofCheckError ()
verifyVersionSessionChoiceLoweringExactShape systemsArtifact operandsWitness llvmArtifact = do
  let versionWitness = phase0VersionSessionChoiceWitness
      systemsProgram = systemsArtifactProgram systemsArtifact
      serverName = versionChoiceServerFunction versionWitness
      clientName = versionChoiceClientFunction versionWitness

  server <- needSystemsFunction serverName systemsProgram
  hello <- needSystemsBlock serverName server (versionOperandsHelloCommitBlock operandsWitness)
  let materializeCount = length
        [ ()
        | OpRuntimeCall name inputs outputs _ decision <- systemsBlockOps hello
        , name == versionOperandsMaterializeCall operandsWitness
        , inputs == []
        , outputs == [versionOperandsHelloRecord operandsWitness]
        , decision == versionOperandsLoweringDecision operandsWitness
        ]
      projectionCount = length
        [ ()
        | OpRuntimeCall name inputs outputs _ decision <- systemsBlockOps hello
        , name == versionOperandsProjectionCall operandsWitness
        , inputs == [versionOperandsHelloRecord operandsWitness]
        , outputs == [versionOperandsHelloVersions operandsWitness]
        , decision == versionOperandsLoweringDecision operandsWitness
        ]
  requireCount VersionLoweringProofSystemsMaterializeMultiplicity 1 materializeCount
  requireCount VersionLoweringProofSystemsProjectionMultiplicity 1 projectionCount

  unsupported <- needSystemsBlock serverName server (versionChoiceServerUnsupportedBlock versionWitness)
  version <- needSystemsBlock serverName server (versionChoiceServerVersionBlock versionWitness)
  let unsupportedSelectCount = countSystemsSelect
        (versionChoiceServerTransport versionWitness)
        (versionChoiceUnsupportedLabel versionWitness)
        Nothing
        (versionChoiceSelectDecision versionWitness)
        (systemsBlockOps unsupported)
      versionSelectCount = countSystemsSelect
        (versionChoiceServerTransport versionWitness)
        (versionChoiceVersionLabel versionWitness)
        (Just (versionChoiceServerSelectedVersion versionWitness))
        (versionChoiceSelectDecision versionWitness)
        (systemsBlockOps version)
  requireCount VersionLoweringProofSystemsUnsupportedSelectMultiplicity 1 unsupportedSelectCount
  requireCount VersionLoweringProofSystemsVersionSelectMultiplicity 1 versionSelectCount

  let moduleValue = llvmArtifactModule llvmArtifact
      llvmServerName = serverName
      llvmClientName = clientName
      helloId = LLVMBlockId (unBlockId (versionOperandsHelloCommitBlock operandsWitness))
      chooserId = LLVMBlockId (unBlockId (versionOperandsChoiceBlock operandsWitness))
      unsupportedId = LLVMBlockId (unBlockId (versionChoiceServerUnsupportedBlock versionWitness))
      versionId = LLVMBlockId (unBlockId (versionChoiceServerVersionBlock versionWitness))
      clientOfferId = LLVMBlockId (unBlockId (versionChoiceClientOfferBlock versionWitness))
      clientVersionId = LLVMBlockId (unBlockId (versionChoiceClientVersionTarget versionWitness))
      clientUnsupportedId = LLVMBlockId (unBlockId (versionChoiceClientUnsupportedTarget versionWitness))
      serverSupported = unValueId (versionOperandsServerSupported operandsWitness)
      helloRecord = unValueId (versionOperandsHelloRecord operandsWitness)
      helloVersions = unValueId (versionOperandsHelloVersions operandsWitness)
      serverSelected = unValueId (versionOperandsSelectedVersion operandsWitness)
      serverTransport = unValueId (versionChoiceServerTransport versionWitness)
      clientTransport = unValueId (versionChoiceClientTransport versionWitness)
      clientSelected = unValueId (versionChoiceClientSelectedVersion versionWitness)

  llvmServer <- needLLVMFunction llvmServerName moduleValue
  llvmHello <- needLLVMBlock llvmServerName llvmServer helloId
  let llvmProjectionCount = length
        [ ()
        | LLVMOpaqueFieldProjection output input recordType field <- llvmBlockOps llvmHello
        , output == helloVersions
        , input == helloRecord
        , recordType == "Hello"
        , field == "versions"
        ]
  requireCount VersionLoweringProofLLVMProjectionMultiplicity 1 llvmProjectionCount

  chooser <- needLLVMBlock llvmServerName llvmServer chooserId
  let expectedChooser = LLVMChooseSupported
        serverSupported helloVersions serverSelected versionId unsupportedId
  if llvmBlockTerminator chooser == expectedChooser
    then pure ()
    else Left (VersionLoweringProofLLVMChooserMismatch (llvmBlockTerminator chooser))

  llvmUnsupported <- needLLVMBlock llvmServerName llvmServer unsupportedId
  let llvmUnsupportedCount = length
        [ () | LLVMUnsupportedSelect transport <- llvmBlockOps llvmUnsupported
             , transport == serverTransport ]
  requireCount VersionLoweringProofLLVMUnsupportedSelectMultiplicity 1 llvmUnsupportedCount

  llvmVersion <- needLLVMBlock llvmServerName llvmServer versionId
  let versionBindingCount = length
        [ () | LLVMChooseSupportedPayloadBinding selected <- llvmBlockOps llvmVersion
             , selected == serverSelected ]
      versionSelectorCount = length
        [ () | LLVMVersionSelect transport selected <- llvmBlockOps llvmVersion
             , transport == serverTransport
             , selected == serverSelected ]
  requireCount VersionLoweringProofLLVMVersionBindingMultiplicity 1 versionBindingCount
  requireCount VersionLoweringProofLLVMVersionSelectMultiplicity 1 versionSelectorCount

  llvmClient <- needLLVMFunction llvmClientName moduleValue
  clientOffer <- needLLVMBlock llvmClientName llvmClient clientOfferId
  let expectedOffer = LLVMVersionChoiceOffer
        clientTransport clientSelected clientVersionId clientUnsupportedId
  if llvmBlockTerminator clientOffer == expectedOffer
    then pure ()
    else Left (VersionLoweringProofLLVMClientOfferMismatch (llvmBlockTerminator clientOffer))

  clientVersion <- needLLVMBlock llvmClientName llvmClient clientVersionId
  let clientBindingCount = length
        [ () | LLVMVersionChoicePayloadBinding selected <- llvmBlockOps clientVersion
             , selected == clientSelected ]
  requireCount VersionLoweringProofLLVMClientBindingMultiplicity 1 clientBindingCount
  case llvmBlockTerminator clientVersion of
    LLVMVersionRefinement _ transport selected yes no
      | transport == clientTransport
          && selected == clientSelected
          && yes == LLVMBlockId (unBlockId (versionChoiceClientVersionSuccess versionWitness))
          && no == LLVMBlockId (unBlockId (versionChoiceClientVersionFailure versionWitness)) -> pure ()
    other -> Left (VersionLoweringProofLLVMClientRefinementMismatch other)

  mapM_ (requireRenderedOnce (llvmArtifactText llvmArtifact))
    [ "declare ptr @phil_record_Hello_get_versions(ptr)"
    , "declare i1 @phil_runtime_choose_supported(ptr, ptr, ptr)"
    , "declare void @phil_runtime_select_unsupported(ptr)"
    , "declare void @phil_runtime_select_version(ptr, i16)"
    , "declare i1 @phil_runtime_receive_version_choice(ptr, ptr)"
    , "declare i1 @phil_runtime_refine_selected_version(ptr, i16)"
    ]

countSystemsSelect
  :: ValueId
  -> Text
  -> Maybe ValueId
  -> DecisionId
  -> [SystemsOp]
  -> Int
countSystemsSelect transport label payload decision operations = length
  [ ()
  | OpSessionSelect actualTransport actualLabel actualPayload actualDecision <- operations
  , actualTransport == transport
  , actualLabel == label
  , actualPayload == payload
  , actualDecision == decision
  ]

needSystemsFunction
  :: Text
  -> SystemsProgram
  -> Either VersionSessionChoiceLoweringProofCheckError SystemsFunction
needSystemsFunction name program =
  maybe (Left (VersionLoweringProofSystemsFunctionMissing name)) Right
    (Map.lookup name (systemsProgramFunctions program))

needSystemsBlock
  :: Text
  -> SystemsFunction
  -> BlockId
  -> Either VersionSessionChoiceLoweringProofCheckError SystemsBlock
needSystemsBlock functionName function blockId =
  maybe (Left (VersionLoweringProofSystemsBlockMissing functionName blockId)) Right
    (Map.lookup blockId (systemsFunctionBlocks function))

needLLVMFunction
  :: Text
  -> LLVMModule
  -> Either VersionSessionChoiceLoweringProofCheckError LLVMFunction
needLLVMFunction name moduleValue =
  maybe (Left (VersionLoweringProofLLVMFunctionMissing name)) Right
    (Map.lookup name (llvmFunctions moduleValue))

needLLVMBlock
  :: Text
  -> LLVMFunction
  -> LLVMBlockId
  -> Either VersionSessionChoiceLoweringProofCheckError LLVMBlock
needLLVMBlock functionName function blockId =
  maybe (Left (VersionLoweringProofLLVMBlockMissing functionName blockId)) Right
    (Map.lookup blockId (llvmFunctionBlocks function))

requireCount :: (Int -> VersionSessionChoiceLoweringProofCheckError) -> Int -> Int -> Either VersionSessionChoiceLoweringProofCheckError ()
requireCount constructor expected actual
  | actual == expected = Right ()
  | otherwise = Left (constructor actual)

requireRenderedOnce :: Text -> Text -> Either VersionSessionChoiceLoweringProofCheckError ()
requireRenderedOnce rendered needle =
  let count = length (Text.breakOnAll needle rendered)
  in if count == 1
      then Right ()
      else Left (VersionLoweringProofRenderedDeclarationMultiplicity needle count)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
