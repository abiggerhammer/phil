{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.VersionSessionChoiceProofCheck
  ( VersionSessionChoiceProofCheckError (..)
  , verifyVersionSessionChoiceProofWitness
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Systems.IR
import Phil.Systems.VersionSessionChoice

data VersionSessionChoiceProofCheckError
  = VersionSessionChoiceBaseError VersionSessionChoiceError
  | VersionSessionChoiceFunctionMissing Text
  | VersionSessionChoiceBlockMissing Text BlockId
  | VersionSessionChoiceServerBinderPredecessors [BlockId]
  | VersionSessionChoiceClientBinderPredecessors [BlockId]
  | VersionSessionChoiceServerSelectMultiplicity Text BlockId Int
  | VersionSessionChoiceServerSelectMismatch Text BlockId [SystemsOp]
  | VersionSessionChoiceEndpointPayloadIdentityConflated ValueId
  deriving (Eq, Show)

verifyVersionSessionChoiceProofWitness
  :: SystemsArtifact
  -> VersionSessionChoiceWitness
  -> Either VersionSessionChoiceProofCheckError ()
verifyVersionSessionChoiceProofWitness artifact witness = do
  mapLeft VersionSessionChoiceBaseError $
    verifyVersionSessionChoiceWitness artifact witness
  let program = systemsArtifactProgram artifact
  server <- needFunction (versionChoiceServerFunction witness) program
  client <- needFunction (versionChoiceClientFunction witness) program

  let serverBinderPredecessors = predecessorsOf server (versionChoiceServerVersionBlock witness)
  if serverBinderPredecessors == [versionChoiceServerChoiceBlock witness]
    then pure ()
    else Left (VersionSessionChoiceServerBinderPredecessors serverBinderPredecessors)

  let clientBinderPredecessors = predecessorsOf client (versionChoiceClientVersionTarget witness)
  if clientBinderPredecessors == [versionChoiceClientOfferBlock witness]
    then pure ()
    else Left (VersionSessionChoiceClientBinderPredecessors clientBinderPredecessors)

  if versionChoiceServerSelectedVersion witness /= versionChoiceClientSelectedVersion witness
    then pure ()
    else Left (VersionSessionChoiceEndpointPayloadIdentityConflated
      (versionChoiceServerSelectedVersion witness))

  verifyExactOneSelect
    witness
    server
    (versionChoiceServerUnsupportedBlock witness)
    (versionChoiceUnsupportedLabel witness)
    Nothing
  verifyExactOneSelect
    witness
    server
    (versionChoiceServerVersionBlock witness)
    (versionChoiceVersionLabel witness)
    (Just (versionChoiceServerSelectedVersion witness))

verifyExactOneSelect
  :: VersionSessionChoiceWitness
  -> SystemsFunction
  -> BlockId
  -> Text
  -> Maybe ValueId
  -> Either VersionSessionChoiceProofCheckError ()
verifyExactOneSelect witness function blockId label payload = do
  blockValue <- needBlock (systemsFunctionName function) function blockId
  let selects =
        [ operation
        | operation@OpSessionSelect {} <- systemsBlockOps blockValue
        ]
      exact operation = case operation of
        OpSessionSelect transport actualLabel actualPayload actualDecision ->
          transport == versionChoiceServerTransport witness
            && actualLabel == label
            && actualPayload == payload
            && actualDecision == versionChoiceSelectDecision witness
        _ -> False
  if length selects /= 1
    then Left (VersionSessionChoiceServerSelectMultiplicity
      (systemsFunctionName function) blockId (length selects))
    else case selects of
      [operation] | exact operation -> pure ()
      _ -> Left (VersionSessionChoiceServerSelectMismatch
        (systemsFunctionName function) blockId (systemsBlockOps blockValue))

needFunction
  :: Text
  -> SystemsProgram
  -> Either VersionSessionChoiceProofCheckError SystemsFunction
needFunction functionName program =
  case Map.lookup functionName (systemsProgramFunctions program) of
    Nothing -> Left (VersionSessionChoiceFunctionMissing functionName)
    Just function -> Right function

needBlock
  :: Text
  -> SystemsFunction
  -> BlockId
  -> Either VersionSessionChoiceProofCheckError SystemsBlock
needBlock functionName function blockId =
  case Map.lookup blockId (systemsFunctionBlocks function) of
    Nothing -> Left (VersionSessionChoiceBlockMissing functionName blockId)
    Just blockValue -> Right blockValue

predecessorsOf :: SystemsFunction -> BlockId -> [BlockId]
predecessorsOf function target =
  [ systemsBlockId blockValue
  | blockValue <- Map.elems (systemsFunctionBlocks function)
  , target `elem` blockSuccessors blockValue
  ]

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
