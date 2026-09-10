{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler.RuntimeChoiceABI
  ( RuntimeChoiceABICarrier (..)
  , RuntimeChoiceABIInput (..)
  , RuntimeChoiceABIArm (..)
  , RuntimeChoiceABISite (..)
  , RuntimeChoiceABIPlan
  , runtimeChoiceABIPlanDigest
  , runtimeChoiceABISites
  , RuntimeChoiceABIError (..)
  , certifyRuntimeChoiceABIPlan
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (Digest (..), digestText)
import Phil.Compiler.RuntimeChoicePayload
import Phil.Systems.GenericLowering (CoreSystemsProgram)
import Phil.Systems.IR
import Phil.Systems.Phase1Stage

-- | Target-independent carrier classes for the qualified-provider ABI seam.
-- These preserve semantic representation choices without yet selecting an LLVM
-- layout.  A later target lowering must refine these carriers explicitly.
data RuntimeChoiceABICarrier
  = ABITransportHandle
  | ABIPendingIngress Text
  | ABIFrameOwner Text
  | ABIOwnedBuffer Text
  | ABIBorrowedSlice ValueId
  | ABIRuntimeScalar Text
  | ABIRuntimeInput Text
  | ABIRuntimeOpaque Text
  | ABITypedScalar ScalarType
  | ABIRuntimeRecord Text
  | ABIDiagnosticState Text
  deriving (Eq, Ord, Show)

data RuntimeChoiceABIInput = RuntimeChoiceABIInput
  { runtimeChoiceABIInputValue :: ValueId
  , runtimeChoiceABIInputCarrier :: RuntimeChoiceABICarrier
  }
  deriving (Eq, Ord, Show)

-- | Stable arm tag plus the optional value produced by that arm.  Tags are
-- assigned from the canonical ascending arm-label order, making the convention
-- deterministic and independent of map construction order.
data RuntimeChoiceABIArm = RuntimeChoiceABIArm
  { runtimeChoiceABIArmTag :: Int
  , runtimeChoiceABIArmTarget :: BlockId
  , runtimeChoiceABIArmPayload :: Maybe (ValueId, RuntimeChoiceABICarrier)
  }
  deriving (Eq, Ord, Show)

data RuntimeChoiceABISite = RuntimeChoiceABISite
  { runtimeChoiceABISiteIdentity :: RuntimeChoiceSite
  , runtimeChoiceABIName :: Text
  , runtimeChoiceABIInputs :: [RuntimeChoiceABIInput]
  , runtimeChoiceABIArms :: Map Text RuntimeChoiceABIArm
  }
  deriving (Eq, Ord, Show)

-- | Opaque ABI certificate.  Its digest binds the exact Systems artifact, the
-- certified checked-Core payload plan, and the normalized ABI site records.
data RuntimeChoiceABIPlan = RuntimeChoiceABIPlan
  Digest
  (Map RuntimeChoiceSite RuntimeChoiceABISite)
  deriving (Eq, Show)

runtimeChoiceABIPlanDigest :: RuntimeChoiceABIPlan -> Digest
runtimeChoiceABIPlanDigest (RuntimeChoiceABIPlan planDigest _) = planDigest

runtimeChoiceABISites
  :: RuntimeChoiceABIPlan
  -> Map RuntimeChoiceSite RuntimeChoiceABISite
runtimeChoiceABISites (RuntimeChoiceABIPlan _ sites) = sites

data RuntimeChoiceABIError
  = RuntimeChoiceABIStageRejected Phase1StageVerificationError
  | RuntimeChoiceABIPayloadPlanRejected RuntimeChoicePayloadError
  | RuntimeChoiceABIFunctionMissing RuntimeChoiceSite
  | RuntimeChoiceABIBlockMissing RuntimeChoiceSite
  | RuntimeChoiceABINotRuntimeChoice RuntimeChoiceSite
  | RuntimeChoiceABIArmDomainMismatch RuntimeChoiceSite (Set.Set Text) (Set.Set Text)
  | RuntimeChoiceABIArmTargetMismatch RuntimeChoiceSite Text BlockId BlockId
  | RuntimeChoiceABIArmPayloadMismatch RuntimeChoiceSite Text (Maybe ValueId) (Maybe ValueId)
  | RuntimeChoiceABIValueMissing RuntimeChoiceSite ValueId
  deriving (Eq, Show)

certifyRuntimeChoiceABIPlan
  :: CoreSystemsProgram
  -> RuntimeChoicePayloadPlan
  -> Phase1StageBundle
  -> Either RuntimeChoiceABIError RuntimeChoiceABIPlan
certifyRuntimeChoiceABIPlan core payloadPlan stage = do
  mapLeft RuntimeChoiceABIStageRejected (verifyPhase1StageBundle stage)
  _ <- mapLeft RuntimeChoiceABIPayloadPlanRejected $
    certifyRuntimeChoicePayloadPlan core
      (Map.elems (runtimeChoicePayloadPlanSpecs payloadPlan))
  sites <- Map.traverseWithKey (certifySite program)
    (runtimeChoicePayloadPlanSpecs payloadPlan)
  let artifactDigest = systemsArtifactDigest artifact
      payloadDigest = runtimeChoicePayloadPlanDigest payloadPlan
      material = Text.intercalate "|"
        [ "systems=" <> unDigest artifactDigest
        , "payload-plan=" <> unDigest payloadDigest
        , "sites=" <> Text.intercalate ";" (map renderSite (Map.toAscList sites))
        ]
  pure (RuntimeChoiceABIPlan (digestText material) sites)
  where
    artifact = phase1StageSystemsArtifact stage
    program = systemsArtifactProgram artifact

certifySite
  :: SystemsProgram
  -> RuntimeChoiceSite
  -> RuntimeChoicePayloadSpec
  -> Either RuntimeChoiceABIError RuntimeChoiceABISite
certifySite program site spec = do
  function <- maybe
    (Left (RuntimeChoiceABIFunctionMissing site))
    Right
    (Map.lookup (runtimeChoiceSiteFunction site) (systemsProgramFunctions program))
  blockValue <- maybe
    (Left (RuntimeChoiceABIBlockMissing site))
    Right
    (Map.lookup (BlockId (runtimeChoiceSiteBlock site)) (systemsFunctionBlocks function))
  (name, inputValues, systemsArms) <- case systemsBlockTerminator blockValue of
    TermRuntimeChoice choiceName inputs _ arms -> Right (choiceName, inputs, arms)
    _ -> Left (RuntimeChoiceABINotRuntimeChoice site)
  inputs <- mapM (certifyInput site function) inputValues
  let plannedArms = runtimeChoicePayloadArms spec
      systemsDomain = Map.keysSet systemsArms
      plannedDomain = Map.keysSet plannedArms
  if systemsDomain == plannedDomain
    then Right ()
    else Left (RuntimeChoiceABIArmDomainMismatch site systemsDomain plannedDomain)
  arms <- Map.fromAscList <$> mapM (certifyArm site function systemsArms)
    (zip [0 ..] (Map.toAscList plannedArms))
  pure RuntimeChoiceABISite
    { runtimeChoiceABISiteIdentity = site
    , runtimeChoiceABIName = name
    , runtimeChoiceABIInputs = inputs
    , runtimeChoiceABIArms = arms
    }

certifyInput
  :: RuntimeChoiceSite
  -> SystemsFunction
  -> ValueId
  -> Either RuntimeChoiceABIError RuntimeChoiceABIInput
certifyInput site function valueId = do
  value <- needValue site function valueId
  pure RuntimeChoiceABIInput
    { runtimeChoiceABIInputValue = valueId
    , runtimeChoiceABIInputCarrier = carrierFor value
    }

certifyArm
  :: RuntimeChoiceSite
  -> SystemsFunction
  -> Map Text SystemsRuntimeChoiceArm
  -> (Int, (Text, RuntimeChoicePayloadArm))
  -> Either RuntimeChoiceABIError (Text, RuntimeChoiceABIArm)
certifyArm site function systemsArms (tag, (label, planned)) = do
  let existing = systemsArms Map.! label
      expectedTarget = runtimeChoiceArmTarget existing
      plannedTarget = BlockId (runtimeChoicePayloadTarget planned)
      expectedPayload = runtimeChoiceArmPayloadBinding existing
      plannedPayload = ValueId <$> runtimeChoicePayloadValue planned
  if expectedTarget == plannedTarget
    then Right ()
    else Left (RuntimeChoiceABIArmTargetMismatch site label expectedTarget plannedTarget)
  if expectedPayload == plannedPayload
    then Right ()
    else Left (RuntimeChoiceABIArmPayloadMismatch site label expectedPayload plannedPayload)
  payload <- case plannedPayload of
    Nothing -> Right Nothing
    Just valueId -> do
      value <- needValue site function valueId
      Right (Just (valueId, carrierFor value))
  pure
    ( label
    , RuntimeChoiceABIArm
        { runtimeChoiceABIArmTag = tag
        , runtimeChoiceABIArmTarget = plannedTarget
        , runtimeChoiceABIArmPayload = payload
        }
    )

needValue
  :: RuntimeChoiceSite
  -> SystemsFunction
  -> ValueId
  -> Either RuntimeChoiceABIError SystemsValue
needValue site function valueId = maybe
  (Left (RuntimeChoiceABIValueMissing site valueId))
  Right
  (Map.lookup valueId (systemsFunctionValues function))

carrierFor :: SystemsValue -> RuntimeChoiceABICarrier
carrierFor value = case systemsValueRole value of
  TransportHandle -> ABITransportHandle
  PendingIngress grammar -> ABIPendingIngress grammar
  FrameOwner grammar -> ABIFrameOwner grammar
  OwnedBuffer semanticType -> ABIOwnedBuffer semanticType
  BorrowedSlice owner -> ABIBorrowedSlice owner
  RuntimeScalar scalarType -> ABIRuntimeScalar scalarType
  RuntimeInput inputType -> ABIRuntimeInput inputType
  RuntimeOpaque opaqueType -> ABIRuntimeOpaque opaqueType
  TypedScalar scalarType -> ABITypedScalar scalarType
  RuntimeRecord recordType -> ABIRuntimeRecord recordType
  DiagnosticState stateType -> ABIDiagnosticState stateType

renderSite :: (RuntimeChoiceSite, RuntimeChoiceABISite) -> Text
renderSite (site, abiSite) = Text.intercalate ","
  [ "function=" <> atom (runtimeChoiceSiteFunction site)
  , "block=" <> atom (runtimeChoiceSiteBlock site)
  , "name=" <> atom (runtimeChoiceABIName abiSite)
  , "inputs=" <> Text.intercalate "/" (map renderInput (runtimeChoiceABIInputs abiSite))
  , "arms=" <> Text.intercalate "/"
      [ atom label <> ":" <> Text.pack (show (runtimeChoiceABIArmTag arm))
          <> ":" <> atom (unBlockId (runtimeChoiceABIArmTarget arm))
          <> ":" <> maybe "none" renderPayload (runtimeChoiceABIArmPayload arm)
      | (label, arm) <- Map.toAscList (runtimeChoiceABIArms abiSite)
      ]
  ]

renderInput :: RuntimeChoiceABIInput -> Text
renderInput input =
  atom (unValueId (runtimeChoiceABIInputValue input))
    <> ":" <> atom (Text.pack (show (runtimeChoiceABIInputCarrier input)))

renderPayload :: (ValueId, RuntimeChoiceABICarrier) -> Text
renderPayload (valueId, carrier) =
  atom (unValueId valueId) <> ":" <> atom (Text.pack (show carrier))

atom :: Text -> Text
atom value = Text.pack (show (Text.length value)) <> ":" <> value

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
