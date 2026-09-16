{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler.RuntimeChoicePayload
  ( RuntimeChoiceSite (..)
  , RuntimeChoicePayloadArm (..)
  , RuntimeChoicePayloadSpec (..)
  , RuntimeChoicePayloadPlan
  , runtimeChoicePayloadPlanDigest
  , runtimeChoicePayloadPlanSpecs
  , RuntimeChoicePayloadError (..)
  , certifyRuntimeChoicePayloadPlan
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (Digest, digestText)
import Phil.Core.Static (canonicalSemanticForm)
import Phil.Systems.GenericLowering
  ( CoreSystemsBlock (..)
  , CoreSystemsFunction (..)
  , CoreSystemsProgram (..)
  , CoreSystemsTerminator (..)
  , coreSystemsProgramSemanticForm
  )

-- | Stable checked-Core location for a runtime choice.  This is structural
-- identity, not a witness/program name: the function and block keys are already
-- part of the CoreSystemsProgram semantic form.
data RuntimeChoiceSite = RuntimeChoiceSite
  { runtimeChoiceSiteFunction :: Text
  , runtimeChoiceSiteBlock :: Text
  }
  deriving (Eq, Ord, Show)

-- | Exact payload disposition for one runtime-choice arm.  'Nothing' means the
-- arm carries no value into the successor (or its source payload is explicitly
-- erased before Systems); 'Just value' names the already-declared checked-Core
-- value that must receive the runtime result.
data RuntimeChoicePayloadArm = RuntimeChoicePayloadArm
  { runtimeChoicePayloadTarget :: Text
  , runtimeChoicePayloadValue :: Maybe Text
  }
  deriving (Eq, Ord, Show)

data RuntimeChoicePayloadSpec = RuntimeChoicePayloadSpec
  { runtimeChoicePayloadSite :: RuntimeChoiceSite
  , runtimeChoicePayloadArms :: Map Text RuntimeChoicePayloadArm
  }
  deriving (Eq, Ord, Show)

-- | Opaque, content-bound payload plan.  The digest binds the complete checked
-- Core semantic identity and the normalized site/arm/value mapping, so a later
-- lowering stage cannot reuse a plan against a different Core program.
data RuntimeChoicePayloadPlan = RuntimeChoicePayloadPlan
  Digest
  (Map RuntimeChoiceSite RuntimeChoicePayloadSpec)
  deriving (Eq, Show)

runtimeChoicePayloadPlanDigest :: RuntimeChoicePayloadPlan -> Digest
runtimeChoicePayloadPlanDigest (RuntimeChoicePayloadPlan planDigest _) = planDigest

runtimeChoicePayloadPlanSpecs
  :: RuntimeChoicePayloadPlan
  -> Map RuntimeChoiceSite RuntimeChoicePayloadSpec
runtimeChoicePayloadPlanSpecs (RuntimeChoicePayloadPlan _ specs) = specs

data RuntimeChoicePayloadError
  = RuntimeChoicePayloadDuplicateSite RuntimeChoiceSite
  | RuntimeChoicePayloadFunctionMissing RuntimeChoiceSite
  | RuntimeChoicePayloadBlockMissing RuntimeChoiceSite
  | RuntimeChoicePayloadNotRuntimeChoice RuntimeChoiceSite
  | RuntimeChoicePayloadArmDomainMismatch RuntimeChoiceSite (Set.Set Text) (Set.Set Text)
  | RuntimeChoicePayloadTargetMismatch RuntimeChoiceSite Text Text Text
  | RuntimeChoicePayloadValueMissing RuntimeChoiceSite Text Text
  deriving (Eq, Show)

certifyRuntimeChoicePayloadPlan
  :: CoreSystemsProgram
  -> [RuntimeChoicePayloadSpec]
  -> Either RuntimeChoicePayloadError RuntimeChoicePayloadPlan
certifyRuntimeChoicePayloadPlan program rawSpecs = do
  specs <- collectSpecs Map.empty rawSpecs
  mapM_ (validateSpec program) (Map.elems specs)
  let payload = Text.intercalate "|"
        [ "core=" <> canonicalSemanticForm (coreSystemsProgramSemanticForm program)
        , "sites=" <> Text.intercalate ";" (map renderSpec (Map.toAscList specs))
        ]
  pure (RuntimeChoicePayloadPlan (digestText payload) specs)

collectSpecs
  :: Map RuntimeChoiceSite RuntimeChoicePayloadSpec
  -> [RuntimeChoicePayloadSpec]
  -> Either RuntimeChoicePayloadError (Map RuntimeChoiceSite RuntimeChoicePayloadSpec)
collectSpecs result [] = Right result
collectSpecs result (spec : rest)
  | Map.member site result = Left (RuntimeChoicePayloadDuplicateSite site)
  | otherwise = collectSpecs (Map.insert site spec result) rest
  where
    site = runtimeChoicePayloadSite spec

validateSpec
  :: CoreSystemsProgram
  -> RuntimeChoicePayloadSpec
  -> Either RuntimeChoicePayloadError ()
validateSpec program spec = do
  function <- maybe
    (Left (RuntimeChoicePayloadFunctionMissing site))
    Right
    (Map.lookup (runtimeChoiceSiteFunction site) (coreProgramFunctions program))
  blockValue <- maybe
    (Left (RuntimeChoicePayloadBlockMissing site))
    Right
    (Map.lookup (runtimeChoiceSiteBlock site) (coreFunctionBlocks function))
  controlArms <- case coreBlockTerminator blockValue of
    CoreSystemsRuntimeChoice _ _ _ arms -> Right arms
    _ -> Left (RuntimeChoicePayloadNotRuntimeChoice site)
  let plannedArms = runtimeChoicePayloadArms spec
      expectedDomain = Map.keysSet controlArms
      actualDomain = Map.keysSet plannedArms
  if expectedDomain == actualDomain
    then Right ()
    else Left (RuntimeChoicePayloadArmDomainMismatch site expectedDomain actualDomain)
  mapM_ (validateArm function controlArms) (Map.toAscList plannedArms)
  where
    site = runtimeChoicePayloadSite spec

    validateArm function controlArms (label, arm) = do
      let expectedTarget = controlArms Map.! label
          actualTarget = runtimeChoicePayloadTarget arm
      if expectedTarget == actualTarget
        then Right ()
        else Left (RuntimeChoicePayloadTargetMismatch
          site label expectedTarget actualTarget)
      case runtimeChoicePayloadValue arm of
        Nothing -> Right ()
        Just value
          | Map.member value (coreFunctionValues function) -> Right ()
          | otherwise -> Left (RuntimeChoicePayloadValueMissing site label value)

renderSpec :: (RuntimeChoiceSite, RuntimeChoicePayloadSpec) -> Text
renderSpec (site, spec) = Text.intercalate ","
  [ "function=" <> atom (runtimeChoiceSiteFunction site)
  , "block=" <> atom (runtimeChoiceSiteBlock site)
  , "arms=" <> Text.intercalate "/"
      [ atom label <> ":" <> atom (runtimeChoicePayloadTarget arm)
          <> ":" <> maybe "none" atom (runtimeChoicePayloadValue arm)
      | (label, arm) <- Map.toAscList (runtimeChoicePayloadArms spec)
      ]
  ]

atom :: Text -> Text
atom value = Text.pack (show (Text.length value)) <> ":" <> value
