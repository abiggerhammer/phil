{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Assurance
  ( ArtifactIdentity (..)
  , ArtifactRef (..)
  , Digest (..)
  )
import Phil.Assurance.Types (RevisionId (..))
import Phil.Core.Generic
  ( GenericEvidence (..)
  , GenericRequirement (..)
  , GenericRequirementDisposition (..)
  , GenericStaticParameterKey (..)
  , checkGenericInstantiation
  , deriveGenericApplicationIdentity
  , deriveGenericDischargeLineage
  , strictGenericInstantiationPolicy
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , DefinitionRevision (..)
  , InterfaceRevision (..)
  , SemanticForm (..)
  )
import Phil.Core.Syntax (Proposition (..))
import Phil.Examples.Phase1.StageClosureWitnesses
  ( uploadStageClosureBundle
  )
import Phil.Systems.CostAttribution
  ( CostAttributionStageBundle (..)
  )
import Phil.Systems.NextStageRequirement
  ( NextStageRequirementStageBundle (..)
  )
import Phil.Systems.Phase1Stage
  ( SystemsArtifactRevision (..)
  )
import Phil.Systems.RuntimeClaimBinding
  ( RuntimeClaimStageBundle (..)
  )
import Phil.Systems.RuntimePrimitiveReuse
  ( RuntimePrimitiveStageBundle (..)
  )
import Phil.Systems.StageClosure
  ( StageClosureBundle (..)
  )
import Phil.Systems.StagingEffect
  ( StagingEffectStageBundle (..)
  )
import Phil.Systems.TargetStrengthening
  ( DerivedObligation (..)
  , TargetStrengthening (..)
  , TargetStrengtheningStageBundle (..)
  , makeTargetStrengtheningStageBundle
  )
import Phil.Verification.ArtifactClosure
  ( ArtifactCertificationError (..)
  , certifiedApplicationSourceAssurance
  , certifyApplicationArtifact
  )
import Phil.Verification.GenericAssurance
  ( GenericApplicationAssurance
  , composeGenericApplicationAssurance
  , prepareReusableGenericBodyAssurance
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  closedSourceAssurance <- sourceAssuranceOrFail
  validStage <- stageOrFail uploadStageClosureBundle
  let changedStage = introduceUnsupportedTargetObligation validStage
      checks =
        [ ("closed source assurance plus valid exact StageClosure certifies",
            testValidArtifactCertification closedSourceAssurance validStage)
        , ("same exact closed source assurance rejects changed realization with unsupported target obligation",
            testSourceClosureIsNotArtifactClosure closedSourceAssurance validStage changedStage)
        , ("changed realization really carries an orphan derived obligation",
            testUnsupportedTargetObligation changedStage)
        , ("artifact identity mutation rejects without changing source assurance",
            testArtifactIdentityMutation closedSourceAssurance validStage)
        ]
  mapM_ report checks
  unless (and (map snd checks)) exitFailure
  where
    report (label, True) = putStrLn ("PASS: VER-010 " ++ label)
    report (label, False) = putStrLn ("FAIL: VER-010 " ++ label)

sourceAssuranceOrFail :: IO GenericApplicationAssurance
sourceAssuranceOrFail = case sourceAssurance of
  Left message -> failCase message
  Right assurance -> pure assurance

stageOrFail :: Either String a -> IO a
stageOrFail result = case result of
  Left message -> failCase message
  Right value -> pure value

failCase :: String -> IO a
failCase message = putStrLn ("FAIL: VER-010 " ++ message) >> exitFailure

sourceAssurance :: Either String GenericApplicationAssurance
sourceAssurance = do
  body <- mapLeft show $ prepareReusableGenericBodyAssurance
    genericDeclarationKey
    interfaceRevision
    definitionRevision
    publicRequirements
    bodyEvidenceArtifact
  application <- mapLeft show $ deriveGenericApplicationIdentity
    genericDeclarationKey
    interfaceRevision
    [(typeParameter, SemanticAtom "Blob")]
  record <- mapLeft show $ checkGenericInstantiation
    strictGenericInstantiationPolicy
    publicRequirements
    [ ( lawRequirement
      , GenericSatisfiedByEvidence GenericEvidence
          { genericEvidenceProposition = orderingLaw
          , genericEvidenceIdentity = "proof.ver010.source.application"
          }
      )
    ]
  let lineage = deriveGenericDischargeLineage
        application definitionRevision record
  mapLeft show $ composeGenericApplicationAssurance
    body publicRequirements lineage

testValidArtifactCertification
  :: GenericApplicationAssurance
  -> StageClosureBundle
  -> Bool
testValidArtifactCertification source stage =
  case certifyApplicationArtifact source stage of
    Left _ -> False
    Right certified -> certifiedApplicationSourceAssurance certified == source

testSourceClosureIsNotArtifactClosure
  :: GenericApplicationAssurance
  -> StageClosureBundle
  -> StageClosureBundle
  -> Bool
testSourceClosureIsNotArtifactClosure source validStage changedStage =
  case ( certifyApplicationArtifact source validStage
       , certifyApplicationArtifact source changedStage
       ) of
    (Right certified, Left (ArtifactCertificationStageClosureRejected _)) ->
      certifiedApplicationSourceAssurance certified == source
    _ -> False

testUnsupportedTargetObligation :: StageClosureBundle -> Bool
testUnsupportedTargetObligation stage =
  let target = targetStageFromNext (stageClosureNextStage stage)
      referencedDerived = Set.fromList
        [ revision
        | strengthening <- Map.elems (targetStrengtheningStageFacts target)
        , Just revision <- [targetStrengtheningDerivedObligation strengthening]
        ]
      registeredDerived = Map.keysSet
        (targetStrengtheningStageDerivedObligations target)
  in Set.member unsupportedTargetObligation registeredDerived
      && not (Set.member unsupportedTargetObligation referencedDerived)

testArtifactIdentityMutation
  :: GenericApplicationAssurance
  -> StageClosureBundle
  -> Bool
testArtifactIdentityMutation source validStage =
  let stale = validStage
        { stageClosureSystemsArtifactRevision =
            SystemsArtifactRevision "ver010.stale.systems-artifact" }
  in case ( certifyApplicationArtifact source validStage
          , certifyApplicationArtifact source stale
          ) of
      (Right certified, Left (ArtifactCertificationStageClosureRejected _)) ->
        certifiedApplicationSourceAssurance certified == source
      _ -> False

introduceUnsupportedTargetObligation
  :: StageClosureBundle
  -> StageClosureBundle
introduceUnsupportedTargetObligation bundle =
  let next = stageClosureNextStage bundle
      cost = nextStageRequirementStageBase next
      staging = costAttributionStageBase cost
      primitive = stagingEffectStageBase staging
      runtime = runtimePrimitiveStageBase primitive
      target = runtimeClaimStageBase runtime
      unsupported = DerivedObligation
        { derivedObligationRevision = unsupportedTargetObligation
        , derivedObligationIntroducedBy = Set.empty
        , derivedObligationSemanticSubjects = Set.singleton "ver010.target"
        , derivedObligationStatement =
            "unsupported realization-derived obligation must not certify"
        , derivedObligationAcceptanceRule =
            "requires an exact target-strengthening introducer"
        }
      changedObligations = Map.insert unsupportedTargetObligation unsupported
        (targetStrengtheningStageDerivedObligations target)
      changedTarget = makeTargetStrengtheningStageBundle
        (targetStrengtheningStageBase target)
        (targetStrengtheningStageFacts target)
        changedObligations
      changedRuntime = runtime { runtimeClaimStageBase = changedTarget }
      changedPrimitive = primitive { runtimePrimitiveStageBase = changedRuntime }
      changedStaging = staging { stagingEffectStageBase = changedPrimitive }
      changedCost = cost { costAttributionStageBase = changedStaging }
      changedNext = next { nextStageRequirementStageBase = changedCost }
  in bundle { stageClosureNextStage = changedNext }

targetStageFromNext
  :: NextStageRequirementStageBundle
  -> TargetStrengtheningStageBundle
targetStageFromNext =
  runtimeClaimStageBase
  . runtimePrimitiveStageBase
  . stagingEffectStageBase
  . costAttributionStageBase
  . nextStageRequirementStageBase

unsupportedTargetObligation :: RevisionId
unsupportedTargetObligation = RevisionId "ver010.target-strengthening.unsupported.v1"

genericDeclarationKey :: DeclarationKey
genericDeclarationKey = DeclarationKey "generic.map"

interfaceRevision :: InterfaceRevision
interfaceRevision = InterfaceRevision "generic.map.interface.v1"

definitionRevision :: DefinitionRevision
definitionRevision = DefinitionRevision "generic.map.definition.v1"

typeParameter :: GenericStaticParameterKey
typeParameter = GenericStaticParameterKey "T"

orderingLaw :: Proposition
orderingLaw = Atom "StrictWeakOrdering" []

lawRequirement :: GenericRequirement
lawRequirement = GenericPropositionRequirement orderingLaw

publicRequirements :: Set.Set GenericRequirement
publicRequirements = Set.singleton lawRequirement

bodyEvidenceArtifact :: ArtifactIdentity
bodyEvidenceArtifact = ArtifactIdentity
  { artifactReference = ArtifactRef "proof.generic.map.body.v1"
  , artifactDigest = Digest "sha256.generic.map.body.v1"
  }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
