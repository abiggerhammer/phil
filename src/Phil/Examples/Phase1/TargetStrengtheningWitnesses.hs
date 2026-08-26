{-# LANGUAGE OverloadedStrings #-}

module Phil.Examples.Phase1.TargetStrengtheningWitnesses
  ( uploadTargetStrengtheningStage
  , steveTargetStrengtheningStage
  , steveHostAbiStrengtheningRef
  , steveHostAbiDerivedObligation
  , completeTargetStrengtheningStage
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Phil.Assurance.Types (RevisionId)
import Phil.Examples.Phase1.AssumptionDependencyWitnesses
  ( steveAssumptionDependencyStage
  , uploadAssumptionDependencyStage
  )
import Phil.Examples.Phase1.SystemsWitnesses
  ( steveHostAbiDecisionId
  , steveHostAbiObligationRevision
  , steveHostAbiTargetPrecondition
  )
import Phil.Systems.AssumptionDependency
  ( AssumptionDependencyStageBundle
  )
import Phil.Systems.TargetStrengthening

uploadTargetStrengtheningStage :: TargetStrengtheningStageBundle
uploadTargetStrengtheningStage =
  completeTargetStrengtheningStage
    uploadAssumptionDependencyStage
    Map.empty
    Map.empty

steveTargetStrengtheningStage :: Either String TargetStrengtheningStageBundle
steveTargetStrengtheningStage = do
  base <- steveAssumptionDependencyStage
  pure (completeTargetStrengtheningStage
    base
    (Map.singleton steveHostAbiStrengtheningRef steveHostAbiStrengthening)
    (Map.singleton steveHostAbiObligationRevision steveHostAbiDerivedObligation))

steveHostAbiStrengtheningRef :: TargetPreconditionRef
steveHostAbiStrengtheningRef = TargetPreconditionRef
  { targetPreconditionDecision = steveHostAbiDecisionId
  , targetPreconditionRequirement = steveHostAbiTargetPrecondition
  }

steveHostAbiStrengthening :: TargetStrengthening
steveHostAbiStrengthening = TargetStrengthening
  { targetStrengtheningRef = steveHostAbiStrengtheningRef
  , targetStrengtheningSemanticSubjects = Set.singleton "steve.blob.byte-slice"
  , targetStrengtheningSourceAssurance = Set.empty
  , targetStrengtheningDerivedObligation = Just steveHostAbiObligationRevision
  }

steveHostAbiDerivedObligation :: DerivedObligation
steveHostAbiDerivedObligation = DerivedObligation
  { derivedObligationRevision = steveHostAbiObligationRevision
  , derivedObligationIntroducedBy = Set.singleton steveHostAbiStrengtheningRef
  , derivedObligationSemanticSubjects = Set.singleton "steve.blob.byte-slice"
  , derivedObligationStatement =
      "the selected host BlobProvider ABI preserves the semantic pointer/length pairing and represents every admitted byte length without range loss"
  , derivedObligationAcceptanceRule =
      "certified release requires checked target/ABI evidence for this exact host ABI profile before the realization is admitted"
  }

completeTargetStrengtheningStage
  :: AssumptionDependencyStageBundle
  -> Map TargetPreconditionRef TargetStrengthening
  -> Map RevisionId DerivedObligation
  -> TargetStrengtheningStageBundle
completeTargetStrengtheningStage = makeTargetStrengtheningStageBundle
