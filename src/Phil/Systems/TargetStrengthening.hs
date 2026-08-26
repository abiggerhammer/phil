{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.TargetStrengthening
  ( TargetStrengtheningStageRevision (..)
  , TargetPreconditionRef (..)
  , TargetStrengthening (..)
  , DerivedObligation (..)
  , TargetStrengtheningStageBundle (..)
  , TargetStrengtheningVerificationError (..)
  , deriveTargetPreconditionRefs
  , deriveTargetStrengtheningStageRevision
  , makeTargetStrengtheningStageBundle
  , verifyTargetStrengtheningStageBundle
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (RevisionId (..))
import Phil.Core.Static
  ( SemanticForm (..)
  , canonicalSemanticForm
  )
import Phil.Systems.AssumptionDependency
  ( AssumptionDependencyStageBundle (..)
  , AssumptionDependencyStageRevision (..)
  , AssumptionDependencyVerificationError
  , verifyAssumptionDependencyStageBundle
  )
import Phil.Systems.EvidenceErasure
  ( EvidenceErasureStageBundle (..)
  )
import Phil.Systems.EvidenceSubjectTransfer
  ( EvidenceTransferStageBundle (..)
  )
import Phil.Systems.IR
  ( DecisionId (..)
  , LoweringDecision (..)
  , LoweringLedger (..)
  , StageContract (..)
  , SystemsArtifact (..)
  )
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  )
import Phil.Systems.SubjectCorrespondence
  ( SubjectStageBundle (..)
  )

newtype TargetStrengtheningStageRevision = TargetStrengtheningStageRevision
  { unTargetStrengtheningStageRevision :: Text
  }
  deriving (Eq, Ord, Show)

-- | One exact target precondition introduced by one exact lowering decision.
-- The requirement text is identity-bearing at this bounded stage because the
-- predecessor IR already stores target preconditions as canonical text atoms.
data TargetPreconditionRef = TargetPreconditionRef
  { targetPreconditionDecision :: DecisionId
  , targetPreconditionRequirement :: Text
  }
  deriving (Eq, Ord, Show)

-- | StageContract accounting for a selected target/realization fact.  Source
-- assurance may be cited only by exact obligation revisions already attached to
-- the same lowering decision.  If none exists, the target fact must name a
-- derived obligation rather than being retroactively attributed to the source.
data TargetStrengthening = TargetStrengthening
  { targetStrengtheningRef :: TargetPreconditionRef
  , targetStrengtheningSemanticSubjects :: Set Text
  , targetStrengtheningSourceAssurance :: Set RevisionId
  , targetStrengtheningDerivedObligation :: Maybe RevisionId
  }
  deriving (Eq, Ord, Show)

-- | SYS-014's bounded DerivedObligation schema follows the governing
-- Systems/StageContract contract: exact revision, exact introducers, semantic
-- subjects, the proposition/refinement statement, and an explicit acceptance
-- rule.  Assurance disposition remains a later closure concern.
data DerivedObligation = DerivedObligation
  { derivedObligationRevision :: RevisionId
  , derivedObligationIntroducedBy :: Set TargetPreconditionRef
  , derivedObligationSemanticSubjects :: Set Text
  , derivedObligationStatement :: Text
  , derivedObligationAcceptanceRule :: Text
  }
  deriving (Eq, Ord, Show)

data TargetStrengtheningStageBundle = TargetStrengtheningStageBundle
  { targetStrengtheningStageBase :: AssumptionDependencyStageBundle
  , targetStrengtheningStageRevision :: TargetStrengtheningStageRevision
  , targetStrengtheningStageFacts :: Map TargetPreconditionRef TargetStrengthening
  , targetStrengtheningStageDerivedObligations :: Map RevisionId DerivedObligation
  }
  deriving (Eq, Show)

data TargetStrengtheningVerificationError
  = TargetStrengtheningBaseError AssumptionDependencyVerificationError
  | TargetStrengtheningStageRevisionMismatch
      TargetStrengtheningStageRevision TargetStrengtheningStageRevision
  | TargetStrengtheningDomainMismatch
      (Set TargetPreconditionRef) (Set TargetPreconditionRef)
  | TargetStrengtheningMapKeyMismatch
      TargetPreconditionRef TargetPreconditionRef
  | TargetStrengtheningEmptyRequirement TargetPreconditionRef
  | TargetStrengtheningUnknownSourceAssurance
      TargetPreconditionRef (Set RevisionId)
  | TargetStrengtheningMissingDerivedObligation TargetPreconditionRef
  | TargetStrengtheningEmptyDerivedRevision TargetPreconditionRef
  | TargetStrengtheningDecisionDerivedMismatch
      DecisionId (Set RevisionId) (Set RevisionId)
  | TargetStrengtheningStageDerivedMismatch
      (Set RevisionId) (Set RevisionId)
  | DerivedObligationRegistryDomainMismatch
      (Set RevisionId) (Set RevisionId)
  | DerivedObligationMapKeyMismatch RevisionId RevisionId
  | DerivedObligationIntroducedByMismatch
      RevisionId (Set TargetPreconditionRef) (Set TargetPreconditionRef)
  | DerivedObligationSubjectMismatch
      RevisionId (Set Text) (Set Text)
  | DerivedObligationEmptyStatement RevisionId
  | DerivedObligationEmptyAcceptanceRule RevisionId
  deriving (Eq, Show)

deriveTargetPreconditionRefs
  :: AssumptionDependencyStageBundle
  -> Set TargetPreconditionRef
deriveTargetPreconditionRefs bundle = Set.fromList
  [ TargetPreconditionRef decisionKey requirement
  | (decisionKey, decision) <- Map.toAscList (baseDecisions bundle)
  , requirement <- loweringTargetPreconditions decision
  ]

deriveTargetStrengtheningStageRevision
  :: TargetStrengtheningStageBundle
  -> TargetStrengtheningStageRevision
deriveTargetStrengtheningStageRevision bundle = TargetStrengtheningStageRevision
  ("phil.phase1.stage.target-strengthening.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("base_stage", SemanticAtom (baseRevisionText (targetStrengtheningStageBase bundle)))
      , ("strengthenings", SemanticUnordered (Set.fromList
          [ semanticStrengthening strengthening
          | (_, strengthening) <- Map.toAscList
              (targetStrengtheningStageFacts bundle)
          ]))
      , ("derived_obligations", SemanticUnordered (Set.fromList
          [ semanticDerivedObligation obligation
          | (_, obligation) <- Map.toAscList
              (targetStrengtheningStageDerivedObligations bundle)
          ]))
      ])))

makeTargetStrengtheningStageBundle
  :: AssumptionDependencyStageBundle
  -> Map TargetPreconditionRef TargetStrengthening
  -> Map RevisionId DerivedObligation
  -> TargetStrengtheningStageBundle
makeTargetStrengtheningStageBundle base strengthenings obligations = provisional
  { targetStrengtheningStageRevision =
      deriveTargetStrengtheningStageRevision provisional }
  where
    provisional = TargetStrengtheningStageBundle
      { targetStrengtheningStageBase = base
      , targetStrengtheningStageRevision = TargetStrengtheningStageRevision "pending"
      , targetStrengtheningStageFacts = strengthenings
      , targetStrengtheningStageDerivedObligations = obligations
      }

verifyTargetStrengtheningStageBundle
  :: TargetStrengtheningStageBundle
  -> Either TargetStrengtheningVerificationError ()
verifyTargetStrengtheningStageBundle bundle = do
  mapLeft TargetStrengtheningBaseError $
    verifyAssumptionDependencyStageBundle (targetStrengtheningStageBase bundle)
  requireEqual TargetStrengtheningStageRevisionMismatch
    (deriveTargetStrengtheningStageRevision bundle)
    (targetStrengtheningStageRevision bundle)

  let expectedRefs = deriveTargetPreconditionRefs (targetStrengtheningStageBase bundle)
      actualRefs = Map.keysSet (targetStrengtheningStageFacts bundle)
      decisions = baseDecisions (targetStrengtheningStageBase bundle)

  requireEqual TargetStrengtheningDomainMismatch expectedRefs actualRefs
  mapM_ (checkStrengthening decisions)
    (Map.toAscList (targetStrengtheningStageFacts bundle))

  let expectedDerived = deriveExpectedDerived
        (targetStrengtheningStageFacts bundle)
      expectedDerivedDomain = Map.keysSet expectedDerived
      actualDerivedDomain = Map.keysSet
        (targetStrengtheningStageDerivedObligations bundle)

  requireEqual DerivedObligationRegistryDomainMismatch
    expectedDerivedDomain actualDerivedDomain
  mapM_ (checkDerivedObligation
      expectedDerived
      (targetStrengtheningStageDerivedObligations bundle))
    (Set.toAscList expectedDerivedDomain)

  mapM_ (checkDecisionDerived bundle) (Map.toAscList decisions)

  let stageDerived = Set.fromList
        (stageDerivedObligations
          (systemsArtifactStageContract (baseArtifact (targetStrengtheningStageBase bundle))))
  requireEqual TargetStrengtheningStageDerivedMismatch
    expectedDerivedDomain stageDerived

checkStrengthening
  :: Map DecisionId LoweringDecision
  -> (TargetPreconditionRef, TargetStrengthening)
  -> Either TargetStrengtheningVerificationError ()
checkStrengthening decisions (key, strengthening) = do
  requireEqual TargetStrengtheningMapKeyMismatch
    key (targetStrengtheningRef strengthening)
  if Text.null (targetPreconditionRequirement key)
    then Left (TargetStrengtheningEmptyRequirement key)
    else Right ()
  decision <- case Map.lookup (targetPreconditionDecision key) decisions of
    Nothing -> Left (TargetStrengtheningDomainMismatch
      (Set.singleton key) Set.empty)
    Just value -> Right value
  let sourceAssurance = targetStrengtheningSourceAssurance strengthening
      availableSource = Set.fromList (loweringObligationRevisions decision)
      unknownSource = Set.difference sourceAssurance availableSource
  if Set.null unknownSource
    then Right ()
    else Left (TargetStrengtheningUnknownSourceAssurance key unknownSource)
  case targetStrengtheningDerivedObligation strengthening of
    Nothing
      | Set.null sourceAssurance ->
          Left (TargetStrengtheningMissingDerivedObligation key)
      | otherwise -> Right ()
    Just revision
      | Text.null (unRevisionId revision) ->
          Left (TargetStrengtheningEmptyDerivedRevision key)
      | otherwise -> Right ()

checkDecisionDerived
  :: TargetStrengtheningStageBundle
  -> (DecisionId, LoweringDecision)
  -> Either TargetStrengtheningVerificationError ()
checkDecisionDerived bundle (decisionKey, decision) =
  requireEqual (TargetStrengtheningDecisionDerivedMismatch decisionKey)
    expected actual
  where
    expected = Set.fromList
      [ revision
      | (ref, strengthening) <- Map.toAscList (targetStrengtheningStageFacts bundle)
      , targetPreconditionDecision ref == decisionKey
      , Just revision <- [targetStrengtheningDerivedObligation strengthening]
      ]
    actual = Set.fromList (loweringDerivedObligations decision)

checkDerivedObligation
  :: Map RevisionId (Set TargetPreconditionRef, Set Text)
  -> Map RevisionId DerivedObligation
  -> RevisionId
  -> Either TargetStrengtheningVerificationError ()
checkDerivedObligation expected actual revision = do
  (expectedIntroducers, expectedSubjects) <- case Map.lookup revision expected of
    Nothing -> Left (DerivedObligationRegistryDomainMismatch
      (Map.keysSet expected) (Map.keysSet actual))
    Just value -> Right value
  obligation <- case Map.lookup revision actual of
    Nothing -> Left (DerivedObligationRegistryDomainMismatch
      (Map.keysSet expected) (Map.keysSet actual))
    Just value -> Right value
  requireEqual DerivedObligationMapKeyMismatch
    revision (derivedObligationRevision obligation)
  requireEqual (DerivedObligationIntroducedByMismatch revision)
    expectedIntroducers (derivedObligationIntroducedBy obligation)
  requireEqual (DerivedObligationSubjectMismatch revision)
    expectedSubjects (derivedObligationSemanticSubjects obligation)
  if Text.null (derivedObligationStatement obligation)
    then Left (DerivedObligationEmptyStatement revision)
    else Right ()
  if Text.null (derivedObligationAcceptanceRule obligation)
    then Left (DerivedObligationEmptyAcceptanceRule revision)
    else Right ()

deriveExpectedDerived
  :: Map TargetPreconditionRef TargetStrengthening
  -> Map RevisionId (Set TargetPreconditionRef, Set Text)
deriveExpectedDerived strengthenings = Map.fromListWith combine
  [ ( revision
    , (Set.singleton ref, targetStrengtheningSemanticSubjects strengthening)
    )
  | (ref, strengthening) <- Map.toAscList strengthenings
  , Just revision <- [targetStrengtheningDerivedObligation strengthening]
  ]
  where
    combine (leftRefs, leftSubjects) (rightRefs, rightSubjects) =
      (Set.union leftRefs rightRefs, Set.union leftSubjects rightSubjects)

baseArtifact :: AssumptionDependencyStageBundle -> SystemsArtifact
baseArtifact =
  phase1StageSystemsArtifact
    . subjectStageBase
    . evidenceTransferStageBase
    . evidenceErasureStageBase
    . assumptionDependencyStageBase

baseDecisions :: AssumptionDependencyStageBundle -> Map DecisionId LoweringDecision
baseDecisions =
  loweringLedgerDecisions
    . systemsArtifactLoweringLedger
    . baseArtifact

baseRevisionText :: AssumptionDependencyStageBundle -> Text
baseRevisionText =
  unAssumptionDependencyStageRevision . assumptionDependencyStageRevision

semanticStrengthening :: TargetStrengthening -> SemanticForm
semanticStrengthening strengthening = SemanticRecord (Map.fromList
  [ ("ref", semanticPreconditionRef (targetStrengtheningRef strengthening))
  , ("subjects", semanticTextSet (targetStrengtheningSemanticSubjects strengthening))
  , ("source_assurance", semanticRevisionSet
      (targetStrengtheningSourceAssurance strengthening))
  , ("derived_obligation", maybe
      (SemanticAtom "none")
      (SemanticAtom . unRevisionId)
      (targetStrengtheningDerivedObligation strengthening))
  ])

semanticDerivedObligation :: DerivedObligation -> SemanticForm
semanticDerivedObligation obligation = SemanticRecord (Map.fromList
  [ ("revision", SemanticAtom (unRevisionId (derivedObligationRevision obligation)))
  , ("introduced_by", SemanticUnordered
      (Set.map semanticPreconditionRef (derivedObligationIntroducedBy obligation)))
  , ("subjects", semanticTextSet (derivedObligationSemanticSubjects obligation))
  , ("statement", SemanticAtom (derivedObligationStatement obligation))
  , ("acceptance_rule", SemanticAtom (derivedObligationAcceptanceRule obligation))
  ])

semanticPreconditionRef :: TargetPreconditionRef -> SemanticForm
semanticPreconditionRef ref = SemanticRecord (Map.fromList
  [ ("decision", SemanticAtom
      (unDecisionId (targetPreconditionDecision ref)))
  , ("requirement", SemanticAtom
      (targetPreconditionRequirement ref))
  ])

semanticRevisionSet :: Set RevisionId -> SemanticForm
semanticRevisionSet = SemanticUnordered . Set.map (SemanticAtom . unRevisionId)

semanticTextSet :: Set Text -> SemanticForm
semanticTextSet = SemanticUnordered . Set.map SemanticAtom

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
