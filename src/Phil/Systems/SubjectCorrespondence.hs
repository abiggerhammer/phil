{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.SubjectCorrespondence
  ( SourceSubjectKey (..)
  , SystemsValueRef (..)
  , SubjectRelationRevision (..)
  , SubjectValidityScopeRevision (..)
  , SubjectCorrespondenceBasis (..)
  , SubjectCorrespondence (..)
  , SubjectStageRevision (..)
  , SubjectStageBundle (..)
  , SubjectStageVerificationError (..)
  , deriveSubjectStageRevision
  , makeSubjectStageBundle
  , verifySubjectStageBundle
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Static
  ( SemanticForm (..)
  , canonicalSemanticForm
  )
import Phil.Systems.IR
  ( SystemsArtifact (..)
  , SystemsFunction (..)
  , SystemsProgram (..)
  , ValueId (..)
  )
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  , Phase1StageContractRevision (..)
  , Phase1StageVerificationError
  , verifyPhase1StageBundle
  )

newtype SourceSubjectKey = SourceSubjectKey
  { unSourceSubjectKey :: Text
  }
  deriving (Eq, Ord, Show)

data SystemsValueRef = SystemsValueRef
  { systemsValueRefFunction :: Text
  , systemsValueRefValue :: ValueId
  }
  deriving (Eq, Ord, Show)

newtype SubjectRelationRevision = SubjectRelationRevision
  { unSubjectRelationRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype SubjectValidityScopeRevision = SubjectValidityScopeRevision
  { unSubjectValidityScopeRevision :: Text
  }
  deriving (Eq, Ord, Show)

-- | Checked semantic correspondence is distinct from runtime coincidence.
-- The coincidence constructor is represented only so SYS-004 can reject the
-- exact invalid inference instead of silently treating it as a relation.
data SubjectCorrespondenceBasis
  = CheckedSubjectRelation SubjectRelationRevision
  | RuntimeRepresentationCoincidence Text
  deriving (Eq, Ord, Show)

data SubjectCorrespondence = SubjectCorrespondence
  { subjectCorrespondenceSource :: SourceSubjectKey
  , subjectCorrespondenceSystemsValues :: Set SystemsValueRef
  , subjectCorrespondenceBasis :: SubjectCorrespondenceBasis
  , subjectCorrespondenceValidityScope :: SubjectValidityScopeRevision
  , subjectCorrespondenceEvidenceRefs :: Set Text
  }
  deriving (Eq, Ord, Show)

newtype SubjectStageRevision = SubjectStageRevision
  { unSubjectStageRevision :: Text
  }
  deriving (Eq, Ord, Show)

-- | Compositional StageContract relation layer for SYS-004. It binds the exact
-- base Phase-1 StageContract revision and the exact subject-correspondence graph.
-- The base stage verifier always runs first.
data SubjectStageBundle = SubjectStageBundle
  { subjectStageBase :: Phase1StageBundle
  , subjectStageRevision :: SubjectStageRevision
  , subjectStageCorrespondences :: Map SourceSubjectKey SubjectCorrespondence
  }
  deriving (Eq, Show)

data SubjectStageVerificationError
  = SubjectStageBaseError Phase1StageVerificationError
  | SubjectStageRevisionMismatch SubjectStageRevision SubjectStageRevision
  | SubjectCorrespondenceMapKeyMismatch SourceSubjectKey SourceSubjectKey
  | SubjectCorrespondenceEmptySystemsSet SourceSubjectKey
  | SubjectCorrespondenceUnknownFunction SourceSubjectKey Text
  | SubjectCorrespondenceUnknownValue SourceSubjectKey SystemsValueRef
  | SubjectCorrespondenceEmptyRelationRevision SourceSubjectKey
  | SubjectCorrespondenceEmptyValidityScope SourceSubjectKey
  | SubjectCorrespondenceRuntimeCoincidenceRejected SourceSubjectKey Text
  | SubjectCorrespondenceSystemsValueShared
      SystemsValueRef (Set SourceSubjectKey)
  deriving (Eq, Show)

deriveSubjectStageRevision :: SubjectStageBundle -> SubjectStageRevision
deriveSubjectStageRevision bundle =
  SubjectStageRevision
    ("phil.phase1.stage.subjects.canonical.v1:"
      <> canonicalSemanticForm (SemanticRecord (Map.fromList
        [ ("base_stage", SemanticAtom (baseStageText (subjectStageBase bundle)))
        , ("correspondences", SemanticRecord (Map.fromList
            [ (unSourceSubjectKey key, semanticCorrespondence value)
            | (key, value) <- Map.toAscList (subjectStageCorrespondences bundle)
            ]))
        ])))

makeSubjectStageBundle
  :: Phase1StageBundle
  -> Map SourceSubjectKey SubjectCorrespondence
  -> SubjectStageBundle
makeSubjectStageBundle base correspondences = provisional
  { subjectStageRevision = deriveSubjectStageRevision provisional }
  where
    provisional = SubjectStageBundle
      { subjectStageBase = base
      , subjectStageRevision = SubjectStageRevision "pending"
      , subjectStageCorrespondences = correspondences
      }

verifySubjectStageBundle
  :: SubjectStageBundle
  -> Either SubjectStageVerificationError ()
verifySubjectStageBundle bundle = do
  mapLeft SubjectStageBaseError (verifyPhase1StageBundle (subjectStageBase bundle))
  let expectedRevision = deriveSubjectStageRevision bundle
      actualRevision = subjectStageRevision bundle
  requireEqual SubjectStageRevisionMismatch expectedRevision actualRevision
  mapM_ checkCorrespondence (Map.toAscList correspondences)
  checkExclusiveSystemsBindings correspondences
  where
    correspondences = subjectStageCorrespondences bundle
    artifact = phase1StageSystemsArtifact (subjectStageBase bundle)
    functions = systemsProgramFunctions (systemsArtifactProgram artifact)

    checkCorrespondence (key, correspondence) = do
      let actualKey = subjectCorrespondenceSource correspondence
          systemsRefs = subjectCorrespondenceSystemsValues correspondence
      requireEqual SubjectCorrespondenceMapKeyMismatch key actualKey
      if Set.null systemsRefs
        then Left (SubjectCorrespondenceEmptySystemsSet key)
        else Right ()
      mapM_ (checkSystemsRef key) (Set.toAscList systemsRefs)
      case subjectCorrespondenceBasis correspondence of
        CheckedSubjectRelation (SubjectRelationRevision relation)
          | Text.null relation -> Left (SubjectCorrespondenceEmptyRelationRevision key)
          | otherwise -> Right ()
        RuntimeRepresentationCoincidence reason ->
          Left (SubjectCorrespondenceRuntimeCoincidenceRejected key reason)
      case subjectCorrespondenceValidityScope correspondence of
        SubjectValidityScopeRevision scope
          | Text.null scope -> Left (SubjectCorrespondenceEmptyValidityScope key)
          | otherwise -> Right ()

    checkSystemsRef sourceSubject ref =
      case Map.lookup (systemsValueRefFunction ref) functions of
        Nothing -> Left (SubjectCorrespondenceUnknownFunction
          sourceSubject (systemsValueRefFunction ref))
        Just function ->
          if Map.member (systemsValueRefValue ref) (systemsFunctionValues function)
            then Right ()
            else Left (SubjectCorrespondenceUnknownValue sourceSubject ref)

checkExclusiveSystemsBindings
  :: Map SourceSubjectKey SubjectCorrespondence
  -> Either SubjectStageVerificationError ()
checkExclusiveSystemsBindings correspondences =
  case
    [ (ref, subjects)
    | (ref, subjects) <- Map.toAscList reverseBindings
    , Set.size subjects > 1
    ] of
    [] -> Right ()
    (ref, subjects) : _ -> Left
      (SubjectCorrespondenceSystemsValueShared ref subjects)
  where
    reverseBindings = Map.fromListWith Set.union
      [ (ref, Set.singleton sourceSubject)
      | (sourceSubject, correspondence) <- Map.toAscList correspondences
      , ref <- Set.toAscList (subjectCorrespondenceSystemsValues correspondence)
      ]

semanticCorrespondence :: SubjectCorrespondence -> SemanticForm
semanticCorrespondence correspondence = SemanticRecord (Map.fromList
  [ ("source", SemanticAtom
      (unSourceSubjectKey (subjectCorrespondenceSource correspondence)))
  , ("systems_values", SemanticUnordered (Set.map semanticSystemsValueRef
      (subjectCorrespondenceSystemsValues correspondence)))
  , ("basis", semanticBasis (subjectCorrespondenceBasis correspondence))
  , ("validity", SemanticAtom (validityText
      (subjectCorrespondenceValidityScope correspondence)))
  , ("evidence_refs", SemanticUnordered
      (Set.map SemanticAtom (subjectCorrespondenceEvidenceRefs correspondence)))
  ])

semanticSystemsValueRef :: SystemsValueRef -> SemanticForm
semanticSystemsValueRef ref = SemanticRecord (Map.fromList
  [ ("function", SemanticAtom (systemsValueRefFunction ref))
  , ("value", SemanticAtom (unValueId (systemsValueRefValue ref)))
  ])

semanticBasis :: SubjectCorrespondenceBasis -> SemanticForm
semanticBasis basis = case basis of
  CheckedSubjectRelation revision -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "checked-relation")
    , ("revision", SemanticAtom (relationText revision))
    ])
  RuntimeRepresentationCoincidence reason -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "runtime-representation-coincidence")
    , ("reason", SemanticAtom reason)
    ])

baseStageText :: Phase1StageBundle -> Text
baseStageText bundle = case phase1StageContractRevision bundle of
  Phase1StageContractRevision value -> value

relationText :: SubjectRelationRevision -> Text
relationText (SubjectRelationRevision value) = value

validityText :: SubjectValidityScopeRevision -> Text
validityText (SubjectValidityScopeRevision value) = value

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
