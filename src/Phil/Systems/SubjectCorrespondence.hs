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
import qualified SystemsSubjectAuthorityKernel as Kernel

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
  mapM_ checkStructuralCorrespondence (Map.toAscList correspondences)
  case Kernel.decideSubjectStageByFacts
      (kernelSubjectBasis correspondences)
      (allSystemsSetsNonempty correspondences)
      (allSystemsValuesExist functions correspondences)
      (systemsBindingsExclusive correspondences)
      (allValidityScopesExact correspondences) of
    Kernel.SubjectStageAcceptedDecision -> Right ()
    Kernel.SubjectStageBasisDecision ->
      firstOrInvariant "subject-basis" (runtimeCoincidenceErrors correspondences)
    Kernel.SubjectStageSystemsSetDecision ->
      firstOrInvariant "subject-systems-set" (emptySystemsSetErrors correspondences)
    Kernel.SubjectStageSystemsValuesDecision ->
      firstOrInvariant "subject-systems-values"
        (unknownSystemsValueErrors functions correspondences)
    Kernel.SubjectStageExclusivityDecision ->
      firstOrInvariant "subject-exclusivity" (sharedSystemsValueErrors correspondences)
    Kernel.SubjectStageValidityScopeDecision ->
      firstOrInvariant "subject-validity" (emptyValidityScopeErrors correspondences)
  where
    correspondences = subjectStageCorrespondences bundle
    artifact = phase1StageSystemsArtifact (subjectStageBase bundle)
    functions = systemsProgramFunctions (systemsArtifactProgram artifact)

checkStructuralCorrespondence
  :: (SourceSubjectKey, SubjectCorrespondence)
  -> Either SubjectStageVerificationError ()
checkStructuralCorrespondence (key, correspondence) = do
  requireEqual SubjectCorrespondenceMapKeyMismatch
    key (subjectCorrespondenceSource correspondence)
  case subjectCorrespondenceBasis correspondence of
    CheckedSubjectRelation (SubjectRelationRevision relation)
      | Text.null relation -> Left (SubjectCorrespondenceEmptyRelationRevision key)
      | otherwise -> Right ()
    RuntimeRepresentationCoincidence _ -> Right ()

kernelSubjectBasis
  :: Map SourceSubjectKey SubjectCorrespondence
  -> Kernel.SubjectCorrespondenceBasis
kernelSubjectBasis correspondences
  | any isRuntimeCoincidence (Map.elems correspondences) =
      Kernel.RuntimeRepresentationCoincidence
  | otherwise = Kernel.CheckedSubjectRelation
  where
    isRuntimeCoincidence correspondence = case subjectCorrespondenceBasis correspondence of
      RuntimeRepresentationCoincidence _ -> True
      CheckedSubjectRelation _ -> False

allSystemsSetsNonempty :: Map SourceSubjectKey SubjectCorrespondence -> Bool
allSystemsSetsNonempty = all (not . Set.null . subjectCorrespondenceSystemsValues) . Map.elems

allSystemsValuesExist
  :: Map Text SystemsFunction
  -> Map SourceSubjectKey SubjectCorrespondence
  -> Bool
allSystemsValuesExist functions = all correspondenceValuesExist . Map.elems
  where
    correspondenceValuesExist correspondence =
      all (systemsRefExists functions)
        (Set.toAscList (subjectCorrespondenceSystemsValues correspondence))

systemsRefExists :: Map Text SystemsFunction -> SystemsValueRef -> Bool
systemsRefExists functions ref =
  case Map.lookup (systemsValueRefFunction ref) functions of
    Nothing -> False
    Just function ->
      Map.member (systemsValueRefValue ref) (systemsFunctionValues function)

systemsBindingsExclusive :: Map SourceSubjectKey SubjectCorrespondence -> Bool
systemsBindingsExclusive = null . sharedSystemsValueErrors

allValidityScopesExact :: Map SourceSubjectKey SubjectCorrespondence -> Bool
allValidityScopesExact = all validityExact . Map.elems
  where
    validityExact correspondence = case subjectCorrespondenceValidityScope correspondence of
      SubjectValidityScopeRevision scope -> not (Text.null scope)

runtimeCoincidenceErrors
  :: Map SourceSubjectKey SubjectCorrespondence
  -> [SubjectStageVerificationError]
runtimeCoincidenceErrors correspondences =
  [ SubjectCorrespondenceRuntimeCoincidenceRejected key reason
  | (key, correspondence) <- Map.toAscList correspondences
  , RuntimeRepresentationCoincidence reason <- [subjectCorrespondenceBasis correspondence]
  ]

emptySystemsSetErrors
  :: Map SourceSubjectKey SubjectCorrespondence
  -> [SubjectStageVerificationError]
emptySystemsSetErrors correspondences =
  [ SubjectCorrespondenceEmptySystemsSet key
  | (key, correspondence) <- Map.toAscList correspondences
  , Set.null (subjectCorrespondenceSystemsValues correspondence)
  ]

unknownSystemsValueErrors
  :: Map Text SystemsFunction
  -> Map SourceSubjectKey SubjectCorrespondence
  -> [SubjectStageVerificationError]
unknownSystemsValueErrors functions correspondences =
  [ err
  | (key, correspondence) <- Map.toAscList correspondences
  , ref <- Set.toAscList (subjectCorrespondenceSystemsValues correspondence)
  , err <- maybeToList (systemsRefError functions key ref)
  ]

systemsRefError
  :: Map Text SystemsFunction
  -> SourceSubjectKey
  -> SystemsValueRef
  -> Maybe SubjectStageVerificationError
systemsRefError functions sourceSubject ref =
  case Map.lookup (systemsValueRefFunction ref) functions of
    Nothing -> Just (SubjectCorrespondenceUnknownFunction
      sourceSubject (systemsValueRefFunction ref))
    Just function
      | Map.member (systemsValueRefValue ref) (systemsFunctionValues function) -> Nothing
      | otherwise -> Just (SubjectCorrespondenceUnknownValue sourceSubject ref)

sharedSystemsValueErrors
  :: Map SourceSubjectKey SubjectCorrespondence
  -> [SubjectStageVerificationError]
sharedSystemsValueErrors correspondences =
  [ SubjectCorrespondenceSystemsValueShared ref subjects
  | (ref, subjects) <- Map.toAscList reverseBindings
  , Set.size subjects > 1
  ]
  where
    reverseBindings = Map.fromListWith Set.union
      [ (ref, Set.singleton sourceSubject)
      | (sourceSubject, correspondence) <- Map.toAscList correspondences
      , ref <- Set.toAscList (subjectCorrespondenceSystemsValues correspondence)
      ]

emptyValidityScopeErrors
  :: Map SourceSubjectKey SubjectCorrespondence
  -> [SubjectStageVerificationError]
emptyValidityScopeErrors correspondences =
  [ SubjectCorrespondenceEmptyValidityScope key
  | (key, correspondence) <- Map.toAscList correspondences
  , SubjectValidityScopeRevision scope <- [subjectCorrespondenceValidityScope correspondence]
  , Text.null scope
  ]

firstOrInvariant :: String -> [SubjectStageVerificationError] -> Either SubjectStageVerificationError ()
firstOrInvariant _ (err : _) = Left err
firstOrInvariant label [] =
  error ("SystemsSubjectAuthorityKernel mismatch: " <> label)

maybeToList :: Maybe a -> [a]
maybeToList Nothing = []
maybeToList (Just value) = [value]

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
