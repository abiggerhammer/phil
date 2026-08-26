{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.CallableQualification.Bound
  ( ForeignCallableArtifactKey (..)
  , ForeignCallableArtifact (..)
  , ForeignCallableEvidenceKind (..)
  , ForeignCallableQualification (..)
  , CheckedForeignCallableQualification (..)
  , ForeignCallableQualificationError (..)
  , requiredForeignCallableEvidence
  , checkForeignCallableQualification
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified ForeignCallableQualificationKernel as Kernel
import Phil.Core.CallableRefinement
  ( CallableRefinementError
  , CallableRefinementSurface
  , CheckedCallableRefinement
  , checkCallableRefinement
  )

newtype ForeignCallableArtifactKey = ForeignCallableArtifactKey
  { unForeignCallableArtifactKey :: Text
  }
  deriving (Eq, Ord, Show)

data ForeignCallableArtifact = ForeignCallableArtifact
  { foreignCallableArtifactKey :: ForeignCallableArtifactKey
  , foreignCallableObservedSurface :: CallableRefinementSurface
  }
  deriving (Eq, Ord, Show)

data ForeignCallableEvidenceKind
  = ForeignCallableAbiCorrespondence
  | ForeignCallableResourceLifecycle
  | ForeignCallableEffectConfinement
  | ForeignCallableAuthorityConfinement
  | ForeignCallableFailureBehavior
  deriving (Eq, Ord, Show)

data ForeignCallableQualification = ForeignCallableQualification
  { foreignQualificationArtifactKey :: ForeignCallableArtifactKey
  , foreignQualificationSurface :: CallableRefinementSurface
  , foreignQualificationEvidence :: Map.Map ForeignCallableEvidenceKind Text
  }
  deriving (Eq, Ord, Show)

data CheckedForeignCallableQualification = CheckedForeignCallableQualification
  { checkedForeignArtifact :: ForeignCallableArtifact
  , checkedForeignQualification :: ForeignCallableQualification
  , checkedForeignRefinement :: CheckedCallableRefinement
  }
  deriving (Eq, Ord, Show)

data ForeignCallableQualificationError
  = ForeignCallableQualificationMissing ForeignCallableArtifactKey
  | ForeignCallableQualificationArtifactMismatch
      ForeignCallableArtifactKey
      ForeignCallableArtifactKey
  | ForeignCallableQualificationSurfaceMismatch
      CallableRefinementSurface
      CallableRefinementSurface
  | ForeignCallableQualificationMissingEvidence
      (Set.Set ForeignCallableEvidenceKind)
  | ForeignCallableQualificationRefinementError CallableRefinementError
  | ForeignCallableQualificationRepresentationBridgeMismatch Text
  deriving (Eq, Ord, Show)

requiredForeignCallableEvidence :: Set.Set ForeignCallableEvidenceKind
requiredForeignCallableEvidence = Set.fromList
  [ ForeignCallableAbiCorrespondence
  , ForeignCallableResourceLifecycle
  , ForeignCallableEffectConfinement
  , ForeignCallableAuthorityConfinement
  , ForeignCallableFailureBehavior
  ]

checkForeignCallableQualification
  :: CallableRefinementSurface
  -> ForeignCallableArtifact
  -> Maybe ForeignCallableQualification
  -> Either ForeignCallableQualificationError CheckedForeignCallableQualification
checkForeignCallableQualification expected artifact maybeQualification = do
  checkEvidenceBridge maybeQualification
  case Kernel.decideForeignQualification
      maybeQualification
      artifactMatches
      surfaceMatches
      (hasEvidence ForeignCallableAbiCorrespondence)
      (hasEvidence ForeignCallableResourceLifecycle)
      (hasEvidence ForeignCallableEffectConfinement)
      (hasEvidence ForeignCallableAuthorityConfinement)
      (hasEvidence ForeignCallableFailureBehavior) of
    True -> acceptQualification
    False ->
      case concreteProjectionError maybeQualification of
        Just err -> Left err
        Nothing -> bridgeMismatch
          "CALL-015 extracted qualification rejection disagreed with concrete projection"
  where
    actualArtifactKey = foreignCallableArtifactKey artifact
    observedSurface = foreignCallableObservedSurface artifact

    artifactMatches qualification =
      foreignQualificationArtifactKey qualification == actualArtifactKey

    surfaceMatches qualification =
      foreignQualificationSurface qualification == observedSurface

    hasEvidence kind qualification =
      Map.member kind (foreignQualificationEvidence qualification)

    acceptQualification =
      case maybeQualification of
        Nothing -> bridgeMismatch
          "CALL-015 extracted qualification accepted an absent qualification"
        Just qualification ->
          case concreteProjectionError maybeQualification of
            Just _ -> bridgeMismatch
              "CALL-015 extracted qualification acceptance disagreed with concrete projection"
            Nothing -> do
              refinement <- mapLeft ForeignCallableQualificationRefinementError
                (checkCallableRefinement expected (foreignQualificationSurface qualification))
              Right CheckedForeignCallableQualification
                { checkedForeignArtifact = artifact
                , checkedForeignQualification = qualification
                , checkedForeignRefinement = refinement
                }

    concreteProjectionError Nothing =
      Just (ForeignCallableQualificationMissing actualArtifactKey)
    concreteProjectionError (Just qualification)
      | qualifiedArtifactKey /= actualArtifactKey =
          Just (ForeignCallableQualificationArtifactMismatch
            actualArtifactKey qualifiedArtifactKey)
      | qualifiedSurface /= observedSurface =
          Just (ForeignCallableQualificationSurfaceMismatch
            observedSurface qualifiedSurface)
      | not (Set.null missingEvidence) =
          Just (ForeignCallableQualificationMissingEvidence missingEvidence)
      | otherwise = Nothing
      where
        qualifiedArtifactKey = foreignQualificationArtifactKey qualification
        qualifiedSurface = foreignQualificationSurface qualification
        provided = Map.keysSet (foreignQualificationEvidence qualification)
        missingEvidence = Set.difference requiredForeignCallableEvidence provided

checkEvidenceBridge
  :: Maybe ForeignCallableQualification
  -> Either ForeignCallableQualificationError ()
checkEvidenceBridge Nothing = Right ()
checkEvidenceBridge (Just qualification)
  | Map.fromList entries /= evidence = bridgeMismatch
      "CALL-015 evidence Map round-trip changed the qualification"
  | Set.fromList (map fst entries) /= Map.keysSet evidence = bridgeMismatch
      "CALL-015 evidence key Set disagreed with the canonical Map projection"
  | otherwise = Right ()
  where
    evidence = foreignQualificationEvidence qualification
    entries = Map.toAscList evidence

bridgeMismatch :: Text -> Either ForeignCallableQualificationError a
bridgeMismatch = Left . ForeignCallableQualificationRepresentationBridgeMismatch

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
