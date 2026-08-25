{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.CallableQualification
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
import Phil.Core.CallableRefinement
  ( CallableRefinementError
  , CallableRefinementSurface
  , CheckedCallableRefinement
  , checkCallableRefinement
  )

-- | Stable identity of one concrete foreign callable artifact. This is not a
-- symbol spelling, load address, or function pointer: qualification is bound to
-- one explicit implementation artifact identity supplied by the competent
-- provider/foreign boundary.
newtype ForeignCallableArtifactKey = ForeignCallableArtifactKey
  { unForeignCallableArtifactKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Concrete foreign callable candidate before semantic qualification. The
-- machine shape is already represented inside the callable refinement surface;
-- this object exists to bind semantic evidence to an exact implementation.
data ForeignCallableArtifact = ForeignCallableArtifact
  { foreignCallableArtifactKey :: ForeignCallableArtifactKey
  , foreignCallableObservedSurface :: CallableRefinementSurface
  }
  deriving (Eq, Ord, Show)

-- | Independent evidence dimensions required by the bounded CALL-015 boundary.
-- Successful linkage or matching ABI supplies none of these automatically.
data ForeignCallableEvidenceKind
  = ForeignCallableAbiCorrespondence
  | ForeignCallableResourceLifecycle
  | ForeignCallableEffectConfinement
  | ForeignCallableAuthorityConfinement
  | ForeignCallableFailureBehavior
  deriving (Eq, Ord, Show)

-- | Explicit qualification facts for one exact foreign callable artifact.
-- Evidence payloads are stable identities/references into the competent
-- qualification/assurance layer; this checker does not pretend to re-prove the
-- external facts they denote.
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
  deriving (Eq, Ord, Show)

requiredForeignCallableEvidence :: Set.Set ForeignCallableEvidenceKind
requiredForeignCallableEvidence = Set.fromList
  [ ForeignCallableAbiCorrespondence
  , ForeignCallableResourceLifecycle
  , ForeignCallableEffectConfinement
  , ForeignCallableAuthorityConfinement
  , ForeignCallableFailureBehavior
  ]

-- | Admit one foreign callable only after qualification has established an exact
-- semantic surface for the exact artifact and supplied evidence for every
-- independent boundary dimension. The existing higher-order refinement checker
-- then decides whether that qualified surface is safe where the expected Phil
-- callable contract is required.
checkForeignCallableQualification
  :: CallableRefinementSurface
  -> ForeignCallableArtifact
  -> Maybe ForeignCallableQualification
  -> Either ForeignCallableQualificationError CheckedForeignCallableQualification
checkForeignCallableQualification expected artifact maybeQualification = do
  qualification <- maybe
    (Left (ForeignCallableQualificationMissing (foreignCallableArtifactKey artifact)))
    Right
    maybeQualification
  let actualArtifactKey = foreignCallableArtifactKey artifact
      qualifiedArtifactKey = foreignQualificationArtifactKey qualification
  if qualifiedArtifactKey /= actualArtifactKey
    then Left (ForeignCallableQualificationArtifactMismatch
      actualArtifactKey qualifiedArtifactKey)
    else pure ()
  if foreignQualificationSurface qualification /= foreignCallableObservedSurface artifact
    then Left (ForeignCallableQualificationSurfaceMismatch
      (foreignCallableObservedSurface artifact)
      (foreignQualificationSurface qualification))
    else pure ()
  let provided = Map.keysSet (foreignQualificationEvidence qualification)
      missing = Set.difference requiredForeignCallableEvidence provided
  if Set.null missing
    then pure ()
    else Left (ForeignCallableQualificationMissingEvidence missing)
  refinement <- mapLeft ForeignCallableQualificationRefinementError
    (checkCallableRefinement expected (foreignQualificationSurface qualification))
  Right CheckedForeignCallableQualification
    { checkedForeignArtifact = artifact
    , checkedForeignQualification = qualification
    , checkedForeignRefinement = refinement
    }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
