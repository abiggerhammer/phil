module Phil.Verification.ArtifactClosure
  ( CertifiedApplicationArtifact
  , certifiedApplicationSourceAssurance
  , certifiedApplicationStageClosure
  , ArtifactCertificationError (..)
  , certifyApplicationArtifact
  ) where

import Phil.Systems.StageClosure
  ( StageClosureBundle
  , StageClosureVerificationError
  , verifyStageClosureBundle
  )
import Phil.Verification.GenericAssurance
  ( GenericApplicationAssurance
  )

-- | A source application assurance paired with one exact emitted-artifact
-- StageClosure that has independently passed the Systems/StageContract gate.
-- Source verification is necessary but deliberately not sufficient here.
data CertifiedApplicationArtifact = CertifiedApplicationArtifact
  GenericApplicationAssurance
  StageClosureBundle
  deriving (Eq, Show)

certifiedApplicationSourceAssurance
  :: CertifiedApplicationArtifact
  -> GenericApplicationAssurance
certifiedApplicationSourceAssurance
  (CertifiedApplicationArtifact sourceAssurance _) = sourceAssurance

certifiedApplicationStageClosure
  :: CertifiedApplicationArtifact
  -> StageClosureBundle
certifiedApplicationStageClosure
  (CertifiedApplicationArtifact _ stageClosure) = stageClosure

data ArtifactCertificationError
  = ArtifactCertificationStageClosureRejected StageClosureVerificationError
  deriving (Eq, Show)

-- | Certify one emitted artifact from an already accepted source assurance.
-- The source assurance is intentionally not replayed or rewritten.  Instead,
-- the existing certified StageClosure verifier independently establishes the
-- realization/Systems preservation relation for this exact artifact.  A source
-- proof may therefore remain reusable while a changed realization still fails
-- artifact certification.
certifyApplicationArtifact
  :: GenericApplicationAssurance
  -> StageClosureBundle
  -> Either ArtifactCertificationError CertifiedApplicationArtifact
certifyApplicationArtifact sourceAssurance stageClosure = do
  mapLeft ArtifactCertificationStageClosureRejected
    (verifyStageClosureBundle stageClosure)
  pure (CertifiedApplicationArtifact sourceAssurance stageClosure)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
