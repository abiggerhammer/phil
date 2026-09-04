module Phil.Systems.RuntimePrimitiveIdentityCertification
  ( CertifiedRuntimePrimitiveStage
  , certifiedRuntimePrimitiveStageBundle
  , certifiedRuntimePrimitiveEntries
  , RuntimePrimitiveIdentityKernelFacts (..)
  , RuntimePrimitiveIdentityCertificationError (..)
  , targetRuntimePrimitiveEntry
  , verifyRuntimePrimitiveIdentityKernelFacts
  , certifyRuntimePrimitiveStage
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified RuntimePrimitiveIdentityKernel as Kernel
import Phil.Systems.IR
  ( RuntimeSiteRef (..)
  )
import Phil.Systems.RuntimeClaimBinding
  ( RuntimeClaimStageBundle (..)
  , RuntimeSiteBinding (..)
  , RuntimeSiteKey
  )
import Phil.Systems.RuntimePrimitiveReuse
  ( RuntimePrimitiveProfileRef (..)
  , RuntimePrimitiveSiteBinding (..)
  , RuntimePrimitiveStageBundle (..)
  , RuntimePrimitiveVerificationError
  , verifyRuntimePrimitiveStageBundle
  )

-- | Opaque admission result for one complete SYS-016 stage.  The certificate
-- can only be constructed after the native SYS-016 verifier succeeds and every
-- selected site crosses the exact PHIL-TARGET-RUNTIME-PRIM-001 kernel gate.
data CertifiedRuntimePrimitiveStage = CertifiedRuntimePrimitiveStage
  RuntimePrimitiveStageBundle
  (Map RuntimeSiteKey RuntimePrimitiveProfileRef)
  deriving (Eq, Show)

certifiedRuntimePrimitiveStageBundle
  :: CertifiedRuntimePrimitiveStage
  -> RuntimePrimitiveStageBundle
certifiedRuntimePrimitiveStageBundle (CertifiedRuntimePrimitiveStage bundle _) = bundle

certifiedRuntimePrimitiveEntries
  :: CertifiedRuntimePrimitiveStage
  -> Map RuntimeSiteKey RuntimePrimitiveProfileRef
certifiedRuntimePrimitiveEntries (CertifiedRuntimePrimitiveStage _ entries) = entries

-- | The two machine facts are intentionally isomorphic to the Certified Rocq
-- success record.  The bounded Systems representation treats RuntimePrimitiveProfileRef
-- as the combined physical-primitive/profile coordinate; concrete target entry
-- representations remain backend-specific refinements.
data RuntimePrimitiveIdentityKernelFacts = RuntimePrimitiveIdentityKernelFacts
  { runtimePrimitivePhysicalProfileExact :: Bool
  , runtimePrimitiveNoAssuranceEncoding :: Bool
  }
  deriving (Eq, Show)

data RuntimePrimitiveIdentityCertificationError
  = RuntimePrimitiveIdentityNativeError RuntimePrimitiveVerificationError
  | RuntimePrimitiveIdentitySourceSiteMissing RuntimeSiteKey
  | RuntimePrimitiveIdentityKernelDisagreement RuntimePrimitiveIdentityKernelFacts
  deriving (Eq, Show)

-- | Target-neutral entry construction for the bounded Phase-1 representation.
-- Only the typed reusable implementation-family/profile coordinate is projected.
-- Runtime-site revision and evidence fields are deliberately not inputs.
targetRuntimePrimitiveEntry :: RuntimeSiteRef -> RuntimePrimitiveProfileRef
targetRuntimePrimitiveEntry siteRef =
  RuntimePrimitiveProfileRef (runtimeSiteCostRef siteRef)

verifyRuntimePrimitiveIdentityKernelFacts
  :: RuntimePrimitiveIdentityKernelFacts
  -> Either RuntimePrimitiveIdentityCertificationError ()
verifyRuntimePrimitiveIdentityKernelFacts facts
  | Kernel.decideRuntimePrimitiveIdentityByFacts
      (runtimePrimitivePhysicalProfileExact facts)
      (runtimePrimitiveNoAssuranceEncoding facts) = Right ()
  | otherwise = Left (RuntimePrimitiveIdentityKernelDisagreement facts)

certifyRuntimePrimitiveStage
  :: RuntimePrimitiveStageBundle
  -> Either RuntimePrimitiveIdentityCertificationError CertifiedRuntimePrimitiveStage
certifyRuntimePrimitiveStage bundle = do
  mapLeft RuntimePrimitiveIdentityNativeError (verifyRuntimePrimitiveStageBundle bundle)
  entries <- Map.traverseWithKey (certifySite bundle)
    (runtimePrimitiveStageSites bundle)
  pure (CertifiedRuntimePrimitiveStage bundle entries)

certifySite
  :: RuntimePrimitiveStageBundle
  -> RuntimeSiteKey
  -> RuntimePrimitiveSiteBinding
  -> Either RuntimePrimitiveIdentityCertificationError RuntimePrimitiveProfileRef
certifySite bundle siteKey actualBinding = do
  sourceBinding <- case Map.lookup siteKey sourceSites of
    Nothing -> Left (RuntimePrimitiveIdentitySourceSiteMissing siteKey)
    Just binding -> Right binding
  let sourceRef = runtimeSiteBindingRef sourceBinding
      targetEntry = targetRuntimePrimitiveEntry sourceRef
      facts = RuntimePrimitiveIdentityKernelFacts
        { runtimePrimitivePhysicalProfileExact =
            runtimePrimitiveSiteKey actualBinding == siteKey
              && runtimePrimitiveSiteProfile actualBinding == targetEntry
        , runtimePrimitiveNoAssuranceEncoding =
            targetEntry == RuntimePrimitiveProfileRef (runtimeSiteCostRef sourceRef)
        }
  verifyRuntimePrimitiveIdentityKernelFacts facts
  pure targetEntry
  where
    sourceSites = runtimeClaimStageSites (runtimePrimitiveStageBase bundle)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
