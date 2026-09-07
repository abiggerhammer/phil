{-# LANGUAGE OverloadedStrings #-}

module Phil.Verification
  ( AssurancePolicyRevision (..)
  , VerificationDisposition (..)
  , ApplicationAssurancePolicy (..)
  , IntrinsicRejection (..)
  , ApplicationVerificationResult (..)
  , verifySurfaceApplication
  ) where

import Data.Set (Set)
import Data.Text (Text)
import Phil.Surface.Check
  ( SurfaceCheckError
  , SurfaceCheckResult
  , SurfaceEnvironment
  , checkSurfaceComponent
  )
import Phil.Surface.Parser
  ( ParseDiagnostic
  , parseSurfaceFile
  )
import Phil.Surface.Syntax (SurfaceFile (..))

-- | Identity-bearing assurance policy input for obligation closure.  VER-001
-- deliberately does not let this policy participate in intrinsic validity.
newtype AssurancePolicyRevision = AssurancePolicyRevision
  { unAssurancePolicyRevision :: Text
  }
  deriving (Eq, Ord, Show)

-- | Phase-1 closure dispositions from the application-verification contract.
-- Their presence here does not make them available to intrinsically invalid
-- programs: only an intrinsically accepted program can reach the closure stage.
data VerificationDisposition
  = StaticallyDischarged
  | RuntimeBound
  | ExternallyDischarged
  | AssumptionDependent
  | Exported
  | DeploymentExported
  | Unresolved
  deriving (Eq, Ord, Show)

data ApplicationAssurancePolicy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision :: AssurancePolicyRevision
  , applicationAssurancePolicyPermittedDispositions :: Set VerificationDisposition
  }
  deriving (Eq, Show)

-- | Competent intrinsic rejection.  No constructor carries an assurance
-- disposition, residual obligation, or VerificationBundle: rejection is a
-- terminal result of intrinsic checking, not an obligation-closure input.
data IntrinsicRejection
  = IntrinsicParseRejected ParseDiagnostic
  | IntrinsicComponentCardinalityRejected Int
  | IntrinsicSurfaceRejected SurfaceCheckError
  deriving (Eq, Show)

-- | VER-001's application-verification boundary.  VER-002 and later slices
-- will replace the successful payload with the canonical VerificationBundle
-- and exact residual obligation graph.  Until then, success exposes only the
-- already-checked semantic surface result plus the policy selected for the
-- *later* obligation-closure stage.
data ApplicationVerificationResult
  = IntrinsicRejected IntrinsicRejection
  | ReadyForObligationClosure
      { readyCheckedSurface :: SurfaceCheckResult
      , readyAssurancePolicy :: ApplicationAssurancePolicy
      }
  deriving (Eq, Show)

-- | Run competent intrinsic checking before assurance disposition.  In
-- particular, even a policy that permits every Phase-1 disposition cannot turn
-- parsing, component-shape, structural, protocol, authority, borrow, or other
-- surface semantic rejection into a residual obligation.
verifySurfaceApplication
  :: SurfaceEnvironment
  -> ApplicationAssurancePolicy
  -> Text
  -> Text
  -> ApplicationVerificationResult
verifySurfaceApplication environment policy sourceName source =
  case parseSurfaceFile sourceName source of
    Left diagnostic -> IntrinsicRejected (IntrinsicParseRejected diagnostic)
    Right (SurfaceFile [component]) ->
      case checkSurfaceComponent environment component of
        Left errorValue -> IntrinsicRejected (IntrinsicSurfaceRejected errorValue)
        Right checked -> ReadyForObligationClosure
          { readyCheckedSurface = checked
          , readyAssurancePolicy = policy
          }
    Right (SurfaceFile components) ->
      IntrinsicRejected (IntrinsicComponentCardinalityRejected (length components))
