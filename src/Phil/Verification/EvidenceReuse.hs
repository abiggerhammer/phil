{-# LANGUAGE OverloadedStrings #-}

module Phil.Verification.EvidenceReuse
  ( ReusableProofEvidence
  , reusableCheckedProofEvidence
  , reusableProofDependencies
  , reusableProofValidityScope
  , EvidenceReuseError (..)
  , EvidenceReuseStaleness (..)
  , EvidenceReuseDecision (..)
  , prepareReusableProofEvidence
  , evaluateReusableProofEvidence
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
  ( Digest
  , RevisionId
  , ValidityScope (..)
  )
import Phil.Verification
  ( VerificationObligationGraph (..)
  )
import Phil.Verification.ProofEvidence
  ( CheckedProofEvidence
  , checkedProofGraphRevision
  , checkedProofObligationRevision
  )

-- | Opaque cacheable form of already checked proof evidence.  The origin graph
-- revision is deliberately not a reuse key: it is only used while preparing the
-- record, to ensure dependency identity is captured from the graph in which the
-- evidence was actually accepted.  Later reuse is scoped to the exact target,
-- that target's dependencies, and the explicitly declared validity dimensions.
data ReusableProofEvidence = ReusableProofEvidence
  { reusableCheckedProofEvidence :: CheckedProofEvidence
  , reusableProofDependencies :: Set RevisionId
  , reusableProofValidityScope :: ValidityScope
  }
  deriving (Eq, Show)

data EvidenceReuseError
  = ReusePreparationGraphRevisionMismatch Digest Digest
  | ReusePreparationUnknownRevision RevisionId
  | ReusePreparationOutsideCertificationScope RevisionId
  | ReusePreparationMalformedValidityDimension Text
  deriving (Eq, Show)

data EvidenceReuseStaleness
  = ReuseTargetRevisionUnavailable RevisionId
  | ReuseTargetOutsideCertificationScope RevisionId
  | ReuseDependencySetChanged (Set RevisionId) (Set RevisionId)
  | ReuseValidityDimensionMissing Text Text
  | ReuseValidityDimensionChanged Text Text Text
  deriving (Eq, Show)

data EvidenceReuseDecision
  = EvidenceReusable
  | EvidenceStale [EvidenceReuseStaleness]
  deriving (Eq, Show)

-- | Prepare accepted evidence for later reuse.  This must happen against the
-- exact graph revision in which the evidence was checked, preventing a caller
-- from rebinding old evidence to a changed dependency graph before caching it.
prepareReusableProofEvidence
  :: VerificationObligationGraph
  -> ValidityScope
  -> CheckedProofEvidence
  -> Either EvidenceReuseError ReusableProofEvidence
prepareReusableProofEvidence graph validityScope checked = do
  let expectedGraph = checkedProofGraphRevision checked
      actualGraph = verificationGraphRevision graph
      target = checkedProofObligationRevision checked
  if actualGraph == expectedGraph
    then Right ()
    else Left (ReusePreparationGraphRevisionMismatch expectedGraph actualGraph)
  if Map.member target (verificationGraphNodes graph)
    then Right ()
    else Left (ReusePreparationUnknownRevision target)
  if Set.member target (verificationGraphCertificationScope graph)
    then Right ()
    else Left (ReusePreparationOutsideCertificationScope target)
  validateValidityScope validityScope
  Right ReusableProofEvidence
    { reusableCheckedProofEvidence = checked
    , reusableProofDependencies = targetDependencies graph target
    , reusableProofValidityScope = validityScope
    }

-- | Decide whether cached evidence is reusable in the current semantic context.
-- Whole-graph identity is intentionally ignored.  An unrelated obligation or
-- an undeclared context dimension may change without invalidating this evidence.
-- Every dimension declared by the cached evidence must still match exactly.
evaluateReusableProofEvidence
  :: VerificationObligationGraph
  -> ValidityScope
  -> ReusableProofEvidence
  -> EvidenceReuseDecision
evaluateReusableProofEvidence graph (ValidityScope currentDimensions) reusable =
  case reasons of
    [] -> EvidenceReusable
    _ -> EvidenceStale reasons
  where
    checked = reusableCheckedProofEvidence reusable
    target = checkedProofObligationRevision checked
    targetPresent = Map.member target (verificationGraphNodes graph)
    targetInScope = Set.member target (verificationGraphCertificationScope graph)
    expectedDependencies = reusableProofDependencies reusable
    currentDependencies = targetDependencies graph target
    targetReasons
      | not targetPresent = [ReuseTargetRevisionUnavailable target]
      | otherwise =
          [ ReuseTargetOutsideCertificationScope target
          | not targetInScope
          ]
          ++ [ ReuseDependencySetChanged expectedDependencies currentDependencies
             | expectedDependencies /= currentDependencies
             ]
    ValidityScope expectedDimensions = reusableProofValidityScope reusable
    validityReasons = concatMap checkDimension (Map.toAscList expectedDimensions)
    checkDimension (dimension, expectedValue) =
      case Map.lookup dimension currentDimensions of
        Nothing -> [ReuseValidityDimensionMissing dimension expectedValue]
        Just actualValue
          | actualValue == expectedValue -> []
          | otherwise ->
              [ReuseValidityDimensionChanged dimension expectedValue actualValue]
    reasons = targetReasons ++ validityReasons

validateValidityScope :: ValidityScope -> Either EvidenceReuseError ()
validateValidityScope (ValidityScope dimensions) =
  case [ key | (key, value) <- Map.toAscList dimensions, blank key || blank value ] of
    [] -> Right ()
    key : _ -> Left (ReusePreparationMalformedValidityDimension key)
  where
    blank = Text.null . Text.strip

targetDependencies :: VerificationObligationGraph -> RevisionId -> Set RevisionId
targetDependencies graph target = Set.fromList
  [ dependency
  | (owner, dependency) <- Set.toAscList (verificationGraphDependencies graph)
  , owner == target
  ]
