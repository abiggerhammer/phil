{-# LANGUAGE OverloadedStrings #-}

module Phil.Verification.Bundle
  ( IntrinsicVerificationResult (..)
  , AcceptedEvidenceReference (..)
  , VerificationBundle (..)
  , VerificationBundleError (..)
  , buildVerificationBundle
  ) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types
  ( Digest (..)
  , EvidenceEntry (..)
  , EvidenceEntryId (..)
  , EvidenceResult (..)
  , RevisionId (..)
  , deriveEvidenceEntryDigest
  , digestText
  )
import Phil.Core.Static
  ( ArchitectureInstanceIdentity (..)
  , ArchitectureRealizationIdentity (..)
  , DeclarationIdentity (..)
  , DeclarationKey (..)
  , DefinitionRevision (..)
  , InstanceKey (..)
  , InstanceRevision (..)
  , InterfaceRevision (..)
  , RealizationRevision (..)
  )
import Phil.Verification
  ( ApplicationAssurancePolicy (..)
  , AssurancePolicyRevision (..)
  , VerificationObligationGraph (..)
  )

-- | Intrinsic rejection remains terminal under VER-001, so only an
-- intrinsically accepted application can possess a VerificationBundle.  The
-- explicit result marker is nevertheless carried in the bundle schema so an
-- independent implementation does not have to infer acceptance from Haskell
-- constructor reachability.
data IntrinsicVerificationResult
  = IntrinsicVerificationAccepted
  deriving (Eq, Ord, Show)

-- | Exact accepted evidence reference exposed to an independent verifier.
-- Producer traversal/search strategy and witness display names are deliberately
-- absent.  The EvidenceEntry digest content-binds the accepted evidence's
-- competence, producer/checker, artifact, assumptions, dependencies, validity
-- scope, runtime residue, and other assurance-bearing inputs in ADR-010.
data AcceptedEvidenceReference = AcceptedEvidenceReference
  { acceptedEvidenceEntryId :: EvidenceEntryId
  , acceptedEvidenceDigest :: Digest
  , acceptedEvidenceObligationRevision :: RevisionId
  }
  deriving (Eq, Ord, Show)

-- | VER-012's stable, inspectable Phase-1 verification target.  All container
-- fields use semantic sets/maps.  Source, declaration, architecture, obligation
-- graph, policy, and accepted-evidence identities are exposed directly rather
-- than hidden behind Haskell object identity or traversal order.
data VerificationBundle = VerificationBundle
  { verificationBundleRevision :: Digest
  , verificationBundleSourceRevision :: Digest
  , verificationBundleDeclarations :: Set DeclarationIdentity
  , verificationBundleArchitectureInstances :: Set ArchitectureInstanceIdentity
  , verificationBundleArchitectureRealizations :: Set ArchitectureRealizationIdentity
  , verificationBundleIntrinsicResult :: IntrinsicVerificationResult
  , verificationBundleObligationGraph :: VerificationObligationGraph
  , verificationBundlePolicyRevision :: AssurancePolicyRevision
  , verificationBundleAcceptedEvidence
      :: Map EvidenceEntryId AcceptedEvidenceReference
  }
  deriving (Eq, Show)

data VerificationBundleError
  = EmptyVerificationSourceRevision
  | EmptyVerificationPolicyRevision
  | VerificationEvidenceRejected EvidenceEntryId Text
  | VerificationEvidenceDigestMismatch EvidenceEntryId Digest Digest
  | VerificationEvidenceUnknownObligation EvidenceEntryId RevisionId
  | ConflictingVerificationEvidenceReference EvidenceEntryId
  deriving (Eq, Show)

-- | Construct the exact Phase-1 verification target from already competent
-- semantic identities.  Input list order is explicitly nonsemantic.  Rejected
-- or stale evidence cannot enter the bundle, and one stable evidence-entry ID
-- cannot be rebound to different accepted evidence content.
buildVerificationBundle
  :: Digest
  -> [DeclarationIdentity]
  -> [ArchitectureInstanceIdentity]
  -> [ArchitectureRealizationIdentity]
  -> VerificationObligationGraph
  -> ApplicationAssurancePolicy
  -> [EvidenceEntry]
  -> Either VerificationBundleError VerificationBundle
buildVerificationBundle sourceRevision declarations instances realizations graph policy rawEvidence = do
  validateSourceRevision sourceRevision
  validatePolicyRevision policyRevision
  evidence <- foldM (insertEvidenceReference graph) Map.empty rawEvidence
  let declarationSet = Set.fromList declarations
      instanceSet = Set.fromList instances
      realizationSet = Set.fromList realizations
      provisional = VerificationBundle
        { verificationBundleRevision = Digest ""
        , verificationBundleSourceRevision = sourceRevision
        , verificationBundleDeclarations = declarationSet
        , verificationBundleArchitectureInstances = instanceSet
        , verificationBundleArchitectureRealizations = realizationSet
        , verificationBundleIntrinsicResult = IntrinsicVerificationAccepted
        , verificationBundleObligationGraph = graph
        , verificationBundlePolicyRevision = policyRevision
        , verificationBundleAcceptedEvidence = evidence
        }
  Right provisional
    { verificationBundleRevision = deriveVerificationBundleRevision provisional }
  where
    policyRevision = applicationAssurancePolicyRevision policy

validateSourceRevision :: Digest -> Either VerificationBundleError ()
validateSourceRevision (Digest sourceRevision)
  | Text.null (Text.strip sourceRevision) = Left EmptyVerificationSourceRevision
  | otherwise = Right ()

validatePolicyRevision :: AssurancePolicyRevision -> Either VerificationBundleError ()
validatePolicyRevision (AssurancePolicyRevision policyRevision)
  | Text.null (Text.strip policyRevision) = Left EmptyVerificationPolicyRevision
  | otherwise = Right ()

insertEvidenceReference
  :: VerificationObligationGraph
  -> Map EvidenceEntryId AcceptedEvidenceReference
  -> EvidenceEntry
  -> Either VerificationBundleError (Map EvidenceEntryId AcceptedEvidenceReference)
insertEvidenceReference graph references entry = do
  reference <- acceptedReference graph entry
  case Map.lookup entryId references of
    Nothing -> Right (Map.insert entryId reference references)
    Just existing
      | existing == reference -> Right references
      | otherwise -> Left (ConflictingVerificationEvidenceReference entryId)
  where
    entryId = evidenceEntryId entry

acceptedReference
  :: VerificationObligationGraph
  -> EvidenceEntry
  -> Either VerificationBundleError AcceptedEvidenceReference
acceptedReference graph entry = do
  case evidenceResult entry of
    EvidenceAccepted -> Right ()
    EvidenceRejected reason -> Left
      (VerificationEvidenceRejected entryId reason)
  let expectedDigest = deriveEvidenceEntryDigest entry
      actualDigest = evidenceEntryDigest entry
  if expectedDigest == actualDigest
    then Right ()
    else Left
      (VerificationEvidenceDigestMismatch entryId expectedDigest actualDigest)
  if Map.member targetRevision (verificationGraphNodes graph)
    then Right ()
    else Left
      (VerificationEvidenceUnknownObligation entryId targetRevision)
  Right AcceptedEvidenceReference
    { acceptedEvidenceEntryId = entryId
    , acceptedEvidenceDigest = actualDigest
    , acceptedEvidenceObligationRevision = targetRevision
    }
  where
    entryId = evidenceEntryId entry
    targetRevision = evidenceObligationRevision entry

-- | Bundle identity is a canonical semantic projection.  The graph revision
-- already content-binds normalized obligation nodes, dependencies, and scope;
-- each accepted evidence digest content-binds its full evidence record.  This
-- keeps the bundle compact while retaining exact references an independent
-- implementation can resolve and check.
deriveVerificationBundleRevision :: VerificationBundle -> Digest
deriveVerificationBundleRevision bundle = digestText (Text.intercalate "\n"
  [ "verification-bundle-v1"
  , "source=" <> unDigest (verificationBundleSourceRevision bundle)
  , "intrinsic=accepted"
  , "declarations=" <> Text.intercalate ","
      (map renderDeclaration
        (Set.toAscList (verificationBundleDeclarations bundle)))
  , "instances=" <> Text.intercalate ","
      (map renderInstance
        (Set.toAscList (verificationBundleArchitectureInstances bundle)))
  , "realizations=" <> Text.intercalate ","
      (map renderRealization
        (Set.toAscList (verificationBundleArchitectureRealizations bundle)))
  , "obligation_graph=" <> unDigest
      (verificationGraphRevision (verificationBundleObligationGraph bundle))
  , "policy=" <> unAssurancePolicyRevision
      (verificationBundlePolicyRevision bundle)
  , "evidence=" <> Text.intercalate ","
      (map renderEvidence
        (Map.toAscList (verificationBundleAcceptedEvidence bundle)))
  ])
  where
    renderDeclaration identity = Text.intercalate "@"
      [ unDeclarationKey (identityDeclarationKey identity)
      , unInterfaceRevision (identityInterfaceRevision identity)
      , unDefinitionRevision (identityDefinitionRevision identity)
      ]

    renderInstance identity = Text.intercalate "@"
      [ unInstanceKey (identityInstanceKey identity)
      , unInstanceRevision (identityInstanceRevision identity)
      ]

    renderRealization identity =
      unRealizationRevision (identityRealizationRevision identity)

    renderEvidence (entryId, reference) = Text.intercalate "@"
      [ unEvidenceEntryId entryId
      , unDigest (acceptedEvidenceDigest reference)
      , unRevisionId (acceptedEvidenceObligationRevision reference)
      ]
