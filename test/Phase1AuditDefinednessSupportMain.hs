{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import Phil.Core.Discharge
  ( ObligationDisposition (..)
  , ResolvedObligation (..)
  , RuntimeBinding (..)
  , StaticDischarge (..)
  , bindRuntime
  , emptyDischargePolicy
  , resolveObligation
  )
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Mode (Unrestricted)
  , Name (Name)
  , Obligation (..)
  , ObligationId (ObligationId)
  , Proposition (..)
  , RefSort (SortNat)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Verification
  ( VerificationObligationGraph (..)
  , buildVerificationRevisionGraphWithSupport
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "R01 empty arithmetic certificate retains resolver prerequisite support"
        certificateDefinednessSupport
    , test "R02 definitionally discharged parent retains resolver prerequisite support"
        definitionDefinednessSupport
    , test "C01 pure arithmetic does not acquire spurious prerequisite support"
        pureArithmeticSupport
    , test "C02 retained support is the exact verification graph relation"
        graphUsesRetainedSupport
    , test "C03 certificate evidence finalization carries retained definedness support"
        certificateEvidenceUsesRetainedSupport
    ]
  unless (and results) exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

name :: Text -> Name
name = Name

var :: Text -> RefTerm
var = RefVar . name

natTy :: Ty
natTy = TyOpaqueSorted "NatValue" SortNat

obligation :: Text -> Proposition -> Obligation
obligation identifier proposition = Obligation
  { obligationId = ObligationId identifier
  , obligationProposition = proposition
  , obligationOrigin = "Phase1AuditDefinednessSupportMain"
  , obligationScope = "audit.definedness-support"
  , obligationRequiredPoint = "before-audit-operation"
  }

withBinding :: Name -> Ty -> CheckState -> Either String CheckState
withBinding binding ty state = do
  context <- mapLeft show $
    insertBinding Unrestricted binding ty (resourceContext state)
  Right state { resourceContext = context }

withNats :: Either String CheckState
withNats = do
  state <- withBinding (name "a") natTy emptyCheckState
  withBinding (name "b") natTy state

runtimeFor :: Obligation -> Proposition -> RuntimeBinding
runtimeFor target proposition = RuntimeBinding
  { runtimeObligationId = obligationId target
  , runtimeProposition = proposition
  , runtimeRequiredPoint = obligationRequiredPoint target
  , runtimeValidator = "audit-definedness-validator"
  , runtimeSuccessEvidence = TyProof proposition
  , runtimeFailureClass = "ValidationFailure"
  , runtimeResourceContract = "no ownership change"
  , runtimeCostRef = "audit.definedness.runtime"
  }

handoffConfig :: HandoffConfig
handoffConfig = HandoffConfig
  { handoffRevisionKind = const "Audit"
  , handoffRepresentation = const "Core"
  , handoffSubjectIds = const ["subject:a", "subject:b"]
  , handoffContextIds = const ["context:audit-definedness"]
  , handoffAcceptanceRule = const
      (AcceptEntry KernelChecked (EvidenceRole "definedness-support"))
  }

resolveSubtractionCase
  :: Text
  -> Proposition
  -> Either String (ResolvedObligation, [LedgerHandoff])
resolveSubtractionCase identifier proposition = do
  state <- withNats
  let target = obligation identifier proposition
      sideId = ObligationId (identifier <> ".nat-sub.1")
      sideProposition = LessEqual (var "b") (var "a")
      side = target
        { obligationId = sideId
        , obligationProposition = sideProposition
        }
      runtime = runtimeFor side sideProposition
  policy <- mapLeft show $ bindRuntime runtime emptyDischargePolicy
  resolved <- mapLeft show $
    resolveObligation emptyStaticContext state policy target
  entries <- mapLeft show $ handoffResolvedObligation handoffConfig resolved
  Right (resolved, entries)

supportPair
  :: [LedgerHandoff]
  -> Either String (LedgerHandoff, LedgerHandoff, (RevisionId, RevisionId))
supportPair entries = case entries of
  [parent, child] ->
    let edge = (revisionId (handoffRevision parent), revisionId (handoffRevision child))
    in Right (parent, child, edge)
  other -> Left ("expected exactly one parent and one prerequisite, got " <> show other)

certificateDefinednessSupport :: Either String ()
certificateDefinednessSupport = do
  let difference = RefSub (var "a") (var "b")
      proposition = Equal (RefAdd difference (var "b")) (var "a")
  (resolved, entries) <- resolveSubtractionCase "audit.definedness.certificate" proposition
  case resolvedDisposition resolved of
    StaticallyDischarged StaticByCertificate {} -> Right ()
    other -> Left ("expected checked arithmetic certificate, got " <> show other)
  (parent, _child, edge@(_parentRevision, childRevision)) <- supportPair entries
  unless (handoffSupportEdges entries == Set.singleton edge) $
    Left ("resolver prerequisite support was not retained: " <> show (handoffSupportEdges entries))
  unless (handoffSupportDependencies parent == [DependsOnObligation childRevision]) $
    Left ("parent handoff did not carry exact prerequisite revision: "
      <> show (handoffSupportDependencies parent))

-- The proposition is definitionally true only after focusing has exposed the
-- subtraction side condition.  The child must therefore remain semantic
-- support even though there is no decision-certificate syntax to mention it.
definitionDefinednessSupport :: Either String ()
definitionDefinednessSupport = do
  let difference = RefSub (var "a") (var "b")
      proposition = Equal difference difference
  (resolved, entries) <- resolveSubtractionCase "audit.definedness.definition" proposition
  case resolvedDisposition resolved of
    StaticallyDischarged StaticByDefinition -> Right ()
    other -> Left ("expected definitionally discharged parent, got " <> show other)
  (_parent, _child, edge) <- supportPair entries
  unless (handoffSupportEdges entries == Set.singleton edge) $
    Left ("definitionally discharged prerequisite support was lost: "
      <> show (handoffSupportEdges entries))

pureArithmeticSupport :: Either String ()
pureArithmeticSupport = do
  state <- withNats
  let target = obligation "audit.definedness.pure"
        (LessEqual (var "a") (RefAdd (var "a") (RefNat 1)))
  resolved <- mapLeft show $
    resolveObligation emptyStaticContext state emptyDischargePolicy target
  entries <- mapLeft show $ handoffResolvedObligation handoffConfig resolved
  unless (null (resolvedPrerequisites resolved)) $
    Left ("pure arithmetic unexpectedly produced prerequisites: "
      <> show (resolvedPrerequisites resolved))
  unless (Set.null (handoffSupportEdges entries)) $
    Left ("pure arithmetic acquired spurious support: "
      <> show (handoffSupportEdges entries))

graphUsesRetainedSupport :: Either String ()
graphUsesRetainedSupport = do
  let difference = RefSub (var "a") (var "b")
      proposition = Equal difference difference
  (_resolved, entries) <- resolveSubtractionCase "audit.definedness.graph" proposition
  graph <- mapLeft show $ buildVerificationRevisionGraphWithSupport
    (map handoffRevision entries)
    (handoffSupportEdges entries)
    Set.empty
  unless (verificationGraphDependencies graph == handoffSupportEdges entries) $
    Left "verification graph did not preserve exact retained support"

certificateEvidenceUsesRetainedSupport :: Either String ()
certificateEvidenceUsesRetainedSupport = do
  let difference = RefSub (var "a") (var "b")
      proposition = Equal (RefAdd difference (var "b")) (var "a")
  (_resolved, entries) <- resolveSubtractionCase "audit.definedness.evidence" proposition
  (parent, _child, (_parentRevision, childRevision)) <- supportPair entries
  let provisional = evidenceFor (revisionId (handoffRevision parent))
  finalized <- mapLeft show $ bindHandoffCertificateEvidence parent provisional
  unless (evidenceDependsOn finalized == [DependsOnObligation childRevision]) $
    Left ("final certificate evidence lost resolver support: "
      <> show (evidenceDependsOn finalized))
  unless (evidenceEntryDigest finalized == deriveEvidenceEntryDigest finalized) $
    Left "final certificate evidence digest was not rebound"

evidenceFor :: RevisionId -> EvidenceEntry
evidenceFor revision = EvidenceEntry
  { evidenceEntryId = EvidenceEntryId "evidence.audit.definedness.parent"
  , evidenceEntryDigest = Digest "stale-before-handoff"
  , evidenceObligationRevision = revision
  , evidenceAssuranceKind = KernelChecked
  , evidenceRole = EvidenceRole "definedness-support"
  , evidenceProducer = "Phil Core certificate checker"
  , evidenceChecker = "Phil Core"
  , evidenceArtifact = Nothing
  , evidenceInputDigests = []
  , evidenceAssumptions = []
  , evidenceDependsOn = []
  , evidenceValidityScope = ValidityScope mempty
  , evidenceResult = EvidenceAccepted
  , evidenceJustifies = ["checked arithmetic certificate"]
  , evidenceRuntimeMechanism = Nothing
  , evidenceRuntimeResidue = []
  , evidenceCostRefs = []
  }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
