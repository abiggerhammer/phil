{-# LANGUAGE OverloadedStrings #-}

-- External audit composition, not a production compiler/evidence exporter.
-- ResolvedObligation and DecisionCertificate are produced only by resolveObligation.
-- Ledger evidence and permitted export metadata are explicit fixture premises.
module Main (main) where

import Control.Monad (foldM, unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Phil.Assurance.Handoff as H
import qualified Phil.Assurance.Types as A
import qualified Phil.Assurance.Verify as AV
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import qualified Phil.Core.Discharge as D
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Mode (Unrestricted), Name (..), Obligation (..), ObligationId (..)
  , Proposition (..), RefSort (SortNat), RefTerm (..), Ty (..) )
import qualified Phil.Verification as V
import qualified Phil.Verification.Bundle as B
import qualified Phil.Verification.ManifestClosure as M
import System.Environment (getArgs)
import System.Exit (exitFailure)

right :: Show e => Either e a -> Either String a
right = either (Left . show) Right
ensure :: Bool -> String -> Either String ()
ensure True _ = Right ()
ensure False message = Left message

var :: Text -> RefTerm
var = RefVar . Name
side, algebra, definition, explicit :: Proposition
side = LessEqual (var "b") (var "a")
algebra = Equal (RefAdd (RefSub (var "a") (var "b")) (var "b")) (var "a")
definition = Equal difference difference where difference = RefSub (var "a") (var "b")
explicit = Conjunction definition side

rootId, childId :: ObligationId
rootId = ObligationId "audit.closure.root"
childId = ObligationId "audit.closure.root.nat-sub.1"
parentId, runtimeId :: A.EvidenceEntryId
parentId = A.EvidenceEntryId "audit.closure.parent"
runtimeId = A.EvidenceEntryId "audit.closure.runtime"
childExportId :: A.ExportId
childExportId = A.ExportId "audit.closure.export.child"
boundary, cost :: Text
boundary = "audit.explicit.external-boundary"
cost = "audit.closure.cost"

rootFor :: Proposition -> Obligation
rootFor proposition = Obligation rootId proposition "DefinednessClosureControls"
  "audit.closure.scope" "before-consumer"
child :: Obligation
child = (rootFor side) { obligationId = childId }

natState :: Either String CheckState
natState = foldM add emptyCheckState ["a", "b"]
  where
    add st name = do
      ctx <- right $ insertBinding Unrestricted (Name name)
        (TyOpaqueSorted "AuditNat" SortNat) (resourceContext st)
      Right st { resourceContext = ctx }

runtimeBinding :: D.RuntimeBinding
runtimeBinding = D.RuntimeBinding childId side (obligationRequiredPoint child)
  "declared-order-validator" (TyProof side) "ValidationFailure"
  "preserve unrelated resources; no continuation on failure" cost

resolve :: Proposition -> Either String D.ResolvedObligation
resolve goal = do
  st <- natState
  policy <- right $ D.bindRuntime runtimeBinding D.emptyDischargePolicy
  result <- right $ D.resolveObligation emptyStaticContext st policy (rootFor goal)
  ensure (D.resolvedObligation result == rootFor goal) "original obligation changed"
  case D.resolvedPrerequisites result of
    [r] -> do
      ensure (D.resolvedObligation r == child) "exact child changed"
      ensure (D.resolvedDisposition r == D.RuntimeBound runtimeBinding) "child disposition changed"
    _ -> Left "expected exactly the original runtime prerequisite"
  Right result

config :: H.HandoffConfig
config = H.HandoffConfig
  { H.handoffRevisionKind = const "AuditDefinednessClosure"
  , H.handoffRepresentation = const "Core"
  , H.handoffSubjectIds = const ["audit:a", "audit:b"]
  , H.handoffContextIds = const ["audit:context"]
  , H.handoffAcceptanceRule = \o ->
      if obligationId o == childId
        then A.AcceptEntry A.RuntimeEnforced (A.EvidenceRole "runtime")
        else A.AcceptEntry A.KernelChecked (A.EvidenceRole "establishes")
  }

seal :: A.EvidenceEntry -> A.EvidenceEntry
seal e = e { A.evidenceEntryDigest = A.deriveEvidenceEntryDigest e }
baseEvidence :: A.RevisionId -> A.EvidenceEntry
baseEvidence revision = A.EvidenceEntry
  { A.evidenceEntryId = parentId, A.evidenceEntryDigest = A.Digest ""
  , A.evidenceObligationRevision = revision, A.evidenceAssuranceKind = A.KernelChecked
  , A.evidenceRole = A.EvidenceRole "establishes"
  , A.evidenceProducer = "audit adapter of actual resolver result"
  , A.evidenceChecker = "Phil Core", A.evidenceArtifact = Nothing
  , A.evidenceInputDigests = [], A.evidenceAssumptions = [], A.evidenceDependsOn = []
  , A.evidenceValidityScope = A.ValidityScope Map.empty
  , A.evidenceResult = A.EvidenceAccepted
  , A.evidenceJustifies = ["conditional local result; exact returned prerequisites retained separately"]
  , A.evidenceRuntimeMechanism = Nothing, A.evidenceRuntimeResidue = [], A.evidenceCostRefs = [] }

-- For a definitional result this is an explicitly audit-owned metadata adapter;
-- no production general-purpose StaticByDefinition finalizer is claimed.
parentEvidence :: H.LedgerHandoff -> Either String A.EvidenceEntry
parentEvidence h = case H.handoffDisposition h of
  D.StaticallyDischarged D.StaticByCertificate {} ->
    right $ H.bindHandoffCertificateEvidence h (baseEvidence (rev h))
  D.StaticallyDischarged D.StaticByDefinition -> Right (seal (baseEvidence (rev h)))
  other -> Left ("unexpected parent disposition: " <> show other)

runtimeEvidence :: H.LedgerHandoff -> Either String A.EvidenceEntry
runtimeEvidence h = case H.handoffDisposition h of
  D.RuntimeBound actual | actual == runtimeBinding -> Right . seal $
    (baseEvidence (rev h))
      { A.evidenceEntryId = runtimeId, A.evidenceAssuranceKind = A.RuntimeEnforced
      , A.evidenceRole = A.EvidenceRole "runtime"
      , A.evidenceProducer = D.runtimeValidator actual
      , A.evidenceJustifies = [A.renderPropositionCanonical (D.runtimeProposition actual)]
      , A.evidenceRuntimeMechanism = Just A.RuntimeMechanism
          { A.runtimeMechanismName = D.runtimeValidator actual
          , A.runtimeExecutionPoint = D.runtimeRequiredPoint actual
          , A.runtimeSuccessEvidenceType = Text.pack (show (D.runtimeSuccessEvidence actual))
          , A.runtimeFailureContract = D.runtimeFailureClass actual <> ": " <> D.runtimeResourceContract actual
          , A.runtimeImplementation = Nothing }
      , A.evidenceRuntimeResidue = ["retain exact declared order check"]
      , A.evidenceCostRefs = [D.runtimeCostRef actual] }
  other -> Left ("unexpected runtime disposition: " <> show other)

rev :: H.LedgerHandoff -> A.RevisionId
rev = A.revisionId . H.handoffRevision

mkExport :: A.ExportId -> H.LedgerHandoff -> A.ExportEntry
mkExport key h = sealed
  where
    raw = A.ExportEntry key (A.Digest "") (rev h) boundary
      (ObligationId ("external:" <> unObligationId (A.revisionObligationId (H.handoffRevision h))))
      (A.ValidityScope Map.empty)
    sealed = raw { A.exportDigest = A.deriveExportDigest raw }

data Fixture = Fixture
  { entries :: [H.LedgerHandoff], parent :: H.LedgerHandoff, prerequisite :: H.LedgerHandoff
  , evidenceEntries :: [A.EvidenceEntry], scope :: Set.Set A.RevisionId
  , selected :: Set.Set A.EvidenceEntryId, exported :: [A.ExportEntry]
  , allowed :: Set.Set V.VerificationDisposition, permittedBoundaries :: Set.Set Text }

fixture :: Proposition -> Either String Fixture
fixture goal = do
  actual <- resolve goal
  hs <- right $ H.handoffResolvedObligation config actual
  (p,c) <- case hs of [p,c] -> Right (p,c); _ -> Left "handoff inventory changed"
  pe <- parentEvidence p
  ce <- runtimeEvidence c
  Right Fixture
    { entries = hs, parent = p, prerequisite = c, evidenceEntries = [pe,ce]
    , scope = Set.fromList [rev p,rev c], selected = Set.fromList [parentId,runtimeId]
    , exported = [], allowed = Set.fromList [V.StaticallyDischarged,V.RuntimeBound,V.Exported]
    , permittedBoundaries = Set.singleton boundary }

exportChild :: Fixture -> Fixture
exportChild f = f
  { scope = Set.singleton (rev (parent f)), selected = Set.singleton parentId
  , exported = [mkExport childExportId (prerequisite f)] }

-- This real closure receives every unchanged handoff node and original disposition.
-- All revisions/evidence are built and sealed by normal APIs. No stale identity
-- is used to substitute for the intended dependency/scope checks.
close :: Fixture -> Either String (Either M.ManifestClosureError A.AssuranceManifest)
close f = do
  graph <- right $ V.buildVerificationRevisionGraphWithSupport
    (map H.handoffRevision (entries f)) (H.handoffSupportEdges (entries f)) (scope f)
  let policy = V.ApplicationAssurancePolicy (V.AssurancePolicyRevision "audit.closure.policy") (allowed f)
  bundle <- right $ B.buildVerificationBundle (A.digestText "audit.closure.source")
    [] [] [] graph policy (evidenceEntries f)
  let ledger = A.emptyLedger
        { A.ledgerRevisions = V.verificationGraphNodes graph
        , A.ledgerEvidence = Map.fromList [(A.evidenceEntryId e,e) | e <- evidenceEntries f]
        , A.ledgerExports = Map.fromList [(A.exportId e,e) | e <- exported f] }
      context = A.emptyVerificationContext
        { A.verificationArchitectureDigest = B.verificationBundleArchitectureDigest bundle
        , A.verificationPhilCoreDigest = A.digestText "audit.closure.core"
        , A.verificationImplementationDigest = A.digestText "audit.closure.implementation"
        , A.verificationTarget = "audit-target", A.verificationCompilationProfile = "checked-runtime"
        , A.verificationExpectedObligations = Map.keysSet (V.verificationGraphNodes graph)
        , A.verificationLoweringLedgerRoot = A.digestText "audit.closure.lowering"
        , A.verificationKnownCostRefs = Set.singleton cost
        , A.verificationPermittedExportBoundaries = permittedBoundaries f }
      selection = M.ManifestClosureSelection (selected f) Set.empty
        (Map.fromList [(A.exportId e,V.Exported) | e <- exported f]) Set.empty
      certificateEntries = [h | h <- entries f, isCertificate h]
      handoff = M.ManifestClosureHandoff (entries f)
        (Map.fromList [(rev h,parentId) | h <- certificateEntries])
  Right $ M.closeVerificationBundleWithHandoff bundle policy context ledger selection handoff
  where
    isCertificate h = case H.handoffDisposition h of
      D.StaticallyDischarged D.StaticByCertificate {} -> True
      _ -> False

accepts :: Fixture -> Either String ()
accepts f = do
  result <- close f
  manifest <- right result
  ensure (A.manifestObligationRevisions manifest == Set.fromList (map rev (entries f))) "manifest dropped nodes"
  ensure (A.manifestCertificationScope manifest == scope f) "manifest changed scope"
  ensure (A.manifestEvidenceEntries manifest == selected f) "manifest changed selected evidence"
  ensure (A.manifestExports manifest == Set.fromList (map A.exportId (exported f))) "manifest changed exports"

rejects :: (M.ManifestClosureError -> Bool) -> Fixture -> Either String ()
rejects expected f = do
  result <- close f
  case result of
    Left err | expected err -> Right ()
    other -> Left ("wrong final closure result: " <> show other)

controls :: [(String, Either String ())]
controls =
  [ ("C01",fixture algebra >>= accepts)
  , ("C02",fixture definition >>= accepts)
  , ("C03",fixture explicit >>= accepts)
  , ("C04",do f <- fixture algebra
               rejects (\e -> e == M.ManifestClosureManifestRejected (AV.AcceptanceRuleUnsatisfied (rev (prerequisite f))))
                 f { selected = Set.singleton parentId })
  , ("C05",do f <- fixture algebra
               rejects (\e -> e == M.ManifestClosureManifestRejected (AV.OutOfScopeObligationNotExported (rev (prerequisite f))))
                 f { scope = Set.singleton (rev (parent f)), selected = Set.singleton parentId })
  , ("C06",do f <- fixture explicit
               ensure (H.handoffSupportDependencies (parent f) == [A.DependsOnObligation (rev (prerequisite f))]) "explicit support prerequisite not produced"
               rejects (\e -> e == M.ManifestClosureManifestRejected (AV.DependencyOnExportedObligation parentId (rev (prerequisite f)))) (exportChild f))
  , ("C07",do f <- fixture algebra
               rejects (\e -> e == M.ManifestClosureManifestRejected (AV.UnpermittedExportBoundary childExportId boundary))
                 (exportChild f) { permittedBoundaries = Set.empty })
  , ("C08",do f <- fixture algebra
               rejects (== M.ManifestClosureUnpermittedDisposition V.RuntimeBound)
                 f { allowed = Set.delete V.RuntimeBound (allowed f) })
  , ("C09",do f <- fixture algebra
               let change e = if A.evidenceEntryId e == runtimeId
                     then seal (e { A.evidenceRuntimeMechanism = Nothing })
                     else e
               rejects (== M.ManifestClosureManifestRejected (AV.RuntimeEvidenceMissingMechanism runtimeId))
                 f { evidenceEntries = map change (evidenceEntries f) })
  ]

observation :: Proposition -> Either String String
observation goal = do
  f <- fixture goal
  result <- close (exportChild f)
  Right $ "parent=" <> show (H.handoffDisposition (parent f))
    <> " child=" <> show (H.handoffDisposition (prerequisite f))
    <> " support=" <> show (H.handoffSupportEdges (entries f))
    <> " closure=" <> show result

requireFix :: Proposition -> Either String ()
requireFix goal = do
  f <- fixture goal
  -- A complete dependency carrier may reject/reclassify this incompatible
  -- final export request, but must not reject the legitimate full-scope case.
  accepts f
  result <- close (exportChild f)
  case result of
    Left (M.ManifestClosureManifestRejected (AV.DependencyOnExportedObligation owner required))
      | owner == parentId, required == rev (prerequisite f) -> Right ()
    other -> Left ("expected exact retained-prerequisite rejection; alternate repaired boundary needs reviewed oracle: " <> show other)

emit :: String -> Either String () -> IO Bool
emit key result = case result of
  Right () -> putStrLn ("PASS " <> key) >> pure True
  Left why -> putStrLn ("FAIL " <> key <> " " <> why) >> pure False
emitObservation :: String -> Either String String -> IO Bool
emitObservation key result = case result of
  Right value -> putStrLn ("OBS " <> key <> " " <> value) >> pure True
  Left why -> putStrLn ("OBS_SETUP_ERROR " <> key <> " " <> why) >> pure False

supportCheck :: Proposition -> Either String ()
supportCheck goal = do
  f <- fixture goal
  ensure (Set.member (rev (parent f), rev (prerequisite f)) (H.handoffSupportEdges (entries f)))
    ("required definedness dependency absent: " <> show (H.handoffDisposition (parent f)))

main :: IO ()
main = do
  args <- getArgs
  if args == ["--support"]
    then do
      results <- sequence [emit "R01" (supportCheck algebra), emit "R02" (supportCheck definition)]
      unless (and results) exitFailure
      putStrLn "COMPLETE support_regressions=2"
    else runClosure args

runClosure :: [String] -> IO ()
runClosure args = do
  observe <- case args of
    [] -> pure False
    ["--require-fix"] -> pure False
    ["--observe"] -> pure True
    _ -> putStrLn "usage: DefinednessClosureControls [--observe|--require-fix]" >> exitFailure
  cs <- mapM (uncurry emit) controls
  rs <- if observe
    then sequence [emitObservation "O01" (observation algebra),emitObservation "O02" (observation definition)]
    else sequence [emit "R01" (requireFix algebra),emit "R02" (requireFix definition)]
  unless (and cs && and rs) exitFailure
  putStrLn (if observe then "COMPLETE controls=9 observations=2" else "COMPLETE controls=9 regressions=2")
