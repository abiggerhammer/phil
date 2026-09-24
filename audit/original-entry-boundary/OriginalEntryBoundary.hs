{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified ClosureFixture as F
import qualified DirectFixture as DF
import qualified Phil.Assurance as A
import qualified Phil.Assurance.EvidenceFactAuthority as E
import qualified Phil.Assurance.Handoff as H
import qualified Phil.Assurance.Types as T
import qualified Phil.Assurance.Verify as AV
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import qualified Phil.Core.Discharge as D
import Phil.Core.Refinement (EvidenceUse (..), ResidualSpec (..))
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
import Phil.Core.Value (ValueResult (..), checkValue, checkValueWithResidual)
import qualified Phil.Verification as V
import qualified Phil.Verification.Bundle as B
import qualified Phil.Verification.ManifestClosure as M
import System.Exit (exitFailure)

-- Helpers only: both imported fixture modules retain their historical sources
-- apart from documented namespace/API adaptations. Their fabricated resolved
-- tree and original test mains are never used. All positive checked values,
-- ValueResults, resolved forests and certificates below are produced by Phil.
-- Evidence-entry packaging/semantic subject IDs remain explicit audit inputs.
data Package = Package
  { bundle :: B.VerificationBundle
  , policy :: V.ApplicationAssurancePolicy
  , context :: T.VerificationContext
  , ledger :: T.AssuranceLedger
  , selection :: M.ManifestClosureSelection
  , certificates :: Map.Map T.RevisionId T.EvidenceEntryId
  , directs :: Map.Map T.RevisionId T.EvidenceEntryId
  }

nativeClose :: H.HandoffConfig -> ResidualSpec -> D.DischargePolicy
  -> ValueResult -> Package -> Either A.OriginalCheckEventClosureError T.AssuranceManifest
nativeClose cfg spec disposition result p = A.closeOriginalCheckEventBundle cfg
  emptyStaticContext disposition spec result (bundle p) (policy p) (context p)
  (ledger p) (selection p) (certificates p) (directs p)

genericClose :: [H.LedgerHandoff] -> Package -> Either M.ManifestClosureError T.AssuranceManifest
genericClose entries p = M.closeVerificationBundleWithHandoff
  (bundle p) (policy p) (context p) (ledger p) (selection p)
  (M.ManifestClosureHandoff entries (certificates p) (directs p))

spec0 :: ResidualSpec
spec0 = ResidualSpec F.rootId "DefinednessClosureControls" "audit.closure.scope" "before-consumer"

actual :: D.DischargePolicy -> Proposition -> Either String (ValueResult,[H.LedgerHandoff])
actual disposition goal = do
  before <- F.natState
  result <- F.right $ checkValueWithResidual spec0 (VBool True)
    (TyRefined (Name "unused") TyBool goal) before
  F.ensure (resourceContext before == resourceContext (valueResultState result)) "source check changed ownership"
  resolved <- F.right $ A.resolveOriginalCheckEvent emptyStaticContext disposition spec0 result
  F.ensure (D.resolvedObligation resolved == F.rootFor goal) "original goal changed"
  entries <- F.right $ A.handoffOriginalCheckEvent F.config Map.empty
    emptyStaticContext disposition spec0 result
  exact <- F.right $ H.handoffResolvedObligation F.config resolved
  F.ensure (entries == exact) "event handoff differs from actual resolver forest"
  pure (result,entries)

runtimeEvent :: Proposition -> Either String (ValueResult,D.DischargePolicy,F.Fixture)
runtimeEvent goal = do
  disposition <- F.right $ D.bindRuntime F.runtimeBinding D.emptyDischargePolicy
  (result,entries) <- actual disposition goal
  case entries of
    [parent,child] -> do
      pe <- F.parentEvidence parent
      ce <- F.runtimeEvidence child
      F.ensure (H.handoffSupportEdges entries == Set.singleton (F.rev parent,F.rev child)) "required original support missing"
      pure (result,disposition,F.Fixture entries parent child [pe,ce]
        (Set.fromList [F.rev parent,F.rev child])
        (Set.fromList [F.parentId,F.runtimeId]) []
        (Set.fromList [V.StaticallyDischarged,V.RuntimeBound,V.Exported])
        (Set.singleton F.boundary))
    _ -> Left "wrong original-event inventory"

pack :: F.Fixture -> Set.Set (T.RevisionId,T.RevisionId) -> Either String Package
pack f support = do
  graph <- F.right $ V.buildVerificationRevisionGraphWithSupport
    (map H.handoffRevision (F.entries f)) support (F.scope f)
  let pol = V.ApplicationAssurancePolicy (V.AssurancePolicyRevision "audit.original-entry") (F.allowed f)
  b <- F.right $ B.buildVerificationBundle (T.digestText "audit.original-entry.source")
    [] [] [] graph pol (F.evidenceEntries f)
  let l = T.emptyLedger
        { T.ledgerRevisions = V.verificationGraphNodes graph
        , T.ledgerEvidence = Map.fromList [(T.evidenceEntryId e,e) | e <- F.evidenceEntries f]
        , T.ledgerExports = Map.fromList [(T.exportId e,e) | e <- F.exported f] }
      ctx = T.emptyVerificationContext
        { T.verificationArchitectureDigest = B.verificationBundleArchitectureDigest b
        , T.verificationPhilCoreDigest = T.digestText "audit.core"
        , T.verificationImplementationDigest = T.digestText "audit.implementation"
        , T.verificationTarget = "audit-target"
        , T.verificationCompilationProfile = "checked-runtime"
        , T.verificationExpectedObligations = Map.keysSet (V.verificationGraphNodes graph)
        , T.verificationLoweringLedgerRoot = T.digestText "audit.lowering"
        , T.verificationKnownCostRefs = Set.singleton F.cost
        , T.verificationPermittedExportBoundaries = F.permittedBoundaries f }
      sel = M.ManifestClosureSelection (F.selected f) Set.empty
        (Map.fromList [(T.exportId e,V.Exported) | e <- F.exported f]) Set.empty
      certs = Map.fromList [(F.rev h,F.parentId) | h <- F.entries f, isCertificate h]
  pure (Package b pol ctx l sel certs Map.empty)
  where
    isCertificate h = case H.handoffDisposition h of
      D.StaticallyDischarged D.StaticByCertificate {} -> True
      _ -> False

checkManifest :: F.Fixture -> T.AssuranceManifest -> Either String ()
checkManifest f m = do
  F.ensure (T.manifestObligationRevisions m == Set.fromList (map F.rev (F.entries f))) "manifest event inventory changed"
  F.ensure (T.manifestCertificationScope m == F.scope f) "manifest scope changed"
  F.ensure (T.manifestEvidenceEntries m == F.selected f) "manifest selection changed"
  F.ensure (T.manifestExports m == Set.fromList (map T.exportId (F.exported f))) "manifest exports changed"

fullScope :: Proposition -> Either String ()
fullScope goal = do
  (result,disp,f) <- runtimeEvent goal
  p <- pack f (H.handoffSupportEdges (F.entries f))
  m <- F.right $ nativeClose F.config spec0 disp result p
  checkManifest f m

exactError :: (Eq e, Show e, Show a) => e -> Either e a -> Either String ()
exactError expected result = case result of
  Left actualError | actualError == expected -> Right ()
  _ -> Left ("expected " <> show expected <> ", got " <> show result)

exportRequired :: Proposition -> Either String ()
exportRequired goal = do
  (result,disp,f) <- runtimeEvent goal
  p <- pack (F.exportChild f) (H.handoffSupportEdges (F.entries f))
  let underlying = if goal == F.definition
        then M.ManifestClosureHandoffRequiredSupportOutOfScope (F.rev (F.parent f)) (F.rev (F.prerequisite f))
        else M.ManifestClosureManifestRejected
          (AV.DependencyOnExportedObligation F.parentId (F.rev (F.prerequisite f)))
  exactError (A.OriginalCheckEventClosureManifestError underlying)
    (nativeClose F.config spec0 disp result p)

missingSupport :: Either String ()
missingSupport = do
  (result,disp,f) <- runtimeEvent F.definition
  p <- pack f Set.empty
  exactError (A.OriginalCheckEventClosureManifestError
      (M.ManifestClosureHandoffSupportMismatch (H.handoffSupportEdges (F.entries f)) Set.empty))
    (nativeClose F.config spec0 disp result p)

otherEvent :: Either String ()
otherEvent = do
  (original,disp,f) <- runtimeEvent F.definition
  (different,_,g) <- runtimeEvent F.algebra
  p <- pack g (H.handoffSupportEdges (F.entries g))
  F.ensure (valueResultType original /= valueResultType different) "events not different"
  _ <- F.right $ nativeClose F.config spec0 disp different p
  -- Revision keys do not replace equality of the full retained revision.
  -- Ordered validation may find the child's differing generation lineage
  -- before the absent parent. Require the exact first native disagreement,
  -- not an arbitrary rejection or an assumed diagnostic ordering.
  let expectedEntries = Map.fromList
        [(F.rev h,H.handoffRevision h) | h <- F.entries f]
      actualNodes = V.verificationGraphNodes (B.verificationBundleObligationGraph (bundle p))
      mismatches =
        [ err
        | (key,wanted) <- Map.toAscList expectedEntries
        , err <- case Map.lookup key actualNodes of
            Nothing -> [M.ManifestClosureHandoffRevisionMissing key]
            Just stored | stored /= wanted -> [M.ManifestClosureHandoffRevisionMismatch key]
            _ -> []
        ]
  case mismatches of
    expected : _ -> exactError (A.OriginalCheckEventClosureManifestError expected)
      (nativeClose F.config spec0 disp original p)
    [] -> Left "different-event fixture has no exact revision disagreement"

wrongScope :: Either String ()
wrongScope = do
  (result,disp,f) <- runtimeEvent F.definition
  p <- pack f (H.handoffSupportEdges (F.entries f))
  let changed = spec0 { residualScope = "another-scope" }
  exactError (A.OriginalCheckEventClosureResolutionError
      (A.OriginalCheckEventResidualMetadataMismatch F.childId changed F.child))
    (nativeClose F.config changed disp result p)

wholeTreeExport :: Either String ()
wholeTreeExport = do
  let ex o = D.ExportBinding (obligationId o) (obligationProposition o) (obligationRequiredPoint o) F.boundary
  childPolicy <- F.right $ D.bindExport (ex F.child) D.emptyDischargePolicy
  disp <- F.right $ D.bindExport (ex (F.rootFor F.definition)) childPolicy
  (result,entries) <- actual disp F.definition
  case entries of
    [parent,child] -> do
      F.ensure (H.handoffDisposition parent == D.Exported (ex (F.rootFor F.definition))) "parent not genuinely exported"
      F.ensure (H.handoffDisposition child == D.Exported (ex F.child)) "child not genuinely exported"
      let f = F.Fixture entries parent child [] Set.empty Set.empty
            [F.mkExport (T.ExportId "audit.parent.export") parent,F.mkExport F.childExportId child]
            (Set.singleton V.Exported) (Set.singleton F.boundary)
      p <- pack f (H.handoffSupportEdges entries)
      m <- F.right $ nativeClose F.config spec0 disp result p
      checkManifest f m
    _ -> Left "wrong whole-export inventory"

data Route = Direct | Arithmetic deriving (Eq,Show)

-- A closed value is independently checked, then its ACTUAL returned refined
-- type is installed. The following Bool check concerns that external original
-- subject; it does not invent a TyProof or an already-resolved tree.
evidenceEvent :: Route -> Either String (ResidualSpec,ValueResult,D.ResolvedObligation,Proposition)
evidenceEvent route = do
  let name = DF.proofName
      subject = Name "subject"
      sourcePredicate = case route of
        Direct -> Equal (RefVar subject) (RefBool True)
        Arithmetic -> LessEqual (RefToNat (RefVar subject)) (RefNat 1)
      base = if route == Direct then TyBool else TyUInt 8
      literal = if route == Direct then VBool True else VUInt 8 0
      sourceFact = case route of
        Direct -> Equal (RefVar name) (RefBool True)
        Arithmetic -> LessEqual (RefToNat (RefVar name)) (RefNat 1)
      goal = case route of
        Direct -> sourceFact
        Arithmetic -> LessThan (RefToNat (RefVar name)) (RefNat 5)
      s = ResidualSpec DF.consumerId "audit" DF.consumerScope "manifest-closure"
  source <- F.right $ checkValue literal (TyRefined subject base sourcePredicate) emptyCheckState
  bindings <- F.right $ insertBinding Unrestricted name (valueResultType source) (resourceContext emptyCheckState)
  let before = emptyCheckState { resourceContext = bindings }
  result <- F.right $ checkValueWithResidual s (VBool False)
    (TyRefined (Name "unused") TyBool goal) before
  F.ensure (resourceContext before == resourceContext (valueResultState result)) "original evidence binding changed"
  case route of
    Direct -> F.ensure (EvidenceByBinding name goal `elem` valueResultEvidence result) "actual direct use missing"
    Arithmetic -> F.ensure (EvidenceResidual DF.consumerId goal `elem` valueResultEvidence result) "actual arithmetic residual missing"
  resolved <- F.right $ A.resolveOriginalCheckEvent emptyStaticContext D.emptyDischargePolicy s result
  F.ensure (obligationProposition (D.resolvedObligation resolved) == goal) "resolved wrong actual fact"
  F.ensure (null (D.resolvedPrerequisites resolved)) "invented evidence prerequisite"
  case (route,D.resolvedDisposition resolved) of
    (Direct,D.StaticallyDischarged (D.StaticByEvidence actualName)) -> F.ensure (actualName == name) "selected another binding"
    (Arithmetic,D.StaticallyDischarged D.StaticByCertificate {}) -> Right ()
    other -> Left ("wrong actual discharge: " <> show other)
  pure (s,result,resolved,sourceFact)

authorityFixture :: Route -> Either String (ResidualSpec,ValueResult,D.ResolvedObligation,[H.LedgerHandoff],DF.Fixture)
authorityFixture route = do
  (s,result,resolved,sourceFact) <- evidenceEvent route
  let sourceRevision = DF.sourceRevision "actual-checked-value" sourceFact [DF.subjectId] DF.consumerScope
      sourceEvidence = DF.sealEvidence (DF.mkSourceEvidence DF.sourceEvidenceId sourceRevision)
      initialLedger = DF.sourceLedger sourceRevision sourceEvidence
      certAuthority = if route == Arithmetic then Map.singleton (DF.proofName,1)
        (E.EvidenceFactAuthorityBinding DF.sourceEvidenceId [DF.subjectId] DF.consumerScope) else Map.empty
      directAuthority = if route == Direct then DF.directAuthorities else Map.empty
  entries <- F.right $ E.handoffResolvedObligationWithAllEvidenceAuthority
    DF.handoffConfig certAuthority directAuthority initialLedger resolved
  entry <- DF.one entries
  F.ensure (H.handoffSupportDependencies entry == [T.DependsOnEvidence DF.sourceEvidenceId]) "precise immutable source dependency missing"
  let cr = H.handoffRevision entry
      rid = T.revisionId cr
  consumerEvidence <- F.right $ (if route == Direct then H.bindHandoffDirectEvidence else H.bindHandoffCertificateEvidence)
    entry (DF.mkConsumerEvidence rid)
  graph <- F.right $ V.buildVerificationRevisionGraphWithSupport
    [cr,sourceRevision] (H.handoffSupportEdges entries) (Set.fromList [rid,T.revisionId sourceRevision])
  let pol = V.ApplicationAssurancePolicy (V.AssurancePolicyRevision "audit.actual-evidence") (Set.singleton V.StaticallyDischarged)
  b <- F.right $ B.buildVerificationBundle (T.digestText "audit-direct-evidence-source") [] [] [] graph pol [consumerEvidence,sourceEvidence]
  let l = T.emptyLedger { T.ledgerRevisions = V.verificationGraphNodes graph
        , T.ledgerEvidence = Map.fromList [(DF.consumerEvidenceId,consumerEvidence),(DF.sourceEvidenceId,sourceEvidence)] }
      ctx = T.emptyVerificationContext
        { T.verificationArchitectureDigest = B.verificationBundleArchitectureDigest b
        , T.verificationPhilCoreDigest = T.digestText "audit.actual-evidence.core"
        , T.verificationImplementationDigest = T.digestText "audit.actual-evidence.impl"
        , T.verificationTarget = "audit-target"
        , T.verificationCompilationProfile = "checked-runtime"
        , T.verificationExpectedObligations = Map.keysSet (V.verificationGraphNodes graph)
        , T.verificationLoweringLedgerRoot = T.digestText "audit.actual-evidence.lowering" }
      sel = M.ManifestClosureSelection (Set.fromList [DF.consumerEvidenceId,DF.sourceEvidenceId]) Set.empty Map.empty Set.empty
      certs = if route == Arithmetic then Map.singleton rid DF.consumerEvidenceId else Map.empty
      ds = if route == Direct then Map.singleton rid DF.consumerEvidenceId else Map.empty
      f = DF.Fixture graph b pol ctx l sel (M.ManifestClosureHandoff entries certs ds) rid DF.consumerEvidenceId DF.sourceEvidenceId
  pure (s,result,resolved,entries,f)

fromDirectFixture :: DF.Fixture -> Package
fromDirectFixture f = Package (DF.fixtureBundle f) (DF.fixturePolicy f) (DF.fixtureContext f)
  (DF.fixtureLedger f) (DF.fixtureSelection f)
  (M.manifestClosureCertificateEvidence (DF.fixtureHandoff f))
  (M.manifestClosureDirectEvidence (DF.fixtureHandoff f))

authorityAccepts :: Route -> Either String ()
authorityAccepts route = do
  (_,_,_,entries,f) <- authorityFixture route
  m <- F.right $ genericClose entries (fromDirectFixture f)
  F.ensure (T.manifestEvidenceEntries m == Set.fromList [DF.consumerEvidenceId,DF.sourceEvidenceId]) "authority selection changed"
  e <- DF.consumerEvidence f
  F.ensure (T.evidenceDependsOn e == [T.DependsOnEvidence DF.sourceEvidenceId]) "final evidence dropped exact source"

boundedAuthorityRejection :: Route -> Either String ()
boundedAuthorityRejection route = do
  (s,result,_,entries,f) <- authorityFixture route
  _ <- F.right $ genericClose entries (fromDirectFixture f)
  let rid = DF.fixtureConsumerRevision f
      expected = case route of
        Direct -> A.OriginalCheckEventClosureManifestError
          (M.ManifestClosureHandoffEvidenceRejected rid DF.consumerEvidenceId (H.HandoffDirectEvidenceSupportMissing rid DF.proofName))
        Arithmetic -> A.OriginalCheckEventClosureResolutionError
          (A.OriginalCheckEventHandoffError (H.UnknownEvidenceFactSupport DF.consumerId DF.proofName 1))
  exactError expected $ nativeClose DF.handoffConfig s D.emptyDischargePolicy result (fromDirectFixture f)

wrongAuthorityEvent :: Either String ()
wrongAuthorityEvent = do
  (_,_,resolved,_,f) <- authorityFixture Direct
  let wrong = Map.singleton (ObligationId "other-event",DF.proofName) (H.DirectEvidenceAuthorityBinding DF.sourceEvidenceId)
  exactError (E.EvidenceFactAuthorityHandoffError (H.MissingDirectEvidenceAuthority DF.consumerId DF.proofName)) $
    E.handoffResolvedObligationWithAllEvidenceAuthority DF.handoffConfig Map.empty wrong (DF.fixtureLedger f) resolved

wrongFinalEvidence :: Either String ()
wrongFinalEvidence = do
  (_,_,_,entries,f) <- authorityFixture Direct
  source <- DF.sourceEvidence f
  let rid = DF.fixtureConsumerRevision f
      p = (fromDirectFixture f) { directs = Map.singleton rid DF.sourceEvidenceId }
  exactError (M.ManifestClosureHandoffEvidenceRejected rid DF.sourceEvidenceId
    (H.HandoffEvidenceRevisionMismatch rid (T.evidenceObligationRevision source))) $ genericClose entries p

droppedDirectSupport :: Either String ()
droppedDirectSupport = do
  (_,_,_,entries,f) <- authorityFixture Direct
  e <- DF.consumerEvidence f
  changed <- DF.rebuildConsumerEvidence f (DF.sealEvidence (e { T.evidenceDependsOn = [] }))
  exactError (M.ManifestClosureHandoffEvidenceMismatch (DF.fixtureConsumerRevision f) DF.consumerEvidenceId) $
    genericClose entries (fromDirectFixture changed)

main :: IO ()
main = do
  results <- sequence
    [ test "C01" "native original entry: definitional full scope" (fullScope F.definition)
    , test "C02" "native original entry: algebraic full scope" (fullScope F.algebra)
    , test "C03" "native original entry: explicit prerequisite full scope" (fullScope F.explicit)
    , test "C04" "native entry enforces definitional required-child scope" (exportRequired F.definition)
    , test "C05" "native entry enforces certificate required-child scope" (exportRequired F.algebra)
    , test "C06" "native entry rejects independently shrunken graph support" missingSupport
    , test "C07" "valid other-event bundle cannot replace this actual event" otherEvent
    , test "C08" "exact returned residual rejects changed scope metadata" wrongScope
    , test "C09" "genuine whole-event export is preserved" wholeTreeExport
    , test "C10" "actual direct use reaches immutable-authority final consumer" (authorityAccepts Direct)
    , test "C11" "bounded original entry rejects raw direct authority" (boundedAuthorityRejection Direct)
    , test "C12" "actual direct use rejects another-event authority" wrongAuthorityEvent
    , test "C13" "actual direct use rejects wrong final evidence revision" wrongFinalEvidence
    , test "C14" "actual direct use rejects dropped immutable support" droppedDirectSupport
    , test "C15" "actual arithmetic evidence reaches authoritative final consumer" (authorityAccepts Arithmetic)
    , test "C16" "bounded original entry rejects missing certificate fact authority" (boundedAuthorityRejection Arithmetic)
    ]
  putStrLn "COMPLETE correctness_groups=16"
  unless (and results) exitFailure

test :: String -> String -> Either String () -> IO Bool
test key label result = case result of
  Right () -> putStrLn ("PASS " <> key <> " " <> label) >> pure True
  Left err -> putStrLn ("FAIL " <> key <> " " <> label <> " -- " <> err) >> pure False
