{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified ClosureFixture as F
import qualified Phil.Assurance as A
import qualified Phil.Assurance.Handoff as H
import qualified Phil.Assurance.Types as T
import qualified Phil.Assurance.Verify as AV
import Phil.Core.Checker (CheckState (..))
import qualified Phil.Core.Discharge as D
import Phil.Core.Refinement (ResidualSpec (..))
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
import Phil.Core.Value (ValueResult (..), checkValueWithResidual)
import qualified Phil.Verification as V
import qualified Phil.Verification.ManifestClosure as M
import System.Exit (exitFailure)

-- ClosureFixture is the historical audit evidence/architecture wrapper, not a
-- production compiler. Its only compatibility edits are a module-name/export
-- change and the new explicit empty direct-evidence map. We do not run its old
-- regression/diagnostic expectations. Every positive forest below starts from
-- an actual ValueResult returned by the current value checker.

spec :: ResidualSpec
spec = ResidualSpec
  { residualObligationId = F.rootId
  , residualOrigin = obligationOrigin (F.rootFor F.definition)
  , residualScope = obligationScope (F.rootFor F.definition)
  , residualRequiredPoint = obligationRequiredPoint (F.rootFor F.definition)
  }

actualEvent :: D.DischargePolicy -> Proposition
  -> Either String (D.ResolvedObligation, [H.LedgerHandoff])
actualEvent policy goal = do
  before <- F.natState
  checked <- F.right $ checkValueWithResidual spec (VBool True)
    (TyRefined (Name "value") TyBool goal) before
  F.ensure (valueResultType checked == TyRefined (Name "value") TyBool goal)
    "value checker changed original expected type"
  F.ensure (resourceContext before == resourceContext (valueResultState checked))
    "literal refinement changed ownership"
  resolved <- F.right $ A.resolveOriginalCheckEvent emptyStaticContext policy spec checked
  F.ensure (D.resolvedObligation resolved == F.rootFor goal)
    "adapter lost original unnormalized event"
  case D.resolvedPrerequisites resolved of
    [child] -> F.ensure (D.resolvedObligation child == F.child)
      "adapter changed original prerequisite identity or proposition"
    _ -> Left "original event did not retain exactly its one prerequisite"
  entries <- F.right $ A.handoffOriginalCheckEvent F.config Map.empty
    emptyStaticContext policy spec checked
  reference <- F.right $ H.handoffResolvedObligation F.config resolved
  F.ensure (entries == reference) "handoff does not match the actual event forest"
  case entries of
    [parent,child] -> F.ensure
      (H.handoffSupportEdges entries == Set.singleton (F.rev parent,F.rev child))
      "event prerequisite did not reach immutable support"
    _ -> Left "handoff changed event node inventory"
  pure (resolved,entries)

runtimeFixture :: Proposition -> Either String F.Fixture
runtimeFixture goal = do
  policy <- F.right $ D.bindRuntime F.runtimeBinding D.emptyDischargePolicy
  (resolved,entries) <- actualEvent policy goal
  case D.resolvedPrerequisites resolved of
    [child] -> F.ensure (D.resolvedDisposition child == D.RuntimeBound F.runtimeBinding)
      "runtime child changed disposition"
    _ -> Left "missing runtime child"
  case entries of
    [parent,child] -> do
      pe <- F.parentEvidence parent
      ce <- F.runtimeEvidence child
      pure F.Fixture
        { F.entries = entries, F.parent = parent, F.prerequisite = child
        , F.evidenceEntries = [pe,ce]
        , F.scope = Set.fromList [F.rev parent,F.rev child]
        , F.selected = Set.fromList [F.parentId,F.runtimeId]
        , F.exported = []
        , F.allowed = Set.fromList [V.StaticallyDischarged,V.RuntimeBound,V.Exported]
        , F.permittedBoundaries = Set.singleton F.boundary
        }
    _ -> Left "unexpected runtime handoff"

rejectExport :: Proposition -> Either String ()
rejectExport goal = do
  fixture <- runtimeFixture goal
  F.accepts fixture
  let expected = case H.handoffDisposition (F.parent fixture) of
        D.StaticallyDischarged D.StaticByDefinition ->
          M.ManifestClosureHandoffRequiredSupportOutOfScope
            (F.rev (F.parent fixture)) (F.rev (F.prerequisite fixture))
        _ -> M.ManifestClosureManifestRejected
          (AV.DependencyOnExportedObligation F.parentId (F.rev (F.prerequisite fixture)))
  F.rejects (== expected) (F.exportChild fixture)

missingChildEvidence :: Either String ()
missingChildEvidence = do
  fixture <- runtimeFixture F.algebra
  F.rejects (== M.ManifestClosureManifestRejected
    (AV.AcceptanceRuleUnsatisfied (F.rev (F.parent fixture))))
    (fixture { F.selected = Set.singleton F.parentId })

wholeTreeExport :: Either String ()
wholeTreeExport = do
  let makeExport obligation = D.ExportBinding
        (obligationId obligation) (obligationProposition obligation)
        (obligationRequiredPoint obligation) F.boundary
  childPolicy <- F.right $ D.bindExport (makeExport F.child) D.emptyDischargePolicy
  policy <- F.right $ D.bindExport (makeExport (F.rootFor F.definition)) childPolicy
  (resolved,entries) <- actualEvent policy F.definition
  case (D.resolvedDisposition resolved, entries) of
    (D.Exported actual,[parent,child]) -> do
      F.ensure (actual == makeExport (F.rootFor F.definition)) "parent export changed"
      F.ensure (H.handoffDisposition child == D.Exported (makeExport F.child))
        "child export changed"
      let fixture = F.Fixture
            { F.entries = entries, F.parent = parent, F.prerequisite = child
            , F.evidenceEntries = [], F.scope = Set.empty, F.selected = Set.empty
            , F.exported =
                [ F.mkExport (T.ExportId "audit.closure.export.parent") parent
                , F.mkExport F.childExportId child ]
            , F.allowed = Set.singleton V.Exported
            , F.permittedBoundaries = Set.singleton F.boundary
            }
      F.accepts fixture
    other -> Left ("whole-tree export not retained: " <> show other)

main :: IO ()
main = do
  rows <- sequence
    [ test "C01" "actual algebraic event reaches full-scope final closure" (runtimeFixture F.algebra >>= F.accepts)
    , test "C02" "actual definitional event reaches full-scope final closure" (runtimeFixture F.definition >>= F.accepts)
    , test "C03" "actual explicit-prerequisite event reaches final closure" (runtimeFixture F.explicit >>= F.accepts)
    , test "C04" "algebraic event rejects exported required child" (rejectExport F.algebra)
    , test "C05" "definitional event rejects exported required child" (rejectExport F.definition)
    , test "C06" "explicit-prerequisite event rejects exported required child" (rejectExport F.explicit)
    , test "C07" "selected parent cannot omit prerequisite evidence" missingChildEvidence
    , test "C08" "genuine whole-tree export remains permitted" wholeTreeExport
    ]
  putStrLn "COMPLETE correctness_groups=8"
  unless (and rows) exitFailure

test :: String -> String -> Either String () -> IO Bool
test key label result = case result of
  Right () -> putStrLn ("PASS " <> key <> " " <> label) >> pure True
  Left err -> putStrLn ("FAIL " <> key <> " " <> label <> " -- " <> err) >> pure False
