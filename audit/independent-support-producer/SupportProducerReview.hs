{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (foldM, unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance.Handoff
import Phil.Assurance.EvidenceFactAuthority
import Phil.Assurance.Types
  ( AcceptanceRule (..), AssuranceKind (KernelChecked), EvidenceDependency (..)
  , EvidenceEntryId (..), EvidenceRole (..), ObligationRevision (..), emptyLedger )
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import qualified Phil.Core.Discharge as D
import Phil.Core.Refinement (EvidenceUse (..), ResidualSpec (..))
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
import Phil.Core.Value (ValueResult (..), checkValueWithResidual)
import qualified Phil.Verification as V
import System.Exit (exitFailure)

-- This is an external audit driver, not a production source-to-assurance
-- adapter. All resolved trees/certificates below come from the real resolver.
-- OBS records describe representation boundaries and earn no correctness pass.
main :: IO ()
main = do
  checks <- sequence
    [ runCheck "C01" "resolver-produced prerequisite reaches handoff" usedPrerequisite
    , runCheck "C02" "actual flat residual records retain exact identities" emittedFlatRecords
    , runCheck "C03" "definitionally closed main still emits its side obligation" emittedSideOnly
    , runCheck "C04" "unmapped certificate EvidenceFact fails closed" unmappedFact
    , runCheck "C05" "real transitive certificate retains both exact evidence IDs" mappedFacts
    , runCheck "C06" "omitted referenced child rejects at handoff" missingUsedChild
    , runCheck "C07" "explicit support graph preserves direction and provenance" graphDirection
    ]
  observations <- sequence
    [ runObservation "O01" definitionPrerequisiteObservation
    , runObservation "O02" directEvidenceObservation
    , runObservation "O03" flatResolverObservation
    ]
  unless (and checks && and observations) exitFailure
  putStrLn "COMPLETE correctness_groups=7 observation_records=3"

runCheck :: String -> String -> Either String () -> IO Bool
runCheck ident label result = case result of
  Right () -> putStrLn ("PASS " <> ident <> " " <> label) >> pure True
  Left detail -> putStrLn ("FAIL " <> ident <> " " <> detail) >> pure False

runObservation :: String -> Either String String -> IO Bool
runObservation ident result = case result of
  Right detail -> putStrLn ("OBS " <> ident <> " " <> detail) >> pure True
  Left detail -> putStrLn ("OBS_SETUP_ERROR " <> ident <> " " <> detail) >> pure False

ensure :: Bool -> String -> Either String ()
ensure True _ = Right ()
ensure False detail = Left detail

right :: Show e => Either e a -> Either String a
right = either (Left . show) Right

n :: Text -> Name
n = Name
v :: Text -> RefTerm
v = RefVar . n
natTy :: Ty
natTy = TyOpaqueSorted "AuditNat" SortNat

natState :: Either String CheckState
natState = foldM (\st name -> add name natTy st) emptyCheckState ["a", "b", "c"]
  where
    add name ty st = do
      context <- right $ insertBinding Unrestricted (n name) ty (resourceContext st)
      Right st { resourceContext = context }

addProof :: Text -> Proposition -> CheckState -> Either String CheckState
addProof name proposition st = do
  context <- right $ insertBinding Unrestricted (n name) (TyProof proposition) (resourceContext st)
  Right st { resourceContext = context }

side, reflexiveDifference, usedGoal, transitiveGoal :: Proposition
side = LessEqual (v "b") (v "a")
reflexiveDifference = Equal (RefSub (v "a") (v "b")) (RefSub (v "a") (v "b"))
usedGoal = Conjunction reflexiveDifference side
transitiveGoal = LessEqual (v "a") (v "c")

rootId, childId :: ObligationId
rootId = ObligationId "audit.support.root"
childId = ObligationId "audit.support.root.nat-sub.1"

rootFor :: Proposition -> Obligation
rootFor proposition = Obligation rootId proposition "SupportProducerReview" "audit.scope" "before-consumer"

runtimeFor :: Obligation -> D.RuntimeBinding
runtimeFor obligation = D.RuntimeBinding
  { D.runtimeObligationId = obligationId obligation
  , D.runtimeProposition = obligationProposition obligation
  , D.runtimeRequiredPoint = obligationRequiredPoint obligation
  , D.runtimeValidator = "declared-audit-check"
  , D.runtimeSuccessEvidence = TyProof (obligationProposition obligation)
  , D.runtimeFailureClass = "ValidationFailure"
  , D.runtimeResourceContract = "preserve unrelated resources; no success continuation on failure"
  , D.runtimeCostRef = "audit.runtime.cost"
  }

resolvedWithSide :: Proposition -> Either String D.ResolvedObligation
resolvedWithSide proposition = do
  st <- natState
  let child = (rootFor side) { obligationId = childId }
  policy <- right $ D.bindRuntime (runtimeFor child) D.emptyDischargePolicy
  right $ D.resolveObligation emptyStaticContext st policy (rootFor proposition)

config :: HandoffConfig
config = HandoffConfig
  { handoffRevisionKind = const "Audit"
  , handoffRepresentation = const "Core"
  , handoffSubjectIds = const ["audit.explicit-subject-domain"]
  , handoffContextIds = const ["audit.explicit-context"]
  , handoffAcceptanceRule = const (AcceptEntry KernelChecked (EvidenceRole "audit"))
  }

handoff :: D.ResolvedObligation -> Either String [LedgerHandoff]
handoff = right . handoffResolvedObligation config

pair :: [a] -> Either String (a, a)
pair [a,b] = Right (a,b)
pair _ = Left "expected exactly a root and one child"

usedPrerequisite :: Either String ()
usedPrerequisite = do
  resolved <- resolvedWithSide usedGoal
  case D.resolvedDisposition resolved of
    D.StaticallyDischarged D.StaticByCertificate {} -> Right ()
    other -> Left ("expected actual checked certificate: " <> show other)
  (parent,child) <- handoff resolved >>= pair
  ensure (handoffSupportDependencies parent == [DependsOnObligation (revisionId (handoffRevision child))])
    "certificate-used prerequisite did not reach exact immutable child revision"

spec :: ResidualSpec
spec = ResidualSpec rootId "SupportProducerReview" "audit.scope" "before-consumer"

emit :: Proposition -> Either String ValueResult
emit proposition = do
  st <- natState
  right $ checkValueWithResidual spec (VBool True) (TyRefined (n "value") TyBool proposition) st

emittedFlatRecords :: Either String ()
emittedFlatRecords = do
  result <- emit usedGoal
  let pending = residualObligations (valueResultState result)
      expected = Map.fromList
        [ (rootId, rootFor side)
        , (childId, (rootFor side) { obligationId = childId })
        ]
  ensure (pending == expected) ("unexpected actual emitted map: " <> show pending)
  ensure (Set.fromList (valueResultEvidence result) == Set.fromList
    [EvidenceResidual rootId side, EvidenceResidual childId side]) "residual use inventory differs"

emittedSideOnly :: Either String ()
emittedSideOnly = do
  result <- emit reflexiveDifference
  let pending = residualObligations (valueResultState result)
  ensure (pending == Map.singleton childId ((rootFor side) { obligationId = childId }))
    "main/side inventory changed"
  ensure (EvidenceByDefinition reflexiveDifference `elem` valueResultEvidence result)
    "original definitionally discharged proposition was not retained in ValueResult evidence"

transitiveResolved :: Either String D.ResolvedObligation
transitiveResolved = do
  st0 <- natState
  st1 <- addProof "ab" (LessEqual (v "a") (v "b")) st0
  st <- addProof "bc" (LessEqual (v "b") (v "c")) st1
  right $ D.resolveObligation emptyStaticContext st D.emptyDischargePolicy (rootFor transitiveGoal)

unmappedFact :: Either String ()
unmappedFact = do
  resolved <- transitiveResolved
  case handoffResolvedObligation config resolved of
    Left (UnknownEvidenceFactSupport ident name index)
      | ident == rootId && name `elem` [n "ab", n "bc"] && index == 1 -> Right ()
    other -> Left ("expected exact missing local EvidenceFact identity: " <> show other)

mappedFacts :: Either String ()
mappedFacts = do
  resolved <- transitiveResolved
  let abId = EvidenceEntryId "audit.evidence.ab"
      bcId = EvidenceEntryId "audit.evidence.bc"
      identities = Map.fromList [((n "ab",1),abId), ((n "bc",1),bcId)]
  entries <- right $ handoffResolvedObligationWithEvidence config identities resolved
  case entries of
    [entry] -> ensure (Set.fromList (handoffSupportDependencies entry) ==
      Set.fromList [DependsOnEvidence abId, DependsOnEvidence bcId]) "mapped evidence inventory differs"
    _ -> Left "transitive goal unexpectedly changed obligation domain"

missingUsedChild :: Either String ()
missingUsedChild = do
  resolved <- resolvedWithSide usedGoal
  case handoffResolvedObligation config resolved { D.resolvedPrerequisites = [] } of
    Left (UnknownPrerequisiteSupport parent child)
      | parent == rootId && child == childId -> Right ()
    other -> Left ("missing certificate-used child did not fail closed: " <> show other)

graphDirection :: Either String ()
graphDirection = do
  resolved <- resolvedWithSide usedGoal
  entries <- handoff resolved
  (parent,child) <- pair entries
  let parentRevision = revisionId (handoffRevision parent)
      childRevision = revisionId (handoffRevision child)
      edges = handoffSupportEdges entries
  graph <- right $ V.buildVerificationRevisionGraphWithSupport
    (map handoffRevision entries) edges (Set.fromList [parentRevision,childRevision])
  ensure (V.verificationGraphDependencies graph == Set.singleton (parentRevision,childRevision))
    "support graph changed direction"
  ensure (revisionGeneratedFrom (handoffRevision child) == [parentRevision]) "child provenance changed"

-- These are observations, not assertions that absent edges are correct or
-- evidence of an accepted final manifest. All returned nodes remain visible.
definitionPrerequisiteObservation :: Either String String
definitionPrerequisiteObservation = do
  resolved <- resolvedWithSide reflexiveDifference
  entries <- handoff resolved
  Right ("resolved=" <> show resolved <> ";handoff=" <> show entries <> ";support_edges=" <> show (handoffSupportEdges entries))

directEvidenceObservation :: Either String String
directEvidenceObservation = do
  st0 <- natState
  let goal = LessEqual (v "a") (RefAdd (v "a") (RefNat 1))
  -- Establish the arithmetic goal with the actual checker before installing
  -- the corresponding named proof as this explicitly supplied Core premise.
  established <- right $ D.resolveObligation emptyStaticContext st0 D.emptyDischargePolicy (rootFor goal)
  st <- addProof "alreadyChecked" goal st0
  resolved <- right $ D.resolveObligation emptyStaticContext st D.emptyDischargePolicy (rootFor goal)
  entries <- handoff resolved
  authorityEntries <- right $ handoffResolvedObligationWithEvidenceAuthority config Map.empty emptyLedger resolved
  Right ("established=" <> show (D.resolvedDisposition established) <> ";named=" <> show (D.resolvedDisposition resolved)
    <> ";ordinary=" <> show entries <> ";authority_facade=" <> show authorityEntries)

flatResolverObservation :: Either String String
flatResolverObservation = do
  result <- emit usedGoal
  let st = valueResultState result
      obligations = Map.elems (residualObligations st)
  policy <- foldM (\p o -> right (D.bindRuntime (runtimeFor o) p)) D.emptyDischargePolicy obligations
  forest <- mapM (right . D.resolveObligation emptyStaticContext st policy) obligations
  entries <- concat <$> mapM handoff forest
  Right ("value_evidence=" <> show (valueResultEvidence result)
    <> ";pending_ids=" <> show (Map.keys (residualObligations st))
    <> ";independently_resolved_roots=" <> show forest
    <> ";support_edges=" <> show (handoffSupportEdges entries))
