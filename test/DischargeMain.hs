{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import Data.Text (Text)
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import Phil.Core.Discharge
  ( DischargeError (..)
  , ExportBinding (..)
  , ObligationDisposition (..)
  , ResolvedObligation (..)
  , RuntimeBinding (..)
  , StaticDischarge (..)
  , bindExplicitEvidence
  , bindExport
  , bindRuntime
  , emptyDischargePolicy
  , resolveObligation
  )
import Phil.Core.Static
  ( declareOpaqueClaim
  , declareTransparentClaim
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Mode (Unrestricted)
  , Name (Name)
  , Obligation (..)
  , ObligationId (ObligationId)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "literal obligations close definitionally" testDefinitionDisposition
    , test "matching in-scope evidence closes before the solver" testEvidenceDisposition
    , test "transparent arithmetic closes by checked certificate" testCertificateDisposition
    , test "solver may combine distinct in-scope evidence facts" testCertificateFromEvidence
    , test "mismatched explicitly named evidence is rejected" testExplicitEvidenceMismatch
    , test "opaque obligations may use an exact declared runtime binding" testOpaqueRuntime
    , test "runtime binding proposition must match the obligation" testRuntimePropositionMismatch
    , test "runtime success evidence must establish the exact proposition" testRuntimeEvidenceMismatch
    , test "runtime binding takes canonical precedence over export" testRuntimeBeforeExport
    , test "unresolved transparent obligations may be explicitly exported" testExport
    , test "missing disposition rejects the obligation" testUnresolved
    , test "Nat subtraction gets a stable child obligation" testSubtractionRuntimePrerequisite
    , test "exported prerequisites cannot justify local static discharge" testExportedPrerequisiteBlocksLocal
    , test "exporting both prerequisite and parent closes only by export" testExportedPrerequisiteAndParent
    , test "policy maps reject duplicate bindings" testDuplicatePolicy
    ]
  unless (and results) exitFailure

test :: String -> Either String () -> IO Bool
test label result =
  case result of
    Right () -> putStrLn ("PASS: " ++ label) >> pure True
    Left message -> putStrLn ("FAIL: " ++ label ++ " -- " ++ message) >> pure False

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
  , obligationOrigin = "DischargeMain"
  , obligationScope = "test-component"
  , obligationRequiredPoint = "before-test-operation"
  }

withBinding :: Name -> Ty -> CheckState -> Either String CheckState
withBinding binding ty state = do
  context <- mapLeft show $
    insertBinding Unrestricted binding ty (resourceContext state)
  Right state { resourceContext = context }

withNats :: [Text] -> Either String CheckState
withNats names = foldl add (Right emptyCheckState) names
  where
    add accumulated text = do
      state <- accumulated
      withBinding (name text) natTy state

runtimeFor :: Obligation -> Proposition -> Ty -> RuntimeBinding
runtimeFor target proposition successEvidence = RuntimeBinding
  { runtimeObligationId = obligationId target
  , runtimeProposition = proposition
  , runtimeRequiredPoint = obligationRequiredPoint target
  , runtimeValidator = "test-validator"
  , runtimeSuccessEvidence = successEvidence
  , runtimeFailureClass = "ValidationFailure"
  , runtimeResourceContract = "preserve unrelated resources; no success continuation on failure"
  , runtimeCostRef = "test.runtime.cost"
  }

exportFor :: Obligation -> Proposition -> ExportBinding
exportFor target proposition = ExportBinding
  { exportObligationId = obligationId target
  , exportProposition = proposition
  , exportRequiredPoint = obligationRequiredPoint target
  , exportBoundary = "test.assurance.boundary"
  }

testDefinitionDisposition :: Either String ()
testDefinitionDisposition = do
  let target = obligation "literal.true" (LessEqual (RefNat 1) (RefNat 2))
  resolved <- mapLeft show $
    resolveObligation emptyStaticContext emptyCheckState emptyDischargePolicy target
  case resolvedDisposition resolved of
    StaticallyDischarged StaticByDefinition -> Right ()
    other -> Left ("literal proposition used the wrong disposition: " ++ show other)

testEvidenceDisposition :: Either String ()
testEvidenceDisposition = do
  let proposition = LessEqual (var "a") (var "b")
      target = obligation "evidence.direct" proposition
  state0 <- withNats ["a", "b"]
  state <- withBinding (name "proof") (TyProof proposition) state0
  resolved <- mapLeft show $
    resolveObligation emptyStaticContext state emptyDischargePolicy target
  case resolvedDisposition resolved of
    StaticallyDischarged (StaticByEvidence evidenceName)
      | evidenceName == name "proof" -> Right ()
    other -> Left ("matching evidence did not win before solver: " ++ show other)

testCertificateDisposition :: Either String ()
testCertificateDisposition = do
  let proposition = LessEqual (var "n") (RefAdd (var "n") (RefNat 1))
      target = obligation "solver.monotone" proposition
  state <- withNats ["n"]
  resolved <- mapLeft show $
    resolveObligation emptyStaticContext state emptyDischargePolicy target
  case resolvedDisposition resolved of
    StaticallyDischarged StaticByCertificate{} -> Right ()
    other -> Left ("transparent arithmetic did not use a checked certificate: " ++ show other)

testCertificateFromEvidence :: Either String ()
testCertificateFromEvidence = do
  let ab = LessEqual (var "a") (var "b")
      bc = LessEqual (var "b") (var "c")
      target = obligation "solver.transitive" (LessEqual (var "a") (var "c"))
  state0 <- withNats ["a", "b", "c"]
  state1 <- withBinding (name "ab") (TyProof ab) state0
  state <- withBinding (name "bc") (TyProof bc) state1
  resolved <- mapLeft show $
    resolveObligation emptyStaticContext state emptyDischargePolicy target
  case resolvedDisposition resolved of
    StaticallyDischarged StaticByCertificate{} -> Right ()
    other -> Left ("solver did not derive transitive order from evidence: " ++ show other)

testExplicitEvidenceMismatch :: Either String ()
testExplicitEvidenceMismatch = do
  let versionsTy = TyOpaqueSorted "Versions" (SortFiniteSet (SortUInt 16))
      actual = Member (RefUInt 16 8) (var "versions")
      required = Member (RefUInt 16 7) (var "versions")
      target = obligation "explicit.mismatch" required
  state0 <- withBinding (name "versions") versionsTy emptyCheckState
  state <- withBinding (name "wrongProof") (TyProof actual) state0
  policy <- mapLeft show $
    bindExplicitEvidence (obligationId target) (name "wrongProof") emptyDischargePolicy
  case resolveObligation emptyStaticContext state policy target of
    Left (ExplicitEvidenceDoesNotMatch actualId evidenceName proposition)
      | actualId == obligationId target
          && evidenceName == name "wrongProof"
          && proposition == required -> Right ()
    other -> Left ("mismatched explicit evidence was not rejected: " ++ show other)

testOpaqueRuntime :: Either String ()
testOpaqueRuntime = do
  staticContext <- mapLeft show $
    declareOpaqueClaim "DigestMatches" [] emptyStaticContext
  let proposition = Atom "DigestMatches" []
      target = obligation "digest.matches" proposition
      binding = runtimeFor target proposition (TyProof proposition)
  policy <- mapLeft show $ bindRuntime binding emptyDischargePolicy
  resolved <- mapLeft show $
    resolveObligation staticContext emptyCheckState policy target
  case resolvedDisposition resolved of
    RuntimeBound actual
      | actual == binding -> Right ()
    other -> Left ("opaque runtime binding was not used: " ++ show other)

testRuntimePropositionMismatch :: Either String ()
testRuntimePropositionMismatch = do
  let required = Member (RefUInt 16 7) (RefOpaque (SortFiniteSet (SortUInt 16)) "versions")
      wrong = Member (RefUInt 16 8) (RefOpaque (SortFiniteSet (SortUInt 16)) "versions")
      target = obligation "runtime.wrong-prop" required
      binding = runtimeFor target wrong (TyProof wrong)
  policy <- mapLeft show $ bindRuntime binding emptyDischargePolicy
  case resolveObligation emptyStaticContext emptyCheckState policy target of
    Left (RuntimeBindingPropositionMismatch actualId expected actual)
      | actualId == obligationId target && expected == required && actual == wrong -> Right ()
    other -> Left ("wrong runtime proposition was accepted: " ++ show other)

testRuntimeEvidenceMismatch :: Either String ()
testRuntimeEvidenceMismatch = do
  let collection = RefOpaque (SortFiniteSet (SortUInt 16)) "versions"
      required = Member (RefUInt 16 7) collection
      wrong = Member (RefUInt 16 8) collection
      target = obligation "runtime.wrong-evidence" required
      binding = runtimeFor target required (TyProof wrong)
  policy <- mapLeft show $ bindRuntime binding emptyDischargePolicy
  case resolveObligation emptyStaticContext emptyCheckState policy target of
    Left (RuntimeSuccessEvidenceMismatch actualId expected actual)
      | actualId == obligationId target && expected == required && actual == wrong -> Right ()
    other -> Left ("wrong runtime success evidence was accepted: " ++ show other)

testRuntimeBeforeExport :: Either String ()
testRuntimeBeforeExport = do
  let collection = RefOpaque (SortFiniteSet (SortUInt 16)) "versions"
      proposition = Member (RefUInt 16 7) collection
      target = obligation "runtime.before-export" proposition
      runtime = runtimeFor target proposition (TyProof proposition)
      exported = exportFor target proposition
  policy0 <- mapLeft show $ bindRuntime runtime emptyDischargePolicy
  policy <- mapLeft show $ bindExport exported policy0
  resolved <- mapLeft show $
    resolveObligation emptyStaticContext emptyCheckState policy target
  case resolvedDisposition resolved of
    RuntimeBound actual
      | actual == runtime -> Right ()
    other -> Left ("export incorrectly won before runtime: " ++ show other)

testExport :: Either String ()
testExport = do
  let collection = RefOpaque (SortFiniteSet (SortUInt 16)) "versions"
      proposition = Member (RefUInt 16 7) collection
      target = obligation "export.allowed" proposition
      binding = exportFor target proposition
  policy <- mapLeft show $ bindExport binding emptyDischargePolicy
  resolved <- mapLeft show $
    resolveObligation emptyStaticContext emptyCheckState policy target
  case resolvedDisposition resolved of
    Exported actual
      | actual == binding -> Right ()
    other -> Left ("explicit export did not close the obligation: " ++ show other)

testUnresolved :: Either String ()
testUnresolved = do
  let collection = RefOpaque (SortFiniteSet (SortUInt 16)) "versions"
      proposition = Member (RefUInt 16 7) collection
      target = obligation "unresolved" proposition
  case resolveObligation emptyStaticContext emptyCheckState emptyDischargePolicy target of
    Left (UnresolvedObligation actualId actualProposition)
      | actualId == obligationId target && actualProposition == proposition -> Right ()
    other -> Left ("unresolved obligation did not reject: " ++ show other)

testSubtractionRuntimePrerequisite :: Either String ()
testSubtractionRuntimePrerequisite = do
  state <- withNats ["a", "b"]
  let difference = RefSub (var "a") (var "b")
      target = obligation "calc.safe" (Equal difference difference)
      sideId = ObligationId "calc.safe.nat-sub.1"
      sideProposition = LessEqual (var "b") (var "a")
      sideObligation = target
        { obligationId = sideId
        , obligationProposition = sideProposition
        }
      runtime = runtimeFor sideObligation sideProposition (TyProof sideProposition)
  policy <- mapLeft show $ bindRuntime runtime emptyDischargePolicy
  resolved <- mapLeft show $
    resolveObligation emptyStaticContext state policy target
  case (resolvedPrerequisites resolved, resolvedDisposition resolved) of
    ([side], StaticallyDischarged StaticByDefinition)
      | obligationId (resolvedObligation side) == sideId
          && resolvedDisposition side == RuntimeBound runtime -> Right ()
    other -> Left ("subtraction prerequisite was not separately runtime-bound: " ++ show other)

testExportedPrerequisiteBlocksLocal :: Either String ()
testExportedPrerequisiteBlocksLocal = do
  state <- withNats ["a", "b"]
  let difference = RefSub (var "a") (var "b")
      target = obligation "calc.exported-side" (Equal difference difference)
      sideId = ObligationId "calc.exported-side.nat-sub.1"
      sideProposition = LessEqual (var "b") (var "a")
      sideObligation = target
        { obligationId = sideId
        , obligationProposition = sideProposition
        }
  policy <- mapLeft show $
    bindExport (exportFor sideObligation sideProposition) emptyDischargePolicy
  case resolveObligation emptyStaticContext state policy target of
    Left (ExportedPrerequisiteBlocksLocalDischarge actualId)
      | actualId == obligationId target -> Right ()
    other -> Left ("exported prerequisite leaked into local static discharge: " ++ show other)

testExportedPrerequisiteAndParent :: Either String ()
testExportedPrerequisiteAndParent = do
  state <- withNats ["a", "b"]
  let difference = RefSub (var "a") (var "b")
      parentProposition = Equal difference difference
      target = obligation "calc.export-all" parentProposition
      sideId = ObligationId "calc.export-all.nat-sub.1"
      sideProposition = LessEqual (var "b") (var "a")
      sideObligation = target
        { obligationId = sideId
        , obligationProposition = sideProposition
        }
  policy0 <- mapLeft show $
    bindExport (exportFor sideObligation sideProposition) emptyDischargePolicy
  policy <- mapLeft show $
    bindExport (exportFor target parentProposition) policy0
  resolved <- mapLeft show $
    resolveObligation emptyStaticContext state policy target
  case (resolvedPrerequisites resolved, resolvedDisposition resolved) of
    ([side], Exported parentBinding)
      | case resolvedDisposition side of Exported _ -> True; _ -> False
      , parentBinding == exportFor target parentProposition -> Right ()
    other -> Left ("exported prerequisite/parent did not remain explicit exports: " ++ show other)

testDuplicatePolicy :: Either String ()
testDuplicatePolicy = do
  let targetId = ObligationId "duplicate.policy"
  first <- mapLeft show $
    bindExplicitEvidence targetId (name "first") emptyDischargePolicy
  case bindExplicitEvidence targetId (name "second") first of
    Left (DuplicatePolicyBinding kind actualId)
      | kind == "explicit-evidence" && actualId == targetId -> Right ()
    other -> Left ("duplicate policy binding was accepted: " ++ show other)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
