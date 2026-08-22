{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Assurance
import Phil.Core.Discharge
  ( ExportBinding (..)
  , ObligationDisposition (..)
  , ResolvedObligation (..)
  , RuntimeBinding (..)
  , StaticDischarge (..)
  )
import Phil.Core.Syntax
  ( Obligation (..)
  , ObligationId (..)
  , Proposition (..)
  , RefTerm (..)
  , Ty (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "handoff preserves runtime disposition and canonical proposition" runtimeDispositionPreserved
    , test "generated prerequisite revision records exact parent lineage" prerequisiteLineagePreserved
    , test "handoff preserves explicit export disposition" exportDispositionPreserved
    ]
  if and results then pure () else exitFailure

runtimeDispositionPreserved :: Bool
runtimeDispositionPreserved =
  case handoffResolvedObligation handoffConfig runtimeResolved of
    parent : _ ->
      handoffDisposition parent == RuntimeBound runtimeBinding
        && handoffCanonicalProposition parent == equalRef
        && revisionGeneratedFrom (handoffRevision parent) == []
    [] -> False

prerequisiteLineagePreserved :: Bool
prerequisiteLineagePreserved =
  case handoffResolvedObligation handoffConfig runtimeResolved of
    parent : child : _ ->
      revisionGeneratedFrom (handoffRevision child)
        == [revisionId (handoffRevision parent)]
        && handoffCanonicalProposition child == Truth
        && handoffDisposition child == StaticallyDischarged StaticByDefinition
    _ -> False

exportDispositionPreserved :: Bool
exportDispositionPreserved =
  case handoffResolvedObligation handoffConfig exportedResolved of
    [entry] ->
      handoffDisposition entry == Exported exportBinding
        && handoffCanonicalProposition entry == Falsehood
    _ -> False

handoffConfig :: HandoffConfig
handoffConfig = HandoffConfig
  { handoffRevisionKind = const "Test"
  , handoffRepresentation = const "Core"
  , handoffSubjectIds = const ["subject"]
  , handoffContextIds = const ["context"]
  , handoffAcceptanceRule = const (AcceptEntry KernelChecked (EvidenceRole "establishes"))
  }

runtimeResolved :: ResolvedObligation
runtimeResolved = ResolvedObligation
  { resolvedObligation = parentObligation
  , resolvedCanonicalProposition = equalRef
  , resolvedPrerequisites = [childResolved]
  , resolvedDisposition = RuntimeBound runtimeBinding
  }

childResolved :: ResolvedObligation
childResolved = ResolvedObligation
  { resolvedObligation = childObligation
  , resolvedCanonicalProposition = Truth
  , resolvedPrerequisites = []
  , resolvedDisposition = StaticallyDischarged StaticByDefinition
  }

exportedResolved :: ResolvedObligation
exportedResolved = ResolvedObligation
  { resolvedObligation = exportObligation
  , resolvedCanonicalProposition = Falsehood
  , resolvedPrerequisites = []
  , resolvedDisposition = Exported exportBinding
  }

parentObligation :: Obligation
parentObligation = Obligation
  { obligationId = ObligationId "test.handoff.parent"
  , obligationProposition = Truth
  , obligationOrigin = "test"
  , obligationScope = "test.scope"
  , obligationRequiredPoint = "parent.required"
  }

childObligation :: Obligation
childObligation = Obligation
  { obligationId = ObligationId "test.handoff.child"
  , obligationProposition = Truth
  , obligationOrigin = "test"
  , obligationScope = "test.scope"
  , obligationRequiredPoint = "child.required"
  }

exportObligation :: Obligation
exportObligation = Obligation
  { obligationId = ObligationId "test.handoff.export"
  , obligationProposition = Falsehood
  , obligationOrigin = "test"
  , obligationScope = "test.scope"
  , obligationRequiredPoint = "export.required"
  }

runtimeBinding :: RuntimeBinding
runtimeBinding = RuntimeBinding
  { runtimeObligationId = obligationId parentObligation
  , runtimeProposition = equalRef
  , runtimeRequiredPoint = obligationRequiredPoint parentObligation
  , runtimeValidator = "test-validator"
  , runtimeSuccessEvidence = TyProof equalRef
  , runtimeFailureClass = "ValidationFailure"
  , runtimeResourceContract = "no ownership change"
  , runtimeCostRef = "test.runtime.cost"
  }

exportBinding :: ExportBinding
exportBinding = ExportBinding
  { exportObligationId = obligationId exportObligation
  , exportProposition = Falsehood
  , exportRequiredPoint = obligationRequiredPoint exportObligation
  , exportBoundary = "parent.component"
  }

equalRef :: Proposition
equalRef = Equal (RefNat 1) (RefNat 1)

test :: String -> Bool -> IO Bool
test label passed = do
  putStrLn ((if passed then "PASS: " else "FAIL: ") <> label)
  pure passed
