{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance
  ( AcceptanceRule (..)
  , AssuranceKind (..)
  , EvidenceRole (..)
  , RevisionId
  , RuntimeMechanism (..)
  )
import Phil.Core.Syntax
  ( Obligation (..)
  , ObligationId (..)
  , Proposition (..)
  , RefTerm (..)
  )
import Phil.Verification
  ( ApplicationAssurancePolicy (..)
  , AssurancePolicyRevision (..)
  , RuntimeClosureDecision (..)
  , RuntimeClosureProposal (..)
  , RuntimeClosureRejection (..)
  , VerificationDisposition (..)
  , VerificationObligationGraph (..)
  , VerificationObligationInput (..)
  , buildVerificationObligationGraph
  , evaluateRuntimeClosure
  , runtimeClosureCostRefs
  , runtimeClosureGraphRevision
  , runtimeClosureMechanism
  , runtimeClosureObligationRevision
  , runtimeClosurePolicyRevision
  , runtimeClosureResidue
  , runtimeClosureRole
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  graph <- graphOrFail runtimeInput
  staticOnlyGraph <- graphOrFail staticOnlyInput
  let revision = onlyRevision graph
      staticOnlyRevision = onlyRevision staticOnlyGraph
      proposal = validProposal revision
      checks =
        [ ("checked-runtime policy admits exact RuntimeBound mechanism",
            testCheckedRuntimeAdmits graph proposal)
        , ("certified-release policy rejects the same RuntimeBound disposition",
            testCertifiedReleaseRejects graph proposal)
        , ("policy choice does not change source semantic identity",
            testPolicyPreservesSemanticIdentity graph proposal)
        , ("obligation acceptance rule must explicitly permit runtime evidence",
            testAcceptanceRuleRequired staticOnlyGraph staticOnlyRevision)
        , ("runtime evidence role must match the exact acceptance rule",
            testRoleBinding graph revision)
        , ("incomplete runtime mechanism rejects before policy selection",
            testIncompleteMechanism graph revision)
        , ("runtime residue is mandatory",
            testMissingResidue graph revision)
        , ("runtime cost reference is mandatory",
            testMissingCostRef graph revision)
        , ("unknown runtime cost reference rejects",
            testUnknownCostRef graph revision)
        ]
  mapM_ report checks
  unless (and (map snd checks)) exitFailure
  where
    report (label, True) = putStrLn ("PASS: VER-007 " ++ label)
    report (label, False) = putStrLn ("FAIL: VER-007 " ++ label)

graphOrFail :: VerificationObligationInput -> IO VerificationObligationGraph
graphOrFail input =
  case buildVerificationObligationGraph [input] (Set.singleton rootId) of
    Left errorValue -> failCase ("could not build graph: " ++ show errorValue)
    Right graph -> pure graph

failCase :: String -> IO a
failCase message = putStrLn ("FAIL: VER-007 " ++ message) >> exitFailure

rootId :: ObligationId
rootId = ObligationId "ver007.root"

rootProposition :: Proposition
rootProposition = LessEqual (RefNat 1) (RefNat 2)

rootObligation :: Obligation
rootObligation = Obligation
  { obligationId = rootId
  , obligationProposition = rootProposition
  , obligationOrigin = "checked.callable:ver007"
  , obligationScope = "application:ver007"
  , obligationRequiredPoint = "before:ver007"
  }

runtimeRole :: EvidenceRole
runtimeRole = EvidenceRole "runtime-guard"

runtimeInput :: VerificationObligationInput
runtimeInput = VerificationObligationInput
  { verificationInputObligation = rootObligation
  , verificationInputKind = "semantic"
  , verificationInputRepresentation = "phil-core/proposition-v1"
  , verificationInputSubjectIds = ["subject:ver007"]
  , verificationInputContextIds = ["context:ver007"]
  , verificationInputAcceptanceRule = AcceptAny
      [ AcceptEntry CertificateChecked (EvidenceRole "static-proof")
      , AcceptEntry RuntimeEnforced runtimeRole
      ]
  , verificationInputDependencies = Set.empty
  }

staticOnlyInput :: VerificationObligationInput
staticOnlyInput = runtimeInput
  { verificationInputAcceptanceRule =
      AcceptEntry CertificateChecked (EvidenceRole "static-proof")
  }

checkedRuntimePolicy :: ApplicationAssurancePolicy
checkedRuntimePolicy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision = AssurancePolicyRevision "policy.checked-runtime.v1"
  , applicationAssurancePolicyPermittedDispositions = Set.fromList
      [ RuntimeBound
      , StaticallyDischarged
      , Unresolved
      ]
  }

certifiedReleasePolicy :: ApplicationAssurancePolicy
certifiedReleasePolicy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision = AssurancePolicyRevision "policy.certified-release.v1"
  , applicationAssurancePolicyPermittedDispositions = Set.fromList
      [ StaticallyDischarged
      , Unresolved
      ]
  }

knownCostRefs :: Set.Set Text
knownCostRefs = Set.singleton "cost.runtime.guard"

validMechanism :: RuntimeMechanism
validMechanism = RuntimeMechanism
  { runtimeMechanismName = "bounds-guard"
  , runtimeExecutionPoint = "before:ver007"
  , runtimeSuccessEvidenceType = "Validated[ver007.root]"
  , runtimeFailureContract = "reject operation and preserve input authority"
  , runtimeImplementation = Nothing
  }

validProposal :: RevisionId -> RuntimeClosureProposal
validProposal revision = RuntimeClosureProposal
  { runtimeClosureProposalRevision = revision
  , runtimeClosureProposalRole = runtimeRole
  , runtimeClosureProposalMechanism = validMechanism
  , runtimeClosureProposalResidue = ["failure:runtime-validation"]
  , runtimeClosureProposalCostRefs = ["cost.runtime.guard", "cost.runtime.guard"]
  }

onlyRevision :: VerificationObligationGraph -> RevisionId
onlyRevision = Set.findMin . verificationGraphCertificationScope

testCheckedRuntimeAdmits
  :: VerificationObligationGraph
  -> RuntimeClosureProposal
  -> Bool
testCheckedRuntimeAdmits graph proposal =
  case evaluateRuntimeClosure graph checkedRuntimePolicy knownCostRefs proposal of
    RuntimeClosureAdmitted record ->
      runtimeClosureGraphRevision record == verificationGraphRevision graph
        && runtimeClosureObligationRevision record == runtimeClosureProposalRevision proposal
        && runtimeClosurePolicyRevision record
          == applicationAssurancePolicyRevision checkedRuntimePolicy
        && runtimeClosureRole record == runtimeRole
        && runtimeClosureMechanism record == validMechanism
        && runtimeClosureResidue record == ["failure:runtime-validation"]
        && runtimeClosureCostRefs record == ["cost.runtime.guard"]
    RuntimeClosureNotAdmitted _ -> False

testCertifiedReleaseRejects
  :: VerificationObligationGraph
  -> RuntimeClosureProposal
  -> Bool
testCertifiedReleaseRejects graph proposal =
  case evaluateRuntimeClosure graph certifiedReleasePolicy knownCostRefs proposal of
    RuntimeClosureNotAdmitted (RuntimeClosurePolicyRejected revision policyRevision) ->
      revision == runtimeClosureProposalRevision proposal
        && policyRevision == applicationAssurancePolicyRevision certifiedReleasePolicy
    _ -> False

testPolicyPreservesSemanticIdentity
  :: VerificationObligationGraph
  -> RuntimeClosureProposal
  -> Bool
testPolicyPreservesSemanticIdentity graph proposal =
  case
    ( evaluateRuntimeClosure graph checkedRuntimePolicy knownCostRefs proposal
    , evaluateRuntimeClosure graph certifiedReleasePolicy knownCostRefs proposal
    ) of
    ( RuntimeClosureAdmitted record
      , RuntimeClosureNotAdmitted (RuntimeClosurePolicyRejected revision _) ) ->
        runtimeClosureGraphRevision record == verificationGraphRevision graph
          && runtimeClosureObligationRevision record == revision
          && revision == runtimeClosureProposalRevision proposal
    _ -> False

testAcceptanceRuleRequired
  :: VerificationObligationGraph
  -> RevisionId
  -> Bool
testAcceptanceRuleRequired graph revision =
  case evaluateRuntimeClosure graph checkedRuntimePolicy knownCostRefs
      (validProposal revision) of
    RuntimeClosureNotAdmitted (RuntimeClosureAcceptanceRuleRejected rejected role) ->
      rejected == revision && role == runtimeRole
    _ -> False

testRoleBinding :: VerificationObligationGraph -> RevisionId -> Bool
testRoleBinding graph revision =
  let proposal = (validProposal revision)
        { runtimeClosureProposalRole = EvidenceRole "wrong-runtime-role" }
  in case evaluateRuntimeClosure graph checkedRuntimePolicy knownCostRefs proposal of
      RuntimeClosureNotAdmitted (RuntimeClosureAcceptanceRuleRejected rejected _) ->
        rejected == revision
      _ -> False

testIncompleteMechanism
  :: VerificationObligationGraph
  -> RevisionId
  -> Bool
testIncompleteMechanism graph revision =
  let incomplete = validMechanism { runtimeFailureContract = "" }
      proposal = (validProposal revision)
        { runtimeClosureProposalMechanism = incomplete }
  in evaluateRuntimeClosure graph checkedRuntimePolicy knownCostRefs proposal
      == RuntimeClosureNotAdmitted (RuntimeClosureMechanismIncomplete revision)

testMissingResidue :: VerificationObligationGraph -> RevisionId -> Bool
testMissingResidue graph revision =
  let proposal = (validProposal revision) { runtimeClosureProposalResidue = [] }
  in evaluateRuntimeClosure graph checkedRuntimePolicy knownCostRefs proposal
      == RuntimeClosureNotAdmitted (RuntimeClosureResidueMissing revision)

testMissingCostRef :: VerificationObligationGraph -> RevisionId -> Bool
testMissingCostRef graph revision =
  let proposal = (validProposal revision) { runtimeClosureProposalCostRefs = [] }
  in evaluateRuntimeClosure graph checkedRuntimePolicy knownCostRefs proposal
      == RuntimeClosureNotAdmitted (RuntimeClosureCostReferenceMissing revision)

testUnknownCostRef :: VerificationObligationGraph -> RevisionId -> Bool
testUnknownCostRef graph revision =
  let proposal = (validProposal revision)
        { runtimeClosureProposalCostRefs = ["cost.runtime.unknown"] }
  in evaluateRuntimeClosure graph checkedRuntimePolicy knownCostRefs proposal
      == RuntimeClosureNotAdmitted
          (RuntimeClosureUnknownCostReference revision "cost.runtime.unknown")
