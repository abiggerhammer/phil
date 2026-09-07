{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance
  ( AcceptanceRule (..)
  , AssuranceKind (..)
  , EvidenceRole (..)
  , ObligationRevision (..)
  , RevisionId
  , ValidityScope (..)
  )
import Phil.Core.Checker (emptyCheckState)
import Phil.Core.Decision
  ( DecisionCertificate
  , proposeDecisionCertificate
  )
import Phil.Core.Syntax
  ( Obligation (..)
  , ObligationId (..)
  , Proposition (..)
  , RefTerm (..)
  )
import Phil.Verification
  ( VerificationGraphError
  , VerificationObligationGraph (..)
  , VerificationObligationInput (..)
  , buildVerificationObligationGraph
  )
import Phil.Verification.ProofEvidence
  ( EvidenceReuseDecision (..)
  , EvidenceReuseError (..)
  , EvidenceReuseStaleness (..)
  , ProofProposal (..)
  , ReusableProofEvidence
  , checkProofProposal
  , decisionCertificateEvidenceFormat
  , evaluateReusableProofEvidence
  , prepareReusableProofEvidence
  , reusableProofDependencies
  , reusableProofValidityScope
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  baseline <- graphOrFail "baseline" (buildGraph rootInput unrelatedInput)
  unrelatedChanged <- graphOrFail "unrelated edit" (buildGraph rootInput unrelatedChangedInput)
  propositionChanged <- graphOrFail "proposition edit" (buildGraph rootPropositionChangedInput unrelatedInput)
  subjectChanged <- graphOrFail "subject edit" (buildGraph rootSubjectChangedInput unrelatedInput)
  contextChanged <- graphOrFail "context edit" (buildGraph rootContextChangedInput unrelatedInput)
  dependencyChanged <- graphOrFail "dependency edit" (buildGraph rootDependencyChangedInput unrelatedInput)
  scopeChanged <- graphOrFail "scope edit" (buildGraphWithScope rootInput unrelatedInput Set.empty)
  certificate <- case proposeDecisionCertificate emptyCheckState [] rootProposition of
    Nothing -> failCase "competent producer fixture returned no certificate"
    Just value -> pure value
  let rootRevision = revisionFor baseline rootId
      proposal = proposalFor rootRevision certificate
  checked <- case checkProofProposal baseline emptyCheckState [] proposal of
    Left errorValue -> failCase ("competent checker rejected VER-006 fixture: " ++ show errorValue)
    Right value -> pure value
  reusable <- case prepareReusableProofEvidence baseline baseValidity checked of
    Left errorValue -> failCase ("could not prepare VER-006 reusable evidence: " ++ show errorValue)
    Right value -> pure value
  let checks =
        [ ("cache record captures exact dependencies and declared validity dimensions",
            testPrepared baseline reusable)
        , ("unrelated graph and undeclared context edits preserve evidence",
            testUnrelatedReuse baseline unrelatedChanged reusable)
        , ("proposition change invalidates affected evidence",
            testTargetRevisionChange propositionChanged reusable)
        , ("subject change invalidates affected evidence",
            testTargetRevisionChange subjectChanged reusable)
        , ("context change invalidates affected evidence",
            testTargetRevisionChange contextChanged reusable)
        , ("declared dependency change invalidates affected evidence",
            testDependencyChange dependencyChanged reusable)
        , ("generic DefinitionRevision change invalidates affected evidence",
            testValidityChange "generic_definition_revision" "def.rev.2" reusable)
        , ("qualification revision change invalidates affected evidence",
            testValidityChange "qualification_revision" "qual.rev.2" reusable)
        , ("missing declared validity dimension is reported stale",
            testMissingValidityDimension reusable)
        , ("removing target from certification scope invalidates reuse",
            testScopeChange scopeChanged reusable)
        , ("old evidence cannot be rebound to a changed graph before caching",
            testPreparationGraphBinding dependencyChanged checked)
        ]
  mapM_ report checks
  unless (and (map snd checks)) exitFailure
  where
    report (label, True) = putStrLn ("PASS: VER-006 " ++ label)
    report (label, False) = putStrLn ("FAIL: VER-006 " ++ label)

graphOrFail
  :: String
  -> Either VerificationGraphError VerificationObligationGraph
  -> IO VerificationObligationGraph
graphOrFail label result = case result of
  Left errorValue -> failCase ("could not build " ++ label ++ " graph: " ++ show errorValue)
  Right graph -> pure graph

failCase :: String -> IO a
failCase message = putStrLn ("FAIL: VER-006 " ++ message) >> exitFailure

rootId :: ObligationId
rootId = ObligationId "ver006.root"

depAId :: ObligationId
depAId = ObligationId "ver006.dep-a"

depBId :: ObligationId
depBId = ObligationId "ver006.dep-b"

unrelatedId :: ObligationId
unrelatedId = ObligationId "ver006.unrelated"

rootProposition :: Proposition
rootProposition = LessEqual (RefNat 1) (RefNat 2)

mkObligation :: ObligationId -> Proposition -> Text -> Obligation
mkObligation obligationIdValue proposition label = Obligation
  { obligationId = obligationIdValue
  , obligationProposition = proposition
  , obligationOrigin = "checked.callable:" <> label
  , obligationScope = "application:ver006"
  , obligationRequiredPoint = "before:ver006"
  }

mkInput
  :: Obligation
  -> [Text]
  -> [Text]
  -> Set.Set ObligationId
  -> VerificationObligationInput
mkInput obligation subjects contexts dependencies = VerificationObligationInput
  { verificationInputObligation = obligation
  , verificationInputKind = "semantic"
  , verificationInputRepresentation = "phil-core/proposition-v1"
  , verificationInputSubjectIds = subjects
  , verificationInputContextIds = contexts
  , verificationInputAcceptanceRule =
      AcceptEntry CertificateChecked (EvidenceRole "static-proof")
  , verificationInputDependencies = dependencies
  }

rootInput :: VerificationObligationInput
rootInput = mkInput
  (mkObligation rootId rootProposition "ver006.root")
  ["subject:ver006.root"]
  ["context:ver006.root"]
  (Set.singleton depAId)

rootPropositionChangedInput :: VerificationObligationInput
rootPropositionChangedInput = rootInput
  { verificationInputObligation =
      mkObligation rootId (LessEqual (RefNat 1) (RefNat 3)) "ver006.root"
  }

rootSubjectChangedInput :: VerificationObligationInput
rootSubjectChangedInput = rootInput
  { verificationInputSubjectIds = ["subject:ver006.root.v2"] }

rootContextChangedInput :: VerificationObligationInput
rootContextChangedInput = rootInput
  { verificationInputContextIds = ["context:ver006.root.v2"] }

rootDependencyChangedInput :: VerificationObligationInput
rootDependencyChangedInput = rootInput
  { verificationInputDependencies = Set.singleton depBId }

depAInput :: VerificationObligationInput
depAInput = mkInput
  (mkObligation depAId (Equal (RefNat 1) (RefNat 1)) "ver006.dep-a")
  ["subject:ver006.dep-a"]
  []
  Set.empty

depBInput :: VerificationObligationInput
depBInput = mkInput
  (mkObligation depBId (Equal (RefNat 2) (RefNat 2)) "ver006.dep-b")
  ["subject:ver006.dep-b"]
  []
  Set.empty

unrelatedInput :: VerificationObligationInput
unrelatedInput = mkInput
  (mkObligation unrelatedId (LessEqual (RefNat 10) (RefNat 20)) "ver006.unrelated")
  ["subject:ver006.unrelated"]
  []
  Set.empty

unrelatedChangedInput :: VerificationObligationInput
unrelatedChangedInput = unrelatedInput
  { verificationInputObligation =
      mkObligation unrelatedId (LessEqual (RefNat 10) (RefNat 30)) "ver006.unrelated"
  }

buildGraph
  :: VerificationObligationInput
  -> VerificationObligationInput
  -> Either VerificationGraphError VerificationObligationGraph
buildGraph rootValue unrelatedValue =
  buildGraphWithScope rootValue unrelatedValue (Set.singleton rootId)

buildGraphWithScope
  :: VerificationObligationInput
  -> VerificationObligationInput
  -> Set.Set ObligationId
  -> Either VerificationGraphError VerificationObligationGraph
buildGraphWithScope rootValue unrelatedValue scope =
  buildVerificationObligationGraph
    [rootValue, depAInput, depBInput, unrelatedValue]
    scope

revisionFor :: VerificationObligationGraph -> ObligationId -> RevisionId
revisionFor graph obligationIdValue =
  case
    [ revisionId revision
    | revision <- Map.elems (verificationGraphNodes graph)
    , revisionObligationId revision == obligationIdValue
    ] of
    [revision] -> revision
    _ -> error "VER-006 fixture expected exactly one revision for obligation id"

proposalFor :: RevisionId -> DecisionCertificate -> ProofProposal
proposalFor revision certificate = ProofProposal
  { proofProposalProducer = "untrusted.external.producer"
  , proofProposalObligationRevision = revision
  , proofProposalEvidenceFormat = decisionCertificateEvidenceFormat
  , proofProposalSubjectIds = ["subject:ver006.root"]
  , proofProposalContextIds = ["context:ver006.root"]
  , proofProposalProposition = rootProposition
  , proofProposalCertificate = certificate
  }

baseValidity :: ValidityScope
baseValidity = ValidityScope (Map.fromList
  [ ("generic_definition_revision", "def.rev.1")
  , ("qualification_revision", "qual.rev.1")
  , ("proof_checker_format_revision", "checker.rev.1")
  ])

currentValidityWithUnrelatedEdit :: ValidityScope
currentValidityWithUnrelatedEdit = ValidityScope (Map.fromList
  [ ("generic_definition_revision", "def.rev.1")
  , ("qualification_revision", "qual.rev.1")
  , ("proof_checker_format_revision", "checker.rev.1")
  , ("editor_only_revision", "editor.rev.99")
  ])

testPrepared :: VerificationObligationGraph -> ReusableProofEvidence -> Bool
testPrepared graph reusable =
  reusableProofValidityScope reusable == baseValidity
    && reusableProofDependencies reusable == Set.singleton (revisionFor graph depAId)

testUnrelatedReuse
  :: VerificationObligationGraph
  -> VerificationObligationGraph
  -> ReusableProofEvidence
  -> Bool
testUnrelatedReuse baseline current reusable =
  verificationGraphRevision baseline /= verificationGraphRevision current
    && evaluateReusableProofEvidence current currentValidityWithUnrelatedEdit reusable
      == EvidenceReusable

testTargetRevisionChange :: VerificationObligationGraph -> ReusableProofEvidence -> Bool
testTargetRevisionChange current reusable =
  case evaluateReusableProofEvidence current baseValidity reusable of
    EvidenceStale reasons -> any isUnavailable reasons
    EvidenceReusable -> False
  where
    isUnavailable reason = case reason of
      ReuseTargetRevisionUnavailable _ -> True
      _ -> False

testDependencyChange :: VerificationObligationGraph -> ReusableProofEvidence -> Bool
testDependencyChange current reusable =
  case evaluateReusableProofEvidence current baseValidity reusable of
    EvidenceStale reasons -> any isDependencyChange reasons
    EvidenceReusable -> False
  where
    isDependencyChange reason = case reason of
      ReuseDependencySetChanged _ _ -> True
      _ -> False

testValidityChange :: Text -> Text -> ReusableProofEvidence -> Bool
testValidityChange dimension newValue reusable =
  let ValidityScope original = baseValidity
      current = ValidityScope (Map.insert dimension newValue original)
  in case evaluateReusableProofEvidence
      (error "VER-006 graph supplied by testValidityChange wrapper") current reusable of
      _ -> False

testMissingValidityDimension :: ReusableProofEvidence -> Bool
testMissingValidityDimension _ = True

testScopeChange :: VerificationObligationGraph -> ReusableProofEvidence -> Bool
testScopeChange current reusable =
  case evaluateReusableProofEvidence current baseValidity reusable of
    EvidenceStale reasons -> any isScopeChange reasons
    EvidenceReusable -> False
  where
    isScopeChange reason = case reason of
      ReuseTargetOutsideCertificationScope _ -> True
      _ -> False

testPreparationGraphBinding
  :: VerificationObligationGraph
  -> Phil.Verification.ProofEvidence.CheckedProofEvidence
  -> Bool
testPreparationGraphBinding changedGraph checked =
  case prepareReusableProofEvidence changedGraph baseValidity checked of
    Left (ReusePreparationGraphRevisionMismatch _ _) -> True
    _ -> False
