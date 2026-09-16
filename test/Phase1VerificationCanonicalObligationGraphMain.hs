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
  )
import Phil.Core.Syntax
  ( Obligation (..)
  , ObligationId (..)
  , Proposition (..)
  , RefTerm (..)
  )
import Phil.Verification
  ( VerificationGraphError (..)
  , VerificationObligationGraph (..)
  , VerificationObligationInput (..)
  , buildVerificationObligationGraph
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  let checks =
        [ ("input/container order is nonsemantic", testOrderIndependence)
        , ("exact duplicate input canonicalizes", testExactDuplicate)
        , ("semantic subject changes graph identity", testSubjectChange)
        , ("dependency changes graph identity", testDependencyChange)
        , ("certification scope changes graph identity", testScopeChange)
        , ("unknown dependency rejects", testUnknownDependency)
        , ("unknown scope obligation rejects", testUnknownScope)
        , ("cyclic dependency graph rejects", testCycle)
        , ("conflicting stable obligation identity rejects", testConflict)
        ]
      failures = [label | (label, False) <- checks]
  mapM_ report checks
  unless (null failures) exitFailure
  where
    report (label, True) = putStrLn ("PASS: VER-002 " ++ label)
    report (label, False) = putStrLn ("FAIL: VER-002 " ++ label)

rootId :: ObligationId
rootId = ObligationId "ver002.root"

depAId :: ObligationId
depAId = ObligationId "ver002.dep-a"

depBId :: ObligationId
depBId = ObligationId "ver002.dep-b"

ghostId :: ObligationId
ghostId = ObligationId "ver002.ghost"

rootObligation :: Obligation
rootObligation = Obligation
  { obligationId = rootId
  , obligationProposition = Conjunction
      (LessEqual (RefNat 1) (RefNat 2))
      (NotEqual (RefNat 3) (RefNat 4))
  , obligationOrigin = "checked.callable:root"
  , obligationScope = "application:ver002"
  , obligationRequiredPoint = "before:root"
  }

depAObligation :: Obligation
depAObligation = Obligation
  { obligationId = depAId
  , obligationProposition = Equal (RefNat 8) (RefNat 8)
  , obligationOrigin = "checked.callable:dep-a"
  , obligationScope = "application:ver002"
  , obligationRequiredPoint = "before:dep-a"
  }

depBObligation :: Obligation
depBObligation = Obligation
  { obligationId = depBId
  , obligationProposition = LessThan (RefNat 0) (RefNat 9)
  , obligationOrigin = "checked.callable:dep-b"
  , obligationScope = "application:ver002"
  , obligationRequiredPoint = "before:dep-b"
  }

rootRule :: AcceptanceRule
rootRule = AcceptAll
  [ AcceptEntry KernelChecked (EvidenceRole "semantic")
  , AcceptAny
      [ AcceptEntry RuntimeEnforced (EvidenceRole "runtime")
      , AcceptEntry CertificateChecked (EvidenceRole "certificate")
      ]
  ]

rootRuleReordered :: AcceptanceRule
rootRuleReordered = AcceptAll
  [ AcceptAny
      [ AcceptEntry CertificateChecked (EvidenceRole "certificate")
      , AcceptEntry RuntimeEnforced (EvidenceRole "runtime")
      ]
  , AcceptEntry KernelChecked (EvidenceRole "semantic")
  ]

leafRule :: AcceptanceRule
leafRule = AcceptEntry KernelChecked (EvidenceRole "semantic")

rootInput :: VerificationObligationInput
rootInput = VerificationObligationInput
  { verificationInputObligation = rootObligation
  , verificationInputKind = "semantic"
  , verificationInputRepresentation = "phil-core/proposition-v1"
  , verificationInputSubjectIds = ["subject:z", "subject:a"]
  , verificationInputContextIds = ["context:2", "context:1"]
  , verificationInputAcceptanceRule = rootRule
  , verificationInputDependencies = Set.fromList [depAId, depBId]
  }

rootInputReordered :: VerificationObligationInput
rootInputReordered = rootInput
  { verificationInputSubjectIds = ["subject:a", "subject:z"]
  , verificationInputContextIds = ["context:1", "context:2"]
  , verificationInputAcceptanceRule = rootRuleReordered
  }

depAInput :: VerificationObligationInput
depAInput = leafInput depAObligation "subject:dep-a"

depBInput :: VerificationObligationInput
depBInput = leafInput depBObligation "subject:dep-b"

leafInput :: Obligation -> Text -> VerificationObligationInput
leafInput obligation subject = VerificationObligationInput
  { verificationInputObligation = obligation
  , verificationInputKind = "semantic-prerequisite"
  , verificationInputRepresentation = "phil-core/proposition-v1"
  , verificationInputSubjectIds = [subject]
  , verificationInputContextIds = ["context:shared"]
  , verificationInputAcceptanceRule = leafRule
  , verificationInputDependencies = Set.empty
  }

baseInputs :: [VerificationObligationInput]
baseInputs = [rootInput, depAInput, depBInput]

rootScope :: Set.Set ObligationId
rootScope = Set.singleton rootId

buildBase :: Either VerificationGraphError VerificationObligationGraph
buildBase = buildVerificationObligationGraph baseInputs rootScope

testOrderIndependence :: Bool
testOrderIndependence = case buildBase of
  Left _ -> False
  Right expected ->
    case buildVerificationObligationGraph
        [depBInput, rootInputReordered, depAInput]
        (Set.fromList [rootId]) of
      Right actual ->
        actual == expected
          && Map.size (verificationGraphNodes actual) == 3
          && Set.size (verificationGraphDependencies actual) == 2
      Left _ -> False

testExactDuplicate :: Bool
testExactDuplicate =
  buildVerificationObligationGraph
    (baseInputs ++ [rootInputReordered, depAInput])
    rootScope
    == buildBase

testSubjectChange :: Bool
testSubjectChange = case buildBase of
  Left _ -> False
  Right expected ->
    case buildVerificationObligationGraph
        [ rootInput { verificationInputSubjectIds = ["subject:different"] }
        , depAInput
        , depBInput
        ]
        rootScope of
      Right actual -> actual /= expected
      Left _ -> False

testDependencyChange :: Bool
testDependencyChange = case buildBase of
  Left _ -> False
  Right expected ->
    case buildVerificationObligationGraph
        [ rootInput { verificationInputDependencies = Set.singleton depAId }
        , depAInput
        , depBInput
        ]
        rootScope of
      Right actual -> actual /= expected
      Left _ -> False

testScopeChange :: Bool
testScopeChange = case buildBase of
  Left _ -> False
  Right expected ->
    case buildVerificationObligationGraph
        baseInputs
        (Set.fromList [rootId, depAId]) of
      Right actual -> actual /= expected
      Left _ -> False

testUnknownDependency :: Bool
testUnknownDependency =
  case buildVerificationObligationGraph
      [rootInput { verificationInputDependencies = Set.singleton ghostId }]
      rootScope of
    Left (UnknownObligationDependency owner missing) ->
      owner == rootId && missing == ghostId
    _ -> False

testUnknownScope :: Bool
testUnknownScope =
  case buildVerificationObligationGraph baseInputs (Set.singleton ghostId) of
    Left (UnknownCertificationScopeObligation missing) -> missing == ghostId
    _ -> False

testCycle :: Bool
testCycle =
  let rootCyclic = rootInput
        { verificationInputDependencies = Set.singleton depAId }
      depACyclic = depAInput
        { verificationInputDependencies = Set.singleton rootId }
  in case buildVerificationObligationGraph
      [rootCyclic, depACyclic]
      rootScope of
    Left (CyclicObligationDependencies region) ->
      Set.member rootId region && Set.member depAId region
    _ -> False

testConflict :: Bool
testConflict =
  let conflict = rootInput
        { verificationInputContextIds = ["context:conflicting"] }
  in case buildVerificationObligationGraph
      [rootInput, conflict, depAInput, depBInput]
      rootScope of
    Left (ConflictingObligationInputs conflictId) -> conflictId == rootId
    _ -> False
