{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.Checker (emptyCheckState)
import Phil.Core.Decision
  ( AssumptionRef (..)
  , DecisionCertificate (..)
  , SolverAssumption (..)
  , checkDecisionCertificate
  , proposeDecisionCertificate
  )
import Phil.Core.FloatArithmetic
  ( FloatFormat (..)
  , floatCoreType
  )
import Phil.Core.NumericPropositionCompetence
  ( NumericPropositionCompetence (..)
  , classifyNumericPropositionCompetence
  , proposeNumericDecisionCertificate
  )
import Phil.Core.Syntax
  ( Name (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "EXEC-019 exact Nat arithmetic is inside built-in proof competence"
        natArithmeticCompetent
    , test "EXEC-019 exact UInt relation is inside built-in proof competence"
        uintRelationCompetent
    , test "EXEC-019 runtime F32 support does not grant proposition competence"
        floatRuntimeDoesNotGrantProofCompetence
    , test "EXEC-019 unsupported opaque numeric domain remains unresolved"
        opaqueNumericRemainsUnresolved
    , test "EXEC-019 mixed competent/opaque numeric proposition remains unresolved"
        mixedNumericRemainsUnresolved
    , test "EXEC-019 explicit exact evidence may establish opaque float proposition"
        explicitFloatEvidenceAccepted
    , test "EXEC-019 unsupported numeric reasoning never manufactures an assumption"
        unsupportedDoesNotInventAssumption
    , test "EXEC-019 nonnumeric propositions are not relabeled numeric competence"
        nonnumericRemainsSeparate
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

natArithmeticCompetent :: Either String ()
natArithmeticCompetent = do
  let proposition = Equal
        (RefAdd (RefNat 2) (RefNat 3))
        (RefNat 5)
  (competence, certificate) <- mapLeft show $
    proposeNumericDecisionCertificate emptyCheckState [] proposition
  assert (competence == NumericPropositionCompetent [SortNat])
    ("Nat competence changed: " <> show competence)
  checked <- case certificate of
    Just value -> Right value
    Nothing -> Left "competent exact Nat proposition produced no certificate"
  mapLeft show $ checkDecisionCertificate emptyCheckState [] proposition checked

uintRelationCompetent :: Either String ()
uintRelationCompetent = do
  let proposition = LessEqual (RefUInt 8 7) (RefUInt 8 7)
  (competence, certificate) <- mapLeft show $
    proposeNumericDecisionCertificate emptyCheckState [] proposition
  assert (competence == NumericPropositionCompetent [SortUInt 8])
    ("UInt competence changed: " <> show competence)
  checked <- case certificate of
    Just value -> Right value
    Nothing -> Left "competent exact UInt proposition produced no certificate"
  mapLeft show $ checkDecisionCertificate emptyCheckState [] proposition checked

floatRuntimeDoesNotGrantProofCompetence :: Either String ()
floatRuntimeDoesNotGrantProofCompetence = do
  let sort = floatSort Float32
      proposition = Equal
        (RefOpaque sort "exec019.float.left")
        (RefOpaque sort "exec019.float.right")
  competence <- mapLeft show $
    classifyNumericPropositionCompetence emptyCheckState proposition
  assert (competence == NumericPropositionRequiresExplicitEvidence [sort])
    ("F32 unexpectedly acquired built-in decision competence: " <> show competence)
  (_, certificate) <- mapLeft show $
    proposeNumericDecisionCertificate emptyCheckState [] proposition
  assert (certificate == Nothing)
    "unsupported F32 proposition received an implicit decision certificate"

opaqueNumericRemainsUnresolved :: Either String ()
opaqueNumericRemainsUnresolved = do
  let sort = SortOpaque "phil.numeric.opaque.v1:test"
      proposition = Equal
        (RefOpaque sort "exec019.opaque.left")
        (RefOpaque sort "exec019.opaque.right")
  competence <- mapLeft show $
    classifyNumericPropositionCompetence emptyCheckState proposition
  assert (competence == NumericPropositionRequiresExplicitEvidence [sort])
    ("opaque numeric domain unexpectedly became competent: " <> show competence)
  (_, certificate) <- mapLeft show $
    proposeNumericDecisionCertificate emptyCheckState [] proposition
  assert (certificate == Nothing)
    "opaque numeric proposition received an implicit certificate"

mixedNumericRemainsUnresolved :: Either String ()
mixedNumericRemainsUnresolved = do
  let floatSort' = floatSort Float64
      exactInteger = Equal (RefNat 4) (RefNat 4)
      opaqueFloat = Equal
        (RefOpaque floatSort' "exec019.mixed.left")
        (RefOpaque floatSort' "exec019.mixed.right")
      proposition = Conjunction exactInteger opaqueFloat
  competence <- mapLeft show $
    classifyNumericPropositionCompetence emptyCheckState proposition
  assert
    (competence == NumericPropositionRequiresExplicitEvidence [SortNat, floatSort'])
    ("mixed proposition exceeded least-competent numeric boundary: " <> show competence)
  (_, certificate) <- mapLeft show $
    proposeNumericDecisionCertificate emptyCheckState [] proposition
  assert (certificate == Nothing)
    "mixed exact/opaque proposition was partially promoted to truth"

explicitFloatEvidenceAccepted :: Either String ()
explicitFloatEvidenceAccepted = do
  let sort = floatSort Float32
      proposition = Equal
        (RefOpaque sort "exec019.evidence.left")
        (RefOpaque sort "exec019.evidence.right")
      reference = EvidenceFact (Name "exec019.float.evidence") 0
      assumption = SolverAssumption reference proposition
      certificate = CertificateAssumption reference proposition
  mapLeft show $
    checkDecisionCertificate emptyCheckState [assumption] proposition certificate

unsupportedDoesNotInventAssumption :: Either String ()
unsupportedDoesNotInventAssumption = do
  let sort = floatSort Float64
      proposition = Equal
        (RefOpaque sort "exec019.no-assumption.left")
        (RefOpaque sort "exec019.no-assumption.right")
  assert (proposeDecisionCertificate emptyCheckState [] proposition == Nothing)
    "existing built-in producer manufactured evidence for an unsupported float proposition"
  (_, wrapped) <- mapLeft show $
    proposeNumericDecisionCertificate emptyCheckState [] proposition
  assert (wrapped == Nothing)
    "numeric competence wrapper manufactured evidence for an unsupported proposition"

nonnumericRemainsSeparate :: Either String ()
nonnumericRemainsSeparate = do
  let proposition = Equal (RefBool True) (RefBool True)
  competence <- mapLeft show $
    classifyNumericPropositionCompetence emptyCheckState proposition
  assert (competence == NumericPropositionNotNumeric)
    ("Bool equality was incorrectly claimed as numeric competence: " <> show competence)

floatSort :: FloatFormat -> RefSort
floatSort format = case floatCoreType format of
  TyOpaqueSorted _ sort -> sort
  other -> error ("EXEC-018 float semantic type lost explicit sort: " <> show other)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
