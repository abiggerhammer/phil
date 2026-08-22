{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import Data.Text (Text)
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import Phil.Core.Decision
  ( AssumptionRef (..)
  , CertificateError (..)
  , DecisionCertificate (..)
  , LinearBasis (..)
  , LinearCertificate (..)
  , SolverAssumption (..)
  , checkDecisionCertificate
  , proposeDecisionCertificate
  )
import Phil.Core.Syntax
  ( Mode (Unrestricted)
  , Name (Name)
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
    [ test "producer proves Nat monotonicity with a checked certificate" testNatMonotonicity
    , test "producer uses UInt upper bounds after canonical toNat" testUIntUpperBound
    , test "producer combines inequality evidence transitively" testTransitiveEvidence
    , test "producer composes conjunction certificates" testConjunction
    , test "producer selects a proved disjunct" testDisjunction
    , test "producer proves inequality-derived disequality" testNotEqual
    , test "finite collection facts are usable only when supplied as evidence" testCollectionEvidence
    , test "finite collection facts are never invented" testCollectionUnknown
    , test "checker rejects negative use of inequality assumptions" testNegativeInequalityWeight
    , test "checker rejects forged UInt bounds on Nat terms" testForgedUIntBound
    , test "checker rejects unknown assumption identities" testUnknownAssumption
    , test "checker requires subtraction prerequisites before normalization" testSubtractionPrerequisiteBeforeNormalization
    , test "checker accepts subtraction after the prerequisite is established" testSubtractionPrerequisiteEstablished
    , test "checker rejects definitionally false subtraction prerequisites" testFalseSubtractionPrerequisite
    , test "equality assumptions may be used symmetrically by certificate" testEqualitySymmetry
    , test "producer remains unknown for unsupported symbolic Nat order" testSolverUnknown
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

assumption :: Text -> Int -> Proposition -> SolverAssumption
assumption source index proposition =
  SolverAssumption (EvidenceFact (name source) index) proposition

proveWithProducer
  :: CheckState
  -> [SolverAssumption]
  -> Proposition
  -> Either String DecisionCertificate
proveWithProducer state assumptions goal =
  case proposeDecisionCertificate state assumptions goal of
    Nothing -> Left ("producer returned unknown for " ++ show goal)
    Just certificate -> do
      mapLeft show $ checkDecisionCertificate state assumptions goal certificate
      Right certificate

testNatMonotonicity :: Either String ()
testNatMonotonicity = do
  state <- withNats ["n"]
  _ <- proveWithProducer state []
    (LessEqual (var "n") (RefAdd (var "n") (RefNat 1)))
  Right ()

testUIntUpperBound :: Either String ()
testUIntUpperBound = do
  state <- withBinding (name "x") (TyUInt 8) emptyCheckState
  certificate <- proveWithProducer state []
    (LessThan (RefToNat (var "x")) (RefNat 256))
  case certificate of
    CertificateLinear linear
      | any isUpper (linearTerms linear) -> Right ()
    other -> Left ("certificate did not use the UInt upper bound: " ++ show other)
  where
    isUpper (BasisUIntUpper 8 _, _) = True
    isUpper _ = False

testTransitiveEvidence :: Either String ()
testTransitiveEvidence = do
  state <- withNats ["a", "b", "c"]
  let first = LessEqual (var "a") (var "b")
      second = LessEqual (var "b") (var "c")
      assumptions =
        [ assumption "ab" 1 first
        , assumption "bc" 1 second
        ]
  certificate <- proveWithProducer state assumptions
    (LessEqual (var "a") (var "c"))
  case certificate of
    CertificateLinear linear ->
      assert (length (linearTerms linear) >= 2) "transitive proof did not combine evidence"
    other -> Left ("unexpected transitive certificate: " ++ show other)

testConjunction :: Either String ()
testConjunction = do
  state <- withNats ["n"]
  certificate <- proveWithProducer state []
    (Conjunction
      (LessEqual (RefNat 0) (var "n"))
      (LessEqual (var "n") (RefAdd (var "n") (RefNat 1))))
  case certificate of
    CertificateConjunction _ _ -> Right ()
    other -> Left ("conjunction did not produce a pair certificate: " ++ show other)

testDisjunction :: Either String ()
testDisjunction = do
  state <- withNats ["a", "b"]
  let fact = LessEqual (var "a") (var "b")
      assumptions = [assumption "ordered" 1 fact]
  certificate <- proveWithProducer state assumptions
    (Disjunction fact (LessThan (var "b") (var "a")))
  case certificate of
    CertificateDisjunctionLeft _ -> Right ()
    other -> Left ("solver did not select the established disjunct: " ++ show other)

testNotEqual :: Either String ()
testNotEqual = do
  state <- withNats ["a", "b"]
  let strict = LessThan (var "a") (var "b")
      assumptions = [assumption "strict" 1 strict]
  certificate <- proveWithProducer state assumptions
    (NotEqual (var "a") (var "b"))
  case certificate of
    CertificateNotEqualLeft _ -> Right ()
    other -> Left ("strict order did not establish disequality: " ++ show other)

testCollectionEvidence :: Either String ()
testCollectionEvidence = do
  let collectionTy = TyOpaqueSorted "Versions" (SortFiniteSet (SortUInt 16))
      fact = Member (RefUInt 16 7) (var "versions")
      assumptions = [assumption "offered" 1 fact]
  state <- withBinding (name "versions") collectionTy emptyCheckState
  certificate <- proveWithProducer state assumptions fact
  case certificate of
    CertificateAssumption _ _ -> Right ()
    other -> Left ("collection fact was not tied to supplied evidence: " ++ show other)

testCollectionUnknown :: Either String ()
testCollectionUnknown = do
  let collectionTy = TyOpaqueSorted "Versions" (SortFiniteSet (SortUInt 16))
      fact = Member (RefUInt 16 7) (var "versions")
  state <- withBinding (name "versions") collectionTy emptyCheckState
  case proposeDecisionCertificate state [] fact of
    Nothing -> Right ()
    Just certificate -> Left ("solver invented a collection fact: " ++ show certificate)

testNegativeInequalityWeight :: Either String ()
testNegativeInequalityWeight = do
  state <- withNats ["a", "b"]
  let fact = LessEqual (var "a") (var "b")
      ref = EvidenceFact (name "ab") 1
      assumptions = [SolverAssumption ref fact]
      forged = CertificateLinear $ LinearCertificate
        [(BasisAssumption ref fact, -1)] 0
  case checkDecisionCertificate state assumptions
    (LessEqual (var "b") (var "a")) forged of
    Left (NegativeInequalityWeight _ weight)
      | weight == -1 -> Right ()
    other -> Left ("negative inequality weight was accepted: " ++ show other)

testForgedUIntBound :: Either String ()
testForgedUIntBound = do
  state <- withNats ["n"]
  let forged = CertificateLinear $ LinearCertificate
        [(BasisUIntUpper 8 (var "n"), 1)] 0
  case checkDecisionCertificate state []
    (LessEqual (var "n") (RefNat 255)) forged of
    Left (InvalidUIntBound 8 term)
      | term == var "n" -> Right ()
    other -> Left ("forged UInt bound was accepted: " ++ show other)

testUnknownAssumption :: Either String ()
testUnknownAssumption = do
  state <- withNats ["a", "b"]
  let fact = LessEqual (var "a") (var "b")
      ref = EvidenceFact (name "missing") 1
      forged = CertificateAssumption ref fact
  case checkDecisionCertificate state [] fact forged of
    Left (UnknownCertificateAssumption actualRef actualFact)
      | actualRef == ref && actualFact == fact -> Right ()
    other -> Left ("unknown assumption identity was accepted: " ++ show other)

testSubtractionPrerequisiteBeforeNormalization :: Either String ()
testSubtractionPrerequisiteBeforeNormalization = do
  state <- withNats ["a", "b"]
  let difference = RefSub (var "a") (var "b")
      goal = Equal difference difference
      prerequisite = LessEqual (var "b") (var "a")
  case checkDecisionCertificate state [] goal CertificateTruth of
    Left (MissingPartialOperationPrerequisite actual)
      | actual == prerequisite -> Right ()
    other -> Left ("normalization hid the subtraction prerequisite: " ++ show other)

testSubtractionPrerequisiteEstablished :: Either String ()
testSubtractionPrerequisiteEstablished = do
  state <- withNats ["a", "b"]
  let difference = RefSub (var "a") (var "b")
      goal = Equal difference difference
      prerequisite = LessEqual (var "b") (var "a")
      ref = PrerequisiteFact (ObligationId "calc.safe.nat-sub.1")
      assumptions = [SolverAssumption ref prerequisite]
  mapLeft show $ checkDecisionCertificate state assumptions goal CertificateTruth

testFalseSubtractionPrerequisite :: Either String ()
testFalseSubtractionPrerequisite = do
  let difference = RefSub (RefNat 3) (RefNat 5)
      goal = Equal difference difference
  case checkDecisionCertificate emptyCheckState [] goal CertificateTruth of
    Left (FalsePartialOperationPrerequisite prerequisite)
      | prerequisite == LessEqual (RefNat 5) (RefNat 3) -> Right ()
    other -> Left ("known-false subtraction prerequisite was accepted: " ++ show other)

testEqualitySymmetry :: Either String ()
testEqualitySymmetry = do
  state <- withNats ["a", "b"]
  let fact = Equal (var "a") (var "b")
      assumptions = [assumption "eq" 1 fact]
  certificate <- proveWithProducer state assumptions
    (Equal (var "b") (var "a"))
  case certificate of
    CertificateLinear linear
      | any ((== -1) . snd) (linearTerms linear) -> Right ()
    other -> Left ("equality symmetry was not certificate-derived: " ++ show other)

testSolverUnknown :: Either String ()
testSolverUnknown = do
  state <- withNats ["a", "b"]
  case proposeDecisionCertificate state [] (LessEqual (var "a") (var "b")) of
    Nothing -> Right ()
    Just certificate -> Left ("solver guessed an unsupported symbolic order: " ++ show certificate)

assert :: Bool -> String -> Either String ()
assert condition message
  | condition = Right ()
  | otherwise = Left message

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
