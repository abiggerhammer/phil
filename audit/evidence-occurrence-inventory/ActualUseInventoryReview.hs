{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (foldM, unless)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Phil.Assurance as A
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (ResourceContext (..), insertBinding)
import Phil.Core.Refinement (EvidenceUse (..), ResidualSpec (..))
import Phil.Core.Syntax
import Phil.Core.Value (ValueResult (..), ValueError (..), checkValue, checkValueWithResidual)
import Phil.Core.Refinement (RefinementError (..))
import System.Exit (exitFailure)

-- The subject is the production inventory, not a Python facsimile. Every
-- ValueResult and EvidenceUse here comes from a real checker invocation.
-- Abstract typed bindings are explicit Core premises, not parsed source or
-- stable semantic SubjectIds. No returned state/evidence list is edited.

right :: Show e => Either e a -> Either String a
right = either (Left . show) Right
ensure :: Bool -> String -> Either String ()
ensure True _ = Right ()
ensure False message = Left message

x, y, u, collection, record, binder, owner :: Name
x = Name "x"
y = Name "y"
u = Name "u"
collection = Name "collection"
record = Name "record"
binder = Name "bound"
owner = Name "owner"

spec :: ResidualSpec
spec = ResidualSpec (ObligationId "audit.inventory") "independent-audit"
  "inventory-scope" "before-inventory-consumer"

withBinding :: Mode -> Name -> Ty -> CheckState -> Either String CheckState
withBinding mode name ty state = do
  context <- right $ insertBinding mode name ty (resourceContext state)
  pure state { resourceContext = context }

premises :: Either String CheckState
premises = foldM add emptyCheckState
  [ (x,TyOpaqueSorted "Nat" SortNat), (y,TyOpaqueSorted "Nat" SortNat)
  , (u,TyUInt 8), (collection,TyOpaqueSorted "NatSet" (SortFiniteSet SortNat))
  , (record,TyOpaque "Record") ]
  where add state (name,ty) = withBinding Unrestricted name ty state

propositionOf :: EvidenceUse -> Proposition
propositionOf evidence = case evidence of
  EvidenceByDefinition p -> p
  EvidenceByBinding _ p -> p
  EvidenceResidual _ p -> p

-- Independent work-list oracle. This advances a syntax cursor, rather than
-- calling or copying production's concatenating name-collection helpers.
data Cursor = P Proposition | T RefTerm
oracle :: Proposition -> [Name]
oracle p = reverse (walk [P p] [])
  where
    walk [] acc = acc
    walk (task:rest) acc = case task of
      T (RefVar name) -> walk rest (name:acc)
      T (RefField base _ _) -> walk (T base:rest) acc
      T (RefLen t) -> walk (T t:rest) acc
      T (RefToNat t) -> walk (T t:rest) acc
      T (RefAdd a b) -> walk (T a:T b:rest) acc
      T (RefSub a b) -> walk (T a:T b:rest) acc
      T (RefScale _ t) -> walk (T t:rest) acc
      T (RefNat _) -> walk rest acc
      T (RefUInt _ _) -> walk rest acc
      T (RefBool _) -> walk rest acc
      T (RefOpaque _ _) -> walk rest acc
      P Truth -> walk rest acc
      P Falsehood -> walk rest acc
      P (Equal a b) -> walk (T a:T b:rest) acc
      P (NotEqual a b) -> walk (T a:T b:rest) acc
      P (LessThan a b) -> walk (T a:T b:rest) acc
      P (LessEqual a b) -> walk (T a:T b:rest) acc
      P (Member a b) -> walk (T a:T b:rest) acc
      P (Disjoint a b) -> walk (T a:T b:rest) acc
      P (Conjunction a b) -> walk (P a:P b:rest) acc
      P (Disjunction a b) -> walk (P a:P b:rest) acc
      P (Negation a) -> walk (P a:rest) acc
      P (Atom _ args) -> walk (map T args ++ rest) acc

inventoryNames :: A.ActualEvidenceUse -> [Name]
inventoryNames use = case use of
  A.ActualCheckedClosedEvidenceUse {} -> []
  A.ActualSubjectBearingEvidenceUse _ _ subjects -> map A.evidenceSubjectName subjects

checkInventory :: ValueResult -> Either String ()
checkInventory result = do
  let original = valueResultEvidence result
      actual = A.actualEvidenceUseInventory result
  ensure (map A.actualEvidenceUse actual == original) "lost/reordered/changed an actual evidence record"
  ensure (map A.actualEvidenceUseIndex actual == [1..length original]) "incorrect one-based use indices"
  mapM_ inspect actual
  ensure (A.actualEvidenceUseInventory result == actual) "inventory not repeatable"
  where
    inspect use = do
      let expected = oracle (propositionOf (A.actualEvidenceUse use))
      ensure (inventoryNames use == expected) ("subject order or multiplicity changed: " <> show use)
      case use of
        A.ActualCheckedClosedEvidenceUse _ _ -> ensure (null expected) "subject-bearing use called closed"
        A.ActualSubjectBearingEvidenceUse i _ subjects -> do
          ensure (not (null expected)) "empty subject-bearing classification"
          ensure (map A.evidenceSubjectUseIndex subjects == replicate (length expected) i) "subject attached to another use"
          ensure (map A.evidenceSubjectOccurrenceIndex subjects == [1..length expected]) "occurrence positions collapsed or shifted"

checkGoal :: Proposition -> Either String ValueResult
checkGoal p = do
  before <- premises
  result <- right $ checkValueWithResidual spec (VBool True)
    (TyRefined binder TyBool p) before
  ensure (resourceContext before == resourceContext (valueResultState result)) "logical check changed resource permissions"
  checkInventory result
  pure result

checkPrimary :: Proposition -> [Name] -> Either String ()
checkPrimary p expected = do
  result <- checkGoal p
  let matches = [e | e <- A.actualEvidenceUseInventory result,
                    propositionOf (A.actualEvidenceUse e) == p]
  ensure (not (null matches)) "original unnormalized goal missing from actual returned uses"
  mapM_ (\e -> ensure (inventoryNames e == expected) "literal expected occurrence list disagrees") matches

type TermWitness = (RefTerm,[Name])
termWitnesses :: [TermWitness]
termWitnesses =
  [ (RefVar x,[x]), (RefNat 2,[]), (RefUInt 8 2,[]), (RefBool False,[])
  , (RefField (RefVar record) "x" SortNat,[record])
  , (RefLen (RefVar collection),[collection]), (RefToNat (RefVar u),[u])
  , (RefAdd (RefVar y) (RefVar x),[y,x])
  , (RefSub (RefVar x) (RefNat 0),[x])
  , (RefScale 0 (RefVar y),[y])
  , (RefOpaque SortNat "x y record",[]) ]

allTerms :: Either String ()
allTerms = mapM_ (\(t,names) -> checkPrimary (Equal t t) (names ++ names)) termWitnesses

propositionWitnesses :: [(Proposition,[Name])]
propositionWitnesses =
  [ (Truth,[]), (Falsehood,[])
  , (Equal (RefVar x) (RefVar y),[x,y])
  , (NotEqual (RefVar y) (RefVar x),[y,x])
  , (LessThan (RefVar x) (RefVar y),[x,y])
  , (LessEqual (RefVar y) (RefVar x),[y,x])
  , (Member (RefVar x) (RefVar collection),[x,collection])
  , (Disjoint (RefVar collection) (RefVar collection),[collection,collection])
  , (Conjunction (Equal (RefVar x) (RefVar y)) (Equal (RefVar y) (RefVar x)),[x,y,y,x])
  , (Disjunction (Equal (RefVar x) (RefVar x)) (Equal (RefVar y) (RefVar y)),[x,x,y,y])
  , (Negation (Equal (RefVar x) (RefVar y)),[x,y])
  , (Atom "u-is-a-label-not-a-subject" [RefVar y,RefVar x,RefVar y],[y,x,y]) ]

allPropositions :: Either String ()
allPropositions = mapM_ (\(p,names) -> checkPrimary (Disjunction p Truth) names) propositionWitnesses

-- Expected sequences are constructed with the independent term builder, not
-- inferred from the production inventory. 96 bounded terms, including nested
-- operands, repeated subjects, zero scaling and partial-operation obligations.
generatedTerms :: [TermWitness]
generatedTerms = first ++
  [ (RefAdd a (RefScale 2 b),as ++ bs) | (a,as) <- take 8 first, (b,bs) <- take 8 first ]
  where
    seeds = [(RefVar x,[x]),(RefVar y,[y]),(RefNat 0,[]),(RefToNat (RefVar u),[u])]
    first = seeds
      ++ [(RefScale k t,ns) | k <- [0,3], (t,ns) <- seeds]
      ++ [(RefSub t (RefNat 0),ns) | (t,ns) <- seeds]
      ++ [(RefAdd a b,as ++ bs) | (a,as) <- seeds, (b,bs) <- seeds]

generated :: Either String ()
generated = do
  ensure (length generatedTerms == 96) "wrong generated corpus count"
  mapM_ (\(t,names) -> checkPrimary (Equal t t) (names ++ names)) generatedTerms

closedLiteral :: Either String ()
closedLiteral = do
  result <- right $ checkValue (VUInt 8 0)
    (TyRefined binder (TyUInt 8) (LessEqual (RefToNat (RefVar binder)) (RefNat 1))) emptyCheckState
  checkInventory result
  case A.actualEvidenceUseInventory result of
    [A.ActualCheckedClosedEvidenceUse 1 (EvidenceByDefinition _)] -> Right ()
    _ -> Left "genuine closed literal not classified explicitly"

carried :: Either String ()
carried = do
  let ty = TyRefined binder (TyUInt 8) (LessEqual (RefToNat (RefVar binder)) (RefNat 1))
  literal <- right $ checkValue (VUInt 8 0) ty emptyCheckState
  before <- withBinding Unrestricted owner (valueResultType literal) emptyCheckState
  result <- right $ checkValue (VVar owner) ty before
  checkInventory result
  let required = LessEqual (RefToNat (RefVar owner)) (RefNat 1)
  ensure (EvidenceByBinding owner required `elem` valueResultEvidence result) "actual carried evidence missing"
  ensure (resourceContext before == resourceContext (valueResultState result)) "original owner changed"

residual :: Mode -> Either String ()
residual mode = do
  before <- withBinding mode owner (TyUInt 8) emptyCheckState
  let goal = LessThan (RefToNat (RefVar owner)) (RefNat 5)
  result <- right $ checkValueWithResidual spec (VVar owner)
    (TyRefined binder (TyUInt 8) (LessThan (RefToNat (RefVar binder)) (RefNat 5))) before
  checkInventory result
  ensure (valueResultEvidence result == [EvidenceResidual (residualObligationId spec) goal]) "wrong actual residual use"
  let ctx = resourceContext (valueResultState result)
  if mode == Unrestricted
    then ensure (ctx == resourceContext before) "unrestricted original changed"
    else ensure (all (Map.notMember owner) [unrestrictedBindings ctx,affineBindings ctx,linearBindings ctx]) "consumed owner restored"

multiUse :: Either String ()
multiUse = do
  let partial = RefSub (RefVar x) (RefVar y)
      goal = Equal partial partial
      condition = LessEqual (RefVar y) (RefVar x)
  result <- checkGoal goal
  ensure (length (valueResultEvidence result) >= 2) "fixture lacks multiple actual uses"
  ensure (EvidenceByDefinition goal `elem` valueResultEvidence result) "normalized-away parent use missing"
  let uses = A.actualEvidenceUseInventory result
  ensure (any (\e -> propositionOf (A.actualEvidenceUse e)==goal && inventoryNames e==[x,y,x,y]) uses) "parent occurrence sequence wrong"
  ensure (any (\e -> propositionOf (A.actualEvidenceUse e)==condition && inventoryNames e==[y,x]) uses) "prerequisite occurrence sequence wrong"

emptyUse :: Either String ()
emptyUse = do
  result <- right $ checkValue (VBool True) TyBool emptyCheckState
  ensure (null (valueResultEvidence result)) "plain literal did not have an empty use inventory"
  checkInventory result
  ensure (null (A.actualEvidenceUseInventory result)) "invented evidence use"

exactFalse :: Either String ()
exactFalse = case checkValue (VUInt 8 2)
  (TyRefined binder (TyUInt 8) (LessEqual (RefToNat (RefVar binder)) (RefNat 1))) emptyCheckState of
    Left (ValueRefinementError (StaticallyFalse p)) ->
      ensure (p == LessEqual (RefToNat (RefUInt 8 2)) (RefNat 1)) "wrong semantic rejection"
    other -> Left ("false literal did not reject at its semantic gate: " <> show other)

main :: IO ()
main = do
  results <- sequence
    [ test "C01" "genuine closed literal" closedLiteral
    , test "C02" "definition retains repeated x occurrences" (checkPrimary (Equal (RefVar x) (RefVar x)) [x,x])
    , test "C03" "genuine carried evidence" carried
    , test "C04" "unrestricted residual use" (residual Unrestricted)
    , test "C05" "affine occurrence without owner restoration" (residual Affine)
    , test "C06" "linear occurrence without owner restoration" (residual Linear)
    , test "C07" "all eleven RefTerm constructors via actual checker" allTerms
    , test "C08" "all twelve Proposition constructors via actual checker" allPropositions
    , test "C09" "96 independently annotated nested term cases" generated
    , test "C10" "parent and prerequisite retain separate ordered inventories" multiUse
    , test "C11" "empty actual use domain remains empty" emptyUse
    , test "C12" "false literal rejected before inventory" exactFalse
    ]
  putStrLn "COMPLETE correctness_groups=12 term_constructor_cases=11 proposition_constructor_cases=12 generated_term_cases=96"
  unless (and results) exitFailure

test :: String -> String -> Either String () -> IO Bool
test key label result = case result of
  Right () -> putStrLn ("PASS " <> key <> " " <> label) >> pure True
  Left err -> putStrLn ("FAIL " <> key <> " " <> label <> " -- " <> err) >> pure False
