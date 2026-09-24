{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Phil.Assurance as Assurance
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (ResourceContext (..), insertBinding)
import Phil.Core.Refinement (EvidenceUse (..), ResidualSpec (..))
import Phil.Core.Syntax
import Phil.Core.Value (ValueResult (..), checkValue, checkValueWithResidual)
import System.Exit (exitFailure)

payload, other, binder :: Name
payload = Name "payload"
other = Name "other"
binder = Name "subject"

spec :: ResidualSpec
spec = ResidualSpec
  { residualObligationId = ObligationId "audit.evidence-use.inventory"
  , residualOrigin = "audit-evidence-use-inventory"
  , residualScope = "audit.same-check"
  , residualRequiredPoint = "before final consumer"
  }

right :: Show e => Either e a -> Either String a
right = either (Left . show) Right

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False message = Left message

withBinding :: Mode -> Name -> Ty -> CheckState -> Either String CheckState
withBinding mode name ty state = do
  context <- right $ insertBinding mode name ty (resourceContext state)
  Right state { resourceContext = context }

subjectNames :: Assurance.ActualEvidenceUse -> [Name]
subjectNames use = case use of
  Assurance.ActualCheckedClosedEvidenceUse {} -> []
  Assurance.ActualSubjectBearingEvidenceUse { Assurance.actualEvidenceSubjects = subjects } ->
    map Assurance.evidenceSubjectName subjects

closedLiteral :: Either String ()
closedLiteral = do
  let expected = TyRefined binder (TyUInt 8)
        (LessEqual (RefToNat (RefVar binder)) (RefNat 1))
  result <- right $ checkValue (VUInt 8 0) expected emptyCheckState
  let evidence = valueResultEvidence result
      inventory = Assurance.actualEvidenceUseInventory result
  assert (length evidence == 1) "closed literal did not produce one actual evidence use"
  case inventory of
    [Assurance.ActualCheckedClosedEvidenceUse 1 use] ->
      assert (use == head evidence) "closed inventory changed the actual evidence use"
    otherInventory -> Left ("closed literal was not explicitly classified closed: " <> show otherInventory)

subjectBearingDefinition :: Either String ()
subjectBearingDefinition = do
  before <- withBinding Unrestricted payload (TyUInt 8) emptyCheckState
  let expected = TyRefined binder (TyUInt 8)
        (Equal (RefVar binder) (RefVar binder))
      required = Equal (RefVar payload) (RefVar payload)
  result <- right $ checkValue (VVar payload) expected before
  assert (EvidenceByDefinition required `elem` valueResultEvidence result)
    "actual definition evidence was not retained"
  case Assurance.actualEvidenceUseInventory result of
    [use@Assurance.ActualSubjectBearingEvidenceUse {}] -> do
      assert (subjectNames use == [payload,payload])
        "definitionally true subject occurrences were normalized away or deduplicated"
      assert (Assurance.actualEvidenceUse use == EvidenceByDefinition required)
        "inventory changed definition evidence"
    inventory -> Left ("subject-bearing definition misclassified: " <> show inventory)

carriedBinding :: Either String ()
carriedBinding = do
  let boundTy = TyRefined binder (TyUInt 8)
        (LessEqual (RefToNat (RefVar binder)) (RefNat 1))
      bound = LessEqual (RefToNat (RefVar payload)) (RefNat 1)
  literal <- right $ checkValue (VUInt 8 0) boundTy emptyCheckState
  before <- withBinding Unrestricted payload (valueResultType literal) emptyCheckState
  result <- right $ checkValue (VVar payload) boundTy before
  assert (EvidenceByBinding payload bound `elem` valueResultEvidence result)
    "actual carried binding evidence missing"
  let matching =
        [ use
        | use@Assurance.ActualSubjectBearingEvidenceUse {} <- Assurance.actualEvidenceUseInventory result
        , Assurance.actualEvidenceUse use == EvidenceByBinding payload bound
        ]
  case matching of
    [use] -> assert (subjectNames use == [payload]) "carried evidence lost its subject occurrence"
    _ -> Left ("carried binding evidence was not uniquely inventoried: " <> show matching)

residualSubject :: Mode -> Either String ValueResult
residualSubject mode = do
  before <- withBinding mode payload (TyUInt 8) emptyCheckState
  let expected = TyRefined binder (TyUInt 8)
        (LessThan (RefToNat (RefVar binder)) (RefNat 5))
  right $ checkValueWithResidual spec (VVar payload) expected before

residualInventory :: Either String ()
residualInventory = do
  result <- residualSubject Unrestricted
  case Assurance.actualEvidenceUseInventory result of
    [use@Assurance.ActualSubjectBearingEvidenceUse {}] -> do
      assert (subjectNames use == [payload]) "residual evidence lost its subject"
      case Assurance.actualEvidenceUse use of
        EvidenceResidual obligationId' _ ->
          assert (obligationId' == residualObligationId spec) "residual identity changed"
        otherUse -> Left ("expected actual residual evidence, got " <> show otherUse)
    inventory -> Left ("residual evidence inventory changed: " <> show inventory)

multiSubjectResidual :: Either String ()
multiSubjectResidual = do
  withPayload <- withBinding Unrestricted payload (TyUInt 8) emptyCheckState
  before <- withBinding Unrestricted other (TyUInt 8) withPayload
  let required = LessEqual
        (RefAdd (RefToNat (RefVar payload)) (RefToNat (RefVar other)))
        (RefNat 10)
      expected = TyRefined binder (TyUInt 8)
        (LessEqual
          (RefAdd (RefToNat (RefVar binder)) (RefToNat (RefVar other)))
          (RefNat 10))
  result <- right $ checkValueWithResidual spec (VVar payload) expected before
  assert (EvidenceResidual (residualObligationId spec) required `elem` valueResultEvidence result)
    "actual multi-subject residual missing"
  let matching =
        [ use
        | use@Assurance.ActualSubjectBearingEvidenceUse {} <- Assurance.actualEvidenceUseInventory result
        , Assurance.actualEvidenceUse use == EvidenceResidual (residualObligationId spec) required
        ]
  case matching of
    [use] -> assert (subjectNames use == [payload,other])
      "multi-subject evidence did not retain every subject occurrence in order"
    _ -> Left ("multi-subject residual was not uniquely inventoried: " <> show matching)

completeOrderedInventory :: Either String ()
completeOrderedInventory = do
  before <- withBinding Unrestricted payload (TyUInt 8) emptyCheckState
  let repeated = RefSub (RefToNat (RefVar binder)) (RefNat 1)
      expected = TyRefined binder (TyUInt 8) (Equal repeated repeated)
  result <- right $ checkValueWithResidual spec (VVar payload) expected before
  let evidence = valueResultEvidence result
      inventory = Assurance.actualEvidenceUseInventory result
      indexed = zip [1 ..] evidence
  assert (length evidence >= 2) "fixture did not exercise more than one actual evidence use"
  assert (length inventory == length evidence) "inventory omitted an actual evidence use"
  assert
    ( zip (map Assurance.actualEvidenceUseIndex inventory) (map Assurance.actualEvidenceUse inventory)
        == indexed
    )
    "inventory changed evidence order, identity, or one-based use indices"

linearOwnershipSeparate :: Either String ()
linearOwnershipSeparate = do
  result <- residualSubject Linear
  assert
    (Map.notMember payload (linearBindings (resourceContext (valueResultState result))))
    "linear owner was restored while building the evidence inventory"
  case Assurance.actualEvidenceUseInventory result of
    [use@Assurance.ActualSubjectBearingEvidenceUse {}] ->
      assert (subjectNames use == [payload])
        "consumption erased the logical subject occurrence from actual evidence"
    inventory -> Left ("linear residual inventory changed: " <> show inventory)

main :: IO ()
main = do
  rows <- sequence
    [ test "C01" "closed actual evidence is explicitly classified closed" closedLiteral
    , test "C02" "definitionally true evidence retains repeated subject occurrences" subjectBearingDefinition
    , test "C03" "carried binding evidence remains subject-bearing" carriedBinding
    , test "C04" "actual residual evidence is inventoried" residualInventory
    , test "C05" "multi-subject evidence preserves all occurrences" multiSubjectResidual
    , test "C06" "inventory covers every actual evidence use in order" completeOrderedInventory
    , test "C07" "logical inventory remains separate from linear ownership" linearOwnershipSeparate
    ]
  putStrLn "COMPLETE correctness_groups=7"
  unless (and rows) exitFailure

test :: String -> String -> Either String () -> IO Bool
test key label outcome = case outcome of
  Right () -> putStrLn ("PASS " <> key <> " " <> label) >> pure True
  Left err -> putStrLn ("FAIL " <> key <> " " <> label <> " -- " <> err) >> pure False
