{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.CheckedBindingMode
  ( CheckedTypeMode (..)
  )
import Phil.Core.Focusing
  ( FocusStep (..)
  , FocusingError (..)
  )
import Phil.Core.NominalDataMode
  ( NominalModeError (..)
  , NominalRestrictionJustification (..)
  )
import Phil.Core.Static
  ( declareTransparentClaim
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.RecordFields
  ( GrammarV1CheckedRecordMode (..)
  , GrammarV1CheckedRecordModeError (..)
  , grammarV1CheckedClosedRecordMode
  , grammarV1CheckedRecordFields
  , grammarV1RecordModeFromCheckedFields
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 closed record fields preserve checked type meaning and exact order"
        closedRecordFields
    , test "SURF-008 record field Core failures remain distinct from source non-competence"
        recordFieldCoreFailure
    , test "SURF-008 unsupported record field types poison the whole projection"
        unsupportedRecordField
    , test "SURF-008 record fields cannot inherit free caller-local term dependencies"
        freeRecordFieldDependency
    , test "SURF-008 closed record mode omission derives the exact Core aggregate mode"
        recordModeDerivation
    , test "SURF-008 explicit record mode strengthening requires admitted nominal justification"
        recordModeStrengthening
    , test "SURF-008 explicit record mode weakening rejects through Core nominal semantics"
        recordModeWeakening
    , test "SURF-008 supplied record field-mode identity must match source fields exactly"
        recordModeFieldCorrespondence
    , test "SURF-008 closed intrinsic records derive mode from exact checked field semantics"
        checkedRecordModeComposition
    , test "SURF-008 composed record mode preserves focusing and nominal failure layers"
        checkedRecordModeFailureBoundaries
    , test "SURF-008 generic and requirement-bearing records remain outside closed field competence"
        openRecordFormsReject
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

closedRecordFields :: Either String ()
closedRecordFields = do
  context <- mapLeft show $
    declareTransparentClaim
      "Positive"
      [(Name "x", SortUInt 8)]
      (LessThan
        (RefNat 0)
        (RefToNat (RefVar (Name "x"))))
      emptyStaticContext
  record <- onlyRecord $ Text.unlines
    [ "record Packet mode linear {"
    , "  count : U32,"
    , "  proof : Proof[true],"
    , "  value : {v : U8 | Positive(v)},"
    , "  count : Bool,"
    , "}"
    ]
  case grammarV1CheckedRecordFields context record of
    Just
      (Right
        [ ("count", TyUInt 32, [])
        , ("proof", TyProof Truth, [])
        , ("value", TyRefined binder base predicate, refinementSteps)
        , ("count", TyBool, [])
        ]) -> do
          assert (binder == Name "v" && base == TyUInt 8)
            "checked record refinement changed binder or base type"
          assert
            (predicate == LessThan
              (RefNat 0)
              (RefToNat (RefVar (Name "v"))))
            "checked record refinement changed canonical predicate"
          assert (ExpandedTransparentClaim "Positive" `elem` refinementSteps)
            "checked record refinement lost transparent-claim focusing trace"
    other -> Left
      ("record field typing changed field names/order/types, interpreted record mode, or rejected duplicate spelling: "
        <> show other)

recordFieldCoreFailure :: Either String ()
recordFieldCoreFailure = do
  record <- onlyRecord
    "record BadClaim { first : U8, proof : Proof[Missing(1)] }"
  assert
    (grammarV1CheckedRecordFields emptyStaticContext record ==
      Just (Left (UnknownClaim "Missing")))
    "record field Core UnknownClaim collapsed into source non-competence or partial success"

unsupportedRecordField :: Either String ()
unsupportedRecordField = do
  record <- onlyRecord
    "record TupleField { first : U8, pair : (U32, Bool) }"
  assert
    (grammarV1CheckedRecordFields emptyStaticContext record == Nothing)
    "unsupported tuple record field was partially accepted"

freeRecordFieldDependency :: Either String ()
freeRecordFieldDependency = do
  record <- onlyRecord
    "record FreeDependency { payload : Bytes[n] }"
  assert
    (grammarV1CheckedRecordFields emptyStaticContext record == Nothing)
    "top-level record field inherited an undeclared caller-local term dependency"

recordModeDerivation :: Either String ()
recordModeDerivation = do
  unrestrictedRecord <- onlyRecord
    "record Plain { left : U8, right : Bool }"
  resourceRecord <- onlyRecord
    "record Owned { plain : U8, resource : Resource }"
  assert
    ( grammarV1RecordModeFromCheckedFields
        [("left", Unrestricted), ("right", Unrestricted)]
        Nothing
        unrestrictedRecord
        == Just (Right Unrestricted)
    )
    "omitted unrestricted record mode did not derive the exact Core minimum"
  assert
    ( grammarV1RecordModeFromCheckedFields
        [("plain", Unrestricted), ("resource", Linear)]
        Nothing
        resourceRecord
        == Just (Right Linear)
    )
    "omitted record mode did not preserve the strongest supplied owned-field mode"

recordModeStrengthening :: Either String ()
recordModeStrengthening = do
  strengthened <- onlyRecord
    "record FireOnce mode linear { id : U64 }"
  assert
    ( grammarV1RecordModeFromCheckedFields
        [("id", Unrestricted)]
        Nothing
        strengthened
        == Just (Left (StrongerModeMissingJustification Unrestricted Linear))
    )
    "strict record-mode strengthening bypassed Core justification requirements"
  assert
    ( grammarV1RecordModeFromCheckedFields
        [("id", Unrestricted)]
        (Just (AdmittedLifecycleObligation "fire-once lifecycle"))
        strengthened
        == Just (Right Linear)
    )
    "admitted lifecycle justification did not permit exact linear strengthening"
  assert
    ( grammarV1RecordModeFromCheckedFields
        [("id", Unrestricted)]
        (Just (UnadmittedNominalRestriction "source spelling is not evidence"))
        strengthened
        == Just
          (Left
            (StrongerModeUnadmittedJustification
              "source spelling is not evidence"))
    )
    "unadmitted nominal restriction was treated as strengthening evidence"

recordModeWeakening :: Either String ()
recordModeWeakening = do
  weakened <- onlyRecord
    "record BadWrapper mode unrestricted { payload : Resource }"
  equal <- onlyRecord
    "record LeaseWrapper mode affine { payload : Lease }"
  assert
    ( grammarV1RecordModeFromCheckedFields
        [("payload", Linear)]
        Nothing
        weakened
        == Just (Left (DeclaredModeWeakensDerived Linear Unrestricted))
    )
    "explicit unrestricted record mode laundered a supplied linear field mode"
  assert
    ( grammarV1RecordModeFromCheckedFields
        [("payload", Affine)]
        Nothing
        equal
        == Just (Right Affine)
    )
    "explicit mode equal to the derived minimum spuriously required strengthening evidence"

recordModeFieldCorrespondence :: Either String ()
recordModeFieldCorrespondence = do
  record <- onlyRecord
    "record Ordered { first : U8, second : Bool }"
  assert
    ( grammarV1RecordModeFromCheckedFields
        [("second", Unrestricted), ("first", Linear)]
        Nothing
        record
        == Nothing
    )
    "reordered checked field-mode evidence was accepted for the wrong source fields"
  assert
    ( grammarV1RecordModeFromCheckedFields
        [("first", Unrestricted)]
        Nothing
        record
        == Nothing
    )
    "incomplete checked field-mode evidence was accepted"
  assert
    ( grammarV1RecordModeFromCheckedFields
        [("first", Unrestricted), ("second", Unrestricted), ("extra", Linear)]
        Nothing
        record
        == Nothing
    )
    "extra checked field-mode evidence was silently folded into the record mode"

checkedRecordModeComposition :: Either String ()
checkedRecordModeComposition = do
  plain <- onlyRecord
    "record Plain { left : U8, right : Bool }"
  owned <- onlyRecord
    "record Owned { plain : U8, payload : Bytes[7] }"
  duplicate <- onlyRecord
    "record Duplicate { item : U8, item : Bytes[7] }"
  assert
    ( grammarV1CheckedClosedRecordMode emptyStaticContext Nothing plain
        == Just
          (Right
            GrammarV1CheckedRecordMode
              { checkedRecordModeFields =
                  [ ("left", CheckedTypeMode (TyUInt 8) Unrestricted, [])
                  , ("right", CheckedTypeMode TyBool Unrestricted, [])
                  ]
              , checkedRecordStructuralMode = Unrestricted
              })
    )
    "closed intrinsic record did not derive unrestricted mode from exact checked fields"
  assert
    ( grammarV1CheckedClosedRecordMode emptyStaticContext Nothing owned
        == Just
          (Right
            GrammarV1CheckedRecordMode
              { checkedRecordModeFields =
                  [ ("plain", CheckedTypeMode (TyUInt 8) Unrestricted, [])
                  , ("payload", CheckedTypeMode (TyBytes (RefNat 7)) Linear, [])
                  ]
              , checkedRecordStructuralMode = Linear
              })
    )
    "owned Bytes field did not drive exact closed record mode to linear"
  case grammarV1CheckedClosedRecordMode emptyStaticContext Nothing duplicate of
    Just (Right checked) -> do
      assert
        (map (\(name, _, _) -> name) (checkedRecordModeFields checked)
          == ["item", "item"])
        "closed record mode composition normalized duplicate source field spelling"
      assert (checkedRecordStructuralMode checked == Linear)
        "duplicate-spelling record lost the strongest exact field mode"
    other -> Left ("duplicate-spelling closed record mode rejected: " <> show other)

checkedRecordModeFailureBoundaries :: Either String ()
checkedRecordModeFailureBoundaries = do
  context <- mapLeft show $
    declareTransparentClaim
      "Positive"
      [(Name "x", SortUInt 8)]
      (LessThan
        (RefNat 0)
        (RefToNat (RefVar (Name "x"))))
      emptyStaticContext
  strengthened <- onlyRecord
    "record FireOnce mode linear { value : {v : U8 | Positive(v)} }"
  weakened <- onlyRecord
    "record BadWrapper mode unrestricted { payload : Bytes[7] }"
  unknown <- onlyRecord
    "record BadClaim { proof : Proof[Missing(1)] }"
  unresolved <- onlyRecord
    "record Framed { frame : Frame[Hello] }"
  assert
    ( grammarV1CheckedClosedRecordMode context Nothing strengthened
        == Just
          (Left
            (GrammarV1RecordModeNominalError
              (StrongerModeMissingJustification Unrestricted Linear)))
    )
    "composed record mode bypassed strict-strengthening justification"
  case grammarV1CheckedClosedRecordMode
      context
      (Just (AdmittedLifecycleObligation "fire-once lifecycle"))
      strengthened of
    Just (Right checked) -> case checkedRecordModeFields checked of
      [("value", CheckedTypeMode (TyRefined binder base predicate) Unrestricted, steps)] -> do
        assert (binder == Name "v" && base == TyUInt 8)
          "composed record mode changed refinement binder/base"
        assert
          (predicate == LessThan
            (RefNat 0)
            (RefToNat (RefVar (Name "v"))))
          "composed record mode changed canonical refinement predicate"
        assert (ExpandedTransparentClaim "Positive" `elem` steps)
          "composed record mode lost checked type focusing trace"
        assert (checkedRecordStructuralMode checked == Linear)
          "admitted nominal strengthening did not produce exact linear mode"
      fields -> Left ("unexpected composed refinement field payload: " <> show fields)
    other -> Left ("admitted composed record strengthening rejected: " <> show other)
  assert
    ( grammarV1CheckedClosedRecordMode emptyStaticContext Nothing weakened
        == Just
          (Left
            (GrammarV1RecordModeNominalError
              (DeclaredModeWeakensDerived Linear Unrestricted)))
    )
    "composed record mode allowed explicit weakening of intrinsic linear field"
  assert
    ( grammarV1CheckedClosedRecordMode emptyStaticContext Nothing unknown
        == Just (Left (GrammarV1RecordModeFocusingError (UnknownClaim "Missing")))
    )
    "record-field Core failure collapsed into nominal failure or source non-competence"
  assert
    (grammarV1CheckedClosedRecordMode emptyStaticContext Nothing unresolved == Nothing)
    "declaration-backed Frame field acquired a guessed structural mode"

openRecordFormsReject :: Either String ()
openRecordFormsReject = do
  genericRecord <- onlyRecord
    "record Generic[T : Type] { value : T }"
  requiredRecord <- onlyRecord
    "record Required requires { proposition true; } { value : U8 }"
  assert
    (grammarV1CheckedRecordFields emptyStaticContext genericRecord == Nothing)
    "generic record bypassed the closed-record field competence wall"
  assert
    (grammarV1CheckedRecordFields emptyStaticContext requiredRecord == Nothing)
    "requirement-bearing record bypassed the closed-record field competence wall"
  assert
    ( grammarV1RecordModeFromCheckedFields
        [("value", Unrestricted)]
        Nothing
        genericRecord
        == Nothing
    )
    "generic record bypassed the closed-record mode competence wall"
  assert
    ( grammarV1RecordModeFromCheckedFields
        [("value", Unrestricted)]
        Nothing
        requiredRecord
        == Nothing
    )
    "requirement-bearing record bypassed the closed-record mode competence wall"
  assert
    (grammarV1CheckedClosedRecordMode emptyStaticContext Nothing genericRecord == Nothing)
    "generic record bypassed composed closed-record mode competence"
  assert
    (grammarV1CheckedClosedRecordMode emptyStaticContext Nothing requiredRecord == Nothing)
    "requirement-bearing record bypassed composed closed-record mode competence"

onlyRecord :: Text.Text -> Either String GrammarV1RecordDecl
onlyRecord source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "checked-record-fields" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1RecordDeclaration record -> Right record
      other -> Left ("expected record declaration, got " <> show other)
    declarations -> Left
      ("expected one record declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
