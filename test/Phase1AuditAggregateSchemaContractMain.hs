{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.CheckedBindingMode
  ( CheckedTypeMode (..)
  )
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext
  , emptyContext
  , insertBinding
  , useBinding
  )
import Phil.Core.DataBorrow
  ( BorrowedAggregateField (..)
  , DataBorrowError (..)
  , beginBorrowedAggregateField
  , endBorrowedAggregateField
  )
import Phil.Core.DataDestruction
  ( DataDestructionError (..)
  , FieldDisposition (..)
  , OwnedField (..)
  , checkOwnedFieldSchema
  , consumeAggregateFields
  )
import Phil.Core.DataSum
  ( DataSumError (..)
  , SumConstructor (..)
  , consumeSelectedSumPayload
  , selectSumConstructorPayload
  )
import Phil.Core.Focusing (FocusStep (..))
import Phil.Core.Static
  ( StaticContext
  , declareTransparentClaim
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
import Phil.Surface.GrammarV1.DataVariants
  ( GrammarV1CheckedDataMode (..)
  , GrammarV1CheckedVariantMode (..)
  , GrammarV1CheckedVariantModePayload (..)
  , grammarV1CheckedClosedDataMode
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.RecordFields
  ( GrammarV1CheckedRecordMode (..)
  , grammarV1CheckedClosedRecordMode
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "D-AGG-SCHEMA-01 record declaration -> exact supplied schema -> borrow/eliminate"
        recordRoute
    , test "D-AGG-SCHEMA-01 duplicate-preserving record view is rejected only at consuming schema boundary"
        recordDuplicateBoundary
    , test "D-AGG-SCHEMA-01 data declaration -> exact supplied constructor schema -> consuming elimination"
        dataRoute
    , test "D-AGG-SCHEMA-01 ambiguous supplied sum tags and payload fields reject before lookup"
        sumAmbiguityBoundary
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

recordRoute :: Either String ()
recordRoute = do
  context <- refinementContext
  declaration <- onlyRecord $ Text.unlines
    [ "record Packet {"
    , "  count : U32,"
    , "  refined : {v : U8 | Positive(v)},"
    , "  payload : Bytes[7],"
    , "}"
    ]
  checked <- case grammarV1CheckedClosedRecordMode context Nothing declaration of
    Just (Right result) -> Right result
    other -> Left ("closed record declaration did not produce checked schema: " <> show other)
  let suppliedFields = recordOwnedFields checked
  assert
    ( suppliedFields
        == [ OwnedField (Name "count") Unrestricted (TyUInt 32)
           , OwnedField (Name "refined") Unrestricted expectedRefinedTy
           , OwnedField (Name "payload") Linear (TyBytes (RefNat 7))
           ]
    )
    "record checked schema did not preserve source order, exact types/refinement, and modes"
  assert (checkedRecordStructuralMode checked == Linear)
    "record aggregate mode did not preserve the owned payload"

  -- Phase 1's Core helper route accepts an explicitly supplied owner/schema
  -- association. The opaque owner type below is deliberately not inferred from
  -- the declaration spelling; this test witnesses the supported interface.
  original <- mapLeft show $
    insertBinding Linear recordOwner (TyOpaque "SuppliedRecordOwner") emptyContext

  (borrowed, loaned) <- mapLeft show $
    beginBorrowedAggregateField recordOwner suppliedFields (Name "payload") original
  assert
    ( borrowedAggregateOwner borrowed == recordOwner
      && borrowedAggregateField borrowed == Name "payload"
      && borrowedAggregateFieldMode borrowed == Linear
      && borrowedAggregateFieldType borrowed == TyBytes (RefNat 7)
    )
    "record borrow did not retain the exact supplied field type/mode"
  restored <- mapLeft show $ endBorrowedAggregateField borrowed loaned
  assert (restored == original)
    "record borrow did not restore the original owner context exactly"

  eliminated <- mapLeft show $
    consumeAggregateFields
      recordOwner
      suppliedFields
      [ (ownedFieldName field, FieldBound) | field <- suppliedFields ]
      original
  assertOwnerConsumed recordOwner eliminated
  assertBinding Unrestricted (Name "count") (TyUInt 32) eliminated
  assertBinding Unrestricted (Name "refined") expectedRefinedTy eliminated
  assertLinearOneUse (Name "payload") (TyBytes (RefNat 7)) eliminated

recordDuplicateBoundary :: Either String ()
recordDuplicateBoundary = do
  declaration <- onlyRecord
    "record Duplicate { item : U8, item : Bytes[7] }"
  checked <- case grammarV1CheckedClosedRecordMode emptyStaticContext Nothing declaration of
    Just (Right result) -> Right result
    other -> Left ("duplicate-preserving record view unexpectedly failed: " <> show other)
  let suppliedFields = recordOwnedFields checked
  assert
    (map ownedFieldName suppliedFields == [Name "item", Name "item"])
    "local checked record view stopped preserving duplicate source spelling"
  assert
    (checkOwnedFieldSchema suppliedFields == Left (DuplicateOwnedField (Name "item")))
    "ambiguous supplied record schema crossed the competent consumer boundary"

  ownerContext <- mapLeft show $
    insertBinding Linear recordOwner (TyOpaque "SuppliedRecordOwner") emptyContext
  case beginBorrowedAggregateField recordOwner suppliedFields (Name "item") ownerContext of
    Left (DataBorrowSchemaError (DuplicateOwnedField (Name "item"))) -> Right ()
    other -> Left ("record borrow performed lossy first-match lookup: " <> show other)

dataRoute :: Either String ()
dataRoute = do
  context <- refinementContext
  declaration <- onlyData $ Text.unlines
    [ "data Choice ="
    , "    None"
    , "  | Pair(U16, Bool)"
    , "  | Owned{payload : Bytes[7], refined : {v : U8 | Positive(v)},}"
    , "  ;"
    ]
  checked <- case grammarV1CheckedClosedDataMode context Nothing declaration of
    Just (Right result) -> Right result
    other -> Left ("closed data declaration did not produce checked schema: " <> show other)

  assert
    (map checkedVariantModeName (checkedDataModeVariants checked)
      == ["None", "Pair", "Owned"])
    "data checked schema changed source variant order"
  assert (checkedDataStructuralMode checked == Linear)
    "data aggregate mode did not preserve the owned payload"

  ownedPayload <- case checkedDataModeVariants checked of
    [ GrammarV1CheckedVariantMode "None" Nothing
      , GrammarV1CheckedVariantMode "Pair"
          (Just (GrammarV1CheckedVariantModeTuple
            [ (CheckedTypeMode (TyUInt 16) Unrestricted, [])
            , (CheckedTypeMode TyBool Unrestricted, [])
            ]))
      , GrammarV1CheckedVariantMode "Owned"
          (Just (GrammarV1CheckedVariantModeRecord fields))
      ] -> do
        let supplied = checkedRecordPayloadFields fields
        assert
          ( supplied
              == [ OwnedField (Name "payload") Linear (TyBytes (RefNat 7))
                 , OwnedField (Name "refined") Unrestricted expectedRefinedTy
                 ]
          )
          "data record payload lost exact source order, types/refinement, or modes"
        Right supplied
    other -> Left ("data checked schema changed payload shape: " <> show other)

  -- Tag assignment and owner/declaration association are explicit caller
  -- premises in the supported helper route; neither is inferred from spelling.
  let constructors =
        [ SumConstructor 0 []
        , SumConstructor 1
            [ OwnedField (Name "first") Unrestricted (TyUInt 16)
            , OwnedField (Name "second") Unrestricted TyBool
            ]
        , SumConstructor 2 ownedPayload
        ]
  selected <- mapLeft show $ selectSumConstructorPayload 2 constructors
  assert (selected == ownedPayload)
    "sum selection changed exact supplied payload schema"

  original <- mapLeft show $
    insertBinding Linear sumOwner (TyOpaque "SuppliedSumOwner") emptyContext
  eliminated <- mapLeft show $
    consumeSelectedSumPayload sumOwner 2 constructors original
  assertOwnerConsumed sumOwner eliminated
  assertLinearOneUse (Name "payload") (TyBytes (RefNat 7)) eliminated
  assertBinding Unrestricted (Name "refined") expectedRefinedTy eliminated

sumAmbiguityBoundary :: Either String ()
sumAmbiguityBoundary = do
  let field = OwnedField (Name "payload") Linear (TyBytes (RefNat 7))
      duplicateField =
        [ OwnedField (Name "item") Unrestricted (TyUInt 8)
        , OwnedField (Name "item") Linear (TyBytes (RefNat 7))
        ]
  assert
    ( selectSumConstructorPayload
        1
        [SumConstructor 1 [field], SumConstructor 1 []]
        == Left (DuplicateSumConstructorTag 1)
    )
    "ambiguous supplied constructor tags used first-match lookup"
  assert
    ( selectSumConstructorPayload 1 [SumConstructor 1 duplicateField]
        == Left
          (DataSumDestructionError (DuplicateOwnedField (Name "item")))
    )
    "sum selection admitted an ambiguous selected payload schema"

recordOwnedFields :: GrammarV1CheckedRecordMode -> [OwnedField]
recordOwnedFields checked =
  [ OwnedField (Name name) (checkedBindingMode typeMode) (checkedBindingType typeMode)
  | (name, typeMode, _) <- checkedRecordModeFields checked
  ]

checkedRecordPayloadFields
  :: [(Text.Text, CheckedTypeMode, [FocusStep])]
  -> [OwnedField]
checkedRecordPayloadFields fields =
  [ OwnedField (Name name) (checkedBindingMode typeMode) (checkedBindingType typeMode)
  | (name, typeMode, _) <- fields
  ]

refinementContext :: Either String StaticContext
refinementContext =
  mapLeft show $
    declareTransparentClaim
      "Positive"
      [(Name "x", SortUInt 8)]
      (LessThan
        (RefNat 0)
        (RefToNat (RefVar (Name "x"))))
      emptyStaticContext

expectedRefinedTy :: Ty
expectedRefinedTy =
  TyRefined
    (Name "v")
    (TyUInt 8)
    (LessThan
      (RefNat 0)
      (RefToNat (RefVar (Name "v"))))

recordOwner, sumOwner :: Name
recordOwner = Name "record-owner"
sumOwner = Name "sum-owner"

assertOwnerConsumed :: Name -> ResourceContext -> Either String ()
assertOwnerConsumed owner context =
  case useBinding owner context of
    Left (UnknownBinding actual) ->
      assert (actual == owner) "wrong aggregate owner reported consumed"
    other -> Left ("aggregate owner remained usable after elimination: " <> show other)

assertBinding :: Mode -> Name -> Ty -> ResourceContext -> Either String ()
assertBinding expectedMode name expectedTy context = do
  (actualMode, actualTy, _) <- mapLeft show $ useBinding name context
  assert
    (actualMode == expectedMode && actualTy == expectedTy)
    ("successor binding changed mode/type: " <> show (actualMode, actualTy))

assertLinearOneUse :: Name -> Ty -> ResourceContext -> Either String ()
assertLinearOneUse name expectedTy context = do
  (mode, actualTy, once) <- mapLeft show $ useBinding name context
  assert (mode == Linear && actualTy == expectedTy)
    "linear successor changed mode/type"
  case useBinding name once of
    Left (UnknownBinding actual) ->
      assert (actual == name) "wrong linear successor reported consumed"
    other -> Left ("linear successor remained reusable: " <> show other)

onlyRecord :: Text.Text -> Either String GrammarV1RecordDecl
onlyRecord source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "aggregate-schema-record" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1RecordDeclaration declaration -> Right declaration
      other -> Left ("expected record declaration, got " <> show other)
    declarations -> Left
      ("expected one record declaration, got " <> show (length declarations))

onlyData :: Text.Text -> Either String GrammarV1DataDecl
onlyData source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "aggregate-schema-data" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1DataDeclaration declaration -> Right declaration
      other -> Left ("expected data declaration, got " <> show other)
    declarations -> Left
      ("expected one data declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
