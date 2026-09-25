{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Checker (emptyCheckState)
import Phil.Core.Context
import qualified Phil.Core.DataBorrow as B
import qualified Phil.Core.DataDestruction as D
import qualified Phil.Core.DataMode as P
import qualified Phil.Core.DataSum as S
import Phil.Core.Static (StaticContext, declareTransparentClaim, emptyStaticContext)
import Phil.Core.Syntax
import Phil.Core.Value (ValueResult (..), checkValue)
import Phil.Surface.GrammarV1.DataVariants
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.RecordFields
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

-- The product schema below is produced and stored by formProductBinding.
-- Record/data declarations are parsed and checked by Phil. Their translation to
-- OwnedField/tag tables and association with an opaque owner are explicitly
-- audit-owned supplied-interface premises, not discovered compiler exporters.
-- No returned product, checked declaration view, or resource state is edited.

right :: Show e => Either e a -> Either String a
right = either (Left . show) Right
ensure :: Bool -> String -> Either String ()
ensure True _ = Right ()
ensure False message = Left message
exact :: (Eq e, Show e, Show a) => e -> Either e a -> Either String ()
exact wanted result = case result of
  Left actual | actual == wanted -> Right ()
  other -> Left ("expected " <> show wanted <> "; got " <> show other)

u, a, l, productName, owner :: Name
u = Name "original-code"
a = Name "original-optional"
l = Name "original-bytes"
productName = Name "actual-product"
owner = Name "supplied-owner"

refinedTy :: Ty
refinedTy = TyRefined (Name "v") (TyUInt 8)
  (LessEqual (RefToNat (RefVar (Name "v"))) (RefNat 1))

seed :: Either String ResourceContext
seed = do
  checked <- right $ checkValue (VUInt 8 0) refinedTy emptyCheckState
  ensure (valueResultType checked == refinedTy
    && valueResultTerm checked == Just (RefUInt 8 0)) "literal admission changed"
  first <- right $ insertBinding Unrestricted u (valueResultType checked) emptyContext
  second <- right $ insertBinding Affine a TyBool first
  right $ insertBinding Linear l (TyBytes (RefNat 5)) second

productFixture :: Either String (ProductValue, ResourceContext)
productFixture = do
  initial <- seed
  actual@(value,after) <- right $ P.formProductBinding productName [u,a,l] initial
  let expectedElements = [ProductElementType Unrestricted refinedTy,
        ProductElementType Affine TyBool, ProductElementType Linear (TyBytes (RefNat 5))]
  ensure (value == ProductValue expectedElements) "formation lost source order, modes or refinement"
  expected <- right $ insertBinding Unrestricted u refinedTy emptyContext
    >>= insertBinding Linear productName (TyProduct expectedElements)
  ensure (after == expected) "formation did not consume precisely the restricted inputs"
  pure actual

successors :: [Name]
successors = map Name ["restored-code","restored-optional","restored-bytes"]

threeSuccessors :: Either String (Name, Name, Name)
threeSuccessors = case successors of
  [nu,na,nl] -> Right (nu,na,nl)
  _ -> Left "audit fixture must provide exactly three successor names"

lookupExact :: Mode -> Name -> Ty -> ResourceContext -> Either String ()
lookupExact mode name ty context = do
  (actualMode,actualTy,_) <- right $ useBinding name context
  ensure (mode == actualMode && ty == actualTy) "binding type/mode changed"

productRoundTrip :: Either String ()
productRoundTrip = do
  (_,formed) <- productFixture
  restored <- right $ P.eliminateProductBinding productName successors formed
  (nu,na,nl) <- threeSuccessors
  base <- right $ insertBinding Unrestricted u refinedTy emptyContext
  withU <- right $ insertBinding Unrestricted nu refinedTy base
  withA <- right $ insertBinding Affine na TyBool withU
  expected <- right $ insertBinding Linear nl (TyBytes (RefNat 5)) withA
  ensure (restored == expected) "elimination did not use the actual stored ordered schema"
  exact (UnknownBinding productName) (useBinding productName restored)
  (_,_,once) <- right $ useBinding nl restored
  exact (UnknownBinding nl) (useBinding nl once)
  right $ ensureComplete once

nestedRoundTrip :: Either String ()
nestedRoundTrip = do
  (_,inner) <- productFixture
  let outerName = Name "outer-product"
      recovered = Name "recovered-inner"
      copyCode = Name "outer-code"
  (_,outer) <- right $ P.formProductBinding outerName [productName,u] inner
  middle <- right $ P.eliminateProductBinding outerName [recovered,copyCode] outer
  restored <- right $ P.eliminateProductBinding recovered successors middle
  (nu,na,nl) <- threeSuccessors
  lookupExact Unrestricted nu refinedTy restored
  lookupExact Affine na TyBool restored
  lookupExact Linear nl (TyBytes (RefNat 5)) restored
  lookupExact Unrestricted copyCode refinedTy restored
  mapM_ (\name -> exact (UnknownBinding name) (useBinding name restored))
    [productName,outerName,recovered]

unrestrictedProduct :: Either String ()
unrestrictedProduct = do
  checked <- right $ checkValue (VUInt 8 0) refinedTy emptyCheckState
  initial <- right $ insertBinding Unrestricted u (valueResultType checked) emptyContext
  (actual,formed) <- right $ P.formProductBinding productName [u,u] initial
  ensure (actual == ProductValue (replicate 2 (ProductElementType Unrestricted refinedTy)))
    "legitimate repeated unrestricted values changed"
  let x = Name "copy-one"; y = Name "copy-two"
  restored <- right $ P.eliminateProductBinding productName [x,y] formed
  lookupExact Unrestricted x refinedTy restored
  lookupExact Unrestricted y refinedTy restored
  lookupExact Unrestricted productName (TyProduct (replicate 2 (ProductElementType Unrestricted refinedTy))) restored
  right $ ensureComplete restored

restrictedRepeated :: Either String ()
restrictedRepeated = do
  initial <- seed
  exact (P.ProductContextError (UnknownBinding l)) $
    P.formProductBinding productName [l,l] initial

productShapeErrors :: Either String ()
productShapeErrors = do
  (_,formed) <- productFixture
  exact (P.ProductArityMismatch 3 2) $ P.eliminateProductBinding productName (take 2 successors) formed
  let duplicate = Name "duplicate-successor"
  exact (P.ProductContextError (DuplicateBinding duplicate)) $
    P.eliminateProductBinding productName [duplicate,duplicate,Name "third"] formed

sourceContext :: Either String StaticContext
sourceContext = right $ declareTransparentClaim "Small" [(Name "x",SortUInt 8)]
  (LessEqual (RefToNat (RefVar (Name "x"))) (RefNat 1)) emptyStaticContext

oneDeclaration :: Text -> Either String GrammarV1Declaration
oneDeclaration source = do
  parsed <- right $ parseGrammarV1StructuralSource "independent-schema-consumer" source
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> Right (locatedValue (grammarV1Declaration top))
    _ -> Left "fixture must contain one source declaration"

recordFields :: Either String [D.OwnedField]
recordFields = do
  static <- sourceContext
  parsed <- oneDeclaration "record AuditRecord { code : {v : U8 | Small(v)}, payload : Bytes[5] }"
  declaration <- case parsed of
    GrammarV1RecordDeclaration value -> Right value
    _ -> Left "wrong record source constructor"
  checked <- case grammarV1CheckedClosedRecordMode static Nothing declaration of
    Just (Right value) -> Right value
    other -> Left ("record did not reach checked view: " <> show other)
  let fields = [D.OwnedField (Name name) (checkedBindingMode tm) (checkedBindingType tm)
               | (name,tm,_) <- checkedRecordModeFields checked]
  ensure (fields == [D.OwnedField (Name "code") Unrestricted refinedTy,
    D.OwnedField (Name "payload") Linear (TyBytes (RefNat 5))]) "record schema changed"
  ensure (checkedRecordStructuralMode checked == Linear) "record structural mode changed"
  pure fields

ownerContext :: Either String ResourceContext
ownerContext = right $ insertBinding Linear owner (TyOpaque "ExplicitSchemaOwner") emptyContext

recordConsume :: Either String ()
recordConsume = do
  fields <- recordFields
  initial <- ownerContext
  after <- right $ D.consumeAggregateFields owner fields
    [(D.ownedFieldName field,D.FieldBound) | field <- fields] initial
  lookupExact Unrestricted (Name "code") refinedTy after
  lookupExact Linear (Name "payload") (TyBytes (RefNat 5)) after
  exact (UnknownBinding owner) (useBinding owner after)
  (_,_,once) <- right $ useBinding (Name "payload") after
  exact (UnknownBinding (Name "payload")) (useBinding (Name "payload") once)
  right $ ensureComplete once

borrowLifecycle :: Either String ()
borrowLifecycle = do
  fields <- recordFields
  initial <- ownerContext
  let unrelated = Name "unrelated"
  withOther <- right $ insertBinding Linear unrelated (TyUInt 8) initial
  (view,loaned) <- right $ B.beginBorrowedAggregateField owner fields (Name "payload") withOther
  ensure (view == B.BorrowedAggregateField owner (Name "payload") Linear (TyBytes (RefNat 5)))
    "borrowed view changed its exact supplied type/mode"
  exact (OwnerBorrowed owner) (useBinding owner loaned)
  exact (EscapingLoans (Set.singleton owner)) (ensureComplete loaned)
  exact (UnknownBinding (Name "payload")) (useBinding (Name "payload") loaned)
  exact (D.DataDestructionContextError (OwnerBorrowed owner)) $
    D.consumeAggregateFields owner fields [(D.ownedFieldName f,D.FieldBound) | f <- fields] loaned
  (_,_,afterOther) <- right $ useBinding unrelated loaned
  ended <- right $ B.endBorrowedAggregateField view afterOther
  ensure (ended == initial) "ending loan reset or lost the actual body resource transition"
  exact (B.DataBorrowContextError (LoanNotActive owner)) (B.endBorrowedAggregateField view ended)

fieldModes :: Either String ()
fieldModes = do
  initial <- ownerContext
  let fields = [D.OwnedField u Unrestricted refinedTy,D.OwnedField a Affine TyBool,
                D.OwnedField l Linear (TyBytes (RefNat 5))]
  after <- right $ D.consumeAggregateFields owner fields [(l,D.FieldBound)] initial
  expected <- right $ insertBinding Linear l (TyBytes (RefNat 5)) emptyContext
  ensure (after == expected) "legitimate omission changed remaining ownership"
  exact (D.MissingLinearFieldDisposition l) $ D.consumeAggregateFields owner fields [(l,D.FieldOmitted)] initial

ambiguousRecord :: Either String ()
ambiguousRecord = do
  fields <- recordFields
  initial <- ownerContext
  case fields of
    [first,lastField] -> do
      let dup = [first,lastField,first]
          key = D.ownedFieldName first
      exact (D.DuplicateOwnedField key) $ D.checkOwnedFieldSchema dup
      exact (D.DuplicateOwnedField key) $ D.consumeAggregateFields owner dup [] initial
      exact (B.DataBorrowSchemaError (D.DuplicateOwnedField key)) $
        B.beginBorrowedAggregateField owner dup (D.ownedFieldName lastField) initial
    _ -> Left "wrong checked record inventory"

dataConstructors :: Either String [S.SumConstructor]
dataConstructors = do
  static <- sourceContext
  parsed <- oneDeclaration "data AuditChoice = Empty | Pair(U16, Bool) | Owned{payload : Bytes[5], code : {v : U8 | Small(v)}};"
  declaration <- case parsed of
    GrammarV1DataDeclaration value -> Right value
    _ -> Left "wrong data source constructor"
  checked <- case grammarV1CheckedClosedDataMode static Nothing declaration of
    Just (Right value) -> Right value
    other -> Left ("data did not reach checked view: " <> show other)
  case checkedDataModeVariants checked of
    [GrammarV1CheckedVariantMode "Empty" Nothing,
     GrammarV1CheckedVariantMode "Pair" (Just (GrammarV1CheckedVariantModeTuple pair)),
     GrammarV1CheckedVariantMode "Owned" (Just (GrammarV1CheckedVariantModeRecord fields))] -> do
       let toField name tm = D.OwnedField name (checkedBindingMode tm) (checkedBindingType tm)
           pairFields = zipWith (\name (tm,_) -> toField name tm) [Name "pair-left",Name "pair-right"] pair
           owned = [toField (Name name) tm | (name,tm,_) <- fields]
       ensure (length pair == 2 && pairFields == [D.OwnedField (Name "pair-left") Unrestricted (TyUInt 16),
           D.OwnedField (Name "pair-right") Unrestricted TyBool]) "tuple source payload changed"
       ensure (owned == [D.OwnedField (Name "payload") Linear (TyBytes (RefNat 5)),
           D.OwnedField (Name "code") Unrestricted refinedTy]) "record source payload changed"
       ensure (checkedDataStructuralMode checked == Linear) "sum source aggregate mode changed"
       -- Deliberately explicit audit-owned tag association and tuple binder names.
       pure [S.SumConstructor 10 [],S.SumConstructor 20 pairFields,S.SumConstructor 30 owned]
    other -> Left ("source variant order/shape changed: " <> show other)

sumConsume :: Int -> Either String ()
sumConsume tag = do
  constructors <- dataConstructors
  initial <- ownerContext
  selected <- right $ S.selectSumConstructorPayload tag constructors
  after <- right $ S.consumeSelectedSumPayload owner tag constructors initial
  expected <- foldl (\acc f -> acc >>= right . insertBinding (D.ownedFieldMode f) (D.ownedFieldName f) (D.ownedFieldType f))
    (Right emptyContext) selected
  ensure (after == expected) "consumer did not restore exactly its actual selected payload"
  exact (UnknownBinding owner) (useBinding owner after)
  if tag == 30 then do
    let key = Name "payload"
    exact (S.DataSumContextError (UnconsumedLinearResources (Map.singleton key (TyBytes (RefNat 5))))) $
      S.checkContinuingSumArm selected after
    (_,_,once) <- right $ useBinding key after
    exact (UnknownBinding key) (useBinding key once)
    right $ S.checkContinuingSumArm selected once
  else right $ S.checkContinuingSumArm selected after

ambiguousSum :: Either String ()
ambiguousSum = do
  constructors <- dataConstructors
  initial <- ownerContext
  let repeatedTags = constructors <> [S.SumConstructor 20 []]
  exact (S.DuplicateSumConstructorTag 20) $ S.selectSumConstructorPayload 10 repeatedTags
  exact (S.DuplicateSumConstructorTag 20) $ S.consumeSelectedSumPayload owner 30 repeatedTags initial
  fields <- recordFields
  case fields of
    first : _ -> do
      let dup = [S.SumConstructor 30 (fields <> [first])]
          expected = S.DataSumDestructionError (D.DuplicateOwnedField (D.ownedFieldName first))
      exact expected $ S.selectSumConstructorPayload 30 dup
      exact expected $ S.consumeSelectedSumPayload owner 30 dup initial
    [] -> Left "missing original checked field"

unknownSchemaSelections :: Either String ()
unknownSchemaSelections = do
  constructors <- dataConstructors
  exact (S.UnknownSumConstructor 99) $ S.selectSumConstructorPayload 99 constructors
  fields <- recordFields
  initial <- ownerContext
  exact (B.UnknownBorrowedAggregateField (Name "absent")) $
    B.beginBorrowedAggregateField owner fields (Name "absent") initial
  exact (D.UnknownFieldDisposition (Name "extra")) $ D.consumeAggregateFields owner fields
    [(Name "payload",D.FieldBound),(Name "extra",D.FieldBound)] initial

branchJoin :: Either String ()
branchJoin = do
  initial <- ownerContext
  let alternatives = [S.SumConstructor 1 [D.OwnedField l Linear (TyBytes (RefNat 5))],
                      S.SumConstructor 2 [D.OwnedField l Linear (TyBytes (RefNat 7))]]
  left <- right $ S.consumeSelectedSumPayload owner 1 alternatives initial
  other <- right $ S.consumeSelectedSumPayload owner 2 alternatives initial
  exact (S.DataSumContextError (LinearBranchMismatch (linearBindings left) (linearBindings other))) $
    S.joinSumContinuing [left,other]
  (_,_,leftDone) <- right $ useBinding l left
  (_,_,rightDone) <- right $ useBinding l other
  joined <- right $ S.joinSumContinuing [leftDone,rightDone]
  ensure (joined == emptyContext) "finished branches did not converge without restoring owners"

main :: IO ()
main = do
  results <- sequence
    [ test "P01" "actual product formation stores exact source-derived ordered schema" (productFixture >> pure ())
    , test "P02" "product elimination recovers the stored refinement and ownership" productRoundTrip
    , test "P03" "nested actual products retain schemas through both eliminations" nestedRoundTrip
    , test "P04" "repeated unrestricted product inputs remain permitted" unrestrictedProduct
    , test "P05" "sequential product formation cannot reuse a restricted input" restrictedRepeated
    , test "P06" "actual product elimination checks arity and successor uniqueness" productShapeErrors
    , test "P07" "real checked record view reaches its explicit schema consumer" recordConsume
    , test "P08" "borrow pins owner and preserves independent body changes on loan end" borrowLifecycle
    , test "P09" "affine omission is permitted while linear omission rejects" fieldModes
    , test "P10" "record schema ambiguity rejects before selection or consumption" ambiguousRecord
    , test "P11" "real checked data owned payload retains refinement and one-use ownership" (sumConsume 30)
    , test "P12" "real checked tuple payload retains types and source order" (sumConsume 20)
    , test "P13" "nullary payload consumes owner without inventing fields" (sumConsume 10)
    , test "P14" "constructor and selected-field ambiguity reject in both entry routes" ambiguousSum
    , test "P15" "missing field/tag and foreign dispositions reject exactly" unknownSchemaSelections
    , test "P16" "sum branch join rejects incompatible live payloads and admits consumed ones" branchJoin
    ]
  putStrLn "COMPLETE aggregate_consumer_groups=16"
  unless (and results) exitFailure

test :: String -> String -> Either String () -> IO Bool
test key label result = case result of
  Right () -> putStrLn ("PASS " <> key <> " " <> label) >> pure True
  Left problem -> putStrLn ("FAIL " <> key <> " " <> label <> " -- " <> problem) >> pure False
