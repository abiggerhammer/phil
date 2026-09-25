{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Checker (emptyCheckState)
import Phil.Core.Context
import Phil.Core.DataBorrow
import Phil.Core.DataDestruction
import Phil.Core.DataMode
import Phil.Core.DataSum
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
import Phil.Core.Value (ValueResult (..), checkValue)
import Phil.Surface.GrammarV1.DataVariants
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.RecordFields
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

-- Independent required-correctness controls for PR1408. All actual product,
-- checked-declaration and borrowed-view outputs are passed to their consumers
-- unchanged. A supplied Core binding context is an explicit typing premise.
-- The record/data-to-OwnedField/tag translation below is audit-owned, not an
-- identified general source compiler or a proof of nominal schema identity.
-- This file is PREPARED, NOT EXECUTED in its creation checkpoint.

type Result a = Either String a
right :: Show e => Either e a -> Result a
right = either (Left . show) Right
require :: Bool -> String -> Result ()
require True _ = Right ()
require False message = Left message
exact :: (Eq e, Show e, Show a) => e -> Either e a -> Result ()
exact wanted result = case result of
  Left actual | actual == wanted -> Right ()
  _ -> Left ("expected " <> show wanted <> ", got " <> show result)

u, a, l, p, owner, other, flag, bytes :: Name
u = Name "scalar"
a = Name "affine"
l = Name "linear"
p = Name "product"
owner = Name "owner"
other = Name "other-owner"
flag = Name "flag"
bytes = Name "bytes"

bind :: Mode -> Name -> Ty -> ResourceContext -> Result ResourceContext
bind mode name ty context = right $ insertBinding mode name ty context
absent :: Name -> ResourceContext -> Bool
absent name context = all (Map.notMember name)
  [unrestrictedBindings context, affineBindings context, linearBindings context]
expectBinding :: Mode -> Name -> Ty -> ResourceContext -> Result ()
expectBinding mode name ty context = do
  (actualMode,actualTy,_) <- right $ useBinding name context
  require (actualMode == mode && actualTy == ty) "binding type or structural mode changed"

refinedLiteral :: Result ValueResult
refinedLiteral = right $ checkValue (VUInt 8 1)
  (TyRefined (Name "v") (TyUInt 8)
    (LessEqual (RefToNat (RefVar (Name "v"))) (RefNat 7))) emptyCheckState

productFixture :: Result ([ProductElementType], ResourceContext, ProductValue, ResourceContext)
productFixture = do
  literal <- refinedLiteral
  start <- bind Unrestricted u (valueResultType literal) emptyContext
    >>= bind Affine a (TyOpaque "AuditAffine")
    >>= bind Linear l (TyBytes (RefNat 7))
    >>= bind Unrestricted (Name "unrelated") TyBool
  (value,formed) <- right $ formProductBinding p [u,a,l] start
  let wanted = [ProductElementType Unrestricted (valueResultType literal),
                ProductElementType Affine (TyOpaque "AuditAffine"),
                ProductElementType Linear (TyBytes (RefNat 7))]
  require (value == ProductValue wanted) "formation did not return the exact original element sequence"
  expectBinding Linear p (TyProduct wanted) formed
  require (absent a formed && absent l formed && not (absent u formed)) "formation changed source-use discipline"
  pure (wanted,start,value,formed)

productRestoration :: Result ()
productRestoration = do
  (wanted,_,_,formed) <- productFixture
  let names = [Name "scalar-out",Name "affine-out",Name "linear-out"]
  restored <- right $ eliminateProductBinding p names formed
  require (absent p restored) "consumed product remains present"
  mapM_ (\(name,element) -> expectBinding (productElementMode element) name
      (productElementType element) restored) (zip names wanted)
  expectBinding Unrestricted (Name "unrelated") TyBool restored
  (_,_,once) <- right $ useBinding (Name "linear-out") restored
  exact (UnknownBinding (Name "linear-out")) (useBinding (Name "linear-out") once)
  (_,_,affineOnce) <- right $ useBinding (Name "affine-out") once
  exact (UnknownBinding (Name "affine-out")) (useBinding (Name "affine-out") affineOnce)
  right $ ensureComplete affineOnce

unrestrictedProduct :: Result ()
unrestrictedProduct = do
  original <- bind Unrestricted u (TyUInt 8) emptyContext
  (value,formed) <- right $ formProductBinding p [u,u] original
  let elements = replicate 2 (ProductElementType Unrestricted (TyUInt 8))
  require (value == ProductValue elements) "legitimate repeated unrestricted use changed"
  restored <- right $ eliminateProductBinding p [Name "x",Name "y"] formed
  expectBinding Unrestricted p (TyProduct elements) restored
  expectBinding Unrestricted u (TyUInt 8) restored
  expectBinding Unrestricted (Name "x") (TyUInt 8) restored
  expectBinding Unrestricted (Name "y") (TyUInt 8) restored

emptyProduct :: Result ()
emptyProduct = do
  (value,formed) <- right $ formProductBinding p [] emptyContext
  require (value == ProductValue []) "empty product acquired elements"
  restored <- right $ eliminateProductBinding p [] formed
  require (restored == formed) "empty unrestricted product changed on elimination"

restrictedReuse :: Result ()
restrictedReuse = do
  start <- bind Linear l (TyBytes (RefNat 7)) emptyContext
  exact (ProductContextError (UnknownBinding l)) (formProductBinding p [l,l] start)
  loaned <- right $ startSharedLoan l start
  exact (ProductContextError (OwnerBorrowed l)) (formProductBinding p [l] loaned)

productBoundary :: Result ()
productBoundary = do
  (_,_,_,formed) <- productFixture
  exact (ProductArityMismatch 3 2) (eliminateProductBinding p [Name "x",Name "y"] formed)
  exact (ProductContextError (DuplicateBinding (Name "x")))
    (eliminateProductBinding p [Name "x",Name "x",Name "z"] formed)

recordSchema :: Text -> Result [OwnedField]
recordSchema source = do
  parsed <- right $ parseGrammarV1StructuralSource "independent-record" source
  declaration <- case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1RecordDeclaration record -> Right record
      _ -> Left "expected one record"
    _ -> Left "expected one declaration"
  checked <- case grammarV1CheckedClosedRecordMode emptyStaticContext Nothing declaration of
    Just (Right record) -> Right record
    result -> Left ("record fixture did not check: " <> show result)
  pure [OwnedField (Name name) (checkedBindingMode tm) (checkedBindingType tm)
       | (name,tm,_) <- checkedRecordModeFields checked]

checkedRecordConsumer :: Result ()
checkedRecordConsumer = do
  fields <- recordSchema "record Packet { flag : Bool, bytes : Bytes[7] }"
  require (fields == [OwnedField flag Unrestricted TyBool,OwnedField bytes Linear (TyBytes (RefNat 7))])
    "checked declaration changed source order or exact field schema"
  start <- bind Linear owner (TyOpaque "SuppliedRecordOwner") emptyContext
  end <- right $ consumeAggregateFields owner fields [(flag,FieldBound),(bytes,FieldBound)] start
  require (absent owner end) "record owner remains usable"
  expectBinding Unrestricted flag TyBool end
  expectBinding Linear bytes (TyBytes (RefNat 7)) end

fieldDispositions :: Result ()
fieldDispositions = do
  literal <- refinedLiteral
  let fields = [OwnedField u Unrestricted (valueResultType literal),
                OwnedField a Affine (TyOpaque "AuditAffine"),
                OwnedField l Linear (TyBytes (RefNat 7))]
  start <- bind Linear owner (TyOpaque "SuppliedRecordOwner") emptyContext
  end <- right $ consumeAggregateFields owner fields [(u,FieldBound),(a,FieldOmitted),(l,FieldBound)] start
  require (absent a end && absent owner end) "affine omission/owner consumption not preserved"
  expectBinding Unrestricted u (valueResultType literal) end
  exact (MissingLinearFieldDisposition l) (consumeAggregateFields owner fields [(u,FieldBound)] start)
  exact (DuplicateFieldDisposition l) (checkFieldDispositions fields [(l,FieldBound),(l,FieldBound)])

borrowRoundTrip :: Result ()
borrowRoundTrip = do
  fields <- recordSchema "record Packet { flag : Bool, bytes : Bytes[7] }"
  start <- bind Linear owner (TyOpaque "SuppliedRecordOwner") emptyContext
    >>= bind Affine other (TyOpaque "OtherOwner")
  before <- right $ startSharedLoan other start
  (view,during) <- right $ beginBorrowedAggregateField owner fields bytes before
  require (view == BorrowedAggregateField owner bytes Linear (TyBytes (RefNat 7))) "borrowed view lost exact returned schema"
  require (sharedLoans during == Set.fromList [owner,other]) "unrelated loan lost"
  exact (OwnerBorrowed owner) (useBinding owner during)
  exact (EscapingLoans (Set.fromList [owner,other])) (ensureComplete during)
  after <- right $ endBorrowedAggregateField view during
  require (after == before) "loan end did not restore the exact prior context"
  expectBinding Linear owner (TyOpaque "SuppliedRecordOwner") after

borrowPreventsElimination :: Result ()
borrowPreventsElimination = do
  fields <- recordSchema "record Packet { flag : Bool, bytes : Bytes[7] }"
  start <- bind Linear owner (TyOpaque "SuppliedRecordOwner") emptyContext
  (view,during) <- right $ beginBorrowedAggregateField owner fields bytes start
  exact (DataDestructionContextError (OwnerBorrowed owner))
    (consumeAggregateFields owner fields [(bytes,FieldBound)] during)
  exact (DataBorrowContextError (LoanAlreadyActive owner))
    (beginBorrowedAggregateField owner fields bytes during)
  after <- right $ endBorrowedAggregateField view during
  exact (DataBorrowContextError (LoanNotActive owner)) (endBorrowedAggregateField view after)

sumSchema :: Result [SumConstructor]
sumSchema = do
  parsed <- right $ parseGrammarV1StructuralSource "independent-sum"
    "data Choice = None | Payload(Bytes[7]) | Metadata(U8);"
  declaration <- case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1DataDeclaration dat -> Right dat
      _ -> Left "expected one data declaration"
    _ -> Left "wrong data declaration count"
  checked <- case grammarV1CheckedClosedDataMode emptyStaticContext Nothing declaration of
    Just (Right value) -> Right value
    result -> Left ("data fixture did not check: " <> show result)
  require (checkedDataStructuralMode checked == Linear) "sum derived mode changed"
  -- The chosen numeric tags and tuple-successor names are explicit audit
  -- association, not source-derived nominal identity.
  case checkedDataModeVariants checked of
    [GrammarV1CheckedVariantMode "None" Nothing,
     GrammarV1CheckedVariantMode "Payload" (Just (GrammarV1CheckedVariantModeTuple [(tm,[])])),
     GrammarV1CheckedVariantMode "Metadata" (Just (GrammarV1CheckedVariantModeTuple [(meta,[])]))] -> do
       require (tm == CheckedTypeMode (TyBytes (RefNat 7)) Linear && meta == CheckedTypeMode (TyUInt 8) Unrestricted)
         "sum payload schema changed"
       pure [SumConstructor 0 [],
             SumConstructor 1 [OwnedField bytes (checkedBindingMode tm) (checkedBindingType tm)],
             SumConstructor 2 [OwnedField u (checkedBindingMode meta) (checkedBindingType meta)]]
    result -> Left ("sum payload shapes changed: " <> show result)

sumSelection :: Result ()
sumSelection = do
  constructors <- sumSchema
  selected <- right $ selectSumConstructorPayload 1 constructors
  require (selected == [OwnedField bytes Linear (TyBytes (RefNat 7))]) "selection combined different alternatives"
  start <- bind Linear owner (TyOpaque "SuppliedSumOwner") emptyContext
  end <- right $ consumeSelectedSumPayload owner 1 constructors start
  require (absent owner end && absent u end) "sum acquired an unselected payload or retained its owner"
  expectBinding Linear bytes (TyBytes (RefNat 7)) end
  emptyEnd <- right $ consumeSelectedSumPayload owner 0 constructors start
  require (emptyEnd == emptyContext) "nullary sum retained owner or invented payload"

sumContinuation :: Result ()
sumContinuation = do
  constructors <- sumSchema
  selected <- right $ selectSumConstructorPayload 1 constructors
  start <- bind Linear owner (TyOpaque "SuppliedSumOwner") emptyContext
  end <- right $ consumeSelectedSumPayload owner 1 constructors start
  exact (DataSumContextError (UnconsumedLinearResources (Map.singleton bytes (TyBytes (RefNat 7)))))
    (checkContinuingSumArm selected end)
  (_,_,used) <- right $ useBinding bytes end
  right $ checkContinuingSumArm selected used
  joined <- right $ joinSumContinuing [used,emptyContext]
  require (joined == emptyContext) "sum convergence invented an owner"

sumNamesAreLocal :: Result ()
sumNamesAreLocal = do
  let first = OwnedField bytes Linear (TyBytes (RefNat 7))
      second = OwnedField bytes Unrestricted (TyUInt 8)
      constructors = [SumConstructor 0 [first],SumConstructor 1 [second]]
  a0 <- right $ selectSumConstructorPayload 0 constructors
  a1 <- right $ selectSumConstructorPayload 1 constructors
  require (a0 == [first] && a1 == [second]) "unique alternatives cannot reuse a local field name"
  exact (UnknownSumConstructor 9) (selectSumConstructorPayload 9 constructors)

rejectDuplicateFields :: Result ()
rejectDuplicateFields = do
  fields <- recordSchema "record Duplicate { bytes : U8, bytes : Bytes[7] }"
  require (length fields == 2 && map ownedFieldName fields == [bytes,bytes]) "duplicate-preserving view changed"
  start <- bind Linear owner (TyOpaque "SuppliedRecordOwner") emptyContext
  exact (DuplicateOwnedField bytes) (checkOwnedFieldSchema fields)
  exact (DuplicateOwnedField bytes) (consumeAggregateFields owner fields [(bytes,FieldBound)] start)
  exact (DataBorrowSchemaError (DuplicateOwnedField bytes)) (beginBorrowedAggregateField owner fields bytes start)

rejectDuplicateTags :: Result ()
rejectDuplicateTags = do
  let field = OwnedField bytes Linear (TyBytes (RefNat 7))
      constructors = [SumConstructor 0 [],SumConstructor 7 [field],SumConstructor 7 []]
  -- The duplicate is later and not the requested tag: this checks the entire
  -- constructor-key domain, not just the first matching entry.
  exact (DuplicateSumConstructorTag 7) (selectSumConstructorPayload 0 constructors)
  start <- bind Linear owner (TyOpaque "SuppliedSumOwner") emptyContext
  exact (DuplicateSumConstructorTag 7) (consumeSelectedSumPayload owner 0 constructors start)

rejectDuplicatePayload :: Result ()
rejectDuplicatePayload = do
  let fields = [OwnedField bytes Linear (TyBytes (RefNat 7)),OwnedField bytes Unrestricted TyBool]
      constructors = [SumConstructor 0 [],SumConstructor 1 fields]
  start <- bind Linear owner (TyOpaque "SuppliedSumOwner") emptyContext
  exact (DataSumDestructionError (DuplicateOwnedField bytes)) (selectSumConstructorPayload 1 constructors)
  exact (DataSumDestructionError (DuplicateOwnedField bytes)) (consumeSelectedSumPayload owner 1 constructors start)

main :: IO ()
main = do
  results <- sequence
    [ test "C01" "actual product formation stores exact refined ordered schema" (productFixture >> pure ())
    , test "C02" "product consumer restores actual stored types and modes" productRestoration
    , test "C03" "repeated unrestricted source and product reuse remain valid" unrestrictedProduct
    , test "C04" "empty unrestricted product remains valid" emptyProduct
    , test "C05" "restricted reuse and borrowed source cannot form a product" restrictedReuse
    , test "C06" "product elimination retains exact arity and collision errors" productBoundary
    , test "C07" "checked record view feeds the explicit consuming schema" checkedRecordConsumer
    , test "C08" "affine omission and linear responsibility remain distinct" fieldDispositions
    , test "C09" "borrow keeps exact selected type and unrelated loan state" borrowRoundTrip
    , test "C10" "active borrow excludes elimination and duplicate/ended loans" borrowPreventsElimination
    , test "C11" "actual data view yields only the selected payload" sumSelection
    , test "C12" "sum continuation accounts for the actual linear payload" sumContinuation
    , test "C13" "different alternatives may share a local field spelling" sumNamesAreLocal
    , test "R01" "duplicate record schema rejects at consuming boundaries" rejectDuplicateFields
    , test "R02" "complete constructor domain rejects later duplicate tags" rejectDuplicateTags
    , test "R03" "selected duplicate payload rejects before restoration" rejectDuplicatePayload
    ]
  putStrLn "COMPLETE aggregate_consumer_groups=16"
  unless (and results) exitFailure

test :: String -> String -> Result () -> IO Bool
test key label result = case result of
  Right () -> putStrLn ("PASS " <> key <> " " <> label) >> pure True
  Left detail -> putStrLn ("FAIL " <> key <> " " <> label <> " -- " <> detail) >> pure False
