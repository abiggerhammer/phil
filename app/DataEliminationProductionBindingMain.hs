{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , emptyContext
  , insertBinding
  , useBinding
  )
import Phil.Core.DataBorrow
  ( DataBorrowError (..)
  , beginBorrowedAggregateField
  , endBorrowedAggregateField
  )
import Phil.Core.DataDestruction
  ( AggregateDisposition (..)
  , DataDestructionError (..)
  , FieldDisposition (..)
  , OwnedField (..)
  , checkAggregateDisposition
  , checkFieldDispositions
  , consumeAggregateFields
  )
import Phil.Core.Syntax (Mode (..), Name (Name), Ty (TyOpaque))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "DATA-ELIM production linear binding accepts" linearBindingAccepts
    , test "DATA-ELIM production linear omission keeps native diagnostic" linearOmissionRejects
    , test "DATA-ELIM production affine omission accepts" affineOmissionAccepts
    , test "DATA-ELIM production duplicate disposition keeps native diagnostic" duplicateDispositionRejects
    , test "DATA-ELIM whole aggregate disposition is certified" wholeAggregateAccepted
    , test "DATA-ELIM explicit typed remainder is certified" explicitRemainderAccepted
    , test "DATA-ELIM implicit partial remainder rejects" implicitRemainderRejects
    , test "DATA-ELIM consuming helper consumes aggregate and restores exact fields" consumingTransferAccepted
    , test "DATA-ELIM duplicate successor rejects through ResourceContext" duplicateSuccessorRejects
    , test "DATA-ELIM scoped borrow lifecycle is kernel-backed" borrowLifecycleAccepted
    , test "DATA-ELIM undeclared borrow retains native diagnostic" undeclaredBorrowRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

linearBindingAccepts :: Either String ()
linearBindingAccepts =
  mapLeft show $ checkFieldDispositions [payloadField] [(payloadName, FieldBound)]

linearOmissionRejects :: Either String ()
linearOmissionRejects =
  assert
    ( checkFieldDispositions [payloadField] [(payloadName, FieldOmitted)]
        == Left (MissingLinearFieldDisposition payloadName)
    )
    "linear omission did not retain MissingLinearFieldDisposition"

affineOmissionAccepts :: Either String ()
affineOmissionAccepts =
  mapLeft show $ checkFieldDispositions [affineField] [(affineName, FieldOmitted)]

duplicateDispositionRejects :: Either String ()
duplicateDispositionRejects =
  assert
    ( checkFieldDispositions
        [payloadField]
        [(payloadName, FieldBound), (payloadName, FieldBound)]
        == Left (DuplicateFieldDisposition payloadName)
    )
    "duplicate field disposition did not retain native diagnostic"

wholeAggregateAccepted :: Either String ()
wholeAggregateAccepted = mapLeft show $ checkAggregateDisposition WholeAggregateConsumed

explicitRemainderAccepted :: Either String ()
explicitRemainderAccepted =
  mapLeft show $ checkAggregateDisposition (ExplicitTypedRemainder remainderTy)

implicitRemainderRejects :: Either String ()
implicitRemainderRejects =
  assert
    (checkAggregateDisposition ImplicitPartialRemainder == Left ImplicitPartialRemainderRejected)
    "implicit partial remainder was not rejected"

consumingTransferAccepted :: Either String ()
consumingTransferAccepted = do
  initial <- mapLeft show $ insertBinding Linear aggregateName aggregateTy emptyContext
  after <- mapLeft show $
    consumeAggregateFields
      aggregateName
      [payloadField, metadataField]
      [(payloadName, FieldBound), (metadataName, FieldBound)]
      initial
  case useBinding aggregateName after of
    Left (UnknownBinding actual) ->
      assert (actual == aggregateName) "wrong aggregate binding reported missing"
    other -> Left ("aggregate remained usable after consuming elimination: " <> show other)
  (payloadMode, payloadType, afterPayload) <- mapLeft show $ useBinding payloadName after
  assert (payloadMode == Linear && payloadType == payloadTy)
    "linear successor was not restored exactly"
  case useBinding payloadName afterPayload of
    Left (UnknownBinding actual) ->
      assert (actual == payloadName) "wrong linear successor reported missing"
    other -> Left ("linear successor was reusable: " <> show other)
  (metadataMode1, metadataType1, afterMetadata) <- mapLeft show $ useBinding metadataName after
  (metadataMode2, metadataType2, _) <- mapLeft show $ useBinding metadataName afterMetadata
  assert
    ( metadataMode1 == Unrestricted
        && metadataMode2 == Unrestricted
        && metadataType1 == metadataTy
        && metadataType2 == metadataTy
    )
    "unrestricted successor was not restored exactly"

duplicateSuccessorRejects :: Either String ()
duplicateSuccessorRejects = do
  initial <- mapLeft show $ insertBinding Linear aggregateName aggregateTy emptyContext
  assert
    ( consumeAggregateFields
        aggregateName
        [payloadField, payloadField]
        [(payloadName, FieldBound)]
        initial
        == Left (DataDestructionContextError (DuplicateBinding payloadName))
    )
    "duplicate successor escaped native ResourceContext rejection"

borrowLifecycleAccepted :: Either String ()
borrowLifecycleAccepted = do
  initial <- mapLeft show $ insertBinding Linear aggregateName aggregateTy emptyContext
  (view, loaned) <- mapLeft show $
    beginBorrowedAggregateField aggregateName [payloadField, metadataField] payloadName initial
  assert (Map.lookup aggregateName (linearBindings loaned) == Just aggregateTy)
    "borrow moved aggregate ownership"
  assert (Set.member aggregateName (sharedLoans loaned))
    "borrow did not activate the aggregate loan"
  restored <- mapLeft show $ endBorrowedAggregateField view loaned
  assert (restored == initial)
    "ending the borrow did not restore the exact pre-loan context"

undeclaredBorrowRejects :: Either String ()
undeclaredBorrowRejects = do
  initial <- mapLeft show $ insertBinding Linear aggregateName aggregateTy emptyContext
  assert
    ( beginBorrowedAggregateField
        aggregateName
        [payloadField]
        (Name "missing")
        initial
        == Left (UnknownBorrowedAggregateField (Name "missing"))
    )
    "undeclared aggregate field borrow did not retain native diagnostic"

payloadField, metadataField, affineField :: OwnedField
payloadField = OwnedField payloadName Linear payloadTy
metadataField = OwnedField metadataName Unrestricted metadataTy
affineField = OwnedField affineName Affine affineTy

aggregateName, payloadName, metadataName, affineName :: Name
aggregateName = Name "packet"
payloadName = Name "payload"
metadataName = Name "tag"
affineName = Name "cache"

aggregateTy, payloadTy, metadataTy, affineTy, remainderTy :: Ty
aggregateTy = TyOpaque "Packet"
payloadTy = TyOpaque "OwnedBytes[4]"
metadataTy = TyOpaque "UInt[8]"
affineTy = TyOpaque "CacheHandle"
remainderTy = TyOpaque "PacketRemainder"

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
