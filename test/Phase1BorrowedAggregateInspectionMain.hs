{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , consumeLinear
  , emptyContext
  , ensureComplete
  , insertBinding
  )
import Phil.Core.DataBorrow
  ( BorrowedAggregateField (..)
  , DataBorrowError (..)
  , beginBorrowedAggregateField
  , endBorrowedAggregateField
  )
import Phil.Core.DataDestruction (OwnedField (..))
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Ty (..)
  )

main :: IO ()
main = do
  initial <- expectRight "insert aggregate owner" $
    insertBinding Linear aggregateOwner aggregateType emptyContext

  (view, loaned) <- expectRight "begin aggregate field observation" $
    beginBorrowedAggregateField aggregateOwner fields payloadField initial

  expect (borrowedAggregateOwner view == aggregateOwner)
    "DATA-006 view keeps exact aggregate owner"
  expect (borrowedAggregateField view == payloadField)
    "DATA-006 view keeps exact selected field"
  expect (borrowedAggregateFieldMode view == Linear)
    "DATA-006 view records original restricted field mode without creating an owner"
  expect (borrowedAggregateFieldType view == payloadType)
    "DATA-006 view keeps exact selected field type"
  expect (Map.lookup aggregateOwner (linearBindings loaned) == Just aggregateType)
    "DATA-006 scoped observation does not move aggregate ownership"
  expect
    (consumeLinear aggregateOwner loaned == Left (OwnerBorrowed aggregateOwner))
    "DATA-006 aggregate owner cannot move while shared observation is live"
  expect
    (ensureComplete loaned == Left (EscapingLoans (Set.singleton aggregateOwner)))
    "DATA-006 shared aggregate view cannot cross the lexical loan boundary"

  restored <- expectRight "end aggregate field observation" $
    endBorrowedAggregateField view loaned
  expect (Set.null (sharedLoans restored))
    "DATA-006 loan is dead after its lexical scope"
  expect (Map.lookup aggregateOwner (linearBindings restored) == Just aggregateType)
    "DATA-006 aggregate owner is available again after observation"

  (restoredType, consumed) <- expectRight "consume restored aggregate owner" $
    consumeLinear aggregateOwner restored
  expect (restoredType == aggregateType)
    "DATA-006 observation preserves exact aggregate type"
  expect (Map.notMember aggregateOwner (linearBindings consumed))
    "DATA-006 later consuming use still consumes the unique aggregate owner exactly once"

  expect
    (beginBorrowedAggregateField aggregateOwner fields (Name "missing") initial
      == Left (UnknownBorrowedAggregateField (Name "missing")))
    "DATA-006 rejects observation of an undeclared aggregate field"

  putStrLn "PASS: DATA-006 borrowed restricted aggregate inspection"

aggregateOwner :: Name
aggregateOwner = Name "packet"

payloadField :: Name
payloadField = Name "payload"

aggregateType :: Ty
aggregateType = TyOpaque "Packet"

payloadType :: Ty
payloadType = TyOpaque "OwnedPayload"

fields :: [OwnedField]
fields =
  [ OwnedField (Name "tag") Unrestricted TyBool
  , OwnedField payloadField Linear payloadType
  ]

expect :: Bool -> String -> IO ()
expect condition message
  | condition = pure ()
  | otherwise = fail message

expectRight :: Show e => String -> Either e a -> IO a
expectRight label result = case result of
  Left errorValue -> fail (label <> ": " <> show errorValue)
  Right value -> pure value
