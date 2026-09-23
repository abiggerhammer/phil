{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import Data.Text (Text)
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (ResourceContext, emptyContext, insertBinding)
import Phil.Core.DataMode (formProductBinding)
import Phil.Core.Syntax
import Phil.Core.Value
import System.Exit (exitFailure)

data AuditCase = AuditCase String (Either String ())

main :: IO ()
main = do
  results <- mapM runCase cases
  unless (and results) exitFailure

runCase :: AuditCase -> IO Bool
runCase (AuditCase ident action) = case action of
  Right () -> putStrLn ("PASS: PHIL-AUD-PRODUCT-DEFEQ-001 " <> ident) >> pure True
  Left detail -> do
    putStrLn ("FAIL: PHIL-AUD-PRODUCT-DEFEQ-001 " <> ident <> " -- " <> detail)
    pure False

cases :: [AuditCase]
cases =
  [ AuditCase "P01 empty product is reflexive" $
      assertEqualTy (TyProduct []) (TyProduct [])
  , AuditCase "P02 unrestricted Bool product is reflexive" $
      assertEqualTy boolProduct boolProduct
  , AuditCase "P03 linear Bytes product is reflexive" $
      assertEqualTy bytesProduct bytesProduct
  , AuditCase "P04 nested products compare recursively" $
      assertEqualTy nestedProduct nestedProduct
  , AuditCase "P05 dependent endpoint elements remain alpha-equivalent" $
      assertEqualTy alphaProductLeft alphaProductRight
  , AuditCase "P06 product arity mismatch rejects" $
      assertNotEqualTy boolProduct (TyProduct [])
  , AuditCase "P07 product element mode mismatch rejects" $
      assertNotEqualTy
        (TyProduct [ProductElementType Unrestricted TyBool])
        (TyProduct [ProductElementType Linear TyBool])
  , AuditCase "P08 product element type mismatch rejects" $
      assertNotEqualTy
        (TyProduct [ProductElementType Unrestricted TyBool])
        (TyProduct [ProductElementType Unrestricted (TyUInt 16)])
  , AuditCase "P09 product element order is significant" $
      assertNotEqualTy
        (TyProduct
          [ ProductElementType Unrestricted TyBool
          , ProductElementType Unrestricted (TyUInt 16)
          ])
        (TyProduct
          [ ProductElementType Unrestricted (TyUInt 16)
          , ProductElementType Unrestricted TyBool
          ])
  , AuditCase "P10 public comparison reports exact products definitionally equal" $
      assert
        (compareTypes nestedProduct nestedProduct == DefinitionallyEqual)
        "public type comparison did not report product equality"
  , AuditCase "G01 formed unrestricted product checks against its stored type" $
      formedProductChecks
        [(Unrestricted, nm "flag", TyBool)]
        (nm "product.bool")
  , AuditCase "G02 formed linear Bytes product checks against its stored type" $
      formedProductChecks
        [(Linear, nm "payload", TyBytes (RefNat 4))]
        (nm "product.bytes")
  , AuditCase "G03 nested formed product checks against its stored type" $
      nestedFormedProductChecks
  ]

boolProduct :: Ty
boolProduct = TyProduct [ProductElementType Unrestricted TyBool]

bytesProduct :: Ty
bytesProduct = TyProduct [ProductElementType Linear (TyBytes (RefNat 4))]

nestedProduct :: Ty
nestedProduct = TyProduct
  [ ProductElementType Unrestricted boolProduct
  , ProductElementType Linear bytesProduct
  ]

alphaProductLeft, alphaProductRight :: Ty
alphaProductLeft = TyProduct
  [ ProductElementType Linear
      (TyEndpoint
        (Receive
          (nm "n")
          (TyUInt 16)
          (Send
            (nm "body")
            (TyBytes (RefToNat (RefVar (nm "n"))))
            (End (Outcome "ok")))))
  ]
alphaProductRight = TyProduct
  [ ProductElementType Linear
      (TyEndpoint
        (Receive
          (nm "length")
          (TyUInt 16)
          (Send
            (nm "message")
            (TyBytes (RefToNat (RefVar (nm "length"))))
            (End (Outcome "ok")))))
  ]

formedProductChecks
  :: [(Mode, Name, Ty)]
  -> Name
  -> Either String ()
formedProductChecks sources productName = do
  initial <- foldBindings sources emptyContext
  let sourceNames = [name | (_, name, _) <- sources]
  (_, formed) <- mapLeft show $ formProductBinding productName sourceNames initial
  productTy <- lookupExpectedProduct productName sources
  checkStoredProduct productName productTy formed

nestedFormedProductChecks :: Either String ()
nestedFormedProductChecks = do
  initial <- foldBindings
    [ (Unrestricted, nm "flag", TyBool)
    , (Unrestricted, nm "count", TyUInt 16)
    ]
    emptyContext
  (innerValue, withInner) <- mapLeft show $
    formProductBinding (nm "inner") [nm "flag", nm "count"] initial
  (_, withOuter) <- mapLeft show $
    formProductBinding (nm "outer") [nm "inner"] withInner
  let innerTy = TyProduct (productValueElements innerValue)
      outerTy = TyProduct [ProductElementType Unrestricted innerTy]
  checkStoredProduct (nm "outer") outerTy withOuter

lookupExpectedProduct :: Name -> [(Mode, Name, Ty)] -> Either String Ty
lookupExpectedProduct _ sources =
  Right (TyProduct [ProductElementType mode ty | (mode, _, ty) <- sources])

checkStoredProduct :: Name -> Ty -> ResourceContext -> Either String ()
checkStoredProduct productName expected context =
  case checkValue
      (VVar productName)
      expected
      (emptyCheckState { resourceContext = context }) of
    Right result -> do
      assert
        (valueResultType result == expected)
        "checkValue returned the wrong product type"
      assert
        (valueResultMode result == Just (productModeOf expected))
        "checkValue returned the wrong product mode"
    Left err -> Left ("exact formed product was rejected: " <> show err)

productModeOf :: Ty -> Mode
productModeOf ty = case ty of
  TyProduct elements -> foldr strongest Unrestricted (map productElementMode elements)
  _ -> Unrestricted
  where
    strongest Linear _ = Linear
    strongest _ Linear = Linear
    strongest Affine _ = Affine
    strongest _ Affine = Affine
    strongest Unrestricted Unrestricted = Unrestricted

foldBindings
  :: [(Mode, Name, Ty)]
  -> ResourceContext
  -> Either String ResourceContext
foldBindings bindings initial = foldl add (Right initial) bindings
  where
    add accumulated (mode, name, ty) = do
      context <- accumulated
      mapLeft show (insertBinding mode name ty context)

assertEqualTy :: Ty -> Ty -> Either String ()
assertEqualTy left right =
  assert (definitionallyEqualTy left right)
    ("types did not compare equal: " <> show left <> " / " <> show right)

assertNotEqualTy :: Ty -> Ty -> Either String ()
assertNotEqualTy left right =
  assert (not (definitionallyEqualTy left right))
    ("incompatible products compared equal: " <> show left <> " / " <> show right)

nm :: Text -> Name
nm = Name

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
