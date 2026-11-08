{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01: real parsed flat product type/mode correspondence and actual
-- production Surface tuples, including a manually checked affine Core
-- argument. This does not claim that an arbitrary affine source type exists.
module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.DataMode (deriveRecordMode)
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Control (..), Mode (..), ProductElementType (..)
  , RefTerm (..), Ty (..) )
import Phil.Surface.Check.Engine (checkSurfaceComponent)
import Phil.Surface.Check.Support (emptySurfaceState, shapeForType, syntheticSpan)
import Phil.Surface.Check.Types
  ( InitialBinding (..), RejectionClass (..), SurfaceCheckError (..)
  , SurfaceCheckResult (..), SurfaceEnvironment (..)
  , emptySurfaceEnvironment )
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedTypeMode)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..), GrammarV1FunctionDecl (..)
  , GrammarV1TopLevelDecl (..), GrammarV1SourceFile (..)
  , parseGrammarV1StructuralSource )
import Phil.Surface.Syntax
  ( Block (..), Component (..), Located (..), Statement (..)
  , SurfaceExpression (..) )
import System.Exit (exitFailure)

type Elem = ProductElementType

bytes :: Integer -> Ty
bytes n = TyBytes (RefNat n)

element :: Mode -> Ty -> Elem
element = ProductElementType

assert :: Bool -> String -> Either String ()
assert ok why = if ok then Right () else Left why

-- Parse actual Grammar-v1, then use the production type/mode checker;
-- no synthetic product AST is supplied to the checker.
sourceProduct :: Text -> Either String (Maybe (CheckedTypeMode, Int))
sourceProduct signature = do
  let source = "fn product() -> " <> signature <>
        " satisfies C { return unit; }"
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "fsem-flat-products" source)
  resultType <- case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1FunctionDeclaration decl ->
        maybe (Left "source result type missing") Right
          (grammarV1FunctionResultType decl)
      _ -> Left "source is not a function declaration"
    _ -> Left "source did not parse as one declaration"
  case grammarV1CheckedTypeMode
    emptyStaticContext emptySurfaceState (locatedValue resultType) of
    Nothing -> Right Nothing
    Just (Left err) -> Left ("unexpected focusing error: " <> show err)
    Just (Right (checked, steps)) ->
      Right (Just (checked, length steps))

checkParsedProduct :: Text -> [Elem] -> Either String ()
checkParsedProduct input expected = do
  actual <- sourceProduct input
  assert (actual == Just
    ( CheckedTypeMode (TyProduct expected) (deriveRecordMode
        (map productElementMode expected)), 0))
    ("wrong source product, mode or element order: " <> show actual)

checkOutsideFragment :: Text -> Either String ()
checkOutsideFragment source = do
  actual <- sourceProduct source
  assert (actual == Nothing)
    ("unsupported source product became accepted: " <> show actual)

-- Check the production return path with a runtime tuple, including
-- affine members which are supplied as an already-checked Core binding
-- rather than inferred from a nonexistent source type.
checkRuntime :: [(Text, Mode, Ty)] -> [Text] -> [Elem] -> Either String ()
checkRuntime inputs names expected = do
  let bindings = Map.fromList
        [ (name, InitialBinding mode ty (shapeForType ty))
        | (name, mode, ty) <- inputs ]
      environment = (emptySurfaceEnvironment emptyStaticContext)
        { surfaceInitialBindings = bindings
        , surfaceExpectedProductReturn = Just expected
        }
      bare = environment { surfaceExpectedProductReturn = Nothing }
      returnExpr = Located syntheticSpan
        (TupleExpression
          [ Located syntheticSpan (VariableExpression n) | n <- names ])
      component = Located syntheticSpan (Component
        { componentName = "flat-product"
        , componentParameters = []
        , componentProvides = Nothing
        , componentBody = Located syntheticSpan
            (Block [Located syntheticSpan (ReturnStatement returnExpr)])
        })
      exact = SurfaceCheckResult "flat-product" [Return (TyProduct expected)]
      legacy = SurfaceCheckResult "flat-product"
        [Return (TyOpaque ("Tuple[" <> Text.pack (show (length names)) <> "]"))]
  assert (checkSurfaceComponent environment component == Right exact)
    "actual flat tuple failed product return verification"
  assert (checkSurfaceComponent bare component == Right legacy)
    "unconfigured tuple behavior changed"
  let rejects expectedWrong = case checkSurfaceComponent
        (environment { surfaceExpectedProductReturn = Just expectedWrong })
        component of
        Left err -> assert
          (surfaceErrorClass err == TypeMismatch &&
           surfaceErrorDetail err ==
            "returned tuple elements do not match the checked product contract")
          ("wrong error on forged product " <> show err)
        Right value -> Left ("forged product passed: " <> show value)
  rejects (reverse expected)
  rejects (drop 1 expected)
  rejects (expected ++ [element Unrestricted TyBool])
  case expected of
    [] -> Left "empty product test"
    first : others ->
      rejects (first { productElementMode =
        if productElementMode first == Linear then Unrestricted else Linear } : others)

checkDuplicateLinear :: Either String ()
checkDuplicateLinear = do
  let ty = bytes 8
      environment = (emptySurfaceEnvironment emptyStaticContext)
        { surfaceInitialBindings = Map.singleton "owned"
            (InitialBinding Linear ty (shapeForType ty))
        , surfaceExpectedProductReturn =
            Just [element Linear ty, element Linear ty]
        }
      expr = Located syntheticSpan
        (TupleExpression [variable, variable])
      variable = Located syntheticSpan (VariableExpression "owned")
      component = Located syntheticSpan (Component
        { componentName = "duplicate-linear-owner"
        , componentParameters = []
        , componentProvides = Nothing
        , componentBody = Located syntheticSpan
            (Block [Located syntheticSpan (ReturnStatement expr)])
        })
  case checkSurfaceComponent environment component of
    Left err -> assert (surfaceErrorClass err == StructuralUse)
      "duplicate restricted source did not reject at its second use"
    Right value -> Left ("linear owner duplicated: " <> show value)

main :: IO ()
main = do
  let unrestricted = [element Unrestricted TyUnit,
        element Unrestricted TyBool, element Unrestricted (TyUInt 32)]
      mixed = unrestricted ++ [element Linear (bytes 8)]
      differentlySized =
        [element Linear (bytes 8), element Unrestricted TyBool,
         element Linear (bytes 9)]
      runtimeMixed =
        [("unit", Unrestricted, TyUnit),
         ("flag", Unrestricted, TyBool),
         ("quantity", Unrestricted, TyUInt 32),
         ("owner", Linear, bytes 8)]
      runtimeAffine =
        [("one", Affine, TyOpaque "AffineToken"),
         ("two", Unrestricted, TyBool),
         ("three", Linear, bytes 9)]
      affineContract =
        [ element Affine (TyOpaque "AffineToken"),
          element Unrestricted TyBool,
          element Linear (bytes 9) ]
      result = do
        checkParsedProduct "(Unit, Bool, U32)" unrestricted
        checkParsedProduct "(Unit, Bool, U32, Bytes[8])" mixed
        checkParsedProduct "(Bytes[8], Bool, Bytes[9])" differentlySized
        checkParsedProduct "(Bytes[8], Bytes[9])"
          [element Linear (bytes 8), element Linear (bytes 9)]
        checkOutsideFragment "(Unit, (Bool, Bytes[8]))"
        checkOutsideFragment "(Bytes[8], NotChecked)"
        checkOutsideFragment "(Bytes[8], Proof[true])"
        checkRuntime runtimeMixed ["unit", "flag", "quantity", "owner"] mixed
        checkRuntime runtimeAffine ["one", "two", "three"] affineContract
        checkDuplicateLinear
  case result of
    Right () ->
      putStrLn "PASS: flat products, mixed unrestricted/linear source and affine Core modes"
    Left err ->
      putStrLn ("FAIL: " <> err) >> exitFailure
