{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing
  ( FocusStep (..)
  , FocusingError (..)
  )
import Phil.Core.Static
  ( declareTransparentClaim
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Name (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.DataVariants
  ( GrammarV1CheckedVariant (..)
  , GrammarV1CheckedVariantPayload (..)
  , grammarV1CheckedDataVariants
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 closed data variants preserve payload shape and checked type semantics"
        checkedDataVariants
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

checkedDataVariants :: Either String ()
checkedDataVariants = do
  context <- mapLeft show $
    declareTransparentClaim
      "Positive"
      [(Name "x", SortUInt 8)]
      (LessThan
        (RefNat 0)
        (RefToNat (RefVar (Name "x"))))
      emptyStaticContext

  rich <- parseData $ unlines
    [ "data Choice mode affine ="
    , "    None"
    , "  | Empty()"
    , "  | EmptyRecord{}"
    , "  | Pair(U8, Bool)"
    , "  | Named{left : U32, refined : {v : U8 | Positive(v)},}"
    , "  ;"
    ]
  duplicate <- parseData "data Duplicate = Same | Same;"
  unknown <- parseData "data Unknown = Bad(Proof[Missing()]);"
  unsupported <- parseData "data Unsupported = Nested((U8, Bool));"
  freeDependency <- parseData "data Free = Packet(Bytes[n]);"
  generic <- parseData "data Box[T : Type] = Value(T);"
  constrained <- parseData "data Constrained requires { proposition true; } = Value(U8);"

  case grammarV1CheckedDataVariants context rich of
    Just
      (Right
        [ GrammarV1CheckedVariant "None" Nothing
        , GrammarV1CheckedVariant "Empty"
            (Just (GrammarV1CheckedVariantTuple []))
        , GrammarV1CheckedVariant "EmptyRecord"
            (Just (GrammarV1CheckedVariantRecord []))
        , GrammarV1CheckedVariant "Pair"
            (Just (GrammarV1CheckedVariantTuple
              [(TyUInt 8, []), (TyBool, [])]))
        , GrammarV1CheckedVariant "Named"
            (Just (GrammarV1CheckedVariantRecord
              [ ("left", TyUInt 32, [])
              , ("refined", TyRefined binder base predicate, steps)
              ]))
        ]) -> do
          assert (binder == Name "v" && base == TyUInt 8)
            "variant refinement changed binder or base type"
          assert
            (predicate == LessThan
              (RefNat 0)
              (RefToNat (RefVar (Name "v"))))
            "variant refinement changed canonical predicate"
          assert (ExpandedTransparentClaim "Positive" `elem` steps)
            "variant refinement lost transparent-claim focusing trace"
    other -> Left
      ("checked data variants changed source order, payload shape, type meaning, or trace: "
        <> show other)

  assert
    (grammarV1CheckedDataVariants context duplicate ==
      Just
        (Right
          [ GrammarV1CheckedVariant "Same" Nothing
          , GrammarV1CheckedVariant "Same" Nothing
          ]))
    "duplicate variant spelling was normalized or newly rejected by the projection"

  assert
    (grammarV1CheckedDataVariants context unknown ==
      Just (Left (UnknownClaim "Missing")))
    "variant payload Core UnknownClaim collapsed into source non-competence"

  assert
    (grammarV1CheckedDataVariants context unsupported == Nothing)
    "unsupported nested tuple type bypassed the checked type competence wall"

  assert
    (grammarV1CheckedDataVariants context freeDependency == Nothing)
    "top-level data payload inherited a free term binding"

  assert
    (grammarV1CheckedDataVariants context generic == Nothing)
    "generic data declaration entered the closed variant fragment"

  assert
    (grammarV1CheckedDataVariants context constrained == Nothing)
    "requirement-bearing data declaration entered the closed variant fragment"

parseData :: String -> Either String GrammarV1DataDecl
parseData source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "checked-data-variants" (Text.pack source)
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
