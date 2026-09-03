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
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.TypeAlias
  ( grammarV1CheckedTypeAlias
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 closed type aliases route through checked type semantics"
        checkedClosedAliases
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

checkedClosedAliases :: Either String ()
checkedClosedAliases = do
  context <- mapLeft show $
    declareTransparentClaim
      "Positive"
      [(Name "x", SortUInt 8)]
      (LessThan
        (RefNat 0)
        (RefToNat (RefVar (Name "x"))))
      emptyStaticContext

  primitive <- onlyAlias "type Word = U32;"
  proofType <- onlyAlias "type Evidence = Proof[true];"
  refinement <- onlyAlias "type PositiveByte = {v : U8 | Positive(v)};"
  unknownClaim <- onlyAlias "type Unknown = Proof[Missing(1)];"
  tupleType <- onlyAlias "type Pair = (U8, Bool);"
  freeTerm <- onlyAlias "type Packet = Bytes[n];"
  generic <- onlyAlias "type Generic[T : Type] = U8;"

  assert
    (grammarV1CheckedTypeAlias context primitive ==
      Just (Right (("Word", TyUInt 32), [])))
    "primitive alias changed name/type or acquired a focusing trace"

  assert
    (grammarV1CheckedTypeAlias context proofType ==
      Just (Right (("Evidence", TyProof Truth), [])))
    "closed Proof alias did not preserve exact checked type meaning"

  case grammarV1CheckedTypeAlias context refinement of
    Just (Right ((name, TyRefined binder base predicate), steps)) -> do
      assert (name == "PositiveByte")
        "checked refinement alias changed declaration name"
      assert (binder == Name "v" && base == TyUInt 8)
        "checked refinement alias changed binder or base type"
      assert
        (predicate == LessThan
          (RefNat 0)
          (RefToNat (RefVar (Name "v"))))
        "checked refinement alias changed canonical predicate"
      assert (ExpandedTransparentClaim "Positive" `elem` steps)
        "checked refinement alias lost transparent-claim focusing trace"
    other -> Left
      ("checked refinement alias did not produce canonical TyRefined: " <> show other)

  assert
    (grammarV1CheckedTypeAlias context unknownClaim ==
      Just (Left (UnknownClaim "Missing")))
    "alias Core UnknownClaim collapsed into source non-competence"

  assert
    (grammarV1CheckedTypeAlias context tupleType == Nothing)
    "tuple alias bypassed current checked type competence"

  assert
    (grammarV1CheckedTypeAlias context freeTerm == Nothing)
    "top-level alias inherited an ambient/free term binding"

  assert
    (grammarV1CheckedTypeAlias context generic == Nothing)
    "generic alias bypassed the first closed declaration competence wall"

onlyAlias :: Text.Text -> Either String GrammarV1TypeAliasDecl
onlyAlias source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "checked-type-alias" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1TypeAliasDeclaration alias -> Right alias
      other -> Left ("expected type alias declaration, got " <> show other)
    declarations -> Left
      ("expected one type alias declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
