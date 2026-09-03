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
import Phil.Surface.GrammarV1.TypeAlias
  ( grammarV1CheckedTypeAlias
  , grammarV1CheckedTypeAliasMode
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 closed type aliases route through checked type semantics"
        checkedClosedAliases
    , test "SURF-008 transparent aliases inherit exact checked target modes"
        checkedClosedAliasModes
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

checkedClosedAliases :: Either String ()
checkedClosedAliases = do
  context <- positiveContext

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

checkedClosedAliasModes :: Either String ()
checkedClosedAliasModes = do
  context <- positiveContext

  primitive <- onlyAlias "type Word = U32;"
  renamed <- onlyAlias "type RenamedWord = U32;"
  bytesType <- onlyAlias "type Buffer = Bytes[7];"
  proofType <- onlyAlias "type Evidence = Proof[true];"
  refinement <- onlyAlias "type PositiveByte = {v : U8 | Positive(v)};"
  unknownClaim <- onlyAlias "type Unknown = Proof[Missing(1)];"
  frameType <- onlyAlias "type Packet = Frame[Hello];"
  validatedType <- onlyAlias "type Checked = Validated[Check, payload, evidence];"
  namedType <- onlyAlias "type External = pkg.Other;"
  freeTerm <- onlyAlias "type DynamicBuffer = Bytes[n];"
  generic <- onlyAlias "type Generic[T : Type] = U8;"

  let wordMode = CheckedTypeMode
        { checkedBindingType = TyUInt 32
        , checkedBindingMode = Unrestricted
        }
  assert
    (grammarV1CheckedTypeAliasMode context primitive ==
      Just (Right (("Word", wordMode), [])))
    "primitive transparent alias did not inherit unrestricted target mode"
  assert
    (grammarV1CheckedTypeAliasMode context renamed ==
      Just (Right (("RenamedWord", wordMode), [])))
    "changing only transparent alias display spelling changed target mode semantics"

  assert
    (grammarV1CheckedTypeAliasMode context bytesType ==
      Just
        (Right
          ( ( "Buffer"
            , CheckedTypeMode
                { checkedBindingType = TyBytes (RefNat 7)
                , checkedBindingMode = Linear
                }
            )
          , []
          )))
    "owned Bytes transparent alias did not inherit linear target mode"

  assert
    (grammarV1CheckedTypeAliasMode context proofType ==
      Just
        (Right
          ( ( "Evidence"
            , CheckedTypeMode
                { checkedBindingType = TyProof Truth
                , checkedBindingMode = Unrestricted
                }
            )
          , []
          )))
    "Proof transparent alias did not inherit unrestricted target mode"

  case grammarV1CheckedTypeAliasMode context refinement of
    Just (Right ((name, CheckedTypeMode ty mode), steps)) -> do
      assert (name == "PositiveByte")
        "mode-aware refinement alias changed declaration name"
      assert
        ( ty == TyRefined
            (Name "v")
            (TyUInt 8)
            (LessThan (RefNat 0) (RefToNat (RefVar (Name "v"))))
        )
        "mode-aware refinement alias changed checked target type"
      assert (mode == Unrestricted)
        "refinement alias failed to inherit unrestricted base mode"
      assert (ExpandedTransparentClaim "Positive" `elem` steps)
        "mode-aware refinement alias lost target focusing trace"
    other -> Left
      ("mode-aware refinement alias did not preserve checked target: " <> show other)

  assert
    (grammarV1CheckedTypeAliasMode context unknownClaim ==
      Just (Left (UnknownClaim "Missing")))
    "mode-aware alias collapsed target Core rejection into source non-competence"

  assert (grammarV1CheckedTypeAliasMode context frameType == Nothing)
    "Frame alias acquired a guessed structural mode from constructor spelling"
  assert (grammarV1CheckedTypeAliasMode context validatedType == Nothing)
    "Validated alias acquired a guessed structural mode from constructor spelling"
  assert (grammarV1CheckedTypeAliasMode context namedType == Nothing)
    "opaque named alias acquired a guessed structural mode without declaration authority"
  assert (grammarV1CheckedTypeAliasMode context freeTerm == Nothing)
    "mode-aware top-level alias inherited an ambient/free term binding"
  assert (grammarV1CheckedTypeAliasMode context generic == Nothing)
    "generic alias bypassed the closed alias-mode competence wall"

positiveContext :: Either String Phil.Core.Static.StaticContext
positiveContext = mapLeft show $
  declareTransparentClaim
    "Positive"
    [(Name "x", SortUInt 8)]
    (LessThan
      (RefNat 0)
      (RefToNat (RefVar (Name "x"))))
    emptyStaticContext

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
