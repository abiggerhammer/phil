{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing
  ( FocusStep (..)
  , FocusingError (..)
  )
import Phil.Core.Static
  ( declareOpaqueClaim
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
import Phil.Surface.Check.Support
  ( emptySurfaceState
  , insertBindingMeta
  , moveVariable
  , syntheticSpan
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceShape (..)
  , SurfaceState
  )
import Phil.Surface.GrammarV1.BoundProofType
  ( grammarV1BoundProofType
  )
import Phil.Surface.GrammarV1.CheckedProofType
  ( grammarV1CheckedProofType
  )
import Phil.Surface.GrammarV1.IntrinsicProofType
  ( grammarV1IntrinsicProofType
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 intrinsic Proof composition preserves exact Core meaning"
        intrinsicProofTypesPreserveMeaning
    , test "SURF-008 binding-aware Proof composition preserves richer exact Core meaning and poisons unresolved trees"
        boundProofTypesPreserveMeaning
    , test "SURF-008 checked Proof types inherit exact Core focusing semantics"
        checkedProofTypesUseCoreFocusing
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

intrinsicProofTypesPreserveMeaning :: Either String ()
intrinsicProofTypesPreserveMeaning = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-intrinsic-proof-composition" intrinsicSource
  sourceTypes <- mapM typeAliasTarget (grammarV1TopLevelDecls sourceFile)
  let actual = map grammarV1IntrinsicProofType sourceTypes
      expected =
        [ Just (TyProof (greaterThanCanonical 7 3))
        , Just (TyProof (Conjunction (Atom "Ready" [RefNat 1]) (Negation Falsehood)))
        , Just (TyProof (Disjunction (Equal (RefNat 1) (RefNat 1)) (Atom "Flag" [RefBool True])))
        , Nothing
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "intrinsic Proof composition changed a verified leaf/tree or accepted contextual specialization: " <> show actual
  where
    greaterThanCanonical left right = LessThan (RefNat right) (RefNat left)

boundProofTypesPreserveMeaning :: Either String ()
boundProofTypesPreserveMeaning = do
  state1 <- bind "n" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) emptySurfaceState
  state2 <- bind "m" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) state1
  state3 <- bind "flag" Unrestricted TyBool state2
  state4 <- bind "spent" Affine (TyOpaqueSorted "NatIndex" SortNat) state3
  (_, state) <- mapLeft show $
    moveVariable (Located syntheticSpan ()) "spent" state4
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-bound-proof-composition" boundSource
  sourceTypes <- mapM typeAliasTarget (grammarV1TopLevelDecls sourceFile)
  let actual = map (grammarV1BoundProofType state) sourceTypes
      expected =
        [ Just
            (TyProof
              (Conjunction
                Truth
                (LessThan (RefVar (Name "n")) (RefVar (Name "m")))))
        , Just
            (TyProof
              (Disjunction
                (Atom "Ready" [RefVar (Name "n"), RefBool True])
                Falsehood))
        , Just
            (TyProof
              ( Disjunction
                  (Conjunction
                    (Negation Falsehood)
                    (LessEqual (RefVar (Name "n")) (RefNat 7)))
                  (Atom "Ready" [RefVar (Name "flag"), RefVar (Name "n")])
              ))
        , Nothing
        , Just
            (TyProof
              (Conjunction
                Truth
                (Equal
                  (RefAdd (RefVar (Name "n")) (RefNat 1))
                  (RefVar (Name "m")))))
        , Nothing
        , Nothing
        , Nothing
        , Nothing
        ]
  assert (actual == expected) $
    "binding-aware Proof composition changed a verified tree or failed to poison an unresolved nested leaf: " <> show actual

checkedProofTypesUseCoreFocusing :: Either String ()
checkedProofTypesUseCoreFocusing = do
  context1 <- mapLeft show $
    declareTransparentClaim
      "Positive"
      [(Name "x", SortUInt 8)]
      (LessThan
        (RefNat 0)
        (RefToNat (RefVar (Name "x"))))
      emptyStaticContext
  context2 <- mapLeft show $
    declareOpaqueClaim "NeedsNat" [(Name "n", SortNat)] context1
  context3 <- mapLeft show $
    declareOpaqueClaim "Flagged" [(Name "flag", SortBool)] context2
  context <- mapLeft show $
    declareOpaqueClaim "NeedsUInt" [(Name "u", SortUInt 8)] context3
  state1 <- bind "u" Unrestricted (TyUInt 8) emptySurfaceState
  state2 <- bind "flag" Unrestricted TyBool state1
  state <- bind "n" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) state2
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "surf008-checked-proof-types" checkedSource
  sourceTypes <- mapM typeAliasTarget (grammarV1TopLevelDecls sourceFile)
  case sourceTypes of
    [ transparent
      , opaque
      , coercion
      , unknown
      , arity
      , sortMismatch
      , reverseCoercion
      , specialized
      , unresolved
      , notProof
      ] -> do
        let u = RefVar (Name "u")
            flag = RefVar (Name "flag")
        case grammarV1CheckedProofType context state transparent of
          Just (Right (TyProof canonical, steps)) -> do
            assert
              (canonical == LessThan (RefNat 0) (RefToNat u))
              ("transparent Proof claim expanded to the wrong proposition: " <> show canonical)
            assert
              (ExpandedTransparentClaim "Positive" `elem` steps)
              ("transparent Proof claim lost its Core expansion trace: " <> show steps)
          other -> Left ("transparent Proof claim did not check successfully: " <> show other)
        case grammarV1CheckedProofType context state opaque of
          Just (Right (TyProof canonical, _)) ->
            assert
              (canonical == Atom "Flagged" [flag])
              ("opaque Proof claim changed meaning: " <> show canonical)
          other -> Left ("opaque Proof claim did not check successfully: " <> show other)
        case grammarV1CheckedProofType context state coercion of
          Just (Right (TyProof canonical, steps)) -> do
            assert
              (canonical == Atom "NeedsNat" [RefToNat u])
              ("checked Proof did not preserve Core UInt-to-Nat coercion: " <> show canonical)
            assert
              (InsertedUIntToNat u `elem` steps)
              ("checked Proof lost the Core UInt-to-Nat focusing trace: " <> show steps)
          other -> Left ("coercing Proof claim did not check successfully: " <> show other)
        case grammarV1CheckedProofType context state unknown of
          Just (Left (UnknownClaim "Missing")) -> Right ()
          other -> Left ("unknown Proof claim did not preserve Core rejection: " <> show other)
        case grammarV1CheckedProofType context state arity of
          Just (Left (ClaimArityMismatch "Flagged" 1 2)) -> Right ()
          other -> Left ("Proof claim arity mismatch did not preserve Core rejection: " <> show other)
        case grammarV1CheckedProofType context state sortMismatch of
          Just (Left (ClaimArgumentSortMismatch "Flagged" 0 SortBool (SortUInt 8))) -> Right ()
          other -> Left ("Proof claim sort mismatch did not preserve Core rejection: " <> show other)
        case grammarV1CheckedProofType context state reverseCoercion of
          Just (Left (ClaimArgumentSortMismatch "NeedsUInt" 0 (SortUInt 8) SortNat)) -> Right ()
          other -> Left ("Proof Nat-to-UInt mismatch acquired an invented coercion: " <> show other)
        assert
          (grammarV1CheckedProofType context state specialized == Nothing)
          "specialized Proof claim reached Core focusing despite structural non-competence"
        assert
          (grammarV1CheckedProofType context state unresolved == Nothing)
          "unresolved Proof argument reached Core focusing despite structural non-competence"
        assert
          (grammarV1CheckedProofType context state notProof == Nothing)
          "non-Proof type entered checked Proof routing"
    other -> Left
      ("expected ten checked Proof type cases, got " <> show (length other))

bind :: Text.Text -> Mode -> Ty -> SurfaceState -> Either String SurfaceState
bind name mode ty state =
  mapLeft show $
    insertBindingMeta syntheticSpan name (BindingMeta mode ty PlainShape) state

typeAliasTarget
  :: Located GrammarV1TopLevelDecl
  -> Either String GrammarV1Type
typeAliasTarget (Located _ topLevel) =
  case locatedValue (grammarV1Declaration topLevel) of
    GrammarV1TypeAliasDeclaration aliasDecl ->
      Right (locatedValue (grammarV1TypeAliasTarget aliasDecl))
    other -> Left ("expected type alias declaration, got " <> show other)

intrinsicSource :: Text.Text
intrinsicSource = Text.unlines
  [ "type RelationProof = Proof[7 > 3];"
  , "type ClaimProof = Proof[Ready(1) and not false];"
  , "type MixedProof = Proof[1 == 1 or Flag(true)];"
  , "type ContextProof = Proof[x == 0];"
  , "type SpecializedProof = Proof[Ready[U32](1)];"
  , "type NotProof = Bool;"
  ]

boundSource :: Text.Text
boundSource = Text.unlines
  [ "type BoundRelationProof = Proof[true and n < m];"
  , "type BoundClaimProof = Proof[Ready(n, true) or false];"
  , "type MixedBoundProof = Proof[not false and n <= 7 or Ready(flag, n)];"
  , "type UnknownProof = Proof[true and missing == n];"
  , "type ArithmeticProof = Proof[true and n + 1 == m];"
  , "type SpecializedProof = Proof[true and Ready[U32](n)];"
  , "type ConsumedProof = Proof[Ready(spent) or false];"
  , "type ProjectedProof = Proof[(n).field == n or true];"
  , "type NotProof = Bool;"
  ]

checkedSource :: Text.Text
checkedSource = Text.unlines
  [ "type Transparent = Proof[Positive(u)];"
  , "type Opaque = Proof[Flagged(flag)];"
  , "type Coercion = Proof[NeedsNat(u)];"
  , "type Unknown = Proof[Missing(u)];"
  , "type Arity = Proof[Flagged(flag, flag)];"
  , "type SortMismatch = Proof[Flagged(u)];"
  , "type ReverseCoercion = Proof[NeedsUInt(n)];"
  , "type Specialized = Proof[Positive[U8](u)];"
  , "type Unresolved = Proof[Positive(missing)];"
  , "type NotProof = Bool;"
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
