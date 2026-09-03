{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing
  ( FocusStep (..)
  , FocusingError (..)
  )
import Phil.Core.NominalDataMode
  ( NominalModeError (..)
  , NominalRestrictionJustification (..)
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
import Phil.Surface.GrammarV1.DataVariants
  ( GrammarV1CheckedVariant (..)
  , GrammarV1CheckedVariantPayload (..)
  , GrammarV1VariantModeEvidence (..)
  , GrammarV1VariantPayloadModeEvidence (..)
  , grammarV1CheckedDataVariants
  , grammarV1DataModeFromCheckedVariants
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 closed data variants preserve payload shape and checked type semantics"
        checkedDataVariants
    , test "SURF-008 closed data mode derives conservatively across constructor payloads"
        dataModeDerivation
    , test "SURF-008 explicit data mode strengthening requires admitted nominal justification"
        dataModeStrengthening
    , test "SURF-008 explicit data mode weakening rejects through Core nominal semantics"
        dataModeWeakening
    , test "SURF-008 data mode evidence preserves exact variant and payload identity"
        dataModeEvidenceCorrespondence
    , test "SURF-008 generic and requirement-bearing data remain outside closed mode competence"
        openDataModeFormsReject
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

dataModeDerivation :: Either String ()
dataModeDerivation = do
  declaration <- parseData $ unlines
    [ "data Ownership ="
    , "    None"
    , "  | Lease(Resource)"
    , "  | Full(U8, Resource)"
    , "  ;"
    ]
  let evidence =
        [ variant "None" Nothing
        , variant "Lease" (Just (GrammarV1VariantTupleModeEvidence [Affine]))
        , variant "Full"
            (Just (GrammarV1VariantTupleModeEvidence [Unrestricted, Linear]))
        ]
  assert
    (grammarV1DataModeFromCheckedVariants evidence Nothing declaration ==
      Just (Right Linear))
    "omitted data mode did not derive the strongest mode across all constructor payloads"

dataModeStrengthening :: Either String ()
dataModeStrengthening = do
  declaration <- parseData
    "data Token mode affine = Token(U64);"
  let evidence =
        [variant "Token" (Just (GrammarV1VariantTupleModeEvidence [Unrestricted]))]
  assert
    ( grammarV1DataModeFromCheckedVariants evidence Nothing declaration
        == Just (Left (StrongerModeMissingJustification Unrestricted Affine))
    )
    "strict data-mode strengthening bypassed Core justification requirements"
  assert
    ( grammarV1DataModeFromCheckedVariants
        evidence
        (Just (AdmittedResourceObligation "nominal token lifecycle"))
        declaration
        == Just (Right Affine)
    )
    "admitted nominal resource obligation did not permit exact affine strengthening"
  assert
    ( grammarV1DataModeFromCheckedVariants
        evidence
        (Just (UnadmittedNominalRestriction "surface mode spelling is not evidence"))
        declaration
        == Just
          (Left
            (StrongerModeUnadmittedJustification
              "surface mode spelling is not evidence"))
    )
    "unadmitted nominal restriction was treated as data-mode strengthening evidence"

dataModeWeakening :: Either String ()
dataModeWeakening = do
  weakened <- parseData
    "data Bad mode unrestricted = Holds(Resource);"
  equal <- parseData
    "data Lease mode affine = Holds(Resource);"
  let linearEvidence =
        [variant "Holds" (Just (GrammarV1VariantTupleModeEvidence [Linear]))]
      affineEvidence =
        [variant "Holds" (Just (GrammarV1VariantTupleModeEvidence [Affine]))]
  assert
    ( grammarV1DataModeFromCheckedVariants linearEvidence Nothing weakened
        == Just (Left (DeclaredModeWeakensDerived Linear Unrestricted))
    )
    "explicit unrestricted data mode laundered a supplied linear payload mode"
  assert
    ( grammarV1DataModeFromCheckedVariants affineEvidence Nothing equal
        == Just (Right Affine)
    )
    "explicit data mode equal to the derived minimum spuriously required strengthening evidence"

dataModeEvidenceCorrespondence :: Either String ()
dataModeEvidenceCorrespondence = do
  shapes <- parseData $ unlines
    [ "data Shapes ="
    , "    None"
    , "  | EmptyTuple()"
    , "  | EmptyRecord{}"
    , "  | Pair(U8, Bool)"
    , "  | Named{left : U8, right : Bool,}"
    , "  ;"
    ]
  let exact =
        [ variant "None" Nothing
        , variant "EmptyTuple" (Just (GrammarV1VariantTupleModeEvidence []))
        , variant "EmptyRecord" (Just (GrammarV1VariantRecordModeEvidence []))
        , variant "Pair"
            (Just (GrammarV1VariantTupleModeEvidence [Unrestricted, Affine]))
        , variant "Named"
            (Just
              (GrammarV1VariantRecordModeEvidence
                [("left", Unrestricted), ("right", Linear)]))
        ]
  assert
    (grammarV1DataModeFromCheckedVariants exact Nothing shapes == Just (Right Linear))
    "exact data-mode evidence did not preserve variant/payload identity before aggregation"

  assertNothing shapes
    [ variant "None" (Just (GrammarV1VariantTupleModeEvidence []))
    , variant "EmptyTuple" (Just (GrammarV1VariantTupleModeEvidence []))
    , variant "EmptyRecord" (Just (GrammarV1VariantRecordModeEvidence []))
    , variant "Pair"
        (Just (GrammarV1VariantTupleModeEvidence [Unrestricted, Affine]))
    , variant "Named"
        (Just
          (GrammarV1VariantRecordModeEvidence
            [("left", Unrestricted), ("right", Linear)]))
    ]
    "nullary source variant accepted explicit-empty tuple mode evidence"

  assertNothing shapes
    [ variant "None" Nothing
    , variant "EmptyTuple" Nothing
    , variant "EmptyRecord" (Just (GrammarV1VariantRecordModeEvidence []))
    , variant "Pair"
        (Just (GrammarV1VariantTupleModeEvidence [Unrestricted, Affine]))
    , variant "Named"
        (Just
          (GrammarV1VariantRecordModeEvidence
            [("left", Unrestricted), ("right", Linear)]))
    ]
    "explicit-empty tuple source variant accepted nullary mode evidence"

  assertNothing shapes
    [ variant "None" Nothing
    , variant "EmptyTuple" (Just (GrammarV1VariantTupleModeEvidence []))
    , variant "EmptyRecord" (Just (GrammarV1VariantTupleModeEvidence []))
    , variant "Pair"
        (Just (GrammarV1VariantTupleModeEvidence [Unrestricted, Affine]))
    , variant "Named"
        (Just
          (GrammarV1VariantRecordModeEvidence
            [("left", Unrestricted), ("right", Linear)]))
    ]
    "explicit-empty record source variant accepted tuple mode evidence"

  assertNothing shapes
    [ variant "None" Nothing
    , variant "EmptyTuple" (Just (GrammarV1VariantTupleModeEvidence []))
    , variant "EmptyRecord" (Just (GrammarV1VariantRecordModeEvidence []))
    , variant "Pair"
        (Just (GrammarV1VariantTupleModeEvidence [Unrestricted]))
    , variant "Named"
        (Just
          (GrammarV1VariantRecordModeEvidence
            [("left", Unrestricted), ("right", Linear)]))
    ]
    "tuple payload accepted wrong-arity checked mode evidence"

  assertNothing shapes
    [ variant "None" Nothing
    , variant "EmptyTuple" (Just (GrammarV1VariantTupleModeEvidence []))
    , variant "EmptyRecord" (Just (GrammarV1VariantRecordModeEvidence []))
    , variant "Pair"
        (Just (GrammarV1VariantTupleModeEvidence [Unrestricted, Affine]))
    , variant "Named"
        (Just
          (GrammarV1VariantRecordModeEvidence
            [("right", Linear), ("left", Unrestricted)]))
    ]
    "record payload accepted reordered field-mode evidence"

  assertNothing shapes
    [ variant "EmptyTuple" (Just (GrammarV1VariantTupleModeEvidence []))
    , variant "None" Nothing
    , variant "EmptyRecord" (Just (GrammarV1VariantRecordModeEvidence []))
    , variant "Pair"
        (Just (GrammarV1VariantTupleModeEvidence [Unrestricted, Affine]))
    , variant "Named"
        (Just
          (GrammarV1VariantRecordModeEvidence
            [("left", Unrestricted), ("right", Linear)]))
    ]
    "data mode accepted evidence for reordered source variants"

openDataModeFormsReject :: Either String ()
openDataModeFormsReject = do
  generic <- parseData "data Box[T : Type] = Value(T);"
  constrained <- parseData
    "data Constrained requires { proposition true; } = Value(U8);"
  let evidence =
        [variant "Value" (Just (GrammarV1VariantTupleModeEvidence [Unrestricted]))]
  assert
    (grammarV1DataModeFromCheckedVariants evidence Nothing generic == Nothing)
    "generic data declaration bypassed the closed data-mode competence wall"
  assert
    (grammarV1DataModeFromCheckedVariants evidence Nothing constrained == Nothing)
    "requirement-bearing data declaration bypassed the closed data-mode competence wall"

variant
  :: Text.Text
  -> Maybe GrammarV1VariantPayloadModeEvidence
  -> GrammarV1VariantModeEvidence
variant = GrammarV1VariantModeEvidence

assertNothing
  :: GrammarV1DataDecl
  -> [GrammarV1VariantModeEvidence]
  -> String
  -> Either String ()
assertNothing declaration evidence detail =
  assert (grammarV1DataModeFromCheckedVariants evidence Nothing declaration == Nothing) detail

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
