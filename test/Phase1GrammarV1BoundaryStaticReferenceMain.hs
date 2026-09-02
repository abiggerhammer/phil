{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.BoundaryDirection (BoundaryDirection (..))
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
  , syntheticSpan
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceShape (..)
  , SurfaceState
  )
import Phil.Surface.GrammarV1.BoundaryDirection
  ( grammarV1BoundaryDirection
  )
import Phil.Surface.GrammarV1.BoundaryFailureTypes
  ( grammarV1BoundaryFailureTypes
  )
import Phil.Surface.GrammarV1.BoundaryPropositions
  ( grammarV1BoundaryCorrespondences
  , grammarV1BoundaryLaws
  )
import Phil.Surface.GrammarV1.BoundaryValueType
  ( grammarV1BoundaryValueType
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ testIO "SURF-002 specialized static references survive boundary items"
        expectSpecializedBoundaryFixture
    , testIO "SURF-003 unclosed static argument still rejects"
        (expectFixtureReject "rejected/21-static-argument-unclosed.phil")
    , test "SURF-002 remaining boundary item forms preserve exact payloads"
        allBoundaryItemsPreserved
    , test "SURF-003 boundary item missing semicolon rejects"
        boundaryMissingSemicolonRejects
    , test "SURF-008 Grammar-v1 boundary items route to exact Core direction"
        boundaryDirectionsRouteExactly
    , test "SURF-008 Grammar-v1 boundary value types inherit exact verified type meaning"
        boundaryValueTypesRouteExactly
    , test "SURF-008 Grammar-v1 boundary failure types preserve ordered verified type meaning"
        boundaryFailureTypesRouteExactly
    , test "SURF-008 Grammar-v1 boundary correspondence and law propositions preserve exact categories"
        boundaryPropositionItemsRouteExactly
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

testIO :: String -> IO (Either String ()) -> IO Bool
testIO label action = action >>= test label

expectSpecializedBoundaryFixture :: IO (Either String ())
expectSpecializedBoundaryFixture = do
  parsed <- parseFixture "accepted/26-specialized-static-reference.phil"
  pure $ do
    boundary <- singleBoundary =<< mapLeft show parsed
    assert (locatedValue (grammarV1BoundaryName boundary) == "Wire")
      "boundary name was not Wire"
    case grammarV1BoundaryGenericParams boundary of
      [Located _ param] -> do
        assert (locatedValue (grammarV1GenericParamName param) == "T")
          "generic parameter name was not T"
        assert (locatedValue (grammarV1GenericParamKind param) == GrammarV1TypeKind)
          "generic parameter kind was not Type"
      params -> Left ("expected one generic parameter, got " <> show params)
    assertNamedType "T" (grammarV1BoundaryType boundary)
    case grammarV1BoundaryItems boundary of
      [ Located _ (GrammarV1BoundaryReceive decoder)
        , Located _ (GrammarV1BoundarySend encoder)
        , Located _ (GrammarV1BoundaryCorrespondence proposition)
        ] -> do
          assertSpecializedReference "Decoder" "T" decoder
          assertSpecializedReference "Encoder" "T" encoder
          assertSpecializedClaim "Good" "T" proposition
      items -> Left ("unexpected boundary items " <> show items)

allBoundaryItemsPreserved :: Either String ()
allBoundaryItemsPreserved = do
  boundary <- singleBoundary =<< mapLeft show
    (parseGrammarV1StructuralSource "boundary-items" source)
  case grammarV1BoundaryItems boundary of
    [ Located _ GrammarV1BoundaryCanonical
      , Located _ (GrammarV1BoundaryFailure failureType)
      , Located _ (GrammarV1BoundaryLaw lawName proposition)
      ] -> do
        assert (locatedValue failureType == GrammarV1UnsignedType "U8")
          "failure type was not U8"
        assert (locatedValue lawName == "Identity") "law name was not Identity"
        assert (locatedValue proposition == GrammarV1TrueProposition)
          "law proposition was not true"
    items -> Left ("unexpected boundary item forms " <> show items)
  where
    source = Text.unlines
      [ "boundary B : U8 {"
      , "  canonical;"
      , "  failure U8;"
      , "  law Identity : true;"
      , "}"
      ]

boundaryMissingSemicolonRejects :: Either String ()
boundaryMissingSemicolonRejects =
  expectReject "boundary B : U8 { receive using Decoder[U8] }"

boundaryDirectionsRouteExactly :: Either String ()
boundaryDirectionsRouteExactly = do
  receiveOnly <- parseBoundary "receive-only"
    "boundary R : U8 { receive using Decoder[U8]; }"
  sendOnly <- parseBoundary "send-only"
    "boundary S : U8 { send using Encoder[U8]; }"
  bidirectional <- parseBoundary "bidirectional"
    "boundary B : U8 { receive using Decoder[U8]; send using Encoder[U8]; }"
  directionless <- parseBoundary "directionless"
    "boundary N : U8 { canonical; }"
  let actual = map grammarV1BoundaryDirection
        [receiveOnly, sendOnly, bidirectional, directionless]
      expected =
        [ Just ReceiveOnly
        , Just SendOnly
        , Just Bidirectional
        , Nothing
        ]
  assert (actual == expected) $
    "boundary direction routing changed explicit receive/send meaning or invented a default: "
      <> show actual

boundaryValueTypesRouteExactly :: Either String ()
boundaryValueTypesRouteExactly = do
  state <- bind "n" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) emptySurfaceState
  primitive <- parseBoundary "boundary-value-primitive"
    "boundary Word : U32 { canonical; }"
  contextualBytes <- parseBoundary "boundary-value-bytes"
    "boundary Packet : Bytes[n + 1] { canonical; }"
  proofType <- parseBoundary "boundary-value-proof"
    "boundary Evidence : Proof[n < 7] { canonical; }"
  focusedRefinement <- parseBoundary "boundary-value-refinement"
    "boundary Positive : {v : U8 | v > 0} { canonical; }"
  tupleType <- parseBoundary "boundary-value-tuple"
    "boundary Pair : (U32, Bool) { canonical; }"
  let actual = map (grammarV1BoundaryValueType state)
        [ primitive
        , contextualBytes
        , proofType
        , focusedRefinement
        , tupleType
        ]
      n = RefVar (Name "n")
      expected =
        [ Just (TyUInt 32)
        , Just (TyBytes (RefAdd n (RefNat 1)))
        , Just (TyProof (LessThan n (RefNat 7)))
        , Just
            (TyRefined
              (Name "v")
              (TyUInt 8)
              (LessThan (RefNat 0) (RefToNat (RefVar (Name "v")))))
        , Nothing
        ]
  assert (actual == expected) $
    "boundary value-type routing changed verified type meaning or admitted an unresolved type: "
      <> show actual

boundaryFailureTypesRouteExactly :: Either String ()
boundaryFailureTypesRouteExactly = do
  state <- bind "n" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) emptySurfaceState
  none <- parseBoundary "boundary-failure-none"
    "boundary None : U8 { canonical; }"
  single <- parseBoundary "boundary-failure-single"
    "boundary Single : U8 { failure U32; }"
  multiple <- parseBoundary "boundary-failure-multiple" $ Text.unlines
    [ "boundary Multiple : U8 {"
    , "  failure Bytes[n + 1];"
    , "  failure Proof[n < 7];"
    , "  failure {v : U8 | v > 0};"
    , "}"
    ]
  unresolved <- parseBoundary "boundary-failure-unresolved" $ Text.unlines
    [ "boundary Unresolved : U8 {"
    , "  failure U8;"
    , "  failure (U32, Bool);"
    , "}"
    ]
  let n = RefVar (Name "n")
      actual = map (grammarV1BoundaryFailureTypes state)
        [none, single, multiple, unresolved]
      expected =
        [ Just []
        , Just [TyUInt 32]
        , Just
            [ TyBytes (RefAdd n (RefNat 1))
            , TyProof (LessThan n (RefNat 7))
            , TyRefined
                (Name "v")
                (TyUInt 8)
                (LessThan (RefNat 0) (RefToNat (RefVar (Name "v"))))
            ]
        , Nothing
        ]
  assert (actual == expected) $
    "boundary failure-type routing changed source order, dropped a failure, or partially accepted an unresolved type: "
      <> show actual

boundaryPropositionItemsRouteExactly :: Either String ()
boundaryPropositionItemsRouteExactly = do
  state1 <- bind "n" Unrestricted (TyOpaqueSorted "NatIndex" SortNat) emptySurfaceState
  state <- bind "u" Unrestricted (TyUInt 32) state1
  none <- parseBoundary "boundary-propositions-none"
    "boundary None : U8 { canonical; }"
  rich <- parseBoundary "boundary-propositions-rich" $ Text.unlines
    [ "boundary Facts : U8 {"
    , "  correspondence n + 1 == 7;"
    , "  correspondence u < 7;"
    , "  law ReadyLaw : Ready(n + 1, true) and n < 7;"
    , "  law FocusedLaw : 7 < u;"
    , "}"
    ]
  unresolvedCorrespondence <- parseBoundary "boundary-propositions-bad-correspondence" $ Text.unlines
    [ "boundary BadCorrespondence : U8 {"
    , "  correspondence missing == n;"
    , "  law StillFine : true;"
    , "}"
    ]
  unresolvedLaw <- parseBoundary "boundary-propositions-bad-law" $ Text.unlines
    [ "boundary BadLaw : U8 {"
    , "  correspondence true;"
    , "  law Bad : Ready[U32](n);"
    , "}"
    ]
  let n = RefVar (Name "n")
      u = RefVar (Name "u")
      boundaries = [none, rich, unresolvedCorrespondence, unresolvedLaw]
      actualCorrespondences = map (grammarV1BoundaryCorrespondences state) boundaries
      actualLaws = map (grammarV1BoundaryLaws state) boundaries
      expectedCorrespondences =
        [ Just []
        , Just
            [ Equal (RefAdd n (RefNat 1)) (RefNat 7)
            , LessThan (RefToNat u) (RefNat 7)
            ]
        , Nothing
        , Just [Truth]
        ]
      expectedLaws =
        [ Just []
        , Just
            [ ( "ReadyLaw"
              , Conjunction
                  (Atom "Ready" [RefAdd n (RefNat 1), RefBool True])
                  (LessThan n (RefNat 7))
              )
            , ("FocusedLaw", LessThan (RefNat 7) (RefToNat u))
            ]
        , Just [("StillFine", Truth)]
        , Nothing
        ]
  assert (actualCorrespondences == expectedCorrespondences) $
    "boundary correspondence routing changed order/meaning or failed to reject an unresolved correspondence: "
      <> show actualCorrespondences
  assert (actualLaws == expectedLaws) $
    "boundary law routing changed names/order/meaning or failed to reject an unresolved law: "
      <> show actualLaws

bind :: Text.Text -> Mode -> Ty -> SurfaceState -> Either String SurfaceState
bind name mode ty state =
  mapLeft show $
    insertBindingMeta syntheticSpan name (BindingMeta mode ty PlainShape) state

parseBoundary :: Text.Text -> Text.Text -> Either String GrammarV1BoundaryDecl
parseBoundary label source =
  singleBoundary =<< mapLeft show (parseGrammarV1StructuralSource label source)

singleBoundary :: GrammarV1SourceFile -> Either String GrammarV1BoundaryDecl
singleBoundary sourceFile =
  case grammarV1TopLevelDecls sourceFile of
    [_, Located _ topLevel] -> extractBoundary topLevel
    [Located _ topLevel] -> extractBoundary topLevel
    declarations -> Left ("expected boundary declaration, got " <> show (length declarations) <> " top-level declarations")
  where
    extractBoundary topLevel = case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1BoundaryDeclaration boundary -> Right boundary
      other -> Left ("expected boundary declaration, got " <> show other)

assertNamedType :: Text.Text -> Located GrammarV1Type -> Either String ()
assertNamedType expected (Located _ ty) = case ty of
  GrammarV1NamedType reference ->
    assert
      (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expected])
      ("expected named type " <> Text.unpack expected)
  other -> Left ("expected named type, got " <> show other)

assertSpecializedReference
  :: Text.Text
  -> Text.Text
  -> Located GrammarV1StaticReference
  -> Either String ()
assertSpecializedReference expectedName expectedArgument (Located _ reference) = do
  assert
    (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expectedName])
    ("unexpected static reference name " <> show (grammarV1StaticReferenceName reference))
  case grammarV1StaticReferenceArguments reference of
    [GrammarV1StaticReferenceArgument argument] ->
      assert
        (grammarV1QualifiedNameParts (grammarV1StaticReferenceName argument) == [expectedArgument])
        ("unexpected static reference argument " <> show argument)
    arguments -> Left ("expected one static reference argument, got " <> show arguments)

assertSpecializedClaim
  :: Text.Text
  -> Text.Text
  -> Located GrammarV1Proposition
  -> Either String ()
assertSpecializedClaim expectedName expectedStaticArgument (Located _ proposition) =
  case proposition of
    GrammarV1ClaimApplicationProposition reference [Located _ (GrammarV1IntegerExpression "1")] -> do
      assert
        (grammarV1QualifiedNameParts (grammarV1StaticReferenceName reference) == [expectedName])
        "claim application name was not Good"
      case grammarV1StaticReferenceArguments reference of
        [GrammarV1StaticReferenceArgument argument] ->
          assert
            (grammarV1QualifiedNameParts (grammarV1StaticReferenceName argument) == [expectedStaticArgument])
            "claim static argument was not T"
        arguments -> Left ("unexpected claim static arguments " <> show arguments)
    other -> Left ("expected specialized claim application, got " <> show other)

expectReject :: Text.Text -> Either String ()
expectReject source = case parseGrammarV1StructuralSource "boundary-negative" source of
  Left _ -> Right ()
  Right value -> Left ("expected syntax rejection, parsed " <> show value)

expectFixtureReject :: FilePath -> IO (Either String ())
expectFixtureReject relativePath = do
  parsed <- parseFixture relativePath
  pure $ case parsed of
    Left _ -> Right ()
    Right value -> Left ("expected syntax rejection, parsed " <> show value)

parseFixture
  :: FilePath
  -> IO (Either GrammarV1ParseDiagnostic GrammarV1SourceFile)
parseFixture relativePath = do
  let path = "test/fixtures/phase1-surface/" <> relativePath
  source <- TextIO.readFile path
  pure (parseGrammarV1StructuralSource (Text.pack relativePath) source)

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
