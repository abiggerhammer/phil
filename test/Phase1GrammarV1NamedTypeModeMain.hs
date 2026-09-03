{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.CheckedBindingMode
  ( CheckedTypeMode (..)
  )
import Phil.Core.Focusing
  ( FocusingError (..)
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  , GenericStaticKind (..)
  )
import Phil.Core.NominalDataMode
  ( NominalModeError (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , InterfaceRevision (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Ty (..)
  )
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.CheckedType
  ( GrammarV1CheckedResolvedTypeMode (..)
  , GrammarV1CheckedTypeModeOrigin (..)
  , GrammarV1CheckedTypeModeResolutionError (..)
  , GrammarV1ResolvedNamedTypeMode (..)
  , grammarV1CheckedTypeModeWithNamedResolutions
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.ResolvedAggregateMode
  ( GrammarV1CheckedResolvedDataMode (..)
  , GrammarV1CheckedResolvedDataModeError (..)
  , GrammarV1CheckedResolvedRecordMode (..)
  , GrammarV1CheckedResolvedRecordModeError (..)
  , GrammarV1CheckedResolvedVariantMode (..)
  , GrammarV1CheckedResolvedVariantModePayload (..)
  , grammarV1CheckedClosedDataModeWithNamedResolutions
  , grammarV1CheckedClosedRecordModeWithNamedResolutions
  )
import Phil.Surface.GrammarV1.TypeAlias
  ( grammarV1CheckedTypeAliasModeWithNamedResolutions
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 named type mode resolution preserves exact stable semantic evidence"
        exactNamedResolution
    , test "SURF-008 named type mode resolution rejects unresolved and wrong-kind references"
        unresolvedAndWrongKind
    , test "SURF-008 named type mode resolution rejects ambiguous and type-mismatched evidence"
        ambiguousAndTypeMismatch
    , test "SURF-008 intrinsic and focusing behavior stays separate from named resolution"
        intrinsicAndFocusingSeparation
    , test "SURF-008 specialized and non-named unresolved types cannot borrow named mode evidence"
        unresolvedFormsStayClosed
    , test "SURF-008 exact named modes compose through aliases, records, and sums"
        namedModesComposeThroughDeclarations
    , test "SURF-008 aggregate named-mode failures preserve resolution and nominal layers"
        aggregateFailuresRemainDistinct
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactNamedResolution :: Either String ()
exactNamedResolution = do
  other <- aliasTarget "type T = Other;"
  qualified <- aliasTarget "type T = pkg.Other;"
  let otherResolved = resolution
        "Other" GenericTypeKind "decl-other" "iface-other" (TyOpaque "Other") Linear
      qualifiedResolved = resolution
        "pkg.Other" GenericTypeKind "decl-qualified" "iface-qualified"
        (TyOpaque "pkg.Other") Affine
      otherExpected = GrammarV1CheckedResolvedTypeMode
        { checkedResolvedTypeMode = CheckedTypeMode (TyOpaque "Other") Linear
        , checkedResolvedTypeModeOrigin = GrammarV1NamedTypeModeOrigin
            (ReferencedGenericStaticActual "Other")
            (DeclarationKey "decl-other")
            (InterfaceRevision "iface-other")
        }
      qualifiedExpected = GrammarV1CheckedResolvedTypeMode
        { checkedResolvedTypeMode = CheckedTypeMode (TyOpaque "pkg.Other") Affine
        , checkedResolvedTypeModeOrigin = GrammarV1NamedTypeModeOrigin
            (ReferencedGenericStaticActual "pkg.Other")
            (DeclarationKey "decl-qualified")
            (InterfaceRevision "iface-qualified")
        }
  assert
    (grammarV1CheckedTypeModeWithNamedResolutions
      emptyStaticContext emptySurfaceState [otherResolved, qualifiedResolved] other
      == Just (Right (otherExpected, [])))
    "bare named type did not preserve exact reference/declaration/interface/mode evidence"
  assert
    (grammarV1CheckedTypeModeWithNamedResolutions
      emptyStaticContext emptySurfaceState [otherResolved, qualifiedResolved] qualified
      == Just (Right (qualifiedExpected, [])))
    "qualified named type lost exact dotted reference or stable semantic identity"

unresolvedAndWrongKind :: Either String ()
unresolvedAndWrongKind = do
  other <- aliasTarget "type T = Other;"
  let reference = ReferencedGenericStaticActual "Other"
      wrongKind = resolution
        "Other" GenericProviderContractKind "decl-provider" "iface-provider"
        (TyOpaque "Other") Linear
  assert
    (grammarV1CheckedTypeModeWithNamedResolutions
      emptyStaticContext emptySurfaceState [] other
      == Just (Left (GrammarV1NamedTypeModeUnresolved reference)))
    "missing exact named resolution collapsed into source non-competence"
  assert
    (grammarV1CheckedTypeModeWithNamedResolutions
      emptyStaticContext emptySurfaceState [wrongKind] other
      == Just
        (Left
          (GrammarV1NamedTypeModeKindMismatch
            reference
            [GenericProviderContractKind])))
    "wrong-kind named resolution was retried or accepted as a Type"

ambiguousAndTypeMismatch :: Either String ()
ambiguousAndTypeMismatch = do
  other <- aliasTarget "type T = Other;"
  let reference = ReferencedGenericStaticActual "Other"
      leftResolution = resolution
        "Other" GenericTypeKind "decl-left" "iface-left" (TyOpaque "Other") Linear
      rightResolution = resolution
        "Other" GenericTypeKind "decl-right" "iface-right" (TyOpaque "Other") Affine
      mismatched = resolution
        "Other" GenericTypeKind "decl-other" "iface-other" (TyOpaque "Different") Linear
  assert
    (grammarV1CheckedTypeModeWithNamedResolutions
      emptyStaticContext emptySurfaceState [leftResolution, rightResolution] other
      == Just
        (Left
          (GrammarV1NamedTypeModeAmbiguous
            reference
            [DeclarationKey "decl-left", DeclarationKey "decl-right"])))
    "multiple Type-kind resolutions silently selected one declaration"
  assert
    (grammarV1CheckedTypeModeWithNamedResolutions
      emptyStaticContext emptySurfaceState [mismatched] other
      == Just
        (Left
          (GrammarV1NamedTypeModeCheckedTypeMismatch
            reference
            (TyOpaque "Other")
            (TyOpaque "Different"))))
    "resolved mode evidence for a different checked type was accepted"

intrinsicAndFocusingSeparation :: Either String ()
intrinsicAndFocusingSeparation = do
  word <- aliasTarget "type T = U32;"
  badProof <- aliasTarget "type T = Proof[Missing()];"
  let distracting = resolution
        "Other" GenericTypeKind "decl-other" "iface-other" (TyOpaque "Other") Linear
      intrinsicExpected = GrammarV1CheckedResolvedTypeMode
        { checkedResolvedTypeMode = CheckedTypeMode (TyUInt 32) Unrestricted
        , checkedResolvedTypeModeOrigin = GrammarV1IntrinsicTypeModeOrigin
        }
  assert
    (grammarV1CheckedTypeModeWithNamedResolutions
      emptyStaticContext emptySurfaceState [distracting] word
      == Just (Right (intrinsicExpected, [])))
    "intrinsic type mode became dependent on unrelated named-resolution evidence"
  assert
    (grammarV1CheckedTypeModeWithNamedResolutions
      emptyStaticContext emptySurfaceState [distracting] badProof
      == Just (Left (GrammarV1TypeModeFocusingError (UnknownClaim "Missing"))))
    "Core focusing rejection was collapsed into named-resolution failure or source non-competence"

unresolvedFormsStayClosed :: Either String ()
unresolvedFormsStayClosed = do
  specialized <- aliasTarget "type T = Other[U32];"
  frame <- aliasTarget "type T = Frame[Hello];"
  let otherResolved = resolution
        "Other" GenericTypeKind "decl-other" "iface-other" (TyOpaque "Other") Linear
      frameLooking = resolution
        "Hello" GenericTypeKind "decl-frame" "iface-frame" (TyOpaque "Hello") Linear
  assert
    (grammarV1CheckedTypeModeWithNamedResolutions
      emptyStaticContext emptySurfaceState [otherResolved] specialized
      == Nothing)
    "specialized named type bypassed generic static-instantiation competence"
  assert
    (grammarV1CheckedTypeModeWithNamedResolutions
      emptyStaticContext emptySurfaceState [frameLooking] frame
      == Nothing)
    "Frame type borrowed unrelated named-type mode evidence"

namedModesComposeThroughDeclarations :: Either String ()
namedModesComposeThroughDeclarations = do
  alias <- parseAlias "type Alias = Other;"
  record <- parseRecord "record Envelope { tag : U8, payload : Other }"
  dat <- parseData "data MaybeOther = None | Some(Other);"
  let resolved = resolution
        "Other" GenericTypeKind "decl-other" "iface-other" (TyOpaque "Other") Linear
      expectedOrigin = GrammarV1NamedTypeModeOrigin
        (ReferencedGenericStaticActual "Other")
        (DeclarationKey "decl-other")
        (InterfaceRevision "iface-other")
  case grammarV1CheckedTypeAliasModeWithNamedResolutions
      emptyStaticContext [resolved] alias of
    Just (Right (("Alias", checked), [])) -> do
      assert
        (checkedResolvedTypeMode checked == CheckedTypeMode (TyOpaque "Other") Linear)
        "transparent alias changed the resolved target type/mode"
      assert
        (checkedResolvedTypeModeOrigin checked == expectedOrigin)
        "transparent alias discarded stable named-type resolution provenance"
    other -> Left ("resolved alias mode composition changed: " <> show other)

  case grammarV1CheckedClosedRecordModeWithNamedResolutions
      emptyStaticContext [resolved] Nothing record of
    Just (Right checkedRecord) -> do
      assert (checkedResolvedRecordStructuralMode checkedRecord == Linear)
        "record did not derive linear mode from exact named field resolution"
      case checkedResolvedRecordModeFields checkedRecord of
        [ ("tag", tagMode, [])
          , ("payload", payloadMode, [])
          ] -> do
            assert
              (checkedResolvedTypeMode tagMode == CheckedTypeMode (TyUInt 8) Unrestricted)
              "record intrinsic field mode changed"
            assert
              (checkedResolvedTypeModeOrigin tagMode == GrammarV1IntrinsicTypeModeOrigin)
              "record intrinsic field acquired named provenance"
            assert
              (checkedResolvedTypeMode payloadMode == CheckedTypeMode (TyOpaque "Other") Linear)
              "record named field type/mode changed"
            assert
              (checkedResolvedTypeModeOrigin payloadMode == expectedOrigin)
              "record named field discarded stable resolution provenance"
        fields -> Left ("record field order/provenance changed: " <> show fields)
    other -> Left ("resolved record mode composition changed: " <> show other)

  case grammarV1CheckedClosedDataModeWithNamedResolutions
      emptyStaticContext [resolved] Nothing dat of
    Just (Right checkedData) -> do
      assert (checkedResolvedDataStructuralMode checkedData == Linear)
        "sum did not derive linear mode from exact named payload resolution"
      case checkedResolvedDataModeVariants checkedData of
        [ GrammarV1CheckedResolvedVariantMode "None" Nothing
          , GrammarV1CheckedResolvedVariantMode "Some"
              (Just (GrammarV1CheckedResolvedVariantModeTuple [(payloadMode, [])]))
          ] -> do
            assert
              (checkedResolvedTypeMode payloadMode == CheckedTypeMode (TyOpaque "Other") Linear)
              "sum named payload type/mode changed"
            assert
              (checkedResolvedTypeModeOrigin payloadMode == expectedOrigin)
              "sum named payload discarded stable resolution provenance"
        variants -> Left ("sum variant order/payload shape changed: " <> show variants)
    other -> Left ("resolved data mode composition changed: " <> show other)

aggregateFailuresRemainDistinct :: Either String ()
aggregateFailuresRemainDistinct = do
  record <- parseRecord "record Envelope { payload : Other }"
  weakenedRecord <- parseRecord
    "record Envelope mode unrestricted { payload : Other }"
  dat <- parseData "data MaybeOther = None | Some(Other);"
  weakenedData <- parseData
    "data MaybeOther mode unrestricted = None | Some(Other);"
  let reference = ReferencedGenericStaticActual "Other"
      resolved = resolution
        "Other" GenericTypeKind "decl-other" "iface-other" (TyOpaque "Other") Linear
  assert
    (grammarV1CheckedClosedRecordModeWithNamedResolutions
      emptyStaticContext [] Nothing record
      == Just
        (Left
          (GrammarV1ResolvedRecordModeTypeError
            (GrammarV1NamedTypeModeUnresolved reference))))
    "record missing-resolution failure collapsed into non-competence or nominal error"
  assert
    (grammarV1CheckedClosedRecordModeWithNamedResolutions
      emptyStaticContext [resolved] Nothing weakenedRecord
      == Just
        (Left
          (GrammarV1ResolvedRecordModeNominalError
            (DeclaredModeWeakensDerived Linear Unrestricted))))
    "record named mode bypassed Core no-weakening authority"
  assert
    (grammarV1CheckedClosedDataModeWithNamedResolutions
      emptyStaticContext [] Nothing dat
      == Just
        (Left
          (GrammarV1ResolvedDataModeTypeError
            (GrammarV1NamedTypeModeUnresolved reference))))
    "sum missing-resolution failure collapsed into non-competence or nominal error"
  assert
    (grammarV1CheckedClosedDataModeWithNamedResolutions
      emptyStaticContext [resolved] Nothing weakenedData
      == Just
        (Left
          (GrammarV1ResolvedDataModeNominalError
            (DeclaredModeWeakensDerived Linear Unrestricted))))
    "sum named mode bypassed Core no-weakening authority"

resolution
  :: Text.Text
  -> GenericStaticKind
  -> Text.Text
  -> Text.Text
  -> Ty
  -> Mode
  -> GrammarV1ResolvedNamedTypeMode
resolution reference kind declarationKey interfaceRevision ty mode =
  GrammarV1ResolvedNamedTypeMode
    { resolvedNamedTypeReference = ReferencedGenericStaticActual reference
    , resolvedNamedTypeKind = kind
    , resolvedNamedTypeDeclarationKey = DeclarationKey declarationKey
    , resolvedNamedTypeInterfaceRevision = InterfaceRevision interfaceRevision
    , resolvedNamedTypeCheckedMode = CheckedTypeMode ty mode
    }

aliasTarget :: Text.Text -> Either String GrammarV1Type
aliasTarget source = do
  alias <- parseAlias source
  Right (locatedValue (grammarV1TypeAliasTarget alias))

parseAlias :: Text.Text -> Either String GrammarV1TypeAliasDecl
parseAlias source = do
  declaration <- onlyDeclaration source
  case declaration of
    GrammarV1TypeAliasDeclaration alias -> Right alias
    other -> Left ("expected type alias declaration, got " <> show other)

parseRecord :: Text.Text -> Either String GrammarV1RecordDecl
parseRecord source = do
  declaration <- onlyDeclaration source
  case declaration of
    GrammarV1RecordDeclaration record -> Right record
    other -> Left ("expected record declaration, got " <> show other)

parseData :: Text.Text -> Either String GrammarV1DataDecl
parseData source = do
  declaration <- onlyDeclaration source
  case declaration of
    GrammarV1DataDeclaration dat -> Right dat
    other -> Left ("expected data declaration, got " <> show other)

onlyDeclaration :: Text.Text -> Either String GrammarV1Declaration
onlyDeclaration source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "named-type-mode" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> Right (locatedValue (grammarV1Declaration topLevel))
    declarations -> Left
      ("expected one declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
