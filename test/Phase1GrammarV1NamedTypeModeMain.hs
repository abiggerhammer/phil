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
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "named-type-mode" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1TypeAliasDeclaration alias ->
        Right (locatedValue (grammarV1TypeAliasTarget alias))
      other -> Left ("expected type alias declaration, got " <> show other)
    declarations -> Left
      ("expected one type alias declaration, got " <> show (length declarations))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
