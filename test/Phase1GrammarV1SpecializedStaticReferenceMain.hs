{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.Generic
  ( GenericApplicationIdentity (..)
  , GenericStaticParameterKey (..)
  , deriveGenericApplicationIdentity
  )
import Phil.Core.Generic.StaticActual
  ( CheckedGenericStaticActual (..)
  , GenericStaticKind (..)
  , GenericStaticKindError (..)
  , GenericStaticParameter (..)
  , GenericStaticReferenceCandidate (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , InterfaceRevision (..)
  , SemanticForm (..)
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.SpecializedStaticReference
  ( GrammarV1CheckedSpecializedStaticReference (..)
  , GrammarV1ResolvedDirectStaticArgument (..)
  , GrammarV1SpecializedStaticReferenceError (..)
  , grammarV1CheckedSpecializedStaticReference
  )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 specialized references preserve exact checked generic application identity"
        checkedSpecialization
    , test "SURF-008 specialized references keep name-shaped actuals reference-selected"
        nameShapedAuthorityBoundary
    , test "SURF-008 specialized references reject missing duplicate and wrong-kind direct evidence"
        directEvidenceFailures
    , test "SURF-008 specialized references preserve Core reference-resolution failures"
        referenceResolutionFailures
    , test "SURF-008 bare targets and nested specializations stay outside unsupported competence"
        competenceBoundaries
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

checkedSpecialization :: Either String ()
checkedSpecialization = do
  reference <- aliasReference "type T = pkg.Box[U32, Shared];"
  arguments <- exactlyTwoArguments reference
  let [typeArgument, providerArgument] = arguments
      typeKey = GenericStaticParameterKey "T"
      providerKey = GenericStaticParameterKey "P"
      parameters =
        [ GenericStaticParameter typeKey GenericTypeKind
        , GenericStaticParameter providerKey GenericProviderContractKind
        ]
      typeSemantics = SemanticAtom "type.U32.checked"
      providerSemantics = SemanticAtom "provider.Shared.checked"
      directEvidence =
        [ GrammarV1ResolvedDirectStaticArgument
            typeArgument
            GenericTypeKind
            typeSemantics
        ]
      references =
        [ GenericStaticReferenceCandidate
            "Shared"
            GenericProviderContractKind
            providerSemantics
        ]
      declarationKey = DeclarationKey "decl.pkg.Box"
      interfaceRevision = InterfaceRevision "iface.pkg.Box.v1"
  expectedIdentity <- mapLeft show $
    deriveGenericApplicationIdentity
      declarationKey
      interfaceRevision
      [ (typeKey, typeSemantics)
      , (providerKey, providerSemantics)
      ]
  let actual = grammarV1CheckedSpecializedStaticReference
        declarationKey interfaceRevision parameters directEvidence references reference
      expectedArguments =
        [ CheckedGenericStaticActual typeKey GenericTypeKind typeSemantics
        , CheckedGenericStaticActual providerKey GenericProviderContractKind providerSemantics
        ]
      expected = GrammarV1CheckedSpecializedStaticReference
        { checkedSpecializedStaticReferenceName = "pkg.Box"
        , checkedSpecializedStaticArguments = expectedArguments
        , checkedSpecializedStaticApplicationIdentity = expectedIdentity
        }
  assert (actual == Just (Right expected))
    ("checked specialization changed exact static application identity: " <> show actual)

nameShapedAuthorityBoundary :: Either String ()
nameShapedAuthorityBoundary = do
  reference <- aliasReference "type T = Box[U32, Shared];"
  [typeArgument, providerArgument] <- exactlyTwoArguments reference
  let parameters =
        [ GenericStaticParameter (GenericStaticParameterKey "T") GenericTypeKind
        , GenericStaticParameter (GenericStaticParameterKey "P") GenericProviderContractKind
        ]
      evidence =
        [ GrammarV1ResolvedDirectStaticArgument
            typeArgument GenericTypeKind (SemanticAtom "type.U32")
        , GrammarV1ResolvedDirectStaticArgument
            providerArgument GenericProviderContractKind (SemanticAtom "provider.forged")
        ]
      actual = grammarV1CheckedSpecializedStaticReference
        (DeclarationKey "decl.Box")
        (InterfaceRevision "iface.Box")
        parameters
        evidence
        [ GenericStaticReferenceCandidate
            "Shared" GenericProviderContractKind (SemanticAtom "provider.real")
        ]
        reference
  assert
    (actual == Just
      (Left (GrammarV1UnexpectedDirectEvidenceForBareReference providerArgument)))
    "bare name-shaped static argument accepted direct semantic replacement"

directEvidenceFailures :: Either String ()
directEvidenceFailures = do
  reference <- aliasReference "type T = Box[U32, Shared];"
  [typeArgument, _] <- exactlyTwoArguments reference
  let typeKey = GenericStaticParameterKey "T"
      providerKey = GenericStaticParameterKey "P"
      parameters =
        [ GenericStaticParameter typeKey GenericTypeKind
        , GenericStaticParameter providerKey GenericProviderContractKind
        ]
      providerCandidate = GenericStaticReferenceCandidate
        "Shared" GenericProviderContractKind (SemanticAtom "provider.Shared")
      check evidence = grammarV1CheckedSpecializedStaticReference
        (DeclarationKey "decl.Box")
        (InterfaceRevision "iface.Box")
        parameters evidence [providerCandidate] reference
      goodEvidence = GrammarV1ResolvedDirectStaticArgument
        typeArgument GenericTypeKind (SemanticAtom "type.U32")
      wrongKindEvidence = GrammarV1ResolvedDirectStaticArgument
        typeArgument GenericIndexKind (SemanticAtom "index.not-type")
  assert
    (check [] == Just
      (Left (GrammarV1MissingDirectStaticArgumentEvidence typeArgument)))
    "missing semantic evidence did not reject the direct static argument"
  assert
    (check [goodEvidence, goodEvidence] == Just
      (Left (GrammarV1DuplicateDirectStaticArgumentEvidence typeArgument)))
    "duplicate direct semantic evidence silently selected one value"
  assert
    (check [wrongKindEvidence] == Just
      (Left
        (GrammarV1SpecializedStaticKindError
          (GenericStaticDirectKindMismatch typeKey GenericTypeKind GenericIndexKind))))
    "wrong direct static kind did not remain a Core generic-kind rejection"
  let countMismatch = grammarV1CheckedSpecializedStaticReference
        (DeclarationKey "decl.Box")
        (InterfaceRevision "iface.Box")
        [GenericStaticParameter typeKey GenericTypeKind]
        [goodEvidence]
        [providerCandidate]
        reference
  assert
    (countMismatch == Just
      (Left
        (GrammarV1SpecializedStaticKindError
          (GenericStaticActualCountMismatch 1 2))))
    "parameter/actual count mismatch was not delegated exactly to Core"

referenceResolutionFailures :: Either String ()
referenceResolutionFailures = do
  reference <- aliasReference "type T = Box[U32, Shared];"
  [typeArgument, _] <- exactlyTwoArguments reference
  let typeKey = GenericStaticParameterKey "T"
      providerKey = GenericStaticParameterKey "P"
      parameters =
        [ GenericStaticParameter typeKey GenericTypeKind
        , GenericStaticParameter providerKey GenericProviderContractKind
        ]
      evidence =
        [ GrammarV1ResolvedDirectStaticArgument
            typeArgument GenericTypeKind (SemanticAtom "type.U32")
        ]
      check candidates = grammarV1CheckedSpecializedStaticReference
        (DeclarationKey "decl.Box")
        (InterfaceRevision "iface.Box")
        parameters evidence candidates reference
  assert
    (check [] == Just
      (Left
        (GrammarV1SpecializedStaticKindError
          (GenericStaticReferenceUnresolved
            providerKey GenericProviderContractKind "Shared"))))
    "missing name-shaped reference did not stay unresolved"
  assert
    (check
      [GenericStaticReferenceCandidate
        "Shared" GenericTypeKind (SemanticAtom "type.Shared")]
      == Just
        (Left
          (GrammarV1SpecializedStaticKindError
            (GenericStaticReferenceKindMismatch
              providerKey
              GenericProviderContractKind
              "Shared"
              (Set.singleton GenericTypeKind)))))
    "wrong-kind name-shaped reference was reinterpreted"
  let firstForm = SemanticAtom "provider.first"
      secondForm = SemanticAtom "provider.second"
  assert
    (check
      [ GenericStaticReferenceCandidate "Shared" GenericProviderContractKind firstForm
      , GenericStaticReferenceCandidate "Shared" GenericProviderContractKind secondForm
      ]
      == Just
        (Left
          (GrammarV1SpecializedStaticKindError
            (GenericStaticReferenceAmbiguous
              providerKey GenericProviderContractKind "Shared" [firstForm, secondForm]))))
    "ambiguous reference candidates silently selected one semantic form"

competenceBoundaries :: Either String ()
competenceBoundaries = do
  bare <- aliasReference "type T = Box;"
  nested <- aliasReference "type T = Outer[Inner[U32]];"
  assert
    (grammarV1CheckedSpecializedStaticReference
      (DeclarationKey "decl.Box")
      (InterfaceRevision "iface.Box")
      [] [] [] bare
      == Nothing)
    "bare static target bypassed the existing bare-reference authority"
  case grammarV1StaticReferenceArguments nested of
    [nestedArgument] -> do
      let actual = grammarV1CheckedSpecializedStaticReference
            (DeclarationKey "decl.Outer")
            (InterfaceRevision "iface.Outer")
            [GenericStaticParameter
              (GenericStaticParameterKey "X") GenericTypeKind]
            [] [] nested
      assert
        (actual == Just
          (Left (GrammarV1MissingDirectStaticArgumentEvidence nestedArgument)))
        "nested specialization was flattened or guessed without checked semantic evidence"
    arguments -> Left
      ("expected one nested specialized argument, got " <> show (length arguments))

aliasReference :: Text.Text -> Either String GrammarV1StaticReference
aliasReference source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "specialized-static-reference" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ topLevel] -> case locatedValue (grammarV1Declaration topLevel) of
      GrammarV1TypeAliasDeclaration alias ->
        case locatedValue (grammarV1TypeAliasTarget alias) of
          GrammarV1NamedType reference -> Right reference
          other -> Left ("expected named alias target, got " <> show other)
      other -> Left ("expected type alias declaration, got " <> show other)
    declarations -> Left
      ("expected one type alias declaration, got " <> show (length declarations))

exactlyTwoArguments
  :: GrammarV1StaticReference
  -> Either String [GrammarV1StaticArgument]
exactlyTwoArguments reference =
  case grammarV1StaticReferenceArguments reference of
    arguments@[_, _] -> Right arguments
    arguments -> Left ("expected two static arguments, got " <> show (length arguments))

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
