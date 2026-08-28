{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.Generic (GenericStaticParameterKey (..))
import Phil.Core.Generic.StaticActual
import Phil.Core.Static (SemanticForm (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "GEN-013 exact static categories accept" exactCategoriesAccept
    , test "GEN-013 direct wrong-kind actual rejects" directWrongKindRejects
    , test "GEN-013 reference resolves only through expected kind" expectedKindSelectsReference
    , test "GEN-013 reference wrong kind does not fallback" referenceWrongKindRejects
    , test "GEN-013 unresolved reference rejects" unresolvedReferenceRejects
    , test "GEN-013 ambiguous same-kind reference rejects" ambiguousReferenceRejects
    , test "GEN-013 telescope arity mismatch rejects" arityMismatchRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactCategoriesAccept :: Either String ()
exactCategoriesAccept = do
  checked <- mapLeft show $ checkGenericStaticActuals parameters actuals references
  assert (map checkedGenericStaticParameterKey checked == map genericStaticParameterKey parameters)
    "checked static actuals changed telescope order/identity"
  assert (map checkedGenericStaticKind checked == map genericStaticParameterKind parameters)
    "checked static actuals changed declared kinds"
  assert (map checkedGenericStaticSemanticForm checked == expectedForms)
    "checked static actuals lost canonical semantic values"

expectedKindSelectsReference :: Either String ()
expectedKindSelectsReference = do
  let providerParam = GenericStaticParameter (key "P") GenericProviderContractKind
      callableParam = GenericStaticParameter (key "C") GenericCallableContractKind
      sharedRefs =
        [ candidate "shared" GenericCallableContractKind "callable.shared"
        , candidate "shared" GenericProviderContractKind "provider.shared"
        ]
  provider <- mapLeft show $ checkGenericStaticActuals
    [providerParam] [ReferencedGenericStaticActual "shared"] sharedRefs
  callable <- mapLeft show $ checkGenericStaticActuals
    [callableParam] [ReferencedGenericStaticActual "shared"] sharedRefs
  assert
    (map checkedGenericStaticSemanticForm provider == [SemanticAtom "provider.shared"])
    "provider reference was chosen by candidate order rather than expected kind"
  assert
    (map checkedGenericStaticSemanticForm callable == [SemanticAtom "callable.shared"])
    "callable reference was chosen by candidate order rather than expected kind"

directWrongKindRejects :: Either String ()
directWrongKindRejects =
  case checkGenericStaticActuals
      [GenericStaticParameter (key "M") GenericMessageKind]
      [DirectGenericStaticActual GenericTypeKind (SemanticAtom "type.UInt")]
      [] of
    Left (GenericStaticDirectKindMismatch actualKey GenericMessageKind GenericTypeKind) ->
      assert (actualKey == key "M") "wrong-kind diagnostic named wrong parameter"
    other -> Left ("wrong direct kind was accepted: " <> show other)

referenceWrongKindRejects :: Either String ()
referenceWrongKindRejects =
  case checkGenericStaticActuals
      [GenericStaticParameter (key "C") GenericCallableContractKind]
      [ReferencedGenericStaticActual "provider-only"]
      [candidate "provider-only" GenericProviderContractKind "provider.only"] of
    Left (GenericStaticReferenceKindMismatch actualKey GenericCallableContractKind ref kinds) ->
      assert
        ( actualKey == key "C"
          && ref == "provider-only"
          && kinds == Set.singleton GenericProviderContractKind )
        "reference kind-mismatch diagnostic lost exact category information"
    other -> Left ("wrong-kind reference was reinterpreted or accepted: " <> show other)

unresolvedReferenceRejects :: Either String ()
unresolvedReferenceRejects =
  case checkGenericStaticActuals
      [GenericStaticParameter (key "A") GenericArchitectureDependencyKind]
      [ReferencedGenericStaticActual "missing"]
      [] of
    Left (GenericStaticReferenceUnresolved actualKey GenericArchitectureDependencyKind ref) ->
      assert (actualKey == key "A" && ref == "missing")
        "unresolved-reference diagnostic lost parameter/reference identity"
    other -> Left ("unresolved static reference was accepted: " <> show other)

ambiguousReferenceRejects :: Either String ()
ambiguousReferenceRejects =
  case checkGenericStaticActuals
      [GenericStaticParameter (key "P") GenericProviderContractKind]
      [ReferencedGenericStaticActual "dup"]
      [ candidate "dup" GenericProviderContractKind "provider.one"
      , candidate "dup" GenericProviderContractKind "provider.two"
      ] of
    Left (GenericStaticReferenceAmbiguous actualKey GenericProviderContractKind ref forms) ->
      assert
        ( actualKey == key "P"
          && ref == "dup"
          && Set.fromList forms == Set.fromList
              [SemanticAtom "provider.one", SemanticAtom "provider.two"] )
        "ambiguous-reference diagnostic lost exact same-kind candidates"
    other -> Left ("ambiguous static reference was accepted: " <> show other)

arityMismatchRejects :: Either String ()
arityMismatchRejects =
  case checkGenericStaticActuals
      [ GenericStaticParameter (key "T") GenericTypeKind
      , GenericStaticParameter (key "N") GenericIndexKind
      ]
      [DirectGenericStaticActual GenericTypeKind (SemanticAtom "type.UInt")]
      [] of
    Left (GenericStaticActualCountMismatch 2 1) -> Right ()
    other -> Left ("generic telescope arity mismatch was accepted: " <> show other)

parameters :: [GenericStaticParameter]
parameters =
  [ GenericStaticParameter (key "T") GenericTypeKind
  , GenericStaticParameter (key "N") GenericIndexKind
  , GenericStaticParameter (key "S") GenericSessionKind
  , GenericStaticParameter (key "M") GenericMessageKind
  , GenericStaticParameter (key "E") GenericEffectsKind
  , GenericStaticParameter (key "P") GenericProviderContractKind
  , GenericStaticParameter (key "C") GenericCallableContractKind
  , GenericStaticParameter (key "B") GenericBoundaryContractKind
  , GenericStaticParameter (key "A") GenericArchitectureDependencyKind
  ]

actuals :: [GenericStaticActual]
actuals =
  [ DirectGenericStaticActual GenericTypeKind (SemanticAtom "type.UInt")
  , DirectGenericStaticActual GenericIndexKind (SemanticAtom "index.32")
  , DirectGenericStaticActual GenericSessionKind (SemanticAtom "session.echo")
  , ReferencedGenericStaticActual "message"
  , DirectGenericStaticActual GenericEffectsKind (SemanticAtom "effects.storage-read")
  , ReferencedGenericStaticActual "shared-contract"
  , ReferencedGenericStaticActual "shared-contract"
  , ReferencedGenericStaticActual "boundary"
  , ReferencedGenericStaticActual "architecture"
  ]

references :: [GenericStaticReferenceCandidate]
references =
  [ candidate "message" GenericMessageKind "message.bytes"
  , candidate "shared-contract" GenericCallableContractKind "callable.worker"
  , candidate "shared-contract" GenericProviderContractKind "provider.store"
  , candidate "boundary" GenericBoundaryContractKind "boundary.upload"
  , candidate "architecture" GenericArchitectureDependencyKind "architecture.worker"
  ]

expectedForms :: [SemanticForm]
expectedForms =
  [ SemanticAtom "type.UInt"
  , SemanticAtom "index.32"
  , SemanticAtom "session.echo"
  , SemanticAtom "message.bytes"
  , SemanticAtom "effects.storage-read"
  , SemanticAtom "provider.store"
  , SemanticAtom "callable.worker"
  , SemanticAtom "boundary.upload"
  , SemanticAtom "architecture.worker"
  ]

candidate :: String -> GenericStaticKind -> String -> GenericStaticReferenceCandidate
candidate name kind form = GenericStaticReferenceCandidate
  { genericStaticReferenceName = fromStringText name
  , genericStaticReferenceKind = kind
  , genericStaticReferenceSemanticForm = SemanticAtom (fromStringText form)
  }

key :: String -> GenericStaticParameterKey
key = GenericStaticParameterKey . fromStringText

fromStringText :: String -> Data.Text.Text
fromStringText = Data.Text.pack

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
