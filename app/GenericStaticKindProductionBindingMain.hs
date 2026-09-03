{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Generic (GenericStaticParameterKey (..))
import Phil.Core.Generic.StaticActual
import Phil.Core.Static (SemanticForm (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "production direct exact kind accepts" directExactKindAccepts
    , test "production direct wrong kind preserves diagnostic" directWrongKindRejects
    , test "production reference selects only expected kind" expectedKindSelectsReference
    , test "production wrong-kind reference preserves diagnostic" referenceWrongKindRejects
    , test "production unresolved reference preserves diagnostic" unresolvedReferenceRejects
    , test "production same-kind ambiguity preserves diagnostic" ambiguousReferenceRejects
    , test "production duplicate parameter gate remains native" duplicateParameterRejects
    , test "production telescope arity gate remains native" arityMismatchRejects
    , test "production checked result preserves exact parameter shape" checkedShapePreserved
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

directExactKindAccepts :: Either String ()
directExactKindAccepts = do
  result <- mapLeft show $ checkGenericStaticActuals
    [GenericStaticParameter (key "T") GenericTypeKind]
    [DirectGenericStaticActual GenericTypeKind (SemanticAtom "type.UInt")]
    []
  assert
    (map checkedGenericStaticSemanticForm result == [SemanticAtom "type.UInt"])
    "direct exact-kind actual lost its semantic form"

directWrongKindRejects :: Either String ()
directWrongKindRejects =
  case checkGenericStaticActuals
      [GenericStaticParameter (key "M") GenericMessageKind]
      [DirectGenericStaticActual GenericTypeKind (SemanticAtom "type.UInt")]
      [] of
    Left (GenericStaticDirectKindMismatch actualKey GenericMessageKind GenericTypeKind) ->
      assert (actualKey == key "M") "wrong direct-kind parameter in diagnostic"
    other -> Left ("wrong direct kind was not rejected natively: " <> show other)

expectedKindSelectsReference :: Either String ()
expectedKindSelectsReference = do
  let refs =
        [ candidate "shared" GenericCallableContractKind "callable.shared"
        , candidate "shared" GenericProviderContractKind "provider.shared"
        ]
  provider <- mapLeft show $ checkGenericStaticActuals
    [GenericStaticParameter (key "P") GenericProviderContractKind]
    [ReferencedGenericStaticActual "shared"]
    refs
  assert
    (map checkedGenericStaticSemanticForm provider == [SemanticAtom "provider.shared"])
    "reference selection did not stay at the declared provider kind"

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
        "wrong-kind reference diagnostic changed"
    other -> Left ("wrong-kind reference was not rejected natively: " <> show other)

unresolvedReferenceRejects :: Either String ()
unresolvedReferenceRejects =
  case checkGenericStaticActuals
      [GenericStaticParameter (key "A") GenericArchitectureDependencyKind]
      [ReferencedGenericStaticActual "missing"]
      [] of
    Left (GenericStaticReferenceUnresolved actualKey GenericArchitectureDependencyKind ref) ->
      assert (actualKey == key "A" && ref == "missing")
        "unresolved reference diagnostic changed"
    other -> Left ("unresolved reference was not rejected natively: " <> show other)

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
        "ambiguous reference diagnostic changed"
    other -> Left ("ambiguous reference was not rejected natively: " <> show other)

duplicateParameterRejects :: Either String ()
duplicateParameterRejects =
  case checkGenericStaticActuals
      [ GenericStaticParameter (key "T") GenericTypeKind
      , GenericStaticParameter (key "T") GenericIndexKind
      ]
      [ DirectGenericStaticActual GenericTypeKind (SemanticAtom "type.UInt")
      , DirectGenericStaticActual GenericIndexKind (SemanticAtom "index.1")
      ]
      [] of
    Left (DuplicateGenericStaticParameter actualKey) ->
      assert (actualKey == key "T") "duplicate parameter diagnostic changed"
    other -> Left ("duplicate static parameter was accepted: " <> show other)

arityMismatchRejects :: Either String ()
arityMismatchRejects =
  case checkGenericStaticActuals
      [ GenericStaticParameter (key "T") GenericTypeKind
      , GenericStaticParameter (key "N") GenericIndexKind
      ]
      [DirectGenericStaticActual GenericTypeKind (SemanticAtom "type.UInt")]
      [] of
    Left (GenericStaticActualCountMismatch 2 1) -> Right ()
    other -> Left ("static telescope arity mismatch changed: " <> show other)

checkedShapePreserved :: Either String ()
checkedShapePreserved = do
  let params =
        [ GenericStaticParameter (key "T") GenericTypeKind
        , GenericStaticParameter (key "P") GenericProviderContractKind
        ]
  checked <- mapLeft show $ checkGenericStaticActuals
    params
    [ DirectGenericStaticActual GenericTypeKind (SemanticAtom "type.UInt")
    , ReferencedGenericStaticActual "provider"
    ]
    [candidate "provider" GenericProviderContractKind "provider.store"]
  assert
    (map checkedGenericStaticParameterKey checked == map genericStaticParameterKey params)
    "checked parameter keys changed"
  assert
    (map checkedGenericStaticKind checked == map genericStaticParameterKind params)
    "checked static kinds changed"

candidate :: Text -> GenericStaticKind -> Text -> GenericStaticReferenceCandidate
candidate name kind form = GenericStaticReferenceCandidate
  { genericStaticReferenceName = name
  , genericStaticReferenceKind = kind
  , genericStaticReferenceSemanticForm = SemanticAtom form
  }

key :: Text -> GenericStaticParameterKey
key = GenericStaticParameterKey

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
