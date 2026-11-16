{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
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
    , test "P8-H4 malformed direct and referenced native forms reject"
        malformedSelectedSemanticsReject
    , test "P8-H4 valid nested Unicode native forms remain accepted"
        validNestedSemanticsAccept
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

-- H3's actual native negative must now fail at the shared Core static-actual
-- checker, for both source-tied direct evidence and a resolved reference.
malformedSelectedSemanticsReject :: Either String ()
malformedSelectedSemanticsReject = do
  let u0 = SemanticUnordered Set.empty
      r0 = SemanticRecord Map.empty
      badSet = SemanticUnordered (Set.fromDistinctAscList [r0, u0])
      badMap = SemanticRecord (Map.fromDistinctAscList
        [("z", SemanticAtom "last"), ("a", SemanticAtom "first")])
      values =
        [ ("unordered", badSet)
        , ("nested ordered", SemanticOrdered [SemanticAtom "ok", badSet])
        , ("nested record", SemanticRecord (Map.singleton "child" badSet))
        , ("nested unordered", SemanticUnordered (Set.singleton badSet))
        , ("record", badMap)
        , ("record nested", SemanticOrdered [badMap])
        ]
      parameter = GenericStaticParameter (key "T") GenericTypeKind
      checkedDirect form = checkGenericStaticActuals
        [parameter] [DirectGenericStaticActual GenericTypeKind form] []
      checkedReference form = checkGenericStaticActuals
        [parameter] [ReferencedGenericStaticActual "actual"]
        [GenericStaticReferenceCandidate "actual" GenericTypeKind form]
      checkMalformed (label, form) = do
        checkResult (label <> " direct") (checkedDirect form)
        checkResult (label <> " referenced") (checkedReference form)
      checkResult label result = case result of
        Left (GenericStaticMalformedSemanticForm actualKey) ->
          assert (actualKey == key "T")
            ("malformed " <> label <> " diagnosed wrong parameter")
        other -> Left ("malformed " <> label <> " was admitted: " <> show other)
  mapM_ checkMalformed values
  -- A wrong-kind direct argument must retain its original error precedence.
  case checkGenericStaticActuals [parameter]
      [DirectGenericStaticActual GenericMessageKind badSet] [] of
    Left (GenericStaticDirectKindMismatch actualKey GenericTypeKind GenericMessageKind) ->
      assert (actualKey == key "T")
        "wrong-kind malformed direct argument changed kind diagnosis"
    other -> Left ("wrong-kind malformed direct argument changed error: " <> show other)

validNestedSemanticsAccept :: Either String ()
validNestedSemanticsAccept = do
  let u0 = SemanticUnordered Set.empty
      r0 = SemanticRecord Map.empty
      valid = SemanticRecord (Map.fromList
        [ ("unicode", SemanticAtom "é / e\\x0301 / 🙂")
        , ("nul", SemanticAtom "\\0")
        , ("nested", SemanticOrdered
            [SemanticUnordered (Set.fromList [r0, u0])])
        ])
      parameter = GenericStaticParameter (key "T") GenericTypeKind
      direct = checkGenericStaticActuals
        [parameter] [DirectGenericStaticActual GenericTypeKind valid] []
      referenced = checkGenericStaticActuals
        [parameter] [ReferencedGenericStaticActual "actual"]
        [GenericStaticReferenceCandidate "actual" GenericTypeKind valid]
      checkPreserved label result = case result of
        Right [actual] ->
          assert (checkedGenericStaticSemanticForm actual == valid)
            ("valid " <> label <> " was changed")
        other -> Left ("valid " <> label <> " was rejected: " <> show other)
  checkPreserved "direct" direct
  checkPreserved "referenced" referenced

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
