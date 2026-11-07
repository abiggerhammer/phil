{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Static
  ( DeclarationDescriptor (..)
  , DeclarationIdentity (..)
  , DeclarationKey (..)
  , DeclarationPresentation (..)
  , SemanticForm (..)
  , deriveDeclarationIdentity
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey (..)
  , grammarV1BinderCoreName
  , grammarV1DecodeBinderCoreName
  )
import System.Exit (exitFailure)

-- A TEST-ONLY, explicitly ordered, finite model catalog. Its ordinal is not
-- persisted or stable across changes to the catalog. Never use it to replace
-- production DeclarationKey identity, which is an exact Text value.
data RootCatalog = RootCatalog
  { rootsByModelId :: Map.Map Integer DeclarationKey
  , modelIdsByRoot :: Map.Map DeclarationKey Integer
  }

buildRootCatalog :: [DeclarationKey] -> Either String RootCatalog
buildRootCatalog roots = foldM add (RootCatalog Map.empty Map.empty)
  (zip [0 ..] roots)
  where
    add catalog (ordinal, root)
      | Map.member root (modelIdsByRoot catalog) =
          Left ("duplicate exact DeclarationKey in catalog: " <> show root)
      | otherwise = Right RootCatalog
          { rootsByModelId =
              Map.insert ordinal root (rootsByModelId catalog)
          , modelIdsByRoot =
              Map.insert root ordinal (modelIdsByRoot catalog)
          }

lookupModelId :: RootCatalog -> DeclarationKey -> Maybe Integer
lookupModelId catalog root = Map.lookup root (modelIdsByRoot catalog)

lookupConcreteRoot :: RootCatalog -> Integer -> Maybe DeclarationKey
lookupConcreteRoot catalog index = Map.lookup index (rootsByModelId catalog)

-- This observer connects the canonical Core.Name producer to the bounded
-- catalog representation. It does not rewrite names or synthesize a missing
-- root/ordinal. The ordinal remains production Int; the catalog id is Integer.
observeModelBinder
  :: RootCatalog
  -> GrammarV1BinderKey
  -> Maybe (Integer, Int)
observeModelBinder catalog key = do
  decoded <- grammarV1DecodeBinderCoreName (grammarV1BinderCoreName key)
  declarationId <- lookupModelId catalog
    (grammarV1BinderDeclarationRoot decoded)
  pure (declarationId, grammarV1BinderOrdinal decoded)

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False message = Left message

test :: String -> Either String () -> IO Bool
test label outcome = case outcome of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail)
    >> pure False

expectCatalog :: [DeclarationKey] -> Either String RootCatalog
expectCatalog = buildRootCatalog

-- Real production declaration identities retain key, interface revision and
-- definition revision as separate fields. We bridge only their key root.
descriptor :: Text -> Text -> Text -> DeclarationDescriptor
descriptor root presentation definition = DeclarationDescriptor
  { declarationPresentation =
      DeclarationPresentation presentation ["fsem", "bridge"]
  , declarationKey = DeclarationKey root
  , declarationInterfaceSemantics = SemanticAtom "interface-1"
  , declarationDefinitionSemantics = SemanticAtom definition
  }

realIdentities :: [DeclarationIdentity]
realIdentities =
  map deriveDeclarationIdentity
    [ descriptor "decl.A" "A" "body-A"
    , descriptor "decl:a:0" "A:0" "body-B"
    , descriptor "é:👩" "Unicode" "body-C"
    , descriptor "" "empty-root" "body-D"
    , descriptor "$phil.local:1:x:2" "looks-like-a-name" "body-E"
    ]

realRoots :: [DeclarationKey]
realRoots = map identityDeclarationKey realIdentities

catalogRoundtrip :: Either String ()
catalogRoundtrip = do
  catalog <- expectCatalog realRoots
  mapM_ (\(index, root) -> do
    assert (lookupModelId catalog root == Just index)
      ("wrong model index for root " <> show root)
    assert (lookupConcreteRoot catalog index == Just root)
      ("catalog root lookup did not roundtrip for " <> show root)
    ) (zip [0 ..] realRoots)
  assert (lookupConcreteRoot catalog (-1) == Nothing)
    "negative model id should not represent a catalog root"
  assert (lookupConcreteRoot catalog (toInteger (length realRoots)) == Nothing)
    "out-of-range model id was assigned a declaration"

distinctNamesPreserveModelIdentity :: Either String ()
distinctNamesPreserveModelIdentity = do
  catalog <- expectCatalog realRoots
  let keys =
        [ GrammarV1BinderKey root ordinal
        | root <- realRoots, ordinal <- [0, 1, 10, maxBound] ]
      observations = [ (grammarV1BinderCoreName key, observeModelBinder catalog key)
                     | key <- keys ]
  mapM_ (\key ->
    assert (observeModelBinder catalog key ==
      ((,) <$> lookupModelId catalog (grammarV1BinderDeclarationRoot key)
           <*> Just (grammarV1BinderOrdinal key)))
      ("producer/decoder/catalog disagree for " <> show key)) keys
  mapM_ (\(firstName, firstObserved) ->
    mapM_ (\(secondName, secondObserved) ->
      assert (firstName /= secondName || firstObserved == secondObserved)
        "one Core.Name represented two normalized catalog keys")
    observations) observations

revisionIsNotDeclarationRoot :: Either String ()
revisionIsNotDeclarationRoot = do
  let original = deriveDeclarationIdentity
        (descriptor "decl.A" "present-A" "original-body")
      revised = deriveDeclarationIdentity
        (descriptor "decl.A" "present-A" "revised-body")
      renamedPresentation = deriveDeclarationIdentity
        (descriptor "decl.A" "other-human-name" "original-body")
  catalog <- expectCatalog [identityDeclarationKey original]
  assert (identityDefinitionRevision original /= identityDefinitionRevision revised)
    "definition change did not change derived definition revision"
  assert (identityDeclarationKey original == identityDeclarationKey revised)
    "definition revision was incorrectly included in declaration root"
  assert (original == renamedPresentation)
    "presentation-only change altered exact production declaration identity"
  assert (lookupModelId catalog (identityDeclarationKey original) ==
    lookupModelId catalog (identityDeclarationKey revised))
    "same persisted root incorrectly received a different model identity"

duplicateRootsRejected :: Either String ()
duplicateRootsRejected = do
  let root = DeclarationKey "decl.same"
  case buildRootCatalog [root, root] of
    Left _ -> Right ()
    Right _ -> Left "duplicate roots silently assigned two model identities"

unrepresentedRootsStayUnrepresented :: Either String ()
unrepresentedRootsStayUnrepresented = do
  catalog <- expectCatalog [DeclarationKey "decl.A"]
  let unknown = DeclarationKey "decl.B"
      key = GrammarV1BinderKey unknown 5
  assert (lookupModelId catalog unknown == Nothing)
    "unlisted root was fabricated into a normalized identity"
  assert (observeModelBinder catalog key == Nothing)
    "unlisted source binder was fabricated into a normalized identity"
  assert (grammarV1DecodeBinderCoreName (grammarV1BinderCoreName key)
            == Just key)
    "missing catalog entry incorrectly affected real Core.Name resolution"

catalogOrderIsNotPersistentIdentity :: Either String ()
catalogOrderIsNotPersistentIdentity = do
  let first = DeclarationKey "decl.A"
      second = DeclarationKey "decl.B"
      originalKey = GrammarV1BinderKey first 3
  original <- expectCatalog [first, second]
  reversed <- expectCatalog [second, first]
  assert (lookupModelId original first == Just 0)
    "unexpected original catalog index"
  assert (lookupModelId reversed first == Just 1)
    "unexpected reordered catalog index"
  assert (observeModelBinder original originalKey /= 
          observeModelBinder reversed originalKey)
    "catalog reordering should change the TEST model index"
  assert (grammarV1BinderCoreName originalKey ==
          grammarV1BinderCoreName (GrammarV1BinderKey first 3))
    "catalog must not change production Core.Name identity"

main :: IO ()
main = do
  results <- sequence
    [ test "FSEM-01 explicit catalog roundtrips actual DeclarationKey roots"
        catalogRoundtrip
    , test "FSEM-01 production Core.Name -> bounded model key is exact"
        distinctNamesPreserveModelIdentity
    , test "FSEM-01 definition revisions and presentation are not binder roots"
        revisionIsNotDeclarationRoot
    , test "FSEM-01 duplicates reject, never alias distinct model ids"
        duplicateRootsRejected
    , test "FSEM-01 unknown roots remain outside the represented model"
        unrepresentedRootsStayUnrepresented
    , test "FSEM-01 model positions depend on ordered catalog"
        catalogOrderIsNotPersistentIdentity
    ]
  if and results then pure () else exitFailure
