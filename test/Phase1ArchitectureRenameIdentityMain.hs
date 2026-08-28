{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Phil.Core.Static
  ( ArchitectureInstanceDescriptor (..)
  , ArchitectureInstanceIdentity
  , DeclarationDescriptor (..)
  , DeclarationIdentity (..)
  , DeclarationKey (..)
  , DeclarationPresentation (..)
  , InstanceKey (..)
  , SemanticForm (..)
  , deriveArchitectureInstanceIdentity
  , deriveDeclarationIdentity
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "ARCH-002 human rename preserves declaration identity" testHumanRename
    , test "ARCH-002 module move preserves declaration identity" testModuleMove
    , test "ARCH-002 combined rename/module move preserves declaration identity" testRenameAndMove
    , test "ARCH-002 presentation changes preserve downstream instance revision" testDownstreamInstance
    , test "ARCH-002 identity test is non-vacuous under semantic change" testSemanticChangeControl
    ]
  unless (and results) exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left message -> putStrLn ("FAIL: " <> label <> " -- " <> message) >> pure False

testHumanRename :: Either String ()
testHumanRename = do
  let original = identityFor (DeclarationPresentation "blob" ["Steve", "Storage"])
      renamed = identityFor (DeclarationPresentation "object_store" ["Steve", "Storage"])
  assertSameIdentity original renamed
    "human display-name change altered DeclarationKey or semantic revisions"

testModuleMove :: Either String ()
testModuleMove = do
  let original = identityFor (DeclarationPresentation "blob" ["Steve", "Storage"])
      moved = identityFor (DeclarationPresentation "blob" ["Library", "CAS", "Storage"])
  assertSameIdentity original moved
    "module-path move altered DeclarationKey or semantic revisions"

testRenameAndMove :: Either String ()
testRenameAndMove = do
  let original = identityFor (DeclarationPresentation "blob" ["Steve", "Storage"])
      changedPresentation = identityFor
        (DeclarationPresentation "persistent_object" ["Library", "CAS"])
  assertSameIdentity original changedPresentation
    "combined human rename/module move altered semantic identity"

testDownstreamInstance :: Either String ()
testDownstreamInstance = do
  let originalDeclaration = identityFor
        (DeclarationPresentation "blob" ["Steve", "Storage"])
      movedDeclaration = identityFor
        (DeclarationPresentation "object_store" ["Library", "CAS"])
      originalInstance = instanceFor originalDeclaration
      movedInstance = instanceFor movedDeclaration
  assert (originalInstance == movedInstance)
    "presentation-only declaration change perturbed downstream ArchitectureInstanceRevision"

testSemanticChangeControl :: Either String ()
testSemanticChangeControl = do
  let presentation = DeclarationPresentation "blob" ["Steve", "Storage"]
      original = deriveDeclarationIdentity (baseDeclaration presentation)
      changed = deriveDeclarationIdentity
        ((baseDeclaration presentation)
          { declarationDefinitionSemantics = SemanticRecord (Map.fromList
              [ ("algorithm", SemanticAtom "install-if-absent-v2")
              , ("cleanup", SemanticAtom "release-on-all-failures")
              ])
          })
  assert (identityDeclarationKey original == identityDeclarationKey changed)
    "semantic-change control unexpectedly changed stable DeclarationKey"
  assert (identityDefinitionRevision original /= identityDefinitionRevision changed)
    "identity-bearing definition change failed to revise DefinitionRevision"

identityFor :: DeclarationPresentation -> DeclarationIdentity
identityFor = deriveDeclarationIdentity . baseDeclaration

instanceFor :: DeclarationIdentity -> ArchitectureInstanceIdentity
instanceFor declarationIdentity = deriveArchitectureInstanceIdentity
  ArchitectureInstanceDescriptor
    { architectureInstanceKey = InstanceKey "steve.store"
    , architectureParentInstanceKey = Just (InstanceKey "steve.root")
    , architectureDeclarationIdentity = declarationIdentity
    , architectureStaticBindings = Map.singleton
        "capacity-policy" (SemanticAtom "bounded")
    }

baseDeclaration :: DeclarationPresentation -> DeclarationDescriptor
baseDeclaration presentation = DeclarationDescriptor
  { declarationPresentation = presentation
  , declarationKey = DeclarationKey "provider.blob"
  , declarationInterfaceSemantics = SemanticRecord (Map.fromList
      [ ("provider", SemanticAtom "BlobProvider")
      , ("authority", SemanticAtom "read-write")
      ])
  , declarationDefinitionSemantics = SemanticRecord (Map.fromList
      [ ("algorithm", SemanticAtom "install-if-absent-v1")
      , ("cleanup", SemanticAtom "release-on-all-failures")
      ])
  }

assertSameIdentity :: DeclarationIdentity -> DeclarationIdentity -> String -> Either String ()
assertSameIdentity left right message = do
  assert (identityDeclarationKey left == identityDeclarationKey right) message
  assert (identityInterfaceRevision left == identityInterfaceRevision right) message
  assert (identityDefinitionRevision left == identityDefinitionRevision right) message

assert :: Bool -> String -> Either String ()
assert condition message
  | condition = Right ()
  | otherwise = Left message
