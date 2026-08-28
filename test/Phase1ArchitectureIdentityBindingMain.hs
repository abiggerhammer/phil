{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import Phil.Core.Static
  ( ArchitectureInstanceIdentity (..)
  , DeclarationIdentity (..)
  , DeclarationKey (..)
  , DefinitionRevision (..)
  , InstanceKey (..)
  , InstanceRevision (..)
  , InterfaceRevision (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "ARCH-ID binding exact declaration identity accepts" testExactDeclarationIdentity
    , test "ARCH-ID binding declaration-key difference rejects" testDeclarationKeyDifference
    , test "ARCH-ID binding interface-revision difference rejects" testInterfaceRevisionDifference
    , test "ARCH-ID binding definition-revision difference rejects" testDefinitionRevisionDifference
    , test "ARCH-ID binding exact architecture instance identity accepts" testExactInstanceIdentity
    , test "ARCH-ID binding instance-key difference rejects" testInstanceKeyDifference
    , test "ARCH-ID binding instance-revision difference rejects" testInstanceRevisionDifference
    , test "ARCH-ID binding declaration Eq and Ord agree" testDeclarationEqOrdConsistency
    , test "ARCH-ID binding instance Eq and Ord agree" testInstanceEqOrdConsistency
    ]
  unless (and results) exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left message -> putStrLn ("FAIL: " <> label <> " -- " <> message) >> pure False

testExactDeclarationIdentity :: Either String ()
testExactDeclarationIdentity =
  assert (declarationV1 == declarationV1) "exact declaration identity rejected"

testDeclarationKeyDifference :: Either String ()
testDeclarationKeyDifference =
  assert (declarationV1 /= declarationV1
    { identityDeclarationKey = DeclarationKey "provider.other" })
    "declaration-key difference was ignored"

testInterfaceRevisionDifference :: Either String ()
testInterfaceRevisionDifference =
  assert (declarationV1 /= declarationV1
    { identityInterfaceRevision = InterfaceRevision "iface.v2" })
    "interface-revision difference was ignored"

testDefinitionRevisionDifference :: Either String ()
testDefinitionRevisionDifference =
  assert (declarationV1 /= declarationV1
    { identityDefinitionRevision = DefinitionRevision "def.v2" })
    "definition-revision difference was ignored"

testExactInstanceIdentity :: Either String ()
testExactInstanceIdentity =
  assert (instanceV1 == instanceV1) "exact architecture instance identity rejected"

testInstanceKeyDifference :: Either String ()
testInstanceKeyDifference =
  assert (instanceV1 /= instanceV1
    { identityInstanceKey = InstanceKey "steve.other" })
    "instance-key difference was ignored"

testInstanceRevisionDifference :: Either String ()
testInstanceRevisionDifference =
  assert (instanceV1 /= instanceV1
    { identityInstanceRevision = InstanceRevision "instance.rev.v2" })
    "instance-revision difference was ignored"

testDeclarationEqOrdConsistency :: Either String ()
testDeclarationEqOrdConsistency =
  mapM_ check
    [ (declarationV1, declarationV1)
    , (declarationV1, declarationV1
        { identityDefinitionRevision = DefinitionRevision "def.v2" })
    , (declarationV1, declarationV1
        { identityInterfaceRevision = InterfaceRevision "iface.v2" })
    ]
  where
    check (left, right) =
      assert ((left == right) == (compare left right == EQ))
        "DeclarationIdentity Eq/Ord disagreement"

testInstanceEqOrdConsistency :: Either String ()
testInstanceEqOrdConsistency =
  mapM_ check
    [ (instanceV1, instanceV1)
    , (instanceV1, instanceV1
        { identityInstanceRevision = InstanceRevision "instance.rev.v2" })
    , (instanceV1, instanceV1
        { identityInstanceKey = InstanceKey "steve.other" })
    ]
  where
    check (left, right) =
      assert ((left == right) == (compare left right == EQ))
        "ArchitectureInstanceIdentity Eq/Ord disagreement"

declarationV1 :: DeclarationIdentity
declarationV1 = DeclarationIdentity
  { identityDeclarationKey = DeclarationKey "provider.blob"
  , identityInterfaceRevision = InterfaceRevision "iface.v1"
  , identityDefinitionRevision = DefinitionRevision "def.v1"
  }

instanceV1 :: ArchitectureInstanceIdentity
instanceV1 = ArchitectureInstanceIdentity
  { identityInstanceKey = InstanceKey "steve.store"
  , identityInstanceRevision = InstanceRevision "instance.rev.v1"
  }

assert :: Bool -> String -> Either String ()
assert condition message
  | condition = Right ()
  | otherwise = Left message
