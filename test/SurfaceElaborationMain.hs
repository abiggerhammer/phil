{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (foldM, unless)
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context (insertBinding)
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( GrammarId (GrammarId)
  , Mode (Unrestricted)
  , Name (Name)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  , Value (..)
  )
import Phil.Surface.Elaborate
  ( ElaborationError (..)
  , ElaborationIssue (..)
  , elaborateProposition
  , elaborateRefTerm
  , elaborateType
  , elaborateValue
  , emptyElaborationEnv
  , withProjectionSort
  )
import Phil.Surface.Parser
  ( parseSurfaceExpression
  , parseSurfaceProposition
  , parseSurfaceType
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "Bytes[UInt] inserts canonical UInt-to-Nat" testBytesUIntIndex
    , test "dependent field indices use declared projection sorts" testProjectionIndex
    , test "Proof propositions elaborate to structured Core" testProofType
    , test "Validated keeps exact context and subject identities" testValidatedType
    , test "Frame elaborates to a grammar-indexed Core type" testFrameType
    , test "unknown surface types elaborate opaquely and stably" testOpaqueNamedType
    , test "unknown projection sorts fail at the projection span" testUnknownProjection
    , test "symbolic multiplication is outside the Phase 0 refinement fragment" testSymbolicMultiply
    , test "integer values require an expected UInt width" testIntegerValueWidth
    , test "greater-than canonicalizes into Core less-than" testGreaterThan
    , test "member uses the specialized Core proposition" testMembership
    ]
  unless (and results) exitFailure

test :: String -> Either String () -> IO Bool
test label result =
  case result of
    Right () -> putStrLn ("PASS: " ++ label) >> pure True
    Left message -> putStrLn ("FAIL: " ++ label ++ " -- " ++ message) >> pure False

stateWith :: [(Name, Ty)] -> Either String CheckState
stateWith bindings = foldM add emptyCheckState bindings
  where
    add state (name, ty) = do
      context <- mapLeft show $
        insertBinding Unrestricted name ty (resourceContext state)
      Right state { resourceContext = context }

environmentWith :: [(Name, Ty)] -> Either String Phil.Surface.Elaborate.ElaborationEnv
environmentWith bindings = do
  state <- stateWith bindings
  Right (emptyElaborationEnv emptyStaticContext state)

testBytesUIntIndex :: Either String ()
testBytesUIntIndex = do
  environment <- environmentWith [(Name "u", TyUInt 32)]
  surface <- mapLeft show $ parseSurfaceType "index.phil" "Bytes[u]"
  actual <- mapLeft show $ elaborateType environment surface
  let expected = TyBytes (RefToNat (RefVar (Name "u")))
  expectEqual expected actual

testProjectionIndex :: Either String ()
testProjectionIndex = do
  environment0 <- environmentWith [(Name "begin", TyOpaque "Begin")]
  let environment = withProjectionSort ["begin", "length"] (SortUInt 32) environment0
  surface <- mapLeft show $ parseSurfaceType "projection.phil" "Bytes[begin.length]"
  actual <- mapLeft show $ elaborateType environment surface
  let expected = TyBytes
        (RefToNat
          (RefField (RefVar (Name "begin")) "length" (SortUInt 32)))
  expectEqual expected actual

testProofType :: Either String ()
testProofType = do
  environment <- environmentWith
    [ (Name "r", TyUInt 32)
    , (Name "a", TyUInt 32)
    , (Name "b", TyUInt 32)
    ]
  surface <- mapLeft show $
    parseSurfaceType "proof.phil" "Proof[toNat(r) == toNat(a) + toNat(b)]"
  actual <- mapLeft show $ elaborateType environment surface
  let expected = TyProof
        (Equal
          (RefToNat (RefVar (Name "r")))
          (RefAdd
            (RefToNat (RefVar (Name "a")))
            (RefToNat (RefVar (Name "b")))))
  expectEqual expected actual

testValidatedType :: Either String ()
testValidatedType = do
  let environment = emptyElaborationEnv emptyStaticContext emptyCheckState
  surface <- mapLeft show $
    parseSurfaceType "validated.phil" "Validated[BeginPolicy, policyContext, begin]"
  actual <- mapLeft show $ elaborateType environment surface
  expectEqual
    (TyValidated "BeginPolicy" (Name "policyContext") (Name "begin"))
    actual

testFrameType :: Either String ()
testFrameType = do
  let environment = emptyElaborationEnv emptyStaticContext emptyCheckState
  surface <- mapLeft show $ parseSurfaceType "frame.phil" "Frame[Hello]"
  actual <- mapLeft show $ elaborateType environment surface
  expectEqual (TyFrame (GrammarId "Hello")) actual

testOpaqueNamedType :: Either String ()
testOpaqueNamedType = do
  let environment = emptyElaborationEnv emptyStaticContext emptyCheckState
  server <- mapLeft show $ parseSurfaceType "opaque.phil" "Server[Upload]"
  owned <- mapLeft show $ parseSurfaceType "opaque.phil" "OwnedBytes[1024]"
  actualServer <- mapLeft show $ elaborateType environment server
  actualOwned <- mapLeft show $ elaborateType environment owned
  expectEqual (TyOpaque "Server[Upload]", TyOpaque "OwnedBytes[1024]") (actualServer, actualOwned)

testUnknownProjection :: Either String ()
testUnknownProjection = do
  environment <- environmentWith [(Name "begin", TyOpaque "Begin")]
  surface <- mapLeft show $ parseSurfaceType "projection-error.phil" "Bytes[begin.length]"
  case elaborateType environment surface of
    Left (ElaborationError _ (UnknownProjectionSort ["begin", "length"])) -> Right ()
    other -> Left ("unexpected result: " ++ show other)

testSymbolicMultiply :: Either String ()
testSymbolicMultiply = do
  environment <- environmentWith
    [ (Name "a", TyOpaqueSorted "NatA" SortNat)
    , (Name "b", TyOpaqueSorted "NatB" SortNat)
    ]
  surface <- mapLeft show $ parseSurfaceExpression "multiply.phil" "a * b"
  case elaborateRefTerm environment surface of
    Left (ElaborationError _ UnsupportedSymbolicMultiplication) -> Right ()
    other -> Left ("unexpected result: " ++ show other)

testIntegerValueWidth :: Either String ()
testIntegerValueWidth = do
  let environment = emptyElaborationEnv emptyStaticContext emptyCheckState
  surface <- mapLeft show $ parseSurfaceExpression "integer.phil" "7"
  actual <- mapLeft show $ elaborateValue environment (Just (TyUInt 16)) surface
  expectEqual (VUInt 16 7) actual
  case elaborateValue environment Nothing surface of
    Left (ElaborationError _ (AmbiguousIntegerLiteral 7)) -> Right ()
    other -> Left ("unannotated integer was not rejected: " ++ show other)

testGreaterThan :: Either String ()
testGreaterThan = do
  environment <- environmentWith
    [ (Name "versions", TyOpaqueSorted "Versions" (SortFiniteSeq (SortUInt 16))) ]
  surface <- mapLeft show $
    parseSurfaceProposition "greater.phil" "len(versions) > 0"
  actual <- mapLeft show $ elaborateProposition environment surface
  expectEqual
    (LessThan (RefNat 0) (RefLen (RefVar (Name "versions"))))
    actual

testMembership :: Either String ()
testMembership = do
  environment0 <- environmentWith
    [ (Name "selected", TyUInt 16)
    , (Name "hello", TyOpaque "Hello")
    ]
  let environment = withProjectionSort
        ["hello", "versions"]
        (SortFiniteSeq (SortUInt 16))
        environment0
  surface <- mapLeft show $
    parseSurfaceProposition "member.phil" "member(selected, hello.versions)"
  actual <- mapLeft show $ elaborateProposition environment surface
  expectEqual
    (Member
      (RefVar (Name "selected"))
      (RefField
        (RefVar (Name "hello"))
        "versions"
        (SortFiniteSeq (SortUInt 16))))
    actual

expectEqual :: (Eq a, Show a) => a -> a -> Either String ()
expectEqual expected actual
  | expected == actual = Right ()
  | otherwise = Left ("expected " ++ show expected ++ ", got " ++ show actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
