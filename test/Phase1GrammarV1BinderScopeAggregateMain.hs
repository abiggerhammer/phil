{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Main (main) where

import Data.List (nub)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (..)
  )
import System.Exit (exitFailure)

-- This inventory is deliberately exhaustive over the production enum.  The
-- closeout workflow compiles it with -Wincomplete-patterns -Werror, so adding a
-- new GrammarV1BinderKind without assigning it to a certified SURF-009 tranche
-- fails CI.
data CertifiedSurfaceBinderSlice
  = TermBinderCoreSlice
  | CallableOutcomeStateSlice
  | RefinementBinderSlice
  | LetPatternSlice
  | CaseArmSlice
  | BorrowViewSlice
  | JoinStateSlice
  | LoopStateSlice
  | ProtocolBinderSlice
  deriving (Eq, Show)

certifiedSliceFor :: GrammarV1BinderKind -> CertifiedSurfaceBinderSlice
certifiedSliceFor kind = case kind of
  GrammarV1FunctionParameterBinder -> TermBinderCoreSlice
  GrammarV1CallableParameterBinder -> TermBinderCoreSlice
  GrammarV1CallableOutcomeStateBinder -> CallableOutcomeStateSlice
  GrammarV1ClaimParameterBinder -> TermBinderCoreSlice
  GrammarV1ComponentParameterBinder -> TermBinderCoreSlice
  GrammarV1ClosureParameterBinder -> TermBinderCoreSlice
  GrammarV1RefinementBinder -> RefinementBinderSlice
  GrammarV1LetPatternBinder -> LetPatternSlice
  GrammarV1MatchArmBinder -> CaseArmSlice
  GrammarV1BorrowViewBinder -> BorrowViewSlice
  GrammarV1JoinStateBinder -> JoinStateSlice
  GrammarV1LoopStateBinder -> LoopStateSlice
  GrammarV1ProtocolMessageBinder -> ProtocolBinderSlice
  GrammarV1ProtocolBranchPayloadBinder -> ProtocolBinderSlice

allProductionBinderKinds :: [GrammarV1BinderKind]
allProductionBinderKinds =
  [ GrammarV1FunctionParameterBinder
  , GrammarV1CallableParameterBinder
  , GrammarV1CallableOutcomeStateBinder
  , GrammarV1ClaimParameterBinder
  , GrammarV1ComponentParameterBinder
  , GrammarV1ClosureParameterBinder
  , GrammarV1RefinementBinder
  , GrammarV1LetPatternBinder
  , GrammarV1MatchArmBinder
  , GrammarV1BorrowViewBinder
  , GrammarV1JoinStateBinder
  , GrammarV1LoopStateBinder
  , GrammarV1ProtocolMessageBinder
  , GrammarV1ProtocolBranchPayloadBinder
  ]

expectedCertifiedSlices :: [CertifiedSurfaceBinderSlice]
expectedCertifiedSlices =
  [ TermBinderCoreSlice
  , CallableOutcomeStateSlice
  , RefinementBinderSlice
  , LetPatternSlice
  , CaseArmSlice
  , BorrowViewSlice
  , JoinStateSlice
  , LoopStateSlice
  , ProtocolBinderSlice
  ]

main :: IO ()
main = do
  let kinds = allProductionBinderKinds
      slices = nub (map certifiedSliceFor kinds)
      checks =
        [ (length kinds == 14,
            "production GrammarV1BinderKind inventory is no longer exactly 14 constructors")
        , (length (nub kinds) == length kinds,
            "production binder-kind inventory contains a duplicate constructor")
        , (slices == expectedCertifiedSlices,
            "production binder kinds no longer map exactly to the certified SURF-009 tranche inventory")
        ]
  if all fst checks
    then putStrLn "PASS: PHIL-SURFACE-BINDER-SCOPE-001 production binder inventory is exhaustively covered"
    else do
      mapM_ (putStrLn . ("FAIL: " <>) . snd) (filter (not . fst) checks)
      exitFailure
