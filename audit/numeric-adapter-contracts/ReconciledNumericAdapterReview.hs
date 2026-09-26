{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (unless)
import qualified Data.Set as Set
import qualified NumericFixture as N
import qualified Phil.Core.NumericConversion as C
import qualified Phil.Core.SIntArithmetic as S
import Phil.Surface.GrammarV1.Lexer (grammarV1ReservedWords)
import System.Exit (exitFailure)

-- The original prepared NumericAdapterReview.hs is byte-preserved. The first
-- run compiled it, passed its other fifteen cases, and failed C06 during source
-- parsing because "negative" is a reserved word, before arithmetic evaluation.
-- This wrapper reuses those fifteen case expressions verbatim and replaces only
-- C06's source label with "signedOperand". Values, domains, explicit conversions
-- and expected result remain unchanged. Original logs/source stay in the packet.

legalSignedOperands :: Either String ()
legalSignedOperands = do
  N.ensure (Set.member "negative" grammarV1ReservedWords)
    "reviewed reserved-word diagnosis changed"
  N.ensure (not (Set.member "signedOperand" grammarV1ReservedWords))
    "replacement fixture identifier became reserved"
  negative <- N.sintLeaf 8 "-7"
  positive <- N.uintLeaf 8 "2"
  environment <- N.registry [("signedOperand",negative),("positive",positive)]
  N.runExpression "(convert signedOperand to I16) + (convert positive to I16)" environment
    >>= N.same (C.NumericSIntValue (S.SIntLiteral (S.SIntType 16) (-5)))

main :: IO ()
main = do
  let cases =
        [ (key,label,if key == "C06" then legalSignedOperands else original)
        | (key,label,original) <- N.controls
        ]
  unless (length [() | (key,_,_) <- cases, key == "C06"] == 1) $ do
    putStrLn "SETUP_ERROR original C06 inventory changed"
    exitFailure
  outcomes <- mapM run cases
  putStrLn "COMPLETE numeric_adapter_groups=16"
  unless (and outcomes) exitFailure
  where
    run (key,label,result) = case result of
      Right () -> putStrLn ("PASS " <> key <> " " <> label) >> pure True
      Left problem -> putStrLn ("FAIL " <> key <> " " <> label <> " -- " <> problem) >> pure False
