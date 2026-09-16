{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Main (main) where

import Phil.Surface.Parser (parseSurfaceExpression)
import Phil.Surface.Syntax
  ( Located (..)
  , SurfaceExpression (..)
  , pattern InvokeExpression
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  let checks =
        [ ("invoke parses as the dedicated callable category", invokeParses)
        , ("plain call remains provider/primitive call syntax", plainCallStaysPlain)
        , ("invoke preserves ordinary term arguments", invokeArgumentsPreserved)
        , ("invoke is reserved and cannot be a bare variable", invokeKeywordReserved)
        ]
  results <- mapM report checks
  if and results then pure () else exitFailure

report :: (String, Either String ()) -> IO Bool
report (label, result) = case result of
  Right () -> putStrLn ("PASS: CALL-019 " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: CALL-019 " <> label <> " -- " <> detail) >> pure False

invokeParses :: Either String ()
invokeParses =
  case parseSurfaceExpression "call019.phil" "invoke StevePut(candidate)" of
    Right (Located _ (InvokeExpression "StevePut" [Located _ (VariableExpression "candidate")])) ->
      Right ()
    Right parsed -> Left ("unexpected invoke AST: " <> show parsed)
    Left diagnostic -> Left ("invoke failed to parse: " <> show diagnostic)

plainCallStaysPlain :: Either String ()
plainCallStaysPlain =
  case parseSurfaceExpression "call019.phil" "StevePut(candidate)" of
    Right (Located _ (CallExpression "StevePut" [Located _ (VariableExpression "candidate")])) ->
      Right ()
    Right (Located _ (InvokeExpression name _)) ->
      Left ("plain call was reclassified as invoke: " <> show name)
    Right parsed -> Left ("unexpected plain-call AST: " <> show parsed)
    Left diagnostic -> Left ("plain call failed to parse: " <> show diagnostic)

invokeArgumentsPreserved :: Either String ()
invokeArgumentsPreserved =
  case parseSurfaceExpression
      "call019.phil"
      "invoke StevePut(candidate, digest_compute(candidate))" of
    Right (Located _ (InvokeExpression "StevePut"
      [ Located _ (VariableExpression "candidate")
      , Located _ (CallExpression "digest_compute" [Located _ (VariableExpression "candidate")])
      ])) -> Right ()
    Right parsed -> Left ("invoke arguments changed category/order: " <> show parsed)
    Left diagnostic -> Left ("invoke argument form failed to parse: " <> show diagnostic)

invokeKeywordReserved :: Either String ()
invokeKeywordReserved =
  case parseSurfaceExpression "call019.phil" "invoke" of
    Left _ -> Right ()
    Right parsed -> Left ("reserved invoke parsed as ordinary expression: " <> show parsed)
