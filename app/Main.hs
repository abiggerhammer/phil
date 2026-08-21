{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Phil.Core.Context
  ( ResourceContext (linearBindings)
  , consumeLinear
  , emptyContext
  , insertBinding
  )
import Phil.Core.Syntax (Mode (Linear), Name (Name), Ty (TyOpaque))

main :: IO ()
main = do
  let endpoint = Name "endpoint"
      endpointTy = TyOpaque "Endpoint[ServerUpload]"
  case insertBinding Linear endpoint endpointTy emptyContext >>= consumeLinear endpoint of
    Left err -> putStrLn ("phil-core bootstrap failed: " ++ show err)
    Right (_, residual) -> do
      putStrLn "phil-core bootstrap: linear endpoint consumed"
      putStrLn ("residual Δ = " ++ show (linearBindings residual))
