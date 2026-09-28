{-# LANGUAGE OverloadedStrings #-}

-- Independent regression for the existing PHIL-AUD-BORROW-LOCAL-001.
-- No production source is altered. Expected failures remain test failures.
module Main (main) where

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.Check
  ( RejectionClass (..)
  , SurfaceCheckError (..)
  , SurfaceCheckResult
  , checkSurfaceComponent
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Phase0 (phase0EnvironmentFor)
import Phil.Surface.Syntax (SurfaceFile (..))
import System.Exit (exitFailure)

data Expectation = MustAccept | MustReject | Observe

main :: IO ()
main = do
  results <- mapM runCase cases
  if and results then pure () else exitFailure

runCase :: (String, Expectation, Text) -> IO Bool
runCase (label, expected, source) = do
  putStrLn ("BEGIN SOURCE " <> label)
  TextIO.putStr source
  putStrLn ("END SOURCE " <> label)
  let result = checkSource source
      ok = case result of
        Left _ -> False
        Right outcome -> case (expected, outcome) of
          (Observe, _) -> True
          (MustAccept, Right _) -> True
          (MustReject, Left err) ->
            surfaceErrorClass err `elem` [BorrowEscape, StructuralUse]
          _ -> False
  putStrLn ("OBSERVED " <> label <> " " <> show result)
  let prefix = case expected of
        Observe | ok -> "OBSERVATION "
        _ | ok -> "PASS "
        _ -> "FAIL "
  putStrLn (prefix <> label)
  pure ok

checkSource :: Text -> Either String (Either SurfaceCheckError SurfaceCheckResult)
checkSource source = do
  environment <- either (Left . Text.unpack) Right $
    phase0EnvironmentFor "examples/rejected/16-escape-shared-loan.phil"
  parsed <- either (Left . show) Right $
    parseSurfaceFile "independent-borrow-rebinding.phil" source
  component <- case parsed of
    SurfaceFile [value] -> Right value
    SurfaceFile values -> Left ("unexpected component count: " <> show (length values))
  pure (checkSurfaceComponent environment component)

cases :: [(String, Expectation, Text)]
cases =
  [ ("C01 unrelated outer consumption stays consumed", MustAccept, component
      [ "    borrow payload as view {"
      , "        use(slot)"
      , "        inspect(view)"
      , "        ()"
      , "    }"
      , "    use(payload)"
      ])
  , ("C02 fresh child alias remains inaccessible", MustReject, component
      [ "    borrow payload as view {"
      , "        use(slot)"
      , "        let fresh = view"
      , "        ()"
      , "    }"
      , "    use(payload)"
      , "    inspect(fresh)"
      ])
  , ("R01 recycled outer spelling must not export a borrowed alias", MustReject, component
      [ "    borrow payload as view {"
      , "        use(slot)"
      , "        let slot = view"
      , "        ()"
      , "    }"
      , "    use(payload)"
      , "    inspect(slot)"
      ])
  , ("O01 recycled child spelling reuse diagnostic", Observe, component
      [ "    borrow payload as view {"
      , "        use(slot)"
      , "        let slot = ()"
      , "        ()"
      , "    }"
      , "    let slot = ()"
      , "    use(payload)"
      ])
  ]

component :: [Text] -> Text
component body = Text.unlines $
  ["component BorrowRebinding(payload : OwnedBytes[1024], slot : OwnedBytes[1024]) {"]
  <> body <> ["}"]
