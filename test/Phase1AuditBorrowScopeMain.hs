{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.Check
  ( RejectionClass (..)
  , SurfaceCheckError (..)
  , checkSurfaceComponent
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Phase0 (phase0EnvironmentFor)
import Phil.Surface.Syntax (SurfaceFile (..))
import System.Exit (exitFailure)

data Expected
  = ExpectAccept
  | ExpectReject RejectionClass
  | ExpectRejectOneOf [RejectionClass]

main :: IO ()
main = do
  results <- sequence
    [ runCase "safe local view use" ExpectAccept safeLocalViewUse
    , runCase "direct returned view rejects" (ExpectReject BorrowEscape) directViewResult
    , runCase "tuple returned view rejects" (ExpectReject BorrowEscape) tupleViewResult
    , runCase "owner consumption during active loan rejects" (ExpectReject StructuralUse)
        ownerConsumptionDuringLoan
    , runCase "view spelling is gone after exit" (ExpectReject StructuralUse)
        viewNameAfterExit
    , runCase "hidden let alias cannot survive borrow exit"
        (ExpectRejectOneOf [BorrowEscape, StructuralUse]) hiddenLetAlias
    , runCase "hidden tuple alias cannot survive borrow exit"
        (ExpectRejectOneOf [BorrowEscape, StructuralUse]) hiddenTupleAlias
    , runCase "closed borrow-local spelling may be reused" ExpectAccept closedNameReuse
    ]
  if and results then pure () else exitFailure

runCase :: String -> Expected -> Text -> IO Bool
runCase label expected source =
  case checkSource source of
    Left harness -> failCase ("harness failure: " <> harness)
    Right result ->
      case (expected, result) of
        (ExpectAccept, Right _) -> passCase
        (ExpectAccept, Left err) ->
          failCase ("expected acceptance, got " <> showError err)
        (ExpectReject klass, Left err)
          | surfaceErrorClass err == klass -> passCase
          | otherwise ->
              failCase ("expected " <> show klass <> ", got " <> showError err)
        (ExpectReject klass, Right _) ->
          failCase ("expected rejection " <> show klass <> ", checker accepted")
        (ExpectRejectOneOf classes, Left err)
          | surfaceErrorClass err `elem` classes -> passCase
          | otherwise ->
              failCase ("expected one of " <> show classes <> ", got " <> showError err)
        (ExpectRejectOneOf classes, Right _) ->
          failCase ("expected one of " <> show classes <> ", checker accepted")
  where
    passCase = putStrLn ("PASS: PHIL-AUD-BORROW-LOCAL-001 " <> label) >> pure True
    failCase detail =
      putStrLn ("FAIL: PHIL-AUD-BORROW-LOCAL-001 " <> label <> " -- " <> detail)
        >> pure False

checkSource
  :: Text
  -> Either String (Either SurfaceCheckError ())
checkSource source = do
  environment <- either (Left . Text.unpack) Right $
    phase0EnvironmentFor "examples/rejected/16-escape-shared-loan.phil"
  surfaceFile <- either (Left . show) Right $
    parseSurfaceFile "audit-borrow-local.phil" source
  component <- case surfaceFile of
    SurfaceFile [value] -> Right value
    SurfaceFile values -> Left ("unexpected component count: " <> show (length values))
  pure (() <$ checkSurfaceComponent environment component)

showError :: SurfaceCheckError -> String
showError err =
  show (surfaceErrorClass err) <> ": " <> Text.unpack (surfaceErrorDetail err)

safeLocalViewUse :: Text
safeLocalViewUse = Text.unlines
  [ "component AuditBorrowSafe(payload : OwnedBytes[1024]) {"
  , "    borrow payload as view {"
  , "        inspect(view)"
  , "        ()"
  , "    }"
  , "    use(payload)"
  , "}"
  ]

directViewResult :: Text
directViewResult = Text.unlines
  [ "component AuditBorrowDirect(payload : OwnedBytes[1024]) {"
  , "    let escaped = borrow payload as view {"
  , "        view"
  , "    }"
  , "    use(payload)"
  , "    inspect(escaped)"
  , "}"
  ]

tupleViewResult :: Text
tupleViewResult = Text.unlines
  [ "component AuditBorrowTupleResult(payload : OwnedBytes[1024]) {"
  , "    let escaped = borrow payload as view {"
  , "        (view, ())"
  , "    }"
  , "    use(payload)"
  , "    inspect(escaped)"
  , "}"
  ]

ownerConsumptionDuringLoan :: Text
ownerConsumptionDuringLoan = Text.unlines
  [ "component AuditBorrowOwnerUse(payload : OwnedBytes[1024]) {"
  , "    borrow payload as view {"
  , "        use(payload)"
  , "        ()"
  , "    }"
  , "}"
  ]

viewNameAfterExit :: Text
viewNameAfterExit = Text.unlines
  [ "component AuditBorrowViewExit(payload : OwnedBytes[1024]) {"
  , "    borrow payload as view {"
  , "        ()"
  , "    }"
  , "    use(payload)"
  , "    inspect(view)"
  , "}"
  ]

hiddenLetAlias :: Text
hiddenLetAlias = Text.unlines
  [ "component AuditBorrowHiddenAlias(payload : OwnedBytes[1024]) {"
  , "    borrow payload as view {"
  , "        let escaped = (view)"
  , "        ()"
  , "    }"
  , "    use(payload)"
  , "    inspect(escaped)"
  , "}"
  ]

hiddenTupleAlias :: Text
hiddenTupleAlias = Text.unlines
  [ "component AuditBorrowHiddenTupleAlias(payload : OwnedBytes[1024]) {"
  , "    borrow payload as view {"
  , "        let (escaped, marker) = (view, ())"
  , "        ()"
  , "    }"
  , "    use(payload)"
  , "    inspect(escaped)"
  , "}"
  ]

closedNameReuse :: Text
closedNameReuse = Text.unlines
  [ "component AuditBorrowNameReuse(payload : OwnedBytes[1024]) {"
  , "    borrow payload as view {"
  , "        let local = ()"
  , "        ()"
  , "    }"
  , "    let local = ()"
  , "    use(payload)"
  , "}"
  ]
