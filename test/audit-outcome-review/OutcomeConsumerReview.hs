{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

-- Audit-only compiler correctness controls. No provider or native code executes.
-- CarrierFixture is the exact permanent fixture with only its module header
-- changed in a separate temporary directory; the production checkout is untouched.
import qualified CarrierFixture as F
import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Control (..), Mode (..), Ty (..))
import Phil.Surface.Check
import Phil.Surface.Syntax (Component, Located)
import System.Environment (getArgs)
import System.Exit (exitFailure)

type Result = Either SurfaceCheckError SurfaceCheckResult
type Prepared = Either String (SurfaceEnvironment, Located Component)
data Expected = Accepted | Rejected RejectionClass deriving Show
data Case = Case String Bool Expected Expected Prepared

takeSignature :: Mode -> SurfaceCallableSignature
takeSignature mode = SurfaceCallableSignature (DeclarationKey "audit.take.decision")
  [(mode, TyOpaque "CallableDecision")] Nothing

callCase :: F.Fixture -> Mode -> Text -> Prepared
callCase fixture mode body = do
  (environment, component) <- F.prepare fixture (F.wrap body)
  pure (environment {surfaceCallables = Map.insert "Take" (takeSignature mode)
    (surfaceCallables environment)}, component)

providerCase :: Text -> Prepared
providerCase body = do
  component <- F.parseOne (F.wrap body)
  let environment = (emptySurfaceEnvironment emptyStaticContext)
        { surfaceInitialBindings = Map.singleton "input" (InitialBinding Linear F.ownerTy PlainShape)
        , surfacePrimitives = Map.singleton "Produce" (PrimitiveProviderDecision
            [PrimitiveConsume]
            [ProviderOutcomeSpec label [(Linear,F.ownerTy)] | label <- ["ok","retry"]])
        , surfaceCallables = Map.singleton "Sink" (SurfaceCallableSignature
            (DeclarationKey "audit.sink") [(Linear,F.ownerTy)] Nothing)
        }
  pure (environment, component)

cases :: [Case]
cases =
  [ Case "R01-direct-owner-to-unrestricted-parameter" True Accepted (Rejected StructuralUse)
      (callCase F.Owners Unrestricted "invoke Take(invoke Worker(input))")
  , Case "R02-direct-owner-to-linear-parameter" True (Rejected StructuralUse) Accepted
      (callCase F.Owners Linear "invoke Take(invoke Worker(input))")
  , Case "R03-direct-obligation-to-unrestricted-parameter" True Accepted (Rejected StructuralUse)
      (callCase F.Obligations Unrestricted "invoke Take(invoke Worker())")
  , Case "C01-named-owner-cannot-be-unrestricted" False (Rejected StructuralUse) (Rejected StructuralUse)
      (callCase F.Owners Unrestricted "let d = invoke Worker(input) invoke Take(d)")
  , Case "C02-named-owner-can-transfer-linearly" False Accepted Accepted
      (callCase F.Owners Linear "let d = invoke Worker(input) invoke Take(d)")
  , Case "C03-tuple-carried-owner-once" False Accepted Accepted
      (callCase F.Owners Linear ("let (d, marker) = (invoke Worker(input), unit) decide d" <> F.ownedArms))
  , Case "C04-tuple-discard-rejects" False (Rejected LinearCompletion) (Rejected LinearCompletion)
      (callCase F.Owners Linear "(invoke Worker(input), unit)")
  , Case "R04-provider-result-repeated" True Accepted (Rejected StructuralUse)
      (providerCase ("let d = Produce(input) decide d" <> F.ownedArms <> "decide d" <> F.ownedArms))
  , Case "R05-provider-result-discarded" True Accepted (Rejected LinearCompletion)
      (providerCase "Produce(input)")
  , Case "R06-provider-result-alias-repeated" True Accepted (Rejected StructuralUse)
      (providerCase ("let d = Produce(input) let alias = d decide d" <> F.ownedArms <> "decide alias" <> F.ownedArms))
  , Case "C05-provider-result-direct-once" False Accepted Accepted
      (providerCase ("decide Produce(input)" <> F.ownedArms))
  , Case "C06-provider-result-stored-once" False Accepted Accepted
      (providerCase ("let d = Produce(input) decide d" <> F.ownedArms))
  ]

matches :: Expected -> Result -> Bool
matches Accepted (Right result) = checkedComponentName result == "Audit"
  && checkedTerminalControls result == [Return TyUnit]
matches (Rejected cls) (Left err) = surfaceErrorClass err == cls
matches _ _ = False

main :: IO ()
main = do
  args <- getArgs
  unless (args == ["--characterize"] || args == ["--require-fix"]) $ do
    putStrLn "SETUP_ERROR expected --characterize or --require-fix"
    exitFailure
  let characterize = args == ["--characterize"]
  putStrLn (if characterize then "MODE CHARACTERIZATION: MATCH is not repair correctness"
            else "MODE REQUIRED_CORRECTNESS")
  results <- mapM (run characterize) cases
  putStrLn ("OUTCOME_DONE " ++ show (length cases))
  unless (and results) exitFailure
  where
    run characterize (Case ident observation old corrected prepared) = case prepared of
      Left detail -> putStrLn ("SETUP_ERROR " ++ ident ++ " " ++ detail) >> pure False
      Right (environment, component) -> do
        let expected = if characterize then old else corrected
            actual = checkSurfaceComponent environment component
            ok = matches expected actual
            prefix = if observation && characterize then "CHAR " else "CHECK "
            status = if ok then (if observation && characterize then " MATCH " else " PASS ") else " FAIL "
        putStrLn (prefix ++ ident ++ status ++ "expected=" ++ show expected ++ "; actual=" ++ show actual)
        pure ok
