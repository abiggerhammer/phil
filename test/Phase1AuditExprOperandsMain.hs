{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (forM)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.Check
  ( RejectionClass (..)
  , SurfaceCheckError (..)
  , SurfaceEnvironment
  , checkSurfaceComponent
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Phase0 (phase0EnvironmentFor)
import Phil.Surface.Syntax (SurfaceFile (..))
import Phil.Verification
  ( ApplicationAssurancePolicy (..)
  , ApplicationVerificationResult (..)
  , AssurancePolicyRevision (..)
  , IntrinsicRejection (..)
  , verifySurfaceApplication
  )
import System.Exit (exitFailure)

data Expectation
  = Accept
  | RejectOneOf [RejectionClass]

data AuditCase = AuditCase
  { caseId :: Text
  , caseSource :: Text
  , caseExpectation :: Expectation
  }

main :: IO ()
main = do
  environment <- either (fail . Text.unpack) pure $
    phase0EnvironmentFor "examples/rejected/16-escape-shared-loan.phil"
  results <- forM auditCases (runCase environment)
  if and results then pure () else exitFailure

policy :: ApplicationAssurancePolicy
policy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision =
      AssurancePolicyRevision "audit.expr-operands.v1"
  , applicationAssurancePolicyPermittedDispositions = Set.empty
  }

runCase :: SurfaceEnvironment -> AuditCase -> IO Bool
runCase environment auditCase =
  case parseSurfaceFile (caseId auditCase <> ".phil") (caseSource auditCase) of
    Left diagnostic -> failCase ("parse failure: " <> show diagnostic)
    Right (SurfaceFile [component]) -> do
      let direct = checkSurfaceComponent environment component
          intrinsic = verifySurfaceApplication
            environment
            policy
            (caseId auditCase <> ".phil")
            (caseSource auditCase)
      compareResults direct intrinsic
    Right (SurfaceFile components) ->
      failCase ("unexpected component count: " <> show (length components))
  where
    label = "PHIL-AUD-EXPR-OPERANDS-001 " <> Text.unpack (caseId auditCase)
    passCase = putStrLn ("PASS: " <> label) >> pure True
    failCase detail = putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

    compareResults direct intrinsic =
      case caseExpectation auditCase of
        Accept ->
          case (direct, intrinsic) of
            (Right _, ReadyForObligationClosure _ _) -> passCase
            other -> failCase ("expected public acceptance, got " <> show other)
        RejectOneOf classes ->
          case (direct, intrinsic) of
            (Left directError, IntrinsicRejected (IntrinsicSurfaceRejected intrinsicError))
              | surfaceErrorClass directError == surfaceErrorClass intrinsicError
              , surfaceErrorClass directError `elem` classes -> passCase
              | otherwise -> failCase
                  ("checker/intrinsic rejection mismatch or wrong class: "
                    <> show (directError, intrinsicError))
            other -> failCase ("invalid expression crossed public boundary: " <> show other)

auditCases :: [AuditCase]
auditCases =
  [ AuditCase "e01-literal-add" e01 Accept
  , AuditCase "e02-bound-operand" e02 Accept
  , AuditCase "e03-direct-unknown" e03 (RejectOneOf [StructuralUse])
  , AuditCase "e04-unknown-left" e04 (RejectOneOf [StructuralUse, TypeMismatch])
  , AuditCase "e05-unknown-right" e05 (RejectOneOf [StructuralUse, TypeMismatch])
  , AuditCase "e06-nested-unknown" e06 (RejectOneOf [StructuralUse, TypeMismatch])
  , AuditCase "e07-bool-arithmetic" e07 (RejectOneOf [TypeMismatch])
  , AuditCase "e08-unknown-call-child" e08 (RejectOneOf [UnknownPrimitive, TypeMismatch])
  , AuditCase "e09-direct-unknown-call" e09 (RejectOneOf [UnknownPrimitive])
  , AuditCase "e10-consumed-child" e10 (RejectOneOf [StructuralUse, TypeMismatch])
  , AuditCase "e11-effectful-child" e11 (RejectOneOf [TypeMismatch, StructuralUse])
  , AuditCase "symbolic-multiply-remains-fail-closed"
      "component Audit(x : U32, y : U32) { let n = x * y inspect(n) }"
      (RejectOneOf [TypeMismatch])
  ]

e01, e02, e03, e04, e05, e06, e07, e08, e09, e10, e11 :: Text
e01 = "component Audit() { let n = 1 + 2 inspect(n) }"
e02 = "component Audit(x : U32) { let n = x + 1 inspect(n) }"
e03 = "component Audit() { inspect(missing) }"
e04 = "component Audit() { let n = missing + 1 inspect(n) }"
e05 = "component Audit() { inspect(1 + missing) }"
e06 = "component Audit() { inspect((1 + missing) * 2) }"
e07 = "component Audit() { let n = true + false inspect(n) }"
e08 = "component Audit() { let n = undeclared() + 1 inspect(n) }"
e09 = "component Audit() { undeclared() }"
e10 = Text.unlines
  [ "component Audit(payload : OwnedBytes[1024]) {"
  , "  use(payload)"
  , "  inspect(payload + 1)"
  , "}"
  ]
e11 = Text.unlines
  [ "component Audit(payload : OwnedBytes[1024]) {"
  , "  let n = use(payload) + 1"
  , "  use(payload)"
  , "  inspect(n)"
  , "}"
  ]
