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
      AssurancePolicyRevision "audit.constructor-schema.v1"
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
    label = "PHIL-AUD-CONSTRUCTOR-SCHEMA-001 " <> Text.unpack (caseId auditCase)
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
            other -> failCase ("invalid constructor crossed public boundary: " <> show other)

auditCases :: [AuditCase]
auditCases =
  [ AuditCase "c01-version-set-positive" c01 Accept
  , AuditCase "c02-missing-field" c02 (RejectOneOf [TypeMismatch])
  , AuditCase "c03-unknown-constructor" c03 (RejectOneOf [TypeMismatch])
  , AuditCase "c04-bool-field" c04 (RejectOneOf [TypeMismatch])
  , AuditCase "c05-duplicate-field" c05 (RejectOneOf [TypeMismatch, StructuralUse])
  , AuditCase "c06-extra-field" c06 (RejectOneOf [TypeMismatch, UnknownPrimitive])
  , AuditCase "c07-record-borrow-escape" c07
      (RejectOneOf [TypeMismatch, BorrowEscape, StructuralUse])
  , AuditCase "c08-safe-record-result" c08 Accept
  ]

c01, c02, c03, c04, c05, c06, c07, c08 :: Text
c01 = Text.unlines
  [ "component Audit() {"
  , "    let versions = supported_versions()"
  , "    let hello = construct Hello { versions = versions }"
  , "    inspect(hello.versions)"
  , "}"
  ]

c02 = Text.unlines
  [ "component Audit() {"
  , "    let hello = construct Hello {}"
  , "    inspect(hello)"
  , "}"
  ]

c03 = Text.unlines
  [ "component Audit() {"
  , "    let hello = construct NotAConstructor {}"
  , "    inspect(hello)"
  , "}"
  ]

c04 = Text.unlines
  [ "component Audit() {"
  , "    let hello = construct Hello { versions = true }"
  , "    inspect(hello.versions)"
  , "}"
  ]

c05 = Text.unlines
  [ "component Audit() {"
  , "    let versions = supported_versions()"
  , "    let hello = construct Hello { versions = missing, versions = versions }"
  , "    inspect(hello)"
  , "}"
  ]

c06 = Text.unlines
  [ "component Audit() {"
  , "    let versions = supported_versions()"
  , "    let hello = construct Hello { versions = versions, spare = undeclared() }"
  , "    inspect(hello)"
  , "}"
  ]

c07 = Text.unlines
  [ "component Audit(payload : OwnedBytes[1024]) {"
  , "    let packet = borrow payload as view {"
  , "        construct Hello { versions = view }"
  , "    }"
  , "    use(payload)"
  , "    inspect(packet.versions)"
  , "}"
  ]

c08 = Text.unlines
  [ "component Audit(payload : OwnedBytes[1024]) {"
  , "    let packet = borrow payload as view {"
  , "        let versions = supported_versions()"
  , "        construct Hello { versions = versions }"
  , "    }"
  , "    use(payload)"
  , "    inspect(packet.versions)"
  , "}"
  ]
