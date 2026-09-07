{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (forM, unless)
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.Check
  ( RejectionClass (..)
  , SurfaceCheckError (..)
  , SurfaceCheckResult (..)
  )
import Phil.Surface.Phase0 (phase0EnvironmentFor)
import Phil.Verification
  ( ApplicationAssurancePolicy (..)
  , ApplicationVerificationResult (..)
  , AssurancePolicyRevision (..)
  , IntrinsicRejection (..)
  , VerificationDisposition (..)
  , verifySurfaceApplication
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  fixtureResults <- forM intrinsicFixtures (uncurry checkIntrinsicFixture)
  parseResult <- checkParseRejection
  cardinalityResult <- checkCardinalityRejection
  acceptedResult <- checkAcceptedControl
  unless (and (acceptedResult : parseResult : cardinalityResult : fixtureResults)) exitFailure

strictPolicy :: ApplicationAssurancePolicy
strictPolicy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision = AssurancePolicyRevision "phase1.ver.strict.v1"
  , applicationAssurancePolicyPermittedDispositions = Set.singleton Unresolved
  }

permissivePolicy :: ApplicationAssurancePolicy
permissivePolicy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision = AssurancePolicyRevision "phase1.ver.permissive.v1"
  , applicationAssurancePolicyPermittedDispositions = Set.fromList
      [ StaticallyDischarged
      , RuntimeBound
      , ExternallyDischarged
      , AssumptionDependent
      , Exported
      , DeploymentExported
      , Unresolved
      ]
  }

intrinsicFixtures :: [(FilePath, RejectionClass)]
intrinsicFixtures =
  [ ("examples/rejected/01-reuse-consumed-endpoint.phil", StructuralUse)
  , ("examples/rejected/03-wrong-protocol-order.phil", SessionAction)
  , ("examples/rejected/11-copy-authority-capability.phil", StructuralUse)
  , ("examples/rejected/16-escape-shared-loan.phil", BorrowEscape)
  ]

checkIntrinsicFixture :: FilePath -> RejectionClass -> IO Bool
checkIntrinsicFixture path expectedClass = do
  source <- TextIO.readFile path
  case phase0EnvironmentFor path of
    Left errorText -> failCase path (Text.unpack errorText)
    Right environment ->
      let strictResult = verifySurfaceApplication
            environment strictPolicy (Text.pack path) source
          permissiveResult = verifySurfaceApplication
            environment permissivePolicy (Text.pack path) source
      in case (strictResult, permissiveResult) of
        ( IntrinsicRejected (IntrinsicSurfaceRejected strictError)
          , IntrinsicRejected (IntrinsicSurfaceRejected permissiveError)
          )
          | strictError == permissiveError
          , surfaceErrorClass strictError == expectedClass ->
              passCase (path ++ " remains intrinsically rejected under permissive policy")
          | otherwise -> failCase path
              ("intrinsic rejection changed across policy or had wrong class: "
                ++ show (strictError, permissiveError))
        other -> failCase path
          ("intrinsic invalidity crossed into obligation closure: " ++ show other)

checkParseRejection :: IO Bool
checkParseRejection = do
  let path = "examples/upload/client.phil"
  case phase0EnvironmentFor path of
    Left errorText -> failCase "parse-negative" (Text.unpack errorText)
    Right environment ->
      let malformed = "component Broken provides Unit {"
          strictResult = verifySurfaceApplication environment strictPolicy "parse-negative.phil" malformed
          permissiveResult = verifySurfaceApplication environment permissivePolicy "parse-negative.phil" malformed
      in case (strictResult, permissiveResult) of
        (IntrinsicRejected (IntrinsicParseRejected leftDiagnostic),
         IntrinsicRejected (IntrinsicParseRejected rightDiagnostic))
          | leftDiagnostic == rightDiagnostic ->
              passCase "parse invalidity is policy-independent"
        other -> failCase "parse-negative"
          ("parse invalidity crossed into obligation closure: " ++ show other)

checkCardinalityRejection :: IO Bool
checkCardinalityRejection = do
  let path = "examples/upload/client.phil"
  source <- TextIO.readFile path
  case phase0EnvironmentFor path of
    Left errorText -> failCase "cardinality-negative" (Text.unpack errorText)
    Right environment ->
      let doubled = source <> "\n" <> source
          result = verifySurfaceApplication environment permissivePolicy "two-components.phil" doubled
      in case result of
        IntrinsicRejected (IntrinsicComponentCardinalityRejected 2) ->
          passCase "component-cardinality invalidity is intrinsic"
        other -> failCase "cardinality-negative"
          ("component cardinality crossed into obligation closure: " ++ show other)

checkAcceptedControl :: IO Bool
checkAcceptedControl = do
  let path = "examples/upload/client.phil"
  source <- TextIO.readFile path
  case phase0EnvironmentFor path of
    Left errorText -> failCase path (Text.unpack errorText)
    Right environment ->
      case verifySurfaceApplication environment permissivePolicy (Text.pack path) source of
        ReadyForObligationClosure checked policy
          | checkedComponentName checked == "UploadClient"
          , policy == permissivePolicy ->
              passCase "intrinsic success alone reaches obligation closure with selected policy"
          | otherwise -> failCase path
              ("accepted control changed checked result/policy: " ++ show (checked, policy))
        other -> failCase path
          ("accepted control did not reach obligation closure: " ++ show other)

passCase :: String -> IO Bool
passCase message = putStrLn ("PASS: VER-001 " ++ message) >> pure True

failCase :: String -> String -> IO Bool
failCase label message =
  putStrLn ("FAIL: VER-001 " ++ label ++ " -- " ++ message) >> pure False
