{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (forM)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Syntax
  ( GrammarId (..)
  , Mode (..)
  , Name (..)
  , Outcome (..)
  , Session (..)
  , Ty (..)
  )
import Phil.Surface.Check
  ( InitialBinding (..)
  , RejectionClass (..)
  , SurfaceCheckError (..)
  , SurfaceEnvironment (..)
  , SurfaceShape (..)
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
  | Reject RejectionClass

data AuditCase = AuditCase
  { caseId :: Text
  , caseIngressGrammar :: Text
  , caseLegacy :: Bool
  , caseSource :: Text
  , caseExpectation :: Expectation
  }

main :: IO ()
main = do
  base <- either (fail . Text.unpack) pure $
    phase0EnvironmentFor "examples/rejected/16-escape-shared-loan.phil"
  results <- forM auditCases (runCase base)
  if and results then pure () else exitFailure

policy :: ApplicationAssurancePolicy
policy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision =
      AssurancePolicyRevision "audit.recognition-grammar.v1"
  , applicationAssurancePolicyPermittedDispositions = Set.empty
  }

runCase :: SurfaceEnvironment -> AuditCase -> IO Bool
runCase base auditCase =
  case parseSurfaceFile (caseId auditCase <> ".phil") (caseSource auditCase) of
    Left diagnostic -> failCase ("parse failure: " <> show diagnostic)
    Right (SurfaceFile [component]) -> do
      let environment = caseEnvironment base auditCase
          direct = checkSurfaceComponent environment component
          intrinsic = verifySurfaceApplication
            environment
            policy
            (caseId auditCase <> ".phil")
            (caseSource auditCase)
      compareResults direct intrinsic
    Right (SurfaceFile components) ->
      failCase ("unexpected component count: " <> show (length components))
  where
    label = "PHIL-AUD-RECOGNITION-GRAMMAR-001 " <> Text.unpack (caseId auditCase)
    passCase = putStrLn ("PASS: " <> label) >> pure True
    failCase detail = putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

    compareResults direct intrinsic =
      case caseExpectation auditCase of
        Accept -> case (direct, intrinsic) of
          (Right _, ReadyForObligationClosure _ _) -> passCase
          other -> failCase ("expected public acceptance, got " <> show other)
        Reject expected -> case (direct, intrinsic) of
          (Left directError, IntrinsicRejected (IntrinsicSurfaceRejected intrinsicError))
            | surfaceErrorClass directError == expected
            , surfaceErrorClass intrinsicError == expected -> passCase
            | otherwise -> failCase
                ("checker/intrinsic rejection mismatch or wrong class: "
                  <> show (directError, intrinsicError))
          other -> failCase ("invalid recognition crossed public boundary: " <> show other)

caseEnvironment :: SurfaceEnvironment -> AuditCase -> SurfaceEnvironment
caseEnvironment base auditCase = base
  { surfaceInitialBindings = Map.singleton "session0"
      (InitialBinding
        Linear
        (TyEndpoint
          (Receive
            (Name "frame")
            (TyFrame (GrammarId (caseIngressGrammar auditCase)))
            (End (Outcome "success"))))
        PlainShape)
  , surfaceExpectedProvides = Nothing
  , surfaceLegacyReceiveFrameRaw = caseLegacy auditCase
  }

auditCases :: [AuditCase]
auditCases =
  [ AuditCase "r01-matching-hello" "Hello" False
      (nonlegacy "Hello" (Just "versions")) Accept
  , AuditCase "r02-matching-begin" "Begin" False
      (nonlegacy "Begin" (Just "length")) Accept
  , AuditCase "r03-hello-as-begin-commit" "Hello" False
      (nonlegacy "Begin" Nothing) (Reject RecognitionProvenance)
  , AuditCase "r04-hello-as-begin-projection" "Hello" False
      (nonlegacy "Begin" (Just "length")) (Reject RecognitionProvenance)
  , AuditCase "r05-begin-as-hello-projection" "Begin" False
      (nonlegacy "Hello" (Just "versions")) (Reject RecognitionProvenance)
  , AuditCase "r06-hello-as-other" "Hello" False
      (nonlegacy "OtherGrammar" Nothing) (Reject RecognitionProvenance)
  , AuditCase "r07-genuine-hello-invalid-field" "Hello" False
      (nonlegacy "Hello" (Just "length")) (Reject IllegalProjection)
  , AuditCase "r08-legacy-matching-begin" "Begin" True
      (legacy "Begin") Accept
  , AuditCase "r09-legacy-hello-as-begin" "Hello" True
      (legacy "Begin") (Reject RecognitionProvenance)
  , AuditCase "r10-raw-field-projection" "Hello" False
      rawFieldProjection (Reject IllegalProjection)
  ]

nonlegacy :: Text -> Maybe Text -> Text
nonlegacy requested projectedField = Text.unlines $
  [ "component Audit() {"
  , "    let pending = receive_frame(session0)"
  , "    let result = borrow pending as raw {"
  , "        recognize " <> requested <> " from raw"
  , "    }"
  , "    decide result {"
  , "        accepted(parsed) => {"
  ]
  <> projection
  <> [ "            let session1 = commit_receive pending using parsed"
     , "            close session1"
     , "        }"
     , "        rejected(reason) => {"
     , "            fail recognition(reason) on pending"
     , "        }"
     , "    }"
     , "}"
     ]
  where
    projection = case projectedField of
      Nothing -> []
      Just field -> ["            inspect(parsed.value." <> field <> ")"]

legacy :: Text -> Text
legacy requested = Text.unlines
  [ "component Audit() {"
  , "    let (pending, raw) = receive_frame(session0)"
  , "    decide recognize " <> requested <> " from raw {"
  , "        success(parsed) => {"
  , "            let session1 = commit_receive pending using parsed"
  , "            close session1"
  , "        }"
  , "        failure(reason) => {"
  , "            fail recognition(reason) on pending"
  , "        }"
  , "    }"
  , "}"
  ]

rawFieldProjection :: Text
rawFieldProjection = Text.unlines
  [ "component Audit() {"
  , "    let pending = receive_frame(session0)"
  , "    let probe = borrow pending as raw {"
  , "        inspect(raw.length)"
  , "    }"
  , "    inspect(probe)"
  , "}"
  ]
