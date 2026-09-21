{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (forM)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Core.Syntax
  ( Control (..)
  , Name (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  )
import Phil.Surface.Check
  ( RejectionClass (..)
  , SurfaceCheckError (..)
  , SurfaceCheckResult (..)
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
  , VerificationDisposition (..)
  , verifySurfaceApplication
  )
import System.Exit (exitFailure)

data Expectation
  = Accept
  | AcceptWithProof Proposition
  | RejectOneOf [RejectionClass]

data AuditCase = AuditCase
  { caseLabel :: String
  , caseEnvironmentPath :: FilePath
  , caseSourceName :: Text
  , caseSource :: IO Text
  , caseExpectation :: Expectation
  }

main :: IO ()
main = do
  cases <- auditCases
  results <- forM cases runCase
  if and results then pure () else exitFailure

permissivePolicy :: ApplicationAssurancePolicy
permissivePolicy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision =
      AssurancePolicyRevision "audit.digest-subject.permissive.v1"
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

runCase :: AuditCase -> IO Bool
runCase auditCase = do
  source <- caseSource auditCase
  case phase0EnvironmentFor (caseEnvironmentPath auditCase) of
    Left errorText -> failCase ("environment failure: " <> Text.unpack errorText)
    Right environment ->
      case parseSurfaceFile (caseSourceName auditCase) source of
        Left diagnostic -> failCase ("parse failure: " <> show diagnostic)
        Right (SurfaceFile [component]) -> do
          let direct = checkSurfaceComponent environment component
              intrinsic = verifySurfaceApplication
                environment permissivePolicy (caseSourceName auditCase) source
          compareResults direct intrinsic
        Right (SurfaceFile components) ->
          failCase ("unexpected component count: " <> show (length components))
  where
    label = "PHIL-AUD-DIGEST-SUBJECT-001 " <> caseLabel auditCase
    passCase = putStrLn ("PASS: " <> label) >> pure True
    failCase detail = putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

    compareResults direct intrinsic =
      case caseExpectation auditCase of
        Accept ->
          case (direct, intrinsic) of
            (Right _, ReadyForObligationClosure _ _) -> passCase
            other -> failCase ("expected public acceptance, got " <> show other)
        AcceptWithProof proposition ->
          case (direct, intrinsic) of
            (Right checked, ReadyForObligationClosure intrinsicChecked _)
              | hasReturnedProof proposition checked
              , hasReturnedProof proposition intrinsicChecked -> passCase
              | otherwise -> failCase
                  ("accepted control lost exact returned proof type: "
                    <> show (checkedTerminalControls checked,
                             checkedTerminalControls intrinsicChecked))
            other -> failCase ("expected proof-producing acceptance, got " <> show other)
        RejectOneOf classes ->
          case (direct, intrinsic) of
            (Left directError, IntrinsicRejected (IntrinsicSurfaceRejected intrinsicError))
              | directError == intrinsicError
              , surfaceErrorClass directError `elem` classes -> passCase
              | otherwise -> failCase
                  ("checker/intrinsic rejection mismatch or wrong class: "
                    <> show (directError, intrinsicError))
            other -> failCase ("invalid subject crossed public boundary: " <> show other)

hasReturnedProof :: Proposition -> SurfaceCheckResult -> Bool
hasReturnedProof proposition checked =
  Return (TyProof proposition) `elem` checkedTerminalControls checked

expectedDigestProof :: Proposition
expectedDigestProof = Atom "DigestMatches"
  [ RefVar (Name "begin")
  , RefOpaque (SortStableId "OwnedBytes") "payload"
  ]

auditCases :: IO [AuditCase]
auditCases = do
  server <- TextIO.readFile "examples/upload/server.phil"
  let needle = "validate DigestMatches on (begin, payloadView)"
      mutated = Text.replace needle "validate DigestMatches on (0, 1)" server
  if Text.count needle server /= 1 || mutated == server
    then fail "full UploadServer digest-subject mutation was not unique"
    else pure
      [ reduced "matched Begin/payload view" validReduced
          (AcceptWithProof expectedDigestProof)
      , reduced "renamed borrowed view" renamedView
          (AcceptWithProof expectedDigestProof)
      , reduced "stable owner identity survives legal move" movedOwner
          (AcceptWithProof expectedDigestProof)
      , reduced "boolean subject rejects" booleanSubject (RejectOneOf badShape)
      , reduced "unit subject rejects" unitSubject (RejectOneOf badShape)
      , reduced "reversed ordered subjects reject" reversedSubject (RejectOneOf badShape)
      , reduced "third subject rejects" thirdSubject (RejectOneOf badShape)
      , reduced "wrong second subject type rejects" wrongSecondType (RejectOneOf badShape)
      , reduced "integer pair rejects" integerPair (RejectOneOf badShape)
      , reduced "unknown view name rejects" unknownView (RejectOneOf [StructuralUse])
      , reduced "explicit context on DigestMatches rejects" explicitContext (RejectOneOf badShape)
      , AuditCase
          "missing digest evidence remains rejected"
          "examples/rejected/10-accept-before-digest-check.phil"
          "audit-digest-missing-evidence.phil"
          (TextIO.readFile "examples/rejected/10-accept-before-digest-check.phil")
          (RejectOneOf [MissingEvidence])
      , AuditCase
          "distinct valid owner cannot authorize received payload"
          "examples/rejected/10-accept-before-digest-check.phil"
          "audit-digest-distinct-owner.phil"
          (pure distinctOwner)
          (RejectOneOf [TypeMismatch, MissingEvidence])
      , AuditCase
          "complete unchanged UploadServer"
          "examples/upload/server.phil"
          "audit-upload-server-control.phil"
          (pure server)
          Accept
      , AuditCase
          "complete UploadServer integer-pair mutation rejects"
          "examples/upload/server.phil"
          "audit-upload-server-mutated.phil"
          (pure mutated)
          (RejectOneOf [TypeMismatch, MissingEvidence])
      , AuditCase
          "opaque DigestMatches still cannot be proved generically"
          "examples/rejected/18-prove-opaque-digest.phil"
          "audit-digest-opaque-proof.phil"
          (TextIO.readFile "examples/rejected/18-prove-opaque-digest.phil")
          (RejectOneOf [OpaqueProof])
      ]
  where
    badShape = [TypeMismatch, MissingEvidence]
    reduced label source expectation = AuditCase
      label
      "examples/rejected/18-prove-opaque-digest.phil"
      ("audit-" <> Text.pack (map normalize label) <> ".phil")
      (pure source)
      expectation
    normalize ' ' = '-'
    normalize '/' = '-'
    normalize ch = ch

validReduced :: Text
validReduced = proofProgram "payload" "view" "(begin, view)"

renamedView :: Text
renamedView = proofProgram "payload" "observation" "(begin, observation)"

movedOwner :: Text
movedOwner = Text.unlines
  [ "component Audit(begin, payload) {"
  , "    let owner = payload"
  , "    let result = borrow owner as view {"
  , "        validate DigestMatches on (begin, view)"
  , "    }"
  , "    decide result {"
  , "        rejected(reason) => { use(owner) return unit }"
  , "        accepted(evidence) => { use(owner) return evidence }"
  , "    }"
  , "}"
  ]

proofProgram :: Text -> Text -> Text -> Text
proofProgram owner view subject = Text.unlines
  [ "component Audit(begin, payload) {"
  , "    let result = borrow " <> owner <> " as " <> view <> " {"
  , "        validate DigestMatches on " <> subject
  , "    }"
  , "    decide result {"
  , "        rejected(reason) => { use(payload) return unit }"
  , "        accepted(evidence) => { use(payload) return evidence }"
  , "    }"
  , "}"
  ]

booleanSubject, unitSubject, reversedSubject, thirdSubject, wrongSecondType
  , integerPair, unknownView, explicitContext :: Text
booleanSubject = proofProgram "payload" "view" "true"
unitSubject = proofProgram "payload" "view" "unit"
reversedSubject = proofProgram "payload" "view" "(view, begin)"
thirdSubject = proofProgram "payload" "view" "(begin, view, unit)"
wrongSecondType = proofProgram "payload" "view" "(begin, true)"
integerPair = proofProgram "payload" "view" "(0, 1)"
unknownView = proofProgram "payload" "view" "(begin, missing)"
explicitContext = Text.unlines
  [ "component Audit(begin, payload) {"
  , "    let result = borrow payload as view {"
  , "        validate DigestMatches at begin on (begin, view)"
  , "    }"
  , "    decide result {"
  , "        rejected(reason) => { use(payload) return unit }"
  , "        accepted(evidence) => { use(payload) return evidence }"
  , "    }"
  , "}"
  ]

distinctOwner :: Text
distinctOwner = Text.unlines
  [ "component AuditDigest(begin, beginPolicy, s0, other : OwnedBytes[1024]) {"
  , "    let (s1, payload) = receive_exact begin.length on s0 using beginPolicy"
  , "    let digestResult = borrow other as view {"
  , "        validate DigestMatches on (begin, view)"
  , "    }"
  , "    use(other)"
  , "    decide digestResult {"
  , "        rejected(reason) => {"
  , "            use(payload)"
  , "            fail internal(reason) on s1"
  , "        }"
  , "        accepted(digestEvidence) => {"
  , "            decide store(payload) {"
  , "                failure(err) => { fail internal(err) on s1 }"
  , "                success(id) => {"
  , "                    let s2 = select accepted(id) on s1 using digestEvidence"
  , "                    close success"
  , "                }"
  , "            }"
  , "        }"
  , "    }"
  , "}"
  ]
