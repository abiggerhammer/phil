{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (forM)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Phil.Core.Context as Context
import Phil.Core.Recognition
  ( CommitReceiveStep (..)
  , RecognitionError (..)
  , beginRawLoan
  , commitReceive
  , endRawLoan
  , receiveFrame
  , receiveFrameContext
  , recognizedOccurrenceTerm
  , trustedRecognitionSuccess
  )
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Branch (..)
  , FrameId (..)
  , GrammarId (..)
  , Mode (..)
  , Name (..)
  , Outcome (..)
  , RefSort (..)
  , RefTerm (..)
  , Session (..)
  , Ty (..)
  )
import Phil.Surface.Check
  ( InitialBinding (..)
  , PrimitiveSemantics (..)
  , RejectionClass (..)
  , SurfaceCheckError (..)
  , SurfaceEnvironment (..)
  , SurfaceShape (..)
  , checkSurfaceComponent
  , emptySurfaceEnvironment
  )
import Phil.Surface.Check.Support (recordShape)
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax (SurfaceFile (..))
import Phil.Verification
  ( ApplicationAssurancePolicy (..)
  , ApplicationVerificationResult (..)
  , AssurancePolicyRevision (..)
  , IntrinsicRejection (..)
  , verifySurfaceApplication
  )
import System.Exit (exitFailure)

-- Permanent replay for the recognition/commit extension of
-- PHIL-AUD-SESSION-CONTINUATION-BINDING-001.
--
-- The central invariant is that the frame occurrence recognized from one
-- pending receive determines both (1) aliases projected from parsed.value and
-- (2) the dependent continuation installed by commit_receive.  Source spelling
-- is presentation only; an unrelated ambient Begin must not satisfy the
-- dependency, while any alias of the recognized value must.

data Expectation = Accept | Reject RejectionClass

data AuditCase = AuditCase
  { caseId :: Text
  , caseSession :: Session
  , caseAmbientBegin :: Bool
  , caseSource :: Text
  , caseExpectation :: Expectation
  }

success :: Outcome
success = Outcome "success"

beginGrammar :: GrammarId
beginGrammar = GrammarId "Begin"

end :: Session
end = End success

frameLength :: RefTerm -> RefTerm
frameLength frame = RefToNat (RefField frame "length" (SortUInt 64))

dependentSession :: Session
dependentSession =
  Receive (Name "frame") (TyFrame beginGrammar) $
    Receive (Name "body") (TyBytes (frameLength (RefVar (Name "frame")))) end

fixedSession :: Session
fixedSession =
  Receive (Name "frame") (TyFrame beginGrammar) $
    Receive (Name "body") (TyBytes (RefNat 7)) end

recursiveSession :: Session
recursiveSession = Rec (Name "R") $
  Receive (Name "frame") (TyFrame beginGrammar) $
    Receive (Name "body") (TyBytes (frameLength (RefVar (Name "frame")))) $
      Select
        [ Branch "again" Nothing (SessionVar (Name "R"))
        , Branch "done" Nothing end
        ]

policy :: ApplicationAssurancePolicy
policy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision =
      AssurancePolicyRevision "audit.recognition-continuation-binding.v1"
  , applicationAssurancePolicyPermittedDispositions = Set.empty
  }

caseEnvironment :: AuditCase -> SurfaceEnvironment
caseEnvironment auditCase = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceInitialBindings = Map.fromList $
      [ ( "session0"
        , InitialBinding Linear (TyEndpoint (caseSession auditCase)) PlainShape
        )
      ]
      <> if caseAmbientBegin auditCase
        then
          [ ( "begin"
            , InitialBinding
                Unrestricted
                (TyFrame beginGrammar)
                (recordShape "Begin" (Just "begin"))
            )
          ]
        else []
  , surfacePrimitives = Map.singleton "use" PrimitiveUse
  , surfaceExpectedProvides = Nothing
  }

runSourceCase :: AuditCase -> IO Bool
runSourceCase auditCase =
  case parseSurfaceFile (caseId auditCase <> ".phil") (caseSource auditCase) of
    Left diagnostic -> failCase ("parse failure: " <> show diagnostic)
    Right (SurfaceFile [component]) -> do
      let environment = caseEnvironment auditCase
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
    label = "PHIL-AUD-SESSION-CONTINUATION-BINDING-001 " <> Text.unpack (caseId auditCase)
    passCase = putStrLn ("PASS: " <> label) >> pure True
    failCase detail = putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

    compareResults direct intrinsic = case caseExpectation auditCase of
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
        other -> failCase ("invalid occurrence alias crossed public boundary: " <> show other)

singleRecognition :: Text -> Text -> Text
singleRecognition valueName count = Text.unlines
  [ "component Audit() {"
  , "    let pending = receive_frame(session0)"
  , "    let result = borrow pending as raw {"
  , "        recognize Begin from raw"
  , "    }"
  , "    decide result {"
  , "        accepted(parsed) => {"
  , "            let " <> valueName <> " = parsed.value"
  , "            let session1 = commit_receive pending using parsed"
  , "            let (session2, payload) = receive OwnedBytes[" <> count <> "] on session1"
  , "            use(payload)"
  , "            close session2"
  , "        }"
  , "        rejected(reason) => {"
  , "            fail recognition(reason) on pending"
  , "        }"
  , "    }"
  , "}"
  ]

aliasedRecognition :: Text
aliasedRecognition = Text.unlines
  [ "component Audit() {"
  , "    let pending = receive_frame(session0)"
  , "    let result = borrow pending as raw {"
  , "        recognize Begin from raw"
  , "    }"
  , "    decide result {"
  , "        accepted(parsed) => {"
  , "            let got = parsed.value"
  , "            let alias = got"
  , "            let session1 = commit_receive pending using parsed"
  , "            let (session2, payload) = receive OwnedBytes[alias.length] on session1"
  , "            use(payload)"
  , "            close session2"
  , "        }"
  , "        rejected(reason) => {"
  , "            fail recognition(reason) on pending"
  , "        }"
  , "    }"
  , "}"
  ]

recursiveRecognition :: Bool -> Text
recursiveRecognition stale = Text.unlines
  [ "component Audit() {"
  , "    let pending1 = receive_frame(session0)"
  , "    let result1 = borrow pending1 as raw1 {"
  , "        recognize Begin from raw1"
  , "    }"
  , "    decide result1 {"
  , "        accepted(parsed1) => {"
  , "            let got1 = parsed1.value"
  , "            let session1 = commit_receive pending1 using parsed1"
  , "            let (session2, payload1) = receive OwnedBytes[got1.length] on session1"
  , "            use(payload1)"
  , "            let session3 = select again on session2"
  , "            let pending2 = receive_frame(session3)"
  , "            let result2 = borrow pending2 as raw2 {"
  , "                recognize Begin from raw2"
  , "            }"
  , "            decide result2 {"
  , "                accepted(parsed2) => {"
  , "                    let got2 = parsed2.value"
  , "                    let session4 = commit_receive pending2 using parsed2"
  , "                    let (session5, payload2) = receive OwnedBytes["
      <> (if stale then "got1.length" else "got2.length") <> "] on session4"
  , "                    use(payload2)"
  , "                    let session6 = select done on session5"
  , "                    close session6"
  , "                }"
  , "                rejected(reason2) => {"
  , "                    fail recognition(reason2) on pending2"
  , "                }"
  , "            }"
  , "        }"
  , "        rejected(reason1) => {"
  , "            fail recognition(reason1) on pending1"
  , "        }"
  , "    }"
  , "}"
  ]

sourceCases :: [AuditCase]
sourceCases =
  [ AuditCase "S01-recognized-alias" dependentSession False
      (singleRecognition "got" "got.length") Accept
  , AuditCase "S02-ambient-spelling" dependentSession True
      (singleRecognition "got" "begin.length") (Reject TypeMismatch)
  , AuditCase "S03-conventional-name" dependentSession False
      (singleRecognition "begin" "begin.length") Accept
  , AuditCase "S04-fixed-continuation" fixedSession False
      (singleRecognition "got" "7") Accept
  , AuditCase "S05-second-alias" dependentSession False
      aliasedRecognition Accept
  , AuditCase "R01-recursive-fresh-occurrence" recursiveSession False
      (recursiveRecognition False) Accept
  , AuditCase "R02-recursive-stale-occurrence" recursiveSession False
      (recursiveRecognition True) (Reject TypeMismatch)
  ]

coreDependentCommit :: Either String ()
coreDependentCommit = do
  let endpoint = Name "ep"
      pendingName = Name "pending"
      successor = Name "ep1"
      frame = FrameId "frame-1"
  context0 <- mapLeft show $
    Context.insertBinding Linear endpoint (TyEndpoint dependentSession) Context.emptyContext
  received <- mapLeft show $ receiveFrame endpoint pendingName frame context0
  (raw, loaned) <- mapLeft show $ beginRawLoan pendingName (receiveFrameContext received)
  parsed <- mapLeft show $
    trustedRecognitionSuccess raw (Name "$parsed-Begin") loaned
  unloaned <- mapLeft show $ endRawLoan raw loaned
  committed <- mapLeft show $ commitReceive pendingName successor parsed unloaned
  let expected = Receive
        (Name "body")
        (TyBytes (frameLength (recognizedOccurrenceTerm parsed)))
        end
  if commitSuccessor committed == (successor, expected)
    then Right ()
    else Left ("dependent commit installed wrong continuation: " <> show committed)

coreFixedCommit :: Either String ()
coreFixedCommit = do
  let endpoint = Name "ep"
      pendingName = Name "pending"
      successor = Name "ep1"
      frame = FrameId "frame-1"
  context0 <- mapLeft show $
    Context.insertBinding Linear endpoint (TyEndpoint fixedSession) Context.emptyContext
  received <- mapLeft show $ receiveFrame endpoint pendingName frame context0
  (raw, loaned) <- mapLeft show $ beginRawLoan pendingName (receiveFrameContext received)
  parsed <- mapLeft show $
    trustedRecognitionSuccess raw (Name "$parsed-Begin") loaned
  unloaned <- mapLeft show $ endRawLoan raw loaned
  committed <- mapLeft show $ commitReceive pendingName successor parsed unloaned
  let expected = Receive (Name "body") (TyBytes (RefNat 7)) end
  if commitSuccessor committed == (successor, expected)
    then Right ()
    else Left ("fixed commit changed continuation: " <> show committed)

runCore :: String -> Either String () -> IO Bool
runCore ident action = case action of
  Right () -> putStrLn ("PASS: PHIL-AUD-SESSION-CONTINUATION-BINDING-001 " <> ident) >> pure True
  Left detail -> putStrLn ("FAIL: PHIL-AUD-SESSION-CONTINUATION-BINDING-001 " <> ident <> " -- " <> detail) >> pure False

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

main :: IO ()
main = do
  surfaceResults <- forM sourceCases runSourceCase
  coreResults <- sequence
    [ runCore "C01-core-dependent-commit" coreDependentCommit
    , runCore "C02-core-fixed-commit" coreFixedCommit
    ]
  if and (surfaceResults <> coreResults) then pure () else exitFailure
