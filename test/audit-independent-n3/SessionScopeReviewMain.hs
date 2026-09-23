{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.Monad (replicateM, unless)
import Data.List (findIndex)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Context (ResourceContext (..), emptyContext, insertBinding)
import Phil.Core.Recognition
  ( ParsedWitness, beginRawLoan, receiveFrame, receiveFrameContext
  , trustedRecognitionSuccess, recognizedOccurrenceTerm, parsedFrameId, parsedValueName )
import Phil.Core.Session
  ( SessionStep (..), sendEndpoint, receiveEndpoint, instantiateMessageStep )
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax
  ( Branch (..), Control (..), FrameId (..), GrammarId (..), Mode (..)
  , Name (..), Outcome (..), Proposition (..), RefTerm (..), Session (..), Ty (..) )
import Phil.Core.Value (definitionallyEqualSession)
import Phil.Surface.Check
  ( InitialBinding (..), RejectionClass (..), SurfaceCheckError (..)
  , SurfaceCheckResult (..), SurfaceEnvironment (..), SurfaceShape (..)
  , checkSurfaceComponent, emptySurfaceEnvironment )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax (SurfaceFile (..))
import System.Exit (exitFailure)

end :: Session
end = End (Outcome "success")
trueBool :: Ty
trueBool = TyRefined (Name "v") TyBool (Equal (RefVar (Name "v")) (RefBool True))

-- Independent finite oracle: compare nearest lexical binder depth, or exact
-- free spelling. This does not reimplement the production paired environment.
lexicalIdentity :: [Name] -> Name -> Either Name Int
lexicalIdentity binders subject = maybe (Left subject) Right
  (findIndex (== subject) (reverse binders))
finiteSession :: [Name] -> Name -> Session
finiteSession binders subject = foldr (\n s -> Receive n (TyUInt 16) s)
  (Send (Name "bytes") (TyBytes (RefToNat (RefVar subject))) end) binders

alphaOracle :: Either String ()
alphaOracle = case take 1
  [ (left, right, a, b, expected, actual)
  | depth <- [0 .. 4]
  , left <- replicateM depth alphabet
  , right <- replicateM depth alphabet
  , a <- subjects
  , b <- subjects
  , let expected = lexicalIdentity left a == lexicalIdentity right b
        actual = definitionallyEqualSession (finiteSession left a) (finiteSession right b)
  , actual /= expected
  ] of
    [] -> Right ()
    mismatch -> Left ("finite lexical oracle mismatch: " ++ show mismatch)
  where
    alphabet = map Name ["a", "b", "c"]
    subjects = alphabet ++ [Name "z"]

messageComposition :: Either String ()
messageComposition = do
  let continuation = Receive (Name "x") (TyUInt 16) $
        Send (Name "bytes") (TyBytes (RefToNat (RefVar (Name "formal")))) end
      protocol = Send (Name "formal") (TyUInt 16) continuation
      expected = Receive (Name "inner") (TyUInt 16) $
        Send (Name "bytes") (TyBytes (RefToNat (RefVar (Name "x")))) end
      captured = Receive (Name "x") (TyUInt 16) $
        Send (Name "bytes") (TyBytes (RefToNat (RefVar (Name "x")))) end
  outer <- checked $ insertBinding Unrestricted (Name "x") (TyUInt 16) emptyContext
  initial <- checked $ insertBinding Linear (Name "ep") (TyEndpoint protocol) outer
  descriptor <- checked $ sendEndpoint (Name "ep") (Name "next") initial
  rebound <- checked $ instantiateMessageStep (Just (RefVar (Name "x"))) descriptor
  actual <- case stepSuccessor rebound of
    Just (Name "next", value) -> Right value
    other -> Left ("wrong successor: " ++ show other)
  assert (definitionallyEqualSession actual expected) "actual occurrence was not retained free"
  assert (not (definitionallyEqualSession actual captured)) "actual occurrence captured by later binder"
  assert (Map.lookup (Name "next") (linearBindings (stepContext rebound)) == Just (TyEndpoint actual))
    "returned successor and context disagree"
  assert (Map.notMember (Name "ep") (linearBindings (stepContext rebound))) "source endpoint resurrected"
  nextDescriptor <- checked $ receiveEndpoint (Name "next") (Name "next2") (stepContext rebound)
  next <- checked $ instantiateMessageStep (Just (RefVar (Name "received"))) nextDescriptor
  case stepSuccessor next of
    Just (_, Send _ (TyBytes index) _) ->
      assert (index == RefToNat (RefVar (Name "x"))) "next message rebound the preceding actual"
    other -> Left ("unexpected next operation: " ++ show other)

baseEnv :: SurfaceEnvironment
baseEnv = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceInitialBindings = Map.fromList
      [ ("good", InitialBinding Unrestricted trueBool PlainShape)
      , ("flag", InitialBinding Unrestricted TyBool PlainShape)
      , ("ctx", InitialBinding Unrestricted (TyOpaque "Context") PlainShape)
      , ("ep", InitialBinding Linear (TyEndpoint (Select
          [Branch "proceed" Nothing end, Branch "reject" Nothing end])) PlainShape)
      ]
  , surfaceSelectRequirements = Map.singleton "proceed"
      [Atom "IsTrue" [RefVar (Name "ctx"), RefVar (Name "x")]]
  }

sourceCheck :: SurfaceEnvironment -> Text -> Either String (Either SurfaceCheckError SurfaceCheckResult)
sourceCheck env source = case parseSurfaceFile "session-scope-independent.phil" source of
  Left diagnostic -> Left ("SETUP parse: " ++ show diagnostic)
  Right (SurfaceFile [component]) -> Right (checkSurfaceComponent env component)
  Right other -> Left ("SETUP component count: " ++ show other)

closed :: Either SurfaceCheckError SurfaceCheckResult -> Either String ()
closed (Right result) = assert
  (not (null (checkedTerminalControls result)) &&
   all (== Closed (Outcome "success")) (checkedTerminalControls result))
  ("unexpected terminal controls: " ++ show result)
closed other = Left ("expected closed source: " ++ show other)

scopeRejected :: Either SurfaceCheckError SurfaceCheckResult -> Either String ()
scopeRejected (Left err) = assert
  (surfaceErrorClass err == TypeMismatch &&
   "branch result depends on out-of-scope subject(s):" `Text.isPrefixOf` surfaceErrorDetail err)
  ("wrong rejection boundary: " ++ show err)
scopeRejected other = Left ("scope exit admitted unsupported value: " ++ show other)

finish :: [Text]
finish =
  [ "let ep1 = decide decision {"
  , " accepted(e) => { select proceed on ep using e }"
  , " rejected(reason) => { select reject on ep }"
  , "}"
  , "close ep1"
  ]

carrierSource :: Bool -> Text
carrierSource tuple = Text.unlines $
  [ "component Audit {"
  , if tuple then "let (decision, marker) = decide flag {" else "let decision = decide flag {"
  , " true => { let x = good"
  , if tuple then " (validate IsTrue at ctx on x, unit) }" else " validate IsTrue at ctx on x }"
  , " false => { let x = good"
  , if tuple then " (validate IsTrue at ctx on x, unit) }" else " validate IsTrue at ctx on x }"
  , "}"
  , "let x = false"
  ] ++ finish ++ ["}"]

sourceControls :: [(String, Either String ())]
sourceControls =
  [ ("S01-characterization-delayed-evidence", sourceCheck baseEnv (carrierSource False) >>= closed)
  , ("S02-characterization-tuple-decision", sourceCheck baseEnv (carrierSource True) >>= closed)
  , ("S03-materialized-proof-scope-guard", do
      let source = Text.unlines
            [ "component Audit {"
            , "let evidence = decide flag {"
            , " true => { let x = good"
            , " prove x == true }"
            , " false => { let x = good"
            , " prove x == true }"
            , "}"
            , "close ep"
            , "}" ]
      sourceCheck baseEnv source >>= scopeRejected)
  , ("S04-outer-subject-decision-valid", do
      let source = Text.unlines $
            [ "component Audit {", "let x = good"
            , "let decision = decide flag {"
            , " true => { validate IsTrue at ctx on x }"
            , " false => { validate IsTrue at ctx on x }"
            , "}" ] ++ finish ++ ["}"]
      sourceCheck baseEnv source >>= closed)
  , ("S05-distinct-required-subject-rejects", do
      let env = baseEnv
            { surfaceSelectRequirements = Map.singleton "proceed"
                [Atom "IsTrue" [RefVar (Name "ctx"), RefVar (Name "y")]] }
          source = Text.replace "let x = false" "let x = false\nlet y = false" (carrierSource False)
      result <- sourceCheck env source
      case result of
        Left err | surfaceErrorClass err == MissingEvidence -> Right ()
        other -> Left ("different subject was authorized: " ++ show other))
  , ("S06-closed-boolean-carrier-valid", do
      let source = Text.unlines
            [ "component Audit {"
            , "let decision = decide flag { true => { true } false => { false } }"
            , "let ep1 = decide decision {"
            , " true => { select reject on ep }"
            , " false => { select reject on ep }"
            , "}"
            , "close ep1"
            , "}" ]
      sourceCheck baseEnv source >>= closed)
  ]

-- Raw supplied-context observation. This is NOT a Surface-admission claim:
-- Surface generates its own restricted frame/value-name domain.
makeWitness :: FrameId -> Name -> Either String ParsedWitness
makeWitness frame valueName = do
  initial <- checked $ insertBinding Linear (Name "ep")
    (TyEndpoint (Receive (Name "formal") (TyFrame (GrammarId "G")) end)) emptyContext
  step <- checked $ receiveFrame (Name "ep") (Name "pending") frame initial
  (raw, loaned) <- checked $ beginRawLoan (Name "pending") (receiveFrameContext step)
  checked $ trustedRecognitionSuccess raw valueName loaned

occurrenceObservation :: Either String String
occurrenceObservation = do
  left <- makeWitness (FrameId "f:a") (Name "b")
  right <- makeWitness (FrameId "f") (Name "a:b")
  assert ((parsedFrameId left, parsedValueName left) /= (parsedFrameId right, parsedValueName right))
    "SETUP: provenance tuples unexpectedly equal"
  ordinary <- makeWitness (FrameId "different") (Name "b")
  assert (recognizedOccurrenceTerm left /= recognizedOccurrenceTerm ordinary)
    "ordinary distinct occurrence control failed"
  Right (show (recognizedOccurrenceTerm left == recognizedOccurrenceTerm right,
    recognizedOccurrenceTerm left, recognizedOccurrenceTerm right))

main :: IO ()
main = do
  putStrLn "MODE characterization: S01/S02 PASS records the existing scope gap, not corrected behavior"
  results <- mapM run $ [("A01-finite-lexical-oracle-118096-pairs", alphaOracle),
    ("M01-message-substitution-next-consumer", messageComposition)] ++ sourceControls
  observation <- case occurrenceObservation of
    Right value -> putStrLn ("OBS Q01 RAW_CONTEXT " ++ value) >> pure True
    Left detail -> putStrLn ("OBS Q01 SETUP_ERROR " ++ detail) >> pure False
  unless (and results && observation) exitFailure
  where
    run (ident, result) = case result of
      Right () -> putStrLn ("CHECK " ++ ident ++ " PASS") >> pure True
      Left detail -> putStrLn ("CHECK " ++ ident ++ " FAIL " ++ detail) >> pure False

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail
checked :: Show e => Either e a -> Either String a
checked = either (Left . ("SETUP/operation: " ++) . show) Right
