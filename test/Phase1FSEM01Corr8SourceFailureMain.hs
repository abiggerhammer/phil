{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01 CORR-8: source-checked pre-join failure prefixes, NOT source semantics.
-- Reuses the real production source/checker traces without changing Engine.hs.
module Main (main) where

import Control.Monad (forM)
import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Encoding
import qualified Data.Text.IO as TextIO
import Numeric (showHex)
import qualified Phil.Core.Context as Core
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Control (Return), Name (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine
  ( BorrowTraceCheckpoint (..), BorrowTracePhase (..)
  , SourceBranchBorrowObservation (..), SourceScopedIfJoinRun (..) )
import Phil.Surface.Check.Types
  ( RejectionClass (..), SurfaceCheckError (..), SurfaceCheckResult (..) )
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1FunctionDecl, GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..), GrammarV1Declaration (..)
  , parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceScopedBorrowJoin
  ( GrammarV1ScopedBorrowJoinTrace (..), grammarV1CheckedScopedBorrowJoinTrace )
import Phil.Surface.Syntax (Located (..))
import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath ((</>))

data Profile
  = AcceptedLeft | AcceptedBoth | EscapeLeft | EscapeRight | EscapeAlias
  | MoveWhileLoaned | ReturnInsideLoan | BorrowUnrestricted
  deriving (Eq, Show)

profiles :: [Profile]
profiles =
  [ AcceptedLeft, AcceptedBoth, EscapeLeft, EscapeRight, EscapeAlias
  , MoveWhileLoaned, ReturnInsideLoan, BorrowUnrestricted ]

fixture :: Profile -> String
fixture AcceptedLeft = "accepted-left"
fixture AcceptedBoth = "accepted-both"
fixture EscapeLeft = "escape-left"
fixture EscapeRight = "escape-right"
fixture EscapeAlias = "escape-alias"
fixture MoveWhileLoaned = "move-while-loaned"
fixture ReturnInsideLoan = "return-inside-borrow"
fixture BorrowUnrestricted = "borrow-unrestricted"

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.scoped-loan-join.choose"

rootText :: Text
rootText = "decl.fsem01.scoped-loan-join.choose"

bytes8 :: Ty
bytes8 = TyBytes (RefNat 8)

check :: Bool -> String -> Either String ()
check ok reason = if ok then Right () else Left reason

parseSource :: Text -> Either String GrammarV1FunctionDecl
parseSource source = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "corr8-source" source)
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1FunctionDeclaration fn -> Right fn
      other -> Left ("not a function: " ++ show other)
    other -> Left ("not one declaration: " ++ show (length other))

checked :: Text -> Either String GrammarV1ScopedBorrowJoinTrace
checked source = do
  fn <- parseSource source
  case grammarV1CheckedScopedBorrowJoinTrace emptyStaticContext root fn of
    Just (Right trace) -> Right trace
    other -> Left ("source checker out of exact fragment: " ++ show other)

binderName :: GrammarV1ResolvedBinder -> Name
binderName = grammarV1ResolvedBinderCoreName

expectedInitial :: GrammarV1ScopedBorrowJoinTrace -> Core.ResourceContext
expectedInitial trace = Core.ResourceContext
  (Map.singleton (binderName (scopedBorrowJoinFlagBinder trace)) TyBool)
  Map.empty
  (Map.singleton (binderName (scopedBorrowJoinPayloadBinder trace)) bytes8)
  Set.empty

phaseChar :: BorrowTracePhase -> Text
phaseChar TraceBeforeLoan = "B"
phaseChar TraceLoanStarted = "S"
phaseChar (TraceBodyResult False) = "V"
phaseChar (TraceBodyResult True) = "E"
phaseChar TraceEscapeRejected = "X"
phaseChar TraceLoanClosed = "C"
phaseChar TraceOwnerReturned = "R"

phaseWord :: Maybe SourceBranchBorrowObservation -> Text
phaseWord Nothing = "-"
phaseWord (Just obs) =
  Text.concat (map (phaseChar . tracePhase) (sourceBranchBorrowCuts obs))

checkObserved :: Name -> Maybe SourceBranchBorrowObservation -> Either String ()
checkObserved _ Nothing = Right ()
checkObserved owner (Just obs) =
  check (all ((== owner) . traceOwnerName) (sourceBranchBorrowCuts obs))
    "loan observation silently changed the checked source owner"

profileExpectation :: Profile -> (Text,Text,Int,Int,Text)
profileExpectation AcceptedLeft = ("BSVC","-",1,1,"JOIN_OK")
profileExpectation AcceptedBoth = ("BSVC","BSVC",1,1,"JOIN_OK")
profileExpectation EscapeLeft = ("BSEX","-",0,0,"SOURCE_BORROW")
profileExpectation EscapeRight = ("-","BSEX",1,0,"SOURCE_BORROW")
profileExpectation EscapeAlias = ("BSEX","-",0,0,"SOURCE_BORROW")
profileExpectation MoveWhileLoaned = ("BS","-",0,0,"SOURCE_STRUCTURAL")
-- The return prefix is checked by its owner-start, no-loan-close and
-- native LinearCompletion class; it is not asserted to be a generic loop.
profileExpectation ReturnInsideLoan = ("BSR","-",0,0,"SOURCE_LINEAR")
profileExpectation BorrowUnrestricted = ("B","-",0,0,"SOURCE_BORROW")

outcomeTag :: Either SurfaceCheckError SurfaceCheckResult -> Text
outcomeTag (Right _) = "JOIN_OK"
outcomeTag (Left err) = case surfaceErrorClass err of
  BorrowEscape -> "SOURCE_BORROW"
  StructuralUse -> "SOURCE_STRUCTURAL"
  LinearCompletion -> "SOURCE_LINEAR"
  _ -> "UNSUPPORTED_FAILURE"

sourceWire :: Profile -> BS.ByteString -> GrammarV1ScopedBorrowJoinTrace
  -> Either String Text
sourceWire profile raw trace = do
  let run = scopedBorrowJoinRun trace
      owner = binderName (scopedBorrowJoinPayloadBinder trace)
      flag = binderName (scopedBorrowJoinFlagBinder trace)
      left = scopedBorrowJoinThenLoan trace
      right = scopedBorrowJoinElseLoan trace
      firstCount = length (scopedIfJoinThenPruned run)
      secondCount = length (scopedIfJoinElsePruned run)
      produced = (phaseWord left,phaseWord right,firstCount,secondCount,
                  outcomeTag (scopedBorrowJoinOutcome trace))
      expected = profileExpectation profile
      initial = expectedInitial trace
  check (produced == expected)
    ("wrong source/checker failure prefix " ++ fixture profile ++ ": " ++ show produced)
  check (scopedIfJoinBefore run == Just initial &&
         scopedIfJoinOutcome run == scopedBorrowJoinOutcome trace &&
         owner /= flag)
    "source initial resource state or trace/ordinary checker parity changed"
  checkObserved (if profile == BorrowUnrestricted then flag else owner) left
  checkObserved owner right
  case profile of
    AcceptedLeft -> accepted run trace
    AcceptedBoth -> accepted run trace
    _ -> do
      check (scopedIfJoinJoined run == Nothing &&
             null (scopedIfJoinElseRaw run))
        "source failure fabricated a completed joined/second-branch state"
      case scopedBorrowJoinOutcome trace of
        Left err -> do
          let observation = if profile == EscapeRight then right else left
          case observation of
            Nothing -> Left "no actual failed-source loan observation"
            Just obs -> check (sourceBranchBorrowOutcome obs == Left err)
              "original error differs between production observer and checker"
        Right _ -> Left "rejected source incorrectly admitted"
  let fields =
        [ hexBytes (SHA256.hash raw)
        , hexBytes (Encoding.encodeUtf8 rootText)
        , hexBytes (Encoding.encodeUtf8 (unName flag))
        , hexBytes (Encoding.encodeUtf8 (unName owner))
        , Text.pack (fixture profile)
        , phaseWord left,phaseWord right
        , Text.pack (show firstCount),Text.pack (show secondCount)
        , outcomeTag (scopedBorrowJoinOutcome trace) ]
      pack value = Text.pack (show (Text.length value)) <> ":" <> value
  Right ("PHIL-FSEM01-CORR8-V1|" <> Text.concat (map pack fields))
  where
    accepted run t =
      check (scopedIfJoinJoined run == Just (expectedInitial t) &&
        scopedIfJoinThenPruned run == [expectedInitial t] &&
        scopedIfJoinElsePruned run == [expectedInitial t] &&
        scopedBorrowJoinOutcome t ==
          Right (SurfaceCheckResult "choose" [Return bytes8]))
        "accepted source did not keep exact joined Linear owner and terminal return"

hexBytes :: BS.ByteString -> Text
hexBytes = Text.pack . concatMap encode . BS.unpack
  where
    encode n = let digits = showHex n ""
               in if length digits == 1 then '0' : digits else digits

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> run Nothing
    ["--emit", dir] -> run (Just dir)
    _ -> putStrLn "usage: Phase1FSEM01Corr8SourceFailureMain [--emit DIR]"
      >> exitFailure
  where
    run destination = do
      result <- forM profiles $ \profile -> do
        raw <- BS.readFile
          ("test/fixtures/fsem01-scoped-borrow-join-v1/" ++ fixture profile ++ ".phil")
        let source = either (Left . show) Right (Encoding.decodeUtf8' raw)
            wire = source >>= checked >>= sourceWire profile raw
        pure (fixture profile,wire)
      case sequence [fmap ((,) name) wire | (name,wire) <- result] of
        Left why -> putStrLn ("FAIL CORR-8: " ++ why) >> exitFailure
        Right verified -> do
          case destination of
            Nothing -> pure ()
            Just dir -> do
              createDirectoryIfMissing True dir
              mapM_ (\(name,wire) ->
                TextIO.writeFile (dir </> (name ++ ".fail")) wire) verified
          putStrLn "PASS CORR-8: eight actual source/checker failure prefixes, exact owner identities and no fabricated continuation"
