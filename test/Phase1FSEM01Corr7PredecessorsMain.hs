{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01 CORR-7 / J-4: real Grammar-v1 predecessor checkpoints and
-- independently computed, globally ordered finite Core join decisions.
-- A terminal source arm never becomes an empty Core successor.
module Main (main) where

import Control.Monad (foldM, forM_)
import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.ByteString as BS
import Data.List (find)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Encoding
import qualified Data.Text.IO as TextIO
import Numeric (showHex)
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import qualified Phil.Core.Context as Core
import Phil.Core.Syntax (Control (Return), Name (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine (SourceIfJoinRun (..))
import Phil.Surface.Check.Types
  ( RejectionClass (..), SurfaceCheckError (..), SurfaceCheckResult (..) )
import Phil.Surface.GrammarV1.BinderScope (GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1FunctionDecl, GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..), GrammarV1Declaration (..)
  , parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceIfJoinResource
  ( GrammarV1SourceIfJoinTrace (..), grammarV1CheckedSourceIfJoinTrace )
import Phil.Surface.Syntax (Located (..))
import System.Directory (createDirectoryIfMissing)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.FilePath ((</>))

data Finite = Finite
  { finiteU :: [(Name,Ty)]
  , finiteA :: [(Name,Ty)]
  , finiteL :: [(Name,Ty)]
  , finiteLoans :: [Name]
  } deriving (Eq,Show)

project :: Core.ResourceContext -> Finite
project c = Finite
  (Map.toAscList (Core.unrestrictedBindings c))
  (Map.toAscList (Core.affineBindings c))
  (Map.toAscList (Core.linearBindings c))
  (Set.toAscList (Core.sharedLoans c))

reify :: Finite -> Core.ResourceContext
reify s = Core.ResourceContext
  (Map.fromList (finiteU s))
  (Map.fromList (finiteA s))
  (Map.fromList (finiteL s))
  (Set.fromList (finiteLoans s))

check :: Bool -> String -> Either String ()
check ok why = if ok then Right () else Left why

validate :: Finite -> Either String ()
validate s =
  let zones = [finiteU s,finiteA s,finiteL s]
      keys = concatMap (map fst) zones
      restricted = map fst (finiteA s ++ finiteL s)
      ascending xs = and (zipWith (<) xs (drop 1 xs))
  in check (all (ascending . map fst) zones
    && ascending (finiteLoans s)
    && Set.size (Set.fromList keys) == length keys
    && all (\x -> elem x restricted) (finiteLoans s))
    "noncanonical duplicate/orphaned finite resource context"

-- All loan checks precede every U check; all U checks precede every
-- Linear check; Affine filtering is left-to-right and cannot resurrect
-- a binding dropped by any earlier predecessor.
finiteMany :: [Finite] -> Either Core.CheckError (Maybe Finite)
finiteMany [] = Right Nothing
finiteMany allStates@(first : rest)
  | Just bad <- find (not . null . finiteLoans) allStates =
      Left (Core.EscapingLoans (Set.fromList (finiteLoans bad)))
  | Just bad <- find ((/= finiteU first) . finiteU) rest =
      Left (Core.UnrestrictedBranchMismatch
        (Map.fromList (finiteU first)) (Map.fromList (finiteU bad)))
  | Just bad <- find ((/= finiteL first) . finiteL) rest =
      Left (Core.LinearBranchMismatch
        (Map.fromList (finiteL first)) (Map.fromList (finiteL bad)))
  | otherwise = do
      affine <- foldM intersect (finiteA first) (map finiteA rest)
      Right (Just (Finite (finiteU first) affine (finiteL first) []))
  where
    intersect carried next =
      case [ (name,leftTy,rightTy)
           | (name,leftTy) <- carried
           , Just rightTy <- [lookup name next]
           , leftTy /= rightTy ] of
        (name,leftTy,rightTy) : _ ->
          Left (Core.AffineBranchTypeMismatch name leftTy rightTy)
        [] -> Right
          [ (name,ty) | (name,ty) <- carried, lookup name next == Just ty ]

data Path = Continue Core.ResourceContext | Terminal | SourceFailure String

data Decision
  = NoContinuation
  | Joined Core.ResourceContext
  | Rejected Core.CheckError
  | FailedBeforeJoin String
  deriving (Eq,Show)

predict :: [Path] -> Decision
predict paths =
  case [reason | SourceFailure reason <- paths] of
    reason : _ -> FailedBeforeJoin reason
    [] -> case finiteMany [project c | Continue c <- paths] of
      Left err -> Rejected err
      Right Nothing -> NoContinuation
      Right (Just success) -> Joined (reify success)

compareNative :: String -> [Core.ResourceContext] -> Either String ()
compareNative label states = do
  forM_ states (validate . project)
  computed <- case finiteMany (map project states) of
    Left err -> Right (Left err)
    Right (Just result) -> do
      validate result
      Right (Right (reify result))
    Right Nothing -> Left "empty source predecessor collection has no Core join"
  check (Core.joinContinuing states == computed)
    (label ++ ": finite global-priority decision differs from native Core")

data Profile = BothContinue | LinearMismatch | SiblingMismatch
  | OneContinue | OneStale | AllTerminal
  deriving (Eq,Show)

fixture :: Profile -> String
fixture BothContinue = "accepted"
fixture LinearMismatch = "linear-mismatch"
fixture SiblingMismatch = "two-local-owners"
fixture OneContinue = "terminal-excluded"
fixture OneStale = "terminal-stale"
fixture AllTerminal = "terminal-both"

profileTag :: Profile -> Text
profileTag = Text.pack . fixture

outcomeTag :: Profile -> Text
outcomeTag BothContinue = "JOIN_OK"
outcomeTag LinearMismatch = "JOIN_LINEAR"
outcomeTag SiblingMismatch = "JOIN_LINEAR"
outcomeTag OneContinue = "JOIN_ONE"
outcomeTag OneStale = "POST_STALE"
outcomeTag AllTerminal = "NO_CONT"

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.j1j2.choose"

bytes8 :: Ty
bytes8 = TyBytes (RefNat 8)

directory :: FilePath
directory = "test/fixtures/fsem01-source-branch-join-v1/"

parseSource :: Text -> Either String GrammarV1FunctionDecl
parseSource source = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "corr7-source" source)
  case grammarV1TopLevelDecls parsed of
    [Located _ decl] ->
      case locatedValue (grammarV1Declaration decl) of
        GrammarV1FunctionDeclaration fn -> Right fn
        other -> Left ("not a function declaration: " ++ show other)
    other -> Left ("not one source declaration: " ++ show (length other))

sourceTrace :: Text -> Either String GrammarV1SourceIfJoinTrace
sourceTrace source = do
  fn <- parseSource source
  case grammarV1CheckedSourceIfJoinTrace emptyStaticContext root fn of
    Just (Right trace) -> Right trace
    other -> Left ("source checker did not produce real trace: " ++ show other)

binder :: GrammarV1ResolvedBinder -> Name
binder = grammarV1ResolvedBinderCoreName

expectedStart :: GrammarV1SourceIfJoinTrace -> Core.ResourceContext
expectedStart trace = Core.ResourceContext
  (Map.singleton (binder (sourceIfJoinFlagBinder trace)) TyBool)
  Map.empty
  (Map.singleton (binder (sourceIfJoinPayloadBinder trace)) bytes8)
  Set.empty

checkSource :: Profile -> GrammarV1SourceIfJoinTrace -> Either String ()
checkSource profile trace = do
  let run = sourceIfJoinBranchRun trace
      start = expectedStart trace
      flag = binder (sourceIfJoinFlagBinder trace)
      payload = binder (sourceIfJoinPayloadBinder trace)
  check (sourceIfJoinBefore run == Just start
      && sourceIfJoinCheckedOutcome trace == sourceIfJoinOutcome run
      && flag /= payload
      && all (Set.null . Core.sharedLoans)
           (sourceIfJoinThenPaths run ++ sourceIfJoinElsePaths run))
    "actual Grammar-v1 source identity/initial state/checker trace changed"
  left <- case sourceIfJoinThenPaths run of
    [one] -> Right one
    _ -> Left "source trace did not retain left reached predecessor"
  right <- case sourceIfJoinElsePaths run of
    [one] -> Right one
    _ -> Left "source trace did not retain right reached predecessor"
  let paths = case profile of
        BothContinue -> [Continue left,Continue right]
        LinearMismatch -> [Continue left,Continue right]
        SiblingMismatch -> [Continue left,Continue right]
        OneContinue -> [Terminal,Continue right]
        OneStale -> [Terminal,Continue right]
        AllTerminal -> [Terminal,Terminal]
      expectedCount = case profile of
        BothContinue -> (2,0)
        LinearMismatch -> (2,0)
        SiblingMismatch -> (2,0)
        OneContinue -> (1,1)
        OneStale -> (1,1)
        AllTerminal -> (0,2)
      actualCount = (sourceIfJoinContinuingCount run,
                     sourceIfJoinTerminalCount run)
      decided = predict paths
  check (actualCount == expectedCount)
    ("source predecessor control classification changed: " ++ show profile)
  case (decided,sourceIfJoinJoined run) of
    (Joined ctx,Just observed) -> do
      check (ctx == observed)
        "source checker joined state differs from independent finite replay"
      compareNative (fixture profile) [c | Continue c <- paths]
    (Rejected (Core.LinearBranchMismatch _ _),Nothing) ->
      compareNative (fixture profile) [left,right]
    (NoContinuation,Nothing) ->
      check (Core.joinContinuing [] == Right Core.emptyContext)
        "Core empty join behavior unexpectedly changed"
    other -> Left ("source classification/join mismatch: " ++ show other)
  case profile of
    BothContinue -> check
      (sourceIfJoinCheckedOutcome trace ==
        Right (SurfaceCheckResult "choose" [Return bytes8]))
      "accepted source did not complete exact Linear return"
    LinearMismatch -> expectedError IncompatibleBranchResidue
    SiblingMismatch -> expectedError IncompatibleBranchResidue
    OneContinue -> check
      (case sourceIfJoinCheckedOutcome trace of Right _ -> True; _ -> False)
      "single live source predecessor did not pass"
    OneStale -> expectedError StructuralUse
    AllTerminal -> expectedError ControlAfterTerminal
  where
    expectedError cls = check
      (case sourceIfJoinCheckedOutcome trace of
        Left err -> surfaceErrorClass err == cls
        Right _ -> False)
      ("wrong exact source rejection class: " ++ fixture profile)

-- The native decision constructor distinguishes a source-check error,
-- no continuing path, and a join rejection. Never model all-terminal as
-- the successful Core.joinContinuing [] result.
adversarial :: GrammarV1SourceIfJoinTrace -> Either String ()
adversarial t = do
  let base = expectedStart t
      flag = binder (sourceIfJoinFlagBinder t)
      payload = binder (sourceIfJoinPayloadBinder t)
      outsider = Name "corr7-affine-owner"
      uWrong = base { Core.unrestrictedBindings =
        Map.singleton flag (TyOpaque "Different") }
      lWrong = base { Core.linearBindings =
        Map.singleton payload TyBool }
      borrow = base { Core.sharedLoans = Set.singleton payload }
      affine = base { Core.affineBindings = Map.singleton outsider TyBool }
      aWrong = base { Core.affineBindings =
        Map.singleton outsider (TyOpaque "Other") }
      dropped = base { Core.affineBindings = Map.empty }
  check (predict [Terminal,Terminal] == NoContinuation
    && predict [] == NoContinuation
    && predict [Terminal,Continue base] == Joined base
    && predict [SourceFailure "original-check",Continue base] ==
       FailedBeforeJoin "original-check"
    && predict [SourceFailure "earlier",SourceFailure "later",Continue base] ==
       FailedBeforeJoin "earlier"
    && predict [Continue base,Terminal,Continue base] == Joined base)
    "wrong finite source predecessor classification"
  forM_ [3,7,15] $ \n -> compareNative
    ("arbitrary finite " ++ show n) (replicate n affine)
  compareNative "one survivor" [base]
  compareNative "terminal-aware two survivors" [base,base]
  compareNative "multiple Affine drops" [affine,dropped,aWrong]
  check (predict [Continue base,Continue uWrong,Continue borrow] ==
      Rejected (Core.EscapingLoans (Set.singleton payload)) &&
    predict [Continue base,Continue uWrong,Continue lWrong] ==
      Rejected (Core.UnrestrictedBranchMismatch
        (Core.unrestrictedBindings base)
        (Core.unrestrictedBindings uWrong)) &&
    predict [Continue base,Continue lWrong,Continue aWrong] ==
      Rejected (Core.LinearBranchMismatch
        (Core.linearBindings base)
        (Core.linearBindings lWrong)) &&
    predict [Continue affine,Continue aWrong] ==
      Rejected (Core.AffineBranchTypeMismatch
        outsider TyBool (TyOpaque "Other")) &&
    predict [Continue dropped,Continue affine,Continue aWrong] ==
      Joined dropped)
    "wrong global loan/U/L/A error precedence or Affine resurrection"
  forM_ [[base,uWrong,borrow],[base,uWrong,lWrong],
         [base,lWrong,aWrong],[affine,aWrong],
         [dropped,affine,aWrong]] $
    compareNative "adversarial global-order native Core"

hexBytes :: BS.ByteString -> Text
hexBytes = Text.pack . concatMap encode . BS.unpack
  where
    encode n = let digits = showHex n ""
               in if length digits == 1 then '0' : digits else digits

utf8Hex :: Text -> Text
utf8Hex = hexBytes . Encoding.encodeUtf8

-- Each source record contains source file SHA256, exact declaration
-- root, real source-scoped binder IDs, selected source profile, the two
-- verified predecessor categories, and its observed source disposition.
-- The Python consumer independently checks byte source and all fields.
sourceWire :: Profile -> BS.ByteString -> GrammarV1SourceIfJoinTrace -> Text
sourceWire profile raw trace =
  let (left,right) = case profile of
        OneContinue -> ("TERM","CONT")
        OneStale -> ("TERM","CONT")
        AllTerminal -> ("TERM","TERM")
        _ -> ("CONT","CONT")
      fields =
        [ hexBytes (SHA256.hash raw)
        , utf8Hex "decl.fsem01.j1j2.choose"
        , utf8Hex (unName (binder (sourceIfJoinFlagBinder trace)))
        , utf8Hex (unName (binder (sourceIfJoinPayloadBinder trace)))
        , profileTag profile, left, right, outcomeTag profile ]
      frame value = Text.pack (show (Text.length value)) <> ":" <> value
  in "PHIL-FSEM01-CORR7-V1|" <> Text.concat (map frame fields)

main :: IO ()
main = do
  let profiles = [BothContinue,LinearMismatch,SiblingMismatch,
                  OneContinue,OneStale,AllTerminal]
  args <- getArgs
  case args of
    [] -> run Nothing profiles
    ["--emit",dest] -> run (Just dest) profiles
    _ -> putStrLn "usage: Phase1FSEM01Corr7PredecessorsMain [--emit DIR]"
           >> exitFailure
  where
    run destination profiles = do
      sources <- mapM (\profile -> do
        raw <- BS.readFile (directory ++ fixture profile ++ ".phil")
        pure (profile,raw)) profiles
      let result = do
            checked <- mapM (\(profile,raw) -> do
              source <- either (Left . show) Right
                (Encoding.decodeUtf8' raw)
              trace <- sourceTrace source
              checkSource profile trace
              let wire = sourceWire profile raw trace
              check (Text.all (\ch -> ch >= ' ' && ch <= '~') wire)
                "non-ASCII source wire"
              pure (profile,wire,trace)) sources
            case find (\(profile,_,_) -> profile == BothContinue) checked of
              Just (_,_,t) -> adversarial t
              Nothing -> Left "missing canonical accepted source"
            pure [(fixture profile,wire) | (profile,wire,_) <- checked]
      case result of
        Left why -> putStrLn ("FAIL CORR-7: " ++ why) >> exitFailure
        Right wires -> do
          case destination of
            Nothing -> pure ()
            Just dir -> do
              createDirectoryIfMissing True dir
              forM_ wires $ \(label,wire) ->
                TextIO.writeFile (dir </> (label ++ ".pred")) wire
          putStrLn "PASS CORR-7: six real source predecessor control profiles, finite global-priority native replay and hostile multi-predecessor controls"
