{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01 J-1/J-2: actual parsed two-predecessor Grammar-v1 if-join through
-- the existing production Surface checkBlock/joinExclusive/Core.joinContinuing.
-- All claims are bounded to the explicit projection admitted by the adapter.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Control (..), Name (..), RefTerm (..), Ty (..))
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
import System.Exit (exitFailure)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.j1j2.choose"

bytes8 :: Ty
bytes8 = TyBytes (RefNat 8)

directory :: FilePath
directory = "test/fixtures/fsem01-source-branch-join-v1/"

assert :: Bool -> String -> Either String ()
assert passed msg = if passed then Right () else Left msg

parseOne :: Text -> Either String GrammarV1FunctionDecl
parseOne source = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "source-branch-join" source)
  case grammarV1TopLevelDecls parsed of
    [Located _ top] ->
      case locatedValue (grammarV1Declaration top) of
        GrammarV1FunctionDeclaration fn -> Right fn
        other -> Left ("not a function declaration: " ++ show other)
    other -> Left ("not one source declaration: " ++ show (length other))

check :: Text -> Maybe (Either a GrammarV1SourceIfJoinTrace)
check source = case parseOne source of
  Left _ -> Nothing
  Right fn -> case grammarV1CheckedSourceIfJoinTrace
      emptyStaticContext root fn of
    Nothing -> Nothing
    Just (Left _) -> Nothing
    Just (Right trace) -> Just (Right trace)

checked :: Text -> Either String GrammarV1SourceIfJoinTrace
checked source = case parseOne source of
  Left err -> Left ("source failed parsing: " ++ err)
  Right fn ->
    case grammarV1CheckedSourceIfJoinTrace emptyStaticContext root fn of
      Just (Right value) -> Right value
      other -> Left ("no admitted exact source if/join projection: " ++ show other)

flagName, payloadName :: GrammarV1SourceIfJoinTrace -> Name
flagName = grammarV1ResolvedBinderCoreName . sourceIfJoinFlagBinder
payloadName = grammarV1ResolvedBinderCoreName . sourceIfJoinPayloadBinder

initial :: GrammarV1SourceIfJoinTrace -> Core.ResourceContext
initial t = Core.ResourceContext
  (Map.singleton (flagName t) TyBool)
  Map.empty (Map.singleton (payloadName t) bytes8) Set.empty

checks :: GrammarV1SourceIfJoinTrace -> Either String SourceIfJoinRun
checks trace = do
  let run = sourceIfJoinBranchRun trace
  assert (sourceIfJoinBefore run == Just (initial trace))
    "source join initial checkpoint lost exact unrestricted flag/linear owner"
  assert (flagName trace /= payloadName trace)
    "source bool and linear payload semantic identities conflated"
  assert (sourceIfJoinCheckedOutcome trace == sourceIfJoinOutcome run)
    "ordinary and traced production projection outcomes disagree"
  assert (all (\context ->
        Core.unrestrictedBindings context ==
          Map.singleton (flagName trace) TyBool &&
        Core.sharedLoans context == Set.empty)
      (sourceIfJoinThenPaths run ++ sourceIfJoinElsePaths run))
    "branch altered foreign flag state or created an active loan"
  Right run

checkAccepted :: Text -> Either String ()
checkAccepted source = do
  trace <- checked source
  run <- checks trace
  let start = initial trace
  assert (null (sourceIfJoinBranchBinders trace))
    "empty branch created a local semantic binder"
  assert (sourceIfJoinThenPaths run == [start] &&
          sourceIfJoinElsePaths run == [start] &&
          sourceIfJoinContinuingCount run == 2 &&
          sourceIfJoinTerminalCount run == 0 &&
          sourceIfJoinJoined run == Just start)
    "accepted two-predecessor production join did not preserve both states"
  assert (Core.joinContinuing [start,start] == Right start)
    "actual native Core join does not agree with source-derived predecessors"
  assert (sourceIfJoinCheckedOutcome trace ==
          Right (SurfaceCheckResult "choose" [Return bytes8]))
    "accepted source join did not return exact linear Bytes[8] once"

checkLinearMismatch :: Text -> Either String ()
checkLinearMismatch source = do
  trace <- checked source
  run <- checks trace
  case sourceIfJoinBranchBinders trace of
    [moved] -> do
      let start = initial trace
          thenContext = start
            { Core.linearBindings = Map.singleton
                (grammarV1ResolvedBinderCoreName moved) bytes8 }
          err = Core.LinearBranchMismatch
            (Core.linearBindings thenContext)
            (Core.linearBindings start)
      assert (grammarV1ResolvedBinderCoreName moved /= payloadName trace &&
              sourceIfJoinThenPaths run == [thenContext] &&
              sourceIfJoinElsePaths run == [start] &&
              sourceIfJoinContinuingCount run == 2 &&
              sourceIfJoinTerminalCount run == 0 &&
              sourceIfJoinJoined run == Nothing)
        "moved branch owner did not cause exact two-continuing-predecessor mismatch"
      assert (Core.joinContinuing [thenContext,start] == Left err)
        "native Core join did not reject unequal linear owner maps"
      case sourceIfJoinCheckedOutcome trace of
        Left productionError ->
          assert (surfaceErrorClass productionError ==
                    IncompatibleBranchResidue &&
                  surfaceErrorDetail productionError == Text.pack (show err))
            ("wrong exact production join error: " ++ show productionError)
        Right _ -> Left "one-sided linear owner move silently joined"
    _ -> Left "source branch did not allocate exactly one successor binder"

checkSameSpellingDifferentOwners :: Text -> Either String ()
checkSameSpellingDifferentOwners source = do
  trace <- checked source
  run <- checks trace
  case sourceIfJoinBranchBinders trace of
    [first,second] -> do
      let leftName = grammarV1ResolvedBinderCoreName first
          rightName = grammarV1ResolvedBinderCoreName second
          leftMap = Map.singleton leftName bytes8
          rightMap = Map.singleton rightName bytes8
          err = Core.LinearBranchMismatch leftMap rightMap
      assert (grammarV1ResolvedBinderDisplayName first == "saved" &&
              grammarV1ResolvedBinderDisplayName second == "saved" &&
              leftName /= rightName)
        "disjoint sibling same-spelling names lost distinct semantic IDs"
      assert (map Core.linearBindings (sourceIfJoinThenPaths run) ==
              [leftMap] &&
              map Core.linearBindings (sourceIfJoinElsePaths run) ==
              [rightMap] &&
              sourceIfJoinJoined run == Nothing)
        "sibling branches were silently joined by display-name equality"
      case sourceIfJoinCheckedOutcome trace of
        Left productionError ->
          assert (surfaceErrorClass productionError ==
                    IncompatibleBranchResidue &&
                  surfaceErrorDetail productionError == Text.pack (show err))
            ("sibling binder mismatch got wrong production error: " ++
              show productionError)
        Right _ -> Left "distinct sibling restricted owners incorrectly joined"
    _ -> Left "expected two source-generated sibling binders"

checkTerminalExcluded :: Text -> Either String ()
checkTerminalExcluded source = do
  trace <- checked source
  run <- checks trace
  let start = initial trace
      done = start { Core.linearBindings = Map.empty }
  assert (sourceIfJoinThenPaths run == [done] &&
          sourceIfJoinElsePaths run == [start] &&
          sourceIfJoinContinuingCount run == 1 &&
          sourceIfJoinTerminalCount run == 1 &&
          sourceIfJoinJoined run == Just start)
    "terminated source arm erroneously entered the continuing join"
  assert (Core.joinContinuing [start] == Right start)
    "Core surviving predecessor was not the exact live linear resource state"
  assert (sourceIfJoinCheckedOutcome trace ==
          Right (SurfaceCheckResult "choose"
            [Return bytes8, Return bytes8]))
    "source terminal predecessor / surviving predecessor did not return exactly"

checkTerminalStale :: Text -> Either String ()
checkTerminalStale source = do
  trace <- checked source
  run <- checks trace
  case sourceIfJoinBranchBinders trace of
    [moved] -> do
      let start = initial trace
          joined = start
            { Core.linearBindings = Map.singleton
                (grammarV1ResolvedBinderCoreName moved) bytes8 }
      assert (sourceIfJoinContinuingCount run == 1 &&
              sourceIfJoinTerminalCount run == 1 &&
              sourceIfJoinJoined run == Just joined)
        "terminating predecessor was accidentally included in joining"
      case sourceIfJoinCheckedOutcome trace of
        Left productionError ->
          assert (surfaceErrorClass productionError == StructuralUse &&
                  surfaceErrorDetail productionError ==
                    "unknown or consumed binding: " <>
                      unName (payloadName trace))
            ("post-join stale owner failed for wrong reason: " ++
              show productionError)
        Right _ -> Left "post-terminal join invented a live predecessor owner"
    _ -> Left "expected one nonterminal moved successor"

checkBothTerminal :: Text -> Either String ()
checkBothTerminal source = do
  trace <- checked source
  run <- checks trace
  let done = (initial trace) { Core.linearBindings = Map.empty }
  assert (sourceIfJoinThenPaths run == [done] &&
          sourceIfJoinElsePaths run == [done] &&
          sourceIfJoinContinuingCount run == 0 &&
          sourceIfJoinTerminalCount run == 2 &&
          sourceIfJoinJoined run == Nothing)
    "two terminal predecessors invented a continuing join state"
  case sourceIfJoinCheckedOutcome trace of
    Left err -> assert
      (surfaceErrorClass err == ControlAfterTerminal &&
       surfaceErrorDetail err ==
         "statement occurs after all incoming paths terminated")
      ("post-terminal return not rejected by production control: " ++ show err)
    Right _ -> Left "post-terminal statement accepted without a predecessor"

checkUnsupported :: Text -> String -> Either String ()
checkUnsupported src label =
  case parseOne src of
    Left _ -> Right ()
    Right fn -> assert
      (grammarV1CheckedSourceIfJoinTrace
         emptyStaticContext root fn == Nothing)
      ("out-of-fragment source was silently admitted: " ++ label)

main :: IO ()
main = do
  let get name = TextIO.readFile (directory ++ name ++ ".phil")
  accepted <- get "accepted"
  changed <- get "linear-mismatch"
  terminal <- get "terminal-excluded"
  stale <- get "terminal-stale"
  siblings <- get "two-local-owners"
  allTerminal <- get "terminal-both"
  noElse <- get "missing-else"
  wrongCondition <- get "wrong-condition"
  joinSlot <- get "unexpected-join-slot"
  width <- get "wrong-return-width"
  unusual <- get "unsupported-branch"
  let result = do
        checkAccepted accepted
        checkLinearMismatch changed
        checkTerminalExcluded terminal
        checkTerminalStale stale
        checkSameSpellingDifferentOwners siblings
        checkBothTerminal allTerminal
        checkUnsupported noElse "missing else branch"
        checkUnsupported wrongCondition "non-bool condition binder"
        checkUnsupported joinSlot "nonempty join state"
        checkUnsupported width "incompatible declared result width"
        checkUnsupported unusual "unelaborated nested branch expression"
        assert (Text.replace "unit;" "let saved = payload;" accepted /=
                changed)
          "mutation fixture accounting unexpectedly changed"
  case result of
    Right () -> putStrLn
      "PASS: two real checked source predecessors, native Core join, exact linear mismatch and terminal exclusion"
    Left err -> putStrLn ("FAIL: " ++ err) >> exitFailure
