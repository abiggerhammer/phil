{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01: actual source-scoped loan checkpoints in continuing if/join arms.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Control (..), Name (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine
  ( BorrowTraceCheckpoint (..), BorrowTracePhase (..)
  , SourceBranchBorrowObservation (..), SourceScopedIfJoinRun (..) )
import Phil.Surface.Check.Types
  ( RejectionClass (..), SurfaceCheckError (..), SurfaceCheckResult (..) )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError (..), GrammarV1ResolvedBinder (..) )
import Phil.Surface.GrammarV1.BorrowViewScope
  ( GrammarV1BorrowViewScopeError (..) )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1FunctionDecl, GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..), GrammarV1Declaration (..)
  , parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceScopedBorrowJoin
  ( GrammarV1ScopedBorrowJoinError (..), GrammarV1ScopedBorrowJoinTrace (..)
  , grammarV1CheckedScopedBorrowJoinTrace )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.scoped-loan-join.choose"

bytes8 :: Ty
bytes8 = TyBytes (RefNat 8)

assert :: Bool -> String -> Either String ()
assert test message = if test then Right () else Left message

parseOne :: Text -> Either String GrammarV1FunctionDecl
parseOne source = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "scoped-loan-join" source)
  case grammarV1TopLevelDecls parsed of
    [Located _ decl] -> case locatedValue (grammarV1Declaration decl) of
      GrammarV1FunctionDeclaration fn -> Right fn
      other -> Left ("not a function declaration: " ++ show other)
    other -> Left ("not one source declaration: " ++ show (length other))

check :: Text
  -> Maybe (Either GrammarV1ScopedBorrowJoinError GrammarV1ScopedBorrowJoinTrace)
check source = case parseOne source of
  Left _ -> Nothing
  Right fn -> grammarV1CheckedScopedBorrowJoinTrace emptyStaticContext root fn

checked :: Text -> Either String GrammarV1ScopedBorrowJoinTrace
checked source = case parseOne source of
  Left err -> Left ("failed parsing source: " ++ err)
  Right fn ->
    case grammarV1CheckedScopedBorrowJoinTrace emptyStaticContext root fn of
      Just (Right result) -> Right result
      other -> Left ("outside checked source fragment: " ++ show other)

flagName, ownerName :: GrammarV1ScopedBorrowJoinTrace -> Name
flagName = grammarV1ResolvedBinderCoreName . scopedBorrowJoinFlagBinder
ownerName = grammarV1ResolvedBinderCoreName . scopedBorrowJoinPayloadBinder

initial :: GrammarV1ScopedBorrowJoinTrace -> Core.ResourceContext
initial t = Core.ResourceContext
  (Map.singleton (flagName t) TyBool) Map.empty
  (Map.singleton (ownerName t) bytes8) Set.empty

cutContext :: BorrowTraceCheckpoint -> Core.ResourceContext
cutContext cut = Core.ResourceContext
  (traceUnrestrictedOwners cut) (traceAffineOwners cut)
  (traceLinearOwners cut) (traceActiveLoans cut)

baseChecks :: GrammarV1ScopedBorrowJoinTrace
  -> Either String SourceScopedIfJoinRun
baseChecks t = do
  let run = scopedBorrowJoinRun t
  assert (flagName t /= ownerName t &&
          scopedIfJoinBefore run == Just (initial t) &&
          scopedIfJoinOutcome run == scopedBorrowJoinOutcome t)
    "source binder names, initial native context or checker parity wrong"
  Right run

observed :: Maybe SourceBranchBorrowObservation
  -> Either String SourceBranchBorrowObservation
observed Nothing = Left "source borrow did not emit actual loan observation"
observed (Just observation) = Right observation

checkClosedLoan :: GrammarV1ScopedBorrowJoinTrace
  -> Maybe GrammarV1ResolvedBinder -> SourceBranchBorrowObservation
  -> Either String ()
checkClosedLoan t maybeView obs = do
  view <- case maybeView of
    Just name -> Right (grammarV1ResolvedBinderCoreName name)
    Nothing -> Left "loan observation lacks its exact source view binder"
  let before = initial t
      owner = ownerName t
      started = before { Core.sharedLoans = Set.singleton owner }
      cuts = sourceBranchBorrowCuts obs
  assert (sourceBranchBorrowOutcome obs == Right () &&
          map tracePhase cuts ==
            [TraceBeforeLoan,TraceLoanStarted,TraceBodyResult False,TraceLoanClosed])
    ("wrong successful production borrow phases/outcome: " ++ show obs)
  assert (all (\cut -> traceOwnerName cut == owner &&
                      traceViewName cut == view) cuts &&
          map cutContext cuts == [before,started,started,before])
    "production observer did not preserve exact source owner/view resource states"
  assert (Core.startSharedLoan owner before == Right started &&
          Core.endSharedLoan owner started == Right before &&
          Core.joinContinuing [started,before] ==
            Left (Core.EscapingLoans (Set.singleton owner)) &&
          Core.joinContinuing [before,before] == Right before)
    "actual source loan interim could cross Core join or failed to close"

checkAccepted :: Text -> Bool -> Bool -> Either String ()
checkAccepted source leftBorrow rightBorrow = do
  t <- checked source
  run <- baseChecks t
  let start = initial t
      left = scopedBorrowJoinThenLoan t
      right = scopedBorrowJoinElseLoan t
  assert (scopedIfJoinThenRaw run == [start] &&
          scopedIfJoinThenPruned run == [start] &&
          scopedIfJoinElseRaw run == [start] &&
          scopedIfJoinElsePruned run == [start] &&
          scopedIfJoinJoined run == Just start &&
          scopedBorrowJoinOutcome t ==
            Right (SurfaceCheckResult "choose" [Return bytes8]))
    "completed source loans did not produce exactly one live joined linear owner"
  assert (isBorrow left == leftBorrow && isBorrow right == rightBorrow)
    "branch observer misclassified an actual source borrow or Unit"
  if leftBorrow
    then observed left >>= checkClosedLoan t (scopedBorrowJoinThenView t)
    else Right ()
  if rightBorrow
    then observed right >>= checkClosedLoan t (scopedBorrowJoinElseView t)
    else Right ()
  where
    isBorrow Nothing = False
    isBorrow (Just _) = True

checkSiblingIdentities :: Text -> Either String ()
checkSiblingIdentities source = do
  t <- checked source
  case (scopedBorrowJoinThenView t,scopedBorrowJoinElseView t) of
    (Just left,Just right) ->
      assert (grammarV1ResolvedBinderDisplayName left == "view" &&
              grammarV1ResolvedBinderDisplayName right == "view" &&
              grammarV1ResolvedBinderCoreName left /=
                grammarV1ResolvedBinderCoreName right)
        "two sibling source views have conflated identity"
    other -> Left ("missing exact sibling source views: " ++ show other)

checkEscape :: Text -> Bool -> Either String ()
checkEscape source leftEscape = do
  t <- checked source
  run <- baseChecks t
  let selected = if leftEscape
        then scopedBorrowJoinThenLoan t
        else scopedBorrowJoinElseLoan t
  obs <- observed selected
  assert (map tracePhase (sourceBranchBorrowCuts obs) ==
      [TraceBeforeLoan,TraceLoanStarted,TraceBodyResult True,TraceEscapeRejected])
    "source view escape did not produce a fail-closed loan transition prefix"
  case (sourceBranchBorrowOutcome obs,scopedBorrowJoinOutcome t) of
    (Left first,Left second) ->
      assert (first == second &&
              surfaceErrorClass second == BorrowEscape &&
              surfaceErrorDetail second == "shared view escapes its lexical scope")
        ("wrong production escape diagnostic: " ++ show second)
    other -> Left ("source view escape admitted a successor: " ++ show other)
  assert (scopedIfJoinJoined run == Nothing &&
          null (scopedIfJoinElsePruned run))
    "rejected source loan produced a post-error joined context"
  if leftEscape
    then assert (null (scopedIfJoinThenRaw run) &&
                 null (scopedIfJoinElseRaw run) &&
                 scopedBorrowJoinElseLoan t == Nothing)
           "left rejected loan incorrectly executed the right branch"
    else assert (scopedIfJoinThenPruned run == [initial t] &&
                 null (scopedIfJoinElseRaw run))
           "right rejected loan invented continuing predecessor"

checkMoveWhileLoaned :: Text -> Either String ()
checkMoveWhileLoaned source = do
  t <- checked source
  run <- baseChecks t
  obs <- observed (scopedBorrowJoinThenLoan t)
  assert (map tracePhase (sourceBranchBorrowCuts obs) ==
      [TraceBeforeLoan,TraceLoanStarted] &&
      scopedIfJoinJoined run == Nothing && null (scopedIfJoinThenRaw run))
    "loaned owner moved without exact production rejection prefix"
  case (sourceBranchBorrowOutcome obs,scopedBorrowJoinOutcome t) of
    (Left e,Left actual) -> assert
      (e == actual && surfaceErrorClass actual == StructuralUse)
      ("owner move during a loan rejected incorrectly: " ++ show actual)
    other -> Left ("borrowed owner move was not rejected: " ++ show other)

checkBorrowUnrestricted :: Text -> Either String ()
checkBorrowUnrestricted source = do
  t <- checked source
  run <- baseChecks t
  obs <- observed (scopedBorrowJoinThenLoan t)
  assert (map tracePhase (sourceBranchBorrowCuts obs) == [TraceBeforeLoan] &&
          scopedIfJoinJoined run == Nothing)
    "borrow of unrestricted Bool created a shared loan or join successor"
  case scopedBorrowJoinOutcome t of
    Left e -> assert
      (surfaceErrorClass e == BorrowEscape &&
       surfaceErrorDetail e == "borrow requires an affine or linear owner" &&
       sourceBranchBorrowOutcome obs == Left e)
      ("wrong unrestricted borrow rejection: " ++ show e)
    Right _ -> Left "borrowed unrestricted source flag as if it were restricted"

checkReturnDuringLoan :: Text -> Either String ()
checkReturnDuringLoan source = do
  t <- checked source
  run <- baseChecks t
  obs <- observed (scopedBorrowJoinThenLoan t)
  assert (scopedIfJoinJoined run == Nothing &&
          null (scopedIfJoinThenRaw run) &&
          not (elem TraceLoanClosed
            (map tracePhase (sourceBranchBorrowCuts obs))))
    "source return while loan active fabricated a closed-loan join"
  case (sourceBranchBorrowOutcome obs,scopedBorrowJoinOutcome t) of
    (Left e,Left actual) ->
      assert (e == actual && surfaceErrorClass actual == LinearCompletion)
        ("terminal return during loan did not fail closure: " ++ show actual)
    other -> Left ("terminal return during loan was accepted: " ++ show other)

checkShadow :: Text -> Either String ()
checkShadow source = case check source of
  Just (Left (ScopedBorrowJoinBorrowError
    (GrammarV1BorrowViewBinderError
      (GrammarV1ActiveShadowing _ _)))) -> Right ()
  other -> Left ("source borrow view shadow not rejected: " ++ show other)

checkUnsupported :: Text -> String -> Either String ()
checkUnsupported source description = do
  _ <- parseOne source
  assert (check source == Nothing)
    ("bounded adapter admitted unsupported source: " ++ description)

main :: IO ()
main = do
  let get name = TextIO.readFile
        ("test/fixtures/fsem01-scoped-borrow-join-v1/" ++ name ++ ".phil")
  acceptedLeft <- get "accepted-left"
  acceptedBoth <- get "accepted-both"
  acceptedRight <- get "accepted-right"
  acceptedAlias <- get "accepted-alias"
  escapedLeft <- get "escape-left"
  escapedRight <- get "escape-right"
  escapedAlias <- get "escape-alias"
  moved <- get "move-while-loaned"
  returned <- get "return-inside-borrow"
  unrestricted <- get "borrow-unrestricted"
  shadow <- get "view-shadow-parameter"
  stale <- get "view-after-join"
  joinSlot <- get "nonempty-join"
  noElse <- get "missing-else"
  wrongWidth <- get "wrong-return-width"
  wrongCondition <- get "wrong-condition"
  unknown <- get "unknown-borrow-owner"
  nested <- get "nested-borrow"
  let result = do
        checkAccepted acceptedLeft True False
        checkAccepted acceptedBoth True True
        checkSiblingIdentities acceptedBoth
        checkAccepted acceptedRight False True
        checkAccepted acceptedAlias True False
        checkEscape escapedLeft True
        checkEscape escapedRight False
        checkEscape escapedAlias True
        checkMoveWhileLoaned moved
        checkReturnDuringLoan returned
        checkBorrowUnrestricted unrestricted
        checkShadow shadow
        checkUnsupported stale "view source name after its lexical region"
        checkUnsupported joinSlot "nonempty join-state telescope"
        checkUnsupported noElse "missing else predecessor"
        checkUnsupported wrongWidth "mismatched result Bytes width"
        checkUnsupported wrongCondition "non-Boolean source condition"
        checkUnsupported unknown "unknown local borrow owner"
        checkUnsupported nested "nested source borrow expression"
        assert (Text.replace "view; unit;" "view;" acceptedLeft == escapedLeft)
          "escaping view is not a minimal source-body mutation"
  case result of
    Right () -> putStrLn
      "PASS: source-scoped loans close before continuing join and reject exact escapes"
    Left e -> putStrLn ("FAIL: " ++ e) >> exitFailure
