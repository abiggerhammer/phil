{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.Callable (CaptureOccurrenceKey (..), CallableOccurrenceKey (..),
  CallableCheckError (..), ClosureCaptureSummary (..))
import Phil.Core.CallableScope (CallableScopeError (..), ClosureExtent (..),
  ClosureRecursionNode (..), checkRestrictedRecursiveClosureCycles)
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Mode (..), Name (..), RefTerm (..), Ty (..))
import Phil.Surface.GrammarV1.BinderScope
  (GrammarV1BinderScopeError (..), GrammarV1ResolvedBinder (..))
import Phil.Surface.GrammarV1.Parser
  (GrammarV1FunctionDecl, GrammarV1SourceFile (..),
   GrammarV1TopLevelDecl (..), GrammarV1Declaration (..),
   parseGrammarV1StructuralSource)
import Phil.Surface.GrammarV1.SourceClosureCapture
  (SourceClosureError (..), SourceDirectClosureRun (..),
   SourceBorrowClosureRun (..), grammarV1SourceDirectClosure,
   grammarV1SourceBorrowClosure)
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.c1.capture"

assert :: Bool -> String -> Either String ()
assert ok why = if ok then Right () else Left why

parse :: Text -> Either String GrammarV1FunctionDecl
parse input = do
  file <- either (Left . show) Right
    (parseGrammarV1StructuralSource "source-capture" input)
  case grammarV1TopLevelDecls file of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1FunctionDeclaration fn -> Right fn
      other -> Left ("not a function " ++ show other)
    other -> Left ("wrong top-level declaration count " ++ show (length other))

direct :: Text -> Either String SourceDirectClosureRun
direct input = do
  fn <- parse input
  case grammarV1SourceDirectClosure emptyStaticContext root fn of
    Just (Right run) -> Right run
    other -> Left ("not in parsed source capture fragment " ++ show other)

borrow :: Text -> Either String SourceBorrowClosureRun
borrow input = do
  fn <- parse input
  case grammarV1SourceBorrowClosure emptyStaticContext root fn of
    Just (Right run) -> Right run
    other -> Left ("not in scoped source fragment " ++ show other)

nm :: GrammarV1ResolvedBinder -> Name
nm = grammarV1ResolvedBinderCoreName

before :: [GrammarV1ResolvedBinder] -> Core.ResourceContext
before [flag,payload] = Core.ResourceContext
  (Map.singleton (nm flag) TyBool) Map.empty
  (Map.singleton (nm payload) (TyBytes (RefNat 8))) Set.empty
before _ = Core.emptyContext

accepted :: Text -> Bool -> Bool -> Either String ()
accepted input moved copied = do
  run <- direct input
  (flag,payload) <- case directParameters run of
    [one,two] -> Right (one,two)
    other -> Left ("wrong checked source parameter arity: " ++ show other)
  let start = before (directParameters run)
      after = start {Core.linearBindings = if moved then Map.empty
        else Core.linearBindings start}
      captureNames = map nm (directCaptures run)
      restricted = if moved
        then Set.singleton (CaptureOccurrenceKey (unName (nm payload)))
        else Set.empty
      cardinality = (if moved then 1 else 0) + (if copied then 1 else 0)
  summary <- maybe (Left "missing native capture summary") Right
    (directSummary run)
  assert (directInitial run == start && directFinal run == Just after &&
          directOutcome run == Right () &&
          elem (nm payload) captureNames == moved &&
          elem (nm flag) captureNames == copied)
    "source captures did not produce exact owner/copy state"
  assert (closureMovedRestrictedOccurrences summary == restricted &&
          Map.size (closureCapturesByOccurrence summary) == cardinality &&
          closureMinimumStructuralMode summary ==
            (if moved then Linear else Unrestricted))
    "capture normalization/mode did not preserve source ownership"
  assert (if moved
    then Core.consumeLinear (nm payload) start ==
      Right (TyBytes (RefNat 8),after) &&
      Core.consumeLinear (nm payload) after ==
      Left (Core.UnknownBinding (nm payload))
    else Core.useUnrestricted (nm flag) start == Right (TyBool,start))
    "native Core move or unrestricted copy disagreed"

directError :: Text -> (SourceClosureError -> Bool) -> Either String ()
directError input f = do
  run <- direct input
  assert (directFinal run == Nothing &&
          either f (const False) (directOutcome run))
    ("wrong capture error or fabricated post-state " ++ show run)

borrowSuccess :: Text -> Either String ()
borrowSuccess input = do
  run <- borrow input
  let owner = nm (borrowOwner run)
      view = nm (borrowView run)
      start = borrowInitial run
  loaned <- maybe (Left "no native loan start") Right (borrowStarted run)
  closed <- maybe (Left "no native loan closure") Right (borrowClosed run)
  assert (owner /= view && borrowExtent run /= EscapingClosure &&
          borrowOutcome run == Right () && closed == start &&
          Core.sharedLoans loaned == Set.singleton owner &&
          Core.linearBindings loaned == Core.linearBindings start &&
          Core.affineBindings loaned == Core.affineBindings start &&
          Core.unrestrictedBindings loaned == Core.unrestrictedBindings start &&
          Core.consumeLinear owner loaned == Left (Core.OwnerBorrowed owner) &&
          Core.endSharedLoan owner loaned == Right start)
    "scoped capture violated native loan lifecycle"

borrowError :: Text -> Bool -> Either String ()
borrowError input escape = do
  run <- borrow input
  assert (borrowStarted run /= Nothing && borrowClosed run == Nothing)
    "rejected capture manufactured a loan-closed successor"
  if escape then case borrowOutcome run of
    Left (SourceClosureScopeError
      (EscapingClosureCapturesScopedLoan _ captured _)) ->
      assert (captured == CaptureOccurrenceKey (unName (nm (borrowView run))))
        "escaped scoped closure diagnostic lost its exact view"
    other -> Left ("escaping closure not rejected: " ++ show other)
  else assert (borrowOutcome run ==
        Left (SourceClosureModeMismatch Unrestricted Linear))
       "unjustified closure mode strengthening was accepted"

unsupported :: Text -> Bool -> Either String ()
unsupported input isDirect = do
  fn <- parse input
  let missing = if isDirect
        then case grammarV1SourceDirectClosure emptyStaticContext root fn of
          Nothing -> True
          _ -> False
        else case grammarV1SourceBorrowClosure emptyStaticContext root fn of
          Nothing -> True
          _ -> False
  assert missing "out-of-fragment source incorrectly admitted"

recursiveCoreControl :: Text -> Either String ()
recursiveCoreControl input = do
  run <- direct input
  summary <- maybe (Left "missing capture") Right (directSummary run)
  let key = CallableOccurrenceKey "explicit-model-supplied-cycle"
      node = ClosureRecursionNode key (Set.singleton key)
        (closureMovedRestrictedOccurrences summary)
  case checkRestrictedRecursiveClosureCycles [node] of
    Left (RestrictedRecursiveClosureCycle closures captures) ->
      assert (closures == Set.singleton key &&
              captures == closureMovedRestrictedOccurrences summary)
        "SCC control lost source-derived restricted capture"
    other -> Left ("model-provided restricted self-cycle did not reject: " ++ show other)

main :: IO ()
main = do
  let get key = TextIO.readFile
        ("test/fixtures/fsem01-source-closure-capture-v1/" ++ key ++ ".phil")
  files <- mapM get
    ["direct-linear","direct-mixed","direct-flag","direct-flag-repeat",
     "direct-derived","direct-renamed","duplicate-linear","weakened-mode",
     "unknown-capture","closure-param-shadow","wrong-nominal","recursive-source",
     "local-borrow","escaped-borrow","derived-borrow",
     "wrong-borrow-mode","wrong-borrow-view"]
  let checked = case files of
        [d1,d2,d3,d4,d5,d6,dup,weak,unknown,shadow,nominal,recursive,
         local,escaped,derived,wrongMode,wrongView] -> do
          accepted d1 True False
          accepted d2 True True
          accepted d3 False True
          accepted d4 False True
          accepted d5 True False
          accepted d6 True True
          directError dup (\err -> case err of
            SourceClosureCaptureError (DuplicateRestrictedCapture _ Linear) -> True
            _ -> False)
          directError weak (== SourceClosureModeMismatch Linear Unrestricted)
          directError unknown (\err -> case err of
            SourceClosureBinderError (GrammarV1BinderNotInScope _) -> True
            _ -> False)
          directError shadow (\err -> case err of
            SourceClosureBinderError (GrammarV1ActiveShadowing _ _) -> True
            _ -> False)
          unsupported nominal True
          unsupported recursive True
          borrowSuccess local
          borrowSuccess derived
          borrowError escaped True
          borrowError wrongMode False
          unsupported wrongView False
          recursiveCoreControl d1
        _ -> Left "fixture arity changed"
  case checked of
    Right () -> putStrLn
      "PASS: 17 parsed source closures, exact Core owner moves/loan scope and bounded SCC control"
    Left detail -> putStrLn ("FAIL: " ++ detail) >> exitFailure
