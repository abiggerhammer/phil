{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01: *single parsed Grammar-v1 function* with two linear Bytes owners.
-- Unlike the preceding synthetic Core-context bridge, every observed resource
-- checkpoint is emitted by the actual production Surface checker from the
-- exact two-parameter source. Tuple type agreement is bounded elementwise;
-- general source-to-Core product type elaboration remains unproved.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.Static
  ( DeclarationKey (..), emptyStaticContext )
import Phil.Core.Syntax
  ( Control (..), Name, RefTerm (..), Ty (..) )
import Phil.Surface.Check.Engine
  ( BorrowTraceCheckpoint (..), BorrowTracePhase (..) )
import Phil.Surface.Check.Types
  ( RejectionClass (BorrowEscape), SurfaceCheckError (..)
  , SurfaceCheckResult (..) )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..) )
import Phil.Surface.GrammarV1.BorrowResourceSurface
  ( GrammarV1BorrowResourceError (..) )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Declaration (..), GrammarV1TopLevelDecl (..)
  , GrammarV1FunctionDecl, GrammarV1SourceFile (..)
  , parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.TwoOwnerBorrowResourceSurface
  ( GrammarV1TwoOwnerBorrowTrace (..)
  , grammarV1CheckedTwoOwnerBorrowFunction
  , grammarV1CheckedTwoOwnerBorrowFunctionTrace )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

sourceDir :: FilePath
sourceDir = "test/fixtures/fsem01-two-owner-source-v1/"

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.source-two-owner.v1"

bytes8 :: Ty
bytes8 = TyBytes (RefNat 8)

assert :: Bool -> String -> Either String ()
assert condition why =
  if condition then Right () else Left why

sourceFunction :: Text -> Either String GrammarV1FunctionDecl
sourceFunction source = do
  sourceFile <- either (Left . show) Right
    (parseGrammarV1StructuralSource "two-owner-source-v1" source)
  case grammarV1TopLevelDecls sourceFile of
    [Located _ top] ->
      case locatedValue (grammarV1Declaration top) of
        GrammarV1FunctionDeclaration fn -> Right fn
        _ -> Left "expected exactly one parsed function"
    _ -> Left "expected exactly one source declaration"

checkSource :: Text -> Either String GrammarV1TwoOwnerBorrowTrace
checkSource source = do
  fn <- sourceFunction source
  trace <- case grammarV1CheckedTwoOwnerBorrowFunctionTrace
    emptyStaticContext root fn of
    Just (Right result) -> Right result
    other -> Left ("two-owner traced source not admitted: " <> show other)
  assert
    (grammarV1CheckedTwoOwnerBorrowFunction emptyStaticContext root fn ==
      Just (twoOwnerOutcome trace))
    "ordinary checker and traced production outcome differ"
  Right trace

contextOf :: BorrowTraceCheckpoint -> Core.ResourceContext
contextOf cut = Core.ResourceContext
  { Core.unrestrictedBindings = traceUnrestrictedOwners cut
  , Core.affineBindings = traceAffineOwners cut
  , Core.linearBindings = traceLinearOwners cut
  , Core.sharedLoans = traceActiveLoans cut
  }

checkResourceDomains
  :: Name -> Name -> [BorrowTraceCheckpoint] -> Either String ()
checkResourceDomains primary spectator cuts = do
  assert (primary /= spectator) "two source binders have identical Core identity"
  assert (not (null cuts)) "production emitted no source checkpoints"
  mapM_ check (zip [0 :: Int ..] cuts)
  where
    check (index, cut) = do
      let ctx = contextOf cut
          linear = Core.linearBindings ctx
          loans = Core.sharedLoans ctx
          expected = if tracePhase cut == TraceOwnerReturned
            then Map.empty else Map.fromList
              [(primary, bytes8), (spectator, bytes8)]
          expectedLoans = case tracePhase cut of
            TraceLoanStarted -> Set.singleton primary
            TraceBodyResult _ -> Set.singleton primary
            TraceEscapeRejected -> Set.singleton primary
            _ -> Set.empty
      assert (traceOwnerName cut == primary)
        ("checkpoint owner mismatch at " <> show index)
      assert (Map.null (Core.unrestrictedBindings ctx) &&
              Map.null (Core.affineBindings ctx))
        ("nonlinear bindings at recorded post-prune checkpoint " <> show index)
      assert (linear == expected)
        ("missing/extra/wrong-type source linear binding " <> show index)
      assert (loans == expectedLoans)
        ("missing or foreign source loan " <> show index)

checkIndependentSpectator
  :: Name -> Name -> Core.ResourceContext -> Either String ()
checkIndependentSpectator primary spectator ctx = do
  assert (Core.consumeLinear primary ctx ==
    Left (Core.OwnerBorrowed primary))
    "borrowed primary was allowed to move"
  (ty, afterSpectator) <- either (Left . show) Right
    (Core.consumeLinear spectator ctx)
  assert (ty == bytes8) "spectator wrong type when independently consumed"
  assert (Core.linearBindings afterSpectator ==
            Map.singleton primary bytes8)
    "spectator use damaged primary binding"
  assert (Core.sharedLoans afterSpectator == Set.singleton primary)
    "spectator use damaged primary active loan"

checkAccepted :: Text -> Either String ()
checkAccepted source = do
  traced <- checkSource source
  let primary = grammarV1ResolvedBinderCoreName (twoOwnerPrimaryBinder traced)
      spectator = grammarV1ResolvedBinderCoreName (twoOwnerSpectatorBinder traced)
      cuts = twoOwnerCheckpoints traced
      actualPhases = map tracePhase cuts
  assert (twoOwnerOutcome traced ==
    Right (SurfaceCheckResult "loan" [Return (TyOpaque "Tuple[2]")]))
    "accepted source did not complete via the two-owner tuple runtime"
  assert
    (actualPhases ==
      [ TraceBeforeLoan, TraceLoanStarted, TraceBodyResult False
      , TraceLoanClosed, TraceOwnerReturned ])
    "successful two-owner source phases do not match the production trace"
  checkResourceDomains primary spectator cuts
  case map contextOf cuts of
    [before, started, body, closed, returned] -> do
      assert (Core.startSharedLoan primary before == Right started)
        "actual two-owner source loan start disagrees with Core"
      assert (started == body)
        "actual scope-exit checkpoint corrupted other owner"
      assert (Core.endSharedLoan primary body == Right closed)
        "actual two-owner source loan end disagrees with Core"
      (primaryTy, afterPrimary) <- either (Left . show) Right
        (Core.consumeLinear primary closed)
      assert (primaryTy == bytes8 &&
              Core.linearBindings afterPrimary == Map.singleton spectator bytes8)
        "primary consumption did not frame exact spectator"
      assert (Core.consumeLinear spectator afterPrimary ==
        Right (bytes8, returned))
        "source tuple did not consume both owners exactly"
      assert (Core.ensureComplete returned == Right ())
        "successful two-owner return had residual obligations"
      checkIndependentSpectator primary spectator started
    _ -> Left "unexpected accepted source trace length"

checkEscaping :: Text -> Either String ()
checkEscaping source = do
  traced <- checkSource source
  let primary = grammarV1ResolvedBinderCoreName (twoOwnerPrimaryBinder traced)
      spectator = grammarV1ResolvedBinderCoreName (twoOwnerSpectatorBinder traced)
      cuts = twoOwnerCheckpoints traced
  case twoOwnerOutcome traced of
    Left (GrammarV1BorrowResourceProductionError err) -> do
      assert (surfaceErrorClass err == BorrowEscape &&
              surfaceErrorDetail err ==
                "shared view escapes its lexical scope")
        "negative source rejected for a different cause"
    other -> Left ("expected exact BorrowEscape; got " <> show other)
  assert (map tracePhase cuts ==
    [ TraceBeforeLoan, TraceLoanStarted, TraceBodyResult True
    , TraceEscapeRejected ])
    "escaped source emitted closure/consumption after rejection"
  checkResourceDomains primary spectator cuts
  case map contextOf cuts of
    [before, started, escaped, rejected] -> do
      assert (Core.startSharedLoan primary before == Right started)
        "negative source prefix is not a real Core start-loan transition"
      assert (started == escaped && escaped == rejected)
        "escaping source fabricated a post-error successor"
      assert (Core.consumeLinear primary rejected ==
        Left (Core.OwnerBorrowed primary))
        "rejected source allowed borrowed owner consumption"
      assert (Core.linearBindings rejected ==
        Map.fromList [(primary, bytes8), (spectator, bytes8)])
        "rejected source lost either live owner"
      checkIndependentSpectator primary spectator rejected
    _ -> Left "unexpected escaped source trace length"

checkUnsupported :: Text -> String -> Either String ()
checkUnsupported source label = do
  fn <- sourceFunction source
  assert
    (grammarV1CheckedTwoOwnerBorrowFunctionTrace
      emptyStaticContext root fn == Nothing)
    ("unexpected acceptance of outside-fragment source: " <> label)
  assert
    (grammarV1CheckedTwoOwnerBorrowFunction
      emptyStaticContext root fn == Nothing)
    ("ordinary route accepted outside-fragment source: " <> label)

main :: IO ()
main = do
  positive <- TextIO.readFile (sourceDir <> "accepted.phil")
  escaping <- TextIO.readFile (sourceDir <> "escape.phil")
  reversed <- TextIO.readFile (sourceDir <> "reversed-return.phil")
  extra <- TextIO.readFile (sourceDir <> "third-owner.phil")
  let result = do
        checkAccepted positive
        checkEscaping escaping
        checkUnsupported reversed "reversed return order"
        checkUnsupported extra "third linear parameter"
        -- The accepted/escaping source differs only in one final Unit
        -- expression within the borrow body, not in binder/type signatures.
        assert (Text.replace "view; unit;" "view;" positive == escaping)
          "negative is not the minimally modified escaping-view source"
  case result of
    Right () ->
      putStrLn "PASS: single-source two-linear-owner borrow, tuple return, exact BorrowEscape"
    Left msg ->
      putStrLn ("FAIL: " <> msg) >> exitFailure
