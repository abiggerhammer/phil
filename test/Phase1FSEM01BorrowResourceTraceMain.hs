{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Control (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine
  ( BorrowTraceCheckpoint (..)
  , BorrowTracePhase (..)
  )
import Phil.Surface.Check.Types
  ( RejectionClass (..)
  , SurfaceCheckError (..)
  , SurfaceCheckResult (..)
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.BorrowResourceSurface
  ( GrammarV1BorrowResourceError (..)
  , GrammarV1BorrowResourceTrace (..)
  , grammarV1CheckedBorrowResourceFunction
  , grammarV1CheckedBorrowResourceFunctionTrace
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "FSEM-01 trace: Unit borrow closes loan before exact owner return"
        (positiveTrace "trace-unit" unitBody)
    , test "FSEM-01 trace: observed view then Unit closes loan"
        (positiveTrace "trace-view-unit" viewThenUnit)
    , test "FSEM-01 trace: escaping body result keeps live loan at rejection"
        (negativeTrace "trace-escape" escapingView)
    , test "FSEM-01 trace: normal and observed checker outcomes agree"
        (mapM_ (uncurry parity)
          [ ("parity-unit", unitBody)
          , ("parity-view-unit", viewThenUnit)
          , ("parity-escape", escapingView)
          , ("parity-unrestricted", unrestrictedOwner)
          , ("parity-unresolved", unresolvedOwner)
          , ("parity-shadow", viewShadow)
          ])
    , test "FSEM-01 trace: unsupported U8/unknown owner remain non-competence"
        unsupportedDoesNotFabricateTrace
    ]
  mapM_ (uncurry printTrace)
    [("positive-unit", unitBody), ("positive-view-unit", viewThenUnit),
     ("negative-escape", escapingView)]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left err -> putStrLn ("FAIL: " <> label <> " -- " <> err) >> pure False

expectedTy :: Ty
expectedTy = TyBytes (RefNat 8)

positiveTrace :: Text.Text -> Text.Text -> Either String ()
positiveTrace label source = do
  trace <- successfulPreparation label source
  let cuts = grammarV1TraceCheckpoints trace
  checkIdentity trace cuts
  assert (map tracePhase cuts ==
    [ TraceBeforeLoan
    , TraceLoanStarted
    , TraceBodyResult False
    , TraceLoanClosed
    , TraceOwnerReturned
    ]) ("wrong positive cut sequence: " <> show cuts)
  checkMembership trace cuts
    [True, True, True, True, False]
    [False, True, True, False, False]
  case grammarV1TraceOutcome trace of
    Right checked ->
      assert (checkedTerminalControls checked == [Return expectedTy])
        ("expected exact terminal Bytes[8] return, got " <>
          show (checkedTerminalControls checked))
    other -> Left ("expected production success, got " <> show other)

negativeTrace :: Text.Text -> Text.Text -> Either String ()
negativeTrace label source = do
  trace <- successfulPreparation label source
  let cuts = grammarV1TraceCheckpoints trace
  checkIdentity trace cuts
  assert (map tracePhase cuts ==
    [ TraceBeforeLoan
    , TraceLoanStarted
    , TraceBodyResult True
    , TraceEscapeRejected
    ]) ("wrong rejection cut sequence: " <> show cuts)
  checkMembership trace cuts
    [True, True, True, True]
    [False, True, True, True]
  case grammarV1TraceOutcome trace of
    Left (GrammarV1BorrowResourceProductionError err) -> do
      assert (surfaceErrorClass err == BorrowEscape)
        ("expected production BorrowEscape, got " <> show err)
      assert (surfaceErrorDetail err == "shared view escapes its lexical scope")
        ("wrong production rejection detail: " <> show err)
    other -> Left ("expected production BorrowEscape, got " <> show other)

checkIdentity
  :: GrammarV1BorrowResourceTrace
  -> [BorrowTraceCheckpoint]
  -> Either String ()
checkIdentity trace cuts = do
  let owner = grammarV1TraceOwnerBinder trace
      view = grammarV1TraceViewBinder trace
  assert (grammarV1ResolvedBinderKey owner /= grammarV1ResolvedBinderKey view)
    "owner and view binder keys unexpectedly coincide"
  assert (grammarV1ResolvedBinderCoreName owner /= grammarV1ResolvedBinderCoreName view)
    "owner and view generated Core names unexpectedly coincide"
  assert (not (null cuts)) "no production checkpoints recorded"
  assert (all ((== grammarV1ResolvedBinderCoreName owner) . traceOwnerName) cuts)
    "trace lost exact generated owner identity"
  assert (all ((== grammarV1ResolvedBinderCoreName view) . traceViewName) cuts)
    "trace lost exact generated view identity"

checkMembership
  :: GrammarV1BorrowResourceTrace
  -> [BorrowTraceCheckpoint]
  -> [Bool]
  -> [Bool]
  -> Either String ()
checkMembership trace cuts linearExpected loanExpected = do
  let owner = grammarV1ResolvedBinderCoreName (grammarV1TraceOwnerBinder trace)
      linearState = map (Map.lookup owner . traceLinearOwners) cuts
      loanState = map (Set.member owner . traceActiveLoans) cuts
  assert (linearState == map (\present -> if present then Just expectedTy else Nothing)
                        linearExpected)
    ("wrong linear owner snapshots: " <> show linearState)
  assert (loanState == loanExpected)
    ("wrong loan snapshots: " <> show loanState)
  assert (all (\cut -> Set.size (traceActiveLoans cut) <= 1) cuts)
    "unexpected extra loan in single-owner admitted fragment"

parity :: Text.Text -> Text.Text -> Either String ()
parity label source = do
  parsed <- parseFun label source
  let normal = grammarV1CheckedBorrowResourceFunction
        emptyStaticContext (DeclarationKey "decl.FSEM01LoanTrace") parsed
      observed = grammarV1CheckedBorrowResourceFunctionTrace
        emptyStaticContext (DeclarationKey "decl.FSEM01LoanTrace") parsed
  case (normal, observed) of
    (Nothing, Nothing) -> Right ()
    (Just (Left leftErr), Just (Left rightErr)) ->
      assert (leftErr == rightErr) "early checker/tracer errors disagree"
    (Just checked, Just (Right trace)) ->
      assert (checked == grammarV1TraceOutcome trace)
        ("traced checker disagrees with ordinary checker: " <> show checked
          <> " /= " <> show (grammarV1TraceOutcome trace))
    _ -> Left ("competence/outcome mismatch: " <> show (normal, observed))

successfulPreparation
  :: Text.Text -> Text.Text -> Either String GrammarV1BorrowResourceTrace
successfulPreparation label source = do
  parsed <- parseFun label source
  case grammarV1CheckedBorrowResourceFunctionTrace
    emptyStaticContext (DeclarationKey "decl.FSEM01LoanTrace") parsed of
    Just (Right trace) -> Right trace
    other -> Left ("source did not enter traced fragment: " <> show other)

unsupportedDoesNotFabricateTrace :: Either String ()
unsupportedDoesNotFabricateTrace = do
  mapM_ (uncurry check)
    [("unsupported-U8", unrestrictedOwner), ("unknown-owner", unresolvedOwner)]
  where
    check label source = do
      parsed <- parseFun label source
      let observed = grammarV1CheckedBorrowResourceFunctionTrace
            emptyStaticContext (DeclarationKey "decl.FSEM01LoanTrace") parsed
      assert (observed == Nothing)
        ("unsupported source fabricated trace: " <> show observed)

parseFun :: Text.Text -> Text.Text -> Either String GrammarV1FunctionDecl
parseFun label source = do
  parsed <- mapLeft show (parseGrammarV1StructuralSource label source)
  case grammarV1TopLevelDecls parsed of
    [Located _ topLevel] ->
      case locatedValue (grammarV1Declaration topLevel) of
        GrammarV1FunctionDeclaration fun -> Right fun
        other -> Left ("expected source function, got " <> show other)
    xs -> Left ("expected exactly one function, got " <> show (length xs))

printTrace :: String -> Text.Text -> IO ()
printTrace label source =
  case successfulPreparation (Text.pack label) source of
    Left _ -> pure ()
    Right result -> do
      putStrLn ("TRACE FSEM-01 " <> label <> ":")
      mapM_ (putStrLn . ("  " <>) . show)
        (grammarV1TraceCheckpoints result)
      putStrLn ("  outcome = " <> show (grammarV1TraceOutcome result))

unitBody, viewThenUnit, escapingView, unrestrictedOwner, unresolvedOwner, viewShadow
  :: Text.Text
unitBody = Text.unlines
  [ "fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {"
  , "  borrow owner as view { unit; };"
  , "  return owner;"
  , "}"
  ]
viewThenUnit = Text.unlines
  [ "fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {"
  , "  borrow owner as view { view; unit; };"
  , "  return owner;"
  , "}"
  ]
escapingView = Text.unlines
  [ "fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {"
  , "  borrow owner as view { view; };"
  , "  return owner;"
  , "}"
  ]
unrestrictedOwner = Text.unlines
  [ "fn loan(owner : U8) -> U8 satisfies C {"
  , "  borrow owner as view { view; };"
  , "  return owner;"
  , "}"
  ]
unresolvedOwner = Text.unlines
  [ "fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {"
  , "  borrow strange as view { view; };"
  , "  return owner;"
  , "}"
  ]
viewShadow = Text.unlines
  [ "fn loan(owner : Bytes[8]) -> Bytes[8] satisfies C {"
  , "  borrow owner as owner { owner; };"
  , "  return owner;"
  , "}"
  ]

assert :: Bool -> String -> Either String ()
assert ok detail = if ok then Right () else Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
