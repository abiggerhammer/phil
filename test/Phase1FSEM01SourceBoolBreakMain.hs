{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01 L-1: real parsed source break, scope exit, and native terminal debt.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Control (..), Mode (..), Name (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine
  ( SourceBoolJoinInvariant (..), SourceBoolLoopBreakRun (..) )
import Phil.Surface.Check.LoopControl
  ( LoopControlError (..), LoopControlKind (BreakControl) )
import Phil.Surface.Check.Types
  ( RejectionClass (..), SurfaceCheckError (..), SurfaceCheckResult (..) )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError (..), GrammarV1ResolvedBinder (..) )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1LexicalReferenceError (..) )
import Phil.Surface.GrammarV1.LoopStateScope
  ( GrammarV1LoopStateScopeError (..) )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1FunctionDecl, GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..), GrammarV1Declaration (..)
  , parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceBoolLoopBreak
  ( GrammarV1SourceBoolLoopBreakError (..)
  , GrammarV1SourceBoolLoopBreakTrace (..)
  , grammarV1CheckedSourceBoolLoopBreakTrace )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.l1.loop.exit"

bytes8, bytes4 :: Ty
bytes8 = TyBytes (RefNat 8)
bytes4 = TyBytes (RefNat 4)

assert :: Bool -> String -> Either String ()
assert condition message = if condition then Right () else Left message

parseOne :: Text -> Either String GrammarV1FunctionDecl
parseOne source = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "fsem01-bool-break" source)
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1FunctionDeclaration fn -> Right fn
      other -> Left ("source is not a function: " ++ show other)
    other -> Left ("source had " ++ show (length other) ++ " declarations")

check :: Text ->
  Maybe (Either GrammarV1SourceBoolLoopBreakError GrammarV1SourceBoolLoopBreakTrace)
check source = case parseOne source of
  Left _ -> Nothing
  Right fn ->
    grammarV1CheckedSourceBoolLoopBreakTrace emptyStaticContext root fn

checked :: Text -> Either String GrammarV1SourceBoolLoopBreakTrace
checked source = do
  fn <- parseOne source
  case grammarV1CheckedSourceBoolLoopBreakTrace emptyStaticContext root fn of
    Just (Right evidence) -> Right evidence
    other -> Left ("not a checked source break: " ++ show other)

name :: GrammarV1ResolvedBinder -> Name
name = grammarV1ResolvedBinderCoreName

before :: GrammarV1SourceBoolLoopBreakTrace -> Core.ResourceContext
before evidence = Core.ResourceContext
  { Core.unrestrictedBindings =
      Map.singleton (name (boolLoopBreakSeedBinder evidence)) TyBool
  , Core.affineBindings = Map.empty
  , Core.linearBindings = Map.fromList
      ( (name (boolLoopBreakPayloadBinder evidence),bytes8) :
        case boolLoopBreakDebtBinder evidence of
          Nothing -> []
          Just debt -> [(name debt,bytes4)] )
  , Core.sharedLoans = Set.empty
  }

header :: GrammarV1SourceBoolLoopBreakTrace -> Core.ResourceContext
header evidence = (before evidence)
  { Core.unrestrictedBindings =
      Map.insert (name (boolLoopBreakHeaderBinder evidence)) TyBool
        (Core.unrestrictedBindings (before evidence)) }

returned :: GrammarV1SourceBoolLoopBreakTrace -> Core.ResourceContext
returned evidence = (before evidence)
  { Core.linearBindings =
      Map.delete (name (boolLoopBreakPayloadBinder evidence))
        (Core.linearBindings (before evidence)) }

checkIdentities :: GrammarV1SourceBoolLoopBreakTrace
  -> Either String SourceBoolLoopBreakRun
checkIdentities evidence = do
  let names = map name
        ([ boolLoopBreakSeedBinder evidence
         , boolLoopBreakPayloadBinder evidence
         , boolLoopBreakHeaderBinder evidence ] ++
         maybe [] pure (boolLoopBreakDebtBinder evidence))
      run = boolLoopBreakNativeRun evidence
      entry = name (boolLoopBreakEntryBinder evidence)
      seed = name (boolLoopBreakSeedBinder evidence)
      payload = name (boolLoopBreakPayloadBinder evidence)
  assert (length (Set.fromList names) == length names)
    "source parameter/header binder identities collided"
  assert (elem entry [seed,payload])
    "source entry was not resolved to a real parameter occurrence"
  assert (boolLoopBreakSlotCheckedMode evidence ==
          CheckedTypeMode TyBool Unrestricted)
    "loop header was not independently typed as Unrestricted Bool"
  assert (sourceBoolLoopBreakBefore run == Just (before evidence) &&
          sourceBoolLoopBreakOutcome run == boolLoopBreakCheckedOutcome evidence)
    "normal production and tracing checker disagree at exact source state"
  Right run

checkAccepted :: Text -> SourceBoolJoinInvariant -> Either String ()
checkAccepted source expectedInvariant = do
  evidence <- checked source
  run <- checkIdentities evidence
  let sourceBefore = before evidence
      sourceHeader = header evidence
      sourceReturned = returned evidence
      headerName = name (boolLoopBreakHeaderBinder evidence)
      payloadName = name (boolLoopBreakPayloadBinder evidence)
  assert (boolLoopBreakInvariantProof evidence == expectedInvariant)
    "actual invariant was not justified from the exact source binder"
  assert (sourceBoolLoopBreakEntry run == Just sourceBefore &&
          sourceBoolLoopBreakHeader run == Just sourceHeader &&
          sourceBoolLoopBreakExited run == Just sourceBefore &&
          sourceBoolLoopBreakTerminal run == Just sourceReturned &&
          sourceBoolLoopBreakEntryType run == Just (Unrestricted,TyBool))
    "real entry/header/pruned-exit/returned native Core cut is wrong"
  assert (Core.insertBinding Unrestricted headerName TyBool sourceBefore ==
          Right sourceHeader &&
          Core.consumeLinear payloadName sourceBefore ==
          Right (bytes8,sourceReturned) &&
          Core.ensureComplete sourceReturned == Right ())
    "independent Core header insert, linear consume or completion differs"
  assert (Core.linearBindings sourceHeader == Core.linearBindings sourceBefore &&
          Core.sharedLoans sourceReturned == Set.empty)
    "linear/loan preservation failed at break"
  assert (boolLoopBreakCheckedOutcome evidence ==
          Right (SurfaceCheckResult "exit" [Return bytes8]))
    "source break did not reach checked Bytes terminal return"

checkDebt :: Text -> Either String ()
checkDebt source = do
  evidence <- checked source
  run <- checkIdentities evidence
  debt <- maybe (Left "negative lacks a source-declared debt owner") Right
    (boolLoopBreakDebtBinder evidence)
  let debtContext = Map.singleton (name debt) bytes4
  assert (sourceBoolLoopBreakEntry run == Just (before evidence) &&
          sourceBoolLoopBreakHeader run == Just (header evidence) &&
          sourceBoolLoopBreakExited run == Just (before evidence) &&
          sourceBoolLoopBreakTerminal run == Nothing)
    "unpaid linear debt fabricated a successful terminal successor"
  case boolLoopBreakCheckedOutcome evidence of
    Left err -> assert
      (surfaceErrorClass err == LinearCompletion &&
       surfaceErrorDetail err ==
         Text.pack (show (Core.UnconsumedLinearResources debtContext)))
      ("expected exact unpaid source owner diagnostic, got " ++ show err)
    Right _ -> Left "return incorrectly accepted with outstanding Bytes"

checkUnproved :: Text -> Either String ()
checkUnproved source = do
  evidence <- checked source
  run <- checkIdentities evidence
  assert (boolLoopBreakInvariantProof evidence == SourceBoolInvariantUnproved &&
          sourceBoolLoopBreakEntry run == Just (before evidence) &&
          sourceBoolLoopBreakHeader run == Just (header evidence) &&
          sourceBoolLoopBreakExited run == Nothing &&
          sourceBoolLoopBreakTerminal run == Nothing)
    "unproved invariant fabricated a break exit or returned state"
  case boolLoopBreakCheckedOutcome evidence of
    Left err -> assert
      (surfaceErrorClass err == MissingEvidence &&
       surfaceErrorDetail err ==
        "loop invariant has no checked proof for this bounded source backedge")
      ("wrong source invariant evidence error: " ++ show err)
    Right _ -> Left "unproved loop invariant was silently accepted"

checkWrongEntry :: Text -> Either String ()
checkWrongEntry source = do
  evidence <- checked source
  run <- checkIdentities evidence
  assert (sourceBoolLoopBreakEntry run == Nothing &&
          sourceBoolLoopBreakHeader run == Nothing &&
          sourceBoolLoopBreakExited run == Nothing &&
          sourceBoolLoopBreakTerminal run == Nothing)
    "wrong typed entry fabricated a header or terminal successor"
  case boolLoopBreakCheckedOutcome evidence of
    Left err -> assert (surfaceErrorClass err == TypeMismatch &&
      surfaceErrorDetail err ==
        "loop break initial entry must produce one unrestricted Bool")
      ("wrong typed source entry error: " ++ show err)
    Right _ -> Left "Linear Bytes accepted as Bool loop entry"

checkArity :: Text -> Int -> Either String ()
checkArity source actual = case check source of
  Just (Left (BoolLoopBreakArityError
    (LoopControlArityMismatch BreakControl 0 found))) ->
      assert (found == actual) "incorrect exact break arity"
  other -> Left ("source break arity not rejected: " ++ show other)

checkForward :: Text -> Either String ()
checkForward source = case check source of
  Just (Left (BoolLoopBreakScopeError
    (GrammarV1LoopStateReferenceError
      (GrammarV1LexicalReferenceForwardReference _)))) -> Right ()
  other -> Left ("future header initializer not rejected: " ++ show other)

checkShadow :: Text -> Either String ()
checkShadow source = case check source of
  Just (Left (BoolLoopBreakScopeError
    (GrammarV1LoopStateBinderError
      (GrammarV1ActiveShadowing _ _)))) -> Right ()
  other -> Left ("source header shadowing not rejected: " ++ show other)

checkUnsupported :: Text -> String -> Either String ()
checkUnsupported source label = do
  _ <- parseOne source
  assert (check source == Nothing)
    ("out-of-scope/unsupported source unexpectedly accepted: " ++ label)

main :: IO ()
main = do
  let get key = TextIO.readFile
        ("test/fixtures/fsem01-source-bool-break-v1/" ++ key ++ ".phil")
  accepted <- get "accepted-reflexive"
  literalTrue <- get "accepted-true"
  emptyParens <- get "accepted-break-parenthesized"
  unprovedFalse <- get "unproved-false"
  unprovedCross <- get "unproved-seed"
  wrongEntry <- get "wrong-entry-type"
  debt <- get "unpaid-linear-debt"
  arity1 <- get "break-one-actual"
  arity2 <- get "break-two-actuals"
  forward <- get "forward-initializer"
  shadow <- get "shadow-header"
  unsupported <- mapM get
    [ "missing-invariant", "unsupported-header-type"
    , "unsupported-two-header-slots", "return-header-out-of-scope"
    , "return-seed-instead-of-payload", "wrong-return-width"
    , "unsupported-continue-instead-of-break"
    , "unsupported-break-after-statement" ]
  let result = do
        checkAccepted accepted SourceBoolInvariantProvenReflexive
        checkAccepted literalTrue SourceBoolInvariantProvenTrue
        checkAccepted emptyParens SourceBoolInvariantProvenReflexive
        checkUnproved unprovedFalse
        checkUnproved unprovedCross
        checkWrongEntry wrongEntry
        checkDebt debt
        checkArity arity1 1
        checkArity arity2 2
        checkForward forward
        checkShadow shadow
        mapM_ (uncurry checkUnsupported) (zip unsupported
          [ "missing invariant", "wrong slot type", "two slots"
          , "returned dead header", "returned wrong source parameter"
          , "wrong declared return width", "continue instead of break"
          , "break not final body step" ])
  case result of
    Right () -> putStrLn
      "PASS: 19 source Bool-break witnesses, exact scoped exit and terminal ownership/error prefixes"
    Left err -> putStrLn ("FAIL: " ++ err) >> exitFailure
