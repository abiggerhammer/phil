{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01 L-1: parsed Grammar-v1 loop initial/header/continue resource
-- correspondence. Full function execution and loop termination are not tested.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Mode (..), Name (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine
  ( SourceBoolJoinInvariant (..), SourceBoolLoopRun (..) )
import Phil.Surface.Check.LoopControl
  ( LoopControlError (..), LoopControlKind (ContinueControl) )
import Phil.Surface.Check.Types
  ( RejectionClass (..), SurfaceCheckError (..) )
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
import Phil.Surface.GrammarV1.SourceBoolLoopResource
  ( GrammarV1SourceBoolLoopError (..), GrammarV1SourceBoolLoopTrace (..)
  , grammarV1CheckedSourceBoolLoopTrace )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.l1.cycle"

bytes8 :: Ty
bytes8 = TyBytes (RefNat 8)

assert :: Bool -> String -> Either String ()
assert condition message = if condition then Right () else Left message

parseOne :: Text -> Either String GrammarV1FunctionDecl
parseOne source = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "fsem01-source-loop" source)
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1FunctionDeclaration fn -> Right fn
      other -> Left ("expected function, got " ++ show other)
    _ -> Left "expected exactly one parsed declaration"

check :: Text ->
  Maybe (Either GrammarV1SourceBoolLoopError GrammarV1SourceBoolLoopTrace)
check source = case parseOne source of
  Left _ -> Nothing
  Right fn ->
    grammarV1CheckedSourceBoolLoopTrace emptyStaticContext root fn

checked :: Text -> Either String GrammarV1SourceBoolLoopTrace
checked source = do
  fn <- parseOne source
  case grammarV1CheckedSourceBoolLoopTrace emptyStaticContext root fn of
    Just (Right evidence) -> Right evidence
    other -> Left ("no bounded checked loop: " ++ show other)

name :: GrammarV1ResolvedBinder -> Name
name = grammarV1ResolvedBinderCoreName

names :: GrammarV1SourceBoolLoopTrace -> [Name]
names evidence = map name
  [ boolLoopSeedBinder evidence, boolLoopAlternativeBinder evidence
  , boolLoopPayloadBinder evidence, boolLoopHeaderBinder evidence ]

before :: GrammarV1SourceBoolLoopTrace -> Core.ResourceContext
before evidence = case names evidence of
  [seed,alternative,payload,_] -> Core.ResourceContext
    { Core.unrestrictedBindings =
        Map.fromList [(seed,TyBool),(alternative,TyBool)]
    , Core.affineBindings = Map.empty
    , Core.linearBindings = Map.singleton payload bytes8
    , Core.sharedLoans = Set.empty }
  _ -> error "four source identities required"

header :: GrammarV1SourceBoolLoopTrace -> Core.ResourceContext
header evidence = case names evidence of
  [_,_,_,cursor] -> (before evidence)
    { Core.unrestrictedBindings =
        Map.insert cursor TyBool
          (Core.unrestrictedBindings (before evidence)) }
  _ -> error "four source identities required"

checkIdentity :: GrammarV1SourceBoolLoopTrace -> Either String SourceBoolLoopRun
checkIdentity evidence = do
  let ns = names evidence
      run = boolLoopNativeRun evidence
      entry = name (boolLoopEntryBinder evidence)
      successor = name (boolLoopBackedgeBinder evidence)
  assert (length (Set.fromList ns) == 4)
    "source parameter and header identities were not distinct"
  assert (elem entry (take 3 ns) && elem successor ns)
    "entry or backedge actual did not resolve to exact source binder"
  assert (boolLoopHeaderCheckedMode evidence ==
    CheckedTypeMode TyBool Unrestricted)
    "loop state type/mode was not independently source checked"
  assert (sourceBoolLoopBefore run == Just (before evidence) &&
          sourceBoolLoopOutcome run == boolLoopCheckedOutcome evidence)
    "source-derived production and tracing paths diverged"
  Right run

checkAccepted :: Text -> SourceBoolJoinInvariant -> Int -> Int -> Either String ()
checkAccepted source expectedProof entryIndex backedgeIndex = do
  evidence <- checked source
  run <- checkIdentity evidence
  let ns = names evidence
      start = before evidence
      bound = header evidence
  assert (name (boolLoopEntryBinder evidence) == ns !! entryIndex &&
          name (boolLoopBackedgeBinder evidence) == ns !! backedgeIndex)
    "entry/continue operand was silently substituted by display name"
  assert (boolLoopInvariantProof evidence == expectedProof)
    "source invariant was not independently justified"
  assert (sourceBoolLoopEntry run == Just start &&
          sourceBoolLoopHeader run == Just bound &&
          sourceBoolLoopBackedge run == Just bound &&
          sourceBoolLoopReentered run == Just bound &&
          sourceBoolLoopEntryType run == Just (Unrestricted,TyBool) &&
          sourceBoolLoopBackedgeType run == Just (Unrestricted,TyBool) &&
          boolLoopCheckedOutcome evidence == Right ())
    "native initial/header/backedge/join resource cut was not reached"
  assert (Core.insertBinding Unrestricted (ns !! 3) TyBool start ==
            Right bound &&
          Core.joinContinuing [bound,bound] == Right bound)
    "actual Core insertion or reentry join disagreed with production trace"
  assert (Core.linearBindings bound == Core.linearBindings start &&
          Core.sharedLoans bound == Core.sharedLoans start)
    "linear spectator or closed shared loans were lost across loop backedge"

checkUnproved :: Text -> Either String ()
checkUnproved source = do
  evidence <- checked source
  run <- checkIdentity evidence
  assert (boolLoopInvariantProof evidence == SourceBoolInvariantUnproved &&
          sourceBoolLoopEntry run == Just (before evidence) &&
          sourceBoolLoopHeader run == Just (header evidence) &&
          sourceBoolLoopBackedge run == Nothing &&
          sourceBoolLoopReentered run == Nothing)
    "unproved invariant fabricated a checked backedge or reentry"
  case boolLoopCheckedOutcome evidence of
    Left err -> assert (surfaceErrorClass err == MissingEvidence &&
      surfaceErrorDetail err ==
        "loop invariant has no checked proof for this bounded source backedge")
      ("incorrect invariant rejection: " ++ show err)
    Right () -> Left "unproved source invariant was silently admitted"

checkWrongEdge :: Text -> Bool -> Either String ()
checkWrongEdge source badEntry = do
  evidence <- checked source
  run <- checkIdentity evidence
  assert (sourceBoolLoopReentered run == Nothing &&
          sourceBoolLoopBackedge run == Nothing &&
          if badEntry
            then sourceBoolLoopEntry run == Nothing &&
                 sourceBoolLoopHeader run == Nothing
            else sourceBoolLoopEntry run == Just (before evidence) &&
                 sourceBoolLoopHeader run == Just (header evidence))
    "ill-typed entry or continue invented a post-error state"
  case boolLoopCheckedOutcome evidence of
    Left err -> assert (surfaceErrorClass err == TypeMismatch &&
      surfaceErrorDetail err ==
        (if badEntry
         then "loop initial entry must produce one unrestricted Bool"
         else "loop continue backedge must produce one unrestricted Bool"))
      ("wrong exact production type rejection: " ++ show err)
    Right () -> Left "Linear Bytes incorrectly supplied as Bool state actual"

checkArity :: Text -> Int -> Either String ()
checkArity source actuals = case check source of
  Just (Left (BoolLoopArityError
    (LoopControlArityMismatch ContinueControl 1 found))) ->
      assert (found == actuals) "wrong exact continue arity"
  other -> Left ("expected real LoopControl arity rejection: " ++ show other)

checkForward :: Text -> Either String ()
checkForward source = case check source of
  Just (Left (BoolLoopScopeError
    (GrammarV1LoopStateReferenceError
      (GrammarV1LexicalReferenceForwardReference _)))) -> Right ()
  other -> Left ("future header was not rejected by scope: " ++ show other)

checkShadow :: Text -> Either String ()
checkShadow source = case check source of
  Just (Left (BoolLoopScopeError
    (GrammarV1LoopStateBinderError (GrammarV1DuplicateBinder _ _)))) ->
      Right ()
  other -> Left ("active header collision was not rejected: " ++ show other)

checkUnsupported :: Text -> String -> Either String ()
checkUnsupported source description = do
  _ <- parseOne source
  assert (check source == Nothing)
    ("unsupported loop form gained accidental competence: " ++ description)

main :: IO ()
main = do
  let get filename = TextIO.readFile
        ("test/fixtures/fsem01-source-bool-loop-v1/" ++ filename ++ ".phil")
  accepted <- get "accepted-reflexive"
  yes <- get "accepted-true"
  backToHeader <- get "accepted-header-backedge"
  swapEntry <- get "accepted-alternative-entry"
  seedContinue <- get "accepted-seed-backedge"
  falseInvariant <- get "unproved-false"
  crossInvariant <- get "unproved-cross"
  wrongEntry <- get "wrong-entry-type"
  wrongBackedge <- get "wrong-backedge-type"
  zero <- get "wrong-arity-zero"
  two <- get "wrong-arity-two"
  forward <- get "forward-initializer"
  shadow <- get "shadow-header"
  unsupported <- mapM get
    [ "missing-invariant", "unsupported-header-type"
    , "unsupported-two-header-slots", "unknown-backedge"
    , "unsupported-backedge-literal" ]
  let result = do
        checkAccepted accepted SourceBoolInvariantProvenReflexive 0 1
        checkAccepted yes SourceBoolInvariantProvenTrue 0 1
        checkAccepted backToHeader SourceBoolInvariantProvenReflexive 0 3
        checkAccepted swapEntry SourceBoolInvariantProvenReflexive 1 1
        checkAccepted seedContinue SourceBoolInvariantProvenReflexive 0 0
        checkUnproved falseInvariant
        checkUnproved crossInvariant
        checkWrongEdge wrongEntry True
        checkWrongEdge wrongBackedge False
        checkArity zero 0
        checkArity two 2
        checkForward forward
        checkShadow shadow
        mapM_ (uncurry checkUnsupported) (zip unsupported
          [ "missing invariant", "non-Bool state slot", "two state slots"
          , "unresolved/static continue actual", "literal continue actual" ])
  case result of
    Right () -> putStrLn
      "PASS: 18 parsed Bool source loop witnesses, exact entry/header/backedge Core contexts and fail-closed error prefixes"
    Left err -> putStrLn ("FAIL: " ++ err) >> exitFailure
