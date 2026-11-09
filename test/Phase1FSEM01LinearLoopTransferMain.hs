{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01 L-2: parsed Linear Bytes loop state with actual Core move/rebind.
-- The code checks one STATIC source/reentry step, never a runtime iteration.
module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import qualified Phil.Core.Context as Core
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Mode (..), Name (..), RefTerm (..), Ty (..))
import Phil.Surface.Check.Engine
  ( SourceBoolJoinInvariant (..), SourceLinearLoopRun (..) )
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
import Phil.Surface.GrammarV1.SourceLinearLoopTransfer
  ( GrammarV1LinearLoopError (..), GrammarV1LinearLoopTrace (..)
  , grammarV1CheckedLinearLoopTransferTrace )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.l2.cycle"

bytes8 :: Ty
bytes8 = TyBytes (RefNat 8)

assert :: Bool -> String -> Either String ()
assert condition message = if condition then Right () else Left message

parseOne :: Text -> Either String GrammarV1FunctionDecl
parseOne input = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "fsem01-linear-loop" input)
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1FunctionDeclaration fn -> Right fn
      other -> Left ("expected parsed function, got " ++ show other)
    other -> Left ("expected one declaration, got " ++ show (length other))

check :: Text -> Maybe (Either GrammarV1LinearLoopError GrammarV1LinearLoopTrace)
check input = case parseOne input of
  Left _ -> Nothing
  Right fn -> grammarV1CheckedLinearLoopTransferTrace
    emptyStaticContext root fn

checked :: Text -> Either String GrammarV1LinearLoopTrace
checked input = do
  fn <- parseOne input
  case grammarV1CheckedLinearLoopTransferTrace emptyStaticContext root fn of
    Just (Right evidence) -> Right evidence
    other -> Left ("not exact checked source Linear loop: " ++ show other)

binderName :: GrammarV1ResolvedBinder -> Name
binderName = grammarV1ResolvedBinderCoreName

before :: GrammarV1LinearLoopTrace -> Core.ResourceContext
before evidence = Core.ResourceContext
  { Core.unrestrictedBindings =
      Map.singleton (binderName (linearLoopFlagBinder evidence)) TyBool
  , Core.affineBindings = Map.empty
  , Core.linearBindings = Map.fromList
      ((binderName (linearLoopPayloadBinder evidence),bytes8) :
        case (linearLoopAlternateBinder evidence,linearLoopAlternateType evidence) of
          (Just alt,Just ty) -> [(binderName alt,ty)]
          _ -> [])
  , Core.sharedLoans = Set.empty
  }

entryConsumed :: GrammarV1LinearLoopTrace -> Core.ResourceContext
entryConsumed evidence = (before evidence)
  { Core.linearBindings =
      Map.delete (binderName (linearLoopPayloadBinder evidence))
        (Core.linearBindings (before evidence)) }

header :: GrammarV1LinearLoopTrace -> Core.ResourceContext
header evidence = (entryConsumed evidence)
  { Core.linearBindings =
      Map.insert (binderName (linearLoopHeaderBinder evidence)) bytes8
        (Core.linearBindings (entryConsumed evidence)) }

backedgeConsumed :: GrammarV1LinearLoopTrace -> Core.ResourceContext
backedgeConsumed evidence = (header evidence)
  { Core.linearBindings =
      Map.delete (binderName (linearLoopBackedgeBinder evidence))
        (Core.linearBindings (header evidence)) }

checkIdentity :: GrammarV1LinearLoopTrace -> Either String SourceLinearLoopRun
checkIdentity evidence = do
  let names = map binderName
        ([linearLoopFlagBinder evidence,linearLoopPayloadBinder evidence,
          linearLoopHeaderBinder evidence] ++
         maybe [] pure (linearLoopAlternateBinder evidence))
      entry = binderName (linearLoopEntryBinder evidence)
      allowed = map binderName
        ([linearLoopFlagBinder evidence,linearLoopPayloadBinder evidence,
          linearLoopHeaderBinder evidence] ++
         maybe [] pure (linearLoopAlternateBinder evidence))
      run = linearLoopNativeRun evidence
  assert (length (Set.fromList names) == length names)
    "declaration-rooted source owner/header identities collided"
  assert (elem entry allowed)
    "entry operand not derived from exact source binder"
  assert (linearLoopHeaderCheckedMode evidence ==
          CheckedTypeMode bytes8 Linear)
    "source loop header was not independently checked Linear Bytes[8]"
  assert (sourceLinearLoopBefore run == Just (before evidence) &&
          sourceLinearLoopOutcome run == linearLoopCheckedOutcome evidence)
    "trace and independent production checker diverged"
  Right run

checkAccepted :: Text -> Bool -> Either String ()
checkAccepted input withAlternate = do
  evidence <- checked input
  run <- checkIdentity evidence
  let old = binderName (linearLoopPayloadBinder evidence)
      slot = binderName (linearLoopHeaderBinder evidence)
      initial = before evidence
      spent = entryConsumed evidence
      bound = header evidence
      reentrySpent = backedgeConsumed evidence
  assert ((linearLoopAlternateBinder evidence /= Nothing) == withAlternate)
    "source optional alternate owner was incorrectly inferred"
  assert (binderName (linearLoopEntryBinder evidence) == old &&
          binderName (linearLoopBackedgeBinder evidence) == slot &&
          old /= slot)
    "source old owner and fresh header were not distinct lexical identities"
  assert (linearLoopInvariantProof evidence == SourceBoolInvariantProvenTrue)
    "source invariant wasn't checked literal true"
  assert (sourceLinearLoopEntryConsumed run == Just spent &&
          sourceLinearLoopHeaderBound run == Just bound &&
          sourceLinearLoopBackedgeConsumed run == Just reentrySpent &&
          sourceLinearLoopBackedgeRebound run == Just bound &&
          sourceLinearLoopReentered run == Just bound &&
          sourceLinearLoopEntryType run == Just (Linear,bytes8) &&
          sourceLinearLoopBackedgeType run == Just (Linear,bytes8) &&
          linearLoopCheckedOutcome evidence == Right ())
    "production entry/consume/rebind/rejoin checkpoint was not exact"
  assert (Core.consumeLinear old initial == Right (bytes8,spent) &&
          Core.insertBinding Linear slot bytes8 spent == Right bound &&
          Core.consumeLinear slot bound == Right (bytes8,reentrySpent) &&
          Core.insertBinding Linear slot bytes8 reentrySpent == Right bound &&
          Core.joinContinuing [bound,bound] == Right bound)
    "independent native Core move/rebind/join disagreed"
  assert (Map.notMember old (Core.linearBindings bound) &&
          Map.lookup slot (Core.linearBindings bound) == Just bytes8 &&
          Map.size (Core.linearBindings bound) ==
            (if withAlternate then 2 else 1) &&
          Core.sharedLoans bound == Set.empty)
    "source old owner remained usable or unique owner was duplicated"
  assert (Core.insertBinding Linear slot bytes8 bound ==
          Left (Core.DuplicateBinding slot))
    "native Core unexpectedly allowed duplicate live loop-header owner"

checkWrongEntry :: Text -> Either String ()
checkWrongEntry input = do
  evidence <- checked input
  run <- checkIdentity evidence
  assert (sourceLinearLoopEntryConsumed run == Nothing &&
          sourceLinearLoopHeaderBound run == Nothing &&
          sourceLinearLoopBackedgeConsumed run == Nothing &&
          sourceLinearLoopBackedgeRebound run == Nothing &&
          sourceLinearLoopReentered run == Nothing)
    "wrong-type entry invented header or reentry"
  case linearLoopCheckedOutcome evidence of
    Left err -> assert
      (surfaceErrorClass err == TypeMismatch &&
       surfaceErrorDetail err ==
        "linear loop entry must move the exact Linear Bytes owner")
      ("incorrect entry type diagnostic: " ++ show err)
    Right () -> Left "unrestricted Bool accepted as Linear Bytes owner"

checkWrongBackedge :: Text -> Either String ()
checkWrongBackedge input = do
  evidence <- checked input
  run <- checkIdentity evidence
  assert (sourceLinearLoopEntryConsumed run == Just (entryConsumed evidence) &&
          sourceLinearLoopHeaderBound run == Just (header evidence) &&
          sourceLinearLoopBackedgeConsumed run == Nothing &&
          sourceLinearLoopBackedgeRebound run == Nothing &&
          sourceLinearLoopReentered run == Nothing)
    "wrong type/width backedge invented completed move/reentry"
  case linearLoopCheckedOutcome evidence of
    Left err -> assert
      (surfaceErrorClass err == TypeMismatch &&
       surfaceErrorDetail err ==
        "linear loop continue must move the exact Linear Bytes owner")
      ("incorrect backedge mismatch diagnostic: " ++ show err)
    Right () -> Left "wrong type or width owner was accepted as loop backedge"

checkStale :: Text -> Either String ()
checkStale input = do
  evidence <- checked input
  run <- checkIdentity evidence
  let old = binderName (linearLoopPayloadBinder evidence)
  assert (sourceLinearLoopEntryConsumed run == Just (entryConsumed evidence) &&
          sourceLinearLoopHeaderBound run == Just (header evidence) &&
          sourceLinearLoopBackedgeConsumed run == Nothing &&
          sourceLinearLoopBackedgeRebound run == Nothing &&
          sourceLinearLoopReentered run == Nothing)
    "stale original owner manufactured a continuing edge"
  case linearLoopCheckedOutcome evidence of
    Left err -> assert
      (surfaceErrorClass err == StructuralUse &&
       surfaceErrorDetail err ==
         "unknown or consumed binding: " <> unName old)
      ("wrong exact stale-source error: " ++ show err)
    Right () -> Left "already-moved source owner was reused"

checkDuplicate :: Text -> Either String ()
checkDuplicate input = do
  evidence <- checked input
  run <- checkIdentity evidence
  let slot = binderName (linearLoopHeaderBinder evidence)
  assert (sourceLinearLoopHeaderBound run == Just (header evidence) &&
          sourceLinearLoopBackedgeConsumed run == Just (backedgeConsumed evidence) &&
          sourceLinearLoopBackedgeType run == Just (Linear,bytes8) &&
          sourceLinearLoopBackedgeRebound run == Nothing &&
          sourceLinearLoopReentered run == Nothing)
    "other same-width owner laundered over a still-live loop-header owner"
  case linearLoopCheckedOutcome evidence of
    Left err -> assert
      (surfaceErrorClass err == StructuralUse &&
       surfaceErrorDetail err ==
        Text.pack (show (Core.DuplicateBinding slot)))
      ("duplicate live ownership did not produce exact Core error: " ++ show err)
    Right () -> Left "a second live owner replaced the original header"

checkUnproved :: Text -> Either String ()
checkUnproved input = do
  evidence <- checked input
  run <- checkIdentity evidence
  assert (linearLoopInvariantProof evidence == SourceBoolInvariantUnproved &&
          sourceLinearLoopEntryConsumed run == Just (entryConsumed evidence) &&
          sourceLinearLoopHeaderBound run == Just (header evidence) &&
          sourceLinearLoopBackedgeConsumed run == Nothing &&
          sourceLinearLoopBackedgeRebound run == Nothing &&
          sourceLinearLoopReentered run == Nothing)
    "unproved invariant introduced fabricated backedge resource state"
  case linearLoopCheckedOutcome evidence of
    Left err -> assert (surfaceErrorClass err == MissingEvidence &&
       surfaceErrorDetail err ==
        "loop invariant has no checked proof for this bounded source backedge")
      ("unexpected invariant error: " ++ show err)
    Right () -> Left "false loop invariant was assumed"

checkArity :: Text -> Int -> Either String ()
checkArity input actuals = case check input of
  Just (Left (LinearLoopArityError
    (LoopControlArityMismatch ContinueControl 1 found))) ->
      assert (found == actuals) "wrong LoopControl actual arity"
  other -> Left ("explicit bad continue arity was not rejected: " ++ show other)

checkForward :: Text -> Either String ()
checkForward input = case check input of
  Just (Left (LinearLoopScopeError
    (GrammarV1LoopStateReferenceError
      (GrammarV1LexicalReferenceForwardReference _)))) -> Right ()
  other -> Left ("future loop-header initializer escaped scope: " ++ show other)

checkShadow :: Text -> Either String ()
checkShadow input = case check input of
  Just (Left (LinearLoopScopeError
    (GrammarV1LoopStateBinderError (GrammarV1ActiveShadowing _ _)))) -> Right ()
  other -> Left ("active header owner shadow escaped lexical checker: " ++ show other)

checkUnsupported :: Text -> String -> Either String ()
checkUnsupported input explanation = do
  _ <- parseOne input
  assert (check input == Nothing)
    ("out-of-fragment source was silently admitted: " ++ explanation)

main :: IO ()
main = do
  let get filename = TextIO.readFile
        ("test/fixtures/fsem01-linear-loop-transfer-v1/" ++ filename ++ ".phil")
  accepted <- get "accepted-owner"
  withAlt4 <- get "accepted-other-linear-width"
  withAlt8 <- get "accepted-same-width-spectator"
  renamed <- get "accepted-renamed-header"
  wrongEntry <- get "wrong-entry-bool"
  wrongMode <- get "wrong-continue-bool"
  stale <- get "stale-original-owner"
  wrongWidth <- get "wrong-continue-width"
  duplicate <- get "duplicate-live-header-owner"
  falseProof <- get "unproved-invariant"
  zero <- get "zero-continue-actual"
  two <- get "two-continue-actuals"
  forward <- get "future-header-initializer"
  shadow <- get "shadow-source-payload"
  unsupported <- mapM get
    [ "missing-invariant", "wrong-header-width"
    , "two-header-slots", "continue-literal"
    , "continue-unknown", "break-instead-of-continue"
    , "body-before-continue", "wrong-result-type"
    , "untyped-header" ]
  let result = do
        checkAccepted accepted False
        checkAccepted withAlt4 True
        checkAccepted withAlt8 True
        checkAccepted renamed False
        checkWrongEntry wrongEntry
        checkWrongBackedge wrongMode
        checkWrongBackedge wrongWidth
        checkStale stale
        checkDuplicate duplicate
        checkUnproved falseProof
        checkArity zero 0
        checkArity two 2
        checkForward forward
        checkShadow shadow
        mapM_ (uncurry checkUnsupported) (zip unsupported
          [ "missing invariant", "wrong header width", "two state slots"
          , "literal actual", "unresolved/global actual", "break not continue"
          , "body statements before continue", "non-Unit result"
          , "untyped loop header" ])
  case result of
    Right () -> putStrLn
      "PASS: 23 real parsed Linear Bytes loop sources, exact native owner move/rebind/reentry, stale and duplicate owner refusal"
    Left err -> putStrLn ("FAIL: " ++ err) >> exitFailure
