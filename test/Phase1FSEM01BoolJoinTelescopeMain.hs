{-# LANGUAGE OverloadedStrings #-}

-- FSEM-01: real checked source predecessor values into one Bool join slot,
-- exact post-join binder identity and explicit invariant discharge/rejection.
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
  ( SourceBoolJoinInvariant (..), SourceBoolJoinRun (..) )
import Phil.Surface.Check.Types
  ( RejectionClass (..), SurfaceCheckError (..), SurfaceCheckResult (..) )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError (..)
  , GrammarV1ResolvedBinder (..) )
import Phil.Surface.GrammarV1.JoinStateScope
  ( GrammarV1JoinStateScopeError (..) )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1FunctionDecl, GrammarV1SourceFile (..)
  , GrammarV1TopLevelDecl (..), GrammarV1Declaration (..)
  , parseGrammarV1StructuralSource )
import Phil.Surface.GrammarV1.SourceBoolJoinTelescope
  ( GrammarV1BoolJoinError (..), GrammarV1BoolJoinTrace (..)
  , grammarV1CheckedBoolJoinTelescopeTrace )
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

root :: DeclarationKey
root = DeclarationKey "decl.fsem01.bool-join.choose"

bytes8 :: Ty
bytes8 = TyBytes (RefNat 8)

dir :: FilePath
dir = "test/fixtures/fsem01-bool-join-telescope-v1/"

assert :: Bool -> String -> Either String ()
assert b msg = if b then Right () else Left msg

parseOne :: Text -> Either String GrammarV1FunctionDecl
parseOne input = do
  parsed <- either (Left . show) Right
    (parseGrammarV1StructuralSource "fsem01-bool-join" input)
  case grammarV1TopLevelDecls parsed of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1FunctionDeclaration fn -> Right fn
      other -> Left ("source is not one function: " ++ show other)
    other -> Left ("not exactly one function: " ++ show (length other))

check :: Text
  -> Maybe (Either GrammarV1BoolJoinError GrammarV1BoolJoinTrace)
check input = case parseOne input of
  Left _ -> Nothing
  Right fn ->
    grammarV1CheckedBoolJoinTelescopeTrace emptyStaticContext root fn

checked :: Text -> Either String GrammarV1BoolJoinTrace
checked input = do
  fn <- parseOne input
  case grammarV1CheckedBoolJoinTelescopeTrace
      emptyStaticContext root fn of
    Just (Right trace) -> Right trace
    other -> Left ("no exact checked source join: " ++ show other)

flagName, otherName, payloadName, selectedName
  :: GrammarV1BoolJoinTrace -> Name
flagName = grammarV1ResolvedBinderCoreName . boolJoinFlagBinder
otherName = grammarV1ResolvedBinderCoreName . boolJoinOtherBinder
payloadName = grammarV1ResolvedBinderCoreName . boolJoinPayloadBinder
selectedName = grammarV1ResolvedBinderCoreName . boolJoinSlotBinder

incoming :: GrammarV1BoolJoinTrace -> Core.ResourceContext
incoming t = Core.ResourceContext
  { Core.unrestrictedBindings =
      Map.fromList [(flagName t, TyBool),(otherName t,TyBool)]
  , Core.affineBindings = Map.empty
  , Core.linearBindings = Map.singleton (payloadName t) bytes8
  , Core.sharedLoans = Set.empty
  }

postSlot :: GrammarV1BoolJoinTrace -> Core.ResourceContext
postSlot t = (incoming t)
  { Core.unrestrictedBindings =
      Map.insert (selectedName t) TyBool
        (Core.unrestrictedBindings (incoming t)) }

checkIdentity :: GrammarV1BoolJoinTrace -> Either String SourceBoolJoinRun
checkIdentity trace = do
  let names = [flagName trace,otherName trace,payloadName trace,
               selectedName trace]
      run = boolJoinBranchRun trace
  assert (length (Set.fromList names) == 4)
    "source telescope binder reused a predecessor/source parameter identity"
  assert (grammarV1ResolvedBinderDisplayName
            (boolJoinSlotBinder trace) == "selected" &&
          boolJoinSlotCheckedMode trace ==
            CheckedTypeMode TyBool Unrestricted)
    "source slot mode/name diverged from independently checked type"
  assert (sourceBoolJoinBefore run == Just (incoming trace) &&
          sourceBoolJoinOutcome run == boolJoinCheckedOutcome trace)
    "source initial Core context or ordinary/trace production outcomes disagree"
  Right run

checkAccepted :: Text -> SourceBoolJoinInvariant -> Either String ()
checkAccepted input expectedProof = do
  trace <- checked input
  run <- checkIdentity trace
  let first = incoming trace
      selected = selectedName trace
  assert (boolJoinInvariantProof trace == expectedProof)
    "source invariant was not classified by its checked lexical form"
  assert (sourceBoolJoinThen run == Just first &&
          sourceBoolJoinElse run == Just first &&
          sourceBoolJoinCoreJoined run == Just first &&
          sourceBoolJoinBound run == Just (postSlot trace) &&
          sourceBoolJoinThenType run == Just (Unrestricted, TyBool) &&
          sourceBoolJoinElseType run == Just (Unrestricted, TyBool))
    "one real typed source predecessor or join/binder resource cut was lost"
  assert (Core.joinContinuing [first,first] == Right first &&
          Core.insertBinding Unrestricted selected TyBool first ==
            Right (postSlot trace))
    "native Core join or fresh Bool-slot insertion disagreed with source trace"
  assert (boolJoinCheckedOutcome trace ==
          Right (SurfaceCheckResult "choose" [Return bytes8]))
    ("source checked-join did not return the linear owner once: " ++
      show (boolJoinCheckedOutcome trace))

checkUnproved :: Text -> Either String ()
checkUnproved input = do
  trace <- checked input
  run <- checkIdentity trace
  assert (boolJoinInvariantProof trace == SourceBoolInvariantUnproved &&
          sourceBoolJoinThen run == Just (incoming trace) &&
          sourceBoolJoinElse run == Just (incoming trace) &&
          sourceBoolJoinCoreJoined run == Just (incoming trace) &&
          sourceBoolJoinBound run == Just (postSlot trace))
    "unproved invariant was rejected before verifying real predecessor/slot data"
  case boolJoinCheckedOutcome trace of
    Left err -> assert
      (surfaceErrorClass err == MissingEvidence &&
       surfaceErrorDetail err ==
         "join invariant has no checked proof for this bounded source telescope")
      ("incorrect actual production invariant diagnostic: " ++ show err)
    Right _ -> Left "unchecked join invariant was silently admitted"

checkWrongSourceOperand :: Text -> Bool -> Either String ()
checkWrongSourceOperand input wrongLeft = do
  trace <- checked input
  run <- checkIdentity trace
  let first = incoming trace
  assert (sourceBoolJoinCoreJoined run == Nothing &&
          sourceBoolJoinBound run == Nothing &&
          if wrongLeft
            then sourceBoolJoinThen run == Nothing &&
                 sourceBoolJoinElse run == Nothing
            else sourceBoolJoinThen run == Just first &&
                 sourceBoolJoinElse run == Nothing)
    "ill-typed predecessor fabricated a continuing joined slot"
  case boolJoinCheckedOutcome trace of
    Left err -> assert
      (surfaceErrorClass err == TypeMismatch &&
       surfaceErrorDetail err ==
         "join predecessor must produce one unrestricted Bool matching its checked state slot")
      ("wrong real source-predecessor type mismatch: " ++ show err)
    Right _ -> Left "Linear Bytes incorrectly supplied as Unrestricted Bool join state"

checkShadow :: Text -> Either String ()
checkShadow input =
  case check input of
    Just (Left (BoolJoinScopeError
      (GrammarV1JoinStateBinderError
        (GrammarV1DuplicateBinder _ _)))) -> Right ()
    other -> Left ("source join slot shadow was not lexically rejected: " ++
      show other)

checkUnsupported :: Text -> String -> Either String ()
checkUnsupported input description = do
  _ <- parseOne input
  assert (check input == Nothing)
    ("outside-fragment source was accidentally accepted: " ++ description)

main :: IO ()
main = do
  let get name = TextIO.readFile (dir ++ name ++ ".phil")
  refl <- get "accepted-reflexive"
  tru <- get "accepted-true"
  same <- get "accepted-same-source"
  swapped <- get "accepted-different-source"
  falseCase <- get "unproved-false"
  nonRefl <- get "unproved-nonreflexive"
  wrongThen <- get "wrong-then-type"
  wrongElse <- get "wrong-else-type"
  future <- get "branch-reads-future-slot"
  shadow <- get "shadow-parameter"
  unsupportedRelation <- get "unproved-relation"
  unknownInvariant <- get "unresolved-invariant-reference"
  noInvariant <- get "missing-invariant"
  missingElse <- get "missing-else"
  badSlot <- get "wrong-slot-type"
  twoSlots <- get "two-slot-telescope"
  wrongReturn <- get "wrong-return-width"
  wrongUse <- get "wrong-join-use"
  wrongCond <- get "wrong-condition"
  let result = do
        checkAccepted refl SourceBoolInvariantProvenReflexive
        checkAccepted tru SourceBoolInvariantProvenTrue
        checkAccepted same SourceBoolInvariantProvenReflexive
        checkAccepted swapped SourceBoolInvariantProvenReflexive
        checkUnproved falseCase
        checkUnproved nonRefl
        checkWrongSourceOperand wrongThen True
        checkWrongSourceOperand wrongElse False
        checkShadow shadow
        checkUnsupported future "join-state slot visible to predecessor"
        checkUnsupported unsupportedRelation "unproved inequality"
        checkUnsupported unknownInvariant "unknown lexical invariant referent"
        checkUnsupported noInvariant "omitted explicit invariant"
        checkUnsupported missingElse "one predecessor"
        checkUnsupported badSlot "Linear rather than Bool join state"
        checkUnsupported twoSlots "multi-slot telescope"
        checkUnsupported wrongReturn "mismatched source result width"
        checkUnsupported wrongUse "different post-join binder"
        checkUnsupported wrongCond "non-Bool source condition"
        assert (Text.replace "    flag;\n  } else"
                  "    payload;\n  } else" refl == wrongThen)
          "mismatched predecessor is not the one-expression source mutation"
  case result of
    Right () -> putStrLn
      "PASS: checked source Bool phi, fresh post-join binder, invariant proof/refusal, exact Core state"
    Left err -> putStrLn ("FAIL: " ++ err) >> exitFailure
