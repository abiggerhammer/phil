{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Main (main) where

-- Permanent defensive replay for PHIL-AUD-OUTCOME-CARRIER-STRUCTURAL-001.
-- This is a static-checker corpus: no provider, network, or native program runs.
import Control.Exception (SomeException, try)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableInvocationSemantics
  (SurfaceCallableInvocationSemanticAccount (..))
import Phil.Compiler.CallableOutcomeBranchFacts
  (SurfaceCallableOutcomeFactBinding (..), bindSurfaceCallableOutcomeBranchFacts,
   installSurfaceCallableOutcomeBranchFacts)
import Phil.Compiler.CallableOutcomeBranchResidue
  (SurfaceCallableOutcomeObligationBinding (..),
   bindSurfaceCallableOutcomeBranchResidue, installSurfaceCallableOutcomeBranchResidue)
import Phil.Compiler.CallableOutcomeContinuation
  (SurfaceCallableOutcomeContinuation (..), SurfaceCallableOutcomeContinuationDisposition (..))
import Phil.Compiler.CallableOutcomeDispatch
  (SurfaceCallableOutcomeBinding (..), planSurfaceCallableOutcomeDispatch,
   installSurfaceCallableOutcomeDispatch)
import Phil.Core.Callable (CalleeTransition (..))
import Phil.Core.CallableOutcome
  (CallableOutcomeAtom (..), CallableOutcomeClass (..),
   CallableOutcomeContract (..), CallableOutcomeState (..))
import Phil.Core.CallableRefinement (CallableFailure (..))
import Phil.Core.Static (DeclarationKey (..), emptyStaticContext)
import Phil.Core.Syntax (Control (..), Mode (..), Outcome (..), Proposition (..), Ty (..))
import Phil.Surface.Check
import Phil.Surface.Syntax
  (Block (..), CaseArm (..), Component (..), Located (..), Statement (..),
   SourceSpan, SurfaceExpression (..), pattern InvokeExpression, SurfaceFile (..))
import Phil.Surface.Parser (parseSurfaceFile)
import System.Exit (exitFailure)

ownerTy :: Ty
ownerTy = TyOpaque "AuditOwner"

workerKey :: DeclarationKey
workerKey = DeclarationKey "decl.audit.worker"

retryFailure :: CallableFailure
retryFailure = CallableTypedNegative (Outcome "retry")

classes :: [CallableOutcomeClass]
classes = [CallableSuccessOutcome, CallableNonSuccessOutcome retryFailure]

labels :: [Text]
labels = ["ok", "retry"]

needAtom :: Text -> CallableOutcomeAtom
needAtom label = CallableOutcomeAtom ("audit.need." <> label)

factAtom :: Text -> CallableOutcomeAtom
factAtom label = CallableOutcomeAtom ("audit.fact." <> label)

needProp :: Text -> Proposition
needProp label = Atom ("AuditNeed_" <> label) []

contract :: Bool -> Text -> CallableOutcomeClass -> CallableOutcomeContract
contract needs label cls = CallableOutcomeContract
  { callableOutcomeClass = cls
  , callableOutcomeState = CallableOutcomeState ("audit.state." <> label)
  , callableOutcomeCalleeTransition = PreserveCallee
  , callableOutcomePostconditions = Set.empty
  , callableOutcomeResidualObligations = if needs then Set.singleton (needAtom label) else Set.empty
  , callableOutcomeAssumptions = Set.empty
  , callableOutcomeEffects = Set.empty
  , callableOutcomeDischargedFacts = Set.empty
  }

continuation :: SourceSpan -> Text -> CallableOutcomeContract -> SurfaceCallableOutcomeContinuation
continuation sp label c = SurfaceCallableOutcomeContinuation
  { surfaceContinuationInvocationSpan = sp
  , surfaceContinuationArmSpan = sp
  , surfaceContinuationDeclarationKey = workerKey
  , surfaceContinuationSourceLabel = label
  , surfaceContinuationPayload = []
  , surfaceContinuationOutcomeClass = callableOutcomeClass c
  , surfaceContinuationDisposition = SurfaceCallableOutcomeCallerContinues
  , surfaceContinuationState = callableOutcomeState c
  , surfaceContinuationCalleeTransition = callableOutcomeCalleeTransition c
  , surfaceContinuationPostconditions = callableOutcomePostconditions c
  , surfaceContinuationResidualObligations = callableOutcomeResidualObligations c
  , surfaceContinuationAssumptions = callableOutcomeAssumptions c
  , surfaceContinuationEffects = callableOutcomeEffects c
  , surfaceContinuationDischargedFacts = callableOutcomeDischargedFacts c
  , surfaceContinuationContract = c
  }

data Fixture = Owners | Obligations | NoInstallation | ExactEvidence | OkOnlyEvidence | LocalFacts
  deriving (Eq, Show)

baseEnvironment :: Fixture -> SurfaceEnvironment
baseEnvironment fixture = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceInitialBindings = Map.fromList (owners <> boolInput <> evidence)
  , surfaceCallables = Map.fromList
      [ ("Worker", SurfaceCallableSignature workerKey workerParameters Nothing)
      , ("Sink", SurfaceCallableSignature (DeclarationKey "decl.audit.sink") [(Linear, ownerTy)] Nothing)
      , ("InspectDecision", SurfaceCallableSignature
          (DeclarationKey "decl.audit.inspect-decision")
          [(Unrestricted, TyOpaque "CallableDecision")]
          Nothing)
      , ("InspectBool", SurfaceCallableSignature
          (DeclarationKey "decl.audit.inspect-bool")
          [(Unrestricted, TyBool)]
          Nothing)
      ]
  }
  where
    hasOwners = fixture == Owners
    workerParameters = if hasOwners then [(Linear, ownerTy)] else []
    owners = if hasOwners
      then [("input", InitialBinding Linear ownerTy PlainShape)] else []
    boolInput = [("flag", InitialBinding Unrestricted TyBool PlainShape)]
    evidence =
      [ ("evidence_" <> label, InitialBinding Unrestricted (TyProof (needProp label)) PlainShape)
      | label <- labels
      , fixture == ExactEvidence || (fixture == OkOnlyEvidence && label == "ok")
      ]

parseOne :: Text -> Either String (Located Component)
parseOne text = do
  file <- mapLeft show (parseSurfaceFile "audit-outcome-consumer" text)
  case surfaceComponents file of
    [c] -> Right c
    _ -> Left "fixture must parse as exactly one component"

-- This collector covers only expressions used in this corpus.
workerSpans :: Located Component -> [SourceSpan]
workerSpans = blockSpans . componentBody . locatedValue
  where
    blockSpans = concatMap statementSpans . blockStatements . locatedValue
    statementSpans s = case locatedValue s of
      LetStatement _ e -> expressionSpans e
      ReturnStatement e -> expressionSpans e
      ExpressionStatement e -> expressionSpans e
    expressionSpans e = case locatedValue e of
      InvokeExpression name args -> [locatedSpan e | name == "Worker"] <> concatMap expressionSpans args
      DecideExpression scrutinee arms -> expressionSpans scrutinee
        <> concatMap (blockSpans . caseArmBody . locatedValue) arms
      TupleExpression es -> concatMap expressionSpans es
      BorrowExpression owner _ body -> expressionSpans owner <> blockSpans body
      _ -> []

prepare :: Fixture -> Text -> Either String (SurfaceEnvironment, Located Component)
prepare fixture text = do
  component <- parseOne text
  let spans = workerSpans component
      needs = fixture /= Owners
      makeContract label cls =
        let c = contract needs label cls
        in if fixture == LocalFacts
          then c { callableOutcomePostconditions = Set.singleton (factAtom label) }
          else c
      contracts = zipWith makeContract labels classes
      payload = if fixture == Owners then [(Linear, ownerTy)] else []
      makeAccount sp = SurfaceCallableInvocationSemanticAccount
        { surfaceSemanticInvocationSpan = sp
        , surfaceSemanticInvocationDisplayName = "Worker"
        , surfaceSemanticInvocationDeclarationKey = workerKey
        , surfaceSemanticInvocationCallerAuthority = Set.empty
        , surfaceSemanticInvocationPublicEffectBound = Set.empty
        , surfaceSemanticInvocationCalleeTransition = PreserveCallee
        , surfaceSemanticInvocationModeledFailures = Set.singleton retryFailure
        , surfaceSemanticInvocationOutcomes = contracts
        }
      bindings = Map.fromList
        [ (cls, SurfaceCallableOutcomeBinding cls label payload)
        | (label, cls) <- zip labels classes
        ]
  dispatched <- foldEither
    (\env sp -> do
      plan <- mapLeft show (planSurfaceCallableOutcomeDispatch bindings (makeAccount sp))
      mapLeft show (installSurfaceCallableOutcomeDispatch plan env))
    (baseEnvironment fixture) spans
  installed <- if not needs || fixture == NoInstallation
    then Right dispatched
    else foldEither (installNeeds contracts) dispatched spans
  withLocalFacts <- if fixture == LocalFacts
    then foldEither (installFacts contracts) installed spans
    else Right installed
  Right (withLocalFacts, component)
  where
    installFacts contracts env sp = do
      let bindingMap = Map.fromList
            [ (factAtom label, SurfaceCallableOutcomeFactBinding
                (factAtom label) ("local_" <> label) (needProp label))
            | label <- labels ]
      facts <- mapLeft show (bindSurfaceCallableOutcomeBranchFacts bindingMap
        (zipWith (continuation sp) labels contracts))
      mapLeft show (installSurfaceCallableOutcomeBranchFacts facts env)
    installNeeds contracts env sp = do
      let bindingMap = Map.fromList
            [ (needAtom label, SurfaceCallableOutcomeObligationBinding
                (needAtom label) ("need_" <> label) (needProp label))
            | label <- labels ]
      residues <- mapLeft show (bindSurfaceCallableOutcomeBranchResidue bindingMap
        (zipWith (continuation sp) labels contracts))
      mapLeft show (installSurfaceCallableOutcomeBranchResidue residues env)

foldEither :: (a -> b -> Either e a) -> a -> [b] -> Either e a
foldEither _ acc [] = Right acc
foldEither step acc (x:xs) = step acc x >>= \next -> foldEither step next xs

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right

data Expect = AcceptUnit | RejectClass RejectionClass | RejectCarrier
  deriving Show

data Case = Case String Fixture Text Expect

wrap :: Text -> Text
wrap body = "component Audit { " <> body <> " return unit }"

ownedArms :: Text
ownedArms = " { ok(x) => { invoke Sink(x) } retry(y) => { invoke Sink(y) } } "

emptyArms :: Text
emptyArms = " { ok => { unit } retry => { unit } } "

cases :: [Case]
cases =
  [ Case "R01-repeat-owner-carrier" Owners
      (wrap ("let d = invoke Worker(input) decide d" <> ownedArms <> "decide d" <> ownedArms))
      RejectCarrier
  , Case "R02-alias-owner-carrier" Owners
      (wrap ("let d = invoke Worker(input) let alias = d decide d" <> ownedArms <> "decide alias" <> ownedArms))
      RejectCarrier
  , Case "R03-discard-owner-carrier" Owners
      (wrap "invoke Worker(input)") RejectCarrier
  , Case "R04-abandon-owner-carrier" Owners
      (wrap "let d = invoke Worker(input)") RejectCarrier
  , Case "R05-discard-obligation-carrier" Obligations
      (wrap "invoke Worker()") RejectCarrier
  , Case "R06-abandon-obligation-carrier" Obligations
      (wrap "let d = invoke Worker()") RejectCarrier
  , Case "R07-anonymous-owner-carrier-argument" Owners
      (wrap "invoke InspectDecision(invoke Worker(input))")
      (RejectClass StructuralUse)
  , Case "R08-anonymous-obligation-carrier-argument" Obligations
      (wrap "invoke InspectDecision(invoke Worker())")
      (RejectClass StructuralUse)
  , Case "C01-direct-owner-once" Owners
      (wrap ("decide invoke Worker(input)" <> ownedArms)) AcceptUnit
  , Case "C02-stored-owner-once" Owners
      (wrap ("let d = invoke Worker(input) decide d" <> ownedArms)) AcceptUnit
  , Case "C03-next-consumer-owning-result" Owners
      (wrap ("let result = decide invoke Worker(input) { ok(x) => { x } retry(y) => { y } } invoke Sink(result)"))
      AcceptUnit
  , Case "C04-local-owner-double-use" Owners
      (wrap "decide invoke Worker(input) { ok(x) => { invoke Sink(x) invoke Sink(x) } retry(y) => { invoke Sink(y) } }")
      (RejectClass StructuralUse)
  , Case "C05-local-owner-not-consumed" Owners
      (wrap "decide invoke Worker(input) { ok(x) => { unit } retry(y) => { invoke Sink(y) } }")
      (RejectClass LinearCompletion)
  , Case "C06-missing-alternative" Owners
      (wrap "decide invoke Worker(input) { ok(x) => { invoke Sink(x) } }")
      (RejectClass BranchExhaustiveness)
  , Case "C07-payload-arity" Owners
      (wrap "decide invoke Worker(input) { ok => { unit } retry(y) => { invoke Sink(y) } }")
      (RejectClass TypeMismatch)
  , Case "C08-repeated-boolean" Obligations
      (wrap "let b = flag decide b { true => { unit } false => { unit } } decide b { true => { unit } false => { unit } }")
      AcceptUnit
  , Case "C09-direct-missing-obligation" Obligations
      (wrap ("decide invoke Worker()" <> emptyArms))
      (RejectClass MissingEvidence)
  , Case "C10-exact-obligation-support" ExactEvidence
      (wrap ("decide invoke Worker()" <> emptyArms)) AcceptUnit
  , Case "C11-missing-occurrence-installation" NoInstallation
      (wrap ("decide invoke Worker()" <> emptyArms))
      (RejectClass MissingEvidence)
  , Case "C12-sibling-proof-insufficient" OkOnlyEvidence
      (wrap ("decide invoke Worker()" <> emptyArms))
      (RejectClass MissingEvidence)
  , Case "C13-return-arm-still-checks-obligation" Obligations
      "component Audit { decide invoke Worker() { ok => { return unit } retry => { return unit } } }"
      (RejectClass MissingEvidence)
  , Case "C14-local-facts-discharge-before-pruning" LocalFacts
      (wrap ("decide invoke Worker()" <> emptyArms)) AcceptUnit
  , Case "C15-fact-name-does-not-leak" LocalFacts
      (wrap ("decide invoke Worker()" <> emptyArms <> "local_ok"))
      (RejectClass StructuralUse)
  , Case "C16-nested-path-still-checks-obligation" Obligations
      (wrap "decide invoke Worker() { ok => { decide flag { true => { return unit } false => { unit } } } retry => { unit } }")
      (RejectClass MissingEvidence)
  , Case "C17-named-owner-carrier-argument" Owners
      (wrap "let d = invoke Worker(input) invoke InspectDecision(d)")
      (RejectClass StructuralUse)
  , Case "C18-named-obligation-carrier-argument" Obligations
      (wrap "let d = invoke Worker() invoke InspectDecision(d)")
      (RejectClass StructuralUse)
  , Case "C19-pure-boolean-anonymous-argument" Obligations
      (wrap "invoke InspectBool(true)") AcceptUnit
  , Case "C20-decision-argument-type-mismatch" Obligations
      (wrap "invoke InspectDecision(true)")
      (RejectClass TypeMismatch)
  ]

main :: IO ()
main = do
  outcomes <- mapM runCase cases
  if and outcomes then pure () else exitFailure

runCase :: Case -> IO Bool
runCase (Case name fixture source expected) = do
  result <- try body :: IO (Either SomeException Bool)
  case result of
    Right status -> pure status
    Left err -> putStrLn ("FAIL: " <> name <> " -- exception: " <> show err) >> pure False
  where
    body = case prepare fixture source of
      Left setup -> putStrLn ("FAIL: " <> name <> " -- setup: " <> setup) >> pure False
      Right (env, component) -> do
        let actual = checkSurfaceComponent env component
            matched = matches expected actual
        putStrLn ((if matched then "PASS: " else "FAIL: ") <> name
          <> " -- expected " <> show expected <> ", got " <> show actual)
        pure matched

matches :: Expect -> Either SurfaceCheckError SurfaceCheckResult -> Bool
matches AcceptUnit (Right r) = checkedTerminalControls r == [Return TyUnit]
matches (RejectClass cls) (Left err) = surfaceErrorClass err == cls
matches RejectCarrier (Left err) = surfaceErrorClass err `elem`
  [StructuralUse, LinearCompletion, MissingEvidence]
matches _ _ = False
