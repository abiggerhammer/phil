from pathlib import Path


def replace_once(path, old, new):
    p = Path(path)
    text = p.read_text()
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{path}: expected one replacement site, found {count}")
    p.write_text(text.replace(old, new, 1))


# Neutral Surface carrier: declaration-wide arity plus occurrence-local obligation bindings.
replace_once(
    "src/Phil/Surface/Check/Types.hs",
    "  , callableOutcomeControl :: CallableOutcomeControlSpec\n  , callableOutcomeFacts :: [(Text, Proposition)]\n  }\n",
    "  , callableOutcomeControl :: CallableOutcomeControlSpec\n"
    "  , callableOutcomeFacts :: [(Text, Proposition)]\n"
    "  , callableOutcomeResidualObligationArity :: Int\n"
    "  , callableOutcomeObligations :: [(Text, Proposition)]\n"
    "  }\n",
)
replace_once(
    "src/Phil/Surface/Check/Types.hs",
    "  , surfaceCallableOutcomeFacts :: Map (SourceSpan, DeclarationKey, Text) [(Text, Proposition)]\n  , surfaceTypeAliases :: Map Text Ty\n",
    "  , surfaceCallableOutcomeFacts :: Map (SourceSpan, DeclarationKey, Text) [(Text, Proposition)]\n"
    "  , surfaceCallableOutcomeObligations ::\n"
    "      Map (SourceSpan, DeclarationKey, Text) [(Text, Proposition)]\n"
    "  , surfaceTypeAliases :: Map Text Ty\n",
)
replace_once(
    "src/Phil/Surface/Check/Types.hs",
    "  , surfaceCallableOutcomeFacts = Map.empty\n  , surfaceTypeAliases = Map.empty\n",
    "  , surfaceCallableOutcomeFacts = Map.empty\n"
    "  , surfaceCallableOutcomeObligations = Map.empty\n"
    "  , surfaceTypeAliases = Map.empty\n",
)

# Dispatch records the exact neutral obligation cardinality but never the semantic atoms.
replace_once(
    "src/Phil/Compiler/CallableOutcomeDispatch.hs",
    "  | SurfaceCallableTerminalOutcomePayloadUnsupported CallableOutcomeClass\n  | SurfaceCallableOutcomeControlMismatch\n",
    "  | SurfaceCallableTerminalOutcomePayloadUnsupported CallableOutcomeClass\n"
    "  | SurfaceCallableTerminalResidualObligationsUnsupported CallableOutcomeClass\n"
    "  | SurfaceCallableOutcomeControlMismatch\n",
)
replace_once(
    "src/Phil/Compiler/CallableOutcomeDispatch.hs",
    "    (SurfaceCallableOutcomeDeclaredTerminal,\n        CallableNonSuccessOutcome (CallableDeclaredTerminal outcome))\n      | null (surfaceOutcomeBranchPayload branch) ->\n          Right CallableOutcomeSpec\n            { callableOutcomeLabel = surfaceOutcomeBranchLabel branch\n            , callableOutcomePayload = []\n            , callableOutcomeControl = CallableOutcomeCloses outcome\n            , callableOutcomeFacts = []\n            }\n      | otherwise -> Left\n          (SurfaceCallableTerminalOutcomePayloadUnsupported\n            (surfaceOutcomeBranchClass branch))\n",
    "    (SurfaceCallableOutcomeDeclaredTerminal,\n        CallableNonSuccessOutcome (CallableDeclaredTerminal outcome))\n"
    "      | not (Set.null (callableOutcomeResidualObligations\n"
    "          (surfaceOutcomeBranchContract branch))) -> Left\n"
    "          (SurfaceCallableTerminalResidualObligationsUnsupported\n"
    "            (surfaceOutcomeBranchClass branch))\n"
    "      | null (surfaceOutcomeBranchPayload branch) ->\n"
    "          Right CallableOutcomeSpec\n"
    "            { callableOutcomeLabel = surfaceOutcomeBranchLabel branch\n"
    "            , callableOutcomePayload = []\n"
    "            , callableOutcomeControl = CallableOutcomeCloses outcome\n"
    "            , callableOutcomeFacts = []\n"
    "            , callableOutcomeResidualObligationArity = 0\n"
    "            , callableOutcomeObligations = []\n"
    "            }\n"
    "      | otherwise -> Left\n"
    "          (SurfaceCallableTerminalOutcomePayloadUnsupported\n"
    "            (surfaceOutcomeBranchClass branch))\n",
)
replace_once(
    "src/Phil/Compiler/CallableOutcomeDispatch.hs",
    "  , callableOutcomeControl = CallableOutcomeContinues\n  , callableOutcomeFacts = []\n  }\n",
    "  , callableOutcomeControl = CallableOutcomeContinues\n"
    "  , callableOutcomeFacts = []\n"
    "  , callableOutcomeResidualObligationArity =\n"
    "      Set.size (callableOutcomeResidualObligations\n"
    "        (surfaceOutcomeBranchContract branch))\n"
    "  , callableOutcomeObligations = []\n"
    "  }\n",
)

# Compiler-side neutral-dispatch correlation also checks exact residual cardinality.
replace_once(
    "src/Phil/Compiler/CallableOutcomeBranchSemantics.hs",
    "  ( CallableOutcomeClass (..)\n  , CallableOutcomeContract\n  )\n",
    "  ( CallableOutcomeClass (..)\n  , CallableOutcomeContract (..)\n  )\n",
)
replace_once(
    "src/Phil/Compiler/CallableOutcomeBranchSemantics.hs",
    "  callableOutcomeLabel spec == surfaceOutcomeBranchLabel branch\n    && callableOutcomePayload spec == surfaceOutcomeBranchPayload branch\n    && neutralControlMatches branch (callableOutcomeControl spec)\n",
    "  callableOutcomeLabel spec == surfaceOutcomeBranchLabel branch\n"
    "    && callableOutcomePayload spec == surfaceOutcomeBranchPayload branch\n"
    "    && callableOutcomeResidualObligationArity spec\n"
    "      == Set.size (callableOutcomeResidualObligations\n"
    "        (surfaceOutcomeBranchContract branch))\n"
    "    && neutralControlMatches branch (callableOutcomeControl spec)\n",
)

# Surface attaches both proof facts and residual obligations to the exact invocation occurrence.
replace_once(
    "src/Phil/Surface/Check/Engine.hs",
    "        Just outcomes ->\n          let invocationSpan = locatedSpan located\n              declarationKey = surfaceCallableDeclarationKey signature\n              withFacts outcome = outcome\n                { callableOutcomeFacts = Map.findWithDefault\n                    []\n                    (invocationSpan, declarationKey, callableOutcomeLabel outcome)\n                    (surfaceCallableOutcomeFacts environment)\n                }\n          in callableDecision next signature (map withFacts outcomes)\n",
    "        Just outcomes ->\n"
    "          let invocationSpan = locatedSpan located\n"
    "              declarationKey = surfaceCallableDeclarationKey signature\n"
    "              withOccurrenceState outcome =\n"
    "                let key =\n"
    "                      (invocationSpan, declarationKey, callableOutcomeLabel outcome)\n"
    "                in outcome\n"
    "                  { callableOutcomeFacts = Map.findWithDefault\n"
    "                      [] key (surfaceCallableOutcomeFacts environment)\n"
    "                  , callableOutcomeObligations = Map.findWithDefault\n"
    "                      [] key (surfaceCallableOutcomeObligations environment)\n"
    "                  }\n"
    "          in callableDecision next signature (map withOccurrenceState outcomes)\n",
)
replace_once(
    "src/Phil/Surface/Check/Engine.hs",
    "      let labels = map callableOutcomeLabel outcomes\n      unless (Set.size (Set.fromList labels) == length labels) $\n        throw located TypeMismatch \"callable decision outcome labels are not unique\"\n      case surfaceCallableResult signature of\n",
    "      let labels = map callableOutcomeLabel outcomes\n"
    "      unless (Set.size (Set.fromList labels) == length labels) $\n"
    "        throw located TypeMismatch \"callable decision outcome labels are not unique\"\n"
    "      unless (all exactObligationArity outcomes) $\n"
    "        throw located MissingEvidence\n"
    "          \"CALL-019 residual obligation bindings are missing or substituted\"\n"
    "      case surfaceCallableResult signature of\n",
)
replace_once(
    "src/Phil/Surface/Check/Engine.hs",
    "        Just _ -> throw located TypeMismatch\n          \"branch-dispatched callable cannot also expose one unbranched result\"\n",
    "        Just _ -> throw located TypeMismatch\n"
    "          \"branch-dispatched callable cannot also expose one unbranched result\"\n"
    "\n"
    "    exactObligationArity outcome =\n"
    "      length (callableOutcomeObligations outcome)\n"
    "        == callableOutcomeResidualObligationArity outcome\n",
)

# Continuing callable arms must discharge exact residual propositions before the ordinary
# Surface resource join can erase branch identity.
replace_once(
    "src/Phil/Surface/Check/Engine.hs",
    "      checkScopedValueBlock\n        environment\n        state\n        withBinders\n        (caseArmBody (locatedValue locatedArm))\n\ncallableDecisionControl :: DecisionKind -> Text -> Maybe CallableOutcomeControlSpec\n",
    "      case callableDecisionObligations decision label of\n"
    "        Just obligations ->\n"
    "          checkCallableDecisionArm\n"
    "            environment\n"
    "            state\n"
    "            withBinders\n"
    "            obligations\n"
    "            (caseArmBody (locatedValue locatedArm))\n"
    "        Nothing ->\n"
    "          checkScopedValueBlock\n"
    "            environment\n"
    "            state\n"
    "            withBinders\n"
    "            (caseArmBody (locatedValue locatedArm))\n"
    "\n"
    "callableDecisionObligations\n"
    "  :: DecisionKind\n"
    "  -> Text\n"
    "  -> Maybe [(Text, Proposition)]\n"
    "callableDecisionObligations decision label = case decision of\n"
    "  CallableDecision outcomes -> case\n"
    "      [ callableOutcomeObligations outcome\n"
    "      | outcome <- outcomes\n"
    "      , callableOutcomeLabel outcome == label\n"
    "      , callableOutcomeControl outcome == CallableOutcomeContinues\n"
    "      ] of\n"
    "    [obligations] -> Just obligations\n"
    "    _ -> Nothing\n"
    "  _ -> Nothing\n"
    "\n"
    "checkCallableDecisionArm\n"
    "  :: SurfaceEnvironment\n"
    "  -> SurfaceState\n"
    "  -> SurfaceState\n"
    "  -> [(Text, Proposition)]\n"
    "  -> Located Block\n"
    "  -> Either SurfaceCheckError [SurfacePath]\n"
    "checkCallableDecisionArm environment incoming scoped obligations body = do\n"
    "  paths <- checkValueBlock environment scoped body\n"
    "  mapM checkAndPrune paths\n"
    "  where\n"
    "    checkAndPrune path = do\n"
    "      mapM_ (checkObligation (pathState path)) obligations\n"
    "      pruneScopedPath\n"
    "        (locatedSpan body)\n"
    "        (Map.keysSet (stateBindings incoming))\n"
    "        path\n"
    "\n"
    "    checkObligation branchState (name, proposition) =\n"
    "      let required = rewriteProposition branchState proposition\n"
    "      in unless (hasExactEvidence required branchState) $\n"
    "        Left SurfaceCheckError\n"
    "          { surfaceErrorSpan = locatedSpan body\n"
    "          , surfaceErrorClass = MissingEvidence\n"
    "          , surfaceErrorDetail =\n"
    "              \"CALL-019 residual obligation is not discharged: \" <> name\n"
    "          }\n"
    "\n"
    "callableDecisionControl :: DecisionKind -> Text -> Maybe CallableOutcomeControlSpec\n",
)

# New compiler-side exact residual-obligation bridge. Opaque semantic atoms are never parsed.
Path("src/Phil/Compiler/CallableOutcomeBranchResidue.hs").write_text(r'''module Phil.Compiler.CallableOutcomeBranchResidue
  ( SurfaceCallableOutcomeObligationBinding (..)
  , SurfaceCallableOutcomeBranchResidueEnvironment (..)
  , SurfaceCallableOutcomeBranchResidueError (..)
  , bindSurfaceCallableOutcomeBranchResidue
  , installSurfaceCallableOutcomeBranchResidue
  ) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Compiler.CallableOutcomeContinuation
  ( SurfaceCallableOutcomeContinuation (..)
  , SurfaceCallableOutcomeContinuationDisposition (..)
  )
import Phil.Core.CallableOutcome (CallableOutcomeAtom)
import Phil.Core.Static (DeclarationKey)
import Phil.Core.Syntax (Proposition)
import Phil.Surface.Check
  ( CallableOutcomeControlSpec (..)
  , CallableOutcomeSpec (..)
  , SurfaceEnvironment (..)
  )
import Phil.Surface.Syntax (SourceSpan)

-- | Explicit competent binding from one opaque residual obligation atom to the
-- neutral proposition that must be established before the source arm exits.
-- CALL-019 never parses the atom spelling into a proposition.
data SurfaceCallableOutcomeObligationBinding =
  SurfaceCallableOutcomeObligationBinding
    { surfaceOutcomeObligationAtom :: CallableOutcomeAtom
    , surfaceOutcomeObligationName :: Text
    , surfaceOutcomeObligationProposition :: Proposition
    }
  deriving (Eq, Ord, Show)

-- | Exact residual-obligation environment for one admitted outcome arm.
-- Terminal branches have no caller continuation and therefore carry no join
-- obligations through this Phase-1 carrier.
data SurfaceCallableOutcomeBranchResidueEnvironment =
  SurfaceCallableOutcomeBranchResidueEnvironment
    { surfaceBranchResidueInvocationSpan :: SourceSpan
    , surfaceBranchResidueArmSpan :: SourceSpan
    , surfaceBranchResidueDeclarationKey :: DeclarationKey
    , surfaceBranchResidueSourceLabel :: Text
    , surfaceBranchResidueDisposition :: SurfaceCallableOutcomeContinuationDisposition
    , surfaceBranchResidualObligations :: [SurfaceCallableOutcomeObligationBinding]
    , surfaceBranchResidueContinuation :: SurfaceCallableOutcomeContinuation
    }
  deriving (Eq, Ord, Show)

data SurfaceCallableOutcomeBranchResidueError
  = SurfaceCallableOutcomeResidualBindingDomainMismatch
      (Set CallableOutcomeAtom)
      (Set CallableOutcomeAtom)
  | SurfaceCallableOutcomeResidualBindingKeyMismatch
      CallableOutcomeAtom
      CallableOutcomeAtom
  | SurfaceCallableOutcomeResidualBindingEmptyName CallableOutcomeAtom
  | SurfaceCallableOutcomeResidualNameCollision
      SourceSpan
      Text
      (Set CallableOutcomeAtom)
  | SurfaceCallableOutcomeTerminalResidualUnsupported
      SourceSpan
      Text
      (Set CallableOutcomeAtom)
  | SurfaceCallableOutcomeResidueEnvironmentIdentityMismatch SourceSpan
  | SurfaceCallableOutcomeResidueDispatchMissing DeclarationKey
  | SurfaceCallableOutcomeResidueSourceLabelMissing DeclarationKey Text
  | SurfaceCallableOutcomeResidueControlMismatch
      DeclarationKey
      Text
      CallableOutcomeControlSpec
  | SurfaceCallableOutcomeResidueArityMismatch
      DeclarationKey
      Text
      Int
      Int
  | SurfaceCallableOutcomeResidueInstallConflict
      SourceSpan
      DeclarationKey
      Text
  deriving (Eq, Ord, Show)

-- | Bind every continuing residual obligation exactly once. Missing, extra, or
-- substituted semantic atoms reject. A declared-terminal branch with residual
-- obligations is deliberately unsupported: Surface has no caller continuation
-- in which to carry them, and silently dropping them would be unsound.
bindSurfaceCallableOutcomeBranchResidue
  :: Map CallableOutcomeAtom SurfaceCallableOutcomeObligationBinding
  -> [SurfaceCallableOutcomeContinuation]
  -> Either SurfaceCallableOutcomeBranchResidueError
       [SurfaceCallableOutcomeBranchResidueEnvironment]
bindSurfaceCallableOutcomeBranchResidue bindings continuations = do
  mapM_ validateBinding (Map.toAscList bindings)
  mapM_ rejectTerminalResidual continuations
  let expectedAtoms = Set.unions (map continuingResidualAtoms continuations)
      actualAtoms = Map.keysSet bindings
  if expectedAtoms == actualAtoms
    then pure ()
    else Left
      (SurfaceCallableOutcomeResidualBindingDomainMismatch expectedAtoms actualAtoms)
  mapM makeEnvironment continuations
  where
    validateBinding (key, binding)
      | surfaceOutcomeObligationAtom binding /= key =
          Left (SurfaceCallableOutcomeResidualBindingKeyMismatch
            key (surfaceOutcomeObligationAtom binding))
      | Text.null (surfaceOutcomeObligationName binding) =
          Left (SurfaceCallableOutcomeResidualBindingEmptyName key)
      | otherwise = Right ()

    rejectTerminalResidual continuation =
      case surfaceContinuationDisposition continuation of
        SurfaceCallableOutcomeCallerContinues -> Right ()
        SurfaceCallableOutcomeCallerTerminates _
          | Set.null (surfaceContinuationResidualObligations continuation) -> Right ()
          | otherwise -> Left
              (SurfaceCallableOutcomeTerminalResidualUnsupported
                (surfaceContinuationArmSpan continuation)
                (surfaceContinuationSourceLabel continuation)
                (surfaceContinuationResidualObligations continuation))

    makeEnvironment continuation =
      case surfaceContinuationDisposition continuation of
        SurfaceCallableOutcomeCallerTerminates _ ->
          Right (environment continuation [])
        SurfaceCallableOutcomeCallerContinues -> do
          obligations <- mapM lookupObligation
            (Set.toAscList (surfaceContinuationResidualObligations continuation))
          checkNames continuation obligations
          Right (environment continuation obligations)

    lookupObligation semanticAtom = case Map.lookup semanticAtom bindings of
      Just binding -> Right binding
      Nothing -> Left
        (SurfaceCallableOutcomeResidualBindingDomainMismatch
          (Set.singleton semanticAtom)
          Set.empty)

    environment continuation obligations =
      SurfaceCallableOutcomeBranchResidueEnvironment
        { surfaceBranchResidueInvocationSpan = surfaceContinuationInvocationSpan continuation
        , surfaceBranchResidueArmSpan = surfaceContinuationArmSpan continuation
        , surfaceBranchResidueDeclarationKey = surfaceContinuationDeclarationKey continuation
        , surfaceBranchResidueSourceLabel = surfaceContinuationSourceLabel continuation
        , surfaceBranchResidueDisposition = surfaceContinuationDisposition continuation
        , surfaceBranchResidualObligations = obligations
        , surfaceBranchResidueContinuation = continuation
        }

-- | Install already-validated neutral obligations for the exact invocation
-- occurrence. Declaration-wide dispatch retains only the expected arity, so a
-- missing occurrence installation fails closed in Surface rather than erasing
-- the obligation at the subsequent resource join.
installSurfaceCallableOutcomeBranchResidue
  :: [SurfaceCallableOutcomeBranchResidueEnvironment]
  -> SurfaceEnvironment
  -> Either SurfaceCallableOutcomeBranchResidueError SurfaceEnvironment
installSurfaceCallableOutcomeBranchResidue residueEnvironments initialEnvironment =
  foldM installOne initialEnvironment residueEnvironments
  where
    installOne environment residueEnvironment = do
      let continuation = surfaceBranchResidueContinuation residueEnvironment
          invocationSpan = surfaceBranchResidueInvocationSpan residueEnvironment
          declarationKey = surfaceBranchResidueDeclarationKey residueEnvironment
          sourceLabel = surfaceBranchResidueSourceLabel residueEnvironment
          obligations = surfaceBranchResidualObligations residueEnvironment
          neutral = map neutralObligation obligations
      if invocationSpan == surfaceContinuationInvocationSpan continuation
          && declarationKey == surfaceContinuationDeclarationKey continuation
          && sourceLabel == surfaceContinuationSourceLabel continuation
        then pure ()
        else Left (SurfaceCallableOutcomeResidueEnvironmentIdentityMismatch
          (surfaceBranchResidueArmSpan residueEnvironment))
      specs <- maybe
        (Left (SurfaceCallableOutcomeResidueDispatchMissing declarationKey))
        Right
        (Map.lookup declarationKey (surfaceCallableOutcomes environment))
      spec <- case
          [ candidate
          | candidate <- specs
          , callableOutcomeLabel candidate == sourceLabel
          ] of
        [candidate] -> Right candidate
        _ -> Left
          (SurfaceCallableOutcomeResidueSourceLabelMissing declarationKey sourceLabel)
      case surfaceBranchResidueDisposition residueEnvironment of
        SurfaceCallableOutcomeCallerTerminates _ ->
          case callableOutcomeControl spec of
            CallableOutcomeCloses _ -> Right environment
            actual -> Left
              (SurfaceCallableOutcomeResidueControlMismatch
                declarationKey sourceLabel actual)
        SurfaceCallableOutcomeCallerContinues -> do
          case callableOutcomeControl spec of
            CallableOutcomeContinues -> Right ()
            actual -> Left
              (SurfaceCallableOutcomeResidueControlMismatch
                declarationKey sourceLabel actual)
          let expectedArity = callableOutcomeResidualObligationArity spec
              actualArity = length neutral
          if expectedArity == actualArity
            then pure ()
            else Left
              (SurfaceCallableOutcomeResidueArityMismatch
                declarationKey sourceLabel expectedArity actualArity)
          let key = (invocationSpan, declarationKey, sourceLabel)
          case Map.lookup key (surfaceCallableOutcomeObligations environment) of
            Nothing -> Right environment
              { surfaceCallableOutcomeObligations = Map.insert key neutral
                  (surfaceCallableOutcomeObligations environment)
              }
            Just existing
              | existing == neutral -> Right environment
              | otherwise -> Left
                  (SurfaceCallableOutcomeResidueInstallConflict
                    invocationSpan declarationKey sourceLabel)

continuingResidualAtoms
  :: SurfaceCallableOutcomeContinuation
  -> Set CallableOutcomeAtom
continuingResidualAtoms continuation =
  case surfaceContinuationDisposition continuation of
    SurfaceCallableOutcomeCallerTerminates _ -> Set.empty
    SurfaceCallableOutcomeCallerContinues ->
      surfaceContinuationResidualObligations continuation

neutralObligation
  :: SurfaceCallableOutcomeObligationBinding
  -> (Text, Proposition)
neutralObligation binding =
  ( surfaceOutcomeObligationName binding
  , surfaceOutcomeObligationProposition binding
  )

checkNames
  :: SurfaceCallableOutcomeContinuation
  -> [SurfaceCallableOutcomeObligationBinding]
  -> Either SurfaceCallableOutcomeBranchResidueError ()
checkNames continuation obligations = mapM_ checkOne (Map.toAscList byName)
  where
    byName = Map.fromListWith Set.union
      [ ( surfaceOutcomeObligationName obligation
        , Set.singleton (surfaceOutcomeObligationAtom obligation)
        )
      | obligation <- obligations
      ]

    checkOne (name, atoms)
      | Set.size atoms <= 1 = Right ()
      | otherwise = Left
          (SurfaceCallableOutcomeResidualNameCollision
            (surfaceContinuationArmSpan continuation)
            name
            atoms)
''')

# Focused behavioral test: missing installation cannot erase obligations, exact evidence is
# required per sibling branch, and declaration-wide dispatch remains occurrence-neutral.
Path("test/Phase1CALL019BranchResidueJoinMain.hs").write_text(r'''{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Compiler.CallableInvocationSemantics
  ( SurfaceCallableInvocationSemanticAccount (..)
  )
import Phil.Compiler.CallableOutcomeBranchResidue
  ( SurfaceCallableOutcomeBranchResidueError (..)
  , SurfaceCallableOutcomeObligationBinding (..)
  , bindSurfaceCallableOutcomeBranchResidue
  , installSurfaceCallableOutcomeBranchResidue
  )
import Phil.Compiler.CallableOutcomeContinuation
  ( SurfaceCallableOutcomeContinuation (..)
  , SurfaceCallableOutcomeContinuationDisposition (..)
  )
import Phil.Compiler.CallableOutcomeDispatch
  ( SurfaceCallableOutcomeBinding (..)
  , installSurfaceCallableOutcomeDispatch
  , planSurfaceCallableOutcomeDispatch
  )
import Phil.Core.Callable (CalleeTransition (..))
import Phil.Core.CallableOutcome
  ( CallableOutcomeAtom (..)
  , CallableOutcomeClass (..)
  , CallableOutcomeContract (..)
  , CallableOutcomeState (..)
  )
import Phil.Core.CallableRefinement (CallableFailure (..))
import Phil.Core.Static
  ( DeclarationKey (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Outcome (..)
  , Proposition (..)
  , Ty (..)
  )
import Phil.Surface.Check
  ( CallableOutcomeSpec (..)
  , InitialBinding (..)
  , RejectionClass (..)
  , SurfaceCallableSignature (..)
  , SurfaceEnvironment (..)
  , SurfaceShape (..)
  , checkSurfaceComponent
  , emptySurfaceEnvironment
  )
import Phil.Surface.Parser (parseSurfaceFile)
import Phil.Surface.Syntax
  ( Block (..)
  , Component (..)
  , Located (..)
  , Pattern (..)
  , SourcePoint (..)
  , SourceSpan (..)
  , Statement (..)
  , SurfaceExpression (..)
  , SurfaceFile (..)
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "CALL-019 exact residual obligations discharge before branch join"
        exactResidualsDischarge
    , test "CALL-019 missing residual binding rejects before installation"
        missingResidualBindingRejects
    , test "CALL-019 missing occurrence installation fails closed"
        missingOccurrenceInstallationRejects
    , test "CALL-019 sibling evidence cannot discharge another outcome"
        siblingEvidenceDoesNotDischarge
    , test "CALL-019 invocation span participates in residual lookup"
        wrongOccurrenceDoesNotInstall
    , test "CALL-019 declaration dispatch retains only neutral residual arity"
        declarationDispatchStaysNeutral
    , test "CALL-019 conflicting residual reinstall rejects"
        conflictingResidualInstallRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

workerKey :: DeclarationKey
workerKey = DeclarationKey "decl.worker"

successClass, retryClass :: CallableOutcomeClass
successClass = CallableSuccessOutcome
retryClass = CallableNonSuccessOutcome retryFailure

retryFailure :: CallableFailure
retryFailure = CallableTypedNegative (Outcome "retry")

okNeed, retryNeed :: CallableOutcomeAtom
okNeed = CallableOutcomeAtom "semantic.ok.need"
retryNeed = CallableOutcomeAtom "semantic.retry.need"

okProposition, retryProposition :: Proposition
okProposition = Atom "OkNeed" []
retryProposition = Atom "RetryNeed" []

successContract, retryContract :: CallableOutcomeContract
successContract = CallableOutcomeContract
  { callableOutcomeClass = successClass
  , callableOutcomeState = CallableOutcomeState "success"
  , callableOutcomeCalleeTransition = PreserveCallee
  , callableOutcomePostconditions = Set.empty
  , callableOutcomeResidualObligations = Set.singleton okNeed
  , callableOutcomeAssumptions = Set.empty
  , callableOutcomeEffects = Set.empty
  , callableOutcomeDischargedFacts = Set.empty
  }
retryContract = CallableOutcomeContract
  { callableOutcomeClass = retryClass
  , callableOutcomeState = CallableOutcomeState "retry"
  , callableOutcomeCalleeTransition = PreserveCallee
  , callableOutcomePostconditions = Set.empty
  , callableOutcomeResidualObligations = Set.singleton retryNeed
  , callableOutcomeAssumptions = Set.empty
  , callableOutcomeEffects = Set.empty
  , callableOutcomeDischargedFacts = Set.empty
  }

baseEnvironment :: Bool -> Bool -> SurfaceEnvironment
baseEnvironment includeOk includeRetry =
  (emptySurfaceEnvironment emptyStaticContext)
    { surfaceCallables = Map.singleton "Worker" SurfaceCallableSignature
        { surfaceCallableDeclarationKey = workerKey
        , surfaceCallableParameters = []
        , surfaceCallableResult = Nothing
        }
    , surfaceInitialBindings = Map.fromList
        (concat
          [ if includeOk
              then [("ok_evidence", proofBinding okProposition)]
              else []
          , if includeRetry
              then [("retry_evidence", proofBinding retryProposition)]
              else []
          ])
    }
  where
    proofBinding proposition = InitialBinding
      { initialMode = Unrestricted
      , initialType = TyProof proposition
      , initialShape = PlainShape
      }

dispatchBinding :: CallableOutcomeClass -> Text -> SurfaceCallableOutcomeBinding
dispatchBinding outcomeClass label = SurfaceCallableOutcomeBinding
  { surfaceOutcomeBindingClass = outcomeClass
  , surfaceOutcomeBindingLabel = label
  , surfaceOutcomeBindingPayload = []
  }

account :: SourceSpan -> SurfaceCallableInvocationSemanticAccount
account invocationSpan = SurfaceCallableInvocationSemanticAccount
  { surfaceSemanticInvocationSpan = invocationSpan
  , surfaceSemanticInvocationDisplayName = "Worker"
  , surfaceSemanticInvocationDeclarationKey = workerKey
  , surfaceSemanticInvocationCallerAuthority = Set.empty
  , surfaceSemanticInvocationPublicEffectBound = Set.empty
  , surfaceSemanticInvocationCalleeTransition = PreserveCallee
  , surfaceSemanticInvocationModeledFailures = Set.singleton retryFailure
  , surfaceSemanticInvocationOutcomes = [successContract, retryContract]
  }

dispatchEnvironment
  :: Bool
  -> Bool
  -> SourceSpan
  -> Either String SurfaceEnvironment
dispatchEnvironment includeOk includeRetry invocationSpan = do
  let bindings = Map.fromList
        [ (successClass, dispatchBinding successClass "ok")
        , (retryClass, dispatchBinding retryClass "retry")
        ]
  plan <- mapLeft show
    (planSurfaceCallableOutcomeDispatch bindings (account invocationSpan))
  mapLeft show
    (installSurfaceCallableOutcomeDispatch plan (baseEnvironment includeOk includeRetry))

continuation
  :: SourceSpan
  -> Text
  -> CallableOutcomeContract
  -> SurfaceCallableOutcomeContinuation
continuation invocationSpan label contract =
  SurfaceCallableOutcomeContinuation
    { surfaceContinuationInvocationSpan = invocationSpan
    , surfaceContinuationArmSpan = invocationSpan
    , surfaceContinuationDeclarationKey = workerKey
    , surfaceContinuationSourceLabel = label
    , surfaceContinuationPayload = []
    , surfaceContinuationOutcomeClass = callableOutcomeClass contract
    , surfaceContinuationDisposition = SurfaceCallableOutcomeCallerContinues
    , surfaceContinuationState = callableOutcomeState contract
    , surfaceContinuationCalleeTransition = callableOutcomeCalleeTransition contract
    , surfaceContinuationPostconditions = callableOutcomePostconditions contract
    , surfaceContinuationResidualObligations = callableOutcomeResidualObligations contract
    , surfaceContinuationAssumptions = callableOutcomeAssumptions contract
    , surfaceContinuationEffects = callableOutcomeEffects contract
    , surfaceContinuationDischargedFacts = callableOutcomeDischargedFacts contract
    , surfaceContinuationContract = contract
    }

obligationBindings
  :: Map.Map CallableOutcomeAtom SurfaceCallableOutcomeObligationBinding
obligationBindings = Map.fromList
  [ (okNeed, obligation okNeed "ok_need" okProposition)
  , (retryNeed, obligation retryNeed "retry_need" retryProposition)
  ]
  where
    obligation semanticAtom name proposition =
      SurfaceCallableOutcomeObligationBinding
        { surfaceOutcomeObligationAtom = semanticAtom
        , surfaceOutcomeObligationName = name
        , surfaceOutcomeObligationProposition = proposition
        }

installResidueFor
  :: SourceSpan
  -> SurfaceEnvironment
  -> Either String SurfaceEnvironment
installResidueFor invocationSpan environment = do
  residue <- mapLeft show $
    bindSurfaceCallableOutcomeBranchResidue
      obligationBindings
      [ continuation invocationSpan "ok" successContract
      , continuation invocationSpan "retry" retryContract
      ]
  mapLeft show (installSurfaceCallableOutcomeBranchResidue residue environment)

continuingSource :: Text
continuingSource =
  "component Caller { let joined = decide invoke Worker() { "
    <> "ok => { unit } retry => { unit } } return joined }"

exactResidualsDischarge :: Either String ()
exactResidualsDischarge = do
  component <- parseOne continuingSource
  invocationSpan <- invocationSpanOf component
  dispatched <- dispatchEnvironment True True invocationSpan
  installed <- installResidueFor invocationSpan dispatched
  _ <- mapLeft show (checkSurfaceComponent installed component)
  Right ()

missingResidualBindingRejects :: Either String ()
missingResidualBindingRejects = do
  component <- parseOne continuingSource
  invocationSpan <- invocationSpanOf component
  let incomplete = Map.delete retryNeed obligationBindings
  case bindSurfaceCallableOutcomeBranchResidue
      incomplete
      [ continuation invocationSpan "ok" successContract
      , continuation invocationSpan "retry" retryContract
      ] of
    Left (SurfaceCallableOutcomeResidualBindingDomainMismatch expected actual)
      | Set.member retryNeed expected && not (Set.member retryNeed actual) -> Right ()
    Left other -> Left ("wrong missing-binding rejection: " <> show other)
    Right accepted -> Left ("incomplete residual binding accepted: " <> show accepted)

missingOccurrenceInstallationRejects :: Either String ()
missingOccurrenceInstallationRejects = do
  component <- parseOne continuingSource
  invocationSpan <- invocationSpanOf component
  dispatched <- dispatchEnvironment True True invocationSpan
  case checkSurfaceComponent dispatched component of
    Left errorValue
      | surfaceErrorClass errorValue == MissingEvidence -> Right ()
    Left other -> Left ("wrong missing-installation rejection: " <> show other)
    Right checked -> Left ("missing residual installation accepted: " <> show checked)

siblingEvidenceDoesNotDischarge :: Either String ()
siblingEvidenceDoesNotDischarge = do
  component <- parseOne continuingSource
  invocationSpan <- invocationSpanOf component
  dispatched <- dispatchEnvironment True False invocationSpan
  installed <- installResidueFor invocationSpan dispatched
  case checkSurfaceComponent installed component of
    Left errorValue
      | surfaceErrorClass errorValue == MissingEvidence -> Right ()
    Left other -> Left ("wrong sibling-evidence rejection: " <> show other)
    Right checked -> Left ("success evidence discharged retry obligation: " <> show checked)

wrongOccurrenceDoesNotInstall :: Either String ()
wrongOccurrenceDoesNotInstall = do
  component <- parseOne continuingSource
  invocationSpan <- invocationSpanOf component
  dispatched <- dispatchEnvironment True True invocationSpan
  let wrongSpan = SourceSpan
        (SourcePoint "wrong-occurrence" 9 1 900)
        (SourcePoint "wrong-occurrence" 9 2 901)
  installed <- installResidueFor wrongSpan dispatched
  case checkSurfaceComponent installed component of
    Left errorValue
      | surfaceErrorClass errorValue == MissingEvidence -> Right ()
    Left other -> Left ("wrong occurrence rejection: " <> show other)
    Right checked -> Left ("wrong-occurrence residuals became visible: " <> show checked)

declarationDispatchStaysNeutral :: Either String ()
declarationDispatchStaysNeutral = do
  component <- parseOne continuingSource
  invocationSpan <- invocationSpanOf component
  dispatched <- dispatchEnvironment True True invocationSpan
  installed <- installResidueFor invocationSpan dispatched
  specs <- maybe
    (Left "callable dispatch disappeared during residual installation")
    Right
    (Map.lookup workerKey (surfaceCallableOutcomes installed))
  assert
    (all (null . callableOutcomeObligations) specs)
    "occurrence residual propositions contaminated declaration dispatch"
  assert
    (map callableOutcomeResidualObligationArity specs == [1, 1])
    "declaration dispatch lost exact residual obligation arity"
  assert
    (Map.size (surfaceCallableOutcomeObligations installed) == 2)
    "expected one residual entry per continuing outcome"

conflictingResidualInstallRejects :: Either String ()
conflictingResidualInstallRejects = do
  component <- parseOne continuingSource
  invocationSpan <- invocationSpanOf component
  dispatched <- dispatchEnvironment True True invocationSpan
  residue <- mapLeft show $
    bindSurfaceCallableOutcomeBranchResidue
      obligationBindings
      [ continuation invocationSpan "ok" successContract
      , continuation invocationSpan "retry" retryContract
      ]
  installed <- mapLeft show
    (installSurfaceCallableOutcomeBranchResidue residue dispatched)
  let key = (invocationSpan, workerKey, "ok")
      poisoned = installed
        { surfaceCallableOutcomeObligations = Map.insert
            key [("wrong", Atom "Wrong" [])]
            (surfaceCallableOutcomeObligations installed)
        }
  case installSurfaceCallableOutcomeBranchResidue residue poisoned of
    Left (SurfaceCallableOutcomeResidueInstallConflict actualSpan actualKey actualLabel)
      | actualSpan == invocationSpan
          && actualKey == workerKey
          && actualLabel == "ok" -> Right ()
    Left other -> Left ("wrong reinstall rejection: " <> show other)
    Right accepted -> Left ("conflicting residual reinstall accepted: " <> show accepted)

invocationSpanOf :: Located Component -> Either String SourceSpan
invocationSpanOf locatedComponent =
  case blockStatements (locatedValue (componentBody (locatedValue locatedComponent))) of
    Located _ (LetStatement _ decision) : _ -> fromDecision decision
    Located _ (ExpressionStatement decision) : _ -> fromDecision decision
    statements -> Left
      ("expected leading decision statement, got " <> show (length statements))
  where
    fromDecision decision = case locatedValue decision of
      DecideExpression scrutinee _ -> Right (locatedSpan scrutinee)
      other -> Left ("expected decide expression, got " <> show other)

parseOne :: Text -> Either String (Located Component)
parseOne source = do
  parsed <- mapLeft show (parseSurfaceFile "call019-branch-residue" source)
  case surfaceComponents parsed of
    [component] -> Right component
    components -> Left ("expected one component, got " <> show (length components))

assert :: Bool -> String -> Either String ()
assert True _ = Right ()
assert False detail = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
''')
