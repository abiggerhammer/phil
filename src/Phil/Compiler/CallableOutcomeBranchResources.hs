module Phil.Compiler.CallableOutcomeBranchResources
  ( SurfaceCallableOutcomeResourceExpectation (..)
  , SurfaceCallableOutcomeResourceResidueBinding (..)
  , SurfaceCallableOutcomeBranchResourceEnvironment (..)
  , SurfaceCallableOutcomeBranchResourceError (..)
  , bindSurfaceCallableOutcomeBranchResources
  ) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import Phil.Compiler.CallableOutcomeContinuation
  ( SurfaceCallableOutcomeContinuation (..)
  , SurfaceCallableOutcomeContinuationDisposition (..)
  )
import Phil.Core.Callable (CalleeTransition)
import Phil.Core.CallableOutcome (CallableOutcomeState)
import Phil.Core.Static (DeclarationKey)
import Phil.Surface.Check.Types (BindingMeta)
import Phil.Surface.Syntax (SourceSpan)

-- | Neutral caller-resource expectation for one source binding at the exact
-- branch entry produced by an ordinary callable invocation.
--
-- A present expectation retains the complete Surface binding metadata so mode,
-- type, and resource shape cannot be reconstructed from spelling.  An absent
-- expectation records checked consumption explicitly.  The bridge deliberately
-- carries expectations rather than mutating Surface state: applying the residue
-- is a separate successor slice owned by ordinary resource-state checking.
data SurfaceCallableOutcomeResourceExpectation
  = SurfaceCallableResourcePresent BindingMeta
  | SurfaceCallableResourceAbsent
  deriving (Eq, Show)

-- | Explicit competent binding from one exact admitted CALL outcome
-- continuation to its neutral caller-visible resource residue.
--
-- The identity is occurrence-scoped: invocation span, declaration identity, and
-- source outcome label all participate.  The opaque 'CallableOutcomeState' and
-- exact callee transition are retained as semantic guard keys rather than parsed
-- or re-derived.  Resource expectations are keyed by source binding name only
-- after that exact semantic/occurrence correlation has succeeded.
data SurfaceCallableOutcomeResourceResidueBinding =
  SurfaceCallableOutcomeResourceResidueBinding
    { surfaceOutcomeResourceInvocationSpan :: SourceSpan
    , surfaceOutcomeResourceDeclarationKey :: DeclarationKey
    , surfaceOutcomeResourceSourceLabel :: Text
    , surfaceOutcomeResourceState :: CallableOutcomeState
    , surfaceOutcomeResourceCalleeTransition :: CalleeTransition
    , surfaceOutcomeResourceBindings :: Map Text SurfaceCallableOutcomeResourceExpectation
    , surfaceOutcomeResourceActiveEndpoint :: Maybe Text
    }
  deriving (Eq, Show)

-- | Exact branch-local resource environment retained for successor Surface
-- composition.  Declared-terminal and declared-fatal outcomes retain their
-- complete CALL continuation but intentionally have no caller resource residue: there is no
-- caller continuation in which that residue could be observed or joined.
data SurfaceCallableOutcomeBranchResourceEnvironment =
  SurfaceCallableOutcomeBranchResourceEnvironment
    { surfaceBranchResourceInvocationSpan :: SourceSpan
    , surfaceBranchResourceArmSpan :: SourceSpan
    , surfaceBranchResourceDeclarationKey :: DeclarationKey
    , surfaceBranchResourceSourceLabel :: Text
    , surfaceBranchResourceDisposition :: SurfaceCallableOutcomeContinuationDisposition
    , surfaceBranchResourceResidue :: Maybe SurfaceCallableOutcomeResourceResidueBinding
    , surfaceBranchResourceContinuation :: SurfaceCallableOutcomeContinuation
    }
  deriving (Eq, Show)

data SurfaceCallableOutcomeBranchResourceError
  = SurfaceCallableOutcomeResourceDuplicateIdentity SourceSpan DeclarationKey Text
  | SurfaceCallableOutcomeResourceDomainMismatch
      (Set (SourceSpan, DeclarationKey, Text))
      (Set (SourceSpan, DeclarationKey, Text))
  | SurfaceCallableOutcomeResourceStateMismatch
      SourceSpan
      DeclarationKey
      Text
      CallableOutcomeState
      CallableOutcomeState
  | SurfaceCallableOutcomeResourceCalleeTransitionMismatch
      SourceSpan
      DeclarationKey
      Text
      CalleeTransition
      CalleeTransition
  deriving (Eq, Show)

-- | Correlate explicit neutral resource residue with exact admitted CALL-019
-- outcome continuations.
--
-- Every continuing branch must have exactly one residue binding and no terminal
-- branch may acquire one.  Extra/missing occurrence identities reject.  The
-- supplied opaque semantic-state key and callee transition must equal the exact
-- continuation values, so a residue from another branch or lifecycle cannot be
-- substituted merely because its source binding names happen to match.
--
-- This function does not inspect or rewrite Surface resource state.  It stages a
-- complete, occurrence-scoped bridge for the successor slice that will compose
-- these expectations at branch entry using the ordinary Surface resource/join
-- machinery.
bindSurfaceCallableOutcomeBranchResources
  :: [SurfaceCallableOutcomeResourceResidueBinding]
  -> [SurfaceCallableOutcomeContinuation]
  -> Either SurfaceCallableOutcomeBranchResourceError
       [SurfaceCallableOutcomeBranchResourceEnvironment]
bindSurfaceCallableOutcomeBranchResources supplied continuations = do
  bindings <- foldM addBinding Map.empty supplied
  let expected = Set.fromList
        [ continuationIdentity continuation
        | continuation <- continuations
        , surfaceContinuationDisposition continuation
            == SurfaceCallableOutcomeCallerContinues
        ]
      actual = Map.keysSet bindings
  if expected == actual
    then pure ()
    else Left (SurfaceCallableOutcomeResourceDomainMismatch expected actual)
  mapM (makeEnvironment bindings) continuations
  where
    addBinding accumulated binding =
      let key = bindingIdentity binding
      in if Map.member key accumulated
          then Left
            (SurfaceCallableOutcomeResourceDuplicateIdentity
              (surfaceOutcomeResourceInvocationSpan binding)
              (surfaceOutcomeResourceDeclarationKey binding)
              (surfaceOutcomeResourceSourceLabel binding))
          else Right (Map.insert key binding accumulated)

makeEnvironment
  :: Map
       (SourceSpan, DeclarationKey, Text)
       SurfaceCallableOutcomeResourceResidueBinding
  -> SurfaceCallableOutcomeContinuation
  -> Either SurfaceCallableOutcomeBranchResourceError
       SurfaceCallableOutcomeBranchResourceEnvironment
makeEnvironment bindings continuation =
  case surfaceContinuationDisposition continuation of
    SurfaceCallableOutcomeCallerTerminates _ ->
      Right (environment Nothing)
    SurfaceCallableOutcomeCallerFatals _ ->
      Right (environment Nothing)
    SurfaceCallableOutcomeCallerContinues -> do
      let key = continuationIdentity continuation
      binding <- case Map.lookup key bindings of
        Just value -> Right value
        Nothing -> Left
          (SurfaceCallableOutcomeResourceDomainMismatch
            (Set.singleton key)
            Set.empty)
      if surfaceOutcomeResourceState binding
          == surfaceContinuationState continuation
        then pure ()
        else Left
          (SurfaceCallableOutcomeResourceStateMismatch
            (surfaceContinuationInvocationSpan continuation)
            (surfaceContinuationDeclarationKey continuation)
            (surfaceContinuationSourceLabel continuation)
            (surfaceContinuationState continuation)
            (surfaceOutcomeResourceState binding))
      if surfaceOutcomeResourceCalleeTransition binding
          == surfaceContinuationCalleeTransition continuation
        then pure ()
        else Left
          (SurfaceCallableOutcomeResourceCalleeTransitionMismatch
            (surfaceContinuationInvocationSpan continuation)
            (surfaceContinuationDeclarationKey continuation)
            (surfaceContinuationSourceLabel continuation)
            (surfaceContinuationCalleeTransition continuation)
            (surfaceOutcomeResourceCalleeTransition binding))
      Right (environment (Just binding))
  where
    environment residue = SurfaceCallableOutcomeBranchResourceEnvironment
      { surfaceBranchResourceInvocationSpan =
          surfaceContinuationInvocationSpan continuation
      , surfaceBranchResourceArmSpan = surfaceContinuationArmSpan continuation
      , surfaceBranchResourceDeclarationKey =
          surfaceContinuationDeclarationKey continuation
      , surfaceBranchResourceSourceLabel =
          surfaceContinuationSourceLabel continuation
      , surfaceBranchResourceDisposition =
          surfaceContinuationDisposition continuation
      , surfaceBranchResourceResidue = residue
      , surfaceBranchResourceContinuation = continuation
      }

bindingIdentity
  :: SurfaceCallableOutcomeResourceResidueBinding
  -> (SourceSpan, DeclarationKey, Text)
bindingIdentity binding =
  ( surfaceOutcomeResourceInvocationSpan binding
  , surfaceOutcomeResourceDeclarationKey binding
  , surfaceOutcomeResourceSourceLabel binding
  )

continuationIdentity
  :: SurfaceCallableOutcomeContinuation
  -> (SourceSpan, DeclarationKey, Text)
continuationIdentity continuation =
  ( surfaceContinuationInvocationSpan continuation
  , surfaceContinuationDeclarationKey continuation
  , surfaceContinuationSourceLabel continuation
  )
