module Phil.Compiler.CallableOutcomeBranchFacts
  ( SurfaceCallableOutcomeFactBinding (..)
  , SurfaceCallableOutcomeBranchFactEnvironment (..)
  , SurfaceCallableOutcomeBranchFactError (..)
  , bindSurfaceCallableOutcomeBranchFacts
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import Phil.Compiler.CallableOutcomeContinuation
  ( SurfaceCallableOutcomeContinuation (..)
  , SurfaceCallableOutcomeContinuationDisposition (..)
  )
import Phil.Core.CallableOutcome (CallableOutcomeAtom)
import Phil.Core.Static (DeclarationKey)
import Phil.Core.Syntax (Proposition)
import Phil.Surface.Syntax (SourceSpan)

-- | Explicit competent binding from one opaque CALL outcome atom to the neutral
-- Surface proposition/evidence name that represents that exact fact in source.
--
-- The bridge never parses 'CallableOutcomeAtom' text.  The semantic atom remains
-- the identity key; proposition and evidence spelling are supplied explicitly by
-- the declaration/elaboration layer that knows their subject/context/revision.
data SurfaceCallableOutcomeFactBinding = SurfaceCallableOutcomeFactBinding
  { surfaceOutcomeFactAtom :: CallableOutcomeAtom
  , surfaceOutcomeFactEvidenceName :: Text
  , surfaceOutcomeFactProposition :: Proposition
  }
  deriving (Eq, Ord, Show)

-- | Exact neutral fact environment for one admitted outcome arm.  The three
-- usable fact categories remain distinct.  Residual obligations and effects are
-- retained through the complete continuation record and are deliberately not
-- reclassified as proof facts.
--
-- Declared-terminal outcomes produce an environment with no usable proof facts:
-- there is no caller continuation in which they could be consumed.
data SurfaceCallableOutcomeBranchFactEnvironment =
  SurfaceCallableOutcomeBranchFactEnvironment
    { surfaceBranchFactInvocationSpan :: SourceSpan
    , surfaceBranchFactArmSpan :: SourceSpan
    , surfaceBranchFactDeclarationKey :: DeclarationKey
    , surfaceBranchFactSourceLabel :: Text
    , surfaceBranchFactDisposition :: SurfaceCallableOutcomeContinuationDisposition
    , surfaceBranchPostconditions :: [SurfaceCallableOutcomeFactBinding]
    , surfaceBranchAssumptions :: [SurfaceCallableOutcomeFactBinding]
    , surfaceBranchDischargedFacts :: [SurfaceCallableOutcomeFactBinding]
    , surfaceBranchFactContinuation :: SurfaceCallableOutcomeContinuation
    }
  deriving (Eq, Ord, Show)

data SurfaceCallableOutcomeBranchFactError
  = SurfaceCallableOutcomeFactBindingDomainMismatch
      (Set CallableOutcomeAtom)
      (Set CallableOutcomeAtom)
  | SurfaceCallableOutcomeFactBindingKeyMismatch
      CallableOutcomeAtom
      CallableOutcomeAtom
  | SurfaceCallableOutcomeFactBindingEmptyEvidenceName CallableOutcomeAtom
  | SurfaceCallableOutcomeFactEvidenceNameCollision
      SourceSpan
      Text
      (Set CallableOutcomeAtom)
  deriving (Eq, Ord, Show)

-- | Build branch-local neutral fact environments from exact admitted outcome
-- continuations and an explicit semantic-atom binding table.
--
-- The binding table must cover exactly the proof-usable facts of continuing
-- branches: postconditions, assumptions, and discharged facts.  Missing facts
-- reject; extra facts reject; residual obligations/effects cannot enter this
-- table by accident.  Terminal-only facts are likewise not made available to a
-- nonexistent continuation.  Source-arm order is preserved.
bindSurfaceCallableOutcomeBranchFacts
  :: Map CallableOutcomeAtom SurfaceCallableOutcomeFactBinding
  -> [SurfaceCallableOutcomeContinuation]
  -> Either SurfaceCallableOutcomeBranchFactError
       [SurfaceCallableOutcomeBranchFactEnvironment]
bindSurfaceCallableOutcomeBranchFacts bindings continuations = do
  mapM_ validateBinding (Map.toAscList bindings)
  let expectedAtoms = Set.unions (map continuingUsableAtoms continuations)
      actualAtoms = Map.keysSet bindings
  if expectedAtoms == actualAtoms
    then pure ()
    else Left
      (SurfaceCallableOutcomeFactBindingDomainMismatch expectedAtoms actualAtoms)
  mapM makeEnvironment continuations
  where
    validateBinding (key, binding)
      | surfaceOutcomeFactAtom binding /= key =
          Left (SurfaceCallableOutcomeFactBindingKeyMismatch
            key
            (surfaceOutcomeFactAtom binding))
      | surfaceOutcomeFactEvidenceName binding == "" =
          Left (SurfaceCallableOutcomeFactBindingEmptyEvidenceName key)
      | otherwise = Right ()

    makeEnvironment continuation = case surfaceContinuationDisposition continuation of
      SurfaceCallableOutcomeCallerTerminates _ ->
        Right (environment continuation [] [] [])
      SurfaceCallableOutcomeCallerContinues -> do
        postconditions <- lookupFacts (surfaceContinuationPostconditions continuation)
        assumptions <- lookupFacts (surfaceContinuationAssumptions continuation)
        discharged <- lookupFacts (surfaceContinuationDischargedFacts continuation)
        checkEvidenceNames continuation (postconditions <> assumptions <> discharged)
        Right (environment continuation postconditions assumptions discharged)

    lookupFacts atoms = mapM lookupFact (Set.toAscList atoms)

    lookupFact atom = case Map.lookup atom bindings of
      Just binding -> Right binding
      Nothing -> Left
        (SurfaceCallableOutcomeFactBindingDomainMismatch
          (Set.singleton atom)
          Set.empty)

    environment continuation postconditions assumptions discharged =
      SurfaceCallableOutcomeBranchFactEnvironment
        { surfaceBranchFactInvocationSpan = surfaceContinuationInvocationSpan continuation
        , surfaceBranchFactArmSpan = surfaceContinuationArmSpan continuation
        , surfaceBranchFactDeclarationKey = surfaceContinuationDeclarationKey continuation
        , surfaceBranchFactSourceLabel = surfaceContinuationSourceLabel continuation
        , surfaceBranchFactDisposition = surfaceContinuationDisposition continuation
        , surfaceBranchPostconditions = postconditions
        , surfaceBranchAssumptions = assumptions
        , surfaceBranchDischargedFacts = discharged
        , surfaceBranchFactContinuation = continuation
        }

continuingUsableAtoms :: SurfaceCallableOutcomeContinuation -> Set CallableOutcomeAtom
continuingUsableAtoms continuation = case surfaceContinuationDisposition continuation of
  SurfaceCallableOutcomeCallerTerminates _ -> Set.empty
  SurfaceCallableOutcomeCallerContinues -> Set.unions
    [ surfaceContinuationPostconditions continuation
    , surfaceContinuationAssumptions continuation
    , surfaceContinuationDischargedFacts continuation
    ]

checkEvidenceNames
  :: SurfaceCallableOutcomeContinuation
  -> [SurfaceCallableOutcomeFactBinding]
  -> Either SurfaceCallableOutcomeBranchFactError ()
checkEvidenceNames continuation bindings = mapM_ checkOne (Map.toAscList byName)
  where
    byName = Map.fromListWith Set.union
      [ (surfaceOutcomeFactEvidenceName binding,
          Set.singleton (surfaceOutcomeFactAtom binding))
      | binding <- bindings
      ]

    checkOne (name, atoms)
      | Set.size atoms <= 1 = Right ()
      | otherwise = Left
          (SurfaceCallableOutcomeFactEvidenceNameCollision
            (surfaceContinuationArmSpan continuation)
            name
            atoms)
