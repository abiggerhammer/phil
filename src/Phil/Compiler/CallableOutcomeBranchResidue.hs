module Phil.Compiler.CallableOutcomeBranchResidue
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
        SurfaceCallableOutcomeCallerFatals _
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
        SurfaceCallableOutcomeCallerFatals _ ->
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
        SurfaceCallableOutcomeCallerFatals _ ->
          case callableOutcomeControl spec of
            CallableOutcomeFatals _ -> Right environment
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
    SurfaceCallableOutcomeCallerFatals _ -> Set.empty
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
