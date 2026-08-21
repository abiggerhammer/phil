{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Focusing
  ( FocusMechanism (..)
  , FocusStep (..)
  , FocusedRequirement (..)
  , FocusPlan (..)
  , FocusingError (..)
  , validateStaticContext
  , canonicalizeProposition
  , elaborateRefTermAs
  , focusProposition
  , resolveMode
  , focusSessionHead
  , checkBranchExhaustiveness
  ) where

import Control.Monad (foldM, zipWithM)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Checker
  ( CheckState (..)
  , emptyCheckState
  )
import Phil.Core.Context
  ( CheckError
  , ResourceContext (..)
  , insertBinding
  )
import Phil.Core.Refinement
  ( bindingEvidencePropositions
  , normalizeProposition
  , substituteProposition
  )
import Phil.Core.Session
  ( SessionError
  , exposeSessionHead
  )
import Phil.Core.SortCheck
  ( SortError
  , checkPropositionSorts
  , propositionSideConditions
  , sortOfRefTerm
  )
import Phil.Core.Static
  ( ClaimDecl (..)
  , ClaimDefinition (..)
  , StaticContext (..)
  , StaticError
  , lookupClaim
  )
import Phil.Core.Syntax
  ( Branch (..)
  , Mode (..)
  , Name (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Session
  , Ty (..)
  )

data FocusMechanism
  = FocusByDefinition
  | FocusByEvidence Name
  | FocusNeedsDecisionProcedure
  | FocusNeedsExplicitMechanism
  deriving (Eq, Ord, Show)

data FocusStep
  = ExpandedTransparentClaim Text
  | InsertedUIntToNat RefTerm
  | SurfacedPrerequisite Proposition
  | NormalizedProposition Proposition Proposition
  | MatchedInScopeEvidence Name
  deriving (Eq, Ord, Show)

data FocusedRequirement = FocusedRequirement
  { focusedOriginal :: Proposition
  , focusedCanonical :: Proposition
  , focusedMechanism :: FocusMechanism
  }
  deriving (Eq, Ord, Show)

data FocusPlan = FocusPlan
  { focusPrerequisites :: [FocusedRequirement]
  , focusGoal :: FocusedRequirement
  , focusTrace :: [FocusStep]
  }
  deriving (Eq, Show)

data FocusingError
  = FocusStaticError StaticError
  | FocusResourceError CheckError
  | FocusSortError SortError
  | FocusSessionError SessionError
  | UnknownClaim Text
  | ClaimArityMismatch Text Int Int
  | ClaimArgumentSortMismatch Text Int RefSort RefSort
  | RecursiveTransparentClaim [Text]
  | ExpectedRefinementSort RefTerm RefSort RefSort
  | StaticallyFalseGoal Proposition
  | UnknownModeBinding Name
  | DuplicateDeclaredBranchLabel Text
  | DuplicateBranchHandlerLabel Text
  | BranchHandlerMismatch [Text] [Text]
  deriving (Eq, Show)

validateStaticContext :: StaticContext -> Either FocusingError ()
validateStaticContext staticContext =
  mapM_ validateOne (Map.toAscList (staticClaims staticContext))
  where
    validateOne (claimName, declaration) = do
      state <- parameterState claimName (claimParameters declaration)
      case claimDefinition declaration of
        OpaqueClaim -> Right ()
        TransparentClaim body -> do
          _ <- canonicalizeDetailed staticContext state [claimName] body
          Right ()

canonicalizeProposition
  :: StaticContext
  -> CheckState
  -> Proposition
  -> Either FocusingError (Proposition, [FocusStep])
canonicalizeProposition staticContext state proposition = do
  validateStaticContext staticContext
  (_, canonical, _, steps) <- canonicalizeDetailed staticContext state [] proposition
  Right (canonical, steps)

elaborateRefTermAs
  :: StaticContext
  -> CheckState
  -> RefSort
  -> RefTerm
  -> Either FocusingError (RefTerm, [FocusStep])
elaborateRefTermAs staticContext state expected term = do
  validateStaticContext staticContext
  elaborateTermAs state expected term

focusProposition
  :: StaticContext
  -> CheckState
  -> Proposition
  -> Either FocusingError FocusPlan
focusProposition staticContext state proposition = do
  validateStaticContext staticContext
  focusRecursive staticContext state proposition

resolveMode :: CheckState -> Name -> Either FocusingError Mode
resolveMode state name
  | Map.member name (unrestrictedBindings context) = Right Unrestricted
  | Map.member name (affineBindings context) = Right Affine
  | Map.member name (linearBindings context) = Right Linear
  | otherwise = Left (UnknownModeBinding name)
  where
    context = resourceContext state

focusSessionHead :: Session -> Either FocusingError Session
focusSessionHead = mapLeft FocusSessionError . exposeSessionHead

checkBranchExhaustiveness :: [Branch] -> [Text] -> Either FocusingError ()
checkBranchExhaustiveness branches handlers = do
  case firstDuplicate declaredLabels of
    Just label -> Left (DuplicateDeclaredBranchLabel label)
    Nothing -> Right ()
  case firstDuplicate handlers of
    Just label -> Left (DuplicateBranchHandlerLabel label)
    Nothing -> Right ()
  let declared = Set.fromList declaredLabels
      handled = Set.fromList handlers
      missing = Set.toAscList (declared `Set.difference` handled)
      extra = Set.toAscList (handled `Set.difference` declared)
  if null missing && null extra
    then Right ()
    else Left (BranchHandlerMismatch missing extra)
  where
    declaredLabels = map branchLabel branches

focusRecursive
  :: StaticContext
  -> CheckState
  -> Proposition
  -> Either FocusingError FocusPlan
focusRecursive staticContext state proposition = do
  (_, canonical, sideConditions, steps) <-
    canonicalizeDetailed staticContext state [] proposition
  sidePlans <- mapM (focusRecursive staticContext state) sideConditions
  (mechanism, mechanismSteps) <- classifyRequirement staticContext state canonical
  let prerequisites = deduplicateRequirements $
        concatMap (\plan -> focusPrerequisites plan ++ [focusGoal plan]) sidePlans
      sideSteps = concatMap focusTrace sidePlans
      surfacedSteps = map (SurfacedPrerequisite . focusedCanonical . focusGoal) sidePlans
      preNormalizationSteps = filter (not . isNormalizationStep) steps
      normalizationSteps = filter isNormalizationStep steps
      goal = FocusedRequirement proposition canonical mechanism
  Right FocusPlan
    { focusPrerequisites = prerequisites
    , focusGoal = goal
    , focusTrace =
        preNormalizationSteps
          ++ surfacedSteps
          ++ sideSteps
          ++ normalizationSteps
          ++ mechanismSteps
    }

classifyRequirement
  :: StaticContext
  -> CheckState
  -> Proposition
  -> Either FocusingError (FocusMechanism, [FocusStep])
classifyRequirement staticContext state canonical
  | canonical == Truth = Right (FocusByDefinition, [])
  | otherwise = do
      matching <- findFocusedEvidence staticContext state canonical
      case matching of
        Just evidenceName ->
          Right (FocusByEvidence evidenceName, [MatchedInScopeEvidence evidenceName])
        Nothing
          | canonical == Falsehood -> Left (StaticallyFalseGoal canonical)
          | containsOpaqueClaim staticContext canonical ->
              Right (FocusNeedsExplicitMechanism, [])
          | otherwise -> Right (FocusNeedsDecisionProcedure, [])

findFocusedEvidence
  :: StaticContext
  -> CheckState
  -> Proposition
  -> Either FocusingError (Maybe Name)
findFocusedEvidence staticContext state required =
  goBindings (Map.toAscList (unrestrictedBindings (resourceContext state)))
  where
    goBindings [] = Right Nothing
    goBindings ((bindingName, ty) : rest) = do
      matches <- anyM (matchesRequired bindingName) (bindingEvidencePropositions bindingName ty)
      if matches then Right (Just bindingName) else goBindings rest

    matchesRequired _ candidate = do
      (_, canonicalCandidate, _, _) <-
        canonicalizeDetailed staticContext state [] candidate
      Right (canonicalCandidate == required)

canonicalizeDetailed
  :: StaticContext
  -> CheckState
  -> [Text]
  -> Proposition
  -> Either FocusingError (Proposition, Proposition, [Proposition], [FocusStep])
canonicalizeDetailed staticContext state expansionStack proposition = do
  (expanded, expansionSteps) <-
    elaborateProposition staticContext state expansionStack proposition
  mapLeft FocusSortError (checkPropositionSorts state expanded)
  let sideConditions = propositionSideConditions expanded
      canonical = normalizeProposition expanded
      normalizationSteps
        | canonical == expanded = []
        | otherwise = [NormalizedProposition expanded canonical]
  Right
    ( expanded
    , canonical
    , sideConditions
    , expansionSteps ++ normalizationSteps
    )

elaborateProposition
  :: StaticContext
  -> CheckState
  -> [Text]
  -> Proposition
  -> Either FocusingError (Proposition, [FocusStep])
elaborateProposition staticContext state expansionStack proposition =
  case proposition of
    Truth -> pure (Truth, [])
    Falsehood -> pure (Falsehood, [])
    Equal left right -> binary Equal left right
    NotEqual left right -> binary NotEqual left right
    LessThan left right -> ordered LessThan left right
    LessEqual left right -> ordered LessEqual left right
    Member value collection -> binary Member value collection
    Disjoint left right -> binary Disjoint left right
    Conjunction left right -> logical Conjunction left right
    Disjunction left right -> logical Disjunction left right
    Negation inner -> do
      (inner', steps) <- recur inner
      pure (Negation inner', steps)
    Atom claimName arguments ->
      elaborateClaimApplication staticContext state expansionStack claimName arguments
  where
    recur = elaborateProposition staticContext state expansionStack

    binary constructor left right = do
      (left', leftSteps) <- elaborateTerm state left
      (right', rightSteps) <- elaborateTerm state right
      pure (constructor left' right', leftSteps ++ rightSteps)

    ordered constructor left right = do
      (left0, leftSteps) <- elaborateTerm state left
      (right0, rightSteps) <- elaborateTerm state right
      leftSort <- mapLeft FocusSortError (sortOfRefTerm state left0)
      rightSort <- mapLeft FocusSortError (sortOfRefTerm state right0)
      let (left', right', coercionSteps) =
            case (leftSort, rightSort) of
              (SortNat, SortUInt _) ->
                (left0, RefToNat right0, [InsertedUIntToNat right0])
              (SortUInt _, SortNat) ->
                (RefToNat left0, right0, [InsertedUIntToNat left0])
              _ -> (left0, right0, [])
      pure
        ( constructor left' right'
        , leftSteps ++ rightSteps ++ coercionSteps
        )

    logical constructor left right = do
      (left', leftSteps) <- recur left
      (right', rightSteps) <- recur right
      pure (constructor left' right', leftSteps ++ rightSteps)

elaborateClaimApplication
  :: StaticContext
  -> CheckState
  -> [Text]
  -> Text
  -> [RefTerm]
  -> Either FocusingError (Proposition, [FocusStep])
elaborateClaimApplication staticContext state expansionStack claimName arguments = do
  declaration <-
    case lookupClaim claimName staticContext of
      Just found -> Right found
      Nothing -> Left (UnknownClaim claimName)
  let parameters = claimParameters declaration
  if length parameters /= length arguments
    then Left (ClaimArityMismatch claimName (length parameters) (length arguments))
    else Right ()
  elaborated <- zipWithM elaborateArgument [0 ..] (zip parameters arguments)
  let elaboratedArguments = map fst elaborated
      argumentSteps = concatMap snd elaborated
  case claimDefinition declaration of
    OpaqueClaim -> Right (Atom claimName elaboratedArguments, argumentSteps)
    TransparentClaim body
      | claimName `elem` expansionStack ->
          Left (RecursiveTransparentClaim (reverse (claimName : expansionStack)))
      | otherwise -> do
          let instantiated = foldl substituteOne body (zip parameters elaboratedArguments)
          (expanded, bodySteps) <- elaborateProposition
            staticContext
            state
            (claimName : expansionStack)
            instantiated
          Right
            ( expanded
            , argumentSteps ++ [ExpandedTransparentClaim claimName] ++ bodySteps
            )
  where
    elaborateArgument index ((_, expectedSort), argument) = do
      (argument', steps) <- elaborateTerm state argument
      actualSort <- mapLeft FocusSortError (sortOfRefTerm state argument')
      if actualSort == expectedSort
        then Right (argument', steps)
        else case (expectedSort, actualSort) of
          (SortNat, SortUInt _) ->
            Right (RefToNat argument', steps ++ [InsertedUIntToNat argument'])
          _ -> Left (ClaimArgumentSortMismatch claimName index expectedSort actualSort)

    substituteOne current ((parameterName, _), argument) =
      substituteProposition parameterName argument current

elaborateTerm
  :: CheckState
  -> RefTerm
  -> Either FocusingError (RefTerm, [FocusStep])
elaborateTerm state term =
  case term of
    RefVar _ -> pure (term, [])
    RefNat _ -> pure (term, [])
    RefUInt _ _ -> pure (term, [])
    RefBool _ -> pure (term, [])
    RefOpaque _ _ -> pure (term, [])
    RefField base field resultSort -> do
      (base', steps) <- elaborateTerm state base
      pure (RefField base' field resultSort, steps)
    RefLen value -> do
      (value', steps) <- elaborateTerm state value
      pure (RefLen value', steps)
    RefToNat value -> do
      (value', steps) <- elaborateTerm state value
      pure (RefToNat value', steps)
    RefAdd left right -> natBinary RefAdd left right
    RefSub left right -> natBinary RefSub left right
    RefScale coefficient value -> do
      (value', steps) <- elaborateTermAs state SortNat value
      pure (RefScale coefficient value', steps)
  where
    natBinary constructor left right = do
      (left', leftSteps) <- elaborateTermAs state SortNat left
      (right', rightSteps) <- elaborateTermAs state SortNat right
      pure (constructor left' right', leftSteps ++ rightSteps)

elaborateTermAs
  :: CheckState
  -> RefSort
  -> RefTerm
  -> Either FocusingError (RefTerm, [FocusStep])
elaborateTermAs state expected term = do
  (elaborated, steps) <- elaborateTerm state term
  actual <- mapLeft FocusSortError (sortOfRefTerm state elaborated)
  if actual == expected
    then Right (elaborated, steps)
    else case (expected, actual) of
      (SortNat, SortUInt _) ->
        Right (RefToNat elaborated, steps ++ [InsertedUIntToNat elaborated])
      _ -> Left (ExpectedRefinementSort elaborated expected actual)

containsOpaqueClaim :: StaticContext -> Proposition -> Bool
containsOpaqueClaim staticContext proposition =
  case proposition of
    Atom claimName _ ->
      case lookupClaim claimName staticContext of
        Just declaration -> claimDefinition declaration == OpaqueClaim
        Nothing -> False
    Conjunction left right -> recur left || recur right
    Disjunction left right -> recur left || recur right
    Negation inner -> recur inner
    _ -> False
  where
    recur = containsOpaqueClaim staticContext

parameterState
  :: Text
  -> [(Name, RefSort)]
  -> Either FocusingError CheckState
parameterState claimName parameters =
  foldM insertParameter emptyCheckState parameters
  where
    insertParameter state (parameterName, sort) = do
      context <- mapLeft FocusResourceError $
        insertBinding
          Unrestricted
          parameterName
          (TyOpaqueSorted ("claim-param:" <> claimName <> ":" <> unName parameterName) sort)
          (resourceContext state)
      Right state { resourceContext = context }

isNormalizationStep :: FocusStep -> Bool
isNormalizationStep step =
  case step of
    NormalizedProposition _ _ -> True
    _ -> False

firstDuplicate :: Ord a => [a] -> Maybe a
firstDuplicate = go Set.empty
  where
    go _ [] = Nothing
    go seen (value : rest)
      | Set.member value seen = Just value
      | otherwise = go (Set.insert value seen) rest

deduplicateRequirements :: [FocusedRequirement] -> [FocusedRequirement]
deduplicateRequirements = go Set.empty
  where
    go _ [] = []
    go seen (requirement : rest)
      | Set.member (focusedCanonical requirement) seen = go seen rest
      | otherwise = requirement : go (Set.insert (focusedCanonical requirement) seen) rest

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM _ [] = pure False
anyM predicate (value : rest) = do
  matches <- predicate value
  if matches then pure True else anyM predicate rest

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
