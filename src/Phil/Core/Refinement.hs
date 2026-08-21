{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Refinement
  ( EvidenceUse (..)
  , ResidualSpec (..)
  , RefinementError (..)
  , normalizeRefTerm
  , normalizeProposition
  , substituteRefTerm
  , substituteProposition
  , propositionMentions
  , evidenceProposition
  , bindingEvidencePropositions
  , findMatchingEvidence
  , dischargeSideConditions
  , residualizeSideConditions
  , dischargeProposition
  , dischargePropositionUsing
  , residualizeProposition
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Data.Text (Text)
import Phil.Core.Checker
  ( CheckState (..)
  , CheckerError
  , emitObligation
  )
import Phil.Core.Context
  ( CheckError
  , ResourceContext (..)
  , useUnrestricted
  )
import Phil.Core.SortCheck
  ( SortError
  , checkPropositionSorts
  , propositionSideConditions
  )
import Phil.Core.Syntax
  ( Name
  , Obligation (..)
  , ObligationId (..)
  , Proposition (..)
  , RefTerm (..)
  , Ty (..)
  )

data EvidenceUse
  = EvidenceByDefinition Proposition
  | EvidenceByBinding Name Proposition
  | EvidenceResidual ObligationId Proposition
  deriving (Eq, Ord, Show)

data ResidualSpec = ResidualSpec
  { residualObligationId :: ObligationId
  , residualOrigin :: Text
  , residualScope :: Text
  , residualRequiredPoint :: Text
  }
  deriving (Eq, Ord, Show)

data RefinementError
  = RefinementResourceError CheckError
  | RefinementSortError SortError
  | NotEvidenceBinding Name Ty
  | EvidenceDoesNotMatch Name Proposition Proposition
  | MissingEvidence Proposition
  | StaticallyFalse Proposition
  | ResidualObligationError CheckerError
  deriving (Eq, Show)

normalizeRefTerm :: RefTerm -> RefTerm
normalizeRefTerm term =
  case term of
    RefField base field sort -> RefField (normalizeRefTerm base) field sort
    RefLen value -> RefLen (normalizeRefTerm value)
    RefToNat value ->
      case normalizeRefTerm value of
        RefUInt _ literal -> RefNat literal
        normalized -> RefToNat normalized
    RefAdd left right ->
      case (normalizeRefTerm left, normalizeRefTerm right) of
        (RefNat 0, normalized) -> normalized
        (normalized, RefNat 0) -> normalized
        (RefNat a, RefNat b) -> RefNat (a + b)
        (a, b) -> RefAdd a b
    RefSub left right ->
      case (normalizeRefTerm left, normalizeRefTerm right) of
        (normalized, RefNat 0) -> normalized
        (RefNat a, RefNat b)
          | b <= a -> RefNat (a - b)
        (a, b) -> RefSub a b
    RefScale coefficient value ->
      case normalizeRefTerm value of
        _ | coefficient == 0 -> RefNat 0
        normalized | coefficient == 1 -> normalized
        RefNat literal -> RefNat (coefficient * literal)
        normalized -> RefScale coefficient normalized
    other -> other

normalizeProposition :: Proposition -> Proposition
normalizeProposition proposition =
  case proposition of
    Equal left right -> normalizeEqual (normalizeRefTerm left) (normalizeRefTerm right)
    NotEqual left right ->
      case normalizeEqual (normalizeRefTerm left) (normalizeRefTerm right) of
        Truth -> Falsehood
        Falsehood -> Truth
        Equal a b -> NotEqual a b
        other -> Negation other
    LessThan left right -> normalizeOrder LessThan (<) (normalizeRefTerm left) (normalizeRefTerm right)
    LessEqual left right -> normalizeOrder LessEqual (<=) (normalizeRefTerm left) (normalizeRefTerm right)
    Member value collection -> Member (normalizeRefTerm value) (normalizeRefTerm collection)
    Disjoint left right -> Disjoint (normalizeRefTerm left) (normalizeRefTerm right)
    Conjunction left right ->
      case (normalizeProposition left, normalizeProposition right) of
        (Falsehood, _) -> Falsehood
        (_, Falsehood) -> Falsehood
        (Truth, normalized) -> normalized
        (normalized, Truth) -> normalized
        (a, b) | a == b -> a
        (a, b) -> Conjunction a b
    Disjunction left right ->
      case (normalizeProposition left, normalizeProposition right) of
        (Truth, _) -> Truth
        (_, Truth) -> Truth
        (Falsehood, normalized) -> normalized
        (normalized, Falsehood) -> normalized
        (a, b) | a == b -> a
        (a, b) -> Disjunction a b
    Negation inner ->
      case normalizeProposition inner of
        Truth -> Falsehood
        Falsehood -> Truth
        Negation nested -> nested
        normalized -> Negation normalized
    Atom claim arguments -> Atom claim (map normalizeRefTerm arguments)
    other -> other

normalizeEqual :: RefTerm -> RefTerm -> Proposition
normalizeEqual left right
  | left == right = Truth
  | otherwise =
      case literalEquality left right of
        Just True -> Truth
        Just False -> Falsehood
        Nothing -> Equal left right

literalEquality :: RefTerm -> RefTerm -> Maybe Bool
literalEquality left right =
  case (left, right) of
    (RefNat a, RefNat b) -> Just (a == b)
    (RefUInt wa a, RefUInt wb b)
      | wa == wb -> Just (a == b)
    (RefBool a, RefBool b) -> Just (a == b)
    _ -> Nothing

normalizeOrder
  :: (RefTerm -> RefTerm -> Proposition)
  -> (Integer -> Integer -> Bool)
  -> RefTerm
  -> RefTerm
  -> Proposition
normalizeOrder constructor relation left right =
  case comparableIntegers left right of
    Just (a, b) -> if relation a b then Truth else Falsehood
    Nothing -> constructor left right

comparableIntegers :: RefTerm -> RefTerm -> Maybe (Integer, Integer)
comparableIntegers left right =
  case (left, right) of
    (RefNat a, RefNat b) -> Just (a, b)
    (RefUInt wa a, RefUInt wb b)
      | wa == wb -> Just (a, b)
    _ -> Nothing

substituteRefTerm :: Name -> RefTerm -> RefTerm -> RefTerm
substituteRefTerm target replacement term =
  case term of
    RefVar variable
      | variable == target -> replacement
      | otherwise -> term
    RefField base field sort -> RefField (substituteRefTerm target replacement base) field sort
    RefLen value -> RefLen (substituteRefTerm target replacement value)
    RefToNat value -> RefToNat (substituteRefTerm target replacement value)
    RefAdd left right ->
      RefAdd (substituteRefTerm target replacement left) (substituteRefTerm target replacement right)
    RefSub left right ->
      RefSub (substituteRefTerm target replacement left) (substituteRefTerm target replacement right)
    RefScale coefficient value -> RefScale coefficient (substituteRefTerm target replacement value)
    _ -> term

substituteProposition :: Name -> RefTerm -> Proposition -> Proposition
substituteProposition target replacement proposition =
  case proposition of
    Equal left right -> Equal (sub left) (sub right)
    NotEqual left right -> NotEqual (sub left) (sub right)
    LessThan left right -> LessThan (sub left) (sub right)
    LessEqual left right -> LessEqual (sub left) (sub right)
    Member value collection -> Member (sub value) (sub collection)
    Disjoint left right -> Disjoint (sub left) (sub right)
    Conjunction left right -> Conjunction (recur left) (recur right)
    Disjunction left right -> Disjunction (recur left) (recur right)
    Negation inner -> Negation (recur inner)
    Atom claim arguments -> Atom claim (map sub arguments)
    other -> other
  where
    sub = substituteRefTerm target replacement
    recur = substituteProposition target replacement

propositionMentions :: Name -> Proposition -> Bool
propositionMentions target proposition =
  case proposition of
    Equal left right -> mentions left || mentions right
    NotEqual left right -> mentions left || mentions right
    LessThan left right -> mentions left || mentions right
    LessEqual left right -> mentions left || mentions right
    Member value collection -> mentions value || mentions collection
    Disjoint left right -> mentions left || mentions right
    Conjunction left right -> propositionMentions target left || propositionMentions target right
    Disjunction left right -> propositionMentions target left || propositionMentions target right
    Negation inner -> propositionMentions target inner
    Atom _ arguments -> any mentions arguments
    _ -> False
  where
    mentions = termMentions target

termMentions :: Name -> RefTerm -> Bool
termMentions target term =
  case term of
    RefVar variable -> variable == target
    RefField base _ _ -> termMentions target base
    RefLen value -> termMentions target value
    RefToNat value -> termMentions target value
    RefAdd left right -> termMentions target left || termMentions target right
    RefSub left right -> termMentions target left || termMentions target right
    RefScale _ value -> termMentions target value
    _ -> False

evidenceProposition :: Ty -> Maybe Proposition
evidenceProposition ty =
  case ty of
    TyProof proposition -> Just proposition
    TyValidated claim context subject ->
      Just (Atom claim [RefVar context, RefVar subject])
    _ -> Nothing

bindingEvidencePropositions :: Name -> Ty -> [Proposition]
bindingEvidencePropositions subjectName ty =
  case ty of
    TyRefined binder base proposition ->
      substituteProposition binder (RefVar subjectName) proposition
        : bindingEvidencePropositions subjectName base
    _ ->
      case evidenceProposition ty of
        Just proposition -> [proposition]
        Nothing -> []

findMatchingEvidence :: Proposition -> CheckState -> Maybe Name
findMatchingEvidence required state =
  fst <$> firstMatching
  where
    normalizedRequired = normalizeProposition required
    candidates = Map.toAscList (unrestrictedBindings (resourceContext state))
    firstMatching =
      case
        [ (name, proposition)
        | (name, ty) <- candidates
        , proposition <- bindingEvidencePropositions name ty
        , normalizeProposition proposition == normalizedRequired
        ] of
          [] -> Nothing
          match : _ -> Just match

dischargeSideConditions
  :: Proposition
  -> CheckState
  -> Either RefinementError [EvidenceUse]
dischargeSideConditions required state = do
  sideConditions <- prepareProposition required state
  mapM (`directDischarge` state) sideConditions

residualizeSideConditions
  :: ResidualSpec
  -> Proposition
  -> CheckState
  -> Either RefinementError ([EvidenceUse], CheckState)
residualizeSideConditions spec required state = do
  sideConditions <- prepareProposition required state
  residualizeSides spec sideConditions state

dischargeProposition
  :: Proposition
  -> CheckState
  -> Either RefinementError [EvidenceUse]
dischargeProposition required state = do
  sideUses <- dischargeSideConditions required state
  mainUse <- directDischarge required state
  pure (deduplicateEvidence (sideUses ++ [mainUse]))

dischargePropositionUsing
  :: Name
  -> Proposition
  -> CheckState
  -> Either RefinementError [EvidenceUse]
dischargePropositionUsing evidenceName required state = do
  sideUses <- dischargeSideConditions required state
  mainUse <- directDischargeUsing evidenceName required state
  pure (deduplicateEvidence (sideUses ++ [mainUse]))

residualizeProposition
  :: ResidualSpec
  -> Proposition
  -> CheckState
  -> Either RefinementError ([EvidenceUse], CheckState)
residualizeProposition spec required state = do
  (sideUses, afterSides) <- residualizeSideConditions spec required state
  (mainUse, finalState) <- residualizeDirect spec required afterSides
  pure (deduplicateEvidence (sideUses ++ [mainUse]), finalState)

prepareProposition :: Proposition -> CheckState -> Either RefinementError [Proposition]
prepareProposition required state = do
  mapLeft RefinementSortError (checkPropositionSorts state required)
  let sideConditions = propositionSideConditions required
  mapM_ (mapLeft RefinementSortError . checkPropositionSorts state) sideConditions
  pure sideConditions

directDischarge :: Proposition -> CheckState -> Either RefinementError EvidenceUse
directDischarge required state =
  let normalized = normalizeProposition required
  in case normalized of
    Truth -> Right (EvidenceByDefinition required)
    Falsehood -> Left (StaticallyFalse required)
    _ ->
      case findMatchingEvidence normalized state of
        Just evidenceName -> Right (EvidenceByBinding evidenceName normalized)
        Nothing -> Left (MissingEvidence normalized)

directDischargeUsing
  :: Name
  -> Proposition
  -> CheckState
  -> Either RefinementError EvidenceUse
directDischargeUsing evidenceName required state = do
  (evidenceTy, _) <- mapLeft RefinementResourceError $
    useUnrestricted evidenceName (resourceContext state)
  actual <-
    case evidenceProposition evidenceTy of
      Just proposition -> Right (normalizeProposition proposition)
      Nothing -> Left (NotEvidenceBinding evidenceName evidenceTy)
  let expected = normalizeProposition required
  case expected of
    Falsehood -> Left (StaticallyFalse required)
    _
      | actual == expected -> Right (EvidenceByBinding evidenceName expected)
      | otherwise -> Left (EvidenceDoesNotMatch evidenceName actual expected)

residualizeSides
  :: ResidualSpec
  -> [Proposition]
  -> CheckState
  -> Either RefinementError ([EvidenceUse], CheckState)
residualizeSides spec sideConditions initial = go 1 [] initial sideConditions
  where
    go _ uses state [] = Right (reverse uses, state)
    go index uses state (side : rest) = do
      let sideSpec = subtractionResidualSpec spec index
      (use, next) <- residualizeDirect sideSpec side state
      go (index + 1) (use : uses) next rest

residualizeDirect
  :: ResidualSpec
  -> Proposition
  -> CheckState
  -> Either RefinementError (EvidenceUse, CheckState)
residualizeDirect spec required state =
  case directDischarge required state of
    Right evidenceUse -> Right (evidenceUse, state)
    Left (MissingEvidence normalized) -> do
      let obligation = Obligation
            { obligationId = residualObligationId spec
            , obligationProposition = normalized
            , obligationOrigin = residualOrigin spec
            , obligationScope = residualScope spec
            , obligationRequiredPoint = residualRequiredPoint spec
            }
      next <- mapLeft ResidualObligationError (emitObligation obligation state)
      Right
        ( EvidenceResidual (residualObligationId spec) normalized
        , next
        )
    Left other -> Left other

subtractionResidualSpec :: ResidualSpec -> Int -> ResidualSpec
subtractionResidualSpec parent index =
  parent
    { residualObligationId = ObligationId
        (unObligationId (residualObligationId parent)
          <> ".nat-sub."
          <> Text.pack (show index))
    }

deduplicateEvidence :: [EvidenceUse] -> [EvidenceUse]
deduplicateEvidence [] = []
deduplicateEvidence (first : rest) =
  first : deduplicateEvidence (filter (/= first) rest)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
