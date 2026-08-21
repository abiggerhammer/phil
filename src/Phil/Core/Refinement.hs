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
  , findMatchingEvidence
  , dischargeProposition
  , dischargePropositionUsing
  , residualizeProposition
  ) where

import qualified Data.Map.Strict as Map
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
import Phil.Core.Syntax
  ( Name
  , Obligation (..)
  , ObligationId
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
  | NotEvidenceBinding Name Ty
  | EvidenceDoesNotMatch Name Proposition Proposition
  | MissingEvidence Proposition
  | StaticallyFalse Proposition
  | ResidualObligationError CheckerError
  deriving (Eq, Show)

normalizeRefTerm :: RefTerm -> RefTerm
normalizeRefTerm term =
  case term of
    RefField base field -> RefField (normalizeRefTerm base) field
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
    RefField base field -> RefField (substituteRefTerm target replacement base) field
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
    RefField base _ -> termMentions target base
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
        , Just proposition <- [evidenceProposition ty]
        , normalizeProposition proposition == normalizedRequired
        ] of
          [] -> Nothing
          match : _ -> Just match

dischargeProposition :: Proposition -> CheckState -> Either RefinementError EvidenceUse
dischargeProposition required state =
  let normalized = normalizeProposition required
  in case normalized of
    Truth -> Right (EvidenceByDefinition required)
    _ ->
      case findMatchingEvidence normalized state of
        Just evidenceName -> Right (EvidenceByBinding evidenceName normalized)
        Nothing
          | normalized == Falsehood -> Left (StaticallyFalse required)
          | otherwise -> Left (MissingEvidence normalized)

dischargePropositionUsing
  :: Name
  -> Proposition
  -> CheckState
  -> Either RefinementError EvidenceUse
dischargePropositionUsing evidenceName required state = do
  (evidenceTy, _) <- mapLeft RefinementResourceError $
    useUnrestricted evidenceName (resourceContext state)
  actual <-
    case evidenceProposition evidenceTy of
      Just proposition -> Right (normalizeProposition proposition)
      Nothing -> Left (NotEvidenceBinding evidenceName evidenceTy)
  let expected = normalizeProposition required
  if actual == expected
    then Right (EvidenceByBinding evidenceName expected)
    else Left (EvidenceDoesNotMatch evidenceName actual expected)

residualizeProposition
  :: ResidualSpec
  -> Proposition
  -> CheckState
  -> Either RefinementError (EvidenceUse, CheckState)
residualizeProposition spec required state =
  case dischargeProposition required state of
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

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
