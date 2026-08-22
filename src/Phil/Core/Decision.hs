{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Decision
  ( AssumptionRef (..)
  , SolverAssumption (..)
  , LinearBasis (..)
  , LinearCertificate (..)
  , DecisionCertificate (..)
  , CertificateError (..)
  , certificateCheckerId
  , certificateProducerId
  , checkDecisionCertificate
  , proposeDecisionCertificate
  ) where

import Data.List (find)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Checker (CheckState)
import Phil.Core.Refinement
  ( normalizeProposition
  , normalizeRefTerm
  )
import Phil.Core.SortCheck
  ( SortError
  , propositionSideConditions
  , sortOfRefTerm
  )
import Phil.Core.Syntax
  ( Name
  , ObligationId
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  )

data AssumptionRef
  = EvidenceFact Name Int
  | PrerequisiteFact ObligationId
  deriving (Eq, Ord, Show)

data SolverAssumption = SolverAssumption
  { solverAssumptionRef :: AssumptionRef
  , solverAssumptionProposition :: Proposition
  }
  deriving (Eq, Ord, Show)

data LinearBasis
  = BasisAssumption AssumptionRef Proposition
  | BasisNatLower RefTerm
  | BasisUIntLower Int RefTerm
  | BasisUIntUpper Int RefTerm
  deriving (Eq, Ord, Show)

data LinearCertificate = LinearCertificate
  { linearTerms :: [(LinearBasis, Rational)]
  , linearSlack :: Rational
  }
  deriving (Eq, Ord, Show)

data DecisionCertificate
  = CertificateTruth
  | CertificateAssumption AssumptionRef Proposition
  | CertificateLinear LinearCertificate
  | CertificateConjunction DecisionCertificate DecisionCertificate
  | CertificateDisjunctionLeft DecisionCertificate
  | CertificateDisjunctionRight DecisionCertificate
  | CertificateNotEqualLeft LinearCertificate
  | CertificateNotEqualRight LinearCertificate
  deriving (Eq, Ord, Show)

data CertificateError
  = CertificateSortError SortError
  | UnsupportedArithmeticTerm RefTerm
  | UnsupportedCertificateGoal Proposition
  | CertificateShapeMismatch Proposition DecisionCertificate
  | UnknownCertificateAssumption AssumptionRef Proposition
  | InvalidLinearAssumption Proposition
  | InvalidNatLowerBound RefTerm RefSort
  | InvalidUIntBound Int RefTerm
  | NegativeInequalityWeight LinearBasis Rational
  | EqualityUsesInequalityBasis LinearBasis
  | NegativeLinearSlack Rational
  | NonzeroEqualitySlack Rational
  | LinearCombinationMismatch Proposition
  | MissingPartialOperationPrerequisite Proposition
  | FalsePartialOperationPrerequisite Proposition
  deriving (Eq, Show)

certificateCheckerId :: Text
certificateCheckerId = "phil-core-linear-certificate-v1"

certificateProducerId :: Text
certificateProducerId = "phil-core-builtin-linear-proposer-v1"

checkDecisionCertificate
  :: CheckState
  -> [SolverAssumption]
  -> Proposition
  -> DecisionCertificate
  -> Either CertificateError ()
checkDecisionCertificate state assumptions proposition certificate = do
  ensurePartialOperationPrerequisites assumptions proposition
  let goal = decisionForm proposition
  checkCertificate state assumptions goal certificate

proposeDecisionCertificate
  :: CheckState
  -> [SolverAssumption]
  -> Proposition
  -> Maybe DecisionCertificate
proposeDecisionCertificate state assumptions proposition =
  if prerequisitesAvailable assumptions proposition
    then propose state assumptions (decisionForm proposition)
    else Nothing

checkCertificate
  :: CheckState
  -> [SolverAssumption]
  -> Proposition
  -> DecisionCertificate
  -> Either CertificateError ()
checkCertificate state assumptions goal certificate =
  case certificate of
    CertificateAssumption ref proposition -> do
      let candidate = decisionForm proposition
      if candidate /= goal
        then Left (CertificateShapeMismatch goal certificate)
        else requireAssumption assumptions ref candidate
    _ ->
      case goal of
        Truth ->
          case certificate of
            CertificateTruth -> Right ()
            _ -> Left (CertificateShapeMismatch goal certificate)
        Conjunction left right ->
          case certificate of
            CertificateConjunction leftCertificate rightCertificate -> do
              checkCertificate state assumptions left leftCertificate
              checkCertificate state assumptions right rightCertificate
            _ -> Left (CertificateShapeMismatch goal certificate)
        Disjunction left right ->
          case certificate of
            CertificateDisjunctionLeft leftCertificate ->
              checkCertificate state assumptions left leftCertificate
            CertificateDisjunctionRight rightCertificate ->
              checkCertificate state assumptions right rightCertificate
            _ -> Left (CertificateShapeMismatch goal certificate)
        Equal _ _ ->
          case certificate of
            CertificateLinear linearCertificate ->
              checkLinearCertificate state assumptions EqualityGoal goal linearCertificate
            _ -> Left (CertificateShapeMismatch goal certificate)
        LessEqual _ _ ->
          case certificate of
            CertificateLinear linearCertificate ->
              checkLinearCertificate state assumptions InequalityGoal goal linearCertificate
            _ -> Left (CertificateShapeMismatch goal certificate)
        LessThan _ _ ->
          case certificate of
            CertificateLinear linearCertificate ->
              checkLinearCertificate state assumptions InequalityGoal goal linearCertificate
            _ -> Left (CertificateShapeMismatch goal certificate)
        NotEqual left right ->
          case certificate of
            CertificateNotEqualLeft linearCertificate ->
              checkLinearCertificate
                state assumptions InequalityGoal (LessThan left right) linearCertificate
            CertificateNotEqualRight linearCertificate ->
              checkLinearCertificate
                state assumptions InequalityGoal (LessThan right left) linearCertificate
            _ -> Left (CertificateShapeMismatch goal certificate)
        _ -> Left (UnsupportedCertificateGoal goal)

data GoalKind = EqualityGoal | InequalityGoal
  deriving (Eq, Show)

data BasisKind = EqualityBasis | InequalityBasis
  deriving (Eq, Show)

data Affine = Affine
  { affineTerms :: Map.Map RefTerm Rational
  , affineConstant :: Rational
  }
  deriving (Eq, Show)

zeroAffine :: Affine
zeroAffine = Affine Map.empty 0

normalizeAffine :: Affine -> Affine
normalizeAffine (Affine terms constant) =
  Affine (Map.filter (/= 0) terms) constant

addAffine :: Affine -> Affine -> Affine
addAffine (Affine leftTerms leftConstant) (Affine rightTerms rightConstant) =
  normalizeAffine $ Affine
    (Map.unionWith (+) leftTerms rightTerms)
    (leftConstant + rightConstant)

scaleAffine :: Rational -> Affine -> Affine
scaleAffine coefficient (Affine terms constant) =
  normalizeAffine $ Affine
    (Map.map (* coefficient) terms)
    (coefficient * constant)

subtractAffine :: Affine -> Affine -> Affine
subtractAffine left right = addAffine left (scaleAffine (-1) right)

constantAffine :: Rational -> Affine
constantAffine value = Affine Map.empty value

leafAffine :: RefTerm -> Affine
leafAffine term = Affine (Map.singleton term 1) 0

termToAffine :: CheckState -> RefTerm -> Either CertificateError Affine
termToAffine state original = do
  sort <- mapLeft CertificateSortError (sortOfRefTerm state original)
  case sort of
    SortNat -> go (normalizeRefTerm original)
    SortUInt _ -> go (normalizeRefTerm original)
    _ -> Left (UnsupportedArithmeticTerm original)
  where
    go term =
      case term of
        RefNat literal -> Right (constantAffine (fromInteger literal))
        RefUInt _ literal -> Right (constantAffine (fromInteger literal))
        RefAdd left right -> addAffine <$> go left <*> go right
        RefSub left right -> subtractAffine <$> go left <*> go right
        RefScale coefficient value ->
          scaleAffine (fromInteger coefficient) <$> go value
        RefToNat value ->
          case normalizeRefTerm (RefToNat value) of
            RefNat literal -> Right (constantAffine (fromInteger literal))
            normalized -> Right (leafAffine normalized)
        RefVar _ -> Right (leafAffine term)
        RefField _ _ _ -> Right (leafAffine term)
        RefLen _ -> Right (leafAffine term)
        RefOpaque _ _ -> Right (leafAffine term)
        _ -> Left (UnsupportedArithmeticTerm term)

relationAffine :: CheckState -> Proposition -> Either CertificateError (GoalKind, Affine)
relationAffine state proposition =
  case decisionForm proposition of
    Equal left right -> do
      leftAffine <- termToAffine state left
      rightAffine <- termToAffine state right
      Right (EqualityGoal, subtractAffine rightAffine leftAffine)
    LessEqual left right -> do
      leftAffine <- termToAffine state left
      rightAffine <- termToAffine state right
      Right (InequalityGoal, subtractAffine rightAffine leftAffine)
    LessThan left right -> do
      leftAffine <- termToAffine state left
      rightAffine <- termToAffine state right
      Right
        ( InequalityGoal
        , addAffine (subtractAffine rightAffine leftAffine) (constantAffine (-1))
        )
    other -> Left (InvalidLinearAssumption other)

checkLinearCertificate
  :: CheckState
  -> [SolverAssumption]
  -> GoalKind
  -> Proposition
  -> LinearCertificate
  -> Either CertificateError ()
checkLinearCertificate state assumptions goalKind proposition certificate = do
  (actualKind, target) <- relationAffine state proposition
  if actualKind /= goalKind
    then Left (UnsupportedCertificateGoal proposition)
    else Right ()
  case goalKind of
    EqualityGoal
      | linearSlack certificate /= 0 ->
          Left (NonzeroEqualitySlack (linearSlack certificate))
    InequalityGoal
      | linearSlack certificate < 0 ->
          Left (NegativeLinearSlack (linearSlack certificate))
    _ -> Right ()
  pieces <- mapM (basisPiece state assumptions goalKind) (linearTerms certificate)
  let combined = foldl addAffine (constantAffine (linearSlack certificate)) pieces
  if normalizeAffine combined == normalizeAffine target
    then Right ()
    else Left (LinearCombinationMismatch proposition)

basisPiece
  :: CheckState
  -> [SolverAssumption]
  -> GoalKind
  -> (LinearBasis, Rational)
  -> Either CertificateError Affine
basisPiece state assumptions goalKind (basis, coefficient) = do
  (basisKind, relation) <- basisRelation state assumptions basis
  case (goalKind, basisKind) of
    (EqualityGoal, InequalityBasis) -> Left (EqualityUsesInequalityBasis basis)
    (InequalityGoal, InequalityBasis)
      | coefficient < 0 -> Left (NegativeInequalityWeight basis coefficient)
    _ -> Right ()
  Right (scaleAffine coefficient relation)

basisRelation
  :: CheckState
  -> [SolverAssumption]
  -> LinearBasis
  -> Either CertificateError (BasisKind, Affine)
basisRelation state assumptions basis =
  case basis of
    BasisAssumption ref proposition -> do
      let canonical = decisionForm proposition
      requireAssumption assumptions ref canonical
      (goalKind, relation) <- relationAffine state canonical
      Right
        ( case goalKind of
            EqualityGoal -> EqualityBasis
            InequalityGoal -> InequalityBasis
        , relation
        )
    BasisNatLower term -> do
      ensurePartialOperationPrerequisites assumptions (Equal term term)
      sort <- mapLeft CertificateSortError (sortOfRefTerm state term)
      if sort == SortNat
        then do
          relation <- termToAffine state term
          Right (InequalityBasis, relation)
        else Left (InvalidNatLowerBound term sort)
    BasisUIntLower width term -> do
      requireUIntWidth state width term
      relation <- termToAffine state term
      Right (InequalityBasis, relation)
    BasisUIntUpper width term -> do
      requireUIntWidth state width term
      relation <- termToAffine state term
      let maximumValue = fromInteger ((2 ^ width) - 1)
      Right
        ( InequalityBasis
        , subtractAffine (constantAffine maximumValue) relation
        )

requireUIntWidth :: CheckState -> Int -> RefTerm -> Either CertificateError ()
requireUIntWidth state expected term =
  case uintWidthForTerm state term of
    Just width
      | width == expected -> Right ()
    _ -> Left (InvalidUIntBound expected term)

uintWidthForTerm :: CheckState -> RefTerm -> Maybe Int
uintWidthForTerm state term =
  case sortOfRefTerm state term of
    Right (SortUInt width) -> Just width
    Right SortNat ->
      case term of
        RefToNat inner ->
          case sortOfRefTerm state inner of
            Right (SortUInt width) -> Just width
            _ -> Nothing
        _ -> Nothing
    _ -> Nothing

requireAssumption
  :: [SolverAssumption]
  -> AssumptionRef
  -> Proposition
  -> Either CertificateError ()
requireAssumption assumptions ref proposition =
  case find matches assumptions of
    Just _ -> Right ()
    Nothing -> Left (UnknownCertificateAssumption ref proposition)
  where
    canonical = decisionForm proposition
    matches assumption =
      solverAssumptionRef assumption == ref
        && decisionForm (solverAssumptionProposition assumption) == canonical

ensurePartialOperationPrerequisites
  :: [SolverAssumption]
  -> Proposition
  -> Either CertificateError ()
ensurePartialOperationPrerequisites assumptions proposition =
  mapM_ requirePrerequisite (propositionSideConditions proposition)
  where
    requirePrerequisite prerequisite =
      case decisionForm prerequisite of
        Truth -> Right ()
        Falsehood -> Left (FalsePartialOperationPrerequisite prerequisite)
        canonical
          | any ((== canonical) . decisionForm . solverAssumptionProposition) assumptions -> Right ()
          | otherwise -> Left (MissingPartialOperationPrerequisite canonical)

prerequisitesAvailable :: [SolverAssumption] -> Proposition -> Bool
prerequisitesAvailable assumptions proposition =
  all available (propositionSideConditions proposition)
  where
    available prerequisite =
      case decisionForm prerequisite of
        Truth -> True
        Falsehood -> False
        canonical ->
          any ((== canonical) . decisionForm . solverAssumptionProposition) assumptions

propose
  :: CheckState
  -> [SolverAssumption]
  -> Proposition
  -> Maybe DecisionCertificate
propose state assumptions goal =
  case findExactAssumption assumptions goal of
    Just assumption ->
      Just (CertificateAssumption
        (solverAssumptionRef assumption)
        (solverAssumptionProposition assumption))
    Nothing ->
      case goal of
        Truth -> Just CertificateTruth
        Conjunction left right ->
          CertificateConjunction
            <$> propose state assumptions left
            <*> propose state assumptions right
        Disjunction left right ->
          case propose state assumptions left of
            Just leftCertificate -> Just (CertificateDisjunctionLeft leftCertificate)
            Nothing -> CertificateDisjunctionRight <$> propose state assumptions right
        Equal _ _ -> CertificateLinear <$> proposeEquality state assumptions goal
        LessEqual _ _ -> CertificateLinear <$> proposeInequality state assumptions goal
        LessThan _ _ -> CertificateLinear <$> proposeInequality state assumptions goal
        NotEqual left right ->
          case proposeInequality state assumptions (LessThan left right) of
            Just linearCertificate -> Just (CertificateNotEqualLeft linearCertificate)
            Nothing ->
              CertificateNotEqualRight
                <$> proposeInequality state assumptions (LessThan right left)
        _ -> Nothing

findExactAssumption :: [SolverAssumption] -> Proposition -> Maybe SolverAssumption
findExactAssumption assumptions proposition =
  find ((== decisionForm proposition) . decisionForm . solverAssumptionProposition) assumptions

proposeEquality
  :: CheckState
  -> [SolverAssumption]
  -> Proposition
  -> Maybe LinearCertificate
proposeEquality state assumptions proposition = do
  (_, target) <- either (const Nothing) Just (relationAffine state proposition)
  if target == zeroAffine
    then Just (LinearCertificate [] 0)
    else
      let candidates = equalityCandidates state assumptions
      in case find (\(_, relation) -> relation == target) candidates of
          Just (basis, _) -> Just (LinearCertificate [(basis, 1)] 0)
          Nothing ->
            case find (\(_, relation) -> scaleAffine (-1) relation == target) candidates of
              Just (basis, _) -> Just (LinearCertificate [(basis, -1)] 0)
              Nothing -> proposeEqualityPair target candidates

proposeEqualityPair
  :: Affine
  -> [(LinearBasis, Affine)]
  -> Maybe LinearCertificate
proposeEqualityPair target candidates =
  firstJust
    [ if addAffine (scaleAffine leftSign leftRelation) (scaleAffine rightSign rightRelation) == target
        then Just (LinearCertificate [(leftBasis, leftSign), (rightBasis, rightSign)] 0)
        else Nothing
    | (leftBasis, leftRelation) <- take 10 candidates
    , (rightBasis, rightRelation) <- take 10 candidates
    , leftBasis < rightBasis
    , leftSign <- [1, -1]
    , rightSign <- [1, -1]
    ]

proposeInequality
  :: CheckState
  -> [SolverAssumption]
  -> Proposition
  -> Maybe LinearCertificate
proposeInequality state assumptions proposition = do
  (_, target) <- either (const Nothing) Just (relationAffine state proposition)
  let candidates = take 10 (inequalityCandidates state assumptions)
      subsets = subsetsUpTo 3 candidates
  firstJust
    [ do
        let selectedRelation = foldl addAffine zeroAffine (map snd selected)
            residual = subtractAffine target selectedRelation
        domainCertificate <- domainDecompose state residual
        Just domainCertificate
          { linearTerms =
              [(basis, 1) | (basis, _) <- selected]
                ++ linearTerms domainCertificate
          }
    | selected <- subsets
    ]

equalityCandidates
  :: CheckState
  -> [SolverAssumption]
  -> [(LinearBasis, Affine)]
equalityCandidates state assumptions =
  [ (BasisAssumption (solverAssumptionRef assumption) proposition, relation)
  | assumption <- assumptions
  , let proposition = decisionForm (solverAssumptionProposition assumption)
  , Right (EqualityGoal, relation) <- [relationAffine state proposition]
  ]

inequalityCandidates
  :: CheckState
  -> [SolverAssumption]
  -> [(LinearBasis, Affine)]
inequalityCandidates state assumptions =
  [ (BasisAssumption (solverAssumptionRef assumption) proposition, relation)
  | assumption <- assumptions
  , let proposition = decisionForm (solverAssumptionProposition assumption)
  , Right (InequalityGoal, relation) <- [relationAffine state proposition]
  ]

domainDecompose :: CheckState -> Affine -> Maybe LinearCertificate
domainDecompose state target = do
  basisTerms <- mapM chooseBasis (Map.toAscList (affineTerms target))
  let pieces = concatMap fst basisTerms
      built = foldl addAffine zeroAffine (concatMap snd basisTerms)
      remaining = subtractAffine target built
  if Map.null (affineTerms remaining) && affineConstant remaining >= 0
    then Just (LinearCertificate pieces (affineConstant remaining))
    else Nothing
  where
    chooseBasis (term, coefficient)
      | coefficient > 0 =
          case sortOfRefTerm state term of
            Right SortNat ->
              Just
                ( [(BasisNatLower term, coefficient)]
                , [scaleAffine coefficient (leafOrAffine term)]
                )
            Right (SortUInt width) ->
              Just
                ( [(BasisUIntLower width term, coefficient)]
                , [scaleAffine coefficient (leafOrAffine term)]
                )
            _ -> Nothing
      | coefficient < 0 = do
          width <- uintWidthForTerm state term
          relation <- either (const Nothing) Just (termToAffine state term)
          let weight = negate coefficient
              maximumValue = fromInteger ((2 ^ width) - 1)
              upperRelation = subtractAffine (constantAffine maximumValue) relation
          Just
            ( [(BasisUIntUpper width term, weight)]
            , [scaleAffine weight upperRelation]
            )
      | otherwise = Just ([], [])

    leafOrAffine term =
      case termToAffine state term of
        Right relation -> relation
        Left _ -> leafAffine term

subsetsUpTo :: Int -> [a] -> [[a]]
subsetsUpTo limit values = go limit values
  where
    go _ [] = [[]]
    go 0 _ = [[]]
    go remaining (value : rest) =
      let without = go remaining rest
          with = map (value :) (go (remaining - 1) rest)
      in without ++ with

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (candidate : rest) =
  case candidate of
    Just value -> Just value
    Nothing -> firstJust rest

decisionForm :: Proposition -> Proposition
decisionForm proposition =
  case normalizeProposition proposition of
    Negation inner -> negateForm (decisionForm inner)
    Conjunction left right -> Conjunction (decisionForm left) (decisionForm right)
    Disjunction left right -> Disjunction (decisionForm left) (decisionForm right)
    other -> other
  where
    negateForm inner =
      case inner of
        Truth -> Falsehood
        Falsehood -> Truth
        Negation nested -> decisionForm nested
        Conjunction left right ->
          Disjunction
            (decisionForm (Negation left))
            (decisionForm (Negation right))
        Disjunction left right ->
          Conjunction
            (decisionForm (Negation left))
            (decisionForm (Negation right))
        LessEqual left right -> LessThan right left
        LessThan left right -> LessEqual right left
        Equal left right -> NotEqual left right
        NotEqual left right -> Equal left right
        other -> Negation other

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
