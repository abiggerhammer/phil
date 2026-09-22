{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.SortCheck
  ( SortError (..)
  , refSortOfTy
  , validateRefSort
  , sortOfRefTerm
  , checkTypeSorts
  , checkPropositionSorts
  , propositionSideConditions
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Checker (CheckState (..))
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Syntax
  ( Branch (..)
  , Name
  , PendingRecvSpec (..)
  , ProductElementType (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Session (..)
  , Ty (..)
  )

data SortError
  = UnknownRefinementVariable Name
  | NonRefinementVisibleVariable Name Ty
  | InvalidNatLiteral Integer
  | InvalidUIntLiteral Int Integer
  | InvalidUIntTypeWidth Int
  | InvalidAnnotatedSort RefSort
  | InvalidBytesIndexSort RefTerm RefSort
  | InvalidFieldProjection RefTerm RefSort Text
  | InvalidLengthOperand RefTerm RefSort
  | InvalidToNatOperand RefTerm RefSort
  | ExpectedNatOperand RefTerm RefSort
  | NegativeScaleCoefficient Integer
  | EqualitySortMismatch RefSort RefSort
  | InvalidOrderedSort RefSort RefSort
  | InvalidMembershipCollection RefSort
  | MembershipElementMismatch RefSort RefSort
  | InvalidDisjointCollection RefSort
  | DisjointSortMismatch RefSort RefSort
  deriving (Eq, Show)

refSortOfTy :: Ty -> Maybe RefSort
refSortOfTy ty =
  case ty of
    TyBool -> Just SortBool
    TyUInt width
      | width > 0 -> Just (SortUInt width)
      | otherwise -> Nothing
    TyBytes _ -> Just (SortFiniteSeq (SortUInt 8))
    TyFrame _ -> Just (SortOpaque "Frame")
    TyRefined _ base _ -> refSortOfTy base
    TyOpaque name -> Just (SortOpaque name)
    TyOpaqueSorted _ sort -> Just sort
    _ -> Nothing

type LogicalScope = Map.Map Name Ty

checkTypeSorts :: CheckState -> Ty -> Either SortError ()
checkTypeSorts = checkTypeSortsWith Map.empty

checkTypeSortsWith
  :: LogicalScope
  -> CheckState
  -> Ty
  -> Either SortError ()
checkTypeSortsWith scope state ty =
  case ty of
    TyUInt width
      | width <= 0 -> Left (InvalidUIntTypeWidth width)
      | otherwise -> Right ()
    TyBytes index -> do
      indexSort <- sortOfRefTermWith scope state index
      if indexSort == SortNat
        then Right ()
        else Left (InvalidBytesIndexSort index indexSort)
    TyPendingRecv pending ->
      checkSessionSorts
        (Map.insert
          (pendingBinder pending)
          (TyFrame (pendingGrammar pending))
          scope)
        state
        (pendingContinuation pending)
    TyProof proposition -> checkPropositionSortsWith scope state proposition
    TyEndpoint session -> checkSessionSorts scope state session
    TyProduct elements ->
      mapM_ (checkTypeSortsWith scope state . productElementType) elements
    TyRefined binder base proposition -> do
      checkTypeSortsWith scope state base
      checkPropositionSortsWith (Map.insert binder base scope) state proposition
    TyOpaqueSorted _ sort -> validateRefSort sort
    _ -> Right ()

checkSessionSorts
  :: LogicalScope
  -> CheckState
  -> Session
  -> Either SortError ()
checkSessionSorts scope state session =
  case session of
    Send binder message continuation -> do
      checkTypeSortsWith scope state message
      checkSessionSorts (Map.insert binder message scope) state continuation
    Receive binder message continuation -> do
      checkTypeSortsWith scope state message
      checkSessionSorts (Map.insert binder message scope) state continuation
    Select branches -> mapM_ checkBranch branches
    Offer branches -> mapM_ checkBranch branches
    End _ -> Right ()
    Rec _ body -> checkSessionSorts scope state body
    SessionVar _ -> Right ()
  where
    checkBranch branch =
      case branchPayload branch of
        Nothing ->
          checkSessionSorts scope state (branchContinuation branch)
        Just (binder, payload) -> do
          checkTypeSortsWith scope state payload
          checkSessionSorts
            (Map.insert binder payload scope)
            state
            (branchContinuation branch)

sortOfRefTerm :: CheckState -> RefTerm -> Either SortError RefSort
sortOfRefTerm = sortOfRefTermWith Map.empty

sortOfRefTermWith
  :: LogicalScope
  -> CheckState
  -> RefTerm
  -> Either SortError RefSort
sortOfRefTermWith scope state = go
  where
    go term =
      case term of
        RefVar name -> sortOfVariableWith scope state name
        RefNat literal
          | literal < 0 -> Left (InvalidNatLiteral literal)
          | otherwise -> Right SortNat
        RefUInt width literal
          | width <= 0 -> Left (InvalidUIntLiteral width literal)
          | literal < 0 || literal >= (2 ^ width) -> Left (InvalidUIntLiteral width literal)
          | otherwise -> Right (SortUInt width)
        RefBool _ -> Right SortBool
        RefField base field resultSort -> do
          validateRefSort resultSort
          baseSort <- go base
          case baseSort of
            SortOpaque _ -> Right resultSort
            _ -> Left (InvalidFieldProjection base baseSort field)
        RefLen value -> do
          valueSort <- go value
          case valueSort of
            SortFiniteSeq _ -> Right SortNat
            SortFiniteSet _ -> Right SortNat
            _ -> Left (InvalidLengthOperand value valueSort)
        RefToNat value -> do
          valueSort <- go value
          case valueSort of
            SortUInt _ -> Right SortNat
            _ -> Left (InvalidToNatOperand value valueSort)
        RefAdd left right -> natBinary left right
        RefSub left right -> natBinary left right
        RefScale coefficient value
          | coefficient < 0 -> Left (NegativeScaleCoefficient coefficient)
          | otherwise -> do
              valueSort <- go value
              if valueSort == SortNat
                then Right SortNat
                else Left (ExpectedNatOperand value valueSort)
        RefOpaque sort _ -> validateRefSort sort >> Right sort

    natBinary left right = do
      leftSort <- go left
      if leftSort /= SortNat
        then Left (ExpectedNatOperand left leftSort)
        else do
          rightSort <- go right
          if rightSort == SortNat
            then Right SortNat
            else Left (ExpectedNatOperand right rightSort)

checkPropositionSorts :: CheckState -> Proposition -> Either SortError ()
checkPropositionSorts = checkPropositionSortsWith Map.empty

checkPropositionSortsWith
  :: LogicalScope
  -> CheckState
  -> Proposition
  -> Either SortError ()
checkPropositionSortsWith scope state = go
  where
    termSort = sortOfRefTermWith scope state

    go proposition =
      case proposition of
        Truth -> Right ()
        Falsehood -> Right ()
        Equal left right -> sameSort left right
        NotEqual left right -> sameSort left right
        LessThan left right -> orderedSort left right
        LessEqual left right -> orderedSort left right
        Member value collection -> do
          valueSort <- termSort value
          collectionSort <- termSort collection
          case collectionSort of
            SortFiniteSeq elementSort -> membership valueSort elementSort
            SortFiniteSet elementSort -> membership valueSort elementSort
            _ -> Left (InvalidMembershipCollection collectionSort)
        Disjoint left right -> do
          leftSort <- termSort left
          rightSort <- termSort right
          if leftSort /= rightSort
            then Left (DisjointSortMismatch leftSort rightSort)
            else case leftSort of
              SortFiniteSeq _ -> Right ()
              SortFiniteSet _ -> Right ()
              _ -> Left (InvalidDisjointCollection leftSort)
        Conjunction left right -> go left >> go right
        Disjunction left right -> go left >> go right
        Negation inner -> go inner
        Atom _ arguments -> mapM_ (fmap (const ()) . termSort) arguments

    sameSort left right = do
      leftSort <- termSort left
      rightSort <- termSort right
      if leftSort == rightSort
        then Right ()
        else Left (EqualitySortMismatch leftSort rightSort)

    orderedSort left right = do
      leftSort <- termSort left
      rightSort <- termSort right
      case (leftSort, rightSort) of
        (SortNat, SortNat) -> Right ()
        (SortUInt leftWidth, SortUInt rightWidth)
          | leftWidth == rightWidth -> Right ()
        _ -> Left (InvalidOrderedSort leftSort rightSort)

    membership actual expected
      | actual == expected = Right ()
      | otherwise = Left (MembershipElementMismatch actual expected)

propositionSideConditions :: Proposition -> [Proposition]
propositionSideConditions proposition = deduplicate (goProposition proposition)
  where
    goProposition prop =
      case prop of
        Truth -> []
        Falsehood -> []
        Equal left right -> goTerm left ++ goTerm right
        NotEqual left right -> goTerm left ++ goTerm right
        LessThan left right -> goTerm left ++ goTerm right
        LessEqual left right -> goTerm left ++ goTerm right
        Member value collection -> goTerm value ++ goTerm collection
        Disjoint left right -> goTerm left ++ goTerm right
        Conjunction left right -> goProposition left ++ goProposition right
        Disjunction left right -> goProposition left ++ goProposition right
        Negation inner -> goProposition inner
        Atom _ arguments -> concatMap goTerm arguments

    goTerm term =
      case term of
        RefField base _ _ -> goTerm base
        RefLen value -> goTerm value
        RefToNat value -> goTerm value
        RefAdd left right -> goTerm left ++ goTerm right
        RefSub left right ->
          goTerm left ++ goTerm right ++ [LessEqual right left]
        RefScale _ value -> goTerm value
        _ -> []

    deduplicate [] = []
    deduplicate (first : rest) = first : deduplicate (filter (/= first) rest)

sortOfVariableWith
  :: LogicalScope
  -> CheckState
  -> Name
  -> Either SortError RefSort
sortOfVariableWith scope state name =
  case Map.lookup name scope <|> lookupBinding name (resourceContext state) of
    Nothing -> Left (UnknownRefinementVariable name)
    Just ty ->
      case refSortOfTy ty of
        Just sort -> Right sort
        Nothing -> Left (NonRefinementVisibleVariable name ty)

lookupBinding :: Name -> ResourceContext -> Maybe Ty
lookupBinding name context =
  Map.lookup name (unrestrictedBindings context)
    <|> Map.lookup name (affineBindings context)
    <|> Map.lookup name (linearBindings context)

validateRefSort :: RefSort -> Either SortError ()
validateRefSort sort =
  case sort of
    SortUInt width
      | width <= 0 -> Left (InvalidAnnotatedSort sort)
    SortFiniteSeq elementSort -> validateRefSort elementSort
    SortFiniteSet elementSort -> validateRefSort elementSort
    _ -> Right ()

infixr 3 <|>
(<|>) :: Maybe a -> Maybe a -> Maybe a
Nothing <|> right = right
left <|> _ = left
