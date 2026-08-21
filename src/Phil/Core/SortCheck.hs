module Phil.Core.SortCheck
  ( RefSort (..)
  , SortError (..)
  , refSortOfTy
  , sortOfRefTerm
  , checkPropositionSorts
  , propositionSideConditions
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Checker (CheckState (..))
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Syntax
  ( Name
  , Proposition (..)
  , RefTerm (..)
  , Ty (..)
  )

data RefSort
  = SortBool
  | SortNat
  | SortUInt Int
  | SortEnum Text
  | SortFiniteSeq RefSort
  | SortFiniteSet RefSort
  | SortStableId Text
  | SortOpaque Text
  deriving (Eq, Ord, Show)

data SortError
  = UnknownRefinementVariable Name
  | NonRefinementVisibleVariable Name Ty
  | InvalidNatLiteral Integer
  | InvalidUIntLiteral Int Integer
  | InvalidAnnotatedSort RefSort
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
    _ -> Nothing

sortOfRefTerm :: CheckState -> RefTerm -> Either SortError RefSort
sortOfRefTerm state = go
  where
    go term =
      case term of
        RefVar name -> sortOfVariable state name
        RefNat literal
          | literal < 0 -> Left (InvalidNatLiteral literal)
          | otherwise -> Right SortNat
        RefUInt width literal
          | width <= 0 -> Left (InvalidUIntLiteral width literal)
          | literal < 0 || literal >= (2 ^ width) -> Left (InvalidUIntLiteral width literal)
          | otherwise -> Right (SortUInt width)
        RefBool _ -> Right SortBool
        RefField base field resultSort -> do
          ensureValidSort resultSort
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
        RefOpaque sort _ -> ensureValidSort sort >> Right sort

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
checkPropositionSorts state = go
  where
    termSort = sortOfRefTerm state

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

sortOfVariable :: CheckState -> Name -> Either SortError RefSort
sortOfVariable state name =
  case lookupBinding name (resourceContext state) of
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

ensureValidSort :: RefSort -> Either SortError ()
ensureValidSort sort =
  case sort of
    SortUInt width
      | width <= 0 -> Left (InvalidAnnotatedSort sort)
    SortFiniteSeq elementSort -> ensureValidSort elementSort
    SortFiniteSet elementSort -> ensureValidSort elementSort
    _ -> Right ()

infixr 3 <|>
(<|>) :: Maybe a -> Maybe a -> Maybe a
Nothing <|> right = right
left <|> _ = left
