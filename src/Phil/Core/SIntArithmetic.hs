{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.SIntArithmetic
  ( SIntType (..)
  , SIntLiteral (..)
  , SIntTerm (..)
  , sIntCoreType
  , sIntTypeFromCoreType
  , sIntLiteralInRange
  , SIntArithmeticOperator (..)
  , PlainSIntArithmeticSite (..)
  , PlainSIntArithmeticDecision (..)
  , SIntArithmeticError (..)
  , checkPlainSIntArithmetic
  , plainSIntArithmeticProposition
  , applySIntArithmeticOperator
  , registerSIntArithmeticClaims
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Read as TextRead
import Phil.Core.Checker (CheckState)
import Phil.Core.Static
  ( ClaimDecl (..)
  , ClaimDefinition (..)
  , StaticContext
  , StaticError (..)
  , declareOpaqueClaim
  , lookupClaim
  )
import Phil.Core.Syntax
  ( Name (..)
  , Obligation (..)
  , ObligationId
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Ty (..)
  )

-- | EXEC-016's signed scalar identity is intentionally local to the signed
-- numeric authority. It does not widen the Phase-0 Systems/LLVM scalar carrier;
-- backend realization remains a later checked relation.
newtype SIntType = SIntType { sIntWidth :: Int }
  deriving (Eq, Ord, Show)

data SIntLiteral = SIntLiteral
  { sIntLiteralType :: SIntType
  , sIntLiteralValue :: Integer
  }
  deriving (Eq, Ord, Show)

data SIntTerm
  = SIntKnown SIntLiteral
  | SIntSymbolic SIntType Text
  deriving (Eq, Ord, Show)

-- | Reuse Core's exact opaque-sorted type identity without pretending that the
-- existing backend ScalarType already admits signed realization.
sIntCoreType :: SIntType -> Ty
sIntCoreType ty@(SIntType width) =
  TyOpaqueSorted (renderType ty) (SortOpaque ("phil.sint.v1:" <> Text.pack (show width)))

sIntTypeFromCoreType :: Ty -> Maybe SIntType
sIntTypeFromCoreType ty = case ty of
  TyOpaqueSorted display (SortOpaque semantic) -> do
    width <- parseWidth display
    if semantic == "phil.sint.v1:" <> Text.pack (show width)
      then Just (SIntType width)
      else Nothing
  _ -> Nothing

sIntLiteralInRange :: SIntLiteral -> Bool
sIntLiteralInRange (SIntLiteral (SIntType width) value) =
  width > 0
    && value >= negate (2 ^ (width - 1))
    && value < 2 ^ (width - 1)

data SIntArithmeticOperator
  = SIntAdd
  | SIntSubtract
  | SIntMultiply
  deriving (Eq, Ord, Show)

data PlainSIntArithmeticSite = PlainSIntArithmeticSite
  { plainSIntArithmeticObligationId :: ObligationId
  , plainSIntArithmeticOrigin :: Text
  , plainSIntArithmeticScope :: Text
  , plainSIntArithmeticRequiredPoint :: Text
  }
  deriving (Eq, Ord, Show)

data PlainSIntArithmeticDecision
  = PlainSIntArithmeticEstablished SIntLiteral
  | PlainSIntArithmeticRequiresProof Obligation
  deriving (Eq, Show)

data SIntArithmeticError
  = SIntArithmeticInvalidWidth Int
  | SIntArithmeticOperandTypeMismatch SIntTerm SIntType
  | SIntArithmeticResultTypeMismatch SIntTerm SIntType
  | SIntArithmeticEmptySymbolicIdentity SIntTerm
  | SIntArithmeticKnownResultOutOfRange
      SIntArithmeticOperator Int Integer Integer Integer
  | SIntArithmeticKnownResultMismatch
      SIntArithmeticOperator Int Integer Integer Integer Integer
  deriving (Eq, Show)

checkPlainSIntArithmetic
  :: CheckState
  -> SIntArithmeticOperator
  -> SIntType
  -> SIntTerm
  -> SIntTerm
  -> SIntTerm
  -> PlainSIntArithmeticSite
  -> Either SIntArithmeticError PlainSIntArithmeticDecision
checkPlainSIntArithmetic _state operator ty@(SIntType width) left right result site = do
  if width > 0 then Right () else Left (SIntArithmeticInvalidWidth width)
  checkTerm SIntArithmeticOperandTypeMismatch ty left
  checkTerm SIntArithmeticOperandTypeMismatch ty right
  checkTerm SIntArithmeticResultTypeMismatch ty result
  case (knownValue left, knownValue right, knownValue result) of
    (Just leftValue, Just rightValue, Just actualResult) -> do
      let mathematicalResult = applySIntArithmeticOperator operator leftValue rightValue
          literal = SIntLiteral ty mathematicalResult
      if not (sIntLiteralInRange literal)
        then Left (SIntArithmeticKnownResultOutOfRange
          operator width leftValue rightValue mathematicalResult)
        else if actualResult /= mathematicalResult
          then Left (SIntArithmeticKnownResultMismatch
            operator width leftValue rightValue mathematicalResult actualResult)
          else Right (PlainSIntArithmeticEstablished literal)
    _ -> Right (PlainSIntArithmeticRequiresProof Obligation
      { obligationId = plainSIntArithmeticObligationId site
      , obligationProposition = plainSIntArithmeticProposition operator ty left right result
      , obligationOrigin = plainSIntArithmeticOrigin site
      , obligationScope = plainSIntArithmeticScope site
      , obligationRequiredPoint = plainSIntArithmeticRequiredPoint site
      })

-- | The opaque arithmetic claim receives a canonical biased-Nat encoding of
-- signed semantic values. This is proof identity, not target representation:
-- v maps to v + 2^(w-1), so the entire I[w] range is represented exactly while
-- existing Core proposition machinery remains unchanged.
plainSIntArithmeticProposition
  :: SIntArithmeticOperator
  -> SIntType
  -> SIntTerm
  -> SIntTerm
  -> SIntTerm
  -> Proposition
plainSIntArithmeticProposition operator ty@(SIntType width) left right result =
  Atom (operatorAtom operator)
    [ RefNat (toInteger width)
    , encodeTerm ty left
    , encodeTerm ty right
    , encodeTerm ty result
    ]

applySIntArithmeticOperator :: SIntArithmeticOperator -> Integer -> Integer -> Integer
applySIntArithmeticOperator operator left right = case operator of
  SIntAdd -> left + right
  SIntSubtract -> left - right
  SIntMultiply -> left * right

registerSIntArithmeticClaims :: StaticContext -> Either StaticError StaticContext
registerSIntArithmeticClaims context =
  foldM ensureClaim context [SIntAdd, SIntSubtract, SIntMultiply]
  where
    parameters =
      [ (Name "width", SortNat)
      , (Name "left-biased", SortNat)
      , (Name "right-biased", SortNat)
      , (Name "result-biased", SortNat)
      ]
    expected = ClaimDecl parameters OpaqueClaim
    ensureClaim current operator =
      let claimName = operatorAtom operator
      in case lookupClaim claimName current of
          Nothing -> declareOpaqueClaim claimName parameters current
          Just actual
            | actual == expected -> Right current
            | otherwise -> Left (DuplicateClaim claimName)

checkTerm
  :: (SIntTerm -> SIntType -> SIntArithmeticError)
  -> SIntType
  -> SIntTerm
  -> Either SIntArithmeticError ()
checkTerm mismatch expected term = do
  if termType term == expected then Right () else Left (mismatch term expected)
  case term of
    SIntSymbolic _ identity
      | Text.null (Text.strip identity) -> Left (SIntArithmeticEmptySymbolicIdentity term)
    _ -> Right ()

termType :: SIntTerm -> SIntType
termType term = case term of
  SIntKnown literal -> sIntLiteralType literal
  SIntSymbolic ty _ -> ty

knownValue :: SIntTerm -> Maybe Integer
knownValue term = case term of
  SIntKnown literal -> Just (sIntLiteralValue literal)
  SIntSymbolic {} -> Nothing

encodeTerm :: SIntType -> SIntTerm -> RefTerm
encodeTerm ty@(SIntType width) term = case term of
  SIntKnown literal -> RefNat (sIntLiteralValue literal + 2 ^ (width - 1))
  SIntSymbolic _ identity ->
    RefOpaque SortNat ("phil.sint.bias.v1:" <> renderType ty <> ":" <> identity)

renderType :: SIntType -> Text
renderType (SIntType width) = "I" <> Text.pack (show width)

parseWidth :: Text -> Maybe Int
parseWidth display = do
  digits <- Text.stripPrefix "I" display
  case TextRead.decimal digits :: Either String (Integer, Text) of
    Right (width, rest)
      | Text.null rest
      , width > 0
      , width <= toInteger (maxBound :: Int) -> Just (fromInteger width)
    _ -> Nothing

operatorAtom :: SIntArithmeticOperator -> Text
operatorAtom operator = case operator of
  SIntAdd -> "phil.sint.add.exact.v1"
  SIntSubtract -> "phil.sint.sub.exact.v1"
  SIntMultiply -> "phil.sint.mul.exact.v1"
