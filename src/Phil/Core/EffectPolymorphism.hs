{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.EffectPolymorphism
  ( EffectSetParameterBound (..)
  , CheckedEffectSetInstantiation (..)
  , EffectSetInstantiationError (..)
  , effectSetSemanticForm
  , effectSetFromSemanticForm
  , checkBoundedEffectSetInstantiation
  ) where

import qualified Data.Set as Set
import Data.Set (Set)
import Phil.Core.Callable (SemanticEffect (..))
import Phil.Core.Generic (GenericStaticParameterKey)
import Phil.Core.Generic.StaticActual
  ( CheckedGenericStaticActual (..)
  , GenericStaticKind (..)
  )
import Phil.Core.Static (SemanticForm (..))

-- | One exact Effects parameter together with its public may-effect upper bound.
-- Parameter identity is the resolver-issued GenericStaticParameterKey; display
-- spelling never participates in this record.
data EffectSetParameterBound = EffectSetParameterBound
  { effectSetBoundParameterKey :: GenericStaticParameterKey
  , effectSetBoundUpper :: Set SemanticEffect
  }
  deriving (Eq, Ord, Show)

-- | Successful binding of one exact Effects parameter to one canonical finite
-- semantic effect set.  The actual remains separate from the upper bound because
-- a narrower instantiation must not silently narrow the declaration's bound.
data CheckedEffectSetInstantiation = CheckedEffectSetInstantiation
  { checkedEffectSetParameterKey :: GenericStaticParameterKey
  , checkedEffectSetActual :: Set SemanticEffect
  , checkedEffectSetUpper :: Set SemanticEffect
  }
  deriving (Eq, Ord, Show)

data EffectSetInstantiationError
  = EffectSetParameterKeyMismatch
      GenericStaticParameterKey
      GenericStaticParameterKey
  | EffectSetActualKindMismatch GenericStaticKind
  | EffectSetActualSemanticFormMalformed SemanticForm
  | EffectSetBoundExceeded
      GenericStaticParameterKey
      (Set SemanticEffect)
      (Set SemanticEffect)
  deriving (Eq, Ord, Show)

-- | Canonical SemanticForm representation for a finite Effects actual.  The
-- unordered carrier gives ordering/duplicate independence, while each member is
-- the already-canonical SemanticEffect identity (including exact subject keys).
effectSetSemanticForm :: Set SemanticEffect -> SemanticForm
effectSetSemanticForm effects =
  SemanticUnordered (Set.map effectForm effects)
  where
    effectForm (SemanticEffect effect) = SemanticAtom effect

-- | Decode only the canonical finite Effects representation.  Other semantic
-- forms remain outside this competence boundary rather than being guessed.
effectSetFromSemanticForm :: SemanticForm -> Maybe (Set SemanticEffect)
effectSetFromSemanticForm semantic = case semantic of
  SemanticUnordered entries ->
    Set.fromList <$> mapM effectFromForm (Set.toAscList entries)
  _ -> Nothing
  where
    effectFromForm entry = case entry of
      SemanticAtom effect -> Just (SemanticEffect effect)
      _ -> Nothing

-- | Bind one kind-checked static actual to one exact Effects parameter.  Generic
-- kind checking happens first; this authority owns only canonical effect-set
-- representation and bounded subeffecting.  Narrower/equal actuals are accepted;
-- any additional semantic effect rejects explicitly.
checkBoundedEffectSetInstantiation
  :: EffectSetParameterBound
  -> CheckedGenericStaticActual
  -> Either EffectSetInstantiationError CheckedEffectSetInstantiation
checkBoundedEffectSetInstantiation bound actual
  | actualKey /= expectedKey =
      Left (EffectSetParameterKeyMismatch expectedKey actualKey)
  | checkedGenericStaticKind actual /= GenericEffectsKind =
      Left (EffectSetActualKindMismatch (checkedGenericStaticKind actual))
  | otherwise = do
      actualEffects <- maybe
        (Left (EffectSetActualSemanticFormMalformed semanticForm))
        Right
        (effectSetFromSemanticForm semanticForm)
      let upper = effectSetBoundUpper bound
          extra = Set.difference actualEffects upper
      if Set.null extra
        then Right CheckedEffectSetInstantiation
          { checkedEffectSetParameterKey = expectedKey
          , checkedEffectSetActual = actualEffects
          , checkedEffectSetUpper = upper
          }
        else Left (EffectSetBoundExceeded expectedKey extra upper)
  where
    expectedKey = effectSetBoundParameterKey bound
    actualKey = checkedGenericStaticParameterKey actual
    semanticForm = checkedGenericStaticSemanticForm actual
