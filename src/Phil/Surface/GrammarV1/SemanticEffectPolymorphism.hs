module Phil.Surface.GrammarV1.SemanticEffectPolymorphism
  ( GrammarV1CheckedCallableEffectParameterBound (..)
  , GrammarV1CallableEffectParameterBoundError (..)
  , GrammarV1CallableEffectInstantiationError (..)
  , grammarV1CheckedCallableEffectParameterBounds
  , grammarV1InstantiateCallableEffectBounds
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Callable (SemanticEffect)
import Phil.Core.EffectPolymorphism
  ( CheckedEffectSetInstantiation (..)
  , EffectSetParameterBound (..)
  )
import Phil.Core.Generic (GenericStaticParameterKey)
import Phil.Core.Generic.StaticActual
  ( GenericStaticKind (..)
  , GenericStaticParameter (..)
  )
import Phil.Core.Static (DeclarationKey)
import Phil.Surface.GrammarV1.CallableEffects
  ( GrammarV1CallableEffectBoundTemplate (..)
  , grammarV1EffectSet
  )
import Phil.Surface.GrammarV1.GenericBinderScope
  ( GrammarV1GenericBinderScopeError
  , GrammarV1ResolvedGenericParameter (..)
  , grammarV1CallableGenericParameterScope
  , grammarV1ResolveGenericParameter
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableContractDecl (..)
  , GrammarV1GenericRequirement (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | One source `effects E within U` requirement after E has been resolved to the
-- exact declaration-rooted generic parameter and U to a canonical concrete
-- semantic effect set.  Source spelling remains diagnostic only.
data GrammarV1CheckedCallableEffectParameterBound =
  GrammarV1CheckedCallableEffectParameterBound
    { checkedCallableEffectParameterBoundSource
        :: Located GrammarV1GenericRequirement
    , checkedCallableEffectParameterBoundParameter
        :: GrammarV1ResolvedGenericParameter
    , checkedCallableEffectParameterBoundCore
        :: EffectSetParameterBound
    }
  deriving (Eq, Show)

data GrammarV1CallableEffectParameterBoundError
  = GrammarV1CallableEffectGenericScopeError GrammarV1GenericBinderScopeError
  | GrammarV1CallableEffectParameterKindMismatch
      GenericStaticParameterKey
      GenericStaticKind
  | GrammarV1CallableEffectUpperBoundUnsupported
      (Located GrammarV1GenericRequirement)
  | GrammarV1DuplicateCallableEffectParameterBound GenericStaticParameterKey
  deriving (Eq, Show)

data GrammarV1CallableEffectInstantiationError
  = GrammarV1DuplicateCallableEffectInstantiation GenericStaticParameterKey
  | GrammarV1MissingCallableEffectInstantiation GenericStaticParameterKey
  | GrammarV1UnexpectedCallableEffectInstantiation GenericStaticParameterKey
  deriving (Eq, Show)

-- | Resolve every callable Effects bound through the SURF-009 generic binder
-- authority.  The source name locates E; GenericStaticParameterKey identifies it.
-- This first bounded route requires a concrete upper set whose members already
-- have ordinary argument-free SemanticEffect identity.  Richer subject-bearing
-- upper bounds can compose through the EFF-001/002 subject resolver later without
-- changing this parameter/bounded-subset authority.
grammarV1CheckedCallableEffectParameterBounds
  :: DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Either
      GrammarV1CallableEffectParameterBoundError
      [GrammarV1CheckedCallableEffectParameterBound]
grammarV1CheckedCallableEffectParameterBounds declarationKey callable = do
  (_, genericScope) <- mapLeft GrammarV1CallableEffectGenericScopeError
    (grammarV1CallableGenericParameterScope declarationKey callable)
  go Set.empty genericScope (grammarV1CallableRequirements callable)
  where
    go _ _ [] = Right []
    go seen scope (source@(Located _ requirement) : rest) =
      case requirement of
        GrammarV1EffectsRequirement sourceParameter sourceUpper -> do
          resolved <- mapLeft GrammarV1CallableEffectGenericScopeError
            (grammarV1ResolveGenericParameter sourceParameter scope)
          let parameter = grammarV1ResolvedGenericParameter resolved
              key = genericStaticParameterKey parameter
              kind = genericStaticParameterKind parameter
          if kind /= GenericEffectsKind
            then Left (GrammarV1CallableEffectParameterKindMismatch key kind)
            else if Set.member key seen
              then Left (GrammarV1DuplicateCallableEffectParameterBound key)
              else case grammarV1EffectSet (locatedValue sourceUpper) of
                Nothing -> Left (GrammarV1CallableEffectUpperBoundUnsupported source)
                Just upper -> do
                  remaining <- go (Set.insert key seen) scope rest
                  Right
                    ( GrammarV1CheckedCallableEffectParameterBound
                        { checkedCallableEffectParameterBoundSource = source
                        , checkedCallableEffectParameterBoundParameter = resolved
                        , checkedCallableEffectParameterBoundCore =
                            EffectSetParameterBound key upper
                        }
                    : remaining
                    )
        _ -> go seen scope rest

-- | Substitute exact checked Effects actuals into callable effect-bound templates.
-- Concrete clauses remain unchanged. Parameter clauses receive exactly the actual
-- finite set admitted by Core bounded-subeffect checking. Stray/missing/duplicate
-- instantiations reject so latent effect identity cannot be silently invented.
grammarV1InstantiateCallableEffectBounds
  :: [CheckedEffectSetInstantiation]
  -> [GrammarV1CallableEffectBoundTemplate]
  -> Either GrammarV1CallableEffectInstantiationError [Set.Set SemanticEffect]
grammarV1InstantiateCallableEffectBounds instantiations templates = do
  bindings <- normalizeInstantiations instantiations
  (result, used) <- go bindings templates
  case
    [ key
    | key <- Map.keys bindings
    , not (Set.member key used)
    ] of
      extra : _ -> Left (GrammarV1UnexpectedCallableEffectInstantiation extra)
      [] -> Right result
  where
    go _ [] = Right ([], Set.empty)
    go bindings (template : rest) = do
      (remaining, used) <- go bindings rest
      case template of
        GrammarV1ConcreteCallableEffectBound effects ->
          Right (effects : remaining, used)
        GrammarV1CallableEffectsParameterBound key ->
          case Map.lookup key bindings of
            Nothing -> Left (GrammarV1MissingCallableEffectInstantiation key)
            Just checked -> Right
              ( checkedEffectSetActual checked : remaining
              , Set.insert key used
              )

normalizeInstantiations
  :: [CheckedEffectSetInstantiation]
  -> Either
      GrammarV1CallableEffectInstantiationError
      (Map.Map GenericStaticParameterKey CheckedEffectSetInstantiation)
normalizeInstantiations = go Map.empty
  where
    go result [] = Right result
    go result (checked : rest)
      | Map.member key result =
          Left (GrammarV1DuplicateCallableEffectInstantiation key)
      | otherwise = go (Map.insert key checked result) rest
      where
        key = checkedEffectSetParameterKey checked

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
