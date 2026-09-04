{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.GenericBinderScope
  ( GrammarV1ResolvedGenericParameter (..)
  , GrammarV1GenericBinderScope
  , GrammarV1GenericBinderScopeError (..)
  , grammarV1RootGenericBinderScope
  , grammarV1BindGenericParameter
  , grammarV1BindGenericParameters
  , grammarV1ResolveGenericParameter
  , grammarV1FunctionGenericParameterScope
  , grammarV1CallableGenericParameterScope
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Generic (GenericStaticParameterKey (..))
import Phil.Core.Generic.StaticActual
  ( GenericStaticParameter (..)
  )
import Phil.Core.Static (DeclarationKey (..))
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1GenericKindCategory
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableContractDecl (..)
  , GrammarV1FunctionDecl (..)
  , GrammarV1GenericParam (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Exact source/Core correspondence for one static generic binder. The Located
-- source occurrence is retained for diagnostics and downstream SURF-008 bridges;
-- semantic identity is the declaration-rooted GenericStaticParameterKey below.
data GrammarV1ResolvedGenericParameter = GrammarV1ResolvedGenericParameter
  { grammarV1ResolvedGenericSource :: Located GrammarV1GenericParam
  , grammarV1ResolvedGenericParameter :: GenericStaticParameter
  }
  deriving (Eq, Show)

-- | Phase 1 generic parameters form one declaration-header telescope. This scope
-- deliberately owns only static binder identity/resolution; term-local lexical
-- composition is a later SURF-009 slice so the two semantic namespaces cannot be
-- accidentally collapsed by implementation convenience.
data GrammarV1GenericBinderScope = GrammarV1GenericBinderScope
  { grammarV1GenericScopeRootDeclaration :: DeclarationKey
  , grammarV1GenericScopeBindings :: Map Text GrammarV1ResolvedGenericParameter
  , grammarV1GenericScopeNextOrdinal :: Int
  }
  deriving (Eq, Show)

data GrammarV1GenericBinderScopeError
  = GrammarV1DuplicateGenericBinder
      (Located Text)
      GrammarV1ResolvedGenericParameter
  | GrammarV1GenericBinderNotInScope (Located Text)
  deriving (Eq, Show)

-- | Begin static-binder resolution for one exact identity-bearing declaration.
grammarV1RootGenericBinderScope :: DeclarationKey -> GrammarV1GenericBinderScope
grammarV1RootGenericBinderScope declarationKey = GrammarV1GenericBinderScope
  { grammarV1GenericScopeRootDeclaration = declarationKey
  , grammarV1GenericScopeBindings = Map.empty
  , grammarV1GenericScopeNextOrdinal = 0
  }

-- | Allocate one generic-static semantic identity in declaration-telescope order.
-- Display spelling and source span do not participate in the key. The declared
-- static kind is interpreted only by the already-existing Grammar-v1 kind bridge;
-- this scope authority does not reimplement generic kind semantics.
grammarV1BindGenericParameter
  :: Located GrammarV1GenericParam
  -> GrammarV1GenericBinderScope
  -> Either
      GrammarV1GenericBinderScopeError
      (GrammarV1ResolvedGenericParameter, GrammarV1GenericBinderScope)
grammarV1BindGenericParameter source@(Located _ parameter) scope =
  case Map.lookup displayName (grammarV1GenericScopeBindings scope) of
    Just previous -> Left
      (GrammarV1DuplicateGenericBinder (grammarV1GenericParamName parameter) previous)
    Nothing ->
      let ordinal = grammarV1GenericScopeNextOrdinal scope
          semanticParameter = GenericStaticParameter
            { genericStaticParameterKey = genericParameterKey
                (grammarV1GenericScopeRootDeclaration scope)
                ordinal
            , genericStaticParameterKind = grammarV1GenericKindCategory
                (locatedValue (grammarV1GenericParamKind parameter))
            }
          resolved = GrammarV1ResolvedGenericParameter
            { grammarV1ResolvedGenericSource = source
            , grammarV1ResolvedGenericParameter = semanticParameter
            }
      in Right
        ( resolved
        , scope
            { grammarV1GenericScopeBindings = Map.insert
                displayName
                resolved
                (grammarV1GenericScopeBindings scope)
            , grammarV1GenericScopeNextOrdinal = ordinal + 1
            }
        )
  where
    displayName = locatedValue (grammarV1GenericParamName parameter)

-- | Allocate one complete generic parameter telescope from left to right.
grammarV1BindGenericParameters
  :: [Located GrammarV1GenericParam]
  -> GrammarV1GenericBinderScope
  -> Either
      GrammarV1GenericBinderScopeError
      ([GrammarV1ResolvedGenericParameter], GrammarV1GenericBinderScope)
grammarV1BindGenericParameters = go []
  where
    go reversed [] scope = Right (reverse reversed, scope)
    go reversed (parameter : rest) scope = do
      (resolved, nextScope) <- grammarV1BindGenericParameter parameter scope
      go (resolved : reversed) rest nextScope

-- | Resolve a source spelling to the exact static parameter occurrence. Source
-- spelling locates; GenericStaticParameterKey identifies.
grammarV1ResolveGenericParameter
  :: Located Text
  -> GrammarV1GenericBinderScope
  -> Either GrammarV1GenericBinderScopeError GrammarV1ResolvedGenericParameter
grammarV1ResolveGenericParameter sourceName scope =
  case Map.lookup (locatedValue sourceName) (grammarV1GenericScopeBindings scope) of
    Just resolved -> Right resolved
    Nothing -> Left (GrammarV1GenericBinderNotInScope sourceName)

-- | Establish the static parameter telescope for one named function.
grammarV1FunctionGenericParameterScope
  :: DeclarationKey
  -> GrammarV1FunctionDecl
  -> Either
      GrammarV1GenericBinderScopeError
      ([GrammarV1ResolvedGenericParameter], GrammarV1GenericBinderScope)
grammarV1FunctionGenericParameterScope declarationKey functionDecl =
  grammarV1BindGenericParameters
    (grammarV1FunctionGenericParams functionDecl)
    (grammarV1RootGenericBinderScope declarationKey)

-- | Establish the static parameter telescope for one callable contract.
grammarV1CallableGenericParameterScope
  :: DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Either
      GrammarV1GenericBinderScopeError
      ([GrammarV1ResolvedGenericParameter], GrammarV1GenericBinderScope)
grammarV1CallableGenericParameterScope declarationKey callableDecl =
  grammarV1BindGenericParameters
    (grammarV1CallableGenericParams callableDecl)
    (grammarV1RootGenericBinderScope declarationKey)

genericParameterKey :: DeclarationKey -> Int -> GenericStaticParameterKey
genericParameterKey (DeclarationKey rootText) ordinal =
  GenericStaticParameterKey
    ( "$phil.static:"
      <> Text.pack (show (Text.length rootText))
      <> ":"
      <> rootText
      <> ":"
      <> Text.pack (show ordinal)
    )
