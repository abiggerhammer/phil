module Phil.Surface.GrammarV1.SemanticCallableOutcomeState
  ( GrammarV1SemanticCallableOutcomeStateScope (..)
  , GrammarV1SemanticCallableOutcomeResidueScope (..)
  , GrammarV1SemanticCallableOutcomeStateError (..)
  , grammarV1SemanticCallableOutcomeScopes
  ) where

import Phil.Core.Static (DeclarationKey)
import Phil.Core.Syntax
  ( Mode (..)
  , Ty
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceCheckError
  , SurfaceShape (..)
  , SurfaceState
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (..)
  , GrammarV1BinderScopeError
  , GrammarV1LexicalScope
  , GrammarV1ResolvedBinder
  , grammarV1BindLocal
  , grammarV1EnterLexicalScope
  , grammarV1LeaveLexicalScope
  )
import Phil.Surface.GrammarV1.Elaborate (grammarV1PrimitiveType)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableClause (..)
  , GrammarV1CallableContractDecl (..)
  , GrammarV1OutcomeKind
  , GrammarV1OutcomeResidue (..)
  , GrammarV1OutcomeResidueClause (..)
  , GrammarV1StateSlot (..)
  )
import Phil.Surface.GrammarV1.SemanticBindingState
  ( grammarV1InsertSemanticBinding
  )
import Phil.Surface.GrammarV1.SemanticCallableSignature
  ( GrammarV1SemanticCallableScope (..)
  , GrammarV1SemanticCallableSignatureError
  , grammarV1SemanticCallableParameterScope
  )
import Phil.Surface.Syntax (Located (..))

-- | One explicit outcome-state telescope in its exact child lexical scope. The
-- SurfaceState always starts from the callable parameter state; sibling residue
-- state never leaks across branches. Binder ordinals, however, advance globally
-- across sibling scopes through the parent lexical scope.
data GrammarV1SemanticCallableOutcomeStateScope =
  GrammarV1SemanticCallableOutcomeStateScope
    { semanticCallableOutcomeStateBindings :: [(GrammarV1ResolvedBinder, Ty)]
    , semanticCallableOutcomeStateLexicalScope :: GrammarV1LexicalScope
    , semanticCallableOutcomeStateSurfaceState :: SurfaceState
    }
  deriving (Eq, Show)

-- | Semantic scope information for one source outcome residue. The base lexical
-- scope contains only the callable parameters (plus the advanced fresh ordinal),
-- while each explicit state clause receives its own child scope. Repeated state
-- clauses remain repeated rather than being merged or assigned an invented
-- cardinality rule.
data GrammarV1SemanticCallableOutcomeResidueScope =
  GrammarV1SemanticCallableOutcomeResidueScope
    { semanticCallableOutcomeResidueSource :: Located GrammarV1OutcomeResidue
    , semanticCallableOutcomeResidueKind :: GrammarV1OutcomeKind
    , semanticCallableOutcomeResidueBaseLexicalScope :: GrammarV1LexicalScope
    , semanticCallableOutcomeResidueBaseState :: SurfaceState
    , semanticCallableOutcomeResidueStateScopes ::
        [GrammarV1SemanticCallableOutcomeStateScope]
    }
  deriving (Eq, Show)

data GrammarV1SemanticCallableOutcomeStateError
  = GrammarV1SemanticCallableOutcomeParameterScopeError
      GrammarV1SemanticCallableSignatureError
  | GrammarV1SemanticCallableOutcomeBinderScopeError
      GrammarV1BinderScopeError
  | GrammarV1SemanticCallableOutcomeBindingInsertError
      SurfaceCheckError
  deriving (Eq, Show)

-- | Allocate exact semantic identities for every callable outcome-state slot in
-- source order. Generic/requirement-bearing callables and nonprimitive state-slot
-- types remain outside this bounded route. Each state clause is a fresh sibling
-- lexical region, but the returned parent scope carries the advanced ordinal into
-- later state clauses and later residues so two distinct slots can never receive
-- one BinderKey/Core name merely because their branch scopes are disjoint.
grammarV1SemanticCallableOutcomeScopes
  :: DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        GrammarV1SemanticCallableOutcomeStateError
        [GrammarV1SemanticCallableOutcomeResidueScope])
grammarV1SemanticCallableOutcomeScopes declarationKey source = do
  scoped <- grammarV1SemanticCallableParameterScope declarationKey source
  case scoped of
    Left scopeError ->
      Just
        (Left
          (GrammarV1SemanticCallableOutcomeParameterScopeError scopeError))
    Right callableScope ->
      buildResidues
        (semanticCallableScopeLexicalScope callableScope)
        (semanticCallableScopeState callableScope)
        residues
  where
    residues =
      [ residue
      | Located _ (GrammarV1CallableOutcomeResidue residue) <-
          grammarV1CallableClauses source
      ]

buildResidues
  :: GrammarV1LexicalScope
  -> SurfaceState
  -> [Located GrammarV1OutcomeResidue]
  -> Maybe
      (Either
        GrammarV1SemanticCallableOutcomeStateError
        [GrammarV1SemanticCallableOutcomeResidueScope])
buildResidues = go []
  where
    go reversed _ _ [] = Just (Right (reverse reversed))
    go reversed parentScope parameterState (residueSource@(Located _ residue) : rest) = do
      built <- buildStateScopes
        parentScope
        parameterState
        stateClauses
      case built of
        Left err -> Just (Left err)
        Right (stateScopes, nextParentScope) ->
          go
            ( GrammarV1SemanticCallableOutcomeResidueScope
                { semanticCallableOutcomeResidueSource = residueSource
                , semanticCallableOutcomeResidueKind =
                    locatedValue (grammarV1OutcomeResidueKind residue)
                , semanticCallableOutcomeResidueBaseLexicalScope = parentScope
                , semanticCallableOutcomeResidueBaseState = parameterState
                , semanticCallableOutcomeResidueStateScopes = stateScopes
                }
              : reversed
            )
            nextParentScope
            parameterState
            rest
      where
        stateClauses =
          [ slots
          | Located _ (GrammarV1OutcomeState slots) <-
              grammarV1OutcomeResidueClauses residue
          ]

buildStateScopes
  :: GrammarV1LexicalScope
  -> SurfaceState
  -> [[Located GrammarV1StateSlot]]
  -> Maybe
      (Either
        GrammarV1SemanticCallableOutcomeStateError
        ( [GrammarV1SemanticCallableOutcomeStateScope]
        , GrammarV1LexicalScope
        ))
buildStateScopes = go []
  where
    go reversed parentScope _ [] =
      Just (Right (reverse reversed, parentScope))
    go reversed parentScope parameterState (slots : rest) = do
      built <- buildOneStateScope parentScope parameterState slots
      case built of
        Left err -> Just (Left err)
        Right (stateScope, nextParentScope) ->
          go (stateScope : reversed) nextParentScope parameterState rest

buildOneStateScope
  :: GrammarV1LexicalScope
  -> SurfaceState
  -> [Located GrammarV1StateSlot]
  -> Maybe
      (Either
        GrammarV1SemanticCallableOutcomeStateError
        ( GrammarV1SemanticCallableOutcomeStateScope
        , GrammarV1LexicalScope
        ))
buildOneStateScope parentScope parameterState slots = do
  built <- buildBindings
    []
    (grammarV1EnterLexicalScope parentScope)
    parameterState
    slots
  pure $ do
    (bindings, childScope, state) <- built
    nextParentScope <- mapLeft
      GrammarV1SemanticCallableOutcomeBinderScopeError
      (grammarV1LeaveLexicalScope childScope)
    Right
      ( GrammarV1SemanticCallableOutcomeStateScope
          { semanticCallableOutcomeStateBindings = bindings
          , semanticCallableOutcomeStateLexicalScope = childScope
          , semanticCallableOutcomeStateSurfaceState = state
          }
      , nextParentScope
      )

buildBindings
  :: [(GrammarV1ResolvedBinder, Ty)]
  -> GrammarV1LexicalScope
  -> SurfaceState
  -> [Located GrammarV1StateSlot]
  -> Maybe
      (Either
        GrammarV1SemanticCallableOutcomeStateError
        ( [(GrammarV1ResolvedBinder, Ty)]
        , GrammarV1LexicalScope
        , SurfaceState
        ))
buildBindings reversed scope state [] =
  Just (Right (reverse reversed, scope, state))
buildBindings reversed scope state (Located _ slot : rest) = do
  ty <- grammarV1PrimitiveType (locatedValue (grammarV1StateSlotType slot))
  case grammarV1BindLocal
      GrammarV1CallableOutcomeStateBinder
      (grammarV1StateSlotName slot)
      scope of
    Left scopeError ->
      Just
        (Left
          (GrammarV1SemanticCallableOutcomeBinderScopeError scopeError))
    Right (binder, nextScope) ->
      case grammarV1InsertSemanticBinding
          binder
          (BindingMeta Unrestricted ty PlainShape)
          state of
        Left insertError ->
          Just
            (Left
              (GrammarV1SemanticCallableOutcomeBindingInsertError insertError))
        Right nextState ->
          buildBindings
            ((binder, ty) : reversed)
            nextScope
            nextState
            rest

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
