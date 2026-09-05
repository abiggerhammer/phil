module Phil.Surface.GrammarV1.SemanticCallableOutcomeState
  ( GrammarV1SemanticCallableOutcomeStateScope (..)
  , GrammarV1SemanticCallableOutcomeResidueScope (..)
  , GrammarV1SemanticCallableOutcomeStateError (..)
  , grammarV1SemanticCallableOutcomeScopes
  , grammarV1SemanticCallableOutcomeScopesAfterResult
  ) where

import Phil.Core.Static
  ( DeclarationKey
  , StaticContext
  )
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
  ( GrammarV1CheckedSemanticCallableSignature (..)
  , GrammarV1SemanticCallableScope (..)
  , GrammarV1SemanticCallableSignatureError
  , grammarV1CheckedSemanticCallableSignature
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
-- scope contains the active callable parameters plus the declaration-wide fresh
-- ordinal supplied by the caller. In independent clause mode that ordinal follows
-- the parameter telescope; in whole-callable composition it also reflects any
-- closed result-refinement binder. Each explicit state clause receives its own
-- child scope, while repeated state clauses remain repeated rather than merged.
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
  | GrammarV1SemanticCallableOutcomeSignatureError
      GrammarV1SemanticCallableSignatureError
  | GrammarV1SemanticCallableOutcomeBinderScopeError
      GrammarV1BinderScopeError
  | GrammarV1SemanticCallableOutcomeBindingInsertError
      SurfaceCheckError
  deriving (Eq, Show)

-- | Allocate exact semantic identities for every callable outcome-state slot in
-- source order from the parameter-only callable scope. This independent API is
-- intentionally retained for clause-local checking: result-type success or binder
-- allocation must not poison an otherwise independently meaningful outcome clause.
-- Whole-callable source-order composition uses
-- 'grammarV1SemanticCallableOutcomeScopesAfterResult' below instead.
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
    residues = outcomeResidues source

-- | Allocate outcome-state identities after the callable result type has been
-- semantically checked. A top-level result refinement may have consumed and then
-- closed a binder; the checked signature retains the resulting parent scope so the
-- first state slot cannot reuse that declaration-wide ordinal. The parameter
-- SurfaceState remains the base state because result-refinement bindings do not
-- escape their predicates.
grammarV1SemanticCallableOutcomeScopesAfterResult
  :: StaticContext
  -> DeclarationKey
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        GrammarV1SemanticCallableOutcomeStateError
        [GrammarV1SemanticCallableOutcomeResidueScope])
grammarV1SemanticCallableOutcomeScopesAfterResult
    staticContext declarationKey source = do
  checked <- grammarV1CheckedSemanticCallableSignature
    staticContext declarationKey source
  case checked of
    Left signatureError ->
      Just
        (Left
          (GrammarV1SemanticCallableOutcomeSignatureError signatureError))
    Right (signature, _focusSteps) ->
      buildResidues
        (checkedSemanticCallableLexicalScope signature)
        (checkedSemanticCallableState signature)
        (outcomeResidues source)

outcomeResidues
  :: GrammarV1CallableContractDecl
  -> [Located GrammarV1OutcomeResidue]
outcomeResidues source =
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
