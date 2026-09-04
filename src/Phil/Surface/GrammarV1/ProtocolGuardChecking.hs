module Phil.Surface.GrammarV1.ProtocolGuardChecking
  ( GrammarV1CheckedProtocolCoreGuard (..)
  , GrammarV1ProtocolGuardCheckingError (..)
  , grammarV1CheckedProtocolCoreGuards
  ) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static
  ( DeclarationKey
  , StaticContext
  )
import Phil.Core.Syntax (Proposition)
import Phil.Surface.Check.Support
  ( emptySurfaceState
  , messageMode
  , shapeForType
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceCheckError
  , SurfaceState
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKey
  , GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.CheckedProposition
  ( grammarV1CheckedProposition
  )
import Phil.Surface.GrammarV1.CheckedType
  ( grammarV1CheckedType
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..)
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ProtocolDecl
  , GrammarV1TermParam (..)
  , GrammarV1Type
  )
import Phil.Surface.GrammarV1.ProtocolBinderScope
  ( GrammarV1CheckedProtocolBinder (..)
  , GrammarV1CheckedProtocolBinderScope (..)
  , GrammarV1CheckedProtocolGuard (..)
  , GrammarV1CheckedProtocolRoleScope (..)
  , GrammarV1ProtocolBinderScopeError
  , grammarV1CheckedProtocolBinderScope
  )
import Phil.Surface.GrammarV1.SemanticBindingState
  ( grammarV1InsertSemanticBinding
  , grammarV1RewritePropositionReferences
  , grammarV1RewriteTypeReferences
  )
import Phil.Surface.Syntax (Located (..))

-- | One protocol guard after exact lexical references have been routed through
-- generated Core names and the ordinary Grammar-v1/Core proposition checker.
-- The retained SurfaceState is deliberately semantic-name keyed on this path;
-- source display spellings remain available through the original scope evidence.
data GrammarV1CheckedProtocolCoreGuard = GrammarV1CheckedProtocolCoreGuard
  { grammarV1CheckedProtocolCoreGuardSource :: GrammarV1CheckedProtocolGuard
  , grammarV1CheckedProtocolCoreGuardProposition :: Proposition
  , grammarV1CheckedProtocolCoreGuardFocusSteps :: [FocusStep]
  , grammarV1CheckedProtocolCoreGuardState :: SurfaceState
  , grammarV1CheckedProtocolCoreGuardBinders :: [GrammarV1ResolvedBinder]
  }
  deriving (Eq, Show)

data GrammarV1ProtocolGuardCheckingError
  = GrammarV1ProtocolGuardBinderScopeError GrammarV1ProtocolBinderScopeError
  | GrammarV1ProtocolGuardMissingBinder GrammarV1BinderKey
  | GrammarV1ProtocolGuardBinderDependencyCycle GrammarV1BinderKey
  | GrammarV1ProtocolGuardTypeRewriteNonCompetent (Located GrammarV1Type)
  | GrammarV1ProtocolGuardTypeCheckNonCompetent (Located GrammarV1Type)
  | GrammarV1ProtocolGuardTypeFocusingError FocusingError
  | GrammarV1ProtocolGuardBindingInsertError SurfaceCheckError
  | GrammarV1ProtocolGuardPropositionRewriteNonCompetent
      GrammarV1CheckedProtocolGuard
  | GrammarV1ProtocolGuardPropositionCheckNonCompetent
      GrammarV1CheckedProtocolGuard
  | GrammarV1ProtocolGuardPropositionFocusingError FocusingError
  deriving (Eq, Show)

-- | Close the SURF-009 protocol-guard handoff: first obtain exact lexical binder
-- evidence, then materialize only the transitive binder dependencies needed by
-- each guard under their generated Core names, and finally delegate proposition
-- semantics to grammarV1CheckedProposition. Source non-competence from the
-- binder/reference pass remains Nothing; once that pass succeeds, all later
-- failures retain their competent checker category explicitly.
grammarV1CheckedProtocolCoreGuards
  :: StaticContext
  -> DeclarationKey
  -> GrammarV1ProtocolDecl
  -> Maybe
      (Either
        GrammarV1ProtocolGuardCheckingError
        [GrammarV1CheckedProtocolCoreGuard])
grammarV1CheckedProtocolCoreGuards staticContext declarationKey protocol = do
  scopeResult <- grammarV1CheckedProtocolBinderScope declarationKey protocol
  pure $ do
    checkedScope <- mapLeft GrammarV1ProtocolGuardBinderScopeError scopeResult
    concat <$> mapM
      (checkRole staticContext)
      (grammarV1CheckedProtocolRoles checkedScope)

checkRole
  :: StaticContext
  -> GrammarV1CheckedProtocolRoleScope
  -> Either
      GrammarV1ProtocolGuardCheckingError
      [GrammarV1CheckedProtocolCoreGuard]
checkRole staticContext role =
  mapM
    (checkGuard staticContext binderTable)
    (grammarV1CheckedProtocolRoleGuards role)
  where
    binderTable = Map.fromList
      [ (grammarV1ResolvedBinderKey resolved, binder)
      | binder <- grammarV1CheckedProtocolRoleBinders role
      , let resolved = grammarV1CheckedProtocolBinderResolved binder
      ]

checkGuard
  :: StaticContext
  -> Map.Map GrammarV1BinderKey GrammarV1CheckedProtocolBinder
  -> GrammarV1CheckedProtocolGuard
  -> Either
      GrammarV1ProtocolGuardCheckingError
      GrammarV1CheckedProtocolCoreGuard
checkGuard staticContext binderTable checkedGuard = do
  built <- foldM
    (materializeReference staticContext binderTable)
    emptyBuildState
    (grammarV1CheckedProtocolGuardReferences checkedGuard)
  rewritten <- maybe
    (Left (GrammarV1ProtocolGuardPropositionRewriteNonCompetent checkedGuard))
    Right
    ( grammarV1RewritePropositionReferences
        (grammarV1CheckedProtocolGuardReferences checkedGuard)
        (grammarV1CheckedProtocolGuardSource checkedGuard)
    )
  checked <- maybe
    (Left (GrammarV1ProtocolGuardPropositionCheckNonCompetent checkedGuard))
    Right
    ( grammarV1CheckedProposition
        staticContext
        (guardBuildSurfaceState built)
        (locatedValue rewritten)
    )
  (proposition, focusSteps) <- mapLeft
    GrammarV1ProtocolGuardPropositionFocusingError
    checked
  Right GrammarV1CheckedProtocolCoreGuard
    { grammarV1CheckedProtocolCoreGuardSource = checkedGuard
    , grammarV1CheckedProtocolCoreGuardProposition = proposition
    , grammarV1CheckedProtocolCoreGuardFocusSteps = focusSteps
    , grammarV1CheckedProtocolCoreGuardState = guardBuildSurfaceState built
    , grammarV1CheckedProtocolCoreGuardBinders = guardBuildOrder built
    }

data GuardBuildState = GuardBuildState
  { guardBuildSurfaceState :: SurfaceState
  , guardBuildInserted :: Set.Set GrammarV1BinderKey
  , guardBuildVisiting :: Set.Set GrammarV1BinderKey
  , guardBuildOrder :: [GrammarV1ResolvedBinder]
  }

emptyBuildState :: GuardBuildState
emptyBuildState = GuardBuildState
  { guardBuildSurfaceState = emptySurfaceState
  , guardBuildInserted = Set.empty
  , guardBuildVisiting = Set.empty
  , guardBuildOrder = []
  }

materializeReference
  :: StaticContext
  -> Map.Map GrammarV1BinderKey GrammarV1CheckedProtocolBinder
  -> GuardBuildState
  -> GrammarV1CheckedLexicalReference
  -> Either GrammarV1ProtocolGuardCheckingError GuardBuildState
materializeReference staticContext binderTable state reference =
  materializeBinder
    staticContext
    binderTable
    state
    (grammarV1CheckedLexicalReferenceBinder reference)

materializeBinder
  :: StaticContext
  -> Map.Map GrammarV1BinderKey GrammarV1CheckedProtocolBinder
  -> GuardBuildState
  -> GrammarV1ResolvedBinder
  -> Either GrammarV1ProtocolGuardCheckingError GuardBuildState
materializeBinder staticContext binderTable state resolved
  | Set.member key (guardBuildInserted state) = Right state
  | Set.member key (guardBuildVisiting state) =
      Left (GrammarV1ProtocolGuardBinderDependencyCycle key)
  | otherwise = do
      checkedBinder <- maybe
        (Left (GrammarV1ProtocolGuardMissingBinder key))
        Right
        (Map.lookup key binderTable)
      let visitingState = state
            { guardBuildVisiting = Set.insert key (guardBuildVisiting state)
            }
      withDependencies <- foldM
        (materializeReference staticContext binderTable)
        visitingState
        (grammarV1CheckedProtocolBinderTypeReferences checkedBinder)
      let sourceType = grammarV1TermParamType
            (locatedValue (grammarV1CheckedProtocolBinderSource checkedBinder))
      rewrittenType <- maybe
        (Left (GrammarV1ProtocolGuardTypeRewriteNonCompetent sourceType))
        Right
        ( grammarV1RewriteTypeReferences
            (grammarV1CheckedProtocolBinderTypeReferences checkedBinder)
            sourceType
        )
      checkedType <- maybe
        (Left (GrammarV1ProtocolGuardTypeCheckNonCompetent rewrittenType))
        Right
        ( grammarV1CheckedType
            staticContext
            (guardBuildSurfaceState withDependencies)
            (locatedValue rewrittenType)
        )
      (ty, _) <- mapLeft GrammarV1ProtocolGuardTypeFocusingError checkedType
      nextSurface <- mapLeft GrammarV1ProtocolGuardBindingInsertError $
        grammarV1InsertSemanticBinding
          resolved
          (BindingMeta (messageMode ty) ty (shapeForType ty))
          (guardBuildSurfaceState withDependencies)
      Right withDependencies
        { guardBuildSurfaceState = nextSurface
        , guardBuildInserted = Set.insert key (guardBuildInserted withDependencies)
        , guardBuildVisiting = Set.delete key (guardBuildVisiting withDependencies)
        , guardBuildOrder = guardBuildOrder withDependencies <> [resolved]
        }
  where
    key = grammarV1ResolvedBinderKey resolved

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
