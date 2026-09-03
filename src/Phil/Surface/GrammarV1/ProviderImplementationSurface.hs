module Phil.Surface.GrammarV1.ProviderImplementationSurface
  ( GrammarV1CheckedOpaqueProviderImplementationSurface (..)
  , GrammarV1CheckedProviderImplementationItem (..)
  , GrammarV1CheckedProviderImplementationSurface (..)
  , GrammarV1ProviderImplementationSurfaceError (..)
  , grammarV1CheckedClosedOpaqueProviderImplementationSurface
  , grammarV1CheckedClosedProviderImplementationSurface
  ) where

import Data.Text (Text)
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual
  )
import Phil.Core.ProviderQualification
  ( ProviderOperationKey (..)
  )
import Phil.Core.Static
  ( DeclarationKey
  , DefinitionRevision
  , StaticContext
  )
import Phil.Core.Syntax
  ( Control
  , Proposition
  )
import Phil.Surface.Check.Engine
  ( checkSurfaceComponent
  )
import Phil.Surface.Check.Support
  ( emptySurfaceState
  )
import Phil.Surface.Check.Types
  ( SurfaceCheckError
  , SurfaceCheckResult (..)
  , emptySurfaceEnvironment
  )
import Phil.Surface.GrammarV1.CheckedProposition
  ( grammarV1CheckedProposition
  )
import Phil.Surface.GrammarV1.ClosedBodySurface
  ( grammarV1ClosedBody
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1BareStaticReferenceActual
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1OpaqueProviderImplementationDecl (..)
  , GrammarV1ProviderImplementationDecl (..)
  , GrammarV1ProviderImplementationItem (..)
  , GrammarV1StaticArgument (..)
  , GrammarV1Type (..)
  )
import Phil.Surface.Syntax
  ( Component (..)
  , Located (..)
  )

-- | Checked declaration surface for the closed opaque-provider implementation
-- fragment. Stable declaration identity and definition revision are supplied by
-- the lineage/revision authority above Grammar v1; neither is derived from the
-- source display name or location.
--
-- The implemented provider contract remains one unresolved static identity at
-- this seam. Only a bare/qualified unspecialized named type is admitted, using
-- the already-established static-reference carrier. This records what contract
-- the opaque implementation claims to satisfy without asserting that the target
-- exists, has provider kind, is at any particular interface revision, or has
-- actually been qualified.
--
-- This is intentionally not a Core 'ProviderImplementation'. Opaque provider
-- realizations require external/foreign qualification evidence and realization
-- facts; this source declaration cannot manufacture implementation entries,
-- callable semantics, authority confinement, evidence, symbols, or runtime
-- bindings. Generic parameters, generic requirements, specialized references,
-- and structured satisfaction types remain outside this bounded fragment.
data GrammarV1CheckedOpaqueProviderImplementationSurface =
  GrammarV1CheckedOpaqueProviderImplementationSurface
    { checkedOpaqueProviderDeclarationKey :: DeclarationKey
    , checkedOpaqueProviderDefinitionRevision :: DefinitionRevision
    , checkedOpaqueProviderContractReference :: GenericStaticActual
    }
  deriving (Eq, Show)

-- | One source-ordered checked item from a closed ordinary provider
-- implementation. Operation callable contracts stay unresolved and their bodies
-- carry only the exact terminal-control projection produced by the ordinary
-- production surface checker. Law and lifecycle propositions preserve the
-- ordinary focusing trace. This carrier does not claim provider qualification,
-- callable outcome correspondence, law discharge, or lifecycle satisfaction.
data GrammarV1CheckedProviderImplementationItem
  = GrammarV1CheckedProviderImplementationOperation
      ProviderOperationKey
      GenericStaticActual
      [Control]
  | GrammarV1CheckedProviderImplementationLaw
      Text
      Proposition
      [FocusStep]
  | GrammarV1CheckedProviderImplementationLifecycle
      Text
      Proposition
      [FocusStep]
  deriving (Eq, Show)

-- | Intermediate checked source surface for one closed ordinary provider
-- implementation. Stable declaration/definition identity comes from the lineage
-- authority. The provider contract remains an unresolved exact static reference,
-- and source item order is preserved so no list-to-map normalization or provider
-- qualification is silently performed at this layer.
data GrammarV1CheckedProviderImplementationSurface =
  GrammarV1CheckedProviderImplementationSurface
    { checkedProviderImplementationDeclarationKey :: DeclarationKey
    , checkedProviderImplementationDefinitionRevision :: DefinitionRevision
    , checkedProviderImplementationContractReference :: GenericStaticActual
    , checkedProviderImplementationItems
        :: [GrammarV1CheckedProviderImplementationItem]
    }
  deriving (Eq, Show)

data GrammarV1ProviderImplementationSurfaceError
  = GrammarV1ProviderImplementationFocusingError FocusingError
  | GrammarV1ProviderImplementationBodyError
      ProviderOperationKey
      SurfaceCheckError
  deriving (Eq, Show)

grammarV1CheckedClosedOpaqueProviderImplementationSurface
  :: DeclarationKey
  -> DefinitionRevision
  -> GrammarV1OpaqueProviderImplementationDecl
  -> Maybe GrammarV1CheckedOpaqueProviderImplementationSurface
grammarV1CheckedClosedOpaqueProviderImplementationSurface
    declarationKey definitionRevision source
  | not (null (grammarV1OpaqueProviderImplementationGenericParams source)) = Nothing
  | not (null (grammarV1OpaqueProviderImplementationRequirements source)) = Nothing
  | otherwise = do
      contractReference <- unresolvedProviderContractReference
        (grammarV1OpaqueProviderImplementationSatisfies source)
      pure GrammarV1CheckedOpaqueProviderImplementationSurface
        { checkedOpaqueProviderDeclarationKey = declarationKey
        , checkedOpaqueProviderDefinitionRevision = definitionRevision
        , checkedOpaqueProviderContractReference = contractReference
        }

-- | Route the closed ordinary provider-implementation fragment through existing
-- semantic authorities without constructing a Core ProviderImplementation.
--
-- Generic parameters and requirements remain outside this bounded slice. The
-- implementation's `satisfies` type and every operation `satisfies` type must be
-- bare/qualified unspecialized named references; exact dotted spelling is
-- preserved without resolving kind, existence, interface revision, or
-- qualification. Each operation body must inhabit the already-established shared
-- binder-free Bool/Unit statement fragment and is then executed through the
-- production `checkSurfaceComponent` path under an empty environment. The exact
-- resulting terminal controls are preserved but are deliberately not compared to
-- the unresolved callable contract here. Provider laws/lifecycle propositions are
-- checked through the ordinary top-level proposition/focusing path.
--
-- Source item order is exact. Duplicate operation/law/lifecycle names remain
-- visible rather than being silently overwritten by a Map; a later competent
-- provider qualification/construction layer owns uniqueness and correspondence.
-- Names/calls, integer literals, let-bindings, branching, protocol/resource
-- operations, closures, generic provider semantics, callable outcome matching,
-- provider preconditions/residues, law discharge, lifecycle satisfaction,
-- authority confinement, realization and SURF-009 binder scope are not inferred.
grammarV1CheckedClosedProviderImplementationSurface
  :: StaticContext
  -> DeclarationKey
  -> DefinitionRevision
  -> GrammarV1ProviderImplementationDecl
  -> Maybe
      (Either
        GrammarV1ProviderImplementationSurfaceError
        GrammarV1CheckedProviderImplementationSurface)
grammarV1CheckedClosedProviderImplementationSurface
    staticContext declarationKey definitionRevision source
  | not (null (grammarV1ProviderImplementationGenericParams source)) = Nothing
  | not (null (grammarV1ProviderImplementationRequirements source)) = Nothing
  | otherwise = do
      contractReference <- unresolvedProviderContractReference
        (grammarV1ProviderImplementationSatisfies source)
      go contractReference [] (grammarV1ProviderImplementationItems source)
  where
    go contractReference reversed remaining = case remaining of
      [] -> Just (Right GrammarV1CheckedProviderImplementationSurface
        { checkedProviderImplementationDeclarationKey = declarationKey
        , checkedProviderImplementationDefinitionRevision = definitionRevision
        , checkedProviderImplementationContractReference = contractReference
        , checkedProviderImplementationItems = reverse reversed
        })
      Located _ item : rest -> case item of
        GrammarV1ProviderImplementationOperation
            (Located _ operationName)
            (Located _ operationType)
            sourceBody -> do
          callableReference <- unresolvedCallableReference operationType
          body <- grammarV1ClosedBody sourceBody
          let operationKey = ProviderOperationKey operationName
              syntheticComponent = Located
                (locatedSpan sourceBody)
                (Component
                  { componentName = operationName
                  , componentParameters = []
                  , componentProvides = Nothing
                  , componentBody = body
                  })
          case checkSurfaceComponent
              (emptySurfaceEnvironment staticContext)
              syntheticComponent of
            Left err -> Just (Left
              (GrammarV1ProviderImplementationBodyError operationKey err))
            Right checked -> go
              contractReference
              ( GrammarV1CheckedProviderImplementationOperation
                  operationKey
                  callableReference
                  (checkedTerminalControls checked)
                : reversed
              )
              rest
        GrammarV1ProviderImplementationLaw
            (Located _ lawName)
            (Located _ proposition) -> do
          checked <- grammarV1CheckedProposition
            staticContext
            emptySurfaceState
            proposition
          case checked of
            Left err -> Just (Left
              (GrammarV1ProviderImplementationFocusingError err))
            Right (accepted, steps) -> go
              contractReference
              ( GrammarV1CheckedProviderImplementationLaw
                  lawName accepted steps
                : reversed
              )
              rest
        GrammarV1ProviderImplementationLifecycle
            (Located _ lifecycleName)
            (Located _ proposition) -> do
          checked <- grammarV1CheckedProposition
            staticContext
            emptySurfaceState
            proposition
          case checked of
            Left err -> Just (Left
              (GrammarV1ProviderImplementationFocusingError err))
            Right (accepted, steps) -> go
              contractReference
              ( GrammarV1CheckedProviderImplementationLifecycle
                  lifecycleName accepted steps
                : reversed
              )
              rest

unresolvedProviderContractReference
  :: Located GrammarV1Type
  -> Maybe GenericStaticActual
unresolvedProviderContractReference (Located _ sourceType) =
  unresolvedStaticTypeReference sourceType

unresolvedCallableReference :: GrammarV1Type -> Maybe GenericStaticActual
unresolvedCallableReference = unresolvedStaticTypeReference

unresolvedStaticTypeReference :: GrammarV1Type -> Maybe GenericStaticActual
unresolvedStaticTypeReference sourceType = case sourceType of
  GrammarV1NamedType reference ->
    grammarV1BareStaticReferenceActual
      (GrammarV1StaticReferenceArgument reference)
  _ -> Nothing
