module Phil.Surface.GrammarV1.CallableSignature
  ( GrammarV1CheckedFunctionHeader (..)
  , grammarV1InsertPrimitiveBinding
  , grammarV1CallableParameterScope
  , grammarV1CheckedCallableSignature
  , grammarV1CheckedClosedFunctionHeader
  ) where

import Data.Text (Text)
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual
  )
import Phil.Core.Static
  ( DeclarationKey
  , DefinitionRevision
  , StaticContext
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Ty
  )
import Phil.Surface.Check.Support
  ( emptySurfaceState
  , insertBindingMeta
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceShape (..)
  , SurfaceState
  )
import Phil.Surface.GrammarV1.CheckedType
  ( grammarV1CheckedType
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1BareStaticReferenceActual
  , grammarV1PrimitiveType
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableContractDecl (..)
  , GrammarV1FunctionDecl (..)
  , GrammarV1StaticArgument (..)
  , GrammarV1TermParam (..)
  , GrammarV1Type (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Insert one source binding whose type is already in the bounded primitive
-- unrestricted fragment shared by callable parameter and outcome-state scope.
-- The ordinary surface binding authority still owns duplicate-name rejection and
-- updates both binding metadata and the live Core resource context together.
grammarV1InsertPrimitiveBinding
  :: Located Text
  -> Located GrammarV1Type
  -> SurfaceState
  -> Maybe ((Name, Ty), SurfaceState)
grammarV1InsertPrimitiveBinding sourceName sourceType state = do
  ty <- grammarV1PrimitiveType (locatedValue sourceType)
  let bindingText = locatedValue sourceName
      bindingName = Name bindingText
  next <- either (const Nothing) Just $
    insertBindingMeta
      (locatedSpan sourceName)
      bindingText
      (BindingMeta Unrestricted ty PlainShape)
      state
  pure ((bindingName, ty), next)

-- | Construct the exact temporary lexical scope shared by checked callable
-- signature and clause projections. Generic parameters and requirements remain
-- outside this bounded fragment. Term parameters are admitted only when their
-- source types have the already-established primitive unrestricted meaning;
-- insertion in source order preserves duplicate-name rejection at the existing
-- binding authority. The returned state is a temporary semantic environment for
-- sibling callable elaboration only and is never installed in the caller.
grammarV1CallableParameterScope
  :: SurfaceState
  -> GrammarV1CallableContractDecl
  -> Maybe ([(Name, Ty)], SurfaceState)
grammarV1CallableParameterScope state source
  | not (null (grammarV1CallableGenericParams source)) = Nothing
  | not (null (grammarV1CallableRequirements source)) = Nothing
  | otherwise = elaborateParameters state (grammarV1CallableTermParams source)

-- | Route the first exact Grammar-v1 callable-signature fragment through the
-- checked type dispatcher. The parameter environment delegates only to
-- grammarV1CallableParameterScope, so later callable clause slices can share the
-- same lexical competence boundary rather than rebuilding it. The checked result
-- type may depend on earlier parameters. Structural source non-competence remains
-- Nothing; Core proposition/type rejection in the result remains a distinct Left,
-- with the exact focusing trace preserved. Callable clauses remain uninterpreted.
grammarV1CheckedCallableSignature
  :: StaticContext
  -> SurfaceState
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        FocusingError
        ((Text, [(Name, Ty)], Ty), [FocusStep]))
grammarV1CheckedCallableSignature staticContext state source = do
  (parameters, scopedState) <- grammarV1CallableParameterScope state source
  checkedResult <- grammarV1CheckedType
    staticContext
    scopedState
    (locatedValue (grammarV1CallableResultType source))
  pure $ fmap
    (\(resultType, steps) ->
      ( ( locatedValue (grammarV1CallableName source)
        , parameters
        , resultType
        )
      , steps
      ))
    checkedResult

-- | Checked declaration header for the first closed Grammar-v1 function
-- correspondence slice. Stable declaration/definition identity is supplied by
-- the lineage authority above source syntax; presentation spelling does not
-- derive it. The explicit recursive marker is preserved as source semantics but
-- no recursive-contract stabilization is claimed here.
--
-- The function body is deliberately absent. This type is a checked header, not a
-- checked implementation: body resource/effect/failure behavior, callable
-- implementation qualification, recursion admissibility, and runtime realization
-- remain outside this bridge.
data GrammarV1CheckedFunctionHeader = GrammarV1CheckedFunctionHeader
  { checkedFunctionDeclarationKey :: DeclarationKey
  , checkedFunctionDefinitionRevision :: DefinitionRevision
  , checkedFunctionRecursive :: Bool
  , checkedFunctionDisplayName :: Text
  , checkedFunctionParameters :: [(Name, Ty)]
  , checkedFunctionResultType :: Ty
  , checkedFunctionSatisfiesReference :: GenericStaticActual
  }
  deriving (Eq, Show)

-- | Route one closed Grammar-v1 function header through already-established
-- callable/type competence without assigning meaning to its body. Generic and
-- requirement-bearing functions remain outside this bounded fragment. Term
-- parameters reuse the primitive unrestricted binding path, preserving duplicate
-- rejection and lexical scope. An explicit result type is required and is checked
-- under that parameter scope, so focusing rejection and trace remain exact.
--
-- The `satisfies` type is preserved only as one bare/qualified unspecialized
-- unresolved static reference. This bridge does not assert that the reference
-- exists, denotes a callable contract, or is qualified for this implementation;
-- a competent callable/static resolver must establish those facts later.
-- Specialized/structured satisfaction types, omitted result types, and unsupported
-- parameter types fail closed instead of receiving inferred contracts or types.
grammarV1CheckedClosedFunctionHeader
  :: StaticContext
  -> DeclarationKey
  -> DefinitionRevision
  -> GrammarV1FunctionDecl
  -> Maybe
      (Either
        FocusingError
        (GrammarV1CheckedFunctionHeader, [FocusStep]))
grammarV1CheckedClosedFunctionHeader
    staticContext declarationKey definitionRevision source
  | not (null (grammarV1FunctionGenericParams source)) = Nothing
  | not (null (grammarV1FunctionRequirements source)) = Nothing
  | otherwise = do
      resultSource <- grammarV1FunctionResultType source
      (parameters, scopedState) <-
        elaborateParameters emptySurfaceState (grammarV1FunctionTermParams source)
      satisfiesReference <- unresolvedCallableReference
        (locatedValue (grammarV1FunctionSatisfies source))
      checkedResult <- grammarV1CheckedType
        staticContext
        scopedState
        (locatedValue resultSource)
      pure $ fmap
        (\(resultType, steps) ->
          ( GrammarV1CheckedFunctionHeader
              { checkedFunctionDeclarationKey = declarationKey
              , checkedFunctionDefinitionRevision = definitionRevision
              , checkedFunctionRecursive = grammarV1FunctionRecursive source
              , checkedFunctionDisplayName = locatedValue (grammarV1FunctionName source)
              , checkedFunctionParameters = parameters
              , checkedFunctionResultType = resultType
              , checkedFunctionSatisfiesReference = satisfiesReference
              }
          , steps
          ))
        checkedResult

unresolvedCallableReference :: GrammarV1Type -> Maybe GenericStaticActual
unresolvedCallableReference sourceType = case sourceType of
  GrammarV1NamedType reference ->
    grammarV1BareStaticReferenceActual
      (GrammarV1StaticReferenceArgument reference)
  _ -> Nothing

elaborateParameters
  :: SurfaceState
  -> [Located GrammarV1TermParam]
  -> Maybe ([(Name, Ty)], SurfaceState)
elaborateParameters = go []
  where
    go reversed state [] = Just (reverse reversed, state)
    go reversed state (Located _ parameter : rest) = do
      ((parameterName, ty), next) <- grammarV1InsertPrimitiveBinding
        (grammarV1TermParamName parameter)
        (grammarV1TermParamType parameter)
        state
      go ((parameterName, ty) : reversed) next rest
