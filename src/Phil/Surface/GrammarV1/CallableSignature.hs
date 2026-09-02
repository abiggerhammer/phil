module Phil.Surface.GrammarV1.CallableSignature
  ( grammarV1InsertPrimitiveBinding
  , grammarV1CallableParameterScope
  , grammarV1CheckedCallableSignature
  ) where

import Data.Text (Text)
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Ty
  )
import Phil.Surface.Check.Support (insertBindingMeta)
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceShape (..)
  , SurfaceState
  )
import Phil.Surface.GrammarV1.CheckedType
  ( grammarV1CheckedType
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1PrimitiveType
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1CallableContractDecl (..)
  , GrammarV1TermParam (..)
  , GrammarV1Type
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
