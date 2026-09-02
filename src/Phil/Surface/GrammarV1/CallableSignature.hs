module Phil.Surface.GrammarV1.CallableSignature
  ( grammarV1CheckedCallableSignature
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
  )
import Phil.Surface.Syntax (Located (..))

-- | Route the first exact Grammar-v1 callable-signature fragment through the
-- checked type dispatcher. Generic parameters and requirements remain outside
-- this bounded bridge. Term parameters are admitted only when their source type
-- has intrinsic primitive meaning (Unit, Bool, or U<n>), whose unrestricted
-- binding mode is already established. Parameters enter one temporary lexical
-- scope in source order, so duplicate names fail at the existing binding
-- authority and the checked result type may depend on earlier parameters.
-- Callable clauses are deliberately not interpreted here: this function projects
-- only the checked signature that later clause slices can reuse. Structural
-- source non-competence remains Nothing; Core proposition/type rejection in the
-- result remains a distinct Left, with the exact focusing trace preserved.
grammarV1CheckedCallableSignature
  :: StaticContext
  -> SurfaceState
  -> GrammarV1CallableContractDecl
  -> Maybe
      (Either
        FocusingError
        ((Text, [(Name, Ty)], Ty), [FocusStep]))
grammarV1CheckedCallableSignature staticContext state source
  | not (null (grammarV1CallableGenericParams source)) = Nothing
  | not (null (grammarV1CallableRequirements source)) = Nothing
  | otherwise = do
      (parameters, scopedState) <-
        elaborateParameters state (grammarV1CallableTermParams source)
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
      ty <- grammarV1PrimitiveType
        (locatedValue (grammarV1TermParamType parameter))
      let parameterText = locatedValue (grammarV1TermParamName parameter)
          parameterName = Name parameterText
      next <- either (const Nothing) Just $
        insertBindingMeta
          (locatedSpan (grammarV1TermParamName parameter))
          parameterText
          (BindingMeta Unrestricted ty PlainShape)
          state
      go ((parameterName, ty) : reversed) next rest
