module Phil.Surface.GrammarV1.ClaimDeclaration
  ( grammarV1ClaimDeclaration
  ) where

import Data.Text (Text)
import Phil.Core.SortCheck (refSortOfTy)
import Phil.Core.Static
  ( ClaimDecl (..)
  , ClaimDefinition (..)
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , RefSort
  )
import Phil.Surface.Check.Support
  ( emptySurfaceState
  , insertBindingMeta
  , syntheticSpan
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceShape (..)
  , SurfaceState
  )
import Phil.Surface.GrammarV1.BoundProposition
  ( grammarV1BoundProposition
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1PrimitiveType
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ClaimDecl (..)
  , GrammarV1TermParam (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Route the first exact Grammar-v1 claim-declaration fragment into Core's
-- established ClaimDecl carrier. Generic parameters and requirements remain
-- outside this bounded bridge. Claim term parameters are accepted only when
-- their source type has intrinsic primitive meaning and an exact RefSort;
-- today that means Bool and U<n>. Those parameter types are already known to be
-- unrestricted, so temporary lexical bindings used by the transparent body do
-- not guess resource discipline. Unit has no refinement sort and richer types
-- remain closed until their full type/mode meaning can be preserved rather than
-- erased to a bare sort. Opaque claims carry no body; transparent claims reuse
-- the verified binding-aware proposition bridge with only their own parameters
-- in scope, so top-level claims cannot accidentally capture ambient term state.
grammarV1ClaimDeclaration
  :: GrammarV1ClaimDecl
  -> Maybe (Text, ClaimDecl)
grammarV1ClaimDeclaration source
  | not (null (grammarV1ClaimGenericParams source)) = Nothing
  | not (null (grammarV1ClaimRequirements source)) = Nothing
  | otherwise = do
      (parameters, state) <- elaborateParameters termParameters
      definition <- case grammarV1ClaimProposition source of
        Nothing -> Just OpaqueClaim
        Just (Located _ proposition) ->
          TransparentClaim <$> grammarV1BoundProposition state proposition
      pure
        ( locatedValue (grammarV1ClaimName source)
        , ClaimDecl
            { claimParameters = parameters
            , claimDefinition = definition
            }
        )
  where
    termParameters = maybe [] id (grammarV1ClaimTermParams source)

elaborateParameters
  :: [Located GrammarV1TermParam]
  -> Maybe ([(Name, RefSort)], SurfaceState)
elaborateParameters = go [] emptySurfaceState
  where
    go parameters state [] = Just (reverse parameters, state)
    go parameters state (Located _ parameter : rest) = do
      ty <- grammarV1PrimitiveType
        (locatedValue (grammarV1TermParamType parameter))
      sort <- refSortOfTy ty
      let parameterText = locatedValue (grammarV1TermParamName parameter)
          parameterName = Name parameterText
      state' <- either (const Nothing) Just $
        insertBindingMeta
          syntheticSpan
          parameterText
          (BindingMeta Unrestricted ty PlainShape)
          state
      go ((parameterName, sort) : parameters) state' rest
