module Phil.Surface.GrammarV1.ComponentSurface
  ( GrammarV1CheckedComponentHeader (..)
  , grammarV1CheckedClosedComponentHeader
  ) where

import Data.Text (Text)
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static
  ( DeclarationKey
  , DefinitionRevision
  , StaticContext
  )
import Phil.Core.Syntax
  ( Name
  , Ty
  )
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.CallableSignature
  ( grammarV1InsertPrimitiveBinding
  )
import Phil.Surface.GrammarV1.CheckedType
  ( grammarV1CheckedType
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ComponentDecl (..)
  , GrammarV1TermParam (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Checked declaration-facing component header. Stable declaration/definition
-- identity is supplied by the lineage layer rather than derived from the source
-- display name. The optional parameter telescope preserves the source distinction
-- between an omitted term-parameter list and an explicitly empty `()` list.
-- `provides` remains an optional checked type only; comparison with an
-- architecture contract is owned by the later architecture/component checker.
data GrammarV1CheckedComponentHeader = GrammarV1CheckedComponentHeader
  { checkedComponentDeclarationKey :: DeclarationKey
  , checkedComponentDefinitionRevision :: DefinitionRevision
  , checkedComponentDisplayName :: Text
  , checkedComponentParameters :: Maybe [(Name, Ty)]
  , checkedComponentProvidesType :: Maybe Ty
  }
  deriving (Eq, Show)

-- | Route the bounded closed Grammar-v1 component header through existing
-- primitive binding and checked-type authority. Generic parameters and generic
-- requirements remain outside this slice. Present term parameters are inserted
-- in source order through the ordinary surface binding checker, so duplicates
-- and nonprimitive parameter types fail closed. A present `provides` type is
-- checked in that temporary parameter scope and preserves Core focusing failure
-- plus trace; absence remains semantically distinct from a checked type.
--
-- The component body is deliberately not inspected. Header success therefore
-- does not claim statement/resource/effect/session/body checking, architecture
-- contract satisfaction, occurrence creation, provider qualification, authority
-- possession, process activation, or realization.
grammarV1CheckedClosedComponentHeader
  :: StaticContext
  -> DeclarationKey
  -> DefinitionRevision
  -> GrammarV1ComponentDecl
  -> Maybe
      (Either
        FocusingError
        (GrammarV1CheckedComponentHeader, [FocusStep]))
grammarV1CheckedClosedComponentHeader
    staticContext declarationKey definitionRevision source
  | not (null (grammarV1ComponentGenericParams source)) = Nothing
  | not (null (grammarV1ComponentRequirements source)) = Nothing
  | otherwise = do
      (parameters, scopedState) <- componentParameterScope source
      case grammarV1ComponentProvides source of
        Nothing -> Just
          (Right
            ( buildHeader parameters Nothing
            , []
            ))
        Just providesType -> do
          checked <- grammarV1CheckedType
            staticContext
            scopedState
            (locatedValue providesType)
          pure $ fmap
            (\(ty, steps) ->
              ( buildHeader parameters (Just ty)
              , steps
              ))
            checked
  where
    buildHeader parameters providesType = GrammarV1CheckedComponentHeader
      { checkedComponentDeclarationKey = declarationKey
      , checkedComponentDefinitionRevision = definitionRevision
      , checkedComponentDisplayName = locatedValue (grammarV1ComponentName source)
      , checkedComponentParameters = parameters
      , checkedComponentProvidesType = providesType
      }

componentParameterScope
  :: GrammarV1ComponentDecl
  -> Maybe (Maybe [(Name, Ty)], SurfaceState)
componentParameterScope source = case grammarV1ComponentTermParams source of
  Nothing -> Just (Nothing, emptySurfaceState)
  Just parameters -> do
    (checked, state) <- elaborateParameters [] emptySurfaceState parameters
    Just (Just checked, state)

elaborateParameters
  :: [(Name, Ty)]
  -> SurfaceState
  -> [Located GrammarV1TermParam]
  -> Maybe ([(Name, Ty)], SurfaceState)
elaborateParameters reversed state remaining = case remaining of
  [] -> Just (reverse reversed, state)
  Located _ parameter : rest -> do
    ((name, ty), nextState) <- grammarV1InsertPrimitiveBinding
      (grammarV1TermParamName parameter)
      (grammarV1TermParamType parameter)
      state
    elaborateParameters ((name, ty) : reversed) nextState rest
