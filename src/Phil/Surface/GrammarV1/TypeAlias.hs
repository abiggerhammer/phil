module Phil.Surface.GrammarV1.TypeAlias
  ( grammarV1CheckedTypeAlias
  , grammarV1CheckedTypeAliasMode
  , grammarV1CheckedTypeAliasModeWithNamedResolutions
  ) where

import Data.Text (Text)
import Phil.Core.CheckedBindingMode
  ( CheckedTypeMode
  )
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax (Ty)
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.CheckedType
  ( GrammarV1CheckedResolvedTypeMode
  , GrammarV1CheckedTypeModeResolutionError
  , GrammarV1ResolvedNamedTypeMode
  , grammarV1CheckedType
  , grammarV1CheckedTypeMode
  , grammarV1CheckedTypeModeWithNamedResolutions
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1TypeAliasDecl (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Route the first complete Grammar-v1 type-alias declaration fragment through
-- the uniform checked type dispatcher. This bounded bridge is intentionally
-- closed: aliases with generic parameters or requirements remain outside current
-- declaration competence, and the target is checked under an empty term scope so
-- a top-level alias cannot accidentally inherit caller-local bindings. Refinement
-- binders still establish their own lexical scope inside grammarV1CheckedType.
-- Core focusing rejection remains a distinct Left, while structurally unsupported
-- target types remain Nothing. No alias expansion, recursive alias environment,
-- generic instantiation, or fallback interpretation is invented here.
grammarV1CheckedTypeAlias
  :: StaticContext
  -> GrammarV1TypeAliasDecl
  -> Maybe (Either FocusingError ((Text, Ty), [FocusStep]))
grammarV1CheckedTypeAlias staticContext source
  | not (null (grammarV1TypeAliasGenericParams source)) = Nothing
  | not (null (grammarV1TypeAliasRequirements source)) = Nothing
  | otherwise = do
      checked <- grammarV1CheckedType
        staticContext
        emptySurfaceState
        (locatedValue (grammarV1TypeAliasTarget source))
      pure $ fmap
        (\(ty, steps) ->
          ( (locatedValue (grammarV1TypeAliasName source), ty)
          , steps
          ))
        checked

-- | Give the same closed transparent alias fragment its structural mode by
-- delegating to the checked target-type mode authority established by SURF-008.
-- A transparent alias has no independent structural classification: its display
-- name cannot strengthen, weaken, or otherwise reclassify the target. The exact
-- CheckedTypeMode and focusing trace are therefore inherited from the target.
--
-- As with grammarV1CheckedTypeAlias, generic/requirement-bearing aliases and
-- top-level free term dependencies remain outside competence. Targets whose mode
-- requires a declaration/resource lookup (for example opaque named, Frame, or
-- Validated types) remain Nothing rather than receiving a default mode.
grammarV1CheckedTypeAliasMode
  :: StaticContext
  -> GrammarV1TypeAliasDecl
  -> Maybe (Either FocusingError ((Text, CheckedTypeMode), [FocusStep]))
grammarV1CheckedTypeAliasMode staticContext source
  | not (null (grammarV1TypeAliasGenericParams source)) = Nothing
  | not (null (grammarV1TypeAliasRequirements source)) = Nothing
  | otherwise = do
      checked <- grammarV1CheckedTypeMode
        staticContext
        emptySurfaceState
        (locatedValue (grammarV1TypeAliasTarget source))
      pure $ fmap
        (\(checkedMode, steps) ->
          ( (locatedValue (grammarV1TypeAliasName source), checkedMode)
          , steps
          ))
        checked

-- | Extend transparent alias mode inheritance through the exact named-type
-- resolution seam established by #616. Intrinsic targets behave exactly as in
-- 'grammarV1CheckedTypeAliasMode'; a bare named target may additionally consume
-- exact declaration/static resolution evidence, and the resulting stable
-- declaration/interface provenance stays attached to the inherited mode.
--
-- Alias spelling still has no authority to reclassify its target. Generic or
-- requirement-bearing aliases remain outside this closed declaration fragment,
-- and specialized named targets remain outside generic-instantiation competence.
grammarV1CheckedTypeAliasModeWithNamedResolutions
  :: StaticContext
  -> [GrammarV1ResolvedNamedTypeMode]
  -> GrammarV1TypeAliasDecl
  -> Maybe
      (Either
        GrammarV1CheckedTypeModeResolutionError
        ((Text, GrammarV1CheckedResolvedTypeMode), [FocusStep]))
grammarV1CheckedTypeAliasModeWithNamedResolutions staticContext resolutions source
  | not (null (grammarV1TypeAliasGenericParams source)) = Nothing
  | not (null (grammarV1TypeAliasRequirements source)) = Nothing
  | otherwise = do
      checked <- grammarV1CheckedTypeModeWithNamedResolutions
        staticContext
        emptySurfaceState
        resolutions
        (locatedValue (grammarV1TypeAliasTarget source))
      pure $ fmap
        (\(checkedMode, steps) ->
          ( (locatedValue (grammarV1TypeAliasName source), checkedMode)
          , steps
          ))
        checked
