module Phil.Surface.GrammarV1.CheckedType
  ( grammarV1CheckedType
  , grammarV1CheckedTypeMode
  ) where

import Phil.Core.CheckedBindingMode
  ( CheckedTypeMode (..)
  )
import Phil.Core.DataMode
  ( deriveRecordMode
  )
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax
  ( Mode (..)
  , ProductElementType (..)
  , Ty (..)
  )
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.BoundType
  ( grammarV1BoundType
  )
import Phil.Surface.GrammarV1.CheckedProofType
  ( grammarV1CheckedProofType
  )
import Phil.Surface.GrammarV1.CheckedRefinementType
  ( grammarV1CheckedRefinementType
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Type (..)
  )

-- | Provide one checked entry point for every currently supported Grammar-v1
-- type fragment. Proof and refinement types retain the checked proposition
-- semantics established by their dedicated bridges, including Core focusing
-- errors and traces. Every other already-supported type delegates once to the
-- existing binding-aware structural dispatcher and carries an empty focusing
-- trace because no proposition focusing occurred. Structural source
-- non-competence remains Nothing throughout; this dispatcher invents no type
-- interpretation, claim semantics, coercion, evidence, element mode, or fallback.
grammarV1CheckedType
  :: StaticContext
  -> SurfaceState
  -> GrammarV1Type
  -> Maybe (Either FocusingError (Ty, [FocusStep]))
grammarV1CheckedType staticContext state sourceType =
  case sourceType of
    GrammarV1ProofType _ ->
      grammarV1CheckedProofType staticContext state sourceType
    GrammarV1RefinementType _ _ _ ->
      grammarV1CheckedRefinementType staticContext state sourceType
    _ -> do
      ty <- grammarV1BoundType state sourceType
      pure (Right (ty, []))

-- | Extend the checked type bridge with structural mode only where the checked
-- Core type itself carries enough semantic authority to determine mode without a
-- named declaration/resource lookup. This is the source-side half of the
-- governing `mode(T)` rule used by RES-012: once the type is checked, primitive
-- immutable values and proof evidence are unrestricted, owned Bytes are linear,
-- refinements inherit their base type's mode, endpoint/pending-receive resources
-- are linear, and Core products use their already-checked element modes.
--
-- Opaque/named types, Frame values, and Validated values remain outside this
-- bounded bridge because their structural behavior belongs to a checked semantic
-- declaration/resource contract rather than their Core constructor spelling.
-- Source non-competence therefore remains 'Nothing'; a Core focusing failure from
-- type checking remains an explicit 'Left FocusingError'.
grammarV1CheckedTypeMode
  :: StaticContext
  -> SurfaceState
  -> GrammarV1Type
  -> Maybe (Either FocusingError (CheckedTypeMode, [FocusStep]))
grammarV1CheckedTypeMode staticContext state sourceType = do
  checked <- grammarV1CheckedType staticContext state sourceType
  case checked of
    Left err -> pure (Left err)
    Right (ty, steps) -> do
      mode <- checkedCoreTypeMode ty
      pure
        (Right
          ( CheckedTypeMode
              { checkedBindingType = ty
              , checkedBindingMode = mode
              }
          , steps
          ))

checkedCoreTypeMode :: Ty -> Maybe Mode
checkedCoreTypeMode ty = case ty of
  TyUnit -> Just Unrestricted
  TyBool -> Just Unrestricted
  TyUInt _ -> Just Unrestricted
  TyBytes _ -> Just Linear
  TyPendingRecv _ -> Just Linear
  TyProof _ -> Just Unrestricted
  TyEndpoint _ -> Just Linear
  TyProduct elements ->
    Just (deriveRecordMode (map productElementMode elements))
  TyRefined _ base _ -> checkedCoreTypeMode base
  TyFrame _ -> Nothing
  TyValidated _ _ _ -> Nothing
  TyOpaque _ -> Nothing
  TyOpaqueSorted _ _ -> Nothing
