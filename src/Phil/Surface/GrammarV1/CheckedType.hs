module Phil.Surface.GrammarV1.CheckedType
  ( GrammarV1ResolvedNamedTypeMode (..)
  , GrammarV1CheckedTypeModeOrigin (..)
  , GrammarV1CheckedResolvedTypeMode (..)
  , GrammarV1CheckedTypeModeResolutionError (..)
  , grammarV1CheckedType
  , grammarV1CheckedTypeMode
  , grammarV1CheckedTypeModeWithNamedResolutions
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
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual
  , GenericStaticKind (..)
  )
import Phil.Core.SIntArithmetic (sIntTypeFromCoreType)
import Phil.Core.Static
  ( DeclarationKey
  , InterfaceRevision
  , StaticContext
  )
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
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1BareStaticReferenceActual
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1StaticArgument (..)
  , GrammarV1Type (..)
  )

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

data GrammarV1ResolvedNamedTypeMode = GrammarV1ResolvedNamedTypeMode
  { resolvedNamedTypeReference :: GenericStaticActual
  , resolvedNamedTypeKind :: GenericStaticKind
  , resolvedNamedTypeDeclarationKey :: DeclarationKey
  , resolvedNamedTypeInterfaceRevision :: InterfaceRevision
  , resolvedNamedTypeCheckedMode :: CheckedTypeMode
  }
  deriving (Eq, Show)

data GrammarV1CheckedTypeModeOrigin
  = GrammarV1IntrinsicTypeModeOrigin
  | GrammarV1NamedTypeModeOrigin
      GenericStaticActual
      DeclarationKey
      InterfaceRevision
  deriving (Eq, Show)

data GrammarV1CheckedResolvedTypeMode = GrammarV1CheckedResolvedTypeMode
  { checkedResolvedTypeMode :: CheckedTypeMode
  , checkedResolvedTypeModeOrigin :: GrammarV1CheckedTypeModeOrigin
  }
  deriving (Eq, Show)

data GrammarV1CheckedTypeModeResolutionError
  = GrammarV1TypeModeFocusingError FocusingError
  | GrammarV1NamedTypeModeUnresolved GenericStaticActual
  | GrammarV1NamedTypeModeKindMismatch
      GenericStaticActual
      [GenericStaticKind]
  | GrammarV1NamedTypeModeAmbiguous
      GenericStaticActual
      [DeclarationKey]
  | GrammarV1NamedTypeModeCheckedTypeMismatch
      GenericStaticActual
      Ty
      Ty
  deriving (Eq, Show)

grammarV1CheckedTypeModeWithNamedResolutions
  :: StaticContext
  -> SurfaceState
  -> [GrammarV1ResolvedNamedTypeMode]
  -> GrammarV1Type
  -> Maybe
      (Either
        GrammarV1CheckedTypeModeResolutionError
        (GrammarV1CheckedResolvedTypeMode, [FocusStep]))
grammarV1CheckedTypeModeWithNamedResolutions
    staticContext state resolutions sourceType = do
  checked <- grammarV1CheckedType staticContext state sourceType
  case checked of
    Left err -> pure (Left (GrammarV1TypeModeFocusingError err))
    Right (ty, steps) -> case checkedCoreTypeMode ty of
      Just mode -> pure
        (Right
          ( GrammarV1CheckedResolvedTypeMode
              { checkedResolvedTypeMode = CheckedTypeMode
                  { checkedBindingType = ty
                  , checkedBindingMode = mode
                  }
              , checkedResolvedTypeModeOrigin = GrammarV1IntrinsicTypeModeOrigin
              }
          , steps
          ))
      Nothing -> do
        sourceReference <- namedTypeReference sourceType
        pure $
          fmap
            (\resolved -> (resolved, steps))
            (resolveNamedTypeMode sourceReference ty resolutions)

namedTypeReference :: GrammarV1Type -> Maybe GenericStaticActual
namedTypeReference sourceType = case sourceType of
  GrammarV1NamedType reference ->
    grammarV1BareStaticReferenceActual
      (GrammarV1StaticReferenceArgument reference)
  _ -> Nothing

resolveNamedTypeMode
  :: GenericStaticActual
  -> Ty
  -> [GrammarV1ResolvedNamedTypeMode]
  -> Either GrammarV1CheckedTypeModeResolutionError GrammarV1CheckedResolvedTypeMode
resolveNamedTypeMode sourceReference checkedType resolutions =
  case referenceMatches of
    [] -> Left (GrammarV1NamedTypeModeUnresolved sourceReference)
    _ -> case typeMatches of
      [] -> Left
        (GrammarV1NamedTypeModeKindMismatch
          sourceReference
          (map resolvedNamedTypeKind referenceMatches))
      [resolved]
        | checkedBindingType (resolvedNamedTypeCheckedMode resolved) == checkedType ->
            Right GrammarV1CheckedResolvedTypeMode
              { checkedResolvedTypeMode = resolvedNamedTypeCheckedMode resolved
              , checkedResolvedTypeModeOrigin = GrammarV1NamedTypeModeOrigin
                  sourceReference
                  (resolvedNamedTypeDeclarationKey resolved)
                  (resolvedNamedTypeInterfaceRevision resolved)
              }
        | otherwise -> Left
            (GrammarV1NamedTypeModeCheckedTypeMismatch
              sourceReference
              checkedType
              (checkedBindingType (resolvedNamedTypeCheckedMode resolved)))
      many -> Left
        (GrammarV1NamedTypeModeAmbiguous
          sourceReference
          (map resolvedNamedTypeDeclarationKey many))
  where
    referenceMatches =
      [ resolved
      | resolved <- resolutions
      , resolvedNamedTypeReference resolved == sourceReference
      ]
    typeMatches =
      [ resolved
      | resolved <- referenceMatches
      , resolvedNamedTypeKind resolved == GenericTypeKind
      ]

checkedCoreTypeMode :: Ty -> Maybe Mode
checkedCoreTypeMode ty
  | Just _ <- sIntTypeFromCoreType ty = Just Unrestricted
  | otherwise = case ty of
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
