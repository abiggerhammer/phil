{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.GenericRequirementCore
  ( GrammarV1ResolvedStructuralRequirement (..)
  , GrammarV1ResolvedProviderRequirement (..)
  , GrammarV1GenericRequirementCoreError (..)
  , grammarV1CheckedCoreGenericRequirement
  ) where

import Data.Text (Text)
import Phil.Core.Focusing (FocusStep, FocusingError)
import Phil.Core.Generic
  ( GenericRequirement (..)
  , GenericStaticParameterKey
  , GenericValueParameterKey
  , StructuralPermission (..)
  )
import Phil.Core.Static (InterfaceRevision, StaticContext)
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.CheckedProposition
  ( grammarV1CheckedProposition
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1GenericRequirement (..)
  , GrammarV1Type
  )
import Phil.Surface.Syntax (Located (..))

-- | Binder identity is supplied by the competent generic-binder layer rather
-- than manufactured from source spelling in this SURF-008 slice.
data GrammarV1ResolvedStructuralRequirement = GrammarV1ResolvedStructuralRequirement
  { resolvedStructuralRequirementSourceName :: Text
  , resolvedStructuralRequirementValueKey :: GenericValueParameterKey
  }
  deriving (Eq, Show)

-- | Provider-interface identity is likewise supplied by competent provider
-- resolution. The exact source name/type are repeated so evidence for a
-- different requirement cannot be silently attached here.
data GrammarV1ResolvedProviderRequirement = GrammarV1ResolvedProviderRequirement
  { resolvedProviderRequirementSourceName :: Text
  , resolvedProviderRequirementSourceType :: GrammarV1Type
  , resolvedProviderRequirementStaticKey :: GenericStaticParameterKey
  , resolvedProviderRequirementInterfaceRevision :: InterfaceRevision
  }
  deriving (Eq, Show)

data GrammarV1GenericRequirementCoreError
  = GrammarV1StructuralRequirementUnresolved Text
  | GrammarV1StructuralRequirementAmbiguous Text [GenericValueParameterKey]
  | GrammarV1StructuralPermissionUnsupported Text
  | GrammarV1ProviderRequirementUnresolved Text GrammarV1Type
  | GrammarV1ProviderRequirementSourceTypeMismatch
      Text
      GrammarV1Type
      [GrammarV1Type]
  | GrammarV1ProviderRequirementAmbiguous
      Text
      GrammarV1Type
      [InterfaceRevision]
  | GrammarV1GenericRequirementFocusingError FocusingError
  deriving (Eq, Show)

-- | Route exactly the Core generic-requirement categories that currently have
-- concrete semantic carriers: structural permissions, propositions, and
-- provider-contract interface requirements. All other Grammar-v1 requirement
-- categories remain structural non-competence (Nothing) until Core owns their
-- corresponding GenericRequirement constructors.
--
-- This bridge never proves that a source identifier denotes a binder, derives
-- a provider InterfaceRevision from type/display spelling, creates evidence,
-- chooses a disposition, or discharges a requirement.
grammarV1CheckedCoreGenericRequirement
  :: StaticContext
  -> SurfaceState
  -> [GrammarV1ResolvedStructuralRequirement]
  -> [GrammarV1ResolvedProviderRequirement]
  -> GrammarV1GenericRequirement
  -> Maybe
      (Either
        GrammarV1GenericRequirementCoreError
        (GenericRequirement, [FocusStep]))
grammarV1CheckedCoreGenericRequirement
    staticContext state structuralResolutions providerResolutions requirement =
  case requirement of
    GrammarV1StructuralRequirement (Located _ sourceName) (Located _ permissionName) ->
      Just $ do
        valueKey <- resolveStructural sourceName
        permission <- case permissionName of
          "discard" -> Right WeakeningPermission
          "duplicate" -> Right ContractionPermission
          other -> Left (GrammarV1StructuralPermissionUnsupported other)
        Right (GenericStructuralRequirement valueKey permission, [])

    GrammarV1PropositionRequirement (Located _ proposition) -> do
      checked <- grammarV1CheckedProposition staticContext state proposition
      Just $ case checked of
        Left err -> Left (GrammarV1GenericRequirementFocusingError err)
        Right (coreProposition, focusSteps) ->
          Right (GenericPropositionRequirement coreProposition, focusSteps)

    GrammarV1ProviderRequirement (Located _ sourceName) (Located _ sourceType) ->
      Just $ do
        (staticKey, interfaceRevision) <- resolveProvider sourceName sourceType
        Right
          ( GenericProviderContractRequirement staticKey interfaceRevision
          , []
          )

    _ -> Nothing
  where
    resolveStructural sourceName =
      case
        [ resolvedStructuralRequirementValueKey resolution
        | resolution <- structuralResolutions
        , resolvedStructuralRequirementSourceName resolution == sourceName
        ] of
          [] -> Left (GrammarV1StructuralRequirementUnresolved sourceName)
          [valueKey] -> Right valueKey
          valueKeys -> Left
            (GrammarV1StructuralRequirementAmbiguous sourceName valueKeys)

    resolveProvider sourceName sourceType =
      case exactMatches of
        [] -> case sameName of
          [] -> Left
            (GrammarV1ProviderRequirementUnresolved sourceName sourceType)
          resolutions -> Left
            (GrammarV1ProviderRequirementSourceTypeMismatch
              sourceName
              sourceType
              (map resolvedProviderRequirementSourceType resolutions))
        [resolution] -> Right
          ( resolvedProviderRequirementStaticKey resolution
          , resolvedProviderRequirementInterfaceRevision resolution
          )
        resolutions -> Left
          (GrammarV1ProviderRequirementAmbiguous
            sourceName
            sourceType
            (map resolvedProviderRequirementInterfaceRevision resolutions))
      where
        sameName =
          [ resolution
          | resolution <- providerResolutions
          , resolvedProviderRequirementSourceName resolution == sourceName
          ]
        exactMatches =
          [ resolution
          | resolution <- sameName
          , resolvedProviderRequirementSourceType resolution == sourceType
          ]
