{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.GrammarV1.ArchitectureComponentProvisioning
  ( GrammarV1ArchitectureProtocolOccurrence (..)
  , GrammarV1ComponentProvisioningSource (..)
  , GrammarV1ProvisionedComponentParameter (..)
  , GrammarV1ResolvedComponentProvisioning (..)
  , GrammarV1ArchitectureComponentProvisioningError (..)
  , grammarV1ResolveArchitectureComponentProvisioning
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.CheckedBindingMode
  ( CheckedTypeMode (..)
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..)
  )
import Phil.Core.Process
  ( ProcessKey
  )
import Phil.Core.ProcessActivation
  ( ActivationOccurrenceKey (..)
  )
import Phil.Core.Protocol
  ( ProtocolInstanceRevision (..)
  , ProtocolRoleKey (..)
  )
import Phil.Core.Protocol.Family
  ( BinaryProtocolInstance
  , ProtocolProjectionEvidence (..)
  )
import Phil.Core.Static
  ( DefinitionRevision (..)
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Name (..)
  , Ty
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceState (..)
  )
import Phil.Surface.GrammarV1.ArchitectureSurface
  ( GrammarV1CheckedArchitectureItem (..)
  , GrammarV1CheckedArchitectureRoleTarget (..)
  , GrammarV1CheckedArchitectureSurface (..)
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ComponentDecl (..)
  , GrammarV1TermParam (..)
  )
import Phil.Surface.GrammarV1.ProtocolEndpointType
  ( GrammarV1ProtocolEndpointResolution (..)
  , GrammarV1ProtocolEndpointTypeError
  , GrammarV1ResolvedProtocolEndpointType (..)
  , grammarV1ResolvedProtocolEndpointType
  )
import Phil.Surface.GrammarV1.SemanticComponentHeader
  ( GrammarV1CheckedSemanticComponentHeader (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | One exact instantiated protocol selected for a named protocol occurrence in
-- one architecture. The occurrence name remains identity-bearing even when two
-- occurrences instantiate the same static protocol application.
data GrammarV1ArchitectureProtocolOccurrence = GrammarV1ArchitectureProtocolOccurrence
  { architectureProtocolOccurrenceName :: Text
  , architectureProtocolOccurrenceSourceReference :: GenericStaticActual
  , architectureProtocolOccurrenceInstance :: BinaryProtocolInstance
  }
  deriving (Eq, Show)

-- | Exact semantic source for one component parameter. Entry and protocol-role
-- occurrence identity are retained rather than collapsed to the parameter's Core
-- type, so equal endpoint Session syntax cannot substitute for exact wiring.
data GrammarV1ComponentProvisioningSource
  = GrammarV1ComponentProvisioningEntry
      Text
      Ty
  | GrammarV1ComponentProvisioningProtocolEndpoint
      Text
      ProtocolProjectionEvidence
  deriving (Eq, Show)

data GrammarV1ProvisionedComponentParameter = GrammarV1ProvisionedComponentParameter
  { provisionedComponentParameterBinder :: GrammarV1ResolvedBinder
  , provisionedComponentParameterCheckedMode :: CheckedTypeMode
  , provisionedComponentParameterOccurrence :: ActivationOccurrenceKey
  , provisionedComponentParameterSource :: GrammarV1ComponentProvisioningSource
  }
  deriving (Eq, Show)

-- | Bounded INT-008 result: architecture occurrence/process identity plus one
-- exact source for every runtime parameter in the checked component header.
-- This is the last static wiring carrier before ProcessActivation/ProtocolContext
-- construction; it does not itself activate or execute the process.
data GrammarV1ResolvedComponentProvisioning = GrammarV1ResolvedComponentProvisioning
  { resolvedProvisioningComponentOccurrence :: Text
  , resolvedProvisioningProcessSite :: Text
  , resolvedProvisioningProcessKey :: ProcessKey
  , resolvedProvisioningParameters :: [GrammarV1ProvisionedComponentParameter]
  }
  deriving (Eq, Show)

data GrammarV1ArchitectureComponentProvisioningError
  = GrammarV1ProvisioningComponentOccurrenceMissing Text
  | GrammarV1ProvisioningComponentOccurrenceAmbiguous Text
  | GrammarV1ProvisioningComponentTargetMismatch
      Text GenericStaticActual GenericStaticActual
  | GrammarV1ProvisioningProcessSiteMissing Text
  | GrammarV1ProvisioningProcessSiteAmbiguous Text
  | GrammarV1ProvisioningProcessTargetMismatch Text Text Text
  | GrammarV1ProvisioningParameterShapeMismatch
  | GrammarV1ProvisioningParameterMetadataMissing Text
  | GrammarV1ProvisioningBindMissing Text
  | GrammarV1ProvisioningBindAmbiguous Text [Text]
  | GrammarV1ProvisioningSourceUnsupported Text Text
  | GrammarV1ProvisioningEntryMissing Text
  | GrammarV1ProvisioningEntryAmbiguous Text
  | GrammarV1ProvisioningEntryTypeMismatch Text Ty Ty
  | GrammarV1ProvisioningProtocolOccurrenceMissing Text
  | GrammarV1ProvisioningProtocolOccurrenceAmbiguous Text
  | GrammarV1ProvisioningProtocolResolutionMissing Text
  | GrammarV1ProvisioningProtocolResolutionAmbiguous Text
  | GrammarV1ProvisioningProtocolSourceMismatch
      Text GenericStaticActual GenericStaticActual
  | GrammarV1ProvisioningRoleBindingMissing Text
  | GrammarV1ProvisioningRoleBindingAmbiguous Text
  | GrammarV1ProvisioningRoleTargetMismatch Text Text
  | GrammarV1ProvisioningProtocolEndpointTypeError
      Text GrammarV1ProtocolEndpointTypeError
  | GrammarV1ProvisioningProtocolEndpointNonCompetent Text
  | GrammarV1ProvisioningProtocolEndpointRoleMismatch
      Text ProtocolRoleKey ProtocolRoleKey
  | GrammarV1ProvisioningProtocolEndpointModeMismatch
      Text CheckedTypeMode CheckedTypeMode
  | GrammarV1ProvisioningDuplicateRestrictedSource
      ActivationOccurrenceKey Text Text
  deriving (Eq, Show)

-- | Resolve the explicit architecture wiring for one already-checked component
-- occurrence and one already-derived ProcessKey.
--
-- The bounded spelling admitted here is deliberately exact:
--
--   * `instance client = ClientWorker;`
--   * `process client_run = client;`
--   * `bind client.payload = payload;` where `payload` is an architecture entry;
--   * `bind client.endpoint = ping.Client;` where `ping` is an exact protocol
--     occurrence and `role ping.Client = client;` selects this participant.
--
-- Every component parameter must have exactly one bind. Restricted sources may
-- not feed two parameters. Endpoint checking is rerun against the exact protocol
-- occurrence so instance/role identity is preserved instead of inferred from an
-- equal `TyEndpoint Session` shape.
grammarV1ResolveArchitectureComponentProvisioning
  :: GrammarV1CheckedArchitectureSurface
  -> Text
  -> Text
  -> ProcessKey
  -> GrammarV1ComponentDecl
  -> GrammarV1CheckedSemanticComponentHeader
  -> [GrammarV1ArchitectureProtocolOccurrence]
  -> Either
      GrammarV1ArchitectureComponentProvisioningError
      GrammarV1ResolvedComponentProvisioning
grammarV1ResolveArchitectureComponentProvisioning
    architecture componentOccurrence processSite processKey component header
    protocolOccurrences = do
  requireComponentOccurrence
  requireProcessSite
  parameterPairs <- exactParameterPairs component header
  provisioned <- mapM provisionOne parameterPairs
  rejectDuplicateRestricted provisioned
  Right GrammarV1ResolvedComponentProvisioning
    { resolvedProvisioningComponentOccurrence = componentOccurrence
    , resolvedProvisioningProcessSite = processSite
    , resolvedProvisioningProcessKey = processKey
    , resolvedProvisioningParameters = provisioned
    }
  where
    items = checkedArchitectureItems architecture

    requireComponentOccurrence =
      case
        [ target
        | GrammarV1CheckedArchitectureInstance occurrence target <- items
        , occurrence == componentOccurrence
        ] of
        [] -> Left (GrammarV1ProvisioningComponentOccurrenceMissing componentOccurrence)
        [target]
          | target == expectedComponentTarget -> Right ()
          | otherwise -> Left
              (GrammarV1ProvisioningComponentTargetMismatch
                componentOccurrence expectedComponentTarget target)
        _ -> Left (GrammarV1ProvisioningComponentOccurrenceAmbiguous componentOccurrence)

    expectedComponentTarget =
      ReferencedGenericStaticActual (checkedSemanticComponentDisplayName header)

    requireProcessSite =
      case
        [ target
        | GrammarV1CheckedArchitectureProcess site target <- items
        , site == processSite
        ] of
        [] -> Left (GrammarV1ProvisioningProcessSiteMissing processSite)
        [target]
          | target == componentOccurrence -> Right ()
          | otherwise -> Left
              (GrammarV1ProvisioningProcessTargetMismatch
                processSite componentOccurrence target)
        _ -> Left (GrammarV1ProvisioningProcessSiteAmbiguous processSite)

    provisionOne (sourceParam, binder, checkedMode) = do
      let parameterName = grammarV1ResolvedBinderDisplayName binder
          targetName = componentOccurrence <> "." <> parameterName
      sourceName <- requireBind targetName
      (occurrenceKey, source) <- resolveSource
        parameterName
        (locatedValue (grammarV1TermParamType sourceParam))
        checkedMode
        sourceName
      Right GrammarV1ProvisionedComponentParameter
        { provisionedComponentParameterBinder = binder
        , provisionedComponentParameterCheckedMode = checkedMode
        , provisionedComponentParameterOccurrence = occurrenceKey
        , provisionedComponentParameterSource = source
        }

    requireBind targetName =
      case
        [ source
        | GrammarV1CheckedArchitectureBind target source <- items
        , target == targetName
        ] of
        [] -> Left (GrammarV1ProvisioningBindMissing targetName)
        [source] -> Right source
        sources -> Left (GrammarV1ProvisioningBindAmbiguous targetName sources)

    resolveSource parameterName sourceType checkedMode sourceName =
      case Text.splitOn "." sourceName of
        [entryName] -> resolveEntry parameterName checkedMode entryName
        [protocolOccurrence, roleName] ->
          resolveProtocolEndpoint
            parameterName sourceType checkedMode protocolOccurrence roleName
        _ -> Left
          (GrammarV1ProvisioningSourceUnsupported parameterName sourceName)

    resolveEntry parameterName checkedMode entryName = do
      entryType <- case
        [ ty
        | GrammarV1CheckedArchitectureEntry name ty _ <- items
        , name == entryName
        ] of
        [] -> Left (GrammarV1ProvisioningEntryMissing entryName)
        [ty] -> Right ty
        _ -> Left (GrammarV1ProvisioningEntryAmbiguous entryName)
      if entryType /= checkedBindingType checkedMode
        then Left
          (GrammarV1ProvisioningEntryTypeMismatch
            parameterName (checkedBindingType checkedMode) entryType)
        else Right
          ( entryOccurrenceKey architecture entryName
          , GrammarV1ComponentProvisioningEntry entryName entryType
          )

    resolveProtocolEndpoint
        parameterName sourceType checkedMode protocolOccurrence roleName = do
      architectureReference <- requireArchitectureProtocol protocolOccurrence
      exactOccurrence <- requireProtocolOccurrence protocolOccurrence
      if architectureProtocolOccurrenceSourceReference exactOccurrence
          /= architectureReference
        then Left
          (GrammarV1ProvisioningProtocolSourceMismatch
            protocolOccurrence
            architectureReference
            (architectureProtocolOccurrenceSourceReference exactOccurrence))
        else Right ()
      requireInternalRoleTarget protocolOccurrence roleName
      let endpointResolution = GrammarV1ProtocolEndpointResolution
            { protocolEndpointResolutionSourceReference = architectureReference
            , protocolEndpointResolutionInstance =
                architectureProtocolOccurrenceInstance exactOccurrence
            }
      resolved <- case grammarV1ResolvedProtocolEndpointType
          [endpointResolution] sourceType of
        Nothing -> Left
          (GrammarV1ProvisioningProtocolEndpointNonCompetent parameterName)
        Just (Left err) -> Left
          (GrammarV1ProvisioningProtocolEndpointTypeError parameterName err)
        Just (Right value) -> Right value
      let projection = resolvedProtocolEndpointProjection resolved
          actualRole = protocolProjectionRole projection
          expectedRole = ProtocolRoleKey roleName
          resolvedMode = resolvedProtocolEndpointCheckedMode resolved
      if actualRole /= expectedRole
        then Left
          (GrammarV1ProvisioningProtocolEndpointRoleMismatch
            parameterName expectedRole actualRole)
        else Right ()
      if resolvedMode /= checkedMode
        then Left
          (GrammarV1ProvisioningProtocolEndpointModeMismatch
            parameterName checkedMode resolvedMode)
        else Right ()
      Right
        ( protocolEndpointOccurrenceKey
            architecture protocolOccurrence projection
        , GrammarV1ComponentProvisioningProtocolEndpoint
            protocolOccurrence projection
        )

    requireArchitectureProtocol protocolOccurrence =
      case
        [ reference
        | GrammarV1CheckedArchitectureProtocol occurrence reference <- items
        , occurrence == protocolOccurrence
        ] of
        [] -> Left
          (GrammarV1ProvisioningProtocolOccurrenceMissing protocolOccurrence)
        [reference] -> Right reference
        _ -> Left
          (GrammarV1ProvisioningProtocolOccurrenceAmbiguous protocolOccurrence)

    requireProtocolOccurrence protocolOccurrence =
      case
        [ occurrence
        | occurrence <- protocolOccurrences
        , architectureProtocolOccurrenceName occurrence == protocolOccurrence
        ] of
        [] -> Left
          (GrammarV1ProvisioningProtocolResolutionMissing protocolOccurrence)
        [occurrence] -> Right occurrence
        _ -> Left
          (GrammarV1ProvisioningProtocolResolutionAmbiguous protocolOccurrence)

    requireInternalRoleTarget protocolOccurrence roleName =
      let role = protocolOccurrence <> "." <> roleName
      in case
        [ target
        | GrammarV1CheckedArchitectureRole candidate target <- items
        , candidate == role
        ] of
        [] -> Left (GrammarV1ProvisioningRoleBindingMissing role)
        [GrammarV1CheckedInternalRoleTarget target]
          | target == componentOccurrence -> Right ()
          | otherwise -> Left
              (GrammarV1ProvisioningRoleTargetMismatch role target)
        [GrammarV1CheckedExternalRoleTarget] -> Left
          (GrammarV1ProvisioningRoleTargetMismatch role "external")
        _ -> Left (GrammarV1ProvisioningRoleBindingAmbiguous role)

exactParameterPairs
  :: GrammarV1ComponentDecl
  -> GrammarV1CheckedSemanticComponentHeader
  -> Either
      GrammarV1ArchitectureComponentProvisioningError
      [(Located GrammarV1TermParam, GrammarV1ResolvedBinder, CheckedTypeMode)]
exactParameterPairs component header =
  case (grammarV1ComponentTermParams component, checkedSemanticComponentParameters header) of
    (Nothing, Nothing) -> Right []
    (Just sourceParams, Just checkedParams)
      | length sourceParams == length checkedParams ->
          mapM pairOne (zip sourceParams checkedParams)
      | otherwise -> Left GrammarV1ProvisioningParameterShapeMismatch
    _ -> Left GrammarV1ProvisioningParameterShapeMismatch
  where
    bindings = stateBindings (checkedSemanticComponentState header)

    pairOne (sourceParam, (binder, _)) = do
      let displayName = grammarV1ResolvedBinderDisplayName binder
          sourceName = locatedValue
            (grammarV1TermParamName (locatedValue sourceParam))
      if sourceName /= displayName
        then Left GrammarV1ProvisioningParameterShapeMismatch
        else Right ()
      let Name coreName = grammarV1ResolvedBinderCoreName binder
      meta <- maybe
        (Left (GrammarV1ProvisioningParameterMetadataMissing displayName))
        Right
        (Map.lookup coreName bindings)
      Right
        ( sourceParam
        , binder
        , CheckedTypeMode
            { checkedBindingType = bindingType meta
            , checkedBindingMode = bindingMode meta
            }
        )

rejectDuplicateRestricted
  :: [GrammarV1ProvisionedComponentParameter]
  -> Either GrammarV1ArchitectureComponentProvisioningError ()
rejectDuplicateRestricted = go Map.empty
  where
    go _ [] = Right ()
    go seen (parameter : rest) =
      case checkedBindingMode (provisionedComponentParameterCheckedMode parameter) of
        Unrestricted -> go seen rest
        Affine -> reserve seen parameter rest
        Linear -> reserve seen parameter rest

    reserve seen parameter rest =
      let key = provisionedComponentParameterOccurrence parameter
          currentName = grammarV1ResolvedBinderDisplayName
            (provisionedComponentParameterBinder parameter)
      in case Map.lookup key seen of
        Just firstName -> Left
          (GrammarV1ProvisioningDuplicateRestrictedSource
            key firstName currentName)
        Nothing -> go (Map.insert key currentName seen) rest

entryOccurrenceKey
  :: GrammarV1CheckedArchitectureSurface
  -> Text
  -> ActivationOccurrenceKey
entryOccurrenceKey architecture entryName =
  ActivationOccurrenceKey
    ("phil.architecture.entry.v1:"
      <> unDefinitionRevision (checkedArchitectureDefinitionRevision architecture)
      <> ":"
      <> entryName)

protocolEndpointOccurrenceKey
  :: GrammarV1CheckedArchitectureSurface
  -> Text
  -> ProtocolProjectionEvidence
  -> ActivationOccurrenceKey
protocolEndpointOccurrenceKey architecture protocolOccurrence projection =
  ActivationOccurrenceKey
    ("phil.architecture.protocol-endpoint.v1:"
      <> unDefinitionRevision (checkedArchitectureDefinitionRevision architecture)
      <> ":"
      <> protocolOccurrence
      <> ":"
      <> unProtocolRoleKey (protocolProjectionRole projection)
      <> ":"
      <> unProtocolInstanceRevision (protocolProjectionInstance projection))
