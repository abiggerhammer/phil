module Phil.Surface.GrammarV1.ProtocolEndpointType
  ( GrammarV1ProtocolEndpointResolution (..)
  , GrammarV1ResolvedProtocolEndpointType (..)
  , GrammarV1ProtocolEndpointTypeError (..)
  , grammarV1ResolvedProtocolEndpointType
  ) where

import Phil.Core.CheckedBindingMode
  ( CheckedTypeMode (..)
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual
  )
import Phil.Core.Protocol
  ( ProtocolRoleKey (..)
  )
import Phil.Core.Protocol.Family
  ( BinaryProtocolInstance
  , ProtocolFamilyError
  , ProtocolProjectionEvidence (..)
  , projectProtocolRole
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Ty (..)
  )
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1BareStaticReferenceActual
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1QualifiedName (..)
  , GrammarV1StaticArgument (..)
  , GrammarV1StaticReference (..)
  , GrammarV1Type (..)
  )

-- | One caller-resolved source protocol family available while checking a
-- component header. The source reference is only a lookup identity: the exact
-- semantic endpoint type comes from the already-instantiated Core protocol
-- projection, not from reinterpreting the spelling of the source type.
data GrammarV1ProtocolEndpointResolution = GrammarV1ProtocolEndpointResolution
  { protocolEndpointResolutionSourceReference :: GenericStaticActual
  , protocolEndpointResolutionInstance :: BinaryProtocolInstance
  }
  deriving (Eq, Show)

-- | Exact result of resolving a bounded source endpoint spelling such as
-- Client[Ping]. The source protocol reference is retained for diagnostics while
-- the Core projection carries the exact protocol-instance revision, role, and
-- local session. Endpoint values are linear by construction.
data GrammarV1ResolvedProtocolEndpointType = GrammarV1ResolvedProtocolEndpointType
  { resolvedProtocolEndpointSourceReference :: GenericStaticActual
  , resolvedProtocolEndpointProjection :: ProtocolProjectionEvidence
  , resolvedProtocolEndpointCheckedMode :: CheckedTypeMode
  }
  deriving (Eq, Show)

data GrammarV1ProtocolEndpointTypeError
  = GrammarV1ProtocolEndpointResolutionAmbiguous GenericStaticActual Int
  | GrammarV1ProtocolEndpointProjectionError ProtocolFamilyError
  deriving (Eq, Show)

-- | Resolve the bounded Grammar-v1 endpoint type shape Role[Protocol] against
-- caller-supplied protocol-family resolutions.
--
-- This function deliberately claims competence only when the static protocol
-- reference matches an explicit resolution. A different specialized named type
-- remains outside this bridge rather than being guessed to be an endpoint. Once
-- a protocol resolution matches, Core's exact role projection is authoritative:
-- an unknown role fails closed, and the resulting type is the exact projected
-- Session wrapped in linear TyEndpoint.
grammarV1ResolvedProtocolEndpointType
  :: [GrammarV1ProtocolEndpointResolution]
  -> GrammarV1Type
  -> Maybe
      (Either
        GrammarV1ProtocolEndpointTypeError
        GrammarV1ResolvedProtocolEndpointType)
grammarV1ResolvedProtocolEndpointType resolutions sourceType = do
  (role, sourceReference) <- endpointSourceShape sourceType
  let matches =
        [ resolution
        | resolution <- resolutions
        , protocolEndpointResolutionSourceReference resolution == sourceReference
        ]
  case matches of
    [] -> Nothing
    [resolution] -> pure $ do
      projection <- mapLeft GrammarV1ProtocolEndpointProjectionError $
        projectProtocolRole
          (protocolEndpointResolutionInstance resolution)
          role
      let checked = CheckedTypeMode
            { checkedBindingType = TyEndpoint (protocolProjectionSession projection)
            , checkedBindingMode = Linear
            }
      Right GrammarV1ResolvedProtocolEndpointType
        { resolvedProtocolEndpointSourceReference = sourceReference
        , resolvedProtocolEndpointProjection = projection
        , resolvedProtocolEndpointCheckedMode = checked
        }
    many -> pure
      (Left
        (GrammarV1ProtocolEndpointResolutionAmbiguous
          sourceReference
          (length many)))

endpointSourceShape
  :: GrammarV1Type
  -> Maybe (ProtocolRoleKey, GenericStaticActual)
endpointSourceShape sourceType = case sourceType of
  GrammarV1NamedType roleReference -> do
    role <- singleRoleName roleReference
    protocolReference <- singleBareProtocolArgument roleReference
    pure (ProtocolRoleKey role, protocolReference)
  _ -> Nothing

singleRoleName :: GrammarV1StaticReference -> Maybe Data.Text.Text
singleRoleName reference = case grammarV1QualifiedNameParts
    (grammarV1StaticReferenceName reference) of
  [role] -> Just role
  _ -> Nothing

singleBareProtocolArgument :: GrammarV1StaticReference -> Maybe GenericStaticActual
singleBareProtocolArgument reference = case grammarV1StaticReferenceArguments reference of
  [GrammarV1StaticReferenceArgument protocolReference] ->
    grammarV1BareStaticReferenceActual
      (GrammarV1StaticReferenceArgument protocolReference)
  _ -> Nothing

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
