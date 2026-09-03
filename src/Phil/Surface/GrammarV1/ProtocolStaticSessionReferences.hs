module Phil.Surface.GrammarV1.ProtocolStaticSessionReferences
  ( grammarV1ClosedProtocolRoleSessionReferences
  ) where

import Phil.Core.Generic.StaticActual (GenericStaticActual)
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Surface.GrammarV1.Elaborate
  ( grammarV1BareStaticReferenceActual
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ProtocolDecl (..)
  , GrammarV1RoleSessionDecl (..)
  , GrammarV1SessionExpression (..)
  , GrammarV1StaticArgument (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Preserve the first closed Grammar-v1 protocol fragment whose role bodies are
-- unresolved static session references rather than inline session expressions.
--
-- This projection deliberately stops before static-category resolution, duality,
-- and BinaryProtocolFamily construction. A bare or qualified unspecialized source
-- session reference becomes the same ReferencedGenericStaticActual carrier used
-- elsewhere in SURF-008; display spelling therefore remains unresolved identity,
-- not a resolved Session declaration or binder key. Specialized references fail
-- closed instead of losing their static arguments.
--
-- Generic parameters and requirements remain outside this closed fragment. In
-- particular, a source role referring to a protocol's own Session parameter must
-- be handled through explicit binder evidence rather than this unresolved-global
-- route. Role order and even duplicate role spelling are preserved here so later
-- competent role/duality checking, rather than this projection, owns rejection.
grammarV1ClosedProtocolRoleSessionReferences
  :: GrammarV1ProtocolDecl
  -> Maybe
      ( (ProtocolRoleKey, GenericStaticActual)
      , (ProtocolRoleKey, GenericStaticActual)
      )
grammarV1ClosedProtocolRoleSessionReferences source
  | not (null (grammarV1ProtocolGenericParams source)) = Nothing
  | not (null (grammarV1ProtocolRequirements source)) = Nothing
  | otherwise = case grammarV1ProtocolRoles source of
      [firstRole, secondRole] -> do
        first <- projectRole firstRole
        second <- projectRole secondRole
        pure (first, second)
      _ -> Nothing
  where
    projectRole (Located _ role) = case
        locatedValue (grammarV1RoleSessionExpression role) of
      GrammarV1SessionReference reference -> do
        actual <- grammarV1BareStaticReferenceActual
          (GrammarV1StaticReferenceArgument reference)
        pure
          ( ProtocolRoleKey (locatedValue (grammarV1RoleSessionName role))
          , actual
          )
      _ -> Nothing
