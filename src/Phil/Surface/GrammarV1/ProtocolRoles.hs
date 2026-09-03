module Phil.Surface.GrammarV1.ProtocolRoles
  ( grammarV1ClosedProtocolRoleTemplates
  ) where

import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Protocol.Family (ProtocolSessionTemplate)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ProtocolDecl (..)
  , GrammarV1RoleSessionDecl (..)
  )
import Phil.Surface.GrammarV1.SessionSemantics
  ( grammarV1PrimitiveSessionTemplate
  )
import Phil.Surface.Syntax (Located (..))

-- | Preserve the exact ordered pair of role-local sessions declared by one
-- closed Grammar-v1 protocol in the Core protocol-family template vocabulary.
-- Grammar v1 itself owns the binary source shape (exactly two role declarations),
-- but this bridge does not claim that the two sessions are dual and does not
-- synthesize declaration/interface identity. Generic parameters and requirements
-- remain outside this first closed protocol fragment.
grammarV1ClosedProtocolRoleTemplates
  :: GrammarV1ProtocolDecl
  -> Maybe
      ( (ProtocolRoleKey, ProtocolSessionTemplate)
      , (ProtocolRoleKey, ProtocolSessionTemplate)
      )
grammarV1ClosedProtocolRoleTemplates source
  | not (null (grammarV1ProtocolGenericParams source)) = Nothing
  | not (null (grammarV1ProtocolRequirements source)) = Nothing
  | otherwise = case grammarV1ProtocolRoles source of
      [firstRole, secondRole] -> do
        first <- projectRole firstRole
        second <- projectRole secondRole
        pure (first, second)
      _ -> Nothing
  where
    projectRole (Located _ role) = do
      session <- grammarV1PrimitiveSessionTemplate
        (locatedValue (grammarV1RoleSessionExpression role))
      pure
        ( ProtocolRoleKey (locatedValue (grammarV1RoleSessionName role))
        , session
        )
