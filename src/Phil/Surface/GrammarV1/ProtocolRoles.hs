module Phil.Surface.GrammarV1.ProtocolRoles
  ( GrammarV1ProtocolRoleError (..)
  , grammarV1ClosedProtocolRoleTemplates
  , grammarV1CheckedClosedProtocolRoleTemplates
  ) where

import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Protocol.Family (ProtocolSessionTemplate)
import Phil.Core.Session (dualSession)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ProtocolDecl (..)
  , GrammarV1RoleSessionDecl (..)
  )
import Phil.Surface.GrammarV1.SessionSemantics
  ( grammarV1PrimitiveSession
  , grammarV1PrimitiveSessionTemplate
  )
import Phil.Surface.Syntax (Located (..))

data GrammarV1ProtocolRoleError
  = DuplicateProtocolRole ProtocolRoleKey
  | NonDualProtocolRoles ProtocolRoleKey ProtocolRoleKey
  deriving (Eq, Show)

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

-- | Validate the closed role pair against the semantic constraints already
-- owned by Core's binary protocol family: the two roles must be distinct, and
-- the second local session must be exactly the Core dual of the first. Source
-- outside the bounded closed/primitive fragment remains Nothing; an admitted
-- source pair that violates role identity or duality is a distinct Left. No
-- declaration/interface identity or protocol-instance revision is synthesized.
grammarV1CheckedClosedProtocolRoleTemplates
  :: GrammarV1ProtocolDecl
  -> Maybe
      (Either
        GrammarV1ProtocolRoleError
        ( (ProtocolRoleKey, ProtocolSessionTemplate)
        , (ProtocolRoleKey, ProtocolSessionTemplate)
        ))
grammarV1CheckedClosedProtocolRoleTemplates source = do
  templates@((firstKey, _), (secondKey, _)) <-
    grammarV1ClosedProtocolRoleTemplates source
  case grammarV1ProtocolRoles source of
    [Located _ firstRole, Located _ secondRole] -> do
      firstSession <- grammarV1PrimitiveSession
        (locatedValue (grammarV1RoleSessionExpression firstRole))
      secondSession <- grammarV1PrimitiveSession
        (locatedValue (grammarV1RoleSessionExpression secondRole))
      pure $
        if firstKey == secondKey
          then Left (DuplicateProtocolRole firstKey)
          else if secondSession /= dualSession firstSession
            then Left (NonDualProtocolRoles firstKey secondKey)
            else Right templates
    _ -> Nothing
