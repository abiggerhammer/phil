module Phil.Surface.GrammarV1.SemanticProtocolRoles
  ( GrammarV1CheckedSemanticProtocolRoleError (..)
  , grammarV1CheckedSemanticProtocolRoleTemplates
  , grammarV1CheckedSemanticBinaryProtocolFamily
  ) where

import qualified Data.Set as Set
import Phil.Core.Focusing (FocusStep)
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Protocol.Family
  ( BinaryProtocolFamily (..)
  , ProtocolBranchTemplate (..)
  , ProtocolSessionTemplate (..)
  , ProtocolTypeTemplate (..)
  )
import Phil.Core.Session (dualSession)
import Phil.Core.Static
  ( DeclarationKey
  , InterfaceRevision
  , StaticContext
  )
import Phil.Core.Syntax
  ( Branch (..)
  , Session (..)
  )
import Phil.Core.Value (definitionallyEqualSession)
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ProtocolDecl (..)
  , GrammarV1RoleSessionDecl (..)
  )
import Phil.Surface.GrammarV1.ProtocolBinderScope
  ( GrammarV1CheckedProtocolBinderScope (..)
  , GrammarV1CheckedProtocolRoleScope (..)
  , GrammarV1ProtocolBinderScopeError
  , grammarV1CheckedProtocolBinderScope
  )
import Phil.Surface.GrammarV1.ProtocolRoles
  ( GrammarV1ProtocolRoleError (..)
  )
import Phil.Surface.GrammarV1.SemanticSessionSemantics
  ( GrammarV1SemanticSessionError
  , grammarV1CheckedSemanticSession
  )
import Phil.Surface.Syntax (Located (..))

-- | Checked protocol-role failures on the semantic binder path. Resolver/scope
-- failures remain distinct from role-local session checking and from the existing
-- Core-owned duplicate-role/duality relation.
data GrammarV1CheckedSemanticProtocolRoleError
  = GrammarV1CheckedSemanticProtocolBinderScopeError
      GrammarV1ProtocolBinderScopeError
  | GrammarV1CheckedSemanticProtocolRoleScopeCountMismatch Int
  | GrammarV1CheckedSemanticProtocolRoleScopeMismatch
      ProtocolRoleKey
      ProtocolRoleKey
  | GrammarV1CheckedSemanticProtocolRoleSessionError
      ProtocolRoleKey
      GrammarV1SemanticSessionError
  | GrammarV1CheckedSemanticProtocolRoleSemanticError
      GrammarV1ProtocolRoleError
  deriving (Eq, Show)

-- | Check a closed binary Grammar-v1 protocol by first obtaining the exact
-- declaration-keyed binder evidence for both roles and then elaborating each
-- local session through SemanticSessionSemantics. Source binder spellings remain
-- diagnostic only; the resulting Core sessions/templates carry generated names.
-- Core's existing alpha-aware session equality still owns duality, so different
-- generated names in the two role scopes do not create a false mismatch.
grammarV1CheckedSemanticProtocolRoleTemplates
  :: StaticContext
  -> DeclarationKey
  -> GrammarV1ProtocolDecl
  -> Maybe
      (Either
        GrammarV1CheckedSemanticProtocolRoleError
        ( ( (ProtocolRoleKey, ProtocolSessionTemplate)
          , (ProtocolRoleKey, ProtocolSessionTemplate)
          )
        , [FocusStep]
        ))
grammarV1CheckedSemanticProtocolRoleTemplates staticContext declarationKey source
  | not (null (grammarV1ProtocolGenericParams source)) = Nothing
  | not (null (grammarV1ProtocolRequirements source)) = Nothing
  | otherwise = case grammarV1ProtocolRoles source of
      [Located _ firstRole, Located _ secondRole] -> do
        checkedScope <- grammarV1CheckedProtocolBinderScope declarationKey source
        case checkedScope of
          Left scopeError -> pure
            (Left
              (GrammarV1CheckedSemanticProtocolBinderScopeError scopeError))
          Right scope -> case grammarV1CheckedProtocolRoles scope of
            [firstRoleScope, secondRoleScope] -> do
              let firstKey = ProtocolRoleKey
                    (locatedValue (grammarV1RoleSessionName firstRole))
                  secondKey = ProtocolRoleKey
                    (locatedValue (grammarV1RoleSessionName secondRole))
                  firstEvidenceKey = grammarV1CheckedProtocolRole firstRoleScope
                  secondEvidenceKey = grammarV1CheckedProtocolRole secondRoleScope
              if firstKey /= firstEvidenceKey
                then pure
                  (Left
                    (GrammarV1CheckedSemanticProtocolRoleScopeMismatch
                      firstKey firstEvidenceKey))
                else if secondKey /= secondEvidenceKey
                  then pure
                    (Left
                      (GrammarV1CheckedSemanticProtocolRoleScopeMismatch
                        secondKey secondEvidenceKey))
                  else do
                    firstChecked <- grammarV1CheckedSemanticSession
                      staticContext
                      firstKey
                      (grammarV1CheckedProtocolRoleBinders firstRoleScope)
                      (locatedValue (grammarV1RoleSessionExpression firstRole))
                    secondChecked <- grammarV1CheckedSemanticSession
                      staticContext
                      secondKey
                      (grammarV1CheckedProtocolRoleBinders secondRoleScope)
                      (locatedValue (grammarV1RoleSessionExpression secondRole))
                    pure $ do
                      (firstSession, firstSteps) <- mapSessionError firstKey firstChecked
                      (secondSession, secondSteps) <- mapSessionError secondKey secondChecked
                      if firstKey == secondKey
                        then Left
                          (GrammarV1CheckedSemanticProtocolRoleSemanticError
                            (DuplicateProtocolRole firstKey))
                        else if not
                            (definitionallyEqualSession
                              secondSession
                              (dualSession firstSession))
                          then Left
                            (GrammarV1CheckedSemanticProtocolRoleSemanticError
                              (NonDualProtocolRoles firstKey secondKey))
                          else Right
                            ( ( (firstKey, sessionTemplate firstSession)
                              , (secondKey, sessionTemplate secondSession)
                              )
                            , firstSteps <> secondSteps
                            )
            roles -> pure
              (Left
                (GrammarV1CheckedSemanticProtocolRoleScopeCountMismatch
                  (length roles)))
      _ -> Nothing

-- | Close the same checked semantic role pair into Core's binary family carrier
-- using caller-supplied stable declaration/interface identity. The peer session
-- is checked for duality before Core stores only the primary template, exactly as
-- on the legacy checked route.
grammarV1CheckedSemanticBinaryProtocolFamily
  :: StaticContext
  -> DeclarationKey
  -> InterfaceRevision
  -> GrammarV1ProtocolDecl
  -> Maybe
      (Either
        GrammarV1CheckedSemanticProtocolRoleError
        (BinaryProtocolFamily, [FocusStep]))
grammarV1CheckedSemanticBinaryProtocolFamily
    staticContext declarationKey interfaceRevision source = do
  checked <- grammarV1CheckedSemanticProtocolRoleTemplates
    staticContext declarationKey source
  pure $ fmap build checked
  where
    build
      ( ( (primaryRole, primarySession)
        , (peerRole, _peerSession)
        )
      , steps
      ) =
        ( BinaryProtocolFamily
            { protocolFamilyDeclarationKey = declarationKey
            , protocolFamilyInterfaceRevision = interfaceRevision
            , protocolFamilyRequirements = Set.empty
            , protocolFamilyPrimaryRole = primaryRole
            , protocolFamilyPeerRole = peerRole
            , protocolFamilyPrimarySession = primarySession
            }
        , steps
        )

mapSessionError
  :: ProtocolRoleKey
  -> Either GrammarV1SemanticSessionError a
  -> Either GrammarV1CheckedSemanticProtocolRoleError a
mapSessionError role = either
  (Left . GrammarV1CheckedSemanticProtocolRoleSessionError role)
  Right

sessionTemplate :: Session -> ProtocolSessionTemplate
sessionTemplate source = case source of
  Send binder ty continuation ->
    ProtocolTemplateSend binder (ProtocolConcreteType ty) (sessionTemplate continuation)
  Receive binder ty continuation ->
    ProtocolTemplateReceive binder (ProtocolConcreteType ty) (sessionTemplate continuation)
  Select branches -> ProtocolTemplateSelect (map branchTemplate branches)
  Offer branches -> ProtocolTemplateOffer (map branchTemplate branches)
  End outcome -> ProtocolTemplateEnd outcome
  Rec recursionName body ->
    ProtocolTemplateRec recursionName (sessionTemplate body)
  SessionVar variable -> ProtocolTemplateVar variable

branchTemplate :: Branch -> ProtocolBranchTemplate
branchTemplate branch = ProtocolBranchTemplate
  { protocolTemplateBranchLabel = branchLabel branch
  , protocolTemplateBranchPayload = fmap
      (\(binder, ty) -> (binder, ProtocolConcreteType ty))
      (branchPayload branch)
  , protocolTemplateBranchContinuation = sessionTemplate (branchContinuation branch)
  }
