module Phil.Surface.GrammarV1.ProtocolRoles
  ( GrammarV1ProtocolRoleError (..)
  , GrammarV1CheckedProtocolRoleError (..)
  , grammarV1ClosedProtocolRoleTemplates
  , grammarV1CheckedClosedProtocolRoleTemplates
  , grammarV1ClosedBinaryProtocolFamily
  , grammarV1CheckedProtocolRoleTemplates
  , grammarV1CheckedBinaryProtocolFamily
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
import Phil.Surface.GrammarV1.SessionSemantics
  ( GrammarV1CheckedSessionError
  , grammarV1CheckedSession
  , grammarV1PrimitiveSession
  , grammarV1PrimitiveSessionTemplate
  )
import Phil.Surface.Syntax (Located (..))

data GrammarV1ProtocolRoleError
  = DuplicateProtocolRole ProtocolRoleKey
  | NonDualProtocolRoles ProtocolRoleKey ProtocolRoleKey
  deriving (Eq, Show)

-- | Checked-role failures keep local-session elaboration separate from the
-- protocol-family relation. A richer payload can therefore fail in the exact role
-- where its type/focusing/binding failed, while duplicate-role and non-duality
-- rejection remain the already-established protocol semantic errors.
data GrammarV1CheckedProtocolRoleError
  = GrammarV1CheckedProtocolRoleSessionError
      ProtocolRoleKey GrammarV1CheckedSessionError
  | GrammarV1CheckedProtocolRoleSemanticError GrammarV1ProtocolRoleError
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
-- the second local session must be definitionally equal to the Core dual of the
-- first. Core's alpha-aware session equality owns binder renaming, so distinct
-- role-local source binder names do not become a false duality failure. Source
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
          else if not (definitionallyEqualSession secondSession (dualSession firstSession))
            then Left (NonDualProtocolRoles firstKey secondKey)
            else Right templates
    _ -> Nothing

-- | Construct the exact closed Core binary-family carrier once stable declaration
-- lineage and public-interface revision have been supplied by an authority above
-- Grammar v1. Source spelling and module location are intentionally ignored for
-- identity: Core's DeclarationKey is stable lineage, not a source-name hash. The
-- peer source session is first checked as the alpha-aware dual of the primary;
-- Core therefore stores only the primary template and derives the peer later at
-- instantiation. Closed Grammar-v1 protocols contribute no generic requirements.
grammarV1ClosedBinaryProtocolFamily
  :: DeclarationKey
  -> InterfaceRevision
  -> GrammarV1ProtocolDecl
  -> Maybe (Either GrammarV1ProtocolRoleError BinaryProtocolFamily)
grammarV1ClosedBinaryProtocolFamily declarationKey interfaceRevision source = do
  checked <- grammarV1CheckedClosedProtocolRoleTemplates source
  pure $ fmap buildFamily checked
  where
    buildFamily
      ( (primaryRole, primarySession)
      , (peerRole, _peerSession)
      ) = BinaryProtocolFamily
        { protocolFamilyDeclarationKey = declarationKey
        , protocolFamilyInterfaceRevision = interfaceRevision
        , protocolFamilyRequirements = Set.empty
        , protocolFamilyPrimaryRole = primaryRole
        , protocolFamilyPeerRole = peerRole
        , protocolFamilyPrimarySession = primarySession
        }

-- | Compose the broader checked local-session route into the existing binary
-- protocol relation without introducing a second duality semantics.
--
-- Both source roles are elaborated exactly once through 'grammarV1CheckedSession'
-- under the same caller-supplied StaticContext. Their exact Core Sessions are then
-- compared by the existing alpha-aware 'definitionallyEqualSession' against
-- 'dualSession'; this already carries binder renaming through dependent payload
-- types such as Bytes[len(payload)]. Successful sessions are converted structurally
-- to ProtocolSessionTemplate only after duality succeeds.
--
-- The focusing trace preserves source role order: all first-role steps precede all
-- second-role steps. Generic/requirement-bearing protocols and source session forms
-- outside the checked-session competence wall remain Nothing. No declaration
-- identity, binder identity, boundary/guard semantics, or family instantiation is
-- inferred here.
grammarV1CheckedProtocolRoleTemplates
  :: StaticContext
  -> GrammarV1ProtocolDecl
  -> Maybe
      (Either
        GrammarV1CheckedProtocolRoleError
        ( ( (ProtocolRoleKey, ProtocolSessionTemplate)
          , (ProtocolRoleKey, ProtocolSessionTemplate)
          )
        , [FocusStep]
        ))
grammarV1CheckedProtocolRoleTemplates staticContext source
  | not (null (grammarV1ProtocolGenericParams source)) = Nothing
  | not (null (grammarV1ProtocolRequirements source)) = Nothing
  | otherwise = case grammarV1ProtocolRoles source of
      [Located _ firstRole, Located _ secondRole] -> do
        let firstKey = ProtocolRoleKey
              (locatedValue (grammarV1RoleSessionName firstRole))
            secondKey = ProtocolRoleKey
              (locatedValue (grammarV1RoleSessionName secondRole))
        firstChecked <- grammarV1CheckedSession
          staticContext
          (locatedValue (grammarV1RoleSessionExpression firstRole))
        secondChecked <- grammarV1CheckedSession
          staticContext
          (locatedValue (grammarV1RoleSessionExpression secondRole))
        pure $ do
          (firstSession, firstSteps) <- mapSessionError firstKey firstChecked
          (secondSession, secondSteps) <- mapSessionError secondKey secondChecked
          if firstKey == secondKey
            then Left
              (GrammarV1CheckedProtocolRoleSemanticError
                (DuplicateProtocolRole firstKey))
            else if not
                (definitionallyEqualSession secondSession (dualSession firstSession))
              then Left
                (GrammarV1CheckedProtocolRoleSemanticError
                  (NonDualProtocolRoles firstKey secondKey))
              else Right
                ( ( (firstKey, checkedSessionTemplate firstSession)
                  , (secondKey, checkedSessionTemplate secondSession)
                  )
                , firstSteps <> secondSteps
                )
      _ -> Nothing

-- | Close one checked, dual richer-payload protocol into the existing Core family
-- carrier using caller-supplied stable identity. This adds no family semantics:
-- requirements remain empty for this closed source fragment, and the peer session
-- is still validated before only the primary template is retained by Core.
grammarV1CheckedBinaryProtocolFamily
  :: StaticContext
  -> DeclarationKey
  -> InterfaceRevision
  -> GrammarV1ProtocolDecl
  -> Maybe
      (Either
        GrammarV1CheckedProtocolRoleError
        (BinaryProtocolFamily, [FocusStep]))
grammarV1CheckedBinaryProtocolFamily
    staticContext declarationKey interfaceRevision source = do
  checked <- grammarV1CheckedProtocolRoleTemplates staticContext source
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
  -> Either GrammarV1CheckedSessionError a
  -> Either GrammarV1CheckedProtocolRoleError a
mapSessionError role = either
  (Left . GrammarV1CheckedProtocolRoleSessionError role)
  Right

checkedSessionTemplate :: Session -> ProtocolSessionTemplate
checkedSessionTemplate source = case source of
  Send binder ty continuation ->
    ProtocolTemplateSend
      binder
      (ProtocolConcreteType ty)
      (checkedSessionTemplate continuation)
  Receive binder ty continuation ->
    ProtocolTemplateReceive
      binder
      (ProtocolConcreteType ty)
      (checkedSessionTemplate continuation)
  Select branches -> ProtocolTemplateSelect (map checkedBranchTemplate branches)
  Offer branches -> ProtocolTemplateOffer (map checkedBranchTemplate branches)
  End outcome -> ProtocolTemplateEnd outcome
  Rec recursionName body ->
    ProtocolTemplateRec recursionName (checkedSessionTemplate body)
  SessionVar variable -> ProtocolTemplateVar variable

checkedBranchTemplate :: Branch -> ProtocolBranchTemplate
checkedBranchTemplate branch = ProtocolBranchTemplate
  { protocolTemplateBranchLabel = branchLabel branch
  , protocolTemplateBranchPayload = fmap
      (\(binder, ty) -> (binder, ProtocolConcreteType ty))
      (branchPayload branch)
  , protocolTemplateBranchContinuation =
      checkedSessionTemplate (branchContinuation branch)
  }
