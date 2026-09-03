module Phil.Surface.GrammarV1.ParameterizedProtocolFamily
  ( GrammarV1ParameterizedProtocolFamilyError (..)
  , grammarV1ResolvedMessageBinaryProtocolFamily
  ) where

import qualified Data.Set as Set
import Phil.Core.Protocol.Family
  ( BinaryProtocolFamily (..)
  , ProtocolBranchTemplate (..)
  , ProtocolSessionTemplate (..)
  , ProtocolTypeTemplate
  )
import Phil.Core.Static
  ( DeclarationKey
  , InterfaceRevision
  )
import Phil.Core.Syntax (Name)
import Phil.Surface.GrammarV1.Parser (GrammarV1ProtocolDecl)
import Phil.Surface.GrammarV1.ProtocolMessageTemplates
  ( GrammarV1ProtocolMessageTemplateError
  , GrammarV1ResolvedProtocolMessageParameter
  , GrammarV1ResolvedProtocolMessageUse
  , grammarV1ResolvedMessageProtocolRoleTemplates
  )
import Phil.Surface.GrammarV1.ProtocolRoles
  ( GrammarV1ProtocolRoleError (..)
  )

data GrammarV1ParameterizedProtocolFamilyError
  = GrammarV1ParameterizedProtocolTemplateError
      GrammarV1ProtocolMessageTemplateError
  | GrammarV1ParameterizedProtocolRoleError
      GrammarV1ProtocolRoleError
  deriving (Eq, Show)

-- | Construct the first parameterized Grammar-v1 binary protocol family from
-- exact Message-binder evidence and stable caller-supplied declaration identity.
--
-- All source-to-template work remains owned by
-- 'grammarV1ResolvedMessageProtocolRoleTemplates'. This layer checks only the
-- semantic constraints needed to turn that exact ordered role pair into Core's
-- 'BinaryProtocolFamily': role keys must be distinct and the peer template must
-- be the structural dual of the primary template modulo local term-binder and
-- recursion-binder alpha-renaming. ProtocolTypeTemplate payloads themselves are
-- compared exactly, so distinct GenericStaticParameterKey identities cannot be
-- collapsed merely because source spellings look alike.
--
-- The bounded #640 template vocabulary makes this alpha rule exact: term binder
-- names never occur inside ProtocolTypeTemplate, while recursion variables are
-- explicit ProtocolTemplateVar nodes. Branch labels, outcomes, concrete types,
-- and Message parameter keys therefore remain semantically visible. Generic
-- requirements remain empty because #640 rejects requirement-bearing protocols.
--
-- This function does not resolve binders, instantiate Message arguments,
-- discharge generic requirements, derive a protocol instance revision, or
-- project a runtime role. Core's ordinary instantiation/projection path retains
-- authority for those later steps.
grammarV1ResolvedMessageBinaryProtocolFamily
  :: DeclarationKey
  -> InterfaceRevision
  -> [GrammarV1ResolvedProtocolMessageParameter]
  -> [GrammarV1ResolvedProtocolMessageUse]
  -> GrammarV1ProtocolDecl
  -> Maybe
      (Either
        GrammarV1ParameterizedProtocolFamilyError
        BinaryProtocolFamily)
grammarV1ResolvedMessageBinaryProtocolFamily
    declarationKey interfaceRevision parameterEvidence useEvidence source = do
  projected <- grammarV1ResolvedMessageProtocolRoleTemplates
    parameterEvidence useEvidence source
  pure $ case projected of
    Left err -> Left (GrammarV1ParameterizedProtocolTemplateError err)
    Right
      ( (primaryRole, primarySession)
      , (peerRole, peerSession)
      )
      | primaryRole == peerRole -> Left
          (GrammarV1ParameterizedProtocolRoleError
            (DuplicateProtocolRole primaryRole))
      | not (dualTemplates [] primarySession peerSession) -> Left
          (GrammarV1ParameterizedProtocolRoleError
            (NonDualProtocolRoles primaryRole peerRole))
      | otherwise -> Right BinaryProtocolFamily
          { protocolFamilyDeclarationKey = declarationKey
          , protocolFamilyInterfaceRevision = interfaceRevision
          , protocolFamilyRequirements = Set.empty
          , protocolFamilyPrimaryRole = primaryRole
          , protocolFamilyPeerRole = peerRole
          , protocolFamilyPrimarySession = primarySession
          }

-- The environment maps a recursion binder in the primary template to the exact
-- alpha-corresponding binder in the peer template. Term message binders can be
-- ignored in this bounded vocabulary because ProtocolTypeTemplate contains no
-- term references.
dualTemplates
  :: [(Name, Name)]
  -> ProtocolSessionTemplate
  -> ProtocolSessionTemplate
  -> Bool
dualTemplates recursionEnvironment primary peer = case (primary, peer) of
  ( ProtocolTemplateSend _ primaryType primaryContinuation
    , ProtocolTemplateReceive _ peerType peerContinuation
    ) ->
      primaryType == peerType
        && dualTemplates recursionEnvironment primaryContinuation peerContinuation
  ( ProtocolTemplateReceive _ primaryType primaryContinuation
    , ProtocolTemplateSend _ peerType peerContinuation
    ) ->
      primaryType == peerType
        && dualTemplates recursionEnvironment primaryContinuation peerContinuation
  (ProtocolTemplateSelect primaryBranches, ProtocolTemplateOffer peerBranches) ->
    dualBranches recursionEnvironment primaryBranches peerBranches
  (ProtocolTemplateOffer primaryBranches, ProtocolTemplateSelect peerBranches) ->
    dualBranches recursionEnvironment primaryBranches peerBranches
  (ProtocolTemplateEnd primaryOutcome, ProtocolTemplateEnd peerOutcome) ->
    primaryOutcome == peerOutcome
  ( ProtocolTemplateRec primaryName primaryBody
    , ProtocolTemplateRec peerName peerBody
    ) ->
      dualTemplates
        ((primaryName, peerName) : recursionEnvironment)
        primaryBody
        peerBody
  (ProtocolTemplateVar primaryName, ProtocolTemplateVar peerName) ->
    lookup primaryName recursionEnvironment == Just peerName
  _ -> False

dualBranches
  :: [(Name, Name)]
  -> [ProtocolBranchTemplate]
  -> [ProtocolBranchTemplate]
  -> Bool
dualBranches _ [] [] = True
dualBranches recursionEnvironment (primary : primaryRest) (peer : peerRest) =
  protocolTemplateBranchLabel primary == protocolTemplateBranchLabel peer
    && dualPayload
      (protocolTemplateBranchPayload primary)
      (protocolTemplateBranchPayload peer)
    && dualTemplates
      recursionEnvironment
      (protocolTemplateBranchContinuation primary)
      (protocolTemplateBranchContinuation peer)
    && dualBranches recursionEnvironment primaryRest peerRest
dualBranches _ _ _ = False

dualPayload
  :: Maybe (Name, ProtocolTypeTemplate)
  -> Maybe (Name, ProtocolTypeTemplate)
  -> Bool
dualPayload Nothing Nothing = True
dualPayload (Just (_, primaryType)) (Just (_, peerType)) =
  primaryType == peerType
dualPayload _ _ = False
