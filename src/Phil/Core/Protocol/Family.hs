{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Protocol.Family
  ( ProtocolTypeTemplate (..)
  , ProtocolBranchTemplate (..)
  , ProtocolSessionTemplate (..)
  , BinaryProtocolFamily (..)
  , ProtocolMessageArgument (..)
  , BinaryProtocolInstance (..)
  , ProtocolProjectionEvidence (..)
  , ProtocolFamilyError (..)
  , instantiateBinaryProtocol
  , projectProtocolRole
  , verifyProtocolProjection
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Text as Text
import Phil.Core.Generic
  ( GenericApplicationIdentity
  , GenericApplicationIdentityError
  , GenericInstantiationError
  , GenericInstantiationPolicy
  , GenericInstantiationRecord
  , GenericRequirement
  , GenericRequirementDisposition
  , GenericStaticParameterKey
  , checkGenericInstantiation
  , deriveGenericApplicationIdentity
  , genericApplicationSemanticForm
  )
import Phil.Core.Protocol
  ( ProtocolInstanceRevision (..)
  , ProtocolRoleKey (..)
  )
import Phil.Core.Session (dualSession)
import Phil.Core.Static
  ( DeclarationKey
  , InterfaceRevision
  , SemanticForm
  , canonicalSemanticForm
  )
import Phil.Core.Syntax
  ( Branch (..)
  , Name
  , Outcome
  , Session (..)
  , Ty
  )

-- | A protocol-family message position is either concrete or supplied by one
-- exact generic static parameter at instantiation time.
data ProtocolTypeTemplate
  = ProtocolConcreteType Ty
  | ProtocolParameterType GenericStaticParameterKey
  deriving (Eq, Ord, Show)

data ProtocolBranchTemplate = ProtocolBranchTemplate
  { protocolTemplateBranchLabel :: Text.Text
  , protocolTemplateBranchPayload :: Maybe (Name, ProtocolTypeTemplate)
  , protocolTemplateBranchContinuation :: ProtocolSessionTemplate
  }
  deriving (Eq, Ord, Show)

data ProtocolSessionTemplate
  = ProtocolTemplateSend Name ProtocolTypeTemplate ProtocolSessionTemplate
  | ProtocolTemplateReceive Name ProtocolTypeTemplate ProtocolSessionTemplate
  | ProtocolTemplateSelect [ProtocolBranchTemplate]
  | ProtocolTemplateOffer [ProtocolBranchTemplate]
  | ProtocolTemplateEnd Outcome
  | ProtocolTemplateRec Name ProtocolSessionTemplate
  | ProtocolTemplateVar Name
  deriving (Eq, Ord, Show)

-- | Bounded Phase-1 binary protocol family.  The family identity is the same
-- stable declaration/interface pair used by ordinary generic applications.
-- The peer projection is derived by exact session duality from the primary
-- projection, so accepted instances cannot carry an independently invented
-- non-dual peer session.
data BinaryProtocolFamily = BinaryProtocolFamily
  { protocolFamilyDeclarationKey :: DeclarationKey
  , protocolFamilyInterfaceRevision :: InterfaceRevision
  , protocolFamilyRequirements :: Set GenericRequirement
  , protocolFamilyPrimaryRole :: ProtocolRoleKey
  , protocolFamilyPeerRole :: ProtocolRoleKey
  , protocolFamilyPrimarySession :: ProtocolSessionTemplate
  }
  deriving (Eq, Ord, Show)

-- | One exact static message argument.  The semantic form is identity-bearing;
-- the type is what is substituted into the local session template.  Their
-- correspondence belongs to the ordinary generic/boundary admissibility layer,
-- not to the projection relation itself.
data ProtocolMessageArgument = ProtocolMessageArgument
  { protocolMessageArgumentKey :: GenericStaticParameterKey
  , protocolMessageArgumentType :: Ty
  , protocolMessageArgumentSemantics :: SemanticForm
  }
  deriving (Eq, Ord, Show)

data BinaryProtocolInstance = BinaryProtocolInstance
  { protocolInstanceApplicationIdentity :: GenericApplicationIdentity
  , protocolInstanceGenericDischarge :: GenericInstantiationRecord
  , binaryProtocolInstanceRevision :: ProtocolInstanceRevision
  , protocolInstanceRoleSessions :: Map ProtocolRoleKey Session
  }
  deriving (Eq, Ord, Show)

-- | Checked projection evidence is tied to one exact protocol instance, role,
-- and local session.  Equal local session syntax in another instance does not
-- make the evidence transferable.
data ProtocolProjectionEvidence = ProtocolProjectionEvidence
  { protocolProjectionInstance :: ProtocolInstanceRevision
  , protocolProjectionRole :: ProtocolRoleKey
  , protocolProjectionSession :: Session
  }
  deriving (Eq, Ord, Show)

data ProtocolFamilyError
  = ProtocolFamilyEmptyRole ProtocolRoleKey
  | ProtocolFamilyDuplicateRoles ProtocolRoleKey
  | DuplicateProtocolMessageArgument GenericStaticParameterKey
  | MissingProtocolMessageArgument GenericStaticParameterKey
  | ProtocolGenericInstantiationError GenericInstantiationError
  | ProtocolGenericApplicationIdentityError GenericApplicationIdentityError
  | UnknownProtocolProjectionRole ProtocolRoleKey [ProtocolRoleKey]
  | ProtocolProjectionInstanceMismatch ProtocolInstanceRevision ProtocolInstanceRevision
  | ProtocolProjectionSessionMismatch ProtocolRoleKey Session Session
  deriving (Eq, Show)

instantiateBinaryProtocol
  :: GenericInstantiationPolicy
  -> BinaryProtocolFamily
  -> [ProtocolMessageArgument]
  -> [(GenericRequirement, GenericRequirementDisposition)]
  -> Either ProtocolFamilyError BinaryProtocolInstance
instantiateBinaryProtocol policy family argumentEntries dispositions = do
  validateRoles family
  arguments <- normalizeArguments argumentEntries
  mapM_ (requireArgument arguments) (Set.toAscList (templateParameters (protocolFamilyPrimarySession family)))
  genericDischarge <- mapLeft ProtocolGenericInstantiationError $
    checkGenericInstantiation policy (protocolFamilyRequirements family) dispositions
  applicationIdentity <- mapLeft ProtocolGenericApplicationIdentityError $
    deriveGenericApplicationIdentity
      (protocolFamilyDeclarationKey family)
      (protocolFamilyInterfaceRevision family)
      [ (key, protocolMessageArgumentSemantics argument)
      | (key, argument) <- Map.toAscList arguments
      ]
  primarySession <- instantiateSessionTemplate arguments (protocolFamilyPrimarySession family)
  let peerSession = dualSession primarySession
      instanceRevision = deriveProtocolInstanceRevision applicationIdentity
      roleSessions = Map.fromList
        [ (protocolFamilyPrimaryRole family, primarySession)
        , (protocolFamilyPeerRole family, peerSession)
        ]
  Right BinaryProtocolInstance
    { protocolInstanceApplicationIdentity = applicationIdentity
    , protocolInstanceGenericDischarge = genericDischarge
    , binaryProtocolInstanceRevision = instanceRevision
    , protocolInstanceRoleSessions = roleSessions
    }

projectProtocolRole
  :: BinaryProtocolInstance
  -> ProtocolRoleKey
  -> Either ProtocolFamilyError ProtocolProjectionEvidence
projectProtocolRole instanceValue role = do
  session <- maybe
    (Left (UnknownProtocolProjectionRole role (Map.keys (protocolInstanceRoleSessions instanceValue))))
    Right
    (Map.lookup role (protocolInstanceRoleSessions instanceValue))
  Right ProtocolProjectionEvidence
    { protocolProjectionInstance = binaryProtocolInstanceRevision instanceValue
    , protocolProjectionRole = role
    , protocolProjectionSession = session
    }

verifyProtocolProjection
  :: BinaryProtocolInstance
  -> ProtocolProjectionEvidence
  -> Either ProtocolFamilyError ()
verifyProtocolProjection instanceValue evidence = do
  requireEqual
    ProtocolProjectionInstanceMismatch
    (binaryProtocolInstanceRevision instanceValue)
    (protocolProjectionInstance evidence)
  expectedSession <- maybe
    (Left (UnknownProtocolProjectionRole
      (protocolProjectionRole evidence)
      (Map.keys (protocolInstanceRoleSessions instanceValue))))
    Right
    (Map.lookup (protocolProjectionRole evidence) (protocolInstanceRoleSessions instanceValue))
  requireEqual
    (ProtocolProjectionSessionMismatch (protocolProjectionRole evidence))
    expectedSession
    (protocolProjectionSession evidence)

validateRoles :: BinaryProtocolFamily -> Either ProtocolFamilyError ()
validateRoles family
  | Text.null (unProtocolRoleKey primary) = Left (ProtocolFamilyEmptyRole primary)
  | Text.null (unProtocolRoleKey peer) = Left (ProtocolFamilyEmptyRole peer)
  | primary == peer = Left (ProtocolFamilyDuplicateRoles primary)
  | otherwise = Right ()
  where
    primary = protocolFamilyPrimaryRole family
    peer = protocolFamilyPeerRole family

normalizeArguments
  :: [ProtocolMessageArgument]
  -> Either ProtocolFamilyError (Map GenericStaticParameterKey ProtocolMessageArgument)
normalizeArguments = go Map.empty
  where
    go result [] = Right result
    go result (argument : rest)
      | Map.member key result = Left (DuplicateProtocolMessageArgument key)
      | otherwise = go (Map.insert key argument result) rest
      where
        key = protocolMessageArgumentKey argument

requireArgument
  :: Map GenericStaticParameterKey ProtocolMessageArgument
  -> GenericStaticParameterKey
  -> Either ProtocolFamilyError ()
requireArgument arguments key
  | Map.member key arguments = Right ()
  | otherwise = Left (MissingProtocolMessageArgument key)

instantiateSessionTemplate
  :: Map GenericStaticParameterKey ProtocolMessageArgument
  -> ProtocolSessionTemplate
  -> Either ProtocolFamilyError Session
instantiateSessionTemplate arguments template = case template of
  ProtocolTemplateSend binder message continuation ->
    Send binder
      <$> instantiateTypeTemplate arguments message
      <*> instantiateSessionTemplate arguments continuation
  ProtocolTemplateReceive binder message continuation ->
    Receive binder
      <$> instantiateTypeTemplate arguments message
      <*> instantiateSessionTemplate arguments continuation
  ProtocolTemplateSelect branches ->
    Select <$> mapM (instantiateBranch arguments) branches
  ProtocolTemplateOffer branches ->
    Offer <$> mapM (instantiateBranch arguments) branches
  ProtocolTemplateEnd outcome -> Right (End outcome)
  ProtocolTemplateRec recursionName body ->
    Rec recursionName <$> instantiateSessionTemplate arguments body
  ProtocolTemplateVar variable -> Right (SessionVar variable)

instantiateBranch
  :: Map GenericStaticParameterKey ProtocolMessageArgument
  -> ProtocolBranchTemplate
  -> Either ProtocolFamilyError Branch
instantiateBranch arguments branch = do
  payload <- case protocolTemplateBranchPayload branch of
    Nothing -> Right Nothing
    Just (binder, message) -> do
      ty <- instantiateTypeTemplate arguments message
      Right (Just (binder, ty))
  continuation <- instantiateSessionTemplate arguments (protocolTemplateBranchContinuation branch)
  Right Branch
    { branchLabel = protocolTemplateBranchLabel branch
    , branchPayload = payload
    , branchContinuation = continuation
    }

instantiateTypeTemplate
  :: Map GenericStaticParameterKey ProtocolMessageArgument
  -> ProtocolTypeTemplate
  -> Either ProtocolFamilyError Ty
instantiateTypeTemplate _ (ProtocolConcreteType ty) = Right ty
instantiateTypeTemplate arguments (ProtocolParameterType key) =
  maybe
    (Left (MissingProtocolMessageArgument key))
    (Right . protocolMessageArgumentType)
    (Map.lookup key arguments)

templateParameters :: ProtocolSessionTemplate -> Set GenericStaticParameterKey
templateParameters template = case template of
  ProtocolTemplateSend _ message continuation ->
    Set.union (typeTemplateParameters message) (templateParameters continuation)
  ProtocolTemplateReceive _ message continuation ->
    Set.union (typeTemplateParameters message) (templateParameters continuation)
  ProtocolTemplateSelect branches -> branchParameters branches
  ProtocolTemplateOffer branches -> branchParameters branches
  ProtocolTemplateEnd _ -> Set.empty
  ProtocolTemplateRec _ body -> templateParameters body
  ProtocolTemplateVar _ -> Set.empty

branchParameters :: [ProtocolBranchTemplate] -> Set GenericStaticParameterKey
branchParameters = Set.unions . map oneBranch
  where
    oneBranch branch = Set.union
      (maybe Set.empty (typeTemplateParameters . snd) (protocolTemplateBranchPayload branch))
      (templateParameters (protocolTemplateBranchContinuation branch))

typeTemplateParameters :: ProtocolTypeTemplate -> Set GenericStaticParameterKey
typeTemplateParameters message = case message of
  ProtocolConcreteType _ -> Set.empty
  ProtocolParameterType key -> Set.singleton key

deriveProtocolInstanceRevision :: GenericApplicationIdentity -> ProtocolInstanceRevision
deriveProtocolInstanceRevision applicationIdentity = ProtocolInstanceRevision
  ("phil.protocol.instance.canonical.v1:"
    <> canonicalSemanticForm (genericApplicationSemanticForm applicationIdentity))

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual constructor expected actual
  | expected == actual = Right ()
  | otherwise = Left (constructor expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
