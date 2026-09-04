module Phil.Surface.GrammarV1.ProtocolBinderScope
  ( GrammarV1ProtocolBinderSite (..)
  , GrammarV1CheckedProtocolBinder (..)
  , GrammarV1CheckedProtocolGuard (..)
  , GrammarV1CheckedProtocolRoleScope (..)
  , GrammarV1CheckedProtocolBinderScope (..)
  , GrammarV1ProtocolBinderScopeError (..)
  , grammarV1CheckedProtocolBinderScope
  ) where

import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Static (DeclarationKey)
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind
      ( GrammarV1ProtocolBranchPayloadBinder
      , GrammarV1ProtocolMessageBinder
      )
  , GrammarV1BinderScopeError
  , GrammarV1LexicalScope
  , GrammarV1ResolvedBinder
  , grammarV1BindLocal
  , grammarV1EnterLexicalScope
  , grammarV1LeaveLexicalScope
  , grammarV1RootLexicalScope
  )
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference
  , GrammarV1LexicalReferenceError
  , grammarV1CheckedPropositionReferences
  , grammarV1CheckedTypeReferences
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1ProtocolDecl (..)
  , GrammarV1Proposition
  , GrammarV1RoleSessionDecl (..)
  , GrammarV1SessionBranch (..)
  , GrammarV1SessionExpression (..)
  , GrammarV1TermParam (..)
  )
import Phil.Surface.GrammarV1.ProtocolGuardAnnotations
  ( GrammarV1ProtocolGuardSite (..)
  )
import Phil.Surface.Syntax (Located (..))

data GrammarV1ProtocolBinderSite
  = GrammarV1SendMessageBinder
  | GrammarV1ReceiveMessageBinder
  | GrammarV1SelectBranchPayloadBinder Text
  | GrammarV1OfferBranchPayloadBinder Text
  deriving (Eq, Show)

data GrammarV1CheckedProtocolBinder = GrammarV1CheckedProtocolBinder
  { grammarV1CheckedProtocolBinderRole :: ProtocolRoleKey
  , grammarV1CheckedProtocolBinderSite :: GrammarV1ProtocolBinderSite
  , grammarV1CheckedProtocolBinderSource :: Located GrammarV1TermParam
  , grammarV1CheckedProtocolBinderResolved :: GrammarV1ResolvedBinder
  , grammarV1CheckedProtocolBinderTypeReferences :: [GrammarV1CheckedLexicalReference]
  }
  deriving (Eq, Show)

data GrammarV1CheckedProtocolGuard = GrammarV1CheckedProtocolGuard
  { grammarV1CheckedProtocolGuardRole :: ProtocolRoleKey
  , grammarV1CheckedProtocolGuardSite :: GrammarV1ProtocolGuardSite
  , grammarV1CheckedProtocolGuardSource :: Located GrammarV1Proposition
  , grammarV1CheckedProtocolGuardReferences :: [GrammarV1CheckedLexicalReference]
  }
  deriving (Eq, Show)

data GrammarV1CheckedProtocolRoleScope = GrammarV1CheckedProtocolRoleScope
  { grammarV1CheckedProtocolRole :: ProtocolRoleKey
  , grammarV1CheckedProtocolRoleBinders :: [GrammarV1CheckedProtocolBinder]
  , grammarV1CheckedProtocolRoleGuards :: [GrammarV1CheckedProtocolGuard]
  }
  deriving (Eq, Show)

data GrammarV1CheckedProtocolBinderScope = GrammarV1CheckedProtocolBinderScope
  { grammarV1CheckedProtocolRoles :: [GrammarV1CheckedProtocolRoleScope]
  , grammarV1CheckedProtocolFinalScope :: GrammarV1LexicalScope
  }
  deriving (Eq, Show)

data GrammarV1ProtocolBinderScopeError
  = GrammarV1ProtocolBinderError GrammarV1BinderScopeError
  | GrammarV1ProtocolReferenceError GrammarV1LexicalReferenceError
  deriving (Eq, Show)

-- | Establish message/payload binder identity and exact lexical visibility for
-- every role in one Grammar-v1 protocol declaration. Send/receive binders remain
-- active through their role continuation. Each select/offer branch is a disjoint
-- child scope, so payloads and later branch-local message binders close before the
-- next sibling. Guard propositions are reference-resolved only; Core proposition
-- checking awaits the semantic-name-aware SurfaceState migration.
grammarV1CheckedProtocolBinderScope
  :: DeclarationKey
  -> GrammarV1ProtocolDecl
  -> Maybe (Either GrammarV1ProtocolBinderScopeError GrammarV1CheckedProtocolBinderScope)
grammarV1CheckedProtocolBinderScope declarationKey protocol = do
  rolesResult <- checkedRoles
    (grammarV1RootLexicalScope declarationKey)
    (grammarV1ProtocolRoles protocol)
  pure $ fmap
    (\(roles, finalScope) -> GrammarV1CheckedProtocolBinderScope
      { grammarV1CheckedProtocolRoles = roles
      , grammarV1CheckedProtocolFinalScope = finalScope
      })
    rolesResult

checkedRoles
  :: GrammarV1LexicalScope
  -> [Located GrammarV1RoleSessionDecl]
  -> Maybe (Either GrammarV1ProtocolBinderScopeError ([GrammarV1CheckedProtocolRoleScope], GrammarV1LexicalScope))
checkedRoles scope [] = Just (Right ([], scope))
checkedRoles scope (Located _ role : rest) = do
  let roleKey = ProtocolRoleKey (locatedValue (grammarV1RoleSessionName role))
      roleScope = grammarV1EnterLexicalScope scope
  sessionResult <- checkedSession roleKey roleScope (locatedValue (grammarV1RoleSessionExpression role))
  case sessionResult of
    Left scopeError -> Just (Left scopeError)
    Right (binders, guards, finalRoleScope) ->
      case grammarV1LeaveLexicalScope finalRoleScope of
        Left scopeError -> Just (Left (GrammarV1ProtocolBinderError scopeError))
        Right nextRoot -> do
          restResult <- checkedRoles nextRoot rest
          Just $ fmap
            (\(checkedRest, finalScope) ->
              ( GrammarV1CheckedProtocolRoleScope
                  { grammarV1CheckedProtocolRole = roleKey
                  , grammarV1CheckedProtocolRoleBinders = binders
                  , grammarV1CheckedProtocolRoleGuards = guards
                  }
                : checkedRest
              , finalScope
              ))
            restResult

checkedSession
  :: ProtocolRoleKey
  -> GrammarV1LexicalScope
  -> GrammarV1SessionExpression
  -> Maybe (Either GrammarV1ProtocolBinderScopeError ([GrammarV1CheckedProtocolBinder], [GrammarV1CheckedProtocolGuard], GrammarV1LexicalScope))
checkedSession roleKey scope source = case source of
  GrammarV1SessionReference _ -> Just (Right ([], [], scope))
  GrammarV1SessionSend parameter _ guard continuation ->
    checkedMessage roleKey GrammarV1SendMessageBinder GrammarV1SendGuard scope parameter guard continuation
  GrammarV1SessionReceive parameter _ guard continuation ->
    checkedMessage roleKey GrammarV1ReceiveMessageBinder GrammarV1ReceiveGuard scope parameter guard continuation
  GrammarV1SessionSelect branches -> checkedBranches True roleKey scope branches
  GrammarV1SessionOffer branches -> checkedBranches False roleKey scope branches
  GrammarV1SessionEnd _ -> Just (Right ([], [], scope))
  GrammarV1SessionRecursive _ body -> checkedSession roleKey scope (locatedValue body)
  GrammarV1SessionContinue _ -> Just (Right ([], [], scope))

checkedMessage
  :: ProtocolRoleKey
  -> GrammarV1ProtocolBinderSite
  -> GrammarV1ProtocolGuardSite
  -> GrammarV1LexicalScope
  -> Located GrammarV1TermParam
  -> Maybe (Located GrammarV1Proposition)
  -> Located GrammarV1SessionExpression
  -> Maybe (Either GrammarV1ProtocolBinderScopeError ([GrammarV1CheckedProtocolBinder], [GrammarV1CheckedProtocolGuard], GrammarV1LexicalScope))
checkedMessage roleKey binderSite guardSite scope source@(Located _ parameter) guard continuation = do
  let sourceName = grammarV1TermParamName parameter
      pendingSelf = Set.singleton (locatedValue sourceName)
  typeResult <- protocolReferences
    (grammarV1CheckedTypeReferences pendingSelf scope (grammarV1TermParamType parameter))
  case typeResult of
    Left scopeError -> Just (Left scopeError)
    Right typeReferences ->
      case grammarV1BindLocal GrammarV1ProtocolMessageBinder sourceName scope of
        Left scopeError -> Just (Left (GrammarV1ProtocolBinderError scopeError))
        Right (binder, boundScope) -> do
          guardResult <- checkedGuard roleKey guardSite boundScope guard
          case guardResult of
            Left scopeError -> Just (Left scopeError)
            Right guards -> do
              continuationResult <- checkedSession roleKey boundScope (locatedValue continuation)
              Just $ fmap
                (\(restBinders, restGuards, finalScope) ->
                  ( GrammarV1CheckedProtocolBinder roleKey binderSite source binder typeReferences : restBinders
                  , guards <> restGuards
                  , finalScope
                  ))
                continuationResult

checkedBranches
  :: Bool
  -> ProtocolRoleKey
  -> GrammarV1LexicalScope
  -> [Located GrammarV1SessionBranch]
  -> Maybe (Either GrammarV1ProtocolBinderScopeError ([GrammarV1CheckedProtocolBinder], [GrammarV1CheckedProtocolGuard], GrammarV1LexicalScope))
checkedBranches _ _ scope [] = Just (Right ([], [], scope))
checkedBranches selecting roleKey scope (source : rest) = do
  firstResult <- checkedBranch selecting roleKey scope source
  case firstResult of
    Left scopeError -> Just (Left scopeError)
    Right (firstBinders, firstGuards, afterFirst) -> do
      restResult <- checkedBranches selecting roleKey afterFirst rest
      Just $ fmap
        (\(restBinders, restGuards, finalScope) ->
          (firstBinders <> restBinders, firstGuards <> restGuards, finalScope))
        restResult

checkedBranch
  :: Bool
  -> ProtocolRoleKey
  -> GrammarV1LexicalScope
  -> Located GrammarV1SessionBranch
  -> Maybe (Either GrammarV1ProtocolBinderScopeError ([GrammarV1CheckedProtocolBinder], [GrammarV1CheckedProtocolGuard], GrammarV1LexicalScope))
checkedBranch selecting roleKey parentScope (Located _ branch) = do
  let label = locatedValue (grammarV1SessionBranchLabel branch)
      binderSite
        | selecting = GrammarV1SelectBranchPayloadBinder label
        | otherwise = GrammarV1OfferBranchPayloadBinder label
      guardSite
        | selecting = GrammarV1SelectBranchGuard label
        | otherwise = GrammarV1OfferBranchGuard label
      childScope = grammarV1EnterLexicalScope parentScope
      parameters = maybe [] id (grammarV1SessionBranchParams branch)
  payloadResult <- checkedPayloadParameters roleKey binderSite childScope parameters
  case payloadResult of
    Left scopeError -> Just (Left scopeError)
    Right (payloadBinders, boundScope) -> do
      guardResult <- checkedGuard roleKey guardSite boundScope (grammarV1SessionBranchGuard branch)
      case guardResult of
        Left scopeError -> Just (Left scopeError)
        Right guards -> do
          continuationResult <- checkedSession roleKey boundScope (locatedValue (grammarV1SessionBranchContinuation branch))
          case continuationResult of
            Left scopeError -> Just (Left scopeError)
            Right (restBinders, restGuards, finalChildScope) ->
              case grammarV1LeaveLexicalScope finalChildScope of
                Left scopeError -> Just (Left (GrammarV1ProtocolBinderError scopeError))
                Right nextParent -> Just (Right
                  (payloadBinders <> restBinders, guards <> restGuards, nextParent))

checkedPayloadParameters
  :: ProtocolRoleKey
  -> GrammarV1ProtocolBinderSite
  -> GrammarV1LexicalScope
  -> [Located GrammarV1TermParam]
  -> Maybe (Either GrammarV1ProtocolBinderScopeError ([GrammarV1CheckedProtocolBinder], GrammarV1LexicalScope))
checkedPayloadParameters roleKey site scope parameters = go parameterNames scope parameters
  where
    parameterNames = map (locatedValue . grammarV1TermParamName . locatedValue) parameters

    go _ currentScope [] = Just (Right ([], currentScope))
    go pendingNames currentScope (source@(Located _ parameter) : rest) = do
      typeResult <- protocolReferences
        (grammarV1CheckedTypeReferences (Set.fromList pendingNames) currentScope (grammarV1TermParamType parameter))
      case typeResult of
        Left scopeError -> Just (Left scopeError)
        Right typeReferences ->
          case grammarV1BindLocal GrammarV1ProtocolBranchPayloadBinder (grammarV1TermParamName parameter) currentScope of
            Left scopeError -> Just (Left (GrammarV1ProtocolBinderError scopeError))
            Right (binder, nextScope) -> do
              restResult <- go (drop 1 pendingNames) nextScope rest
              Just $ fmap
                (\(restBinders, finalScope) ->
                  (GrammarV1CheckedProtocolBinder roleKey site source binder typeReferences : restBinders, finalScope))
                restResult

checkedGuard
  :: ProtocolRoleKey
  -> GrammarV1ProtocolGuardSite
  -> GrammarV1LexicalScope
  -> Maybe (Located GrammarV1Proposition)
  -> Maybe (Either GrammarV1ProtocolBinderScopeError [GrammarV1CheckedProtocolGuard])
checkedGuard _ _ _ Nothing = Just (Right [])
checkedGuard roleKey site scope (Just proposition) = do
  referencesResult <- protocolReferences
    (grammarV1CheckedPropositionReferences Set.empty scope proposition)
  Just $ fmap
    (\references -> [GrammarV1CheckedProtocolGuard roleKey site proposition references])
    referencesResult

protocolReferences
  :: Maybe (Either GrammarV1LexicalReferenceError [GrammarV1CheckedLexicalReference])
  -> Maybe (Either GrammarV1ProtocolBinderScopeError [GrammarV1CheckedLexicalReference])
protocolReferences = fmap $ either (Left . GrammarV1ProtocolReferenceError) Right
