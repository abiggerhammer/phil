module Phil.Surface.GrammarV1.ProtocolMessageTemplates
  ( GrammarV1ResolvedProtocolMessageParameter (..)
  , GrammarV1ResolvedProtocolMessageUse (..)
  , GrammarV1ProtocolMessageTemplateError (..)
  , grammarV1ResolvedMessageProtocolRoleTemplates
  ) where

import qualified Data.Set as Set
import Phil.Core.Generic (GenericStaticParameterKey)
import Phil.Core.Generic.StaticActual
  ( GenericStaticKind (..)
  , GenericStaticParameter (..)
  )
import Phil.Core.Protocol (ProtocolRoleKey (..))
import Phil.Core.Protocol.Family
  ( ProtocolBranchTemplate (..)
  , ProtocolSessionTemplate (..)
  , ProtocolTypeTemplate (..)
  )
import Phil.Core.Syntax (Name (..))
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.CallableSignature
  ( grammarV1InsertPrimitiveBinding
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1GenericKind (..)
  , GrammarV1GenericParam (..)
  , GrammarV1ProtocolDecl (..)
  , GrammarV1RoleSessionDecl (..)
  , GrammarV1SessionBranch (..)
  , GrammarV1SessionExpression (..)
  , GrammarV1StaticReference (..)
  , GrammarV1TermParam (..)
  , GrammarV1Type (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Exact binder-resolution evidence for one source protocol Message parameter.
-- The source occurrence is repeated so this bridge can require correspondence to
-- the parsed declaration without deriving a semantic key from display spelling.
-- The GenericStaticParameter itself is supplied by the competent binder/static
-- resolver; SURF-008 consumes it but does not manufacture it.
data GrammarV1ResolvedProtocolMessageParameter =
  GrammarV1ResolvedProtocolMessageParameter
    { resolvedProtocolMessageSourceParameter :: Located GrammarV1GenericParam
    , resolvedProtocolMessageParameter :: GenericStaticParameter
    }
  deriving (Eq, Show)

-- | Exact binder-resolution evidence for one source type occurrence that denotes
-- a declared Message parameter. Matching is by the full Located source occurrence,
-- not by its textual spelling, so this bridge performs no source-name lookup.
data GrammarV1ResolvedProtocolMessageUse = GrammarV1ResolvedProtocolMessageUse
  { resolvedProtocolMessageSourceType :: Located GrammarV1Type
  , resolvedProtocolMessageUseParameterKey :: GenericStaticParameterKey
  }
  deriving (Eq, Show)

data GrammarV1ProtocolMessageTemplateError
  = GrammarV1ProtocolMessageParameterEvidenceCountMismatch Int Int
  | GrammarV1ProtocolMessageParameterSourceMismatch
      Int
      (Located GrammarV1GenericParam)
      (Located GrammarV1GenericParam)
  | GrammarV1ProtocolMessageParameterKindMismatch
      GenericStaticParameterKey
      GenericStaticKind
  | GrammarV1DuplicateProtocolMessageParameterKey GenericStaticParameterKey
  | GrammarV1MissingProtocolMessageUseEvidence (Located GrammarV1Type)
  | GrammarV1DuplicateProtocolMessageUseEvidence (Located GrammarV1Type)
  | GrammarV1ProtocolMessageUseUndeclaredParameter GenericStaticParameterKey
  | GrammarV1UnexpectedProtocolMessageUseEvidence (Located GrammarV1Type)
  deriving (Eq, Show)

-- | Project the first parameterized Grammar-v1 protocol fragment into Core's
-- ProtocolSessionTemplate vocabulary while keeping static binder resolution
-- outside SURF-008.
--
-- This route is intentionally separate from the closed protocol-family route.
-- It requires at least one source generic parameter and every source parameter
-- must have Message kind. Caller-supplied parameter evidence must correspond to
-- the exact source parameter occurrences in declaration order, carry distinct
-- semantic keys, and retain GenericMessageKind. Every nonprimitive message type
-- use must be a bare unspecialized named type with exactly one caller-supplied
-- use-evidence entry tied to one declared semantic key. The source spelling is
-- never used to choose that key.
--
-- Unit/Bool/U<n> message positions continue to use the established primitive
-- type checker and become ProtocolConcreteType. Resolved Message-parameter uses
-- become ProtocolParameterType. Boundary/codec clauses, guards, static session
-- references, explicit empty or multi-value branch payloads, non-Message generic
-- parameters, generic requirements, and richer message types remain structural
-- non-competence (Nothing).
--
-- This slice does not check duality and does not construct or instantiate a
-- BinaryProtocolFamily. Those steps require a template-aware duality route and
-- later generic discharge/instantiation. SURF-009 remains authoritative for the
-- source-binder-to-GenericStaticParameterKey evidence consumed here.
grammarV1ResolvedMessageProtocolRoleTemplates
  :: [GrammarV1ResolvedProtocolMessageParameter]
  -> [GrammarV1ResolvedProtocolMessageUse]
  -> GrammarV1ProtocolDecl
  -> Maybe
      (Either
        GrammarV1ProtocolMessageTemplateError
        ( (ProtocolRoleKey, ProtocolSessionTemplate)
        , (ProtocolRoleKey, ProtocolSessionTemplate)
        ))
grammarV1ResolvedMessageProtocolRoleTemplates parameterEvidence useEvidence source
  | null sourceParameters = Nothing
  | not (all sourceParameterIsMessage sourceParameters) = Nothing
  | not (null (grammarV1ProtocolRequirements source)) = Nothing
  | otherwise = case grammarV1ProtocolRoles source of
      [firstRole, secondRole] -> do
        let checkedParameters = validateParameterEvidence
              sourceParameters parameterEvidence
        pure $ do
          parameterKeys <- checkedParameters
          (first, firstUses) <- projectRole parameterKeys useEvidence firstRole
          (second, secondUses) <- projectRole parameterKeys useEvidence secondRole
          let used = firstUses <> secondUses
          case firstUnexpectedUseEvidence used useEvidence of
            Just extra -> Left
              (GrammarV1UnexpectedProtocolMessageUseEvidence
                (resolvedProtocolMessageSourceType extra))
            Nothing -> Right (first, second)
      _ -> Nothing
  where
    sourceParameters = grammarV1ProtocolGenericParams source

sourceParameterIsMessage :: Located GrammarV1GenericParam -> Bool
sourceParameterIsMessage (Located _ parameter) =
  locatedValue (grammarV1GenericParamKind parameter) == GrammarV1MessageKind

validateParameterEvidence
  :: [Located GrammarV1GenericParam]
  -> [GrammarV1ResolvedProtocolMessageParameter]
  -> Either GrammarV1ProtocolMessageTemplateError (Set.Set GenericStaticParameterKey)
validateParameterEvidence sourceParameters evidence
  | length sourceParameters /= length evidence = Left
      (GrammarV1ProtocolMessageParameterEvidenceCountMismatch
        (length sourceParameters)
        (length evidence))
  | otherwise = go 0 Set.empty sourceParameters evidence
  where
    go _ keys [] [] = Right keys
    go index keys (sourceParameter : sourceRest) (resolved : resolvedRest)
      | sourceParameter /= resolvedProtocolMessageSourceParameter resolved = Left
          (GrammarV1ProtocolMessageParameterSourceMismatch
            index
            sourceParameter
            (resolvedProtocolMessageSourceParameter resolved))
      | genericStaticParameterKind parameter /= GenericMessageKind = Left
          (GrammarV1ProtocolMessageParameterKindMismatch
            key
            (genericStaticParameterKind parameter))
      | Set.member key keys = Left
          (GrammarV1DuplicateProtocolMessageParameterKey key)
      | otherwise = go
          (index + 1)
          (Set.insert key keys)
          sourceRest
          resolvedRest
      where
        parameter = resolvedProtocolMessageParameter resolved
        key = genericStaticParameterKey parameter
    go _ _ _ _ = error "protocol Message parameter evidence length guard failed"

projectRole
  :: Set.Set GenericStaticParameterKey
  -> [GrammarV1ResolvedProtocolMessageUse]
  -> Located GrammarV1RoleSessionDecl
  -> Either
      GrammarV1ProtocolMessageTemplateError
      ((ProtocolRoleKey, ProtocolSessionTemplate), [Located GrammarV1Type])
projectRole parameterKeys evidence (Located _ role) = do
  (session, used) <- maybe
    (error "parameterized protocol role escaped structural competence guard")
    id
    (projectSession
      Set.empty
      Set.empty
      emptySurfaceState
      parameterKeys
      evidence
      (locatedValue (grammarV1RoleSessionExpression role)))
  Right
    ( ( ProtocolRoleKey (locatedValue (grammarV1RoleSessionName role))
      , session
      )
    , used
    )

projectSession
  :: Set.Set Name
  -> Set.Set Name
  -> SurfaceState
  -> Set.Set GenericStaticParameterKey
  -> [GrammarV1ResolvedProtocolMessageUse]
  -> GrammarV1SessionExpression
  -> Maybe
      (Either
        GrammarV1ProtocolMessageTemplateError
        (ProtocolSessionTemplate, [Located GrammarV1Type]))
projectSession recursionNames binders state parameterKeys evidence source =
  case source of
    GrammarV1SessionReference _ -> Nothing
    GrammarV1SessionSend param Nothing Nothing continuation -> do
      projected <- projectMessageParameter binders state parameterKeys evidence param
      pure $ do
        ((binder, message), nextBinders, nextState, ownUses) <- projected
        successor <- maybe
          (error "parameterized send continuation escaped structural competence guard")
          id
          (projectSession
            recursionNames
            nextBinders
            nextState
            parameterKeys
            evidence
            (locatedValue continuation))
        let (continuationTemplate, continuationUses) = successor
        Right
          ( ProtocolTemplateSend binder message continuationTemplate
          , ownUses <> continuationUses
          )
    GrammarV1SessionSend _ _ _ _ -> Nothing
    GrammarV1SessionReceive param Nothing Nothing continuation -> do
      projected <- projectMessageParameter binders state parameterKeys evidence param
      pure $ do
        ((binder, message), nextBinders, nextState, ownUses) <- projected
        successor <- maybe
          (error "parameterized receive continuation escaped structural competence guard")
          id
          (projectSession
            recursionNames
            nextBinders
            nextState
            parameterKeys
            evidence
            (locatedValue continuation))
        let (continuationTemplate, continuationUses) = successor
        Right
          ( ProtocolTemplateReceive binder message continuationTemplate
          , ownUses <> continuationUses
          )
    GrammarV1SessionReceive _ _ _ _ -> Nothing
    GrammarV1SessionSelect branches -> do
      projected <- projectBranches
        recursionNames binders state parameterKeys evidence branches
      pure $ fmap
        (\(checked, used) -> (ProtocolTemplateSelect checked, used))
        projected
    GrammarV1SessionOffer branches -> do
      projected <- projectBranches
        recursionNames binders state parameterKeys evidence branches
      pure $ fmap
        (\(checked, used) -> (ProtocolTemplateOffer checked, used))
        projected
    GrammarV1SessionEnd outcome ->
      Just (Right (ProtocolTemplateEnd (Phil.Core.Syntax.Outcome (locatedValue outcome)), []))
    GrammarV1SessionRecursive recursionName body -> do
      let name = Name (locatedValue recursionName)
      projected <- projectSession
        (Set.insert name recursionNames)
        binders
        state
        parameterKeys
        evidence
        (locatedValue body)
      pure $ fmap
        (\(checked, used) -> (ProtocolTemplateRec name checked, used))
        projected
    GrammarV1SessionContinue recursionName ->
      let name = Name (locatedValue recursionName)
      in if Set.member name recursionNames
          then Just (Right (ProtocolTemplateVar name, []))
          else Nothing

projectBranches
  :: Set.Set Name
  -> Set.Set Name
  -> SurfaceState
  -> Set.Set GenericStaticParameterKey
  -> [GrammarV1ResolvedProtocolMessageUse]
  -> [Located GrammarV1SessionBranch]
  -> Maybe
      (Either
        GrammarV1ProtocolMessageTemplateError
        ([ProtocolBranchTemplate], [Located GrammarV1Type]))
projectBranches _ _ _ _ _ [] = Just (Right ([], []))
projectBranches recursionNames binders state parameterKeys evidence (branch : rest) = do
  first <- projectBranch recursionNames binders state parameterKeys evidence branch
  remaining <- projectBranches recursionNames binders state parameterKeys evidence rest
  pure $ do
    (firstBranch, firstUses) <- first
    (restBranches, restUses) <- remaining
    Right (firstBranch : restBranches, firstUses <> restUses)

projectBranch
  :: Set.Set Name
  -> Set.Set Name
  -> SurfaceState
  -> Set.Set GenericStaticParameterKey
  -> [GrammarV1ResolvedProtocolMessageUse]
  -> Located GrammarV1SessionBranch
  -> Maybe
      (Either
        GrammarV1ProtocolMessageTemplateError
        (ProtocolBranchTemplate, [Located GrammarV1Type]))
projectBranch recursionNames binders state parameterKeys evidence (Located _ branch)
  | grammarV1SessionBranchBoundary branch /= Nothing = Nothing
  | grammarV1SessionBranchGuard branch /= Nothing = Nothing
  | otherwise = do
      payload <- case grammarV1SessionBranchParams branch of
        Nothing -> Just (Right (Nothing, binders, state, []))
        Just [param] -> do
          projected <- projectMessageParameter binders state parameterKeys evidence param
          pure $ fmap
            (\((binder, message), nextBinders, nextState, used) ->
              (Just (binder, message), nextBinders, nextState, used))
            projected
        Just _ -> Nothing
      pure $ do
        (checkedPayload, nextBinders, nextState, payloadUses) <- payload
        continuation <- maybe
          (error "parameterized branch continuation escaped structural competence guard")
          id
          (projectSession
            recursionNames
            nextBinders
            nextState
            parameterKeys
            evidence
            (locatedValue (grammarV1SessionBranchContinuation branch)))
        let (continuationTemplate, continuationUses) = continuation
        Right
          ( ProtocolBranchTemplate
              { protocolTemplateBranchLabel =
                  locatedValue (grammarV1SessionBranchLabel branch)
              , protocolTemplateBranchPayload = checkedPayload
              , protocolTemplateBranchContinuation = continuationTemplate
              }
          , payloadUses <> continuationUses
          )

projectMessageParameter
  :: Set.Set Name
  -> SurfaceState
  -> Set.Set GenericStaticParameterKey
  -> [GrammarV1ResolvedProtocolMessageUse]
  -> Located GrammarV1TermParam
  -> Maybe
      (Either
        GrammarV1ProtocolMessageTemplateError
        ( (Name, ProtocolTypeTemplate)
        , Set.Set Name
        , SurfaceState
        , [Located GrammarV1Type]
        ))
projectMessageParameter binders state parameterKeys evidence (Located _ parameter)
  | Set.member binder binders = Nothing
  | primitiveType sourceType = do
      ((checkedBinder, ty), nextState) <- grammarV1InsertPrimitiveBinding
        (grammarV1TermParamName parameter)
        sourceType
        state
      Just (Right
        ( (checkedBinder, ProtocolConcreteType ty)
        , Set.insert checkedBinder binders
        , nextState
        , []
        ))
  | otherwise = case locatedValue sourceType of
      GrammarV1NamedType reference
        | null (grammarV1StaticReferenceArguments reference) ->
            Just $ case matchingEvidence sourceType evidence of
              [] -> Left (GrammarV1MissingProtocolMessageUseEvidence sourceType)
              [resolved]
                | not (Set.member key parameterKeys) -> Left
                    (GrammarV1ProtocolMessageUseUndeclaredParameter key)
                | otherwise -> Right
                    ( (binder, ProtocolParameterType key)
                    , Set.insert binder binders
                    , state
                    , [sourceType]
                    )
                where
                  key = resolvedProtocolMessageUseParameterKey resolved
              _ -> Left (GrammarV1DuplicateProtocolMessageUseEvidence sourceType)
      _ -> Nothing
  where
    sourceType = grammarV1TermParamType parameter
    binder = Name (locatedValue (grammarV1TermParamName parameter))

primitiveType :: Located GrammarV1Type -> Bool
primitiveType (Located _ sourceType) = case sourceType of
  GrammarV1UnitType -> True
  GrammarV1BoolType -> True
  GrammarV1UnsignedType _ -> True
  _ -> False

matchingEvidence
  :: Located GrammarV1Type
  -> [GrammarV1ResolvedProtocolMessageUse]
  -> [GrammarV1ResolvedProtocolMessageUse]
matchingEvidence sourceType = filter
  ((== sourceType) . resolvedProtocolMessageSourceType)

firstUnexpectedUseEvidence
  :: [Located GrammarV1Type]
  -> [GrammarV1ResolvedProtocolMessageUse]
  -> Maybe GrammarV1ResolvedProtocolMessageUse
firstUnexpectedUseEvidence used = firstUnexpected
  where
    firstUnexpected [] = Nothing
    firstUnexpected (entry : rest)
      | resolvedProtocolMessageSourceType entry `elem` used = firstUnexpected rest
      | otherwise = Just entry
