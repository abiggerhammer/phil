module Phil.Surface.GrammarV1.SemanticSessionSemantics
  ( GrammarV1SemanticSessionError (..)
  , grammarV1CheckedSemanticSession
  , grammarV1CheckedSemanticSessionTemplate
  ) where

import qualified Data.Set as Set
import Phil.Core.CheckedBindingMode
  ( CheckedTypeMode (..)
  )
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
import Phil.Core.Protocol (ProtocolRoleKey)
import Phil.Core.Protocol.Family
  ( ProtocolBranchTemplate (..)
  , ProtocolSessionTemplate (..)
  , ProtocolTypeTemplate (..)
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax
  ( Branch (..)
  , Name (..)
  , Outcome (..)
  , Session (..)
  , Ty
  )
import Phil.Surface.Check.Support
  ( emptySurfaceState
  , shapeForType
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceCheckError
  , SurfaceState
  )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1ResolvedBinder (..)
  )
import Phil.Surface.GrammarV1.CheckedType
  ( grammarV1CheckedTypeMode
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1SessionBranch (..)
  , GrammarV1SessionExpression (..)
  , GrammarV1TermParam (..)
  , GrammarV1Type
  )
import Phil.Surface.GrammarV1.ProtocolBinderScope
  ( GrammarV1CheckedProtocolBinder (..)
  , GrammarV1ProtocolBinderSite (..)
  )
import Phil.Surface.GrammarV1.SemanticBindingState
  ( grammarV1InsertSemanticBinding
  , grammarV1RewriteTypeReferences
  )
import Phil.Surface.Syntax (Located (..))

-- | Failures after exact protocol binder evidence has already been supplied by
-- ProtocolBinderScope. Unsupported session source shapes remain 'Nothing'; an
-- admitted shape with missing/misordered evidence, failed exact type rewriting,
-- Core focusing failure, or semantic binding insertion failure is explicit.
data GrammarV1SemanticSessionError
  = GrammarV1SemanticSessionBinderEvidenceMismatch
      ProtocolRoleKey
      GrammarV1ProtocolBinderSite
      (Located GrammarV1TermParam)
      (Maybe GrammarV1CheckedProtocolBinder)
  | GrammarV1SemanticSessionUnexpectedBinderEvidence
      [GrammarV1CheckedProtocolBinder]
  | GrammarV1SemanticSessionTypeRewriteNonCompetent
      (Located GrammarV1Type)
  | GrammarV1SemanticSessionFocusingError
      (Located GrammarV1Type)
      FocusingError
  | GrammarV1SemanticSessionBindingError
      GrammarV1CheckedProtocolBinder
      SurfaceCheckError
  deriving (Eq, Show)

-- | Elaborate one role-local session using only resolver-issued protocol binder
-- evidence. Binder evidence is consumed in the exact source traversal order
-- produced by ProtocolBinderScope. Message binders remain active through their
-- continuation; each select/offer branch starts from the same parent semantic
-- state, so sibling payload/message bindings cannot leak across branches.
--
-- The source competence deliberately matches the older checked SessionSemantics
-- route: static session references, guards/boundaries, and multi-parameter branch
-- payloads remain outside this bounded bridge. Recursive session-variable names
-- are not SurfaceState bindings and therefore remain presentation-named here; a
-- later closeout audit may assign them a separate identity obligation.
grammarV1CheckedSemanticSession
  :: StaticContext
  -> ProtocolRoleKey
  -> [GrammarV1CheckedProtocolBinder]
  -> GrammarV1SessionExpression
  -> Maybe
      (Either
        GrammarV1SemanticSessionError
        (Session, [FocusStep]))
grammarV1CheckedSemanticSession staticContext roleKey evidence source = do
  checked <- checkedElaborate
    staticContext
    roleKey
    Set.empty
    emptySurfaceState
    evidence
    source
  pure $ do
    (session, steps, remaining) <- checked
    if null remaining
      then Right (session, steps)
      else Left (GrammarV1SemanticSessionUnexpectedBinderEvidence remaining)

-- | Structural template projection of the exact checked semantic session. No
-- additional protocol-family or duality semantics are introduced here.
grammarV1CheckedSemanticSessionTemplate
  :: StaticContext
  -> ProtocolRoleKey
  -> [GrammarV1CheckedProtocolBinder]
  -> GrammarV1SessionExpression
  -> Maybe
      (Either
        GrammarV1SemanticSessionError
        (ProtocolSessionTemplate, [FocusStep]))
grammarV1CheckedSemanticSessionTemplate staticContext roleKey evidence source = do
  checked <- grammarV1CheckedSemanticSession
    staticContext roleKey evidence source
  pure $ fmap
    (\(session, steps) -> (sessionTemplate session, steps))
    checked

checkedElaborate
  :: StaticContext
  -> ProtocolRoleKey
  -> Set.Set Name
  -> SurfaceState
  -> [GrammarV1CheckedProtocolBinder]
  -> GrammarV1SessionExpression
  -> Maybe
      (Either
        GrammarV1SemanticSessionError
        (Session, [FocusStep], [GrammarV1CheckedProtocolBinder]))
checkedElaborate staticContext roleKey recursionNames state evidence source =
  case source of
    GrammarV1SessionReference _ -> Nothing
    GrammarV1SessionSend parameter Nothing Nothing continuation -> do
      inserted <- checkedInsertParam
        staticContext
        roleKey
        GrammarV1SendMessageBinder
        parameter
        state
        evidence
      case inserted of
        Left err -> pure (Left err)
        Right ((binder, messageType), nextState, ownSteps, restEvidence) -> do
          successor <- checkedElaborate
            staticContext
            roleKey
            recursionNames
            nextState
            restEvidence
            (locatedValue continuation)
          pure $ fmap
            (\(nextSession, restSteps, finalEvidence) ->
              ( Send binder messageType nextSession
              , ownSteps <> restSteps
              , finalEvidence
              ))
            successor
    GrammarV1SessionSend _ _ _ _ -> Nothing
    GrammarV1SessionReceive parameter Nothing Nothing continuation -> do
      inserted <- checkedInsertParam
        staticContext
        roleKey
        GrammarV1ReceiveMessageBinder
        parameter
        state
        evidence
      case inserted of
        Left err -> pure (Left err)
        Right ((binder, messageType), nextState, ownSteps, restEvidence) -> do
          successor <- checkedElaborate
            staticContext
            roleKey
            recursionNames
            nextState
            restEvidence
            (locatedValue continuation)
          pure $ fmap
            (\(nextSession, restSteps, finalEvidence) ->
              ( Receive binder messageType nextSession
              , ownSteps <> restSteps
              , finalEvidence
              ))
            successor
    GrammarV1SessionReceive _ _ _ _ -> Nothing
    GrammarV1SessionSelect branches -> do
      checkedBranches <- checkedElaborateBranches
        True staticContext roleKey recursionNames state evidence branches
      pure $ fmap
        (\(branches', steps, remaining) ->
          (Select branches', steps, remaining))
        checkedBranches
    GrammarV1SessionOffer branches -> do
      checkedBranches <- checkedElaborateBranches
        False staticContext roleKey recursionNames state evidence branches
      pure $ fmap
        (\(branches', steps, remaining) ->
          (Offer branches', steps, remaining))
        checkedBranches
    GrammarV1SessionEnd outcome ->
      pure (Right (End (Outcome (locatedValue outcome)), [], evidence))
    GrammarV1SessionRecursive recursionName body -> do
      let name = Name (locatedValue recursionName)
      checkedBody <- checkedElaborate
        staticContext
        roleKey
        (Set.insert name recursionNames)
        state
        evidence
        (locatedValue body)
      pure $ fmap
        (\(bodySession, steps, remaining) ->
          (Rec name bodySession, steps, remaining))
        checkedBody
    GrammarV1SessionContinue recursionName ->
      let name = Name (locatedValue recursionName)
      in if Set.member name recursionNames
          then pure (Right (SessionVar name, [], evidence))
          else Nothing

checkedElaborateBranches
  :: Bool
  -> StaticContext
  -> ProtocolRoleKey
  -> Set.Set Name
  -> SurfaceState
  -> [GrammarV1CheckedProtocolBinder]
  -> [Located GrammarV1SessionBranch]
  -> Maybe
      (Either
        GrammarV1SemanticSessionError
        ([Branch], [FocusStep], [GrammarV1CheckedProtocolBinder]))
checkedElaborateBranches _ _ _ _ _ evidence [] =
  pure (Right ([], [], evidence))
checkedElaborateBranches selecting staticContext roleKey recursionNames parentState evidence
    (branch : rest) = do
  first <- checkedElaborateBranch
    selecting staticContext roleKey recursionNames parentState evidence branch
  case first of
    Left err -> pure (Left err)
    Right (checkedBranch, firstSteps, afterFirst) -> do
      checkedRest <- checkedElaborateBranches
        selecting staticContext roleKey recursionNames parentState afterFirst rest
      pure $ fmap
        (\(restBranches, restSteps, finalEvidence) ->
          ( checkedBranch : restBranches
          , firstSteps <> restSteps
          , finalEvidence
          ))
        checkedRest

checkedElaborateBranch
  :: Bool
  -> StaticContext
  -> ProtocolRoleKey
  -> Set.Set Name
  -> SurfaceState
  -> [GrammarV1CheckedProtocolBinder]
  -> Located GrammarV1SessionBranch
  -> Maybe
      (Either
        GrammarV1SemanticSessionError
        (Branch, [FocusStep], [GrammarV1CheckedProtocolBinder]))
checkedElaborateBranch selecting staticContext roleKey recursionNames parentState evidence
    (Located _ branch)
  | grammarV1SessionBranchBoundary branch /= Nothing = Nothing
  | grammarV1SessionBranchGuard branch /= Nothing = Nothing
  | otherwise = do
      let label = locatedValue (grammarV1SessionBranchLabel branch)
          site
            | selecting = GrammarV1SelectBranchPayloadBinder label
            | otherwise = GrammarV1OfferBranchPayloadBinder label
      payload <- checkedElaboratePayload
        staticContext roleKey site (grammarV1SessionBranchParams branch)
        parentState evidence
      case payload of
        Left err -> pure (Left err)
        Right (checkedPayload, branchState, payloadSteps, afterPayload) -> do
          continuation <- checkedElaborate
            staticContext
            roleKey
            recursionNames
            branchState
            afterPayload
            (locatedValue (grammarV1SessionBranchContinuation branch))
          pure $ fmap
            (\(nextSession, continuationSteps, remaining) ->
              ( Branch
                  { branchLabel = label
                  , branchPayload = checkedPayload
                  , branchContinuation = nextSession
                  }
              , payloadSteps <> continuationSteps
              , remaining
              ))
            continuation

checkedElaboratePayload
  :: StaticContext
  -> ProtocolRoleKey
  -> GrammarV1ProtocolBinderSite
  -> Maybe [Located GrammarV1TermParam]
  -> SurfaceState
  -> [GrammarV1CheckedProtocolBinder]
  -> Maybe
      (Either
        GrammarV1SemanticSessionError
        ( Maybe (Name, Ty)
        , SurfaceState
        , [FocusStep]
        , [GrammarV1CheckedProtocolBinder]
        ))
checkedElaboratePayload _ _ _ Nothing state evidence =
  pure (Right (Nothing, state, [], evidence))
checkedElaboratePayload _ _ _ (Just []) state evidence =
  pure (Right (Nothing, state, [], evidence))
checkedElaboratePayload staticContext roleKey site (Just [parameter]) state evidence = do
  inserted <- checkedInsertParam
    staticContext roleKey site parameter state evidence
  pure $ fmap
    (\(binding, nextState, steps, remaining) ->
      (Just binding, nextState, steps, remaining))
    inserted
checkedElaboratePayload _ _ _ (Just _) _ _ = Nothing

checkedInsertParam
  :: StaticContext
  -> ProtocolRoleKey
  -> GrammarV1ProtocolBinderSite
  -> Located GrammarV1TermParam
  -> SurfaceState
  -> [GrammarV1CheckedProtocolBinder]
  -> Maybe
      (Either
        GrammarV1SemanticSessionError
        ( (Name, Ty)
        , SurfaceState
        , [FocusStep]
        , [GrammarV1CheckedProtocolBinder]
        ))
checkedInsertParam staticContext roleKey site source@(Located _ parameter) state evidence = do
  let (checkedBinder, remaining) = consumeBinderEvidence roleKey site source evidence
  case checkedBinder of
    Left err -> pure (Left err)
    Right binderEvidence ->
      case grammarV1RewriteTypeReferences
          (grammarV1CheckedProtocolBinderTypeReferences binderEvidence)
          (grammarV1TermParamType parameter) of
        Nothing -> pure
          (Left
            (GrammarV1SemanticSessionTypeRewriteNonCompetent
              (grammarV1TermParamType parameter)))
        Just rewrittenType -> do
          checkedType <- grammarV1CheckedTypeMode
            staticContext
            state
            (locatedValue rewrittenType)
          case checkedType of
            Left err -> pure
              (Left
                (GrammarV1SemanticSessionFocusingError rewrittenType err))
            Right (typeMode, steps) -> do
              let ty = checkedBindingType typeMode
                  binder = grammarV1CheckedProtocolBinderResolved binderEvidence
                  name = grammarV1ResolvedBinderCoreName binder
                  meta = BindingMeta
                    { bindingMode = checkedBindingMode typeMode
                    , bindingType = ty
                    , bindingShape = shapeForType ty
                    }
              pure $ case grammarV1InsertSemanticBinding binder meta state of
                Left err -> Left
                  (GrammarV1SemanticSessionBindingError binderEvidence err)
                Right nextState -> Right
                  ((name, ty), nextState, steps, remaining)

consumeBinderEvidence
  :: ProtocolRoleKey
  -> GrammarV1ProtocolBinderSite
  -> Located GrammarV1TermParam
  -> [GrammarV1CheckedProtocolBinder]
  -> ( Either
        GrammarV1SemanticSessionError
        GrammarV1CheckedProtocolBinder
     , [GrammarV1CheckedProtocolBinder]
     )
consumeBinderEvidence roleKey site source evidence =
  case evidence of
    [] ->
      ( Left
          (GrammarV1SemanticSessionBinderEvidenceMismatch
            roleKey site source Nothing)
      , []
      )
    candidate : rest
      | grammarV1CheckedProtocolBinderRole candidate == roleKey
      , grammarV1CheckedProtocolBinderSite candidate == site
      , grammarV1CheckedProtocolBinderSource candidate == source ->
          (Right candidate, rest)
      | otherwise ->
          ( Left
              (GrammarV1SemanticSessionBinderEvidenceMismatch
                roleKey site source (Just candidate))
          , evidence
          )

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
