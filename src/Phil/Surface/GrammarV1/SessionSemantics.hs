module Phil.Surface.GrammarV1.SessionSemantics
  ( GrammarV1CheckedSessionError (..)
  , grammarV1PrimitiveSession
  , grammarV1PrimitiveSessionTemplate
  , grammarV1CheckedSession
  , grammarV1CheckedSessionTemplate
  ) where

import qualified Data.Set as Set
import Phil.Core.CheckedBindingMode
  ( CheckedTypeMode (..)
  )
import Phil.Core.Focusing
  ( FocusStep
  , FocusingError
  )
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
  , insertBindingMeta
  , shapeForBinding
  , shapeForType
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , SurfaceCheckError
  , SurfaceState
  )
import Phil.Surface.GrammarV1.CallableSignature
  ( grammarV1InsertPrimitiveBinding
  )
import Phil.Surface.GrammarV1.CheckedType
  ( grammarV1CheckedTypeMode
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1SessionBranch (..)
  , GrammarV1SessionExpression (..)
  , GrammarV1TermParam (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Checked failures that arise after the source session shape has entered the
-- bounded checked-payload route. Type/proposition canonicalization remains owned
-- by Core focusing, while lexical/resource insertion remains owned by the ordinary
-- surface binding authority. Unsupported source structure still reports Nothing.
data GrammarV1CheckedSessionError
  = GrammarV1CheckedSessionFocusingError FocusingError
  | GrammarV1CheckedSessionBindingError SurfaceCheckError
  deriving (Eq, Show)

-- | Project the first exact Grammar-v1 session fragment into Core Session.
-- Message binders reuse the established primitive/unrestricted lexical binding
-- authority, so only Unit/Bool/U<n> payloads enter this bridge for now.
-- Codec/boundary references, guards, static session references, richer checked
-- message types, and multi-parameter branch payloads remain outside this bounded
-- competence rather than being erased or flattened. Omitted branch parameters
-- and an explicitly empty source list are distinct parser forms but both denote
-- the same Core no-payload branch carrier.
grammarV1PrimitiveSession :: GrammarV1SessionExpression -> Maybe Session
grammarV1PrimitiveSession = elaborate Set.empty emptySurfaceState

-- | Preserve the same admitted local-session fragment in the Core protocol
-- family template vocabulary. This is a structural change of carrier only:
-- every admitted concrete message type is wrapped as ProtocolConcreteType and
-- no generic message parameter, role relation, family identity, or duality fact
-- is inferred here.
grammarV1PrimitiveSessionTemplate
  :: GrammarV1SessionExpression
  -> Maybe ProtocolSessionTemplate
grammarV1PrimitiveSessionTemplate = fmap sessionTemplate . grammarV1PrimitiveSession

-- | Extend local-session elaboration through the existing checked type+mode
-- authority instead of assigning structural behavior from source spelling.
--
-- Every send/receive or single branch-payload binder is checked with
-- 'grammarV1CheckedTypeMode' under the exact lexical state established by earlier
-- session binders. The returned Core mode is then installed unchanged through
-- 'insertBindingMeta'. This admits intrinsically classified richer types such as
-- linear Bytes, unrestricted proofs/refinements, and other already-supported
-- checked types whose mode is authoritative, while named/Frame/Validated forms
-- whose structural mode still needs declaration/resource resolution remain
-- outside competence.
--
-- Type focusing traces are concatenated in exact source traversal order. Core
-- focusing failures and binding failures remain explicit Left values; unsupported
-- source structure remains Nothing. Boundaries, guards, static session references,
-- multi-parameter branch payloads, and unbound continuation targets stay outside
-- this route. No source binder identity is stabilized beyond the ordinary lexical
-- binding itself, so SURF-009 remains authoritative for separate binder-resolution
-- obligations.
grammarV1CheckedSession
  :: StaticContext
  -> GrammarV1SessionExpression
  -> Maybe
      (Either
        GrammarV1CheckedSessionError
        (Session, [FocusStep]))
grammarV1CheckedSession staticContext =
  checkedElaborate staticContext Set.empty emptySurfaceState

-- | Structural carrier sibling of 'grammarV1CheckedSession'. The checked Core
-- Session is converted exactly to ProtocolSessionTemplate after all type/mode and
-- lexical checks have succeeded; no role relation, family identity, or duality is
-- inferred here.
grammarV1CheckedSessionTemplate
  :: StaticContext
  -> GrammarV1SessionExpression
  -> Maybe
      (Either
        GrammarV1CheckedSessionError
        (ProtocolSessionTemplate, [FocusStep]))
grammarV1CheckedSessionTemplate staticContext source = do
  checked <- grammarV1CheckedSession staticContext source
  pure $ fmap
    (\(session, steps) -> (sessionTemplate session, steps))
    checked

elaborate
  :: Set.Set Name
  -> SurfaceState
  -> GrammarV1SessionExpression
  -> Maybe Session
elaborate recursionNames state source =
  case source of
    GrammarV1SessionReference _ -> Nothing
    GrammarV1SessionSend param Nothing Nothing continuation -> do
      ((binder, messageType), nextState) <- insertPrimitiveParam param state
      successor <- elaborate recursionNames nextState (locatedValue continuation)
      pure (Send binder messageType successor)
    GrammarV1SessionSend _ _ _ _ -> Nothing
    GrammarV1SessionReceive param Nothing Nothing continuation -> do
      ((binder, messageType), nextState) <- insertPrimitiveParam param state
      successor <- elaborate recursionNames nextState (locatedValue continuation)
      pure (Receive binder messageType successor)
    GrammarV1SessionReceive _ _ _ _ -> Nothing
    GrammarV1SessionSelect branches ->
      Select <$> mapM (elaborateBranch recursionNames state) branches
    GrammarV1SessionOffer branches ->
      Offer <$> mapM (elaborateBranch recursionNames state) branches
    GrammarV1SessionEnd outcome ->
      pure (End (Outcome (locatedValue outcome)))
    GrammarV1SessionRecursive recursionName body -> do
      let name = Name (locatedValue recursionName)
      Rec name <$> elaborate
        (Set.insert name recursionNames)
        state
        (locatedValue body)
    GrammarV1SessionContinue recursionName ->
      let name = Name (locatedValue recursionName)
      in if Set.member name recursionNames
          then Just (SessionVar name)
          else Nothing

elaborateBranch
  :: Set.Set Name
  -> SurfaceState
  -> Located GrammarV1SessionBranch
  -> Maybe Branch
elaborateBranch recursionNames state (Located _ branch)
  | grammarV1SessionBranchBoundary branch /= Nothing = Nothing
  | grammarV1SessionBranchGuard branch /= Nothing = Nothing
  | otherwise = do
      (payload, branchState) <- elaboratePayload
        (grammarV1SessionBranchParams branch)
        state
      continuation <- elaborate
        recursionNames
        branchState
        (locatedValue (grammarV1SessionBranchContinuation branch))
      pure Branch
        { branchLabel = locatedValue (grammarV1SessionBranchLabel branch)
        , branchPayload = payload
        , branchContinuation = continuation
        }

elaboratePayload
  :: Maybe [Located GrammarV1TermParam]
  -> SurfaceState
  -> Maybe (Maybe (Name, Ty), SurfaceState)
elaboratePayload source state =
  case source of
    Nothing -> Just (Nothing, state)
    Just [] -> Just (Nothing, state)
    Just [param] -> do
      ((binder, payloadType), nextState) <- insertPrimitiveParam param state
      pure (Just (binder, payloadType), nextState)
    Just _ -> Nothing

insertPrimitiveParam
  :: Located GrammarV1TermParam
  -> SurfaceState
  -> Maybe ((Name, Ty), SurfaceState)
insertPrimitiveParam (Located _ param) =
  grammarV1InsertPrimitiveBinding
    (grammarV1TermParamName param)
    (grammarV1TermParamType param)

checkedElaborate
  :: StaticContext
  -> Set.Set Name
  -> SurfaceState
  -> GrammarV1SessionExpression
  -> Maybe
      (Either
        GrammarV1CheckedSessionError
        (Session, [FocusStep]))
checkedElaborate staticContext recursionNames state source =
  case source of
    GrammarV1SessionReference _ -> Nothing
    GrammarV1SessionSend param Nothing Nothing continuation -> do
      inserted <- checkedInsertParam staticContext param state
      case inserted of
        Left err -> pure (Left err)
        Right ((binder, messageType), nextState, ownSteps) -> do
          successor <- checkedElaborate
            staticContext
            recursionNames
            nextState
            (locatedValue continuation)
          pure $ fmap
            (\(nextSession, restSteps) ->
              (Send binder messageType nextSession, ownSteps <> restSteps))
            successor
    GrammarV1SessionSend _ _ _ _ -> Nothing
    GrammarV1SessionReceive param Nothing Nothing continuation -> do
      inserted <- checkedInsertParam staticContext param state
      case inserted of
        Left err -> pure (Left err)
        Right ((binder, messageType), nextState, ownSteps) -> do
          successor <- checkedElaborate
            staticContext
            recursionNames
            nextState
            (locatedValue continuation)
          pure $ fmap
            (\(nextSession, restSteps) ->
              (Receive binder messageType nextSession, ownSteps <> restSteps))
            successor
    GrammarV1SessionReceive _ _ _ _ -> Nothing
    GrammarV1SessionSelect branches -> do
      branchResults <- mapM
        (checkedElaborateBranch staticContext recursionNames state)
        branches
      pure $ do
        checkedBranches <- sequence branchResults
        Right
          ( Select (map fst checkedBranches)
          , concatMap snd checkedBranches
          )
    GrammarV1SessionOffer branches -> do
      branchResults <- mapM
        (checkedElaborateBranch staticContext recursionNames state)
        branches
      pure $ do
        checkedBranches <- sequence branchResults
        Right
          ( Offer (map fst checkedBranches)
          , concatMap snd checkedBranches
          )
    GrammarV1SessionEnd outcome ->
      pure (Right (End (Outcome (locatedValue outcome)), []))
    GrammarV1SessionRecursive recursionName body -> do
      let name = Name (locatedValue recursionName)
      checkedBody <- checkedElaborate
        staticContext
        (Set.insert name recursionNames)
        state
        (locatedValue body)
      pure $ fmap
        (\(bodySession, steps) -> (Rec name bodySession, steps))
        checkedBody
    GrammarV1SessionContinue recursionName ->
      let name = Name (locatedValue recursionName)
      in if Set.member name recursionNames
          then pure (Right (SessionVar name, []))
          else Nothing

checkedElaborateBranch
  :: StaticContext
  -> Set.Set Name
  -> SurfaceState
  -> Located GrammarV1SessionBranch
  -> Maybe
      (Either
        GrammarV1CheckedSessionError
        (Branch, [FocusStep]))
checkedElaborateBranch
    staticContext recursionNames state (Located _ branch)
  | grammarV1SessionBranchBoundary branch /= Nothing = Nothing
  | grammarV1SessionBranchGuard branch /= Nothing = Nothing
  | otherwise = do
      payloadResult <- checkedElaboratePayload
        staticContext
        (grammarV1SessionBranchParams branch)
        state
      case payloadResult of
        Left err -> pure (Left err)
        Right (payload, branchState, payloadSteps) -> do
          continuationResult <- checkedElaborate
            staticContext
            recursionNames
            branchState
            (locatedValue (grammarV1SessionBranchContinuation branch))
          pure $ fmap
            (\(continuation, continuationSteps) ->
              ( Branch
                  { branchLabel = locatedValue (grammarV1SessionBranchLabel branch)
                  , branchPayload = payload
                  , branchContinuation = continuation
                  }
              , payloadSteps <> continuationSteps
              ))
            continuationResult

checkedElaboratePayload
  :: StaticContext
  -> Maybe [Located GrammarV1TermParam]
  -> SurfaceState
  -> Maybe
      (Either
        GrammarV1CheckedSessionError
        (Maybe (Name, Ty), SurfaceState, [FocusStep]))
checkedElaboratePayload staticContext source state =
  case source of
    Nothing -> pure (Right (Nothing, state, []))
    Just [] -> pure (Right (Nothing, state, []))
    Just [param] -> do
      inserted <- checkedInsertParam staticContext param state
      pure $ fmap
        (\((binder, payloadType), nextState, steps) ->
          (Just (binder, payloadType), nextState, steps))
        inserted
    Just _ -> Nothing

checkedInsertParam
  :: StaticContext
  -> Located GrammarV1TermParam
  -> SurfaceState
  -> Maybe
      (Either
        GrammarV1CheckedSessionError
        ((Name, Ty), SurfaceState, [FocusStep]))
checkedInsertParam staticContext (Located _ param) state = do
  checked <- grammarV1CheckedTypeMode
    staticContext
    state
    (locatedValue (grammarV1TermParamType param))
  case checked of
    Left err -> pure (Left (GrammarV1CheckedSessionFocusingError err))
    Right (typeMode, steps) ->
      let sourceName = grammarV1TermParamName param
          bindingText = locatedValue sourceName
          bindingName = Name bindingText
          bindingType' = checkedBindingType typeMode
          bindingMeta = BindingMeta
            { bindingMode = checkedBindingMode typeMode
            , bindingType = bindingType'
            , bindingShape = shapeForBinding
                bindingText
                (shapeForType bindingType')
            }
      in pure $ case insertBindingMeta
          (locatedSpan sourceName)
          bindingText
          bindingMeta
          state of
        Left err -> Left (GrammarV1CheckedSessionBindingError err)
        Right nextState -> Right
          ((bindingName, bindingType'), nextState, steps)

sessionTemplate :: Session -> ProtocolSessionTemplate
sessionTemplate source = case source of
  Send binder ty continuation ->
    ProtocolTemplateSend binder (ProtocolConcreteType ty) (sessionTemplate continuation)
  Receive binder ty continuation ->
    ProtocolTemplateReceive binder (ProtocolConcreteType ty) (sessionTemplate continuation)
  Select branches -> ProtocolTemplateSelect (map branchTemplate branches)
  Offer branches -> ProtocolTemplateOffer (map branchTemplate branches)
  End outcome -> ProtocolTemplateEnd outcome
  Rec recursionName body -> ProtocolTemplateRec recursionName (sessionTemplate body)
  SessionVar variable -> ProtocolTemplateVar variable

branchTemplate :: Branch -> ProtocolBranchTemplate
branchTemplate branch = ProtocolBranchTemplate
  { protocolTemplateBranchLabel = branchLabel branch
  , protocolTemplateBranchPayload = fmap
      (\(binder, ty) -> (binder, ProtocolConcreteType ty))
      (branchPayload branch)
  , protocolTemplateBranchContinuation = sessionTemplate (branchContinuation branch)
  }
