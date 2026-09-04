module Phil.Surface.GrammarV1.SessionSemantics
  ( grammarV1PrimitiveSession
  , grammarV1PrimitiveSessionTemplate
  ) where

import qualified Data.Set as Set
import Phil.Core.Protocol.Family
  ( ProtocolBranchTemplate (..)
  , ProtocolSessionTemplate (..)
  , ProtocolTypeTemplate (..)
  )
import Phil.Core.Syntax
  ( Branch (..)
  , Name (..)
  , Outcome (..)
  , Session (..)
  , Ty
  )
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.Check.Types (SurfaceState)
import Phil.Surface.GrammarV1.CallableSignature
  ( grammarV1InsertPrimitiveBinding
  )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1SessionBranch (..)
  , GrammarV1SessionExpression (..)
  , GrammarV1TermParam (..)
  )
import Phil.Surface.Syntax (Located (..))

-- | Project the first exact Grammar-v1 session fragment into Core Session.
-- Message binders reuse the established primitive/unrestricted lexical binding
-- authority, so only Unit/Bool/U<n> payloads enter this bridge for now.
-- Codec/boundary references, guards, static session references, and
-- multi-parameter branch payloads remain outside this bounded competence rather
-- than being erased or flattened. Omitted branch parameters and an explicitly
-- empty source list are distinct parser forms but both denote the same Core
-- no-payload branch carrier.
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
