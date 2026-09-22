{-# LANGUAGE TupleSections #-}

module Phil.Core.Session
  ( SessionAction (..)
  , MessageSpec (..)
  , SessionStep (..)
  , SessionError (..)
  , exposeSessionHead
  , sendEndpoint
  , receiveEndpoint
  , selectEndpoint
  , offerEndpoint
  , closeEndpoint
  , instantiateMessageStep
  , dualSession
  ) where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Context
  ( CheckError
  , ResourceContext
  , consumeLinear
  , insertBinding
  )
import Phil.Core.Refinement
  ( substituteProposition
  , substituteRefTerm
  )
import Phil.Core.Syntax
  ( Branch (..)
  , GrammarId
  , Mode (Linear)
  , Name (..)
  , Outcome
  , PendingRecvSpec (..)
  , Proposition (..)
  , RefTerm (..)
  , Session (..)
  , Ty (..)
  , ProductElementType (..)
  )

data SessionAction
  = SendAction
  | ReceiveAction
  | SelectAction Text
  | OfferAction Text
  | CloseAction Outcome
  deriving (Eq, Show)

data MessageSpec = MessageSpec
  { messageBinder :: Name
  , messageType :: Ty
  }
  deriving (Eq, Show)

data SessionStep = SessionStep
  { stepAction :: SessionAction
  , stepMessage :: Maybe MessageSpec
  , stepSuccessor :: Maybe (Name, Session)
  , stepContext :: ResourceContext
  }
  deriving (Eq, Show)

data SessionError
  = SessionResourceError CheckError
  | ExpectedLinearEndpoint Name Ty
  | UnexpectedSessionAction SessionAction Session
  | GrammarBackedReceiveRequiresRecognition GrammarId
  | GrammarBackedOfferPayloadRequiresRecognition Text GrammarId
  | UnknownSessionLabel Text [Text]
  | DuplicateSessionLabel Text
  | CloseOutcomeMismatch Outcome Outcome
  | SuccessorReusesEndpointName Name
  | UnguardedRecursion Name
  | UnboundSessionVariable Name
  | MissingMessageInstantiation Name
  | UnsupportedMessageInstantiation Name RefTerm
  deriving (Eq, Show)

exposeSessionHead :: Session -> Either SessionError Session
exposeSessionHead = go Set.empty
  where
    go :: Set Name -> Session -> Either SessionError Session
    go seen session =
      case session of
        Rec recursionName body
          | Set.member recursionName seen -> Left (UnguardedRecursion recursionName)
          | otherwise ->
              go
                (Set.insert recursionName seen)
                (substituteSessionVar recursionName session body)
        SessionVar variable -> Left (UnboundSessionVariable variable)
        headSession -> Right headSession

sendEndpoint :: Name -> Name -> ResourceContext -> Either SessionError SessionStep
sendEndpoint endpoint successor context = do
  (headSession, consumed) <- consumeEndpoint endpoint context
  case headSession of
    Send binder messageTy continuation ->
      continueWith endpoint successor SendAction (Just (MessageSpec binder messageTy)) continuation consumed
    _ -> Left (UnexpectedSessionAction SendAction headSession)

receiveEndpoint :: Name -> Name -> ResourceContext -> Either SessionError SessionStep
receiveEndpoint endpoint successor context = do
  (headSession, consumed) <- consumeEndpoint endpoint context
  case headSession of
    Receive _ messageTy _
      | Just grammar <- frameGrammar messageTy ->
          Left (GrammarBackedReceiveRequiresRecognition grammar)
    Receive binder messageTy continuation ->
      continueWith endpoint successor ReceiveAction (Just (MessageSpec binder messageTy)) continuation consumed
    _ -> Left (UnexpectedSessionAction ReceiveAction headSession)

selectEndpoint :: Name -> Name -> Text -> ResourceContext -> Either SessionError SessionStep
selectEndpoint endpoint successor label context = do
  (headSession, consumed) <- consumeEndpoint endpoint context
  case headSession of
    Select branches -> do
      branch <- selectBranch label branches
      continueWith
        endpoint
        successor
        (SelectAction label)
        (branchMessage branch)
        (branchContinuation branch)
        consumed
    _ -> Left (UnexpectedSessionAction (SelectAction label) headSession)

offerEndpoint :: Name -> Name -> Text -> ResourceContext -> Either SessionError SessionStep
offerEndpoint endpoint successor label context = do
  (headSession, consumed) <- consumeEndpoint endpoint context
  case headSession of
    Offer branches -> do
      branch <- selectBranch label branches
      case branchPayload branch >>= (frameGrammar . snd) of
        Just grammar -> Left (GrammarBackedOfferPayloadRequiresRecognition label grammar)
        Nothing ->
          continueWith
            endpoint
            successor
            (OfferAction label)
            (branchMessage branch)
            (branchContinuation branch)
            consumed
    _ -> Left (UnexpectedSessionAction (OfferAction label) headSession)

closeEndpoint :: Name -> Outcome -> ResourceContext -> Either SessionError SessionStep
closeEndpoint endpoint outcome context = do
  (headSession, consumed) <- consumeEndpoint endpoint context
  case headSession of
    End expected
      | expected == outcome ->
          Right SessionStep
            { stepAction = CloseAction outcome
            , stepMessage = Nothing
            , stepSuccessor = Nothing
            , stepContext = consumed
            }
      | otherwise -> Left (CloseOutcomeMismatch expected outcome)
    _ -> Left (UnexpectedSessionAction (CloseAction outcome) headSession)

-- | Bind a checked message occurrence into the continuation produced by one
-- session step.  The ordinary endpoint helpers intentionally remain descriptor
-- and resource transitions; Surface calls this only after it has checked the
-- concrete send/receive/select/offer payload and can supply its logical term.
--
-- A formal message binder scopes over the continuation, not its own message
-- type.  Substitution therefore descends through every Phase-1 term-bearing
-- type/session constructor, respects later shadowing, and alpha-renames a
-- later binder if it would capture a free name from the actual term.
instantiateMessageStep :: Maybe RefTerm -> SessionStep -> Either SessionError SessionStep
instantiateMessageStep actual step =
  case (stepMessage step, stepSuccessor step) of
    (Just message, Just (successor, continuation))
      | not (sessionMentions (messageBinder message) continuation) -> Right step
      | otherwise -> do
          replacement <- case actual of
            Just term -> Right term
            Nothing -> Left (MissingMessageInstantiation (messageBinder message))
          instantiated <- substituteSessionTerm
            (messageBinder message)
            replacement
            continuation
          (_, withoutSuccessor) <- mapLeft SessionResourceError $
            consumeLinear successor (stepContext step)
          rebound <- mapLeft SessionResourceError $
            insertBinding Linear successor (TyEndpoint instantiated) withoutSuccessor
          Right step
            { stepSuccessor = Just (successor, instantiated)
            , stepContext = rebound
            }
    _ -> Right step

consumeEndpoint :: Name -> ResourceContext -> Either SessionError (Session, ResourceContext)
consumeEndpoint endpoint context = do
  (endpointTy, consumed) <- mapLeft SessionResourceError (consumeLinear endpoint context)
  case endpointTy of
    TyEndpoint session -> do
      headSession <- exposeSessionHead session
      Right (headSession, consumed)
    other -> Left (ExpectedLinearEndpoint endpoint other)

continueWith
  :: Name
  -> Name
  -> SessionAction
  -> Maybe MessageSpec
  -> Session
  -> ResourceContext
  -> Either SessionError SessionStep
continueWith endpoint successor action message continuation consumed
  | endpoint == successor = Left (SuccessorReusesEndpointName endpoint)
  | otherwise = do
      continued <- mapLeft SessionResourceError $
        insertBinding Linear successor (TyEndpoint continuation) consumed
      Right SessionStep
        { stepAction = action
        , stepMessage = message
        , stepSuccessor = Just (successor, continuation)
        , stepContext = continued
        }

selectBranch :: Text -> [Branch] -> Either SessionError Branch
selectBranch label branches = do
  ensureUniqueLabels branches
  case filter ((== label) . branchLabel) branches of
    [] -> Left (UnknownSessionLabel label (map branchLabel branches))
    [branch] -> Right branch
    _ -> Left (DuplicateSessionLabel label)

ensureUniqueLabels :: [Branch] -> Either SessionError ()
ensureUniqueLabels = go Set.empty
  where
    go :: Set Text -> [Branch] -> Either SessionError ()
    go _ [] = Right ()
    go seen (branch : rest)
      | Set.member label seen = Left (DuplicateSessionLabel label)
      | otherwise = go (Set.insert label seen) rest
      where
        label = branchLabel branch

branchMessage :: Branch -> Maybe MessageSpec
branchMessage branch =
  fmap (uncurry MessageSpec) (branchPayload branch)

frameGrammar :: Ty -> Maybe GrammarId
frameGrammar ty =
  case ty of
    TyFrame grammar -> Just grammar
    TyRefined _ inner _ -> frameGrammar inner
    _ -> Nothing

dualSession :: Session -> Session
dualSession session =
  case session of
    Send binder messageTy continuation -> Receive binder messageTy (dualSession continuation)
    Receive binder messageTy continuation -> Send binder messageTy (dualSession continuation)
    Select branches -> Offer (map dualBranch branches)
    Offer branches -> Select (map dualBranch branches)
    End outcome -> End outcome
    Rec recursionName body -> Rec recursionName (dualSession body)
    SessionVar variable -> SessionVar variable
  where
    dualBranch branch = branch { branchContinuation = dualSession (branchContinuation branch) }

substituteSessionTerm :: Name -> RefTerm -> Session -> Either SessionError Session
substituteSessionTerm target replacement session =
  case session of
    Send binder messageTy continuation -> do
      messageTy' <- substituteTyTerm target replacement messageTy
      (binder', continuation') <- substituteScopedSessionBinder target replacement binder continuation
      Right (Send binder' messageTy' continuation')
    Receive binder messageTy continuation -> do
      messageTy' <- substituteTyTerm target replacement messageTy
      (binder', continuation') <- substituteScopedSessionBinder target replacement binder continuation
      Right (Receive binder' messageTy' continuation')
    Select branches -> Select <$> mapM (substituteBranchTerm target replacement) branches
    Offer branches -> Offer <$> mapM (substituteBranchTerm target replacement) branches
    End outcome -> Right (End outcome)
    Rec recursionName body -> Rec recursionName <$> substituteSessionTerm target replacement body
    SessionVar variable -> Right (SessionVar variable)

substituteScopedSessionBinder
  :: Name
  -> RefTerm
  -> Name
  -> Session
  -> Either SessionError (Name, Session)
substituteScopedSessionBinder target replacement binder continuation
  | binder == target = Right (binder, continuation)
  | Set.member binder (refTermNames replacement) = do
      let fresh = freshBinder (sessionNames continuation `Set.union` refTermNames replacement `Set.union` Set.fromList [target, binder])
      renamed <- substituteSessionTerm binder (RefVar fresh) continuation
      substituted <- substituteSessionTerm target replacement renamed
      Right (fresh, substituted)
  | otherwise = (binder,) <$> substituteSessionTerm target replacement continuation

substituteBranchTerm :: Name -> RefTerm -> Branch -> Either SessionError Branch
substituteBranchTerm target replacement branch = do
  payload' <- case branchPayload branch of
    Nothing -> Right Nothing
    Just (binder, payloadTy) -> do
      payloadTy' <- substituteTyTerm target replacement payloadTy
      Right (Just (binder, payloadTy'))
  case branchPayload branch of
    Nothing -> do
      continuation' <- substituteSessionTerm target replacement (branchContinuation branch)
      Right branch { branchPayload = payload', branchContinuation = continuation' }
    Just (binder, _) -> do
      (binder', continuation') <- substituteScopedSessionBinder
        target replacement binder (branchContinuation branch)
      Right branch
        { branchPayload = fmap (\(_, ty) -> (binder', ty)) payload'
        , branchContinuation = continuation'
        }

substituteTyTerm :: Name -> RefTerm -> Ty -> Either SessionError Ty
substituteTyTerm target replacement ty =
  case ty of
    TyUnit -> Right TyUnit
    TyBool -> Right TyBool
    TyUInt width -> Right (TyUInt width)
    TyBytes index -> Right (TyBytes (substituteRefTerm target replacement index))
    TyFrame grammar -> Right (TyFrame grammar)
    TyPendingRecv pending -> do
      let binder = pendingBinder pending
      if binder == target
        then Right ty
        else do
          (binder', continuation') <- substituteScopedSessionBinder
            target replacement binder (pendingContinuation pending)
          Right (TyPendingRecv pending
            { pendingBinder = binder'
            , pendingContinuation = continuation'
            })
    TyProof proposition -> Right (TyProof (substituteProposition target replacement proposition))
    TyValidated claim context subject -> do
      context' <- substituteNameField target replacement context
      subject' <- substituteNameField target replacement subject
      Right (TyValidated claim context' subject')
    TyEndpoint session -> TyEndpoint <$> substituteSessionTerm target replacement session
    TyProduct elements -> TyProduct <$> mapM substituteElement elements
    TyRefined binder inner proposition -> do
      inner' <- substituteTyTerm target replacement inner
      if binder == target
        then Right (TyRefined binder inner' proposition)
        else if Set.member binder (refTermNames replacement)
          then do
            let used = propositionNames proposition `Set.union` refTermNames replacement `Set.union` Set.fromList [target, binder]
                fresh = freshBinder used
                renamed = substituteProposition binder (RefVar fresh) proposition
            Right (TyRefined fresh inner' (substituteProposition target replacement renamed))
          else Right (TyRefined binder inner' (substituteProposition target replacement proposition))
    TyOpaque name -> Right (TyOpaque name)
    TyOpaqueSorted name sort -> Right (TyOpaqueSorted name sort)
  where
    substituteElement element = do
      elementTy <- substituteTyTerm target replacement (productElementType element)
      Right element { productElementType = elementTy }

substituteNameField :: Name -> RefTerm -> Name -> Either SessionError Name
substituteNameField target replacement actual
  | actual /= target = Right actual
  | otherwise = case replacement of
      RefVar replacementName -> Right replacementName
      _ -> Left (UnsupportedMessageInstantiation target replacement)

sessionMentions :: Name -> Session -> Bool
sessionMentions target session =
  case session of
    Send binder messageTy continuation ->
      tyMentions target messageTy || (binder /= target && sessionMentions target continuation)
    Receive binder messageTy continuation ->
      tyMentions target messageTy || (binder /= target && sessionMentions target continuation)
    Select branches -> any (branchMentions target) branches
    Offer branches -> any (branchMentions target) branches
    End _ -> False
    Rec _ body -> sessionMentions target body
    SessionVar _ -> False

branchMentions :: Name -> Branch -> Bool
branchMentions target branch =
  case branchPayload branch of
    Nothing -> sessionMentions target (branchContinuation branch)
    Just (binder, payloadTy) ->
      tyMentions target payloadTy || (binder /= target && sessionMentions target (branchContinuation branch))

tyMentions :: Name -> Ty -> Bool
tyMentions target ty = Set.member target (tyNames ty)

refTermNames :: RefTerm -> Set Name
refTermNames term =
  case term of
    RefVar name -> Set.singleton name
    RefNat _ -> Set.empty
    RefUInt _ _ -> Set.empty
    RefBool _ -> Set.empty
    RefField base _ _ -> refTermNames base
    RefLen value -> refTermNames value
    RefToNat value -> refTermNames value
    RefAdd left right -> refTermNames left `Set.union` refTermNames right
    RefSub left right -> refTermNames left `Set.union` refTermNames right
    RefScale _ value -> refTermNames value
    RefOpaque _ _ -> Set.empty

propositionNames :: Proposition -> Set Name
propositionNames proposition =
  case proposition of
    Truth -> Set.empty
    Falsehood -> Set.empty
    Equal left right -> names2 left right
    NotEqual left right -> names2 left right
    LessThan left right -> names2 left right
    LessEqual left right -> names2 left right
    Member value collection -> names2 value collection
    Disjoint left right -> names2 left right
    Conjunction left right -> propositionNames left `Set.union` propositionNames right
    Disjunction left right -> propositionNames left `Set.union` propositionNames right
    Negation inner -> propositionNames inner
    Atom _ arguments -> Set.unions (map refTermNames arguments)
  where
    names2 left right = refTermNames left `Set.union` refTermNames right

tyNames :: Ty -> Set Name
tyNames ty =
  case ty of
    TyUnit -> Set.empty
    TyBool -> Set.empty
    TyUInt _ -> Set.empty
    TyBytes index -> refTermNames index
    TyFrame _ -> Set.empty
    TyPendingRecv pending ->
      Set.insert (pendingBinder pending) (sessionNames (pendingContinuation pending))
    TyProof proposition -> propositionNames proposition
    TyValidated _ context subject -> Set.fromList [context, subject]
    TyEndpoint session -> sessionNames session
    TyProduct elements -> Set.unions (map (tyNames . productElementType) elements)
    TyRefined binder inner proposition ->
      Set.insert binder (tyNames inner `Set.union` propositionNames proposition)
    TyOpaque _ -> Set.empty
    TyOpaqueSorted _ _ -> Set.empty

sessionNames :: Session -> Set Name
sessionNames session =
  case session of
    Send binder messageTy continuation ->
      Set.insert binder (tyNames messageTy `Set.union` sessionNames continuation)
    Receive binder messageTy continuation ->
      Set.insert binder (tyNames messageTy `Set.union` sessionNames continuation)
    Select branches -> Set.unions (map branchNames branches)
    Offer branches -> Set.unions (map branchNames branches)
    End _ -> Set.empty
    Rec recursionName body -> Set.insert recursionName (sessionNames body)
    SessionVar variable -> Set.singleton variable
  where
    branchNames branch =
      let payloadNames = case branchPayload branch of
            Nothing -> Set.empty
            Just (binder, payloadTy) -> Set.insert binder (tyNames payloadTy)
      in payloadNames `Set.union` sessionNames (branchContinuation branch)

freshBinder :: Set Name -> Name
freshBinder used = go (0 :: Integer)
  where
    go counter =
      let candidate = Name ("$message-binding." <> Text.pack (show counter))
      in if Set.member candidate used then go (counter + 1) else candidate

substituteSessionVar :: Name -> Session -> Session -> Session
substituteSessionVar target replacement session =
  case session of
    Send binder messageTy continuation ->
      Send binder (substituteTy target replacement messageTy) (substituteSessionVar target replacement continuation)
    Receive binder messageTy continuation ->
      Receive binder (substituteTy target replacement messageTy) (substituteSessionVar target replacement continuation)
    Select branches -> Select (map (substituteBranch target replacement) branches)
    Offer branches -> Offer (map (substituteBranch target replacement) branches)
    End outcome -> End outcome
    Rec recursionName body
      | recursionName == target -> Rec recursionName body
      | otherwise -> Rec recursionName (substituteSessionVar target replacement body)
    SessionVar variable
      | variable == target -> replacement
      | otherwise -> SessionVar variable

substituteBranch :: Name -> Session -> Branch -> Branch
substituteBranch target replacement branch =
  branch
    { branchPayload = fmap substitutePayload (branchPayload branch)
    , branchContinuation = substituteSessionVar target replacement (branchContinuation branch)
    }
  where
    substitutePayload (binder, payloadTy) =
      (binder, substituteTy target replacement payloadTy)

substituteTy :: Name -> Session -> Ty -> Ty
substituteTy target replacement ty =
  case ty of
    TyEndpoint session -> TyEndpoint (substituteSessionVar target replacement session)
    TyPendingRecv pending ->
      TyPendingRecv (pending
        { pendingContinuation = substituteSessionVar target replacement (pendingContinuation pending)
        })
    TyRefined binder inner proposition -> TyRefined binder (substituteTy target replacement inner) proposition
    other -> other

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
