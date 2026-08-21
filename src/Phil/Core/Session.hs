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
  , dualSession
  ) where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Context
  ( CheckError
  , ResourceContext
  , consumeLinear
  , insertBinding
  )
import Phil.Core.Syntax
  ( Branch (..)
  , GrammarId
  , Mode (Linear)
  , Name
  , Outcome
  , PendingRecvSpec (..)
  , Session (..)
  , Ty (..)
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
