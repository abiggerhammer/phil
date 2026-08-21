module Phil.Core.Recognition
  ( ReceiveFrameStep (..)
  , CommitReceiveStep (..)
  , PendingRawView
  , rawPendingOwner
  , rawGrammarId
  , rawFrameId
  , ParsedWitness
  , parsedPendingOwner
  , parsedGrammarId
  , parsedFrameId
  , parsedValueName
  , RecognitionFailure
  , recognitionPendingOwner
  , recognitionFailureGrammar
  , recognitionFailureFrame
  , recognitionFailureDetail
  , RecognitionError (..)
  , receiveFrame
  , beginRawLoan
  , trustedRecognitionSuccess
  , trustedRecognitionFailure
  , endRawLoan
  , commitReceive
  , failPendingRecognition
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Context
  ( CheckError (..)
  , ResourceContext (..)
  , consumeLinear
  , endSharedLoan
  , insertBinding
  , startSharedLoan
  )
import Phil.Core.Session (SessionError, exposeSessionHead)
import Phil.Core.Syntax
  ( FrameId
  , GrammarId
  , Mode (..)
  , Name
  , PendingRecvSpec (..)
  , Session (..)
  , Ty (..)
  )

data ReceiveFrameStep = ReceiveFrameStep
  { receivePendingName :: Name
  , receivePendingSpec :: PendingRecvSpec
  , receiveFrameContext :: ResourceContext
  }
  deriving (Eq, Show)

data CommitReceiveStep = CommitReceiveStep
  { commitParsedWitness :: ParsedWitness
  , commitSuccessor :: (Name, Session)
  , commitContext :: ResourceContext
  }
  deriving (Eq, Show)

data PendingRawView = PendingRawView Name GrammarId FrameId
  deriving (Eq, Show)

data ParsedWitness = ParsedWitness Name GrammarId FrameId Name
  deriving (Eq, Show)

data RecognitionFailure = RecognitionFailure Name GrammarId FrameId Text
  deriving (Eq, Show)

data RecognitionError
  = RecognitionResourceError CheckError
  | RecognitionSessionError SessionError
  | ExpectedGrammarBackedReceive Name Ty
  | RefinedGrammarReceiveRequiresValueChecking GrammarId
  | UnexpectedReceiveFrameHead Session
  | PendingReusesSourceEndpoint Name
  | ExpectedPendingReceive Name Ty
  | RawViewDoesNotMatchPending Name
  | RawLoanNotActive Name
  | ParsedEvidenceMismatch PendingRecvSpec ParsedWitness
  | RecognitionFailureMismatch PendingRecvSpec RecognitionFailure
  | SuccessorReusesIngressIdentity Name
  deriving (Eq, Show)

rawPendingOwner :: PendingRawView -> Name
rawPendingOwner (PendingRawView owner _ _) = owner

rawGrammarId :: PendingRawView -> GrammarId
rawGrammarId (PendingRawView _ grammar _) = grammar

rawFrameId :: PendingRawView -> FrameId
rawFrameId (PendingRawView _ _ frame) = frame

parsedPendingOwner :: ParsedWitness -> Name
parsedPendingOwner (ParsedWitness owner _ _ _) = owner

parsedGrammarId :: ParsedWitness -> GrammarId
parsedGrammarId (ParsedWitness _ grammar _ _) = grammar

parsedFrameId :: ParsedWitness -> FrameId
parsedFrameId (ParsedWitness _ _ frame _) = frame

parsedValueName :: ParsedWitness -> Name
parsedValueName (ParsedWitness _ _ _ valueName) = valueName

recognitionPendingOwner :: RecognitionFailure -> Name
recognitionPendingOwner (RecognitionFailure owner _ _ _) = owner

recognitionFailureGrammar :: RecognitionFailure -> GrammarId
recognitionFailureGrammar (RecognitionFailure _ grammar _ _) = grammar

recognitionFailureFrame :: RecognitionFailure -> FrameId
recognitionFailureFrame (RecognitionFailure _ _ frame _) = frame

recognitionFailureDetail :: RecognitionFailure -> Text
recognitionFailureDetail (RecognitionFailure _ _ _ detail) = detail

receiveFrame
  :: Name
  -> Name
  -> FrameId
  -> ResourceContext
  -> Either RecognitionError ReceiveFrameStep
receiveFrame endpoint pendingName frameId context
  | endpoint == pendingName = Left (PendingReusesSourceEndpoint endpoint)
  | otherwise = do
      (endpointTy, consumed) <- mapLeft RecognitionResourceError (consumeLinear endpoint context)
      session <-
        case endpointTy of
          TyEndpoint endpointSession ->
            mapLeft RecognitionSessionError (exposeSessionHead endpointSession)
          other -> Left (ExpectedGrammarBackedReceive endpoint other)
      case session of
        Receive binder (TyFrame grammar) continuation -> do
          let pending = PendingRecvSpec
                { pendingSourceEndpoint = endpoint
                , pendingGrammar = grammar
                , pendingFrame = frameId
                , pendingBinder = binder
                , pendingContinuation = continuation
                }
          withPending <- mapLeft RecognitionResourceError $
            insertBinding Linear pendingName (TyPendingRecv pending) consumed
          pure ReceiveFrameStep
            { receivePendingName = pendingName
            , receivePendingSpec = pending
            , receiveFrameContext = withPending
            }
        Receive _ messageTy _
          | Just grammar <- frameGrammar messageTy ->
              Left (RefinedGrammarReceiveRequiresValueChecking grammar)
        Receive _ messageTy _ -> Left (ExpectedGrammarBackedReceive endpoint messageTy)
        other -> Left (UnexpectedReceiveFrameHead other)

beginRawLoan
  :: Name
  -> ResourceContext
  -> Either RecognitionError (PendingRawView, ResourceContext)
beginRawLoan pendingName context = do
  pending <- pendingSpecFor pendingName context
  borrowed <- mapLeft RecognitionResourceError (startSharedLoan pendingName context)
  pure
    ( PendingRawView pendingName (pendingGrammar pending) (pendingFrame pending)
    , borrowed
    )

trustedRecognitionSuccess
  :: PendingRawView
  -> Name
  -> ResourceContext
  -> Either RecognitionError ParsedWitness
trustedRecognitionSuccess raw valueName context = do
  _ <- ensureRawLoanActive raw context
  pure (ParsedWitness
    (rawPendingOwner raw)
    (rawGrammarId raw)
    (rawFrameId raw)
    valueName)

trustedRecognitionFailure
  :: PendingRawView
  -> Text
  -> ResourceContext
  -> Either RecognitionError RecognitionFailure
trustedRecognitionFailure raw detail context = do
  _ <- ensureRawLoanActive raw context
  pure (RecognitionFailure
    (rawPendingOwner raw)
    (rawGrammarId raw)
    (rawFrameId raw)
    detail)

endRawLoan
  :: PendingRawView
  -> ResourceContext
  -> Either RecognitionError ResourceContext
endRawLoan raw context = do
  _ <- ensureRawLoanActive raw context
  mapLeft RecognitionResourceError (endSharedLoan (rawPendingOwner raw) context)

commitReceive
  :: Name
  -> Name
  -> ParsedWitness
  -> ResourceContext
  -> Either RecognitionError CommitReceiveStep
commitReceive pendingName successor parsed context = do
  pending <- pendingSpecFor pendingName context
  ensureParsedMatches pendingName pending parsed
  if successor == pendingName || successor == pendingSourceEndpoint pending
    then Left (SuccessorReusesIngressIdentity successor)
    else do
      (_, consumed) <- mapLeft RecognitionResourceError (consumeLinear pendingName context)
      continued <- mapLeft RecognitionResourceError $
        insertBinding Linear successor (TyEndpoint (pendingContinuation pending)) consumed
      pure CommitReceiveStep
        { commitParsedWitness = parsed
        , commitSuccessor = (successor, pendingContinuation pending)
        , commitContext = continued
        }

failPendingRecognition
  :: Name
  -> RecognitionFailure
  -> ResourceContext
  -> Either RecognitionError ResourceContext
failPendingRecognition pendingName failure context = do
  pending <- pendingSpecFor pendingName context
  ensureFailureMatches pendingName pending failure
  (_, consumed) <- mapLeft RecognitionResourceError (consumeLinear pendingName context)
  pure consumed

pendingSpecFor :: Name -> ResourceContext -> Either RecognitionError PendingRecvSpec
pendingSpecFor pendingName context =
  case Map.lookup pendingName (linearBindings context) of
    Just (TyPendingRecv pending) -> Right pending
    Just other -> Left (ExpectedPendingReceive pendingName other)
    Nothing ->
      case () of
        _ | Map.member pendingName (affineBindings context) ->
              Left (RecognitionResourceError (WrongStructuralMode pendingName Linear Affine))
          | Map.member pendingName (unrestrictedBindings context) ->
              Left (RecognitionResourceError (WrongStructuralMode pendingName Linear Unrestricted))
          | otherwise -> Left (RecognitionResourceError (UnknownBinding pendingName))

ensureRawLoanActive
  :: PendingRawView
  -> ResourceContext
  -> Either RecognitionError PendingRecvSpec
ensureRawLoanActive raw context = do
  pending <- pendingSpecFor (rawPendingOwner raw) context
  if rawGrammarId raw /= pendingGrammar pending || rawFrameId raw /= pendingFrame pending
    then Left (RawViewDoesNotMatchPending (rawPendingOwner raw))
    else if Set.member (rawPendingOwner raw) (sharedLoans context)
      then Right pending
      else Left (RawLoanNotActive (rawPendingOwner raw))

ensureParsedMatches :: Name -> PendingRecvSpec -> ParsedWitness -> Either RecognitionError ()
ensureParsedMatches pendingName pending parsed
  | parsedPendingOwner parsed == pendingName
      && parsedGrammarId parsed == pendingGrammar pending
      && parsedFrameId parsed == pendingFrame pending = Right ()
  | otherwise = Left (ParsedEvidenceMismatch pending parsed)

ensureFailureMatches :: Name -> PendingRecvSpec -> RecognitionFailure -> Either RecognitionError ()
ensureFailureMatches pendingName pending failure
  | recognitionPendingOwner failure == pendingName
      && recognitionFailureGrammar failure == pendingGrammar pending
      && recognitionFailureFrame failure == pendingFrame pending = Right ()
  | otherwise = Left (RecognitionFailureMismatch pending failure)

frameGrammar :: Ty -> Maybe GrammarId
frameGrammar ty =
  case ty of
    TyFrame grammar -> Just grammar
    TyRefined _ inner _ -> frameGrammar inner
    _ -> Nothing

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
