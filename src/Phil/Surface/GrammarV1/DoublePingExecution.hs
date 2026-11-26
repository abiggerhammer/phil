{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Original-source reference execution through the two pre-Close prefixes.
module Phil.Surface.GrammarV1.DoublePingExecution
  ( runSelectedDoublePing
  , AdmissionError (..), StepFailure (..), Stage (..)
  , DoublePingRun, Snapshot, CommittedEvent, BinderIdentity
  , runInputs, runDeclarations, runSnapshots, runOutcome
  , snapshotStages, snapshotPositions, snapshotReceived, snapshotResources
  , snapshotOwners, snapshotEvents
  , binderIdentity, eventPositions, eventBinders, eventValue, eventKey
#ifdef PHIL_D3_INTERNAL_TEST
  , runInternalControls
#endif
  ) where

import Control.Monad (unless)
import qualified Data.ByteString as Bytes
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text.Encoding as UTF8
import Data.Word (Word8)
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.ConcurrencyRendezvousCertification
import Phil.Core.Context (ResourceContext (..))
#ifdef PHIL_D3_INTERNAL_TEST
import Phil.Core.Context (CheckError (..))
import Phil.Core.Session (SessionError (..))
#endif
import Phil.Core.Generic (strictGenericInstantiationPolicy)
import Phil.Core.Generic.StaticActual (GenericStaticActual (..))
import Phil.Core.Process
import Phil.Core.ProcessActivation
import Phil.Core.ProcessCausality
import Phil.Core.ProcessParticipants
import Phil.Core.ProcessRendezvous
import Phil.Core.Protocol
import Phil.Core.Protocol.Family
import Phil.Core.Static
import Phil.Core.Syntax (Mode (..), Name, Session (..), Ty (..))
import Phil.Surface.GrammarV1.ArchitectureComponentActivation
import Phil.Surface.GrammarV1.ArchitectureSurface
import Phil.Surface.GrammarV1.BinderScope
import Phil.Surface.GrammarV1.ComponentTwoStepChain
import Phil.Surface.GrammarV1.DoublePingOrigin
import Phil.Surface.GrammarV1.ParameterBodyScope
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.PatternBinderScope
import Phil.Surface.GrammarV1.ProtocolEndpointType
import Phil.Surface.GrammarV1.ProtocolRoles
import Phil.Surface.Syntax (Located (..), SourceSpan, sourcePointOffset, sourceSpanStart)
import qualified Data.Text as Text

data AdmissionError
  = UnselectedSource
  | UnselectedSidecar
  | InvalidEntries
  | OriginRejected CandidateError
  | CheckedSourceRelation
  | ActivationRejected ConcurrencyRendezvousCertificationError
  | ActivationContextRejected GrammarV1ArchitectureComponentActivationError
  | InitialNativeStateRejected ProcessRendezvousError
  | InitialEndpointRelation
  deriving (Eq, Show)

data Stage = First | Second | PreClose
  deriving (Eq, Show)

data StepFailure
  = NoD3Successor
  | SourceCursorMismatch
  | SourceBinderMismatch
  | ReceiveDestinationOccupied
  | SourcePayloadUnavailable
  | NativePredecessorMismatch
  | NativeEndpointRelation
  | NativeStepRejected ConcurrencyRendezvousCertificationError
  | EventRelation
  | CausalityRejected ProcessCausalityError
  deriving (Eq, Show)

data BinderIdentity = BinderIdentity ProcessKey GrammarV1BinderKey
  deriving (Eq, Ord, Show)

data Action = Action SourceSpan GrammarV1ResolvedBinder GrammarV1ResolvedBinder
  GrammarV1ResolvedBinder
  deriving (Eq, Show)

data Body = Body Action Action SourceSpan GrammarV1ResolvedBinder

data Lane = Lane ProcessKey ProtocolRoleKey ActivationOccurrenceKey Body

data AdmittedRun = AdmittedRun [DeclarationIdentity] (Word8, Word8) Lane Lane
  CertifiedRendezvousActivation CertifiedRendezvousProtocol ProcessCommunicationState

data StepState = StepState Stage Stage (Map.Map BinderIdentity Word8)
  ProcessCommunicationState (Maybe CertifiedRendezvousResult) [CommittedEvent]
  deriving (Eq, Show)

-- The exact source action pair, input state and opaque result are retained.
data CommittedEvent = CommittedEvent Stage ProcessEventKey (Action, Action)
  (BinderIdentity, BinderIdentity) Word8 ProcessCommunicationState
  CertifiedRendezvousResult
  deriving (Eq, Show)

data Snapshot = Snapshot Lane Lane StepState

data DoublePingRun = DoublePingRun AdmittedRun [Snapshot] (Either StepFailure ())

runInputs :: DoublePingRun -> (Word8, Word8)
runInputs (DoublePingRun (AdmittedRun _ inputs _ _ _ _ _) _ _) = inputs

runDeclarations :: DoublePingRun -> [DeclarationIdentity]
runDeclarations (DoublePingRun (AdmittedRun declarations _ _ _ _ _ _) _ _) = declarations

runSnapshots :: DoublePingRun -> [Snapshot]
runSnapshots (DoublePingRun _ snapshots _) = snapshots

runOutcome :: DoublePingRun -> Either StepFailure ()
runOutcome (DoublePingRun _ _ outcome) = outcome

snapshotStages :: Snapshot -> (Stage, Stage)
snapshotStages (Snapshot _ _ (StepState client server _ _ _ _)) = (client, server)

snapshotPositions :: Snapshot -> (SourceSpan, SourceSpan)
snapshotPositions (Snapshot (Lane _ _ _ client) (Lane _ _ _ server)
    (StepState clientStage serverStage _ _ _ _)) =
  (position clientStage client, position serverStage server)
  where
    position First (Body (Action location _ _ _) _ _ _) = location
    position Second (Body _ (Action location _ _ _) _ _) = location
    position PreClose (Body _ _ location _) = location

snapshotReceived :: Snapshot -> [(BinderIdentity, Word8)]
snapshotReceived (Snapshot _ (Lane process _ _ (Body first second _ _))
    (StepState _ _ store _ _ _)) =
  [(key, value) | action <- [first, second], let key = binding process (payload action)
                , Just value <- [Map.lookup key store]]

snapshotResources :: Snapshot -> Map.Map ProcessKey ResourceContext
snapshotResources (Snapshot _ _ (StepState _ _ _ native _ _)) =
  Map.map protocolResources (communicationProtocolContexts native)

snapshotOwners :: Snapshot -> RestrictedOwnerIndex
snapshotOwners (Snapshot _ _ (StepState _ _ _ native _ _)) = communicationRestrictedOwners native

snapshotEvents :: Snapshot -> [CommittedEvent]
snapshotEvents (Snapshot _ _ (StepState _ _ _ _ _ events)) = events

binderIdentity :: BinderIdentity -> (ProcessKey, DeclarationKey, Int)
binderIdentity (BinderIdentity process (GrammarV1BinderKey declaration ordinal)) =
  (process, declaration, ordinal)

eventPositions :: CommittedEvent -> (SourceSpan, SourceSpan)
eventPositions (CommittedEvent _ _ (Action send _ _ _, Action receive _ _ _) _ _ _ _) =
  (send, receive)

eventBinders :: CommittedEvent -> (BinderIdentity, BinderIdentity)
eventBinders (CommittedEvent _ _ _ binders _ _ _) = binders

eventValue :: CommittedEvent -> Word8
eventValue (CommittedEvent _ _ _ _ value _ _) = value

eventKey :: CommittedEvent -> Text
eventKey (CommittedEvent _ key _ _ _ _ _) = unProcessEventKey key

binding :: ProcessKey -> GrammarV1ResolvedBinder -> BinderIdentity
binding process = BinderIdentity process . grammarV1ResolvedBinderKey

payload :: Action -> GrammarV1ResolvedBinder
payload (Action _ _ _ value) = value

core :: GrammarV1ResolvedBinder -> Name
core = grammarV1ResolvedBinderCoreName

runSelectedDoublePing
  :: Bytes.ByteString -> Bytes.ByteString -> [(Text, Integer)]
  -> Either AdmissionError DoublePingRun
runSelectedDoublePing source sidecar entries = do
  (admitted, initial) <- admit source sidecar entries
  let first = [snapshot admitted initial]
  pure $ case extendPrefix admitted first (advance admitted initial) of
    (prefix, Left failure) -> DoublePingRun admitted prefix (Left failure)
    (prefix, Right middle) ->
      let (complete, outcome) = extendPrefix admitted prefix (advance admitted middle)
      in DoublePingRun admitted complete (fmap (const ()) outcome)

snapshot :: AdmittedRun -> StepState -> Snapshot
snapshot (AdmittedRun _ _ client server _ _ _) = Snapshot client server

extendPrefix
  :: AdmittedRun -> [Snapshot] -> Either StepFailure StepState
  -> ([Snapshot], Either StepFailure StepState)
extendPrefix admitted prefix attempt =
  case attempt of
    Left failure -> (prefix, Left failure)
    Right next -> (prefix ++ [snapshot admitted next], Right next)

sourceAnchor :: SourceAnchor
sourceAnchor = SourceAnchor
  "2fc0c4abe970f398b516a2bdff2000ac4d09333f"
  "76f1d238407397ec09d358a42ff9ebaac4c44909"
  "test/fixtures/fsem02-two-step-source-chain-v1/accepted.phil"
  "33687d0c4320dda4d136fa16038f4fad043d14e1367729b8db43044e2d5c51e7"

admit
  :: Bytes.ByteString -> Bytes.ByteString -> [(Text, Integer)]
  -> Either AdmissionError (AdmittedRun, StepState)
admit source sidecar entries = do
  require UnselectedSource (source == selectedSource)
  require UnselectedSidecar (sidecar == selectedSidecar)
  inputs <- checkedEntries entries
  candidate <- mapError OriginRejected $
    checkSelectedCandidate sourceAnchor (selectedSource, selectedSidecar) (source, sidecar)
  parsed <- mapError (OriginRejected . SourceParseFailure) $
    parseGrammarV1StructuralSource (anchorPath sourceAnchor) (UTF8.decodeUtf8 selectedSource)
  case (map (locatedValue . grammarV1Declaration . locatedValue) (grammarV1TopLevelDecls parsed),
        candidateDeclarations candidate, candidateActivation candidate, candidateSites candidate) of
    ([GrammarV1ProtocolDeclaration protocol, GrammarV1ComponentDeclaration client,
      GrammarV1ComponentDeclaration server, GrammarV1ArchitectureDeclaration architecture,
      GrammarV1ProgramDeclaration _],
     declarations@[protocolId, clientId, serverId, architectureId, _],
     [clientContract, serverContract], [clientSite, serverSite]) -> do
      let key = identityDeclarationKey
          graph = candidateGraph candidate
          network = candidateNetwork candidate
      family <- checkedMaybe $ grammarV1ClosedBinaryProtocolFamily
        (key protocolId) (identityInterfaceRevision protocolId) protocol
      certified <- mapError ActivationRejected $
        certifyRendezvousProtocol strictGenericInstantiationPolicy family [] []
      let instanceValue = certifiedRendezvousProtocolInstance certified
          revision = binaryProtocolInstanceRevision instanceValue
          clientRole = certifiedRendezvousPrimaryRole certified
          serverRole = certifiedRendezvousPeerRole certified
          resolutions = [GrammarV1ProtocolEndpointResolution
            (ReferencedGenericStaticActual (locatedValue (grammarV1ProtocolName protocol)))
            instanceValue]
      clientProjection <- mapError (const CheckedSourceRelation) (projectProtocolRole instanceValue clientRole)
      serverProjection <- mapError (const CheckedSourceRelation) (projectProtocolRole instanceValue serverRole)
      (clientBody, clientParams) <- sourceBody True resolutions clientProjection (key clientId) client
      (serverBody, serverParams) <- sourceBody False resolutions serverProjection (key serverId) server
      architectureSurface <- checkedMaybe $ grammarV1CheckedArchitectureSurface emptyStaticContext
        (key architectureId) (identityDefinitionRevision architectureId) architecture
      let contracts = map resolvedComponentActivationContract [clientContract, serverContract]
          items = checkedArchitectureItems architectureSurface
          entryMap = Map.fromList [("first", fst inputs), ("second", snd inputs)]
      (clientLane, clientTarget, clientEntries) <- qualifyLane network graph items
        revision clientRole clientId clientSite clientContract clientBody clientParams entryMap
      (serverLane, serverTarget, serverEntries) <- qualifyLane network graph items
        revision serverRole serverId serverSite serverContract serverBody serverParams entryMap
      require CheckedSourceRelation (length clientEntries == 2 && null serverEntries)
      let roles = map (ProtocolRoleOccurrence revision) [clientRole, serverRole]
          participants = zipWith ParticipantDeclaration roles
            (map InternalParticipantTarget [clientTarget, serverTarget])
      activation <- mapError ActivationRejected $
        certifyRendezvousActivation graph network contracts roles participants
      let activationState = certifiedRendezvousActivationState activation
          context resolved = mapError ActivationContextRejected $
            grammarV1ComponentProtocolContextFromActivation resolved activationState
      clientContext <- context clientContract
      serverContext <- context serverContract
      initial <- mapError InitialNativeStateRejected $
        communicationStateFromActivation activationState
          (Map.fromList [(laneProcess clientLane, clientContext), (laneProcess serverLane, serverContext)])
      let qualified = AdmittedRun declarations inputs clientLane serverLane activation certified initial
          state = StepState First First (Map.fromList clientEntries) initial Nothing []
      require InitialEndpointRelation (endpointsMatch qualified First initial)
      pure (qualified, state)
    _ -> Left CheckedSourceRelation

checkedEntries :: [(Text, Integer)] -> Either AdmissionError (Word8, Word8)
checkedEntries entries = case take 3 entries of
  [("first", first), ("second", second)] -> bounded first second
  [("second", second), ("first", first)] -> bounded first second
  _ -> Left InvalidEntries
  where
    bounded a b
      | all (\number -> number >= 0 && number <= 255) [a, b] =
          Right (fromInteger a, fromInteger b)
      | otherwise = Left InvalidEntries

qualifyLane
  :: ProcessNetwork -> ArchitectureInstanceGraph -> [GrammarV1CheckedArchitectureItem]
  -> ProtocolInstanceRevision -> ProtocolRoleKey -> DeclarationIdentity -> ProcessDeclarationSite
  -> GrammarV1ResolvedComponentActivation -> Body -> [GrammarV1ResolvedBinder]
  -> Map.Map Text Word8
  -> Either AdmissionError (Lane, InstanceKey, [(BinderIdentity, Word8)])
qualifyLane network graph items revision role componentIdentity site resolved body params input = do
  let contract = resolvedComponentActivationContract resolved
      process = activationContractProcess contract
  occurrence <- required (Map.lookup process (processNetworkPopulation network))
  let target = identityInstanceKey (processOccurrenceTarget occurrence)
      root = identityInstanceKey (architectureGraphRoot graph)
  require CheckedSourceRelation $
    processOccurrenceOwner occurrence == processNetworkRoot network
    && site == ScopedProcessDeclarationSite root (processSiteKey site) target
  owner <- required (Map.lookup root (architectureGraphInstances graph))
  let children = Map.toList (checkedArchitectureChildren owner)
      itemChildren = [label | GrammarV1CheckedArchitectureInstance label _ <- items]
      roleChildren = case role of
        ProtocolRoleKey "Client" -> take 1 itemChildren
        ProtocolRoleKey "Server" -> drop 1 itemChildren
        _ -> []
  child <- only roleChildren
  instanceNode <- required (Map.lookup target (architectureGraphInstances graph))
  require CheckedSourceRelation $
    length children == 2 && elem target (map snd children)
    && checkedArchitectureIdentity instanceNode == processOccurrenceTarget occurrence
    && architectureDeclarationIdentity (checkedArchitectureDescriptor instanceNode) == componentIdentity
  protocolLabel <- only [label | GrammarV1CheckedArchitectureProtocol label _ <- items]
  let roleName = protocolLabel <> "." <> unProtocolRoleKey role
  require CheckedSourceRelation $
    [destination | GrammarV1CheckedArchitectureRole name (GrammarV1CheckedInternalRoleTarget destination) <- items
                 , name == roleName] == [child]
  (endpointParameter, others) <- case params of
    first : rest -> Right (first, rest)
    [] -> Left CheckedSourceRelation
  endpoint <- only (resolvedComponentActivationProtocolEndpoints resolved)
  endpointBinding <- localBinding contract endpointParameter
  require CheckedSourceRelation $
    protocolEndpointName endpoint == core endpointParameter
    && protocolEndpointInstance endpoint == revision && protocolEndpointRole endpoint == role
    && activationBindingOrigin endpointBinding == ProtocolEndpointOrigin protocolLabel
    && boundTo items child endpointParameter == [roleName]
  sourceEntries <- traverse (entryBinding process contract child) others
  pure (Lane process role (activationOccurrenceKey endpointBinding) body, target, sourceEntries)
  where
    localBinding contract binder = only
      [item | item <- activationContractBindings contract, activationLocalName item == core binder]
    entryBinding process contract child binder = do
      item <- localBinding contract binder
      label <- only (boundTo items child binder)
      require CheckedSourceRelation $
        activationBindingOrigin item == RootEntryOrigin label
        && checkedBindingMode (activationCheckedTypeMode item) == Unrestricted
        && checkedBindingType (activationCheckedTypeMode item) == TyUInt 8
        && [ty | GrammarV1CheckedArchitectureEntry name ty _ <- items, name == label] == [TyUInt 8]
      value <- required (Map.lookup label input)
      pure (binding process binder, value)

boundTo
  :: [GrammarV1CheckedArchitectureItem] -> Text -> GrammarV1ResolvedBinder -> [Text]
boundTo items child binder =
  [right | GrammarV1CheckedArchitectureBind left right <- items
         , left == child <> "." <> grammarV1ResolvedBinderDisplayName binder]

sourceBody
  :: Bool -> [GrammarV1ProtocolEndpointResolution] -> ProtocolProjectionEvidence
  -> DeclarationKey -> GrammarV1ComponentDecl
  -> Either AdmissionError (Body, [GrammarV1ResolvedBinder])
sourceBody sending resolutions projection declaration component = do
  chain <- mapError (const CheckedSourceRelation) $
    (if sending then checkSendChain else checkReceiveChain) resolutions projection declaration component
  (maybeParameters, scope) <- mapError (const CheckedSourceRelation) $
    grammarV1ComponentParameterScope declaration component
  parameters <- required maybeParameters
  case grammarV1BlockStatements (locatedValue (grammarV1ComponentBody component)) of
    [Located _ (GrammarV1LetStatement p1 e1), Located _ (GrammarV1LetStatement p2 e2),
     Located _ (GrammarV1ExpressionStatement (Located closeSpan (GrammarV1CloseExpression operand)))] -> do
      (first@(Action _ initial middle _), afterFirst) <- sourceAction sending scope p1 e1
      (second@(Action _ beforeFinal final _), afterSecond) <- sourceAction sending afterFirst p2 e2
      closed <- local afterSecond operand
      require CheckedSourceRelation $
        core initial == chainBefore chain && core middle == chainMiddle chain
        && middle == beforeFinal && core final == chainFinal chain && final == closed
      pure (Body first second closeSpan closed, parameters)
    _ -> Left CheckedSourceRelation

sourceAction
  :: Bool -> GrammarV1LexicalScope -> Located GrammarV1Pattern -> Located GrammarV1Expression
  -> Either AdmissionError (Action, GrammarV1LexicalScope)
sourceAction sending before patternSource expression = do
  (binders, after) <- mapError (const CheckedSourceRelation) $
    grammarV1BindPattern GrammarV1LetPatternBinder patternSource before
  (old, next, valueBinder) <- case (sending, locatedValue expression, binders) of
    (True, GrammarV1SendExpression value predecessor, [successor]) ->
      (,,) <$> local before predecessor <*> pure successor <*> local before value
    (False, GrammarV1ReceiveExpression _ predecessor, [successor, receiver]) ->
      (,,) <$> local before predecessor <*> pure successor <*> pure receiver
    _ -> Left CheckedSourceRelation
  pure (Action (locatedSpan expression) old next valueBinder, after)

local
  :: GrammarV1LexicalScope -> Located GrammarV1Expression
  -> Either AdmissionError GrammarV1ResolvedBinder
local scope = fmap grammarV1CheckedLocalValueBinder . required
  . grammarV1CheckedLocalValueOccurrenceInScope scope

require :: e -> Bool -> Either e ()
require failure condition = unless condition (Left failure)

mapError :: (a -> b) -> Either a c -> Either b c
mapError wrap = either (Left . wrap) Right

required :: Maybe a -> Either AdmissionError a
required = maybe (Left CheckedSourceRelation) Right

only :: [a] -> Either AdmissionError a
only [value] = Right value
only _ = Left CheckedSourceRelation

checkedMaybe :: Maybe (Either e a) -> Either AdmissionError a
checkedMaybe value = required value >>= mapError (const CheckedSourceRelation)

laneProcess :: Lane -> ProcessKey
laneProcess (Lane process _ _ _) = process

stageActions :: Stage -> AdmittedRun -> Either StepFailure (Action, Action)
stageActions stage (AdmittedRun _ _ (Lane _ _ _ (Body c1 c2 _ _))
    (Lane _ _ _ (Body s1 s2 _ _)) _ _ _) = case stage of
  First -> Right (c1, s1)
  Second -> Right (c2, s2)
  PreClose -> Left NoD3Successor

advance :: AdmittedRun -> StepState -> Either StepFailure StepState
advance admitted state@(StepState stage _ _ native predecessor _) = do
  actions <- stageActions stage admitted
  value <- qualifySource admitted state actions
  let AdmittedRun _ _ client server activation protocol _ = admitted
      request = requestFor protocol client server actions
  result <- certifyStep admitted state activation protocol native predecessor request message
  let event = observeEvent admitted stage actions value native result
      events = candidateEvents state event
  commitStep admitted state actions value result events (eventSequences client server events)

qualifySource :: AdmittedRun -> StepState -> (Action, Action) -> Either StepFailure Word8
qualifySource admitted (StepState stage serverStage store native _ history) actions@(send, receive) = do
  require SourceCursorMismatch $
    stage == serverStage && map eventStage history == case stage of
      First -> []
      Second -> [First]
      PreClose -> [First, Second]
  expected <- stageActions stage admitted
  require SourceBinderMismatch (actions == expected)
  let AdmittedRun _ _ client server _ _ _ = admitted
  require ReceiveDestinationOccupied $
    Map.notMember (binding (laneProcess server) (payload receive)) store
  require NativeEndpointRelation (endpointsMatch admitted stage native)
  maybe (Left SourcePayloadUnavailable) Right (Map.lookup (binding (laneProcess client) (payload send)) store)
  where
    eventStage (CommittedEvent stageValue _ _ _ _ _ _) = stageValue

requestFor
  :: CertifiedRendezvousProtocol -> Lane -> Lane -> (Action, Action) -> ProcessRendezvousRequest
requestFor protocol client server (send, receive) = SendReceiveRendezvous (side client send) (side server receive)
  where
    revision = binaryProtocolInstanceRevision (certifiedRendezvousProtocolInstance protocol)
    side (Lane process role _ _) (Action _ predecessor successor _) =
      ProcessRendezvousSide process (core predecessor) (core successor) revision role

certifyStep
  :: AdmittedRun -> StepState -> CertifiedRendezvousActivation -> CertifiedRendezvousProtocol
  -> ProcessCommunicationState -> Maybe CertifiedRendezvousResult -> ProcessRendezvousRequest
  -> RendezvousMessageEvidence -> Either StepFailure CertifiedRendezvousResult
certifyStep (AdmittedRun _ _ _ _ admittedActivation admittedProtocol initial)
    (StepState stage _ _ native predecessor _) activation protocol observed selected request evidence = do
  require NativePredecessorMismatch (observed == native && selected == predecessor)
  require NativeEndpointRelation (activation == admittedActivation && protocol == admittedProtocol)
  case (stage, selected) of
    (First, Nothing) | observed == initial -> mapError NativeStepRejected $
      certifyProcessRendezvous activation protocol (communicationProtocolContexts observed) request evidence
    (Second, Just previous) -> mapError NativeStepRejected $
      certifyProcessRendezvousSuccessor activation protocol previous request evidence
    _ -> Left NativePredecessorMismatch

message :: RendezvousMessageEvidence
message = RendezvousMessageEvidence ty form $
  BoundaryMessageContract "phil.doubleping.intrinsic-u8.v1" ty form (BoundaryMessageAdmittedLeaf "U8")
  where
    ty = TyUInt 8
    form = SemanticOrdered [SemanticAtom "uint", SemanticAtom "8"]

endpointsMatch :: AdmittedRun -> Stage -> ProcessCommunicationState -> Bool
endpointsMatch (AdmittedRun _ _ client server _ protocol _) stage native =
  Map.size contexts == 2 && Map.size owners == 2 && verifyLane client && verifyLane server
  where
    contexts = communicationProtocolContexts native
    owners = communicationRestrictedOwners native
    instanceValue = certifiedRendezvousProtocolInstance protocol
    verifyLane (Lane process role occurrence body) =
      case (Map.lookup process contexts, projectProtocolRole instanceValue role) of
        (Just context, Right projection) ->
          let name = core (currentBinder stage body)
              revision = binaryProtocolInstanceRevision instanceValue
          in case sessionAt stage (protocolProjectionSession projection) of
               Just session ->
                 protocolEndpoints context == Map.singleton name (ProtocolEndpointBinding name revision role session)
                 && linearBindings (protocolResources context) == Map.singleton name (TyEndpoint session)
                 && Map.lookup occurrence owners == Just (process, name)
               Nothing -> False
        _ -> False
    currentBinder First (Body (Action _ before _ _) _ _ _) = before
    currentBinder Second (Body _ (Action _ before _ _) _ _) = before
    currentBinder PreClose (Body _ _ _ close) = close
    sessionAt First session = Just session
    sessionAt Second session = nextSession session
    sessionAt PreClose session = nextSession session >>= nextSession
    nextSession (Send _ (TyUInt 8) next) = Just next
    nextSession (Receive _ (TyUInt 8) next) = Just next
    nextSession _ = Nothing

observeEvent
  :: AdmittedRun -> Stage -> (Action, Action) -> Word8 -> ProcessCommunicationState
  -> CertifiedRendezvousResult -> CommittedEvent
observeEvent (AdmittedRun _ _ client server _ _ _) stage actions@(send, receive) value native result =
  CommittedEvent stage key actions
    (binding (laneProcess client) (payload send), binding (laneProcess server) (payload receive))
    value native result
  where
    -- Invocation-local event identity incorporates the actual two occurrences.
    key = ProcessEventKey $ Text.intercalate ":" $
      "phil.doubleping.rendezvous" : Text.pack (show stage) : map offset [send, receive]
    offset (Action location _ _ _) = Text.pack (show (sourcePointOffset (sourceSpanStart location)))

candidateEvents :: StepState -> CommittedEvent -> [CommittedEvent]
candidateEvents (StepState _ _ _ _ _ history) event = history ++ [event]

eventSequences :: Lane -> Lane -> [CommittedEvent] -> [(ProcessKey, [ProcessEventKey])]
eventSequences client server events =
  [(process, [key | CommittedEvent _ key _ _ _ _ result <- events, contains process result])
   | process <- map laneProcess [client, server]]
  where
    contains process result =
      let cause = certifiedRendezvousCausality result
      in process == certifiedRendezvousSenderProcess cause || process == certifiedRendezvousReceiverProcess cause

commitStep
  :: AdmittedRun -> StepState -> (Action, Action) -> Word8 -> CertifiedRendezvousResult
  -> [CommittedEvent] -> [(ProcessKey, [ProcessEventKey])] -> Either StepFailure StepState
commitStep admitted state@(StepState stage _ store native previous _) actions@(_, receive) value result events sequences = do
  next <- case stage of
    First -> Right Second
    Second -> Right PreClose
    PreClose -> Left NoD3Successor
  let successor = certifiedRendezvousState result
      AdmittedRun _ _ client server activation _ _ = admitted
      event = observeEvent admitted stage actions value native result
      receiver = binding (laneProcess server) (payload receive)
  require NativeEndpointRelation $
    certifiedRendezvousActivationMatches activation result
    && endpointsMatch admitted next successor
    && unchangedValues native successor
    && Just result /= previous
  require EventRelation (events == candidateEvents state event)
  let asEvent (CommittedEvent _ key _ _ _ _ executed) =
        ProcessEvent key (certifiedRendezvousEventKind (certifiedRendezvousCausality executed))
  qualifyCausality client server (map asEvent events) sequences
  pure (StepState next next (Map.insert receiver value store) successor (Just result) events)

unchangedValues :: ProcessCommunicationState -> ProcessCommunicationState -> Bool
unchangedValues before after =
  Map.map frame (communicationProtocolContexts before) ==
    Map.map frame (communicationProtocolContexts after)
  where
    frame context = let resources = protocolResources context
      in (unrestrictedBindings resources, affineBindings resources)

qualifyCausality
  :: Lane -> Lane -> [ProcessEvent] -> [(ProcessKey, [ProcessEventKey])] -> Either StepFailure ()
qualifyCausality client server events sequences = do
  let sender = laneProcess client
      receiver = laneProcess server
      keys = map processEventKey events
      participants = SynchronousRendezvousEvent sender receiver
  require EventRelation $
    not (null keys) && all ((== participants) . processEventKind) events
    && sequences == [(sender, keys), (receiver, keys)]
  order <- mapError CausalityRejected (buildProcessPartialOrder events sequences [])
  case keys of
    [_] -> Right ()
    [first, second] -> require EventRelation (orderedBefore order first second)
    _ -> Left EventRelation

-- Literal bytes of the independently adopted packet at #7134143196.

selectedSource :: Bytes.ByteString
selectedSource = Bytes.concat
  [ "protocol DoublePing {\n"
  , "  role Client = send (x : U8) then send (y : U8) then end Done;\n"
  , "  role Server = receive (x : U8) then receive (y : U8) then end Done;\n"
  , "}\n"
  , "component ClientWorker(endpoint : Client[DoublePing], first : U8, second : U8) {\n"
  , "  let middle = send first on endpoint;\n"
  , "  let done = send second on middle;\n"
  , "  close done;\n"
  , "}\n"
  , "component ServerWorker(endpoint : Server[DoublePing]) {\n"
  , "  let (middle, received1) = receive U8 on endpoint;\n"
  , "  let (done, received2) = receive U8 on middle;\n"
  , "  close done;\n"
  , "}\n"
  , "architecture LocalDoublePing {\n"
  , "  instance client = ClientWorker;\n"
  , "  instance server = ServerWorker;\n"
  , "  process client_run = client;\n"
  , "  process server_run = server;\n"
  , "  protocol ping = DoublePing;\n"
  , "  role ping.Client = client;\n"
  , "  role ping.Server = server;\n"
  , "  entry first : U8;\n"
  , "  entry second : U8;\n"
  , "  bind client.endpoint = ping.Client;\n"
  , "  bind client.first = first;\n"
  , "  bind client.second = second;\n"
  , "  bind server.endpoint = ping.Server;\n"
  , "}\n"
  , "program main = instantiate LocalDoublePing;\n"
  ]

selectedSidecar :: Bytes.ByteString
selectedSidecar = Bytes.concat
  [ "FSEM03-DOUBLEPING-ORIGIN-V1\n"
  , "origin\tabiggerhammer/phil\t2fc0c4abe970f398b516a2bdff2000ac4d09333f\t76f1d238407397ec09d358a42ff9ebaac4c44909\tte"
  , "st/fixtures/fsem02-two-step-source-chain-v1/accepted.phil\n"
  , "source-sha256\t33687d0c4320dda4d136fa16038f4fad043d14e1367729b8db43044e2d5c51e7\n"
  , "grammar\tsha256:c352ccc31cd264af42ee7408426fabea871710d4905baef22c4cc209971ac1c5\n"
  , "offsets\tunicode-code-points\tzero-based\texclusive-end\n"
  , "decl\tDoublePing\tprotocol\tsite:8dfe\tdecl:3e98e243-262e-4c0b-bfc9-849a36a83f2d\t0\t158\tphil.interface.canonical.v1"
  , ":ordered[atom(40:phil.protocol.closed-binary-interface.v1),ordered[atom(18:generic-parameters)],ordered[atom(1"
  , "2:requirements)],ordered[atom(5:roles),ordered[atom(4:role),atom(6:Client),ordered[atom(4:send),ordered[atom(4"
  , ":uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]],or"
  , "dered[atom(4:role),atom(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:recei"
  , "ve),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]]\tphil.definition.canonical.v1:record"
  , "{10:definition=ordered[atom(41:phil.protocol.closed-binary-definition.v1),ordered[atom(40:phil.protocol.closed"
  , "-binary-interface.v1),ordered[atom(18:generic-parameters)],ordered[atom(12:requirements)],ordered[atom(5:roles"
  , "),ordered[atom(4:role),atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(4:send"
  , "),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]],ordered[atom(4:role),atom(6:Server),ord"
  , "ered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],o"
  , "rdered[atom(3:end),atom(4:Done)]]]]]]],18:interface_revision=atom(541:phil.interface.canonical.v1:ordered[atom"
  , "(40:phil.protocol.closed-binary-interface.v1),ordered[atom(18:generic-parameters)],ordered[atom(12:requirement"
  , "s)],ordered[atom(5:roles),ordered[atom(4:role),atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint),atom(1"
  , ":8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]],ordered[atom(4:"
  , "role),atom(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[a"
  , "tom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]])}\n"
  , "decl\tClientWorker\tcomponent\tsite:3cd1\tdecl:5d21799d-9609-4c0c-b4af-a599192d5bd9\t158\t330\tphil.interface.canonic"
  , "al.v1:ordered[atom(38:phil.component.doubleping-interface.v1),ordered[atom(10:parameters),ordered[atom(9:param"
  , "eter),atom(8:endpoint),atom(6:linear),ordered[atom(8:endpoint),atom(41:decl:3e98e243-262e-4c0b-bfc9-849a36a83f"
  , "2d),atom(541:phil.interface.canonical.v1:ordered[atom(40:phil.protocol.closed-binary-interface.v1),ordered[ato"
  , "m(18:generic-parameters)],ordered[atom(12:requirements)],ordered[atom(5:roles),ordered[atom(4:role),atom(6:Cli"
  , "ent),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)]"
  , ",ordered[atom(3:end),atom(4:Done)]]]],ordered[atom(4:role),atom(6:Server),ordered[atom(7:receive),ordered[atom"
  , "(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]"
  , "]]]]),atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:"
  , "uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]],ordered[atom(9:parameter),atom(5:first),atom(12:unrestr"
  , "icted),ordered[atom(4:uint),atom(1:8)]],ordered[atom(9:parameter),atom(6:second),atom(12:unrestricted),ordered"
  , "[atom(4:uint),atom(1:8)]]],ordered[atom(8:provides)]]\tphil.definition.canonical.v1:record{10:definition=ordere"
  , "d[atom(39:phil.component.doubleping-definition.v1),ordered[atom(38:phil.component.doubleping-interface.v1),ord"
  , "ered[atom(10:parameters),ordered[atom(9:parameter),atom(8:endpoint),atom(6:linear),ordered[atom(8:endpoint),at"
  , "om(41:decl:3e98e243-262e-4c0b-bfc9-849a36a83f2d),atom(541:phil.interface.canonical.v1:ordered[atom(40:phil.pro"
  , "tocol.closed-binary-interface.v1),ordered[atom(18:generic-parameters)],ordered[atom(12:requirements)],ordered["
  , "atom(5:roles),ordered[atom(4:role),atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered"
  , "[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]],ordered[atom(4:role),atom(6"
  , ":Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uint),"
  , "atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]]),atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint),at"
  , "om(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]],ordered[at"
  , "om(9:parameter),atom(5:first),atom(12:unrestricted),ordered[atom(4:uint),atom(1:8)]],ordered[atom(9:parameter)"
  , ",atom(6:second),atom(12:unrestricted),ordered[atom(4:uint),atom(1:8)]]],ordered[atom(8:provides)]],ordered[ato"
  , "m(4:body),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],atom(1:0),atom(1:3),atom(1:1)],ordered[atom(4:s"
  , "end),ordered[atom(4:uint),atom(1:8)],atom(1:3),atom(1:4),atom(1:2)],ordered[atom(5:close),atom(1:4)]]],18:inte"
  , "rface_revision=atom(1175:phil.interface.canonical.v1:ordered[atom(38:phil.component.doubleping-interface.v1),o"
  , "rdered[atom(10:parameters),ordered[atom(9:parameter),atom(8:endpoint),atom(6:linear),ordered[atom(8:endpoint),"
  , "atom(41:decl:3e98e243-262e-4c0b-bfc9-849a36a83f2d),atom(541:phil.interface.canonical.v1:ordered[atom(40:phil.p"
  , "rotocol.closed-binary-interface.v1),ordered[atom(18:generic-parameters)],ordered[atom(12:requirements)],ordere"
  , "d[atom(5:roles),ordered[atom(4:role),atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],order"
  , "ed[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]],ordered[atom(4:role),atom"
  , "(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uint"
  , "),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]]),atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint),"
  , "atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]],ordered["
  , "atom(9:parameter),atom(5:first),atom(12:unrestricted),ordered[atom(4:uint),atom(1:8)]],ordered[atom(9:paramete"
  , "r),atom(6:second),atom(12:unrestricted),ordered[atom(4:uint),atom(1:8)]]],ordered[atom(8:provides)]])}\n"
  , "decl\tServerWorker\tcomponent\tsite:0f94\tdecl:cc94aab1-3cdc-4a89-b755-f38218cda401\t330\t502\tphil.interface.canonic"
  , "al.v1:ordered[atom(38:phil.component.doubleping-interface.v1),ordered[atom(10:parameters),ordered[atom(9:param"
  , "eter),atom(8:endpoint),atom(6:linear),ordered[atom(8:endpoint),atom(41:decl:3e98e243-262e-4c0b-bfc9-849a36a83f"
  , "2d),atom(541:phil.interface.canonical.v1:ordered[atom(40:phil.protocol.closed-binary-interface.v1),ordered[ato"
  , "m(18:generic-parameters)],ordered[atom(12:requirements)],ordered[atom(5:roles),ordered[atom(4:role),atom(6:Cli"
  , "ent),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)]"
  , ",ordered[atom(3:end),atom(4:Done)]]]],ordered[atom(4:role),atom(6:Server),ordered[atom(7:receive),ordered[atom"
  , "(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]"
  , "]]]]),atom(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[a"
  , "tom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]],ordered[atom(8:provides)]]\tphil.definition.canon"
  , "ical.v1:record{10:definition=ordered[atom(39:phil.component.doubleping-definition.v1),ordered[atom(38:phil.com"
  , "ponent.doubleping-interface.v1),ordered[atom(10:parameters),ordered[atom(9:parameter),atom(8:endpoint),atom(6:"
  , "linear),ordered[atom(8:endpoint),atom(41:decl:3e98e243-262e-4c0b-bfc9-849a36a83f2d),atom(541:phil.interface.ca"
  , "nonical.v1:ordered[atom(40:phil.protocol.closed-binary-interface.v1),ordered[atom(18:generic-parameters)],orde"
  , "red[atom(12:requirements)],ordered[atom(5:roles),ordered[atom(4:role),atom(6:Client),ordered[atom(4:send),orde"
  , "red[atom(4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Do"
  , "ne)]]]],ordered[atom(4:role),atom(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[at"
  , "om(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]]),atom(6:Server),ordered[a"
  , "tom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered"
  , "[atom(3:end),atom(4:Done)]]]]]],ordered[atom(8:provides)]],ordered[atom(4:body),ordered[atom(7:receive),ordere"
  , "d[atom(4:uint),atom(1:8)],atom(1:0),atom(1:1),atom(1:2)],ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8"
  , ")],atom(1:1),atom(1:3),atom(1:4)],ordered[atom(5:close),atom(1:3)]]],18:interface_revision=atom(990:phil.inter"
  , "face.canonical.v1:ordered[atom(38:phil.component.doubleping-interface.v1),ordered[atom(10:parameters),ordered["
  , "atom(9:parameter),atom(8:endpoint),atom(6:linear),ordered[atom(8:endpoint),atom(41:decl:3e98e243-262e-4c0b-bfc"
  , "9-849a36a83f2d),atom(541:phil.interface.canonical.v1:ordered[atom(40:phil.protocol.closed-binary-interface.v1)"
  , ",ordered[atom(18:generic-parameters)],ordered[atom(12:requirements)],ordered[atom(5:roles),ordered[atom(4:role"
  , "),atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint"
  , "),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]],ordered[atom(4:role),atom(6:Server),ordered[atom(7:receive),"
  , "ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),at"
  , "om(4:Done)]]]]]]),atom(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receiv"
  , "e),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]],ordered[atom(8:provides)]])}\n"
  , "decl\tLocalDoublePing\tarchitecture\tsite:ad23\tdecl:4940750f-e575-4ea5-a63c-4b88bda44062\t502\t930\tphil.interface.c"
  , "anonical.v1:ordered[atom(41:phil.architecture.doubleping-interface.v1),ordered[atom(7:entries),ordered[atom(5:"
  , "entry),atom(5:first),atom(12:unrestricted),ordered[atom(4:uint),atom(1:8)]],ordered[atom(5:entry),atom(6:secon"
  , "d),atom(12:unrestricted),ordered[atom(4:uint),atom(1:8)]]],ordered[atom(18:external-contracts)]]\tphil.definiti"
  , "on.canonical.v1:record{10:definition=ordered[atom(42:phil.architecture.doubleping-definition.v1),ordered[atom("
  , "41:phil.architecture.doubleping-interface.v1),ordered[atom(7:entries),ordered[atom(5:entry),atom(5:first),atom"
  , "(12:unrestricted),ordered[atom(4:uint),atom(1:8)]],ordered[atom(5:entry),atom(6:second),atom(12:unrestricted),"
  , "ordered[atom(4:uint),atom(1:8)]]],ordered[atom(18:external-contracts)]],ordered[atom(8:children),ordered[atom("
  , "5:child),atom(9:slot:7acb),ordered[atom(8:identity),atom(41:decl:5d21799d-9609-4c0c-b4af-a599192d5bd9),atom(11"
  , "75:phil.interface.canonical.v1:ordered[atom(38:phil.component.doubleping-interface.v1),ordered[atom(10:paramet"
  , "ers),ordered[atom(9:parameter),atom(8:endpoint),atom(6:linear),ordered[atom(8:endpoint),atom(41:decl:3e98e243-"
  , "262e-4c0b-bfc9-849a36a83f2d),atom(541:phil.interface.canonical.v1:ordered[atom(40:phil.protocol.closed-binary-"
  , "interface.v1),ordered[atom(18:generic-parameters)],ordered[atom(12:requirements)],ordered[atom(5:roles),ordere"
  , "d[atom(4:role),atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(4:send),ordere"
  , "d[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]],ordered[atom(4:role),atom(6:Server),ordered[ato"
  , "m(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[a"
  , "tom(3:end),atom(4:Done)]]]]]]),atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[ato"
  , "m(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]],ordered[atom(9:parameter),atom"
  , "(5:first),atom(12:unrestricted),ordered[atom(4:uint),atom(1:8)]],ordered[atom(9:parameter),atom(6:second),atom"
  , "(12:unrestricted),ordered[atom(4:uint),atom(1:8)]]],ordered[atom(8:provides)]]),atom(2688:phil.definition.cano"
  , "nical.v1:record{10:definition=ordered[atom(39:phil.component.doubleping-definition.v1),ordered[atom(38:phil.co"
  , "mponent.doubleping-interface.v1),ordered[atom(10:parameters),ordered[atom(9:parameter),atom(8:endpoint),atom(6"
  , ":linear),ordered[atom(8:endpoint),atom(41:decl:3e98e243-262e-4c0b-bfc9-849a36a83f2d),atom(541:phil.interface.c"
  , "anonical.v1:ordered[atom(40:phil.protocol.closed-binary-interface.v1),ordered[atom(18:generic-parameters)],ord"
  , "ered[atom(12:requirements)],ordered[atom(5:roles),ordered[atom(4:role),atom(6:Client),ordered[atom(4:send),ord"
  , "ered[atom(4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:D"
  , "one)]]]],ordered[atom(4:role),atom(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[a"
  , "tom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]]),atom(6:Client),ordered["
  , "atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom"
  , "(3:end),atom(4:Done)]]]]],ordered[atom(9:parameter),atom(5:first),atom(12:unrestricted),ordered[atom(4:uint),a"
  , "tom(1:8)]],ordered[atom(9:parameter),atom(6:second),atom(12:unrestricted),ordered[atom(4:uint),atom(1:8)]]],or"
  , "dered[atom(8:provides)]],ordered[atom(4:body),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],atom(1:0),a"
  , "tom(1:3),atom(1:1)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],atom(1:3),atom(1:4),atom(1:2)],ordere"
  , "d[atom(5:close),atom(1:4)]]],18:interface_revision=atom(1175:phil.interface.canonical.v1:ordered[atom(38:phil."
  , "component.doubleping-interface.v1),ordered[atom(10:parameters),ordered[atom(9:parameter),atom(8:endpoint),atom"
  , "(6:linear),ordered[atom(8:endpoint),atom(41:decl:3e98e243-262e-4c0b-bfc9-849a36a83f2d),atom(541:phil.interface"
  , ".canonical.v1:ordered[atom(40:phil.protocol.closed-binary-interface.v1),ordered[atom(18:generic-parameters)],o"
  , "rdered[atom(12:requirements)],ordered[atom(5:roles),ordered[atom(4:role),atom(6:Client),ordered[atom(4:send),o"
  , "rdered[atom(4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4"
  , ":Done)]]]],ordered[atom(4:role),atom(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered"
  , "[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]]),atom(6:Client),ordere"
  , "d[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[at"
  , "om(3:end),atom(4:Done)]]]]],ordered[atom(9:parameter),atom(5:first),atom(12:unrestricted),ordered[atom(4:uint)"
  , ",atom(1:8)]],ordered[atom(9:parameter),atom(6:second),atom(12:unrestricted),ordered[atom(4:uint),atom(1:8)]]],"
  , "ordered[atom(8:provides)]])})]],ordered[atom(5:child),atom(9:slot:f2e7),ordered[atom(8:identity),atom(41:decl:"
  , "cc94aab1-3cdc-4a89-b755-f38218cda401),atom(990:phil.interface.canonical.v1:ordered[atom(38:phil.component.doub"
  , "leping-interface.v1),ordered[atom(10:parameters),ordered[atom(9:parameter),atom(8:endpoint),atom(6:linear),ord"
  , "ered[atom(8:endpoint),atom(41:decl:3e98e243-262e-4c0b-bfc9-849a36a83f2d),atom(541:phil.interface.canonical.v1:"
  , "ordered[atom(40:phil.protocol.closed-binary-interface.v1),ordered[atom(18:generic-parameters)],ordered[atom(12"
  , ":requirements)],ordered[atom(5:roles),ordered[atom(4:role),atom(6:Client),ordered[atom(4:send),ordered[atom(4:"
  , "uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]],ord"
  , "ered[atom(4:role),atom(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receiv"
  , "e),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]]),atom(6:Server),ordered[atom(7:recei"
  , "ve),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end"
  , "),atom(4:Done)]]]]]],ordered[atom(8:provides)]]),atom(2323:phil.definition.canonical.v1:record{10:definition=o"
  , "rdered[atom(39:phil.component.doubleping-definition.v1),ordered[atom(38:phil.component.doubleping-interface.v1"
  , "),ordered[atom(10:parameters),ordered[atom(9:parameter),atom(8:endpoint),atom(6:linear),ordered[atom(8:endpoin"
  , "t),atom(41:decl:3e98e243-262e-4c0b-bfc9-849a36a83f2d),atom(541:phil.interface.canonical.v1:ordered[atom(40:phi"
  , "l.protocol.closed-binary-interface.v1),ordered[atom(18:generic-parameters)],ordered[atom(12:requirements)],ord"
  , "ered[atom(5:roles),ordered[atom(4:role),atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],or"
  , "dered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]],ordered[atom(4:role),a"
  , "tom(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:u"
  , "int),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]]),atom(6:Server),ordered[atom(7:receive),ordered[atom(4:"
  , "uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]"
  , "],ordered[atom(8:provides)]],ordered[atom(4:body),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],atom"
  , "(1:0),atom(1:1),atom(1:2)],ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],atom(1:1),atom(1:3),atom(1:"
  , "4)],ordered[atom(5:close),atom(1:3)]]],18:interface_revision=atom(990:phil.interface.canonical.v1:ordered[atom"
  , "(38:phil.component.doubleping-interface.v1),ordered[atom(10:parameters),ordered[atom(9:parameter),atom(8:endpo"
  , "int),atom(6:linear),ordered[atom(8:endpoint),atom(41:decl:3e98e243-262e-4c0b-bfc9-849a36a83f2d),atom(541:phil."
  , "interface.canonical.v1:ordered[atom(40:phil.protocol.closed-binary-interface.v1),ordered[atom(18:generic-param"
  , "eters)],ordered[atom(12:requirements)],ordered[atom(5:roles),ordered[atom(4:role),atom(6:Client),ordered[atom("
  , "4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:en"
  , "d),atom(4:Done)]]]],ordered[atom(4:role),atom(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)"
  , "],ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]]),atom(6:Serve"
  , "r),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uint),atom(1"
  , ":8)],ordered[atom(3:end),atom(4:Done)]]]]]],ordered[atom(8:provides)]])})]]],ordered[atom(9:processes),ordered"
  , "[atom(18:root-owned-process),atom(12:process:9d3b),atom(9:slot:7acb)],ordered[atom(18:root-owned-process),atom"
  , "(12:process:f71c),atom(9:slot:f2e7)]],ordered[atom(19:protocol-occurrence),atom(4:ping),ordered[atom(8:identit"
  , "y),atom(41:decl:3e98e243-262e-4c0b-bfc9-849a36a83f2d),atom(541:phil.interface.canonical.v1:ordered[atom(40:phi"
  , "l.protocol.closed-binary-interface.v1),ordered[atom(18:generic-parameters)],ordered[atom(12:requirements)],ord"
  , "ered[atom(5:roles),ordered[atom(4:role),atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],or"
  , "dered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]],ordered[atom(4:role),a"
  , "tom(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:u"
  , "int),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]]),atom(1198:phil.definition.canonical.v1:record{10:defin"
  , "ition=ordered[atom(41:phil.protocol.closed-binary-definition.v1),ordered[atom(40:phil.protocol.closed-binary-i"
  , "nterface.v1),ordered[atom(18:generic-parameters)],ordered[atom(12:requirements)],ordered[atom(5:roles),ordered"
  , "[atom(4:role),atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(4:send),ordered"
  , "[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]],ordered[atom(4:role),atom(6:Server),ordered[atom"
  , "(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[at"
  , "om(3:end),atom(4:Done)]]]]]]],18:interface_revision=atom(541:phil.interface.canonical.v1:ordered[atom(40:phil."
  , "protocol.closed-binary-interface.v1),ordered[atom(18:generic-parameters)],ordered[atom(12:requirements)],order"
  , "ed[atom(5:roles),ordered[atom(4:role),atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],orde"
  , "red[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]],ordered[atom(4:role),ato"
  , "m(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uin"
  , "t),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]])})]],ordered[atom(5:roles),ordered[atom(13:internal-role)"
  , ",atom(6:Client),atom(9:slot:7acb)],ordered[atom(13:internal-role),atom(6:Server),atom(9:slot:f2e7)]],ordered[a"
  , "tom(8:bindings),ordered[atom(4:bind),atom(9:slot:7acb),atom(8:endpoint),ordered[atom(17:protocol-role-ref),ato"
  , "m(4:ping),atom(6:Client)]],ordered[atom(4:bind),atom(9:slot:7acb),atom(5:first),ordered[atom(9:entry-ref),atom"
  , "(5:first)]],ordered[atom(4:bind),atom(9:slot:7acb),atom(6:second),ordered[atom(9:entry-ref),atom(6:second)]],o"
  , "rdered[atom(4:bind),atom(9:slot:f2e7),atom(8:endpoint),ordered[atom(17:protocol-role-ref),atom(4:ping),atom(6:"
  , "Server)]]]],18:interface_revision=atom(332:phil.interface.canonical.v1:ordered[atom(41:phil.architecture.doubl"
  , "eping-interface.v1),ordered[atom(7:entries),ordered[atom(5:entry),atom(5:first),atom(12:unrestricted),ordered["
  , "atom(4:uint),atom(1:8)]],ordered[atom(5:entry),atom(6:second),atom(12:unrestricted),ordered[atom(4:uint),atom("
  , "1:8)]]],ordered[atom(18:external-contracts)]])}\n"
  , "decl\tmain\tprogram\tsite:6e5c\tdecl:a228fb5e-5be6-424e-bffe-b890252bbe12\t930\t974\tphil.interface.canonical.v1:orde"
  , "red[atom(36:phil.program.doubleping-interface.v1),ordered[atom(7:entries)],ordered[atom(7:exports)],ordered[at"
  , "om(11:observables)],ordered[atom(11:assumptions)]]\tphil.definition.canonical.v1:record{10:definition=ordered[a"
  , "tom(37:phil.program.doubleping-definition.v1),ordered[atom(36:phil.program.doubleping-interface.v1),ordered[at"
  , "om(7:entries)],ordered[atom(7:exports)],ordered[atom(11:observables)],ordered[atom(11:assumptions)]],ordered[a"
  , "tom(11:instantiate),ordered[atom(8:identity),atom(41:decl:4940750f-e575-4ea5-a63c-4b88bda44062),atom(332:phil."
  , "interface.canonical.v1:ordered[atom(41:phil.architecture.doubleping-interface.v1),ordered[atom(7:entries),orde"
  , "red[atom(5:entry),atom(5:first),atom(12:unrestricted),ordered[atom(4:uint),atom(1:8)]],ordered[atom(5:entry),a"
  , "tom(6:second),atom(12:unrestricted),ordered[atom(4:uint),atom(1:8)]]],ordered[atom(18:external-contracts)]]),a"
  , "tom(10950:phil.definition.canonical.v1:record{10:definition=ordered[atom(42:phil.architecture.doubleping-defin"
  , "ition.v1),ordered[atom(41:phil.architecture.doubleping-interface.v1),ordered[atom(7:entries),ordered[atom(5:en"
  , "try),atom(5:first),atom(12:unrestricted),ordered[atom(4:uint),atom(1:8)]],ordered[atom(5:entry),atom(6:second)"
  , ",atom(12:unrestricted),ordered[atom(4:uint),atom(1:8)]]],ordered[atom(18:external-contracts)]],ordered[atom(8:"
  , "children),ordered[atom(5:child),atom(9:slot:7acb),ordered[atom(8:identity),atom(41:decl:5d21799d-9609-4c0c-b4a"
  , "f-a599192d5bd9),atom(1175:phil.interface.canonical.v1:ordered[atom(38:phil.component.doubleping-interface.v1),"
  , "ordered[atom(10:parameters),ordered[atom(9:parameter),atom(8:endpoint),atom(6:linear),ordered[atom(8:endpoint)"
  , ",atom(41:decl:3e98e243-262e-4c0b-bfc9-849a36a83f2d),atom(541:phil.interface.canonical.v1:ordered[atom(40:phil."
  , "protocol.closed-binary-interface.v1),ordered[atom(18:generic-parameters)],ordered[atom(12:requirements)],order"
  , "ed[atom(5:roles),ordered[atom(4:role),atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],orde"
  , "red[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]],ordered[atom(4:role),ato"
  , "m(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uin"
  , "t),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]]),atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint)"
  , ",atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]],ordered"
  , "[atom(9:parameter),atom(5:first),atom(12:unrestricted),ordered[atom(4:uint),atom(1:8)]],ordered[atom(9:paramet"
  , "er),atom(6:second),atom(12:unrestricted),ordered[atom(4:uint),atom(1:8)]]],ordered[atom(8:provides)]]),atom(26"
  , "88:phil.definition.canonical.v1:record{10:definition=ordered[atom(39:phil.component.doubleping-definition.v1),"
  , "ordered[atom(38:phil.component.doubleping-interface.v1),ordered[atom(10:parameters),ordered[atom(9:parameter),"
  , "atom(8:endpoint),atom(6:linear),ordered[atom(8:endpoint),atom(41:decl:3e98e243-262e-4c0b-bfc9-849a36a83f2d),at"
  , "om(541:phil.interface.canonical.v1:ordered[atom(40:phil.protocol.closed-binary-interface.v1),ordered[atom(18:g"
  , "eneric-parameters)],ordered[atom(12:requirements)],ordered[atom(5:roles),ordered[atom(4:role),atom(6:Client),o"
  , "rdered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],order"
  , "ed[atom(3:end),atom(4:Done)]]]],ordered[atom(4:role),atom(6:Server),ordered[atom(7:receive),ordered[atom(4:uin"
  , "t),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]]),"
  , "atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),"
  , "atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]],ordered[atom(9:parameter),atom(5:first),atom(12:unrestricted)"
  , ",ordered[atom(4:uint),atom(1:8)]],ordered[atom(9:parameter),atom(6:second),atom(12:unrestricted),ordered[atom("
  , "4:uint),atom(1:8)]]],ordered[atom(8:provides)]],ordered[atom(4:body),ordered[atom(4:send),ordered[atom(4:uint)"
  , ",atom(1:8)],atom(1:0),atom(1:3),atom(1:1)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],atom(1:3),atom"
  , "(1:4),atom(1:2)],ordered[atom(5:close),atom(1:4)]]],18:interface_revision=atom(1175:phil.interface.canonical.v"
  , "1:ordered[atom(38:phil.component.doubleping-interface.v1),ordered[atom(10:parameters),ordered[atom(9:parameter"
  , "),atom(8:endpoint),atom(6:linear),ordered[atom(8:endpoint),atom(41:decl:3e98e243-262e-4c0b-bfc9-849a36a83f2d),"
  , "atom(541:phil.interface.canonical.v1:ordered[atom(40:phil.protocol.closed-binary-interface.v1),ordered[atom(18"
  , ":generic-parameters)],ordered[atom(12:requirements)],ordered[atom(5:roles),ordered[atom(4:role),atom(6:Client)"
  , ",ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ord"
  , "ered[atom(3:end),atom(4:Done)]]]],ordered[atom(4:role),atom(6:Server),ordered[atom(7:receive),ordered[atom(4:u"
  , "int),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]]"
  , "),atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint"
  , "),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]],ordered[atom(9:parameter),atom(5:first),atom(12:unrestricte"
  , "d),ordered[atom(4:uint),atom(1:8)]],ordered[atom(9:parameter),atom(6:second),atom(12:unrestricted),ordered[ato"
  , "m(4:uint),atom(1:8)]]],ordered[atom(8:provides)]])})]],ordered[atom(5:child),atom(9:slot:f2e7),ordered[atom(8:"
  , "identity),atom(41:decl:cc94aab1-3cdc-4a89-b755-f38218cda401),atom(990:phil.interface.canonical.v1:ordered[atom"
  , "(38:phil.component.doubleping-interface.v1),ordered[atom(10:parameters),ordered[atom(9:parameter),atom(8:endpo"
  , "int),atom(6:linear),ordered[atom(8:endpoint),atom(41:decl:3e98e243-262e-4c0b-bfc9-849a36a83f2d),atom(541:phil."
  , "interface.canonical.v1:ordered[atom(40:phil.protocol.closed-binary-interface.v1),ordered[atom(18:generic-param"
  , "eters)],ordered[atom(12:requirements)],ordered[atom(5:roles),ordered[atom(4:role),atom(6:Client),ordered[atom("
  , "4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:en"
  , "d),atom(4:Done)]]]],ordered[atom(4:role),atom(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)"
  , "],ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]]),atom(6:Serve"
  , "r),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uint),atom(1"
  , ":8)],ordered[atom(3:end),atom(4:Done)]]]]]],ordered[atom(8:provides)]]),atom(2323:phil.definition.canonical.v1"
  , ":record{10:definition=ordered[atom(39:phil.component.doubleping-definition.v1),ordered[atom(38:phil.component."
  , "doubleping-interface.v1),ordered[atom(10:parameters),ordered[atom(9:parameter),atom(8:endpoint),atom(6:linear)"
  , ",ordered[atom(8:endpoint),atom(41:decl:3e98e243-262e-4c0b-bfc9-849a36a83f2d),atom(541:phil.interface.canonical"
  , ".v1:ordered[atom(40:phil.protocol.closed-binary-interface.v1),ordered[atom(18:generic-parameters)],ordered[ato"
  , "m(12:requirements)],ordered[atom(5:roles),ordered[atom(4:role),atom(6:Client),ordered[atom(4:send),ordered[ato"
  , "m(4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]"
  , ",ordered[atom(4:role),atom(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:re"
  , "ceive),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]]),atom(6:Server),ordered[atom(7:r"
  , "eceive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(3"
  , ":end),atom(4:Done)]]]]]],ordered[atom(8:provides)]],ordered[atom(4:body),ordered[atom(7:receive),ordered[atom("
  , "4:uint),atom(1:8)],atom(1:0),atom(1:1),atom(1:2)],ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],atom"
  , "(1:1),atom(1:3),atom(1:4)],ordered[atom(5:close),atom(1:3)]]],18:interface_revision=atom(990:phil.interface.ca"
  , "nonical.v1:ordered[atom(38:phil.component.doubleping-interface.v1),ordered[atom(10:parameters),ordered[atom(9:"
  , "parameter),atom(8:endpoint),atom(6:linear),ordered[atom(8:endpoint),atom(41:decl:3e98e243-262e-4c0b-bfc9-849a3"
  , "6a83f2d),atom(541:phil.interface.canonical.v1:ordered[atom(40:phil.protocol.closed-binary-interface.v1),ordere"
  , "d[atom(18:generic-parameters)],ordered[atom(12:requirements)],ordered[atom(5:roles),ordered[atom(4:role),atom("
  , "6:Client),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom("
  , "1:8)],ordered[atom(3:end),atom(4:Done)]]]],ordered[atom(4:role),atom(6:Server),ordered[atom(7:receive),ordered"
  , "[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Do"
  , "ne)]]]]]]),atom(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),orde"
  , "red[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]],ordered[atom(8:provides)]])})]]],ordered[at"
  , "om(9:processes),ordered[atom(18:root-owned-process),atom(12:process:9d3b),atom(9:slot:7acb)],ordered[atom(18:r"
  , "oot-owned-process),atom(12:process:f71c),atom(9:slot:f2e7)]],ordered[atom(19:protocol-occurrence),atom(4:ping)"
  , ",ordered[atom(8:identity),atom(41:decl:3e98e243-262e-4c0b-bfc9-849a36a83f2d),atom(541:phil.interface.canonical"
  , ".v1:ordered[atom(40:phil.protocol.closed-binary-interface.v1),ordered[atom(18:generic-parameters)],ordered[ato"
  , "m(12:requirements)],ordered[atom(5:roles),ordered[atom(4:role),atom(6:Client),ordered[atom(4:send),ordered[ato"
  , "m(4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]"
  , ",ordered[atom(4:role),atom(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:re"
  , "ceive),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]]),atom(1198:phil.definition.canon"
  , "ical.v1:record{10:definition=ordered[atom(41:phil.protocol.closed-binary-definition.v1),ordered[atom(40:phil.p"
  , "rotocol.closed-binary-interface.v1),ordered[atom(18:generic-parameters)],ordered[atom(12:requirements)],ordere"
  , "d[atom(5:roles),ordered[atom(4:role),atom(6:Client),ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],order"
  , "ed[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]],ordered[atom(4:role),atom"
  , "(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:receive),ordered[atom(4:uint"
  , "),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]]],18:interface_revision=atom(541:phil.interface.canonical.v"
  , "1:ordered[atom(40:phil.protocol.closed-binary-interface.v1),ordered[atom(18:generic-parameters)],ordered[atom("
  , "12:requirements)],ordered[atom(5:roles),ordered[atom(4:role),atom(6:Client),ordered[atom(4:send),ordered[atom("
  , "4:uint),atom(1:8)],ordered[atom(4:send),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]],o"
  , "rdered[atom(4:role),atom(6:Server),ordered[atom(7:receive),ordered[atom(4:uint),atom(1:8)],ordered[atom(7:rece"
  , "ive),ordered[atom(4:uint),atom(1:8)],ordered[atom(3:end),atom(4:Done)]]]]]])})]],ordered[atom(5:roles),ordered"
  , "[atom(13:internal-role),atom(6:Client),atom(9:slot:7acb)],ordered[atom(13:internal-role),atom(6:Server),atom(9"
  , ":slot:f2e7)]],ordered[atom(8:bindings),ordered[atom(4:bind),atom(9:slot:7acb),atom(8:endpoint),ordered[atom(17"
  , ":protocol-role-ref),atom(4:ping),atom(6:Client)]],ordered[atom(4:bind),atom(9:slot:7acb),atom(5:first),ordered"
  , "[atom(9:entry-ref),atom(5:first)]],ordered[atom(4:bind),atom(9:slot:7acb),atom(6:second),ordered[atom(9:entry-"
  , "ref),atom(6:second)]],ordered[atom(4:bind),atom(9:slot:f2e7),atom(8:endpoint),ordered[atom(17:protocol-role-re"
  , "f),atom(4:ping),atom(6:Server)]]]],18:interface_revision=atom(332:phil.interface.canonical.v1:ordered[atom(41:"
  , "phil.architecture.doubleping-interface.v1),ordered[atom(7:entries),ordered[atom(5:entry),atom(5:first),atom(12"
  , ":unrestricted),ordered[atom(4:uint),atom(1:8)]],ordered[atom(5:entry),atom(6:second),atom(12:unrestricted),ord"
  , "ered[atom(4:uint),atom(1:8)]]],ordered[atom(18:external-contracts)]])})],atom(77:phil.grammar-v1.program-insta"
  , "nce.v1:decl:a228fb5e-5be6-424e-bffe-b890252bbe12)]],18:interface_revision=atom(192:phil.interface.canonical.v1"
  , ":ordered[atom(36:phil.program.doubleping-interface.v1),ordered[atom(7:entries)],ordered[atom(7:exports)],order"
  , "ed[atom(11:observables)],ordered[atom(11:assumptions)]])}\n"
  , "root\tmain\tphil.grammar-v1.program-instance.v1:decl:a228fb5e-5be6-424e-bffe-b890252bbe12\tLocalDoublePing\n"
  , "child\tclient\tslot:7acb\tLocalDoublePing\tClientWorker\t535\t569\n"
  , "child\tserver\tslot:f2e7\tLocalDoublePing\tServerWorker\t569\t603\n"
  , "process\tclient_run\tprocess:9d3b\tphil.grammar-v1.program-instance.v1:decl:a228fb5e-5be6-424e-bffe-b890252bbe12\t"
  , "slot:7acb\t603\t634\n"
  , "process\tserver_run\tprocess:f71c\tphil.grammar-v1.program-instance.v1:decl:a228fb5e-5be6-424e-bffe-b890252bbe12\t"
  , "slot:f2e7\t634\t665\n"
  ]

#ifdef PHIL_D3_INTERNAL_TEST
-- Fixed fault controls compiled against these same definitions. The test-only
-- export accepts no candidate, continuation, state, or caller-controlled fault.
runInternalControls :: Either String [String]
runInternalControls = do
  (admitted, initial) <- displayError $
    admit selectedSource selectedSidecar [("first", 17), ("second", 17)]
  middle <- displayError $ advance admitted initial
  final <- displayError $ advance admitted middle
  let AdmittedRun declarations _ client server activation protocol _ = admitted
      firstPrefix = [snapshot admitted initial]
      secondPrefix = firstPrefix ++ [snapshot admitted middle]
      StepState _ _ _ _ later _ = final
  first@(send1, receive1) <- displayError $ stageActions First admitted
  second@(send2, receive2) <- displayError $ stageActions Second admitted
  let equalValueOperand = (replacePayload send2 send1, receive2)
      swappedReceiveOperand = (send2, replacePayload receive2 receive1)
  checks1 <- faultChecks admitted firstPrefix initial first second
  checks2 <- faultChecks admitted secondPrefix middle second first
  candidate <- displayError $
    checkSelectedCandidate sourceAnchor (selectedSource, selectedSidecar) (selectedSource, selectedSidecar)
  otherProtocol <- foreignProtocol declarations
  let StepState _ _ _ current previous _ = middle
      initialNative = nativeOf initial
      revision = binaryProtocolInstanceRevision (certifiedRendezvousProtocolInstance protocol)
      roles = [ProtocolRoleOccurrence revision role | Lane _ role _ _ <- [client, server]]
      network = candidateNetwork candidate
      graph = candidateGraph candidate
      contracts = map resolvedComponentActivationContract (candidateActivation candidate)
  case (roles, map (targetOf network) [client, server]) of
    ([clientRole, serverRole], [Just clientTarget, Just serverTarget]) -> do
      let participants = [ParticipantDeclaration clientRole (InternalParticipantTarget clientTarget),
                          ParticipantDeclaration serverRole (InternalParticipantTarget serverTarget)]
          alternatives = [ParticipantDeclaration clientRole (InternalParticipantTarget serverTarget),
                          ParticipantDeclaration serverRole (InternalParticipantTarget clientTarget)]
      foreignRoot <- maybe (Left "expected selected graph child") Right $
        Map.lookup clientTarget (architectureGraphInstances graph)
      let rootFault = certifyRendezvousActivation
            graph {architectureGraphRoot = checkedArchitectureIdentity foreignRoot} network contracts roles participants
      rootCheck <- case rootFault of
        Left _ -> Right "PASS: actual activation rejects foreign root before S0"
        Right _ -> Left "foreign activation root passed native certification"
      donor <- displayError $
        certifyRendezvousActivation graph network contracts roles alternatives
      more <- sequence
        [ refuse admitted firstPrefix "foreign role metadata before first native call" NativeEndpointRelation
            (qualifySource admitted (alterNative (alterRole client) initial) first >> Right initial)
        , refuse admitted firstPrefix "foreign process before first native call" NativeEndpointRelation
            (qualifySource admitted (alterNative (removeProcess client) initial) first >> Right initial)
        , refuse admitted firstPrefix "foreign nominal protocol before first native call" NativeEndpointRelation
            (certifyStep admitted initial activation otherProtocol initialNative Nothing
              (requestFor protocol client server first) message >> Right initial)
        , refuse admitted firstPrefix "independent valid donor activation at S0" NativeEndpointRelation
            (certifyStep admitted initial donor protocol initialNative Nothing
              (requestFor protocol client server first) message >> Right initial)
        , refuse admitted secondPrefix "independent valid donor activation at S1" NativeEndpointRelation
            (certifyStep admitted middle donor protocol current previous
              (requestFor protocol client server second) message >> Right middle)
        , refuse admitted secondPrefix "foreign nominal protocol at S1" NativeEndpointRelation
            (certifyStep admitted middle activation otherProtocol current previous
              (requestFor protocol client server second) message >> Right middle)
        , refuse admitted secondPrefix "same-valued wrong source send binder" SourceBinderMismatch
            (qualifySource admitted middle equalValueOperand >> Right middle)
        , refuse admitted secondPrefix "swapped receiver binder" SourceBinderMismatch
            (qualifySource admitted middle swappedReceiveOperand >> Right middle)
        , refuse admitted secondPrefix "wrong opaque predecessor at S1" NativePredecessorMismatch
            (certifyStep admitted middle activation protocol current later
              (requestFor protocol client server second) message >> Right middle)
        , refuse admitted secondPrefix "stale initial communication state at S1" NativePredecessorMismatch
            (certifyStep admitted middle activation protocol initialNative previous
              (requestFor protocol client server second) message >> Right middle)
        , refuse admitted (secondPrefix ++ [snapshot admitted final]) "D3 has no successor from pre-Close S2"
            NoD3Successor (advance admitted final)
        ]
      pure (rootCheck : checks1 ++ checks2 ++ more)
    _ -> Left "unrecognized native participant inventory"
  where
    targetOf network lane =
      identityInstanceKey . processOccurrenceTarget <$>
        Map.lookup (laneProcess lane) (processNetworkPopulation network)
    removeProcess lane native = native
      { communicationProtocolContexts = Map.delete (laneProcess lane) (communicationProtocolContexts native) }
    alterRole lane native = native
      { communicationProtocolContexts = Map.adjust change (laneProcess lane) (communicationProtocolContexts native) }
      where
        change context = context
          { protocolEndpoints = Map.map (\endpoint -> endpoint
              {protocolEndpointRole = ProtocolRoleKey "Foreign"}) (protocolEndpoints context) }

foreignProtocol :: [DeclarationIdentity] -> Either String CertifiedRendezvousProtocol
foreignProtocol declarations = do
  parsed <- displayError $
    parseGrammarV1StructuralSource (anchorPath sourceAnchor) (UTF8.decodeUtf8 selectedSource)
  case (declarations, map (locatedValue . grammarV1Declaration . locatedValue) (grammarV1TopLevelDecls parsed)) of
    (identity : _, GrammarV1ProtocolDeclaration protocol : _) -> do
      family <- displayError $ checkedMaybe $
        grammarV1ClosedBinaryProtocolFamily (DeclarationKey "foreign-doubleping-test")
          (identityInterfaceRevision identity) protocol
      displayError $ certifyRendezvousProtocol strictGenericInstantiationPolicy family [] []
    _ -> Left "expected protocol declaration for nominal negative"

faultChecks
  :: AdmittedRun -> [Snapshot] -> StepState -> (Action, Action) -> (Action, Action)
  -> Either String [String]
faultChecks admitted prefix committed@(StepState stage _ store native previous history)
    operands@(send, receive) (otherSend, _) = do
  let AdmittedRun _ _ client server activation protocol _ = admitted
      request = requestFor protocol client server operands
      label name = show stage <> " " <> name
      nativeCall = certifyStep admitted committed activation protocol native previous
      refuseHere name = refuse admitted prefix (label name)
      poisonedMessage = message
        {rendezvousMessageEvidenceContract = (rendezvousMessageEvidenceContract message)
          {boundaryMessageContractRevision = ""}}
      occupiedSource = StepState stage stage
        (Map.insert (binding (laneProcess server) (payload receive)) 17 store)
        native previous history
      wrongPC = StepState stage PreClose store native previous history
      occupied = core (payload send)
      duplicate = NativeStepRejected (ConcurrencyRendezvousNativeError
        (RendezvousProtocolError (laneProcess client)
          (ProtocolSessionError (SessionResourceError (DuplicateBinding occupied)))))
  value <- displayError $ qualifySource admitted committed operands
  result <- displayError $ nativeCall request message
  occupiedRequest <- case request of
    SendReceiveRendezvous sender receiver -> Right $
      SendReceiveRendezvous sender {rendezvousSuccessor = occupied} receiver
    _ -> Left "expected an actual Send/Receive request"
  let event = observeEvent admitted stage operands value native result
      events = candidateEvents committed event
      sequences = eventSequences client server events
      replaceLast substitute = history ++ [substitute]
      missing = history
      repeatedKey = replaceLast (rekey (case history of
        prior : _ -> eventKey prior
        [] -> eventKey event <> ":foreign") event)
      duplicateResult = events ++ [rekey "second-label-for-same-result" event]
      badSequence = map (\(process, keys) -> (process, drop 1 keys)) sequences
      badPair = replaceLast (replaceObservedActions (otherSend, receive) event)
      commit = commitStep admitted committed operands value result
      messageFailure = NativeStepRejected (ConcurrencyRendezvousMessageError BoundaryMessageContractRevisionEmpty)
  sequence
    [ refuseHere "wrong program counter" SourceCursorMismatch (qualifySource admitted wrongPC operands >> Right committed)
    , refuseHere "wrong lexical sender binder" SourceBinderMismatch
        (qualifySource admitted committed (replacePayload send otherSend, receive) >> Right committed)
    , refuseHere "occupied source receiver slot" ReceiveDestinationOccupied
        (qualifySource admitted occupiedSource operands >> Right committed)
    , refuseHere "occupied native successor resource" duplicate (nativeCall occupiedRequest message >> Right committed)
    , refuseHere "tentative transition refused by Message" messageFailure
        (nativeCall request poisonedMessage >> Right committed)
    , refuseHere "missing event" EventRelation (commit missing (eventSequences client server missing))
    , refuseHere "invalid or duplicate event key" EventRelation
        (commit repeatedKey (eventSequences client server repeatedKey))
    , refuseHere "two labels for one result" EventRelation
        (commit duplicateResult (eventSequences client server duplicateResult))
    , refuseHere "event names wrong source pair" EventRelation (commit badPair sequences)
    , refuseHere "wrong process sequence" EventRelation (commit events badSequence)
    , refuseHere "early Close at the selected action PC" SourceCursorMismatch
        (qualifySource admitted (StepState PreClose stage store native previous history) operands >> Right committed)
    ]
  where
    rekey key (CommittedEvent step _ actions binders value before result) =
      CommittedEvent step (ProcessEventKey key) actions binders value before result
    replaceObservedActions actions (CommittedEvent step key _ binders value before result) =
      CommittedEvent step key actions binders value before result

nativeOf :: StepState -> ProcessCommunicationState
nativeOf (StepState _ _ _ native _ _) = native

alterNative :: (ProcessCommunicationState -> ProcessCommunicationState) -> StepState -> StepState
alterNative change (StepState c s store native previous history) =
  StepState c s store (change native) previous history

replacePayload :: Action -> Action -> Action
replacePayload (Action location old next _) donor = Action location old next (payload donor)

refuse
  :: AdmittedRun -> [Snapshot] -> String -> StepFailure -> Either StepFailure StepState
  -> Either String String
refuse admitted prefix name expected attempt =
  case extendPrefix admitted prefix attempt of
    (retained, Left actual)
      | actual == expected && states retained == states prefix ->
          Right ("PASS: " <> name <> " preserved the complete committed prefix")
      | otherwise -> Left (name <> ": expected " <> show expected <> ", got " <> show actual)
    (_, Right _) -> Left (name <> ": unexpected new commit")
  where
    states snapshots = [state | Snapshot _ _ state <- snapshots]

displayError :: Show a => Either a b -> Either String b
displayError = mapError show
#endif
