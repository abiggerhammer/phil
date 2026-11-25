{-# LANGUAGE OverloadedStrings #-}

-- | Bounded selected SteveGet reference interpreter.  Admission is over the
-- actual ordinary-Surface selector and full native Steve Core + exact plan,
-- not their lossy digests.  This module is a proposed FSEM-06 rule producer;
-- it is not a proof of native execution, or of Haskell/Rocq correspondence.
module Phil.Compiler.SelectedSteveGetCoreExecution
  ( SelectedSteveGetCore
  , prepareSelectedSteveGetCore
  , SelectedCoreWorld
  , newSelectedCoreWorld
  , TargetOrigin
  , CoreObservation (..)
  , CoreReceipt
  , receiptObservations
  , receiptConsumedResponses
  , receiptOriginPair
  , receiptMatchesContext
  , receiptMatchesOriginPair
  , CoreRunResult (..)
  , runSelectedSteveGetCore
  ) where

import Control.Concurrent.MVar (MVar, newMVar, putMVar, takeMVar)
import Control.Exception (mask, onException)
import Control.Monad (foldM, unless)
import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Data.Unique (Unique, newUnique)
import Data.Word (Word8)
import qualified FSEM06SteveGetNativeKernel as K
import qualified Phil.Compiler.RuntimeChoicePayload as P
import Phil.Core.Static (DeclarationKey (..), InstanceKey (..))
import Phil.Examples.Phase1.SystemsWitnesses (steveCoreProgram)
import qualified Phil.Surface.SelectedSteveGetExecution as S
import qualified Phil.Systems.GenericLowering as C

-- Positional, admission-only representation; no public record labels.
data SelectedSteveGetCore = SelectedSteveGetCore
  !S.SelectedSteveGet !C.CoreSystemsFunction !P.RuntimeChoicePayloadPlan
  deriving (Eq)

prepareSelectedSteveGetCore
  :: Text -> C.CoreSystemsProgram -> P.RuntimeChoicePayloadPlan
  -> Either Text SelectedSteveGetCore
prepareSelectedSteveGetCore raw program plan = do
  source <- mapError S.prepareSelectedSteveGet raw
  require (S.selectedDeclarationKey source == DeclarationKey "decl:steve.get"
    && S.selectedInstanceKey source == InstanceKey "inst:phase1.steve")
    "wrong selected source declaration/instance"
  -- Check raw containers before any Eq, lookup, Map projection or digest.
  mapError C.validateCoreNativeContainers program
  mapError C.validateCoreNativeContainers steveCoreProgram
  require (program == steveCoreProgram) "not the exact native Steve Core object"
  function <- findKey "SteveGet" (C.coreProgramFunctions program)
  require (C.coreFunctionKey function == "SteveGet"
    && C.coreFunctionEntry function == "get.entry")
    "wrong selected Core function/entry"
  let specs = P.runtimeChoicePayloadPlanSpecs plan
  require (Map.valid specs && all (Map.valid . P.runtimeChoicePayloadArms)
    (Map.elems specs)) "malformed payload-plan containers"
  recertified <- mapError (P.certifyRuntimeChoicePayloadPlan program) (Map.elems specs)
  expected <- mapError (P.certifyRuntimeChoicePayloadPlan program) exactSpecs
  require (recertified == plan && expected == plan)
    "wrong complete payload plan or recertified Core identity"
  role function "get.id" (C.CoreRuntimeScalar "ContentId[SHA256]")
  role function "get.bytes" (C.CoreOwnedBuffer "OwnedBytes")
  role function "get.bytes-view" (C.CoreBorrowedValue "get.bytes")
  encoded <- nativeSubject source function plan
  require (K.selected_native_accepts encoded) "proof-extracted full typed selector rejected"
  pure (SelectedSteveGetCore source function plan)

-- The exact full plan domain includes both StevePut sites, but only the
-- selected SteveGet function is executed here.  Native membership alone
-- does not distinguish get.id from the required owned-buffer destination.
exactSpecs :: [P.RuntimeChoicePayloadSpec]
exactSpecs =
  [ spec "StevePut" "put.entry" [arm "computed" "put.install" (Just "put.id")]
  , spec "StevePut" "put.install"
      [ arm "installed" "put.ok" Nothing
      , arm "already-exists" "put.ok" Nothing
      , arm "storage-failure" "put.failure" Nothing ]
  , spec "SteveGet" "get.entry"
      [ arm "found" "get.check" (Just "get.bytes")
      , arm "not-found" "get.not-found" Nothing
      , arm "storage-failure" "get.failure" Nothing ]
  , spec "SteveGet" "get.check"
      [arm "accepted" "get.ok" Nothing, arm "rejected" "get.integrity-failure" Nothing]
  ]
  where
    spec fn block arms = P.RuntimeChoicePayloadSpec
      (P.RuntimeChoiceSite fn block) (Map.fromList arms)
    arm label target value = (label, P.RuntimeChoicePayloadArm target value)

-- Direct native-to-extracted representation: UTF-8 byte lists, exact map
-- keys and internal keys, complete ordered operations/operands/arms/plan,
-- explicit optional realization and storage fields. Unsupported native
-- constructors reject; no projected hash, pretty printer, or caller proof.
nativeName :: Text -> [K.Nat]
nativeName = map byteNat . BS.unpack . TextEncoding.encodeUtf8
  where
    byteNat :: Word8 -> K.Nat
    byteNat = go . fromIntegral
    go :: Int -> K.Nat
    go 0 = K.O
    go n = K.S (go (n - 1))

nativeSubject
  :: S.SelectedSteveGet -> C.CoreSystemsFunction -> P.RuntimeChoicePayloadPlan
  -> Either Text K.NativeSubject
nativeSubject source fn plan = do
  values <- mapM nativeValue (Map.toAscList (C.coreFunctionValues fn))
  blocks <- mapM nativeBlock (Map.toAscList (C.coreFunctionBlocks fn))
  let DeclarationKey declaration = S.selectedDeclarationKey source
      InstanceKey instanceKey = S.selectedInstanceKey source
  pure (K.NSubject (nativeName declaration) (nativeName instanceKey)
    (nativeName (S.qualifiedProviderOperation (S.selectedReadProvider source)))
    (nativeName (S.qualifiedProviderOperation (S.selectedDigestProvider source)))
    (K.NFunction (nativeName "SteveGet") (nativeName (C.coreFunctionKey fn))
      (nativeName (C.coreFunctionEntry fn)) values blocks)
    (map nativeSpec (Map.toAscList (P.runtimeChoicePayloadPlanSpecs plan))))

nativeValue :: (Text, C.CoreSystemsValue) -> Either Text K.NativeValue
nativeValue (key, value) = do
  convertedRole <- case C.coreValueRole value of
    C.CoreRuntimeScalar ty -> Right (K.NScalar (nativeName ty))
    C.CoreOwnedBuffer ty -> Right (K.NOwned (nativeName ty))
    C.CoreBorrowedValue owner -> Right (K.NBorrowed (nativeName owner))
    _ -> Left "unsupported selected native value role"
  pure (K.NValue (nativeName key) (nativeName (C.coreValueKey value))
    convertedRole (fmap nativeName (C.coreValueStorageIdentity value)))

nativeBlock :: (Text, C.CoreSystemsBlock) -> Either Text K.NativeBlock
nativeBlock (key, block) = do
  operations <- mapM nativeOp (C.coreBlockOperations block)
  terminator <- case C.coreBlockTerminator block of
    C.CoreSystemsRuntimeChoice operation operands site arms ->
      Right (K.NChoice (nativeName operation) (map nativeName operands)
        (fmap nativeName site)
        [(nativeName label, nativeName target) | (label, target) <- Map.toAscList arms])
    C.CoreSystemsEnd label -> Right (K.NEnd (nativeName label))
    _ -> Left "unsupported selected native terminator"
  pure (K.NBlock (nativeName key) (nativeName (C.coreBlockKey block))
    operations terminator)

nativeOp :: C.CoreSystemsOperation -> Either Text K.NativeOp
nativeOp operation = case operation of
  C.CoreReleaseOwner decision owner -> Right (K.NRelease (nativeName decision) (nativeName owner))
  C.CoreTrace message -> Right (K.NTrace (nativeName message))
  _ -> Left "unsupported selected native operation"

nativeSpec :: (P.RuntimeChoiceSite, P.RuntimeChoicePayloadSpec) -> K.NativeSpec
nativeSpec (key, payloadSpec) =
  let actualSite = P.runtimeChoicePayloadSite payloadSpec
  in K.NSpec (nativeName (P.runtimeChoiceSiteFunction key))
    (nativeName (P.runtimeChoiceSiteBlock key))
    (nativeName (P.runtimeChoiceSiteFunction actualSite))
    (nativeName (P.runtimeChoiceSiteBlock actualSite))
    [ K.NArm (nativeName label) (nativeName (P.runtimeChoicePayloadTarget arm))
        (fmap nativeName (P.runtimeChoicePayloadValue arm))
    | (label, arm) <- Map.toAscList (P.runtimeChoicePayloadArms payloadSpec) ]

require :: Bool -> Text -> Either Text ()
require ok problem = unless ok (Left problem)

findKey :: (Ord k, Show k) => k -> Map k a -> Either Text a
findKey key entries = maybe (Left ("missing key: " <> Text.pack (show key))) Right
  (Map.lookup key entries)

mapError :: Show e => (a -> Either e b) -> a -> Either Text b
mapError fn = either (Left . Text.pack . show) Right . fn

role :: C.CoreSystemsFunction -> Text -> C.CoreSystemsValueRole -> Either Text ()
role fn key expected = do
  value <- findKey key (C.coreFunctionValues fn)
  require (C.coreValueKey value == key && C.coreValueRole value == expected)
    ("wrong Core value role: " <> key)

-- Target origin generation is independent of source origin generation.
-- The namespace is opaque, and no hash/display/caller integer is identity.
data TargetOrigin = TargetOrigin !Unique !Integer deriving (Eq, Ord)

data CoreObservation
  = CoreReadFound !Text !TargetOrigin
  | CoreReadNotFound
  | CoreReadFailure
  | CoreBorrowOpened !TargetOrigin !TargetOrigin
  | CoreDigest !TargetOrigin !TargetOrigin !S.DigestOutcome
  | CoreBorrowClosed !TargetOrigin
  | CoreReleased !TargetOrigin
  | CoreDiagnostic !Text
  | CoreReturnedUnit !S.UnitBranch
  deriving (Eq)

data TargetValue
  = ScalarId !Text
  | Owned !TargetOrigin !Text
  | Borrowed !TargetOrigin !TargetOrigin
  deriving (Eq)

data TargetLedger = TargetLedger
  { ledgerNamespace :: !Unique
  , ledgerNext :: !Integer
  , ledgerIssued :: !(Set TargetOrigin)
  , ledgerRetired :: !(Set TargetOrigin)
  }

data TargetFrame = TargetFrame
  { framePC :: !Text
  , frameValues :: !(Map Text TargetValue)
  , frameBranch :: !(Maybe S.UnitBranch)
  , frameComplete :: !Bool
  }

type OriginMap = Map TargetOrigin S.Origin

-- Public receipts are sealed.  Public source events/snapshots are never
-- accepted as inputs.  Only the private joint driver constructs a receipt
-- after it steps its own private source run under the fixed E.
data ReceiptContext = ReceiptContext !SelectedSteveGetCore !Text ![S.SuppliedResponse]
data CoreReceipt = CoreReceipt
  !ReceiptContext ![CoreObservation] ![S.SuppliedResponse] !OriginMap

receiptMatchesContext
  :: CoreReceipt -> SelectedSteveGetCore -> Text -> [S.SuppliedResponse] -> Bool
receiptMatchesContext (CoreReceipt (ReceiptContext actual actualId actualE) _ _ _)
    selected contentId fixedE =
  actual == selected && actualId == contentId && actualE == fixedE

receiptObservations :: CoreReceipt -> [CoreObservation]
receiptObservations (CoreReceipt _ observations _ _) = observations

receiptConsumedResponses :: CoreReceipt -> [S.SuppliedResponse]
receiptConsumedResponses (CoreReceipt _ _ consumed _) = consumed

receiptOriginPair :: CoreReceipt -> Maybe (S.Origin, S.Origin)
receiptOriginPair (CoreReceipt _ observations _ origins) = case
    [(owner, loan) | CoreBorrowOpened owner loan <- observations] of
  [(owner, loan)] -> (,) <$> Map.lookup owner origins <*> Map.lookup loan origins
  _ -> Nothing

receiptMatchesOriginPair :: CoreReceipt -> S.Origin -> S.Origin -> Bool
receiptMatchesOriginPair (CoreReceipt _ observations _ origins) owner loan = case
    [(targetOwner, targetLoan) | CoreBorrowOpened targetOwner targetLoan <- observations] of
  [(targetOwner, targetLoan)] ->
    sameMappedPair origins targetOwner targetLoan owner loan
  _ -> False

sameMappedPair :: OriginMap -> TargetOrigin -> TargetOrigin -> S.Origin -> S.Origin -> Bool
sameMappedPair origins targetOwner targetLoan owner loan =
  targetOwner /= targetLoan && owner /= loan
    && Map.lookup targetOwner origins == Just owner
    && Map.lookup targetLoan origins == Just loan

data CoreRunResult
  = CoreCompleted !CoreReceipt
  | CoreWaiting !CoreReceipt
  | CoreRejected !Text

-- A world admits one invocation at a time.  A finite E ending in a wait, or
-- a rejected run, is not silently reset/cancelled: its world remains blocked.
-- Completed invocations reuse the same monotone source and target histories.
data World = World !S.SelectedWorld !TargetLedger !OriginMap !Bool
newtype SelectedCoreWorld = SelectedCoreWorld (MVar World)

newSelectedCoreWorld :: IO SelectedCoreWorld
newSelectedCoreWorld = do
  source <- S.newSelectedWorld
  namespace <- newUnique
  SelectedCoreWorld <$> newMVar
    (World source (TargetLedger namespace 0 Set.empty Set.empty) Map.empty False)

-- All target branches/payloads/operations are computed from the admitted
-- actual Core and exact plan plus E BEFORE the source is stepped.
data TargetAdvance = TargetAdvance
  !TargetLedger !TargetFrame ![CoreObservation]

mint :: TargetLedger -> (TargetOrigin, TargetLedger)
mint ledger =
  let origin = TargetOrigin (ledgerNamespace ledger) (ledgerNext ledger)
  in (origin, ledger { ledgerNext = ledgerNext ledger + 1
                     , ledgerIssued = Set.insert origin (ledgerIssued ledger) })

live :: TargetLedger -> TargetOrigin -> Bool
live ledger origin = Set.member origin (ledgerIssued ledger)
  && not (Set.member origin (ledgerRetired ledger))

retire :: TargetLedger -> TargetOrigin -> Either Text TargetLedger
retire ledger origin = do
  require (live ledger origin) "non-live or already retired target origin"
  pure ledger { ledgerRetired = Set.insert origin (ledgerRetired ledger) }

-- Read the actual choice terminator and the separately recertified plan.
-- The arm target and result identifier are not guessed from an outcome label.
choiceArm
  :: C.CoreSystemsFunction -> P.RuntimeChoicePayloadPlan -> TargetFrame
  -> Map Text Text -> Text -> Either Text P.RuntimeChoicePayloadArm
choiceArm fn plan frame arms label = do
  target <- findKey label arms
  let site = P.RuntimeChoiceSite (C.coreFunctionKey fn) (framePC frame)
  spec <- findKey site (P.runtimeChoicePayloadPlanSpecs plan)
  require (P.runtimeChoicePayloadSite spec == site) "plan site mismatch"
  planned <- findKey label (P.runtimeChoicePayloadArms spec)
  require (P.runtimeChoicePayloadTarget planned == target) "plan target mismatch"
  pure planned

targetAdvance
  :: SelectedSteveGetCore -> TargetLedger -> TargetFrame
  -> Maybe S.SuppliedResponse -> Either Text TargetAdvance
targetAdvance (SelectedSteveGetCore source fn plan) ledger frame supplied = do
  block <- findKey (framePC frame) (C.coreFunctionBlocks fn)
  require (C.coreBlockKey block == framePC frame && not (frameComplete frame))
    "invalid target program counter"
  case C.coreBlockTerminator block of
    C.CoreSystemsRuntimeChoice operation operands site arms -> do
      require (null (C.coreBlockOperations block) && site == Nothing)
        "unexpected operation or realization site before choice"
      case (operation, operands, supplied) of
        ("BlobProvider.read", [idKey],
          Just (S.ReadResponse at provider contentId outcome)) -> do
          require (framePC frame == "get.entry" && idKey == "get.id"
            && at == S.selectedReadOccurrence source
            && provider == S.selectedReadProvider source)
            "wrong selected read occurrence, qualification, or operands"
          role fn idKey (C.CoreRuntimeScalar "ContentId[SHA256]")
          require (Map.lookup idKey (frameValues frame) == Just (ScalarId contentId))
            "wrong original ContentId"
          case outcome of
            S.ReadFound payload -> do
              arm <- choiceArm fn plan frame arms "found"
              destination <- maybe (Left "missing found destination") Right
                (P.runtimeChoicePayloadValue arm)
              require (destination == "get.bytes"
                && Map.notMember destination (frameValues frame))
                "found result is not assigned to the exact new owned buffer"
              role fn destination (C.CoreOwnedBuffer "OwnedBytes")
              role fn "get.bytes-view" (C.CoreBorrowedValue destination)
              let (owner, afterOwner) = mint ledger
                  (loan, afterLoan) = mint afterOwner
                  values = Map.insert "get.bytes-view" (Borrowed owner loan)
                    (Map.insert destination (Owned owner payload) (frameValues frame))
              pure (TargetAdvance afterLoan
                (frame { framePC = P.runtimeChoicePayloadTarget arm
                       , frameValues = values })
                [CoreReadFound payload owner, CoreBorrowOpened owner loan])
            S.ReadNotFound -> nonfound fn plan frame arms ledger
              "not-found" S.UnitNotFound CoreReadNotFound
            S.ReadStorageFailure _ -> nonfound fn plan frame arms ledger
              "storage-failure" S.UnitStorageFailure CoreReadFailure
        ("DigestProvider.check", [idKey, viewKey],
          Just (S.DigestResponse at provider contentId sourceView decision)) -> do
          require (framePC frame == "get.check" && idKey == "get.id"
            && viewKey == "get.bytes-view"
            && at == S.selectedDigestOccurrence source
            && provider == S.selectedDigestProvider source
            && sourceView == "bytesView")
            "wrong selected digest occurrence, qualification, view or operands"
          require (Map.lookup idKey (frameValues frame) == Just (ScalarId contentId))
            "wrong original digest ContentId"
          role fn viewKey (C.CoreBorrowedValue "get.bytes")
          (owner, loan) <- case Map.lookup viewKey (frameValues frame) of
            Just (Borrowed o l) -> Right (o, l)
            _ -> Left "missing borrowed digest operand"
          case Map.lookup "get.bytes" (frameValues frame) of
            Just (Owned actualOwner _) -> require (actualOwner == owner)
              "digest view not borrowed from assigned read result"
            _ -> Left "missing owned read result"
          require (owner /= loan && live ledger owner && live ledger loan)
            "digest requires distinct live read owner and loan"
          let (label, branch) = case decision of
                S.DigestAccepted -> ("accepted", S.UnitFoundAccepted)
                S.DigestRejected _ -> ("rejected", S.UnitFoundRejected)
          arm <- choiceArm fn plan frame arms label
          require (P.runtimeChoicePayloadValue arm == Nothing)
            "unexpected digest payload"
          closed <- retire ledger loan
          pure (TargetAdvance closed
            (frame { framePC = P.runtimeChoicePayloadTarget arm
                   , frameValues = Map.delete viewKey (frameValues frame)
                   , frameBranch = Just branch })
            [CoreDigest owner loan decision, CoreBorrowClosed loan])
        _ -> Left "wrong event kind or actual selected Core choice"
    C.CoreSystemsEnd label -> do
      require (supplied == Nothing) "unexpected response at Core end"
      branch <- maybe (Left "missing selected branch") Right (frameBranch frame)
      require (label == branchLabel branch) "wrong Core terminal branch"
      (finishedLedger, values, events) <- foldM terminalOp
        (ledger, frameValues frame, []) (C.coreBlockOperations block)
      require (Map.keys values == ["get.id"]
        && ledgerIssued finishedLedger == ledgerRetired finishedLedger)
        "Core end with live owned result or loan"
      pure (TargetAdvance finishedLedger
        (frame { frameValues = values, frameComplete = True })
        (events ++ [CoreReturnedUnit branch]))
    _ -> Left "unexpected selected Core terminator"

nonfound
  :: C.CoreSystemsFunction -> P.RuntimeChoicePayloadPlan -> TargetFrame
  -> Map Text Text -> TargetLedger -> Text -> S.UnitBranch -> CoreObservation
  -> Either Text TargetAdvance
nonfound fn plan frame arms ledger label branch event = do
  arm <- choiceArm fn plan frame arms label
  require (P.runtimeChoicePayloadValue arm == Nothing
    && Map.keys (frameValues frame) == ["get.id"])
    "nonfound read allocated a payload"
  pure (TargetAdvance ledger
    (frame { framePC = P.runtimeChoicePayloadTarget arm
           , frameBranch = Just branch }) [event])

terminalOp
  :: (TargetLedger, Map Text TargetValue, [CoreObservation])
  -> C.CoreSystemsOperation
  -> Either Text (TargetLedger, Map Text TargetValue, [CoreObservation])
terminalOp (ledger, values, observations) operation = case operation of
  C.CoreReleaseOwner "cleanup" "get.bytes" -> do
    require (Map.notMember "get.bytes-view" values) "release under live loan"
    owner <- case Map.lookup "get.bytes" values of
      Just (Owned o _) -> Right o
      _ -> Left "release without exact owned result"
    released <- retire ledger owner
    pure (released, Map.delete "get.bytes" values, observations ++ [CoreReleased owner])
  C.CoreTrace message -> pure (ledger, values, observations ++ [CoreDiagnostic message])
  _ -> Left "unexpected effect in selected Core terminal block"

branchLabel :: S.UnitBranch -> Text
branchLabel branch = case branch of
  S.UnitFoundAccepted -> "success"
  S.UnitFoundRejected -> "integrity-failure"
  S.UnitNotFound -> "not-found"
  S.UnitStorageFailure -> "storage-failure"

-- Compare private actual source-run deltas with independently computed
-- target observations.  The only point that extends originMap is the actual
-- corresponding found/borrow event pair of this invocation.
matchSource
  :: S.SelectedSteveGet -> OriginMap -> [CoreObservation] -> [S.SourceEvent]
  -> Either Text OriginMap
matchSource source origins targetEvents sourceEvents = case
    (filter relevant targetEvents, sourceEvents) of
  ([CoreReadFound payload tOwner, CoreBorrowOpened tOwner' tLoan],
    [S.ObservedReadFound at actualPayload owner, S.OpenedLoan owner' loan]) -> do
      require (at == S.selectedReadOccurrence source && payload == actualPayload
        && tOwner == tOwner' && tOwner /= tLoan
        && owner == owner' && owner /= loan
        && Map.notMember tOwner origins && Map.notMember tLoan origins
        && owner `notElem` Map.elems origins && loan `notElem` Map.elems origins)
        "read/borrow occurrence, payload, or fresh origin injection mismatch"
      pure (Map.insert tLoan loan (Map.insert tOwner owner origins))
  ([CoreReadNotFound], [S.ObservedReadNotFound at, S.ReturnedUnit S.UnitNotFound]) ->
    require (at == S.selectedReadOccurrence source) "wrong not-found event site"
      >> pure origins
  ([CoreReadFailure], [S.ObservedReadFailure at, S.ReturnedUnit S.UnitStorageFailure]) ->
    require (at == S.selectedReadOccurrence source) "wrong storage-failure event site"
      >> pure origins
  ([CoreDigest tOwner tLoan decision, CoreBorrowClosed tLoan'],
    [S.ObservedDigest at owner loan actualDecision, S.ClosedLoan closed]) -> do
      require (at == S.selectedDigestOccurrence source && decision == actualDecision
        && tLoan == tLoan' && loan == closed
        && sameMappedPair origins tOwner tLoan owner loan)
        "digest result or live original owner/loan mismatch"
      pure origins
  ([CoreReleased tOwner, CoreReturnedUnit branch],
    [S.ReleasedOwner owner, S.ReturnedUnit actualBranch]) ->
      require (Map.lookup tOwner origins == Just owner && branch == actualBranch)
        "release or Unit branch mismatch" >> pure origins
  ([CoreReturnedUnit S.UnitNotFound], []) -> pure origins
  ([CoreReturnedUnit S.UnitStorageFailure], []) -> pure origins
  _ -> Left "unexpected source/target observation delta"
  where
    relevant (CoreDiagnostic _) = False
    relevant _ = True

-- A source snapshot is used ONLY internally, immediately around our own
-- private source-run steps.  No caller can provide a snapshot or event list.
sourceDelta
  :: S.SelectedWorld -> S.SelectedRun -> [Maybe S.SuppliedResponse]
  -> IO (Either Text [S.SourceEvent])
sourceDelta world run inputs = do
  before <- S.snapshotSelectedWorld world
  results <- mapM (S.stepSelectedSteveGet run) inputs
  after <- S.snapshotSelectedWorld world
  let prefix = S.snapshotEvents before
      events = S.snapshotEvents after
      ok (S.SourceAdvanced _) = True
      ok (S.SourceReturnedUnit _) = True
      ok _ = False
  pure $ do
    require (all ok results && take (length prefix) events == prefix)
      "actual private source step failed or history changed"
    pure (drop (length prefix) events)

sourceInputs :: Maybe S.SuppliedResponse -> [CoreObservation] -> [Maybe S.SuppliedResponse]
sourceInputs supplied events = case events of
  CoreReadFound _ _ : _ -> [supplied, Nothing]
  CoreReadNotFound : _ -> [supplied]
  CoreReadFailure : _ -> [supplied]
  CoreDigest _ _ _ : _ -> [supplied, Nothing]
  CoreReleased _ : _ -> [Nothing]
  _ -> []

-- Compare the complete private source and target H histories after every
-- segment.  Map equality is on the actual opaque Origin, not its Show/hash.
-- Repeated equal payloads and separate namespaces cannot collapse.
ledgerMatches :: TargetLedger -> OriginMap -> S.WorldSnapshot -> Bool
ledgerMatches ledger origins snapshot =
  ledgerNext ledger == S.snapshotNextOrigin snapshot
    && Map.keysSet origins == ledgerIssued ledger
    && Map.size origins == Set.size (Set.fromList (Map.elems origins))
    && Set.fromList (Map.elems origins) == S.snapshotIssued snapshot
    && Set.fromList [sourceOrigin | targetOrigin <- Set.toList (ledgerRetired ledger),
         Just sourceOrigin <- [Map.lookup targetOrigin origins]] == S.snapshotRetired snapshot

expectedSourceActive :: TargetFrame -> Bool
expectedSourceActive frame = not (frameComplete frame)
  && frameBranch frame /= Just S.UnitNotFound
  && frameBranch frame /= Just S.UnitStorageFailure

-- The E list is captured once, not supplied by the caller at each step.
-- At most three actual Core blocks execute.  A missing E response is a
-- finite waiting prefix; polling twice must leave the private source H and
-- completed history unchanged.  There is no cancel/rewind operation.
runSelectedSteveGetCore
  :: SelectedCoreWorld -> SelectedSteveGetCore -> Text
  -> [S.SuppliedResponse] -> IO CoreRunResult
runSelectedSteveGetCore (SelectedCoreWorld lock) selected@(SelectedSteveGetCore source fn _)
    contentId fixedE = mask $ \_ -> do
  original@(World sourceWorld ledger origins blocked) <- takeMVar lock
  if blocked
    then putMVar lock original >> pure (CoreRejected "world has an unfinished or rejected invocation")
    else do
      let poison = putMVar lock (World sourceWorld ledger origins True)
      (do
        initial <- S.snapshotSelectedWorld sourceWorld
        started <- if ledgerMatches ledger origins initial
            && not (S.snapshotHasActiveInvocation initial)
            && ledgerIssued ledger == ledgerRetired ledger
          then S.beginSelectedSteveGet sourceWorld source contentId
          else pure (Left "initial persistent origin history mismatch")
        case started of
          Left problem -> poison >> pure (CoreRejected problem)
          Right sourceRun -> do
            let frame = TargetFrame (C.coreFunctionEntry fn)
                  (Map.singleton "get.id" (ScalarId contentId)) Nothing False
            (result, newLedger, newOrigins) <-
              drive sourceWorld sourceRun selected (ReceiptContext selected contentId fixedE)
                3 ledger origins frame [] [] fixedE
            let complete = case result of
                  CoreCompleted _ -> True
                  _ -> False
            putMVar lock (World sourceWorld newLedger newOrigins (not complete))
            pure result) `onException` poison

drive
  :: S.SelectedWorld -> S.SelectedRun -> SelectedSteveGetCore -> ReceiptContext -> Int
  -> TargetLedger -> OriginMap -> TargetFrame -> [CoreObservation]
  -> [S.SuppliedResponse] -> [S.SuppliedResponse]
  -> IO (CoreRunResult, TargetLedger, OriginMap)
drive world run selected@(SelectedSteveGetCore source fn _) context fuel ledger origins frame
    history consumed remaining
  | frameComplete frame =
      if null remaining
        then pure (CoreCompleted (CoreReceipt context history consumed origins), ledger, origins)
        else failed "extra response after selected invocation"
  | fuel <= 0 = failed "target exceeded closed-fragment block bound"
  | otherwise = case Map.lookup (framePC frame) (C.coreFunctionBlocks fn) of
      Nothing -> failed "missing actual target block"
      Just block -> case C.coreBlockTerminator block of
        C.CoreSystemsRuntimeChoice operation _ _ _ -> case remaining of
          [] -> do
            before <- S.snapshotSelectedWorld world
            first <- S.stepSelectedSteveGet run Nothing
            second <- S.stepSelectedSteveGet run Nothing
            after <- S.snapshotSelectedWorld world
            let expected = if operation == "BlobProvider.read"
                  then S.NeedsReadResponse else S.NeedsDigestResponse
            if first == expected && second == expected && before == after
                && ledgerMatches ledger origins after
              then pure (CoreWaiting (CoreReceipt context history consumed origins), ledger, origins)
              else failed "waiting changed source request or history"
          response : rest -> advance (Just response) (consumed ++ [response]) rest
        _ -> advance Nothing consumed remaining
  where
    failed problem = pure (CoreRejected problem, ledger, origins)
    advance supplied used rest =
      case targetAdvance selected ledger frame supplied of
        Left problem -> failed problem
        Right (TargetAdvance nextLedger nextFrame events) -> do
          observed <- sourceDelta world run (sourceInputs supplied events)
          case observed >>= matchSource source origins events of
            Left problem -> pure (CoreRejected problem, nextLedger, origins)
            Right nextOrigins -> do
              snapshot <- S.snapshotSelectedWorld world
              if ledgerMatches nextLedger nextOrigins snapshot
                  && S.snapshotHasActiveInvocation snapshot == expectedSourceActive nextFrame
                then drive world run selected context (fuel - 1)
                  nextLedger nextOrigins nextFrame (history ++ events) used rest
                else pure (CoreRejected "persistent source/target H or phase mismatch",
                  nextLedger, nextOrigins)
