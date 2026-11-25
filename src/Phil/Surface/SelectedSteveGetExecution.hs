{-# LANGUAGE OverloadedStrings #-}

-- | FSEM-05: a bounded *selected* evaluator for the original ordinary Surface
-- SteveGet declaration. This is proposed source-level operational semantics,
-- NOT an interpretation of native StablePtr values or a linked-provider proof.
--
-- The source is reparsed/rechecked from raw bytes. The externally supplied E
-- chooses only a typed outcome and payload. No E value carries an owner, loan,
-- origin serial, or mutable history: those are minted by this private world.
module Phil.Surface.SelectedSteveGetExecution
  ( SelectedSteveGet
  , SelectedSourceError (..)
  , prepareSelectedSteveGet
  , selectedReadOccurrence
  , selectedDigestOccurrence
  , selectedDeclarationKey
  , selectedInstanceKey
  , QualifiedProviderRef (..)
  , selectedReadProvider
  , selectedDigestProvider
  , SelectedWorld
  , SelectedRun
  , Origin
  , WorldSnapshot (..)
  , newSelectedWorld
  , snapshotSelectedWorld
  , beginSelectedSteveGet
  , ReadOutcome (..)
  , DigestOutcome (..)
  , SuppliedResponse (..)
  , UnitBranch (..)
  , SourceEvent (..)
  , StepResult (..)
  , stepSelectedSteveGet
  , DriveResult (..)
  , runSelectedFuel
  ) where

import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Unique (Unique, hashUnique, newUnique)
import Phil.Compiler.SourceArchitecture
  ( buildCheckedSourceArchitecture
  , checkedSourceArchitectureInstanceKey )
import Phil.Compiler.SourceBundle
  ( CheckedSourceUnit (..), CheckedSourceBundle (..)
  , checkPortableSourceBundle )
import Phil.Core.Static
  ( DeclarationKey (..), InstanceKey (..)
  , InterfaceRevision, DefinitionRevision, emptyStaticContext )
import Phil.Core.ProviderQualification
  ( ProviderContract (..), ProviderImplementation (..) )
import Phil.Core.Syntax (Mode (..), Ty (..))
import Phil.Examples.Steve.ApplicationShell (steveGetShellEnvironment)
import Phil.Examples.Steve.ProviderQualifications
  ( SteveProviderQualifications (..), SteveProviderQualificationArtifact (..)
  , materializeSteveProviderQualifications )
import Phil.Surface.Check
  ( InitialBinding (..), SurfaceShape (..), SurfaceEnvironment (..)
  , PrimitiveArgumentDiscipline (..), PrimitiveSemantics (..)
  , ProviderOutcomeSpec (..), emptySurfaceEnvironment )
import Phil.Surface.Lineage
  ( SourceUnitId (..), DeclarationSiteId (..), InstanceLineageSiteId (..)
  , PortableSourceBundle (..), PortableSourceUnit (..)
  , PortableInstanceLineage (..), canonicalGrammarRevisionV1 )
import Phil.Surface.Syntax

data SelectedSourceError
  = SelectedSourceRejected Text
  | SelectedSourceShapeMismatch
  | SelectedSourceQualificationMismatch
  deriving (Eq, Show)

-- | The qualified provider response ref remains constructible so tests can
-- submit malformed provider identities. It is not an admitted source object.
data QualifiedProviderRef = QualifiedProviderRef
  { qualifiedProviderOperation :: Text
  , qualifiedProviderInterface :: InterfaceRevision
  , qualifiedProviderImplementation :: DefinitionRevision
  }
  deriving (Eq, Show)

-- | Admission-only positional constructor: exporting six getter functions
-- cannot grant record-update syntax to a client holding SelectedSteveGet.
-- No source identity or qualification field is writable outside this module.
data SelectedSteveGet = SelectedSteveGet
  !SourceSpan !SourceSpan !DeclarationKey !InstanceKey
  !QualifiedProviderRef !QualifiedProviderRef
  deriving (Eq, Show)

selectedReadOccurrence :: SelectedSteveGet -> SourceSpan
selectedReadOccurrence (SelectedSteveGet site _ _ _ _ _) = site

selectedDigestOccurrence :: SelectedSteveGet -> SourceSpan
selectedDigestOccurrence (SelectedSteveGet _ site _ _ _ _) = site

selectedDeclarationKey :: SelectedSteveGet -> DeclarationKey
selectedDeclarationKey (SelectedSteveGet _ _ key _ _ _) = key

selectedInstanceKey :: SelectedSteveGet -> InstanceKey
selectedInstanceKey (SelectedSteveGet _ _ _ key _ _) = key

selectedReadProvider :: SelectedSteveGet -> QualifiedProviderRef
selectedReadProvider (SelectedSteveGet _ _ _ _ provider _) = provider

selectedDigestProvider :: SelectedSteveGet -> QualifiedProviderRef
selectedDigestProvider (SelectedSteveGet _ _ _ _ _ provider) = provider

-- | Canonical *original free* contentId binder. The separately defined shell
-- callable's formal parameter does not represent get.phil's zero-arity source.
prepareSelectedSteveGet :: Text -> Either SelectedSourceError SelectedSteveGet
prepareSelectedSteveGet originalRaw = do
  qualifications <- mapLeft (SelectedSourceRejected . Text.pack . show)
    materializeSteveProviderQualifications
  if steveProviderLabel (steveBlobProviderQualification qualifications)
       == "BlobProvider"
       && steveProviderLabel (steveDigestProviderQualification qualifications)
       == "DigestProvider[SHA256]"
    then Right ()
    else Left SelectedSourceQualificationMismatch
  shell <- mapLeft SelectedSourceRejected steveGetShellEnvironment
  let blob = steveBlobProviderQualification qualifications
      digest = steveDigestProviderQualification qualifications
      qualifiedRef operation artifact = QualifiedProviderRef
        { qualifiedProviderOperation = operation
        , qualifiedProviderInterface =
            providerContractInterfaceRevision (steveProviderContract artifact)
        , qualifiedProviderImplementation =
            providerImplementationDefinitionRevision
              (steveProviderImplementation artifact)
        }
      readProvider = qualifiedRef "BlobProvider.read" blob
      digestProvider = qualifiedRef "DigestProvider.check" digest
      expectedRead = PrimitiveProviderDecision [PrimitiveReadOnly]
        [ ProviderOutcomeSpec "found" [(Linear, TyOpaque "OwnedBytes")]
        , ProviderOutcomeSpec "not-found" []
        , ProviderOutcomeSpec "storage-failure"
            [(Unrestricted, TyOpaque "StorageFailure")]
        ]
      expectedDigest = PrimitiveProviderDecision
        [PrimitiveReadOnly, PrimitiveReadOnly]
        [ ProviderOutcomeSpec "accepted" []
        , ProviderOutcomeSpec "rejected"
            [(Unrestricted, TyOpaque "DigestFailure")]
        ]
      primitives = Map.restrictKeys (surfacePrimitives shell)
        (Set.fromList ["blob_read", "digest_check"])
      canonical = (emptySurfaceEnvironment emptyStaticContext)
        { surfaceInitialBindings = Map.singleton "contentId"
            (InitialBinding Unrestricted
              (TyOpaque "ContentId[SHA256]") PlainShape)
        , surfacePrimitives = primitives
        , surfaceExpectedProvides = Just TyUnit
        , surfaceReleaseTransitions = surfaceReleaseTransitions shell
        }
      key = DeclarationKey "decl:steve.get"
      root = "program:steve.get"
      instanceSite = InstanceLineageSiteId "instance.steve"
      bundle = PortableSourceBundle
        { portableGrammarRevision = canonicalGrammarRevisionV1
        , portableSelectedProgramRoot = root
        , portableSourceUnits =
            [PortableSourceUnit
              (SourceUnitId "unit.steve.get")
              (DeclarationSiteId "site.steve.get")
              (Just "decl:steve.get")
              originalRaw]
        , portableInstanceLineage =
            [PortableInstanceLineage instanceSite "inst:phase1.steve"]
        , portableProcessLineage = []
        }
  if Map.lookup "blob_read" primitives == Just expectedRead
       && Map.lookup "digest_check" primitives == Just expectedDigest
       && Map.size primitives == 2
    then Right ()
    else Left SelectedSourceQualificationMismatch
  checked <- mapLeft (SelectedSourceRejected . Text.pack . show) $
    checkPortableSourceBundle (Map.singleton root key)
      (Map.singleton key canonical) bundle
  architecture <- mapLeft (SelectedSourceRejected . Text.pack . show) $
    buildCheckedSourceArchitecture
      (Map.singleton root instanceSite) checked
  if checkedSourceSelectedRootKey checked == key
      && checkedSourceArchitectureInstanceKey architecture
           == InstanceKey "inst:phase1.steve"
    then Right ()
    else Left SelectedSourceQualificationMismatch
  unit <- case checkedSourceUnits checked of
    [a] | checkedSourceDeclarationKey a == key -> Right a
    _ -> Left SelectedSourceShapeMismatch
  case sourceOccurrences (checkedSourceComponent unit) of
    Just (readAt, digestAt) ->
      Right (SelectedSteveGet readAt digestAt key
        (checkedSourceArchitectureInstanceKey architecture)
        readProvider digestProvider)
    Nothing -> Left SelectedSourceShapeMismatch

-- | Complete selected whole-AST discriminator, not a substring match or a
-- static event projected as a runtime read. Every statement/arm is inspected.
sourceOccurrences :: Located Component -> Maybe (SourceSpan, SourceSpan)
sourceOccurrences locatedComponent = do
  let component = locatedValue locatedComponent
  require (componentName component == "SteveGet"
    && null (componentParameters component))
  provides <- componentProvides component
  require (locatedValue provides == SurfaceUnitType)
  [outer] <- pure (blockStatements (locatedValue (componentBody component)))
  outerExpression <- expressionStatement outer
  (readCall, readArms) <- decide outerExpression
  (readName, [idArgument]) <- call readCall
  require (readName == "blob_read" && var "contentId" idArgument)
  [found, missing, failure] <- pure readArms
  require (arm "found" ["bytes"] found
    && arm "not-found" [] missing
    && arm "storage-failure" ["reason"] failure)
  require (returnsUnit (caseArmBody (locatedValue missing))
    && returnsUnit (caseArmBody (locatedValue failure)))
  [bind, digestDecide] <- pure
    (blockStatements (locatedValue (caseArmBody (locatedValue found))))
  (patternValue, borrowExpr) <- letStatement bind
  require (locatedValue patternValue == BindPattern "digestDecision")
  (owner, viewName, borrowBody) <- case locatedValue borrowExpr of
    BorrowExpression o v b -> Just (o,v,b)
    _ -> Nothing
  require (var "bytes" owner && viewName == "bytesView")
  [digestStatement] <- pure (blockStatements (locatedValue borrowBody))
  digestCall <- expressionStatement digestStatement
  (digestName, [digestId, digestView]) <- call digestCall
  require (digestName == "digest_check" && var "contentId" digestId
    && var "bytesView" digestView)
  decisionExpression <- expressionStatement digestDecide
  (decision, digestArms) <- decide decisionExpression
  require (var "digestDecision" decision)
  [accepted, rejected] <- pure digestArms
  require (arm "accepted" [] accepted && arm "rejected" ["reason"] rejected)
  require (releasesUnit (caseArmBody (locatedValue accepted))
    && releasesUnit (caseArmBody (locatedValue rejected)))
  pure (locatedSpan readCall, locatedSpan digestCall)
  where
    require True = Just ()
    require False = Nothing
    expressionStatement s = case locatedValue s of
      ExpressionStatement e -> Just e
      _ -> Nothing
    letStatement s = case locatedValue s of
      LetStatement p e -> Just (p,e)
      _ -> Nothing
    decide e = case locatedValue e of
      DecideExpression s as -> Just (s,as)
      _ -> Nothing
    call e = case locatedValue e of
      CallExpression n as -> Just (n,as)
      _ -> Nothing
    var n e = locatedValue e == VariableExpression n
    arm n binds a = let p = caseArmPattern (locatedValue a)
      in casePatternLabel p == n && casePatternBinders p == binds
    returnsUnit b = case blockStatements (locatedValue b) of
      [s] -> case locatedValue s of
        ReturnStatement e -> locatedValue e == UnitExpression
        _ -> False
      _ -> False
    releasesUnit b = case blockStatements (locatedValue b) of
      [first, second] -> case (locatedValue first, locatedValue second) of
        (ExpressionStatement release, ReturnStatement result) ->
          case locatedValue release of
            ReleaseExpression owner ->
              var "bytes" owner && locatedValue result == UnitExpression
            _ -> False
        _ -> False
      _ -> False

-- | The namespace is private to a world; the counter is never supplied by E.
-- Unique is *not* a persisted cross-process or native StablePtr identity.
data Origin = Origin !Unique !Integer deriving (Eq, Ord)
instance Show Origin where
  show (Origin u n) = "Origin(" ++ show (hashUnique u) ++ "," ++ show n ++ ")"

data ReadOutcome = ReadFound Text | ReadNotFound | ReadStorageFailure Text
  deriving (Eq, Show)
data DigestOutcome = DigestAccepted | DigestRejected Text
  deriving (Eq, Show)

-- | E contributes typed outcome/payload and exact source/qualified call
-- location. It cannot choose owner, loan or serial. Its authenticity as a
-- *native* provider response is deliberately an undischarged boundary.
data SuppliedResponse
  = ReadResponse SourceSpan QualifiedProviderRef Text ReadOutcome
  | DigestResponse SourceSpan QualifiedProviderRef Text Text DigestOutcome
  deriving (Eq, Show)

data UnitBranch
  = UnitFoundAccepted | UnitFoundRejected | UnitNotFound | UnitStorageFailure
  deriving (Eq, Show)

data SourceEvent
  = ObservedReadFound SourceSpan Text Origin
  | ObservedReadNotFound SourceSpan
  | ObservedReadFailure SourceSpan
  | OpenedLoan Origin Origin
  | ObservedDigest SourceSpan Origin Origin DigestOutcome
  | ClosedLoan Origin
  | ReleasedOwner Origin
  | ReturnedUnit UnitBranch
  deriving (Eq, Show)

data StepResult
  = NeedsReadResponse
  | NeedsDigestResponse
  | SourceAdvanced SourceEvent
  | SourceReturnedUnit UnitBranch
  | SourceRejected Text
  deriving (Eq, Show)

-- | Finite driver partiality is separate from the actual selected step:
-- an exhausted scheduler prefix, a missing provider reply, a rejection and
-- fuel depletion are four different outcomes.
data DriveResult
  = DriveCompleted UnitBranch
  | DriveWaitingForResponse
  | DriveRejected Text
  | DriveFuelExhausted
  | DriveInputPrefixEnded
  deriving (Eq, Show)

runSelectedFuel :: Int -> SelectedRun -> [Maybe SuppliedResponse] -> IO DriveResult
runSelectedFuel fuel selected inputs
  | fuel <= 0 = pure DriveFuelExhausted
  | otherwise = case inputs of
      [] -> pure DriveInputPrefixEnded
      supplied : rest -> do
        result <- stepSelectedSteveGet selected supplied
        case result of
          SourceReturnedUnit branch -> pure (DriveCompleted branch)
          NeedsReadResponse -> pure DriveWaitingForResponse
          NeedsDigestResponse -> pure DriveWaitingForResponse
          SourceRejected problem -> pure (DriveRejected problem)
          SourceAdvanced _ -> runSelectedFuel (fuel - 1) selected rest

data Phase = NeedRead | NeedBorrow | NeedDigest | NeedClose | NeedRelease
  deriving (Eq, Show)

data Active = Active
  { activeToken :: !Unique
  , activeSelected :: !SelectedSteveGet
  , activeContentId :: !Text
  , activePhase :: !Phase
  , activeOwner :: !(Maybe Origin)
  , activeLoan :: !(Maybe Origin)
  , activeBranch :: !(Maybe UnitBranch)
  }

data WorldState = WorldState
  { worldNamespace :: !Unique
  , worldNextOrigin :: !Integer
  , worldIssued :: !(Set Origin)
  , worldRetired :: !(Set Origin)
  , worldActive :: !(Maybe Active)
  , worldEvents :: ![SourceEvent]
  }

newtype SelectedWorld = SelectedWorld (IORef WorldState)
data SelectedRun = SelectedRun !SelectedWorld !Unique

data WorldSnapshot = WorldSnapshot
  { snapshotIssued :: Set Origin
  , snapshotRetired :: Set Origin
  , snapshotEvents :: [SourceEvent]
  , snapshotNextOrigin :: Integer
  , snapshotHasActiveInvocation :: Bool
  }
  deriving (Eq, Show)

newSelectedWorld :: IO SelectedWorld
newSelectedWorld = do
  namespace <- newUnique
  SelectedWorld <$> newIORef WorldState
    { worldNamespace = namespace, worldNextOrigin = 0
    , worldIssued = Set.empty, worldRetired = Set.empty
    , worldActive = Nothing, worldEvents = []
    }

snapshotSelectedWorld :: SelectedWorld -> IO WorldSnapshot
snapshotSelectedWorld (SelectedWorld ref) = do
  w <- readIORef ref
  pure WorldSnapshot
    { snapshotIssued = worldIssued w
    , snapshotRetired = worldRetired w
    , snapshotEvents = reverse (worldEvents w)
    , snapshotNextOrigin = worldNextOrigin w
    , snapshotHasActiveInvocation = case worldActive w of
        Nothing -> False
        Just _ -> True
    }

beginSelectedSteveGet
  :: SelectedWorld -> SelectedSteveGet -> Text -> IO (Either Text SelectedRun)
beginSelectedSteveGet world@(SelectedWorld ref) selected idValue = do
  token <- newUnique
  atomicModifyIORef' ref $ \w ->
    case worldActive w of
      Just _ -> (w, Left "non-reentrant selected fragment already active")
      Nothing ->
        let active = Active token selected idValue NeedRead Nothing Nothing Nothing
        in (w { worldActive = Just active }, Right (SelectedRun world token))

-- | One actual selected step, independent of the static checker. The only
-- external input is the next *qualified* E outcome. A wrong/missing E event
-- never manufactures a successor. Non-provider internal steps take Nothing.
stepSelectedSteveGet :: SelectedRun -> Maybe SuppliedResponse -> IO StepResult
stepSelectedSteveGet (SelectedRun (SelectedWorld ref) token) response =
  atomicModifyIORef' ref $ \w ->
    case worldActive w of
      Nothing -> (w, SourceRejected "no live selected invocation")
      Just active
        | activeToken active /= token ->
            (w, SourceRejected "stale or foreign invocation")
        | otherwise -> transition w active response

transition :: WorldState -> Active -> Maybe SuppliedResponse -> (WorldState, StepResult)
transition w a supplied = case (activePhase a, supplied) of
  -- NeedRead/NeedDigest each represent a single pending selected request
  -- with immutable occurrence/provider/id (and loan/view for digest). A
  -- Nothing response preserves the same Active and never reissues a call;
  -- SourceEvent is a completed-event projection, not a request log.
  (NeedRead, Nothing) -> (w, NeedsReadResponse)
  (NeedRead, Just (ReadResponse site provider actualId outcome))
    | site == selectedReadOccurrence (activeSelected a)
      && provider == selectedReadProvider (activeSelected a)
      && actualId == activeContentId a ->
      case outcome of
        ReadFound payload ->
          let (origin, minted) = mint w
              next = a { activePhase = NeedBorrow, activeOwner = Just origin }
              event = ObservedReadFound site payload origin
          in (record event (minted { worldActive = Just next }), SourceAdvanced event)
        ReadNotFound -> finish w UnitNotFound
          (ObservedReadNotFound site)
        ReadStorageFailure _ -> finish w UnitStorageFailure
          (ObservedReadFailure site)
  (NeedBorrow, Nothing) ->
    case activeOwner a of
      Just owner | Set.member owner (worldIssued w)
          && not (Set.member owner (worldRetired w)) ->
        let (loan, minted) = mint w
            next = a { activePhase = NeedDigest, activeLoan = Just loan }
            event = OpenedLoan owner loan
        in (record event (minted { worldActive = Just next }), SourceAdvanced event)
      _ -> reject w "borrow requires live exact found owner"
  (NeedDigest, Nothing) -> (w, NeedsDigestResponse)
  (NeedDigest, Just (DigestResponse site provider actualId view decision))
    | site == selectedDigestOccurrence (activeSelected a)
      && provider == selectedDigestProvider (activeSelected a)
      && actualId == activeContentId a && view == "bytesView" ->
      case (activeOwner a, activeLoan a) of
        (Just owner, Just loan)
          | Set.member owner (worldIssued w)
          , Set.member loan (worldIssued w)
          , not (Set.member owner (worldRetired w))
          , not (Set.member loan (worldRetired w)) ->
            let next = a
                  { activePhase = NeedClose
                  , activeBranch = Just (case decision of
                      DigestAccepted -> UnitFoundAccepted
                      DigestRejected _ -> UnitFoundRejected)
                  }
                event = ObservedDigest site owner loan decision
            in (record event (w { worldActive = Just next }), SourceAdvanced event)
        _ -> reject w "digest requires live owner-linked loan"
  (NeedClose, Nothing) ->
    case activeLoan a of
      Just loan | Set.member loan (worldIssued w)
        && not (Set.member loan (worldRetired w)) ->
          let next = a { activePhase = NeedRelease, activeLoan = Nothing }
              event = ClosedLoan loan
          in (record event
                (w { worldRetired = Set.insert loan (worldRetired w)
                   , worldActive = Just next }), SourceAdvanced event)
      _ -> reject w "close requires live loan"
  (NeedRelease, Nothing) ->
    case (activeOwner a, activeBranch a) of
      (Just owner, Just branch)
        | Set.member owner (worldIssued w)
        , not (Set.member owner (worldRetired w)) ->
          let event = ReleasedOwner owner
              released = record event
                (w { worldRetired = Set.insert owner (worldRetired w) })
          in finish released branch (ReturnedUnit branch)
      _ -> reject w "release requires exactly one live owner and digest branch"
  _ -> reject w "wrong event kind, qualified occurrence, or source program counter"
  where
    reject original message = (original, SourceRejected message)
    record event original =
      original { worldEvents = event : worldEvents original }
    mint original =
      let origin = Origin (worldNamespace original) (worldNextOrigin original)
      in (origin, original
        { worldNextOrigin = worldNextOrigin original + 1
        , worldIssued = Set.insert origin (worldIssued original) })
    finish original branch event =
      let ended = record event (original { worldActive = Nothing })
          done = case event of
            ReturnedUnit _ -> ended
            _ -> record (ReturnedUnit branch) ended
      in (done, SourceReturnedUnit branch)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
