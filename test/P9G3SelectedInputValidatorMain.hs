{-# LANGUAGE OverloadedStrings #-}

-- Scratch evidence-only selected original input gate. No production API,
-- new provider authority, or arbitrary native ABI claim.
module Main (main) where

import Control.Monad (unless)
import qualified Data.ByteString as BS
import Data.List (elemIndex, isPrefixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as TText
import qualified Data.Text.Encoding as Text
import Data.Word (Word8)
import qualified P9G3OriginalInputKernel as K
import qualified Phil.Compiler.RuntimeChoicePayload as P
import qualified Phil.Compiler.SourceArchitecture as A
import qualified Phil.Compiler.SourceBundle as B
import qualified Phil.Core.ProviderQualification as QP
import qualified Phil.Core.Static as D
import qualified Phil.Core.Syntax as T
import Phil.Examples.Steve.ApplicationShell (steveGetShellEnvironment)
import qualified Phil.Examples.Steve.ProviderQualifications as Q
import qualified Phil.Surface.Check as E
import qualified Phil.Surface.Lineage as L
import qualified Phil.Surface.Syntax as X
import Phil.Compiler.SelectedSteveGetCoreExecution
import Phil.Examples.Phase1.SystemsWitnesses (steveCoreProgram)
import qualified Phil.Surface.SelectedSteveGetExecution as S
import qualified Phil.Systems.GenericLowering as C
import System.Exit (exitFailure)

require :: String -> Bool -> IO ()
require label ok = do
  unless ok (putStrLn ("FAIL: " ++ label) >> exitFailure)
  putStrLn ("PASS: " ++ label)

orDie :: Show e => String -> Either e a -> IO a
orDie label result = case result of
  Left e -> putStrLn ("FAIL: " ++ label ++ ": " ++ show e) >> exitFailure
  Right a -> pure a

toNat :: Integer -> K.Nat
toNat 0 = K.O
toNat n = K.S (toNat (n - 1))

byteNat :: Word8 -> K.Nat
byteNat = toNat . fromIntegral

-- The extracted proof pins the original carrier, BEFORE decoding or native
-- selected admission. The native selector is the independently accepted
-- FSEM-06 implementation; no expected_native stand-in is supplied here.
admitOriginal :: BS.ByteString -> C.CoreSystemsProgram
  -> P.RuntimeChoicePayloadPlan -> Either Text SelectedSteveGetCore
admitOriginal raw program plan
  | not (K.p9_raw_accepts (map byteNat (BS.unpack raw))) =
      Left "not the pinned original source carrier"
  | otherwise = case Text.decodeUtf8' raw of
      Left _ -> Left "invalid original UTF-8"
      Right decoded -> prepareSelectedSteveGetCore decoded program plan

payloadSpecs :: [P.RuntimeChoicePayloadSpec]
payloadSpecs =
  [ spec "StevePut" "put.entry" [arm "computed" "put.install" (Just "put.id")]
  , spec "StevePut" "put.install"
      [arm "installed" "put.ok" Nothing, arm "already-exists" "put.ok" Nothing,
       arm "storage-failure" "put.failure" Nothing]
  , spec "SteveGet" "get.entry"
      [arm "found" "get.check" (Just "get.bytes"), arm "not-found" "get.not-found" Nothing,
       arm "storage-failure" "get.failure" Nothing]
  , spec "SteveGet" "get.check"
      [arm "accepted" "get.ok" Nothing, arm "rejected" "get.integrity-failure" Nothing]
  ]
  where
    spec fn block arms = P.RuntimeChoicePayloadSpec (P.RuntimeChoiceSite fn block)
      (Map.fromList arms)
    arm label target value = (label, P.RuntimeChoicePayloadArm target value)

complete :: IO CoreRunResult -> IO CoreReceipt
complete action = do
  result <- action
  case result of
    CoreCompleted receipt -> pure receipt
    CoreRejected problem -> putStrLn ("FAIL: Core rejected " ++ show problem) >> exitFailure
    CoreWaiting _ -> putStrLn "FAIL: unexpected wait" >> exitFailure


-- Reify actual opaque origins by equality, never Show/hash/caller serial.
-- Allocation/retirement order comes from the persistent native event log;
-- independently observed sets and counter must agree.
allocationOrder :: [S.SourceEvent] -> [S.Origin]
allocationOrder = concatMap $ \event -> case event of
  S.ObservedReadFound _ _ owner -> [owner]
  S.OpenedLoan _ loan -> [loan]
  _ -> []

retirementOrder :: [S.SourceEvent] -> [S.Origin]
retirementOrder = concatMap $ \event -> case event of
  S.ClosedLoan loan -> [loan]
  S.ReleasedOwner owner -> [owner]
  _ -> []

snapshotLedger :: S.WorldSnapshot -> Either Text (K.Nat, [K.Nat], [K.Nat])
snapshotLedger snapshot = do
  let issued = allocationOrder (S.snapshotEvents snapshot)
      retired = retirementOrder (S.snapshotEvents snapshot)
      index origin = case elemIndex origin issued of
        Nothing -> Left "unissued actual origin"
        Just i -> Right (toNat (fromIntegral i))
      exact xs ys = Set.fromList xs == ys && length xs == Set.size ys
  unless (exact issued (S.snapshotIssued snapshot)
      && exact retired (S.snapshotRetired snapshot)
      && S.snapshotNextOrigin snapshot == fromIntegral (length issued))
    (Left "actual event history/ledger disagreement")
  i <- mapM index (reverse issued)
  r <- mapM index (reverse retired)
  pure (toNat (S.snapshotNextOrigin snapshot), i, r)

encodeBranch :: S.UnitBranch -> K.Unit_branch
encodeBranch branch = case branch of
  S.UnitFoundAccepted -> K.UnitAccepted
  S.UnitFoundRejected -> K.UnitRejected
  S.UnitNotFound -> K.UnitNotFound
  S.UnitStorageFailure -> K.UnitStorageFailure

-- Labels come from original qualified E, observations separately from the
-- actual delta. Full Text equality precedes singleton payload-table index
-- projection, and the actual digest outcome is compared before projection.
checkSourcePrefix :: S.SelectedSteveGet -> Text -> [S.SuppliedResponse]
  -> S.WorldSnapshot -> S.WorldSnapshot -> Int -> Either Text Bool
checkSourcePrefix source ident fixedE before after count = do
  let old = S.snapshotEvents before
      new = S.snapshotEvents after
      issued = allocationOrder new
      index origin = case elemIndex origin issued of
        Nothing -> Left "actual event names foreign origin"
        Just i -> Right (toNat (fromIntegral i))
      validRead at provider cid = at == S.selectedReadOccurrence source
        && provider == S.selectedReadProvider source && cid == ident
      validDigest at provider cid view = at == S.selectedDigestOccurrence source
        && provider == S.selectedDigestProvider source && cid == ident
        && view == "bytesView"
      digestLabel decision = case decision of
        S.DigestAccepted -> K.DigestAccepted
        S.DigestRejected _ -> K.DigestRejected
  unless (isPrefixOf old new && not (S.snapshotHasActiveInvocation before))
    (Left "not an actual source prefix on the original idle history")
  (readOutcome, digestOutcome, labels) <- case fixedE of
    [S.ReadResponse at p cid (S.ReadFound payload),
      S.DigestResponse at' p' cid' view decision]
      | validRead at p cid && validDigest at' p' cid' view ->
          Right (S.ReadFound payload, Just decision,
            [K.ReadFound K.O, K.NoInput, digestLabel decision, K.NoInput, K.NoInput])
    [S.ReadResponse at p cid S.ReadNotFound] | validRead at p cid ->
      Right (S.ReadNotFound, Nothing, [K.ReadNotFound])
    [S.ReadResponse at p cid (S.ReadStorageFailure reason)] | validRead at p cid ->
      Right (S.ReadStorageFailure reason, Nothing, [K.ReadFailure])
    _ -> Left "not an exact qualified selected E"
  let encode event = case event of
        S.ObservedReadFound at payload owner
          | at == S.selectedReadOccurrence source
          , readOutcome == S.ReadFound payload ->
              K.ObsFound K.O <$> index owner
        S.ObservedReadNotFound at
          | at == S.selectedReadOccurrence source
          , readOutcome == S.ReadNotFound -> Right K.ObsNotFound
        S.ObservedReadFailure at
          | at == S.selectedReadOccurrence source
          , S.ReadStorageFailure _ <- readOutcome -> Right K.ObsFailure
        S.OpenedLoan owner loan -> K.ObsBorrow <$> index owner <*> index loan
        S.ObservedDigest at owner loan decision
          | at == S.selectedDigestOccurrence source
          , Just decision == digestOutcome ->
              K.ObsDigest <$> index owner <*> index loan
                <*> pure (decision == S.DigestAccepted)
        S.ClosedLoan loan -> K.ObsClose <$> index loan
        S.ReleasedOwner owner -> K.ObsRelease <$> index owner
        S.ReturnedUnit result -> Right (K.ObsUnit (encodeBranch result))
        _ -> Left "actual source observation disagrees with qualified E"
  observations <- mapM encode (drop (length old) new)
  (n, i, r) <- snapshotLedger before
  (n', i', r') <- snapshotLedger after
  unless (count >= 0 && count <= length labels)
    (Left "invalid selected successful-step prefix length")
  -- Reconstruct the represented current control position from actual
  -- completed events and active status, not from offered E or a Core trace.
  let active = S.snapshotHasActiveInvocation after
  final <- case observations of
    [] | active -> Right (K.AwaitRead n' i' r')
    [K.ObsFound _ owner] | active ->
      Right (K.AwaitBorrow n' i' r' owner)
    [K.ObsFound _ owner, K.ObsBorrow _ loan] | active ->
      Right (K.AwaitDigest n' i' r' owner loan)
    [K.ObsFound _ owner, K.ObsBorrow _ loan, K.ObsDigest _ _ decision]
      | active -> Right (K.AwaitClose n' i' r' owner loan decision)
    [K.ObsFound _ owner, K.ObsBorrow _ loan, K.ObsDigest _ _ decision, K.ObsClose _]
      | active -> Right (K.AwaitRelease n' i' r' owner loan decision)
    [K.ObsFound _ _, K.ObsBorrow _ _, K.ObsDigest _ _ _, K.ObsClose _,
      K.ObsRelease _, K.ObsUnit branch] | not active ->
      Right (K.Done n' i' r' branch)
    [K.ObsNotFound, K.ObsUnit branch] | not active ->
      Right (K.Done n' i' r' branch)
    [K.ObsFailure, K.ObsUnit branch] | not active ->
      Right (K.Done n' i' r' branch)
    _ -> Left "actual prefix events and active status disagree"
  pure (K.p9_source_segment_accepts (K.AwaitRead n i r) (take count labels)
    final observations)

checkSourceRun :: S.SelectedSteveGet -> Text -> [S.SuppliedResponse]
  -> S.WorldSnapshot -> S.WorldSnapshot -> S.UnitBranch -> Either Text Bool
checkSourceRun source ident fixedE before after branch = do
  let count = case fixedE of
        [S.ReadResponse _ _ _ (S.ReadFound _), S.DigestResponse _ _ _ _ _] -> 5
        _ -> 1
  unless (not (S.snapshotHasActiveInvocation after)
      && reverse (S.snapshotEvents after) /= []
      && take 1 (reverse (S.snapshotEvents after)) == [S.ReturnedUnit branch])
    (Left "not the claimed completed actual source branch")
  checkSourcePrefix source ident fixedE before after count

-- Acquire the actual run and snapshots locally from one private world.
-- The pure prefix checker is not a credential for arbitrary supplied snapshots.
sourcePrefixControls :: S.SelectedSteveGet -> Text -> [S.SuppliedResponse]
  -> S.UnitBranch -> IO ()
sourcePrefixControls source ident fixedE branch = do
  world <- S.newSelectedWorld
  initial <- S.snapshotSelectedWorld world
  run <- S.beginSelectedSteveGet world source ident >>= orDie "prefix begin"
  let checkAt count = do
        snapshot <- S.snapshotSelectedWorld world
        checked <- orDie "actual source prefix representation"
          (checkSourcePrefix source ident fixedE initial snapshot count)
        require ("extracted actual prefix " ++ show branch ++ "/" ++ show count) checked
      waiting expected = do
        before <- S.snapshotSelectedWorld world
        result <- S.stepSelectedSteveGet run Nothing
        after <- S.snapshotSelectedWorld world
        require "actual waiting leaves source prefix unchanged"
          (result == expected && before == after)
      inputs = case fixedE of
        [readReply, digestReply] -> [Just readReply, Nothing, Just digestReply, Nothing, Nothing]
        [readReply] -> [Just readReply]
        _ -> []
  checkAt 0
  waiting S.NeedsReadResponse
  mapM_ (\(count, supplied) -> do
    result <- S.stepSelectedSteveGet run supplied
    require "actual selected source step advances or returns its exact branch"
      (if count == length inputs then result == S.SourceReturnedUnit branch
       else case result of S.SourceAdvanced _ -> True; _ -> False)
    checkAt count
    if length inputs == 5 && count == 2 then waiting S.NeedsDigestResponse else pure ()
    ) (zip [1..] inputs)

-- The standalone selected source producer is actually executed twice on
-- the same world (not reconstructed from a target trace). Its observations
-- and opaque origin histories are compared at the public snapshot boundary.
sourceOnly :: S.SelectedSteveGet -> Text -> S.SuppliedResponse
  -> S.SuppliedResponse -> IO ()
sourceOnly source ident readFound digestAccepted = do
  world <- S.newSelectedWorld
  let inputs = [Just readFound, Nothing, Just digestAccepted, Nothing, Nothing]
  initial <- S.snapshotSelectedWorld world
  runA <- S.beginSelectedSteveGet world source ident >>= orDie "source begin A"
  resultA <- S.runSelectedFuel 5 runA inputs
  a <- S.snapshotSelectedWorld world
  require "source A completes without live resource"
    (resultA == S.DriveCompleted S.UnitFoundAccepted
      && not (S.snapshotHasActiveInvocation a)
      && S.snapshotIssued a == S.snapshotRetired a
      && S.snapshotNextOrigin a == 2)
  checkedA <- orDie "actual source A representation"
    (checkSourceRun source ident [readFound, digestAccepted] initial a S.UnitFoundAccepted)
  require "extracted source-only A segment reflection" checkedA
  runB <- S.beginSelectedSteveGet world source ident >>= orDie "source begin B"
  resultB <- S.runSelectedFuel 5 runB inputs
  b <- S.snapshotSelectedWorld world
  require "source B preserves complete A history with fresh distinct origins"
    (resultB == S.DriveCompleted S.UnitFoundAccepted
      && S.snapshotNextOrigin b == 4
      && S.snapshotIssued a `Set.isProperSubsetOf` S.snapshotIssued b
      && S.snapshotRetired a `Set.isProperSubsetOf` S.snapshotRetired b
      && S.snapshotIssued b == S.snapshotRetired b
      && take (length (S.snapshotEvents a)) (S.snapshotEvents b) == S.snapshotEvents a)
  checkedB <- orDie "actual source B representation"
    (checkSourceRun source ident [readFound, digestAccepted] a b S.UnitFoundAccepted)
  require "extracted source-only B segment reflection across persistent H" checkedB
  require "source-only checker rejects a different payload under the same original E"
    (case readFound of
      S.ReadResponse at provider cid (S.ReadFound _) ->
        case checkSourceRun source ident
          [S.ReadResponse at provider cid (S.ReadFound "different actual payload"), digestAccepted]
          initial a S.UnitFoundAccepted of
            Left _ -> True
            Right ok -> not ok
      _ -> False)
  stale <- S.stepSelectedSteveGet runA Nothing
  after <- S.snapshotSelectedWorld world
  require "retired source invocation cannot replay"
    (case stale of S.SourceRejected _ -> after == b; _ -> False)


-- Re-run the accepted ordinary bundle/architecture checker independently
-- from original bytes with the canonical FREE binder. Public diagnostics
-- do not mint a selected source or qualification credential.
originalMetadata :: Text -> S.SelectedSteveGet -> IO [Text]
originalMetadata decoded selected = do
  shell <- orDie "independent canonical environment" steveGetShellEnvironment
  let root = "program:steve.get"
      key = D.DeclarationKey "decl:steve.get"
      instanceSite = L.InstanceLineageSiteId "instance.steve"
      primitives = Map.restrictKeys (E.surfacePrimitives shell)
        (Set.fromList ["blob_read", "digest_check"])
      canonical = (E.emptySurfaceEnvironment D.emptyStaticContext)
        { E.surfaceInitialBindings = Map.singleton "contentId"
            (E.InitialBinding T.Unrestricted
              (T.TyOpaque "ContentId[SHA256]") E.PlainShape)
        , E.surfacePrimitives = primitives
        , E.surfaceExpectedProvides = Just T.TyUnit
        , E.surfaceReleaseTransitions = E.surfaceReleaseTransitions shell
        }
      bundle = L.PortableSourceBundle
        { L.portableGrammarRevision = L.canonicalGrammarRevisionV1
        , L.portableSelectedProgramRoot = root
        , L.portableSourceUnits =
            [ L.PortableSourceUnit (L.SourceUnitId "unit.steve.get")
                (L.DeclarationSiteId "site.steve.get")
                (Just "decl:steve.get") decoded ]
        , L.portableInstanceLineage =
            [L.PortableInstanceLineage instanceSite "inst:phase1.steve"]
        , L.portableProcessLineage = []
        }
  checked <- orDie "independent original checked source"
    (B.checkPortableSourceBundle (Map.singleton root key)
      (Map.singleton key canonical) bundle)
  architecture <- orDie "independent checked original architecture"
    (A.buildCheckedSourceArchitecture (Map.singleton root instanceSite) checked)
  let declaration = A.checkedSourceArchitectureDeclaration architecture
  require "independent checked original declaration and instance"
    (D.identityDeclarationKey declaration == S.selectedDeclarationKey selected
      && A.checkedSourceArchitectureInstanceKey architecture ==
        S.selectedInstanceKey selected
      && Map.size primitives == 2)
  component <- case B.checkedSourceUnits checked of
    [unit] | B.checkedSourceDeclarationKey unit == key ->
      pure (B.checkedSourceComponent unit)
    _ -> putStrLn "FAIL: independent checked source unit" >> exitFailure
  -- Ordinals count selected primitive calls in structural execution order,
  -- not the SourceEvidenceEvent proof-use ordinals.
  routes <- case originalCallSites component of
    Just [(0, readRoute, readAt), (1, digestRoute, digestAt)] -> do
      require "independent original AST call routes and occurrence spans"
        (readRoute == ["statement:0", "decide:scrutinee"]
          && digestRoute == ["statement:0", "arm:0:found", "statement:0",
              "borrow:body", "statement:0"]
          && readAt == S.selectedReadOccurrence selected
          && digestAt == S.selectedDigestOccurrence selected)
      putStrLn ("P9 ORIGINAL CALL 0: " ++ show (readRoute, readAt))
      putStrLn ("P9 ORIGINAL CALL 1: " ++ show (digestRoute, digestAt))
      pure (["0"] ++ readRoute ++ ["1"] ++ digestRoute)
    _ -> putStrLn "FAIL: independently checked original call route" >> exitFailure
  qualifications <- orDie "independent provider qualification materialization"
    Q.materializeSteveProviderQualifications
  let qualify operation artifact = S.QualifiedProviderRef
        operation
        (QP.providerContractInterfaceRevision (Q.steveProviderContract artifact))
        (QP.providerImplementationDefinitionRevision (Q.steveProviderImplementation artifact))
      blob = qualify "BlobProvider.read" (Q.steveBlobProviderQualification qualifications)
      digest = qualify "DigestProvider.check" (Q.steveDigestProviderQualification qualifications)
  require "independent qualified provider revision equality"
    (blob == S.selectedReadProvider selected && digest == S.selectedDigestProvider selected)
  putStrLn ("P9 ORIGINAL CHECKED DECLARATION: " ++ show declaration)
  putStrLn ("P9 ORIGINAL QUALIFIED READ: " ++ show blob)
  putStrLn ("P9 ORIGINAL QUALIFIED DIGEST: " ++ show digest)
  let D.InterfaceRevision interfaceRevision = D.identityInterfaceRevision declaration
      D.DefinitionRevision definitionRevision = D.identityDefinitionRevision declaration
  pure ([interfaceRevision, definitionRevision] ++ routes)

originalCallSites :: X.Located X.Component -> Maybe [(Int, [Text], X.SourceSpan)]
originalCallSites component = do
  [outerStatement] <- pure (X.blockStatements
    (X.locatedValue (X.componentBody (X.locatedValue component))))
  X.ExpressionStatement outer <- pure (X.locatedValue outerStatement)
  X.DecideExpression readCall [found, _, _] <- pure (X.locatedValue outer)
  X.CallExpression "blob_read" [_] <- pure (X.locatedValue readCall)
  let foundArm = X.locatedValue found
      armLabel = X.casePatternLabel (X.caseArmPattern foundArm)
  [binding, _] <- pure (X.blockStatements (X.locatedValue (X.caseArmBody foundArm)))
  X.LetStatement _ borrowed <- pure (X.locatedValue binding)
  X.BorrowExpression _ "bytesView" borrowBody <- pure (X.locatedValue borrowed)
  [digestStatement] <- pure (X.blockStatements (X.locatedValue borrowBody))
  X.ExpressionStatement digestCall <- pure (X.locatedValue digestStatement)
  X.CallExpression "digest_check" [_, _] <- pure (X.locatedValue digestCall)
  pure [(0, ["statement:0", "decide:scrutinee"], X.locatedSpan readCall),
        (1, ["statement:0", "arm:0:" <> armLabel, "statement:0",
             "borrow:body", "statement:0"], X.locatedSpan digestCall)]


-- Reify the sealed selected descriptor independently of offered E. The
-- original metadata above comes from a distinct ordinary checked path;
-- neither the metadata nor actual binding supplies the kernel's expectation.
encodeName :: Text -> [K.Nat]
encodeName = map byteNat . BS.unpack . Text.encodeUtf8

encodeSpan :: X.SourceSpan -> [[K.Nat]]
encodeSpan s = point (X.sourceSpanStart s) ++ point (X.sourceSpanEnd s)
  where
    point p = map encodeName [X.sourcePointFile p,
      TText.pack (show (X.sourcePointLine p)),
      TText.pack (show (X.sourcePointColumn p)),
      TText.pack (show (X.sourcePointOffset p))]

encodeBinding :: S.SelectedSteveGet -> Text -> K.Selected_binding
encodeBinding source ident =
  let D.DeclarationKey key = S.selectedDeclarationKey source
      D.InstanceKey instanceKey = S.selectedInstanceKey source
      readProvider = S.selectedReadProvider source
      digestProvider = S.selectedDigestProvider source
      D.InterfaceRevision ri = S.qualifiedProviderInterface readProvider
      D.DefinitionRevision rd = S.qualifiedProviderImplementation readProvider
      D.InterfaceRevision di = S.qualifiedProviderInterface digestProvider
      D.DefinitionRevision dd = S.qualifiedProviderImplementation digestProvider
  in K.Binding (encodeName key) (encodeName instanceKey)
       (encodeSpan (S.selectedReadOccurrence source))
       (encodeSpan (S.selectedDigestOccurrence source))
       (encodeName (S.qualifiedProviderOperation readProvider)) (encodeName ri) (encodeName rd)
       (encodeName (S.qualifiedProviderOperation digestProvider)) (encodeName di) (encodeName dd)
       (encodeName ident)

checkAnchor :: BS.ByteString -> [Text] -> Text -> K.Selected_binding -> Bool
checkAnchor raw metadata ident = K.p9_anchored_source_accepts
  (map byteNat (BS.unpack raw)) (map encodeName metadata) (encodeName ident)

-- This test-only wrapper retains the free argument that passed the anchor.
-- No subsequent caller can choose a second ContentId at invocation start.
data AnchoredOriginal = AnchoredOriginal !SelectedSteveGetCore !Text

admitAnchoredOriginal :: BS.ByteString -> [Text] -> S.SelectedSteveGet -> Text
  -> C.CoreSystemsProgram -> P.RuntimeChoicePayloadPlan -> Either Text AnchoredOriginal
admitAnchoredOriginal raw metadata source ident program plan = do
  decoded <- either (const (Left "invalid original UTF-8")) Right (Text.decodeUtf8' raw)
  admitted <- either (Left . TText.pack . show) Right (S.prepareSelectedSteveGet decoded)
  unless (source == admitted && checkAnchor raw metadata ident (encodeBinding admitted ident))
    (Left "original checked source anchor rejected")
  selected <- admitOriginal raw program plan
  pure (AnchoredOriginal selected ident)

runAnchoredOriginal :: SelectedCoreWorld -> AnchoredOriginal
  -> [S.SuppliedResponse] -> IO CoreRunResult
runAnchoredOriginal world (AnchoredOriginal selected ident) =
  runSelectedSteveGetCore world selected ident

anchorNegatives :: BS.ByteString -> [Text] -> S.SelectedSteveGet -> Text -> IO ()
anchorNegatives raw metadata source ident = do
  let actual = encodeBinding source ident
      K.Binding dk ik readAt digestAt blob ri rd digest di dd cid = actual
      alternatives =
        [ ("read occurrence", K.Binding dk ik [] digestAt blob ri rd digest di dd cid)
        , ("digest occurrence", K.Binding dk ik readAt [] blob ri rd digest di dd cid)
        , ("Blob qualification revision", K.Binding dk ik readAt digestAt blob [] rd digest di dd cid)
        , ("Digest qualification revision", K.Binding dk ik readAt digestAt blob ri rd digest di [] cid)
        , ("original declaration", K.Binding [] ik readAt digestAt blob ri rd digest di dd cid)
        , ("original instance", K.Binding dk [] readAt digestAt blob ri rd digest di dd cid)
        , ("self-paired empty occurrence/revisions", K.Binding dk ik [] [] blob [] [] digest [] [] cid)
        ]
  require "extracted anchored original source and invocation binding" (checkAnchor raw metadata ident actual)
  mapM_ (\(label, bad) -> require ("anchored gate rejects " ++ label)
    (not (checkAnchor raw metadata ident bad))) alternatives
  require "anchored gate rejects different invocation ContentId"
    (not (checkAnchor raw metadata "different-content-id" actual))
  require "anchored gate rejects different actual declaration revision"
    (not (checkAnchor raw ("different-revision" : drop 1 metadata) ident actual))
  require "anchored gate rejects different original occurrence route/ordinal"
    (not (checkAnchor raw (take 2 metadata ++ ["9"] ++ drop 3 metadata) ident actual))

main :: IO ()
main = do
  raw <- BS.readFile "examples/steve/get.phil"
  decoded <- orDie "exact UTF-8 original" (Text.decodeUtf8' raw)
  source <- orDie "independent admitted source" (S.prepareSelectedSteveGet decoded)
  metadata <- originalMetadata decoded source
  let ident = "sha256:fixed-selected"
  anchorNegatives raw metadata source ident
  plan <- orDie "recertified actual full native plan"
    (P.certifyRuntimeChoicePayloadPlan steveCoreProgram payloadSpecs)
  anchored@(AnchoredOriginal selected _) <- orDie "exact original + accepted full native selector"
    (admitAnchoredOriginal raw metadata source ident steveCoreProgram plan)
  require "same semantic shape but changed carrier cannot pass P9 raw gate"
    (case admitOriginal (raw <> "// changed original carrier\n") steveCoreProgram plan of
      Left "not the pinned original source carrier" -> True
      _ -> False)
  let readFound = S.ReadResponse (S.selectedReadOccurrence source)
        (S.selectedReadProvider source) ident (S.ReadFound "same exact bytes")
      digestAccepted = S.DigestResponse (S.selectedDigestOccurrence source)
        (S.selectedDigestProvider source) ident "bytesView" S.DigestAccepted
      digestRejected = S.DigestResponse (S.selectedDigestOccurrence source)
        (S.selectedDigestProvider source) ident "bytesView" (S.DigestRejected "reason")
      fixedE = [readFound, digestAccepted]
  sourceOnly source ident readFound digestAccepted
  sourcePrefixControls source ident fixedE S.UnitFoundAccepted
  sourcePrefixControls source ident [readFound, digestRejected] S.UnitFoundRejected
  sourcePrefixControls source ident
    [S.ReadResponse (S.selectedReadOccurrence source) (S.selectedReadProvider source)
       ident S.ReadNotFound] S.UnitNotFound
  sourcePrefixControls source ident
    [S.ReadResponse (S.selectedReadOccurrence source) (S.selectedReadProvider source)
       ident (S.ReadStorageFailure "reason")] S.UnitStorageFailure
  world <- newSelectedCoreWorld
  a <- complete (runAnchoredOriginal world anchored fixedE)
  b <- complete (runAnchoredOriginal world anchored fixedE)
  pairA <- maybe (putStrLn "FAIL: missing original origin pair" >> exitFailure) pure
    (receiptOriginPair a)
  pairB <- maybe (putStrLn "FAIL: missing second origin pair" >> exitFailure) pure
    (receiptOriginPair b)
  require "exact invocation E and original contentId only"
    (receiptMatchesContext a selected ident fixedE
      && not (receiptMatchesContext a selected ident [readFound, digestRejected])
      && not (receiptMatchesContext a selected "other-id" fixedE))
  require "both actual pairs valid, cross-invocation B/B substitution rejected"
    (uncurry (receiptMatchesOriginPair a) pairA
      && uncurry (receiptMatchesOriginPair b) pairB
      && not (uncurry (receiptMatchesOriginPair a) pairB))
  putStrLn "PASS: scratch original-input and selected reference integration controls; not a P9 discharge"
