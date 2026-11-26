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
import qualified Data.Text.Encoding as Text
import Data.Word (Word8)
import qualified P9G3OriginalInputKernel as K
import qualified Phil.Compiler.RuntimeChoicePayload as P
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
checkSourceRun :: S.SelectedSteveGet -> Text -> [S.SuppliedResponse]
  -> S.WorldSnapshot -> S.WorldSnapshot -> S.UnitBranch -> Either Text Bool
checkSourceRun source ident fixedE before after branch = do
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
  unless (isPrefixOf old new
      && not (S.snapshotHasActiveInvocation before)
      && not (S.snapshotHasActiveInvocation after))
    (Left "not a complete actual source invocation on the same history")
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
  pure (K.p9_source_segment_accepts (K.AwaitRead n i r) labels
    (K.Done n' i' r' (encodeBranch branch)) observations)

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

main :: IO ()
main = do
  raw <- BS.readFile "examples/steve/get.phil"
  decoded <- orDie "exact UTF-8 original" (Text.decodeUtf8' raw)
  source <- orDie "independent admitted source" (S.prepareSelectedSteveGet decoded)
  plan <- orDie "recertified actual full native plan"
    (P.certifyRuntimeChoicePayloadPlan steveCoreProgram payloadSpecs)
  selected <- orDie "exact original + accepted full native selector"
    (admitOriginal raw steveCoreProgram plan)
  require "same semantic shape but changed carrier cannot pass P9 raw gate"
    (case admitOriginal (raw <> "// changed original carrier\n") steveCoreProgram plan of
      Left "not the pinned original source carrier" -> True
      _ -> False)
  let ident = "sha256:fixed-selected"
      readFound = S.ReadResponse (S.selectedReadOccurrence source)
        (S.selectedReadProvider source) ident (S.ReadFound "same exact bytes")
      digestAccepted = S.DigestResponse (S.selectedDigestOccurrence source)
        (S.selectedDigestProvider source) ident "bytesView" S.DigestAccepted
      digestRejected = S.DigestResponse (S.selectedDigestOccurrence source)
        (S.selectedDigestProvider source) ident "bytesView" (S.DigestRejected "reason")
      fixedE = [readFound, digestAccepted]
  sourceOnly source ident readFound digestAccepted
  world <- newSelectedCoreWorld
  a <- complete (runSelectedSteveGetCore world selected ident fixedE)
  b <- complete (runSelectedSteveGetCore world selected ident fixedE)
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
