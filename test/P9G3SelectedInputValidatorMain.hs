{-# LANGUAGE OverloadedStrings #-}

-- Scratch evidence-only selected original input gate. No production API,
-- new provider authority, or arbitrary native ABI claim.
module Main (main) where

import Control.Monad (unless)
import qualified Data.ByteString as BS
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

byteNat :: Word8 -> K.Nat
byteNat = go . fromIntegral
  where
    go :: Int -> K.Nat
    go 0 = K.O
    go n = K.S (go (n - 1))

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

-- The standalone selected source producer is actually executed twice on
-- the same world (not reconstructed from a target trace). Its observations
-- and opaque origin histories are compared at the public snapshot boundary.
sourceOnly :: S.SelectedSteveGet -> Text -> S.SuppliedResponse
  -> S.SuppliedResponse -> IO ()
sourceOnly source ident readFound digestAccepted = do
  world <- S.newSelectedWorld
  let inputs = [Just readFound, Nothing, Just digestAccepted, Nothing, Nothing]
  runA <- S.beginSelectedSteveGet world source ident >>= orDie "source begin A"
  resultA <- S.runSelectedFuel 5 runA inputs
  a <- S.snapshotSelectedWorld world
  require "source A completes without live resource"
    (resultA == S.DriveCompleted S.UnitFoundAccepted
      && not (S.snapshotHasActiveInvocation a)
      && S.snapshotIssued a == S.snapshotRetired a
      && S.snapshotNextOrigin a == 2)
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
