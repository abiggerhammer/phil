{-# LANGUAGE OverloadedStrings #-}

-- | Standalone bounded Haskell producer adversarial replay, not native ABI.
module Main (main) where

import Control.Monad (unless)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Surface.SelectedSteveGetExecution
import Phil.Core.Static (DeclarationKey (..), InstanceKey (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  original <- TextIO.readFile "examples/steve/get.phil"
  selected <- case prepareSelectedSteveGet original of
    Left problem -> die ("original source recheck failed: " ++ show problem)
    Right value -> pure value
  require "rechecked original source K" $
    selectedDeclarationKey selected == DeclarationKey "decl:steve.get"
  require "rechecked original source I" $
    selectedInstanceKey selected == InstanceKey "inst:phase1.steve"
  mapM_ (rejectMutation original) mutations

  world <- newSelectedWorld
  first <- beginOrDie world selected "sha256:exact-id"
  require "no reentrant selected invocation" . either (const True) (const False)
    =<< beginSelectedSteveGet world selected "sha256:exact-id"
  require "bounded driver reports zero-fuel partiality" . (== DriveFuelExhausted)
    =<< runSelectedFuel 0 first [Nothing]
  require "bounded driver reports empty E prefix" . (== DriveInputPrefixEnded)
    =<< runSelectedFuel 2 first []
  require "bounded driver reports unanswered read" . (== DriveWaitingForResponse)
    =<< runSelectedFuel 2 first [Nothing]
  requireResult "missing first response waits" NeedsReadResponse
    =<< stepSelectedSteveGet first Nothing
  beforeBad <- snapshotSelectedWorld world
  requireRejected "wrong read occurrence"
    =<< stepSelectedSteveGet first (Just
      (ReadResponse (selectedDigestOccurrence selected)
        "BlobProvider.read" "sha256:exact-id" (ReadFound "same-payload")))
  requireRejected "wrong provider at read"
    =<< stepSelectedSteveGet first (Just
      (ReadResponse (selectedReadOccurrence selected)
        "OtherProvider.read" "sha256:exact-id" (ReadFound "same-payload")))
  requireRejected "forged read argument"
    =<< stepSelectedSteveGet first (Just
      (ReadResponse (selectedReadOccurrence selected)
        "BlobProvider.read" "sha256:swapped" (ReadFound "same-payload")))
  require "rejections preserve world" . (== beforeBad)
    =<< snapshotSelectedWorld world
  requireRejected "digest before read"
    =<< stepSelectedSteveGet first (Just
      (DigestResponse (selectedDigestOccurrence selected)
        "DigestProvider.check" "sha256:exact-id" "bytesView" DigestAccepted))
  requireAdvanced "qualified actual source found response"
    =<< stepSelectedSteveGet first (Just
      (ReadResponse (selectedReadOccurrence selected)
        "BlobProvider.read" "sha256:exact-id" (ReadFound "same-payload")))
  require "found allocated one owner" . ((== 1) . Set.size . snapshotIssued)
    =<< snapshotSelectedWorld world
  requireAdvanced "lexical borrow generates loan"
    =<< stepSelectedSteveGet first Nothing
  require "loan allocated distinct origin" . ((== 2) . Set.size . snapshotIssued)
    =<< snapshotSelectedWorld world
  requireRejected "wrong digest occurrence"
    =<< stepSelectedSteveGet first (Just
      (DigestResponse (selectedReadOccurrence selected)
        "DigestProvider.check" "sha256:exact-id" "bytesView" DigestAccepted))
  requireRejected "swapped digest id"
    =<< stepSelectedSteveGet first (Just
      (DigestResponse (selectedDigestOccurrence selected)
        "DigestProvider.check" "sha256:swapped" "bytesView" DigestAccepted))
  requireRejected "replaced view"
    =<< stepSelectedSteveGet first (Just
      (DigestResponse (selectedDigestOccurrence selected)
        "DigestProvider.check" "sha256:exact-id" "otherView" DigestAccepted))
  requireRejected "premature close attempted by wrong event"
    =<< stepSelectedSteveGet first (Just
      (ReadResponse (selectedReadOccurrence selected)
        "BlobProvider.read" "sha256:exact-id" (ReadNotFound)))
  requireResult "wait for digest" NeedsDigestResponse
    =<< stepSelectedSteveGet first Nothing
  requireAdvanced "digest only under live loan"
    =<< stepSelectedSteveGet first (Just
      (DigestResponse (selectedDigestOccurrence selected)
        "DigestProvider.check" "sha256:exact-id" "bytesView" DigestAccepted))
  requireRejected "new digest forbidden after source decides"
    =<< stepSelectedSteveGet first (Just
      (DigestResponse (selectedDigestOccurrence selected)
        "DigestProvider.check" "sha256:exact-id" "bytesView" DigestAccepted))
  requireAdvanced "loan close" =<< stepSelectedSteveGet first Nothing
  require "loan close retires only loan" . ((== 1) . Set.size . snapshotRetired)
    =<< snapshotSelectedWorld world
  requireRejected "digest after closed loan"
    =<< stepSelectedSteveGet first (Just
      (DigestResponse (selectedDigestOccurrence selected)
        "DigestProvider.check" "sha256:exact-id" "bytesView" DigestAccepted))
  requireResult "release exact owner and return Unit" (SourceReturnedUnit UnitFoundAccepted)
    =<< stepSelectedSteveGet first Nothing
  requireRejected "replay finished invocation"
    =<< stepSelectedSteveGet first Nothing

  firstDone <- snapshotSelectedWorld world
  require "owner and loan retained retired" $
    Set.size (snapshotRetired firstDone) == 2
      && snapshotIssued firstDone == snapshotRetired firstDone
      && not (snapshotHasActiveInvocation firstDone)

  second <- beginOrDie world selected "sha256:exact-id"
  requireAdvanced "identical second payload, fresh owner"
    =<< stepSelectedSteveGet second (Just
      (ReadResponse (selectedReadOccurrence selected)
        "BlobProvider.read" "sha256:exact-id" (ReadFound "same-payload")))
  requireAdvanced "second fresh loan" =<< stepSelectedSteveGet second Nothing
  requireAdvanced "second digest rejected" =<< stepSelectedSteveGet second
    (Just (DigestResponse (selectedDigestOccurrence selected)
      "DigestProvider.check" "sha256:exact-id" "bytesView" (DigestRejected "wrong-digest")))
  requireAdvanced "second close" =<< stepSelectedSteveGet second Nothing
  requireResult "second release Unit" (SourceReturnedUnit UnitFoundRejected)
    =<< stepSelectedSteveGet second Nothing
  twice <- snapshotSelectedWorld world
  require "fresh distinct nonreusable origins across same-content invocations" $
    Set.size (snapshotIssued twice) == 4
      && snapshotIssued twice == snapshotRetired twice
      && snapshotNextOrigin twice == 4
  require "old retired origins retained" $
    snapshotIssued firstDone `Set.isSubsetOf` snapshotIssued twice

  notFound <- beginOrDie world selected "sha256:exact-id"
  requireResult "not-found returns Unit" (SourceReturnedUnit UnitNotFound)
    =<< stepSelectedSteveGet notFound (Just
      (ReadResponse (selectedReadOccurrence selected)
        "BlobProvider.read" "sha256:exact-id" ReadNotFound))
  storageFail <- beginOrDie world selected "sha256:exact-id"
  requireResult "storage failure returns Unit" (SourceReturnedUnit UnitStorageFailure)
    =<< stepSelectedSteveGet storageFail (Just
      (ReadResponse (selectedReadOccurrence selected)
        "BlobProvider.read" "sha256:exact-id" (ReadStorageFailure "read-failed")))
  nonFound <- snapshotSelectedWorld world
  require "nonfound allocations empty" $
    snapshotIssued nonFound == snapshotIssued twice
      && snapshotNextOrigin nonFound == snapshotNextOrigin twice
  require "observed events include source-qualified digest/close/release" $
    length (snapshotEvents nonFound) >= 14

  otherWorld <- newSelectedWorld
  other <- beginOrDie otherWorld selected "sha256:exact-id"
  requireAdvanced "new world cannot reuse another world's abstract namespace"
    =<< stepSelectedSteveGet other (Just
      (ReadResponse (selectedReadOccurrence selected)
        "BlobProvider.read" "sha256:exact-id" (ReadFound "same-payload")))
  otherSnapshot <- snapshotSelectedWorld otherWorld
  require "reset/new world does not equal previous origin" $
    Set.null (Set.intersection (snapshotIssued otherSnapshot) (snapshotIssued twice))
  requireRejected "stale invocation cannot forge live origin in another world"
    =<< stepSelectedSteveGet first Nothing

  -- The snapshot is read-only; no API accepts a serial or rewrites issued H.
  putStrLn "PASS: selected original Surface read/digest producer adversarial matrix"
  where
    die message = putStrLn ("FAIL: " ++ message) >> exitFailure

mutations :: [(String, Text, Text)]
mutations =
  [ ("different found binder", "found(bytes)", "found(other)")
  , ("borrow wrong owner", "borrow bytes as bytesView", "borrow contentId as bytesView")
  , ("swapped digest arguments", "digest_check(contentId, bytesView)",
       "digest_check(bytesView, contentId)")
  , ("digest call moved to wrong scope", "digest_check(contentId, bytesView)",
       "blob_read(contentId)")
  , ("wrong result binder", "let digestDecision", "let wrongDecision")
  , ("wrong release", "release bytes", "release contentId")
  , ("unknown branch", "not-found =>", "notfound =>")
  , ("duplicate digest", "accepted => {",
       "accepted => {\n                    digest_check(contentId, bytesView)")
  ]

rejectMutation :: Text -> (String, Text, Text) -> IO ()
rejectMutation original (label, before, after) = do
  let mutated = Text.replace before after original
  require ("mutation actually changes source: " ++ label) (mutated /= original)
  case prepareSelectedSteveGet mutated of
    Left _ -> putStrLn ("PASS: rejection " ++ label)
    Right _ -> putStrLn ("FAIL: accepted source mutation " ++ label) >> exitFailure

beginOrDie :: SelectedWorld -> SelectedSteveGet -> Text -> IO SelectedRun
beginOrDie world selected contentId = do
  x <- beginSelectedSteveGet world selected contentId
  case x of
    Right run -> pure run
    Left reason -> putStrLn ("FAIL: begin selected: " ++ Text.unpack reason)
      >> exitFailure

require :: String -> Bool -> IO ()
require label value =
  unless value $ putStrLn ("FAIL: " ++ label) >> exitFailure

requireResult :: String -> StepResult -> StepResult -> IO ()
requireResult label expected actual = do
  require label (expected == actual)
  putStrLn ("PASS: " ++ label)

requireAdvanced :: String -> StepResult -> IO ()
requireAdvanced label actual = case actual of
  SourceAdvanced _ -> putStrLn ("PASS: " ++ label)
  _ -> putStrLn ("FAIL: " ++ label ++ " got " ++ show actual)
       >> exitFailure

requireRejected :: String -> StepResult -> IO ()
requireRejected label actual = case actual of
  SourceRejected _ -> putStrLn ("PASS: " ++ label)
  _ -> putStrLn ("FAIL: " ++ label ++ " got " ++ show actual)
       >> exitFailure
