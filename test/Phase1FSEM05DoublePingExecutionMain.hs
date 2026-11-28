{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (forM_, unless)
import qualified Data.ByteString as Bytes
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Context (ResourceContext (..))
import Phil.Core.Static (DeclarationKey (..))
import Phil.Core.Syntax (Outcome (..), Session (..), Ty (..))
import Phil.Surface.GrammarV1.DoublePingExecution
import Phil.Surface.Syntax (SourceSpan, sourcePointOffset, sourceSpanEnd, sourceSpanStart)

assert :: String -> Bool -> IO ()
assert label result = unless result (fail label)

sourcePath, sidecarPath :: FilePath
sourcePath = "test/fixtures/fsem02-two-step-source-chain-v1/accepted.phil"
sidecarPath = "test/fixtures/fsem03-doubleping-origin-v1/candidate.tsv"

main :: IO ()
main = do
  source <- Bytes.readFile sourcePath
  sidecar <- Bytes.readFile sidecarPath
  forM_ [(17, 42), (42, 17), (0, 255), (255, 0), (17, 17)] $ \(first, second) ->
    positive source sidecar first second
  let valid = [("first", 17), ("second", 42)]
      reject label want actual = case actual of
        Left got -> assert label (got == want)
        Right _ -> fail (label <> ": unexpectedly admitted")
  forM_ invalidAssignments $ \(label, entries) ->
    reject label InvalidEntries (runSelectedDoublePing source sidecar entries)
  reject "foreign source" UnselectedSource (runSelectedDoublePing (source <> "\n") sidecar valid)
  reject "foreign sidecar" UnselectedSidecar (runSelectedDoublePing source (sidecar <> "\n") valid)
  forM_ [("stale origin", "2fc0c4abe970f398b516a2bdff2000ac4d09333f")
        ,("foreign K", "decl:3e98e243-262e-4c0b-bfc9-849a36a83f2d")
        ,("foreign I/D", "phil.component.doubleping-interface.v1")
        ,("foreign graph slot", "slot:7acb")] $ \(label, original) -> do
    let (before, after) = Bytes.breakSubstring original sidecar
    assert (label <> ": fixture occurrence") (not (Bytes.null after))
    let changed = before <> "X" <> Bytes.drop 1 after
    reject label UnselectedSidecar (runSelectedDoublePing source changed valid)
  putStrLn "PASS: selected bytes and malformed entry admission negatives"

invalidAssignments :: [(String, [(Text, Integer)])]
invalidAssignments =
  [("missing both", []), ("missing second", [("first", 17)])
  ,("extra", [("first", 17), ("second", 42), ("third", 7)])
  ,("duplicate first", [("first", 17), ("first", 42)])
  ,("duplicate second", [("second", 17), ("second", 42)])
  ,("mis-cased label", [("First", 17), ("second", 42)])
  ,("unrelated label", [("third", 17), ("second", 42)])
  ,("negative", [("first", -1), ("second", 42)])
  ,("oversized", [("first", 17), ("second", 256)])
  ,("integer far outside U8", [("first", 2 ^ (100 :: Int)), ("second", 42)])]

positive :: Bytes.ByteString -> Bytes.ByteString -> Integer -> Integer -> IO ()
positive source sidecar first second = do
  -- Exercise reversed input list order without altering entry identity.
  run <- either (fail . show) pure $
    runSelectedDoublePing source sidecar [("second", second), ("first", first)]
  let a = fromInteger first
      b = fromInteger second
  assert "qualification and exact input assignment" $
    runOutcome run == Right () && runInputs run == (a, b) && length (runDeclarations run) == 5
  case runSnapshots run of
    [s0, s1, s2] -> do
      assert "exact checked PC progression" $
        map snapshotStages [s0, s1, s2] == [(First, First), (Second, Second), (PreClose, PreClose)]
      assert "two original actions, then the original two Close PCs" $
        map (observedExpressions source . snapshotPositions) [s0, s1, s2] ==
          [("send first on endpoint", "receive U8 on endpoint")
          ,("send second on middle", "receive U8 on middle")
          ,("close done", "close done")]
      case (snapshotEvents s0, snapshotEvents s1, snapshotEvents s2) of
        ([], [e1], [again, e2]) -> do
          let (send1, receive1) = eventBinders e1
              (send2, receive2) = eventBinders e2
              (client, clientDecl, n1) = binderIdentity send1
              (server, serverDecl, m1) = binderIdentity receive1
          assert "joint event spans and retained S1 event" $
            eventPositions e1 == snapshotPositions s0 && eventPositions e2 == snapshotPositions s1
            && eventKey e1 == eventKey again && eventValue e1 == eventValue again && eventKey e1 /= eventKey e2
          assert "exact lexical identity even for equal payloads" $
            client /= server && n1 == 1 && m1 == 2
            && clientDecl == DeclarationKey "decl:5d21799d-9609-4c0c-b4af-a599192d5bd9"
            && serverDecl == DeclarationKey "decl:cc94aab1-3cdc-4a89-b755-f38218cda401"
            && binderIdentity send2 == (client, clientDecl, 2)
            && binderIdentity receive2 == (server, serverDecl, 4)
          assert "source values advance without inserting native values" $
            eventValue e1 == a && eventValue e2 == b && null (snapshotReceived s0)
            && snapshotReceived s1 == [(receive1, a)]
            && snapshotReceived s2 == [(receive1, a), (receive2, b)]
          forM_ [s0, s1, s2] $ \s -> do
            let resources = snapshotResources s
                owners = Map.elems (snapshotOwners s)
            assert "both exact endpoint owners inhabit native resource maps" $
              Map.size resources == 2 && length owners == 2
              && all (\(process, name) -> maybe False (Map.member name . linearBindings) (Map.lookup process resources)) owners
              && all ((== 1) . Map.size . linearBindings) (Map.elems resources)
              && maybe False ((== [TyUInt 8, TyUInt 8]) . Map.elems . unrestrictedBindings) (Map.lookup client resources)
              && maybe False (Map.null . unrestrictedBindings) (Map.lookup server resources)
          assert "pre-Close keeps both Done endpoint resources" $
            all ((== [TyEndpoint (End (Outcome "Done"))]) . Map.elems . linearBindings) $
              Map.elems (snapshotResources s2)
        _ -> fail "wrong committed event prefix"
    _ -> fail "wrong committed snapshot length"
  putStrLn ("PASS: selected D3 value and endpoint prefix " <> show (first, second))

observedExpressions :: Bytes.ByteString -> (SourceSpan, SourceSpan)
                    -> (Bytes.ByteString, Bytes.ByteString)
observedExpressions source (first, second) = (extract first, extract second)
  where
    extract spanValue =
      let start = sourcePointOffset (sourceSpanStart spanValue)
          end = sourcePointOffset (sourceSpanEnd spanValue)
      in Bytes.take (end - start) (Bytes.drop start source)
