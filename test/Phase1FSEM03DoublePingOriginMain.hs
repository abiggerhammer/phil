{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (forM_, unless)
import qualified Data.ByteString as Bytes
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as UTF8
import Phil.Core.Process
import Phil.Core.ProcessActivation (ProcessActivationContract (..))
import Phil.Core.Protocol (ProtocolEndpointBinding (..), ProtocolRoleKey (..))
import Phil.Core.Static
import Phil.Surface.GrammarV1.ArchitectureComponentActivation (GrammarV1ResolvedComponentActivation (..))
import Phil.Surface.GrammarV1.ComponentTwoStepChain (ChainError (..))
import Phil.Surface.GrammarV1.DoublePingOrigin
import System.Environment (getArgs)

sourcePath :: FilePath
sourcePath = "test/fixtures/fsem02-two-step-source-chain-v1/accepted.phil"

manifestPath :: FilePath
manifestPath = "test/fixtures/fsem03-doubleping-origin-v1/candidate.tsv"

anchor :: SourceAnchor
anchor = SourceAnchor "2fc0c4abe970f398b516a2bdff2000ac4d09333f"
  "76f1d238407397ec09d358a42ff9ebaac4c44909" (Text.pack sourcePath)
  "33687d0c4320dda4d136fa16038f4fad043d14e1367729b8db43044e2d5c51e7"

-- Proposed opaque tokens, deliberately lacking any issuance semantics.
lineage :: CandidateLineage
lineage = CandidateLineage
  [ ("site:8dfe", DeclarationKey "decl:3e98e243-262e-4c0b-bfc9-849a36a83f2d")
  , ("site:3cd1", DeclarationKey "decl:5d21799d-9609-4c0c-b4af-a599192d5bd9")
  , ("site:0f94", DeclarationKey "decl:cc94aab1-3cdc-4a89-b755-f38218cda401")
  , ("site:ad23", DeclarationKey "decl:4940750f-e575-4ea5-a63c-4b88bda44062")
  , ("site:6e5c", DeclarationKey "decl:a228fb5e-5be6-424e-bffe-b890252bbe12")
  ]
  [OccurrenceSlotKey "slot:7acb", OccurrenceSlotKey "slot:f2e7"]
  [ProcessSiteKey "process:9d3b", ProcessSiteKey "process:f71c"]

main :: IO ()
main = do
  source <- Bytes.readFile sourcePath
  args <- getArgs
  case args of
    ["--prepare"] -> fst <$> right (prepareCandidate anchor source lineage) >>= Bytes.putStr
    [] -> runTests source
    _ -> fail "expected no arguments or --prepare"

runTests :: Bytes.ByteString -> IO ()
runTests source = do
  manifest <- Bytes.readFile manifestPath
  let selected = (source, manifest)
      examine = checkSelectedCandidate anchor selected
      testAnchor bytes = anchor {anchorSHA256 = sourceDigest bytes}
      selectForTest bytes metadata = checkSelectedCandidate (testAnchor bytes) (bytes, metadata) (bytes, metadata)
      prepareTest bytes = prepareCandidate (testAnchor bytes) bytes lineage
      sourceEdit old new = replace old new source
      revision row field = changeField row field (const "stale-revision") manifest
  assert "original SHA-256" $
    sourceDigest source == "33687d0c4320dda4d136fa16038f4fad043d14e1367729b8db43044e2d5c51e7"
  accepted <- right (examine selected)
  assert "exact conditional original association" $
    candidateManifest accepted == manifest && length (candidateDeclarations accepted) == 5
    && Map.size (architectureGraphInstances (candidateGraph accepted)) == 3
    && length (candidateSites accepted) == 2 && length (candidateActivation accepted) == 2
  let network = candidateNetwork accepted
      population = Map.elems (processNetworkPopulation network)
  assert "exact root-owned unactivated population" $
    length population == 2
    && all (\p -> processOccurrenceOwner p == processNetworkRoot network
               && processOccurrenceActivation p == NotActivated) population
    && all (\site -> any ((== processTargetInstance site) . identityInstanceKey . processOccurrenceTarget)
                  population) (candidateSites accepted)
  case candidateActivation accepted of
    [client, server] -> do
      let clientContract = resolvedComponentActivationContract client
          serverContract = resolvedComponentActivationContract server
          contracts = [clientContract, serverContract]
      assert "four bindings on the exact graph-derived keys" $
        map (length . activationContractBindings) contracts == [3, 1]
        && all (`Map.member` processNetworkPopulation network) (map activationContractProcess contracts)
        && activationContractProcess clientContract /= activationContractProcess serverContract
      case map resolvedComponentActivationProtocolEndpoints [client, server] of
        [[send], [receive]] -> assert "same nominal instance, distinct exact roles" $
          protocolEndpointInstance send == protocolEndpointInstance receive
          && protocolEndpointRole send == ProtocolRoleKey "Client"
          && protocolEndpointRole receive == ProtocolRoleKey "Server"
        _ -> fail "expected one endpoint per process"
    _ -> fail "expected two activation contracts"

  let unicodeSource = UTF8.encodeUtf8 "// é漢\n" <> source
      sourceDigestRow bytes = changeField 2 1 (const (sourceDigest bytes)) manifest
  reject "source byte substitution" SelectedOriginMismatch (examine (unicodeSource, manifest))
  reject "sidecar substitution" SelectedOriginMismatch (examine (source, revision 5 7))
  reject "stale source digest" OriginHeaderMismatch (selectForTest unicodeSource manifest)
  forM_ [(1, 2), (1, 3), (1, 4), (3, 1), (4, 1)] $ \(row, field) ->
    reject "foreign origin or grammar/offset coordinate" OriginHeaderMismatch
      (selectForTest source (changeField row field (const "foreign") manifest))
  reject "stale offsets after reprint" (DeclarationSiteMismatch "DoublePing")
    (selectForTest unicodeSource (sourceDigestRow unicodeSource))
  (unicodeManifest, unicodeCandidate) <- right (prepareTest unicodeSource)
  _ <- right (selectForTest unicodeSource unicodeManifest)
  assert "new test selection preserves semantic revisions for a comment" $
    candidateDeclarations accepted == candidateDeclarations unicodeCandidate
  reject "byte offsets in Unicode selection" (DeclarationSiteMismatch "DoublePing")
    (selectForTest unicodeSource (changeField 5 5 (const "9") unicodeManifest))

  forM_ (zip [5 .. 9] ["DoublePing", "ClientWorker", "ServerWorker", "LocalDoublePing", "main"]) $
    \(row, label) -> forM_ [7, 8] $ \field ->
      reject "exact source and stable key with stale I or D" (RevisionMismatch label)
        (selectForTest source (revision row field))
  reject "wrong kind" (DeclarationSiteMismatch "DoublePing")
    (selectForTest source (changeField 5 2 (const "component") manifest))
  reject "duplicate site ID" InvalidLineage
    (selectForTest source (changeField 5 3 (const "site:3cd1") manifest))
  reject "duplicate declaration key" InvalidLineage
    (selectForTest source (changeField 5 4 (const "decl:5d21799d-9609-4c0c-b4af-a599192d5bd9") manifest))
  reject "swapped declaration rows" (DeclarationSiteMismatch "ClientWorker")
    (selectForTest source (editRows (\rows -> take 6 rows ++ [rows !! 7, rows !! 6] ++ drop 8 rows) manifest))
  reject "extra row" InvalidSidecar (selectForTest source (manifest <> "bogus\n"))
  reject "missing row" InvalidSidecar (selectForTest source (editRows (take 14) manifest))
  forM_ [(10, "main"), (11, "client"), (12, "server"), (13, "client_run"), (14, "server_run")] $
    \(row, label) -> reject "foreign occurrence owner or target" (OccurrenceSiteMismatch label)
      (selectForTest source (changeField row (if row == 10 then 2 else 3) (const "foreign") manifest))
  reject "foreign child slot with stale composition revisions" (RevisionMismatch "LocalDoublePing")
    (selectForTest source (changeField 11 2 (const "slot:foreign") manifest))
  reject "foreign process site with stale composition revisions" (RevisionMismatch "LocalDoublePing")
    (selectForTest source (changeField 13 2 (const "process:foreign") manifest))
  reject "same protocol shape paired with foreign lineage key" (RevisionMismatch "ClientWorker")
    (selectForTest source (changeField 5 4 (const "decl:foreign") manifest))

  let altered old new err = do
        let bytes = sourceEdit old new
        assert "negative source really differs" (bytes /= source)
        reject (Text.unpack old) err (selectForTest bytes (sourceDigestRow bytes))
  altered "instantiate LocalDoublePing;" "instantiate Missing;" SelectedTargetMismatch
  altered "let middle = send" "let Bogus { slot = middle } = send" (ComponentPattern "ClientWorker" 1)
  altered "let done = send" "let Bogus { slot = done } = send" (ComponentPattern "ClientWorker" 2)
  altered "(middle, received1)" "(Bogus { slot = middle }, received1)" (ComponentPattern "ServerWorker" 1)
  altered "(done, received2)" "(done, received2, other)" (ComponentPattern "ServerWorker" 2)
  altered "receive U8 on middle" "receive U16 on middle"
    (ComponentBodyFailure "ServerWorker" ChainSecondReceiveAnnotationNotU8)
  altered "second : U8)" "second : U16)"
    (ComponentBodyFailure "ClientWorker" ChainSecondSendPayloadNotU8)
  altered "send second on middle" "send second on endpoint"
    (ComponentBodyFailure "ClientWorker" ChainSecondPredecessorMismatch)
  altered "close done;" "close middle;"
    (ComponentBodyFailure "ClientWorker" ChainTerminalCloseMismatch)
  altered "(x : U8)" "(x : U16)" ProtocolProfile
  altered "instantiate LocalDoublePing;" "instantiate LocalDoublePing;\nprogram other = instantiate LocalDoublePing;"
    DeclarationInventory
  forM_ [ ("  instance client = ClientWorker;\n", "  instance extra = ClientWorker;\n", "  instance client = ServerWorker;\n")
        , ("  process client_run = client;\n", "  process extra = client;\n", "  process client_run = server;\n")
        , ("  protocol ping = DoublePing;\n", "  protocol other = DoublePing;\n", "  protocol ping = Foreign;\n")
        , ("  role ping.Client = client;\n", "  role ping.Other = client;\n", "  role ping.Client = server;\n")
        , ("  entry first : U8;\n", "  entry extra : U8;\n", "  entry first : U16;\n")
        , ("  bind client.first = first;\n", "  bind server.extra = first;\n", "  bind client.first = second;\n")
        ] $ \(row, extra, mistargeted) ->
    forM_ ["", row <> row, row <> extra, mistargeted] $ \replacement ->
      altered row replacement ArchitectureInventory

  (renamedBytes, renamed) <- right $
    prepareTest (sourceEdit "middle" "renamed_middle")
  assert "local alpha rename preserves revision columns under a new test selection" $
    candidateDeclarations renamed == candidateDeclarations accepted
  _ <- right (selectForTest (sourceEdit "middle" "renamed_middle") renamedBytes)
  (changedManifest, changedBody) <- right $ prepareTest (sourceEdit "send second" "send first")
  let oldClient = candidateDeclarations accepted !! 1
      newClient = candidateDeclarations changedBody !! 1
  assert "different payload parameter preserves component I and changes D" $
    identityInterfaceRevision oldClient == identityInterfaceRevision newClient
    && identityDefinitionRevision oldClient /= identityDefinitionRevision newClient
  let newBody = sourceEdit "send second" "send first"
      oldD = ((Text.splitOn "\t" . (!! 6) . Text.lines . UTF8.decodeUtf8) manifest) !! 8
  reject "changed body under stale component definition" (RevisionMismatch "ClientWorker")
    (selectForTest newBody (changeField 6 8 (const oldD) changedManifest))
  putStrLn "FSEM-03 D0 conditional origin, semantic profiles, and adversarial controls passed."

assert :: String -> Bool -> IO ()
assert label condition = unless condition (fail label)

right :: Show a => Either a b -> IO b
right = either (fail . show) pure

reject :: String -> CandidateError -> Either CandidateError Candidate -> IO ()
reject label expected actual = case actual of
  Left err -> assert (label <> ": expected " <> show expected <> ", got " <> show err) (err == expected)
  Right _ -> fail (label <> ": unexpectedly produced a candidate")

replace :: Text -> Text -> Bytes.ByteString -> Bytes.ByteString
replace old new = UTF8.encodeUtf8 . Text.replace old new . UTF8.decodeUtf8

editRows :: ([Text] -> [Text]) -> Bytes.ByteString -> Bytes.ByteString
editRows edit = UTF8.encodeUtf8 . Text.unlines . edit . Text.lines . UTF8.decodeUtf8

changeField :: Int -> Int -> (Text -> Text) -> Bytes.ByteString -> Bytes.ByteString
changeField row field change = editRows (editAt row (Text.intercalate "\t" . editAt field change . Text.splitOn "\t"))
  where
    editAt index edit xs = case splitAt index xs of
      (before, value : after) -> before ++ edit value : after
      _ -> error "invalid control coordinate"
