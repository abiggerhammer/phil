#!/usr/bin/env python3
from pathlib import Path
import sys

path = Path("test/Phase1INT004PortableNegativeManifestMain.hs")
text = path.read_text()

if "data PortableSessionNode = PortableSessionNode" in text:
    print("INT-004 final frozen environment decoder already applied")
    sys.exit(0)


def replace_once(old: str, new: str) -> None:
    global text
    if old not in text:
        raise SystemExit(f"missing staging anchor: {old[:80]!r}")
    text = text.replace(old, new, 1)


def replace_between(start: str, end: str, new: str) -> None:
    global text
    i = text.find(start)
    if i < 0:
        raise SystemExit(f"missing staging start anchor: {start!r}")
    j = text.find(end, i)
    if j < 0:
        raise SystemExit(f"missing staging end anchor: {end!r}")
    text = text[:i] + new + text[j:]


replace_once(
    "import Phil.Surface.Phase0\n  ( FixtureExpectation (..)\n  , phase0EnvironmentFor\n  , phase0ExpectationFor\n  )",
    "import Phil.Surface.Phase0\n  ( FixtureExpectation (..)\n  , phase0ExpectationFor\n  )",
)

new_data = r'''data PortableSessionNode = PortableSessionNode
  { portableSessionNodeSessionId :: Text
  , portableSessionNodeId :: Text
  , portableSessionNodeIsRoot :: Text
  , portableSessionNodeKind :: Text
  , portableSessionNodeMessageName :: Text
  , portableSessionNodeMessageType :: Text
  , portableSessionNodeTerminalOutcome :: Text
  , portableSessionNodeNext :: Text
  }
  deriving (Eq, Show)

data PortableSessionBranch = PortableSessionBranch
  { portableSessionBranchSessionId :: Text
  , portableSessionBranchSourceNode :: Text
  , portableSessionBranchLabel :: Text
  , portableSessionBranchPayloadName :: Text
  , portableSessionBranchPayloadType :: Text
  , portableSessionBranchNext :: Text
  }
  deriving (Eq, Show)

data PortableTypeAlias = PortableTypeAlias
  { portableAliasProfileId :: Text
  , portableAliasName :: Text
  , portableAliasSessionId :: Text
  }
  deriving (Eq, Show)

'''
replace_once("manifestPath :: FilePath\n", new_data + "manifestPath :: FilePath\n")

new_paths = r'''environmentSessionNodesPath :: FilePath
environmentSessionNodesPath = "test/fixtures/phase1-negative/environment-session-nodes-v1.tsv"

environmentSessionBranchesPath :: FilePath
environmentSessionBranchesPath = "test/fixtures/phase1-negative/environment-session-branches-v1.tsv"

environmentTypeAliasesPath :: FilePath
environmentTypeAliasesPath = "test/fixtures/phase1-negative/environment-type-aliases-v1.tsv"

'''
replace_once("seedPortableProfiles :: Set Text\n", new_paths + "seedPortableProfiles :: Set Text\n")

sets_and_main = r'''seedPortableProfiles :: Set Text
seedPortableProfiles = Set.fromList
  [ "phase0.simple-receive"
  , "phase0.wrong-order"
  , "phase0.nonexhaustive-offer"
  , "phase0.legacy-raw"
  , "phase0.failure-reuse"
  , "phase0.common"
  , "phase0.incompatible-join"
  , "phase0.parsed-validation-bypass"
  , "phase0.unrelated-length"
  , "phase0.premature-acceptance"
  , "phase0.pending-commit"
  , "phase0.pending-drop"
  , "phase0.stale-policy"
  , "phase0.opaque-proof"
  , "phase0.label-proof"
  ]

seedPortableFixtures :: Set Text
seedPortableFixtures = Set.fromList
  [ "P1-NEG-P0-001"
  , "P1-NEG-P0-002"
  , "P1-NEG-P0-003"
  , "P1-NEG-P0-004"
  , "P1-NEG-P0-005"
  , "P1-NEG-P0-006"
  , "P1-NEG-P0-007"
  , "P1-NEG-P0-008"
  , "P1-NEG-P0-009"
  , "P1-NEG-P0-010"
  , "P1-NEG-P0-011"
  , "P1-NEG-P0-012"
  , "P1-NEG-P0-013"
  , "P1-NEG-P0-014"
  , "P1-NEG-P0-015"
  , "P1-NEG-P0-016"
  , "P1-NEG-P0-017"
  , "P1-NEG-P0-018"
  , "P1-NEG-P0-019"
  , "P1-NEG-P0-020"
  ]

main :: IO ()
main = do
  manifest <- TextIO.readFile manifestPath
  cases <- case parseManifest manifest of
    Left detail -> putStrLn ("FAIL: manifest -- " <> detail) >> exitFailure
    Right value -> pure value
  profileText <- TextIO.readFile environmentProfilesPath
  profiles <- case parseEnvironmentProfiles profileText of
    Left detail -> putStrLn ("FAIL: environment profiles -- " <> detail) >> exitFailure
    Right value -> pure value
  bindingText <- TextIO.readFile environmentBindingsPath
  bindings <- case parseEnvironmentBindings bindingText of
    Left detail -> putStrLn ("FAIL: environment bindings -- " <> detail) >> exitFailure
    Right value -> pure value
  requirementText <- TextIO.readFile environmentRequirementsPath
  requirements <- case parseEnvironmentRequirements requirementText of
    Left detail -> putStrLn ("FAIL: environment requirements -- " <> detail) >> exitFailure
    Right value -> pure value
  staticClaimText <- TextIO.readFile environmentStaticClaimsPath
  staticClaims <- case parsePortableStaticClaims staticClaimText of
    Left detail -> putStrLn ("FAIL: static claims -- " <> detail) >> exitFailure
    Right value -> pure value
  staticContext <- case materializePortableStaticContext staticClaims of
    Left detail -> putStrLn ("FAIL: static context -- " <> Text.unpack detail) >> exitFailure
    Right value -> pure value
  sessionNodeText <- TextIO.readFile environmentSessionNodesPath
  sessionNodes <- case parsePortableSessionNodes sessionNodeText of
    Left detail -> putStrLn ("FAIL: session nodes -- " <> detail) >> exitFailure
    Right value -> pure value
  sessionBranchText <- TextIO.readFile environmentSessionBranchesPath
  sessionBranches <- case parsePortableSessionBranches sessionBranchText of
    Left detail -> putStrLn ("FAIL: session branches -- " <> detail) >> exitFailure
    Right value -> pure value
  sessions <- case materializePortableSessions sessionNodes sessionBranches of
    Left detail -> putStrLn ("FAIL: portable sessions -- " <> Text.unpack detail) >> exitFailure
    Right value -> pure value
  aliasText <- TextIO.readFile environmentTypeAliasesPath
  typeAliases <- case parseEnvironmentTypeAliases aliasText of
    Left detail -> putStrLn ("FAIL: type aliases -- " <> detail) >> exitFailure
    Right value -> pure value
  integrityOk <- checkIntegrity staticClaims sessions typeAliases requirements bindings profiles cases
  results <- forM cases (replayCase staticContext sessions typeAliases requirements bindings profiles)
  unless (integrityOk && and results) exitFailure
  putStrLn ("PASS: INT-004 portable frozen negative manifest (" <> show (length cases) <> " fixtures)")

'''
replace_between("seedPortableProfiles :: Set Text\n", "parseManifest :: Text -> Either String [NegativeCase]\n", sets_and_main)

parser_insert = r'''parsePortableSessionNodes :: Text -> Either String (Map Text [PortableSessionNode])
parsePortableSessionNodes input = case Text.lines input of
  [] -> Left "empty portable session node file"
  header : rows
    | header /= Text.intercalate "\t"
        [ "session_id", "node_id", "is_root", "node_kind", "message_name"
        , "message_type", "terminal_outcome", "next_node"
        ] -> Left ("unexpected session node header: " <> Text.unpack header)
    | otherwise -> do
        parsed <- traverse parsePortableSessionNodeRow (filter (not . Text.null) rows)
        let grouped = Map.fromListWith (++)
              [(portableSessionNodeSessionId node, [node]) | node <- parsed]
            unique nodes =
              Set.size (Set.fromList (map portableSessionNodeId nodes)) == length nodes
        if all unique (Map.elems grouped)
          then Right grouped
          else Left "duplicate portable session node id within session"

parsePortableSessionNodeRow :: Text -> Either String PortableSessionNode
parsePortableSessionNodeRow row = case Text.splitOn "\t" row of
  [sessionId, nodeId, isRoot, nodeKind, messageName, messageType, terminalOutcome, nextNode]
    | any Text.null [sessionId, nodeId, isRoot, nodeKind, messageName, messageType, terminalOutcome, nextNode] ->
        Left ("empty portable session node field: " <> Text.unpack row)
    | otherwise -> Right PortableSessionNode
        { portableSessionNodeSessionId = sessionId
        , portableSessionNodeId = nodeId
        , portableSessionNodeIsRoot = isRoot
        , portableSessionNodeKind = nodeKind
        , portableSessionNodeMessageName = messageName
        , portableSessionNodeMessageType = messageType
        , portableSessionNodeTerminalOutcome = terminalOutcome
        , portableSessionNodeNext = nextNode
        }
  _ -> Left ("invalid portable session node TSV row: " <> Text.unpack row)

parsePortableSessionBranches :: Text -> Either String (Map Text [PortableSessionBranch])
parsePortableSessionBranches input = case Text.lines input of
  [] -> Left "empty portable session branch file"
  header : rows
    | header /= Text.intercalate "\t"
        [ "session_id", "source_node", "branch_label", "payload_name", "payload_type", "next_node" ] ->
        Left ("unexpected session branch header: " <> Text.unpack header)
    | otherwise -> do
        parsed <- traverse parsePortableSessionBranchRow (filter (not . Text.null) rows)
        let grouped = foldl
              (\acc branch -> Map.insertWith (flip (++))
                (portableSessionBranchSessionId branch) [branch] acc)
              Map.empty
              parsed
            unique branches =
              let keys = [(portableSessionBranchSourceNode branch, portableSessionBranchLabel branch) | branch <- branches]
              in Set.size (Set.fromList keys) == length keys
        if all unique (Map.elems grouped)
          then Right grouped
          else Left "duplicate portable session branch label at source node"

parsePortableSessionBranchRow :: Text -> Either String PortableSessionBranch
parsePortableSessionBranchRow row = case Text.splitOn "\t" row of
  [sessionId, sourceNode, branchLabel, payloadName, payloadType, nextNode]
    | any Text.null [sessionId, sourceNode, branchLabel, payloadName, payloadType, nextNode] ->
        Left ("empty portable session branch field: " <> Text.unpack row)
    | otherwise -> Right PortableSessionBranch
        { portableSessionBranchSessionId = sessionId
        , portableSessionBranchSourceNode = sourceNode
        , portableSessionBranchLabel = branchLabel
        , portableSessionBranchPayloadName = payloadName
        , portableSessionBranchPayloadType = payloadType
        , portableSessionBranchNext = nextNode
        }
  _ -> Left ("invalid portable session branch TSV row: " <> Text.unpack row)

parseEnvironmentTypeAliases :: Text -> Either String (Map Text [PortableTypeAlias])
parseEnvironmentTypeAliases input = case Text.lines input of
  [] -> Left "empty portable type alias file"
  header : rows
    | header /= Text.intercalate "\t" ["profile_id", "alias_name", "session_id"] ->
        Left ("unexpected type alias header: " <> Text.unpack header)
    | otherwise -> do
        parsed <- traverse parseEnvironmentTypeAliasRow (filter (not . Text.null) rows)
        let grouped = Map.fromListWith (++)
              [(portableAliasProfileId alias, [alias]) | alias <- parsed]
            unique aliases =
              Set.size (Set.fromList (map portableAliasName aliases)) == length aliases
        if all unique (Map.elems grouped)
          then Right grouped
          else Left "duplicate portable type alias within profile"

parseEnvironmentTypeAliasRow :: Text -> Either String PortableTypeAlias
parseEnvironmentTypeAliasRow row = case Text.splitOn "\t" row of
  [profileId, aliasName, sessionId]
    | any Text.null [profileId, aliasName, sessionId] ->
        Left ("empty portable type alias field: " <> Text.unpack row)
    | otherwise -> Right PortableTypeAlias
        { portableAliasProfileId = profileId
        , portableAliasName = aliasName
        , portableAliasSessionId = sessionId
        }
  _ -> Left ("invalid portable type alias TSV row: " <> Text.unpack row)

'''
replace_once("parseEnvironmentRow :: Text -> Either String PortableEnvironmentProfile\n", parser_insert + "parseEnvironmentRow :: Text -> Either String PortableEnvironmentProfile\n")

materialize_section = r'''materializePortableProfile
  :: StaticContext
  -> Map Text Session
  -> Map Text [PortableTypeAlias]
  -> Map Text [PortableEnvironmentRequirement]
  -> Map Text [PortableEnvironmentBinding]
  -> PortableEnvironmentProfile
  -> Either Text SurfaceEnvironment
materializePortableProfile staticContext sessions aliases requirements extraBindings profile = do
  bindings <- materializePortableBindings sessions extraBindings profile
  typeAliases <- materializePortableTypeAliases
    sessions
    (Map.findWithDefault [] (portableProfileId profile) aliases)
  primitives <- parsePrimitiveBindings (portablePrimitiveBindings profile)
  legacyReceiveFrameRaw <- parsePortableBool
    "legacy_receive_frame_raw"
    (portableLegacyReceiveFrameRaw profile)
  (receiveExactRequirement, selectRequirements) <- materializePortableRequirements
    (Map.findWithDefault [] (portableProfileId profile) requirements)
  pure (emptySurfaceEnvironment staticContext)
    { surfaceInitialBindings = bindings
    , surfacePrimitives = primitives
    , surfaceTypeAliases = typeAliases
    , surfaceLegacyReceiveFrameRaw = legacyReceiveFrameRaw
    , surfaceReceiveExactRequirement = receiveExactRequirement
    , surfaceSelectRequirements = selectRequirements
    }

materializePortableBindings
  :: Map Text Session
  -> Map Text [PortableEnvironmentBinding]
  -> PortableEnvironmentProfile
  -> Either Text (Map Text InitialBinding)
materializePortableBindings sessions extraBindings profile = do
  primary <- case portableSessionKind profile of
    "none" -> do
      requireDash "binding_name" (portableBindingName profile)
      requireDash "binding_mode" (portableBindingMode profile)
      requireDash "message_name" (portableMessageName profile)
      requireDash "message_type" (portableMessageType profile)
      requireDash "terminal_outcome" (portableTerminalOutcome profile)
      requireDash "branches" (portableBranches profile)
      Right Map.empty
    _ -> do
      bindingName <- requireValue "binding_name" (portableBindingName profile)
      mode <- parsePortableMode (portableBindingMode profile)
      session <- parsePortableSession profile
      let binding = InitialBinding mode (TyEndpoint session) PlainShape
      Right (Map.singleton bindingName binding)
  extras <- traverse (materializePortableExtraBinding sessions)
    (Map.findWithDefault [] (portableProfileId profile) extraBindings)
  let extrasMap = Map.fromList extras
  if Map.size extrasMap /= length extras
    then Left "duplicate materialized portable extra binding"
    else if not (Set.null (Map.keysSet primary `Set.intersection` Map.keysSet extrasMap))
      then Left "portable extra binding conflicts with primary binding"
      else Right (Map.union primary extrasMap)

materializePortableExtraBinding
  :: Map Text Session
  -> PortableEnvironmentBinding
  -> Either Text (Text, InitialBinding)
materializePortableExtraBinding sessions binding = do
  mode <- parsePortableMode (portableExtraBindingMode binding)
  ty <- parsePortableBindingType sessions (portableExtraBindingType binding)
  shape <- parsePortableBindingShape
    (portableExtraBindingName binding)
    ty
    (portableExtraBindingShape binding)
  Right
    ( portableExtraBindingName binding
    , InitialBinding mode ty shape
    )

parsePortableBindingType :: Map Text Session -> Text -> Either Text Ty
parsePortableBindingType sessions value
  | value == "bool" = Right TyBool
  | Just sessionId <- Text.stripPrefix "endpoint-session:" value
  , not (Text.null sessionId) = case Map.lookup sessionId sessions of
      Just session -> Right (TyEndpoint session)
      Nothing -> Left ("unknown portable endpoint session: " <> sessionId)
  | Just grammar <- Text.stripPrefix "frame:" value
  , not (Text.null grammar) = Right (TyFrame (GrammarId grammar))
  | Just rest <- Text.stripPrefix "validated:" value =
      case Text.splitOn ":" rest of
        [claim, context, subject]
          | all (not . Text.null) [claim, context, subject] ->
              Right (TyValidated claim (Name context) (Name subject))
        _ -> Left ("invalid portable validated binding type: " <> value)
  | Just rest <- Text.stripPrefix "opaque-sorted:" value =
      case Text.splitOn ":" rest of
        [name, sortEncoding] | not (Text.null name) ->
          TyOpaqueSorted name <$> parsePortableSort sortEncoding
        _ -> Left ("invalid portable sorted opaque binding type: " <> value)
  | otherwise = Left ("unsupported portable binding type: " <> value)

parsePortableSort :: Text -> Either Text RefSort
parsePortableSort value
  | value == "finite-seq-u8" = Right (SortFiniteSeq (SortUInt 8))
  | value == "finite-set-u16" = Right (SortFiniteSet (SortUInt 16))
  | Just name <- Text.stripPrefix "opaque-" value
  , not (Text.null name) = Right (SortOpaque name)
  | Just name <- Text.stripPrefix "stable-id-" value
  , not (Text.null name) = Right (SortStableId name)
  | otherwise = Left ("unsupported portable sort: " <> value)

materializePortableSessions
  :: Map Text [PortableSessionNode]
  -> Map Text [PortableSessionBranch]
  -> Either Text (Map Text Session)
materializePortableSessions nodesBySession branchesBySession
  | not (Map.keysSet branchesBySession `Set.isSubsetOf` Map.keysSet nodesBySession) =
      Left "portable session branch references undeclared session"
  | otherwise = Map.fromList <$> traverse materializeOne (Map.toList nodesBySession)
  where
    materializeOne (sessionId, nodes) = do
      let nodeMap = Map.fromList [(portableSessionNodeId node, node) | node <- nodes]
          branchRows = Map.findWithDefault [] sessionId branchesBySession
      rootFlags <- traverse
        (\node -> do
          flag <- parsePortableBool "is_root" (portableSessionNodeIsRoot node)
          Right (portableSessionNodeId node, flag))
        nodes
      rootId <- case [nodeId | (nodeId, True) <- rootFlags] of
        [nodeId] -> Right nodeId
        [] -> Left ("portable session has no root: " <> sessionId)
        _ -> Left ("portable session has multiple roots: " <> sessionId)
      _ <- traverse (validateBranchReference sessionId nodeMap) branchRows
      _ <- traverse (validateNodeReference sessionId nodeMap) nodes
      (session, visited) <- buildSession sessionId nodeMap branchRows Set.empty rootId
      if visited == Map.keysSet nodeMap
        then Right (sessionId, session)
        else Left ("portable session has unreachable nodes: " <> sessionId)

    validateBranchReference sessionId nodeMap branch = do
      source <- case Map.lookup (portableSessionBranchSourceNode branch) nodeMap of
        Nothing -> Left ("portable session branch has unknown source in " <> sessionId)
        Just node -> Right node
      if portableSessionNodeKind source `elem` ["offer", "select"]
        then Right ()
        else Left ("portable branch source is not offer/select in " <> sessionId)
      if Map.member (portableSessionBranchNext branch) nodeMap
        then Right ()
        else Left ("portable session branch has unknown target in " <> sessionId)

    validateNodeReference sessionId node = case portableSessionNodeKind node of
      "receive" ->
        if Map.member (portableSessionNodeNext node) nodeMap
          then Right ()
          else Left ("portable receive node has unknown target in " <> sessionId)
        where nodeMap = Map.fromList
                [(portableSessionNodeId candidate, candidate)
                | candidate <- Map.findWithDefault [] sessionId nodesBySession]
      "offer" -> Right ()
      "select" -> Right ()
      "end" -> Right ()
      other -> Left ("unsupported portable session node kind: " <> other)

    buildSession sessionId nodeMap branchRows visiting nodeId
      | Set.member nodeId visiting = Left ("portable session cycle is unsupported in " <> sessionId)
      | otherwise = case Map.lookup nodeId nodeMap of
          Nothing -> Left ("portable session references missing node in " <> sessionId <> ": " <> nodeId)
          Just node -> do
            let ownedBranches = filter
                  ((== nodeId) . portableSessionBranchSourceNode)
                  branchRows
                visitingNext = Set.insert nodeId visiting
            case portableSessionNodeKind node of
              "end" -> do
                requireDash "end message_name" (portableSessionNodeMessageName node)
                requireDash "end message_type" (portableSessionNodeMessageType node)
                requireDash "end next_node" (portableSessionNodeNext node)
                outcome <- requireValue "end terminal_outcome" (portableSessionNodeTerminalOutcome node)
                if null ownedBranches
                  then Right (End (Outcome outcome), Set.singleton nodeId)
                  else Left ("end node owns portable branches in " <> sessionId)
              "receive" -> do
                if null ownedBranches
                  then Right ()
                  else Left ("receive node owns portable branches in " <> sessionId)
                messageName <- requireValue "receive message_name" (portableSessionNodeMessageName node)
                messageType <- parsePortableType (portableSessionNodeMessageType node)
                requireDash "receive terminal_outcome" (portableSessionNodeTerminalOutcome node)
                nextNode <- requireValue "receive next_node" (portableSessionNodeNext node)
                (continuation, visited) <- buildSession sessionId nodeMap branchRows visitingNext nextNode
                Right
                  ( Receive (Name messageName) messageType continuation
                  , Set.insert nodeId visited
                  )
              kind | kind `elem` ["offer", "select"] -> do
                requireDash (kind <> " message_name") (portableSessionNodeMessageName node)
                requireDash (kind <> " message_type") (portableSessionNodeMessageType node)
                requireDash (kind <> " terminal_outcome") (portableSessionNodeTerminalOutcome node)
                requireDash (kind <> " next_node") (portableSessionNodeNext node)
                if null ownedBranches
                  then Left ("portable " <> kind <> " node has no branches in " <> sessionId)
                  else do
                    built <- traverse
                      (materializeBranch sessionId nodeMap branchRows visitingNext)
                      ownedBranches
                    let branches = map fst built
                        visited = Set.unions (Set.singleton nodeId : map snd built)
                        constructor = if kind == "offer" then Offer else Select
                    Right (constructor branches, visited)
              other -> Left ("unsupported portable session node kind: " <> other)

    materializeBranch sessionId nodeMap branchRows visiting branch = do
      label <- requireValue "session branch label" (portableSessionBranchLabel branch)
      payload <- case
          (portableSessionBranchPayloadName branch, portableSessionBranchPayloadType branch) of
        ("-", "-") -> Right Nothing
        (name, tyText)
          | name /= "-" && tyText /= "-" -> do
              ty <- parsePortableType tyText
              Right (Just (Name name, ty))
        _ -> Left ("portable session branch payload name/type must both be populated or '-' in " <> sessionId)
      nextNode <- requireValue "session branch next_node" (portableSessionBranchNext branch)
      (continuation, visited) <- buildSession sessionId nodeMap branchRows visiting nextNode
      Right (Branch label payload continuation, visited)

materializePortableTypeAliases
  :: Map Text Session
  -> [PortableTypeAlias]
  -> Either Text (Map Text Ty)
materializePortableTypeAliases sessions aliases = do
  pairs <- traverse materialize aliases
  let result = Map.fromList pairs
  if Map.size result == length pairs
    then Right result
    else Left "duplicate materialized portable type alias"
  where
    materialize alias = case Map.lookup (portableAliasSessionId alias) sessions of
      Nothing -> Left ("portable type alias references unknown session: " <> portableAliasSessionId alias)
      Just session -> Right (portableAliasName alias, TyEndpoint session)

'''
replace_between(
    "materializePortableProfile\n",
    "materializePortableStaticContext :: [PortableStaticClaim] -> Either Text StaticContext\n",
    materialize_section,
)

session_and_requirements = r'''parsePortableSession :: PortableEnvironmentProfile -> Either Text Session
parsePortableSession profile = case portableSessionKind profile of
  "receive" -> do
    messageName <- requireValue "message_name" (portableMessageName profile)
    messageType <- parsePortableType (portableMessageType profile)
    terminal <- requireValue "terminal_outcome" (portableTerminalOutcome profile)
    requireDash "branches" (portableBranches profile)
    pure (Receive (Name messageName) messageType (End (Outcome terminal)))
  "offer" -> do
    requireDash "message_name" (portableMessageName profile)
    requireDash "message_type" (portableMessageType profile)
    requireDash "terminal_outcome" (portableTerminalOutcome profile)
    branches <- parsePortableBranches (portableBranches profile)
    pure (Offer branches)
  "select" -> do
    requireDash "message_name" (portableMessageName profile)
    requireDash "message_type" (portableMessageType profile)
    requireDash "terminal_outcome" (portableTerminalOutcome profile)
    branches <- parsePortableBranches (portableBranches profile)
    pure (Select branches)
  other -> Left ("unknown portable session kind: " <> other)

parsePortableType :: Text -> Either Text Ty
parsePortableType value
  | Just name <- Text.stripPrefix "opaque:" value
  , not (Text.null name) = Right (TyOpaque name)
  | Just grammar <- Text.stripPrefix "frame:" value
  , not (Text.null grammar) = Right (TyFrame (GrammarId grammar))
  | Just amount <- Text.stripPrefix "bytes:nat:" value =
      TyBytes . RefNat <$> parsePortableNat amount
  | Just fieldSpec <- Text.stripPrefix "bytes:toNat-field:" value =
      case Text.splitOn ":" fieldSpec of
        [pathSpec, "u64"] -> case Text.splitOn "." pathSpec of
          [bindingName, fieldName]
            | all (not . Text.null) [bindingName, fieldName] ->
                Right (TyBytes (RefToNat (RefField
                  (RefVar (Name bindingName))
                  fieldName
                  (SortUInt 64))))
          _ -> Left ("invalid portable byte field path: " <> fieldSpec)
        _ -> Left ("invalid portable byte-index type: " <> value)
  | Just refined <- Text.stripPrefix "refined-member-field:" value =
      case Text.splitOn ":" refined of
        ["u16", binder, pathSpec, sortEncoding] -> case Text.splitOn "." pathSpec of
          [recordName, fieldName]
            | all (not . Text.null) [binder, recordName, fieldName, sortEncoding] -> do
                sortValue <- parsePortableSort sortEncoding
                Right (TyRefined
                  (Name binder)
                  (TyUInt 16)
                  (Member
                    (RefVar (Name binder))
                    (RefField (RefVar (Name recordName)) fieldName sortValue)))
          _ -> Left ("invalid portable refined field path: " <> refined)
        _ -> Left ("invalid portable refined member type: " <> value)
  | otherwise = Left ("unsupported portable message type: " <> value)

parsePortableBranches :: Text -> Either Text [Branch]
parsePortableBranches value
  | value == "-" = Left "offer session requires at least one branch"
  | otherwise = do
      branches <- traverse parseBranch (Text.splitOn ";" value)
      let labels = [label | Branch label _ _ <- branches]
      if Set.size (Set.fromList labels) /= length labels
        then Left "duplicate portable offer branch label"
        else Right branches
  where
    parseBranch branchText = case Text.splitOn ":" branchText of
      [label, outcome]
        | not (Text.null label) && not (Text.null outcome) ->
            Right (Branch label Nothing (End (Outcome outcome)))
      _ -> Left ("invalid portable offer branch: " <> branchText)

parsePrimitiveBindings :: Text -> Either Text (Map Text PrimitiveSemantics)
parsePrimitiveBindings value
  | value == "-" = Right Map.empty
  | otherwise = do
      bindings <- traverse parsePrimitive (Text.splitOn ";" value)
      let result = Map.fromList bindings
      if Map.size result /= length bindings
        then Left "duplicate portable primitive binding name"
        else Right result
  where
    parsePrimitive entry = case Text.splitOn ":" entry of
      [name, semantic] | not (Text.null name) ->
        case semantic of
          "handle-payload" -> Right (name, PrimitiveHandlePayload)
          "authorize-store" -> Right (name, PrimitiveAuthorizeStore)
          "delegate" -> Right (name, PrimitiveDelegate)
          "new-cancellation-scope" -> Right (name, PrimitiveNewCancellationScope)
          "allocate-linear-buffer" -> Right (name, PrimitiveAllocateLinearBuffer)
          "inspect" -> Right (name, PrimitiveInspect)
          "unchecked-u32-add" -> Right (name, PrimitiveUncheckedU32Add)
          "continue-common-state" -> Right (name, PrimitiveContinueCommonState)
          "store" -> Right (name, PrimitiveStore)
          "fixture-bytes" -> Right (name, PrimitiveFixtureBytes)
          "consume-begin-policy-evidence" -> Right (name, PrimitiveConsumeBeginPolicyEvidence)
          _ -> Left ("unsupported portable primitive semantic: " <> semantic)
      _ -> Left ("unsupported portable primitive binding: " <> entry)

materializePortableRequirements
  :: [PortableEnvironmentRequirement]
  -> Either Text (Maybe Proposition, Map Text [Proposition])
materializePortableRequirements requirements = do
  materialized <- traverse materializeRequirement requirements
  let receiveRequirements = [proposition | ("receive-exact", _, proposition) <- materialized]
      selectEntries = [(siteName, [proposition]) | ("select", siteName, proposition) <- materialized]
      selectMap = Map.fromList selectEntries
  if length receiveRequirements > 1
    then Left "duplicate portable receive-exact requirement"
    else if Map.size selectMap /= length selectEntries
      then Left "duplicate portable select requirement site"
      else Right
        ( case receiveRequirements of
            [] -> Nothing
            [proposition] -> Just proposition
            _ -> Nothing
        , selectMap
        )
  where
    materializeRequirement
      :: PortableEnvironmentRequirement
      -> Either Text (Text, Text, Proposition)
    materializeRequirement requirement = do
      proposition <- parsePortableProposition (portableRequirementProposition requirement)
      case portableRequirementSiteKind requirement of
        "receive-exact" -> do
          requireDash "receive-exact site_name" (portableRequirementSiteName requirement)
          Right ("receive-exact", "-", proposition)
        "select" -> do
          siteName <- requireValue "select site_name" (portableRequirementSiteName requirement)
          Right ("select", siteName, proposition)
        other -> Left ("unsupported portable requirement site kind: " <> other)

parsePortableProposition :: Text -> Either Text Proposition
parsePortableProposition value = case Text.stripPrefix "atom:" value of
  Nothing -> Left ("unsupported portable proposition: " <> value)
  Just body ->
    let (claim, argumentTextWithColon) = Text.breakOn ":" body
    in case Text.stripPrefix ":" argumentTextWithColon of
      Nothing -> Left ("portable atom requires arguments: " <> value)
      Just argumentText
        | Text.null claim || Text.null argumentText -> Left ("invalid portable atom: " <> value)
        | otherwise -> Atom claim <$> traverse parseArgument (Text.splitOn "," argumentText)
  where
    parseArgument argument = case Text.stripPrefix "var:" argument of
      Just name | not (Text.null name) -> Right (RefVar (Name name))
      _ -> case Text.stripPrefix "opaque:" argument of
        Just rest -> case Text.splitOn ":" rest of
          [sortEncoding, label]
            | not (Text.null sortEncoding) && not (Text.null label) -> do
                sortValue <- parsePortableSort sortEncoding
                Right (RefOpaque sortValue label)
          _ -> Left ("invalid portable opaque proposition argument: " <> argument)
        Nothing -> Left ("unsupported portable proposition argument: " <> argument)

'''
replace_between(
    "parsePortableSession :: PortableEnvironmentProfile -> Either Text Session\n",
    "requireValue :: Text -> Text -> Either Text Text\n",
    session_and_requirements,
)

resolve_integrity_replay = r'''resolveProfileEnvironment
  :: StaticContext
  -> Map Text Session
  -> Map Text [PortableTypeAlias]
  -> Map Text [PortableEnvironmentRequirement]
  -> Map Text [PortableEnvironmentBinding]
  -> Map Text PortableEnvironmentProfile
  -> Text
  -> Either Text SurfaceEnvironment
resolveProfileEnvironment staticContext sessions aliases requirements bindings profiles profile =
  case Map.lookup profile profiles of
    Just portable -> materializePortableProfile
      staticContext sessions aliases requirements bindings portable
    Nothing -> Left ("portable environment profile missing: " <> profile)

checkIntegrity
  :: [PortableStaticClaim]
  -> Map Text Session
  -> Map Text [PortableTypeAlias]
  -> Map Text [PortableEnvironmentRequirement]
  -> Map Text [PortableEnvironmentBinding]
  -> Map Text PortableEnvironmentProfile
  -> [NegativeCase]
  -> IO Bool
checkIntegrity staticClaims sessions aliases requirements bindings profiles cases = do
  let ids = map negativeCaseId cases
      paths = map negativeCasePath cases
      uniqueIds = Set.size (Set.fromList ids) == length ids
      uniquePaths = Set.size (Set.fromList paths) == length paths
      exactFrozenCount = length cases == 20
      layersExact = all ((== "surface-check") . negativeCaseLayer) cases
      authoritiesPresent = all ((== "INT-004") . negativeCaseAuthority) cases
      profilesNamed = all (Text.isPrefixOf "phase0." . negativeCaseEnvironmentProfile) cases
      seedProfileDomainExact = Map.keysSet profiles == seedPortableProfiles
      seedFixturesPortable = all
        (\negativeCase ->
          Set.member (negativeCaseId negativeCase) seedPortableFixtures
            && Map.member (negativeCaseEnvironmentProfile negativeCase) profiles)
        cases
      bindingProfilesDeclared = Map.keysSet bindings `Set.isSubsetOf` Map.keysSet profiles
      requirementProfilesDeclared = Map.keysSet requirements `Set.isSubsetOf` Map.keysSet profiles
      aliasProfilesDeclared = Map.keysSet aliases `Set.isSubsetOf` Map.keysSet profiles
      multibindingDomainExact = Map.keysSet bindings == Set.fromList
        [ "phase0.incompatible-join"
        , "phase0.parsed-validation-bypass"
        , "phase0.unrelated-length"
        , "phase0.premature-acceptance"
        , "phase0.pending-commit"
        , "phase0.pending-drop"
        , "phase0.stale-policy"
        , "phase0.opaque-proof"
        , "phase0.label-proof"
        ]
      requirementDomainExact = Map.keysSet requirements == Set.fromList
        [ "phase0.parsed-validation-bypass"
        , "phase0.premature-acceptance"
        , "phase0.stale-policy"
        ]
      sessionDomainExact = Map.keysSet sessions == Set.fromList
        [ "phase0.premature-acceptance"
        , "phase0.label-proof"
        , "phase0.server-upload"
        ]
      aliasDomainExact = Map.keysSet aliases == Set.fromList
        [ "phase0.pending-commit"
        , "phase0.pending-drop"
        ]
      staticClaimDomainExact = map portableStaticClaimName staticClaims == ["DigestMatches"]
      staticContextResult = materializePortableStaticContext staticClaims
      profilesResolve = case staticContextResult of
        Left _ -> False
        Right staticContext -> all
          (either (const False) (const True)
            . resolveProfileEnvironment staticContext sessions aliases requirements bindings profiles
            . negativeCaseEnvironmentProfile)
          cases
  filesPresent <- and <$> mapM doesFileExist paths
  report "20 frozen negative fixtures are manifest-owned" exactFrozenCount
  report "stable fixture IDs are unique" uniqueIds
  report "portable fixture paths are unique" uniquePaths
  report "every fixture names surface-check as competent layer" layersExact
  report "every fixture names its governing INT-004 matrix authority" authoritiesPresent
  report "every fixture names an explicit environment profile" profilesNamed
  report "portable environment set has exact frozen profile domain" seedProfileDomainExact
  report "portable extra bindings reference declared profiles" bindingProfilesDeclared
  report "portable requirements reference declared profiles" requirementProfilesDeclared
  report "portable aliases reference declared profiles" aliasProfilesDeclared
  report "portable extra-binding domain is exact for frozen corpus" multibindingDomainExact
  report "portable requirement domain is exact for frozen corpus" requirementDomainExact
  report "portable nested-session domain is exact for frozen corpus" sessionDomainExact
  report "portable type-alias domain is exact for frozen corpus" aliasDomainExact
  report "portable static claim domain is exact for frozen Phase 0" staticClaimDomainExact
  report "all 20 frozen fixtures use portable environment material" seedFixturesPortable
  report "every named environment profile resolves without compatibility fallback" profilesResolve
  report "every portable fixture path exists" filesPresent
  pure (and
    [ exactFrozenCount
    , uniqueIds
    , uniquePaths
    , layersExact
    , authoritiesPresent
    , profilesNamed
    , seedProfileDomainExact
    , bindingProfilesDeclared
    , requirementProfilesDeclared
    , aliasProfilesDeclared
    , multibindingDomainExact
    , requirementDomainExact
    , sessionDomainExact
    , aliasDomainExact
    , staticClaimDomainExact
    , seedFixturesPortable
    , profilesResolve
    , filesPresent
    ])

replayCase
  :: StaticContext
  -> Map Text Session
  -> Map Text [PortableTypeAlias]
  -> Map Text [PortableEnvironmentRequirement]
  -> Map Text [PortableEnvironmentBinding]
  -> Map Text PortableEnvironmentProfile
  -> NegativeCase
  -> IO Bool
replayCase staticContext sessions aliases requirements bindings profiles negativeCase = do
  source <- TextIO.readFile (negativeCasePath negativeCase)
  let path = negativeCasePath negativeCase
      expected = negativeCaseExpectedClass negativeCase
  parityOk <- case phase0ExpectationFor path of
    Just (FixtureReject legacyClass) -> do
      let ok = legacyClass == expected
      when (not ok) $ putStrLn
        ("FAIL: " <> Text.unpack (negativeCaseId negativeCase)
          <> " -- portable manifest disagrees with frozen legacy classification")
      pure ok
    _ -> putStrLn
      ("FAIL: " <> Text.unpack (negativeCaseId negativeCase)
        <> " -- frozen legacy fixture missing during migration") >> pure False
  case resolveProfileEnvironment
      staticContext sessions aliases requirements bindings profiles
      (negativeCaseEnvironmentProfile negativeCase) of
    Left detail -> failCase ("environment profile failed: " <> Text.unpack detail)
    Right environment -> case parseSurfaceFile (Text.pack path) source of
      Left diagnostic -> failCase
        ("rejected before recorded competent layer: syntax -- " <> show diagnostic)
      Right (SurfaceFile [component]) -> do
        checked <- timeout 2000000 $ evaluate (checkSurfaceComponent environment component)
        case checked of
          Nothing -> failCase "checker did not terminate"
          Just (Right _) -> failCase
            ("expected portable rejection class " <> show expected <> ", checker accepted")
          Just (Left errorValue)
            | surfaceErrorClass errorValue == expected -> do
                putStrLn ("PASS: " <> Text.unpack (negativeCaseId negativeCase)
                  <> " " <> path <> " @ surface-check")
                pure parityOk
            | otherwise -> failCase
                ("expected " <> show expected <> ", got "
                  <> show (surfaceErrorClass errorValue) <> ": "
                  <> Text.unpack (surfaceErrorDetail errorValue))
      Right (SurfaceFile components) -> failCase
        ("unexpected component count before competent layer: " <> show (length components))
  where
    failCase detail = putStrLn
      ("FAIL: " <> Text.unpack (negativeCaseId negativeCase)
        <> " " <> negativeCasePath negativeCase <> " -- " <> detail) >> pure False

'''
replace_between(
    "resolveProfileEnvironment\n",
    "report :: String -> Bool -> IO ()\n",
    resolve_integrity_replay,
)

path.write_text(text)
print("applied INT-004 final frozen environment decoder")
