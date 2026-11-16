#!/usr/bin/env python3
"""Generate an H5 temporary Haskell probe from the real INT-001 witness."""
from pathlib import Path

source = Path("test/Phase1INT001WitnessE2EMain.hs").read_text()
changes = [
    (
        "import qualified Data.Map.Strict as Map\n",
        "import qualified Data.Map.Strict as Map\n"
        "import qualified Data.Map.Internal as MapInternal\n",
    ),
    (
        "import qualified Data.Set as Set\n",
        "import qualified Data.Set as Set\n"
        "import qualified Data.Set.Internal as SetInternal\n",
    ),
    (
        "  ( CoreSystemsProgram (..)\n",
        "  ( CoreSystemsProgram (..)\n"
        "  , CoreSystemsFunction (..)\n"
        "  , CoreSystemsBlock (..)\n"
        "  , CoreSystemsTerminator (..)\n",
    ),
    (
        "  results <- sequence\n",
        "  p8H5Probe uploadClient uploadServer stevePut steveGet\n"
        "  results <- sequence\n",
    ),
]
for before, after in changes:
    count = source.count(before)
    if count != 1:
        raise SystemExit(f"Fixture drift: {before!r} occurs {count} times")
    source = source.replace(before, after, 1)

probe = r'''
-- These internal constructors are used ONLY in this ephemeral native test,
-- not in Phil production. Damage the root cached size without changing keys,
-- values, sorted enumeration, binary search paths, or tree layout.
p8H5CorruptMap :: Map.Map k a -> Map.Map k a
p8H5CorruptMap root = case root of
  MapInternal.Tip -> root
  MapInternal.Bin n k v left right ->
    MapInternal.Bin (n + 1) k v left right

p8H5CorruptSet :: Set.Set a -> Set.Set a
p8H5CorruptSet root = case root of
  SetInternal.Tip -> root
  SetInternal.Bin n value left right ->
    SetInternal.Bin (n + 1) value left right

p8H5MapWitness
  :: (Ord k, Eq a) => String -> Map.Map k a -> Map.Map k a -> IO ()
p8H5MapWitness label original bad = do
  let proper = Map.valid original
      invalid = not (Map.valid bad)
      sameEntries = Map.toAscList original == Map.toAscList bad
      sameLookups = all (\(k,v) -> Map.lookup k bad == Just v)
        (Map.toAscList original)
  putStrLn ("H5_" <> label <> "_TREE_VALID " <> show (Map.valid bad))
  putStrLn ("H5_" <> label <> "_SAME_ENTRIES " <> show sameEntries)
  putStrLn ("H5_" <> label <> "_SAME_LOOKUPS " <> show sameLookups)
  if proper && invalid && sameEntries && sameLookups
    then pure ()
    else fail ("H5 bad Map did not preserve the full original lookup domain: " <> label)

p8H5SetWitness :: Ord a => String -> Set.Set a -> Set.Set a -> IO ()
p8H5SetWitness label original bad = do
  let proper = Set.valid original
      invalid = not (Set.valid bad)
      sameEntries = Set.toAscList original == Set.toAscList bad
      sameLookups = all (\k -> Set.member k bad) (Set.toAscList original)
  putStrLn ("H5_" <> label <> "_TREE_VALID " <> show (Set.valid bad))
  putStrLn ("H5_" <> label <> "_SAME_ENTRIES " <> show sameEntries)
  putStrLn ("H5_" <> label <> "_SAME_LOOKUPS " <> show sameLookups)
  if proper && invalid && sameEntries && sameLookups
    then pure ()
    else fail ("H5 bad Set did not preserve the full original lookup domain: " <> label)

p8H5UploadP2
  :: Text -> Text -> CoreSystemsProgram -> GenericRealizationContext
  -> Either String VerifiedSourceSystemsProduction
p8H5UploadP2 clientSource serverSource program context = do
  clientEnvironment <- mapLeft show (phase0EnvironmentFor "client.phil")
  serverEnvironment <- mapLeft show (phase0EnvironmentFor "server.phil")
  mapLeft show (produceVerifiedSourceSystems
    uploadRoots
    (Map.fromList
      [ (uploadClientDeclaration, clientEnvironment)
      , (uploadServerDeclaration, serverEnvironment) ])
    (Map.singleton "program:upload"
      (InstanceLineageSiteId "instance.upload"))
    uploadPolicy (uploadBundle clientSource serverSource)
    program context)

p8H5SteveP2
  :: Text -> Text -> CoreSystemsProgram -> GenericRealizationContext
  -> Either String VerifiedSourceSystemsProduction
p8H5SteveP2 putSource getSource program context =
  mapLeft show (produceVerifiedSourceSystems
    steveRoots steveEnvironments
    (Map.singleton "program:steve"
      (InstanceLineageSiteId "instance.steve"))
    stevePolicy (steveBundle putSource getSource)
    program context)

-- Stop at the first real rejection gate. Existing makeP7Fixture builds the
-- complete checked manifest/assurance and reconstructs P6 from the same
-- sealed P2 value and original template; it does NOT prove P10 release.
p8H5Report
  :: String
  -> Either String VerifiedSourceSystemsProduction
  -> Either String VerifiedSourceSystemsProduction
  -> ProviderCallExpectationMap
  -> Either String StageClosureBundle
  -> IO ()
p8H5Report label control bad expectations templateResult =
  case control of
    Left err -> putStrLn
      ("H5_" <> label <> "_VALID_CONTROL_P2_LEFT " <> take 800 err)
    Right _ -> do
      putStrLn ("H5_" <> label <> "_VALID_CONTROL_P2_RIGHT")
      case bad of
        Left err -> putStrLn
          ("H5_" <> label <> "_BAD_P2_LEFT " <> take 800 err)
        Right production -> do
          putStrLn ("H5_" <> label <> "_BAD_P2_RIGHT")
          case templateResult of
            Left err -> putStrLn
              ("H5_" <> label <> "_P6_TEMPLATE_LEFT " <> take 800 err)
            Right template ->
              case produceVerifiedStageClosure production expectations template of
                Left err -> putStrLn
                  ("H5_" <> label <> "_BAD_P6_LEFT " <> take 800 (show err))
                Right _stage -> do
                  putStrLn ("H5_" <> label <> "_BAD_P6_RIGHT")
                  case makeP7Fixture production expectations template of
                    Left err -> putStrLn
                      ("H5_" <> label <> "_BAD_P7_FIXTURE_LEFT " <> take 800 err)
                    Right fixture ->
                      case p7AcceptsExact fixture of
                        Left err -> putStrLn
                          ("H5_" <> label <> "_BAD_P7_ACCEPT_LEFT " <> take 800 err)
                        Right () -> putStrLn
                          ("H5_" <> label <> "_BAD_P7_ACCEPT_RIGHT (native only)")

p8H5Probe :: Text -> Text -> Text -> Text -> IO ()
p8H5Probe clientSource serverSource putSource getSource = do
  let ctx = uploadRealizationContext
      program = uploadCoreProgram
      uploadP2 p c = p8H5UploadP2 clientSource serverSource p c
      uploadReport label goodP goodCtx badP badCtx =
        p8H5Report label (uploadP2 goodP goodCtx) (uploadP2 badP badCtx)
          uploadProviderCallExpectations uploadStageClosureBundle

      originalDecisions = genericContextDecisions ctx
      badDecisions = p8H5CorruptMap originalDecisions
      originalSites = genericContextRuntimeSites ctx
      badSites = p8H5CorruptMap originalSites
      originalRefs = genericContextRealizationRefs ctx
      badRefs = p8H5CorruptSet originalRefs
      qualifiedCtx = ctx
        { genericContextQualificationRefs =
            Set.singleton "h5.qualification.control" }
      badQualified = p8H5CorruptSet
        (genericContextQualificationRefs qualifiedCtx)
      assumedCtx = ctx
        { genericContextAssumptions =
            Set.singleton "h5.assumption.control" }
      badAssumed = p8H5CorruptSet (genericContextAssumptions assumedCtx)

      originalFacts = coreProgramFacts program
      badFacts = p8H5CorruptMap originalFacts
      originalFunctions = coreProgramFunctions program
      badFunctions = p8H5CorruptMap originalFunctions
      client = originalFunctions Map.! "UploadClient"
      originalValues = coreFunctionValues client
      badValues = p8H5CorruptMap originalValues
      originalBlocks = coreFunctionBlocks client
      badBlocks = p8H5CorruptMap originalBlocks

  p8H5MapWitness "CTX_DECISIONS" originalDecisions badDecisions
  uploadReport "CTX_DECISIONS" program ctx program
    (ctx { genericContextDecisions = badDecisions })

  p8H5MapWitness "CTX_RUNTIME_SITES" originalSites badSites
  uploadReport "CTX_RUNTIME_SITES" program ctx program
    (ctx { genericContextRuntimeSites = badSites })

  p8H5SetWitness "CTX_REALIZATION_REFS" originalRefs badRefs
  uploadReport "CTX_REALIZATION_REFS" program ctx program
    (ctx { genericContextRealizationRefs = badRefs })

  p8H5SetWitness "CTX_QUALIFICATION_REFS"
    (genericContextQualificationRefs qualifiedCtx) badQualified
  uploadReport "CTX_QUALIFICATION_REFS" program qualifiedCtx program
    (qualifiedCtx { genericContextQualificationRefs = badQualified })

  p8H5SetWitness "CTX_ASSUMPTIONS"
    (genericContextAssumptions assumedCtx) badAssumed
  uploadReport "CTX_ASSUMPTIONS" program assumedCtx program
    (assumedCtx { genericContextAssumptions = badAssumed })

  p8H5MapWitness "CORE_FACTS" originalFacts badFacts
  uploadReport "CORE_FACTS" program ctx
    (program { coreProgramFacts = badFacts }) ctx

  p8H5MapWitness "CORE_FUNCTIONS" originalFunctions badFunctions
  uploadReport "CORE_FUNCTIONS" program ctx
    (program { coreProgramFunctions = badFunctions }) ctx

  p8H5MapWitness "CORE_VALUES" originalValues badValues
  let changedValues = client { coreFunctionValues = badValues }
      withBadValues = program { coreProgramFunctions =
        Map.insert "UploadClient" changedValues originalFunctions }
  uploadReport "CORE_VALUES" program ctx withBadValues ctx

  p8H5MapWitness "CORE_BLOCKS" originalBlocks badBlocks
  let changedBlocks = client { coreFunctionBlocks = badBlocks }
      withBadBlocks = program { coreProgramFunctions =
        Map.insert "UploadClient" changedBlocks originalFunctions }
  uploadReport "CORE_BLOCKS" program ctx withBadBlocks ctx

  -- Steve has an actual RuntimeChoice arm Map with several entries.
  case steveQualifiedRealizationContext of
    Left err -> putStrLn ("H5_STEVE_CONTEXT_LEFT " <> take 800 err)
    Right steveCtx -> do
      let steveProgram = steveCoreProgram
          steveFunctions = coreProgramFunctions steveProgram
          putFunction = steveFunctions Map.! "StevePut"
          putBlocks = coreFunctionBlocks putFunction
          installBlock = putBlocks Map.! "put.install"
      case coreBlockTerminator installBlock of
        CoreSystemsRuntimeChoice name inputs site arms -> do
          let badArms = p8H5CorruptMap arms
          p8H5MapWitness "CORE_RUNTIME_CHOICE_ARMS" arms badArms
          let changedInstall = installBlock
                { coreBlockTerminator =
                    CoreSystemsRuntimeChoice name inputs site badArms }
              changedPut = putFunction { coreFunctionBlocks =
                Map.insert "put.install" changedInstall putBlocks }
              changedSteve = steveProgram { coreProgramFunctions =
                Map.insert "StevePut" changedPut steveFunctions }
              steveP2 p = p8H5SteveP2 putSource getSource p steveCtx
          p8H5Report "CORE_RUNTIME_CHOICE_ARMS"
            (steveP2 steveProgram) (steveP2 changedSteve)
            steveProviderCallExpectations steveStageClosureBundle
        _ -> fail "H5 fixture drift: Steve put.install not RuntimeChoice"
'''
destination = Path("/tmp/PhilP8H5NativeMain.hs")
destination.write_text(source + "\n" + probe)
print(f"H5 generated {destination}; original tests remain unchanged")
