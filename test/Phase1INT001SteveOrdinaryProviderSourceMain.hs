{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Compiler.SourceArchitecture
import Phil.Compiler.SourceBundle
import Phil.Compiler.SourceCorePolicy
import Phil.Core.Static
  ( DeclarationKey (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Ty (..)
  )
import Phil.Surface.Check
import Phil.Surface.Lineage
  ( DeclarationSiteId (..)
  , InstanceLineageSiteId (..)
  , PortableInstanceLineage (..)
  , PortableSourceBundle (..)
  , PortableSourceUnit (..)
  , SourceUnitId (..)
  , canonicalGrammarRevisionV1
  )
import System.Exit (exitFailure)

main :: IO ()
main = do
  putSource <- TextIO.readFile "examples/steve/put.phil"
  getSource <- TextIO.readFile "examples/steve/get.phil"
  results <- sequence
    [ test "ordinary Steve SourceBundle checks through shared front end"
        (ordinarySteveChecks putSource getSource)
    , test "Steve call occurrences stay generic and complete"
        (steveCallSitesAreExact putSource getSource)
    , test "Steve provider outcome branches retain exact labels"
        (steveBranchSitesAreExact putSource getSource)
    , test "undeclared provider operation fails at ordinary surface checking"
        (undeclaredProviderRejects putSource getSource)
    , test "provider outcome-label drift fails closed"
        (providerOutcomeDriftRejects putSource getSource)
    , test "provider consume discipline consumes restricted owner"
        providerConsumeDisciplineIsLinear
    , test "provider read discipline preserves owner across shared borrow"
        providerReadDisciplinePreservesOwner
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

ordinarySteveChecks :: Text -> Text -> Either String ()
ordinarySteveChecks putSource getSource = do
  checked <- checkedSteve putSource getSource steveEnvironments
  assert (length (checkedSourceUnits checked) == 2)
    "shared Steve SourceBundle did not retain both ordinary source units"

steveCallSitesAreExact :: Text -> Text -> Either String ()
steveCallSitesAreExact putSource getSource = do
  architecture <- checkedSteveArchitecture putSource getSource
  let expected = Map.fromList
        [ (SourceCoreSite "SteveGet" 0, "blob_read")
        , (SourceCoreSite "SteveGet" 1, "digest_check")
        , (SourceCoreSite "StevePut" 0, "digest_compute")
        , (SourceCoreSite "StevePut" 1, "blob_install")
        ]
  assert (sourceCoreCallSites architecture == expected)
    ("ordinary Steve call inventory drifted: " <> show (sourceCoreCallSites architecture))

steveBranchSitesAreExact :: Text -> Text -> Either String ()
steveBranchSitesAreExact putSource getSource = do
  architecture <- checkedSteveArchitecture putSource getSource
  let expected = Map.fromList
        [ (SourceCoreSite "SteveGet" 0,
            Set.fromList ["found", "not-found", "storage-failure"])
        , (SourceCoreSite "SteveGet" 1,
            Set.fromList ["accepted", "rejected"])
        , (SourceCoreSite "StevePut" 0,
            Set.singleton "computed")
        , (SourceCoreSite "StevePut" 1,
            Set.fromList ["installed", "already-exists", "storage-failure"])
        ]
  assert (sourceCoreBranchSites architecture == expected)
    ("ordinary Steve branch inventory drifted: " <> show (sourceCoreBranchSites architecture))

undeclaredProviderRejects :: Text -> Text -> Either String ()
undeclaredProviderRejects putSource getSource =
  let brokenPut = putEnvironment
        { surfacePrimitives = Map.delete "digest_compute" (surfacePrimitives putEnvironment) }
      environments = Map.insert putDeclaration brokenPut steveEnvironments
  in case checkPortableSourceBundle steveRoots environments (steveBundle putSource getSource) of
      Left (SourceBundleSurfaceCheckError _ _ SurfaceCheckError
        { surfaceErrorClass = UnknownPrimitive }) -> Right ()
      other -> Left ("undeclared provider call did not reject as UnknownPrimitive: " <> show other)

providerOutcomeDriftRejects :: Text -> Text -> Either String ()
providerOutcomeDriftRejects putSource getSource =
  let driftedGet = Text.replace "not-found =>" "not_found =>" getSource
  in case checkPortableSourceBundle steveRoots steveEnvironments (steveBundle putSource driftedGet) of
      Left (SourceBundleSurfaceCheckError _ _ SurfaceCheckError
        { surfaceErrorClass = BranchExhaustiveness }) -> Right ()
      other -> Left ("provider branch-label drift crossed checking: " <> show other)

providerConsumeDisciplineIsLinear :: Either String ()
providerConsumeDisciplineIsLinear =
  let source = "component ConsumeProbe provides Unit { blob_install(contentId, candidate) release candidate return unit }"
  in case checkPortableSourceBundle
      (Map.singleton "program:probe" probeDeclaration)
      (Map.singleton probeDeclaration putProbeEnvironment)
      (probeBundle source) of
      Left (SourceBundleSurfaceCheckError _ _ SurfaceCheckError
        { surfaceErrorClass = StructuralUse }) -> Right ()
      other -> Left ("consumed provider owner remained usable: " <> show other)

providerReadDisciplinePreservesOwner :: Either String ()
providerReadDisciplinePreservesOwner = do
  let source = Text.unwords
        [ "component ReadProbe provides Unit {"
        , "let digestDecision = borrow candidate as digestView { digest_compute(digestView) }"
        , "release candidate"
        , "return unit"
        , "}"
        ]
  _ <- mapLeft show $ checkPortableSourceBundle
    (Map.singleton "program:probe" probeDeclaration)
    (Map.singleton probeDeclaration readProbeEnvironment)
    (probeBundle source)
  Right ()

checkedSteveArchitecture :: Text -> Text -> Either String CheckedSourceArchitecture
checkedSteveArchitecture putSource getSource = do
  checked <- checkedSteve putSource getSource steveEnvironments
  mapLeft show $ buildCheckedSourceArchitecture
    (Map.singleton "program:steve" (InstanceLineageSiteId "instance.steve"))
    checked

checkedSteve
  :: Text
  -> Text
  -> SourceEnvironmentMap
  -> Either String CheckedSourceBundle
checkedSteve putSource getSource environments =
  mapLeft show $ checkPortableSourceBundle
    steveRoots environments (steveBundle putSource getSource)

steveBundle :: Text -> Text -> PortableSourceBundle
steveBundle putSource getSource = PortableSourceBundle
  { portableGrammarRevision = canonicalGrammarRevisionV1
  , portableSelectedProgramRoot = "program:steve"
  , portableSourceUnits =
      [ PortableSourceUnit
          (SourceUnitId "unit.steve.put")
          (DeclarationSiteId "site.steve.put")
          (Just "decl:steve.put")
          putSource
      , PortableSourceUnit
          (SourceUnitId "unit.steve.get")
          (DeclarationSiteId "site.steve.get")
          (Just "decl:steve.get")
          getSource
      ]
  , portableInstanceLineage =
      [ PortableInstanceLineage
          (InstanceLineageSiteId "instance.steve")
          "inst:phase1.steve"
      ]
  , portableProcessLineage = []
  }

probeBundle :: Text -> PortableSourceBundle
probeBundle source = PortableSourceBundle
  { portableGrammarRevision = canonicalGrammarRevisionV1
  , portableSelectedProgramRoot = "program:probe"
  , portableSourceUnits =
      [ PortableSourceUnit
          (SourceUnitId "unit.probe")
          (DeclarationSiteId "site.probe")
          (Just "decl:probe")
          source
      ]
  , portableInstanceLineage = []
  , portableProcessLineage = []
  }

steveRoots :: SourceRootMap
steveRoots = Map.singleton "program:steve" putDeclaration

steveEnvironments :: SourceEnvironmentMap
steveEnvironments = Map.fromList
  [ (putDeclaration, putEnvironment)
  , (getDeclaration, getEnvironment)
  ]

putDeclaration, getDeclaration, probeDeclaration :: DeclarationKey
putDeclaration = DeclarationKey "decl:steve.put"
getDeclaration = DeclarationKey "decl:steve.get"
probeDeclaration = DeclarationKey "decl:probe"

putEnvironment :: SurfaceEnvironment
putEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceInitialBindings = Map.singleton "candidate"
      (InitialBinding Linear ownedBytesType PlainShape)
  , surfacePrimitives = Map.fromList
      [ ("digest_compute", digestComputePrimitive)
      , ("blob_install", blobInstallPrimitive)
      ]
  , surfaceExpectedProvides = Just TyUnit
  }

getEnvironment :: SurfaceEnvironment
getEnvironment = (emptySurfaceEnvironment emptyStaticContext)
  { surfaceInitialBindings = Map.singleton "contentId"
      (InitialBinding Unrestricted contentIdType PlainShape)
  , surfacePrimitives = Map.fromList
      [ ("blob_read", blobReadPrimitive)
      , ("digest_check", digestCheckPrimitive)
      ]
  , surfaceExpectedProvides = Just TyUnit
  , surfaceReleaseTransitions = [ownedBytesRelease]
  }

putProbeEnvironment :: SurfaceEnvironment
putProbeEnvironment = putEnvironment
  { surfaceInitialBindings = Map.fromList
      [ ("candidate", InitialBinding Linear ownedBytesType PlainShape)
      , ("contentId", InitialBinding Unrestricted contentIdType PlainShape)
      ]
  , surfacePrimitives = Map.singleton "blob_install" blobInstallPrimitive
  , surfaceReleaseTransitions = [ownedBytesRelease]
  }

readProbeEnvironment :: SurfaceEnvironment
readProbeEnvironment = putEnvironment
  { surfacePrimitives = Map.singleton "digest_compute" digestComputePrimitive
  , surfaceReleaseTransitions = [ownedBytesRelease]
  }

digestComputePrimitive :: PrimitiveSemantics
digestComputePrimitive = PrimitiveProviderDecision
  [PrimitiveReadOnly]
  [ProviderOutcomeSpec "computed" [(Unrestricted, contentIdType)]]

blobInstallPrimitive :: PrimitiveSemantics
blobInstallPrimitive = PrimitiveProviderDecision
  [PrimitiveReadOnly, PrimitiveConsume]
  [ ProviderOutcomeSpec "installed" []
  , ProviderOutcomeSpec "already-exists" []
  , ProviderOutcomeSpec "storage-failure" [(Unrestricted, storageFailureType)]
  ]

blobReadPrimitive :: PrimitiveSemantics
blobReadPrimitive = PrimitiveProviderDecision
  [PrimitiveReadOnly]
  [ ProviderOutcomeSpec "found" [(Linear, ownedBytesType)]
  , ProviderOutcomeSpec "not-found" []
  , ProviderOutcomeSpec "storage-failure" [(Unrestricted, storageFailureType)]
  ]

digestCheckPrimitive :: PrimitiveSemantics
digestCheckPrimitive = PrimitiveProviderDecision
  [PrimitiveReadOnly, PrimitiveReadOnly]
  [ ProviderOutcomeSpec "accepted" []
  , ProviderOutcomeSpec "rejected" [(Unrestricted, digestFailureType)]
  ]

ownedBytesType, contentIdType, storageFailureType, digestFailureType :: Ty
ownedBytesType = TyOpaque "OwnedBytes"
contentIdType = TyOpaque "ContentId[SHA256]"
storageFailureType = TyOpaque "StorageFailure"
digestFailureType = TyOpaque "DigestFailure"

ownedBytesRelease :: ReleaseTransitionContract
ownedBytesRelease = ReleaseTransitionContract
  { releaseTransitionKey = "provider.owned-bytes.release"
  , releaseTransitionOwnerType = ownedBytesType
  , releaseTransitionRequirements = Set.empty
  , releaseTransitionSemanticAccount = ReleaseSemanticAccount
      { releaseAccountAuthorityRefs = Set.empty
      , releaseAccountEvidenceRefs = Set.empty
      , releaseAccountEffectRefs = Set.empty
      , releaseAccountAssumptionRefs = Set.empty
      , releaseAccountCostRefs = Set.empty
      , releaseAccountSubjectRef = "owned-bytes"
      }
  , releaseTransitionOutcome = ReleaseContinuesUnit
  , releaseTransitionResidue = ReleaseConsumesOwner
  }

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
