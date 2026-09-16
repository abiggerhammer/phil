{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Phil.Assurance.Phase0
  ( phase0UploadLedger
  , phase0UploadManifest
  , phase0UploadVerificationContext
  )
import Phil.Assurance.Types
import Phil.Assurance.Verify (verifyManifest)
import Phil.Compiler.SourceArchitecture
import Phil.Compiler.SourceBundle
import Phil.Core.Static
  ( ArchitectureInstanceIdentity (..)
  , CheckedArchitectureInstance (..)
  , DeclarationDescriptor (..)
  , DeclarationIdentity (..)
  , DeclarationKey (..)
  , DeclarationPresentation (..)
  , DefinitionRevision (..)
  , InstanceKey (..)
  , InstanceRevision (..)
  , InterfaceRevision (..)
  , canonicalSemanticForm
  , deriveDeclarationIdentity
  )
import Phil.Examples.Phase1.SystemsWitnesses
  ( uploadCoreProgram
  , uploadPhase1StageBundle
  )
import Phil.Surface.Lineage
  ( DeclarationSiteId (..)
  , InstanceLineageSiteId (..)
  , PortableInstanceLineage (..)
  , PortableSourceBundle (..)
  , PortableSourceUnit (..)
  , SourceUnitId (..)
  , canonicalGrammarRevisionV1
  )
import Phil.Surface.Phase0 (phase0EnvironmentFor)
import Phil.Surface.Syntax (Located (..))
import Phil.Systems.GenericLowering (coreSystemsProgramSemanticForm)
import Phil.Systems.IR
  ( loweringLedgerRoot
  , systemsArtifactDigest
  , systemsArtifactLoweringLedger
  )
import Phil.Systems.Phase1Stage
  ( phase1StageSystemsArtifact
  , verifyPhase1StageBundle
  )
import Phil.Verification
import Phil.Verification.Bundle
import Phil.Verification.ManifestClosure
import System.Exit (exitFailure)

main :: IO ()
main = do
  clientSource <- TextIO.readFile "examples/upload/client.phil"
  serverSource <- TextIO.readFile "examples/upload/server.phil"
  results <- sequence
    [ test "INT-002 ordinary Upload source closes a real manifest through the generic path"
        (uploadManifestCloses clientSource serverSource)
    , test "INT-002 Upload manifest architecture is bound to the VerificationBundle"
        (architectureSubstitutionRejected clientSource serverSource)
    , test "INT-002 exact ledger revisions form a canonical checked verification graph"
        revisionGraphRejectsIdentityDrift
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

uploadManifestCloses :: Text -> Text -> Either String ()
uploadManifestCloses clientSource serverSource = do
  (bundle, context, selection) <- uploadClosureFixture clientSource serverSource
  manifest <- mapLeft show $ closeVerificationBundle
    bundle uploadAssurancePolicy context phase0UploadLedger selection
  mapLeft show (verifyManifest context phase0UploadLedger manifest)
  assert
    (manifestArchitectureDigest manifest == verificationBundleArchitectureDigest bundle)
    "accepted Upload manifest is not bound to the ordinary-source Architecture identity"
  assert
    (manifestObligationRevisions manifest == Map.keysSet
      (verificationGraphNodes (verificationBundleObligationGraph bundle)))
    "accepted Upload manifest changed the VerificationBundle obligation domain"
  assert
    (manifestEvidenceEntries manifest == manifestClosureEvidence selection)
    "accepted Upload manifest changed the explicit evidence selection"
  assert
    (manifestAssumptionNodes manifest == manifestClosureAssumptions selection)
    "accepted Upload manifest hid or invented assumption nodes"
  assert
    (manifestExports manifest == Map.keysSet (manifestClosureExports selection))
    "accepted Upload manifest hid or invented exports"

architectureSubstitutionRejected :: Text -> Text -> Either String ()
architectureSubstitutionRejected clientSource serverSource = do
  (bundle, context, selection) <- uploadClosureFixture clientSource serverSource
  let badContext = context
        { verificationArchitectureDigest = digestText "unrelated-architecture" }
      expected = verificationBundleArchitectureDigest bundle
      actual = verificationArchitectureDigest badContext
  case closeVerificationBundle
      bundle uploadAssurancePolicy badContext phase0UploadLedger selection of
    Left (ManifestClosureArchitectureDigestMismatch expected' actual')
      | expected' == expected && actual' == actual -> Right ()
    other -> Left ("expected architecture-substitution rejection, got " <> show other)

revisionGraphRejectsIdentityDrift :: Either String ()
revisionGraphRejectsIdentityDrift =
  case Map.elems (ledgerRevisions phase0UploadLedger) of
    [] -> Left "Phase 0 Upload assurance ledger unexpectedly has no revisions"
    revision : rest ->
      let tampered = revision
            { revisionStatement = revisionStatement revision <> " [tampered]" }
          scope = manifestCertificationScope phase0UploadManifest
      in case buildVerificationRevisionGraph (tampered : rest) scope of
          Left (InvalidObligationRevisionIdentity _ actual)
            | actual == revisionId revision -> Right ()
          other -> Left ("expected exact revision-identity rejection, got " <> show other)

uploadClosureFixture
  :: Text
  -> Text
  -> Either String (VerificationBundle, VerificationContext, ManifestClosureSelection)
uploadClosureFixture clientSource serverSource = do
  architecture <- checkedUploadArchitecture clientSource serverSource
  mapLeft show (verifyPhase1StageBundle uploadPhase1StageBundle)
  graph <- mapLeft show $ buildVerificationRevisionGraph
    (Map.elems (ledgerRevisions phase0UploadLedger))
    (manifestCertificationScope phase0UploadManifest)
  let declarations = map sourceDeclarationIdentity
        (checkedSourceUnits (checkedSourceArchitectureBundle architecture))
      architectureIdentity =
        checkedArchitectureIdentity (checkedSourceArchitectureRoot architecture)
      sourceRevision = deriveSourceRevision declarations architectureIdentity
  bundle <- mapLeft show $ buildVerificationBundle
    sourceRevision
    declarations
    [architectureIdentity]
    []
    graph
    uploadAssurancePolicy
    (Map.elems (ledgerEvidence phase0UploadLedger))
  let stageArtifact = phase1StageSystemsArtifact uploadPhase1StageBundle
      context = phase0UploadVerificationContext
        { verificationArchitectureDigest = verificationBundleArchitectureDigest bundle
        , verificationPhilCoreDigest = digestText
            (canonicalSemanticForm (coreSystemsProgramSemanticForm uploadCoreProgram))
        , verificationImplementationDigest = systemsArtifactDigest stageArtifact
        , verificationTarget = "phase1-upload"
        , verificationCompilationProfile = "phase1/int002/certified-release"
        , verificationExpectedObligations = Map.keysSet (verificationGraphNodes graph)
        , verificationLoweringLedgerRoot =
            loweringLedgerRoot (systemsArtifactLoweringLedger stageArtifact)
        }
      selection = ManifestClosureSelection
        { manifestClosureEvidence = manifestEvidenceEntries phase0UploadManifest
        , manifestClosureAssumptions = manifestAssumptionNodes phase0UploadManifest
        , manifestClosureExports = Map.fromSet
            (const Exported) (manifestExports phase0UploadManifest)
        , manifestClosureUses = manifestAssuranceUses phase0UploadManifest
        }
  Right (bundle, context, selection)

uploadAssurancePolicy :: ApplicationAssurancePolicy
uploadAssurancePolicy = ApplicationAssurancePolicy
  { applicationAssurancePolicyRevision =
      AssurancePolicyRevision "phase1.int002.upload.certified-release.v1"
  , applicationAssurancePolicyPermittedDispositions = Set.fromList
      [ StaticallyDischarged
      , RuntimeBound
      , ExternallyDischarged
      , AssumptionDependent
      , Exported
      , DeploymentExported
      ]
  }

checkedUploadArchitecture :: Text -> Text -> Either String CheckedSourceArchitecture
checkedUploadArchitecture clientSource serverSource = do
  clientEnvironment <- mapLeft show (phase0EnvironmentFor "client.phil")
  serverEnvironment <- mapLeft show (phase0EnvironmentFor "server.phil")
  checked <- mapLeft show $ checkPortableSourceBundle
    uploadRoots
    (Map.fromList
      [ (uploadClientDeclaration, clientEnvironment)
      , (uploadServerDeclaration, serverEnvironment)
      ])
    (uploadBundle clientSource serverSource)
  mapLeft show $ buildCheckedSourceArchitecture
    (Map.singleton "program:upload" (InstanceLineageSiteId "instance.upload"))
    checked

uploadBundle :: Text -> Text -> PortableSourceBundle
uploadBundle clientSource serverSource = PortableSourceBundle
  { portableGrammarRevision = canonicalGrammarRevisionV1
  , portableSelectedProgramRoot = "program:upload"
  , portableSourceUnits =
      [ PortableSourceUnit
          (SourceUnitId "unit.upload.client")
          (DeclarationSiteId "site.upload.client")
          (Just "decl:upload.client")
          clientSource
      , PortableSourceUnit
          (SourceUnitId "unit.upload.server")
          (DeclarationSiteId "site.upload.server")
          (Just "decl:upload.server")
          serverSource
      ]
  , portableInstanceLineage =
      [ PortableInstanceLineage
          (InstanceLineageSiteId "instance.upload")
          "inst:phase1.upload"
      ]
  , portableProcessLineage = []
  }

uploadRoots :: SourceRootMap
uploadRoots = Map.singleton "program:upload" uploadServerDeclaration

uploadClientDeclaration, uploadServerDeclaration :: DeclarationKey
uploadClientDeclaration = DeclarationKey "decl:upload.client"
uploadServerDeclaration = DeclarationKey "decl:upload.server"

sourceDeclarationIdentity :: CheckedSourceUnit -> DeclarationIdentity
sourceDeclarationIdentity unit = deriveDeclarationIdentity DeclarationDescriptor
  { declarationPresentation = DeclarationPresentation "ordinary-source" []
  , declarationKey = checkedSourceDeclarationKey unit
  , declarationInterfaceSemantics = sourceComponentInterfaceSemantics component
  , declarationDefinitionSemantics = sourceComponentDefinitionSemantics component
  }
  where
    component = locatedValue (checkedSourceComponent unit)

deriveSourceRevision
  :: [DeclarationIdentity]
  -> ArchitectureInstanceIdentity
  -> Digest
deriveSourceRevision declarations instanceIdentity = digestText (Text.intercalate "\n"
  ("phase1-int002-upload-source-v1" : map renderDeclaration ordered
    <> ["instance=" <> renderInstance instanceIdentity]))
  where
    ordered = Set.toAscList (Set.fromList declarations)
    renderDeclaration identity = Text.intercalate "@"
      [ unDeclarationKey (identityDeclarationKey identity)
      , unInterfaceRevision (identityInterfaceRevision identity)
      , unDefinitionRevision (identityDefinitionRevision identity)
      ]
    renderInstance identity = Text.intercalate "@"
      [ unInstanceKey (identityInstanceKey identity)
      , unInstanceRevision (identityInstanceRevision identity)
      ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
