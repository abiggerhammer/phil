{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Assurance
import Phil.Core.Syntax (ObligationId (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  unless (length revisions == 12) $ do
    putStrLn "FAIL: Steve obligation set drifted from the twelve-row matrix"
    exitFailure

  expectPass "Steve 0 provisional assurance manifest" steveManifest

  -- Collision resistance is intentionally disclosed but not used to justify
  -- Steve's fail-closed safety obligations. Removing it from the selected
  -- manifest therefore leaves the safety closure valid.
  expectPass
    "Steve safety closure does not depend on SHA-256 collision resistance"
    (withoutAssumption collisionResistanceAssumption steveManifest)

  -- The provider trust boundaries are different: concrete Steve obligations
  -- do depend on their declared contracts until stronger evidence replaces
  -- these assumptions.
  expectFailure
    "BlobProvider trust boundary is required"
    (withoutAssumption blobProviderAssumption steveManifest)
  expectFailure
    "DigestProvider trust boundary is required"
    (withoutAssumption digestProviderAssumption steveManifest)

expectPass :: String -> AssuranceManifest -> IO ()
expectPass label manifest =
  case verifyManifest steveVerificationContext steveLedger manifest of
    Right () -> putStrLn ("PASS: " ++ label)
    Left err -> do
      putStrLn ("FAIL: " ++ label ++ " -- " ++ show err)
      exitFailure

expectFailure :: String -> AssuranceManifest -> IO ()
expectFailure label manifest =
  case verifyManifest steveVerificationContext steveLedger manifest of
    Left _ -> putStrLn ("PASS: " ++ label)
    Right () -> do
      putStrLn ("FAIL: " ++ label ++ " -- verifier unexpectedly accepted manifest")
      exitFailure

withoutAssumption :: Assumption -> AssuranceManifest -> AssuranceManifest
withoutAssumption assumption manifest = reidentify manifest
  { manifestAssumptionNodes =
      Set.delete (assumptionId assumption) (manifestAssumptionNodes manifest)
  }

reidentify :: AssuranceManifest -> AssuranceManifest
reidentify manifest = manifest
  { manifestId = deriveManifestId steveLedger manifest }

-- ---------------------------------------------------------------------------
-- Build / validity identity
-- ---------------------------------------------------------------------------

architectureDigest :: Digest
architectureDigest = digestText
  "Steve 0 ADR-001 + ADR-002 + Provider Protocols + Obligation Matrix"

coreDigest :: Digest
coreDigest = digestText
  "Phil Core assurance-verifier semantic boundary"

implementationDigest :: Digest
implementationDigest = digestText
  "Steve 0 checker-facing semantic witness on steve/architecture-sketch"

loweringRoot :: Digest
loweringRoot = digestText
  "Steve 0 provisional runtime-cost ledger root"

validityContext :: Map.Map Text Text
validityContext = Map.fromList
  [ ("architecture", "Steve 0")
  , ("storage", "local append-only content-addressed byte store")
  , ("digest", "SHA-256")
  , ("provider_model", "abstract DigestProvider + BlobProvider")
  ]

runtimeScope :: ValidityScope
runtimeScope = ValidityScope validityContext

unscoped :: ValidityScope
unscoped = ValidityScope Map.empty

role :: Text -> EvidenceRole
role = EvidenceRole

entryRule :: AssuranceKind -> Text -> AcceptanceRule
entryRule kind roleName = AcceptEntry kind (role roleName)

allOf :: [(AssuranceKind, Text)] -> AcceptanceRule
allOf = AcceptAll . map (uncurry entryRule)

-- ---------------------------------------------------------------------------
-- Obligation revisions: the twelve Steve 0 safety/architecture claims.
-- ---------------------------------------------------------------------------

mkRevision
  :: Text
  -> Text
  -> [Text]
  -> AcceptanceRule
  -> ObligationRevision
mkRevision obligationName statement subjects acceptance = provisional
  { revisionId = deriveRevisionId provisional }
  where
    provisional = ObligationRevision
      { revisionObligationId = ObligationId obligationName
      , revisionId = RevisionId ""
      , revisionStatement = statement
      , revisionStatementDigest = digestText statement
      , revisionKind = "Steve0"
      , revisionOrigin = "Steve 0 Obligation Matrix"
      , revisionScope = "steve.0.semantic"
      , revisionRequiredAt = "semantic/reference certification"
      , revisionRepresentation = "Steve .phil witness + provider protocol"
      , revisionSubjectIds = subjects
      , revisionContextIds = []
      , revisionAcceptanceRule = acceptance
      , revisionGeneratedFrom = []
      }

putDigest :: ObligationRevision
putDigest = mkRevision
  "STEVE-PUT-DIGEST"
  "Successful put returns a ContentId with DigestMatches(id, objectId(candidate)) for the stable candidate byte-object identity"
  ["candidateObject", "contentId"]
  (allOf
    [ (KernelChecked, "checks_success_evidence")
    , (RuntimeEnforced, "digest_establishes")
    ])

getDigest :: ObligationRevision
getDigest = mkRevision
  "STEVE-GET-DIGEST"
  "Successful get returns exactly one owned byte object with DigestMatches(id, objectId(bytes)) indexed by that same stable identity"
  ["storedObject", "contentId"]
  (allOf
    [ (KernelChecked, "checks_success_evidence")
    , (RuntimeEnforced, "digest_validates")
    ])

noClobber :: ObligationRevision
noClobber = mkRevision
  "STEVE-NO-CLOBBER"
  "Steve never replaces the contents of an existing committed object"
  ["contentId"]
  (allOf
    [ (KernelChecked, "authority_surface")
    , (Assumed, "assumption_boundary")
    ])

atomicPublish :: ObligationRevision
atomicPublish = mkRevision
  "STEVE-ATOMIC-PUBLISH"
  "Partial writes are never observable as committed objects"
  ["contentId"]
  (entryRule Assumed "assumption_boundary")

putIdempotent :: ObligationRevision
putIdempotent = mkRevision
  "STEVE-PUT-IDEMPOTENT"
  "Repeated put of identical bytes returns the same ContentId without changing the committed object"
  ["candidateObject", "existingObject", "contentId"]
  (entryRule KernelChecked "derived_control_flow")

collisionFails :: ObligationRevision
collisionFails = mkRevision
  "STEVE-COLLISION-FAILS"
  "When different byte strings are observed with one ContentId, ordinary put success is forbidden and DigestCollision is reported when both digests match"
  ["candidateObject", "existingObject", "contentId"]
  (allOf
    [ (KernelChecked, "fail_closed_control")
    , (RuntimeEnforced, "checks_existing_digest")
    ])

corruptionFails :: ObligationRevision
corruptionFails = mkRevision
  "STEVE-CORRUPTION-FAILS"
  "Stored bytes whose digest disagrees with the requested ContentId are never returned or accepted as valid Steve objects"
  ["storedObject", "contentId"]
  (allOf
    [ (KernelChecked, "fail_closed_control")
    , (RuntimeEnforced, "digest_validates")
    ])

noDelete :: ObligationRevision
noDelete = mkRevision
  "STEVE-NO-DELETE"
  "No Steve 0 operation possesses authority to remove a committed object"
  []
  (entryRule KernelChecked "authority_surface")

crashState :: ObligationRevision
crashState = mkRevision
  "STEVE-CRASH-STATE"
  "After interrupted put, an object is absent or completely committed; no partial committed state is visible"
  ["contentId"]
  (entryRule Assumed "assumption_boundary")

installBorrowScope :: ObligationRevision
installBorrowScope = mkRevision
  "STEVE-INSTALL-BORROW-SCOPE"
  "BlobProvider.installIfAbsent observes only a scoped read-only candidate view and neither consumes ownership nor retains the view beyond its borrow scope"
  ["candidateObject"]
  (allOf
    [ (KernelChecked, "borrow_scope")
    , (Assumed, "assumption_boundary")
    ])

digestEvidenceIdentity :: ObligationRevision
digestEvidenceIdentity = mkRevision
  "STEVE-DIGEST-EVIDENCE-IDENTITY"
  "Persistent DigestMatches evidence about restricted bytes is indexed by stable byte-object identity and never by the ephemeral borrowed view"
  ["byteObject"]
  (allOf
    [ (KernelChecked, "stable_identity_contract")
    , (Assumed, "assumption_boundary")
    ])

byteEqualityEvidence :: ObligationRevision
byteEqualityEvidence = mkRevision
  "STEVE-BYTE-EQUALITY-EVIDENCE"
  "Exact byte comparison produces branch evidence BytewiseEqual(leftId,rightId) or BytewiseDifferent(leftId,rightId)"
  ["leftObject", "rightObject"]
  (allOf
    [ (KernelChecked, "checks_branch_evidence")
    , (RuntimeEnforced, "compares_exactly")
    ])

revisions :: [ObligationRevision]
revisions =
  [ putDigest
  , getDigest
  , noClobber
  , atomicPublish
  , putIdempotent
  , collisionFails
  , corruptionFails
  , noDelete
  , crashState
  , installBorrowScope
  , digestEvidenceIdentity
  , byteEqualityEvidence
  ]

-- ---------------------------------------------------------------------------
-- Assumption / TCB nodes.
-- ---------------------------------------------------------------------------

mkAssumption :: Text -> Text -> Text -> Text -> Assumption
mkAssumption stableId statement owner rationale = provisional
  { assumptionDigest = deriveAssumptionDigest provisional }
  where
    provisional = Assumption
      { assumptionId = AssumptionId stableId
      , assumptionDigest = Digest ""
      , assumptionStatement = statement
      , assumptionScope = "steve.0.semantic"
      , assumptionOwnerBoundary = owner
      , assumptionRationale = rationale
      , assumptionValidityScope = runtimeScope
      }

collisionResistanceAssumption :: Assumption
collisionResistanceAssumption = mkAssumption
  "assumption.steve.sha256_collision_resistance"
  "Finding distinct byte strings with the same SHA-256 digest is computationally infeasible for practical Steve object identity"
  "cryptographic environment"
  "Disclosed for practical global identity interpretation; deliberately not required by Steve's fail-closed safety obligations"

digestProviderAssumption :: Assumption
digestProviderAssumption = mkAssumption
  "assumption.steve.digest_provider_contract"
  "DigestProvider faithfully computes SHA-256 over the exact borrowed bytes and persistent evidence names the declared stable byte-object identity rather than the loan token"
  "DigestProvider / crypto runtime TCB"
  "Initial trusted implementation boundary for digest computation and stable evidence production"

blobProviderAssumption :: Assumption
blobProviderAssumption = mkAssumption
  "assumption.steve.blob_provider_contract"
  "BlobProvider faithfully implements read plus atomic no-replace install-if-absent and copies the exact borrowed bytes before the loan ends"
  "BlobProvider / storage runtime TCB"
  "Initial trusted implementation boundary for append-only publication, crash visibility, and borrow-safe copied publication"

assumptions :: [Assumption]
assumptions =
  [ collisionResistanceAssumption
  , digestProviderAssumption
  , blobProviderAssumption
  ]

-- ---------------------------------------------------------------------------
-- Evidence entries.
-- ---------------------------------------------------------------------------

mkEvidence
  :: Text
  -> ObligationRevision
  -> AssuranceKind
  -> Text
  -> Text
  -> Text
  -> [AssumptionId]
  -> [EvidenceDependency]
  -> Maybe RuntimeMechanism
  -> [Text]
  -> [Text]
  -> EvidenceEntry
mkEvidence stableId revision kind roleName producer checker assumptionIds dependencies runtimeMechanism residue costRefs =
  provisional { evidenceEntryDigest = deriveEvidenceEntryDigest provisional }
  where
    scoped
      | kind == RuntimeEnforced = runtimeScope
      | kind == Assumed = runtimeScope
      | otherwise = unscoped
    provisional = EvidenceEntry
      { evidenceEntryId = EvidenceEntryId stableId
      , evidenceEntryDigest = Digest ""
      , evidenceObligationRevision = revisionId revision
      , evidenceAssuranceKind = kind
      , evidenceRole = role roleName
      , evidenceProducer = producer
      , evidenceChecker = checker
      , evidenceArtifact = Nothing
      , evidenceInputDigests = []
      , evidenceAssumptions = assumptionIds
      , evidenceDependsOn = dependencies
      , evidenceValidityScope = scoped
      , evidenceResult = EvidenceAccepted
      , evidenceJustifies = []
      , evidenceRuntimeMechanism = runtimeMechanism
      , evidenceRuntimeResidue = residue
      , evidenceCostRefs = costRefs
      }

runtime :: Text -> Text -> Text -> Text -> RuntimeMechanism
runtime name point success failure = RuntimeMechanism
  { runtimeMechanismName = name
  , runtimeExecutionPoint = point
  , runtimeSuccessEvidenceType = success
  , runtimeFailureContract = failure
  , runtimeImplementation = Nothing
  }

kernelEvidence
  :: Text
  -> ObligationRevision
  -> Text
  -> Text
  -> [EvidenceDependency]
  -> EvidenceEntry
kernelEvidence stableId revision roleName producer dependencies = mkEvidence
  stableId revision KernelChecked roleName producer "Phil Core" [] dependencies Nothing [] []

assumedEvidence
  :: Text
  -> ObligationRevision
  -> Assumption
  -> [EvidenceDependency]
  -> EvidenceEntry
assumedEvidence stableId revision assumption dependencies = mkEvidence
  stableId revision Assumed "assumption_boundary"
  (assumptionOwnerBoundary assumption) "Phil assurance verifier"
  [assumptionId assumption] dependencies Nothing [] []

runtimeEvidence
  :: Text
  -> ObligationRevision
  -> Text
  -> Text
  -> [AssumptionId]
  -> [EvidenceDependency]
  -> RuntimeMechanism
  -> [Text]
  -> Text
  -> EvidenceEntry
runtimeEvidence stableId revision roleName producer assumptionIds dependencies mechanism residue costRef = mkEvidence
  stableId revision RuntimeEnforced roleName producer "declared Steve runtime boundary"
  assumptionIds dependencies (Just mechanism) residue [costRef]

putDigestKernel :: EvidenceEntry
putDigestKernel = kernelEvidence
  "evidence.steve.put_digest.kernel" putDigest "checks_success_evidence"
  "Phil result/evidence checker" []

putDigestRuntime :: EvidenceEntry
putDigestRuntime = runtimeEvidence
  "evidence.steve.put_digest.runtime" putDigest "digest_establishes"
  "DigestProvider.digest"
  [assumptionId digestProviderAssumption]
  [DependsOnObligation (revisionId digestEvidenceIdentity)]
  (runtime
    "SHA-256 candidate digest"
    "StevePut before installIfAbsent"
    "Proof[DigestMatches(id,candidateObject)]"
    "digest-provider failure cannot produce PutOk")
  ["SHA-256 computation retained at runtime"]
  "steve.runtime.digest_compute"

getDigestKernel :: EvidenceEntry
getDigestKernel = kernelEvidence
  "evidence.steve.get_digest.kernel" getDigest "checks_success_evidence"
  "Phil result/evidence checker" []

getDigestRuntime :: EvidenceEntry
getDigestRuntime = runtimeEvidence
  "evidence.steve.get_digest.runtime" getDigest "digest_validates"
  "DigestProvider.digest_check"
  [assumptionId digestProviderAssumption]
  [DependsOnObligation (revisionId digestEvidenceIdentity)]
  (runtime
    "SHA-256 get validation"
    "SteveGet found(bytes), before GetOk"
    "Proof[DigestMatches(id,byteObject)]"
    "digest mismatch releases bytes and returns GetIntegrityFailure")
  ["SHA-256 recomputation and comparison retained at runtime"]
  "steve.runtime.digest_check"

noClobberKernel :: EvidenceEntry
noClobberKernel = kernelEvidence
  "evidence.steve.no_clobber.kernel" noClobber "authority_surface"
  "Steve provider-capability architecture" []

noClobberAssumed :: EvidenceEntry
noClobberAssumed = assumedEvidence
  "evidence.steve.no_clobber.provider" noClobber blobProviderAssumption []

atomicPublishAssumed :: EvidenceEntry
atomicPublishAssumed = assumedEvidence
  "evidence.steve.atomic_publish.provider" atomicPublish blobProviderAssumption []

putIdempotentKernel :: EvidenceEntry
putIdempotentKernel = kernelEvidence
  "evidence.steve.put_idempotent.kernel" putIdempotent "derived_control_flow"
  "Phil branch/resource checker"
  [ DependsOnObligation (revisionId putDigest)
  , DependsOnObligation (revisionId noClobber)
  , DependsOnObligation (revisionId byteEqualityEvidence)
  ]

collisionKernel :: EvidenceEntry
collisionKernel = kernelEvidence
  "evidence.steve.collision.kernel" collisionFails "fail_closed_control"
  "Phil result/control checker"
  [ DependsOnObligation (revisionId putDigest)
  , DependsOnObligation (revisionId byteEqualityEvidence)
  ]

collisionRuntime :: EvidenceEntry
collisionRuntime = runtimeEvidence
  "evidence.steve.collision.runtime" collisionFails "checks_existing_digest"
  "DigestProvider.digest_check"
  [assumptionId digestProviderAssumption]
  [ DependsOnObligation (revisionId digestEvidenceIdentity)
  , DependsOnObligation (revisionId byteEqualityEvidence)
  ]
  (runtime
    "SHA-256 existing-object collision check"
    "StevePut after BytewiseDifferent"
    "Proof[DigestMatches(id,existingObject)] or rejected digest result"
    "rejected digest returns ExistingObjectCorrupt; accepted digest with inequality returns DigestCollision")
  ["conditional SHA-256 existing-object check retained at runtime"]
  "steve.runtime.digest_check"

corruptionKernel :: EvidenceEntry
corruptionKernel = kernelEvidence
  "evidence.steve.corruption.kernel" corruptionFails "fail_closed_control"
  "Phil result/control checker" []

corruptionRuntime :: EvidenceEntry
corruptionRuntime = runtimeEvidence
  "evidence.steve.corruption.runtime" corruptionFails "digest_validates"
  "DigestProvider.digest_check"
  [assumptionId digestProviderAssumption]
  [DependsOnObligation (revisionId digestEvidenceIdentity)]
  (runtime
    "SHA-256 corruption check"
    "SteveGet and StevePut existing-object validation"
    "Proof[DigestMatches(id,byteObject)] on success"
    "mismatch cannot flow to a valid object result")
  ["SHA-256 corruption detection retained at runtime"]
  "steve.runtime.digest_check"

noDeleteKernel :: EvidenceEntry
noDeleteKernel = kernelEvidence
  "evidence.steve.no_delete.kernel" noDelete "authority_surface"
  "Steve public/provider capability architecture" []

crashStateAssumed :: EvidenceEntry
crashStateAssumed = assumedEvidence
  "evidence.steve.crash_state.provider" crashState blobProviderAssumption
  [DependsOnObligation (revisionId atomicPublish)]

installBorrowKernel :: EvidenceEntry
installBorrowKernel = kernelEvidence
  "evidence.steve.install_borrow.kernel" installBorrowScope "borrow_scope"
  "Phil shared-loan checker" []

installBorrowAssumed :: EvidenceEntry
installBorrowAssumed = assumedEvidence
  "evidence.steve.install_borrow.provider" installBorrowScope blobProviderAssumption []

digestIdentityKernel :: EvidenceEntry
digestIdentityKernel = kernelEvidence
  "evidence.steve.digest_identity.kernel" digestEvidenceIdentity "stable_identity_contract"
  "Phil evidence/borrow checker" []

digestIdentityAssumed :: EvidenceEntry
digestIdentityAssumed = assumedEvidence
  "evidence.steve.digest_identity.provider" digestEvidenceIdentity digestProviderAssumption []

byteEqualityKernel :: EvidenceEntry
byteEqualityKernel = kernelEvidence
  "evidence.steve.byte_equality.kernel" byteEqualityEvidence "checks_branch_evidence"
  "Phil decision/result checker" []

byteEqualityRuntime :: EvidenceEntry
byteEqualityRuntime = runtimeEvidence
  "evidence.steve.byte_equality.runtime" byteEqualityEvidence "compares_exactly"
  "bytes_compare" [] []
  (runtime
    "exact byte comparison"
    "StevePut AlreadyExists found(existing)"
    "BytewiseEqual(leftId,rightId) or BytewiseDifferent(leftId,rightId)"
    "comparison failure cannot select either evidence-bearing success arm")
  ["exact byte comparison retained at runtime"]
  "steve.runtime.bytes_compare"

evidenceEntries :: [EvidenceEntry]
evidenceEntries =
  [ putDigestKernel
  , putDigestRuntime
  , getDigestKernel
  , getDigestRuntime
  , noClobberKernel
  , noClobberAssumed
  , atomicPublishAssumed
  , putIdempotentKernel
  , collisionKernel
  , collisionRuntime
  , corruptionKernel
  , corruptionRuntime
  , noDeleteKernel
  , crashStateAssumed
  , installBorrowKernel
  , installBorrowAssumed
  , digestIdentityKernel
  , digestIdentityAssumed
  , byteEqualityKernel
  , byteEqualityRuntime
  ]

-- ---------------------------------------------------------------------------
-- Retained runtime assurance uses and provisional cost references.
-- ---------------------------------------------------------------------------

mkRuntimeUse :: Text -> ObligationRevision -> EvidenceEntry -> Text -> AssuranceUse
mkRuntimeUse stableId revision entry costRef = provisional
  { assuranceUseDigest = deriveAssuranceUseDigest provisional }
  where
    provisional = RetainedRuntimeUse
      { assuranceUseId = AssuranceUseId stableId
      , assuranceUseDigest = Digest ""
      , useObligationRevision = revisionId revision
      , useRuntimeEvidence = evidenceEntryId entry
      , useCostRef = costRef
      }

assuranceUses :: [AssuranceUse]
assuranceUses =
  [ mkRuntimeUse "use.steve.put_digest" putDigest putDigestRuntime "steve.runtime.digest_compute"
  , mkRuntimeUse "use.steve.get_digest" getDigest getDigestRuntime "steve.runtime.digest_check"
  , mkRuntimeUse "use.steve.collision_digest" collisionFails collisionRuntime "steve.runtime.digest_check"
  , mkRuntimeUse "use.steve.corruption_digest" corruptionFails corruptionRuntime "steve.runtime.digest_check"
  , mkRuntimeUse "use.steve.byte_equality" byteEqualityEvidence byteEqualityRuntime "steve.runtime.bytes_compare"
  ]

runtimeCostRefs :: [Text]
runtimeCostRefs =
  [ "steve.runtime.digest_compute"
  , "steve.runtime.digest_check"
  , "steve.runtime.bytes_compare"
  ]

-- ---------------------------------------------------------------------------
-- Ledger / manifest / verification context.
-- ---------------------------------------------------------------------------

steveLedger :: AssuranceLedger
steveLedger = emptyLedger
  { ledgerRevisions = Map.fromList [(revisionId revision, revision) | revision <- revisions]
  , ledgerEvidence = Map.fromList [(evidenceEntryId entry, entry) | entry <- evidenceEntries]
  , ledgerAssumptions = Map.fromList [(assumptionId assumption, assumption) | assumption <- assumptions]
  , ledgerUses = Map.fromList [(assuranceUseId use, use) | use <- assuranceUses]
  }

steveManifest :: AssuranceManifest
steveManifest = reidentify provisionalManifest

provisionalManifest :: AssuranceManifest
provisionalManifest = emptyManifest
  { manifestArchitectureDigest = architectureDigest
  , manifestPhilCoreDigest = coreDigest
  , manifestImplementationDigest = implementationDigest
  , manifestTarget = "steve0-semantic"
  , manifestCompilationProfile = "semantic/provisional"
  , manifestObligationRevisions = revisionSet
  , manifestCertificationScope = revisionSet
  , manifestEvidenceEntries = Set.fromList (map evidenceEntryId evidenceEntries)
  , manifestAssumptionNodes = Set.fromList (map assumptionId assumptions)
  , manifestAssuranceUses = Set.fromList (map assuranceUseId assuranceUses)
  , manifestLoweringLedgerRoot = loweringRoot
  , manifestValidityContext = validityContext
  }
  where
    revisionSet = Set.fromList (map revisionId revisions)

steveVerificationContext :: VerificationContext
steveVerificationContext = emptyVerificationContext
  { verificationArchitectureDigest = architectureDigest
  , verificationPhilCoreDigest = coreDigest
  , verificationImplementationDigest = implementationDigest
  , verificationTarget = "steve0-semantic"
  , verificationCompilationProfile = "semantic/provisional"
  , verificationExpectedObligations = Set.fromList (map revisionId revisions)
  , verificationPermittedAssumptions = Set.fromList (map assumptionId assumptions)
  , verificationLoweringLedgerRoot = loweringRoot
  , verificationKnownCostRefs = Set.fromList runtimeCostRefs
  , verificationValidityContext = validityContext
  }
