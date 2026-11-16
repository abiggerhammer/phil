{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler.SourceSystems
  ( SourceSystemsAdmission
  , SourceSystemsError (..)
  , prepareSourceSystemsAdmission
  , lowerSourceSystems
  , VerifiedSourceSystemsProduction
  , VerifiedSourceCheckEventGraph
  , verifiedSourceSystemsCheckEventGraph
  , verifiedSourceCheckEventOccurrences
  , verifiedSourceCheckEventArchitectureIdentity
  , verifiedSourceCheckEventCoreSemantics
  , VerifiedSourceSystemsProductionError (..)
  , produceVerifiedSourceSystems
  , verifiedSourceSystemsArchitectureIdentity
  , verifiedSourceSystemsArchitectureDescriptor
  , verifiedSourceSystemsStage
  , sourceSystemsArchitectureIdentity
  , sourceSystemsProgramSemantics
  , withVerifiedSourceCore
  ) where

import Phil.Compiler.SourceArchitecture
  ( CheckedSourceArchitecture (..)
  , SourceArchitectureError
  , SourceArchitectureRootMap
  , buildCheckedSourceArchitecture
  )
import Phil.Compiler.SourceBundle
  ( CheckedSourceEvidenceOccurrence
  , checkedSourceEvidenceOccurrences
  , SourceBundleCheckError
  , SourceEnvironmentMap
  , SourceRootMap
  , checkPortableSourceBundle
  )
import Phil.Compiler.SourceCore
  ( CheckedSourceCoreCorrespondence
  , SourceCoreCorrespondenceError
  , sourceCoreArchitectureIdentity
  , sourceCoreProgramSemantics
  , verifySourceCoreCorrespondence
  )
import Phil.Compiler.SourceCorePolicy
  ( SourceCoreCorrespondencePolicy, SourceCorePolicyError
  , verifySourceCorePolicy )
import Phil.Core.Static
  ( ArchitectureInstanceDescriptor
  , ArchitectureInstanceIdentity
  , SemanticForm
  , checkedArchitectureDescriptor
  , checkedArchitectureIdentity
  , identityInstanceRevision
  )
import Phil.Systems.GenericLowering
  ( CoreSystemsProgram
  , GenericLoweringError
  , GenericRealizationContext
  , coreSystemsProgramSemanticForm
  , lowerGenericSystems
  )
import Phil.Systems.Phase1Stage (Phase1StageBundle (..))
import Phil.Surface.Lineage (PortableSourceBundle)

-- | Opaque admission object sealing the exact source-derived Architecture and
-- CoreSystemsProgram pair that passed both structural correspondence and the
-- complete independent source-call/branch correspondence policy. Callers cannot
-- replace either member between verification and lowering.
data SourceSystemsAdmission = SourceSystemsAdmission
  CheckedSourceArchitecture
  CoreSystemsProgram
  CheckedSourceCoreCorrespondence
  deriving (Eq, Show)

data SourceSystemsError
  = SourceSystemsCorrespondenceRejected SourceCoreCorrespondenceError
  | SourceSystemsPolicyRejected SourceCorePolicyError
  | SourceSystemsAdmissionArchitectureDrift
  | SourceSystemsAdmissionProgramDrift
  | SourceSystemsLoweringRejected GenericLoweringError
  deriving (Eq, Show)

prepareSourceSystemsAdmission
  :: SourceCoreCorrespondencePolicy
  -> CheckedSourceArchitecture
  -> CoreSystemsProgram
  -> Either SourceSystemsError SourceSystemsAdmission
prepareSourceSystemsAdmission policy architecture program = do
  correspondence <- mapLeft SourceSystemsCorrespondenceRejected
    (verifySourceCoreCorrespondence architecture program)
  mapLeft SourceSystemsPolicyRejected
    (verifySourceCorePolicy policy architecture program)
  Right (SourceSystemsAdmission architecture program correspondence)

lowerSourceSystems
  :: SourceSystemsAdmission
  -> GenericRealizationContext
  -> Either SourceSystemsError Phase1StageBundle
lowerSourceSystems (SourceSystemsAdmission architecture program correspondence) context = do
  if checkedArchitectureIdentity (checkedSourceArchitectureRoot architecture)
      == sourceCoreArchitectureIdentity correspondence
    then Right ()
    else Left SourceSystemsAdmissionArchitectureDrift
  if coreSystemsProgramSemanticForm program == sourceCoreProgramSemantics correspondence
    then Right ()
    else Left SourceSystemsAdmissionProgramDrift
  mapLeft SourceSystemsLoweringRejected
    (lowerGenericSystems
      (checkedSourceArchitectureRoot architecture)
      program
      context)

-- | The exact stage produced by an ordinary checked-source/checked-Core
-- event, paired with that event's complete sealed admission (including K/I).
-- Its constructor is private; caller-created CheckedSourceArchitecture values
-- cannot enter the stronger producing function below.
-- This is NOT a StageClosure or CertifiedRelease origin certificate.
-- | Private provenance of original *static checker* observations from the
-- rechecked raw source bundle and the exact already-admitted Core/Architecture
-- pair. The constructor is private: public CheckedSourceUnit/Surface results
-- and copied evidence arrays cannot construct this witness. This witnesses
-- P2 transport, NOT an actual later P7 assurance use, universal Core op-event
-- simulation, SYS-012 completeness or SYS-013 discharge.
data VerifiedSourceCheckEventGraph = VerifiedSourceCheckEventGraph
  [CheckedSourceEvidenceOccurrence]
  ArchitectureInstanceIdentity
  SemanticForm
  deriving (Eq, Show)

data VerifiedSourceSystemsProduction = VerifiedSourceSystemsProduction
  SourceSystemsAdmission
  Phase1StageBundle
  VerifiedSourceCheckEventGraph
  deriving (Eq, Show)

verifiedSourceCheckEventOccurrences
  :: VerifiedSourceCheckEventGraph -> [CheckedSourceEvidenceOccurrence]
verifiedSourceCheckEventOccurrences (VerifiedSourceCheckEventGraph events _ _) = events

verifiedSourceCheckEventArchitectureIdentity
  :: VerifiedSourceCheckEventGraph -> ArchitectureInstanceIdentity
verifiedSourceCheckEventArchitectureIdentity
  (VerifiedSourceCheckEventGraph _ identity _) = identity

verifiedSourceCheckEventCoreSemantics
  :: VerifiedSourceCheckEventGraph -> SemanticForm
verifiedSourceCheckEventCoreSemantics
  (VerifiedSourceCheckEventGraph _ _ semantics) = semantics

verifiedSourceSystemsCheckEventGraph
  :: VerifiedSourceSystemsProduction -> VerifiedSourceCheckEventGraph
verifiedSourceSystemsCheckEventGraph
  (VerifiedSourceSystemsProduction _ _ graph) = graph

data VerifiedSourceSystemsProductionError
  = VerifiedSourceBundleRejected SourceBundleCheckError
  | VerifiedSourceArchitectureRejected SourceArchitectureError
  | VerifiedSourceAdmissionRejected SourceSystemsError
  | VerifiedSourceLoweringRejected SourceSystemsError
  | VerifiedSourceInstanceRevisionDrift
  deriving (Eq, Show)

-- | Recheck raw ordinary source/lineage rather than accepting a public
-- "checked" record. Preserve its exact K and I next to the complete stage
-- from the actual admitted generic Core-to-Systems lowering event.
-- Source environments and Core correspondence policy remain the existing
-- Phase 1 authority inputs, not newly proved compiler facts.
produceVerifiedSourceSystems
  :: SourceRootMap
  -> SourceEnvironmentMap
  -> SourceArchitectureRootMap
  -> SourceCoreCorrespondencePolicy
  -> PortableSourceBundle
  -> CoreSystemsProgram
  -> GenericRealizationContext
  -> Either VerifiedSourceSystemsProductionError VerifiedSourceSystemsProduction
produceVerifiedSourceSystems roots environments sites policy portable program context = do
  checked <- mapLeft VerifiedSourceBundleRejected
    (checkPortableSourceBundle roots environments portable)
  architecture <- mapLeft VerifiedSourceArchitectureRejected
    (buildCheckedSourceArchitecture sites checked)
  admitted <- mapLeft VerifiedSourceAdmissionRejected
    (prepareSourceSystemsAdmission policy architecture program)
  stage <- mapLeft VerifiedSourceLoweringRejected
    (lowerSourceSystems admitted context)
  let graph = VerifiedSourceCheckEventGraph
        (checkedSourceEvidenceOccurrences checked)
        (sourceSystemsArchitectureIdentity admitted)
        (sourceSystemsProgramSemantics admitted)
  if phase1StageInstanceRevision stage ==
      identityInstanceRevision (sourceSystemsArchitectureIdentity admitted)
    then Right (VerifiedSourceSystemsProduction admitted stage graph)
    else Left VerifiedSourceInstanceRevisionDrift

verifiedSourceSystemsArchitectureIdentity
  :: VerifiedSourceSystemsProduction -> ArchitectureInstanceIdentity
verifiedSourceSystemsArchitectureIdentity
  (VerifiedSourceSystemsProduction admitted _ _) =
    sourceSystemsArchitectureIdentity admitted

-- | The exact descriptor independently rederived from the raw ordinary source
-- and sealed in the checked producer. Full K, parent, declaration, and
-- semantic actuals survive; no caller-created checked record is accepted.
verifiedSourceSystemsArchitectureDescriptor
  :: VerifiedSourceSystemsProduction -> ArchitectureInstanceDescriptor
verifiedSourceSystemsArchitectureDescriptor
  (VerifiedSourceSystemsProduction (SourceSystemsAdmission architecture _ _) _ _) =
    checkedArchitectureDescriptor (checkedSourceArchitectureRoot architecture)

verifiedSourceSystemsStage
  :: VerifiedSourceSystemsProduction -> Phase1StageBundle
verifiedSourceSystemsStage (VerifiedSourceSystemsProduction _ stage _) = stage

sourceSystemsArchitectureIdentity
  :: SourceSystemsAdmission
  -> ArchitectureInstanceIdentity
sourceSystemsArchitectureIdentity
  (SourceSystemsAdmission _ _ correspondence) =
    sourceCoreArchitectureIdentity correspondence

sourceSystemsProgramSemantics
  :: SourceSystemsAdmission
  -> SemanticForm
sourceSystemsProgramSemantics
  (SourceSystemsAdmission _ _ correspondence) =
    sourceCoreProgramSemantics correspondence

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right



-- | A read-only diagnostic projection of the original privately sealed
-- source/Core pair. Neither value on its own is a P9 authority certificate.
withVerifiedSourceCore
  :: VerifiedSourceSystemsProduction
  -> (CheckedSourceArchitecture -> CoreSystemsProgram -> a)
  -> a
withVerifiedSourceCore
  (VerifiedSourceSystemsProduction (SourceSystemsAdmission arch core _) _ _) f =
    f arch core
