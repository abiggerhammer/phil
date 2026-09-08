{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler.SourceSystems
  ( SourceSystemsAdmission
  , SourceSystemsError (..)
  , prepareSourceSystemsAdmission
  , lowerSourceSystems
  , sourceSystemsArchitectureIdentity
  , sourceSystemsProgramSemantics
  ) where

import Phil.Compiler.SourceArchitecture
  ( CheckedSourceArchitecture (..)
  )
import Phil.Compiler.SourceCore
  ( CheckedSourceCoreCorrespondence
  , SourceCoreCorrespondenceError
  , sourceCoreArchitectureIdentity
  , sourceCoreProgramSemantics
  , verifySourceCoreCorrespondence
  )
import Phil.Core.Static
  ( ArchitectureInstanceIdentity
  , SemanticForm
  , checkedArchitectureIdentity
  )
import Phil.Systems.GenericLowering
  ( CoreSystemsProgram
  , GenericLoweringError
  , GenericRealizationContext
  , coreSystemsProgramSemanticForm
  , lowerGenericSystems
  )
import Phil.Systems.Phase1Stage (Phase1StageBundle)

-- | Opaque admission object sealing the exact source-derived Architecture and
-- CoreSystemsProgram pair that passed source/Core correspondence checking.
-- Callers cannot replace either member between verification and lowering.
data SourceSystemsAdmission = SourceSystemsAdmission
  CheckedSourceArchitecture
  CoreSystemsProgram
  CheckedSourceCoreCorrespondence
  deriving (Eq, Show)

data SourceSystemsError
  = SourceSystemsCorrespondenceRejected SourceCoreCorrespondenceError
  | SourceSystemsAdmissionArchitectureDrift
  | SourceSystemsAdmissionProgramDrift
  | SourceSystemsLoweringRejected GenericLoweringError
  deriving (Eq, Show)

prepareSourceSystemsAdmission
  :: CheckedSourceArchitecture
  -> CoreSystemsProgram
  -> Either SourceSystemsError SourceSystemsAdmission
prepareSourceSystemsAdmission architecture program = do
  correspondence <- mapLeft SourceSystemsCorrespondenceRejected
    (verifySourceCoreCorrespondence architecture program)
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
