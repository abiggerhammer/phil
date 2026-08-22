{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler
  ( RunnableCompileError (..)
  , RunnableProgram (..)
  , compileRunnableUnit
  , renderRunnableCompileError
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax (Ty (TyUnit))
import Phil.LLVM
  ( LLVMArtifact
  , LLVMTargetProfile (..)
  , LLVMVerificationContext (..)
  , LLVMVerificationError
  , lowerSystemsConservative
  , phase0LLVMTarget
  , verifyLLVMEmission
  )
import Phil.Surface.Check
  ( SurfaceCheckError
  , SurfaceEnvironment (..)
  , checkSurfaceComponent
  , emptySurfaceEnvironment
  )
import Phil.Surface.Parser (ParseDiagnostic, parseSurfaceFile)
import Phil.Surface.Syntax
  ( Block (..)
  , Component (..)
  , Located (..)
  , Statement (..)
  , SurfaceExpression (..)
  , SurfaceFile (..)
  , SurfaceType (..)
  )
import Phil.Systems
  ( BlockId (..)
  , CompilationProfile (CertifiedRelease)
  , LoweringLedger (..)
  , StageContract (..)
  , SystemsArtifact (..)
  , SystemsBlock (..)
  , SystemsFunction (..)
  , SystemsProgram (..)
  , SystemsTerminator (TermEnd)
  , SystemsVerificationContext (..)
  , SystemsVerificationError
  , deriveLoweringLedgerRoot
  , systemsArtifactDigest
  , systemsProgramDigest
  , verifySystemsArtifact
  )

data RunnableCompileError
  = RunnableParseError ParseDiagnostic
  | RunnableSurfaceCheckError SurfaceCheckError
  | RunnableFragmentError Text
  | RunnableSystemsVerificationError SystemsVerificationError
  | RunnableLLVMVerificationError LLVMVerificationError
  deriving (Eq, Show)

data RunnableProgram = RunnableProgram
  { runnableSourceDigest :: Digest
  , runnableSystemsArtifact :: SystemsArtifact
  , runnableLLVMArtifact :: LLVMArtifact
  }
  deriving (Eq, Show)

compileRunnableUnit :: Text -> Text -> Either RunnableCompileError RunnableProgram
compileRunnableUnit sourceName source = do
  surfaceFile <- mapLeft RunnableParseError (parseSurfaceFile sourceName source)
  component <- requireSingleComponent surfaceFile
  mapLeft RunnableSurfaceCheckError $
    checkSurfaceComponent runnableSurfaceEnvironment component
  requireRunnableUnitShape component
  let sourceDigest = digestText source
      (systemsArtifact, systemsContext) = buildRunnableSystems sourceDigest
  mapLeft RunnableSystemsVerificationError $
    verifySystemsArtifact systemsContext systemsArtifact
  let llvmArtifact = lowerSystemsConservative phase0LLVMTarget systemsArtifact
      llvmContext = runnableLLVMContext systemsContext phase0LLVMTarget
  mapLeft RunnableLLVMVerificationError $
    verifyLLVMEmission llvmContext systemsArtifact llvmArtifact
  Right RunnableProgram
    { runnableSourceDigest = sourceDigest
    , runnableSystemsArtifact = systemsArtifact
    , runnableLLVMArtifact = llvmArtifact
    }

renderRunnableCompileError :: RunnableCompileError -> Text
renderRunnableCompileError compileError = case compileError of
  RunnableFragmentError detail -> detail
  _ -> Text.pack (show compileError)

runnableSurfaceEnvironment :: SurfaceEnvironment
runnableSurfaceEnvironment =
  (emptySurfaceEnvironment emptyStaticContext)
    { surfaceExpectedProvides = Just TyUnit }

requireSingleComponent :: SurfaceFile -> Either RunnableCompileError (Located Component)
requireSingleComponent (SurfaceFile [component]) = Right component
requireSingleComponent (SurfaceFile components) =
  Left (RunnableFragmentError
    ("runnable fragment requires exactly one component; found "
      <> Text.pack (show (length components))))

requireRunnableUnitShape :: Located Component -> Either RunnableCompileError ()
requireRunnableUnitShape locatedComponent = do
  let component = locatedValue locatedComponent
  unless (componentName component == "main") $
    fragment "runnable fragment requires the component name `main`"
  unless (null (componentParameters component)) $
    fragment "runnable fragment does not yet support component parameters"
  case componentProvides component of
    Just provided | locatedValue provided == SurfaceUnitType -> pure ()
    _ -> fragment "runnable fragment requires `provides Unit`"
  case blockStatements (locatedValue (componentBody component)) of
    [statement] -> case locatedValue statement of
      ReturnStatement expression
        | locatedValue expression == UnitExpression -> pure ()
      _ -> fragment "runnable fragment body must be exactly `return unit`"
    _ -> fragment "runnable fragment body must contain exactly one statement: `return unit`"
  where
    fragment = Left . RunnableFragmentError

buildRunnableSystems
  :: Digest
  -> (SystemsArtifact, SystemsVerificationContext)
buildRunnableSystems sourceDigest = (artifact, systemsContext)
  where
    entryBlock = BlockId "entry"
    function = SystemsFunction
      { systemsFunctionName = "main"
      , systemsFunctionEntry = entryBlock
      , systemsFunctionValues = Map.empty
      , systemsFunctionBlocks = Map.singleton entryBlock SystemsBlock
          { systemsBlockId = entryBlock
          , systemsBlockOps = []
          , systemsBlockTerminator = TermEnd "return-unit"
          }
      }
    program = SystemsProgram
      { systemsProgramName = "runnable-unit"
      , systemsProgramProfile = CertifiedRelease
      , systemsProgramFunctions = Map.singleton "main" function
      }
    targetDigest = systemsProgramDigest program
    decisions = Map.empty
    loweringRoot = deriveLoweringLedgerRoot decisions
    loweringLedger = LoweringLedger
      { loweringLedgerDecisions = decisions
      , loweringLedgerRoot = loweringRoot
      }
    stageContract = StageContract
      { stageContractId = "surface-to-systems/runnable-unit/v1"
      , stageSourceArtifactDigest = sourceDigest
      , stageTargetArtifactDigest = targetDigest
      , stageFacts = []
      , stageInvariants = Map.empty
      , stageRequiredEdges = []
      , stageDerivedObligations = []
      , stageAssumptions = []
      , stageTraceRelation = ["return unit -> normal completion"]
      , stageResourceFailureRelation = ["no resources; no failure edges"]
      }
    artifact = SystemsArtifact
      { systemsArtifactProgram = program
      , systemsArtifactStageContract = stageContract
      , systemsArtifactLoweringLedger = loweringLedger
      }
    assuranceLedger = emptyLedger
    coreDigest = digestText "phil-core/runnable-unit-fragment/v1"
    systemsTarget = "systems-ir/runnable-unit/v1"
    systemsProfile = "systems/certified-release/runnable-unit/v1"
    validityContext = Map.singleton "fragment" "runnable-unit/v1"
    provisionalManifest = emptyManifest
      { manifestArchitectureDigest = sourceDigest
      , manifestPhilCoreDigest = coreDigest
      , manifestImplementationDigest = systemsArtifactDigest artifact
      , manifestTarget = systemsTarget
      , manifestCompilationProfile = systemsProfile
      , manifestLoweringLedgerRoot = loweringRoot
      , manifestValidityContext = validityContext
      }
    manifest = provisionalManifest
      { manifestId = deriveManifestId assuranceLedger provisionalManifest }
    assuranceContext = emptyVerificationContext
      { verificationArchitectureDigest = sourceDigest
      , verificationPhilCoreDigest = coreDigest
      , verificationImplementationDigest = systemsArtifactDigest artifact
      , verificationTarget = systemsTarget
      , verificationCompilationProfile = systemsProfile
      , verificationExpectedObligations = Set.empty
      , verificationLoweringLedgerRoot = loweringRoot
      , verificationValidityContext = validityContext
      }
    systemsContext = SystemsVerificationContext
      { systemsAssuranceLedger = assuranceLedger
      , systemsAssuranceManifest = manifest
      , systemsAssuranceVerificationContext = assuranceContext
      , systemsExpectedSourceArtifactDigest = sourceDigest
      , systemsExpectedRuntimeKinds = Map.empty
      , systemsExpectedSourceFacts = Set.empty
      , systemsFactsRequiringTransfer = Set.empty
      }

runnableLLVMContext
  :: SystemsVerificationContext
  -> LLVMTargetProfile
  -> LLVMVerificationContext
runnableLLVMContext systemsContext target = LLVMVerificationContext
  { llvmSystemsContext = systemsContext
  , llvmExpectedLanguageVersion = llvmTargetLanguageVersion target
  , llvmExpectedToolVersion = llvmTargetToolVersion target
  , llvmExpectedTargetTriple = llvmTargetTripleName target
  , llvmExpectedDataLayout = llvmTargetDataLayout target
  , llvmExpectedRuntimeABIDigest = llvmTargetRuntimeABIDigest target
  , llvmExpectedRuntimeABIProfile = llvmTargetRuntimeABIProfile target
  , llvmAuthorizedStrengthenings = Map.empty
  }

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
