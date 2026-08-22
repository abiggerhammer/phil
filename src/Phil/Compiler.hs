{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler
  ( RunnableCompileError (..)
  , RunnableResult (..)
  , RunnableProgram (..)
  , compileRunnable
  , compileRunnableUnit
  , renderRunnableCompileError
  ) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance
import Phil.Core.Scalar
  ( ScalarLiteral (..)
  , scalarLiteralInRange
  , scalarLiteralType
  , renderScalarLiteral
  )
import Phil.Core.Static (emptyStaticContext)
import Phil.Core.Syntax (Ty (TyUInt, TyUnit))
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
  , SystemsOp (OpScalarLiteral)
  , SystemsProgram (..)
  , SystemsTerminator (TermEnd, TermReturnScalar)
  , SystemsValue (..)
  , SystemsValueRole (TypedScalar)
  , SystemsVerificationContext (..)
  , SystemsVerificationError
  , ValueId (..)
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

data RunnableResult
  = RunnableUnit
  | RunnableScalar ScalarLiteral
  deriving (Eq, Show)

data RunnableProgram = RunnableProgram
  { runnableSourceDigest :: Digest
  , runnableResult :: RunnableResult
  , runnableSystemsArtifact :: SystemsArtifact
  , runnableLLVMArtifact :: LLVMArtifact
  }
  deriving (Eq, Show)

compileRunnable :: Text -> Text -> Either RunnableCompileError RunnableProgram
compileRunnable sourceName source = do
  surfaceFile <- mapLeft RunnableParseError (parseSurfaceFile sourceName source)
  component <- requireSingleComponent surfaceFile
  result <- requireRunnableShape component
  _ <- mapLeft RunnableSurfaceCheckError $
    checkSurfaceComponent (runnableSurfaceEnvironment result) component
  let sourceDigest = digestText source
      (systemsArtifact, systemsContext) = buildRunnableSystems sourceDigest result
  mapLeft RunnableSystemsVerificationError $
    verifySystemsArtifact systemsContext systemsArtifact
  let llvmArtifact = lowerSystemsConservative phase0LLVMTarget systemsArtifact
      llvmContext = runnableLLVMContext systemsContext phase0LLVMTarget
  mapLeft RunnableLLVMVerificationError $
    verifyLLVMEmission llvmContext systemsArtifact llvmArtifact
  Right RunnableProgram
    { runnableSourceDigest = sourceDigest
    , runnableResult = result
    , runnableSystemsArtifact = systemsArtifact
    , runnableLLVMArtifact = llvmArtifact
    }

compileRunnableUnit :: Text -> Text -> Either RunnableCompileError RunnableProgram
compileRunnableUnit sourceName source = do
  runnable <- compileRunnable sourceName source
  case runnableResult runnable of
    RunnableUnit -> Right runnable
    RunnableScalar _ ->
      Left (RunnableFragmentError "Unit-only compiler entry point received a scalar program")

renderRunnableCompileError :: RunnableCompileError -> Text
renderRunnableCompileError compileError = case compileError of
  RunnableFragmentError detail -> detail
  _ -> Text.pack (show compileError)

runnableSurfaceEnvironment :: RunnableResult -> SurfaceEnvironment
runnableSurfaceEnvironment result =
  (emptySurfaceEnvironment emptyStaticContext)
    { surfaceExpectedProvides = Just expectedType }
  where
    expectedType = case result of
      RunnableUnit -> TyUnit
      RunnableScalar (ScalarUIntLiteral width _) -> TyUInt width
      RunnableScalar (ScalarBoolLiteral _) -> TyUInt 1

requireSingleComponent :: SurfaceFile -> Either RunnableCompileError (Located Component)
requireSingleComponent (SurfaceFile [component]) = Right component
requireSingleComponent (SurfaceFile components) =
  Left (RunnableFragmentError
    ("runnable fragment requires exactly one component; found "
      <> Text.pack (show (length components))))

requireRunnableShape :: Located Component -> Either RunnableCompileError RunnableResult
requireRunnableShape locatedComponent = do
  let component = locatedValue locatedComponent
  unless (componentName component == "main") $
    fragment "runnable fragment requires the component name `main`"
  unless (null (componentParameters component)) $
    fragment "runnable fragment does not yet support component parameters"
  case (componentProvides component, blockStatements (locatedValue (componentBody component))) of
    (Just provided, [statement]) ->
      case (locatedValue provided, locatedValue statement) of
        (SurfaceUnitType, ReturnStatement expression)
          | locatedValue expression == UnitExpression -> Right RunnableUnit
        (SurfaceUIntType 32, ReturnStatement expression) ->
          case locatedValue expression of
            IntegerExpression value -> do
              let literal = ScalarUIntLiteral 32 value
              unless (scalarLiteralInRange literal) $
                fragment "U32 return literal is outside 0..4294967295"
              Right (RunnableScalar literal)
            _ -> fragment "U32 runnable main must return an integer literal"
        (SurfaceUIntType width, _) ->
          fragment
            ("native runnable main currently supports U32 scalar returns; found U"
              <> Text.pack (show width))
        (SurfaceUnitType, _) ->
          fragment "Unit runnable main body must be exactly `return unit`"
        _ -> fragment "runnable main currently requires `provides Unit` or `provides U32`"
    (_, statements)
      | length statements /= 1 ->
          fragment "runnable main body must contain exactly one return statement"
    _ -> fragment "runnable main requires an explicit provides type"
  where
    fragment = Left . RunnableFragmentError

buildRunnableSystems
  :: Digest
  -> RunnableResult
  -> (SystemsArtifact, SystemsVerificationContext)
buildRunnableSystems sourceDigest result = (artifact, systemsContext)
  where
    entryBlock = BlockId "entry"
    returnValueId = ValueId "return.value"
    (values, operations, terminator, traceRelation) = case result of
      RunnableUnit ->
        ( Map.empty
        , []
        , TermEnd "return-unit"
        , ["return unit -> normal completion"]
        )
      RunnableScalar literal ->
        ( Map.singleton returnValueId SystemsValue
            { systemsValueId = returnValueId
            , systemsValueRole = TypedScalar (scalarLiteralType literal)
            , systemsStorageIdentity = Nothing
            }
        , [OpScalarLiteral returnValueId literal]
        , TermReturnScalar returnValueId
        , ["return " <> renderScalarLiteral literal <> " -> typed native scalar return"]
        )
    blockValue = SystemsBlock
      { systemsBlockId = entryBlock
      , systemsBlockOps = operations
      , systemsBlockTerminator = terminator
      }
    function = SystemsFunction
      { systemsFunctionName = "main"
      , systemsFunctionEntry = entryBlock
      , systemsFunctionValues = values
      , systemsFunctionBlocks = Map.singleton entryBlock blockValue
      }
    program = SystemsProgram
      { systemsProgramName = "runnable-main"
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
      { stageContractId = "surface-to-systems/runnable-main/v2"
      , stageSourceArtifactDigest = sourceDigest
      , stageTargetArtifactDigest = targetDigest
      , stageFacts = []
      , stageInvariants = Map.empty
      , stageRequiredEdges = []
      , stageDerivedObligations = []
      , stageAssumptions = []
      , stageTraceRelation = traceRelation
      , stageResourceFailureRelation = ["no resources; no failure edges"]
      }
    artifact = SystemsArtifact
      { systemsArtifactProgram = program
      , systemsArtifactStageContract = stageContract
      , systemsArtifactLoweringLedger = loweringLedger
      }
    assuranceLedger = emptyLedger
    coreDigest = digestText "phil-core/runnable-main-fragment/v2"
    systemsTarget = "systems-ir/runnable-main/v2"
    systemsProfile = "systems/certified-release/runnable-main/v2"
    validityContext = Map.singleton "fragment" "runnable-main/v2"
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
