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
  , ScalarType (..)
  , renderScalarType
  , scalarLiteralInRange
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
  , Pattern (..)
  , Statement (..)
  , SurfaceExpression (..)
  , SurfaceFile (..)
  , SurfaceType (..)
  )
import Phil.Systems
  ( BlockId (..)
  , CompilationProfile (CertifiedRelease)
  , LoweringLedger (..)
  , ScalarDataflowError
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
  , verifyScalarDataflow
  , verifySystemsArtifact
  )

data RunnableCompileError
  = RunnableParseError ParseDiagnostic
  | RunnableSurfaceCheckError SurfaceCheckError
  | RunnableFragmentError Text
  | RunnableSystemsVerificationError SystemsVerificationError
  | RunnableScalarDataflowError ScalarDataflowError
  | RunnableLLVMVerificationError LLVMVerificationError
  deriving (Eq, Show)

data RunnableResult
  = RunnableUnit
  | RunnableScalar ScalarType
  deriving (Eq, Show)

data RunnableProgram = RunnableProgram
  { runnableSourceDigest :: Digest
  , runnableResult :: RunnableResult
  , runnableSystemsArtifact :: SystemsArtifact
  , runnableLLVMArtifact :: LLVMArtifact
  }
  deriving (Eq, Show)

data LoweredBody = LoweredBody
  { loweredValues :: Map.Map ValueId SystemsValue
  , loweredOperations :: [SystemsOp]
  , loweredTerminator :: SystemsTerminator
  , loweredTraceRelation :: [Text]
  }

data ScalarLowerState = ScalarLowerState
  { scalarBindings :: Map.Map Text ValueId
  , scalarValues :: Map.Map ValueId SystemsValue
  , scalarOperations :: [SystemsOp]
  , scalarSyntheticIndex :: Int
  }

compileRunnable :: Text -> Text -> Either RunnableCompileError RunnableProgram
compileRunnable sourceName source = do
  surfaceFile <- mapLeft RunnableParseError (parseSurfaceFile sourceName source)
  component <- requireSingleComponent surfaceFile
  result <- requireRunnableHeader component
  _ <- mapLeft RunnableSurfaceCheckError $
    checkSurfaceComponent (runnableSurfaceEnvironment result) component
  let sourceDigest = digestText source
  (systemsArtifact, systemsContext) <- buildRunnableSystems sourceDigest result component
  mapLeft RunnableSystemsVerificationError $
    verifySystemsArtifact systemsContext systemsArtifact
  mapLeft RunnableScalarDataflowError $
    verifyScalarDataflow systemsArtifact
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
      RunnableScalar (ScalarUInt width) -> TyUInt width
      RunnableScalar ScalarBool -> TyUInt 1

requireSingleComponent :: SurfaceFile -> Either RunnableCompileError (Located Component)
requireSingleComponent (SurfaceFile [component]) = Right component
requireSingleComponent (SurfaceFile components) =
  Left (RunnableFragmentError
    ("runnable fragment requires exactly one component; found "
      <> Text.pack (show (length components))))

requireRunnableHeader :: Located Component -> Either RunnableCompileError RunnableResult
requireRunnableHeader locatedComponent = do
  let component = locatedValue locatedComponent
  unless (componentName component == "main") $
    fragment "runnable fragment requires the component name `main`"
  unless (null (componentParameters component)) $
    fragment "runnable fragment does not yet support component parameters"
  case componentProvides component of
    Just provided -> case locatedValue provided of
      SurfaceUnitType -> Right RunnableUnit
      SurfaceUIntType 32 -> Right (RunnableScalar (ScalarUInt 32))
      SurfaceUIntType width ->
        fragment
          ("native runnable main currently supports U32 scalar returns; found U"
            <> Text.pack (show width))
      _ -> fragment "runnable main currently requires `provides Unit` or `provides U32`"
    Nothing -> fragment "runnable main requires an explicit provides type"
  where
    fragment = Left . RunnableFragmentError

buildRunnableSystems
  :: Digest
  -> RunnableResult
  -> Located Component
  -> Either RunnableCompileError (SystemsArtifact, SystemsVerificationContext)
buildRunnableSystems sourceDigest result locatedComponent = do
  body <- case result of
    RunnableUnit -> lowerUnitBody (componentBody (locatedValue locatedComponent))
    RunnableScalar scalarType ->
      lowerScalarBody scalarType (componentBody (locatedValue locatedComponent))
  let entryBlock = BlockId "entry"
      blockValue = SystemsBlock
        { systemsBlockId = entryBlock
        , systemsBlockOps = loweredOperations body
        , systemsBlockTerminator = loweredTerminator body
        }
      function = SystemsFunction
        { systemsFunctionName = "main"
        , systemsFunctionEntry = entryBlock
        , systemsFunctionValues = loweredValues body
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
        { stageContractId = "surface-to-systems/runnable-main/v3"
        , stageSourceArtifactDigest = sourceDigest
        , stageTargetArtifactDigest = targetDigest
        , stageFacts = []
        , stageInvariants = Map.empty
        , stageRequiredEdges = []
        , stageDerivedObligations = []
        , stageAssumptions = []
        , stageTraceRelation = loweredTraceRelation body
        , stageResourceFailureRelation = ["no resources; no failure edges"]
        }
      artifact = SystemsArtifact
        { systemsArtifactProgram = program
        , systemsArtifactStageContract = stageContract
        , systemsArtifactLoweringLedger = loweringLedger
        }
      assuranceLedger = emptyLedger
      coreDigest = digestText "phil-core/runnable-main-fragment/v3"
      systemsTarget = "systems-ir/runnable-main/v3"
      systemsProfile = "systems/certified-release/runnable-main/v3"
      validityContext = Map.singleton "fragment" "runnable-main/v3"
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
  Right (artifact, systemsContext)

lowerUnitBody :: Located Block -> Either RunnableCompileError LoweredBody
lowerUnitBody locatedBlock =
  case blockStatements (locatedValue locatedBlock) of
    [statement] -> case locatedValue statement of
      ReturnStatement expression
        | locatedValue expression == UnitExpression -> Right LoweredBody
            { loweredValues = Map.empty
            , loweredOperations = []
            , loweredTerminator = TermEnd "return-unit"
            , loweredTraceRelation = ["return unit -> normal completion"]
            }
      _ -> fragment "Unit runnable main body must be exactly `return unit`"
    _ -> fragment "Unit runnable main body must be exactly `return unit`"
  where
    fragment = Left . RunnableFragmentError

lowerScalarBody
  :: ScalarType
  -> Located Block
  -> Either RunnableCompileError LoweredBody
lowerScalarBody scalarType locatedBlock = do
  (finalState, returnValue) <- lowerScalarStatements
    scalarType
    emptyScalarLowerState
    (blockStatements (locatedValue locatedBlock))
  Right LoweredBody
    { loweredValues = scalarValues finalState
    , loweredOperations = scalarOperations finalState
    , loweredTerminator = TermReturnScalar returnValue
    , loweredTraceRelation =
        [ "checked surface scalar bindings -> Systems SSA values"
        , "return " <> renderScalarType scalarType <> " -> typed native scalar return"
        ]
    }

emptyScalarLowerState :: ScalarLowerState
emptyScalarLowerState = ScalarLowerState
  { scalarBindings = Map.empty
  , scalarValues = Map.empty
  , scalarOperations = []
  , scalarSyntheticIndex = 0
  }

lowerScalarStatements
  :: ScalarType
  -> ScalarLowerState
  -> [Located Statement]
  -> Either RunnableCompileError (ScalarLowerState, ValueId)
lowerScalarStatements _ _ [] =
  fragment "scalar runnable main must end with a return statement"
lowerScalarStatements scalarType state (statement : rest) =
  case locatedValue statement of
    LetStatement patternValue expression -> do
      next <- lowerScalarLet scalarType state patternValue expression
      lowerScalarStatements scalarType next rest
    ReturnStatement expression -> do
      unless (null rest) $
        fragment "scalar return must be the final statement in runnable main"
      lowerScalarReturn scalarType state expression
    ExpressionStatement _ ->
      fragment "scalar runnable main currently supports only `let` bindings and `return`"

lowerScalarLet
  :: ScalarType
  -> ScalarLowerState
  -> Located Pattern
  -> Located SurfaceExpression
  -> Either RunnableCompileError ScalarLowerState
lowerScalarLet scalarType state patternValue expression =
  case locatedValue patternValue of
    TuplePattern _ -> fragment "scalar runnable `let` requires a single-name binding"
    BindPattern name -> do
      unless (Map.notMember name (scalarBindings state)) $
        fragment ("scalar binding is already defined: " <> name)
      case locatedValue expression of
        IntegerExpression value -> do
          literal <- scalarIntegerLiteral scalarType value
          defineNamedScalar name literal state
        VariableExpression source -> do
          sourceValue <- lookupScalarBinding source state
          Right state
            { scalarBindings = Map.insert name sourceValue (scalarBindings state) }
        _ -> fragment
          "scalar runnable `let` currently accepts an integer literal or scalar variable"

lowerScalarReturn
  :: ScalarType
  -> ScalarLowerState
  -> Located SurfaceExpression
  -> Either RunnableCompileError (ScalarLowerState, ValueId)
lowerScalarReturn scalarType state expression =
  case locatedValue expression of
    VariableExpression name -> do
      valueId <- lookupScalarBinding name state
      Right (state, valueId)
    IntegerExpression value -> do
      literal <- scalarIntegerLiteral scalarType value
      defineSyntheticScalar literal state
    _ -> fragment
      "scalar runnable return currently accepts an integer literal or scalar variable"

lookupScalarBinding :: Text -> ScalarLowerState -> Either RunnableCompileError ValueId
lookupScalarBinding name state =
  case Map.lookup name (scalarBindings state) of
    Nothing -> fragment ("unknown scalar binding during lowering: " <> name)
    Just valueId -> Right valueId

scalarIntegerLiteral :: ScalarType -> Integer -> Either RunnableCompileError ScalarLiteral
scalarIntegerLiteral scalarType value =
  case scalarType of
    ScalarUInt width -> do
      let literal = ScalarUIntLiteral width value
      unless (scalarLiteralInRange literal) $
        fragment
          (renderScalarType scalarType <> " return literal is outside its mathematical range")
      Right literal
    ScalarBool -> fragment "boolean scalar lowering does not accept integer literals"

defineNamedScalar
  :: Text
  -> ScalarLiteral
  -> ScalarLowerState
  -> Either RunnableCompileError ScalarLowerState
defineNamedScalar name literal state = do
  let valueId = ValueId name
  unless (Map.notMember valueId (scalarValues state)) $
    fragment ("Systems scalar value identity is already defined: " <> name)
  Right (appendScalarDefinition name valueId literal state)

defineSyntheticScalar
  :: ScalarLiteral
  -> ScalarLowerState
  -> Either RunnableCompileError (ScalarLowerState, ValueId)
defineSyntheticScalar literal state =
  let (valueId, nextIndex) = freshSyntheticValue state
      next = appendScalarDefinition "" valueId literal state
        { scalarSyntheticIndex = nextIndex }
  in Right (next, valueId)

freshSyntheticValue :: ScalarLowerState -> (ValueId, Int)
freshSyntheticValue state = choose (scalarSyntheticIndex state)
  where
    choose index =
      let candidate = ValueId ("return.value." <> Text.pack (show index))
      in if Map.member candidate (scalarValues state)
          then choose (index + 1)
          else (candidate, index + 1)

appendScalarDefinition
  :: Text
  -> ValueId
  -> ScalarLiteral
  -> ScalarLowerState
  -> ScalarLowerState
appendScalarDefinition sourceName valueId literal state = state
  { scalarBindings =
      if Text.null sourceName
        then scalarBindings state
        else Map.insert sourceName valueId (scalarBindings state)
  , scalarValues = Map.insert valueId scalarValue (scalarValues state)
  , scalarOperations = scalarOperations state <> [OpScalarLiteral valueId literal]
  }
  where
    scalarType = case literal of
      ScalarBoolLiteral _ -> ScalarBool
      ScalarUIntLiteral width _ -> ScalarUInt width
    scalarValue = SystemsValue
      { systemsValueId = valueId
      , systemsValueRole = TypedScalar scalarType
      , systemsStorageIdentity = Nothing
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

fragment :: Text -> Either RunnableCompileError a
fragment = Left . RunnableFragmentError

mapLeft :: (left -> mapped) -> Either left right -> Either mapped right
mapLeft transform = either (Left . transform) Right
