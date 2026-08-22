{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler
  ( RunnableCompileError (..)
  , SourceProjectionError (..)
  , RunnableResult (..)
  , RunnableProgram (..)
  , compileRunnable
  , compileRunnableUnit
  , verifyRunnableSourceProjection
  , renderRunnableCompileError
  ) where

import Control.Monad (forM_, unless, when)
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
  , scalarLiteralType
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
  | RunnableSourceProjectionError SourceProjectionError
  | RunnableLLVMVerificationError LLVMVerificationError
  deriving (Eq, Show)

data SourceProjectionError
  = SourceProjectionFunctionSetMismatch [Text]
  | SourceProjectionBlockSetMismatch [BlockId]
  | SourceProjectionNamedLiteralMismatch ValueId ScalarLiteral (Maybe ScalarLiteral)
  | SourceProjectionUnexpectedLiteralDefinition ValueId ScalarLiteral
  | SourceProjectionScalarValueSetMismatch [ValueId] [ValueId]
  | SourceProjectionScalarTypeMismatch ValueId ScalarType (Maybe ScalarType)
  | SourceProjectionReturnTargetMismatch ValueId SystemsTerminator
  | SourceProjectionReturnLiteralMismatch ScalarLiteral SystemsTerminator
  | SourceProjectionUnitTerminatorMismatch SystemsTerminator
  | SourceProjectionUnsupportedSource Text
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

data ExpectedScalarReturn
  = ExpectedReturnValue ValueId
  | ExpectedReturnLiteral ScalarLiteral
  deriving (Eq, Show)

data ExpectedScalarProjection = ExpectedScalarProjection
  { expectedNamedLiterals :: Map.Map ValueId ScalarLiteral
  , expectedScalarReturn :: ExpectedScalarReturn
  }
  deriving (Eq, Show)

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
  mapLeft RunnableSourceProjectionError $
    verifySourceProjection result component systemsArtifact
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

verifyRunnableSourceProjection
  :: Text
  -> Text
  -> SystemsArtifact
  -> Either RunnableCompileError ()
verifyRunnableSourceProjection sourceName source systemsArtifact = do
  surfaceFile <- mapLeft RunnableParseError (parseSurfaceFile sourceName source)
  component <- requireSingleComponent surfaceFile
  result <- requireRunnableHeader component
  _ <- mapLeft RunnableSurfaceCheckError $
    checkSurfaceComponent (runnableSurfaceEnvironment result) component
  mapLeft RunnableScalarDataflowError $
    verifyScalarDataflow systemsArtifact
  mapLeft RunnableSourceProjectionError $
    verifySourceProjection result component systemsArtifact

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
          (renderScalarType scalarType <> " scalar literal is outside its mathematical range")
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
      advanced = state { scalarSyntheticIndex = nextIndex }
      next = appendScalarDefinition "" valueId literal advanced
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
    scalarValue = SystemsValue
      { systemsValueId = valueId
      , systemsValueRole = TypedScalar (scalarLiteralType literal)
      , systemsStorageIdentity = Nothing
      }

verifySourceProjection
  :: RunnableResult
  -> Located Component
  -> SystemsArtifact
  -> Either SourceProjectionError ()
verifySourceProjection result locatedComponent artifact = do
  function <- requireProjectionMain artifact
  blockValue <- requireProjectionEntryBlock function
  case result of
    RunnableUnit -> verifyUnitProjection function blockValue
    RunnableScalar scalarType -> do
      expected <- expectedScalarProjection
        scalarType
        (blockStatements (locatedValue (componentBody (locatedValue locatedComponent))))
      verifyScalarProjection scalarType expected function blockValue

requireProjectionMain :: SystemsArtifact -> Either SourceProjectionError SystemsFunction
requireProjectionMain artifact =
  case Map.toAscList (systemsProgramFunctions (systemsArtifactProgram artifact)) of
    [("main", function)] -> Right function
    entries -> Left (SourceProjectionFunctionSetMismatch (map fst entries))

requireProjectionEntryBlock :: SystemsFunction -> Either SourceProjectionError SystemsBlock
requireProjectionEntryBlock function =
  case Map.toAscList (systemsFunctionBlocks function) of
    [(blockId, blockValue)]
      | blockId == systemsFunctionEntry function -> Right blockValue
    entries -> Left (SourceProjectionBlockSetMismatch (map fst entries))

verifyUnitProjection
  :: SystemsFunction
  -> SystemsBlock
  -> Either SourceProjectionError ()
verifyUnitProjection function blockValue = do
  let scalarIds =
        [ valueId
        | (valueId, value) <- Map.toAscList (systemsFunctionValues function)
        , TypedScalar _ <- [systemsValueRole value]
        ]
      definitions = scalarLiteralDefinitions blockValue
  unless (null scalarIds && Map.null definitions) $
    Left (SourceProjectionScalarValueSetMismatch [] scalarIds)
  unless (systemsBlockTerminator blockValue == TermEnd "return-unit") $
    Left (SourceProjectionUnitTerminatorMismatch (systemsBlockTerminator blockValue))

verifyScalarProjection
  :: ScalarType
  -> ExpectedScalarProjection
  -> SystemsFunction
  -> SystemsBlock
  -> Either SourceProjectionError ()
verifyScalarProjection scalarType expected function blockValue = do
  let definitions = scalarLiteralDefinitions blockValue
      typedValues = Map.fromList
        [ (valueId, actualType)
        | (valueId, value) <- Map.toAscList (systemsFunctionValues function)
        , TypedScalar actualType <- [systemsValueRole value]
        ]
      definitionIds = Map.keysSet definitions
      typedIds = Map.keysSet typedValues
  unless (definitionIds == typedIds) $
    Left (SourceProjectionScalarValueSetMismatch
      (Set.toAscList definitionIds)
      (Set.toAscList typedIds))
  forM_ (Map.toAscList typedValues) $ \(valueId, actualType) ->
    unless (actualType == scalarType) $
      Left (SourceProjectionScalarTypeMismatch valueId scalarType (Just actualType))
  forM_ (Map.toAscList (expectedNamedLiterals expected)) $ \(valueId, expectedLiteral) ->
    case Map.lookup valueId definitions of
      Just actualLiteral | actualLiteral == expectedLiteral -> pure ()
      actual -> Left (SourceProjectionNamedLiteralMismatch valueId expectedLiteral actual)
  case expectedScalarReturn expected of
    ExpectedReturnValue expectedValue -> do
      unless (systemsBlockTerminator blockValue == TermReturnScalar expectedValue) $
        Left (SourceProjectionReturnTargetMismatch
          expectedValue
          (systemsBlockTerminator blockValue))
      rejectUnexpectedDefinitions
        (Map.keysSet (expectedNamedLiterals expected))
        definitions
    ExpectedReturnLiteral expectedLiteral ->
      case systemsBlockTerminator blockValue of
        TermReturnScalar returnedValue -> do
          case Map.lookup returnedValue definitions of
            Just actualLiteral | actualLiteral == expectedLiteral -> pure ()
            _ -> Left (SourceProjectionReturnLiteralMismatch
              expectedLiteral
              (systemsBlockTerminator blockValue))
          let allowed = Set.insert returnedValue
                (Map.keysSet (expectedNamedLiterals expected))
          rejectUnexpectedDefinitions allowed definitions
        other -> Left (SourceProjectionReturnLiteralMismatch expectedLiteral other)
  where
    rejectUnexpectedDefinitions allowed definitions =
      case
        [ (valueId, literal)
        | (valueId, literal) <- Map.toAscList definitions
        , Set.notMember valueId allowed
        ] of
          [] -> pure ()
          (valueId, literal) : _ ->
            Left (SourceProjectionUnexpectedLiteralDefinition valueId literal)

scalarLiteralDefinitions :: SystemsBlock -> Map.Map ValueId ScalarLiteral
scalarLiteralDefinitions blockValue = Map.fromList
  [ (output, literal)
  | OpScalarLiteral output literal <- systemsBlockOps blockValue
  ]

expectedScalarProjection
  :: ScalarType
  -> [Located Statement]
  -> Either SourceProjectionError ExpectedScalarProjection
expectedScalarProjection scalarType = go Map.empty Map.empty
  where
    go _ _ [] = unsupported "scalar source projection has no return"
    go bindings definitions (statement : rest) =
      case locatedValue statement of
        LetStatement patternValue expression ->
          case locatedValue patternValue of
            TuplePattern _ -> unsupported "scalar source projection does not support tuple bindings"
            BindPattern name -> do
              when (Map.member name bindings) $
                unsupported ("duplicate scalar source binding: " <> name)
              case locatedValue expression of
                IntegerExpression value -> do
                  literal <- projectionIntegerLiteral scalarType value
                  let valueId = ValueId name
                  go
                    (Map.insert name valueId bindings)
                    (Map.insert valueId literal definitions)
                    rest
                VariableExpression source ->
                  case Map.lookup source bindings of
                    Nothing -> unsupported ("unknown scalar source alias: " <> source)
                    Just sourceValue ->
                      go (Map.insert name sourceValue bindings) definitions rest
                _ -> unsupported "unsupported scalar source binding expression"
        ReturnStatement expression -> do
          unless (null rest) $
            unsupported "scalar source return is not final"
          expectedReturn <- case locatedValue expression of
            VariableExpression name ->
              case Map.lookup name bindings of
                Nothing -> unsupported ("unknown scalar source return: " <> name)
                Just valueId -> Right (ExpectedReturnValue valueId)
            IntegerExpression value ->
              ExpectedReturnLiteral <$> projectionIntegerLiteral scalarType value
            _ -> unsupported "unsupported scalar source return expression"
          Right ExpectedScalarProjection
            { expectedNamedLiterals = definitions
            , expectedScalarReturn = expectedReturn
            }
        ExpressionStatement _ ->
          unsupported "unsupported scalar source expression statement"

projectionIntegerLiteral
  :: ScalarType
  -> Integer
  -> Either SourceProjectionError ScalarLiteral
projectionIntegerLiteral scalarType value = case scalarType of
  ScalarUInt width ->
    let literal = ScalarUIntLiteral width value
    in if scalarLiteralInRange literal
        then Right literal
        else unsupported "scalar source literal is outside its mathematical range"
  ScalarBool -> unsupported "boolean source projection does not accept integer literals"

unsupported :: Text -> Either SourceProjectionError a
unsupported = Left . SourceProjectionUnsupportedSource

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
