{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler.SourceCore
  ( SourceCoreInventory (..)
  , CheckedSourceCoreCorrespondence (..)
  , SourceCoreCorrespondenceError (..)
  , verifySourceCoreCorrespondence
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import Phil.Compiler.SourceArchitecture
  ( CheckedSourceArchitecture (..)
  , sourceComponentDefinitionSemantics
  )
import Phil.Compiler.SourceBundle
  ( CheckedSourceBundle (..)
  , CheckedSourceUnit (..)
  )
import Phil.Core.Static
  ( ArchitectureInstanceIdentity
  , SemanticForm
  , checkedArchitectureIdentity
  )
import Phil.Core.Syntax (Control (..), Outcome (..))
import Phil.Surface.Check (SurfaceCheckResult (..))
import Phil.Surface.Syntax
import Phil.Systems.GenericLowering
  ( CoreSystemsBlock (..)
  , CoreSystemsFunction (..)
  , CoreSystemsOperation (..)
  , CoreSystemsProgram (..)
  , CoreSystemsTerminator (..)
  , coreSystemsProgramSemanticForm
  )

-- | Independently recoverable source/Core actions whose representation is
-- already unambiguous at the current INT-001 seam. This intentionally excludes
-- operations whose source-to-Core realization still needs a later refinement
-- (for example general provider calls and branch normalization).
data SourceCoreInventory = SourceCoreInventory
  { sourceCoreReceiveFrames :: Int
  , sourceCoreRecognitions :: Int
  , sourceCoreReceiveExact :: Int
  , sourceCoreSendExact :: Int
  , sourceCoreCommitReceives :: Int
  , sourceCoreReleases :: Int
  }
  deriving (Eq, Ord, Show)

data CheckedSourceCoreCorrespondence = CheckedSourceCoreCorrespondence
  { sourceCoreArchitectureIdentity :: ArchitectureInstanceIdentity
  , sourceCoreSourceDefinitions :: Map Text SemanticForm
  , sourceCoreProgramSemantics :: SemanticForm
  , sourceCoreSourceInventories :: Map Text SourceCoreInventory
  , sourceCoreCoreInventories :: Map Text SourceCoreInventory
  }
  deriving (Eq, Show)

data SourceCoreCorrespondenceError
  = SourceCoreDuplicateSourceFunction Text
  | SourceCoreFunctionSetMismatch (Set Text) (Set Text)
  | SourceCoreFunctionKeyMismatch Text Text
  | SourceCoreMissingSourceFunction Text
  | SourceCoreClosedOutcomeMissing Text Text
  | SourceCoreFailureTerminalMissing Text
  | SourceCoreReturnTerminalMissing Text
  | SourceCoreInventoryUnderrepresented Text SourceCoreInventory SourceCoreInventory
  deriving (Eq, Show)

-- | Bind one already checked ordinary-source Architecture occurrence to one
-- concrete CoreSystemsProgram only after independently reconstructible facts
-- agree. Source presentation names outside component/function identity, source
-- carrier paths, and witness/program labels are not consulted.
verifySourceCoreCorrespondence
  :: CheckedSourceArchitecture
  -> CoreSystemsProgram
  -> Either SourceCoreCorrespondenceError CheckedSourceCoreCorrespondence
verifySourceCoreCorrespondence architecture program = do
  sourceFunctions <- collectSourceFunctions
    (checkedSourceUnits (checkedSourceArchitectureBundle architecture))
  let coreFunctions = coreProgramFunctions program
      sourceKeys = Map.keysSet sourceFunctions
      coreKeys = Map.keysSet coreFunctions
  if sourceKeys == coreKeys
    then Right ()
    else Left (SourceCoreFunctionSetMismatch sourceKeys coreKeys)
  mapM_ requireEmbeddedFunctionKey (Map.toAscList coreFunctions)
  mapM_ (verifyFunction coreFunctions) (Map.toAscList sourceFunctions)
  let sourceDefinitions = Map.map
        (sourceComponentDefinitionSemantics . locatedValue . checkedSourceComponent)
        sourceFunctions
      sourceInventories = Map.map sourceInventory sourceFunctions
      coreInventories = Map.map coreInventory coreFunctions
  Right CheckedSourceCoreCorrespondence
    { sourceCoreArchitectureIdentity =
        checkedArchitectureIdentity (checkedSourceArchitectureRoot architecture)
    , sourceCoreSourceDefinitions = sourceDefinitions
    , sourceCoreProgramSemantics = coreSystemsProgramSemanticForm program
    , sourceCoreSourceInventories = sourceInventories
    , sourceCoreCoreInventories = coreInventories
    }
  where
    requireEmbeddedFunctionKey (mapKey, function)
      | mapKey == coreFunctionKey function = Right ()
      | otherwise = Left
          (SourceCoreFunctionKeyMismatch mapKey (coreFunctionKey function))

verifyFunction
  :: Map Text CoreSystemsFunction
  -> (Text, CheckedSourceUnit)
  -> Either SourceCoreCorrespondenceError ()
verifyFunction coreFunctions (functionName, sourceUnit) = do
  coreFunction <- maybe
    (Left (SourceCoreMissingSourceFunction functionName))
    Right
    (Map.lookup functionName coreFunctions)
  let sourceControls = checkedTerminalControls (checkedSourceResult sourceUnit)
      coreTerminals =
        [ coreBlockTerminator blockValue
        | blockValue <- Map.elems (coreFunctionBlocks coreFunction)
        ]
  mapM_ (verifyTerminal functionName coreTerminals) sourceControls
  let expectedInventory = sourceInventory sourceUnit
      actualInventory = coreInventory coreFunction
  if inventoryContains actualInventory expectedInventory
    then Right ()
    else Left
      (SourceCoreInventoryUnderrepresented
        functionName expectedInventory actualInventory)

verifyTerminal
  :: Text
  -> [CoreSystemsTerminator]
  -> Control
  -> Either SourceCoreCorrespondenceError ()
verifyTerminal functionName coreTerminals control = case control of
  Continue -> Right ()
  Return _
    | any isEnd coreTerminals -> Right ()
    | otherwise -> Left (SourceCoreReturnTerminalMissing functionName)
  Closed (Outcome outcome)
    | any (endsWith outcome) coreTerminals -> Right ()
    | otherwise -> Left (SourceCoreClosedOutcomeMissing functionName outcome)
  Failed _ _
    | any isFatal coreTerminals -> Right ()
    | otherwise -> Left (SourceCoreFailureTerminalMissing functionName)
  where
    isEnd terminator = case terminator of
      CoreSystemsEnd _ -> True
      _ -> False
    endsWith expected terminator = case terminator of
      CoreSystemsEnd actual -> actual == expected
      _ -> False
    isFatal terminator = case terminator of
      CoreSystemsFatal _ -> True
      _ -> False

collectSourceFunctions
  :: [CheckedSourceUnit]
  -> Either SourceCoreCorrespondenceError (Map Text CheckedSourceUnit)
collectSourceFunctions = go Map.empty
  where
    go functions [] = Right functions
    go functions (unit : rest) =
      let name = componentName (locatedValue (checkedSourceComponent unit))
      in if Map.member name functions
          then Left (SourceCoreDuplicateSourceFunction name)
          else go (Map.insert name unit functions) rest

sourceInventory :: CheckedSourceUnit -> SourceCoreInventory
sourceInventory =
  inventoryBlock . locatedValue . componentBody . locatedValue . checkedSourceComponent

coreInventory :: CoreSystemsFunction -> SourceCoreInventory
coreInventory function = foldl addInventory zeroInventory
  [ inventoryCoreBlock blockValue
  | blockValue <- Map.elems (coreFunctionBlocks function)
  ]

inventoryCoreBlock :: CoreSystemsBlock -> SourceCoreInventory
inventoryCoreBlock blockValue =
  foldl addInventory (inventoryCoreTerminator (coreBlockTerminator blockValue))
    (map inventoryCoreOperation (coreBlockOperations blockValue))

inventoryCoreOperation :: CoreSystemsOperation -> SourceCoreInventory
inventoryCoreOperation operation = case operation of
  CoreReceiveFrame {} -> zeroInventory { sourceCoreReceiveFrames = 1 }
  CoreCommitIngress {} -> zeroInventory { sourceCoreCommitReceives = 1 }
  CoreReleaseOwner {} -> zeroInventory { sourceCoreReleases = 1 }
  CoreRuntimeCall _ name _ _ _
    | name == "send_exact" -> zeroInventory { sourceCoreSendExact = 1 }
  _ -> zeroInventory

inventoryCoreTerminator :: CoreSystemsTerminator -> SourceCoreInventory
inventoryCoreTerminator terminator = case terminator of
  CoreSystemsRecognize {} -> zeroInventory { sourceCoreRecognitions = 1 }
  CoreSystemsReceiveExact {} -> zeroInventory { sourceCoreReceiveExact = 1 }
  _ -> zeroInventory

inventoryBlock :: Block -> SourceCoreInventory
inventoryBlock blockValue = foldl addInventory zeroInventory
  (map (inventoryStatement . locatedValue) (blockStatements blockValue))

inventoryStatement :: Statement -> SourceCoreInventory
inventoryStatement statement = case statement of
  LetStatement _ expression -> inventoryExpression (locatedValue expression)
  ReturnStatement expression -> inventoryExpression (locatedValue expression)
  ExpressionStatement expression -> inventoryExpression (locatedValue expression)

inventoryExpression :: SurfaceExpression -> SourceCoreInventory
inventoryExpression expression = case expression of
  VariableExpression _ -> zeroInventory
  IntegerExpression _ -> zeroInventory
  BooleanExpression _ -> zeroInventory
  UnitExpression -> zeroInventory
  TupleExpression values -> inventories (map (inventoryExpression . locatedValue) values)
  CallExpression _ arguments -> inventories (map (inventoryExpression . locatedValue) arguments)
  FieldExpression base _ -> inventoryExpression (locatedValue base)
  BinaryExpression _ left right -> inventories
    [inventoryExpression (locatedValue left), inventoryExpression (locatedValue right)]
  ConstructExpression _ fields -> inventories
    [ inventoryExpression (locatedValue value) | (_, value) <- fields ]
  ReceiveExpression messageType endpoint -> inventories
    [ inventoryType (locatedValue messageType)
    , inventoryExpression (locatedValue endpoint)
    ]
  ReceiveFrameExpression endpoint ->
    addInventory
      (zeroInventory { sourceCoreReceiveFrames = 1 })
      (inventoryExpression (locatedValue endpoint))
  RecognizeExpression _ raw ->
    addInventory
      (zeroInventory { sourceCoreRecognitions = 1 })
      (inventoryExpression (locatedValue raw))
  ValidateExpression _ context subject -> inventories
    (inventoryExpression (locatedValue subject)
      : maybe [] (pure . inventoryExpression . locatedValue) context)
  SendExpression value endpoint -> inventories
    [inventoryExpression (locatedValue value), inventoryExpression (locatedValue endpoint)]
  SendExactExpression value endpoint ->
    addInventory
      (zeroInventory { sourceCoreSendExact = 1 })
      (inventories
        [inventoryExpression (locatedValue value), inventoryExpression (locatedValue endpoint)])
  ReceiveExactExpression count endpoint evidence ->
    addInventory
      (zeroInventory { sourceCoreReceiveExact = 1 })
      (inventories
        ( [ inventoryExpression (locatedValue count)
          , inventoryExpression (locatedValue endpoint)
          ]
          <> maybe [] (pure . inventoryExpression . locatedValue) evidence))
  SelectExpression branch endpoint evidence -> inventories
    ( inventoryBranchValue branch
      : inventoryExpression (locatedValue endpoint)
      : maybe [] (pure . inventoryExpression . locatedValue) evidence)
  CommitReceiveExpression pending evidence ->
    addInventory
      (zeroInventory { sourceCoreCommitReceives = 1 })
      (inventories
        [ inventoryExpression (locatedValue pending)
        , inventoryExpression (locatedValue evidence)
        ])
  BorrowExpression owner _ body -> inventories
    [inventoryExpression (locatedValue owner), inventoryBlock (locatedValue body)]
  DecideExpression scrutinee arms -> inventories
    (inventoryExpression (locatedValue scrutinee)
      : map (inventoryCaseArm . locatedValue) arms)
  OfferExpression endpoint arms -> inventories
    (inventoryExpression (locatedValue endpoint)
      : map (inventoryCaseArm . locatedValue) arms)
  FailExpression target resource -> inventories
    [inventoryFailureTarget target, inventoryExpression (locatedValue resource)]
  CloseExpression endpoint -> inventoryExpression (locatedValue endpoint)
  ReleaseExpression owner ->
    addInventory
      (zeroInventory { sourceCoreReleases = 1 })
      (inventoryExpression (locatedValue owner))
  AcceptExpression value acceptedType -> inventories
    [ inventoryExpression (locatedValue value)
    , inventoryType (locatedValue acceptedType)
    ]
  ProveExpression proposition -> inventoryProposition (locatedValue proposition)
  FallbackExpression primary fallback -> inventories
    [inventoryExpression (locatedValue primary), inventoryFallback fallback]

inventoryType :: SurfaceType -> SourceCoreInventory
inventoryType surfaceType = case surfaceType of
  SurfaceBytesType index -> inventoryExpression (locatedValue index)
  SurfaceProofType proposition -> inventoryProposition (locatedValue proposition)
  SurfaceValidatedType _ context subject -> inventories
    [inventoryExpression (locatedValue context), inventoryExpression (locatedValue subject)]
  SurfaceNamedType _ arguments -> inventories (map (inventoryExpression . locatedValue) arguments)
  _ -> zeroInventory

inventoryProposition :: SurfaceProposition -> SourceCoreInventory
inventoryProposition proposition = case proposition of
  PropositionEqual left right -> binaryExpressionInventory left right
  PropositionNotEqual left right -> binaryExpressionInventory left right
  PropositionLessThan left right -> binaryExpressionInventory left right
  PropositionLessEqual left right -> binaryExpressionInventory left right
  PropositionGreaterThan left right -> binaryExpressionInventory left right
  PropositionGreaterEqual left right -> binaryExpressionInventory left right
  PropositionAtom _ arguments -> inventories (map (inventoryExpression . locatedValue) arguments)
  PropositionConjunction left right -> binaryPropositionInventory left right
  PropositionDisjunction left right -> binaryPropositionInventory left right
  PropositionNegation inner -> inventoryProposition (locatedValue inner)
  _ -> zeroInventory

inventoryCaseArm :: CaseArm -> SourceCoreInventory
inventoryCaseArm = inventoryBlock . locatedValue . caseArmBody

inventoryBranchValue :: BranchValue -> SourceCoreInventory
inventoryBranchValue = inventories . map (inventoryExpression . locatedValue) . branchValueArguments

inventoryFailureTarget :: FailureTarget -> SourceCoreInventory
inventoryFailureTarget = inventories . map (inventoryExpression . locatedValue) . failureTargetArguments

inventoryFallback :: Fallback -> SourceCoreInventory
inventoryFallback fallback = case fallback of
  FailFallback _ -> zeroInventory
  RejectFallback expression -> inventoryExpression (locatedValue expression)

binaryExpressionInventory
  :: Located SurfaceExpression
  -> Located SurfaceExpression
  -> SourceCoreInventory
binaryExpressionInventory left right = inventories
  [inventoryExpression (locatedValue left), inventoryExpression (locatedValue right)]

binaryPropositionInventory
  :: Located SurfaceProposition
  -> Located SurfaceProposition
  -> SourceCoreInventory
binaryPropositionInventory left right = inventories
  [inventoryProposition (locatedValue left), inventoryProposition (locatedValue right)]

inventoryContains :: SourceCoreInventory -> SourceCoreInventory -> Bool
inventoryContains actual expected = and
  [ sourceCoreReceiveFrames actual >= sourceCoreReceiveFrames expected
  , sourceCoreRecognitions actual >= sourceCoreRecognitions expected
  , sourceCoreReceiveExact actual >= sourceCoreReceiveExact expected
  , sourceCoreSendExact actual >= sourceCoreSendExact expected
  , sourceCoreCommitReceives actual >= sourceCoreCommitReceives expected
  , sourceCoreReleases actual >= sourceCoreReleases expected
  ]

inventories :: [SourceCoreInventory] -> SourceCoreInventory
inventories = foldl addInventory zeroInventory

addInventory :: SourceCoreInventory -> SourceCoreInventory -> SourceCoreInventory
addInventory left right = SourceCoreInventory
  { sourceCoreReceiveFrames = sourceCoreReceiveFrames left + sourceCoreReceiveFrames right
  , sourceCoreRecognitions = sourceCoreRecognitions left + sourceCoreRecognitions right
  , sourceCoreReceiveExact = sourceCoreReceiveExact left + sourceCoreReceiveExact right
  , sourceCoreSendExact = sourceCoreSendExact left + sourceCoreSendExact right
  , sourceCoreCommitReceives = sourceCoreCommitReceives left + sourceCoreCommitReceives right
  , sourceCoreReleases = sourceCoreReleases left + sourceCoreReleases right
  }

zeroInventory :: SourceCoreInventory
zeroInventory = SourceCoreInventory 0 0 0 0 0 0
