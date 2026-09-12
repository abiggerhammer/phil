{-# LANGUAGE PatternSynonyms #-}

module Phil.Surface.Check
  ( RejectionClass (..)
  , SurfaceCheckError (..)
  , FieldInfo (..)
  , SurfaceShape (..)
  , InitialBinding (..)
  , PrimitiveArgumentDiscipline (..)
  , ProviderOutcomeSpec (..)
  , PrimitiveSemantics (..)
  , SurfaceCallableSignature (..)
  , SurfaceCallableInvocationWitness (..)
  , ReleaseRequirement (..)
  , ReleaseSemanticAccount (..)
  , ReleaseTransitionOutcome (..)
  , ReleaseResidue (..)
  , ReleaseTransitionContract (..)
  , ReleaseSelectionError (..)
  , selectReleaseTransition
  , SurfaceEnvironment (..)
  , SurfaceCheckResult (..)
  , SurfaceSemanticCheckResult (..)
  , ModuleName (..)
  , ModuleTable
  , ResolutionScope
  , ImportBinding (..)
  , ImportSelection (..)
  , ImportSpec (..)
  , ModuleResolutionError (..)
  , emptySurfaceEnvironment
  , checkSurfaceComponent
  , checkSurfaceComponentWithCallableSemantics
  , emptyModuleTable
  , emptyResolutionScope
  , declareModule
  , insertLocalDeclaration
  , resolveImports
  , lookupResolvedDeclaration
  , resolutionBindings
  ) where

import qualified ArchitectureImportKernel as ImportKernel
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Static (DeclarationIdentity)
import qualified Phil.Surface.Check.Engine as Engine
import Phil.Surface.Check.Preflight (preflightComponent)
import Phil.Surface.Check.Types
import Phil.Surface.Syntax
  ( Block (..)
  , BranchValue (..)
  , CaseArm (..)
  , Component (..)
  , FailureTarget (..)
  , Fallback (..)
  , Located (..)
  , Statement (..)
  , SurfaceExpression (..)
  , pattern InvokeExpression
  , SurfaceProposition (..)
  , SurfaceType (..)
  )

checkSurfaceComponent
  :: SurfaceEnvironment
  -> Located Component
  -> Either SurfaceCheckError SurfaceCheckResult
checkSurfaceComponent environment component =
  checkedSurfaceResult <$> checkSurfaceComponentWithCallableSemantics environment component

-- | Run the ordinary surface checker and, when the environment opts into the
-- CALL-019 semantic map, retain the exact complete contract for every explicit
-- source invocation. `Nothing` preserves the compatibility path used by callers
-- that have not yet been migrated. `Just contracts` is strict: a successful
-- shape-level invoke whose exact DeclarationKey has no semantic contract fails
-- closed rather than silently degrading to the old name/shape-only surface.
checkSurfaceComponentWithCallableSemantics
  :: SurfaceEnvironment
  -> Located Component
  -> Either SurfaceCheckError SurfaceSemanticCheckResult
checkSurfaceComponentWithCallableSemantics environment component = do
  preflightComponent environment component
  checked <- Engine.checkSurfaceComponent environment component
  invocations <- collectCallableInvocations environment component
  pure SurfaceSemanticCheckResult
    { checkedSurfaceResult = checked
    , checkedCallableInvocations = invocations
    }

collectCallableInvocations
  :: SurfaceEnvironment
  -> Located Component
  -> Either SurfaceCheckError (Set.Set SurfaceCallableInvocationWitness)
collectCallableInvocations environment component =
  collectBlock environment (componentBody (locatedValue component))

collectBlock
  :: SurfaceEnvironment
  -> Located Block
  -> Either SurfaceCheckError (Set.Set SurfaceCallableInvocationWitness)
collectBlock environment block =
  unionsM (map (collectStatement environment) (blockStatements (locatedValue block)))

collectStatement
  :: SurfaceEnvironment
  -> Located Statement
  -> Either SurfaceCheckError (Set.Set SurfaceCallableInvocationWitness)
collectStatement environment statement = case locatedValue statement of
  LetStatement _ expression -> collectExpression environment expression
  ReturnStatement expression -> collectExpression environment expression
  ExpressionStatement expression -> collectExpression environment expression

collectExpression
  :: SurfaceEnvironment
  -> Located SurfaceExpression
  -> Either SurfaceCheckError (Set.Set SurfaceCallableInvocationWitness)
collectExpression environment expression = case locatedValue expression of
  InvokeExpression name arguments -> do
    nested <- unionsM (map (collectExpression environment) arguments)
    case surfaceCallableSemanticContracts environment of
      Nothing -> Right nested
      Just contracts -> do
        signature <- maybe
          (Left SurfaceCheckError
            { surfaceErrorSpan = locatedSpan expression
            , surfaceErrorClass = UnknownCallable
            , surfaceErrorDetail =
                "callable disappeared before semantic invocation composition: " <> name
            })
          Right
          (Map.lookup name (surfaceCallables environment))
        let declarationKey = surfaceCallableDeclarationKey signature
        contract <- maybe
          (Left SurfaceCheckError
            { surfaceErrorSpan = locatedSpan expression
            , surfaceErrorClass = UnknownCallable
            , surfaceErrorDetail =
                "callable semantic contract missing for exact declaration identity"
            })
          Right
          (Map.lookup declarationKey contracts)
        Right (Set.insert
          SurfaceCallableInvocationWitness
            { surfaceInvocationDisplayName = name
            , surfaceInvocationDeclarationKey = declarationKey
            , surfaceInvocationSemanticContract = contract
            }
          nested)
  VariableExpression _ -> empty
  IntegerExpression _ -> empty
  BooleanExpression _ -> empty
  UnitExpression -> empty
  TupleExpression values -> expressions values
  CallExpression _ arguments -> expressions arguments
  FieldExpression base _ -> collectExpression environment base
  BinaryExpression _ left right -> expressions [left, right]
  ConstructExpression _ fields -> expressions (map snd fields)
  ReceiveExpression messageType endpoint -> unionsM
    [ collectType environment messageType
    , collectExpression environment endpoint
    ]
  ReceiveFrameExpression endpoint -> collectExpression environment endpoint
  RecognizeExpression _ raw -> collectExpression environment raw
  ValidateExpression _ context subject -> unionsM
    ( collectExpression environment subject
      : maybe [] (pure . collectExpression environment) context)
  SendExpression value endpoint -> expressions [value, endpoint]
  SendExactExpression value endpoint -> expressions [value, endpoint]
  ReceiveExactExpression count endpoint evidence -> unionsM
    ( [ collectExpression environment count
      , collectExpression environment endpoint
      ]
      <> maybe [] (pure . collectExpression environment) evidence)
  SelectExpression branch endpoint evidence -> unionsM
    ( collectBranchValue environment branch
      : collectExpression environment endpoint
      : maybe [] (pure . collectExpression environment) evidence)
  CommitReceiveExpression pending evidence -> expressions [pending, evidence]
  BorrowExpression owner _ body -> unionsM
    [ collectExpression environment owner
    , collectBlock environment body
    ]
  DecideExpression scrutinee arms -> unionsM
    (collectExpression environment scrutinee : map (collectArm environment) arms)
  OfferExpression endpoint arms -> unionsM
    (collectExpression environment endpoint : map (collectArm environment) arms)
  FailExpression target resource -> unionsM
    [ collectFailureTarget environment target
    , collectExpression environment resource
    ]
  CloseExpression endpoint -> collectExpression environment endpoint
  ReleaseExpression owner -> collectExpression environment owner
  AcceptExpression value acceptedType -> unionsM
    [ collectExpression environment value
    , collectType environment acceptedType
    ]
  ProveExpression proposition -> collectProposition environment proposition
  FallbackExpression primary fallback -> unionsM
    [ collectExpression environment primary
    , collectFallback environment fallback
    ]
  where
    empty = Right Set.empty
    expressions = unionsM . map (collectExpression environment)

collectType
  :: SurfaceEnvironment
  -> Located SurfaceType
  -> Either SurfaceCheckError (Set.Set SurfaceCallableInvocationWitness)
collectType environment surfaceType = case locatedValue surfaceType of
  SurfaceBytesType index -> collectExpression environment index
  SurfaceProofType proposition -> collectProposition environment proposition
  SurfaceValidatedType _ context subject -> unionsM
    [ collectExpression environment context
    , collectExpression environment subject
    ]
  SurfaceNamedType _ arguments ->
    unionsM (map (collectExpression environment) arguments)
  _ -> Right Set.empty

collectProposition
  :: SurfaceEnvironment
  -> Located SurfaceProposition
  -> Either SurfaceCheckError (Set.Set SurfaceCallableInvocationWitness)
collectProposition environment proposition = case locatedValue proposition of
  PropositionEqual left right -> binary left right
  PropositionNotEqual left right -> binary left right
  PropositionLessThan left right -> binary left right
  PropositionLessEqual left right -> binary left right
  PropositionGreaterThan left right -> binary left right
  PropositionGreaterEqual left right -> binary left right
  PropositionAtom _ arguments ->
    unionsM (map (collectExpression environment) arguments)
  PropositionConjunction left right -> propositions left right
  PropositionDisjunction left right -> propositions left right
  PropositionNegation inner -> collectProposition environment inner
  _ -> Right Set.empty
  where
    binary left right = unionsM
      [ collectExpression environment left
      , collectExpression environment right
      ]
    propositions left right = unionsM
      [ collectProposition environment left
      , collectProposition environment right
      ]

collectArm
  :: SurfaceEnvironment
  -> Located CaseArm
  -> Either SurfaceCheckError (Set.Set SurfaceCallableInvocationWitness)
collectArm environment arm =
  collectBlock environment (caseArmBody (locatedValue arm))

collectBranchValue
  :: SurfaceEnvironment
  -> BranchValue
  -> Either SurfaceCheckError (Set.Set SurfaceCallableInvocationWitness)
collectBranchValue environment =
  unionsM . map (collectExpression environment) . branchValueArguments

collectFailureTarget
  :: SurfaceEnvironment
  -> FailureTarget
  -> Either SurfaceCheckError (Set.Set SurfaceCallableInvocationWitness)
collectFailureTarget environment =
  unionsM . map (collectExpression environment) . failureTargetArguments

collectFallback
  :: SurfaceEnvironment
  -> Fallback
  -> Either SurfaceCheckError (Set.Set SurfaceCallableInvocationWitness)
collectFallback environment fallback = case fallback of
  FailFallback _ -> Right Set.empty
  RejectFallback expression -> collectExpression environment expression

unionsM
  :: [Either SurfaceCheckError (Set.Set SurfaceCallableInvocationWitness)]
  -> Either SurfaceCheckError (Set.Set SurfaceCallableInvocationWitness)
unionsM = fmap Set.unions . sequence

-- Phase 1 module/import resolution -------------------------------------------

-- | Human-facing module locator.  It is deliberately not a semantic identity.
newtype ModuleName = ModuleName { unModuleName :: Text }
  deriving (Eq, Ord, Show)

-- | A module exports names that locate already checked declaration identities.
-- No authority-bearing or assurance-bearing state lives in this interface.
data ModuleInterface = ModuleInterface
  { moduleInterfaceName :: ModuleName
  , moduleInterfaceExports :: Map.Map Text DeclarationIdentity
  }
  deriving (Eq, Show)

newtype ModuleTable = ModuleTable
  { moduleTableInterfaces :: Map.Map ModuleName ModuleInterface
  }
  deriving (Eq, Show)

-- | The complete semantic result of import resolution in this Phase 1 slice.
-- Imports can change only which DeclarationIdentity is available under which
-- local source name.
newtype ResolutionScope = ResolutionScope
  { resolutionBindings :: Map.Map Text DeclarationIdentity
  }
  deriving (Eq, Show)

-- | Select one exported declaration and optionally change only its local name.
data ImportBinding = ImportBinding
  { importExportName :: Text
  , importLocalName :: Text
  }
  deriving (Eq, Ord, Show)

data ImportSelection
  = ImportAll
  | ImportOnly [ImportBinding]
  deriving (Eq, Ord, Show)

data ImportSpec = ImportSpec
  { importModuleName :: ModuleName
  , importSelection :: ImportSelection
  }
  deriving (Eq, Ord, Show)

data ModuleResolutionError
  = DuplicateModule ModuleName
  | DuplicateModuleExport ModuleName Text
  | DuplicateResolutionName Text
  | UnknownModule ModuleName
  | UnknownModuleExport ModuleName Text
  deriving (Eq, Ord, Show)

emptyModuleTable :: ModuleTable
emptyModuleTable = ModuleTable Map.empty

emptyResolutionScope :: ResolutionScope
emptyResolutionScope = ResolutionScope Map.empty

declareModule
  :: ModuleName
  -> [(Text, DeclarationIdentity)]
  -> ModuleTable
  -> Either ModuleResolutionError ModuleTable
declareModule moduleName exports table
  | Map.member moduleName (moduleTableInterfaces table) =
      Left (DuplicateModule moduleName)
  | otherwise = do
      exportMap <- uniqueExports moduleName exports
      let interface = ModuleInterface
            { moduleInterfaceName = moduleName
            , moduleInterfaceExports = exportMap
            }
      Right table
        { moduleTableInterfaces =
            Map.insert moduleName interface (moduleTableInterfaces table)
        }

insertLocalDeclaration
  :: Text
  -> DeclarationIdentity
  -> ResolutionScope
  -> Either ModuleResolutionError ResolutionScope
insertLocalDeclaration localName declarationIdentity scope =
  case ImportKernel.decideImportResolutionByFacts
      True
      (not (Map.member localName (resolutionBindings scope))) of
    ImportKernel.ImportResolutionDecisionAccepted ->
      case ImportKernel.planImportedBinding localName declarationIdentity of
        ImportKernel.MkImportedBindingPlan plannedLocalName plannedIdentity ->
          Right scope
            { resolutionBindings =
                Map.insert plannedLocalName plannedIdentity (resolutionBindings scope)
            }
    ImportKernel.DuplicateResolutionNameDecision ->
      Left (DuplicateResolutionName localName)
    ImportKernel.UnknownSelectedExportDecision ->
      -- The selected-export fact is the literal True at this bridge.  Treat any
      -- impossible kernel/bridge disagreement as the existing fail-closed name
      -- collision rather than accepting an unvalidated binding.
      Left (DuplicateResolutionName localName)

resolveImports
  :: ModuleTable
  -> ResolutionScope
  -> [ImportSpec]
  -> Either ModuleResolutionError ResolutionScope
resolveImports table initialScope specs = foldl resolveImport (Right initialScope) specs
  where
    resolveImport accumulated spec = do
      scope <- accumulated
      interface <- maybe
        (Left (UnknownModule (importModuleName spec)))
        Right
        (Map.lookup (importModuleName spec) (moduleTableInterfaces table))
      bindings <- selectedBindings interface (importSelection spec)
      foldl insertBinding (Right scope) bindings

    insertBinding accumulated (localName, declarationIdentity) = do
      scope <- accumulated
      insertLocalDeclaration localName declarationIdentity scope

selectedBindings
  :: ModuleInterface
  -> ImportSelection
  -> Either ModuleResolutionError [(Text, DeclarationIdentity)]
selectedBindings interface selection = case selection of
  ImportAll -> Right (Map.toAscList (moduleInterfaceExports interface))
  ImportOnly bindings -> mapM resolveOne bindings
  where
    resolveOne binding =
      let selectedIdentity =
            Map.lookup (importExportName binding) (moduleInterfaceExports interface)
          selectedExportPresent = maybe False (const True) selectedIdentity
      in case ImportKernel.decideImportResolutionByFacts selectedExportPresent True of
        ImportKernel.ImportResolutionDecisionAccepted ->
          case selectedIdentity of
            Just declarationIdentity ->
              case ImportKernel.planImportedBinding
                  (importLocalName binding)
                  declarationIdentity of
                ImportKernel.MkImportedBindingPlan plannedLocalName plannedIdentity ->
                  Right (plannedLocalName, plannedIdentity)
            Nothing -> unknownExport binding
        ImportKernel.UnknownSelectedExportDecision -> unknownExport binding
        ImportKernel.DuplicateResolutionNameDecision ->
          -- The local-name-fresh fact is the literal True during selection.
          -- Fail closed through the native unknown-export diagnostic if an
          -- impossible bridge disagreement is ever observed.
          unknownExport binding

    unknownExport binding =
      Left (UnknownModuleExport
        (moduleInterfaceName interface)
        (importExportName binding))

lookupResolvedDeclaration :: Text -> ResolutionScope -> Maybe DeclarationIdentity
lookupResolvedDeclaration localName = Map.lookup localName . resolutionBindings

uniqueExports
  :: ModuleName
  -> [(Text, DeclarationIdentity)]
  -> Either ModuleResolutionError (Map.Map Text DeclarationIdentity)
uniqueExports moduleName = go Set.empty Map.empty
  where
    go _ exports [] = Right exports
    go seen exports ((exportName, declarationIdentity) : rest)
      | Set.member exportName seen = Left (DuplicateModuleExport moduleName exportName)
      | otherwise = go
          (Set.insert exportName seen)
          (Map.insert exportName declarationIdentity exports)
          rest
