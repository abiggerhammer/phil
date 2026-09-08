{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler.SourceCorePolicy
  ( SourceCoreSite (..)
  , SourceCallDisposition (..)
  , SourceBranchDisposition (..)
  , SourceCoreCorrespondencePolicy (..)
  , SourceCorePolicyError (..)
  , emptySourceCoreCorrespondencePolicy
  , sourceCoreCallSites
  , sourceCoreBranchSites
  , verifySourceCorePolicy
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Compiler.SourceArchitecture (CheckedSourceArchitecture (..))
import Phil.Compiler.SourceBundle
  ( CheckedSourceBundle (..)
  , CheckedSourceUnit (..)
  )
import Phil.Surface.Syntax
import Phil.Systems.GenericLowering
  ( CoreSystemsBlock (..)
  , CoreSystemsFunction (..)
  , CoreSystemsOperation (..)
  , CoreSystemsProgram (..)
  , CoreSystemsTerminator (..)
  )

-- | Canonical semantic occurrence within one checked source component.
-- Calls and branch sites are numbered independently in preorder over the
-- span-free AST. Whitespace, comments, carrier paths, and SourceSpan do not
-- participate in the identity.
data SourceCoreSite = SourceCoreSite
  { sourceCoreSiteFunction :: Text
  , sourceCoreSiteIndex :: Int
  }
  deriving (Eq, Ord, Show)

-- | Independent expected disposition for one source call occurrence.
-- Qualified provider calls are required to remain exact runtime operations or
-- runtime choices with the same qualified name; ordinary calls may explicitly
-- map to differently named runtime machinery, a checked fact, or static erasure.
data SourceCallDisposition
  = SourceCallRuntimeOperation Text
  | SourceCallRuntimeChoice Text
  | SourceCallFact Text
  | SourceCallErasedStatic
  deriving (Eq, Ord, Show)

-- | Independent expected normalization for one source branch occurrence.
-- The map is source arm label -> exact Core successor block. For a Core
-- RuntimeChoice the labeled map must match exactly. For a binary Branch or
-- RuntimeCheck the successor set must match exactly.
data SourceBranchDisposition = SourceBranchDisposition
  { sourceBranchCoreBlock :: Text
  , sourceBranchTargets :: Map Text Text
  }
  deriving (Eq, Ord, Show)

data SourceCoreCorrespondencePolicy = SourceCoreCorrespondencePolicy
  { sourceCoreCallPolicy :: Map SourceCoreSite SourceCallDisposition
  , sourceCoreBranchPolicy :: Map SourceCoreSite SourceBranchDisposition
  }
  deriving (Eq, Show)

data SourceCorePolicyError
  = SourceCoreCallPolicyDomainMismatch (Set SourceCoreSite) (Set SourceCoreSite)
  | SourceCoreBranchPolicyDomainMismatch (Set SourceCoreSite) (Set SourceCoreSite)
  | SourceCoreCallSiteMissing SourceCoreSite
  | SourceCoreBranchSiteMissing SourceCoreSite
  | SourceCoreFunctionMissing SourceCoreSite
  | SourceCoreQualifiedCallDispositionInvalid SourceCoreSite Text SourceCallDisposition
  | SourceCoreRuntimeOperationMissing SourceCoreSite Text
  | SourceCoreRuntimeChoiceMissing SourceCoreSite Text
  | SourceCoreFactMissing SourceCoreSite Text
  | SourceCoreBranchLabelMismatch SourceCoreSite (Set Text) (Set Text)
  | SourceCoreBranchBlockMissing SourceCoreSite Text
  | SourceCoreBranchNotNormalized SourceCoreSite Text
  | SourceCoreBranchTargetsMismatch SourceCoreSite (Map Text Text) (Map Text Text)
  deriving (Eq, Show)

emptySourceCoreCorrespondencePolicy :: SourceCoreCorrespondencePolicy
emptySourceCoreCorrespondencePolicy = SourceCoreCorrespondencePolicy Map.empty Map.empty

verifySourceCorePolicy
  :: SourceCoreCorrespondencePolicy
  -> CheckedSourceArchitecture
  -> CoreSystemsProgram
  -> Either SourceCorePolicyError ()
verifySourceCorePolicy policy architecture program = do
  let callSites = sourceCoreCallSites architecture
      branchSites = sourceCoreBranchSites architecture
      expectedCallDomain = Map.keysSet callSites
      suppliedCallDomain = Map.keysSet (sourceCoreCallPolicy policy)
      expectedBranchDomain = Map.keysSet branchSites
      suppliedBranchDomain = Map.keysSet (sourceCoreBranchPolicy policy)
  if expectedCallDomain == suppliedCallDomain
    then Right ()
    else Left (SourceCoreCallPolicyDomainMismatch expectedCallDomain suppliedCallDomain)
  if expectedBranchDomain == suppliedBranchDomain
    then Right ()
    else Left (SourceCoreBranchPolicyDomainMismatch expectedBranchDomain suppliedBranchDomain)
  mapM_ (verifyCall callSites program) (Map.toAscList (sourceCoreCallPolicy policy))
  mapM_ (verifyBranch branchSites program) (Map.toAscList (sourceCoreBranchPolicy policy))

sourceCoreCallSites :: CheckedSourceArchitecture -> Map SourceCoreSite Text
sourceCoreCallSites architecture = Map.fromList
  [ (SourceCoreSite functionName index, callName)
  | unit <- checkedSourceUnits (checkedSourceArchitectureBundle architecture)
  , let component = locatedValue (checkedSourceComponent unit)
        functionName = componentName component
  , (index, callName) <- zip [0 ..] (callNamesBlock (locatedValue (componentBody component)))
  ]

sourceCoreBranchSites :: CheckedSourceArchitecture -> Map SourceCoreSite (Set Text)
sourceCoreBranchSites architecture = Map.fromList
  [ (SourceCoreSite functionName index, labels)
  | unit <- checkedSourceUnits (checkedSourceArchitectureBundle architecture)
  , let component = locatedValue (checkedSourceComponent unit)
        functionName = componentName component
  , (index, labels) <- zip [0 ..] (branchLabelsBlock (locatedValue (componentBody component)))
  ]

verifyCall
  :: Map SourceCoreSite Text
  -> CoreSystemsProgram
  -> (SourceCoreSite, SourceCallDisposition)
  -> Either SourceCorePolicyError ()
verifyCall callSites program (site, disposition) = do
  sourceName <- maybe (Left (SourceCoreCallSiteMissing site)) Right (Map.lookup site callSites)
  function <- coreFunction site program
  requireQualifiedExact site sourceName disposition
  case disposition of
    SourceCallRuntimeOperation expectedName
      | hasRuntimeOperation expectedName function -> Right ()
      | otherwise -> Left (SourceCoreRuntimeOperationMissing site expectedName)
    SourceCallRuntimeChoice expectedName
      | hasRuntimeChoice expectedName function -> Right ()
      | otherwise -> Left (SourceCoreRuntimeChoiceMissing site expectedName)
    SourceCallFact factKey
      | Map.member factKey (coreProgramFacts program) -> Right ()
      | otherwise -> Left (SourceCoreFactMissing site factKey)
    SourceCallErasedStatic -> Right ()

verifyBranch
  :: Map SourceCoreSite (Set Text)
  -> CoreSystemsProgram
  -> (SourceCoreSite, SourceBranchDisposition)
  -> Either SourceCorePolicyError ()
verifyBranch branchSites program (site, disposition) = do
  sourceLabels <- maybe (Left (SourceCoreBranchSiteMissing site)) Right
    (Map.lookup site branchSites)
  let expectedLabels = Map.keysSet (sourceBranchTargets disposition)
  if sourceLabels == expectedLabels
    then Right ()
    else Left (SourceCoreBranchLabelMismatch site sourceLabels expectedLabels)
  function <- coreFunction site program
  blockValue <- maybe
    (Left (SourceCoreBranchBlockMissing site (sourceBranchCoreBlock disposition)))
    Right
    (Map.lookup (sourceBranchCoreBlock disposition) (coreFunctionBlocks function))
  let expectedTargets = sourceBranchTargets disposition
  case coreBlockTerminator blockValue of
    CoreSystemsRuntimeChoice _ _ _ actualTargets
      | actualTargets == expectedTargets -> Right ()
      | otherwise -> Left (SourceCoreBranchTargetsMismatch site expectedTargets actualTargets)
    CoreSystemsBranch _ yesTarget noTarget ->
      compareUnlabeledTargets site expectedTargets [yesTarget, noTarget]
    CoreSystemsRuntimeCheck _ _ yesTarget noTarget ->
      compareUnlabeledTargets site expectedTargets [yesTarget, noTarget]
    _ -> Left (SourceCoreBranchNotNormalized site (sourceBranchCoreBlock disposition))

compareUnlabeledTargets
  :: SourceCoreSite
  -> Map Text Text
  -> [Text]
  -> Either SourceCorePolicyError ()
compareUnlabeledTargets site expectedTargets actualTargets =
  let expectedSet = Set.fromList (Map.elems expectedTargets)
      actualSet = Set.fromList actualTargets
      actualMap = Map.fromSet (const "<unlabeled-core-successor>") actualSet
      expectedMap = Map.fromSet (const "<expected-core-successor>") expectedSet
  in if expectedSet == actualSet && Map.size expectedTargets == length actualTargets
      then Right ()
      else Left (SourceCoreBranchTargetsMismatch site expectedMap actualMap)

coreFunction
  :: SourceCoreSite
  -> CoreSystemsProgram
  -> Either SourceCorePolicyError CoreSystemsFunction
coreFunction site program = maybe
  (Left (SourceCoreFunctionMissing site))
  Right
  (Map.lookup (sourceCoreSiteFunction site) (coreProgramFunctions program))

requireQualifiedExact
  :: SourceCoreSite
  -> Text
  -> SourceCallDisposition
  -> Either SourceCorePolicyError ()
requireQualifiedExact site sourceName disposition
  | not (Text.isInfixOf "." sourceName) = Right ()
  | otherwise = case disposition of
      SourceCallRuntimeOperation target
        | target == sourceName -> Right ()
      SourceCallRuntimeChoice target
        | target == sourceName -> Right ()
      _ -> Left (SourceCoreQualifiedCallDispositionInvalid site sourceName disposition)

hasRuntimeOperation :: Text -> CoreSystemsFunction -> Bool
hasRuntimeOperation expectedName function = any matches
  [ operation
  | blockValue <- Map.elems (coreFunctionBlocks function)
  , operation <- coreBlockOperations blockValue
  ]
  where
    matches operation = case operation of
      CoreRuntimeCall _ actualName _ _ _ -> actualName == expectedName
      _ -> False

hasRuntimeChoice :: Text -> CoreSystemsFunction -> Bool
hasRuntimeChoice expectedName function = any matches
  [ coreBlockTerminator blockValue
  | blockValue <- Map.elems (coreFunctionBlocks function)
  ]
  where
    matches terminator = case terminator of
      CoreSystemsRuntimeChoice actualName _ _ _ -> actualName == expectedName
      _ -> False

callNamesBlock :: Block -> [Text]
callNamesBlock blockValue = concatMap (callNamesStatement . locatedValue)
  (blockStatements blockValue)

callNamesStatement :: Statement -> [Text]
callNamesStatement statement = case statement of
  LetStatement _ expression -> callNamesExpression (locatedValue expression)
  ReturnStatement expression -> callNamesExpression (locatedValue expression)
  ExpressionStatement expression -> callNamesExpression (locatedValue expression)

callNamesExpression :: SurfaceExpression -> [Text]
callNamesExpression expression = case expression of
  VariableExpression _ -> []
  IntegerExpression _ -> []
  BooleanExpression _ -> []
  UnitExpression -> []
  TupleExpression values -> calls values
  CallExpression name arguments -> name : calls arguments
  FieldExpression base _ -> callNamesExpression (locatedValue base)
  BinaryExpression _ left right -> calls [left, right]
  ConstructExpression _ fields -> calls (map snd fields)
  ReceiveExpression messageType endpoint -> callNamesType (locatedValue messageType) <> calls [endpoint]
  ReceiveFrameExpression endpoint -> calls [endpoint]
  RecognizeExpression _ raw -> calls [raw]
  ValidateExpression _ context subject -> calls (subject : maybe [] pure context)
  SendExpression value endpoint -> calls [value, endpoint]
  SendExactExpression value endpoint -> calls [value, endpoint]
  ReceiveExactExpression count endpoint evidence -> calls ([count, endpoint] <> maybe [] pure evidence)
  SelectExpression branch endpoint evidence ->
    callNamesBranchValue branch <> calls (endpoint : maybe [] pure evidence)
  CommitReceiveExpression pending evidence -> calls [pending, evidence]
  BorrowExpression owner _ body -> calls [owner] <> callNamesBlock (locatedValue body)
  DecideExpression scrutinee arms -> calls [scrutinee] <> concatMap (callNamesCaseArm . locatedValue) arms
  OfferExpression endpoint arms -> calls [endpoint] <> concatMap (callNamesCaseArm . locatedValue) arms
  FailExpression target resource -> callNamesFailureTarget target <> calls [resource]
  CloseExpression endpoint -> calls [endpoint]
  ReleaseExpression owner -> calls [owner]
  AcceptExpression value acceptedType -> calls [value] <> callNamesType (locatedValue acceptedType)
  ProveExpression proposition -> callNamesProposition (locatedValue proposition)
  FallbackExpression primary fallback -> callNamesExpression (locatedValue primary) <> callNamesFallback fallback
  where
    calls = concatMap (callNamesExpression . locatedValue)

callNamesType :: SurfaceType -> [Text]
callNamesType surfaceType = case surfaceType of
  SurfaceBytesType index -> callNamesExpression (locatedValue index)
  SurfaceProofType proposition -> callNamesProposition (locatedValue proposition)
  SurfaceValidatedType _ context subject ->
    callNamesExpression (locatedValue context) <> callNamesExpression (locatedValue subject)
  SurfaceNamedType _ arguments -> concatMap (callNamesExpression . locatedValue) arguments
  _ -> []

callNamesProposition :: SurfaceProposition -> [Text]
callNamesProposition proposition = case proposition of
  PropositionEqual left right -> calls [left, right]
  PropositionNotEqual left right -> calls [left, right]
  PropositionLessThan left right -> calls [left, right]
  PropositionLessEqual left right -> calls [left, right]
  PropositionGreaterThan left right -> calls [left, right]
  PropositionGreaterEqual left right -> calls [left, right]
  PropositionAtom _ arguments -> calls arguments
  PropositionConjunction left right -> propositions [left, right]
  PropositionDisjunction left right -> propositions [left, right]
  PropositionNegation inner -> propositions [inner]
  _ -> []
  where
    calls = concatMap (callNamesExpression . locatedValue)
    propositions = concatMap (callNamesProposition . locatedValue)

callNamesCaseArm :: CaseArm -> [Text]
callNamesCaseArm = callNamesBlock . locatedValue . caseArmBody

callNamesBranchValue :: BranchValue -> [Text]
callNamesBranchValue = concatMap (callNamesExpression . locatedValue) . branchValueArguments

callNamesFailureTarget :: FailureTarget -> [Text]
callNamesFailureTarget = concatMap (callNamesExpression . locatedValue) . failureTargetArguments

callNamesFallback :: Fallback -> [Text]
callNamesFallback fallback = case fallback of
  FailFallback _ -> []
  RejectFallback expression -> callNamesExpression (locatedValue expression)

branchLabelsBlock :: Block -> [Set Text]
branchLabelsBlock blockValue = concatMap (branchLabelsStatement . locatedValue)
  (blockStatements blockValue)

branchLabelsStatement :: Statement -> [Set Text]
branchLabelsStatement statement = case statement of
  LetStatement _ expression -> branchLabelsExpression (locatedValue expression)
  ReturnStatement expression -> branchLabelsExpression (locatedValue expression)
  ExpressionStatement expression -> branchLabelsExpression (locatedValue expression)

branchLabelsExpression :: SurfaceExpression -> [Set Text]
branchLabelsExpression expression = case expression of
  VariableExpression _ -> []
  IntegerExpression _ -> []
  BooleanExpression _ -> []
  UnitExpression -> []
  TupleExpression values -> branches values
  CallExpression _ arguments -> branches arguments
  FieldExpression base _ -> branchLabelsExpression (locatedValue base)
  BinaryExpression _ left right -> branches [left, right]
  ConstructExpression _ fields -> branches (map snd fields)
  ReceiveExpression _ endpoint -> branches [endpoint]
  ReceiveFrameExpression endpoint -> branches [endpoint]
  RecognizeExpression _ raw -> branches [raw]
  ValidateExpression _ context subject -> branches (subject : maybe [] pure context)
  SendExpression value endpoint -> branches [value, endpoint]
  SendExactExpression value endpoint -> branches [value, endpoint]
  ReceiveExactExpression count endpoint evidence -> branches ([count, endpoint] <> maybe [] pure evidence)
  SelectExpression branch endpoint evidence ->
    branchLabelsBranchValue branch <> branches (endpoint : maybe [] pure evidence)
  CommitReceiveExpression pending evidence -> branches [pending, evidence]
  BorrowExpression owner _ body -> branches [owner] <> branchLabelsBlock (locatedValue body)
  DecideExpression scrutinee arms ->
    Set.fromList (map (casePatternLabel . caseArmPattern . locatedValue) arms)
      : branches [scrutinee]
      <> concatMap (branchLabelsCaseArm . locatedValue) arms
  OfferExpression endpoint arms ->
    Set.fromList (map (casePatternLabel . caseArmPattern . locatedValue) arms)
      : branches [endpoint]
      <> concatMap (branchLabelsCaseArm . locatedValue) arms
  FailExpression _ resource -> branches [resource]
  CloseExpression endpoint -> branches [endpoint]
  ReleaseExpression owner -> branches [owner]
  AcceptExpression value _ -> branches [value]
  ProveExpression _ -> []
  FallbackExpression primary fallback ->
    Set.fromList ["primary", "fallback"]
      : branchLabelsExpression (locatedValue primary)
      <> branchLabelsFallback fallback
  where
    branches = concatMap (branchLabelsExpression . locatedValue)

branchLabelsCaseArm :: CaseArm -> [Set Text]
branchLabelsCaseArm = branchLabelsBlock . locatedValue . caseArmBody

branchLabelsBranchValue :: BranchValue -> [Set Text]
branchLabelsBranchValue = concatMap (branchLabelsExpression . locatedValue) . branchValueArguments

branchLabelsFallback :: Fallback -> [Set Text]
branchLabelsFallback fallback = case fallback of
  FailFallback _ -> []
  RejectFallback expression -> branchLabelsExpression (locatedValue expression)
