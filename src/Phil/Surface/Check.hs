{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.Check
  ( RejectionClass (..)
  , SurfaceCheckError (..)
  , FieldInfo (..)
  , SurfaceShape (..)
  , InitialBinding (..)
  , PrimitiveSemantics (..)
  , SurfaceEnvironment (..)
  , SurfaceCheckResult (..)
  , emptySurfaceEnvironment
  , checkSurfaceComponent
  ) where

import Control.Monad (foldM, unless, when)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context
  ( CheckError
  , ResourceContext (..)
  , consumeLinear
  , endSharedLoan
  , ensureComplete
  , insertBinding
  , joinContinuing
  , startSharedLoan
  , useBinding
  )
import Phil.Core.Decision
  ( checkDecisionCertificate
  , proposeDecisionCertificate
  )
import Phil.Core.Focusing
  ( FocusMechanism (..)
  , FocusPlan (..)
  , FocusedRequirement (..)
  , FocusingError
  , checkBranchExhaustiveness
  , elaborateRefTermAs
  , focusProposition
  )
import Phil.Core.Recognition
  ( ParsedWitness
  , PendingRawView
  , RecognitionError
  , RecognitionFailure
  , beginRawLoan
  , commitContext
  , commitReceive
  , failPendingRecognition
  , receiveFrame
  , receiveFrameContext
  , receivePendingSpec
  , trustedRecognitionFailure
  , trustedRecognitionSuccess
  )
import Phil.Core.Refinement
  ( evidenceProposition
  , normalizeProposition
  , normalizeRefTerm
  )
import Phil.Core.Session
  ( MessageSpec (..)
  , SessionError
  , SessionStep (..)
  , closeEndpoint
  , exposeSessionHead
  , offerEndpoint
  , receiveEndpoint
  , selectEndpoint
  , sendEndpoint
  )
import Phil.Core.SortCheck (refSortOfTy)
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax
  ( Branch (..)
  , Control (..)
  , FrameId (..)
  , GrammarId (..)
  , Mode (..)
  , Name (..)
  , Outcome (..)
  , PendingRecvSpec (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Session (..)
  , Ty (..)
  , Value (..)
  )
import Phil.Core.Value
  ( EqualityBoundary (..)
  , ValueError (..)
  , ValueResult (..)
  , checkValue
  , checkValueUsing
  , compareTypes
  )
import Phil.Surface.Elaborate
  ( ElaborationEnv
  , ElaborationError
  , elaborateProposition
  , elaborateRefTerm
  , elaborateType
  , emptyElaborationEnv
  , withProjectionSort
  )
import Phil.Surface.Syntax
  ( Block (..)
  , BranchValue (..)
  , CaseArm (..)
  , CasePattern (..)
  , Component (..)
  , FailureTarget (..)
  , Fallback (..)
  , Located (..)
  , Parameter (..)
  , Pattern (..)
  , SourcePoint (..)
  , SourceSpan (..)
  , Statement (..)
  , SurfaceExpression (..)
  , SurfaceProposition
  , SurfaceType (..)
  )

-- | Stable semantic rejection categories for conformance.  Wording may change;
-- this classification is intended to remain compatible across checkers.
data RejectionClass
  = StructuralUse
  | LinearCompletion
  | SessionAction
  | BranchExhaustiveness
  | IllegalProjection
  | MissingEvidence
  | ExplicitTransport
  | IncompatibleBranchResidue
  | ControlAfterTerminal
  | RecognitionProvenance
  | BorrowEscape
  | OpaqueProof
  | UncheckedArithmetic
  | UnknownPrimitive
  | TypeMismatch
  deriving (Eq, Ord, Show)

data SurfaceCheckError = SurfaceCheckError
  { surfaceErrorSpan :: SourceSpan
  , surfaceErrorClass :: RejectionClass
  , surfaceErrorDetail :: Text
  }
  deriving (Eq, Show)

data FieldInfo = FieldInfo
  { fieldType :: Ty
  , fieldSort :: RefSort
  , fieldAlias :: Maybe RefTerm
  }
  deriving (Eq, Show)

data SurfaceShape
  = PlainShape
  | RecordShape Text (Map Text FieldInfo)
  | OwnedBytesShape RefTerm
  | PendingRawShape PendingRawView
  | LegacyRawShape GrammarId FrameId
  | BorrowedViewShape Name
  | ParsedShape ParsedWitness Text
  | LegacyParsedShape GrammarId FrameId Text
  | ExternalParsedShape Text FrameId
  | RecognitionFailureShape RecognitionFailure
  | LegacyRecognitionFailureShape GrammarId FrameId
  | FixtureRawShape FrameId
  | DecisionShape DecisionKind
  | UncheckedArithmeticShape
  | ForgedParsedShape
  deriving (Eq, Show)

data InitialBinding = InitialBinding
  { initialMode :: Mode
  , initialType :: Ty
  , initialShape :: SurfaceShape
  }
  deriving (Eq, Show)

data PrimitiveSemantics
  = PrimitiveSupportedVersions
  | PrimitiveSha256
  | PrimitiveShouldCancel
  | PrimitiveChooseSupported
  | PrimitiveStore
  | PrimitiveFixtureBytes
  | PrimitiveUncheckedU32Add
  | PrimitiveNewCancellationScope
  | PrimitiveAllocateLinearBuffer
  | PrimitiveRecordUploadId
  | PrimitiveConsumeBeginPolicyEvidence
  | PrimitiveUse
  | PrimitiveInspect
  | PrimitiveAuthorizeStore
  | PrimitiveDelegate
  | PrimitiveContinueCommonState
  | PrimitiveHandlePayload
  deriving (Eq, Ord, Show)

data SurfaceEnvironment = SurfaceEnvironment
  { surfaceStaticContext :: StaticContext
  , surfaceInitialBindings :: Map Text InitialBinding
  , surfacePrimitives :: Map Text PrimitiveSemantics
  , surfaceSelectRequirements :: Map Text [Proposition]
  , surfaceReceiveExactRequirement :: Maybe Proposition
  , surfaceTerminalAllowances :: Map Outcome (Set Text)
  , surfaceExpectedProvides :: Maybe Ty
  , surfaceLegacyReceiveFrameRaw :: Bool
  }
  deriving (Eq, Show)

data SurfaceCheckResult = SurfaceCheckResult
  { checkedComponentName :: Text
  , checkedTerminalControls :: [Control]
  }
  deriving (Eq, Show)

emptySurfaceEnvironment :: StaticContext -> SurfaceEnvironment
emptySurfaceEnvironment staticContext = SurfaceEnvironment
  { surfaceStaticContext = staticContext
  , surfaceInitialBindings = Map.empty
  , surfacePrimitives = Map.empty
  , surfaceSelectRequirements = Map.empty
  , surfaceReceiveExactRequirement = Nothing
  , surfaceTerminalAllowances = Map.empty
  , surfaceExpectedProvides = Nothing
  , surfaceLegacyReceiveFrameRaw = False
  }

data BindingMeta = BindingMeta
  { bindingMode :: Mode
  , bindingType :: Ty
  , bindingShape :: SurfaceShape
  }
  deriving (Eq, Show)

data SurfaceState = SurfaceState
  { stateCore :: CheckState
  , stateBindings :: Map Text BindingMeta
  , stateFresh :: Int
  , stateFrame :: Int
  , stateActiveEndpoint :: Maybe Text
  }
  deriving (Eq, Show)

data ScalarValue = ScalarValue
  { scalarMode :: Mode
  , scalarType :: Ty
  , scalarShape :: SurfaceShape
  }
  deriving (Eq, Show)

data RuntimeValue
  = RuntimeScalar ScalarValue
  | RuntimeTuple [RuntimeValue]
  | RuntimeUnit
  deriving (Eq, Show)

data PathControl
  = PathContinue
  | PathReturn Ty
  | PathClosed Outcome
  | PathFailed Text Text
  deriving (Eq, Show)

data SurfacePath = SurfacePath
  { pathControl :: PathControl
  , pathState :: SurfaceState
  , pathValue :: Maybe RuntimeValue
  }
  deriving (Eq, Show)

data DecisionKind
  = BooleanDecision
  | ChooseSupportedDecision
  | RecognitionDecision ParsedWitness RecognitionFailure Text
  | LegacyRecognitionDecision GrammarId FrameId Text
  | ValidationDecision Text Name Name
  | DigestDecision Proposition
  | StoreDecision
  deriving (Eq, Show)

checkSurfaceComponent
  :: SurfaceEnvironment
  -> Located Component
  -> Either SurfaceCheckError SurfaceCheckResult
checkSurfaceComponent environment locatedComponent = do
  initial <- initializeState environment (locatedValue locatedComponent)
  checkProvides environment initial (locatedValue locatedComponent)
  paths <- checkBlock environment initial (componentBody (locatedValue locatedComponent))
  finalPaths <- mapM (finalizePath environment (locatedSpan locatedComponent)) paths
  pure SurfaceCheckResult
    { checkedComponentName = componentName (locatedValue locatedComponent)
    , checkedTerminalControls = map toCoreControl finalPaths
    }

initializeState :: SurfaceEnvironment -> Component -> Either SurfaceCheckError SurfaceState
initializeState environment component = do
  withInitial <- foldM insertInitial emptySurfaceState (Map.toAscList (surfaceInitialBindings environment))
  foldM insertParameter withInitial (componentParameters component)
  where
    insertInitial state (name, binding) =
      insertBindingMeta syntheticSpan name
        (BindingMeta (initialMode binding) (initialType binding) (initialShape binding)) state

    -- Architecture-supplied bindings are authoritative for untyped role-local
    -- witness parameters.  A later declaration pass will resolve aliases such
    -- as Server[Upload] before this checker boundary.
    insertParameter state locatedParameter =
      let parameter = locatedValue locatedParameter
          name = parameterName parameter
      in case Map.lookup name (stateBindings state) of
          Just _ -> Right state
          Nothing ->
            case parameterType parameter of
              Nothing -> throw locatedParameter TypeMismatch "untyped parameter has no architecture-supplied binding"
              Just surfaceTy -> do
                (mode, ty, shape) <- resolveSurfaceType environment state surfaceTy
                insertBindingMeta (locatedSpan locatedParameter) name (BindingMeta mode ty shape) state

emptySurfaceState :: SurfaceState
emptySurfaceState = SurfaceState
  { stateCore = emptyCheckState
  , stateBindings = Map.empty
  , stateFresh = 0
  , stateFrame = 0
  , stateActiveEndpoint = Nothing
  }

checkProvides :: SurfaceEnvironment -> SurfaceState -> Component -> Either SurfaceCheckError ()
checkProvides environment state component =
  case (surfaceExpectedProvides environment, componentProvides component) of
    (Nothing, _) -> Right ()
    (Just expected, Just surfaceTy) -> do
      (_, actual, _) <- resolveSurfaceType environment state surfaceTy
      unless (compareTypes actual expected == DefinitionallyEqual) $
        throw surfaceTy TypeMismatch "provides type disagrees with the architecture contract"
    (Just _, Nothing) -> Left SurfaceCheckError
      { surfaceErrorSpan = locatedSpan (componentBody component)
      , surfaceErrorClass = TypeMismatch
      , surfaceErrorDetail = "component is missing its required provides clause"
      }

checkBlock :: SurfaceEnvironment -> SurfaceState -> Located Block -> Either SurfaceCheckError [SurfacePath]
checkBlock environment state locatedBlock =
  checkStatements environment [continuePath state] (blockStatements (locatedValue locatedBlock))

checkStatements
  :: SurfaceEnvironment
  -> [SurfacePath]
  -> [Located Statement]
  -> Either SurfaceCheckError [SurfacePath]
checkStatements _ paths [] = Right paths
checkStatements environment paths (statement : rest) = do
  let continuing = filter ((== PathContinue) . pathControl) paths
      stopped = filter ((/= PathContinue) . pathControl) paths
  when (null continuing) $
    throw statement ControlAfterTerminal "statement occurs after all incoming paths terminated"
  advanced <- concat <$> mapM (checkStatement environment statement) continuing
  checkStatements environment (stopped ++ advanced) rest

checkStatement
  :: SurfaceEnvironment
  -> Located Statement
  -> SurfacePath
  -> Either SurfaceCheckError [SurfacePath]
checkStatement environment locatedStatement path =
  case locatedValue locatedStatement of
    LetStatement pattern' expression -> do
      evaluated <- evalExpression environment (pathState path) expression
      bound <- mapM (bindPath pattern') evaluated
      joinExclusive (locatedSpan locatedStatement) bound
    ReturnStatement expression -> do
      evaluated <- evalExpression environment (pathState path) expression
      mapM (returnPath environment (locatedSpan locatedStatement)) evaluated
    ExpressionStatement expression -> do
      evaluated <- evalExpression environment (pathState path) expression
      discarded <- mapM (discardValue (locatedSpan locatedStatement)) evaluated
      joinExclusive (locatedSpan locatedStatement) discarded

bindPath :: Located Pattern -> SurfacePath -> Either SurfaceCheckError SurfacePath
bindPath _ path | pathControl path /= PathContinue = Right path
bindPath pattern' path =
  case pathValue path of
    Nothing -> throw pattern' TypeMismatch "expression produced no bindable result"
    Just value -> do
      next <- bindPattern pattern' value (pathState path)
      Right (continuePath next)

returnPath :: SurfaceEnvironment -> SourceSpan -> SurfacePath -> Either SurfaceCheckError SurfacePath
returnPath _ _ path | pathControl path /= PathContinue = Right path
returnPath environment span' path = do
  let state = pathState path
      ty = maybe TyUnit runtimeType (pathValue path)
  ensureTerminalState environment span' Nothing state
  Right path { pathControl = PathReturn ty, pathValue = Nothing }

runtimeType :: RuntimeValue -> Ty
runtimeType RuntimeUnit = TyUnit
runtimeType (RuntimeScalar scalar) = scalarType scalar
runtimeType (RuntimeTuple values) = TyOpaque ("Tuple[" <> Text.pack (show (length values)) <> "]")

discardValue :: SourceSpan -> SurfacePath -> Either SurfaceCheckError SurfacePath
discardValue _ path | pathControl path /= PathContinue = Right path
discardValue span' path =
  case pathValue path of
    Just value | restrictedRuntimeValue value -> Left SurfaceCheckError
      { surfaceErrorSpan = span'
      , surfaceErrorClass = LinearCompletion
      , surfaceErrorDetail = "restricted expression result is discarded"
      }
    _ -> Right path { pathValue = Nothing }

restrictedRuntimeValue :: RuntimeValue -> Bool
restrictedRuntimeValue RuntimeUnit = False
restrictedRuntimeValue (RuntimeScalar scalar) = scalarMode scalar /= Unrestricted
restrictedRuntimeValue (RuntimeTuple values) = any restrictedRuntimeValue values

continuePath :: SurfaceState -> SurfacePath
continuePath state = SurfacePath PathContinue state Nothing

valuePath :: SurfaceState -> RuntimeValue -> SurfacePath
valuePath state value = SurfacePath PathContinue state (Just value)

evalExpression
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalExpression environment state locatedExpression =
  case locatedValue locatedExpression of
    VariableExpression name -> do
      (scalar, next) <- moveVariable locatedExpression name state
      Right [valuePath next (RuntimeScalar scalar)]
    IntegerExpression literal -> Right [valuePath state (RuntimeScalar
      (ScalarValue Unrestricted (TyOpaque ("Integer[" <> Text.pack (show literal) <> "]")) PlainShape))]
    BooleanExpression _ -> Right [valuePath state (RuntimeScalar
      (ScalarValue Unrestricted TyBool (DecisionShape BooleanDecision)))]
    UnitExpression -> Right [valuePath state RuntimeUnit]
    TupleExpression expressions -> do
      (values, next) <- evalSequentialValues environment state expressions
      Right [valuePath next (RuntimeTuple values)]
    FieldExpression base field -> do
      scalar <- readField environment state locatedExpression base field
      Right [valuePath state (RuntimeScalar scalar)]
    BinaryExpression {} -> do
      scalar <- inferReadOnlyScalar environment state locatedExpression
      Right [valuePath state (RuntimeScalar scalar)]
    ConstructExpression constructor fields -> do
      scalar <- constructValue environment state locatedExpression constructor fields
      Right [valuePath state (RuntimeScalar scalar)]
    CallExpression name arguments -> evalPrimitive environment state locatedExpression name arguments
    ReceiveExpression messageTy endpoint -> evalReceive environment state locatedExpression messageTy endpoint
    ReceiveFrameExpression endpoint -> evalReceiveFrame environment state locatedExpression endpoint
    RecognizeExpression grammar raw -> evalRecognize environment state locatedExpression grammar raw
    ValidateExpression claim context subject -> evalValidate environment state locatedExpression claim context subject
    SendExpression value endpoint -> evalSend environment False state locatedExpression value endpoint
    SendExactExpression value endpoint -> evalSend environment True state locatedExpression value endpoint
    ReceiveExactExpression count endpoint evidence ->
      evalReceiveExact environment state locatedExpression count endpoint evidence
    SelectExpression branch endpoint evidence ->
      evalSelect environment state locatedExpression branch endpoint evidence
    CommitReceiveExpression pending evidence ->
      evalCommit environment state locatedExpression pending evidence
    BorrowExpression owner view body -> evalBorrow environment state locatedExpression owner view body
    DecideExpression scrutinee arms -> evalDecide environment state locatedExpression scrutinee arms
    OfferExpression endpoint arms -> evalOffer environment state locatedExpression endpoint arms
    FailExpression target resource -> evalFail environment state locatedExpression target resource
    CloseExpression target -> evalClose environment state locatedExpression target
    ReleaseExpression owner -> evalRelease state locatedExpression owner
    AcceptExpression value targetTy -> evalAccept environment state locatedExpression value targetTy
    ProveExpression proposition -> evalProve environment state locatedExpression proposition
    FallbackExpression base fallback -> evalFallback environment state locatedExpression base fallback

bindPattern :: Located Pattern -> RuntimeValue -> SurfaceState -> Either SurfaceCheckError SurfaceState
bindPattern pattern' value state =
  case (locatedValue pattern', value) of
    (BindPattern name, RuntimeScalar scalar) ->
      insertBindingMeta (locatedSpan pattern') name
        (BindingMeta (scalarMode scalar) (scalarType scalar) (shapeForBinding name (scalarShape scalar))) state
    (BindPattern name, RuntimeUnit) ->
      insertBindingMeta (locatedSpan pattern') name (BindingMeta Unrestricted TyUnit PlainShape) state
    (TuplePattern patterns, RuntimeTuple values)
      | length patterns == length values -> foldM bindOne state (zip patterns values)
      | otherwise -> throw pattern' TypeMismatch "tuple binding arity mismatch"
    _ -> throw pattern' TypeMismatch "pattern does not match expression result"
  where
    bindOne current (subPattern, subValue) = bindPattern subPattern subValue current

shapeForBinding :: Text -> SurfaceShape -> SurfaceShape
shapeForBinding name shape =
  case shape of
    RecordShape record fields -> RecordShape record (Map.mapWithKey rebase fields)
      where
        rebase field info =
          case fieldAlias info of
            Just _ -> info
            Nothing -> info { fieldAlias = Just (RefField (RefVar (Name name)) field (fieldSort info)) }
    other -> other

insertBindingMeta :: SourceSpan -> Text -> BindingMeta -> SurfaceState -> Either SurfaceCheckError SurfaceState
insertBindingMeta span' name meta state = do
  context <- mapCore span' StructuralUse $
    insertBinding (bindingMode meta) (Name name) (bindingType meta) (resourceContext (stateCore state))
  let active = case bindingType meta of
        TyEndpoint _ -> Just name
        _ -> stateActiveEndpoint state
  Right state
    { stateCore = (stateCore state) { resourceContext = context }
    , stateBindings = Map.insert name meta (stateBindings state)
    , stateActiveEndpoint = active
    }

moveVariable :: Located a -> Text -> SurfaceState -> Either SurfaceCheckError (ScalarValue, SurfaceState)
moveVariable located name state = do
  meta <- lookupMeta located name state
  (mode, ty, context) <- mapCore (locatedSpan located) StructuralUse $
    useBinding (Name name) (resourceContext (stateCore state))
  let next = state
        { stateCore = (stateCore state) { resourceContext = context }
        , stateBindings = if mode == Unrestricted then stateBindings state else Map.delete name (stateBindings state)
        , stateActiveEndpoint = if mode /= Unrestricted && stateActiveEndpoint state == Just name
            then Nothing else stateActiveEndpoint state
        }
  Right (ScalarValue mode ty (bindingShape meta), next)

lookupMeta :: Located a -> Text -> SurfaceState -> Either SurfaceCheckError BindingMeta
lookupMeta located name state =
  case Map.lookup name (stateBindings state) of
    Just meta -> Right meta
    Nothing -> throw located StructuralUse ("unknown or consumed binding: " <> name)

inferReadOnlyScalar
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Either SurfaceCheckError ScalarValue
inferReadOnlyScalar environment state located =
  case locatedValue located of
    VariableExpression name -> do
      meta <- lookupMeta located name state
      Right (ScalarValue (bindingMode meta) (bindingType meta) (bindingShape meta))
    IntegerExpression literal -> Right
      (ScalarValue Unrestricted (TyOpaque ("Integer[" <> Text.pack (show literal) <> "]")) PlainShape)
    BooleanExpression _ -> Right (ScalarValue Unrestricted TyBool (DecisionShape BooleanDecision))
    UnitExpression -> Right (ScalarValue Unrestricted TyUnit PlainShape)
    FieldExpression base field -> readField environment state located base field
    BinaryExpression _ _ _ -> Right (ScalarValue Unrestricted (TyOpaqueSorted "NatExpr" SortNat) PlainShape)
    TupleExpression values -> do
      mapM_ (inferReadOnlyScalar environment state) values
      Right (ScalarValue Unrestricted (TyOpaque "Tuple") PlainShape)
    _ -> throw located TypeMismatch "expression is not a read-only value at this use site"

readField
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Text
  -> Either SurfaceCheckError ScalarValue
readField environment state whole base field = do
  baseScalar <- inferReadOnlyScalar environment state base
  case scalarShape baseScalar of
    RecordShape _ fields -> fieldFrom fields
    ParsedShape _ grammar | field == "value" -> Right
      (ScalarValue Unrestricted (TyFrame (GrammarId grammar)) (recordShape grammar Nothing))
    LegacyParsedShape _ _ grammar | field == "value" -> Right
      (ScalarValue Unrestricted (TyFrame (GrammarId grammar)) (recordShape grammar Nothing))
    ExternalParsedShape grammar _ -> semanticField grammar
    OwnedBytesShape _ -> ownedBytesField
    FixtureRawShape _ -> rawFailure
    LegacyRawShape _ _ -> rawFailure
    PendingRawShape _ -> rawFailure
    BorrowedViewShape _ -> rawFailure
    _ -> case grammarOfTy (scalarType baseScalar) of
      Just grammar -> semanticField grammar
      Nothing -> throw whole IllegalProjection "value has no declared structured fields"
  where
    fieldFrom fields = case Map.lookup field fields of
      Just info -> Right (ScalarValue Unrestricted (fieldType info) PlainShape)
      Nothing -> throw whole IllegalProjection ("field not declared: " <> field)

    semanticField grammar =
      case recordShape grammar (baseVariable base) of
        RecordShape _ fields -> fieldFrom fields
        _ -> throw whole IllegalProjection "internal record-shape error"

    ownedBytesField = case field of
      "length" -> Right (ScalarValue Unrestricted (TyUInt 64) PlainShape)
      "kind" -> Right (ScalarValue Unrestricted
        (TyOpaqueSorted "PayloadKind" (SortEnum "PayloadKind")) PlainShape)
      "id" -> Right (ScalarValue Unrestricted
        (TyOpaqueSorted "PayloadId" (SortStableId "OwnedBytes")) PlainShape)
      _ -> throw whole IllegalProjection "owned bytes do not have that field"

    rawFailure = throw whole IllegalProjection "raw byte views have no structured semantic fields"

baseVariable :: Located SurfaceExpression -> Maybe Text
baseVariable expression = case locatedValue expression of
  VariableExpression name -> Just name
  _ -> Nothing

constructValue
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Text
  -> [(Text, Located SurfaceExpression)]
  -> Either SurfaceCheckError ScalarValue
constructValue environment state located constructor assignments =
  case constructor of
    "Hello" -> build "Hello" ["versions"]
    "Begin" -> build "Begin" ["length", "kind", "digestAlg", "digest"]
    _ -> throw located TypeMismatch ("unknown constructor: " <> constructor)
  where
    table = Map.fromList assignments
    build grammar required = do
      fields <- Map.fromList <$> mapM fieldEntry required
      Right (ScalarValue Unrestricted (TyFrame (GrammarId grammar)) (RecordShape grammar fields))

    fieldEntry field = do
      expression <- case Map.lookup field table of
        Just value -> Right value
        Nothing -> throw located TypeMismatch ("missing constructor field: " <> field)
      scalar <- inferReadOnlyScalar environment state expression
      sort <- case refSortOfTy (scalarType scalar) of
        Just result -> Right result
        Nothing -> throw expression TypeMismatch "constructor field is not refinement-visible"
      alias <- optionalRefTerm environment state expression
      Right (field, FieldInfo (scalarType scalar) sort alias)

optionalRefTerm
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Either SurfaceCheckError (Maybe RefTerm)
optionalRefTerm environment state expression =
  case elaborateRefTerm (elaborationEnv environment state) expression of
    Right term -> Right (Just (rewriteRefTerm state term))
    Left _ -> Right Nothing

evalPrimitive
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Text
  -> [Located SurfaceExpression]
  -> Either SurfaceCheckError [SurfacePath]
evalPrimitive environment state located name arguments =
  case Map.lookup name (surfacePrimitives environment) of
    Nothing -> throw located UnknownPrimitive ("primitive is not declared in Sigma: " <> name)
    Just primitive -> evalPrimitiveRule environment state located primitive arguments

evalPrimitiveRule
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> PrimitiveSemantics
  -> [Located SurfaceExpression]
  -> Either SurfaceCheckError [SurfacePath]
evalPrimitiveRule environment state located primitive arguments =
  case primitive of
    PrimitiveSupportedVersions -> do
      arity 0
      let binder = Name "$versions"
          base = TyOpaqueSorted "SupportedVersions" versionSetSort
          proposition = LessThan (RefNat 0) (RefLen (RefVar binder))
      scalar (TyRefined binder base proposition) PlainShape
    PrimitiveSha256 -> reads 1 >> scalar (TyOpaque "Digest") PlainShape
    PrimitiveShouldCancel -> arity 0 >> scalar TyBool (DecisionShape BooleanDecision)
    PrimitiveChooseSupported -> reads 2 >> scalar (TyOpaque "SupportedDecision") (DecisionShape ChooseSupportedDecision)
    PrimitiveStore -> do
      arity 1
      (_, next) <- moveLinearArgument environment state (head arguments)
      Right [valuePath next (RuntimeScalar
        (ScalarValue Unrestricted (TyOpaque "StoreResult") (DecisionShape StoreDecision)))]
    PrimitiveFixtureBytes -> do
      arity 0
      let (frame, next) = freshFrame state
      Right [valuePath next (RuntimeScalar
        (ScalarValue Unrestricted (TyOpaqueSorted "RawBytes" byteSequenceSort) (FixtureRawShape frame)))]
    PrimitiveUncheckedU32Add -> do
      reads 2
      scalar (TyUInt 32) UncheckedArithmeticShape
    PrimitiveNewCancellationScope -> do
      arity 0
      Right [valuePath state (RuntimeTuple
        [ RuntimeScalar (ScalarValue Linear (TyOpaque "CancelScope") PlainShape)
        , RuntimeScalar (ScalarValue Affine (TyOpaque "CancelCap") PlainShape)
        ])]
    PrimitiveAllocateLinearBuffer -> arity 1 >> scalarWithMode Linear (TyOpaque "LinearBuffer") PlainShape
    PrimitiveRecordUploadId -> reads 1 >> unit
    PrimitiveConsumeBeginPolicyEvidence -> do
      arity 1
      evidenceName <- namedExpression MissingEvidence (head arguments)
      case Map.lookup (unName evidenceName) (stateBindings state) of
        Nothing -> throw (head arguments) MissingEvidence "no BeginPolicy evidence is in scope"
        Just meta -> case bindingType meta of
          TyValidated "BeginPolicy" _ _ -> unit
          TyProof (Atom "BeginPolicy" _) -> unit
          _ -> throw (head arguments) MissingEvidence "binding is not BeginPolicy evidence"
    PrimitiveUse -> do
      next <- foldM consumeRestrictedIfNamed state arguments
      Right [valuePath next RuntimeUnit]
    PrimitiveInspect -> reads 1 >> unit
    PrimitiveAuthorizeStore -> consumeOne
    PrimitiveDelegate -> consumeOne
    PrimitiveContinueCommonState -> reads 1 >> unit
    PrimitiveHandlePayload -> unit
  where
    arity expected = unless (length arguments == expected) $
      throw located TypeMismatch ("primitive arity mismatch; expected " <> Text.pack (show expected))

    reads expected = do
      arity expected
      mapM_ (inferReadOnlyScalar environment state) arguments

    scalar ty shape = scalarWithMode Unrestricted ty shape
    scalarWithMode mode ty shape = Right [valuePath state (RuntimeScalar (ScalarValue mode ty shape))]
    unit = Right [valuePath state RuntimeUnit]

    consumeOne = do
      arity 1
      (_, next) <- moveVariableArgument state (head arguments)
      Right [valuePath next RuntimeUnit]

    consumeRestrictedIfNamed current expression =
      case locatedValue expression of
        VariableExpression name ->
          case Map.lookup name (stateBindings current) of
            Just meta | bindingMode meta /= Unrestricted -> snd <$> moveVariable expression name current
            _ -> Right current
        _ -> Right current

moveVariableArgument :: SurfaceState -> Located SurfaceExpression -> Either SurfaceCheckError (ScalarValue, SurfaceState)
moveVariableArgument state expression = do
  name <- namedExpression StructuralUse expression
  moveVariable expression (unName name) state

moveLinearArgument
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Either SurfaceCheckError (ScalarValue, SurfaceState)
moveLinearArgument _ state expression = do
  (scalar, next) <- moveVariableArgument state expression
  unless (scalarMode scalar == Linear) $
    throw expression StructuralUse "operation requires a linear owner"
  Right (scalar, next)

evalSequentialValues
  :: SurfaceEnvironment
  -> SurfaceState
  -> [Located SurfaceExpression]
  -> Either SurfaceCheckError ([RuntimeValue], SurfaceState)
evalSequentialValues environment = go []
  where
    go accumulated state [] = Right (reverse accumulated, state)
    go accumulated state (expression : rest) = do
      paths <- evalExpression environment state expression
      case paths of
        [SurfacePath PathContinue next (Just value)] -> go (value : accumulated) next rest
        _ -> throw expression TypeMismatch "tuple element cannot branch or terminate"

evalReceive
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceType
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalReceive environment state located surfaceMessage endpointExpression = do
  endpoint <- endpointName endpointExpression
  meta <- lookupMeta endpointExpression endpoint state
  expectedMessage <- sessionReceiveMessage located meta
  (_, writtenMessage, _) <- resolveSurfaceType environment state surfaceMessage
  unless (compareTypes writtenMessage expectedMessage == DefinitionallyEqual) $
    throw surfaceMessage TypeMismatch "written receive type does not match the protocol message"
  (temp, state1) <- freshName "$recv" state
  step <- mapSession located $
    receiveEndpoint (Name endpoint) temp (resourceContext (stateCore state1))
  message <- requireMessage located step
  let state2 = applySessionContext endpoint (stepContext step) state1
  (successor, state3) <- extractLinearTemp temp state2
  let received = ScalarValue (messageMode (messageType message)) (messageType message) (shapeForType (messageType message))
  Right [valuePath state3 (RuntimeTuple [RuntimeScalar successor, RuntimeScalar received])]

evalReceiveFrame
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalReceiveFrame environment state located endpointExpression = do
  endpoint <- endpointName endpointExpression
  _ <- sessionReceiveFrameGrammar located =<< lookupMeta endpointExpression endpoint state
  (pendingTemp, state1) <- freshName "$pending" state
  let (frame, state2) = freshFrame state1
  step <- mapRecognition located $
    receiveFrame (Name endpoint) pendingTemp frame (resourceContext (stateCore state2))
  let state3 = applySessionContext endpoint (receiveFrameContext step) state2
  (pendingScalar, state4) <- extractLinearTemp pendingTemp state3
  if surfaceLegacyReceiveFrameRaw environment
    then Right [valuePath state4 (RuntimeTuple
      [ RuntimeScalar pendingScalar
      , RuntimeScalar (ScalarValue Unrestricted (TyOpaqueSorted "RawBytes" byteSequenceSort)
          (LegacyRawShape (pendingGrammar (receivePendingSpec step)) frame))
      ])]
    else Right [valuePath state4 (RuntimeScalar pendingScalar)]

evalRecognize
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Text
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalRecognize environment state located grammar rawExpression = do
  raw <- inferReadOnlyScalar environment state rawExpression
  case scalarShape raw of
    PendingRawShape rawView -> do
      parsed <- mapRecognition located $
        trustedRecognitionSuccess rawView (Name ("$parsed-" <> grammar)) (resourceContext (stateCore state))
      failure <- mapRecognition located $
        trustedRecognitionFailure rawView "recognition-failure" (resourceContext (stateCore state))
      decision (RecognitionDecision parsed failure grammar)
    LegacyRawShape grammarId frame
      | grammarId == GrammarId grammar -> decision (LegacyRecognitionDecision grammarId frame grammar)
      | otherwise -> throw located RecognitionProvenance "recognizer grammar differs from pending frame grammar"
    FixtureRawShape frame -> Right [valuePath state (RuntimeScalar
      (ScalarValue Unrestricted (TyOpaque ("Parsed[" <> grammar <> "]")) (ExternalParsedShape grammar frame)))]
    _ -> throw rawExpression TypeMismatch "recognize requires a raw byte view"
  where
    _ = environment
    decision kind = Right [valuePath state (RuntimeScalar
      (ScalarValue Unrestricted (TyOpaque "RecognitionDecision") (DecisionShape kind)))]

evalValidate
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Text
  -> Maybe (Located SurfaceExpression)
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalValidate environment state _located claim context subject
  | claim == "DigestMatches" = do
      validateDigestSubject subject
      decision (DigestDecision digestMatchesProposition)
  | otherwise = do
      contextName <- case context of
        Just expression -> namedExpression MissingEvidence expression
        Nothing -> Right (Name "$implicit-context")
      subjectName <- namedExpression TypeMismatch subject
      _ <- lookupMeta subject subjectNameText state
      decision (ValidationDecision claim contextName subjectName)
  where
    subjectNameText = case locatedValue subject of
      VariableExpression name -> name
      _ -> ""

    validateDigestSubject expression = case locatedValue expression of
      TupleExpression values -> mapM_ (inferReadOnlyScalar environment state) values
      _ -> inferReadOnlyScalar environment state expression >> Right ()

    decision kind = Right [valuePath state (RuntimeScalar
      (ScalarValue Unrestricted (TyOpaque "ValidationDecision") (DecisionShape kind)))]

evalSend
  :: SurfaceEnvironment
  -> Bool
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalSend environment exact state located valueExpression endpointExpression = do
  endpoint <- endpointName endpointExpression
  endpointMeta <- lookupMeta endpointExpression endpoint state
  expected <- sessionSendMessage located endpointMeta
  when (exact && not (isBytesTy expected)) $
    throw located TypeMismatch "send_exact requires a byte protocol message"
  (value, state1) <- moveOrReadValue environment state valueExpression
  checkScalarAgainst environment state1 valueExpression value expected
  (temp, state2) <- freshName "$send" state1
  step <- mapSession located $
    sendEndpoint (Name endpoint) temp (resourceContext (stateCore state2))
  let state3 = applySessionContext endpoint (stepContext step) state2
  (successor, state4) <- extractLinearTemp temp state3
  Right [valuePath state4 (RuntimeScalar successor)]

evalReceiveExact
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Maybe (Located SurfaceExpression)
  -> Either SurfaceCheckError [SurfacePath]
evalReceiveExact environment state located count endpointExpression explicitEvidence = do
  endpoint <- endpointName endpointExpression
  endpointMeta <- lookupMeta endpointExpression endpoint state
  expected <- sessionReceiveMessage located endpointMeta
  expectedIndex <- case rewriteTy state expected of
    TyBytes index -> Right index
    other -> throw located TypeMismatch ("receive_exact requires Bytes, found " <> Text.pack (show other))
  checkConfiguredRequirement environment state count (surfaceReceiveExactRequirement environment) explicitEvidence
  rawCount <- mapElaboration count $ elaborateRefTerm (elaborationEnv environment state) count
  (natCount, _) <- mapFocusing count $
    elaborateRefTermAs (surfaceStaticContext environment) (stateCore state) SortNat (rewriteRefTerm state rawCount)
  unless (normalizeRefTerm natCount == normalizeRefTerm expectedIndex) $
    throw count TypeMismatch "receive_exact count differs from the protocol byte length"
  (temp, state1) <- freshName "$receive-exact" state
  step <- mapSession located $
    receiveEndpoint (Name endpoint) temp (resourceContext (stateCore state1))
  let state2 = applySessionContext endpoint (stepContext step) state1
  (successor, state3) <- extractLinearTemp temp state2
  let payload = ScalarValue Linear (TyBytes expectedIndex) (OwnedBytesShape expectedIndex)
  Right [valuePath state3 (RuntimeTuple [RuntimeScalar successor, RuntimeScalar payload])]

evalSelect
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> BranchValue
  -> Located SurfaceExpression
  -> Maybe (Located SurfaceExpression)
  -> Either SurfaceCheckError [SurfacePath]
evalSelect environment state located branch endpointExpression explicitEvidence = do
  endpoint <- endpointName endpointExpression
  endpointMeta <- lookupMeta endpointExpression endpoint state
  (expectedPayload, _) <- sessionSelectBranch located endpointMeta (branchValueLabel branch)
  mapM_ (\requirement -> checkRequirement environment state located requirement explicitEvidence)
    (Map.findWithDefault [] (branchValueLabel branch) (surfaceSelectRequirements environment))
  state1 <- checkSelectedPayload environment state located expectedPayload (branchValueArguments branch) explicitEvidence
  (temp, state2) <- freshName "$select" state1
  step <- mapSession located $
    selectEndpoint (Name endpoint) temp (branchValueLabel branch) (resourceContext (stateCore state2))
  let state3 = applySessionContext endpoint (stepContext step) state2
  (successor, state4) <- extractLinearTemp temp state3
  Right [valuePath state4 (RuntimeScalar successor)]

evalCommit
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalCommit _environment state located pendingExpression evidenceExpression = do
  pendingName <- namedExpression RecognitionProvenance pendingExpression
  pendingMeta <- lookupMeta pendingExpression (unName pendingName) state
  spec <- case bindingType pendingMeta of
    TyPendingRecv pending -> Right pending
    _ -> throw pendingExpression RecognitionProvenance "commit_receive target is not a pending receive"
  evidence <- inferReadOnlyScalar undefinedEnvironment state evidenceExpression
  matches <- case scalarShape evidence of
    ParsedShape parsed _ -> do
      (temp, state1) <- freshName "$commit" state
      step <- mapRecognition located $
        commitReceive pendingName temp parsed (resourceContext (stateCore state1))
      let state2 = applySessionContext (unName pendingName) (commitContext step) state1
      (successor, state3) <- extractLinearTemp temp state2
      Right (successor, state3)
    LegacyParsedShape grammar frame _
      | grammar == pendingGrammar spec && frame == pendingFrame spec -> do
          (_, context) <- mapCore (locatedSpan located) RecognitionProvenance $
            consumeLinear pendingName (resourceContext (stateCore state))
          let state1 = consumeSurfaceName (unName pendingName) state
          (successorName, state2) <- freshName "$legacy-commit" state1
          context2 <- mapCore (locatedSpan located) RecognitionProvenance $
            insertBinding Linear successorName (TyEndpoint (pendingContinuation spec)) context
          let state3 = state2 { stateCore = (stateCore state2) { resourceContext = context2 } }
          (successor, state4) <- extractLinearTemp successorName state3
          Right (successor, state4)
      | otherwise -> throw evidenceExpression RecognitionProvenance "parsed evidence belongs to a different frame"
    ExternalParsedShape _ _ -> throw evidenceExpression RecognitionProvenance "fixture recognition evidence cannot commit this pending receive"
    ForgedParsedShape -> throw evidenceExpression RecognitionProvenance "forged parsed evidence has no ingress provenance"
    _ -> throw evidenceExpression RecognitionProvenance "commit_receive requires Parsed evidence"
  let (successor, next) = matches
  Right [valuePath next (RuntimeScalar successor)]
  where
    -- Only metadata lookup is needed for evidence; no environment-sensitive
    -- projection is performed in this call.
    undefinedEnvironment = emptySurfaceEnvironment (surfaceStaticContext _environment)

evalBorrow
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Text
  -> Located Block
  -> Either SurfaceCheckError [SurfacePath]
evalBorrow environment state located ownerExpression viewName body = do
  ownerName <- namedExpression BorrowEscape ownerExpression
  ownerMeta <- lookupMeta ownerExpression (unName ownerName) state
  (view, loaned) <- case bindingType ownerMeta of
    TyPendingRecv _ -> do
      (raw, context) <- mapRecognition located $
        beginRawLoan ownerName (resourceContext (stateCore state))
      Right
        ( ScalarValue Unrestricted (TyOpaqueSorted "RawBytes" byteSequenceSort) (PendingRawShape raw)
        , state { stateCore = (stateCore state) { resourceContext = context } }
        )
    _ | bindingMode ownerMeta == Linear || bindingMode ownerMeta == Affine -> do
          context <- mapCore (locatedSpan located) BorrowEscape $
            startSharedLoan ownerName (resourceContext (stateCore state))
          Right
            ( ScalarValue Unrestricted (TyOpaqueSorted "SharedBytes" byteSequenceSort) (BorrowedViewShape ownerName)
            , state { stateCore = (stateCore state) { resourceContext = context } }
            )
      | otherwise -> throw ownerExpression BorrowEscape "borrow requires an affine or linear owner"
  withView <- insertBindingMeta (locatedSpan located) viewName
    (BindingMeta Unrestricted (scalarType view) (scalarShape view)) loaned
  bodyPaths <- checkValueBlock environment withView body
  mapM (finish ownerName) bodyPaths
  where
    finish owner path
      | pathControl path /= PathContinue = throw located BorrowEscape "borrow body terminates before the loan ends"
      | otherwise = do
          case pathValue path of
            Just value | containsBorrowedView owner value ->
              throw located BorrowEscape "shared view escapes its lexical scope"
            _ -> Right ()
          state1 <- removeScopedBinding viewName (pathState path)
          context <- mapCore (locatedSpan located) BorrowEscape $
            endSharedLoan owner (resourceContext (stateCore state1))
          Right path { pathState = state1 { stateCore = (stateCore state1) { resourceContext = context } } }

containsBorrowedView :: Name -> RuntimeValue -> Bool
containsBorrowedView _ RuntimeUnit = False
containsBorrowedView owner (RuntimeTuple values) = any (containsBorrowedView owner) values
containsBorrowedView owner (RuntimeScalar scalar) = case scalarShape scalar of
  BorrowedViewShape actual -> actual == owner
  PendingRawShape _ -> True
  _ -> False

evalDecide
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> [Located CaseArm]
  -> Either SurfaceCheckError [SurfacePath]
evalDecide environment state located scrutinee arms = do
  scalar <- inferReadOnlyScalar environment state scrutinee
  decision <- case scalarShape scalar of
    DecisionShape value -> Right value
    _ | scalarType scalar == TyBool -> Right BooleanDecision
      | otherwise -> throw scrutinee TypeMismatch "decide requires a declared decision value"
  let expected = Set.fromList (decisionLabels decision)
      actual = Set.fromList (map (casePatternLabel . caseArmPattern . locatedValue) arms)
  unless (expected == actual && Set.size expected == length arms) $
    throw located BranchExhaustiveness "decision handlers do not exactly cover all alternatives"
  concat <$> mapM (checkDecisionArm environment state decision) arms

checkDecisionArm
  :: SurfaceEnvironment
  -> SurfaceState
  -> DecisionKind
  -> Located CaseArm
  -> Either SurfaceCheckError [SurfacePath]
checkDecisionArm environment state decision locatedArm = do
  let pattern' = caseArmPattern (locatedValue locatedArm)
  withBinders <- bindDecisionPattern state decision (casePatternLabel pattern') (casePatternBinders pattern') locatedArm
  checkScopedValueBlock environment state withBinders (caseArmBody (locatedValue locatedArm))

decisionLabels :: DecisionKind -> [Text]
decisionLabels decision = case decision of
  BooleanDecision -> ["true", "false"]
  ChooseSupportedDecision -> ["none", "some"]
  RecognitionDecision {} -> ["rejected", "accepted"]
  LegacyRecognitionDecision {} -> ["failure", "success"]
  ValidationDecision {} -> ["rejected", "accepted"]
  DigestDecision {} -> ["rejected", "accepted"]
  StoreDecision -> ["failure", "success"]

bindDecisionPattern
  :: SurfaceState
  -> DecisionKind
  -> Text
  -> [Text]
  -> Located a
  -> Either SurfaceCheckError SurfaceState
bindDecisionPattern state decision label binders located =
  case (decision, label, binders) of
    (BooleanDecision, "true", []) -> Right state
    (BooleanDecision, "false", []) -> Right state
    (ChooseSupportedDecision, "none", [noCommon]) ->
      insertProof located noCommon (Disjoint serverSupportedTerm helloVersionsTerm) state
    (ChooseSupportedDecision, "some", [version, offered, supported]) -> do
      state1 <- insertBindingMeta (locatedSpan located) version (BindingMeta Unrestricted (TyUInt 16) PlainShape) state
      state2 <- insertProof located offered (Member (RefVar (Name version)) helloVersionsTerm) state1
      insertProof located supported (Member (RefVar (Name version)) serverSupportedTerm) state2
    (RecognitionDecision parsed _ grammar, "accepted", [parsedName]) ->
      insertBindingMeta (locatedSpan located) parsedName
        (BindingMeta Unrestricted (TyOpaque ("Parsed[" <> grammar <> "]")) (ParsedShape parsed grammar)) state
    (RecognitionDecision _ failure _, "rejected", [reason]) ->
      insertBindingMeta (locatedSpan located) reason
        (BindingMeta Unrestricted (TyOpaque "RecognitionFailure") (RecognitionFailureShape failure)) state
    (LegacyRecognitionDecision grammar frame grammarText, "success", [parsedName]) ->
      insertBindingMeta (locatedSpan located) parsedName
        (BindingMeta Unrestricted (TyOpaque ("Parsed[" <> grammarText <> "]"))
          (LegacyParsedShape grammar frame grammarText)) state
    (LegacyRecognitionDecision grammar frame _, "failure", [reason]) ->
      insertBindingMeta (locatedSpan located) reason
        (BindingMeta Unrestricted (TyOpaque "RecognitionFailure")
          (LegacyRecognitionFailureShape grammar frame)) state
    (ValidationDecision claim context subject, "accepted", [evidence]) ->
      insertBindingMeta (locatedSpan located) evidence
        (BindingMeta Unrestricted (TyValidated claim context subject) PlainShape) state
    (ValidationDecision claim _ _, "rejected", [reason]) ->
      insertBindingMeta (locatedSpan located) reason
        (BindingMeta Unrestricted (TyOpaque ("ValidationFailure[" <> claim <> "]")) PlainShape) state
    (DigestDecision proposition, "accepted", [evidence]) -> insertProof located evidence proposition state
    (DigestDecision _, "rejected", [reason]) ->
      insertBindingMeta (locatedSpan located) reason
        (BindingMeta Unrestricted (TyOpaque "DigestFailure") PlainShape) state
    (StoreDecision, "success", [identifier]) ->
      insertBindingMeta (locatedSpan located) identifier
        (BindingMeta Unrestricted (TyOpaque "UploadId") PlainShape) state
    (StoreDecision, "failure", [reason]) ->
      insertBindingMeta (locatedSpan located) reason
        (BindingMeta Unrestricted (TyOpaque "StorageFailure") PlainShape) state
    _ -> throw located TypeMismatch "decision arm binder shape is incompatible with the decision result"

insertProof :: Located a -> Text -> Proposition -> SurfaceState -> Either SurfaceCheckError SurfaceState
insertProof located name proposition =
  insertBindingMeta (locatedSpan located) name (BindingMeta Unrestricted (TyProof proposition) PlainShape)

evalOffer
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> [Located CaseArm]
  -> Either SurfaceCheckError [SurfacePath]
evalOffer environment state located endpointExpression arms = do
  endpoint <- endpointName endpointExpression
  endpointMeta <- lookupMeta endpointExpression endpoint state
  branches <- sessionOfferBranches located endpointMeta
  mapBranchExhaustiveness located branches (map (casePatternLabel . caseArmPattern . locatedValue) arms)
  concat <$> mapM (checkOfferArm environment state endpoint) arms

checkOfferArm
  :: SurfaceEnvironment
  -> SurfaceState
  -> Text
  -> Located CaseArm
  -> Either SurfaceCheckError [SurfacePath]
checkOfferArm environment incoming endpoint locatedArm = do
  let pattern' = caseArmPattern (locatedValue locatedArm)
      label = casePatternLabel pattern'
  (temp, state1) <- freshName "$offer" incoming
  step <- mapSession locatedArm $
    offerEndpoint (Name endpoint) temp label (resourceContext (stateCore state1))
  let state2 = applySessionContext endpoint (stepContext step) state1
  (successor, state3) <- extractLinearTemp temp state2
  rebound <- insertBindingMeta (locatedSpan locatedArm) endpoint
    (BindingMeta Linear (scalarType successor) PlainShape) state3
  withPayload <- bindOfferPayload locatedArm (stepMessage step) (casePatternBinders pattern') rebound
  checkScopedValueBlock environment incoming withPayload (caseArmBody (locatedValue locatedArm))

bindOfferPayload
  :: Located a
  -> Maybe MessageSpec
  -> [Text]
  -> SurfaceState
  -> Either SurfaceCheckError SurfaceState
bindOfferPayload _ Nothing [] state = Right state
bindOfferPayload located (Just message) [name] state =
  insertBindingMeta (locatedSpan located) name
    (BindingMeta (messageMode (messageType message)) (messageType message) (shapeForBinding name (shapeForType (messageType message)))) state
bindOfferPayload located Nothing (_ : _) _ = throw located TypeMismatch "branch carries no payload"
bindOfferPayload located (Just _) _ _ = throw located TypeMismatch "branch payload binder arity mismatch"

checkValueBlock :: SurfaceEnvironment -> SurfaceState -> Located Block -> Either SurfaceCheckError [SurfacePath]
checkValueBlock environment state locatedBlock =
  case blockStatements (locatedValue locatedBlock) of
    [] -> Right [valuePath state RuntimeUnit]
    statements -> do
      prefix <- checkStatements environment [continuePath state] (init statements)
      concat <$> mapM (finish (last statements)) prefix
  where
    finish statement path
      | pathControl path /= PathContinue = Right [path]
      | otherwise = case locatedValue statement of
          ExpressionStatement expression -> evalExpression environment (pathState path) expression
          _ -> checkStatement environment statement path

checkScopedValueBlock
  :: SurfaceEnvironment
  -> SurfaceState
  -> SurfaceState
  -> Located Block
  -> Either SurfaceCheckError [SurfacePath]
checkScopedValueBlock environment incoming scoped body = do
  paths <- checkValueBlock environment scoped body
  mapM (pruneScopedPath (locatedSpan body) (Map.keysSet (stateBindings incoming))) paths

pruneScopedPath :: SourceSpan -> Set Text -> SurfacePath -> Either SurfaceCheckError SurfacePath
pruneScopedPath _ _ path | pathControl path /= PathContinue = Right path
pruneScopedPath span' incoming path = do
  let state = pathState path
      localNames = Map.keysSet (stateBindings state) `Set.difference` incoming
      locals = mapMaybe (\name -> fmap ((,) name) (Map.lookup name (stateBindings state))) (Set.toList localNames)
  mapM_ ensureDiscardable locals
  next <- foldM (flip removeScopedBinding) state (map fst locals)
  Right path { pathState = next }
  where
    ensureDiscardable (name, meta)
      | bindingMode meta == Linear = Left SurfaceCheckError
          { surfaceErrorSpan = span'
          , surfaceErrorClass = LinearCompletion
          , surfaceErrorDetail = "linear branch-local binding remains live: " <> name
          }
      | otherwise = Right ()

evalFail
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> FailureTarget
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalFail environment state located target resourceExpression = do
  resourceName <- namedExpression StructuralUse resourceExpression
  next <- if failureTargetClass target == "recognition"
    then failRecognition state located resourceName target
    else consumeFatal state located resourceName
  ensureTerminalState environment (locatedSpan located) (Just (Outcome "failure")) next
  Right [SurfacePath (PathFailed (failureTargetClass target) "explicit") next Nothing]

failRecognition
  :: SurfaceState
  -> Located a
  -> Name
  -> FailureTarget
  -> Either SurfaceCheckError SurfaceState
failRecognition state located pendingName target =
  case failureTargetArguments target of
    [reasonExpression] -> do
      reason <- namedExpression RecognitionProvenance reasonExpression
      reasonMeta <- lookupMeta reasonExpression (unName reason) state
      pendingMeta <- lookupMeta located (unName pendingName) state
      spec <- case bindingType pendingMeta of
        TyPendingRecv pending -> Right pending
        _ -> throw located RecognitionProvenance "recognition failure target is not PendingRecv"
      case bindingShape reasonMeta of
        RecognitionFailureShape failure -> do
          context <- mapRecognition located $
            failPendingRecognition pendingName failure (resourceContext (stateCore state))
          Right (applySessionContext (unName pendingName) context state)
        LegacyRecognitionFailureShape grammar frame
          | grammar == pendingGrammar spec && frame == pendingFrame spec -> consumeFatal state located pendingName
          | otherwise -> throw reasonExpression RecognitionProvenance "recognition failure belongs to a different frame"
        _ -> throw reasonExpression RecognitionProvenance "failure value lacks matching recognition provenance"
    _ -> throw located RecognitionProvenance "recognition failure requires exactly one reason value"

consumeFatal :: SurfaceState -> Located a -> Name -> Either SurfaceCheckError SurfaceState
consumeFatal state located name = do
  (_, context) <- mapCore (locatedSpan located) StructuralUse $
    consumeLinear name (resourceContext (stateCore state))
  Right (applySessionContext (unName name) context state)

evalClose
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalClose environment state located target = do
  (endpoint, outcome) <- resolveCloseTarget state target
  step <- mapSession located $ closeEndpoint (Name endpoint) outcome (resourceContext (stateCore state))
  let next = applySessionContext endpoint (stepContext step) state
  ensureTerminalState environment (locatedSpan located) (Just outcome) next
  Right [SurfacePath (PathClosed outcome) next Nothing]

resolveCloseTarget :: SurfaceState -> Located SurfaceExpression -> Either SurfaceCheckError (Text, Outcome)
resolveCloseTarget state target = case locatedValue target of
  VariableExpression name | name `elem` ["success", "failure", "cancelled"] -> do
    endpoint <- currentEndpoint target state
    Right (endpoint, Outcome name)
  VariableExpression name -> do
    meta <- lookupMeta target name state
    case bindingType meta of
      TyEndpoint session -> do
        headSession <- mapSession target (exposeSessionHead session)
        case headSession of
          End outcome -> Right (name, outcome)
          _ -> throw target SessionAction "endpoint is not at an end state"
      _ -> throw target SessionAction "close requires an endpoint or terminal outcome"
  _ -> throw target SessionAction "close target must be a name"

evalRelease
  :: SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Either SurfaceCheckError [SurfacePath]
evalRelease state located ownerExpression = do
  name <- namedExpression StructuralUse ownerExpression
  meta <- lookupMeta ownerExpression (unName name) state
  unless (bindingMode meta == Linear) $
    throw ownerExpression StructuralUse "release requires a linear owner"
  (_, context) <- mapCore (locatedSpan located) StructuralUse $
    consumeLinear name (resourceContext (stateCore state))
  Right [valuePath (applySessionContext (unName name) context state) RuntimeUnit]

evalAccept
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Located SurfaceType
  -> Either SurfaceCheckError [SurfacePath]
evalAccept environment state located valueExpression surfaceTarget = do
  valueName <- namedExpression TypeMismatch valueExpression
  (_, target, _) <- resolveSurfaceType environment state surfaceTarget
  result <- case checkValue (VVar valueName) (rewriteTy state target) (stateCore state) of
    Left (ExplicitTransportRequired _ _) -> throw located ExplicitTransport "dependent type change requires explicit equality transport"
    Left errorValue -> Left (valueError located errorValue)
    Right checked -> Right checked
  let next = applyValueResult (unName valueName) state result
  Right [valuePath next (RuntimeScalar
    (ScalarValue (fromMaybeMode (Map.lookup (unName valueName) (stateBindings state))) target PlainShape))]

evalProve
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceProposition
  -> Either SurfaceCheckError [SurfacePath]
evalProve environment state located propositionSource = do
  proposition <- mapElaboration propositionSource $
    elaborateProposition (elaborationEnv environment state) propositionSource
  plan <- mapFocusing propositionSource $
    focusProposition (surfaceStaticContext environment) (stateCore state) proposition
  let requirements = focusPrerequisites plan ++ [focusGoal plan]
      unresolved = filter (not . dischargedRequirement) requirements
  if null unresolved
    then proofValue proposition
    else if any ((== FocusNeedsExplicitMechanism) . focusedMechanism) unresolved
      then throw located OpaqueProof "opaque claim cannot be introduced by generic prove"
      else if propositionMentionsUnchecked state proposition
        then throw located UncheckedArithmetic "unchecked machine arithmetic has no mathematical proof postcondition"
        else do
          solved <- mapM (solveRequirement state) unresolved
          if and solved
            then proofValue proposition
            else throw located MissingEvidence "transparent proposition is not established by checked evidence/certificate"
  where
    proofValue proposition = Right [valuePath state (RuntimeScalar
      (ScalarValue Unrestricted (TyProof proposition) PlainShape))]

evalFallback
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Located SurfaceExpression
  -> Fallback
  -> Either SurfaceCheckError [SurfacePath]
evalFallback environment state located base fallback = do
  case fallback of
    FailFallback _ -> validateFatalFallback environment state located base
    RejectFallback _ -> Right ()
  evalExpression environment state base

validateFatalFallback
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located a
  -> Located SurfaceExpression
  -> Either SurfaceCheckError ()
validateFatalFallback environment state located base = do
  failureState <- case locatedValue base of
    ReceiveFrameExpression endpoint -> consumeEndpoint endpoint
    ReceiveExactExpression _ endpoint _ -> consumeEndpoint endpoint
    SendExpression _ endpoint -> consumeEndpoint endpoint
    SendExactExpression _ endpoint -> consumeEndpoint endpoint
    _ -> Right state
  ensureTerminalState environment (locatedSpan located) (Just (Outcome "failure")) failureState
  where
    consumeEndpoint expression = do
      endpoint <- endpointName expression
      (_, context) <- mapCore (locatedSpan located) StructuralUse $
        consumeLinear (Name endpoint) (resourceContext (stateCore state))
      Right (applySessionContext endpoint context state)

checkSelectedPayload
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located a
  -> Maybe MessageSpec
  -> [Located SurfaceExpression]
  -> Maybe (Located SurfaceExpression)
  -> Either SurfaceCheckError SurfaceState
checkSelectedPayload _ state _ Nothing [] _ = Right state
checkSelectedPayload environment state located (Just message) [argument] explicitEvidence = do
  case locatedValue argument of
    VariableExpression name -> do
      result <- case explicitEvidence of
        Just evidence | isRefined (messageType message) -> do
          evidenceName <- namedExpression MissingEvidence evidence
          mapValueResult argument $ checkValueUsing evidenceName (VVar (Name name)) (rewriteTy state (messageType message)) (stateCore state)
        _ -> mapValueResult argument $ checkValue (VVar (Name name)) (rewriteTy state (messageType message)) (stateCore state)
      Right (applyValueResult name state result)
    _ -> do
      scalar <- inferReadOnlyScalar environment state argument
      checkScalarAgainst environment state argument scalar (messageType message)
      Right state
checkSelectedPayload _ _ located Nothing (_ : _) _ = throw located TypeMismatch "branch carries no payload"
checkSelectedPayload _ _ located (Just _) _ _ = throw located TypeMismatch "branch payload arity mismatch"

checkConfiguredRequirement
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located a
  -> Maybe Proposition
  -> Maybe (Located SurfaceExpression)
  -> Either SurfaceCheckError ()
checkConfiguredRequirement _ _ _ Nothing _ = Right ()
checkConfiguredRequirement environment state located (Just proposition) explicitEvidence =
  checkRequirement environment state located proposition explicitEvidence

checkRequirement
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located a
  -> Proposition
  -> Maybe (Located SurfaceExpression)
  -> Either SurfaceCheckError ()
checkRequirement environment state located proposition explicitEvidence = do
  let required = rewriteProposition state proposition
  if hasExactEvidence required state
    then Right ()
    else case explicitEvidence of
      Just expression -> do
        evidenceName <- namedExpression MissingEvidence expression
        meta <- lookupMeta expression (unName evidenceName) state
        case evidenceProposition (bindingType meta) of
          Just actual | normalizeProposition (rewriteProposition state actual) == normalizeProposition required -> Right ()
          _ -> throw expression MissingEvidence "explicit evidence proves a different proposition/context/subject"
      Nothing -> do
        plan <- mapFocusing located $ focusProposition (surfaceStaticContext environment) (stateCore state) required
        if dischargedRequirement (focusGoal plan) && all dischargedRequirement (focusPrerequisites plan)
          then Right ()
          else throw located MissingEvidence ("required proposition is not established: " <> Text.pack (show required))

hasExactEvidence :: Proposition -> SurfaceState -> Bool
hasExactEvidence proposition state =
  any matches (Map.elems (unrestrictedBindings (resourceContext (stateCore state))))
  where
    required = normalizeProposition proposition
    matches ty = case evidenceProposition ty of
      Just actual -> normalizeProposition (rewriteProposition state actual) == required
      Nothing -> False

checkScalarAgainst
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located a
  -> ScalarValue
  -> Ty
  -> Either SurfaceCheckError ()
checkScalarAgainst _ state located scalar expected =
  case compareTypes (rewriteTy state (scalarType scalar)) (rewriteTy state expected) of
    DefinitionallyEqual -> Right ()
    RequiresPropositionalEquality -> throw located ExplicitTransport "dependent value requires explicit equality transport"
    IncompatibleTypes -> throw located TypeMismatch "value type is incompatible with protocol/target type"

moveOrReadValue
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Either SurfaceCheckError (ScalarValue, SurfaceState)
moveOrReadValue environment state expression = case locatedValue expression of
  VariableExpression name -> moveVariable expression name state
  _ -> do
    scalar <- inferReadOnlyScalar environment state expression
    Right (scalar, state)

sessionSendMessage :: Located a -> BindingMeta -> Either SurfaceCheckError Ty
sessionSendMessage located meta = case bindingType meta of
  TyEndpoint session -> do
    headSession <- mapSession located (exposeSessionHead session)
    case headSession of
      Send _ message _ -> Right message
      _ -> throw located SessionAction "send used at a non-send session state"
  _ -> throw located SessionAction "send target is not an endpoint"

sessionReceiveMessage :: Located a -> BindingMeta -> Either SurfaceCheckError Ty
sessionReceiveMessage located meta = case bindingType meta of
  TyEndpoint session -> do
    headSession <- mapSession located (exposeSessionHead session)
    case headSession of
      Receive _ message _ -> Right message
      _ -> throw located SessionAction "receive used at a non-receive session state"
  _ -> throw located SessionAction "receive target is not an endpoint"

sessionReceiveFrameGrammar :: Located a -> BindingMeta -> Either SurfaceCheckError GrammarId
sessionReceiveFrameGrammar located meta = do
  message <- sessionReceiveMessage located meta
  case stripRefinement message of
    TyFrame grammar -> Right grammar
    _ -> throw located SessionAction "receive_frame requires a grammar-backed protocol message"

sessionSelectBranch :: Located a -> BindingMeta -> Text -> Either SurfaceCheckError (Maybe MessageSpec, Session)
sessionSelectBranch located meta label = case bindingType meta of
  TyEndpoint session -> do
    headSession <- mapSession located (exposeSessionHead session)
    case headSession of
      Select branches -> case filter ((== label) . branchLabel) branches of
        [branch] -> Right (fmap (uncurry MessageSpec) (branchPayload branch), branchContinuation branch)
        [] -> throw located SessionAction "selected label is not declared by the protocol"
        _ -> throw located SessionAction "protocol contains duplicate branch labels"
      _ -> throw located SessionAction "select used at a non-select session state"
  _ -> throw located SessionAction "select target is not an endpoint"

sessionOfferBranches :: Located a -> BindingMeta -> Either SurfaceCheckError [Branch]
sessionOfferBranches located meta = case bindingType meta of
  TyEndpoint session -> do
    headSession <- mapSession located (exposeSessionHead session)
    case headSession of
      Offer branches -> Right branches
      _ -> throw located SessionAction "offer used at a non-offer session state"
  _ -> throw located SessionAction "offer target is not an endpoint"

requireMessage :: Located a -> SessionStep -> Either SurfaceCheckError MessageSpec
requireMessage located step = case stepMessage step of
  Just message -> Right message
  Nothing -> throw located TypeMismatch "session action did not expose a message contract"

endpointName :: Located SurfaceExpression -> Either SurfaceCheckError Text
endpointName expression = unName <$> namedExpression SessionAction expression

namedExpression :: RejectionClass -> Located SurfaceExpression -> Either SurfaceCheckError Name
namedExpression rejection expression = case locatedValue expression of
  VariableExpression name -> Right (Name name)
  _ -> throw expression rejection "operation requires a named binding"

currentEndpoint :: Located a -> SurfaceState -> Either SurfaceCheckError Text
currentEndpoint located state = case stateActiveEndpoint state of
  Just name -> Right name
  Nothing -> case [name | (name, meta) <- Map.toAscList (stateBindings state), isEndpointTy (bindingType meta)] of
    [name] -> Right name
    [] -> throw located SessionAction "no live endpoint is available"
    _ -> throw located SessionAction "implicit close is ambiguous"

applySessionContext :: Text -> ResourceContext -> SurfaceState -> SurfaceState
applySessionContext consumedName context state =
  (consumeSurfaceName consumedName state)
    { stateCore = (stateCore state) { resourceContext = context }
    }

consumeSurfaceName :: Text -> SurfaceState -> SurfaceState
consumeSurfaceName name state = state
  { stateBindings = Map.delete name (stateBindings state)
  , stateActiveEndpoint = if stateActiveEndpoint state == Just name then Nothing else stateActiveEndpoint state
  }

extractLinearTemp :: Name -> SurfaceState -> Either SurfaceCheckError (ScalarValue, SurfaceState)
extractLinearTemp temp state = do
  (ty, context) <- mapCore syntheticSpan StructuralUse $
    consumeLinear temp (resourceContext (stateCore state))
  Right
    ( ScalarValue Linear ty (shapeForType ty)
    , state { stateCore = (stateCore state) { resourceContext = context } }
    )

freshName :: Text -> SurfaceState -> Either SurfaceCheckError (Name, SurfaceState)
freshName prefix state =
  let next = stateFresh state + 1
  in Right (Name (prefix <> "." <> Text.pack (show next)), state { stateFresh = next })

freshFrame :: SurfaceState -> (FrameId, SurfaceState)
freshFrame state =
  let next = stateFrame state + 1
  in (FrameId ("frame-" <> Text.pack (show next)), state { stateFrame = next })

removeScopedBinding :: Text -> SurfaceState -> Either SurfaceCheckError SurfaceState
removeScopedBinding name state = case Map.lookup name (stateBindings state) of
  Nothing -> Right state
  Just meta -> case bindingMode meta of
    Linear -> Left SurfaceCheckError
      { surfaceErrorSpan = syntheticSpan
      , surfaceErrorClass = LinearCompletion
      , surfaceErrorDetail = "cannot discard scoped linear binding: " <> name
      }
    Unrestricted -> Right (removeFromZone name Unrestricted state)
    Affine -> Right (removeFromZone name Affine state)

removeFromZone :: Text -> Mode -> SurfaceState -> SurfaceState
removeFromZone name mode state =
  let context = resourceContext (stateCore state)
      name' = Name name
      nextContext = case mode of
        Unrestricted -> context { unrestrictedBindings = Map.delete name' (unrestrictedBindings context) }
        Affine -> context { affineBindings = Map.delete name' (affineBindings context) }
        Linear -> context { linearBindings = Map.delete name' (linearBindings context) }
  in (consumeSurfaceName name state)
      { stateCore = (stateCore state) { resourceContext = nextContext }
      }

joinExclusive :: SourceSpan -> [SurfacePath] -> Either SurfaceCheckError [SurfacePath]
joinExclusive _ [] = Right []
joinExclusive span' paths = do
  let continuing = filter ((== PathContinue) . pathControl) paths
      stopped = filter ((/= PathContinue) . pathControl) paths
  case continuing of
    [] -> Right stopped
    [single] -> Right (stopped ++ [single])
    _ -> do
      joined <- mapCore span' IncompatibleBranchResidue $
        joinContinuing (map (resourceContext . stateCore . pathState) continuing)
      state <- joinMetadata span' continuing joined
      Right (stopped ++ [continuePath state])

joinMetadata :: SourceSpan -> [SurfacePath] -> ResourceContext -> Either SurfaceCheckError SurfaceState
joinMetadata span' paths joined = do
  let states = map pathState paths
      firstState = head states
      surviving = Map.filterWithKey (bindingSurvives joined) (stateBindings firstState)
  mapM_ (ensureAgrees surviving) (tail states)
  Right firstState
    { stateCore = (stateCore firstState) { resourceContext = joined }
    , stateBindings = surviving
    , stateFresh = maximum (map stateFresh states)
    , stateFrame = maximum (map stateFrame states)
    , stateActiveEndpoint = commonActiveEndpoint states surviving
    }
  where
    ensureAgrees surviving state = mapM_ (\(name, meta) ->
      case Map.lookup name (stateBindings state) of
        Just other | other == meta -> Right ()
        _ -> Left SurfaceCheckError
          { surfaceErrorSpan = span'
          , surfaceErrorClass = IncompatibleBranchResidue
          , surfaceErrorDetail = "continuing branches disagree on metadata for " <> name
          }) (Map.toList surviving)

bindingSurvives :: ResourceContext -> Text -> BindingMeta -> Bool
bindingSurvives context name meta = case bindingMode meta of
  Unrestricted -> Map.member (Name name) (unrestrictedBindings context)
  Affine -> Map.member (Name name) (affineBindings context)
  Linear -> Map.member (Name name) (linearBindings context)

commonActiveEndpoint :: [SurfaceState] -> Map Text BindingMeta -> Maybe Text
commonActiveEndpoint states surviving =
  case map stateActiveEndpoint states of
    first : rest | all (== first) rest -> first
    _ -> case [name | (name, meta) <- Map.toList surviving, isEndpointTy (bindingType meta)] of
      [name] -> Just name
      _ -> Nothing

finalizePath :: SurfaceEnvironment -> SourceSpan -> SurfacePath -> Either SurfaceCheckError SurfacePath
finalizePath environment span' path = do
  case pathControl path of
    PathContinue -> ensureTerminalState environment span' Nothing (pathState path)
    PathReturn _ -> ensureTerminalState environment span' Nothing (pathState path)
    PathClosed outcome -> ensureTerminalState environment span' (Just outcome) (pathState path)
    PathFailed _ _ -> ensureTerminalState environment span' (Just (Outcome "failure")) (pathState path)
  Right path

ensureTerminalState
  :: SurfaceEnvironment
  -> SourceSpan
  -> Maybe Outcome
  -> SurfaceState
  -> Either SurfaceCheckError ()
ensureTerminalState environment span' maybeOutcome state =
  let allowed = maybe Set.empty (\outcome -> Map.findWithDefault Set.empty outcome (surfaceTerminalAllowances environment)) maybeOutcome
      context = resourceContext (stateCore state)
      reduced = context { linearBindings = Map.withoutKeys (linearBindings context) (Set.map Name allowed) }
  in case ensureComplete reduced of
      Right () -> Right ()
      Left errorValue -> Left SurfaceCheckError
        { surfaceErrorSpan = span'
        , surfaceErrorClass = LinearCompletion
        , surfaceErrorDetail = Text.pack (show errorValue)
        }

toCoreControl :: SurfacePath -> Control
toCoreControl path = case pathControl path of
  PathContinue -> Continue
  PathReturn ty -> Return ty
  PathClosed outcome -> Closed outcome
  PathFailed failureClass detail -> Failed failureClass detail

resolveSurfaceType
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceType
  -> Either SurfaceCheckError (Mode, Ty, SurfaceShape)
resolveSurfaceType environment state surfaceTy = case locatedValue surfaceTy of
  SurfaceNamedType "OwnedBytes" [indexSource] -> do
    raw <- mapElaboration indexSource $ elaborateRefTerm (elaborationEnv environment state) indexSource
    (index, _) <- mapFocusing indexSource $
      elaborateRefTermAs (surfaceStaticContext environment) (stateCore state) SortNat (rewriteRefTerm state raw)
    Right (Linear, TyBytes index, OwnedBytesShape index)
  SurfaceNamedType "StoreCap" _ -> opaque Affine
  SurfaceNamedType "CancelScope" _ -> opaque Linear
  SurfaceNamedType "CancelCap" _ -> opaque Affine
  _ -> do
    ty <- mapElaboration surfaceTy $ elaborateType (elaborationEnv environment state) surfaceTy
    Right (defaultMode ty, ty, shapeForType ty)
  where
    opaque mode = do
      ty <- mapElaboration surfaceTy $ elaborateType (elaborationEnv environment state) surfaceTy
      Right (mode, ty, PlainShape)

defaultMode :: Ty -> Mode
defaultMode ty = case ty of
  TyEndpoint _ -> Linear
  TyPendingRecv _ -> Linear
  _ -> Unrestricted

messageMode :: Ty -> Mode
messageMode ty = case stripRefinement ty of
  TyBytes _ -> Linear
  _ -> defaultMode ty

stripRefinement :: Ty -> Ty
stripRefinement (TyRefined _ inner _) = stripRefinement inner
stripRefinement ty = ty

shapeForType :: Ty -> SurfaceShape
shapeForType ty = case stripRefinement ty of
  TyFrame (GrammarId grammar) -> recordShape grammar Nothing
  TyBytes index -> OwnedBytesShape index
  _ -> PlainShape

recordShape :: Text -> Maybe Text -> SurfaceShape
recordShape grammar base = case grammar of
  "Hello" -> RecordShape "Hello" (Map.fromList
    [ ("versions", field "versions" (TyOpaqueSorted "Versions" versionSetSort) versionSetSort)
    ])
  "Begin" -> RecordShape "Begin" (Map.fromList
    [ ("length", field "length" (TyUInt 64) (SortUInt 64))
    , ("kind", field "kind" (TyOpaqueSorted "PayloadKind" (SortEnum "PayloadKind")) (SortEnum "PayloadKind"))
    , ("digestAlg", field "digestAlg" (TyOpaque "DigestAlgorithm") (SortOpaque "DigestAlgorithm"))
    , ("digest", field "digest" (TyOpaque "Digest") (SortOpaque "Digest"))
    ])
  _ -> RecordShape grammar Map.empty
  where
    field name ty sort = FieldInfo ty sort (fmap (\binder -> RefField (RefVar (Name binder)) name sort) base)

grammarOfTy :: Ty -> Maybe Text
grammarOfTy ty = case stripRefinement ty of
  TyFrame (GrammarId grammar) -> Just grammar
  _ -> Nothing

isBytesTy :: Ty -> Bool
isBytesTy ty = case stripRefinement ty of
  TyBytes _ -> True
  _ -> False

isEndpointTy :: Ty -> Bool
isEndpointTy (TyEndpoint _) = True
isEndpointTy _ = False

isRefined :: Ty -> Bool
isRefined TyRefined {} = True
isRefined _ = False

rewriteTy :: SurfaceState -> Ty -> Ty
rewriteTy state ty = case ty of
  TyBytes index -> TyBytes (rewriteRefTerm state index)
  TyProof proposition -> TyProof (rewriteProposition state proposition)
  TyRefined binder base proposition -> TyRefined binder (rewriteTy state base) (rewriteProposition state proposition)
  other -> other

rewriteProposition :: SurfaceState -> Proposition -> Proposition
rewriteProposition state proposition = case proposition of
  Truth -> Truth
  Falsehood -> Falsehood
  Equal left right -> Equal (term left) (term right)
  NotEqual left right -> NotEqual (term left) (term right)
  LessThan left right -> LessThan (term left) (term right)
  LessEqual left right -> LessEqual (term left) (term right)
  Member value collection -> Member (term value) (term collection)
  Disjoint left right -> Disjoint (term left) (term right)
  Conjunction left right -> Conjunction (rewriteProposition state left) (rewriteProposition state right)
  Disjunction left right -> Disjunction (rewriteProposition state left) (rewriteProposition state right)
  Negation inner -> Negation (rewriteProposition state inner)
  Atom claim arguments -> Atom claim (map term arguments)
  where
    term = rewriteRefTerm state

rewriteRefTerm :: SurfaceState -> RefTerm -> RefTerm
rewriteRefTerm state term = case term of
  RefField (RefVar (Name base)) field sort ->
    case Map.lookup base (stateBindings state) >>= fieldAliasFor field of
      Just alias -> rewriteRefTerm state alias
      Nothing -> RefField (RefVar (Name base)) field sort
  RefField base field sort -> RefField (rewriteRefTerm state base) field sort
  RefLen value -> RefLen (rewriteRefTerm state value)
  RefToNat value -> RefToNat (rewriteRefTerm state value)
  RefAdd left right -> RefAdd (rewriteRefTerm state left) (rewriteRefTerm state right)
  RefSub left right -> RefSub (rewriteRefTerm state left) (rewriteRefTerm state right)
  RefScale coefficient value -> RefScale coefficient (rewriteRefTerm state value)
  other -> other

fieldAliasFor :: Text -> BindingMeta -> Maybe RefTerm
fieldAliasFor field meta = case bindingShape meta of
  RecordShape _ fields -> Map.lookup field fields >>= fieldAlias
  OwnedBytesShape _ -> case field of
    "length" -> Just (RefField (RefVar (bindingNamePlaceholder meta)) "length" (SortUInt 64))
    "id" -> Just payloadStableTerm
    _ -> Nothing
  _ -> Nothing

-- Owned-byte aliases are generated by elaboration from the actual variable path;
-- this placeholder branch is never selected for a directly projected binding.
bindingNamePlaceholder :: BindingMeta -> Name
bindingNamePlaceholder _ = Name "$owned"

elaborationEnv :: SurfaceEnvironment -> SurfaceState -> ElaborationEnv
elaborationEnv environment state = foldl add base (concatMap projections (Map.toList (stateBindings state)))
  where
    base = emptyElaborationEnv (surfaceStaticContext environment) (stateCore state)
    add current (path, sort) = withProjectionSort path sort current
    projections (name, meta) = case bindingShape meta of
      RecordShape _ fields -> [([name, field], fieldSort info) | (field, info) <- Map.toList fields]
      OwnedBytesShape _ ->
        [ ([name, "length"], SortUInt 64)
        , ([name, "kind"], SortEnum "PayloadKind")
        , ([name, "id"], SortStableId "OwnedBytes")
        ]
      ExternalParsedShape grammar _ -> case recordShape grammar (Just name) of
        RecordShape _ fields -> [([name, field], fieldSort info) | (field, info) <- Map.toList fields]
        _ -> []
      _ -> []

checkBranchPayloadTerm :: SurfaceState -> Located SurfaceExpression -> Ty -> Either SurfaceCheckError ()
checkBranchPayloadTerm state expression expected = case locatedValue expression of
  VariableExpression name -> do
    meta <- lookupMeta expression name state
    case compareTypes (rewriteTy state (bindingType meta)) (rewriteTy state expected) of
      DefinitionallyEqual -> Right ()
      RequiresPropositionalEquality -> throw expression ExplicitTransport "branch payload requires explicit transport"
      IncompatibleTypes -> throw expression TypeMismatch "branch payload has the wrong type"
  _ -> Right ()

mapBranchExhaustiveness :: Located a -> [Branch] -> [Text] -> Either SurfaceCheckError ()
mapBranchExhaustiveness located branches handlers =
  case checkBranchExhaustiveness branches handlers of
    Right () -> Right ()
    Left errorValue -> Left SurfaceCheckError
      { surfaceErrorSpan = locatedSpan located
      , surfaceErrorClass = BranchExhaustiveness
      , surfaceErrorDetail = Text.pack (show errorValue)
      }

dischargedRequirement :: FocusedRequirement -> Bool
dischargedRequirement requirement = case focusedMechanism requirement of
  FocusByDefinition -> True
  FocusByEvidence _ -> True
  _ -> False

solveRequirement :: SurfaceState -> FocusedRequirement -> Either SurfaceCheckError Bool
solveRequirement state requirement = case focusedMechanism requirement of
  FocusNeedsDecisionProcedure -> case proposeDecisionCertificate (stateCore state) [] (focusedCanonical requirement) of
    Nothing -> Right False
    Just certificate -> case checkDecisionCertificate (stateCore state) [] (focusedCanonical requirement) certificate of
      Right () -> Right True
      Left _ -> Right False
  _ -> Right False

propositionMentionsUnchecked :: SurfaceState -> Proposition -> Bool
propositionMentionsUnchecked state proposition = any tainted (propositionNames proposition)
  where
    tainted (Name name) = case Map.lookup name (stateBindings state) of
      Just meta -> bindingShape meta == UncheckedArithmeticShape
      Nothing -> False

propositionNames :: Proposition -> [Name]
propositionNames proposition = case proposition of
  Truth -> []
  Falsehood -> []
  Equal left right -> names left ++ names right
  NotEqual left right -> names left ++ names right
  LessThan left right -> names left ++ names right
  LessEqual left right -> names left ++ names right
  Member left right -> names left ++ names right
  Disjoint left right -> names left ++ names right
  Conjunction left right -> propositionNames left ++ propositionNames right
  Disjunction left right -> propositionNames left ++ propositionNames right
  Negation inner -> propositionNames inner
  Atom _ arguments -> concatMap names arguments
  where
    names = termNames

termNames :: RefTerm -> [Name]
termNames term = case term of
  RefVar name -> [name]
  RefField base _ _ -> termNames base
  RefLen value -> termNames value
  RefToNat value -> termNames value
  RefAdd left right -> termNames left ++ termNames right
  RefSub left right -> termNames left ++ termNames right
  RefScale _ value -> termNames value
  _ -> []

applyValueResult :: Text -> SurfaceState -> ValueResult -> SurfaceState
applyValueResult source state result =
  let next = state { stateCore = valueResultState result }
      name = Name source
      context = resourceContext (stateCore next)
      stillPresent = Map.member name (unrestrictedBindings context)
        || Map.member name (affineBindings context)
        || Map.member name (linearBindings context)
  in if stillPresent then next else consumeSurfaceName source next

fromMaybeMode :: Maybe BindingMeta -> Mode
fromMaybeMode = maybe Unrestricted bindingMode

serverSupportedTerm :: RefTerm
serverSupportedTerm = RefVar (Name "serverSupported")

helloVersionsTerm :: RefTerm
helloVersionsTerm = RefField (RefVar (Name "hello")) "versions" versionSetSort

payloadStableTerm :: RefTerm
payloadStableTerm = RefOpaque (SortStableId "OwnedBytes") "payload"

digestMatchesProposition :: Proposition
digestMatchesProposition = Atom "DigestMatches" [RefVar (Name "begin"), payloadStableTerm]

versionSetSort :: RefSort
versionSetSort = SortFiniteSet (SortUInt 16)

byteSequenceSort :: RefSort
byteSequenceSort = SortFiniteSeq (SortUInt 8)

mapCore :: SourceSpan -> RejectionClass -> Either CheckError a -> Either SurfaceCheckError a
mapCore span' rejection = either (\errorValue -> Left SurfaceCheckError
  { surfaceErrorSpan = span'
  , surfaceErrorClass = rejection
  , surfaceErrorDetail = Text.pack (show errorValue)
  }) Right

mapSession :: Located a -> Either SessionError b -> Either SurfaceCheckError b
mapSession located = either (\errorValue -> Left SurfaceCheckError
  { surfaceErrorSpan = locatedSpan located
  , surfaceErrorClass = SessionAction
  , surfaceErrorDetail = Text.pack (show errorValue)
  }) Right

mapRecognition :: Located a -> Either RecognitionError b -> Either SurfaceCheckError b
mapRecognition located = either (\errorValue -> Left SurfaceCheckError
  { surfaceErrorSpan = locatedSpan located
  , surfaceErrorClass = RecognitionProvenance
  , surfaceErrorDetail = Text.pack (show errorValue)
  }) Right

mapFocusing :: Located a -> Either FocusingError b -> Either SurfaceCheckError b
mapFocusing located = either (\errorValue -> Left SurfaceCheckError
  { surfaceErrorSpan = locatedSpan located
  , surfaceErrorClass = MissingEvidence
  , surfaceErrorDetail = Text.pack (show errorValue)
  }) Right

mapElaboration :: Located a -> Either ElaborationError b -> Either SurfaceCheckError b
mapElaboration located = either (\errorValue -> Left SurfaceCheckError
  { surfaceErrorSpan = locatedSpan located
  , surfaceErrorClass = TypeMismatch
  , surfaceErrorDetail = Text.pack (show errorValue)
  }) Right

mapValueResult :: Located a -> Either ValueError b -> Either SurfaceCheckError b
mapValueResult located = either (Left . valueError located) Right

valueError :: Located a -> ValueError -> SurfaceCheckError
valueError located errorValue = SurfaceCheckError
  { surfaceErrorSpan = locatedSpan located
  , surfaceErrorClass = case errorValue of
      ExplicitTransportRequired _ _ -> ExplicitTransport
      ValueResourceError _ -> StructuralUse
      ValueRefinementError _ -> MissingEvidence
      _ -> TypeMismatch
  , surfaceErrorDetail = Text.pack (show errorValue)
  }

throw :: Located a -> RejectionClass -> Text -> Either SurfaceCheckError b
throw located rejection detail = Left SurfaceCheckError
  { surfaceErrorSpan = locatedSpan located
  , surfaceErrorClass = rejection
  , surfaceErrorDetail = detail
  }

syntheticSpan :: SourceSpan
syntheticSpan = SourceSpan point point
  where
    point = SourcePoint "<architecture>" 1 1 0
