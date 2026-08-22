{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.Check.Support
  ( emptySurfaceState
  , continuePath
  , valuePath
  , runtimeType
  , restrictedRuntimeValue
  , insertBindingMeta
  , lookupMeta
  , moveVariable
  , consumeSurfaceName
  , applySessionContext
  , freshName
  , freshFrame
  , extractLinearTemp
  , removeScopedBinding
  , resolveSurfaceType
  , defaultMode
  , messageMode
  , stripRefinement
  , shapeForType
  , shapeForBinding
  , recordShape
  , grammarOfTy
  , isBytesTy
  , isEndpointTy
  , isRefined
  , rewriteTy
  , rewriteProposition
  , rewriteRefTerm
  , elaborationEnv
  , inferReadOnlyScalar
  , readField
  , constructValue
  , optionalRefTerm
  , sessionSendMessage
  , sessionReceiveMessage
  , sessionReceiveFrameGrammar
  , sessionSelectBranch
  , sessionOfferBranches
  , requireMessage
  , endpointName
  , namedExpression
  , currentEndpoint
  , mapCore
  , mapSession
  , mapRecognition
  , mapFocusing
  , mapElaboration
  , mapValueResult
  , valueError
  , throw
  , syntheticSpan
  , versionSetSort
  , byteSequenceSort
  , payloadStableTerm
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Checker (CheckState (..), emptyCheckState)
import Phil.Core.Context
  ( CheckError
  , ResourceContext (..)
  , consumeLinear
  , insertBinding
  , useBinding
  )
import Phil.Core.Focusing (FocusingError, elaborateRefTermAs)
import Phil.Core.Recognition (RecognitionError)
import Phil.Core.Session
  ( MessageSpec (..)
  , SessionError
  , SessionStep (..)
  , exposeSessionHead
  )
import Phil.Core.SortCheck (refSortOfTy)
import Phil.Core.Syntax
  ( Branch (..)
  , FrameId (..)
  , GrammarId (..)
  , Mode (..)
  , Name (..)
  , Proposition (..)
  , RefSort (..)
  , RefTerm (..)
  , Session (..)
  , Ty (..)
  )
import Phil.Core.Value (ValueError (..))
import Phil.Surface.Check.Types
import Phil.Surface.Elaborate
  ( ElaborationEnv
  , ElaborationError
  , elaborateRefTerm
  , elaborateType
  , emptyElaborationEnv
  , withProjectionSort
  )
import Phil.Surface.Syntax
  ( Located (..)
  , SourcePoint (..)
  , SourceSpan (..)
  , SurfaceExpression (..)
  , SurfaceType (..)
  )

emptySurfaceState :: SurfaceState
emptySurfaceState = SurfaceState
  { stateCore = emptyCheckState
  , stateBindings = Map.empty
  , stateFresh = 0
  , stateFrame = 0
  , stateActiveEndpoint = Nothing
  }

continuePath :: SurfaceState -> SurfacePath
continuePath state = SurfacePath PathContinue state Nothing

valuePath :: SurfaceState -> RuntimeValue -> SurfacePath
valuePath state value = SurfacePath PathContinue state (Just value)

runtimeType :: RuntimeValue -> Ty
runtimeType RuntimeUnit = TyUnit
runtimeType (RuntimeScalar scalar) = scalarType scalar
runtimeType (RuntimeTuple values) = TyOpaque ("Tuple[" <> Text.pack (show (length values)) <> "]")

restrictedRuntimeValue :: RuntimeValue -> Bool
restrictedRuntimeValue RuntimeUnit = False
restrictedRuntimeValue (RuntimeScalar scalar) = scalarMode scalar /= Unrestricted
restrictedRuntimeValue (RuntimeTuple values) = any restrictedRuntimeValue values

insertBindingMeta
  :: SourceSpan
  -> Text
  -> BindingMeta
  -> SurfaceState
  -> Either SurfaceCheckError SurfaceState
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

lookupMeta :: Located a -> Text -> SurfaceState -> Either SurfaceCheckError BindingMeta
lookupMeta located name state =
  case Map.lookup name (stateBindings state) of
    Just meta -> Right meta
    Nothing -> throw located StructuralUse ("unknown or consumed binding: " <> name)

moveVariable
  :: Located a
  -> Text
  -> SurfaceState
  -> Either SurfaceCheckError (ScalarValue, SurfaceState)
moveVariable located name state = do
  meta <- lookupMeta located name state
  (mode, ty, context) <- mapCore (locatedSpan located) StructuralUse $
    useBinding (Name name) (resourceContext (stateCore state))
  let next = state
        { stateCore = (stateCore state) { resourceContext = context }
        , stateBindings =
            if mode == Unrestricted then stateBindings state else Map.delete name (stateBindings state)
        , stateActiveEndpoint =
            if mode /= Unrestricted && stateActiveEndpoint state == Just name
              then Nothing
              else stateActiveEndpoint state
        }
  Right (ScalarValue mode ty (bindingShape meta), next)

consumeSurfaceName :: Text -> SurfaceState -> SurfaceState
consumeSurfaceName name state = state
  { stateBindings = Map.delete name (stateBindings state)
  , stateActiveEndpoint =
      if stateActiveEndpoint state == Just name then Nothing else stateActiveEndpoint state
  }

applySessionContext :: Text -> ResourceContext -> SurfaceState -> SurfaceState
applySessionContext consumedName context state =
  (consumeSurfaceName consumedName state)
    { stateCore = (stateCore state) { resourceContext = context }
    }

freshName :: Text -> SurfaceState -> (Name, SurfaceState)
freshName prefix state =
  let next = stateFresh state + 1
  in (Name (prefix <> "." <> Text.pack (show next)), state { stateFresh = next })

freshFrame :: SurfaceState -> (FrameId, SurfaceState)
freshFrame state =
  let next = stateFrame state + 1
  in (FrameId ("frame-" <> Text.pack (show next)), state { stateFrame = next })

extractLinearTemp
  :: SourceSpan
  -> Name
  -> SurfaceState
  -> Either SurfaceCheckError (ScalarValue, SurfaceState)
extractLinearTemp span' temp state = do
  (ty, context) <- mapCore span' StructuralUse $
    consumeLinear temp (resourceContext (stateCore state))
  Right
    ( ScalarValue Linear ty (shapeForType ty)
    , state { stateCore = (stateCore state) { resourceContext = context } }
    )

removeScopedBinding :: SourceSpan -> Text -> SurfaceState -> Either SurfaceCheckError SurfaceState
removeScopedBinding span' name state =
  case Map.lookup name (stateBindings state) of
    Nothing -> Right state
    Just meta -> case bindingMode meta of
      Linear -> Left SurfaceCheckError
        { surfaceErrorSpan = span'
        , surfaceErrorClass = LinearCompletion
        , surfaceErrorDetail = "cannot discard scoped linear binding: " <> name
        }
      Unrestricted -> Right (removeFromZone name Unrestricted state)
      Affine -> Right (removeFromZone name Affine state)

removeFromZone :: Text -> Mode -> SurfaceState -> SurfaceState
removeFromZone name mode state =
  let context = resourceContext (stateCore state)
      coreName = Name name
      nextContext = case mode of
        Unrestricted -> context { unrestrictedBindings = Map.delete coreName (unrestrictedBindings context) }
        Affine -> context { affineBindings = Map.delete coreName (affineBindings context) }
        Linear -> context { linearBindings = Map.delete coreName (linearBindings context) }
  in (consumeSurfaceName name state)
      { stateCore = (stateCore state) { resourceContext = nextContext } }

resolveSurfaceType
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceType
  -> Either SurfaceCheckError (Mode, Ty, SurfaceShape)
resolveSurfaceType environment state surfaceTy =
  case locatedValue surfaceTy of
    SurfaceNamedType "OwnedBytes" [indexSource] -> do
      raw <- mapElaboration indexSource $
        elaborateRefTerm (elaborationEnv environment state) indexSource
      (index, _) <- mapFocusing indexSource $
        elaborateRefTermAs
          (surfaceStaticContext environment)
          (stateCore state)
          SortNat
          (rewriteRefTerm state raw)
      Right (Linear, TyBytes index, OwnedBytesShape index)
    SurfaceNamedType "StoreCap" _ -> opaque Affine
    SurfaceNamedType "CancelScope" _ -> opaque Linear
    SurfaceNamedType "CancelCap" _ -> opaque Affine
    _ -> do
      ty <- mapElaboration surfaceTy $
        elaborateType (elaborationEnv environment state) surfaceTy
      Right (defaultMode ty, ty, shapeForType ty)
  where
    opaque mode = do
      ty <- mapElaboration surfaceTy $
        elaborateType (elaborationEnv environment state) surfaceTy
      Right (mode, ty, PlainShape)

defaultMode :: Ty -> Mode
defaultMode ty = case ty of
  TyEndpoint _ -> Linear
  TyPendingRecv _ -> Linear
  _ -> Unrestricted

messageMode :: Ty -> Mode
messageMode ty = case stripRefinement ty of
  TyBytes _ -> Linear
  other -> defaultMode other

stripRefinement :: Ty -> Ty
stripRefinement (TyRefined _ inner _) = stripRefinement inner
stripRefinement ty = ty

shapeForType :: Ty -> SurfaceShape
shapeForType ty = case stripRefinement ty of
  TyFrame (GrammarId grammar) -> recordShape grammar Nothing
  TyBytes index -> OwnedBytesShape index
  _ -> PlainShape

shapeForBinding :: Text -> SurfaceShape -> SurfaceShape
shapeForBinding name shape = case shape of
  RecordShape record fields -> RecordShape record (Map.mapWithKey rebase fields)
    where
      rebase field info = case fieldAlias info of
        Just _ -> info
        Nothing -> info
          { fieldAlias = Just (RefField (RefVar (Name name)) field (fieldSort info))
          }
  other -> other

recordShape :: Text -> Maybe Text -> SurfaceShape
recordShape grammar base = case grammar of
  "Hello" -> RecordShape "Hello" (Map.fromList
    [ ("versions", field "versions" (TyOpaqueSorted "Versions" versionSetSort) versionSetSort)
    ])
  "Begin" -> RecordShape "Begin" (Map.fromList
    [ ("length", field "length" (TyUInt 64) (SortUInt 64))
    , ("kind", field "kind"
        (TyOpaqueSorted "PayloadKind" (SortEnum "PayloadKind"))
        (SortEnum "PayloadKind"))
    , ("digestAlg", field "digestAlg"
        (TyOpaque "DigestAlgorithm")
        (SortOpaque "DigestAlgorithm"))
    , ("digest", field "digest" (TyOpaque "Digest") (SortOpaque "Digest"))
    ])
  _ -> RecordShape grammar Map.empty
  where
    field fieldName ty sort = FieldInfo ty sort $
      fmap (\binder -> RefField (RefVar (Name binder)) fieldName sort) base

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
  TyRefined binder base proposition ->
    TyRefined binder (rewriteTy state base) (rewriteProposition state proposition)
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

-- | Resolve semantic aliases without assuming that an alias graph is acyclic.
-- Self projections such as begin.length are legitimate canonical terms, so a
-- fixed point is a normal stopping condition rather than a recursive rewrite.
rewriteRefTerm :: SurfaceState -> RefTerm -> RefTerm
rewriteRefTerm state = go Set.empty
  where
    go seen term
      | Set.member term seen = term
      | otherwise =
          let seen' = Set.insert term seen
          in case term of
            RefField (RefVar (Name base)) field sort ->
              let original = RefField (RefVar (Name base)) field sort
              in case Map.lookup base (stateBindings state) >>= fieldAliasFor field of
                Just alias
                  | alias /= original -> go seen' alias
                _ -> original
            RefField base field sort -> RefField (go seen' base) field sort
            RefLen value -> RefLen (go seen' value)
            RefToNat value -> RefToNat (go seen' value)
            RefAdd left right -> RefAdd (go seen' left) (go seen' right)
            RefSub left right -> RefSub (go seen' left) (go seen' right)
            RefScale coefficient value -> RefScale coefficient (go seen' value)
            other -> other

fieldAliasFor :: Text -> BindingMeta -> Maybe RefTerm
fieldAliasFor field meta = case bindingShape meta of
  RecordShape _ fields -> Map.lookup field fields >>= fieldAlias
  -- Owned-byte projections are already canonical in the surface variable's
  -- identity.  Rewriting them through a synthetic placeholder would destroy
  -- the equality between payload.length and a Begin field constructed from it.
  OwnedBytesShape _ -> Nothing
  _ -> Nothing

elaborationEnv :: SurfaceEnvironment -> SurfaceState -> ElaborationEnv
elaborationEnv environment state =
  foldl add base (concatMap projections (Map.toList (stateBindings state)))
  where
    base = emptyElaborationEnv (surfaceStaticContext environment) (stateCore state)
    add current (path, sort) = withProjectionSort path sort current

    projections (name, meta) = case bindingShape meta of
      RecordShape _ fields ->
        [ ([name, fieldName], fieldSort info)
        | (fieldName, info) <- Map.toList fields
        ]
      OwnedBytesShape _ ->
        [ ([name, "length"], SortUInt 64)
        , ([name, "kind"], SortEnum "PayloadKind")
        , ([name, "id"], SortStableId "OwnedBytes")
        ]
      ExternalParsedShape grammar _ -> case recordShape grammar (Just name) of
        RecordShape _ fields ->
          [ ([name, fieldName], fieldSort info)
          | (fieldName, info) <- Map.toList fields
          ]
        _ -> []
      _ -> []

inferReadOnlyScalar
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Either SurfaceCheckError ScalarValue
inferReadOnlyScalar environment state located = case locatedValue located of
  VariableExpression name -> do
    meta <- lookupMeta located name state
    Right (ScalarValue (bindingMode meta) (bindingType meta) (bindingShape meta))
  IntegerExpression literal -> Right $
    ScalarValue Unrestricted (TyOpaque ("Integer[" <> Text.pack (show literal) <> "]")) PlainShape
  BooleanExpression _ -> Right (ScalarValue Unrestricted TyBool (DecisionShape BooleanDecision))
  UnitExpression -> Right (ScalarValue Unrestricted TyUnit PlainShape)
  FieldExpression base field -> readField environment state located base field
  BinaryExpression _ _ _ -> Right $
    ScalarValue Unrestricted (TyOpaqueSorted "NatExpr" SortNat) PlainShape
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
    ParsedShape _ grammar
      | field == "value" -> semanticValue grammar
    LegacyParsedShape _ _ grammar
      | field == "value" -> semanticValue grammar
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

    semanticValue grammar = Right $
      ScalarValue Unrestricted (TyFrame (GrammarId grammar)) (recordShape grammar Nothing)

    semanticField grammar = case recordShape grammar (baseVariable base) of
      RecordShape _ fields -> fieldFrom fields
      _ -> throw whole IllegalProjection "internal record-shape error"

    ownedBytesField = case field of
      "length" -> Right (ScalarValue Unrestricted (TyUInt 64) PlainShape)
      "kind" -> Right $
        ScalarValue Unrestricted
          (TyOpaqueSorted "PayloadKind" (SortEnum "PayloadKind"))
          PlainShape
      "id" -> Right $
        ScalarValue Unrestricted
          (TyOpaqueSorted "PayloadId" (SortStableId "OwnedBytes"))
          PlainShape
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

    fieldEntry fieldName = do
      expression <- case Map.lookup fieldName table of
        Just value -> Right value
        Nothing -> throw located TypeMismatch ("missing constructor field: " <> fieldName)
      scalar <- inferReadOnlyScalar environment state expression
      sort <- case refSortOfTy (scalarType scalar) of
        Just result -> Right result
        Nothing -> throw expression TypeMismatch "constructor field is not refinement-visible"
      alias <- optionalRefTerm environment state expression
      Right (fieldName, FieldInfo (scalarType scalar) sort alias)

optionalRefTerm
  :: SurfaceEnvironment
  -> SurfaceState
  -> Located SurfaceExpression
  -> Either SurfaceCheckError (Maybe RefTerm)
optionalRefTerm environment state expression =
  case elaborateRefTerm (elaborationEnv environment state) expression of
    Right term -> Right (Just (rewriteRefTerm state term))
    Left _ -> Right Nothing

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

sessionSelectBranch
  :: Located a
  -> BindingMeta
  -> Text
  -> Either SurfaceCheckError (Maybe MessageSpec, Session)
sessionSelectBranch located meta label = case bindingType meta of
  TyEndpoint session -> do
    headSession <- mapSession located (exposeSessionHead session)
    case headSession of
      Select branches -> case filter ((== label) . branchLabel) branches of
        [branch] -> Right
          ( fmap (uncurry MessageSpec) (branchPayload branch)
          , branchContinuation branch
          )
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
  Nothing -> case
    [ name
    | (name, meta) <- Map.toAscList (stateBindings state)
    , isEndpointTy (bindingType meta)
    ] of
      [name] -> Right name
      [] -> throw located SessionAction "no live endpoint is available"
      _ -> throw located SessionAction "implicit close is ambiguous"

mapCore :: SourceSpan -> RejectionClass -> Either CheckError a -> Either SurfaceCheckError a
mapCore span' rejection = either
  (\errorValue -> Left SurfaceCheckError
    { surfaceErrorSpan = span'
    , surfaceErrorClass = rejection
    , surfaceErrorDetail = Text.pack (show errorValue)
    })
  Right

mapSession :: Located a -> Either SessionError b -> Either SurfaceCheckError b
mapSession located = either
  (\errorValue -> Left SurfaceCheckError
    { surfaceErrorSpan = locatedSpan located
    , surfaceErrorClass = SessionAction
    , surfaceErrorDetail = Text.pack (show errorValue)
    })
  Right

mapRecognition :: Located a -> Either RecognitionError b -> Either SurfaceCheckError b
mapRecognition located = either
  (\errorValue -> Left SurfaceCheckError
    { surfaceErrorSpan = locatedSpan located
    , surfaceErrorClass = RecognitionProvenance
    , surfaceErrorDetail = Text.pack (show errorValue)
    })
  Right

mapFocusing :: Located a -> Either FocusingError b -> Either SurfaceCheckError b
mapFocusing located = either
  (\errorValue -> Left SurfaceCheckError
    { surfaceErrorSpan = locatedSpan located
    , surfaceErrorClass = MissingEvidence
    , surfaceErrorDetail = Text.pack (show errorValue)
    })
  Right

mapElaboration :: Located a -> Either ElaborationError b -> Either SurfaceCheckError b
mapElaboration located = either
  (\errorValue -> Left SurfaceCheckError
    { surfaceErrorSpan = locatedSpan located
    , surfaceErrorClass = TypeMismatch
    , surfaceErrorDetail = Text.pack (show errorValue)
    })
  Right

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

versionSetSort :: RefSort
versionSetSort = SortFiniteSet (SortUInt 16)

byteSequenceSort :: RefSort
byteSequenceSort = SortFiniteSeq (SortUInt 8)

payloadStableTerm :: RefTerm
payloadStableTerm = RefOpaque (SortStableId "OwnedBytes") "payload"
