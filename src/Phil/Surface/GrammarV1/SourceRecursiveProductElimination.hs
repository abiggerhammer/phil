{-# LANGUAGE OverloadedStrings #-}

-- | FSEM-01 DATA-04/05E: source-owned finite binary product-tree admission.
--
-- Arbitrary finite tuple nesting over primitive leaves is elaborated by
-- structural recursion. Exactly ONE Bytes[N] Linear leaf may be returned.
-- Every other source-checked leaf is Unrestricted. No caller provides an
-- environment, product contract or generated Core owner identity.
-- C/D's separate bounded production entry points are unchanged.
module Phil.Surface.GrammarV1.SourceRecursiveProductElimination
  ( RecursiveProductError (..)
  , RecursiveProductStep (..)
  , RecursiveProductTrace (..)
  , grammarV1CheckedRecursiveProductElimination
  ) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import qualified Phil.Core.Context as Core
import qualified Phil.Core.DataMode as ProductMode
import Phil.Core.Focusing (FocusingError)
import Phil.Core.Static (DeclarationKey, StaticContext)
import Phil.Core.Syntax
  ( Control (..), Mode (..), Name (..), ProductElementType (..)
  , Ty (..) )
import Phil.Surface.Check.Engine
  ( ProductEliminationRun (..), checkSurfaceComponent
  , traceSurfaceProductEliminationComponent )
import Phil.Surface.Check.Support (emptySurfaceState, shapeForType)
import Phil.Surface.Check.Types
  ( InitialBinding (..), RejectionClass (..), SurfaceCheckError (..)
  , SurfaceCheckResult (..), SurfaceEnvironment (..), emptySurfaceEnvironment )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError, GrammarV1ResolvedBinder (..)
  , grammarV1FunctionParameterScope )
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedTypeMode)
import Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep (..), GrammarV1LetPatternScopeError
  , grammarV1CheckedLetPatternBlockInScope )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..) )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..), GrammarV1FunctionDecl (..)
  , GrammarV1Pattern (..), GrammarV1Statement (..)
  , GrammarV1TermParam (..), GrammarV1Type (..) )
import Phil.Surface.Syntax
  ( Block (..), Component (..), Located (..), Pattern (..)
  , SourceSpan, Statement (..), SurfaceExpression (..) )

data RecursiveProductError
  = RecursiveParameterError GrammarV1BinderScopeError
  | RecursiveLetError GrammarV1LetPatternScopeError
  | RecursiveLeafTypeError FocusingError
  | RecursiveSourceMismatch Text
  | RecursiveNativeError ProductMode.ProductError
  | RecursiveSurfaceError SurfaceCheckError
  | RecursiveTransitionMismatch Text
  deriving (Eq, Show)

-- | An actual reached production Surface transition, independently compared
-- with the Core operation on the exact predecessor context.
data RecursiveProductStep = RecursiveProductStep
  { recursiveStepSourceOwner :: Name
  , recursiveStepSourceSpan :: SourceSpan
  , recursiveStepContract :: [ProductElementType]
  , recursiveStepSuccessorNames :: [Name]
  , recursiveStepBefore :: Core.ResourceContext
  , recursiveStepAfter :: Core.ResourceContext
  , recursiveStepSurface :: ProductEliminationRun
  }
  deriving (Eq, Show)

data RecursiveProductTrace = RecursiveProductTrace
  { recursiveProductDeclarationKey :: DeclarationKey
  , recursiveProductOriginalOwner :: GrammarV1ResolvedBinder
  , recursiveProductOriginalLeaves :: [GrammarV1ResolvedBinder]
  , recursiveProductReturnedOwner :: GrammarV1ResolvedBinder
  , recursiveProductDeclaredReturn :: CheckedTypeMode
  , recursiveProductInternalOwners :: [Name]
  , recursiveProductSteps :: [RecursiveProductStep]
  , recursiveProductFinalContext :: Core.ResourceContext
  , recursiveProductAccepted :: SurfaceCheckResult
  }
  deriving (Eq, Show)

-- | These trees contain source-rooted leaf names and synthesized *internal*
-- product nodes only. The nodes are constructed from exact source pattern
-- structure and separately checked source types/modes, not supplied by callers.
data ProductTree
  = ProductLeaf Name Mode Ty
  | ProductFork Name SourceSpan [ProductElementType] ProductTree ProductTree
  deriving (Eq, Show)

treeName :: ProductTree -> Name
treeName tree = case tree of
  ProductLeaf name _ _ -> name
  ProductFork name _ _ _ _ -> name

treeLeaves :: ProductTree -> [(Name, Mode, Ty)]
treeLeaves tree = case tree of
  ProductLeaf name mode ty -> [(name,mode,ty)]
  ProductFork _ _ _ a b -> treeLeaves a ++ treeLeaves b

treeInternalOwners :: ProductTree -> [Name]
treeInternalOwners tree = case tree of
  ProductLeaf _ _ _ -> []
  ProductFork name _ _ a b -> name : treeInternalOwners a ++ treeInternalOwners b

data PlannedStep = PlannedStep
  { plannedOwner :: Name
  , plannedSpan :: SourceSpan
  , plannedContract :: [ProductElementType]
  , plannedSuccessors :: [Name]
  }

-- | Deterministic preorder: root first, left subtree, right subtree.
-- This is structural recursion, not a depth- or orientation-specific list.
planSteps :: ProductTree -> [PlannedStep]
planSteps tree = case tree of
  ProductLeaf _ _ _ -> []
  ProductFork owner span' members left right ->
    PlannedStep owner span' members [treeName left,treeName right]
      : planSteps left ++ planSteps right

generatedOwner :: Name -> [Int] -> Name
generatedOwner (Name root) path =
  Name ("$phil.data05e.internal:" <> root <> ":" <>
        Text.intercalate "." (map (Text.pack . show) path))

-- | Leaf authority is inherited from the existing production checker.
-- No nominal proof, alias, refinement or recursively named type enters this
-- adapter through a "trusted mode" supplied by a caller.
checkedTreeType
  :: StaticContext
  -> Located GrammarV1Type
  -> Maybe (Either FocusingError CheckedTypeMode)
checkedTreeType static (Located _ sourceTy) = case sourceTy of
  GrammarV1TupleType [a,b] -> do
    left <- checkedTreeType static a
    right <- checkedTreeType static b
    pure $ do
      l <- left
      r <- right
      let members =
            [ ProductElementType (checkedBindingMode l) (checkedBindingType l)
            , ProductElementType (checkedBindingMode r) (checkedBindingType r)
            ]
      pure (CheckedTypeMode
        (TyProduct members) (ProductMode.productMode members))
  GrammarV1TupleType _ -> Nothing
  GrammarV1UnitType -> primitive
  GrammarV1BoolType -> primitive
  GrammarV1UnsignedType _ -> primitive
  GrammarV1BytesType _ -> primitive
  _ -> Nothing
  where
    primitive = do
      checked <- grammarV1CheckedTypeMode static emptySurfaceState sourceTy
      pure (fst <$> checked)

binaryPattern :: Located GrammarV1Pattern -> Bool
binaryPattern (Located _ patternValue) = case patternValue of
  GrammarV1IdentifierPattern _ -> True
  GrammarV1TuplePattern [a,b] -> binaryPattern a && binaryPattern b
  _ -> False

sourceMismatch :: Text -> Either RecursiveProductError a
sourceMismatch = Left . RecursiveSourceMismatch

-- | Zip actual source lexical binder preorder with the checked product type
-- tree. A source leaf never becomes a fabricated semantic owner. The pattern
-- and TyProduct structure must agree at *each* recursive fork.
buildTree
  :: Name -> [Int] -> Located GrammarV1Pattern -> CheckedTypeMode
  -> [GrammarV1ResolvedBinder]
  -> Either RecursiveProductError (ProductTree,[GrammarV1ResolvedBinder])
buildTree root path pattern' checked binders =
  case (locatedValue pattern',checkedBindingType checked) of
    (GrammarV1TuplePattern [a,b],TyProduct [left,right]) -> do
      (leftTree,afterLeft) <- buildTree root (path ++ [0]) a
        (CheckedTypeMode
          (productElementType left) (productElementMode left)) binders
      (rightTree,afterRight) <- buildTree root (path ++ [1]) b
        (CheckedTypeMode
          (productElementType right) (productElementMode right)) afterLeft
      let name = if null path then root else generatedOwner root path
      Right (ProductFork name (locatedSpan pattern') [left,right]
        leftTree rightTree,afterRight)
    (GrammarV1IdentifierPattern sourceName,ty)
      | not (isProduct ty) ->
          case binders of
            binder : rest
              | grammarV1ResolvedBinderDisplayName binder ==
                  locatedValue sourceName ->
                  Right (ProductLeaf
                    (grammarV1ResolvedBinderCoreName binder)
                    (checkedBindingMode checked) ty,rest)
            _ -> sourceMismatch
              "source tuple leaf does not match checked lexical identity"
    _ -> sourceMismatch
      "source tuple pattern and checked type tree disagree in shape or arity"
  where
    isProduct (TyProduct _) = True
    isProduct _ = False

flatLet :: SourceSpan -> Name -> [Name] -> Located Statement
flatLet span' owner successors =
  Located span' (LetStatement
    (Located span' (TuplePattern
      [ Located span' (BindPattern (unName name))
      | name <- successors ]))
    (Located span' (VariableExpression (unName owner))))

unitReturn :: SourceSpan -> Located Statement
unitReturn span' =
  Located span' (ReturnStatement (Located span' UnitExpression))

ownerReturn :: SourceSpan -> Name -> Located Statement
ownerReturn span' owner =
  Located span' (ReturnStatement
    (Located span' (VariableExpression (unName owner))))

component
  :: Text -> SourceSpan -> [Located Statement] -> Located Component
component name span' statements =
  Located span' (Component
    { componentName = name
    , componentParameters = []
    , componentProvides = Nothing
    , componentBody = Located span' (Block statements)
    })

-- | Preserve all four native resource zones. The finite source fragment has
-- no externally justified Affine/loan authority; those zones must remain
-- empty. Unrestricted product copies *may remain*: only restricted owners
-- have one-shot consumption obligations.
environmentFor
  :: StaticContext -> [(Text,[ProductElementType])]
  -> Core.ResourceContext -> SurfaceEnvironment
environmentFor static contracts ctx =
  (emptySurfaceEnvironment static)
    { surfaceInitialBindings = Map.fromList
        ( bindingList Unrestricted (Core.unrestrictedBindings ctx)
       ++ bindingList Affine (Core.affineBindings ctx)
       ++ bindingList Linear (Core.linearBindings ctx) )
    , surfaceExpectedProductEliminations = Map.fromList contracts
    }
  where
    bindingList mode bindings =
      [ (unName name, InitialBinding mode ty (shapeForType ty))
      | (name,ty) <- Map.toAscList bindings ]

-- | Exactly one step, using *both* independent native Core execution and
-- the unchanged production Surface trace/ordinary checker. A diagnostic
-- partial return of Unit must fail while one linear Bytes owner is live.
executeStep
  :: StaticContext -> Text -> SourceSpan
  -> [(Text,[ProductElementType])]
  -> (Core.ResourceContext,[RecursiveProductStep])
  -> PlannedStep
  -> Either RecursiveProductError (Core.ResourceContext,[RecursiveProductStep])
executeStep static sourceName returnSpan contracts (before,reversed) step = do
  let env = environmentFor static contracts before
      projected = flatLet (plannedSpan step)
        (plannedOwner step) (plannedSuccessors step)
      fragment = component sourceName (plannedSpan step)
        [projected,unitReturn returnSpan]
      native = ProductMode.eliminateProductBinding
        (plannedOwner step) (plannedSuccessors step) before
      observed = traceSurfaceProductEliminationComponent env fragment
  after <- case native of
    Left err -> Left (RecursiveNativeError err)
    Right result -> Right result
  trace <- case observed of
    Nothing -> Left (RecursiveTransitionMismatch
      "production Surface could not trace the checked product elimination")
    Just result -> Right result
  if productEliminationBefore trace /= Just before ||
     productEliminationAfter trace /= Just after
    then Left (RecursiveTransitionMismatch
      "actual Surface Map/Set predecessor/successor differs from native Core")
    else Right ()
  case productEliminationOutcome trace of
    Left err | surfaceErrorClass err == LinearCompletion -> Right ()
    Left err -> Left (RecursiveSurfaceError err)
    Right _ -> Left (RecursiveTransitionMismatch
      "partial Unit return silently escaped outstanding Linear Bytes owner")
  let recorded = RecursiveProductStep
        { recursiveStepSourceOwner = plannedOwner step
        , recursiveStepSourceSpan = plannedSpan step
        , recursiveStepContract = plannedContract step
        , recursiveStepSuccessorNames = plannedSuccessors step
        , recursiveStepBefore = before
        , recursiveStepAfter = after
        , recursiveStepSurface = trace
        }
  Right (after,recorded:reversed)

-- | One checked original function/tuple-let/return, with a structurally
-- recursive, *unbounded finite* binary product-tree elaboration schedule.
-- All general source and proof authority remains outside this adapter.
grammarV1CheckedRecursiveProductElimination
  :: StaticContext -> DeclarationKey -> GrammarV1FunctionDecl
  -> Maybe (Either RecursiveProductError RecursiveProductTrace)
grammarV1CheckedRecursiveProductElimination static declarationKey source
  | grammarV1FunctionRecursive source = Nothing
  | not (null (grammarV1FunctionGenericParams source)) = Nothing
  | not (null (grammarV1FunctionRequirements source)) = Nothing
  | otherwise = do
      [Located _ parameter] <- pure (grammarV1FunctionTermParams source)
      resultTypeSource <- grammarV1FunctionResultType source
      [Located letSpan (GrammarV1LetStatement pattern' _),
       Located returnSpan (GrammarV1ReturnStatement _)] <-
        pure (grammarV1BlockStatements
          (locatedValue (grammarV1FunctionBody source)))
      -- This is a binary product adapter, not a general pattern elaborator.
      case locatedValue pattern' of
        GrammarV1TuplePattern [_,_] | binaryPattern pattern' -> Just ()
        _ -> Nothing
      -- A local value might resolve to a static/global reference. Preserve
      -- source noncompetence in that case, not a false invalidity verdict.
      case grammarV1FunctionParameterScope declarationKey source of
        Right (_,scope) ->
          case grammarV1CheckedLetPatternBlockInScope scope
              (grammarV1FunctionBody source) of
            Nothing -> Nothing
            _ -> Just ()
        Left _ -> Just ()
      inputChecked <- checkedTreeType static (grammarV1TermParamType parameter)
      returnChecked <- checkedTreeType static resultTypeSource
      case (inputChecked,returnChecked) of
        (Left err,_) -> Just (Left (RecursiveLeafTypeError err))
        (_,Left err) -> Just (Left (RecursiveLeafTypeError err))
        (Right inputType,Right resultType) ->
          Just $ do
            (packet,leafBinders,returnedBinder) <-
              case grammarV1FunctionParameterScope declarationKey source of
                Left err -> Left (RecursiveParameterError err)
                Right ([owner],scope) ->
                  case grammarV1CheckedLetPatternBlockInScope scope
                      (grammarV1FunctionBody source) of
                    Nothing -> sourceMismatch "source lexical let is outside the adapter"
                    Just (Left err) -> Left (RecursiveLetError err)
                    Just (Right
                      ([GrammarV1CheckedLetBindingStep _ input binders,
                        GrammarV1CheckedLetOccurrenceStep _ returned],_))
                      | grammarV1ResolvedBinderKey
                          (grammarV1CheckedLocalValueBinder input)
                          == grammarV1ResolvedBinderKey owner ->
                          Right (owner,binders,
                            grammarV1CheckedLocalValueBinder returned)
                      | otherwise -> sourceMismatch
                          "product initializer is not the checked source parameter"
                    Just (Right _) -> sourceMismatch
                      "source statement sequence is not an admitted tuple-let/return"
                Right _ -> sourceMismatch
                  "exactly one source parameter is required"
            let sourceOwner = grammarV1ResolvedBinderCoreName packet
            (tree,rest) <- buildTree sourceOwner [] pattern' inputType leafBinders
            if not (null rest)
              then sourceMismatch "source product leaf binder count differs"
              else Right ()
            let leaves = treeLeaves tree
                linearLeaves = [(name,ty) | (name,mode,ty) <- leaves,
                                mode == Linear]
            (returnedOwner,returnedType) <- case linearLeaves of
              [(name,ty@(TyBytes _))] -> Right (name,ty)
              _ -> sourceMismatch
                "adapter requires exactly one checked Linear Bytes[N] leaf"
            if grammarV1ResolvedBinderCoreName returnedBinder /= returnedOwner
              then sourceMismatch
                "source return is not the unique checked Linear Bytes leaf"
              else Right ()
            if resultType /= CheckedTypeMode returnedType Linear
              then sourceMismatch
                "source return type/mode differs from the Linear Bytes leaf"
              else Right ()
            let internal = filter (/= sourceOwner) (treeInternalOwners tree)
                allNames = sourceOwner : map (\(name,_,_) -> name) leaves ++ internal
                steps = planSteps tree
                contracts =
                  [ (unName (plannedOwner step),plannedContract step)
                  | step <- steps ]
            if null steps || Set.size (Set.fromList allNames) /= length allNames
              then sourceMismatch
                "generated product owners are not globally fresh"
              else Right ()
            initial <- case Core.insertBinding Linear sourceOwner
                (checkedBindingType inputType) Core.emptyContext of
              Left err -> Left (RecursiveTransitionMismatch
                ("initial checked product owner rejected: " <>
                  Text.pack (show err)))
              Right ctx -> Right ctx
            (lastContext,reversed) <- foldM
              (executeStep static
                (locatedValue (grammarV1FunctionName source))
                returnSpan contracts)
              (initial,[]) steps
            let reached = reverse reversed
            (returned,terminal) <- case Core.consumeLinear returnedOwner lastContext of
              Left err -> Left (RecursiveTransitionMismatch
                ("one-shot source return failed: " <> Text.pack (show err)))
              Right ok -> Right ok
            if returned /= returnedType || Core.ensureComplete terminal /= Right ()
              then Left (RecursiveTransitionMismatch
                "source return left unpaid Linear resources")
              else Right ()
            let env = environmentFor static contracts initial
                full = component
                  (locatedValue (grammarV1FunctionName source)) letSpan
                  ( [ flatLet (plannedSpan step)
                        (plannedOwner step) (plannedSuccessors step)
                    | step <- steps ] ++
                    [ownerReturn returnSpan returnedOwner] )
                expected = SurfaceCheckResult
                  (locatedValue (grammarV1FunctionName source))
                  [Return returnedType]
            accepted <- case checkSurfaceComponent env full of
              Left err -> Left (RecursiveSurfaceError err)
              Right actual | actual == expected -> Right actual
              Right _ -> Left (RecursiveTransitionMismatch
                "full production Surface outcome differs from checked source return")
            Right RecursiveProductTrace
              { recursiveProductDeclarationKey = declarationKey
              , recursiveProductOriginalOwner = packet
              , recursiveProductOriginalLeaves = leafBinders
              , recursiveProductReturnedOwner = returnedBinder
              , recursiveProductDeclaredReturn = resultType
              , recursiveProductInternalOwners = internal
              , recursiveProductSteps = reached
              , recursiveProductFinalContext = lastContext
              , recursiveProductAccepted = accepted
              }
