{-# LANGUAGE OverloadedStrings #-}

-- | FSEM-01: bounded source-declared affine nominal + intrinsic linear
-- product return, through the actual production Surface checker.
--
-- The source nominal declaration still requires a separately admitted
-- external lifecycle justification; this route cannot prove it from text.
-- Both parameter identities share one real parsed function's binder scope.
-- This is deliberately not a general source-to-Core elaborator.
module Phil.Surface.GrammarV1.SourceAffineProduct
  ( GrammarV1AffineProductError (..)
  , GrammarV1AffineProductTrace (..)
  , grammarV1CheckedAffineProductFunctionTrace
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..), GenericStaticKind (..) )
import Phil.Core.NominalDataMode (NominalRestrictionJustification)
import Phil.Core.Static (DeclarationKey, InterfaceRevision, StaticContext)
import Phil.Core.Syntax
  ( Mode (..), Name (..), Ty (..) )
import Phil.Surface.Check.Engine
  ( BorrowTraceCheckpoint, BorrowTraceRun (..)
  , checkSurfaceComponent, traceSurfaceBorrowComponent )
import Phil.Surface.Check.Support (emptySurfaceState, shapeForType)
import Phil.Surface.Check.Types
  ( InitialBinding (..), SurfaceCheckError, SurfaceCheckResult
  , SurfaceEnvironment (..), emptySurfaceEnvironment )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError, GrammarV1LexicalScope
  , GrammarV1ResolvedBinder (..)
  , grammarV1FunctionParameterScope )
import Phil.Surface.GrammarV1.BorrowViewScope
  ( GrammarV1BorrowViewScopeError, GrammarV1CheckedBorrowView (..)
  , grammarV1CheckedBorrowViewInScope )
import Phil.Surface.GrammarV1.CheckedType
  ( GrammarV1CheckedResolvedFlatProduct (..)
  , GrammarV1CheckedResolvedTypeMode (..)
  , GrammarV1CheckedTypeModeOrigin (..)
  , GrammarV1CheckedTypeModeResolutionError
  , GrammarV1ResolvedNamedTypeMode (..)
  , grammarV1CheckedFlatProductWithNamedResolutions
  , grammarV1CheckedTypeModeWithNamedResolutions )
import Phil.Surface.GrammarV1.DataVariants
  ( GrammarV1CheckedDataMode (..), GrammarV1CheckedDataModeError
  , grammarV1CheckedClosedDataMode )
import Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep (..) )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , grammarV1CheckedLocalValueOccurrenceInScope )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..), GrammarV1DataDecl (..)
  , GrammarV1Expression (..), GrammarV1FunctionDecl (..)
  , GrammarV1Statement (..), GrammarV1TermParam (..) )
import Phil.Surface.Syntax
  ( Block (..), Component (..), Located (..)
  , Statement (..), SurfaceExpression (..) )

data GrammarV1AffineProductError
  = AffineProductNominalError GrammarV1CheckedDataModeError
  | AffineProductTypeError GrammarV1CheckedTypeModeResolutionError
  | AffineProductBinderError GrammarV1BinderScopeError
  | AffineProductBorrowError GrammarV1BorrowViewScopeError
  deriving (Eq, Show)

-- | Source-declared exact ordered product and per-element provenance, plus
-- production resource checkpoints and exact result or rejection class.
data GrammarV1AffineProductTrace = GrammarV1AffineProductTrace
  { affineProductDeclarationKey :: DeclarationKey
  , affineProductInterfaceRevision :: InterfaceRevision
  , affineProductPermitBinder :: GrammarV1ResolvedBinder
  , affineProductPayloadBinder :: GrammarV1ResolvedBinder
  , affineProductViewBinder :: GrammarV1ResolvedBinder
  , affineProductPermitMode :: CheckedTypeMode
  , affineProductPayloadMode :: CheckedTypeMode
  , affineProductPermitOrigin :: GrammarV1CheckedTypeModeOrigin
  , affineProductCheckedReturn :: CheckedTypeMode
  , affineProductReturnElements :: [GrammarV1CheckedResolvedTypeMode]
  , affineProductCheckpoints :: [BorrowTraceCheckpoint]
  , affineProductOutcome :: Either SurfaceCheckError SurfaceCheckResult
  } deriving (Eq, Show)

-- | Admit a two-parameter function only after independently checking its
-- nominal affine and intrinsic linear declarations. Resolve the flat result
-- product element-by-element with exact nominal declaration provenance, then
-- install its ordered contract in the real production Surface environment.
--
-- Return expressions contain two source-resolved local owners. The projection
-- does not pre-validate their *order* or possible duplication: these cases
-- must be rejected by the production checker, not by a test-only validator.
-- Wrong source shapes and nested products remain outside competence (Nothing).
grammarV1CheckedAffineProductFunctionTrace
  :: StaticContext
  -> DeclarationKey
  -> InterfaceRevision
  -> Maybe NominalRestrictionJustification
  -> GrammarV1DataDecl
  -> DeclarationKey
  -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1AffineProductError GrammarV1AffineProductTrace)
grammarV1CheckedAffineProductFunctionTrace
    staticContext dataKey revision lifecycle dataDecl functionKey functionDecl
  | grammarV1FunctionRecursive functionDecl = Nothing
  | not (null (grammarV1FunctionGenericParams functionDecl)) = Nothing
  | not (null (grammarV1FunctionRequirements functionDecl)) = Nothing
  | otherwise = do
      [Located _ permitParam, Located _ payloadParam] <-
        pure (grammarV1FunctionTermParams functionDecl)
      returnSource <- grammarV1FunctionResultType functionDecl
      nominalResult <- grammarV1CheckedClosedDataMode
        staticContext lifecycle dataDecl
      case nominalResult of
        Left err -> Just (Left (AffineProductNominalError err))
        Right admitted
          | checkedDataStructuralMode admitted /= Affine -> Nothing
          | otherwise -> do
              let dataName = locatedValue (grammarV1DataName dataDecl)
                  namedTy = TyOpaque dataName
                  reference = ReferencedGenericStaticActual dataName
                  resolution = GrammarV1ResolvedNamedTypeMode
                    { resolvedNamedTypeReference = reference
                    , resolvedNamedTypeKind = GenericTypeKind
                    , resolvedNamedTypeDeclarationKey = dataKey
                    , resolvedNamedTypeInterfaceRevision = revision
                    , resolvedNamedTypeCheckedMode = CheckedTypeMode
                        namedTy (checkedDataStructuralMode admitted)
                    }
                  checkType = grammarV1CheckedTypeModeWithNamedResolutions
                    staticContext emptySurfaceState [resolution]
              permitChecked <- checkType
                (locatedValue (grammarV1TermParamType permitParam))
              payloadChecked <- checkType
                (locatedValue (grammarV1TermParamType payloadParam))
              returnChecked <- grammarV1CheckedFlatProductWithNamedResolutions
                staticContext emptySurfaceState [resolution]
                (locatedValue returnSource)
              case (permitChecked, payloadChecked, returnChecked) of
                (Left err, _, _) -> Just (Left (AffineProductTypeError err))
                (_, Left err, _) -> Just (Left (AffineProductTypeError err))
                (_, _, Left err) -> Just (Left (AffineProductTypeError err))
                (Right (permit, _), Right (payload, _), Right checkedProduct) ->
                  let permitMode = checkedResolvedTypeMode permit
                      payloadMode = checkedResolvedTypeMode payload
                  in if permitMode == CheckedTypeMode namedTy Affine
                       && checkedResolvedTypeModeOrigin permit ==
                            GrammarV1NamedTypeModeOrigin
                              reference dataKey revision
                       && isLinearBytes payloadMode
                    then sourceBody permit payload checkedProduct
                    else Nothing
  where
    isLinearBytes mode = case checkedBindingType mode of
      TyBytes _ -> checkedBindingMode mode == Linear
      _ -> False

    sourceBody permit payload checkedProduct = do
      [Located borrowSpan (GrammarV1ExpressionStatement borrowed),
       Located returnSpan (GrammarV1ReturnStatement returned)] <-
        pure (grammarV1BlockStatements
          (locatedValue (grammarV1FunctionBody functionDecl)))
      GrammarV1TupleExpression returnedMembers <- pure (locatedValue returned)
      [firstReturn, secondReturn] <- pure returnedMembers
      case grammarV1FunctionParameterScope functionKey functionDecl of
        Left err -> Just (Left (AffineProductBinderError err))
        Right ([permitBinder, payloadBinder], initialScope) -> do
          checkedBorrow <- grammarV1CheckedBorrowViewInScope
            initialScope borrowed
          case checkedBorrow of
            Left err -> Just (Left (AffineProductBorrowError err))
            Right (borrowScope, afterScope) -> do
              let owner = grammarV1CheckedBorrowOwner borrowScope
                  view = grammarV1CheckedBorrowViewBinder borrowScope
                  same a b = grammarV1ResolvedBinderKey a ==
                    grammarV1ResolvedBinderKey b
              if not (same
                  (grammarV1CheckedLocalValueBinder owner) permitBinder)
                then Nothing
                else do
                  first <- projectReturned afterScope permitBinder payloadBinder
                    firstReturn
                  second <- projectReturned afterScope permitBinder payloadBinder
                    secondReturn
                  projectedSteps <- mapM (projectBorrowStep view)
                    (grammarV1CheckedBorrowBodySteps borrowScope)
                  Located _ (GrammarV1BorrowExpression sourceOwner _ sourceBlock)
                    <- pure (grammarV1CheckedBorrowViewSource borrowScope)
                  TyProduct expected <- pure
                    (checkedBindingType (checkedResolvedFlatProductMode checkedProduct))
                  let permitName = semanticName permitBinder
                      payloadName = semanticName payloadBinder
                      viewName = semanticName view
                      permitMode = checkedResolvedTypeMode permit
                      payloadMode = checkedResolvedTypeMode payload
                      borrowExpression = Located (locatedSpan borrowed)
                        (BorrowExpression
                          (Located (locatedSpan sourceOwner)
                            (VariableExpression permitName))
                          viewName
                          (Located (locatedSpan sourceBlock)
                            (Block projectedSteps)))
                      returnExpression = Located (locatedSpan returned)
                        (TupleExpression [first, second])
                      block = Located
                        (locatedSpan (grammarV1FunctionBody functionDecl))
                        (Block
                          [ Located borrowSpan
                              (ExpressionStatement borrowExpression)
                          , Located returnSpan
                              (ReturnStatement returnExpression) ])
                      component = Located
                        (locatedSpan (grammarV1FunctionBody functionDecl))
                        (Component
                          { componentName =
                              locatedValue (grammarV1FunctionName functionDecl)
                          , componentParameters = []
                          , componentProvides = Nothing
                          , componentBody = block
                          })
                      environment = (emptySurfaceEnvironment staticContext)
                        { surfaceInitialBindings = Map.fromList
                            [ (permitName, InitialBinding
                                (checkedBindingMode permitMode)
                                (checkedBindingType permitMode)
                                (shapeForType (checkedBindingType permitMode)))
                            , (payloadName, InitialBinding
                                (checkedBindingMode payloadMode)
                                (checkedBindingType payloadMode)
                                (shapeForType (checkedBindingType payloadMode)))
                            ]
                        , surfaceExpectedProductReturn = Just expected
                        }
                  run <- traceSurfaceBorrowComponent environment component
                  if checkSurfaceComponent environment component /= traceOutcome run
                    then Nothing
                    else Just (Right GrammarV1AffineProductTrace
                      { affineProductDeclarationKey = dataKey
                      , affineProductInterfaceRevision = revision
                      , affineProductPermitBinder = permitBinder
                      , affineProductPayloadBinder = payloadBinder
                      , affineProductViewBinder = view
                      , affineProductPermitMode = permitMode
                      , affineProductPayloadMode = payloadMode
                      , affineProductPermitOrigin =
                          checkedResolvedTypeModeOrigin permit
                      , affineProductCheckedReturn =
                          checkedResolvedFlatProductMode product
                      , affineProductReturnElements =
                          checkedResolvedFlatProductElements checkedProduct
                      , affineProductCheckpoints = traceCheckpoints run
                      , affineProductOutcome = traceOutcome run
                      })
        Right _ -> Nothing

semanticName :: GrammarV1ResolvedBinder -> Text
semanticName = unName . grammarV1ResolvedBinderCoreName

projectReturned
  :: GrammarV1LexicalScope
  -> GrammarV1ResolvedBinder
  -> GrammarV1ResolvedBinder
  -> Located GrammarV1Expression
  -> Maybe (Located SurfaceExpression)
projectReturned scope permit payload source = do
  occurrence <- grammarV1CheckedLocalValueOccurrenceInScope scope source
  let actual = grammarV1CheckedLocalValueBinder occurrence
      same a b = grammarV1ResolvedBinderKey a == grammarV1ResolvedBinderKey b
  if same actual permit || same actual payload
    then Just (Located (locatedSpan source)
      (VariableExpression (semanticName actual)))
    else Nothing

projectBorrowStep
  :: GrammarV1ResolvedBinder
  -> GrammarV1CheckedLetScopeStep
  -> Maybe (Located Statement)
projectBorrowStep view (GrammarV1CheckedLetOccurrenceStep
  (Located span' (GrammarV1ExpressionStatement _)) occurrence)
    | grammarV1ResolvedBinderKey
        (grammarV1CheckedLocalValueBinder occurrence) ==
          grammarV1ResolvedBinderKey view =
      Just (Located span' (ExpressionStatement
        (Located (locatedSpan (grammarV1CheckedLocalValueSource occurrence))
          (VariableExpression (semanticName view)))))
projectBorrowStep _ (GrammarV1CheckedLetUnitStep
  (Located span' (GrammarV1ExpressionStatement source)))
    | GrammarV1UnitExpression <- locatedValue source =
        Just (Located span' (ExpressionStatement
          (Located (locatedSpan source) UnitExpression)))
projectBorrowStep _ _ = Nothing
