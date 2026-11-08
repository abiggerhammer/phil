{-# LANGUAGE OverloadedStrings #-}

-- | A bounded source-derived affine resource route. This does not promote the
-- source's "mode affine" spelling into semantic authority: the existing
-- nominal checker must also admit the supplied external lifecycle evidence.
-- Named parameters retain exact declaration and interface provenance.
module Phil.Surface.GrammarV1.SourceAffineResource
  ( GrammarV1AffineSourceError (..)
  , GrammarV1AffineSourceTrace (..)
  , grammarV1CheckedAffineFunctionTrace
  , GrammarV1MixedAffineLinearTrace (..)
  , grammarV1CheckedMixedAffineLinearFunctionTrace
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Focusing (FocusStep)
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..), GenericStaticKind (..) )
import Phil.Core.NominalDataMode (NominalRestrictionJustification)
import Phil.Core.Static
  ( DeclarationKey, InterfaceRevision, StaticContext )
import Phil.Core.Syntax (Mode (..), Name (..), Ty (..))
import Phil.Surface.Check.Engine
  ( BorrowTraceCheckpoint
  , BorrowTraceRun (..)
  , checkSurfaceComponent
  , traceSurfaceBorrowComponent
  )
import Phil.Surface.Check.Support (emptySurfaceState, shapeForType)
import Phil.Surface.Check.Types
  ( InitialBinding (..), SurfaceCheckError, SurfaceCheckResult (..)
  , SurfaceEnvironment (..), emptySurfaceEnvironment )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError
  , GrammarV1ResolvedBinder (..)
  , grammarV1FunctionParameterScope )
import Phil.Surface.GrammarV1.BorrowViewScope
  ( GrammarV1BorrowViewScopeError
  , GrammarV1CheckedBorrowView (..)
  , grammarV1CheckedBorrowViewInScope )
import Phil.Surface.GrammarV1.CheckedType
  ( GrammarV1CheckedResolvedTypeMode (..)
  , GrammarV1CheckedTypeModeOrigin (..)
  , GrammarV1CheckedTypeModeResolutionError
  , GrammarV1ResolvedNamedTypeMode (..)
  , grammarV1CheckedTypeModeWithNamedResolutions )
import Phil.Surface.GrammarV1.DataVariants
  ( GrammarV1CheckedDataMode (..)
  , GrammarV1CheckedDataModeError
  , grammarV1CheckedClosedDataMode )
import Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep (..) )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , grammarV1CheckedLocalValueOccurrenceInScope )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..)
  , GrammarV1DataDecl (..)
  , GrammarV1Expression (..)
  , GrammarV1FunctionDecl (..)
  , GrammarV1Statement (..)
  , GrammarV1TermParam (..)
  )
import Phil.Surface.Syntax
  ( Block (..), Component (..), Located (..)
  , Statement (..), SurfaceExpression (..) )

data GrammarV1AffineSourceError
  = AffineSourceNominalError GrammarV1CheckedDataModeError
  | AffineSourceTypeError GrammarV1CheckedTypeModeResolutionError
  | AffineSourceBinderError GrammarV1BinderScopeError
  | AffineSourceBorrowError GrammarV1BorrowViewScopeError
  deriving (Eq, Show)

-- | Observation of the actual production Surface checker. Core snapshots and
-- the outcome are retained even for a source witness with BorrowEscape.
data GrammarV1AffineSourceTrace = GrammarV1AffineSourceTrace
  { affineSourceDeclarationKey :: DeclarationKey
  , affineSourceInterfaceRevision :: InterfaceRevision
  , affineSourceBinder :: GrammarV1ResolvedBinder
  , affineSourceViewBinder :: GrammarV1ResolvedBinder
  , affineSourceCheckedMode :: CheckedTypeMode
  , affineSourceTypeOrigin :: GrammarV1CheckedTypeModeOrigin
  , affineSourceFocusingSteps :: [FocusStep]
  , affineSourceCheckpoints :: [BorrowTraceCheckpoint]
  , affineSourceOutcome :: Either SurfaceCheckError SurfaceCheckResult
  } deriving (Eq, Show)

-- | Interpret a deliberately small, nonrecursive Grammar-v1 function with one
-- named affine parameter, one lexical borrow, and a return of either Unit
-- (discardable affine owner) or the exact source parameter (consumed once).
--
-- The admitted data declaration MUST pass checked nominal-mode authority with
-- an independently supplied admitted lifecycle/resource justification. The
-- justifying text is an existing external attestation seam, not proof from the
-- source declaration itself. Absence/unadmitted evidence remains a nominal
-- rejection. Other source shapes return Nothing (non-competence).
--
-- The production resource checker is executed, not modeled here. The route
-- does not prove the external nominal attestation, general source elaboration,
-- full 'satisfies C', or implementation-to-Rocq simulation.
grammarV1CheckedAffineFunctionTrace
  :: StaticContext
  -> DeclarationKey
  -> InterfaceRevision
  -> Maybe NominalRestrictionJustification
  -> GrammarV1DataDecl
  -> DeclarationKey
  -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1AffineSourceError GrammarV1AffineSourceTrace)
grammarV1CheckedAffineFunctionTrace
    staticContext dataKey revision lifecycle dataDecl functionKey functionDecl
  | grammarV1FunctionRecursive functionDecl = Nothing
  | not (null (grammarV1FunctionGenericParams functionDecl)) = Nothing
  | not (null (grammarV1FunctionRequirements functionDecl)) = Nothing
  | otherwise = do
      [Located _ param] <- pure (grammarV1FunctionTermParams functionDecl)
      sourceResult <- grammarV1FunctionResultType functionDecl
      checkedData <- grammarV1CheckedClosedDataMode
        staticContext lifecycle dataDecl
      case checkedData of
        Left err -> Just (Left (AffineSourceNominalError err))
        Right admitted
          | checkedDataStructuralMode admitted /= Affine -> Nothing
          | otherwise -> do
              let dataName = locatedValue (grammarV1DataName dataDecl)
                  namedTy = TyOpaque dataName
                  reference = ReferencedGenericStaticActual dataName
                  resolved = GrammarV1ResolvedNamedTypeMode
                    { resolvedNamedTypeReference = reference
                    , resolvedNamedTypeKind = GenericTypeKind
                    , resolvedNamedTypeDeclarationKey = dataKey
                    , resolvedNamedTypeInterfaceRevision = revision
                    , resolvedNamedTypeCheckedMode =
                        CheckedTypeMode namedTy
                          (checkedDataStructuralMode admitted)
                    }
                  checkType sourceTy =
                    grammarV1CheckedTypeModeWithNamedResolutions
                      staticContext emptySurfaceState [resolved] sourceTy
              paramChecked <- checkType
                (locatedValue (grammarV1TermParamType param))
              resultChecked <- checkType (locatedValue sourceResult)
              case (paramChecked, resultChecked) of
                (Left err, _) -> Just (Left (AffineSourceTypeError err))
                (_, Left err) -> Just (Left (AffineSourceTypeError err))
                (Right (paramMode, steps), Right (resultMode, _))
                  | checkedResolvedTypeMode paramMode /=
                      CheckedTypeMode namedTy Affine -> Nothing
                  | checkedResolvedTypeModeOrigin paramMode /=
                      GrammarV1NamedTypeModeOrigin reference dataKey revision ->
                      Nothing
                  | checkedBindingType
                      (checkedResolvedTypeMode resultMode) /=
                        TyUnit
                    && checkedBindingType
                      (checkedResolvedTypeMode resultMode) /= namedTy ->
                      Nothing
                  | otherwise ->
                      sourceBody paramMode steps
                        (checkedBindingType
                          (checkedResolvedTypeMode resultMode))
  where
    sourceBody paramMode steps returnTy = do
      [Located borrowSpan (GrammarV1ExpressionStatement borrow),
       Located returnSpan (GrammarV1ReturnStatement returned)] <-
        pure (grammarV1BlockStatements
          (locatedValue (grammarV1FunctionBody functionDecl)))
      case grammarV1FunctionParameterScope functionKey functionDecl of
        Left err -> Just (Left (AffineSourceBinderError err))
        Right ([paramBinder], scope) -> do
          borrowed <- grammarV1CheckedBorrowViewInScope scope borrow
          case borrowed of
            Left err -> Just (Left (AffineSourceBorrowError err))
            Right (borrowTrace, afterScope) -> do
              let owner = grammarV1CheckedBorrowOwner borrowTrace
                  viewBinder = grammarV1CheckedBorrowViewBinder borrowTrace
                  same a b = grammarV1ResolvedBinderKey a ==
                    grammarV1ResolvedBinderKey b
              if not (same
                  (grammarV1CheckedLocalValueBinder owner) paramBinder)
                then Nothing
                else do
                  returnedExpression <- case (returnTy, locatedValue returned) of
                    (TyUnit, GrammarV1UnitExpression) ->
                      Just (UnitExpression)
                    (TyOpaque _, _) -> do
                      resultOccurrence <-
                        grammarV1CheckedLocalValueOccurrenceInScope
                          afterScope returned
                      if same
                        (grammarV1CheckedLocalValueBinder resultOccurrence)
                        paramBinder
                        then Just (VariableExpression (semanticName paramBinder))
                        else Nothing
                    _ -> Nothing
                  stepsInBorrow <- mapM (bridgeStep viewBinder)
                    (grammarV1CheckedBorrowBodySteps borrowTrace)
                  Located _ (GrammarV1BorrowExpression sourceOwner _ sourceBlock)
                    <- pure (grammarV1CheckedBorrowViewSource borrowTrace)
                  let ownerText = semanticName paramBinder
                      viewText = semanticName viewBinder
                      ownerExpression = Located (locatedSpan sourceOwner)
                        (VariableExpression ownerText)
                      borrowExpression = Located (locatedSpan borrow)
                        (BorrowExpression ownerExpression viewText
                          (Located (locatedSpan sourceBlock)
                            (Block stepsInBorrow)))
                      projected = Located (locatedSpan
                          (grammarV1FunctionBody functionDecl))
                        (Block
                          [ Located borrowSpan
                              (ExpressionStatement borrowExpression)
                          , Located returnSpan (ReturnStatement
                              (Located (locatedSpan returned)
                                returnedExpression))
                          ])
                      component = Located (locatedSpan
                          (grammarV1FunctionBody functionDecl))
                        (Component
                          { componentName =
                              locatedValue (grammarV1FunctionName functionDecl)
                          , componentParameters = []
                          , componentProvides = Nothing
                          , componentBody = projected
                          })
                      checkedMode = checkedResolvedTypeMode paramMode
                      environment = (emptySurfaceEnvironment staticContext)
                        { surfaceInitialBindings = Map.singleton ownerText
                            (InitialBinding
                              (checkedBindingMode checkedMode)
                              (checkedBindingType checkedMode)
                              (shapeForType (checkedBindingType checkedMode)))
                        }
                  run <- traceSurfaceBorrowComponent environment component
                  -- The tracing and regular production paths must agree.
                  let ordinary = checkSurfaceComponent environment component
                  if ordinary /= traceOutcome run then Nothing else
                    Just (Right GrammarV1AffineSourceTrace
                      { affineSourceDeclarationKey = dataKey
                      , affineSourceInterfaceRevision = revision
                      , affineSourceBinder = paramBinder
                      , affineSourceViewBinder = viewBinder
                      , affineSourceCheckedMode = checkedMode
                      , affineSourceTypeOrigin =
                          checkedResolvedTypeModeOrigin paramMode
                      , affineSourceFocusingSteps = steps
                      , affineSourceCheckpoints = traceCheckpoints run
                      , affineSourceOutcome = traceOutcome run
                      })
        Right _ -> Nothing

semanticName :: GrammarV1ResolvedBinder -> Text
semanticName = unName . grammarV1ResolvedBinderCoreName

-- The bounded lexical surface admits only a resolved view occurrence and
-- explicit Unit within the borrow body. No invented general expression route.
bridgeStep
  :: GrammarV1ResolvedBinder
  -> GrammarV1CheckedLetScopeStep
  -> Maybe (Located Statement)
bridgeStep view (GrammarV1CheckedLetOccurrenceStep
  (Located span' (GrammarV1ExpressionStatement _)) occurrence)
    | grammarV1ResolvedBinderKey
        (grammarV1CheckedLocalValueBinder occurrence) ==
        grammarV1ResolvedBinderKey view =
      Just (Located span' (ExpressionStatement
        (Located (locatedSpan (grammarV1CheckedLocalValueSource occurrence))
          (VariableExpression (semanticName view)))))
bridgeStep _ (GrammarV1CheckedLetUnitStep
  (Located span' (GrammarV1ExpressionStatement source)))
    | GrammarV1UnitExpression <- locatedValue source =
        Just (Located span' (ExpressionStatement
          (Located (locatedSpan source) UnitExpression)))
bridgeStep _ _ = Nothing


-- | FSEM-01: source-checked affine Permit and linear Bytes owner in the
-- SAME two-parameter Grammar-v1 function and SAME production Surface run.
-- These are separate structural obligations: Permit is optionally droppable,
-- while Bytes must be moved before return. A failed return cannot be
-- reinterpreted as successful terminal cleanup.
data GrammarV1MixedAffineLinearTrace = GrammarV1MixedAffineLinearTrace
  { mixedDeclarationKey :: DeclarationKey
  , mixedInterfaceRevision :: InterfaceRevision
  , mixedAffineBinder :: GrammarV1ResolvedBinder
  , mixedLinearBinder :: GrammarV1ResolvedBinder
  , mixedViewBinder :: GrammarV1ResolvedBinder
  , mixedAffineCheckedMode :: CheckedTypeMode
  , mixedLinearCheckedMode :: CheckedTypeMode
  , mixedAffineTypeOrigin :: GrammarV1CheckedTypeModeOrigin
  , mixedCheckpoints :: [BorrowTraceCheckpoint]
  , mixedOutcome :: Either SurfaceCheckError SurfaceCheckResult
  } deriving (Eq, Show)

-- | Explicitly bounded two-owner elaboration. First parameter resolves to the
-- *admitted* nominal affine declaration, second to an intrinsically linear
-- Bytes[N] type. The result is exactly Unit or one of those two owner types.
-- There is only one lexical borrow of the affine owner, followed by one return.
-- Anything else is outside competence (Nothing), not silently validated.
-- Source declaration/interface roots and lifecycle attestation are still
-- supplied by the caller; satisfies C is NOT checked here.
grammarV1CheckedMixedAffineLinearFunctionTrace
  :: StaticContext
  -> DeclarationKey
  -> InterfaceRevision
  -> Maybe NominalRestrictionJustification
  -> GrammarV1DataDecl
  -> DeclarationKey
  -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1AffineSourceError GrammarV1MixedAffineLinearTrace)
grammarV1CheckedMixedAffineLinearFunctionTrace
    staticContext dataKey revision lifecycle dataDecl functionKey functionDecl
  | grammarV1FunctionRecursive functionDecl = Nothing
  | not (null (grammarV1FunctionGenericParams functionDecl)) = Nothing
  | not (null (grammarV1FunctionRequirements functionDecl)) = Nothing
  | otherwise = do
      [Located _ permitParam, Located _ bytesParam] <-
        pure (grammarV1FunctionTermParams functionDecl)
      resultSource <- grammarV1FunctionResultType functionDecl
      checkedData <- grammarV1CheckedClosedDataMode
        staticContext lifecycle dataDecl
      case checkedData of
        Left err -> Just (Left (AffineSourceNominalError err))
        Right admitted
          | checkedDataStructuralMode admitted /= Affine -> Nothing
          | otherwise -> do
              let dataName = locatedValue (grammarV1DataName dataDecl)
                  namedTy = TyOpaque dataName
                  reference = ReferencedGenericStaticActual dataName
                  resolved = GrammarV1ResolvedNamedTypeMode
                    { resolvedNamedTypeReference = reference
                    , resolvedNamedTypeKind = GenericTypeKind
                    , resolvedNamedTypeDeclarationKey = dataKey
                    , resolvedNamedTypeInterfaceRevision = revision
                    , resolvedNamedTypeCheckedMode =
                        CheckedTypeMode namedTy
                          (checkedDataStructuralMode admitted)
                    }
                  checkType ty =
                    grammarV1CheckedTypeModeWithNamedResolutions
                      staticContext emptySurfaceState [resolved] ty
              permitChecked <- checkType
                (locatedValue (grammarV1TermParamType permitParam))
              bytesChecked <- checkType
                (locatedValue (grammarV1TermParamType bytesParam))
              resultChecked <- checkType (locatedValue resultSource)
              case (permitChecked, bytesChecked, resultChecked) of
                (Left err, _, _) ->
                  Just (Left (AffineSourceTypeError err))
                (_, Left err, _) ->
                  Just (Left (AffineSourceTypeError err))
                (_, _, Left err) ->
                  Just (Left (AffineSourceTypeError err))
                (Right (permit, _), Right (bytes, _), Right (result, _)) ->
                  let permitMode = checkedResolvedTypeMode permit
                      bytesMode = checkedResolvedTypeMode bytes
                      returnTy = checkedBindingType (checkedResolvedTypeMode result)
                  in if permitMode == CheckedTypeMode namedTy Affine
                      && checkedResolvedTypeModeOrigin permit ==
                          GrammarV1NamedTypeModeOrigin reference dataKey revision
                      && isCheckedLinearBytes bytesMode
                      && (returnTy == TyUnit
                        || returnTy == checkedBindingType bytesMode
                        || returnTy == namedTy)
                    then sourceBody permit bytesMode returnTy
                    else Nothing
  where
    isCheckedLinearBytes binding = case checkedBindingType binding of
      TyBytes _ -> checkedBindingMode binding == Linear
      _ -> False

    sourceBody permit bytesMode returnTy = do
      [Located borrowSpan (GrammarV1ExpressionStatement borrow),
       Located returnSpan (GrammarV1ReturnStatement returned)] <-
        pure (grammarV1BlockStatements
          (locatedValue (grammarV1FunctionBody functionDecl)))
      case grammarV1FunctionParameterScope functionKey functionDecl of
        Left err -> Just (Left (AffineSourceBinderError err))
        Right ([permitBinder, bytesBinder], scope) -> do
          checkedBorrow <- grammarV1CheckedBorrowViewInScope scope borrow
          case checkedBorrow of
            Left err -> Just (Left (AffineSourceBorrowError err))
            Right (borrowTrace, afterScope) -> do
              let owner = grammarV1CheckedBorrowOwner borrowTrace
                  viewBinder = grammarV1CheckedBorrowViewBinder borrowTrace
                  same a b = grammarV1ResolvedBinderKey a ==
                    grammarV1ResolvedBinderKey b
                  permitMode = checkedResolvedTypeMode permit
              if not (same
                  (grammarV1CheckedLocalValueBinder owner) permitBinder)
                  then Nothing
                  else do
                    returnedExpression <- case (returnTy, locatedValue returned) of
                      (TyUnit, GrammarV1UnitExpression) -> Just UnitExpression
                      _ -> do
                        occurrence <- grammarV1CheckedLocalValueOccurrenceInScope
                          afterScope returned
                        let returnedBinder =
                              grammarV1CheckedLocalValueBinder occurrence
                        if same returnedBinder bytesBinder &&
                            returnTy == checkedBindingType bytesMode
                          then Just (VariableExpression (semanticName bytesBinder))
                          else if same returnedBinder permitBinder &&
                              returnTy == checkedBindingType permitMode
                            then Just (VariableExpression (semanticName permitBinder))
                            else Nothing
                    bodySteps <- mapM (bridgeStep viewBinder)
                      (grammarV1CheckedBorrowBodySteps borrowTrace)
                    Located _ (GrammarV1BorrowExpression sourceOwner _ sourceBlock)
                      <- pure (grammarV1CheckedBorrowViewSource borrowTrace)
                    let permitName = semanticName permitBinder
                        bytesName = semanticName bytesBinder
                        viewName = semanticName viewBinder
                        borrowExpression = Located (locatedSpan borrow)
                          (BorrowExpression
                            (Located (locatedSpan sourceOwner)
                              (VariableExpression permitName))
                            viewName
                            (Located (locatedSpan sourceBlock) (Block bodySteps)))
                        projected = Located (locatedSpan
                            (grammarV1FunctionBody functionDecl))
                          (Block
                            [ Located borrowSpan
                                (ExpressionStatement borrowExpression)
                            , Located returnSpan (ReturnStatement
                                (Located (locatedSpan returned) returnedExpression))
                            ])
                        component = Located (locatedSpan
                            (grammarV1FunctionBody functionDecl))
                          (Component
                            { componentName =
                                locatedValue (grammarV1FunctionName functionDecl)
                            , componentParameters = []
                            , componentProvides = Nothing
                            , componentBody = projected
                            })
                        environment = (emptySurfaceEnvironment staticContext)
                          { surfaceInitialBindings = Map.fromList
                              [ (permitName, InitialBinding
                                  (checkedBindingMode permitMode)
                                  (checkedBindingType permitMode)
                                  (shapeForType (checkedBindingType permitMode)))
                              , (bytesName, InitialBinding
                                  (checkedBindingMode bytesMode)
                                  (checkedBindingType bytesMode)
                                  (shapeForType (checkedBindingType bytesMode)))
                              ]
                          }
                    run <- traceSurfaceBorrowComponent environment component
                    if checkSurfaceComponent environment component /=
                        traceOutcome run
                      then Nothing
                      else Just (Right GrammarV1MixedAffineLinearTrace
                        { mixedDeclarationKey = dataKey
                        , mixedInterfaceRevision = revision
                        , mixedAffineBinder = permitBinder
                        , mixedLinearBinder = bytesBinder
                        , mixedViewBinder = viewBinder
                        , mixedAffineCheckedMode = permitMode
                        , mixedLinearCheckedMode = bytesMode
                        , mixedAffineTypeOrigin =
                            checkedResolvedTypeModeOrigin permit
                        , mixedCheckpoints = traceCheckpoints run
                        , mixedOutcome = traceOutcome run
                        })
        Right _ -> Nothing
