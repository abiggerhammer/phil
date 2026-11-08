{-# LANGUAGE OverloadedStrings #-}

-- | A bounded source-derived affine resource route. This does not promote the
-- source's "mode affine" spelling into semantic authority: the existing
-- nominal checker must also admit the supplied external lifecycle evidence.
-- Named parameters retain exact declaration and interface provenance.
module Phil.Surface.GrammarV1.SourceAffineResource
  ( GrammarV1AffineSourceError (..)
  , GrammarV1AffineSourceTrace (..)
  , grammarV1CheckedAffineFunctionTrace
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
import Phil.Core.Syntax (Control (..), Mode (..), Name (..), Ty (..))
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
  , GrammarV1Type (..)
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
