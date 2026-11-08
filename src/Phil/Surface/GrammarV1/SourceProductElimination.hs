{-# LANGUAGE OverloadedStrings #-}

-- | Bounded FSEM-01 source authority for an affine/linear product let.
-- A source-declared nominal mode still needs external admitted lifecycle
-- evidence; this adapter does not prove the external attestation.
module Phil.Surface.GrammarV1.SourceProductElimination
  ( GrammarV1ProductEliminationError (..)
  , GrammarV1ProductEliminationTrace (..)
  , grammarV1CheckedProductEliminationTrace
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..), GenericStaticKind (..) )
import Phil.Core.NominalDataMode (NominalRestrictionJustification)
import Phil.Core.Static (DeclarationKey, InterfaceRevision, StaticContext)
import Phil.Core.Syntax (Mode (..), Name (..), ProductElementType (..), Ty (..))
import Phil.Surface.Check.Engine
  ( ProductEliminationRun (..), checkSurfaceComponent
  , traceSurfaceProductEliminationComponent )
import Phil.Surface.Check.Support (emptySurfaceState, shapeForType)
import Phil.Surface.Check.Types
  ( InitialBinding (..), SurfaceCheckError, SurfaceCheckResult
  , SurfaceEnvironment (..), emptySurfaceEnvironment )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderKind (GrammarV1LetPatternBinder)
  , GrammarV1BinderScopeError, GrammarV1LexicalScope
  , GrammarV1ResolvedBinder (..), grammarV1FunctionParameterScope )
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
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , grammarV1CheckedLocalValueOccurrenceInScope )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..), GrammarV1DataDecl (..), GrammarV1Expression (..)
  , GrammarV1FunctionDecl (..), GrammarV1Pattern (..)
  , GrammarV1Statement (..), GrammarV1TermParam (..), GrammarV1Type (..) )
import Phil.Surface.GrammarV1.PatternBinderScope (grammarV1BindPattern)
import Phil.Surface.Syntax
  ( Block (..), Component (..), Located (..), Pattern (..)
  , Statement (..), SurfaceExpression (..) )

data GrammarV1ProductEliminationError
  = ProductEliminationNominalError GrammarV1CheckedDataModeError
  | ProductEliminationTypeError GrammarV1CheckedTypeModeResolutionError
  | ProductEliminationBinderError GrammarV1BinderScopeError
  deriving (Eq, Show)

data GrammarV1ProductEliminationTrace = GrammarV1ProductEliminationTrace
  { eliminatedSourceDeclarationKey :: DeclarationKey
  , eliminatedSourceInterfaceRevision :: InterfaceRevision
  , eliminatedSourceOwnerBinder :: GrammarV1ResolvedBinder
  , eliminatedSourceSuccessorBinders :: [GrammarV1ResolvedBinder]
  , eliminatedSourceParameter :: CheckedTypeMode
  , eliminatedSourceElements :: [GrammarV1CheckedResolvedTypeMode]
  , eliminatedSourceReturn :: CheckedTypeMode
  , eliminatedSourceProduction :: ProductEliminationRun
  , eliminatedSourceOutcome :: Either SurfaceCheckError SurfaceCheckResult
  } deriving (Eq, Show)

-- | Exactly one checked nominal affine + intrinsic linear product parameter,
-- one flat tuple let, one scalar or flat two-element return. A third let
-- successor is admitted only to exercise native arity rejection. Generic,
-- nested, recursive and unrelated source constructs remain non-competence.
grammarV1CheckedProductEliminationTrace
  :: StaticContext
  -> DeclarationKey
  -> InterfaceRevision
  -> Maybe NominalRestrictionJustification
  -> GrammarV1DataDecl
  -> DeclarationKey
  -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1ProductEliminationError GrammarV1ProductEliminationTrace)
grammarV1CheckedProductEliminationTrace
    staticContext dataKey revision lifecycle dataDecl functionKey functionDecl
  | grammarV1FunctionRecursive functionDecl = Nothing
  | not (null (grammarV1FunctionGenericParams functionDecl)) = Nothing
  | not (null (grammarV1FunctionRequirements functionDecl)) = Nothing
  | otherwise = do
      [Located _ packetParam] <- pure (grammarV1FunctionTermParams functionDecl)
      sourceResult <- grammarV1FunctionResultType functionDecl
      checkedData <- grammarV1CheckedClosedDataMode
        staticContext lifecycle dataDecl
      case checkedData of
        Left err -> Just (Left (ProductEliminationNominalError err))
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
                    , resolvedNamedTypeCheckedMode = CheckedTypeMode namedTy Affine
                    }
                  checkFlat = grammarV1CheckedFlatProductWithNamedResolutions
                    staticContext emptySurfaceState [resolution]
                  checkSingle = grammarV1CheckedTypeModeWithNamedResolutions
                    staticContext emptySurfaceState [resolution]
              parameterChecked <- checkFlat
                (locatedValue (grammarV1TermParamType packetParam))
              returnChecked <- case locatedValue sourceResult of
                GrammarV1TupleType _ -> do
                  result <- checkFlat (locatedValue sourceResult)
                  Just $ fmap (\flat ->
                    (checkedResolvedFlatProductMode flat,
                     Just (flatMembers flat))) result
                _ -> do
                  result <- checkSingle (locatedValue sourceResult)
                  Just $ fmap (\(single, _) ->
                    (checkedResolvedTypeMode single, Nothing)) result
              case (parameterChecked, returnChecked) of
                (Left err, _) -> Just (Left (ProductEliminationTypeError err))
                (_, Left err) -> Just (Left (ProductEliminationTypeError err))
                (Right packet, Right (returnMode, returnProduct)) ->
                  case checkedResolvedFlatProductElements packet of
                    [affineMember, linearMember]
                      | TyBytes size <-
                          checkedBindingType (checkedResolvedTypeMode linearMember)
                      , checkedResolvedTypeMode affineMember ==
                          CheckedTypeMode namedTy Affine
                      , checkedBindingMode (checkedResolvedTypeMode linearMember) ==
                          Linear
                      , checkedResolvedFlatProductMode packet ==
                          CheckedTypeMode (TyProduct
                            [ ProductElementType Affine namedTy
                            , ProductElementType Linear (TyBytes size) ]) Linear
                      , checkedResolvedTypeModeOrigin affineMember ==
                          GrammarV1NamedTypeModeOrigin reference dataKey revision
                      , checkedResolvedTypeModeOrigin linearMember ==
                          GrammarV1IntrinsicTypeModeOrigin
                      , admissibleReturn namedTy (TyBytes size)
                          returnMode returnProduct ->
                          sourceBody packet returnMode returnProduct
                    _ -> Nothing
  where
    flatMembers flat = case
        checkedBindingType (checkedResolvedFlatProductMode flat) of
      TyProduct elements -> elements
      _ -> []

    admissibleReturn nominal bytes checked maybeProduct =
      case (checkedBindingType checked, maybeProduct) of
        (TyUnit, Nothing) -> True
        (TyOpaque _, Nothing) -> checkedBindingType checked == nominal
        (TyBytes _, Nothing) -> checkedBindingType checked == bytes
        (TyProduct members, Just exact) ->
          members == exact && length members == 2
        _ -> False

    sourceBody packet returnMode returnProduct = do
      [Located letSpan (GrammarV1LetStatement patternSource initializer),
       Located returnSpan (GrammarV1ReturnStatement returned)] <-
        pure (grammarV1BlockStatements
          (locatedValue (grammarV1FunctionBody functionDecl)))
      Located _ (GrammarV1TuplePattern patternMembers) <- pure patternSource
      if length patternMembers < 2 || length patternMembers > 3
        then Nothing
        else do
          _ <- traverse onlyIdentifier patternMembers
          case grammarV1FunctionParameterScope functionKey functionDecl of
            Left err -> Just (Left (ProductEliminationBinderError err))
            Right ([packetBinder], initialScope) -> do
              original <- grammarV1CheckedLocalValueOccurrenceInScope
                initialScope initializer
              if grammarV1ResolvedBinderKey
                   (grammarV1CheckedLocalValueBinder original) /=
                   grammarV1ResolvedBinderKey packetBinder
                then Nothing
                else case grammarV1BindPattern GrammarV1LetPatternBinder
                    patternSource initialScope of
                  Left err -> Just (Left (ProductEliminationBinderError err))
                  Right (successors, afterLetScope) -> do
                    returnedExpr <- projectReturned afterLetScope returned
                    let packetName = semanticName packetBinder
                        restoredNames = map semanticName successors
                        projectedPattern = Located (locatedSpan patternSource)
                          (TuplePattern
                            [ Located (locatedSpan entry) (BindPattern name)
                            | (entry, name) <- zip patternMembers restoredNames ])
                        projectedLet = Located letSpan
                          (LetStatement projectedPattern
                            (Located (locatedSpan initializer)
                              (VariableExpression packetName)))
                        projectedReturn = Located returnSpan
                          (ReturnStatement
                            (Located (locatedSpan returned) returnedExpr))
                        component = Located
                          (locatedSpan (grammarV1FunctionBody functionDecl))
                          (Component
                            { componentName =
                                locatedValue (grammarV1FunctionName functionDecl)
                            , componentParameters = []
                            , componentProvides = Nothing
                            , componentBody = Located
                                (locatedSpan (grammarV1FunctionBody functionDecl))
                                (Block [projectedLet, projectedReturn])
                            })
                        expected = case checkedBindingType
                          (checkedResolvedFlatProductMode packet) of
                            TyProduct members -> members
                            _ -> []
                        environment = (emptySurfaceEnvironment staticContext)
                          { surfaceInitialBindings = Map.singleton packetName
                              (InitialBinding
                                (checkedBindingMode
                                  (checkedResolvedFlatProductMode packet))
                                (checkedBindingType
                                  (checkedResolvedFlatProductMode packet))
                                (shapeForType
                                  (checkedBindingType
                                    (checkedResolvedFlatProductMode packet))))
                          , surfaceExpectedProductEliminations =
                              Map.singleton packetName expected
                          , surfaceExpectedProductReturn = returnProduct
                          }
                    run <- traceSurfaceProductEliminationComponent
                      environment component
                    let normal = checkSurfaceComponent environment component
                    if productEliminationOutcome run /= normal
                      then Nothing
                      else Just (Right GrammarV1ProductEliminationTrace
                        { eliminatedSourceDeclarationKey = dataKey
                        , eliminatedSourceInterfaceRevision = revision
                        , eliminatedSourceOwnerBinder = packetBinder
                        , eliminatedSourceSuccessorBinders = successors
                        , eliminatedSourceParameter =
                            checkedResolvedFlatProductMode packet
                        , eliminatedSourceElements =
                            checkedResolvedFlatProductElements packet
                        , eliminatedSourceReturn = returnMode
                        , eliminatedSourceProduction = run
                        , eliminatedSourceOutcome = normal
                        })
            Right _ -> Nothing

    onlyIdentifier item = case locatedValue item of
      GrammarV1IdentifierPattern _ -> Just ()
      _ -> Nothing

semanticName :: GrammarV1ResolvedBinder -> Text
semanticName = unName . grammarV1ResolvedBinderCoreName

projectReturned
  :: GrammarV1LexicalScope
  -> Located GrammarV1Expression
  -> Maybe SurfaceExpression
projectReturned scope source@(Located _ expression) = case expression of
  GrammarV1UnitExpression -> Just UnitExpression
  GrammarV1TupleExpression members
    | length members == 2 -> do
        resolved <- traverse
          (grammarV1CheckedLocalValueOccurrenceInScope scope) members
        Just (TupleExpression
          [ Located (locatedSpan original)
              (VariableExpression (semanticName
                (grammarV1CheckedLocalValueBinder occurrence)))
          | (original, occurrence) <- zip members resolved ])
  _ -> do
    occurrence <- grammarV1CheckedLocalValueOccurrenceInScope scope source
    Just (VariableExpression
      (semanticName (grammarV1CheckedLocalValueBinder occurrence)))
