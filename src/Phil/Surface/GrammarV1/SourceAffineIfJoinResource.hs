{-# LANGUAGE OverloadedStrings #-}

-- | FSEM-01 J-1/J-2: a single source-declared affine owner, a linear
-- spectator and two scoped if predecessors. The named affine mode is checked
-- against the existing externally admitted lifecycle gate; neither source
-- spelling nor this adapter supplies that authority.
module Phil.Surface.GrammarV1.SourceAffineIfJoinResource
  ( GrammarV1AffineIfJoinError (..)
  , GrammarV1AffineIfJoinTrace (..)
  , grammarV1CheckedAffineIfJoinTrace
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Generic.StaticActual
  ( GenericStaticActual (..), GenericStaticKind (..) )
import Phil.Core.NominalDataMode (NominalRestrictionJustification)
import Phil.Core.Static (DeclarationKey, InterfaceRevision, StaticContext)
import Phil.Core.Syntax (Mode (..), Name (..), Ty (..))
import Phil.Surface.Check.Engine
  ( SourceScopedIfJoinRun (..)
  , checkSurfaceScopedSourceIfJoinComponent
  , traceSurfaceScopedSourceIfJoinComponent )
import Phil.Surface.Check.Support (emptySurfaceState, shapeForType)
import Phil.Surface.Check.Types
  ( InitialBinding (..), SurfaceCheckError, SurfaceCheckResult
  , SurfaceEnvironment (..), emptySurfaceEnvironment )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError, GrammarV1ResolvedBinder (..)
  , grammarV1FunctionParameterScope )
import Phil.Surface.GrammarV1.CheckedType
  ( GrammarV1CheckedResolvedTypeMode (..)
  , GrammarV1CheckedTypeModeOrigin (..)
  , GrammarV1CheckedTypeModeResolutionError
  , GrammarV1ResolvedNamedTypeMode (..)
  , grammarV1CheckedTypeModeWithNamedResolutions )
import Phil.Surface.GrammarV1.DataVariants
  ( GrammarV1CheckedDataMode (..), GrammarV1CheckedDataModeError
  , grammarV1CheckedClosedDataMode )
import Phil.Surface.GrammarV1.JoinStateScope
  ( GrammarV1CheckedIfBranch (..), GrammarV1CheckedJoinClause (..)
  , GrammarV1CheckedJoinExpression (..), GrammarV1JoinStateScopeError
  , grammarV1CheckedJoinExpressionInScope )
import Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep (..) )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , grammarV1CheckedLocalValueOccurrenceInScope )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..), GrammarV1DataDecl (..)
  , GrammarV1Expression (..), GrammarV1FunctionDecl (..)
  , GrammarV1JoinClause (..), GrammarV1Pattern (..)
  , GrammarV1Statement (..), GrammarV1TermParam (..) )
import Phil.Surface.Syntax
  ( Block (..), Component (..), Located (..), Pattern (..)
  , Statement (..), SurfaceExpression (..) )

data GrammarV1AffineIfJoinError
  = AffineIfJoinNominalError GrammarV1CheckedDataModeError
  | AffineIfJoinTypeError GrammarV1CheckedTypeModeResolutionError
  | AffineIfJoinBinderError GrammarV1BinderScopeError
  | AffineIfJoinScopeError GrammarV1JoinStateScopeError
  deriving (Eq, Show)

-- | Exact source-derived identities and production before/raw/pruned/after
-- native contexts; source type/provenance are not reconstructed from display
-- spelling after source admission. The ordinary and traced outcomes are
-- independently run through the production Surface checker operations.
data GrammarV1AffineIfJoinTrace = GrammarV1AffineIfJoinTrace
  { affineIfJoinDataKey :: DeclarationKey
  , affineIfJoinInterfaceRevision :: InterfaceRevision
  , affineIfJoinFlagBinder :: GrammarV1ResolvedBinder
  , affineIfJoinPermitBinder :: GrammarV1ResolvedBinder
  , affineIfJoinPayloadBinder :: GrammarV1ResolvedBinder
  , affineIfJoinLocalBinders :: [GrammarV1ResolvedBinder]
  , affineIfJoinPermitMode :: CheckedTypeMode
  , affineIfJoinPermitOrigin :: GrammarV1CheckedTypeModeOrigin
  , affineIfJoinPayloadMode :: CheckedTypeMode
  , affineIfJoinRun :: SourceScopedIfJoinRun
  , affineIfJoinOutcome :: Either SurfaceCheckError SurfaceCheckResult
  } deriving (Eq, Show)

-- | Closed source fragment: data Permit mode affine, one nonrecursive
-- fn(flag:Bool, permit:Permit, payload:Bytes[N])->Bytes[N], and one
-- if flag join state () with one Unit or single-binder let from an existing
-- parameter in each arm. After the join, return payload, optionally preceded
-- by an occurrence of permit (used to verify illegal post-join reuse).
--
-- Only the checked and externally admitted named mode may enter the real
-- Surface checker. A source declaration alone is never lifecycle evidence.
grammarV1CheckedAffineIfJoinTrace
  :: StaticContext
  -> DeclarationKey
  -> InterfaceRevision
  -> Maybe NominalRestrictionJustification
  -> GrammarV1DataDecl
  -> DeclarationKey
  -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1AffineIfJoinError GrammarV1AffineIfJoinTrace)
grammarV1CheckedAffineIfJoinTrace
    staticContext dataKey revision lifecycle dataDecl fnKey functionDecl
  | grammarV1FunctionRecursive functionDecl = Nothing
  | not (null (grammarV1FunctionGenericParams functionDecl)) = Nothing
  | not (null (grammarV1FunctionRequirements functionDecl)) = Nothing
  | otherwise = do
      [Located _ flagParam, Located _ permitParam, Located _ payloadParam] <-
        pure (grammarV1FunctionTermParams functionDecl)
      sourceResult <- grammarV1FunctionResultType functionDecl
      checkedData <- grammarV1CheckedClosedDataMode
        staticContext lifecycle dataDecl
      case checkedData of
        Left err -> Just (Left (AffineIfJoinNominalError err))
        Right admitted
          | checkedDataStructuralMode admitted /= Affine -> Nothing
          | otherwise -> do
              let dataName = locatedValue (grammarV1DataName dataDecl)
                  nominalTy = TyOpaque dataName
                  reference = ReferencedGenericStaticActual dataName
                  resolved = GrammarV1ResolvedNamedTypeMode
                    { resolvedNamedTypeReference = reference
                    , resolvedNamedTypeKind = GenericTypeKind
                    , resolvedNamedTypeDeclarationKey = dataKey
                    , resolvedNamedTypeInterfaceRevision = revision
                    , resolvedNamedTypeCheckedMode =
                        CheckedTypeMode nominalTy Affine
                    }
                  checkType locatedType =
                    grammarV1CheckedTypeModeWithNamedResolutions
                      staticContext emptySurfaceState [resolved]
                      (locatedValue locatedType)
              checkedTypes <- mapM checkType
                [ grammarV1TermParamType flagParam
                , grammarV1TermParamType permitParam
                , grammarV1TermParamType payloadParam
                , sourceResult ]
              case sequence checkedTypes of
                Left err -> Just (Left (AffineIfJoinTypeError err))
                Right
                  [ (flag, _), (permit, _)
                  , (payload, _), (result, _) ] ->
                    let checkedMode = checkedResolvedTypeMode
                        permitMode = checkedMode permit
                        payloadMode = checkedMode payload
                    in case (checkedMode flag, permitMode, payloadMode,
                             checkedMode result) of
                      ( CheckedTypeMode TyBool Unrestricted
                        , CheckedTypeMode permitType Affine
                        , CheckedTypeMode payloadType Linear
                        , CheckedTypeMode returnType Linear )
                          | permitType == nominalTy
                          , TyBytes _ <- payloadType
                          , returnType == payloadType
                          , checkedResolvedTypeModeOrigin permit ==
                              GrammarV1NamedTypeModeOrigin
                                reference dataKey revision ->
                                  checkedSourceBody permit payloadMode
                                    permitMode payloadType
                      _ -> Nothing
                Right _ -> Nothing
  where
    checkedSourceBody permitResolved payloadMode permitMode payloadType = do
      (ifSource, afterSource) <- case
        grammarV1BlockStatements
          (locatedValue (grammarV1FunctionBody functionDecl)) of
          Located _ (GrammarV1ExpressionStatement source) : rest
            | not (null rest) -> Just (source, rest)
          _ -> Nothing
      GrammarV1IfExpression _ (Just joinSource) _ (Just _) <-
        pure (locatedValue ifSource)
      let clause = locatedValue joinSource
      if not (null (grammarV1JoinState clause)) ||
         grammarV1JoinInvariant clause /= Nothing
        then Nothing
        else case grammarV1FunctionParameterScope fnKey functionDecl of
          Left err -> Just (Left (AffineIfJoinBinderError err))
          Right ([flagBinder, permitBinder, payloadBinder], initialScope) -> do
            checkedJoin <- grammarV1CheckedJoinExpressionInScope
              initialScope ifSource
            case checkedJoin of
              Left err -> Just (Left (AffineIfJoinScopeError err))
              Right (GrammarV1CheckedIfJoinExpression condition left
                    (Just right) checkedClause, afterScope) -> do
                let same a b = grammarV1ResolvedBinderKey a ==
                      grammarV1ResolvedBinderKey b
                if not (same
                    (grammarV1CheckedLocalValueBinder condition) flagBinder)
                    || not (null (grammarV1CheckedJoinSlots checkedClause))
                  then Nothing
                  else do
                    (leftBlock, leftLocals) <- projectBranch
                      [flagBinder,permitBinder,payloadBinder] left
                    (rightBlock,rightLocals) <- projectBranch
                      [flagBinder,permitBinder,payloadBinder] right
                    tailStatements <- projectAfter afterScope
                      permitBinder payloadBinder afterSource
                    let flagName = semanticName flagBinder
                        permitName = semanticName permitBinder
                        payloadName = semanticName payloadBinder
                        component = Located
                          (locatedSpan (grammarV1FunctionBody functionDecl))
                          (Component
                            { componentName =
                                locatedValue (grammarV1FunctionName functionDecl)
                            , componentParameters = []
                            , componentProvides = Nothing
                            , componentBody = Located
                                (locatedSpan (grammarV1FunctionBody functionDecl))
                                (Block [])
                            })
                        environment = (emptySurfaceEnvironment staticContext)
                          { surfaceInitialBindings = Map.fromList
                              [ (flagName, InitialBinding
                                  Unrestricted TyBool (shapeForType TyBool))
                              , (permitName, InitialBinding
                                  (checkedBindingMode permitMode)
                                  (checkedBindingType permitMode)
                                  (shapeForType (checkedBindingType permitMode)))
                              , (payloadName, InitialBinding
                                  (checkedBindingMode payloadMode)
                                  (checkedBindingType payloadMode)
                                  (shapeForType payloadType))
                              ]
                          }
                        run = traceSurfaceScopedSourceIfJoinComponent
                          environment component leftBlock rightBlock tailStatements
                        ordinary = checkSurfaceScopedSourceIfJoinComponent
                          environment component leftBlock rightBlock tailStatements
                    if scopedIfJoinOutcome run /= ordinary
                      then Nothing
                      else Just (Right GrammarV1AffineIfJoinTrace
                        { affineIfJoinDataKey = dataKey
                        , affineIfJoinInterfaceRevision = revision
                        , affineIfJoinFlagBinder = flagBinder
                        , affineIfJoinPermitBinder = permitBinder
                        , affineIfJoinPayloadBinder = payloadBinder
                        , affineIfJoinLocalBinders = leftLocals ++ rightLocals
                        , affineIfJoinPermitMode =
                            checkedResolvedTypeMode permitResolved
                        , affineIfJoinPermitOrigin =
                            checkedResolvedTypeModeOrigin permitResolved
                        , affineIfJoinPayloadMode = payloadMode
                        , affineIfJoinRun = run
                        , affineIfJoinOutcome = ordinary
                        })
              Right _ -> Nothing
          Right _ -> Nothing

    semanticName :: GrammarV1ResolvedBinder -> Text
    semanticName = unName . grammarV1ResolvedBinderCoreName

    projectBranch parameters branch = do
      [step] <- pure (grammarV1CheckedIfBranchSteps branch)
      let src = grammarV1CheckedIfBranchSource branch
      case step of
        GrammarV1CheckedLetUnitStep
          (Located span' (GrammarV1ExpressionStatement source))
            | GrammarV1UnitExpression <- locatedValue source ->
                Just (Located (locatedSpan src)
                  (Block [Located span' (ExpressionStatement
                    (Located (locatedSpan source) UnitExpression))]), [])
        GrammarV1CheckedLetBindingStep
          (Located span' (GrammarV1LetStatement pattern' initializer))
          occurrence [binder] -> do
            GrammarV1IdentifierPattern _ <- pure (locatedValue pattern')
            let owner = grammarV1CheckedLocalValueBinder occurrence
            matched <- case filter
              (\param -> grammarV1ResolvedBinderKey param ==
                 grammarV1ResolvedBinderKey owner) parameters of
                [param] -> Just param
                _ -> Nothing
            Just
              ( Located (locatedSpan src) (Block
                  [ Located span' (LetStatement
                      (Located (locatedSpan pattern')
                        (BindPattern (semanticName binder)))
                      (Located (locatedSpan initializer)
                        (VariableExpression (semanticName matched)))) ])
              , [binder] )
        _ -> Nothing

    projectAfter scope permitBinder payloadBinder statements =
      case statements of
        [Located span' (GrammarV1ReturnStatement returned)] -> do
          occurrence <- grammarV1CheckedLocalValueOccurrenceInScope scope returned
          if sameBinder (grammarV1CheckedLocalValueBinder occurrence) payloadBinder
            then Just [Located span' (ReturnStatement
              (Located (locatedSpan returned)
                (VariableExpression (semanticName payloadBinder))))]
            else Nothing
        [ Located occurrenceSpan (GrammarV1ExpressionStatement value)
          , Located returnSpan (GrammarV1ReturnStatement returned) ] -> do
            occurrence <- grammarV1CheckedLocalValueOccurrenceInScope scope value
            returnedOccurrence <-
              grammarV1CheckedLocalValueOccurrenceInScope scope returned
            if sameBinder (grammarV1CheckedLocalValueBinder occurrence)
                 permitBinder
                 && sameBinder
                     (grammarV1CheckedLocalValueBinder returnedOccurrence)
                     payloadBinder
              then Just
                [ Located occurrenceSpan (ExpressionStatement
                    (Located (locatedSpan value)
                      (VariableExpression (semanticName permitBinder))))
                , Located returnSpan (ReturnStatement
                    (Located (locatedSpan returned)
                      (VariableExpression (semanticName payloadBinder))))
                ]
              else Nothing
        _ -> Nothing

    sameBinder a b = grammarV1ResolvedBinderKey a ==
      grammarV1ResolvedBinderKey b
