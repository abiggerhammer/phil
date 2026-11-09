{-# LANGUAGE OverloadedStrings #-}

-- | FSEM-01 L-2: a real parsed-source Linear Bytes owner moves into the
-- loop header, then back through an explicit continue actual. The original
-- source owner cannot be reused. This is a static, finite resource bridge.
module Phil.Surface.GrammarV1.SourceLinearLoopTransfer
  ( GrammarV1LinearLoopError (..)
  , GrammarV1LinearLoopTrace (..)
  , grammarV1CheckedLinearLoopTransferTrace
  ) where

import qualified Data.Map.Strict as Map
import Phil.Core.CheckedBindingMode (CheckedTypeMode (..))
import Phil.Core.Static (DeclarationKey, StaticContext)
import Phil.Core.Syntax (Mode (..), Name (..), Ty (..))
import Phil.Surface.Check.Engine
  ( SourceBoolJoinInvariant (..), SourceLinearLoopRun (..)
  , checkSurfaceSourceLinearLoopComponent
  , traceSurfaceSourceLinearLoopComponent )
import Phil.Surface.Check.LoopControl
  ( LoopControlContract (..), LoopControlError
  , LoopControlKind (ContinueControl)
  , LoopControlSyntax (ExplicitLoopControl), elaborateLoopControl )
import Phil.Surface.Check.Support (emptySurfaceState, shapeForType)
import Phil.Surface.Check.Types
  ( InitialBinding (..), SurfaceCheckError
  , SurfaceEnvironment (..), emptySurfaceEnvironment )
import Phil.Surface.GrammarV1.BorrowViewScope
  ( GrammarV1CheckedBorrowView (..) )
import Phil.Surface.GrammarV1.LetPatternScope
  ( GrammarV1CheckedLetScopeStep (..) )
import Phil.Surface.GrammarV1.BinderScope
  ( GrammarV1BinderScopeError, GrammarV1ResolvedBinder (..)
  , grammarV1FunctionParameterScope )
import Phil.Surface.GrammarV1.CheckedType (grammarV1CheckedTypeMode)
import Phil.Surface.GrammarV1.LexicalReferenceScope
  ( GrammarV1CheckedLexicalReference (..) )
import Phil.Surface.GrammarV1.LoopStateScope
  ( GrammarV1CheckedLoopBodyStep (..)
  , GrammarV1CheckedLoopSlot (..), GrammarV1CheckedLoopState (..)
  , GrammarV1LoopStateScopeError, grammarV1CheckedLoopExpressionInScope )
import Phil.Surface.GrammarV1.ParameterBodyScope
  ( GrammarV1CheckedLocalValueOccurrence (..)
  , grammarV1CheckedLocalValueOccurrenceInScope )
import Phil.Surface.GrammarV1.Parser
  ( GrammarV1Block (..), GrammarV1Expression (..)
  , GrammarV1FunctionDecl (..), GrammarV1Proposition (..)
  , GrammarV1StateBinding (..), GrammarV1Statement (..)
  , GrammarV1TermParam (..) )
import Phil.Surface.Syntax
  ( Block (..), Component (..), Located (..), Statement (..)
  , SurfaceExpression (..) )

data GrammarV1LinearLoopError
  = LinearLoopBinderError GrammarV1BinderScopeError
  | LinearLoopScopeError GrammarV1LoopStateScopeError
  | LinearLoopArityError LoopControlError
  deriving (Eq, Show)

data GrammarV1LinearLoopTrace = GrammarV1LinearLoopTrace
  { linearLoopFlagBinder :: GrammarV1ResolvedBinder
  , linearLoopPayloadBinder :: GrammarV1ResolvedBinder
  , linearLoopAlternateBinder :: Maybe GrammarV1ResolvedBinder
  , linearLoopAlternateType :: Maybe Ty
  , linearLoopHeaderBinder :: GrammarV1ResolvedBinder
  , linearLoopEntryBinder :: GrammarV1ResolvedBinder
  , linearLoopBackedgeBinder :: GrammarV1ResolvedBinder
  , linearLoopBorrowViewBinder :: Maybe GrammarV1ResolvedBinder
  , linearLoopHeaderCheckedMode :: CheckedTypeMode
  , linearLoopInvariantProof :: SourceBoolJoinInvariant
  , linearLoopNativeRun :: SourceLinearLoopRun
  , linearLoopCheckedOutcome :: Either SurfaceCheckError ()
  } deriving (Eq, Show)

-- | Narrow admitted source:
--
-- fn cycle(flag:Bool,payload:Bytes[N])->Unit satisfies C {
--   loop state (owner:Bytes[N] = payload) invariant true {
--     continue(owner);
--   };
-- }
--
-- An optional one-statement scoped borrow before the explicit continue is
-- checked with the production loan path; no active loan may cross reentry.
-- Optional third source-declared Bytes[M] owner is admitted to test a
-- wrong-width predecessor and a second same-width owner that attempts to
-- rebind a STILL-LIVE header. No invented owner or arbitrary payload type.
grammarV1CheckedLinearLoopTransferTrace
  :: StaticContext -> DeclarationKey -> GrammarV1FunctionDecl
  -> Maybe (Either GrammarV1LinearLoopError GrammarV1LinearLoopTrace)
grammarV1CheckedLinearLoopTransferTrace staticContext fnKey fn
  | grammarV1FunctionRecursive fn = Nothing
  | not (null (grammarV1FunctionGenericParams fn)) = Nothing
  | not (null (grammarV1FunctionRequirements fn)) = Nothing
  | otherwise = do
      (Located _ flagParam,Located _ payloadParam,extra) <-
        case grammarV1FunctionTermParams fn of
          [flag,payload] -> Just (flag,payload,Nothing)
          [flag,payload,alternate] -> Just (flag,payload,Just alternate)
          _ -> Nothing
      resultSource <- grammarV1FunctionResultType fn
      checked <- mapM
        (grammarV1CheckedTypeMode staticContext emptySurfaceState . locatedValue)
        ( [ grammarV1TermParamType flagParam
          , grammarV1TermParamType payloadParam
          , resultSource ]
          ++ maybe [] (\(Located _ p) -> [grammarV1TermParamType p]) extra )
      case sequence checked of
        Right [ (CheckedTypeMode TyBool Unrestricted, _)
              , (CheckedTypeMode payloadTy Linear, _)
              , (CheckedTypeMode TyUnit Unrestricted, _) ]
          | TyBytes _ <- payloadTy -> checkedBody payloadTy Nothing
        Right [ (CheckedTypeMode TyBool Unrestricted, _)
              , (CheckedTypeMode payloadTy Linear, _)
              , (CheckedTypeMode TyUnit Unrestricted, _)
              , (CheckedTypeMode extraTy Linear, _) ]
          | TyBytes _ <- payloadTy
          , TyBytes _ <- extraTy -> checkedBody payloadTy (Just extraTy)
        _ -> Nothing
  where
    checkedBody payloadTy maybeAlternateTy = do
      [Located _ (GrammarV1ExpressionStatement loopSource)] <-
        pure (grammarV1BlockStatements
          (locatedValue (grammarV1FunctionBody fn)))
      GrammarV1LoopExpression [locatedSlot] sourceInvariant _ <-
        pure (locatedValue loopSource)
      sourceHeaderTy <- grammarV1StateBindingType (locatedValue locatedSlot)
      checkedHeader <- grammarV1CheckedTypeMode
        staticContext emptySurfaceState (locatedValue sourceHeaderTy)
      case checkedHeader of
        Right (CheckedTypeMode actualTy Linear, _)
          | actualTy == payloadTy ->
            case grammarV1FunctionParameterScope fnKey fn of
              Left err -> Just (Left (LinearLoopBinderError err))
              Right (parameters,preLoopScope) -> do
                (flag,payload,maybeAlternate) <- case parameters of
                  [one,two] | maybeAlternateTy == Nothing ->
                    Just (one,two,Nothing)
                  [one,two,three] | maybeAlternateTy /= Nothing ->
                    Just (one,two,Just three)
                  _ -> Nothing
                checked <- grammarV1CheckedLoopExpressionInScope
                  preLoopScope loopSource
                case checked of
                  Left err -> Just (Left (LinearLoopScopeError err))
                  Right (checkedLoop,_) -> do
                    [slot] <- pure (grammarV1CheckedLoopSlots checkedLoop)
                    _ <- if null (grammarV1CheckedLoopSlotTypeReferences slot)
                      then Just () else Nothing
                    let header = grammarV1CheckedLoopSlotBinder slot
                        initializer = grammarV1StateBindingInitializer
                          (locatedValue locatedSlot)
                        known = [flag,payload] ++ maybe [] pure maybeAlternate
                    [entryReference] <- pure
                      (grammarV1CheckedLoopSlotInitializerReferences slot)
                    entryBinder <- exactEntry preLoopScope initializer
                      known entryReference
                    (maybeBorrow, actuals, refs) <-
                      case grammarV1CheckedLoopBodySteps checkedLoop of
                        [GrammarV1CheckedLoopContinueStep _ values references] ->
                          Just (Nothing,values,references)
                        [GrammarV1CheckedLoopBodyBorrowStep _ loan,
                         GrammarV1CheckedLoopContinueStep _ values references] ->
                          Just (Just loan,values,references)
                        _ -> Nothing
                    selectedActuals <- Just (elaborateLoopControl
                      ContinueControl
                      (LoopControlContract [semanticName header] [])
                      (ExplicitLoopControl actuals))
                    case selectedActuals of
                      Left err -> Just (Left (LinearLoopArityError err))
                      Right [backedgeSource] -> do
                        [actualReference] <- pure refs
                        backedgeBinder <- exactBackedge backedgeSource
                          (known ++ [header]) actualReference
                        (borrowBlock,maybeView) <-
                          projectBorrow (known ++ [header]) maybeBorrow
                        invariant <- checkInvariant checkedLoop sourceInvariant
                        let span' = locatedSpan (grammarV1FunctionBody fn)
                            component = Located span' (Component
                              { componentName =
                                  locatedValue (grammarV1FunctionName fn)
                              , componentParameters = []
                              , componentProvides = Nothing
                              , componentBody = Located span' (Block []) })
                            bindings =
                              [ (semanticName flag, InitialBinding
                                  Unrestricted TyBool (shapeForType TyBool))
                              , (semanticName payload, InitialBinding
                                  Linear payloadTy (shapeForType payloadTy))
                              ] ++ case (maybeAlternate,maybeAlternateTy) of
                                (Just alt,Just ty) ->
                                  [(semanticName alt, InitialBinding
                                    Linear ty (shapeForType ty))]
                                _ -> []
                            env = (emptySurfaceEnvironment staticContext)
                              { surfaceInitialBindings = Map.fromList bindings }
                            entryBlock = sourceBlock initializer entryBinder
                            backedgeBlock = sourceBlock
                              backedgeSource backedgeBinder
                            loopSpan = locatedSpan loopSource
                            production = checkSurfaceSourceLinearLoopComponent
                              env component entryBlock borrowBlock backedgeBlock loopSpan
                              (semanticName header) payloadTy invariant
                            replay = traceSurfaceSourceLinearLoopComponent
                              env component entryBlock borrowBlock backedgeBlock loopSpan
                              (semanticName header) payloadTy invariant
                        if sourceLinearLoopOutcome replay /= production
                          then Nothing
                          else Just (Right GrammarV1LinearLoopTrace
                            { linearLoopFlagBinder = flag
                            , linearLoopPayloadBinder = payload
                            , linearLoopAlternateBinder = maybeAlternate
                            , linearLoopAlternateType = maybeAlternateTy
                            , linearLoopHeaderBinder = header
                            , linearLoopEntryBinder = entryBinder
                            , linearLoopBackedgeBinder = backedgeBinder
                            , linearLoopBorrowViewBinder = maybeView
                            , linearLoopHeaderCheckedMode =
                                CheckedTypeMode payloadTy Linear
                            , linearLoopInvariantProof = invariant
                            , linearLoopNativeRun = replay
                            , linearLoopCheckedOutcome = production })
                      Right _ -> Nothing
        _ -> Nothing

    -- Borrow owner/view identities come from the Grammar-v1 scoped source.
    -- The restricted body projection accepts Unit and exact resolved value
    -- occurrences only. It never synthesizes a loan or an unscoped alias.
    projectBorrow _ Nothing = Just (Nothing,Nothing)
    projectBorrow known (Just checked) = do
      let source = grammarV1CheckedBorrowViewSource checked
          ownerOccurrence = grammarV1CheckedBorrowOwner checked
          view = grammarV1CheckedBorrowViewBinder checked
      originalOwner <- findExact known
        (grammarV1CheckedLocalValueBinder ownerOccurrence)
      Located _ (GrammarV1BorrowExpression ownerSource _ sourceBody) <-
        pure source
      body <- projectBorrowBody (view : known)
        (grammarV1CheckedBorrowBodySteps checked)
      let borrow = Located (locatedSpan source)
            (BorrowExpression
              (Located (locatedSpan ownerSource)
                (VariableExpression (semanticName originalOwner)))
              (semanticName view)
              (Located (locatedSpan sourceBody) (Block body)))
          block = Located (locatedSpan source)
            (Block [Located (locatedSpan source)
              (ExpressionStatement borrow)])
      Just (Just block,Just view)

    projectBorrowBody _ [] = Just []
    projectBorrowBody known (step : rest) =
      case step of
        GrammarV1CheckedLetUnitStep
          (Located span' (GrammarV1ExpressionStatement expression))
          | GrammarV1UnitExpression <- locatedValue expression -> do
              later <- projectBorrowBody known rest
              Just (Located span'
                (ExpressionStatement (Located
                  (locatedSpan expression) UnitExpression)) : later)
        GrammarV1CheckedLetOccurrenceStep
          (Located span' (GrammarV1ExpressionStatement _)) occurrence -> do
            resolved <- findExact known
              (grammarV1CheckedLocalValueBinder occurrence)
            later <- projectBorrowBody known rest
            Just (Located span' (ExpressionStatement (Located
              (locatedSpan (grammarV1CheckedLocalValueSource occurrence))
              (VariableExpression (semanticName resolved)))) : later)
        _ -> Nothing

    sourceBlock source binder = Located (locatedSpan source)
      (Block [Located (locatedSpan source)
        (ExpressionStatement (Located (locatedSpan source)
          (VariableExpression (semanticName binder))))])

    exactEntry scope source permitted reference = do
      occurrence <- grammarV1CheckedLocalValueOccurrenceInScope scope source
      let binder = grammarV1CheckedLocalValueBinder occurrence
      _ <- if same binder
               (grammarV1CheckedLexicalReferenceBinder reference)
             && locatedSpan
               (grammarV1CheckedLexicalReferenceSource reference)
               == locatedSpan source
        then Just () else Nothing
      findExact permitted binder

    exactBackedge source permitted reference = do
      _ <- if locatedSpan
        (grammarV1CheckedLexicalReferenceSource reference)
          == locatedSpan source then Just () else Nothing
      findExact permitted (grammarV1CheckedLexicalReferenceBinder reference)

    checkInvariant checkedLoop maybeProposition = do
      proposition <- maybeProposition
      case locatedValue proposition of
        GrammarV1TrueProposition
          | null (grammarV1CheckedLoopInvariantReferences checkedLoop) ->
              Just SourceBoolInvariantProvenTrue
        GrammarV1FalseProposition
          | null (grammarV1CheckedLoopInvariantReferences checkedLoop) ->
              Just SourceBoolInvariantUnproved
        _ -> Nothing

    findExact known binder = case filter (same binder) known of
      [one] -> Just one
      _ -> Nothing
    same a b = grammarV1ResolvedBinderKey a ==
      grammarV1ResolvedBinderKey b
    semanticName = unName . grammarV1ResolvedBinderCoreName
