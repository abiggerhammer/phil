module Phil.Core.Value
  ( ValueResult (..)
  , EqualityBoundary (..)
  , ValueError (..)
  , synthValue
  , checkValue
  , checkValueUsing
  , checkValueWithResidual
  , transportValue
  , compareTypes
  , definitionallyEqualTy
  , definitionallyEqualSession
  ) where

import Data.List (findIndex, sortOn)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Phil.Core.Checker (CheckState (..))
import Phil.Core.Context
  ( CheckError
  , ResourceContext (..)
  , useBinding
  )
import Phil.Core.Refinement
  ( EvidenceUse (..)
  , RefinementError (..)
  , ResidualSpec
  , bindingEvidencePropositions
  , dischargeProposition
  , dischargePropositionUsing
  , dischargeSideConditions
  , dischargeSideConditionsUnder
  , normalizeProposition
  , normalizeRefTerm
  , propositionMentions
  , residualizeProposition
  , residualizeSideConditions
  , substituteProposition
  )
import Phil.Core.Session (exposeSessionHead)
import Phil.Core.SortCheck (SortError, checkTypeSorts)
import Phil.Core.Syntax
  ( Branch (..)
  , Mode
  , Name
  , PendingRecvSpec (..)
  , ProductElementType (..)
  , Proposition (..)
  , RefTerm (..)
  , Session (..)
  , Ty (..)
  , Value (..)
  , isRuntimeBytesType
  )
import qualified ResourceLoopKernel as ResourceLoopKernel
import qualified RuntimeBytesKernel as RuntimeBytesKernel

data ValueResult = ValueResult
  { valueResultType :: Ty
  , valueResultMode :: Maybe Mode
  , valueResultTerm :: Maybe RefTerm
  , valueResultEvidence :: [EvidenceUse]
  , valueResultState :: CheckState
  }
  deriving (Eq, Show)

data EqualityBoundary
  = DefinitionallyEqual
  | RequiresPropositionalEquality
  | IncompatibleTypes
  deriving (Eq, Ord, Show)

data ValueError
  = ValueResourceError CheckError
  | ValueRefinementError RefinementError
  | InternalResourceNotValue Name Ty
  | InvalidUIntWidth Int
  | UIntLiteralOutOfRange Int Integer
  | RefinementSubjectNotVisible Name
  | ExplicitTransportRequired Ty Ty
  | TransportNotRequired Ty
  | UnsupportedTransport Ty Ty
  | TransportTargetRefined Ty
  | ValueTypeMismatch Ty Ty
  deriving (Eq, Show)

synthValue :: Value -> CheckState -> Either ValueError ValueResult
synthValue value state =
  case value of
    VVar name -> do
      (mode, ty, nextContext) <- mapLeft ValueResourceError $
        useBinding name (resourceContext state)
      mapLeft valueSortError (checkTypeSorts state ty)
      definednessUses <-
        checkTypeDefinednessWithSubject (Just (RefVar name)) [] ty state
      case ty of
        TyPendingRecv _ -> Left (InternalResourceNotValue name ty)
        _ -> pure ValueResult
          { valueResultType = ty
          , valueResultMode = Just mode
          , valueResultTerm = Just (RefVar name)
          , valueResultEvidence =
              appendEvidenceList
                definednessUses
                ( map (EvidenceByBinding name . normalizeProposition)
                    (bindingEvidencePropositions name ty)
                )
          , valueResultState = state { resourceContext = nextContext }
          }
    VUnit -> pureLiteral TyUnit Nothing
    VBool literal -> pureLiteral TyBool (Just (RefBool literal))
    VUInt width literal
      | width <= 0 -> Left (InvalidUIntWidth width)
      | literal < 0 || literal >= (2 ^ width) -> Left (UIntLiteralOutOfRange width literal)
      | otherwise -> pureLiteral (TyUInt width) (Just (RefUInt width literal))
    VAscribe inner annotatedTy -> do
      checked <- checkValue inner annotatedTy state
      pure checked { valueResultType = annotatedTy }
    VTransport inner proofName targetTy ->
      transportValue inner proofName targetTy state
  where
    pureLiteral ty term = Right ValueResult
      { valueResultType = ty
      , valueResultMode = Nothing
      , valueResultTerm = term
      , valueResultEvidence = []
      , valueResultState = state
      }

checkValue :: Value -> Ty -> CheckState -> Either ValueError ValueResult
checkValue value expected state =
  checkValueInternal Nothing Nothing value expected state

checkValueUsing
  :: Name
  -> Value
  -> Ty
  -> CheckState
  -> Either ValueError ValueResult
checkValueUsing evidenceName value expected state =
  checkValueInternal (Just evidenceName) Nothing value expected state

checkValueWithResidual
  :: ResidualSpec
  -> Value
  -> Ty
  -> CheckState
  -> Either ValueError ValueResult
checkValueWithResidual residualSpec value expected state =
  checkValueInternal Nothing (Just residualSpec) value expected state

checkValueInternal
  :: Maybe Name
  -> Maybe ResidualSpec
  -> Value
  -> Ty
  -> CheckState
  -> Either ValueError ValueResult
checkValueInternal explicitEvidence residualSpec value expected state =
  case expected of
    TyRefined binder base proposition -> do
      baseResult <- checkValue value base state
      required <- instantiateRefinement binder proposition baseResult
      let postState = valueResultState baseResult
          logicalState = refinementLogicalState state baseResult
      case matchingCarriedEvidence required (valueResultEvidence baseResult) of
        Just carried -> do
          (sideUses, nextState) <-
            case residualSpec of
              Just spec -> do
                (uses, refinementState) <- mapLeft ValueRefinementError $
                  residualizeSideConditions spec required logicalState
                Right (uses, refinementResultState postState refinementState)
              Nothing -> do
                uses <- mapLeft ValueRefinementError $
                  dischargeSideConditions required logicalState
                Right (uses, postState)
          Right baseResult
            { valueResultType = expected
            , valueResultEvidence = appendEvidenceList
                (sideUses ++ [carried])
                (valueResultEvidence baseResult)
            , valueResultState = nextState
            }
        Nothing -> do
          (evidenceUses, nextState) <-
            case (explicitEvidence, residualSpec) of
              (Just evidenceName, _) -> do
                uses <- mapLeft ValueRefinementError $
                  dischargePropositionUsing evidenceName required logicalState
                Right (uses, postState)
              (Nothing, Just spec) -> do
                (uses, refinementState) <- mapLeft ValueRefinementError $
                  residualizeProposition spec required logicalState
                Right (uses, refinementResultState postState refinementState)
              (Nothing, Nothing) -> do
                uses <- mapLeft ValueRefinementError $
                  dischargeProposition required logicalState
                Right (uses, postState)
          Right baseResult
            { valueResultType = expected
            , valueResultEvidence = appendEvidenceList evidenceUses (valueResultEvidence baseResult)
            , valueResultState = nextState
            }
    _ -> do
      mapLeft valueSortError (checkTypeSorts state expected)
      definednessUses <- checkTypeDefinedness expected state
      synthesized <- synthValue value state
      let actual = valueResultType synthesized
          accepted = synthesized
            { valueResultType = expected
            , valueResultEvidence = appendEvidenceList
                definednessUses
                (valueResultEvidence synthesized)
            }
      case bytesCheckDecision actual expected of
        RuntimeBytesKernel.BytesCheckAcceptedForgetting -> Right accepted
        RuntimeBytesKernel.BytesCheckAcceptedDefinitionallyEqual -> Right accepted
        RuntimeBytesKernel.BytesCheckRequiresExplicitTransport ->
          Left (ExplicitTransportRequired actual expected)
        RuntimeBytesKernel.BytesCheckIncompatible
          | refinementErasesTo actual expected -> Right accepted
          | otherwise -> Left (ValueTypeMismatch actual expected)

-- Refinement predicates live in a logical typing context, while affine and
-- linear values still have to make their ordinary one-shot resource transition.
-- Restore only the subject binding needed to interpret the checked value's
-- logical term; do not restore unrelated consumed resources or active loans.
refinementLogicalState :: CheckState -> ValueResult -> CheckState
refinementLogicalState before result =
  let after = valueResultState result
  in after
    { resourceContext =
        restoreLogicalSubject
          (valueResultTerm result)
          (resourceContext before)
          (resourceContext after)
    }

restoreLogicalSubject
  :: Maybe RefTerm
  -> ResourceContext
  -> ResourceContext
  -> ResourceContext
restoreLogicalSubject subject before after =
  case subject of
    Just (RefVar name) ->
      case Map.lookup name (unrestrictedBindings before) of
        Just ty -> after
          { unrestrictedBindings = Map.insert name ty (unrestrictedBindings after) }
        Nothing ->
          case Map.lookup name (affineBindings before) of
            Just ty -> after
              { affineBindings = Map.insert name ty (affineBindings after) }
            Nothing ->
              case Map.lookup name (linearBindings before) of
                Just ty -> after
                  { linearBindings = Map.insert name ty (linearBindings after) }
                Nothing -> after
    _ -> after

-- Residualization may add obligations while it is using the logical subject
-- view. Keep those obligations and their durable logical typing support, but
-- always return the actual post-consumption resource context from the base
-- value check.
refinementResultState :: CheckState -> CheckState -> CheckState
refinementResultState post refinementState =
  post
    { residualObligations = residualObligations refinementState
    , residualLogicalSubjects = residualLogicalSubjects refinementState
    }

matchingCarriedEvidence :: Proposition -> [EvidenceUse] -> Maybe EvidenceUse
matchingCarriedEvidence required = go
  where
    normalizedRequired = normalizeProposition required
    go [] = Nothing
    go (evidenceUse : rest) =
      case evidenceUse of
        EvidenceByDefinition proposition
          | normalizeProposition proposition == normalizedRequired -> Just evidenceUse
        EvidenceByBinding _ proposition
          | normalizeProposition proposition == normalizedRequired -> Just evidenceUse
        _ -> go rest

appendEvidenceList :: [EvidenceUse] -> [EvidenceUse] -> [EvidenceUse]
appendEvidenceList additions existing =
  foldl (flip appendEvidence) existing additions
  where
    appendEvidence evidenceUse accumulated
      | evidenceUse `elem` accumulated = accumulated
      | otherwise = accumulated ++ [evidenceUse]

-- | Discharge type-definedness prerequisites before definitional equality can
-- normalize away the partial term which generated them. Nested refinements are
-- checked under their logical binders without turning those binders into
-- resource bindings or requiring the refinement proposition itself to be true.
-- When a concrete subject term is available, instantiate the binder first.
checkTypeDefinedness :: Ty -> CheckState -> Either ValueError [EvidenceUse]
checkTypeDefinedness = checkTypeDefinednessWithSubject Nothing []

checkTypeDefinednessWithSubject
  :: Maybe RefTerm
  -> [(Name, Ty)]
  -> Ty
  -> CheckState
  -> Either ValueError [EvidenceUse]
checkTypeDefinednessWithSubject subject logicalBindings ty state =
  case ty of
    TyBytes index -> sideConditions logicalBindings (Equal index index)
    TyProof proposition -> sideConditions logicalBindings proposition
    TyProduct elements ->
      fmap concat $
        mapM
          (\element ->
            -- An aggregate product subject is not a logical subject for any
            -- individual element. Element refinements therefore keep their
            -- own binder scope instead of fabricating a field projection.
            checkTypeDefinednessWithSubject
              Nothing
              logicalBindings
              (productElementType element)
              state
          )
          elements
    TyRefined binder base proposition -> do
      baseUses <-
        checkTypeDefinednessWithSubject subject logicalBindings base state
      predicateUses <-
        case subject of
          Just term ->
            sideConditions
              logicalBindings
              (substituteProposition binder term proposition)
          Nothing ->
            sideConditions ((binder, base) : logicalBindings) proposition
      pure (baseUses ++ predicateUses)
    _ -> Right []
  where
    sideConditions bindings proposition =
      mapLeft ValueRefinementError $
        dischargeSideConditionsUnder bindings proposition state

refinementErasesTo :: Ty -> Ty -> Bool
refinementErasesTo actual expected =
  case actual of
    TyRefined _ base _ ->
      definitionallyEqualTy base expected || refinementErasesTo base expected
    _ -> False

instantiateRefinement
  :: Name
  -> Proposition
  -> ValueResult
  -> Either ValueError Proposition
instantiateRefinement binder proposition result
  | not (propositionMentions binder proposition) = Right proposition
  | otherwise =
      case valueResultTerm result of
        Just term -> Right (substituteProposition binder term proposition)
        Nothing -> Left (RefinementSubjectNotVisible binder)

transportValue
  :: Value
  -> Name
  -> Ty
  -> CheckState
  -> Either ValueError ValueResult
transportValue value proofName targetTy state = do
  source <- synthValue value state
  let sourceTy = valueResultType source
  case targetTy of
    TyRefined _ _ _ -> Left (TransportTargetRefined targetTy)
    _ -> do
      mapLeft valueSortError (checkTypeSorts state targetTy)
      case bytesCheckDecision sourceTy targetTy of
        RuntimeBytesKernel.BytesCheckAcceptedForgetting ->
          Left (TransportNotRequired sourceTy)
        _ -> case transportRequirement (valueResultTerm source) sourceTy targetTy of
          TransportDefinitionallyEqual ->
            case ResourceLoopKernel.decideStateTransportByFacts
                (definitionallyEqualTy sourceTy targetTy) False of
              ResourceLoopKernel.StateTransportAcceptedDecision ->
                Left (TransportNotRequired sourceTy)
              _ -> resourceLoopKernelInvariant "definitional-transport"
          TransportUnsupported -> Left (UnsupportedTransport sourceTy targetTy)
          TransportRequires proposition ->
            dischargeAndAcceptTransport (valueResultState source) source sourceTy proposition
          TransportRequiresPreConsumption proposition ->
            dischargeAndAcceptRuntimeBytesTransport state source sourceTy proposition
  where
    dischargeAndAcceptTransport evidenceState source sourceTy proposition = do
      evidenceUses <- mapLeft ValueRefinementError $
        dischargePropositionUsing proofName proposition evidenceState
      let explicitEvidenceAccepted = not (null evidenceUses)
      case ResourceLoopKernel.decideStateTransportByFacts
          (definitionallyEqualTy sourceTy targetTy)
          explicitEvidenceAccepted of
        ResourceLoopKernel.StateTransportAcceptedDecision ->
          Right source
            { valueResultType = targetTy
            , valueResultEvidence = appendEvidenceList evidenceUses (valueResultEvidence source)
            }
        _ -> resourceLoopKernelInvariant "explicit-transport"

    dischargeAndAcceptRuntimeBytesTransport evidenceState source sourceTy proposition = do
      evidenceUses <- mapLeft ValueRefinementError $
        dischargePropositionUsing proofName proposition evidenceState
      let explicitEvidenceAccepted = not (null evidenceUses)
          subjectVisible = maybe False (const True) (valueResultTerm source)
      case RuntimeBytesKernel.decideRuntimeBytesRefinementByFacts
          (isRuntimeBytesType sourceTy)
          (isExactBytesType targetTy)
          subjectVisible
          explicitEvidenceAccepted of
        RuntimeBytesKernel.RuntimeBytesRefinementAccepted ->
          case ResourceLoopKernel.decideStateTransportByFacts
              (definitionallyEqualTy sourceTy targetTy)
              explicitEvidenceAccepted of
            ResourceLoopKernel.StateTransportAcceptedDecision ->
              Right source
                { valueResultType = targetTy
                , valueResultEvidence = appendEvidenceList evidenceUses (valueResultEvidence source)
                }
            _ -> resourceLoopKernelInvariant "runtime-bytes-explicit-transport"
        _ -> Left (UnsupportedTransport sourceTy targetTy)

data TransportRequirement
  = TransportDefinitionallyEqual
  | TransportRequires Proposition
  | TransportRequiresPreConsumption Proposition
  | TransportUnsupported

transportRequirement :: Maybe RefTerm -> Ty -> Ty -> TransportRequirement
transportRequirement subject source target
  | definitionallyEqualTy source target = TransportDefinitionallyEqual
  | otherwise =
      case (source, target) of
        (TyBytes _, TyBytes targetIndex)
          | isRuntimeBytesType source ->
              case RuntimeBytesKernel.decideRuntimeBytesRefinementByFacts
                  True
                  (isExactBytesType target)
                  (maybe False (const True) subject)
                  False of
                RuntimeBytesKernel.RuntimeBytesRefinementEvidenceRequired ->
                  case subject of
                    Just valueTerm ->
                      TransportRequiresPreConsumption (Equal (RefLen valueTerm) targetIndex)
                    Nothing -> TransportUnsupported
                _ -> TransportUnsupported
        (TyBytes sourceIndex, TyBytes targetIndex) ->
          TransportRequires (Equal sourceIndex targetIndex)
        _ -> TransportUnsupported

bytesCheckDecision :: Ty -> Ty -> RuntimeBytesKernel.BytesCheckDecision
bytesCheckDecision source target =
  RuntimeBytesKernel.decideBytesCheckByFacts
    (bytesLengthForgetting source target)
    (definitionallyEqualTy source target)
    (sameDependentFamily source target)

-- | Dropping an exact Bytes index is directional type forgetting, not equality:
-- it preserves the same linear value while intentionally discarding only the
-- tracked length fact. The reverse direction therefore cannot use this path.
bytesLengthForgetting :: Ty -> Ty -> Bool
bytesLengthForgetting source target =
  case (source, target) of
    (TyBytes _, TyBytes _) ->
      not (isRuntimeBytesType source) && isRuntimeBytesType target
    _ -> False

isExactBytesType :: Ty -> Bool
isExactBytesType ty =
  case ty of
    TyBytes _ -> not (isRuntimeBytesType ty)
    _ -> False

resourceLoopKernelInvariant :: String -> Either e a
resourceLoopKernelInvariant label =
  error ("ResourceLoopKernel mismatch: " <> label)

compareTypes :: Ty -> Ty -> EqualityBoundary
compareTypes actual expected
  | definitionallyEqualTy actual expected = DefinitionallyEqual
  | sameDependentFamily actual expected = RequiresPropositionalEquality
  | otherwise = IncompatibleTypes

sameDependentFamily :: Ty -> Ty -> Bool
sameDependentFamily left right =
  case (left, right) of
    (TyBytes _, TyBytes _) -> True
    _ -> False

-- A paired binder entry is kept until both of its sides have been shadowed.
-- This preserves the independent nearest-binding depth on each side of an
-- alpha-equivalence comparison.  Dropping an entire pair when only one side is
-- shadowed loses a still-live binding and can turn two bound names into equal
-- free spellings.  Fully shadowed entries are removed so recursive comparison
-- reaches the same canonical environment again.
type BinderEnv = [(Maybe Name, Maybe Name)]

definitionallyEqualTy :: Ty -> Ty -> Bool
definitionallyEqualTy = equalTy []

definitionallyEqualSession :: Session -> Session -> Bool
definitionallyEqualSession = equalSession [] Set.empty

equalTy :: BinderEnv -> Ty -> Ty -> Bool
equalTy env left right =
  case (left, right) of
    (TyUnit, TyUnit) -> True
    (TyBool, TyBool) -> True
    (TyUInt leftWidth, TyUInt rightWidth) -> leftWidth == rightWidth
    (TyBytes leftIndex, TyBytes rightIndex) -> equalRefTerm env leftIndex rightIndex
    (TyFrame leftGrammar, TyFrame rightGrammar) -> leftGrammar == rightGrammar
    (TyProof leftProp, TyProof rightProp) -> equalProposition env leftProp rightProp
    (TyValidated leftClaim leftContext leftSubject, TyValidated rightClaim rightContext rightSubject) ->
      leftClaim == rightClaim
        && equalReferencedName env leftContext rightContext
        && equalReferencedName env leftSubject rightSubject
    (TyEndpoint leftSession, TyEndpoint rightSession) ->
      equalSession env Set.empty leftSession rightSession
    (TyPendingRecv leftPending, TyPendingRecv rightPending) ->
      pendingSourceEndpoint leftPending == pendingSourceEndpoint rightPending
        && pendingGrammar leftPending == pendingGrammar rightPending
        && pendingFrame leftPending == pendingFrame rightPending
        && equalSession
          (extendBinder (pendingBinder leftPending) (pendingBinder rightPending) env)
          Set.empty
          (pendingContinuation leftPending)
          (pendingContinuation rightPending)
    (TyProduct leftElements, TyProduct rightElements) ->
      length leftElements == length rightElements
        && and
          ( zipWith
              (\leftElement rightElement ->
                productElementMode leftElement == productElementMode rightElement
                  && equalTy env
                    (productElementType leftElement)
                    (productElementType rightElement)
              )
              leftElements
              rightElements
          )
    (TyRefined leftBinder leftBase leftProp, TyRefined rightBinder rightBase rightProp) ->
      equalTy env leftBase rightBase
        && equalProposition
          (extendBinder leftBinder rightBinder env)
          leftProp
          rightProp
    (TyOpaque leftName, TyOpaque rightName) -> leftName == rightName
    (TyOpaqueSorted leftName leftSort, TyOpaqueSorted rightName rightSort) ->
      leftName == rightName && leftSort == rightSort
    _ -> False

equalSession
  :: BinderEnv
  -> Set.Set (BinderEnv, Session, Session)
  -> Session
  -> Session
  -> Bool
equalSession env seen left right
  | Set.member (env, left, right) seen = True
  | otherwise =
      let seen' = Set.insert (env, left, right) seen
      in case (exposeSessionHead left, exposeSessionHead right) of
        (Right leftHead, Right rightHead) -> compareHeads env seen' leftHead rightHead
        _ -> False

compareHeads
  :: BinderEnv
  -> Set.Set (BinderEnv, Session, Session)
  -> Session
  -> Session
  -> Bool
compareHeads env seen left right =
  case (left, right) of
    (Send leftBinder leftTy leftNext, Send rightBinder rightTy rightNext) ->
      equalTy env leftTy rightTy
        && equalSession (extendBinder leftBinder rightBinder env) seen leftNext rightNext
    (Receive leftBinder leftTy leftNext, Receive rightBinder rightTy rightNext) ->
      equalTy env leftTy rightTy
        && equalSession (extendBinder leftBinder rightBinder env) seen leftNext rightNext
    (Select leftBranches, Select rightBranches) -> compareBranches env seen leftBranches rightBranches
    (Offer leftBranches, Offer rightBranches) -> compareBranches env seen leftBranches rightBranches
    (End leftOutcome, End rightOutcome) -> leftOutcome == rightOutcome
    _ -> False

compareBranches
  :: BinderEnv
  -> Set.Set (BinderEnv, Session, Session)
  -> [Branch]
  -> [Branch]
  -> Bool
compareBranches env seen leftBranches rightBranches =
  let leftSorted = sortOn branchLabel leftBranches
      rightSorted = sortOn branchLabel rightBranches
  in length leftSorted == length rightSorted
    && and (zipWith (compareBranch env seen) leftSorted rightSorted)

compareBranch
  :: BinderEnv
  -> Set.Set (BinderEnv, Session, Session)
  -> Branch
  -> Branch
  -> Bool
compareBranch env seen left right =
  branchLabel left == branchLabel right
    && case (branchPayload left, branchPayload right) of
      (Nothing, Nothing) ->
        equalSession env seen (branchContinuation left) (branchContinuation right)
      (Just (leftBinder, leftTy), Just (rightBinder, rightTy)) ->
        equalTy env leftTy rightTy
          && equalSession
            (extendBinder leftBinder rightBinder env)
            seen
            (branchContinuation left)
            (branchContinuation right)
      _ -> False

extendBinder :: Name -> Name -> BinderEnv -> BinderEnv
extendBinder left right env =
  (Just left, Just right) : foldr keep [] env
  where
    keep (existingLeft, existingRight) rest =
      case
          ( if existingLeft == Just left then Nothing else existingLeft
          , if existingRight == Just right then Nothing else existingRight
          ) of
        (Nothing, Nothing) -> rest
        surviving -> surviving : rest

equalReferencedName :: BinderEnv -> Name -> Name -> Bool
equalReferencedName env left right =
  case (bindingDepth fst left env, bindingDepth snd right env) of
    (Nothing, Nothing) -> left == right
    (Just leftDepth, Just rightDepth) -> leftDepth == rightDepth
    _ -> False

bindingDepth
  :: ((Maybe Name, Maybe Name) -> Maybe Name)
  -> Name
  -> BinderEnv
  -> Maybe Int
bindingDepth project target = findIndex ((== Just target) . project)

equalRefTerm :: BinderEnv -> RefTerm -> RefTerm -> Bool
equalRefTerm env left right =
  case (normalizeRefTerm left, normalizeRefTerm right) of
    (RefVar leftName, RefVar rightName) -> equalReferencedName env leftName rightName
    (RefNat leftValue, RefNat rightValue) -> leftValue == rightValue
    (RefUInt leftWidth leftValue, RefUInt rightWidth rightValue) ->
      leftWidth == rightWidth && leftValue == rightValue
    (RefBool leftValue, RefBool rightValue) -> leftValue == rightValue
    (RefField leftBase leftField leftSort, RefField rightBase rightField rightSort) ->
      leftField == rightField
        && leftSort == rightSort
        && equalRefTerm env leftBase rightBase
    (RefLen leftValue, RefLen rightValue) -> equalRefTerm env leftValue rightValue
    (RefToNat leftValue, RefToNat rightValue) -> equalRefTerm env leftValue rightValue
    (RefAdd leftA leftB, RefAdd rightA rightB) ->
      equalRefTerm env leftA rightA && equalRefTerm env leftB rightB
    (RefSub leftA leftB, RefSub rightA rightB) ->
      equalRefTerm env leftA rightA && equalRefTerm env leftB rightB
    (RefScale leftCoefficient leftValue, RefScale rightCoefficient rightValue) ->
      leftCoefficient == rightCoefficient && equalRefTerm env leftValue rightValue
    (RefOpaque leftSort leftText, RefOpaque rightSort rightText) ->
      leftSort == rightSort && leftText == rightText
    _ -> False

equalProposition :: BinderEnv -> Proposition -> Proposition -> Bool
equalProposition env left right =
  case (normalizeProposition left, normalizeProposition right) of
    (Truth, Truth) -> True
    (Falsehood, Falsehood) -> True
    (Equal leftA leftB, Equal rightA rightB) ->
      equalRefTerm env leftA rightA && equalRefTerm env leftB rightB
    (NotEqual leftA leftB, NotEqual rightA rightB) ->
      equalRefTerm env leftA rightA && equalRefTerm env leftB rightB
    (LessThan leftA leftB, LessThan rightA rightB) ->
      equalRefTerm env leftA rightA && equalRefTerm env leftB rightB
    (LessEqual leftA leftB, LessEqual rightA rightB) ->
      equalRefTerm env leftA rightA && equalRefTerm env leftB rightB
    (Member leftValue leftCollection, Member rightValue rightCollection) ->
      equalRefTerm env leftValue rightValue && equalRefTerm env leftCollection rightCollection
    (Disjoint leftA leftB, Disjoint rightA rightB) ->
      equalRefTerm env leftA rightA && equalRefTerm env leftB rightB
    (Conjunction leftA leftB, Conjunction rightA rightB) ->
      equalProposition env leftA rightA && equalProposition env leftB rightB
    (Disjunction leftA leftB, Disjunction rightA rightB) ->
      equalProposition env leftA rightA && equalProposition env leftB rightB
    (Negation leftInner, Negation rightInner) -> equalProposition env leftInner rightInner
    (Atom leftClaim leftArgs, Atom rightClaim rightArgs) ->
      leftClaim == rightClaim
        && length leftArgs == length rightArgs
        && and (zipWith (equalRefTerm env) leftArgs rightArgs)
    _ -> False

valueSortError :: SortError -> ValueError
valueSortError = ValueRefinementError . RefinementSortError

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
