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
import qualified Data.Set as Set
import Phil.Core.Checker (CheckState (..))
import Phil.Core.Context
  ( CheckError
  , useBinding
  )
import Phil.Core.Refinement
  ( EvidenceUse (..)
  , RefinementError
  , ResidualSpec
  , bindingEvidencePropositions
  , dischargeProposition
  , dischargePropositionUsing
  , normalizeProposition
  , normalizeRefTerm
  , propositionMentions
  , residualizeProposition
  , substituteProposition
  )
import Phil.Core.Session (exposeSessionHead)
import Phil.Core.Syntax
  ( Branch (..)
  , Mode
  , Name
  , PendingRecvSpec (..)
  , Proposition (..)
  , RefTerm (..)
  , Session (..)
  , Ty (..)
  , Value (..)
  )

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
      case ty of
        TyPendingRecv _ -> Left (InternalResourceNotValue name ty)
        _ -> pure ValueResult
          { valueResultType = ty
          , valueResultMode = Just mode
          , valueResultTerm = Just (RefVar name)
          , valueResultEvidence =
              map (EvidenceByBinding name . normalizeProposition)
                (bindingEvidencePropositions name ty)
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
      (evidenceUse, nextState) <-
        case matchingCarriedEvidence required (valueResultEvidence baseResult) of
          Just carried -> Right (carried, valueResultState baseResult)
          Nothing ->
            case (explicitEvidence, residualSpec) of
              (_, _) | normalizeProposition required == Truth ->
                Right (EvidenceByDefinition required, valueResultState baseResult)
              (Just evidenceName, _) -> do
                use <- mapLeft ValueRefinementError $
                  dischargePropositionUsing evidenceName required (valueResultState baseResult)
                Right (use, valueResultState baseResult)
              (Nothing, Just spec) ->
                mapLeft ValueRefinementError $
                  residualizeProposition spec required (valueResultState baseResult)
              (Nothing, Nothing) -> do
                use <- mapLeft ValueRefinementError $
                  dischargeProposition required (valueResultState baseResult)
                Right (use, valueResultState baseResult)
      Right baseResult
        { valueResultType = expected
        , valueResultEvidence = appendEvidence evidenceUse (valueResultEvidence baseResult)
        , valueResultState = nextState
        }
    _ -> do
      synthesized <- synthValue value state
      let actual = valueResultType synthesized
      case compareTypes actual expected of
        DefinitionallyEqual -> Right synthesized { valueResultType = expected }
        RequiresPropositionalEquality -> Left (ExplicitTransportRequired actual expected)
        IncompatibleTypes
          | refinementErasesTo actual expected ->
              Right synthesized { valueResultType = expected }
          | otherwise -> Left (ValueTypeMismatch actual expected)

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

appendEvidence :: EvidenceUse -> [EvidenceUse] -> [EvidenceUse]
appendEvidence evidenceUse existing
  | evidenceUse `elem` existing = existing
  | otherwise = existing ++ [evidenceUse]

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
  | not (propositionMentions binder proposition) =
      Right (normalizeProposition proposition)
  | otherwise =
      case valueResultTerm result of
        Just term -> Right (normalizeProposition (substituteProposition binder term proposition))
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
    _ ->
      case transportRequirement sourceTy targetTy of
        TransportDefinitionallyEqual -> Left (TransportNotRequired sourceTy)
        TransportUnsupported -> Left (UnsupportedTransport sourceTy targetTy)
        TransportRequires proposition -> do
          evidenceUse <- mapLeft ValueRefinementError $
            dischargePropositionUsing proofName proposition (valueResultState source)
          Right source
            { valueResultType = targetTy
            , valueResultEvidence = appendEvidence evidenceUse (valueResultEvidence source)
            }

data TransportRequirement
  = TransportDefinitionallyEqual
  | TransportRequires Proposition
  | TransportUnsupported

transportRequirement :: Ty -> Ty -> TransportRequirement
transportRequirement source target
  | definitionallyEqualTy source target = TransportDefinitionallyEqual
  | otherwise =
      case (source, target) of
        (TyBytes sourceIndex, TyBytes targetIndex) ->
          TransportRequires (Equal (normalizeRefTerm sourceIndex) (normalizeRefTerm targetIndex))
        _ -> TransportUnsupported

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

type BinderEnv = [(Name, Name)]

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
    (TyRefined leftBinder leftBase leftProp, TyRefined rightBinder rightBase rightProp) ->
      equalTy env leftBase rightBase
        && equalProposition
          (extendBinder leftBinder rightBinder env)
          leftProp
          rightProp
    (TyOpaque leftName, TyOpaque rightName) -> leftName == rightName
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
  (left, right) : filter notShadowed env
  where
    notShadowed (existingLeft, existingRight) =
      existingLeft /= left && existingRight /= right

equalReferencedName :: BinderEnv -> Name -> Name -> Bool
equalReferencedName env left right =
  case (bindingDepth fst left env, bindingDepth snd right env) of
    (Nothing, Nothing) -> left == right
    (Just leftDepth, Just rightDepth) -> leftDepth == rightDepth
    _ -> False

bindingDepth :: ((Name, Name) -> Name) -> Name -> BinderEnv -> Maybe Int
bindingDepth project target = findIndex ((== target) . project)

equalRefTerm :: BinderEnv -> RefTerm -> RefTerm -> Bool
equalRefTerm env left right =
  case (normalizeRefTerm left, normalizeRefTerm right) of
    (RefVar leftName, RefVar rightName) -> equalReferencedName env leftName rightName
    (RefNat leftValue, RefNat rightValue) -> leftValue == rightValue
    (RefUInt leftWidth leftValue, RefUInt rightWidth rightValue) ->
      leftWidth == rightWidth && leftValue == rightValue
    (RefBool leftValue, RefBool rightValue) -> leftValue == rightValue
    (RefField leftBase leftField, RefField rightBase rightField) ->
      leftField == rightField && equalRefTerm env leftBase rightBase
    (RefLen leftValue, RefLen rightValue) -> equalRefTerm env leftValue rightValue
    (RefToNat leftValue, RefToNat rightValue) -> equalRefTerm env leftValue rightValue
    (RefAdd leftA leftB, RefAdd rightA rightB) ->
      equalRefTerm env leftA rightA && equalRefTerm env leftB rightB
    (RefSub leftA leftB, RefSub rightA rightB) ->
      equalRefTerm env leftA rightA && equalRefTerm env leftB rightB
    (RefScale leftCoefficient leftValue, RefScale rightCoefficient rightValue) ->
      leftCoefficient == rightCoefficient && equalRefTerm env leftValue rightValue
    (RefOpaque leftText, RefOpaque rightText) -> leftText == rightText
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

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
