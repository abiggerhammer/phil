module Phil.Core.Value
  ( ValueResult (..)
  , EqualityBoundary (..)
  , ValueError (..)
  , synthValue
  , checkValue
  , compareTypes
  , definitionallyEqualTy
  , definitionallyEqualSession
  ) where

import Data.List (sortOn)
import qualified Data.Set as Set
import Phil.Core.Checker (CheckState (..))
import Phil.Core.Context
  ( CheckError
  , useBinding
  )
import Phil.Core.Session (exposeSessionHead)
import Phil.Core.Syntax
  ( Branch (..)
  , Mode
  , Name
  , PendingRecvSpec (..)
  , Session (..)
  , Ty (..)
  , Value (..)
  )

data ValueResult = ValueResult
  { valueResultType :: Ty
  , valueResultMode :: Maybe Mode
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
  | InternalResourceNotValue Name Ty
  | InvalidUIntWidth Int
  | UIntLiteralOutOfRange Int Integer
  | RefinementEvidenceRequired Ty
  | ExplicitTransportRequired Ty Ty
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
          , valueResultState = state { resourceContext = nextContext }
          }
    VUnit -> pureLiteral TyUnit
    VBool _ -> pureLiteral TyBool
    VUInt width literal
      | width <= 0 -> Left (InvalidUIntWidth width)
      | literal < 0 || literal >= (2 ^ width) -> Left (UIntLiteralOutOfRange width literal)
      | otherwise -> pureLiteral (TyUInt width)
    VAscribe inner annotatedTy -> do
      checked <- checkValue inner annotatedTy state
      pure checked { valueResultType = annotatedTy }
  where
    pureLiteral ty = Right ValueResult
      { valueResultType = ty
      , valueResultMode = Nothing
      , valueResultState = state
      }

checkValue :: Value -> Ty -> CheckState -> Either ValueError ValueResult
checkValue value expected state =
  case expected of
    TyRefined _ _ _ -> Left (RefinementEvidenceRequired expected)
    _ -> do
      synthesized <- synthValue value state
      let actual = valueResultType synthesized
      case compareTypes actual expected of
        DefinitionallyEqual -> Right synthesized { valueResultType = expected }
        RequiresPropositionalEquality -> Left (ExplicitTransportRequired actual expected)
        IncompatibleTypes -> Left (ValueTypeMismatch actual expected)

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

definitionallyEqualTy :: Ty -> Ty -> Bool
definitionallyEqualTy left right =
  case (left, right) of
    (TyEndpoint leftSession, TyEndpoint rightSession) ->
      definitionallyEqualSession leftSession rightSession
    (TyPendingRecv leftPending, TyPendingRecv rightPending) ->
      pendingMetadataEqual leftPending rightPending
        && definitionallyEqualSession
          (pendingContinuation leftPending)
          (pendingContinuation rightPending)
    (TyRefined leftBinder leftBase leftProp, TyRefined rightBinder rightBase rightProp) ->
      leftBinder == rightBinder
        && leftProp == rightProp
        && definitionallyEqualTy leftBase rightBase
    _ -> left == right

pendingMetadataEqual :: PendingRecvSpec -> PendingRecvSpec -> Bool
pendingMetadataEqual left right =
  pendingSourceEndpoint left == pendingSourceEndpoint right
    && pendingGrammar left == pendingGrammar right
    && pendingFrame left == pendingFrame right
    && pendingBinder left == pendingBinder right

definitionallyEqualSession :: Session -> Session -> Bool
definitionallyEqualSession = go Set.empty
  where
    go seen left right
      | left == right = True
      | Set.member (left, right) seen = True
      | otherwise =
          let seen' = Set.insert (left, right) seen
          in case (exposeSessionHead left, exposeSessionHead right) of
            (Right leftHead, Right rightHead) -> compareHeads seen' leftHead rightHead
            _ -> False

    compareHeads seen left right =
      case (left, right) of
        (Send leftBinder leftTy leftNext, Send rightBinder rightTy rightNext) ->
          leftBinder == rightBinder
            && definitionallyEqualTy leftTy rightTy
            && go seen leftNext rightNext
        (Receive leftBinder leftTy leftNext, Receive rightBinder rightTy rightNext) ->
          leftBinder == rightBinder
            && definitionallyEqualTy leftTy rightTy
            && go seen leftNext rightNext
        (Select leftBranches, Select rightBranches) -> compareBranches seen leftBranches rightBranches
        (Offer leftBranches, Offer rightBranches) -> compareBranches seen leftBranches rightBranches
        (End leftOutcome, End rightOutcome) -> leftOutcome == rightOutcome
        _ -> False

    compareBranches seen leftBranches rightBranches =
      let leftSorted = sortOn branchLabel leftBranches
          rightSorted = sortOn branchLabel rightBranches
      in length leftSorted == length rightSorted
        && and (zipWith (compareBranch seen) leftSorted rightSorted)

    compareBranch seen left right =
      branchLabel left == branchLabel right
        && comparePayload (branchPayload left) (branchPayload right)
        && go seen (branchContinuation left) (branchContinuation right)

    comparePayload Nothing Nothing = True
    comparePayload (Just (leftBinder, leftTy)) (Just (rightBinder, rightTy)) =
      leftBinder == rightBinder && definitionallyEqualTy leftTy rightTy
    comparePayload _ _ = False

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
