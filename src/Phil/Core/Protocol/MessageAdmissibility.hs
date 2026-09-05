{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Protocol.MessageAdmissibility
  ( BoundaryMessageShape (..)
  , BoundaryMessageContract (..)
  , BoundaryMessageInadmissibility (..)
  , BoundaryMessageError (..)
  , checkBoundaryMessageContract
  , intrinsicBoundaryMessageType
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Static (SemanticForm)
import Phil.Core.Syntax
  ( ProductElementType (..)
  , Ty (..)
  )
import qualified ProtocolMessageAdmissibilityKernel as Kernel

-- | Semantic shape established by the competent boundary-message checker.
-- Structural mode is deliberately absent: movability/linearity is not Message
-- competence. Aggregates are transparent for admissibility, so a forbidden
-- constituent cannot be laundered by record/product wrapping.
data BoundaryMessageShape
  = BoundaryMessageAdmittedLeaf Text
  | BoundaryMessageAggregate [BoundaryMessageShape]
  | BoundaryMessageScopedView Text
  | BoundaryMessageLiveEndpoint
  | BoundaryMessageLiveAuthority Text
  deriving (Eq, Ord, Show)

-- | Exact semantic contract carried by one protocol Message actual. The type and
-- semantic identity are repeated intentionally so a contract admitted for one
-- value cannot be attached to a different actual merely because its runtime
-- representation is convenient.
data BoundaryMessageContract = BoundaryMessageContract
  { boundaryMessageContractRevision :: Text
  , boundaryMessageContractType :: Ty
  , boundaryMessageContractSemantics :: SemanticForm
  , boundaryMessageContractShape :: BoundaryMessageShape
  }
  deriving (Eq, Ord, Show)

data BoundaryMessageInadmissibility
  = ScopedViewNotCommunicable Text
  | LiveEndpointNotCommunicable
  | LiveAuthorityNotCommunicable Text
  | InternalReceiveStateNotCommunicable
  deriving (Eq, Ord, Show)

data BoundaryMessageError
  = BoundaryMessageContractRevisionEmpty
  | BoundaryMessageContractTypeMismatch Ty Ty
  | BoundaryMessageContractSemanticsMismatch SemanticForm SemanticForm
  | BoundaryMessageInadmissible [Int] BoundaryMessageInadmissibility
  deriving (Eq, Ord, Show)

-- | Check one exact Message actual before protocol instantiation/session
-- substitution. Concrete equality and recursive path discovery remain native;
-- the exact extracted kernel owns which reflected gate wins.
checkBoundaryMessageContract
  :: Ty
  -> SemanticForm
  -> BoundaryMessageContract
  -> Either BoundaryMessageError ()
checkBoundaryMessageContract actualType actualSemantics contract =
  case Kernel.decideBoundaryMessageContractByFacts
    revisionNonempty typeMatches semanticsMatches shapeAllows hardTypeAllows of
      Kernel.BoundaryMessageContractAcceptedDecision -> Right ()
      Kernel.BoundaryMessageRevisionEmptyDecision ->
        Left BoundaryMessageContractRevisionEmpty
      Kernel.BoundaryMessageTypeMismatchDecision ->
        Left (BoundaryMessageContractTypeMismatch actualType contractType)
      Kernel.BoundaryMessageSemanticsMismatchDecision ->
        Left (BoundaryMessageContractSemanticsMismatch actualSemantics contractSemantics)
      Kernel.BoundaryMessageShapeRejectedDecision ->
        case shapeFailure of
          Just failure -> Left failure
          Nothing -> Left kernelShapeInvariantFailure
      Kernel.BoundaryMessageHardTypeRejectedDecision ->
        case hardTypeFailure of
          Just failure -> Left failure
          Nothing -> Left kernelHardTypeInvariantFailure
  where
    revisionNonempty = not (Text.null (boundaryMessageContractRevision contract))
    contractType = boundaryMessageContractType contract
    contractSemantics = boundaryMessageContractSemantics contract
    typeMatches = actualType == contractType
    semanticsMatches = actualSemantics == contractSemantics
    shapeFailure = firstForbiddenShape [] (boundaryMessageContractShape contract)
    hardTypeFailure = firstHardTypeFailure [] actualType
    shapeAllows = case shapeFailure of
      Nothing -> True
      Just _ -> False
    hardTypeAllows = case hardTypeFailure of
      Nothing -> True
      Just _ -> False

kernelShapeInvariantFailure :: BoundaryMessageError
kernelShapeInvariantFailure =
  BoundaryMessageInadmissible [] LiveEndpointNotCommunicable

kernelHardTypeInvariantFailure :: BoundaryMessageError
kernelHardTypeInvariantFailure =
  BoundaryMessageInadmissible [] InternalReceiveStateNotCommunicable

-- | Bare concrete session-message types are admitted only when the type itself
-- is sufficient to establish boundary competence. Signed fixed-width integers
-- are the same primitive immutable Message class as unsigned integers; this says
-- nothing about their physical target representation and does not erase
-- signedness from exact Ty equality.
intrinsicBoundaryMessageType :: Ty -> Bool
intrinsicBoundaryMessageType ty =
  case Kernel.decideIntrinsicBoundaryMessageByFact (intrinsicBoundaryMessageTypeFact ty) of
    Kernel.IntrinsicBoundaryMessageAcceptedDecision -> True
    Kernel.IntrinsicBoundaryMessageRequiresContractDecision -> False

intrinsicBoundaryMessageTypeFact :: Ty -> Bool
intrinsicBoundaryMessageTypeFact ty = case ty of
  TyUnit -> True
  TyBool -> True
  TyUInt _ -> True
  TySInt _ -> True
  TyProduct elements -> all (intrinsicBoundaryMessageTypeFact . productElementType) elements
  TyRefined _ inner _ -> intrinsicBoundaryMessageTypeFact inner
  _ -> False

firstForbiddenShape
  :: [Int]
  -> BoundaryMessageShape
  -> Maybe BoundaryMessageError
firstForbiddenShape path shape = case shape of
  BoundaryMessageAdmittedLeaf _ -> Nothing
  BoundaryMessageAggregate fields -> firstIndexed firstForbiddenShape path fields
  BoundaryMessageScopedView detail ->
    Just (BoundaryMessageInadmissible path (ScopedViewNotCommunicable detail))
  BoundaryMessageLiveEndpoint ->
    Just (BoundaryMessageInadmissible path LiveEndpointNotCommunicable)
  BoundaryMessageLiveAuthority authority ->
    Just (BoundaryMessageInadmissible path (LiveAuthorityNotCommunicable authority))

firstHardTypeFailure :: [Int] -> Ty -> Maybe BoundaryMessageError
firstHardTypeFailure path ty = case ty of
  TyEndpoint _ ->
    Just (BoundaryMessageInadmissible path LiveEndpointNotCommunicable)
  TyPendingRecv _ ->
    Just (BoundaryMessageInadmissible path InternalReceiveStateNotCommunicable)
  TyProduct elements ->
    firstIndexed
      (\childPath element -> firstHardTypeFailure childPath (productElementType element))
      path
      elements
  TyRefined _ inner _ -> firstHardTypeFailure path inner
  _ -> Nothing

firstIndexed
  :: ([Int] -> a -> Maybe b)
  -> [Int]
  -> [a]
  -> Maybe b
firstIndexed check path = go 0
  where
    go _ [] = Nothing
    go index (value : rest) =
      case check (path <> [index]) value of
        Just failure -> Just failure
        Nothing -> go (index + 1) rest
