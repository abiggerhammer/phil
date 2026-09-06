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
import Phil.Core.FloatArithmetic (floatTypeFromCoreType)
import Phil.Core.SIntArithmetic (sIntTypeFromCoreType)
import Phil.Core.UnicodeChar (unicodeCharTypeFromCoreType)
import Phil.Core.UnicodeString (unicodeStringTypeFromCoreType)
import Phil.Core.Static (SemanticForm)
import Phil.Core.Syntax
  ( ProductElementType (..)
  , Ty (..)
  )
import qualified ProtocolMessageAdmissibilityKernel as Kernel

data BoundaryMessageShape
  = BoundaryMessageAdmittedLeaf Text
  | BoundaryMessageAggregate [BoundaryMessageShape]
  | BoundaryMessageScopedView Text
  | BoundaryMessageLiveEndpoint
  | BoundaryMessageLiveAuthority Text
  deriving (Eq, Ord, Show)

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

intrinsicBoundaryMessageType :: Ty -> Bool
intrinsicBoundaryMessageType ty =
  case Kernel.decideIntrinsicBoundaryMessageByFact (intrinsicBoundaryMessageTypeFact ty) of
    Kernel.IntrinsicBoundaryMessageAcceptedDecision -> True
    Kernel.IntrinsicBoundaryMessageRequiresContractDecision -> False

-- | EXEC-016 signed integers use an exact semantic Ty identity recognized only
-- by their checked smart recognizer. They are primitive immutable Message values
-- without implying that the Phase-0 backend ScalarType already realizes them.
intrinsicBoundaryMessageTypeFact :: Ty -> Bool
intrinsicBoundaryMessageTypeFact ty
  | unicodeCharTypeFromCoreType ty = True
  | unicodeStringTypeFromCoreType ty = True
  | Just _ <- floatTypeFromCoreType ty = True
  | Just _ <- sIntTypeFromCoreType ty = True
  | otherwise = case ty of
      TyUnit -> True
      TyBool -> True
      TyUInt _ -> True
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
