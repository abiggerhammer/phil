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
-- substitution. This is deliberately independent of ownership-transfer rules.
checkBoundaryMessageContract
  :: Ty
  -> SemanticForm
  -> BoundaryMessageContract
  -> Either BoundaryMessageError ()
checkBoundaryMessageContract actualType actualSemantics contract = do
  if Text.null (boundaryMessageContractRevision contract)
    then Left BoundaryMessageContractRevisionEmpty
    else Right ()
  requireEqual BoundaryMessageContractTypeMismatch
    actualType
    (boundaryMessageContractType contract)
  requireEqual BoundaryMessageContractSemanticsMismatch
    actualSemantics
    (boundaryMessageContractSemantics contract)
  case firstForbiddenShape [] (boundaryMessageContractShape contract) of
    Just failure -> Left failure
    Nothing -> Right ()
  case firstHardTypeFailure [] actualType of
    Just failure -> Left failure
    Nothing -> Right ()

-- | Bare concrete session-message types are admitted only when the type itself
-- is sufficient to establish boundary competence. Ownership-sensitive or
-- authority-sensitive types must use a parameterized Message actual carrying an
-- explicit BoundaryMessageContract instead of relying on structural movement.
intrinsicBoundaryMessageType :: Ty -> Bool
intrinsicBoundaryMessageType ty = case ty of
  TyUnit -> True
  TyBool -> True
  TyUInt _ -> True
  TyProduct elements -> all (intrinsicBoundaryMessageType . productElementType) elements
  TyRefined _ inner _ -> intrinsicBoundaryMessageType inner
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

-- Endpoint and pending-receive state have enough structure in Core to reject
-- even if a malformed external classifier calls them an admitted leaf. Loans
-- and authority-bearing opaque occurrences require the semantic shape above.
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

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual makeError expected actual
  | expected == actual = Right ()
  | otherwise = Left (makeError expected actual)
