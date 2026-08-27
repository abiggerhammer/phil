module Phil.Core.BoundaryDirection
  ( BoundaryDirection (..)
  , BoundaryUse (..)
  , BoundaryDirectionError (..)
  , checkBoundaryUse
  ) where

data BoundaryDirection
  = ReceiveOnly
  | SendOnly
  | Bidirectional
  deriving (Eq, Show)

data BoundaryUse
  = InboundUse
  | OutboundUse
  deriving (Eq, Show)

data BoundaryDirectionError
  = ReceiveOnlyCannotEncode
  | SendOnlyCannotAcceptInbound
  deriving (Eq, Show)

checkBoundaryUse :: BoundaryDirection -> BoundaryUse -> Either BoundaryDirectionError ()
checkBoundaryUse direction use = case (direction, use) of
  (ReceiveOnly, OutboundUse) -> Left ReceiveOnlyCannotEncode
  (SendOnly, InboundUse) -> Left SendOnlyCannotAcceptInbound
  _ -> Right ()
