module Phil.Core.BoundaryDirection
  ( BoundaryDirection (..)
  , BoundaryUse (..)
  , BoundaryDirectionError (..)
  , checkBoundaryUse
  ) where

import qualified BoundaryRepresentationKernel as Kernel

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
checkBoundaryUse direction use =
  case Kernel.decideBoundaryUse
      (toKernelDirection direction)
      (toKernelUse use) of
    Kernel.BoundaryUseAccepted -> Right ()
    Kernel.BoundaryUseRejected Kernel.ReceiveOnlyCannotEncode ->
      Left ReceiveOnlyCannotEncode
    Kernel.BoundaryUseRejected Kernel.SendOnlyCannotAcceptInbound ->
      Left SendOnlyCannotAcceptInbound

toKernelDirection :: BoundaryDirection -> Kernel.BoundaryDirection
toKernelDirection direction = case direction of
  ReceiveOnly -> Kernel.ReceiveOnly
  SendOnly -> Kernel.SendOnly
  Bidirectional -> Kernel.Bidirectional

toKernelUse :: BoundaryUse -> Kernel.BoundaryUse
toKernelUse use = case use of
  InboundUse -> Kernel.InboundUse
  OutboundUse -> Kernel.OutboundUse
