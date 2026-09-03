module Phil.Core.DataProductKernelBridge
  ( KernelProductElimination (..)
  , classifyProductElimination
  , productRestorationAccepted
  ) where

import qualified DataProductKernel as Kernel

data KernelProductElimination
  = KernelProductEliminationAccepted
  | KernelProductEliminationArity
  | KernelProductEliminationDuplicateSuccessor
  deriving (Eq, Show)

classifyProductElimination
  :: Bool
  -> Bool
  -> KernelProductElimination
classifyProductElimination exactArity successorsDistinct =
  case Kernel.decideProductEliminationByFacts exactArity successorsDistinct of
    Kernel.ProductEliminationAcceptedDecision ->
      KernelProductEliminationAccepted
    Kernel.ProductEliminationArityDecision ->
      KernelProductEliminationArity
    Kernel.ProductEliminationDuplicateSuccessorDecision ->
      KernelProductEliminationDuplicateSuccessor

productRestorationAccepted :: Bool -> Bool -> Bool
productRestorationAccepted ownerObligationSatisfied successorsInstalledExact =
  case Kernel.decideProductRestorationByFacts
      ownerObligationSatisfied
      successorsInstalledExact of
    Kernel.ProductRestorationAcceptedDecision -> True
    Kernel.ProductRestorationOwnerDecision -> False
    Kernel.ProductRestorationExactnessDecision -> False
