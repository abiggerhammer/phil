{-# OPTIONS_GHC -Wno-unused-imports #-}
module ArchitectureRealizationKernel where

import qualified Prelude

data ArchitectureRealizationPlan key revision semantics =
   MkArchitectureRealizationPlan key revision semantics

planArchitectureRealization :: a1 -> a2 -> a3 -> ArchitectureRealizationPlan
                               a1 a2 a3
planArchitectureRealization instanceKey instanceRevision semantics =
  MkArchitectureRealizationPlan instanceKey instanceRevision semantics

