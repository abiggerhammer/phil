module Phil.Assurance.EvidenceAuthorityKernelBridge
  ( artifactAuthorityKernelAccepts
  , runtimeAuthorityKernelAccepts
  ) where

import qualified AssuranceEvidenceAuthorityKernel as Kernel

artifactAuthorityKernelAccepts :: Bool -> Bool -> Bool -> Bool
artifactAuthorityKernelAccepts declared identityMatches digestMatches =
  case Kernel.decideArtifactAuthorityByFacts declared identityMatches digestMatches of
    Kernel.GateAccepted -> True
    Kernel.GateRejected -> False

runtimeAuthorityKernelAccepts :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool
runtimeAuthorityKernelAccepts mechanismPresent mechanismComplete residuePresent costReferencePresent costReferenceKnown =
  case Kernel.decideRuntimeAuthorityByFacts
    mechanismPresent
    mechanismComplete
    residuePresent
    costReferencePresent
    costReferenceKnown of
      Kernel.GateAccepted -> True
      Kernel.GateRejected -> False
