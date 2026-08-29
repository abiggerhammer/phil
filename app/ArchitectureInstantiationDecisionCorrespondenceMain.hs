module Main (main) where

import qualified ArchitectureInstantiationKernel as Kernel

main :: IO ()
main = mapM_ (uncurry check)
  [ ("child fresh accepts", childAccepted (Kernel.decideChildSlotByFacts True))
  , ("child duplicate rejects", childDuplicate (Kernel.decideChildSlotByFacts False))
  , ("implicit requirement remains unresolved",
      requirementUnresolved
        (Kernel.decideArchitectureRequirementByFacts False False True True))
  , ("explicit nonbinding disposition accepts",
      requirementAccepted
        (Kernel.decideArchitectureRequirementByFacts True False False False))
  , ("bound requirement missing target rejects",
      requirementMissingTarget
        (Kernel.decideArchitectureRequirementByFacts True True False True))
  , ("bound requirement interface mismatch rejects",
      requirementInterfaceMismatch
        (Kernel.decideArchitectureRequirementByFacts True True True False))
  , ("bound requirement exact target/interface accepts",
      requirementAccepted
        (Kernel.decideArchitectureRequirementByFacts True True True True))
  , ("root implicit requirement remains unresolved",
      requirementUnresolved
        (Kernel.decideRootRequirementByFacts False False True True))
  , ("missing explicit reference target rejects",
      referenceUnknown (Kernel.decideArchitectureReferenceByFacts False))
  , ("existing explicit reference target accepts",
      referenceAccepted (Kernel.decideArchitectureReferenceByFacts True))
  ]

check :: String -> Bool -> IO ()
check label ok
  | ok = putStrLn ("PASS: " <> label)
  | otherwise = error ("FAIL: " <> label)

childAccepted :: Kernel.ChildSlotDecision -> Bool
childAccepted decision = case decision of
  Kernel.ChildSlotAccepted -> True
  Kernel.ChildSlotDuplicate -> False

childDuplicate :: Kernel.ChildSlotDecision -> Bool
childDuplicate decision = case decision of
  Kernel.ChildSlotAccepted -> False
  Kernel.ChildSlotDuplicate -> True

requirementAccepted :: Kernel.ArchitectureRequirementDecision -> Bool
requirementAccepted decision = case decision of
  Kernel.ArchitectureRequirementAccepted -> True
  _ -> False

requirementUnresolved :: Kernel.ArchitectureRequirementDecision -> Bool
requirementUnresolved decision = case decision of
  Kernel.ArchitectureRequirementUnresolved -> True
  _ -> False

requirementMissingTarget :: Kernel.ArchitectureRequirementDecision -> Bool
requirementMissingTarget decision = case decision of
  Kernel.ArchitectureRequirementMissingBindingTarget -> True
  _ -> False

requirementInterfaceMismatch :: Kernel.ArchitectureRequirementDecision -> Bool
requirementInterfaceMismatch decision = case decision of
  Kernel.ArchitectureRequirementInterfaceMismatch -> True
  _ -> False

referenceAccepted :: Kernel.ArchitectureReferenceDecision -> Bool
referenceAccepted decision = case decision of
  Kernel.ArchitectureReferenceAccepted -> True
  Kernel.ArchitectureReferenceUnknownTarget -> False

referenceUnknown :: Kernel.ArchitectureReferenceDecision -> Bool
referenceUnknown decision = case decision of
  Kernel.ArchitectureReferenceAccepted -> False
  Kernel.ArchitectureReferenceUnknownTarget -> True
