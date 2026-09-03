module Main (main) where

import qualified GenericRequirementCategoryKernel as Kernel
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ competence "structural" Kernel.GenericStructuralCategory isStructural
    , competence "proposition" Kernel.GenericPropositionCategory isProposition
    , competence "provider" Kernel.GenericProviderCategory isProvider
    , competence "callable" Kernel.GenericCallableCategory isCallable
    , competence "boundary" Kernel.GenericBoundaryCategory isBoundary
    , competence "architecture" Kernel.GenericArchitectureCategory isArchitecture
    , competence "effects" Kernel.GenericEffectsCategory isEffects
    , competence "authority" Kernel.GenericAuthorityCategory isAuthority
    , competence "boundary representation" Kernel.GenericBoundaryRepresentationCategory isBoundaryRepresentation
    , competence "representation" Kernel.GenericRepresentationCategory isRepresentation
    , competence "placement" Kernel.GenericPlacementCategory isPlacement
    , competence "cost" Kernel.GenericCostCategory isCost
    , competence "environment" Kernel.GenericEnvironmentCategory isEnvironment
    , handoff "exact handoff accepts" [True, True, True, True, True, True, True] isHandoffAccepted
    , handoff "key mismatch rejects first" [False, True, True, True, True, True, True] isHandoffKey
    , handoff "category mismatch rejects" [True, False, True, True, True, True, True] isHandoffCategory
    , handoff "target mismatch rejects" [True, True, False, True, True, True, True] isHandoffTarget
    , handoff "checked key mismatch rejects" [True, True, True, False, True, True, True] isCheckedKey
    , handoff "checked category mismatch rejects" [True, True, True, True, False, True, True] isCheckedCategory
    , handoff "checked semantic form mismatch rejects" [True, True, True, True, True, False, True] isCheckedSemanticForm
    , handoff "checked competence mismatch rejects" [True, True, True, True, True, True, False] isCheckedCompetence
    , domain "exact interface domains accept" True True isDomainAccepted
    , domain "handoff-domain mismatch rejects first" False False isHandoffDomain
    , domain "checked-domain mismatch rejects" True False isCheckedDomain
    ]
  if and results then pure () else exitFailure

competence
  :: String
  -> Kernel.GenericRequirementCategory
  -> (Kernel.GenericRequirementCompetence -> Bool)
  -> IO Bool
competence label category predicate =
  expect ("category maps to exact competence: " <> label)
    (predicate (Kernel.competenceForRequirementCategory category))

handoff
  :: String
  -> [Bool]
  -> (Kernel.RequirementHandoffDecision -> Bool)
  -> IO Bool
handoff label facts predicate = case facts of
  [a,b,c,d,e,f,g] -> expect label
    (predicate (Kernel.decideRequirementHandoffByFacts a b c d e f g))
  _ -> pure False

domain
  :: String
  -> Bool
  -> Bool
  -> (Kernel.RequirementInterfaceDomainDecision -> Bool)
  -> IO Bool
domain label handoffExact checkedExact predicate =
  expect label
    (predicate (Kernel.decideRequirementInterfaceDomainByFacts handoffExact checkedExact))

expect :: String -> Bool -> IO Bool
expect label ok
  | ok = putStrLn ("PASS: " <> label) >> pure True
  | otherwise = putStrLn ("FAIL: " <> label) >> pure False

isStructural, isProposition, isProvider, isCallable, isBoundary,
  isArchitecture, isEffects, isAuthority, isBoundaryRepresentation,
  isRepresentation, isPlacement, isCost, isEnvironment
  :: Kernel.GenericRequirementCompetence -> Bool
isStructural value = case value of Kernel.StructuralRequirementChecker -> True; _ -> False
isProposition value = case value of Kernel.PropositionRequirementChecker -> True; _ -> False
isProvider value = case value of Kernel.ProviderRequirementChecker -> True; _ -> False
isCallable value = case value of Kernel.CallableRequirementChecker -> True; _ -> False
isBoundary value = case value of Kernel.BoundaryRequirementChecker -> True; _ -> False
isArchitecture value = case value of Kernel.ArchitectureRequirementChecker -> True; _ -> False
isEffects value = case value of Kernel.EffectsRequirementChecker -> True; _ -> False
isAuthority value = case value of Kernel.AuthorityRequirementChecker -> True; _ -> False
isBoundaryRepresentation value = case value of Kernel.BoundaryRepresentationRequirementChecker -> True; _ -> False
isRepresentation value = case value of Kernel.RepresentationRequirementChecker -> True; _ -> False
isPlacement value = case value of Kernel.PlacementRequirementChecker -> True; _ -> False
isCost value = case value of Kernel.CostRequirementChecker -> True; _ -> False
isEnvironment value = case value of Kernel.EnvironmentRequirementChecker -> True; _ -> False

isHandoffKey, isHandoffCategory, isHandoffTarget, isCheckedKey,
  isCheckedCategory, isCheckedSemanticForm, isCheckedCompetence,
  isHandoffAccepted :: Kernel.RequirementHandoffDecision -> Bool
isHandoffKey value = case value of Kernel.RequirementHandoffKeyDecision -> True; _ -> False
isHandoffCategory value = case value of Kernel.RequirementHandoffCategoryDecision -> True; _ -> False
isHandoffTarget value = case value of Kernel.RequirementHandoffTargetDecision -> True; _ -> False
isCheckedKey value = case value of Kernel.RequirementCheckedKeyDecision -> True; _ -> False
isCheckedCategory value = case value of Kernel.RequirementCheckedCategoryDecision -> True; _ -> False
isCheckedSemanticForm value = case value of Kernel.RequirementCheckedSemanticFormDecision -> True; _ -> False
isCheckedCompetence value = case value of Kernel.RequirementCheckedCompetenceDecision -> True; _ -> False
isHandoffAccepted value = case value of Kernel.RequirementHandoffAcceptedDecision -> True; _ -> False

isHandoffDomain, isCheckedDomain, isDomainAccepted
  :: Kernel.RequirementInterfaceDomainDecision -> Bool
isHandoffDomain value = case value of Kernel.RequirementInterfaceHandoffDomainDecision -> True; _ -> False
isCheckedDomain value = case value of Kernel.RequirementInterfaceCheckedDomainDecision -> True; _ -> False
isDomainAccepted value = case value of Kernel.RequirementInterfaceDomainAcceptedDecision -> True; _ -> False
