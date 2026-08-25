{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Set as Set
import Phil.Core.Generic
import Phil.Core.Static (InterfaceRevision (..))
import Phil.Core.Syntax (Mode (..), Proposition (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "GEN-007 exact provider contract accepts" exactProviderAccepts
    , test "GEN-007 nominal provider superset does not satisfy exact contract" nominalProviderSupersetRejects
    , test "GEN-007 explicit checked provider refinement accepts" checkedProviderRefinementAccepts
    , test "GEN-007 refinement must target exact required interface" wrongProviderRefinementRejects
    , test "GEN-008 provider operation availability does not discharge law" providerDoesNotDischargeLaw
    , test "GEN-008 exact proposition evidence discharges law" exactPropositionEvidenceAccepts
    , test "GEN-008 wrong proposition evidence rejects" wrongPropositionEvidenceRejects
    , test "GEN-012 missing requirement never becomes assumption" missingRequirementRejects
    , test "GEN-012 assumption disposition requires explicit policy" assumptionRequiresPolicy
    , test "GEN-012 explicit permitted assumption is recorded" explicitPermittedAssumptionAccepts
    , test "GEN-012 export disposition requires explicit policy" exportRequiresPolicy
    , test "structural published requirement discharges through exact actual mode" structuralRequirementDischarge
    , test "structural requirement still rejects insufficient actual mode" structuralRequirementRejects
    , test "duplicate requirement dispositions reject" duplicateDispositionRejects
    , test "disposition for unexposed requirement rejects" unexpectedDispositionRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

exactProviderAccepts :: Either String ()
exactProviderAccepts = do
  _ <- mapLeft show $ checkGenericInstantiation
    strictGenericInstantiationPolicy
    (Set.singleton providerRequirement)
    [(providerRequirement, GenericSatisfiedByExactProvider requiredProviderInterface)]
  pure ()

nominalProviderSupersetRejects :: Either String ()
nominalProviderSupersetRejects =
  case checkGenericInstantiation
      strictGenericInstantiationPolicy
      (Set.singleton providerRequirement)
      [(providerRequirement, GenericSatisfiedByExactProvider richerNominalProviderInterface)] of
    Left (GenericProviderInterfaceMismatch key required actual) ->
      assert
        ( key == providerParameter
          && required == requiredProviderInterface
          && actual == richerNominalProviderInterface )
        "provider mismatch diagnostic did not preserve exact interfaces"
    other -> Left ("nominal/superset provider was not rejected exactly: " <> show other)

checkedProviderRefinementAccepts :: Either String ()
checkedProviderRefinementAccepts = do
  _ <- mapLeft show $ checkGenericInstantiation
    strictGenericInstantiationPolicy
    (Set.singleton providerRequirement)
    [ ( providerRequirement
      , GenericSatisfiedByCheckedProviderRefinement CheckedProviderRefinement
          { checkedProviderRefinementActual = richerNominalProviderInterface
          , checkedProviderRefinementRequired = requiredProviderInterface
          , checkedProviderRefinementWitness = "provider-refinement-001"
          }
      )
    ]
  pure ()

wrongProviderRefinementRejects :: Either String ()
wrongProviderRefinementRejects =
  case checkGenericInstantiation
      strictGenericInstantiationPolicy
      (Set.singleton providerRequirement)
      [ ( providerRequirement
        , GenericSatisfiedByCheckedProviderRefinement CheckedProviderRefinement
            { checkedProviderRefinementActual = richerNominalProviderInterface
            , checkedProviderRefinementRequired = unrelatedProviderInterface
            , checkedProviderRefinementWitness = "wrong-target"
            }
        )
      ] of
    Left (GenericProviderRefinementMismatch key required actual refinementTarget) ->
      assert
        ( key == providerParameter
          && required == requiredProviderInterface
          && actual == richerNominalProviderInterface
          && refinementTarget == unrelatedProviderInterface )
        "wrong provider refinement mismatch reported"
    other -> Left ("refinement to wrong interface was not rejected: " <> show other)

providerDoesNotDischargeLaw :: Either String ()
providerDoesNotDischargeLaw =
  case checkGenericInstantiation
      strictGenericInstantiationPolicy
      providerAndLawRequirements
      [(providerRequirement, GenericSatisfiedByExactProvider requiredProviderInterface)] of
    Left (MissingGenericRequirementDisposition missing) ->
      assert (missing == lawRequirement)
        "provider binding left the wrong requirement unresolved"
    other -> Left ("provider operation availability discharged a law: " <> show other)

exactPropositionEvidenceAccepts :: Either String ()
exactPropositionEvidenceAccepts = do
  _ <- mapLeft show $ checkGenericInstantiation
    strictGenericInstantiationPolicy
    providerAndLawRequirements
    [ (providerRequirement, GenericSatisfiedByExactProvider requiredProviderInterface)
    , ( lawRequirement
      , GenericSatisfiedByEvidence GenericEvidence
          { genericEvidenceProposition = orderingLaw
          , genericEvidenceIdentity = "proof.ordering-law.001"
          }
      )
    ]
  pure ()

wrongPropositionEvidenceRejects :: Either String ()
wrongPropositionEvidenceRejects =
  case checkGenericInstantiation
      strictGenericInstantiationPolicy
      (Set.singleton lawRequirement)
      [ ( lawRequirement
        , GenericSatisfiedByEvidence GenericEvidence
            { genericEvidenceProposition = otherLaw
            , genericEvidenceIdentity = "proof.other-law.001"
            }
        )
      ] of
    Left (GenericPropositionEvidenceMismatch expected actual) ->
      assert (expected == orderingLaw && actual == otherLaw)
        "wrong proposition mismatch reported"
    other -> Left ("evidence for another proposition was accepted: " <> show other)

missingRequirementRejects :: Either String ()
missingRequirementRejects =
  case checkGenericInstantiation
      strictGenericInstantiationPolicy
      (Set.singleton lawRequirement)
      [] of
    Left (MissingGenericRequirementDisposition missing) ->
      assert (missing == lawRequirement)
        "missing requirement identity was not preserved"
    other -> Left ("missing requirement was silently disposed: " <> show other)

assumptionRequiresPolicy :: Either String ()
assumptionRequiresPolicy =
  case checkGenericInstantiation
      strictGenericInstantiationPolicy
      (Set.singleton lawRequirement)
      [(lawRequirement, GenericAssumptionDependent "deployment-assumption-A")] of
    Left (GenericAssumptionNotPermitted requirement) ->
      assert (requirement == lawRequirement)
        "assumption rejection named the wrong requirement"
    other -> Left ("strict policy accepted an assumption: " <> show other)

explicitPermittedAssumptionAccepts :: Either String ()
explicitPermittedAssumptionAccepts = do
  record <- mapLeft show $ checkGenericInstantiation
    assumptionPolicy
    (Set.singleton lawRequirement)
    [(lawRequirement, GenericAssumptionDependent "deployment-assumption-A")]
  assert
    (genericInstantiationDispositions record
      == singletonDisposition lawRequirement (GenericAssumptionDependent "deployment-assumption-A"))
    "explicit assumption disposition was not retained exactly"

exportRequiresPolicy :: Either String ()
exportRequiresPolicy =
  case checkGenericInstantiation
      strictGenericInstantiationPolicy
      (Set.singleton lawRequirement)
      [(lawRequirement, GenericExported "outer-architecture") ] of
    Left (GenericExportNotPermitted requirement) ->
      assert (requirement == lawRequirement)
        "export rejection named the wrong requirement"
    other -> Left ("strict policy accepted an export: " <> show other)

structuralRequirementDischarge :: Either String ()
structuralRequirementDischarge = do
  interface <- mapLeft show $ checkGenericStructuralInterface
    [valueParameter]
    [DiscardGenericValue valueParameter]
    Nothing
  let requirements = publishedStructuralRequirements interface
  assert
    (requirements == Set.singleton structuralWeakeningRequirement)
    "published structural interface did not lift to exact generic requirement"
  _ <- mapLeft show $ checkGenericInstantiation
    strictGenericInstantiationPolicy
    requirements
    [(structuralWeakeningRequirement, GenericSatisfiedByStructuralMode Affine)]
  pure ()

structuralRequirementRejects :: Either String ()
structuralRequirementRejects =
  case checkGenericInstantiation
      strictGenericInstantiationPolicy
      (Set.singleton structuralWeakeningRequirement)
      [(structuralWeakeningRequirement, GenericSatisfiedByStructuralMode Linear)] of
    Left (GenericStructuralInstantiationError (MissingStructuralPermission key permission mode)) ->
      assert
        ( key == valueParameter
          && permission == WeakeningPermission
          && mode == Linear )
        "structural instantiation failure lost exact requirement"
    other -> Left ("linear actual satisfied weakening: " <> show other)

duplicateDispositionRejects :: Either String ()
duplicateDispositionRejects =
  case checkGenericInstantiation
      strictGenericInstantiationPolicy
      (Set.singleton providerRequirement)
      [ (providerRequirement, GenericSatisfiedByExactProvider requiredProviderInterface)
      , (providerRequirement, GenericSatisfiedByExactProvider requiredProviderInterface)
      ] of
    Left (DuplicateGenericRequirementDisposition requirement) ->
      assert (requirement == providerRequirement)
        "duplicate disposition reported wrong requirement"
    other -> Left ("duplicate disposition did not reject: " <> show other)

unexpectedDispositionRejects :: Either String ()
unexpectedDispositionRejects =
  case checkGenericInstantiation
      strictGenericInstantiationPolicy
      Set.empty
      [(providerRequirement, GenericSatisfiedByExactProvider requiredProviderInterface)] of
    Left (UnexpectedGenericRequirementDisposition requirement) ->
      assert (requirement == providerRequirement)
        "unexpected disposition reported wrong requirement"
    other -> Left ("disposition for unexposed requirement did not reject: " <> show other)

providerParameter :: GenericStaticParameterKey
providerParameter = GenericStaticParameterKey "provider.compare"

valueParameter :: GenericValueParameterKey
valueParameter = GenericValueParameterKey "T"

requiredProviderInterface :: InterfaceRevision
requiredProviderInterface = InterfaceRevision "provider.compare.v1"

richerNominalProviderInterface :: InterfaceRevision
richerNominalProviderInterface = InterfaceRevision "provider.compare-plus-hash.v1"

unrelatedProviderInterface :: InterfaceRevision
unrelatedProviderInterface = InterfaceRevision "provider.storage.v1"

orderingLaw :: Proposition
orderingLaw = Atom "StrictWeakOrdering" []

otherLaw :: Proposition
otherLaw = Atom "HashStable" []

providerRequirement :: GenericRequirement
providerRequirement = GenericProviderContractRequirement
  providerParameter
  requiredProviderInterface

lawRequirement :: GenericRequirement
lawRequirement = GenericPropositionRequirement orderingLaw

structuralWeakeningRequirement :: GenericRequirement
structuralWeakeningRequirement = GenericStructuralRequirement
  valueParameter
  WeakeningPermission

providerAndLawRequirements :: Set.Set GenericRequirement
providerAndLawRequirements = Set.fromList [providerRequirement, lawRequirement]

assumptionPolicy :: GenericInstantiationPolicy
assumptionPolicy = strictGenericInstantiationPolicy
  { genericPolicyAllowsAssumptions = True
  }

singletonDisposition
  :: GenericRequirement
  -> GenericRequirementDisposition
  -> Data.Map.Strict.Map GenericRequirement GenericRequirementDisposition
singletonDisposition = Data.Map.Strict.singleton

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
