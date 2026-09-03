{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Phil.Core.Generic.RequirementCategory
import Phil.Core.Static (SemanticForm (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "production category map is exact for all 13 categories" allCategoryMappingsExact
    , test "production exact handoff preserves checked shape" exactHandoffPreservesShape
    , test "production category substitution preserves diagnostic" categorySubstitutionPreservesDiagnostic
    , test "production competence substitution preserves diagnostic" competenceSubstitutionPreservesDiagnostic
    , test "production silent assumption preserves diagnostic" silentAssumptionPreservesDiagnostic
    , test "production missing handoff preserves diagnostic" missingHandoffPreservesDiagnostic
    , test "production unexpected handoff preserves diagnostic" unexpectedHandoffPreservesDiagnostic
    , test "production duplicate requirement gate remains native" duplicateRequirementGateRemainsNative
    , test "production duplicate handoff gate remains native" duplicateHandoffGateRemainsNative
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

allCategoryMappingsExact :: Either String ()
allCategoryMappingsExact =
  assert
    (map (competenceForRequirementCategory . fst) categoryPairs == map snd categoryPairs)
    "extracted category-to-competence map diverged from GEN-014"

exactHandoffPreservesShape :: Either String ()
exactHandoffPreservesShape = do
  let requirement = public "provider" GenericProviderCategory
      handoff = exactHandoff requirement
  checked <- mapLeft show $ checkGenericRequirementHandoffs [requirement] [handoff]
  result <- maybe (Left "missing checked handoff") Right
    (Map.lookup (key "provider") (checkedGenericRequirementHandoffs checked))
  assert
    ( checkedRequirementKey result == key "provider"
      && checkedRequirementCategory result == GenericProviderCategory
      && checkedRequirementSemanticForm result == genericPublicRequirementSemanticForm requirement
      && checkedRequirementCompetence result == ProviderRequirementChecker )
    "production checked handoff lost exact GEN-014 identity/category/payload/competence"

categorySubstitutionPreservesDiagnostic :: Either String ()
categorySubstitutionPreservesDiagnostic =
  let requirement = public "provider" GenericProviderCategory
      handoff = GenericRequirementHandoff
        { genericHandoffRequirementKey = key "provider"
        , genericHandoffRequirementCategory = GenericPropositionCategory
        , genericHandoffTarget = GenericHandoffToCompetence PropositionRequirementChecker
        }
  in case checkGenericRequirementHandoffs [requirement] [handoff] of
      Left (GenericRequirementCategorySubstitution actualKey expected actual) ->
        assert
          (actualKey == key "provider"
            && expected == GenericProviderCategory
            && actual == GenericPropositionCategory)
          "category-substitution diagnostic changed"
      other -> Left ("unexpected result: " <> show other)

competenceSubstitutionPreservesDiagnostic :: Either String ()
competenceSubstitutionPreservesDiagnostic =
  let requirement = public "effects" GenericEffectsCategory
      handoff = GenericRequirementHandoff
        { genericHandoffRequirementKey = key "effects"
        , genericHandoffRequirementCategory = GenericEffectsCategory
        , genericHandoffTarget = GenericHandoffToCompetence PropositionRequirementChecker
        }
  in case checkGenericRequirementHandoffs [requirement] [handoff] of
      Left (GenericRequirementCompetenceMismatch actualKey category expected actual) ->
        assert
          (actualKey == key "effects"
            && category == GenericEffectsCategory
            && expected == EffectsRequirementChecker
            && actual == PropositionRequirementChecker)
          "competence-mismatch diagnostic changed"
      other -> Left ("unexpected result: " <> show other)

silentAssumptionPreservesDiagnostic :: Either String ()
silentAssumptionPreservesDiagnostic =
  let requirement = public "environment" GenericEnvironmentCategory
      handoff = GenericRequirementHandoff
        { genericHandoffRequirementKey = key "environment"
        , genericHandoffRequirementCategory = GenericEnvironmentCategory
        , genericHandoffTarget = GenericHandoffAsAssumption "deployment guess"
        }
  in case checkGenericRequirementHandoffs [requirement] [handoff] of
      Left (GenericRequirementSilentAssumption actualKey category detail) ->
        assert
          (actualKey == key "environment"
            && category == GenericEnvironmentCategory
            && detail == "deployment guess")
          "silent-assumption diagnostic changed"
      other -> Left ("unexpected result: " <> show other)

missingHandoffPreservesDiagnostic :: Either String ()
missingHandoffPreservesDiagnostic =
  case checkGenericRequirementHandoffs [public "cost" GenericCostCategory] [] of
    Left (MissingGenericRequirementHandoff actualKey) ->
      assert (actualKey == key "cost") "missing-handoff diagnostic changed"
    other -> Left ("unexpected result: " <> show other)

unexpectedHandoffPreservesDiagnostic :: Either String ()
unexpectedHandoffPreservesDiagnostic =
  let extra = GenericRequirementHandoff
        { genericHandoffRequirementKey = key "extra"
        , genericHandoffRequirementCategory = GenericCostCategory
        , genericHandoffTarget = GenericHandoffToCompetence CostRequirementChecker
        }
  in case checkGenericRequirementHandoffs [] [extra] of
      Left (UnexpectedGenericRequirementHandoff actualKey) ->
        assert (actualKey == key "extra") "unexpected-handoff diagnostic changed"
      other -> Left ("unexpected result: " <> show other)

duplicateRequirementGateRemainsNative :: Either String ()
duplicateRequirementGateRemainsNative =
  let requirement = public "dup" GenericCostCategory
  in case checkGenericRequirementHandoffs [requirement, requirement] [] of
      Left (DuplicateGenericPublicRequirement actualKey) ->
        assert (actualKey == key "dup") "duplicate-requirement diagnostic changed"
      other -> Left ("unexpected result: " <> show other)

duplicateHandoffGateRemainsNative :: Either String ()
duplicateHandoffGateRemainsNative =
  let requirement = public "dup" GenericCostCategory
      handoff = exactHandoff requirement
  in case checkGenericRequirementHandoffs [requirement] [handoff, handoff] of
      Left (DuplicateGenericRequirementHandoff actualKey) ->
        assert (actualKey == key "dup") "duplicate-handoff diagnostic changed"
      other -> Left ("unexpected result: " <> show other)

categoryPairs :: [(GenericRequirementCategory, GenericRequirementCompetence)]
categoryPairs =
  [ (GenericStructuralCategory, StructuralRequirementChecker)
  , (GenericPropositionCategory, PropositionRequirementChecker)
  , (GenericProviderCategory, ProviderRequirementChecker)
  , (GenericCallableCategory, CallableRequirementChecker)
  , (GenericBoundaryCategory, BoundaryRequirementChecker)
  , (GenericArchitectureCategory, ArchitectureRequirementChecker)
  , (GenericEffectsCategory, EffectsRequirementChecker)
  , (GenericAuthorityCategory, AuthorityRequirementChecker)
  , (GenericBoundaryRepresentationCategory, BoundaryRepresentationRequirementChecker)
  , (GenericRepresentationCategory, RepresentationRequirementChecker)
  , (GenericPlacementCategory, PlacementRequirementChecker)
  , (GenericCostCategory, CostRequirementChecker)
  , (GenericEnvironmentCategory, EnvironmentRequirementChecker)
  ]

public :: Text -> GenericRequirementCategory -> GenericPublicRequirement
public name category = GenericPublicRequirement
  { genericPublicRequirementKey = key name
  , genericPublicRequirementCategory = category
  , genericPublicRequirementSemanticForm = SemanticRecord (Map.fromList
      [("name", SemanticAtom name), ("subject", SemanticAtom ("subject." <> name))])
  }

exactHandoff :: GenericPublicRequirement -> GenericRequirementHandoff
exactHandoff requirement = GenericRequirementHandoff
  { genericHandoffRequirementKey = genericPublicRequirementKey requirement
  , genericHandoffRequirementCategory = genericPublicRequirementCategory requirement
  , genericHandoffTarget = GenericHandoffToCompetence
      (competenceForRequirementCategory (genericPublicRequirementCategory requirement))
  }

key :: Text -> GenericRequirementKey
key = GenericRequirementKey

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
