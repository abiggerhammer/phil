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
    [ test "GEN-014 all public requirement categories retain exact competence" allCategoriesAccept
    , test "GEN-014 category substitution rejects" categorySubstitutionRejects
    , test "GEN-014 competence substitution rejects" competenceSubstitutionRejects
    , test "GEN-014 silent assumption conversion rejects" silentAssumptionRejects
    , test "GEN-014 missing category handoff rejects" missingHandoffRejects
    , test "GEN-014 unexpected category handoff rejects" unexpectedHandoffRejects
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

allCategoriesAccept :: Either String ()
allCategoriesAccept = do
  checked <- mapLeft show $ checkGenericRequirementHandoffs requirements handoffs
  let results = checkedGenericRequirementHandoffs checked
  assert (Map.keysSet results == Map.keysSet expectedByKey)
    "checked requirement interface changed exact requirement-key domain"
  mapM_ (checkOne results) requirements
  where
    expectedByKey = Map.fromList
      [ (genericPublicRequirementKey requirement, requirement)
      | requirement <- requirements
      ]

    checkOne results requirement = do
      let requirementKey = genericPublicRequirementKey requirement
          category = genericPublicRequirementCategory requirement
          semanticForm = genericPublicRequirementSemanticForm requirement
      checked <- maybe (Left "missing checked requirement") Right
        (Map.lookup requirementKey results)
      assert (checkedRequirementKey checked == requirementKey)
        "checked handoff changed requirement identity"
      assert (checkedRequirementCategory checked == category)
        "checked handoff changed requirement category"
      assert (checkedRequirementSemanticForm checked == semanticForm)
        "checked handoff changed semantic requirement payload"
      assert
        (checkedRequirementCompetence checked == competenceForRequirementCategory category)
        "checked handoff selected the wrong competent checker"

categorySubstitutionRejects :: Either String ()
categorySubstitutionRejects =
  let requirement = public "provider" GenericProviderCategory
      handoff = GenericRequirementHandoff
        { genericHandoffRequirementKey = key "provider"
        , genericHandoffRequirementCategory = GenericPropositionCategory
        , genericHandoffTarget = GenericHandoffToCompetence PropositionRequirementChecker
        }
  in case checkGenericRequirementHandoffs [requirement] [handoff] of
      Left (GenericRequirementCategorySubstitution actualKey expected actual) ->
        assert
          ( actualKey == key "provider"
            && expected == GenericProviderCategory
            && actual == GenericPropositionCategory )
          "category-substitution rejection lost exact identity/categories"
      other -> Left ("provider requirement collapsed into proposition category: " <> show other)

competenceSubstitutionRejects :: Either String ()
competenceSubstitutionRejects =
  let requirement = public "effects" GenericEffectsCategory
      handoff = GenericRequirementHandoff
        { genericHandoffRequirementKey = key "effects"
        , genericHandoffRequirementCategory = GenericEffectsCategory
        , genericHandoffTarget = GenericHandoffToCompetence PropositionRequirementChecker
        }
  in case checkGenericRequirementHandoffs [requirement] [handoff] of
      Left (GenericRequirementCompetenceMismatch actualKey category expected actual) ->
        assert
          ( actualKey == key "effects"
            && category == GenericEffectsCategory
            && expected == EffectsRequirementChecker
            && actual == PropositionRequirementChecker )
          "competence-substitution rejection lost exact routing information"
      other -> Left ("effects requirement was routed through wrong checker: " <> show other)

silentAssumptionRejects :: Either String ()
silentAssumptionRejects =
  let requirement = public "environment" GenericEnvironmentCategory
      handoff = GenericRequirementHandoff
        { genericHandoffRequirementKey = key "environment"
        , genericHandoffRequirementCategory = GenericEnvironmentCategory
        , genericHandoffTarget = GenericHandoffAsAssumption "probably true on deployment"
        }
  in case checkGenericRequirementHandoffs [requirement] [handoff] of
      Left (GenericRequirementSilentAssumption actualKey category detail) ->
        assert
          ( actualKey == key "environment"
            && category == GenericEnvironmentCategory
            && detail == "probably true on deployment" )
          "silent-assumption rejection lost requirement identity/detail"
      other -> Left ("generic requirement silently became an assumption: " <> show other)

missingHandoffRejects :: Either String ()
missingHandoffRejects =
  case checkGenericRequirementHandoffs
      [public "cost" GenericCostCategory]
      [] of
    Left (MissingGenericRequirementHandoff actualKey) ->
      assert (actualKey == key "cost") "missing-handoff diagnostic named wrong requirement"
    other -> Left ("missing requirement handoff was accepted: " <> show other)

unexpectedHandoffRejects :: Either String ()
unexpectedHandoffRejects =
  let extra = GenericRequirementHandoff
        { genericHandoffRequirementKey = key "extra"
        , genericHandoffRequirementCategory = GenericCostCategory
        , genericHandoffTarget = GenericHandoffToCompetence CostRequirementChecker
        }
  in case checkGenericRequirementHandoffs [] [extra] of
      Left (UnexpectedGenericRequirementHandoff actualKey) ->
        assert (actualKey == key "extra") "unexpected-handoff diagnostic named wrong requirement"
      other -> Left ("unexpected generic requirement handoff was accepted: " <> show other)

requirements :: [GenericPublicRequirement]
requirements =
  [ public "structural" GenericStructuralCategory
  , public "proposition" GenericPropositionCategory
  , public "provider" GenericProviderCategory
  , public "callable" GenericCallableCategory
  , public "boundary" GenericBoundaryCategory
  , public "architecture" GenericArchitectureCategory
  , public "effects" GenericEffectsCategory
  , public "authority" GenericAuthorityCategory
  , public "boundary-representation" GenericBoundaryRepresentationCategory
  , public "representation" GenericRepresentationCategory
  , public "placement" GenericPlacementCategory
  , public "cost" GenericCostCategory
  , public "environment" GenericEnvironmentCategory
  ]

handoffs :: [GenericRequirementHandoff]
handoffs =
  [ GenericRequirementHandoff
      { genericHandoffRequirementKey = genericPublicRequirementKey requirement
      , genericHandoffRequirementCategory = genericPublicRequirementCategory requirement
      , genericHandoffTarget = GenericHandoffToCompetence
          (competenceForRequirementCategory (genericPublicRequirementCategory requirement))
      }
  | requirement <- requirements
  ]

public :: Text -> GenericRequirementCategory -> GenericPublicRequirement
public name category = GenericPublicRequirement
  { genericPublicRequirementKey = key name
  , genericPublicRequirementCategory = category
  , genericPublicRequirementSemanticForm = SemanticRecord (Map.fromList
      [ ("name", SemanticAtom name)
      , ("subject", SemanticAtom ("subject." <> name))
      ])
  }

key :: Text -> GenericRequirementKey
key = GenericRequirementKey

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
