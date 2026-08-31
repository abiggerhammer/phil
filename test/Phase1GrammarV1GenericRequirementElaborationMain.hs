{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Generic.RequirementCategory
  ( GenericRequirementCategory (..)
  , GenericRequirementCompetence (..)
  )
import Phil.Surface.GrammarV1.Elaborate
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = case genericRequirementRouting of
  Right () -> putStrLn "PASS: SURF-008 Grammar-v1 generic requirements route to exact semantic categories"
  Left detail -> putStrLn ("FAIL: SURF-008 generic requirement elaboration -- " <> detail) >> exitFailure

genericRequirementRouting :: Either String ()
genericRequirementRouting = do
  sourceFile <- mapLeft show $ parseGrammarV1StructuralSource "surf008-generic-routing" source
  requirements <- case grammarV1TopLevelDecls sourceFile of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1RecordDeclaration recordDecl ->
        Right (map locatedValue (grammarV1RecordRequirements recordDecl))
      other -> Left ("expected record declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))
  let actualCategories = map grammarV1GenericRequirementCategory requirements
      actualCompetences = map grammarV1GenericRequirementCompetence requirements
  assert (actualCategories == expectedCategories)
    ("category routing changed: " <> show actualCategories)
  assert (actualCompetences == expectedCompetences)
    ("competence routing changed: " <> show actualCompetences)
  where
    source = Text.unlines
      [ "record Routed[T : Type] requires {"
      , "  structural T : duplicate;"
      , "  proposition true;"
      , "  provider P : ProviderContract;"
      , "  callable F : CallableContract;"
      , "  boundary B : BoundaryContract;"
      , "  architecture A : ArchitectureContract;"
      , "  effects E within {IO};"
      , "  authority Capability;"
      , "  boundary representation WireRep;"
      , "  representation true;"
      , "  placement true;"
      , "  cost true;"
      , "  environment true;"
      , "} {"
      , "  value : T"
      , "}"
      ]

expectedCategories :: [GenericRequirementCategory]
expectedCategories =
  [ GenericStructuralCategory
  , GenericPropositionCategory
  , GenericProviderCategory
  , GenericCallableCategory
  , GenericBoundaryCategory
  , GenericArchitectureCategory
  , GenericEffectsCategory
  , GenericAuthorityCategory
  , GenericBoundaryRepresentationCategory
  , GenericRepresentationCategory
  , GenericPlacementCategory
  , GenericCostCategory
  , GenericEnvironmentCategory
  ]

expectedCompetences :: [GenericRequirementCompetence]
expectedCompetences =
  [ StructuralRequirementChecker
  , PropositionRequirementChecker
  , ProviderRequirementChecker
  , CallableRequirementChecker
  , BoundaryRequirementChecker
  , ArchitectureRequirementChecker
  , EffectsRequirementChecker
  , AuthorityRequirementChecker
  , BoundaryRepresentationRequirementChecker
  , RepresentationRequirementChecker
  , PlacementRequirementChecker
  , CostRequirementChecker
  , EnvironmentRequirementChecker
  ]

assert :: Bool -> String -> Either String ()
assert condition detail
  | condition = Right ()
  | otherwise = Left detail

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
