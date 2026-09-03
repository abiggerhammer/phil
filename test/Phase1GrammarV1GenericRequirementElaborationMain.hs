{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Text as Text
import Phil.Core.Focusing (FocusingError (..))
import Phil.Core.Generic
  ( GenericRequirement (..)
  , GenericStaticParameterKey (..)
  , GenericValueParameterKey (..)
  , StructuralPermission (..)
  )
import Phil.Core.Generic.RequirementCategory
  ( GenericRequirementCategory (..)
  , GenericRequirementCompetence (..)
  )
import Phil.Core.Static
  ( InterfaceRevision (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax (Proposition (..))
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.Elaborate
import Phil.Surface.GrammarV1.GenericRequirementCore
  ( GrammarV1GenericRequirementCoreError (..)
  , GrammarV1ResolvedProviderRequirement (..)
  , GrammarV1ResolvedStructuralRequirement (..)
  , grammarV1CheckedCoreGenericRequirement
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.Syntax (Located (..))
import System.Exit (exitFailure)

main :: IO ()
main = do
  results <- sequence
    [ test "SURF-008 Grammar-v1 generic requirements route to exact semantic categories"
        genericRequirementRouting
    , test "SURF-008 Core-supported generic requirements preserve exact semantic identities"
        coreRequirementRouting
    , test "SURF-008 structural generic requirements require resolved binder identity"
        structuralResolutionFailures
    , test "SURF-008 provider generic requirements require exact resolved interface evidence"
        providerResolutionFailures
    , test "SURF-008 proposition generic requirements preserve Core focusing rejection"
        propositionFocusingFailure
    , test "SURF-008 unsupported Core generic requirement categories remain fail-closed"
        unsupportedCategoriesStayClosed
    ]
  if and results then pure () else exitFailure

test :: String -> Either String () -> IO Bool
test label result = case result of
  Right () -> putStrLn ("PASS: " <> label) >> pure True
  Left detail -> putStrLn ("FAIL: " <> label <> " -- " <> detail) >> pure False

genericRequirementRouting :: Either String ()
genericRequirementRouting = do
  requirements <- requirementsFromRecord source
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

coreRequirementRouting :: Either String ()
coreRequirementRouting = do
  requirements <- requirementsFromRecord $ Text.unlines
    [ "record Routed[T : Type] requires {"
    , "  structural T : duplicate;"
    , "  proposition true;"
    , "  provider P : ProviderContract;"
    , "} { value : U8 }"
    ]
  case requirements of
    [structural, proposition, provider] -> do
      providerType <- providerRequirementType provider
      let valueKey = GenericValueParameterKey "resolved-value-T"
          staticKey = GenericStaticParameterKey "resolved-provider-P"
          interfaceRevision = InterfaceRevision "iface.provider-contract.v1"
          structuralEvidence =
            [GrammarV1ResolvedStructuralRequirement "T" valueKey]
          providerEvidence =
            [ GrammarV1ResolvedProviderRequirement
                "P" providerType staticKey interfaceRevision
            ]
          check = grammarV1CheckedCoreGenericRequirement
            emptyStaticContext
            emptySurfaceState
            structuralEvidence
            providerEvidence
      assert
        (check structural == Just
          (Right
            ( GenericStructuralRequirement valueKey ContractionPermission
            , []
            )))
        "structural requirement did not preserve resolved value-key and contraction identity"
      assert
        (check proposition == Just
          (Right (GenericPropositionRequirement Truth, [])))
        "proposition requirement did not preserve checked Core proposition identity"
      assert
        (check provider == Just
          (Right
            ( GenericProviderContractRequirement staticKey interfaceRevision
            , []
            )))
        "provider requirement did not preserve resolved static key/interface revision"
    other -> Left
      ("expected three Core-supported requirements, got " <> show (length other))

structuralResolutionFailures :: Either String ()
structuralResolutionFailures = do
  duplicateRequirement <- onlyRequirement "structural T : duplicate;"
  unsupportedRequirement <- onlyRequirement "structural T : frobnicate;"
  let leftKey = GenericValueParameterKey "left-T"
      rightKey = GenericValueParameterKey "right-T"
      check resolutions requirement = grammarV1CheckedCoreGenericRequirement
        emptyStaticContext emptySurfaceState resolutions [] requirement
  assert
    (check [] duplicateRequirement
      == Just (Left (GrammarV1StructuralRequirementUnresolved "T")))
    "missing structural binder resolution did not reject explicitly"
  assert
    (check
      [ GrammarV1ResolvedStructuralRequirement "T" leftKey
      , GrammarV1ResolvedStructuralRequirement "T" rightKey
      ]
      duplicateRequirement
      == Just
        (Left
          (GrammarV1StructuralRequirementAmbiguous "T" [leftKey, rightKey])))
    "ambiguous structural binder resolution silently selected one key"
  assert
    (check
      [GrammarV1ResolvedStructuralRequirement "T" leftKey]
      unsupportedRequirement
      == Just (Left (GrammarV1StructuralPermissionUnsupported "frobnicate")))
    "unknown structural permission was guessed as a Core permission"

providerResolutionFailures :: Either String ()
providerResolutionFailures = do
  provider <- onlyRequirement "provider P : ProviderContract;"
  providerType <- providerRequirementType provider
  let staticKey = GenericStaticParameterKey "provider-P"
      firstRevision = InterfaceRevision "iface.first"
      secondRevision = InterfaceRevision "iface.second"
      exact revision = GrammarV1ResolvedProviderRequirement
        "P" providerType staticKey revision
      wrongType = GrammarV1ResolvedProviderRequirement
        "P" GrammarV1BoolType staticKey firstRevision
      check resolutions = grammarV1CheckedCoreGenericRequirement
        emptyStaticContext emptySurfaceState [] resolutions provider
  assert
    (check [] == Just
      (Left (GrammarV1ProviderRequirementUnresolved "P" providerType)))
    "missing provider resolution did not reject explicitly"
  assert
    (check [wrongType] == Just
      (Left
        (GrammarV1ProviderRequirementSourceTypeMismatch
          "P" providerType [GrammarV1BoolType])))
    "provider evidence for a different source type was accepted"
  assert
    (check [exact firstRevision, exact secondRevision] == Just
      (Left
        (GrammarV1ProviderRequirementAmbiguous
          "P" providerType [firstRevision, secondRevision])))
    "ambiguous provider interface evidence silently selected one revision"

propositionFocusingFailure :: Either String ()
propositionFocusingFailure = do
  proposition <- onlyRequirement "proposition Missing();"
  let actual = grammarV1CheckedCoreGenericRequirement
        emptyStaticContext emptySurfaceState [] [] proposition
  assert
    (actual == Just
      (Left (GrammarV1GenericRequirementFocusingError (UnknownClaim "Missing"))))
    "generic proposition requirement collapsed Core focusing failure"

unsupportedCategoriesStayClosed :: Either String ()
unsupportedCategoriesStayClosed = do
  requirements <- requirementsFromRecord $ Text.unlines
    [ "record Routed[T : Type] requires {"
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
    , "} { value : U8 }"
    ]
  let check requirement = grammarV1CheckedCoreGenericRequirement
        emptyStaticContext emptySurfaceState [] [] requirement
  assert (all ((== Nothing) . check) requirements)
    "a requirement category without a Core GenericRequirement carrier escaped competence"

requirementsFromRecord :: Text.Text -> Either String [GrammarV1GenericRequirement]
requirementsFromRecord source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "surf008-generic-routing" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1RecordDeclaration recordDecl ->
        Right (map locatedValue (grammarV1RecordRequirements recordDecl))
      other -> Left ("expected record declaration, got " <> show other)
    declarations -> Left ("expected one declaration, got " <> show (length declarations))

onlyRequirement :: Text.Text -> Either String GrammarV1GenericRequirement
onlyRequirement requirement = do
  requirements <- requirementsFromRecord $ Text.unlines
    [ "record Routed[T : Type] requires {"
    , "  " <> requirement
    , "} { value : U8 }"
    ]
  case requirements of
    [single] -> Right single
    other -> Left ("expected one requirement, got " <> show (length other))

providerRequirementType :: GrammarV1GenericRequirement -> Either String GrammarV1Type
providerRequirementType requirement = case requirement of
  GrammarV1ProviderRequirement _ (Located _ sourceType) -> Right sourceType
  other -> Left ("expected provider requirement, got " <> show other)

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
