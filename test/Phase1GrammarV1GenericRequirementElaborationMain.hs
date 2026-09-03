{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.Core.Focusing (FocusingError (..))
import Phil.Core.Generic
  ( GenericDischargeLineage (..)
  , GenericEvidence (..)
  , GenericInstantiationError (..)
  , GenericInstantiationRecord (..)
  , GenericRequirement (..)
  , GenericRequirementDisposition (..)
  , GenericStaticParameterKey (..)
  , GenericStructuralError (..)
  , GenericValueParameterKey (..)
  , StructuralPermission (..)
  )
import Phil.Core.Generic.RequirementCategory
  ( GenericRequirementCategory (..)
  , GenericRequirementCompetence (..)
  )
import Phil.Core.Generic.StaticActual
  ( GenericStaticKind (..)
  , GenericStaticParameter (..)
  )
import Phil.Core.Static
  ( DeclarationKey (..)
  , DefinitionRevision (..)
  , InterfaceRevision (..)
  , SemanticForm (..)
  , emptyStaticContext
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Proposition (..)
  )
import Phil.Surface.Check.Support (emptySurfaceState)
import Phil.Surface.GrammarV1.Elaborate
import Phil.Surface.GrammarV1.GenericDischarge
  ( GrammarV1CheckedGenericRequirement (..)
  , GrammarV1CheckedSpecializedGenericDischarge (..)
  , GrammarV1GenericDischargeError (..)
  , GrammarV1ResolvedGenericRequirementSet (..)
  , GrammarV1ResolvedRequirementDisposition (..)
  , grammarV1CheckedStrictSpecializedGenericDischarge
  )
import Phil.Surface.GrammarV1.GenericRequirementCore
  ( GrammarV1GenericRequirementCoreError (..)
  , GrammarV1ResolvedProviderRequirement (..)
  , GrammarV1ResolvedStructuralRequirement (..)
  , grammarV1CheckedCoreGenericRequirement
  )
import Phil.Surface.GrammarV1.Parser
import Phil.Surface.GrammarV1.SpecializedStaticReference
  ( GrammarV1CheckedSpecializedStaticReference (..)
  , GrammarV1ResolvedDirectStaticArgument (..)
  , grammarV1CheckedSpecializedStaticReference
  )
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
    , test "SURF-008 specialized applications compose through strict Core generic discharge"
        strictGenericDischargeComposition
    , test "SURF-008 generic discharge requires the exact application target identity"
        genericDischargeTargetIdentity
    , test "SURF-008 generic discharge binds dispositions to exact source occurrences"
        genericDischargeDispositionDomain
    , test "SURF-008 generic discharge preserves strict Core semantic rejections"
        genericDischargeCoreRejections
    , test "SURF-008 generic discharge stays fail-closed for unsupported requirement carriers"
        genericDischargeUnsupportedRequirements
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

strictGenericDischargeComposition :: Either String ()
strictGenericDischargeComposition = do
  application <- checkedBoxApplication
  requirements <- supportedLocatedRequirements
  case requirements of
    [structural, proposition, provider] -> do
      providerType <- providerRequirementType (locatedValue provider)
      let valueKey = GenericValueParameterKey "value.T"
          providerKey = GenericStaticParameterKey "provider.P"
          requiredProviderInterface = InterfaceRevision "iface.provider.v1"
          definitionRevision = DefinitionRevision "def.Box.v7"
          structuralResolutions =
            [GrammarV1ResolvedStructuralRequirement "T" valueKey]
          providerResolutions =
            [ GrammarV1ResolvedProviderRequirement
                "P" providerType providerKey requiredProviderInterface
            ]
          requirementSet = GrammarV1ResolvedGenericRequirementSet
            boxDeclarationKey boxInterfaceRevision requirements
          dispositions =
            [ GrammarV1ResolvedRequirementDisposition
                structural (GenericSatisfiedByStructuralMode Unrestricted)
            , GrammarV1ResolvedRequirementDisposition
                proposition
                (GenericSatisfiedByEvidence GenericEvidence
                  { genericEvidenceProposition = Truth
                  , genericEvidenceIdentity = "proof.true.001"
                  })
            , GrammarV1ResolvedRequirementDisposition
                provider
                (GenericSatisfiedByExactProvider requiredProviderInterface)
            ]
          actual = grammarV1CheckedStrictSpecializedGenericDischarge
            emptyStaticContext
            emptySurfaceState
            structuralResolutions
            providerResolutions
            definitionRevision
            application
            requirementSet
            dispositions
      case actual of
        Just (Right checked) -> do
          assert
            (map checkedGenericRequirementSource
              (checkedGenericDischargeRequirements checked) == requirements)
            "generic discharge reordered declaration-side requirements"
          let instantiation = checkedGenericDischargeInstantiation checked
              lineage = checkedGenericDischargeLineage checked
          assert
            (Map.size (genericInstantiationDispositions instantiation) == 3)
            "strict generic discharge lost an accepted disposition"
          assert
            (genericDischargeApplicationIdentity lineage
              == checkedSpecializedStaticApplicationIdentity application)
            "generic discharge lineage changed the checked application identity"
          assert
            (genericDischargeDefinitionRevision lineage == definitionRevision)
            "generic discharge lineage changed the supplied definition revision"
          assert
            (genericDischargeDispositions lineage
              == genericInstantiationDispositions instantiation)
            "generic discharge lineage changed the accepted disposition record"
        other -> Left ("strict generic discharge composition changed: " <> show other)
    other -> Left ("expected three supported located requirements, got " <> show (length other))

genericDischargeTargetIdentity :: Either String ()
genericDischargeTargetIdentity = do
  application <- checkedBoxApplication
  requirements <- supportedLocatedRequirements
  let wrongDeclaration = DeclarationKey "decl.Other"
      requirementSet = GrammarV1ResolvedGenericRequirementSet
        wrongDeclaration boxInterfaceRevision requirements
      actual = grammarV1CheckedStrictSpecializedGenericDischarge
        emptyStaticContext emptySurfaceState [] []
        (DefinitionRevision "def.Box")
        application
        requirementSet
        []
  assert
    (actual == Just
      (Left
        (GrammarV1GenericRequirementTargetMismatch
          boxDeclarationKey
          boxInterfaceRevision
          wrongDeclaration
          boxInterfaceRevision)))
    "requirement set for another generic declaration attached to the application"

genericDischargeDispositionDomain :: Either String ()
genericDischargeDispositionDomain = do
  application <- checkedBoxApplication
  requirements <- locatedRequirementsFromRecord $ Text.unlines
    [ "record Routed[T : Type] requires {"
    , "  proposition true;"
    , "} { value : U8 }"
    ]
  foreignRequirements <- locatedRequirementsFromRecord $ Text.unlines
    [ "record Foreign[T : Type] requires {"
    , "  proposition false;"
    , "} { value : U8 }"
    ]
  case (requirements, foreignRequirements) of
    ([requirement], [foreignRequirement]) -> do
      let requirementSet = GrammarV1ResolvedGenericRequirementSet
            boxDeclarationKey boxInterfaceRevision requirements
          evidence = GenericSatisfiedByEvidence GenericEvidence
            { genericEvidenceProposition = Truth
            , genericEvidenceIdentity = "proof.true"
            }
          disposition = GrammarV1ResolvedRequirementDisposition requirement evidence
          foreignDisposition = GrammarV1ResolvedRequirementDisposition
            foreignRequirement evidence
          check dispositions = grammarV1CheckedStrictSpecializedGenericDischarge
            emptyStaticContext emptySurfaceState [] []
            (DefinitionRevision "def.Box")
            application
            requirementSet
            dispositions
      assert
        (check [] == Just
          (Left (GrammarV1MissingRequirementDisposition requirement)))
        "missing source-bound disposition was silently synthesized"
      assert
        (check [disposition, disposition] == Just
          (Left (GrammarV1DuplicateRequirementDisposition requirement)))
        "duplicate source-bound disposition silently selected one value"
      assert
        (check [foreignDisposition] == Just
          (Left (GrammarV1UnexpectedRequirementDisposition foreignRequirement)))
        "disposition for a foreign source requirement entered the domain"
    other -> Left ("unexpected disposition-domain fixture shape: " <> show other)

genericDischargeCoreRejections :: Either String ()
genericDischargeCoreRejections = do
  application <- checkedBoxApplication
  structuralRequirements <- locatedRequirementsFromRecord $ Text.unlines
    [ "record Routed[T : Type] requires {"
    , "  structural T : duplicate;"
    , "} { value : U8 }"
    ]
  propositionRequirements <- locatedRequirementsFromRecord $ Text.unlines
    [ "record Routed[T : Type] requires {"
    , "  proposition true;"
    , "} { value : U8 }"
    ]
  case (structuralRequirements, propositionRequirements) of
    ([structural], [proposition]) -> do
      let valueKey = GenericValueParameterKey "value.T"
          structuralSet = GrammarV1ResolvedGenericRequirementSet
            boxDeclarationKey boxInterfaceRevision structuralRequirements
          structuralActual = grammarV1CheckedStrictSpecializedGenericDischarge
            emptyStaticContext
            emptySurfaceState
            [GrammarV1ResolvedStructuralRequirement "T" valueKey]
            []
            (DefinitionRevision "def.Box")
            application
            structuralSet
            [ GrammarV1ResolvedRequirementDisposition
                structural (GenericSatisfiedByStructuralMode Linear)
            ]
      assert
        (structuralActual == Just
          (Left
            (GrammarV1GenericInstantiationError
              (GenericStructuralInstantiationError
                (MissingStructuralPermission
                  valueKey ContractionPermission Linear)))))
        "surface composition weakened Core structural-discharge rejection"
      let propositionSet = GrammarV1ResolvedGenericRequirementSet
            boxDeclarationKey boxInterfaceRevision propositionRequirements
          propositionActual = grammarV1CheckedStrictSpecializedGenericDischarge
            emptyStaticContext
            emptySurfaceState
            []
            []
            (DefinitionRevision "def.Box")
            application
            propositionSet
            [ GrammarV1ResolvedRequirementDisposition
                proposition (GenericAssumptionDependent "not-source-authorized")
            ]
      assert
        (propositionActual == Just
          (Left
            (GrammarV1GenericInstantiationError
              (GenericAssumptionNotPermitted
                (GenericPropositionRequirement Truth)))))
        "strict surface discharge silently admitted an assumption disposition"
    other -> Left ("unexpected Core-rejection fixture shape: " <> show other)

genericDischargeUnsupportedRequirements :: Either String ()
genericDischargeUnsupportedRequirements = do
  application <- checkedBoxApplication
  requirements <- locatedRequirementsFromRecord $ Text.unlines
    [ "record Routed[T : Type] requires {"
    , "  callable F : CallableContract;"
    , "} { value : U8 }"
    ]
  let requirementSet = GrammarV1ResolvedGenericRequirementSet
        boxDeclarationKey boxInterfaceRevision requirements
      actual = grammarV1CheckedStrictSpecializedGenericDischarge
        emptyStaticContext emptySurfaceState [] []
        (DefinitionRevision "def.Box")
        application
        requirementSet
        []
  assert (actual == Nothing)
    "strict generic discharge invented a Core carrier for an unsupported requirement"

checkedBoxApplication :: Either String GrammarV1CheckedSpecializedStaticReference
checkedBoxApplication = do
  reference <- aliasStaticReference "type Applied = Box[U32];"
  case grammarV1StaticReferenceArguments reference of
    [argument] ->
      case grammarV1CheckedSpecializedStaticReference
          boxDeclarationKey
          boxInterfaceRevision
          [GenericStaticParameter (GenericStaticParameterKey "T") GenericTypeKind]
          [ GrammarV1ResolvedDirectStaticArgument
              argument GenericTypeKind (SemanticAtom "type.U32.checked")
          ]
          []
          reference of
        Just (Right checked) -> Right checked
        other -> Left ("checked Box application changed: " <> show other)
    arguments -> Left
      ("expected one Box static argument, got " <> show (length arguments))

supportedLocatedRequirements
  :: Either String [Located GrammarV1GenericRequirement]
supportedLocatedRequirements = locatedRequirementsFromRecord $ Text.unlines
  [ "record Routed[T : Type] requires {"
  , "  structural T : duplicate;"
  , "  proposition true;"
  , "  provider P : ProviderContract;"
  , "} { value : U8 }"
  ]

boxDeclarationKey :: DeclarationKey
boxDeclarationKey = DeclarationKey "decl.Box"

boxInterfaceRevision :: InterfaceRevision
boxInterfaceRevision = InterfaceRevision "iface.Box.v1"

requirementsFromRecord :: Text.Text -> Either String [GrammarV1GenericRequirement]
requirementsFromRecord source =
  map locatedValue <$> locatedRequirementsFromRecord source

locatedRequirementsFromRecord
  :: Text.Text
  -> Either String [Located GrammarV1GenericRequirement]
locatedRequirementsFromRecord source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "surf008-generic-routing" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1RecordDeclaration recordDecl ->
        Right (grammarV1RecordRequirements recordDecl)
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

aliasStaticReference :: Text.Text -> Either String GrammarV1StaticReference
aliasStaticReference source = do
  sourceFile <- mapLeft show $
    parseGrammarV1StructuralSource "surf008-generic-discharge" source
  case grammarV1TopLevelDecls sourceFile of
    [Located _ top] -> case locatedValue (grammarV1Declaration top) of
      GrammarV1TypeAliasDeclaration alias ->
        case locatedValue (grammarV1TypeAliasTarget alias) of
          GrammarV1NamedType reference -> Right reference
          other -> Left ("expected named alias target, got " <> show other)
      other -> Left ("expected type alias declaration, got " <> show other)
    declarations -> Left
      ("expected one type alias declaration, got " <> show (length declarations))

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
