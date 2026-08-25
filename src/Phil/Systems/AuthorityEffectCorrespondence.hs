{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.AuthorityEffectCorrespondence
  ( AuthorityEffectStageRevision (..)
  , RealizationEffectRevision (..)
  , EffectVisibility (..)
  , ProviderEffectUse (..)
  , ProviderAuthorityExercise (..)
  , ProviderOperationAuthorityAssignment (..)
  , OpaqueProviderOperationSurface (..)
  , ProviderSemanticSurfaceBasis (..)
  , SystemsProviderUse (..)
  , AuthorityEffectStageBundle (..)
  , AuthorityEffectStageVerificationError (..)
  , deriveAuthorityEffectStageRevision
  , makeAuthorityEffectStageBundle
  , verifyAuthorityEffectStageBundle
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.AuthorityConfinement (AuthorityUse (..))
import Phil.Core.Callable
  ( CallableContract (..)
  , SemanticEffect (..)
  )
import Phil.Core.CallableRefinement
  ( CallableRefinementSurface (..)
  , CheckedCallableRefinement (..)
  )
import Phil.Core.ProviderAuthorityQualification
  ( CheckedProviderAuthorityQualification (..)
  , ProviderAuthoritySubject (..)
  , ProviderExtraAuthorityDisposition
  )
import Phil.Core.ProviderQualification
  ( CheckedProviderOperationQualification (..)
  , CheckedProviderSemanticQualification (..)
  , ProviderOperationKey (..)
  )
import Phil.Core.ProviderQualificationIdentity
  ( ProviderQualificationSubject (..)
  )
import Phil.Core.Static
  ( DefinitionRevision (..)
  , InterfaceRevision (..)
  , SemanticForm (..)
  , canonicalSemanticForm
  )
import Phil.Systems.Phase1Stage (SystemsMechanismKey (..))
import Phil.Systems.ProviderCallCorrespondence
  ( ProviderCallBindingBasis (..)
  , ProviderCallLink (..)
  , ProviderCallStageBundle (..)
  , ProviderCallStageRevision (..)
  , ProviderCallStageVerificationError
  , SelectedProviderAdmission (..)
  , verifyProviderCallStageBundle
  )

newtype AuthorityEffectStageRevision = AuthorityEffectStageRevision
  { unAuthorityEffectStageRevision :: Text
  }
  deriving (Eq, Ord, Show)

newtype RealizationEffectRevision = RealizationEffectRevision
  { unRealizationEffectRevision :: Text
  }
  deriving (Eq, Ord, Show)

data EffectVisibility
  = SourceObservableEffect
  | InternalRealizationEffect
  deriving (Eq, Ord, Show)

data ProviderEffectUse = ProviderEffectUse
  { providerEffectUseEffect :: SemanticEffect
  , providerEffectUseVisibility :: EffectVisibility
  , providerEffectUseRefinement :: Maybe RealizationEffectRevision
  }
  deriving (Eq, Ord, Show)

data ProviderAuthorityExercise
  = PublicProviderAuthority AuthorityUse
  | QualifiedInternalProviderAuthority AuthorityUse ProviderExtraAuthorityDisposition
  deriving (Eq, Ord, Show)

data ProviderOperationAuthorityAssignment = ProviderOperationAuthorityAssignment
  { operationPublicAuthority :: Set AuthorityUse
  , operationInternalAuthority :: Map AuthorityUse ProviderExtraAuthorityDisposition
  }
  deriving (Eq, Ord, Show)

data OpaqueProviderOperationSurface = OpaqueProviderOperationSurface
  { opaqueOperationEffectBound :: Set SemanticEffect
  , opaqueOperationPublicAuthority :: Set AuthorityUse
  }
  deriving (Eq, Ord, Show)

data ProviderSemanticSurfaceBasis
  = QualifiedProviderSemanticSurface
      CheckedProviderSemanticQualification
      CheckedProviderAuthorityQualification
      (Map ProviderOperationKey ProviderOperationAuthorityAssignment)
  | OpaqueProviderSemanticSurface
      Text
      (Map ProviderOperationKey OpaqueProviderOperationSurface)
  deriving (Eq, Ord, Show)

data SystemsProviderUse = SystemsProviderUse
  { systemsProviderUseMechanism :: SystemsMechanismKey
  , systemsProviderUseEffects :: Set ProviderEffectUse
  , systemsProviderUseAuthority :: Set ProviderAuthorityExercise
  }
  deriving (Eq, Ord, Show)

data AuthorityEffectStageBundle = AuthorityEffectStageBundle
  { authorityEffectStageBase :: ProviderCallStageBundle
  , authorityEffectStageRevision :: AuthorityEffectStageRevision
  , authorityEffectStageSurfaces :: Map Text ProviderSemanticSurfaceBasis
  , authorityEffectStageUses :: Map SystemsMechanismKey SystemsProviderUse
  }
  deriving (Eq, Show)

data AuthorityEffectStageVerificationError
  = AuthorityEffectBaseStageError ProviderCallStageVerificationError
  | AuthorityEffectStageRevisionMismatch AuthorityEffectStageRevision AuthorityEffectStageRevision
  | AuthorityEffectSurfaceDomainMismatch (Set Text) (Set Text)
  | AuthorityEffectUseDomainMismatch (Set SystemsMechanismKey) (Set SystemsMechanismKey)
  | AuthorityEffectUseMapKeyMismatch SystemsMechanismKey SystemsMechanismKey
  | AuthorityEffectQualifiedInterfaceMismatch Text InterfaceRevision InterfaceRevision
  | AuthorityEffectQualifiedDefinitionMismatch Text DefinitionRevision DefinitionRevision
  | AuthorityEffectAuthoritySubjectMismatch Text
  | AuthorityEffectOperationDomainMismatch Text (Set ProviderOperationKey) (Set ProviderOperationKey)
  | AuthorityEffectOperationEntryMismatch Text ProviderOperationKey
  | AuthorityEffectAuthorityAssignmentDomainMismatch Text (Set ProviderOperationKey) (Set ProviderOperationKey)
  | AuthorityEffectPublicAuthorityEscape Text (Set AuthorityUse)
  | AuthorityEffectPublicAuthorityUnassigned Text (Set AuthorityUse)
  | AuthorityEffectInternalAuthorityNotQualified Text ProviderOperationKey AuthorityUse
  | AuthorityEffectInternalAuthorityDispositionMismatch Text ProviderOperationKey AuthorityUse
  | AuthorityEffectOpaqueSurfaceRequiresOpaqueSelection Text
  | AuthorityEffectOpaqueSurfaceMissingEvidence Text
  | AuthorityEffectUnknownCallLink SystemsMechanismKey
  | AuthorityEffectRuntimeSymbolOnlyCall SystemsMechanismKey
  | AuthorityEffectMissingOperationSurface SystemsMechanismKey ProviderOperationKey
  | AuthorityEffectSemanticEffectWidening SystemsMechanismKey SemanticEffect
  | AuthorityEffectObservableRealizationWidening SystemsMechanismKey SemanticEffect
  | AuthorityEffectMissingRealizationRefinement SystemsMechanismKey SemanticEffect
  | AuthorityEffectHiddenPublicAuthority SystemsMechanismKey AuthorityUse
  | AuthorityEffectHiddenInternalAuthority SystemsMechanismKey AuthorityUse
  | AuthorityEffectInternalAuthorityUseDispositionMismatch SystemsMechanismKey AuthorityUse
  deriving (Eq, Show)

deriveAuthorityEffectStageRevision :: AuthorityEffectStageBundle -> AuthorityEffectStageRevision
deriveAuthorityEffectStageRevision bundle = AuthorityEffectStageRevision
  ("phil.phase1.authority-effect-stage.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("base_stage", SemanticAtom
          (unProviderCallStageRevision
            (providerCallStageRevision (authorityEffectStageBase bundle))))
      , ("surfaces", SemanticRecord (Map.fromList
          [ (key, semanticSurface surface)
          | (key, surface) <- Map.toAscList (authorityEffectStageSurfaces bundle)
          ]))
      , ("uses", SemanticRecord (Map.fromList
          [ (unSystemsMechanismKey key, semanticUse value)
          | (key, value) <- Map.toAscList (authorityEffectStageUses bundle)
          ]))
      ])))

makeAuthorityEffectStageBundle
  :: ProviderCallStageBundle
  -> Map Text ProviderSemanticSurfaceBasis
  -> Map SystemsMechanismKey SystemsProviderUse
  -> AuthorityEffectStageBundle
makeAuthorityEffectStageBundle base surfaces uses =
  provisional
    { authorityEffectStageRevision = deriveAuthorityEffectStageRevision provisional }
  where
    provisional = AuthorityEffectStageBundle
      { authorityEffectStageBase = base
      , authorityEffectStageRevision = AuthorityEffectStageRevision "pending"
      , authorityEffectStageSurfaces = surfaces
      , authorityEffectStageUses = uses
      }

verifyAuthorityEffectStageBundle
  :: AuthorityEffectStageBundle
  -> Either AuthorityEffectStageVerificationError ()
verifyAuthorityEffectStageBundle bundle = do
  mapLeft AuthorityEffectBaseStageError $
    verifyProviderCallStageBundle (authorityEffectStageBase bundle)
  requireEqual AuthorityEffectStageRevisionMismatch
    (deriveAuthorityEffectStageRevision bundle)
    (authorityEffectStageRevision bundle)
  let base = authorityEffectStageBase bundle
      selections = providerCallStageSelections base
      expectedOccurrences = Map.keysSet selections
      actualOccurrences = Map.keysSet (authorityEffectStageSurfaces bundle)
      expectedUses = providerCallStageCallSites base
      actualUses = Map.keysSet (authorityEffectStageUses bundle)
  requireEqual AuthorityEffectSurfaceDomainMismatch expectedOccurrences actualOccurrences
  requireEqual AuthorityEffectUseDomainMismatch expectedUses actualUses
  mapM_ (checkSurface selections) (Map.toAscList (authorityEffectStageSurfaces bundle))
  mapM_ (checkUse base (authorityEffectStageSurfaces bundle))
    (Map.toAscList (authorityEffectStageUses bundle))

checkSurface
  :: Map Text SelectedProviderAdmission
  -> (Text, ProviderSemanticSurfaceBasis)
  -> Either AuthorityEffectStageVerificationError ()
checkSurface selections (occurrence, surface) = do
  selection <- case Map.lookup occurrence selections of
    Just value -> Right value
    Nothing -> Left (AuthorityEffectSurfaceDomainMismatch (Map.keysSet selections) Set.empty)
  case surface of
    QualifiedProviderSemanticSurface semantic authority assignments -> do
      requireEqual (AuthorityEffectQualifiedInterfaceMismatch occurrence)
        (selectedProviderRequiredInterface selection)
        (checkedProviderContractRevision semantic)
      expectedDefinition <- case selectedProviderSubject selection of
        SemanticProviderImplementation definition -> Right definition
        ConcreteProviderRealization definition _ -> Right definition
        OpaqueProviderBoundary _ ->
          Left (AuthorityEffectQualifiedDefinitionMismatch occurrence
            (checkedProviderImplementationRevision semantic)
            (checkedProviderImplementationRevision semantic))
      requireEqual (AuthorityEffectQualifiedDefinitionMismatch occurrence)
        expectedDefinition (checkedProviderImplementationRevision semantic)
      checkAuthoritySubject occurrence selection authority
      let selectedOps = selectedProviderOperationEntries selection
          qualifiedOps = checkedProviderOperations semantic
          selectedKeys = Map.keysSet selectedOps
          qualifiedKeys = Map.keysSet qualifiedOps
          assignmentKeys = Map.keysSet assignments
      requireEqual (AuthorityEffectOperationDomainMismatch occurrence)
        selectedKeys qualifiedKeys
      mapM_ (checkQualifiedEntry occurrence selectedOps) (Map.toAscList qualifiedOps)
      requireEqual (AuthorityEffectAuthorityAssignmentDomainMismatch occurrence)
        selectedKeys assignmentKeys
      let assignedPublic = Set.unions
            [ operationPublicAuthority assignment
            | assignment <- Map.elems assignments
            ]
          allowedPublic = checkedProviderAuthorityClientVisible authority
          publicEscape = Set.difference assignedPublic allowedPublic
          unassignedPublic = Set.difference allowedPublic assignedPublic
      if Set.null publicEscape
        then Right ()
        else Left (AuthorityEffectPublicAuthorityEscape occurrence publicEscape)
      if Set.null unassignedPublic
        then Right ()
        else Left (AuthorityEffectPublicAuthorityUnassigned occurrence unassignedPublic)
      mapM_ (checkInternalAssignments occurrence authority)
        (Map.toAscList assignments)
    OpaqueProviderSemanticSurface evidence operations -> do
      case selectedProviderSubject selection of
        OpaqueProviderBoundary _ -> Right ()
        _ -> Left (AuthorityEffectOpaqueSurfaceRequiresOpaqueSelection occurrence)
      if Text.null evidence
        then Left (AuthorityEffectOpaqueSurfaceMissingEvidence occurrence)
        else Right ()
      requireEqual (AuthorityEffectOperationDomainMismatch occurrence)
        (Map.keysSet (selectedProviderOperationEntries selection))
        (Map.keysSet operations)

checkQualifiedEntry
  :: Text
  -> Map ProviderOperationKey a
  -> (ProviderOperationKey, CheckedProviderOperationQualification)
  -> Either AuthorityEffectStageVerificationError ()
checkQualifiedEntry occurrence selectedOps (operation, checked) =
  case Map.lookup operation selectedOps of
    Nothing -> Left (AuthorityEffectOperationEntryMismatch occurrence operation)
    Just _ ->
      if checkedProviderOperationKey checked == operation
        then Right ()
        else Left (AuthorityEffectOperationEntryMismatch occurrence operation)

checkAuthoritySubject
  :: Text
  -> SelectedProviderAdmission
  -> CheckedProviderAuthorityQualification
  -> Either AuthorityEffectStageVerificationError ()
checkAuthoritySubject occurrence selection checked =
  case (selectedProviderSubject selection, checkedProviderAuthoritySubject checked) of
    (SemanticProviderImplementation definition,
      SemanticProviderAuthoritySubject interface actualDefinition)
      | interface == selectedProviderRequiredInterface selection
        && actualDefinition == definition -> Right ()
    (ConcreteProviderRealization definition _,
      SemanticProviderAuthoritySubject interface actualDefinition)
      | interface == selectedProviderRequiredInterface selection
        && actualDefinition == definition -> Right ()
    _ -> Left (AuthorityEffectAuthoritySubjectMismatch occurrence)

checkInternalAssignments
  :: Text
  -> CheckedProviderAuthorityQualification
  -> (ProviderOperationKey, ProviderOperationAuthorityAssignment)
  -> Either AuthorityEffectStageVerificationError ()
checkInternalAssignments occurrence authority (operation, assignment) =
  mapM_ checkOne (Map.toAscList (operationInternalAuthority assignment))
  where
    qualifiedExtra = checkedProviderAuthorityDispositions authority
    checkOne (use, disposition) = case Map.lookup use qualifiedExtra of
      Nothing -> Left (AuthorityEffectInternalAuthorityNotQualified occurrence operation use)
      Just expected
        | expected == disposition -> Right ()
        | otherwise -> Left
            (AuthorityEffectInternalAuthorityDispositionMismatch occurrence operation use)

checkUse
  :: ProviderCallStageBundle
  -> Map Text ProviderSemanticSurfaceBasis
  -> (SystemsMechanismKey, SystemsProviderUse)
  -> Either AuthorityEffectStageVerificationError ()
checkUse base surfaces (key, use) = do
  requireEqual AuthorityEffectUseMapKeyMismatch key (systemsProviderUseMechanism use)
  link <- case Map.lookup key (providerCallStageLinks base) of
    Just value -> Right value
    Nothing -> Left (AuthorityEffectUnknownCallLink key)
  (occurrence, operation) <- case providerCallBindingBasis link of
    RuntimeSymbolOnlyProviderCall _ _ -> Left (AuthorityEffectRuntimeSymbolOnlyCall key)
    ExactProviderCallBinding selectedOccurrence _ _ selectedOperation _ ->
      Right (selectedOccurrence, selectedOperation)
  surface <- case Map.lookup occurrence surfaces of
    Just value -> Right value
    Nothing -> Left (AuthorityEffectMissingOperationSurface key operation)
  (effectBound, publicAuthority, internalAuthority) <-
    operationSurface occurrence operation surface
  mapM_ (checkEffect key effectBound) (Set.toAscList (systemsProviderUseEffects use))
  mapM_ (checkAuthority key publicAuthority internalAuthority)
    (Set.toAscList (systemsProviderUseAuthority use))

operationSurface
  :: Text
  -> ProviderOperationKey
  -> ProviderSemanticSurfaceBasis
  -> Either AuthorityEffectStageVerificationError
       (Set SemanticEffect, Set AuthorityUse, Map AuthorityUse ProviderExtraAuthorityDisposition)
operationSurface _ operation surface = case surface of
  QualifiedProviderSemanticSurface semantic _ assignments -> do
    checked <- case Map.lookup operation (checkedProviderOperations semantic) of
      Just value -> Right value
      Nothing -> Left (AuthorityEffectMissingOperationSurface
        (SystemsMechanismKey "unknown") operation)
    assignment <- case Map.lookup operation assignments of
      Just value -> Right value
      Nothing -> Left (AuthorityEffectMissingOperationSurface
        (SystemsMechanismKey "unknown") operation)
    let expectedSurface = checkedCallableRefinementExpected
          (checkedProviderCallableRefinement checked)
        bound = callableContractEffectBound
          (callableRefinementContract expectedSurface)
    Right (bound, operationPublicAuthority assignment, operationInternalAuthority assignment)
  OpaqueProviderSemanticSurface _ operations -> do
    selected <- case Map.lookup operation operations of
      Just value -> Right value
      Nothing -> Left (AuthorityEffectMissingOperationSurface
        (SystemsMechanismKey "unknown") operation)
    Right (opaqueOperationEffectBound selected, opaqueOperationPublicAuthority selected, Map.empty)

checkEffect
  :: SystemsMechanismKey
  -> Set SemanticEffect
  -> ProviderEffectUse
  -> Either AuthorityEffectStageVerificationError ()
checkEffect mechanism bound use
  | Set.member effect bound = Right ()
  | visibility == SourceObservableEffect =
      Left (AuthorityEffectObservableRealizationWidening mechanism effect)
  | otherwise = case providerEffectUseRefinement use of
      Just (RealizationEffectRevision revision)
        | not (Text.null revision) -> Right ()
      _ -> Left (AuthorityEffectMissingRealizationRefinement mechanism effect)
  where
    effect = providerEffectUseEffect use
    visibility = providerEffectUseVisibility use

checkAuthority
  :: SystemsMechanismKey
  -> Set AuthorityUse
  -> Map AuthorityUse ProviderExtraAuthorityDisposition
  -> ProviderAuthorityExercise
  -> Either AuthorityEffectStageVerificationError ()
checkAuthority mechanism publicAuthority internalAuthority exercise = case exercise of
  PublicProviderAuthority use
    | Set.member use publicAuthority -> Right ()
    | otherwise -> Left (AuthorityEffectHiddenPublicAuthority mechanism use)
  QualifiedInternalProviderAuthority use disposition ->
    case Map.lookup use internalAuthority of
      Nothing -> Left (AuthorityEffectHiddenInternalAuthority mechanism use)
      Just expected
        | expected == disposition -> Right ()
        | otherwise -> Left
            (AuthorityEffectInternalAuthorityUseDispositionMismatch mechanism use)

semanticSurface :: ProviderSemanticSurfaceBasis -> SemanticForm
semanticSurface surface = case surface of
  QualifiedProviderSemanticSurface semantic authority assignments -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "qualified")
    , ("interface", SemanticAtom (interfaceText (checkedProviderContractRevision semantic)))
    , ("definition", SemanticAtom (definitionText (checkedProviderImplementationRevision semantic)))
    , ("client_authority", semanticAuthoritySet (checkedProviderAuthorityClientVisible authority))
    , ("internal_authority", semanticAuthoritySet (checkedProviderAuthorityInternal authority))
    , ("assignments", SemanticRecord (Map.fromList
        [ (unProviderOperationKey operation, semanticAssignment assignment)
        | (operation, assignment) <- Map.toAscList assignments
        ]))
    ])
  OpaqueProviderSemanticSurface evidence operations -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "opaque")
    , ("evidence", SemanticAtom evidence)
    , ("operations", SemanticRecord (Map.fromList
        [ (unProviderOperationKey operation, semanticOpaqueOperation value)
        | (operation, value) <- Map.toAscList operations
        ]))
    ])

semanticAssignment :: ProviderOperationAuthorityAssignment -> SemanticForm
semanticAssignment assignment = SemanticRecord (Map.fromList
  [ ("public", semanticAuthoritySet (operationPublicAuthority assignment))
  , ("internal", SemanticRecord (Map.fromList
      [ (renderAuthority use, SemanticAtom (Text.pack (show disposition)))
      | (use, disposition) <- Map.toAscList (operationInternalAuthority assignment)
      ]))
  ])

semanticOpaqueOperation :: OpaqueProviderOperationSurface -> SemanticForm
semanticOpaqueOperation operation = SemanticRecord (Map.fromList
  [ ("effects", semanticEffectSet (opaqueOperationEffectBound operation))
  , ("authority", semanticAuthoritySet (opaqueOperationPublicAuthority operation))
  ])

semanticUse :: SystemsProviderUse -> SemanticForm
semanticUse use = SemanticRecord (Map.fromList
  [ ("mechanism", SemanticAtom (unSystemsMechanismKey (systemsProviderUseMechanism use)))
  , ("effects", SemanticUnordered (Set.map semanticEffectUse (systemsProviderUseEffects use)))
  , ("authority", SemanticUnordered (Set.map semanticAuthorityExercise (systemsProviderUseAuthority use)))
  ])

semanticEffectUse :: ProviderEffectUse -> SemanticForm
semanticEffectUse use = SemanticRecord (Map.fromList
  [ ("effect", SemanticAtom (unSemanticEffect (providerEffectUseEffect use)))
  , ("visibility", SemanticAtom (case providerEffectUseVisibility use of
      SourceObservableEffect -> "source-observable"
      InternalRealizationEffect -> "internal"))
  , ("refinement", maybe (SemanticAtom "none")
      (SemanticAtom . unRealizationEffectRevision)
      (providerEffectUseRefinement use))
  ])

semanticAuthorityExercise :: ProviderAuthorityExercise -> SemanticForm
semanticAuthorityExercise exercise = case exercise of
  PublicProviderAuthority use -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "public")
    , ("authority", SemanticAtom (renderAuthority use))
    ])
  QualifiedInternalProviderAuthority use disposition -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "qualified-internal")
    , ("authority", SemanticAtom (renderAuthority use))
    , ("disposition", SemanticAtom (Text.pack (show disposition)))
    ])

semanticEffectSet :: Set SemanticEffect -> SemanticForm
semanticEffectSet = SemanticUnordered . Set.map (SemanticAtom . unSemanticEffect)

semanticAuthoritySet :: Set AuthorityUse -> SemanticForm
semanticAuthoritySet = SemanticUnordered . Set.map (SemanticAtom . renderAuthority)

renderAuthority :: AuthorityUse -> Text
renderAuthority = Text.pack . show

interfaceText :: InterfaceRevision -> Text
interfaceText (InterfaceRevision value) = value

definitionText :: DefinitionRevision -> Text
definitionText (DefinitionRevision value) = value

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
