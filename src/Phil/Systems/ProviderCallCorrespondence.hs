{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.ProviderCallCorrespondence
  ( ProviderCallStageRevision (..)
  , SelectedProviderAdmission (..)
  , ProviderCallBindingBasis (..)
  , ProviderCallLink (..)
  , ProviderCallStageBundle (..)
  , ProviderCallStageVerificationError (..)
  , deriveProviderCallStageRevision
  , makeProviderCallStageBundle
  , verifyProviderCallStageBundle
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.ProviderQualification
  ( ProviderImplementationEntryKey (..)
  , ProviderOperationKey (..)
  )
import Phil.Core.ProviderQualificationIdentity
  ( CheckedProviderQualificationAdmissionIdentity (..)
  , ProviderQualificationAdmissionDecision (..)
  , ProviderQualificationAdmissionIdentityInput (..)
  , ProviderQualificationClaimIdentityInput (..)
  , ProviderQualificationSubject (..)
  , QualificationAdmissionRevision (..)
  , QualificationClaimRevision (..)
  , deriveQualificationAdmissionRevision
  , deriveQualificationClaimRevision
  )
import Phil.Core.Static
  ( DefinitionRevision (..)
  , InterfaceRevision (..)
  , SemanticForm (..)
  , canonicalSemanticForm
  )
import Phil.Systems.Phase1Stage
  ( Phase1StageBundle (..)
  , SystemsMechanismKey (..)
  )
import Phil.Systems.SubjectCorrespondence
  ( SubjectStageBundle (..)
  , SubjectStageRevision (..)
  , SubjectStageVerificationError
  , verifySubjectStageBundle
  )
import qualified SystemsSubjectAuthorityKernel as Kernel

newtype ProviderCallStageRevision = ProviderCallStageRevision
  { unProviderCallStageRevision :: Text
  }
  deriving (Eq, Ord, Show)

data SelectedProviderAdmission = SelectedProviderAdmission
  { selectedProviderOccurrence :: Text
  , selectedProviderRequiredInterface :: InterfaceRevision
  , selectedProviderSubject :: ProviderQualificationSubject
  , selectedProviderClaimInput :: ProviderQualificationClaimIdentityInput
  , selectedProviderAdmissionInput :: ProviderQualificationAdmissionIdentityInput
  , selectedProviderCheckedAdmission :: CheckedProviderQualificationAdmissionIdentity
  , selectedProviderOperationEntries
      :: Map ProviderOperationKey ProviderImplementationEntryKey
  , selectedProviderRuntimeSymbols :: Set Text
  }
  deriving (Eq, Ord, Show)

data ProviderCallBindingBasis
  = ExactProviderCallBinding
      Text
      QualificationAdmissionRevision
      InterfaceRevision
      ProviderOperationKey
      ProviderImplementationEntryKey
  | RuntimeSymbolOnlyProviderCall Text Text
  deriving (Eq, Ord, Show)

data ProviderCallLink = ProviderCallLink
  { providerCallMechanism :: SystemsMechanismKey
  , providerCallBindingBasis :: ProviderCallBindingBasis
  , providerCallRuntimeSymbol :: Text
  , providerCallRuntimeSignature :: Text
  }
  deriving (Eq, Ord, Show)

data ProviderCallStageBundle = ProviderCallStageBundle
  { providerCallStageBase :: SubjectStageBundle
  , providerCallStageRevision :: ProviderCallStageRevision
  , providerCallStageSelections :: Map Text SelectedProviderAdmission
  , providerCallStageCallSites :: Set SystemsMechanismKey
  , providerCallStageLinks :: Map SystemsMechanismKey ProviderCallLink
  }
  deriving (Eq, Show)

data ProviderCallStageVerificationError
  = ProviderCallBaseStageError SubjectStageVerificationError
  | ProviderCallStageRevisionMismatch ProviderCallStageRevision ProviderCallStageRevision
  | ProviderSelectionMapKeyMismatch Text Text
  | ProviderSelectionAdmissionRejected Text
  | ProviderSelectionEmptyOccurrence
  | ProviderSelectionClaimRevisionMismatch
      Text QualificationClaimRevision QualificationClaimRevision
  | ProviderSelectionAdmissionRevisionMismatch
      Text QualificationAdmissionRevision QualificationAdmissionRevision
  | ProviderSelectionOccurrenceInputMismatch Text Text
  | ProviderSelectionInterfaceInputMismatch Text InterfaceRevision InterfaceRevision
  | ProviderSelectionSubjectInputMismatch
      Text ProviderQualificationSubject ProviderQualificationSubject
  | ProviderSelectionDecisionInputMismatch
      Text ProviderQualificationAdmissionDecision ProviderQualificationAdmissionDecision
  | ProviderSelectionEmptyOperationMap Text
  | ProviderCallSiteUnknown (Set SystemsMechanismKey)
  | ProviderCallLinkDomainMismatch (Set SystemsMechanismKey) (Set SystemsMechanismKey)
  | ProviderCallLinkMapKeyMismatch SystemsMechanismKey SystemsMechanismKey
  | ProviderCallRuntimeSymbolInferenceRejected SystemsMechanismKey Text Text
  | ProviderCallUnknownSelection SystemsMechanismKey Text
  | ProviderCallAdmissionMismatch
      SystemsMechanismKey QualificationAdmissionRevision QualificationAdmissionRevision
  | ProviderCallInterfaceMismatch SystemsMechanismKey InterfaceRevision InterfaceRevision
  | ProviderCallOperationNotSelected SystemsMechanismKey ProviderOperationKey
  | ProviderCallImplementationEntryMismatch
      SystemsMechanismKey ProviderImplementationEntryKey ProviderImplementationEntryKey
  deriving (Eq, Show)

deriveProviderCallStageRevision :: ProviderCallStageBundle -> ProviderCallStageRevision
deriveProviderCallStageRevision bundle = ProviderCallStageRevision
  ("phil.phase1.provider-call-stage.canonical.v1:"
    <> canonicalSemanticForm (SemanticRecord (Map.fromList
      [ ("base_stage", SemanticAtom
          (unSubjectStageRevision (subjectStageRevision (providerCallStageBase bundle))))
      , ("selections", SemanticRecord
          (Map.fromList
            [ (key, semanticSelection selection)
            | (key, selection) <- Map.toAscList (providerCallStageSelections bundle)
            ]))
      , ("call_sites", semanticMechanismSet (providerCallStageCallSites bundle))
      , ("links", SemanticRecord
          (Map.fromList
            [ (unSystemsMechanismKey key, semanticLink link)
            | (key, link) <- Map.toAscList (providerCallStageLinks bundle)
            ]))
      ])))

makeProviderCallStageBundle
  :: SubjectStageBundle
  -> Map Text SelectedProviderAdmission
  -> Set SystemsMechanismKey
  -> Map SystemsMechanismKey ProviderCallLink
  -> ProviderCallStageBundle
makeProviderCallStageBundle base selections callSites links =
  provisional
    { providerCallStageRevision = deriveProviderCallStageRevision provisional }
  where
    provisional = ProviderCallStageBundle
      { providerCallStageBase = base
      , providerCallStageRevision = ProviderCallStageRevision "pending"
      , providerCallStageSelections = selections
      , providerCallStageCallSites = callSites
      , providerCallStageLinks = links
      }

verifyProviderCallStageBundle
  :: ProviderCallStageBundle
  -> Either ProviderCallStageVerificationError ()
verifyProviderCallStageBundle bundle = do
  mapLeft ProviderCallBaseStageError $
    verifySubjectStageBundle (providerCallStageBase bundle)
  let expectedRevision = deriveProviderCallStageRevision bundle
      actualRevision = providerCallStageRevision bundle
      mechanisms =
        phase1StageSystemsMechanisms
          (subjectStageBase (providerCallStageBase bundle))
      callSites = providerCallStageCallSites bundle
      links = providerCallStageLinks bundle
      selections = providerCallStageSelections bundle
      unknownCallSites = Set.difference callSites mechanisms
      linkDomain = Map.keysSet links
  requireEqual ProviderCallStageRevisionMismatch expectedRevision actualRevision
  mapM_ checkSelection (Map.toAscList selections)
  mapM_ checkLinkStructure (Map.toAscList links)
  case Kernel.decideProviderCallStageByFacts
      True
      (kernelProviderBindingBasis links)
      (allAdmissionsExact selections links)
      (allInterfacesExact selections links)
      (allOperationsExact selections links)
      (allImplementationEntriesExact selections links)
      (Set.null unknownCallSites && callSites == linkDomain) of
    Kernel.ProviderCallStageAcceptedDecision -> Right ()
    Kernel.ProviderCallSubjectStageDecision ->
      kernelInvariant "provider-subject-stage"
    Kernel.ProviderCallBindingDecision ->
      firstOrInvariant "provider-binding" (runtimeBindingErrors links)
    Kernel.ProviderCallAdmissionDecision ->
      firstOrInvariant "provider-admission" (admissionBindingErrors selections links)
    Kernel.ProviderCallInterfaceDecision ->
      firstOrInvariant "provider-interface" (interfaceBindingErrors selections links)
    Kernel.ProviderCallOperationDecision ->
      firstOrInvariant "provider-operation" (operationBindingErrors selections links)
    Kernel.ProviderCallImplementationEntryDecision ->
      firstOrInvariant "provider-entry" (entryBindingErrors selections links)
    Kernel.ProviderCallSiteDomainDecision
      | not (Set.null unknownCallSites) -> Left (ProviderCallSiteUnknown unknownCallSites)
      | otherwise -> Left (ProviderCallLinkDomainMismatch callSites linkDomain)
  where
    checkSelection (key, selection) = do
      requireEqual ProviderSelectionMapKeyMismatch key (selectedProviderOccurrence selection)
      if Text.null key
        then Left ProviderSelectionEmptyOccurrence
        else Right ()
      case checkedQualificationAdmissionDecision
          (selectedProviderCheckedAdmission selection) of
        QualificationAdmitted -> Right ()
        QualificationRejected _ -> Left (ProviderSelectionAdmissionRejected key)
      let claimInput = selectedProviderClaimInput selection
          admissionInput = selectedProviderAdmissionInput selection
          checked = selectedProviderCheckedAdmission selection
          expectedClaim = deriveQualificationClaimRevision claimInput
          actualClaim = checkedQualificationAdmissionClaimRevision checked
          expectedAdmission = deriveQualificationAdmissionRevision admissionInput
          actualAdmission = checkedQualificationAdmissionRevision checked
          inputOccurrence = qualificationAdmissionProviderOccurrence admissionInput
          inputInterface = qualificationAdmissionRequiredInterface admissionInput
          inputSubject = qualificationClaimSubject claimInput
          inputDecision = qualificationAdmissionDecision admissionInput
          actualDecision = checkedQualificationAdmissionDecision checked
      requireEqual (ProviderSelectionClaimRevisionMismatch key)
        expectedClaim actualClaim
      requireEqual (ProviderSelectionAdmissionRevisionMismatch key)
        expectedAdmission actualAdmission
      requireEqual ProviderSelectionOccurrenceInputMismatch
        key inputOccurrence
      requireEqual (ProviderSelectionInterfaceInputMismatch key)
        (selectedProviderRequiredInterface selection) inputInterface
      requireEqual (ProviderSelectionSubjectInputMismatch key)
        (selectedProviderSubject selection) inputSubject
      requireEqual (ProviderSelectionDecisionInputMismatch key)
        inputDecision actualDecision
      if Map.null (selectedProviderOperationEntries selection)
        then Left (ProviderSelectionEmptyOperationMap key)
        else Right ()

    checkLinkStructure (key, link) =
      requireEqual ProviderCallLinkMapKeyMismatch key (providerCallMechanism link)

kernelProviderBindingBasis
  :: Map SystemsMechanismKey ProviderCallLink
  -> Kernel.ProviderCallBindingBasis
kernelProviderBindingBasis links
  | any runtimeOnly (Map.elems links) = Kernel.RuntimeSymbolOnlyProviderCall
  | otherwise = Kernel.ExactProviderCallBinding
  where
    runtimeOnly link = case providerCallBindingBasis link of
      RuntimeSymbolOnlyProviderCall _ _ -> True
      ExactProviderCallBinding {} -> False

allAdmissionsExact
  :: Map Text SelectedProviderAdmission
  -> Map SystemsMechanismKey ProviderCallLink
  -> Bool
allAdmissionsExact selections = all linkAdmissionExact . Map.toAscList
  where
    linkAdmissionExact (_, link) = case providerCallBindingBasis link of
      RuntimeSymbolOnlyProviderCall _ _ -> False
      ExactProviderCallBinding occurrence admission _ _ _ ->
        case Map.lookup occurrence selections of
          Nothing -> False
          Just selection ->
            checkedQualificationAdmissionRevision
              (selectedProviderCheckedAdmission selection) == admission

allInterfacesExact
  :: Map Text SelectedProviderAdmission
  -> Map SystemsMechanismKey ProviderCallLink
  -> Bool
allInterfacesExact selections = all linkInterfaceExact . Map.elems
  where
    linkInterfaceExact link = case providerCallBindingBasis link of
      RuntimeSymbolOnlyProviderCall _ _ -> False
      ExactProviderCallBinding occurrence _ interface _ _ ->
        maybe False ((== interface) . selectedProviderRequiredInterface)
          (Map.lookup occurrence selections)

allOperationsExact
  :: Map Text SelectedProviderAdmission
  -> Map SystemsMechanismKey ProviderCallLink
  -> Bool
allOperationsExact selections = all linkOperationExact . Map.elems
  where
    linkOperationExact link = case providerCallBindingBasis link of
      RuntimeSymbolOnlyProviderCall _ _ -> False
      ExactProviderCallBinding occurrence _ _ operation _ ->
        maybe False (Map.member operation . selectedProviderOperationEntries)
          (Map.lookup occurrence selections)

allImplementationEntriesExact
  :: Map Text SelectedProviderAdmission
  -> Map SystemsMechanismKey ProviderCallLink
  -> Bool
allImplementationEntriesExact selections = all linkEntryExact . Map.elems
  where
    linkEntryExact link = case providerCallBindingBasis link of
      RuntimeSymbolOnlyProviderCall _ _ -> False
      ExactProviderCallBinding occurrence _ _ operation entry ->
        case Map.lookup occurrence selections of
          Nothing -> False
          Just selection ->
            Map.lookup operation (selectedProviderOperationEntries selection) == Just entry

runtimeBindingErrors
  :: Map SystemsMechanismKey ProviderCallLink
  -> [ProviderCallStageVerificationError]
runtimeBindingErrors links =
  [ ProviderCallRuntimeSymbolInferenceRejected key symbol signature
  | (key, link) <- Map.toAscList links
  , RuntimeSymbolOnlyProviderCall symbol signature <- [providerCallBindingBasis link]
  ]

admissionBindingErrors
  :: Map Text SelectedProviderAdmission
  -> Map SystemsMechanismKey ProviderCallLink
  -> [ProviderCallStageVerificationError]
admissionBindingErrors selections links = concatMap check (Map.toAscList links)
  where
    check (key, link) = case providerCallBindingBasis link of
      RuntimeSymbolOnlyProviderCall _ _ -> []
      ExactProviderCallBinding occurrence admission _ _ _ ->
        case Map.lookup occurrence selections of
          Nothing -> [ProviderCallUnknownSelection key occurrence]
          Just selection ->
            let expected = checkedQualificationAdmissionRevision
                  (selectedProviderCheckedAdmission selection)
            in [ ProviderCallAdmissionMismatch key expected admission
               | expected /= admission
               ]

interfaceBindingErrors
  :: Map Text SelectedProviderAdmission
  -> Map SystemsMechanismKey ProviderCallLink
  -> [ProviderCallStageVerificationError]
interfaceBindingErrors selections links = concatMap check (Map.toAscList links)
  where
    check (key, link) = case providerCallBindingBasis link of
      RuntimeSymbolOnlyProviderCall _ _ -> []
      ExactProviderCallBinding occurrence _ interface _ _ ->
        case Map.lookup occurrence selections of
          Nothing -> []
          Just selection ->
            let expected = selectedProviderRequiredInterface selection
            in [ ProviderCallInterfaceMismatch key expected interface
               | expected /= interface
               ]

operationBindingErrors
  :: Map Text SelectedProviderAdmission
  -> Map SystemsMechanismKey ProviderCallLink
  -> [ProviderCallStageVerificationError]
operationBindingErrors selections links = concatMap check (Map.toAscList links)
  where
    check (key, link) = case providerCallBindingBasis link of
      RuntimeSymbolOnlyProviderCall _ _ -> []
      ExactProviderCallBinding occurrence _ _ operation _ ->
        case Map.lookup occurrence selections of
          Just selection
            | Map.notMember operation (selectedProviderOperationEntries selection) ->
                [ProviderCallOperationNotSelected key operation]
          _ -> []

entryBindingErrors
  :: Map Text SelectedProviderAdmission
  -> Map SystemsMechanismKey ProviderCallLink
  -> [ProviderCallStageVerificationError]
entryBindingErrors selections links = concatMap check (Map.toAscList links)
  where
    check (key, link) = case providerCallBindingBasis link of
      RuntimeSymbolOnlyProviderCall _ _ -> []
      ExactProviderCallBinding occurrence _ _ operation entry ->
        case Map.lookup occurrence selections of
          Nothing -> []
          Just selection ->
            case Map.lookup operation (selectedProviderOperationEntries selection) of
              Just expected
                | expected /= entry ->
                    [ProviderCallImplementationEntryMismatch key expected entry]
              _ -> []

firstOrInvariant
  :: String
  -> [ProviderCallStageVerificationError]
  -> Either ProviderCallStageVerificationError ()
firstOrInvariant _ (err : _) = Left err
firstOrInvariant label [] = kernelInvariant label

kernelInvariant :: String -> Either ProviderCallStageVerificationError ()
kernelInvariant label =
  error ("SystemsSubjectAuthorityKernel mismatch: " <> label)

semanticSelection :: SelectedProviderAdmission -> SemanticForm
semanticSelection selection = SemanticRecord (Map.fromList
  [ ("occurrence", SemanticAtom (selectedProviderOccurrence selection))
  , ("interface", SemanticAtom
      (interfaceText (selectedProviderRequiredInterface selection)))
  , ("subject", semanticSubject (selectedProviderSubject selection))
  , ("claim_revision", SemanticAtom
      (claimText (checkedQualificationAdmissionClaimRevision
        (selectedProviderCheckedAdmission selection))))
  , ("admission", SemanticAtom
      (admissionText (checkedQualificationAdmissionRevision
        (selectedProviderCheckedAdmission selection))))
  , ("decision", SemanticAtom (decisionText
      (checkedQualificationAdmissionDecision
        (selectedProviderCheckedAdmission selection))))
  , ("operations", SemanticRecord (Map.fromList
      [ (unProviderOperationKey operation, SemanticAtom
          (unProviderImplementationEntryKey entry))
      | (operation, entry) <- Map.toAscList
          (selectedProviderOperationEntries selection)
      ]))
  , ("runtime_symbols", SemanticUnordered
      (Set.map SemanticAtom (selectedProviderRuntimeSymbols selection)))
  ])

semanticLink :: ProviderCallLink -> SemanticForm
semanticLink link = SemanticRecord (Map.fromList
  [ ("mechanism", SemanticAtom
      (unSystemsMechanismKey (providerCallMechanism link)))
  , ("binding", semanticBinding (providerCallBindingBasis link))
  , ("runtime_symbol", SemanticAtom (providerCallRuntimeSymbol link))
  , ("runtime_signature", SemanticAtom (providerCallRuntimeSignature link))
  ])

semanticBinding :: ProviderCallBindingBasis -> SemanticForm
semanticBinding basis = case basis of
  ExactProviderCallBinding occurrence admission interface operation entry ->
    SemanticRecord (Map.fromList
      [ ("kind", SemanticAtom "exact")
      , ("provider_occurrence", SemanticAtom occurrence)
      , ("admission", SemanticAtom (admissionText admission))
      , ("interface", SemanticAtom (interfaceText interface))
      , ("operation", SemanticAtom (unProviderOperationKey operation))
      , ("implementation_entry", SemanticAtom
          (unProviderImplementationEntryKey entry))
      ])
  RuntimeSymbolOnlyProviderCall symbol signature -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "runtime-symbol-only")
    , ("symbol", SemanticAtom symbol)
    , ("signature", SemanticAtom signature)
    ])

semanticSubject :: ProviderQualificationSubject -> SemanticForm
semanticSubject subject = case subject of
  SemanticProviderImplementation definition -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "semantic-implementation")
    , ("definition", SemanticAtom (definitionText definition))
    ])
  ConcreteProviderRealization definition realization -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "concrete-realization")
    , ("definition", SemanticAtom (definitionText definition))
    , ("realization", SemanticAtom realization)
    ])
  OpaqueProviderBoundary boundary -> SemanticRecord (Map.fromList
    [ ("kind", SemanticAtom "opaque-boundary")
    , ("boundary", SemanticAtom boundary)
    ])

semanticMechanismSet :: Set SystemsMechanismKey -> SemanticForm
semanticMechanismSet = SemanticUnordered . Set.map
  (SemanticAtom . unSystemsMechanismKey)

interfaceText :: InterfaceRevision -> Text
interfaceText (InterfaceRevision value) = value

definitionText :: DefinitionRevision -> Text
definitionText (DefinitionRevision value) = value

claimText :: QualificationClaimRevision -> Text
claimText = unQualificationClaimRevision

admissionText :: QualificationAdmissionRevision -> Text
admissionText (QualificationAdmissionRevision value) = value

decisionText :: ProviderQualificationAdmissionDecision -> Text
decisionText decision = case decision of
  QualificationAdmitted -> "admitted"
  QualificationRejected reasons ->
    "rejected:" <> Text.intercalate "," (Set.toAscList reasons)

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mkError expected actual
  | expected == actual = Right ()
  | otherwise = Left (mkError expected actual)

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
