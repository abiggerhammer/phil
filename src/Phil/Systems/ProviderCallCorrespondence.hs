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
  , QualificationClaimRevision
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
      unknownCallSites = Set.difference (providerCallStageCallSites bundle) mechanisms
      linkDomain = Map.keysSet (providerCallStageLinks bundle)
  requireEqual ProviderCallStageRevisionMismatch expectedRevision actualRevision
  if Set.null unknownCallSites
    then Right ()
    else Left (ProviderCallSiteUnknown unknownCallSites)
  requireEqual ProviderCallLinkDomainMismatch
    (providerCallStageCallSites bundle) linkDomain
  mapM_ checkSelection (Map.toAscList (providerCallStageSelections bundle))
  mapM_ (checkLink (providerCallStageSelections bundle))
    (Map.toAscList (providerCallStageLinks bundle))
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

    checkLink selections (key, link) = do
      requireEqual ProviderCallLinkMapKeyMismatch key (providerCallMechanism link)
      case providerCallBindingBasis link of
        RuntimeSymbolOnlyProviderCall symbol signature ->
          Left (ProviderCallRuntimeSymbolInferenceRejected key symbol signature)
        ExactProviderCallBinding occurrence admission interface operation entry -> do
          selection <- case Map.lookup occurrence selections of
            Just value -> Right value
            Nothing -> Left (ProviderCallUnknownSelection key occurrence)
          let expectedAdmission = checkedQualificationAdmissionRevision
                (selectedProviderCheckedAdmission selection)
              expectedInterface = selectedProviderRequiredInterface selection
          requireEqual (ProviderCallAdmissionMismatch key)
            expectedAdmission admission
          requireEqual (ProviderCallInterfaceMismatch key)
            expectedInterface interface
          expectedEntry <- case Map.lookup operation
              (selectedProviderOperationEntries selection) of
            Just value -> Right value
            Nothing -> Left (ProviderCallOperationNotSelected key operation)
          requireEqual (ProviderCallImplementationEntryMismatch key)
            expectedEntry entry

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
