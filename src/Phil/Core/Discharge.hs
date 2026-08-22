{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Discharge
  ( RuntimeBinding (..)
  , ExportBinding (..)
  , DischargePolicy
  , StaticDischarge (..)
  , ObligationDisposition (..)
  , ResolvedObligation (..)
  , DischargeError (..)
  , emptyDischargePolicy
  , bindExplicitEvidence
  , bindRuntime
  , bindExport
  , resolveObligation
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Core.Checker (CheckState (..))
import Phil.Core.Context
  ( CheckError
  , ResourceContext (..)
  , useUnrestricted
  )
import Phil.Core.Decision
  ( AssumptionRef (..)
  , CertificateError
  , DecisionCertificate
  , SolverAssumption (..)
  , certificateCheckerId
  , certificateProducerId
  , checkDecisionCertificate
  , proposeDecisionCertificate
  )
import Phil.Core.Focusing
  ( FocusMechanism (..)
  , FocusPlan (..)
  , FocusedRequirement (..)
  , FocusingError
  , canonicalizeProposition
  , focusProposition
  )
import Phil.Core.Refinement
  ( bindingEvidencePropositions
  , evidenceProposition
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax
  ( Name
  , Obligation (..)
  , ObligationId (..)
  , Proposition (..)
  , Ty
  )

data RuntimeBinding = RuntimeBinding
  { runtimeObligationId :: ObligationId
  , runtimeProposition :: Proposition
  , runtimeRequiredPoint :: Text
  , runtimeValidator :: Text
  , runtimeSuccessEvidence :: Ty
  , runtimeFailureClass :: Text
  , runtimeResourceContract :: Text
  , runtimeCostRef :: Text
  }
  deriving (Eq, Ord, Show)

data ExportBinding = ExportBinding
  { exportObligationId :: ObligationId
  , exportProposition :: Proposition
  , exportRequiredPoint :: Text
  , exportBoundary :: Text
  }
  deriving (Eq, Ord, Show)

data DischargePolicy = DischargePolicy
  { explicitEvidenceBindings :: Map.Map ObligationId Name
  , runtimeBindings :: Map.Map ObligationId RuntimeBinding
  , exportBindings :: Map.Map ObligationId ExportBinding
  }
  deriving (Eq, Show)

data StaticDischarge
  = StaticByDefinition
  | StaticByEvidence Name
  | StaticByCertificate
      { staticCertificateProducer :: Text
      , staticCertificateChecker :: Text
      , staticCertificate :: DecisionCertificate
      }
  deriving (Eq, Ord, Show)

data ObligationDisposition
  = StaticallyDischarged StaticDischarge
  | RuntimeBound RuntimeBinding
  | Exported ExportBinding
  deriving (Eq, Ord, Show)

data ResolvedObligation = ResolvedObligation
  { resolvedObligation :: Obligation
  , resolvedCanonicalProposition :: Proposition
  , resolvedPrerequisites :: [ResolvedObligation]
  , resolvedDisposition :: ObligationDisposition
  }
  deriving (Eq, Show)

data DischargeError
  = DischargeFocusingError FocusingError
  | DischargeResourceError CheckError
  | ProducedInvalidCertificate CertificateError
  | DuplicatePolicyBinding Text ObligationId
  | ExplicitEvidenceDoesNotMatch ObligationId Name Proposition
  | RuntimeBindingIdMismatch ObligationId ObligationId
  | RuntimeBindingRequiredPointMismatch ObligationId Text Text
  | RuntimeBindingPropositionMismatch ObligationId Proposition Proposition
  | RuntimeSuccessEvidenceNotProof ObligationId Ty
  | RuntimeSuccessEvidenceMismatch ObligationId Proposition Proposition
  | ExportBindingIdMismatch ObligationId ObligationId
  | ExportBindingRequiredPointMismatch ObligationId Text Text
  | ExportBindingPropositionMismatch ObligationId Proposition Proposition
  | ExportedPrerequisiteBlocksLocalDischarge ObligationId
  | UnresolvedObligation ObligationId Proposition
  deriving (Eq, Show)

emptyDischargePolicy :: DischargePolicy
emptyDischargePolicy = DischargePolicy Map.empty Map.empty Map.empty

bindExplicitEvidence
  :: ObligationId
  -> Name
  -> DischargePolicy
  -> Either DischargeError DischargePolicy
bindExplicitEvidence obligationId evidenceName policy
  | Map.member obligationId (explicitEvidenceBindings policy) =
      Left (DuplicatePolicyBinding "explicit-evidence" obligationId)
  | otherwise = Right policy
      { explicitEvidenceBindings =
          Map.insert obligationId evidenceName (explicitEvidenceBindings policy)
      }

bindRuntime
  :: RuntimeBinding
  -> DischargePolicy
  -> Either DischargeError DischargePolicy
bindRuntime binding policy
  | Map.member obligationId (runtimeBindings policy) =
      Left (DuplicatePolicyBinding "runtime" obligationId)
  | otherwise = Right policy
      { runtimeBindings = Map.insert obligationId binding (runtimeBindings policy) }
  where
    obligationId = runtimeObligationId binding

bindExport
  :: ExportBinding
  -> DischargePolicy
  -> Either DischargeError DischargePolicy
bindExport binding policy
  | Map.member obligationId (exportBindings policy) =
      Left (DuplicatePolicyBinding "export" obligationId)
  | otherwise = Right policy
      { exportBindings = Map.insert obligationId binding (exportBindings policy) }
  where
    obligationId = exportObligationId binding

resolveObligation
  :: StaticContext
  -> CheckState
  -> DischargePolicy
  -> Obligation
  -> Either DischargeError ResolvedObligation
resolveObligation staticContext state policy obligation = do
  focusPlan <- mapLeft DischargeFocusingError $
    focusProposition staticContext state (obligationProposition obligation)
  evidenceAssumptions <- collectEvidenceAssumptions staticContext state
  (resolvedSides, sideAssumptions, allSidesLocal) <-
    resolvePrerequisites
      staticContext
      state
      policy
      obligation
      evidenceAssumptions
      (focusPrerequisites focusPlan)
  disposition <-
    resolveFocusedRequirement
      staticContext
      state
      policy
      obligation
      (evidenceAssumptions ++ sideAssumptions)
      allSidesLocal
      (focusGoal focusPlan)
  Right ResolvedObligation
    { resolvedObligation = obligation
    , resolvedCanonicalProposition = focusedCanonical (focusGoal focusPlan)
    , resolvedPrerequisites = resolvedSides
    , resolvedDisposition = disposition
    }

resolvePrerequisites
  :: StaticContext
  -> CheckState
  -> DischargePolicy
  -> Obligation
  -> [SolverAssumption]
  -> [FocusedRequirement]
  -> Either DischargeError ([ResolvedObligation], [SolverAssumption], Bool)
resolvePrerequisites staticContext state policy parent evidenceAssumptions requirements =
  go 1 [] [] True requirements
  where
    go _ resolved assumptions allLocal [] =
      Right (reverse resolved, reverse assumptions, allLocal)
    go index resolved assumptions allLocal (requirement : rest) = do
      let child = subtractionChildObligation parent index requirement
          availableAssumptions = evidenceAssumptions ++ reverse assumptions
      disposition <-
        resolveFocusedRequirement
          staticContext
          state
          policy
          child
          availableAssumptions
          True
          requirement
      let resolvedChild = ResolvedObligation
            { resolvedObligation = child
            , resolvedCanonicalProposition = focusedCanonical requirement
            , resolvedPrerequisites = []
            , resolvedDisposition = disposition
            }
          locallyEstablished =
            case disposition of
              Exported _ -> False
              _ -> True
          nextAssumptions
            | locallyEstablished =
                SolverAssumption
                  (PrerequisiteFact (obligationId child))
                  (focusedCanonical requirement)
                  : assumptions
            | otherwise = assumptions
      go
        (index + 1)
        (resolvedChild : resolved)
        nextAssumptions
        (allLocal && locallyEstablished)
        rest

resolveFocusedRequirement
  :: StaticContext
  -> CheckState
  -> DischargePolicy
  -> Obligation
  -> [SolverAssumption]
  -> Bool
  -> FocusedRequirement
  -> Either DischargeError ObligationDisposition
resolveFocusedRequirement staticContext state policy obligation assumptions prerequisitesLocal requirement
  | not prerequisitesLocal =
      resolveExportOnly staticContext state policy obligation requirement
  | otherwise =
      case focusedMechanism requirement of
        FocusByDefinition -> Right (StaticallyDischarged StaticByDefinition)
        FocusByEvidence evidenceName ->
          Right (StaticallyDischarged (StaticByEvidence evidenceName))
        FocusNeedsDecisionProcedure ->
          case proposeDecisionCertificate state assumptions (focusedCanonical requirement) of
            Just certificate -> do
              case checkDecisionCertificate state assumptions (focusedCanonical requirement) certificate of
                Right () -> Right $ StaticallyDischarged StaticByCertificate
                  { staticCertificateProducer = certificateProducerId
                  , staticCertificateChecker = certificateCheckerId
                  , staticCertificate = certificate
                  }
                Left error -> Left (ProducedInvalidCertificate error)
            Nothing -> resolveExplicitThenArchitecture staticContext state policy obligation requirement
        FocusNeedsExplicitMechanism ->
          resolveExplicitThenArchitecture staticContext state policy obligation requirement

resolveExplicitThenArchitecture
  :: StaticContext
  -> CheckState
  -> DischargePolicy
  -> Obligation
  -> FocusedRequirement
  -> Either DischargeError ObligationDisposition
resolveExplicitThenArchitecture staticContext state policy obligation requirement =
  case Map.lookup obligationId' (explicitEvidenceBindings policy) of
    Just evidenceName -> do
      matches <- explicitEvidenceMatches
        staticContext state evidenceName (focusedCanonical requirement)
      if matches
        then Right (StaticallyDischarged (StaticByEvidence evidenceName))
        else Left
          (ExplicitEvidenceDoesNotMatch
            obligationId'
            evidenceName
            (focusedCanonical requirement))
    Nothing -> resolveArchitecture staticContext state policy obligation requirement
  where
    obligationId' = obligationId obligation

resolveArchitecture
  :: StaticContext
  -> CheckState
  -> DischargePolicy
  -> Obligation
  -> FocusedRequirement
  -> Either DischargeError ObligationDisposition
resolveArchitecture staticContext state policy obligation requirement =
  case Map.lookup obligationId' (runtimeBindings policy) of
    Just binding -> do
      validateRuntimeBinding staticContext state obligation requirement binding
      Right (RuntimeBound binding)
    Nothing ->
      case Map.lookup obligationId' (exportBindings policy) of
        Just binding -> do
          validateExportBinding staticContext state obligation requirement binding
          Right (Exported binding)
        Nothing -> Left (UnresolvedObligation obligationId' (focusedCanonical requirement))
  where
    obligationId' = obligationId obligation

resolveExportOnly
  :: StaticContext
  -> CheckState
  -> DischargePolicy
  -> Obligation
  -> FocusedRequirement
  -> Either DischargeError ObligationDisposition
resolveExportOnly staticContext state policy obligation requirement =
  case Map.lookup obligationId' (exportBindings policy) of
    Just binding -> do
      validateExportBinding staticContext state obligation requirement binding
      Right (Exported binding)
    Nothing -> Left (ExportedPrerequisiteBlocksLocalDischarge obligationId')
  where
    obligationId' = obligationId obligation

explicitEvidenceMatches
  :: StaticContext
  -> CheckState
  -> Name
  -> Proposition
  -> Either DischargeError Bool
explicitEvidenceMatches staticContext state evidenceName required = do
  (evidenceTy, _) <- mapLeft DischargeResourceError $
    useUnrestricted evidenceName (resourceContext state)
  candidates <- mapM canonicalize (bindingEvidencePropositions evidenceName evidenceTy)
  Right (required `elem` candidates)
  where
    canonicalize proposition =
      fst <$> mapLeft DischargeFocusingError
        (canonicalizeProposition staticContext state proposition)

validateRuntimeBinding
  :: StaticContext
  -> CheckState
  -> Obligation
  -> FocusedRequirement
  -> RuntimeBinding
  -> Either DischargeError ()
validateRuntimeBinding staticContext state obligation requirement binding = do
  let expectedId = obligationId obligation
      expectedPoint = obligationRequiredPoint obligation
      expectedProposition = focusedCanonical requirement
  if runtimeObligationId binding /= expectedId
    then Left (RuntimeBindingIdMismatch expectedId (runtimeObligationId binding))
    else Right ()
  if runtimeRequiredPoint binding /= expectedPoint
    then Left
      (RuntimeBindingRequiredPointMismatch
        expectedId expectedPoint (runtimeRequiredPoint binding))
    else Right ()
  actualBindingProposition <- canonicalize (runtimeProposition binding)
  if actualBindingProposition /= expectedProposition
    then Left
      (RuntimeBindingPropositionMismatch
        expectedId expectedProposition actualBindingProposition)
    else Right ()
  evidence <-
    case evidenceProposition (runtimeSuccessEvidence binding) of
      Just proposition -> Right proposition
      Nothing -> Left (RuntimeSuccessEvidenceNotProof expectedId (runtimeSuccessEvidence binding))
  actualEvidence <- canonicalize evidence
  if actualEvidence == expectedProposition
    then Right ()
    else Left
      (RuntimeSuccessEvidenceMismatch expectedId expectedProposition actualEvidence)
  where
    canonicalize proposition =
      fst <$> mapLeft DischargeFocusingError
        (canonicalizeProposition staticContext state proposition)

validateExportBinding
  :: StaticContext
  -> CheckState
  -> Obligation
  -> FocusedRequirement
  -> ExportBinding
  -> Either DischargeError ()
validateExportBinding staticContext state obligation requirement binding = do
  let expectedId = obligationId obligation
      expectedPoint = obligationRequiredPoint obligation
      expectedProposition = focusedCanonical requirement
  if exportObligationId binding /= expectedId
    then Left (ExportBindingIdMismatch expectedId (exportObligationId binding))
    else Right ()
  if exportRequiredPoint binding /= expectedPoint
    then Left
      (ExportBindingRequiredPointMismatch
        expectedId expectedPoint (exportRequiredPoint binding))
    else Right ()
  actualProposition <-
    fst <$> mapLeft DischargeFocusingError
      (canonicalizeProposition staticContext state (exportProposition binding))
  if actualProposition == expectedProposition
    then Right ()
    else Left
      (ExportBindingPropositionMismatch expectedId expectedProposition actualProposition)

collectEvidenceAssumptions
  :: StaticContext
  -> CheckState
  -> Either DischargeError [SolverAssumption]
collectEvidenceAssumptions staticContext state =
  fmap concat $ mapM collectBinding (Map.toAscList (unrestrictedBindings (resourceContext state)))
  where
    collectBinding (bindingName, ty) = do
      canonical <- mapM canonicalize (bindingEvidencePropositions bindingName ty)
      let facts = concatMap flattenConjunction canonical
      Right
        [ SolverAssumption (EvidenceFact bindingName index) proposition
        | (index, proposition) <- zip [1 ..] facts
        ]

    canonicalize proposition =
      fst <$> mapLeft DischargeFocusingError
        (canonicalizeProposition staticContext state proposition)

flattenConjunction :: Proposition -> [Proposition]
flattenConjunction proposition =
  case proposition of
    Conjunction left right -> flattenConjunction left ++ flattenConjunction right
    other -> [other]

subtractionChildObligation
  :: Obligation
  -> Int
  -> FocusedRequirement
  -> Obligation
subtractionChildObligation parent index requirement =
  Obligation
    { obligationId = ObligationId
        (unObligationId (obligationId parent)
          <> ".nat-sub."
          <> Text.pack (show index))
    , obligationProposition = focusedCanonical requirement
    , obligationOrigin = obligationOrigin parent
    , obligationScope = obligationScope parent
    , obligationRequiredPoint = obligationRequiredPoint parent
    }

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
