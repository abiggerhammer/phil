{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.Check.Types
  ( RejectionClass (..)
  , SurfaceCheckError (..)
  , FieldInfo (..)
  , SurfaceShape (..)
  , InitialBinding (..)
  , PrimitiveSemantics (..)
  , ReleaseRequirement (..)
  , ReleaseSemanticAccount (..)
  , ReleaseTransitionOutcome (..)
  , ReleaseResidue (..)
  , ReleaseTransitionContract (..)
  , ReleaseSelectionError (..)
  , selectReleaseTransition
  , SurfaceEnvironment (..)
  , SurfaceCheckResult (..)
  , emptySurfaceEnvironment
  , BindingMeta (..)
  , SurfaceState (..)
  , ScalarValue (..)
  , RuntimeValue (..)
  , PathControl (..)
  , SurfacePath (..)
  , DecisionKind (..)
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Checker (CheckState)
import Phil.Core.Recognition
  ( ParsedWitness
  , PendingRawView
  , RecognitionFailure
  )
import Phil.Core.Static (StaticContext)
import Phil.Core.Syntax
  ( Control
  , FrameId
  , GrammarId
  , Mode (..)
  , Name
  , Outcome
  , Proposition
  , RefSort
  , RefTerm
  , Ty
  )
import Phil.Core.Value
  ( EqualityBoundary (DefinitionallyEqual)
  , compareTypes
  )
import Phil.Surface.Syntax (SourceSpan)

data RejectionClass
  = StructuralUse
  | LinearCompletion
  | SessionAction
  | BranchExhaustiveness
  | IllegalProjection
  | MissingEvidence
  | ExplicitTransport
  | IncompatibleBranchResidue
  | ControlAfterTerminal
  | RecognitionProvenance
  | BorrowEscape
  | OpaqueProof
  | UncheckedArithmetic
  | UnknownPrimitive
  | TypeMismatch
  | ReleaseCompetence
  deriving (Eq, Ord, Show)

data SurfaceCheckError = SurfaceCheckError
  { surfaceErrorSpan :: SourceSpan
  , surfaceErrorClass :: RejectionClass
  , surfaceErrorDetail :: Text
  }
  deriving (Eq, Show)

data FieldInfo = FieldInfo
  { fieldType :: Ty
  , fieldSort :: RefSort
  , fieldAlias :: Maybe RefTerm
  }
  deriving (Eq, Show)

data SurfaceShape
  = PlainShape
  | RecordShape Text (Map Text FieldInfo)
  | OwnedBytesShape RefTerm
  | PendingRawShape PendingRawView
  | LegacyRawShape GrammarId FrameId
  | BorrowedViewShape Name
  | ParsedShape ParsedWitness Text
  | LegacyParsedShape GrammarId FrameId Text
  | ExternalParsedShape Text FrameId
  | RecognitionFailureShape RecognitionFailure
  | LegacyRecognitionFailureShape GrammarId FrameId
  | FixtureRawShape FrameId
  | DecisionShape DecisionKind
  | UncheckedArithmeticShape
  | ForgedParsedShape
  deriving (Eq, Show)

data InitialBinding = InitialBinding
  { initialMode :: Mode
  , initialType :: Ty
  , initialShape :: SurfaceShape
  }
  deriving (Eq, Show)

data PrimitiveSemantics
  = PrimitiveSupportedVersions
  | PrimitiveSha256
  | PrimitiveShouldCancel
  | PrimitiveChooseSupported
  | PrimitiveStore
  | PrimitiveFixtureBytes
  | PrimitiveUncheckedU32Add
  | PrimitiveNewCancellationScope
  | PrimitiveAllocateLinearBuffer
  | PrimitiveRecordUploadId
  | PrimitiveConsumeBeginPolicyEvidence
  | PrimitiveUse
  | PrimitiveInspect
  | PrimitiveAuthorizeStore
  | PrimitiveDelegate
  | PrimitiveContinueCommonState
  | PrimitiveHandlePayload
  deriving (Eq, Ord, Show)

-- | Exact prerequisites established by the competent resource/callable/provider
-- layer before the surface `release` shorthand may select a transition.
data ReleaseRequirement
  = ReleaseAuthorityRequirement Text
  | ReleaseEvidenceRequirement Text
  | ReleaseAssumptionRequirement Text
  deriving (Eq, Ord, Show)

-- | Semantic dimensions of the selected resource-specific release operation.
-- These stay attached to the transition even when the source shorthand has a
-- Unit-valued continuing result.
data ReleaseSemanticAccount = ReleaseSemanticAccount
  { releaseAccountAuthorityRefs :: Set Text
  , releaseAccountEvidenceRefs :: Set Text
  , releaseAccountEffectRefs :: Set Text
  , releaseAccountAssumptionRefs :: Set Text
  , releaseAccountCostRefs :: Set Text
  , releaseAccountSubjectRef :: Text
  }
  deriving (Eq, Show)

-- | A single deterministic release outcome can be represented by the shorthand.
-- A branch-sensitive operation must be called explicitly instead.
data ReleaseTransitionOutcome
  = ReleaseContinuesUnit
  | ReleaseTerminates Outcome
  | ReleaseFails Text Text
  | ReleaseBranchSensitive [Outcome]
  deriving (Eq, Show)

-- | `release e` consumes the owner. A transition that replaces it with a live
-- successor cannot be faithfully hidden behind Unit-valued release sugar.
data ReleaseResidue
  = ReleaseConsumesOwner
  | ReleaseReplacesOwner Ty
  deriving (Eq, Show)

data ReleaseTransitionContract = ReleaseTransitionContract
  { releaseTransitionKey :: Text
  , releaseTransitionOwnerType :: Ty
  , releaseTransitionRequirements :: Set ReleaseRequirement
  , releaseTransitionSemanticAccount :: ReleaseSemanticAccount
  , releaseTransitionOutcome :: ReleaseTransitionOutcome
  , releaseTransitionResidue :: ReleaseResidue
  }
  deriving (Eq, Show)

data ReleaseSelectionError
  = NoApplicableReleaseTransition Ty
  | AmbiguousReleaseTransitions Ty [Text]
  | UnsatisfiedReleaseRequirements Text (Set ReleaseRequirement)
  | ReleaseReplacementRequiresExplicitOperation Text Ty
  | ReleaseBranchSensitiveRequiresExplicitOperation Text [Outcome]
  deriving (Eq, Show)

data SurfaceEnvironment = SurfaceEnvironment
  { surfaceStaticContext :: StaticContext
  , surfaceInitialBindings :: Map Text InitialBinding
  , surfacePrimitives :: Map Text PrimitiveSemantics
  , surfaceTypeAliases :: Map Text Ty
  , surfaceSelectRequirements :: Map Text [Proposition]
  , surfaceReceiveExactRequirement :: Maybe Proposition
  , surfaceTerminalAllowances :: Map Outcome (Set Text)
  , surfaceExpectedProvides :: Maybe Ty
  , surfaceLegacyReceiveFrameRaw :: Bool
  , surfaceReleaseTransitions :: [ReleaseTransitionContract]
  , surfaceSatisfiedReleaseRequirements :: Set ReleaseRequirement
  }
  deriving (Eq, Show)

-- | Select exactly one already-checked release transition applicable to the
-- owner's exact semantic type. This function deliberately does not inspect the
-- owner's structural mode: mode controls use-count discipline, not disposal
-- competence. The exact contract object is returned unchanged so authority,
-- evidence, effects, assumptions, subject residue, outcome and cost metadata
-- cannot be replaced by a generic "drop" fact.
selectReleaseTransition
  :: SurfaceEnvironment
  -> Ty
  -> Either ReleaseSelectionError ReleaseTransitionContract
selectReleaseTransition environment ownerType =
  case applicable of
    [] -> Left (NoApplicableReleaseTransition ownerType)
    [transition] -> validate transition
    transitions -> Left (AmbiguousReleaseTransitions ownerType
      (map releaseTransitionKey transitions))
  where
    applicable = filter
      (\transition ->
        compareTypes ownerType (releaseTransitionOwnerType transition)
          == DefinitionallyEqual)
      (surfaceReleaseTransitions environment)

    validate transition
      | not (Set.null missingRequirements) =
          Left (UnsatisfiedReleaseRequirements
            (releaseTransitionKey transition)
            missingRequirements)
      | ReleaseReplacesOwner successor <- releaseTransitionResidue transition =
          Left (ReleaseReplacementRequiresExplicitOperation
            (releaseTransitionKey transition)
            successor)
      | ReleaseBranchSensitive outcomes <- releaseTransitionOutcome transition =
          Left (ReleaseBranchSensitiveRequiresExplicitOperation
            (releaseTransitionKey transition)
            outcomes)
      | otherwise = Right transition
      where
        missingRequirements = Set.difference
          (releaseTransitionRequirements transition)
          (surfaceSatisfiedReleaseRequirements environment)

data SurfaceCheckResult = SurfaceCheckResult
  { checkedComponentName :: Text
  , checkedTerminalControls :: [Control]
  }
  deriving (Eq, Show)

emptySurfaceEnvironment :: StaticContext -> SurfaceEnvironment
emptySurfaceEnvironment staticContext = SurfaceEnvironment
  { surfaceStaticContext = staticContext
  , surfaceInitialBindings = Map.empty
  , surfacePrimitives = Map.empty
  , surfaceTypeAliases = Map.empty
  , surfaceSelectRequirements = Map.empty
  , surfaceReceiveExactRequirement = Nothing
  , surfaceTerminalAllowances = Map.empty
  , surfaceExpectedProvides = Nothing
  , surfaceLegacyReceiveFrameRaw = False
  , surfaceReleaseTransitions = []
  , surfaceSatisfiedReleaseRequirements = Set.empty
  }

data BindingMeta = BindingMeta
  { bindingMode :: Mode
  , bindingType :: Ty
  , bindingShape :: SurfaceShape
  }
  deriving (Eq, Show)

data SurfaceState = SurfaceState
  { stateCore :: CheckState
  , stateBindings :: Map Text BindingMeta
  , stateFresh :: Int
  , stateFrame :: Int
  , stateActiveEndpoint :: Maybe Text
  }
  deriving (Eq, Show)

data ScalarValue = ScalarValue
  { scalarMode :: Mode
  , scalarType :: Ty
  , scalarShape :: SurfaceShape
  }
  deriving (Eq, Show)

data RuntimeValue
  = RuntimeScalar ScalarValue
  | RuntimeTuple [RuntimeValue]
  | RuntimeUnit
  deriving (Eq, Show)

data PathControl
  = PathContinue
  | PathReturn Ty
  | PathClosed Outcome
  | PathFailed Text Text
  deriving (Eq, Show)

data SurfacePath = SurfacePath
  { pathControl :: PathControl
  , pathState :: SurfaceState
  , pathValue :: Maybe RuntimeValue
  }
  deriving (Eq, Show)

data DecisionKind
  = BooleanDecision
  | ChooseSupportedDecision
  | RecognitionDecision ParsedWitness RecognitionFailure Text
  | LegacyRecognitionDecision GrammarId FrameId Text
  | ValidationDecision Text Name Name
  | DigestDecision Proposition
  | StoreDecision
  deriving (Eq, Show)
