{-# LANGUAGE OverloadedStrings #-}

module Phil.Surface.Check.Types
  ( RejectionClass (..)
  , SurfaceCheckError (..)
  , FieldInfo (..)
  , SurfaceShape (..)
  , InitialBinding (..)
  , PrimitiveSemantics (..)
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

data SurfaceEnvironment = SurfaceEnvironment
  { surfaceStaticContext :: StaticContext
  , surfaceInitialBindings :: Map Text InitialBinding
  , surfacePrimitives :: Map Text PrimitiveSemantics
  , surfaceSelectRequirements :: Map Text [Proposition]
  , surfaceReceiveExactRequirement :: Maybe Proposition
  , surfaceTerminalAllowances :: Map Outcome (Set Text)
  , surfaceExpectedProvides :: Maybe Ty
  , surfaceLegacyReceiveFrameRaw :: Bool
  }
  deriving (Eq, Show)

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
  , surfaceSelectRequirements = Map.empty
  , surfaceReceiveExactRequirement = Nothing
  , surfaceTerminalAllowances = Map.empty
  , surfaceExpectedProvides = Nothing
  , surfaceLegacyReceiveFrameRaw = False
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
