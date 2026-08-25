{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.Callable
  ( CaptureOccurrenceKey (..)
  , CaptureTransfer (..)
  , ClosureCapture (..)
  , ClosureCaptureSummary (..)
  , CalleeTransition (..)
  , SemanticEffect (..)
  , CallableContract (..)
  , CallableUse (..)
  , CallableCheckError (..)
  , checkClosureCaptures
  , closureStructuralMode
  , inferReachableCallableEffects
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Static (InterfaceRevision)
import Phil.Core.Syntax (Mode (..))

-- | Stable term-occurrence identity for one source value captured by a closure.
-- Source spelling and target environment slot are deliberately absent.
newtype CaptureOccurrenceKey = CaptureOccurrenceKey
  { unCaptureOccurrenceKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Whether closure construction copies an unrestricted value or transfers an
-- ownership occurrence into the sealed closure environment.
data CaptureTransfer
  = CopyCapture
  | MoveCapture
  deriving (Eq, Ord, Show)

-- | Canonical checker-facing capture description for the first Phase 1 slice.
data ClosureCapture = ClosureCapture
  { closureCaptureOccurrence :: CaptureOccurrenceKey
  , closureCaptureTransfer :: CaptureTransfer
  , closureCaptureStructuralMode :: Mode
  }
  deriving (Eq, Ord, Show)

-- | Normalized closure capture state. Restricted moves are listed explicitly so
-- the outer checker can remove those predecessor ownership occurrences.
data ClosureCaptureSummary = ClosureCaptureSummary
  { closureCapturesByOccurrence :: Map.Map CaptureOccurrenceKey ClosureCapture
  , closureMovedRestrictedOccurrences :: Set.Set CaptureOccurrenceKey
  , closureMinimumStructuralMode :: Mode
  }
  deriving (Eq, Ord, Show)

-- | Normative callee-transition distinctions from the callable contract. Only
-- PreserveCallee is exercised by CALL-001--005; the other constructors reserve
-- the semantic vocabulary for later resource-state slices.
data CalleeTransition
  = PreserveCallee
  | ConsumeCallee
  | ReplaceCallee InterfaceRevision
  deriving (Eq, Ord, Show)

newtype SemanticEffect = SemanticEffect
  { unSemanticEffect :: Text
  }
  deriving (Eq, Ord, Show)

-- | Bounded callable contract surface needed by the initial closure/effect
-- tranche. Effect bound is a may-effect upper bound for invocation.
data CallableContract = CallableContract
  { callableContractInterfaceRevision :: InterfaceRevision
  , callableContractCalleeTransition :: CalleeTransition
  , callableContractEffectBound :: Set.Set SemanticEffect
  }
  deriving (Eq, Ord, Show)

-- | Reachable higher-order operations observed by body checking. Possession,
-- forwarding, storage, and return carry no invocation effect by themselves.
data CallableUse
  = PossessCallable CallableContract
  | PassCallable CallableContract
  | StoreCallable CallableContract
  | ReturnCallable CallableContract
  | InvokeCallable CallableContract
  deriving (Eq, Ord, Show)

data CallableCheckError
  = RestrictedCaptureMustMove CaptureOccurrenceKey Mode
  | DuplicateRestrictedCapture CaptureOccurrenceKey Mode
  deriving (Eq, Ord, Show)

-- | Normalize closure capture ownership. Repeated unrestricted mentions collapse
-- to one canonical free-variable capture; affine/linear capture must be an exact
-- ownership move and may occur at most once.
checkClosureCaptures
  :: [ClosureCapture]
  -> Either CallableCheckError ClosureCaptureSummary
checkClosureCaptures captures = do
  normalized <- foldl addCapture (Right Map.empty) captures
  let movedRestricted = Set.fromList
        [ key
        | (key, capture) <- Map.toAscList normalized
        , closureCaptureTransfer capture == MoveCapture
        , closureCaptureStructuralMode capture /= Unrestricted
        ]
  Right ClosureCaptureSummary
    { closureCapturesByOccurrence = normalized
    , closureMovedRestrictedOccurrences = movedRestricted
    , closureMinimumStructuralMode = closureStructuralMode (Map.elems normalized)
    }
  where
    addCapture accumulated capture = do
      result <- accumulated
      let key = closureCaptureOccurrence capture
          mode = closureCaptureStructuralMode capture
      case mode of
        Unrestricted ->
          Right (Map.insertWith keepExisting key capture result)
        _
          | closureCaptureTransfer capture /= MoveCapture ->
              Left (RestrictedCaptureMustMove key mode)
          | Map.member key result ->
              Left (DuplicateRestrictedCapture key mode)
          | otherwise ->
              Right (Map.insert key capture result)

    keepExisting _new old = old

-- | Closure structural mode is the least upper bound of the modes of values it
-- owns: unrestricted < affine < linear.
closureStructuralMode :: [ClosureCapture] -> Mode
closureStructuralMode = foldl joinMode Unrestricted . map closureCaptureStructuralMode
  where
    joinMode Linear _ = Linear
    joinMode _ Linear = Linear
    joinMode Affine _ = Affine
    joinMode _ Affine = Affine
    joinMode Unrestricted Unrestricted = Unrestricted

-- | Infer effects from reachable checked callable uses. Merely possessing,
-- passing, storing, or returning a callable does not import its invocation
-- effects; an actual reachable invocation contributes the exact public bound.
inferReachableCallableEffects :: [CallableUse] -> Set.Set SemanticEffect
inferReachableCallableEffects = foldl addUse Set.empty
  where
    addUse effects use = case use of
      InvokeCallable contract -> Set.union effects (callableContractEffectBound contract)
      PossessCallable _ -> effects
      PassCallable _ -> effects
      StoreCallable _ -> effects
      ReturnCallable _ -> effects
