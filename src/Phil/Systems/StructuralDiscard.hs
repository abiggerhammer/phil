{-# LANGUAGE OverloadedStrings #-}

module Phil.Systems.StructuralDiscard
  ( StructuralDiscardTrace (..)
  , TargetStructuralDiscard (..)
  , CheckedStructuralDiscard (..)
  , StructuralDiscardError (..)
  , renderStructuralDiscardTrace
  , checkStructuralDiscardCorrespondence
  ) where

import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Types (Digest)
import Phil.Core.Callable (SemanticEffect)
import Phil.Core.Syntax (Mode (..))
import Phil.Systems.IR (StageContract (..))

-- | Exact source semantic event for EXEC-010. Structural discard is permitted
-- only for affine or unrestricted bindings. It is a disposition fact, not an
-- invocation of a destructor, provider, release operation, or finalizer.
data StructuralDiscardTrace = StructuralDiscardTrace
  { structuralDiscardStageContractId :: Text
  , structuralDiscardSourceDigest :: Digest
  , structuralDiscardTargetDigest :: Digest
  , structuralDiscardBinding :: Text
  , structuralDiscardMode :: Mode
  }
  deriving (Eq, Show)

-- | Target projection of one structural discard. Physical reclamation is kept
-- deliberately separate from source-visible semantic consequences: a backend
-- may forget a register, stack slot, GC root, or allocation when otherwise
-- justified, but it may not smuggle effects, failures, or resource transitions
-- into the Phil discard operation.
data TargetStructuralDiscard = TargetStructuralDiscard
  { targetStructuralDiscardBinding :: Text
  , targetStructuralDiscardMode :: Mode
  , targetStructuralDiscardSemanticEffects :: Set.Set SemanticEffect
  , targetStructuralDiscardFailures :: Set.Set Text
  , targetStructuralDiscardResourceTransitions :: Set.Set Text
  , targetStructuralDiscardPhysicalReclamation :: Set.Set Text
  }
  deriving (Eq, Show)

data CheckedStructuralDiscard = CheckedStructuralDiscard
  { checkedStructuralDiscardTrace :: StructuralDiscardTrace
  , checkedStructuralDiscardTarget :: TargetStructuralDiscard
  }
  deriving (Eq, Show)

data StructuralDiscardError
  = StructuralDiscardStageContractIdMismatch Text Text
  | StructuralDiscardSourceDigestMismatch Digest Digest
  | StructuralDiscardTargetDigestMismatch Digest Digest
  | StructuralDiscardLinearBinding Text
  | StructuralDiscardBindingMismatch Text Text
  | StructuralDiscardModeMismatch Mode Mode
  | StructuralDiscardHiddenSemanticEffects (Set.Set SemanticEffect)
  | StructuralDiscardHiddenFailures (Set.Set Text)
  | StructuralDiscardHiddenResourceTransitions (Set.Set Text)
  | StructuralDiscardMissingTraceRelation Text
  deriving (Eq, Show)

renderStructuralDiscardTrace :: StructuralDiscardTrace -> Text
renderStructuralDiscardTrace trace = Text.intercalate "|"
  [ "exec010.structural-discard.v1"
  , structuralDiscardStageContractId trace
  , structuralDiscardBinding trace
  , renderMode (structuralDiscardMode trace)
  ]

-- | Check one source structural discard against its target realization and the
-- exact StageContract that binds the source/target artifacts.
--
-- The decisive negative rule is intentionally strict: semantic effects,
-- caller-visible failures, and resource transitions must all be empty. Those
-- behaviors remain available only through explicit source operations such as
-- the already-checked resource-specific `release` transition (EXEC-014).
-- Nonsemantic physical reclamation is retained only as inspection/accounting
-- data and is not promoted into Phil semantics.
checkStructuralDiscardCorrespondence
  :: StageContract
  -> StructuralDiscardTrace
  -> TargetStructuralDiscard
  -> Either StructuralDiscardError CheckedStructuralDiscard
checkStructuralDiscardCorrespondence contract trace target = do
  requireEqual
    StructuralDiscardStageContractIdMismatch
    (structuralDiscardStageContractId trace)
    (stageContractId contract)
  requireEqual
    StructuralDiscardSourceDigestMismatch
    (structuralDiscardSourceDigest trace)
    (stageSourceArtifactDigest contract)
  requireEqual
    StructuralDiscardTargetDigestMismatch
    (structuralDiscardTargetDigest trace)
    (stageTargetArtifactDigest contract)
  case structuralDiscardMode trace of
    Linear -> Left (StructuralDiscardLinearBinding (structuralDiscardBinding trace))
    Affine -> Right ()
    Unrestricted -> Right ()
  requireEqual
    StructuralDiscardBindingMismatch
    (structuralDiscardBinding trace)
    (targetStructuralDiscardBinding target)
  requireEqual
    StructuralDiscardModeMismatch
    (structuralDiscardMode trace)
    (targetStructuralDiscardMode target)
  if Set.null (targetStructuralDiscardSemanticEffects target)
    then Right ()
    else Left
      (StructuralDiscardHiddenSemanticEffects
        (targetStructuralDiscardSemanticEffects target))
  if Set.null (targetStructuralDiscardFailures target)
    then Right ()
    else Left (StructuralDiscardHiddenFailures (targetStructuralDiscardFailures target))
  if Set.null (targetStructuralDiscardResourceTransitions target)
    then Right ()
    else Left
      (StructuralDiscardHiddenResourceTransitions
        (targetStructuralDiscardResourceTransitions target))
  let relation = renderStructuralDiscardTrace trace
  if relation `elem` stageTraceRelation contract
    then Right CheckedStructuralDiscard
      { checkedStructuralDiscardTrace = trace
      , checkedStructuralDiscardTarget = target
      }
    else Left (StructuralDiscardMissingTraceRelation relation)

renderMode :: Mode -> Text
renderMode mode = case mode of
  Linear -> "linear"
  Affine -> "affine"
  Unrestricted -> "unrestricted"

requireEqual :: Eq a => (a -> a -> e) -> a -> a -> Either e ()
requireEqual mismatch expected actual
  | expected == actual = Right ()
  | otherwise = Left (mismatch expected actual)
