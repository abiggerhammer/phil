module Phil.Surface.Check.LoopControl
  ( LoopControlKind (..)
  , LoopControlSyntax (..)
  , LoopControlContract (..)
  , LoopControlError (..)
  , elaborateLoopControl
  ) where

import Data.Text (Text)

data LoopControlKind
  = ContinueControl
  | BreakControl
  deriving (Eq, Ord, Show)

data LoopControlSyntax a
  = BareLoopControl
  | EmptyLoopControl
  | ExplicitLoopControl [a]
  deriving (Eq, Ord, Show)

data LoopControlContract = LoopControlContract
  { loopSuccessorSlots :: [Text]
  , loopExitSlots :: [Text]
  }
  deriving (Eq, Ord, Show)

data LoopControlError
  = LoopControlArityMismatch LoopControlKind Int Int
  deriving (Eq, Ord, Show)

-- | Grammar-v1 bare and empty-parenthesized loop control carry exactly zero
-- explicit actuals. They never capture currently scoped loop-state binders.
-- Ordinary LoopContract/state projection checking consumes the returned actuals.
elaborateLoopControl
  :: LoopControlKind
  -> LoopControlContract
  -> LoopControlSyntax a
  -> Either LoopControlError [a]
elaborateLoopControl kind contract syntax =
  if actualArity == expectedArity
    then Right actuals
    else Left (LoopControlArityMismatch kind expectedArity actualArity)
  where
    actuals = case syntax of
      BareLoopControl -> []
      EmptyLoopControl -> []
      ExplicitLoopControl values -> values
    actualArity = length actuals
    expectedArity = case kind of
      ContinueControl -> length (loopSuccessorSlots contract)
      BreakControl -> length (loopExitSlots contract)
