{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.CallableRecursion
  ( NamedCallableKey (..)
  , NamedCallableDefinition (..)
  , RecursiveCallableEnvironment (..)
  , RecursiveCallableError (..)
  , stabilizeRecursiveCallableGroup
  , lookupRecursiveCallableSurface
  ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Callable (CallableContract (..), SemanticEffect)
import Phil.Core.CallableRefinement (CallableRefinementSurface (..))
import Phil.Core.Static (DefinitionRevision, InterfaceRevision)

-- | Stable identity of a named callable inside one checked recursive group.
newtype NamedCallableKey = NamedCallableKey
  { unNamedCallableKey :: Text
  }
  deriving (Eq, Ord, Show)

-- | Full checker input for a named callable definition. Current-body facts are
-- intentionally present here so stabilization can prove that they are *not*
-- exported into the recursive hypothesis.
data NamedCallableDefinition = NamedCallableDefinition
  { namedCallableKey :: NamedCallableKey
  , namedCallablePublicSurface :: CallableRefinementSurface
  , namedCallableDefinitionRevision :: DefinitionRevision
  , namedCallableCurrentBodyEffects :: Set.Set SemanticEffect
  }
  deriving (Eq, Ord, Show)

-- | The recursive hypothesis contains public callable contracts only. Definition
-- revisions and current-body summaries are deliberately absent.
newtype RecursiveCallableEnvironment = RecursiveCallableEnvironment
  { recursiveCallableSurfaces
      :: Map.Map NamedCallableKey CallableRefinementSurface
  }
  deriving (Eq, Ord, Show)

data RecursiveCallableError
  = DuplicateNamedCallableDefinition NamedCallableKey
  | UnknownRecursiveCallable NamedCallableKey
  | RecursiveCallableInterfaceRevisionMismatch
      NamedCallableKey
      InterfaceRevision
      InterfaceRevision
  deriving (Eq, Ord, Show)

-- | Stabilize the entire recursive group before any body is checked. The result
-- is canonical under declaration order and contains only public contract facts.
stabilizeRecursiveCallableGroup
  :: [NamedCallableDefinition]
  -> Either RecursiveCallableError RecursiveCallableEnvironment
stabilizeRecursiveCallableGroup definitions =
  RecursiveCallableEnvironment <$> go Map.empty definitions
  where
    go result [] = Right result
    go result (definition : rest)
      | Map.member key result = Left (DuplicateNamedCallableDefinition key)
      | otherwise = go
          (Map.insert key (namedCallablePublicSurface definition) result)
          rest
      where
        key = namedCallableKey definition

-- | Resolve a recursive call against the exact stabilized public interface.
-- Callers receive the public surface and cannot observe the target definition
-- revision or narrower current-body behavior through this environment.
lookupRecursiveCallableSurface
  :: NamedCallableKey
  -> InterfaceRevision
  -> RecursiveCallableEnvironment
  -> Either RecursiveCallableError CallableRefinementSurface
lookupRecursiveCallableSurface key expectedRevision environment = do
  surface <- maybe
    (Left (UnknownRecursiveCallable key))
    Right
    (Map.lookup key (recursiveCallableSurfaces environment))
  let actualRevision = callableContractInterfaceRevision
        (callableRefinementContract surface)
  if actualRevision == expectedRevision
    then Right surface
    else Left (RecursiveCallableInterfaceRevisionMismatch
      key
      expectedRevision
      actualRevision)
