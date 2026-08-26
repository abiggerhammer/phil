{-# LANGUAGE OverloadedStrings #-}

module Phil.Core.CallableRecursion.Bound
  ( NamedCallableKey (..)
  , NamedCallableDefinition (..)
  , RecursiveCallableEnvironment (..)
  , RecursiveCallableError (..)
  , stabilizeRecursiveCallableGroup
  , lookupRecursiveCallableSurface
  ) where

import qualified CallableRecursionKernel as Kernel
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Phil.Core.Callable (CallableContract (..), SemanticEffect)
import Phil.Core.CallableRefinement (CallableRefinementSurface (..))
import Phil.Core.Static (DefinitionRevision, InterfaceRevision)

newtype NamedCallableKey = NamedCallableKey
  { unNamedCallableKey :: Text
  }
  deriving (Eq, Ord, Show)

data NamedCallableDefinition = NamedCallableDefinition
  { namedCallableKey :: NamedCallableKey
  , namedCallablePublicSurface :: CallableRefinementSurface
  , namedCallableDefinitionRevision :: DefinitionRevision
  , namedCallableCurrentBodyEffects :: Set.Set SemanticEffect
  }
  deriving (Eq, Ord, Show)

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
  | RecursiveCallableRepresentationBridgeMismatch Text
  deriving (Eq, Ord, Show)

stabilizeRecursiveCallableGroup
  :: [NamedCallableDefinition]
  -> Either RecursiveCallableError RecursiveCallableEnvironment
stabilizeRecursiveCallableGroup definitions =
  case Kernel.stabilizePublic
      (==)
      namedCallableKey
      namedCallablePublicSurface
      definitions of
    Nothing ->
      case firstDuplicate definitions of
        Just key -> Left (DuplicateNamedCallableDefinition key)
        Nothing -> bridgeMismatch
          "CALL-013 extracted decision disagreed with concrete duplicate diagnostics"
    Just projected -> acceptProjection projected
  where
    expectedProjection = map
      (\definition ->
        (namedCallableKey definition, namedCallablePublicSurface definition))
      definitions

    acceptProjection projected
      | projected /= expectedProjection = bridgeMismatch
          "CALL-013 extracted public projection disagreed with concrete projection"
      | Map.size result /= length projected = bridgeMismatch
          "CALL-013 accepted projection collapsed during Map construction"
      | Map.fromList (Map.toAscList result) /= result = bridgeMismatch
          "CALL-013 recursive environment Map round-trip changed the result"
      | otherwise = Right (RecursiveCallableEnvironment result)
      where
        result = Map.fromList projected

lookupRecursiveCallableSurface
  :: NamedCallableKey
  -> InterfaceRevision
  -> RecursiveCallableEnvironment
  -> Either RecursiveCallableError CallableRefinementSurface
lookupRecursiveCallableSurface key expectedRevision environment
  | Map.fromList entries /= surfaces = bridgeMismatch
      "CALL-013 recursive environment Map round-trip changed the input"
  | otherwise =
      case Kernel.decideRecursiveLookup (==) key revisionMatches entries of
        Kernel.RecursiveLookupAccepted surface ->
          case Map.lookup key surfaces of
            Nothing -> bridgeMismatch
              "CALL-013 extracted decision accepted a missing target"
            Just concrete
              | concrete /= surface -> bridgeMismatch
                  "CALL-013 extracted accepted surface disagreed with Map lookup"
              | surfaceRevision surface /= expectedRevision -> bridgeMismatch
                  "CALL-013 extracted acceptance disagreed with interface revision equality"
              | otherwise -> Right surface
        Kernel.RecursiveLookupUnknown ->
          case Map.lookup key surfaces of
            Nothing -> Left (UnknownRecursiveCallable key)
            Just _ -> bridgeMismatch
              "CALL-013 extracted unknown decision disagreed with Map lookup"
        Kernel.RecursiveLookupRevisionMismatch surface ->
          diagnoseRevisionMismatch surface
  where
    surfaces = recursiveCallableSurfaces environment
    entries = Map.toAscList surfaces
    revisionMatches surface = surfaceRevision surface == expectedRevision

    diagnoseRevisionMismatch surface =
      case Map.lookup key surfaces of
        Nothing -> bridgeMismatch
          "CALL-013 extracted revision mismatch named a missing target"
        Just concrete
          | concrete /= surface -> bridgeMismatch
              "CALL-013 extracted mismatch surface disagreed with Map lookup"
          | actualRevision == expectedRevision -> bridgeMismatch
              "CALL-013 extracted revision mismatch disagreed with revision equality"
          | otherwise -> Left (RecursiveCallableInterfaceRevisionMismatch
              key
              expectedRevision
              actualRevision)
          where
            actualRevision = surfaceRevision surface

surfaceRevision :: CallableRefinementSurface -> InterfaceRevision
surfaceRevision = callableContractInterfaceRevision . callableRefinementContract

firstDuplicate :: [NamedCallableDefinition] -> Maybe NamedCallableKey
firstDuplicate = go Set.empty
  where
    go _ [] = Nothing
    go seen (definition : rest)
      | Set.member key seen = Just key
      | otherwise = go (Set.insert key seen) rest
      where
        key = namedCallableKey definition

bridgeMismatch :: Text -> Either RecursiveCallableError a
bridgeMismatch = Left . RecursiveCallableRepresentationBridgeMismatch
