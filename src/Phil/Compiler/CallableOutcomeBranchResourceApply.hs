{-# LANGUAGE OverloadedStrings #-}

module Phil.Compiler.CallableOutcomeBranchResourceApply
  ( applySurfaceCallableOutcomeResourceResidue
  ) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import Phil.Compiler.CallableOutcomeBranchResources
  ( SurfaceCallableOutcomeResourceExpectation (..)
  , SurfaceCallableOutcomeResourceResidueBinding (..)
  )
import Phil.Core.Syntax
  ( Mode (..)
  , Ty (..)
  )
import Phil.Surface.Check.Support
  ( insertBindingMeta
  , moveVariable
  , removeScopedBinding
  )
import Phil.Surface.Check.Types
  ( BindingMeta (..)
  , RejectionClass (..)
  , SurfaceCheckError (..)
  , SurfaceState (..)
  )
import Phil.Surface.Syntax
  ( Located (..)
  , SourceSpan
  )

-- | Apply one already-validated CALL-019 branch-local resource residue to the
-- Surface resource state at branch entry.
--
-- Only bindings named by the residue are changed. Unmentioned caller state is
-- preserved exactly. Existing restricted occurrences are consumed through the
-- ordinary Surface move path before a checked successor is installed; existing
-- unrestricted occurrences are removed through ordinary scoped-removal logic.
-- New/preserved occurrences are installed through 'insertBindingMeta', so the
-- normal Core structural zones remain authoritative.
applySurfaceCallableOutcomeResourceResidue
  :: SourceSpan
  -> SurfaceCallableOutcomeResourceResidueBinding
  -> SurfaceState
  -> Either SurfaceCheckError SurfaceState
applySurfaceCallableOutcomeResourceResidue span' residue initial = do
  next <- foldM applyOne initial
    (Map.toAscList (surfaceOutcomeResourceBindings residue))
  applyActiveEndpoint next
  where
    applyOne state (name, expectation) = case expectation of
      SurfaceCallableResourceAbsent -> removeExisting name state
      SurfaceCallableResourcePresent expected ->
        case Map.lookup name (stateBindings state) of
          Just actual | actual == expected -> Right state
          _ -> do
            cleared <- removeExisting name state
            insertBindingMeta span' name expected cleared

    removeExisting name state = case Map.lookup name (stateBindings state) of
      Nothing -> Right state
      Just meta -> case bindingMode meta of
        Unrestricted -> removeScopedBinding span' name state
        Affine -> snd <$> moveVariable (Located span' ()) name state
        Linear -> snd <$> moveVariable (Located span' ()) name state

    applyActiveEndpoint state = case surfaceOutcomeResourceActiveEndpoint residue of
      Nothing -> Right state { stateActiveEndpoint = Nothing }
      Just name -> case Map.lookup name (stateBindings state) of
        Just meta -> case bindingType meta of
          TyEndpoint _ -> Right state { stateActiveEndpoint = Just name }
          actual -> resourceError
            ("CALL-019 active endpoint residue names non-endpoint binding "
              <> name <> ": " <> Text.pack (show actual))
        Nothing -> resourceError
          ("CALL-019 active endpoint residue names absent binding " <> name)

    resourceError detail = Left SurfaceCheckError
      { surfaceErrorSpan = span'
      , surfaceErrorClass = IncompatibleBranchResidue
      , surfaceErrorDetail = detail
      }
