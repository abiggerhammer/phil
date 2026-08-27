module Phil.Assurance.ProtocolGuard
  ( ProtocolGuardOrigin (..)
  , ProtocolTransitionGuard (..)
  , GuardedProtocolActionRequest (..)
  , ProtocolGuardError (..)
  , checkGuardedProtocolAction
  ) where

import qualified Data.Set as Set
import Phil.Assurance.Types
  ( AssuranceLedger
  , AssuranceManifest (..)
  , RevisionId
  , VerificationContext
  )
import Phil.Assurance.Verify
  ( ManifestError
  , verifyManifest
  )
import Phil.Core.Protocol
  ( CheckedProtocolStep
  , ProtocolActionRequest
  , ProtocolCheckError
  , ProtocolContext
  , checkProtocolAction
  )

-- | Guards stay layered: reusable protocol requirements are distinct from
-- architecture-specific strengthening, even though both are discharged through
-- the same assurance graph.
data ProtocolGuardOrigin
  = ProtocolDeclaredGuard
  | ArchitectureStrengtheningGuard
  deriving (Eq, Ord, Show)

-- | Exact assurance obligation required before one structurally available
-- protocol transition may be exercised.
data ProtocolTransitionGuard = ProtocolTransitionGuard
  { protocolGuardOrigin :: ProtocolGuardOrigin
  , protocolGuardRevision :: RevisionId
  }
  deriving (Eq, Ord, Show)

-- | A guarded action names the Core transition separately from the exact
-- assurance obligations that authorize it. A branch label or transition name is
-- never interpreted as proof of these obligations.
data GuardedProtocolActionRequest = GuardedProtocolActionRequest
  { guardedProtocolAction :: ProtocolActionRequest
  , guardedProtocolRequirements :: [ProtocolTransitionGuard]
  }
  deriving (Eq, Show)

data ProtocolGuardError
  = ProtocolGuardManifestError ManifestError
  | DuplicateProtocolTransitionGuard ProtocolTransitionGuard
  | MissingProtocolTransitionGuardRevision ProtocolTransitionGuard
  | ProtocolTransitionGuardNotCertified ProtocolTransitionGuard
  | ProtocolGuardCoreError ProtocolCheckError
  deriving (Eq, Show)

-- | Verify the assurance package first, then require every exact guard revision
-- to be present and certified before delegating to ordinary Core protocol
-- progression. Evidence truth/acceptance remains the assurance verifier's job;
-- this relation establishes exact identity and gating at the transition.
checkGuardedProtocolAction
  :: VerificationContext
  -> AssuranceLedger
  -> AssuranceManifest
  -> GuardedProtocolActionRequest
  -> ProtocolContext
  -> Either ProtocolGuardError CheckedProtocolStep
checkGuardedProtocolAction verification ledger manifest request context = do
  mapLeft ProtocolGuardManifestError (verifyManifest verification ledger manifest)
  guards <- normalizeGuards (guardedProtocolRequirements request)
  mapM_ requireGuard guards
  mapLeft ProtocolGuardCoreError
    (checkProtocolAction (guardedProtocolAction request) context)
  where
    requireGuard guard
      | not (Set.member revision (manifestObligationRevisions manifest)) =
          Left (MissingProtocolTransitionGuardRevision guard)
      | not (Set.member revision (manifestCertificationScope manifest)) =
          Left (ProtocolTransitionGuardNotCertified guard)
      | otherwise = Right ()
      where
        revision = protocolGuardRevision guard

normalizeGuards
  :: [ProtocolTransitionGuard]
  -> Either ProtocolGuardError [ProtocolTransitionGuard]
normalizeGuards = go Set.empty
  where
    go _ [] = Right []
    go seen (guard : rest)
      | Set.member guard seen = Left (DuplicateProtocolTransitionGuard guard)
      | otherwise = (guard :) <$> go (Set.insert guard seen) rest

mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f = either (Left . f) Right
