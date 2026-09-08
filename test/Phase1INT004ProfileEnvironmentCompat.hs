{-# LANGUAGE OverloadedStrings #-}

module Phase1INT004ProfileEnvironmentCompat
  ( phase0ProfileEnvironment
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Surface.Check (SurfaceEnvironment)
import Phil.Surface.Phase0 (phase0EnvironmentFor)

-- | Transitional INT-004 compatibility boundary. Portable fixture manifests
-- select an environment by a stable profile identifier; this adapter alone
-- translates that identifier to the frozen Phase-0 fixture environment table.
-- The caller never supplies or derives an environment from the fixture path.
-- A later INT-004 slice will replace this compatibility adapter with portable
-- environment materialization.
phase0ProfileEnvironment :: Text -> Either Text SurfaceEnvironment
phase0ProfileEnvironment profile =
  case profile of
    "phase0.simple-receive" -> legacy "01-reuse-consumed-endpoint.phil"
    "phase0.wrong-order" -> legacy "03-wrong-protocol-order.phil"
    "phase0.nonexhaustive-offer" -> legacy "04-nonexhaustive-offer.phil"
    "phase0.legacy-raw" -> legacy "05-raw-field-access.phil"
    "phase0.parsed-validation-bypass" -> legacy "06-parsed-used-as-validated.phil"
    "phase0.unrelated-length" -> legacy "07-unrelated-payload-length.phil"
    "phase0.incompatible-join" -> legacy "08-incompatible-branch-join.phil"
    "phase0.failure-reuse" -> legacy "09-continue-after-fatal-recognition-failure.phil"
    "phase0.premature-acceptance" -> legacy "10-accept-before-digest-check.phil"
    "phase0.common" -> legacy "11-copy-authority-capability.phil"
    "phase0.pending-commit" -> legacy "13-commit-unrelated-parsed.phil"
    "phase0.pending-drop" -> legacy "15-drop-pending-receive.phil"
    "phase0.stale-policy" -> legacy "17-use-evidence-wrong-context.phil"
    "phase0.opaque-proof" -> legacy "18-prove-opaque-digest.phil"
    "phase0.label-proof" -> legacy "19-label-does-not-transfer-proof.phil"
    _ -> Left ("unknown Phase-0 environment profile: " <> profile)
  where
    legacy name = phase0EnvironmentFor ("examples/rejected/" <> Text.unpack name)
