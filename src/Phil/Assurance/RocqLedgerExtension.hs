{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.RocqLedgerExtension
  ( ledgerExtensionCertificationSpec
  ) where

import Phil.Assurance.Rocq (RocqCertificationSpec (..))
import Phil.Assurance.Types
import Phil.Core.Syntax (ObligationId (..))

ledgerExtensionCertificationSpec :: RocqCertificationSpec
ledgerExtensionCertificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "assurance-ledger-extension"
  , rocqSpecObligation = ObligationId "PHIL-ASSURE-LEDGER-EXT-001"
  , rocqSpecClaim =
      "Append-only assurance-ledger extension is compositional. Preservation of existing nodes is reflexive and transitive for each ledger map, so LedgerExtension is a preorder; every finite chain of verified adjacent extensions collapses to a verified ancestor-to-descendant extension and preserves every ancestor node. Pairwise verification remains essential: a direct root-to-tip extension check alone does not protect nodes first introduced at an intermediate stage."
  , rocqSpecKind = "Assurance append-only ledger extension algebra"
  , rocqSpecOrigin =
      "src/Phil/Assurance/Verify.hs; proof/Phil/Assurance/EvidenceUse.v; proof/Phil/Assurance/LedgerExtension.v"
  , rocqSpecScope =
      "Phil.Assurance.Verify.verifyLedgerExtension / append-only AssuranceLedger history"
  , rocqSpecRepresentation =
      "five-map immutable-node preservation relation and finite verified-extension chain"
  , rocqSpecSubjects =
      [ "ledgerRevisions"
      , "ledgerEvidence"
      , "ledgerAssumptions"
      , "ledgerExports"
      , "ledgerUses"
      , "LedgerExtensionChain"
      ]
  , rocqSpecTheorems =
      [ "preserves_map_reflexive"
      , "preserves_map_transitive"
      , "ledger_extension_reflexive"
      , "ledger_extension_transitive"
      , "ledger_extension_is_preorder"
      , "ledger_extension_chain_collapses"
      , "verified_extension_chain_preserves_every_ancestor_node"
      , "root_to_tip_extension_does_not_imply_intermediate_preservation"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Assurance/LedgerExtension.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Assurance/LedgerExtension.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-ASSURE-LEDGER-EXT-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-ASSURE-LEDGER-EXT-001.rocq.v1"
  , rocqSpecResidualBoundary =
      "Rocq kernel/toolchain correctness plus reviewed correspondence from Haskell Data.Map key/value equality and Phil.Assurance.Verify.verifyLedgerExtension's five preserve traversals to the normalized LedgerView model remain explicit trust boundaries. The theorem proves immutable logical history composition; durable storage, serialization, process concurrency, and atomic publication of ledger states are not proved here."
  }
