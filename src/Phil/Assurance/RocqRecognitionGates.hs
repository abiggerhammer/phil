{-# LANGUAGE OverloadedStrings #-}

module Phil.Assurance.RocqRecognitionGates
  ( recognitionGateCertificationSpecs
  ) where

import Data.Text (Text)
import qualified Data.Text as Text
import Phil.Assurance.Rocq (RocqCertificationSpec (..))
import Phil.Assurance.Types (ArtifactRef (..), EvidenceEntryId (..))
import Phil.Core.Syntax (ObligationId (..))

recognitionGateCertificationSpecs :: [RocqCertificationSpec]
recognitionGateCertificationSpecs = [gateSpec, refineSpec]

mkSpec :: Text -> Text -> Text -> [Text] -> Text -> RocqCertificationSpec
mkSpec profile obligation claim theorems residual =
  RocqCertificationSpec
    { rocqSpecProfile = profile
    , rocqSpecObligation = ObligationId obligation
    , rocqSpecClaim = claim
    , rocqSpecKind = "Core recognition ingress authority"
    , rocqSpecOrigin = "src/Phil/Core/Session.hs; src/Phil/Core/Recognition.hs; proof/Phil/Core/Recognition.v"
    , rocqSpecScope = "Phil.Core grammar-backed recognition ingress"
    , rocqSpecRepresentation = "proof-oriented grammar-relevant type projection and pending-recognition model"
    , rocqSpecSubjects = []
    , rocqSpecTheorems = theorems
    , rocqSpecSourceRef = ArtifactRef source
    , rocqSpecCompiledRef = ArtifactRef (Text.dropEnd 2 source <> ".vo")
    , rocqSpecCertificateRef = ArtifactRef ("certificate:rocq:" <> obligation <> ":v1")
    , rocqSpecEvidenceId = EvidenceEntryId ("evidence." <> obligation <> ".rocq.v1")
    , rocqSpecResidualBoundary = residual
    }
  where
    source = "proof/Phil/Core/Recognition.v"

gateSpec :: RocqCertificationSpec
gateSpec = mkSpec
  "core-recognition-gate"
  "PHIL-RECOG-GATE-001"
  "Raw session receive cannot advance a grammar-backed frame receive, and raw offer cannot advance a grammar-backed branch payload; such ingress must use the recognition path."
  [ "raw_receive_grammar_backed_rejected"
  , "raw_offer_grammar_payload_rejected"
  ]
  "General proof-side Ty remains opaque; the theorem uses a grammar-relevant ordinary/frame/refined projection. Parser/recognizer correctness itself remains outside this fail-closed routing theorem."

refineSpec :: RocqCertificationSpec
refineSpec = mkSpec
  "core-recognition-refine"
  "PHIL-RECOG-REFINE-001"
  "A grammar-backed frame hidden beneath TyRefined remains recognition-gated; the current receiveFrame path rejects it until refinement-value checking is implemented rather than accepting an unchecked value."
  [ "refined_grammar_receive_fails_closed"
  , "refined_grammar_raw_receive_still_rejected"
  ]
  "The proof models only the grammar-relevant projection of Ty. Current refined-frame rejection is a deliberate temporary boundary, not a permanent unsupported-feature claim."
