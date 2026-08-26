{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import qualified Data.ByteString as ByteString
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Phil.Assurance
import Phil.Core.Syntax (ObligationId (..))
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [sourcePath, compiledPath, outputPath] -> certifyWith certificationSpec sourcePath compiledPath outputPath
    _ -> hPutStrLn stderr "usage: CERTIFIER SOURCE.v COMPILED.vo OUTPUT.cert" >> exitFailure

certificationSpec :: RocqCertificationSpec
certificationSpec = RocqCertificationSpec
  { rocqSpecProfile = "phase1-callable-recursion"
  , rocqSpecObligation = ObligationId "PHIL-CALL-REC-001"
  , rocqSpecClaim = "Named self-recursive and mutually recursive callables are checked only through a stabilized public callable-contract environment. Declaration order is nonsemantic; current DefinitionRevision and current-body effect facts cannot alter or strengthen the recursive hypothesis; duplicate stable callable identities reject; unknown recursive targets reject; and recursive lookup succeeds only at the exact stabilized InterfaceRevision."
  , rocqSpecKind = "Stabilized recursive callable contracts and no implementation peeking"
  , rocqSpecOrigin = "src/Phil/Core/CallableRecursion.hs; test/Phase1CallableRecursionMain.hs; docs/phase-1/callable-recursion-v1.md; proof/Phil/Core/CallableRefinement.v; proof/Phil/Core/CallableRecursion.v"
  , rocqSpecScope = "Phase 1 CALL-013 named self/mutual recursion boundary"
  , rocqSpecRepresentation = "lists of named definitions, public callable projections, permutation-invariant stabilized lookup, exact interface revision gating, and private implementation fields erased from the recursive hypothesis"
  , rocqSpecSubjects = ["NamedCallableDefinition", "RecursiveCallableEnvironment", "CallableRefinementSurface", "InterfaceRevision"]
  , rocqSpecTheorems =
      [ "stabilization_exports_public_surface_only"
      , "private_implementation_facts_do_not_change_recursive_hypothesis"
      , "declaration_order_is_nonsemantic"
      , "accepted_group_has_unique_stable_names"
      , "adjacent_duplicate_stable_identity_rejects"
      , "recursive_lookup_uses_exact_stabilized_revision"
      , "stale_interface_revision_cannot_rebind"
      , "unknown_recursive_target_rejects"
      , "recursive_hypothesis_does_not_expose_private_revision"
      , "recursive_lookup_returns_public_callable_surface"
      ]
  , rocqSpecSourceRef = ArtifactRef "proof/Phil/Core/CallableRecursion.v"
  , rocqSpecCompiledRef = ArtifactRef "proof/Phil/Core/CallableRecursion.vo"
  , rocqSpecCertificateRef = ArtifactRef "certificate:rocq:PHIL-CALL-REC-001:v1"
  , rocqSpecEvidenceId = EvidenceEntryId "evidence.PHIL-CALL-REC-001.rocq.v1"
  , rocqSpecResidualBoundary = "The proof models the Haskell Map-normalized recursive environment extensionally as a public projection and uses the already-certified CALL-012 CallableRefinementSurface model. Rocq kernel/toolchain correctness and reviewed correspondence from NamedCallableKey/Text and InterfaceRevision identities, Haskell Map insertion/lookup and duplicate detection, declaration-order normalization, and the omission of DefinitionRevision/current-body summaries from RecursiveCallableEnvironment remain explicit trust boundaries. General termination/liveness, hidden restricted recursive closure environments (CALL-014), pre/postcondition refinement beyond the existing callable surface, foreign qualification, target lowering, and final source syntax remain outside this theorem family."
  }

certifyWith :: RocqCertificationSpec -> FilePath -> FilePath -> FilePath -> IO ()
certifyWith spec sourcePath compiledPath outputPath = do
  sourceBytes <- ByteString.readFile sourcePath
  compiledBytes <- ByteString.readFile compiledPath
  case certifyRocqProof spec sourceBytes compiledBytes of
    Left err -> hPutStrLn stderr ("Rocq certification failed: " <> show err) >> exitFailure
    Right bundle -> do
      let certificate = rocqBundleCertificate bundle
          artifact = rocqBundleCertificateArtifact bundle
          ObligationId obligation = rocqCertificateObligation certificate
      ByteString.writeFile outputPath (TextEncoding.encodeUtf8 (renderRocqProofCertificate certificate))
      putStrLn ("certified " <> Text.unpack obligation <> " as ProofAssistantTheorem evidence")
      putStrLn ("certificate artifact: " <> Text.unpack (unArtifactRef (artifactReference artifact)))
      putStrLn ("certificate sha256: " <> Text.unpack (unDigest (artifactDigest artifact)))
