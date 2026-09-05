From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import Grammar GrammarDeterminacyCertificate.

Import ListNotations.
Open Scope string_scope.

(*
  Checked binding facts for the generated Grammar-v1 overlap certificate.

  The generated certificate is derived from the canonical EBNF rather than from
  the reviewed JSON inventory.  This file establishes exact source binding and
  that the generated certificate is inhabited.  Exact completeness/cardinality
  relative to the machine-computed grammar overlap set is proved separately in
  GrammarDeterminacyFollowOverlap.v, so this binding does not hard-code the
  current number of reviewed sites.
*)

Theorem phase1_surface_determinacy_certificate_source_exact :
  phase1_surface_determinacy_certificate_source_sha256 =
  phase1_surface_grammar_source_sha256.
Proof.
  reflexivity.
Qed.

Theorem phase1_surface_determinacy_certificate_has_reviewed_sites :
  phase1_surface_determinacy_certificate <> [].
Proof.
  discriminate.
Qed.
