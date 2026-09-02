From Stdlib Require Import Lists.List Strings.String.

From Phil.Surface Require Import Grammar GrammarDeterminacyCertificate.

Open Scope string_scope.

(*
  Checked binding facts for the generated Grammar-v1 overlap certificate.

  The generated certificate is derived from the canonical EBNF rather than from
  the reviewed JSON inventory.  These facts establish exact source binding and
  current cardinality only.  The successor proof must still mechanize the
  completeness bridge from Grammar.v to this certificate, construct one
  admissible resolver oracle for every certified site, and prove every ordinary
  complete derivation is resolved by that oracle.
*)

Theorem phase1_surface_determinacy_certificate_source_exact :
  phase1_surface_determinacy_certificate_source_sha256 =
  phase1_surface_grammar_source_sha256.
Proof.
  reflexivity.
Qed.

Theorem phase1_surface_determinacy_certificate_has_exact_reviewed_cardinality :
  List.length phase1_surface_determinacy_certificate = 15.
Proof.
  reflexivity.
Qed.
