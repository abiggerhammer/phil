From Stdlib Require Import Extraction.
From Phil.Surface Require Import DigestSubjectCorrespondence.

Extraction Language Haskell.

Extract Inductive bool =>
  "Prelude.Bool" ["Prelude.True" "Prelude.False"].

Extraction "SurfaceDigestSubjectKernel"
  decideSurfaceDigestSubjectByFacts.
