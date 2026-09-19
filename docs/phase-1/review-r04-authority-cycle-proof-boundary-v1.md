# PHIL-P1-REVIEW-R04 proof boundary

This slice certifies the Astra Review R04 repair as an explicit composition of two existing assurance authorities:

- PHIL-ASSURE-LINEAGE-001: revisionGeneratedFrom is provenance, not evidence authority; exact evidence must target the exact revision it establishes.
- PHIL-ASSURE-GRAPH-001: genuine evidence/obligation justification edges must form an acyclic graph, and recursive revisits reject rather than becoming proof.

The aggregate theorem therefore rules out the false cycle R04 identified: historical/generated prerequisite lineage cannot let ancestor evidence establish a distinct child conclusion, while a genuine two-way justification dependency cannot survive accepted graph verification.

The concrete Haskell correspondence remains Phil.Assurance.Verify plus app/LineageAuthorityProofCorrespondenceMain.hs. That fixture exercises:

- explicit in-scope obligation dependency success;
- generated prerequisite lineage with one-way justification success;
- genuine two-way justification-cycle rejection;
- lineage without child evidence rejection;
- missing lineage-parent rejection;
- exported historical ancestor success;
- exported historical ancestor as justification rejection; and
- explicit justification without lineage success.

Concrete IDs/digests, Data.Map/Data.Set traversal, diagnostic ordering, Rocq/GHC/toolchain correctness, and assurance-verifier implementation correspondence remain explicit boundaries.
