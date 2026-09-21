From Stdlib Require Import Bool.Bool.

Set Implicit Arguments.

(*
  PHIL-AUD-DIGEST-SUBJECT-001 — Surface validator-subject correspondence.

  The production Surface checker establishes concrete source/type/shape facts
  natively. This normalized decision owns only the ordered admissibility
  checks and, critically, carries the exact checked Begin subject and exact
  stable byte-owner value through successful admission.

  The view spelling is deliberately absent from this model. A renamed borrowed
  view therefore cannot change the evidence subject, while a different stable
  owner remains a different carried subject.
*)

Inductive SurfaceDigestSubjectDecision
  (BeginSubject StableOwner : Type) : Type :=
| SurfaceDigestSubjectAccepted
    (acceptedBeginSubject : BeginSubject)
    (acceptedStableOwner : StableOwner)
| SurfaceDigestExplicitContextRejected
| SurfaceDigestArityRejected
| SurfaceDigestBeginNameRejected
| SurfaceDigestBeginTypeRejected
| SurfaceDigestPayloadBorrowRejected
| SurfaceDigestStableOwnerRejected
| SurfaceDigestPayloadTypeRejected.

Arguments SurfaceDigestSubjectAccepted
  {BeginSubject StableOwner} _ _.
Arguments SurfaceDigestExplicitContextRejected
  {BeginSubject StableOwner}.
Arguments SurfaceDigestArityRejected
  {BeginSubject StableOwner}.
Arguments SurfaceDigestBeginNameRejected
  {BeginSubject StableOwner}.
Arguments SurfaceDigestBeginTypeRejected
  {BeginSubject StableOwner}.
Arguments SurfaceDigestPayloadBorrowRejected
  {BeginSubject StableOwner}.
Arguments SurfaceDigestStableOwnerRejected
  {BeginSubject StableOwner}.
Arguments SurfaceDigestPayloadTypeRejected
  {BeginSubject StableOwner}.

Definition decideSurfaceDigestSubjectByFacts
  {BeginSubject StableOwner : Type}
  (noExplicitContext
   exactArity
   beginNamed
   beginIsBegin
   payloadBorrowed
   stableOwnerPresent
   payloadIsSharedBytes : bool)
  (beginSubject : BeginSubject)
  (stableOwner : StableOwner)
  : SurfaceDigestSubjectDecision BeginSubject StableOwner :=
  if noExplicitContext then
    if exactArity then
      if beginNamed then
        if beginIsBegin then
          if payloadBorrowed then
            if stableOwnerPresent then
              if payloadIsSharedBytes then
                SurfaceDigestSubjectAccepted beginSubject stableOwner
              else SurfaceDigestPayloadTypeRejected
            else SurfaceDigestStableOwnerRejected
          else SurfaceDigestPayloadBorrowRejected
        else SurfaceDigestBeginTypeRejected
      else SurfaceDigestBeginNameRejected
    else SurfaceDigestArityRejected
  else SurfaceDigestExplicitContextRejected.

Theorem surface_digest_subject_accepts_iff_all_facts :
  forall
    (BeginSubject StableOwner : Type)
    noExplicitContext exactArity beginNamed beginIsBegin
    payloadBorrowed stableOwnerPresent payloadIsSharedBytes
    (beginSubject : BeginSubject)
    (stableOwner : StableOwner),
    decideSurfaceDigestSubjectByFacts
      noExplicitContext exactArity beginNamed beginIsBegin
      payloadBorrowed stableOwnerPresent payloadIsSharedBytes
      beginSubject stableOwner =
      SurfaceDigestSubjectAccepted beginSubject stableOwner <->
    noExplicitContext = true /\
    exactArity = true /\
    beginNamed = true /\
    beginIsBegin = true /\
    payloadBorrowed = true /\
    stableOwnerPresent = true /\
    payloadIsSharedBytes = true.
Proof.
  intros BeginSubject StableOwner
    noExplicitContext exactArity beginNamed beginIsBegin
    payloadBorrowed stableOwnerPresent payloadIsSharedBytes
    beginSubject stableOwner.
  destruct noExplicitContext, exactArity, beginNamed, beginIsBegin,
           payloadBorrowed, stableOwnerPresent, payloadIsSharedBytes;
    cbn; intuition discriminate.
Qed.

Theorem accepted_surface_digest_subject_carries_exact_inputs :
  forall
    (BeginSubject StableOwner : Type)
    noExplicitContext exactArity beginNamed beginIsBegin
    payloadBorrowed stableOwnerPresent payloadIsSharedBytes
    (beginSubject acceptedBegin : BeginSubject)
    (stableOwner acceptedStable : StableOwner),
    decideSurfaceDigestSubjectByFacts
      noExplicitContext exactArity beginNamed beginIsBegin
      payloadBorrowed stableOwnerPresent payloadIsSharedBytes
      beginSubject stableOwner =
      SurfaceDigestSubjectAccepted acceptedBegin acceptedStable ->
    acceptedBegin = beginSubject /\
    acceptedStable = stableOwner /\
    noExplicitContext = true /\
    exactArity = true /\
    beginNamed = true /\
    beginIsBegin = true /\
    payloadBorrowed = true /\
    stableOwnerPresent = true /\
    payloadIsSharedBytes = true.
Proof.
  intros BeginSubject StableOwner
    noExplicitContext exactArity beginNamed beginIsBegin
    payloadBorrowed stableOwnerPresent payloadIsSharedBytes
    beginSubject acceptedBegin stableOwner acceptedStable Haccepted.
  destruct noExplicitContext, exactArity, beginNamed, beginIsBegin,
           payloadBorrowed, stableOwnerPresent, payloadIsSharedBytes;
    cbn in Haccepted; try discriminate.
  inversion Haccepted; subst.
  repeat split; reflexivity.
Qed.

Theorem accepted_surface_digest_subject_preserves_distinct_owners :
  forall
    (BeginSubject StableOwner : Type)
    noExplicitContext exactArity beginNamed beginIsBegin
    payloadBorrowed stableOwnerPresent payloadIsSharedBytes
    (beginSubject : BeginSubject)
    (leftOwner rightOwner leftAccepted rightAccepted : StableOwner),
    leftOwner <> rightOwner ->
    decideSurfaceDigestSubjectByFacts
      noExplicitContext exactArity beginNamed beginIsBegin
      payloadBorrowed stableOwnerPresent payloadIsSharedBytes
      beginSubject leftOwner =
      SurfaceDigestSubjectAccepted beginSubject leftAccepted ->
    decideSurfaceDigestSubjectByFacts
      noExplicitContext exactArity beginNamed beginIsBegin
      payloadBorrowed stableOwnerPresent payloadIsSharedBytes
      beginSubject rightOwner =
      SurfaceDigestSubjectAccepted beginSubject rightAccepted ->
    leftAccepted <> rightAccepted.
Proof.
  intros BeginSubject StableOwner
    noExplicitContext exactArity beginNamed beginIsBegin
    payloadBorrowed stableOwnerPresent payloadIsSharedBytes
    beginSubject leftOwner rightOwner leftAccepted rightAccepted
    Hdistinct Hleft Hright Hequal.
  destruct noExplicitContext, exactArity, beginNamed, beginIsBegin,
           payloadBorrowed, stableOwnerPresent, payloadIsSharedBytes;
    cbn in Hleft, Hright; try discriminate.
  injection Hleft as HleftOwner.
  injection Hright as HrightOwner.
  apply Hdistinct.
  rewrite HleftOwner, HrightOwner.
  exact Hequal.
Qed.

Theorem digest_subject_explicit_context_rejects_first :
  forall
    (BeginSubject StableOwner : Type)
    exactArity beginNamed beginIsBegin payloadBorrowed
    stableOwnerPresent payloadIsSharedBytes
    (beginSubject : BeginSubject)
    (stableOwner : StableOwner),
    decideSurfaceDigestSubjectByFacts
      false exactArity beginNamed beginIsBegin
      payloadBorrowed stableOwnerPresent payloadIsSharedBytes
      beginSubject stableOwner =
      SurfaceDigestExplicitContextRejected.
Proof. reflexivity. Qed.

Theorem digest_subject_wrong_arity_rejects_second :
  forall
    (BeginSubject StableOwner : Type)
    beginNamed beginIsBegin payloadBorrowed stableOwnerPresent
    payloadIsSharedBytes
    (beginSubject : BeginSubject)
    (stableOwner : StableOwner),
    decideSurfaceDigestSubjectByFacts
      true false beginNamed beginIsBegin
      payloadBorrowed stableOwnerPresent payloadIsSharedBytes
      beginSubject stableOwner =
      SurfaceDigestArityRejected.
Proof. reflexivity. Qed.

Theorem digest_subject_unnamed_begin_rejects_third :
  forall
    (BeginSubject StableOwner : Type)
    beginIsBegin payloadBorrowed stableOwnerPresent payloadIsSharedBytes
    (beginSubject : BeginSubject)
    (stableOwner : StableOwner),
    decideSurfaceDigestSubjectByFacts
      true true false beginIsBegin
      payloadBorrowed stableOwnerPresent payloadIsSharedBytes
      beginSubject stableOwner =
      SurfaceDigestBeginNameRejected.
Proof. reflexivity. Qed.

Theorem digest_subject_wrong_begin_type_rejects_fourth :
  forall
    (BeginSubject StableOwner : Type)
    payloadBorrowed stableOwnerPresent payloadIsSharedBytes
    (beginSubject : BeginSubject)
    (stableOwner : StableOwner),
    decideSurfaceDigestSubjectByFacts
      true true true false
      payloadBorrowed stableOwnerPresent payloadIsSharedBytes
      beginSubject stableOwner =
      SurfaceDigestBeginTypeRejected.
Proof. reflexivity. Qed.

Theorem digest_subject_nonborrowed_payload_rejects_fifth :
  forall
    (BeginSubject StableOwner : Type)
    stableOwnerPresent payloadIsSharedBytes
    (beginSubject : BeginSubject)
    (stableOwner : StableOwner),
    decideSurfaceDigestSubjectByFacts
      true true true true
      false stableOwnerPresent payloadIsSharedBytes
      beginSubject stableOwner =
      SurfaceDigestPayloadBorrowRejected.
Proof. reflexivity. Qed.

Theorem digest_subject_missing_stable_owner_rejects_sixth :
  forall
    (BeginSubject StableOwner : Type)
    payloadIsSharedBytes
    (beginSubject : BeginSubject)
    (stableOwner : StableOwner),
    decideSurfaceDigestSubjectByFacts
      true true true true
      true false payloadIsSharedBytes
      beginSubject stableOwner =
      SurfaceDigestStableOwnerRejected.
Proof. reflexivity. Qed.

Theorem digest_subject_wrong_payload_type_rejects_seventh :
  forall
    (BeginSubject StableOwner : Type)
    (beginSubject : BeginSubject)
    (stableOwner : StableOwner),
    decideSurfaceDigestSubjectByFacts
      true true true true
      true true false
      beginSubject stableOwner =
      SurfaceDigestPayloadTypeRejected.
Proof. reflexivity. Qed.
