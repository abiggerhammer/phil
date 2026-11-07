From Stdlib Require Import Strings.String Bool.Bool Lists.List Arith.PeanoNat.
From Phil.Core Require Import Syntax Context.
From Phil.Surface Require Import
  SurfaceObservationWire SurfaceBinderNameEncoding
  SurfaceBorrowLoanStateCorrespondence.

Import ListNotations.
Open Scope string_scope.

(*
  FSEM-01: bounded two-owner finite-context frame bridge.
  CONTEXT2-V1 is a distinct wire; CONTEXT-V1 and OBS-V1 are untouched.

  An independently checked source fragment yields each owner identity, but
  composing them into one Core.ResourceContext is a *Core test*, not a claim
  that a two-owner source program is recognized or elaborated by Phil.
  This Rocq model has extensional Context lookups and an opaque Ty carrier.
  No arbitrary Unicode/Text, Haskell Map/Set implementation, source evaluator,
  SHA-256, or universal source-to-Rocq refinement theorem is claimed.
*)

Definition context2Header : string := "PHIL-FSEM01-CONTEXT2-V1|".

Record TwoOwnerArtifact : Type := mkTwoOwnerArtifact {
  primarySourceHash : string;
  spectatorSourceHash : string;
  primaryRootHex : string;
  spectatorRootHex : string;
  primaryNameHex : string;
  spectatorNameHex : string;
  twoOwnerStates : string;
  twoOwnerOutcome : string
}.

Definition twoOwnerFields (a : TwoOwnerArtifact) : list string :=
  [primarySourceHash a; spectatorSourceHash a;
   primaryRootHex a; spectatorRootHex a;
   primaryNameHex a; spectatorNameHex a;
   twoOwnerStates a; twoOwnerOutcome a].

Lemma two_owner_fields_length :
  forall a, List.length (twoOwnerFields a) = 8.
Proof.
  intros [? ? ? ? ? ? ? ?].
  reflexivity.
Qed.

Definition stateOfFields (values : list string) : option TwoOwnerArtifact :=
  match values with
  | [h1; h2; r1; r2; n1; n2; states; outcome] =>
      Some (mkTwoOwnerArtifact h1 h2 r1 r2 n1 n2 states outcome)
  | _ => None
  end.

Lemma state_of_fields_roundtrip :
  forall a, stateOfFields (twoOwnerFields a) = Some a.
Proof.
  intros [? ? ? ? ? ? ? ?].
  reflexivity.
Qed.

(* Role-ordered finite maps: the complete linear domain is exactly the
   primary owner and spectator, both Bytes8, until primary consumption.
   The spectator remains present even after the primary's return.
   Unrestricted/affine are empty at these post-prune checkpoints. *)
Definition twoOwnerWord
  (phase owner spectator : string)
  (primaryPresent loaned : bool) : string :=
  phase ++ "/-/-/" ++
    (if primaryPresent then owner ++ "=Bytes8;" else "") ++
    spectator ++ "=Bytes8/" ++
    (if loaned then owner else "-").

Definition acceptedTwoOwnerStates (owner spectator : string) : string :=
  String.concat "," [
    twoOwnerWord "B" owner spectator true false;
    twoOwnerWord "S" owner spectator true true;
    twoOwnerWord "N" owner spectator true true;
    twoOwnerWord "C" owner spectator true false;
    twoOwnerWord "R" owner spectator false false].

Definition rejectedTwoOwnerStates (owner spectator : string) : string :=
  String.concat "," [
    twoOwnerWord "B" owner spectator true false;
    twoOwnerWord "S" owner spectator true true;
    twoOwnerWord "E" owner spectator true true;
    twoOwnerWord "X" owner spectator true true].

Definition sourceHashForm (hash : string) : bool :=
  Nat.eqb (String.length hash) 64 &&
    SurfaceObservationWire.isLowerHex hash.

Definition validTwoOwnerArtifact (a : TwoOwnerArtifact) : bool :=
  sourceHashForm (primarySourceHash a) &&
  sourceHashForm (spectatorSourceHash a) &&
  SurfaceObservationWire.canonicalHex (primaryRootHex a) &&
  SurfaceObservationWire.canonicalHex (spectatorRootHex a) &&
  SurfaceObservationWire.canonicalHex (primaryNameHex a) &&
  SurfaceObservationWire.canonicalHex (spectatorNameHex a) &&
  negb (String.eqb (primaryNameHex a) (spectatorNameHex a)) &&
  ((String.eqb (twoOwnerStates a)
       (acceptedTwoOwnerStates (primaryNameHex a) (spectatorNameHex a)) &&
     String.eqb (twoOwnerOutcome a) "OK:Bytes8") ||
   (String.eqb (twoOwnerStates a)
       (rejectedTwoOwnerStates (primaryNameHex a) (spectatorNameHex a)) &&
     String.eqb (twoOwnerOutcome a)
       "ERR:BorrowEscape:shared view escapes its lexical scope")).

Definition encodeTwoOwner (a : TwoOwnerArtifact) : string :=
  context2Header ++
    SurfaceObservationWire.packFieldsWithTail (twoOwnerFields a) "".

Definition decodeTwoOwner (wire : string) : option TwoOwnerArtifact :=
  match SurfaceBinderNameEncoding.stripPrefix context2Header wire with
  | None => None
  | Some payload =>
      match SurfaceObservationWire.parseFields 8 payload with
      | Some (fields, EmptyString) =>
          match stateOfFields fields with
          | Some a => if validTwoOwnerArtifact a then Some a else None
          | None => None
          end
      | _ => None
      end
  end.

Theorem decode_encode_valid_two_owner :
  forall a, validTwoOwnerArtifact a = true ->
    decodeTwoOwner (encodeTwoOwner a) = Some a.
Proof.
  intros a Hvalid.
  unfold decodeTwoOwner, encodeTwoOwner.
  rewrite SurfaceBinderNameEncoding.strip_prefix_self.
  rewrite <- (two_owner_fields_length a).
  rewrite (SurfaceObservationWire.parse_pack_fields (twoOwnerFields a) "").
  rewrite state_of_fields_roundtrip.
  now rewrite Hvalid.
Qed.

Theorem decode_two_owner_is_valid :
  forall wire a, decodeTwoOwner wire = Some a ->
    validTwoOwnerArtifact a = true.
Proof.
  intros wire a Hdecoded.
  unfold decodeTwoOwner in Hdecoded.
  destruct (SurfaceBinderNameEncoding.stripPrefix context2Header wire)
    as [payload|]; try discriminate.
  destruct (SurfaceObservationWire.parseFields 8 payload)
    as [[fields trailing]|]; try discriminate.
  destruct trailing; try discriminate.
  destruct (stateOfFields fields) as [record|] eqn:Hrecord;
    try discriminate.
  destruct (validTwoOwnerArtifact record) eqn:Hvalid;
    inversion Hdecoded; subst; assumption.
Qed.

Theorem rejects_unknown_context2_version :
  forall a,
    decodeTwoOwner ("PHIL-FSEM01-CONTEXT2-V2|" ++
      SurfaceObservationWire.packFieldsWithTail (twoOwnerFields a) "") = None.
Proof.
  intros a; reflexivity.
Qed.

(* Extensional two-owner model; these are COMPLETE resource functions for
   the represented finite domain. The two roles must have distinct Names. *)
Definition noBindings : Context.BindingMap := fun _ => None.
Definition noLoans : Context.LoanSet := fun _ => false.

Definition twoOwnerContext
  (owner spectator : Syntax.Name)
  (ownerTy spectatorTy : Syntax.Ty) : Context.ResourceContext :=
  Context.mkResourceContext noBindings noBindings
    (fun query =>
      if String.eqb query owner then Some ownerTy
      else if String.eqb query spectator then Some spectatorTy
      else None)
    noLoans.

Theorem primary_present_in_two_owner_context :
  forall owner spectator ty1 ty2,
    Context.linearBindings (twoOwnerContext owner spectator ty1 ty2)
      owner = Some ty1.
Proof.
  intros; unfold twoOwnerContext; simpl.
  now rewrite String.eqb_refl.
Qed.

Theorem spectator_present_in_two_owner_context :
  forall owner spectator ty1 ty2,
    String.eqb spectator owner = false ->
    Context.linearBindings (twoOwnerContext owner spectator ty1 ty2)
      spectator = Some ty2.
Proof.
  intros owner spectator ty1 ty2 Hdiff.
  unfold twoOwnerContext; simpl.
  now rewrite Hdiff, String.eqb_refl.
Qed.

Theorem foreign_binding_and_loan_absent :
  forall owner spectator ty1 ty2 candidate,
    String.eqb candidate owner = false ->
    String.eqb candidate spectator = false ->
    Context.linearBindings (twoOwnerContext owner spectator ty1 ty2)
      candidate = None /\
    Context.sharedLoans (twoOwnerContext owner spectator ty1 ty2)
      candidate = false.
Proof.
  intros owner spectator ty1 ty2 candidate Howner Hspectator.
  unfold twoOwnerContext; simpl.
  rewrite Howner, Hspectator.
  split; reflexivity.
Qed.

Theorem other_owner_is_preserved_by_loan_start :
  forall owner other ctx started,
    String.eqb other owner = false ->
    SurfaceBorrowLoanStateCorrespondence.startLinearSharedLoan owner ctx =
      Some started ->
    Context.linearBindings started other =
      Context.linearBindings ctx other /\
    Context.sharedLoans started other = Context.sharedLoans ctx other.
Proof.
  intros owner other ctx started Hdiff Hstart.
  unfold SurfaceBorrowLoanStateCorrespondence.startLinearSharedLoan in Hstart.
  destruct (Context.sharedLoans ctx owner) eqn:Hloan; try discriminate.
  destruct (Context.linearBindings ctx owner) as [ty|] eqn:Hty;
    try discriminate.
  inversion Hstart; subst started; clear Hstart.
  split.
  - reflexivity.
  - apply SurfaceBorrowLoanStateCorrespondence.set_core_loan_preserves_other_names.
    exact Hdiff.
Qed.

Theorem other_owner_is_preserved_by_loan_end :
  forall owner other ctx ended,
    String.eqb other owner = false ->
    SurfaceBorrowLoanStateCorrespondence.endLinearSharedLoan owner ctx =
      Some ended ->
    Context.linearBindings ended other =
      Context.linearBindings ctx other /\
    Context.sharedLoans ended other = Context.sharedLoans ctx other.
Proof.
  intros owner other ctx ended Hdiff Hend.
  unfold SurfaceBorrowLoanStateCorrespondence.endLinearSharedLoan in Hend.
  destruct (Context.sharedLoans ctx owner) eqn:Hloan; try discriminate.
  inversion Hend; subst ended; clear Hend.
  split.
  - reflexivity.
  - apply SurfaceBorrowLoanStateCorrespondence.set_core_loan_preserves_other_names.
    exact Hdiff.
Qed.

Theorem other_owner_is_preserved_by_linear_consumption :
  forall owner other ctx returned ty,
    String.eqb other owner = false ->
    Context.consumeLinear owner ctx = Context.Consumed ty returned ->
    Context.linearBindings returned other =
      Context.linearBindings ctx other /\
    Context.sharedLoans returned other = Context.sharedLoans ctx other.
Proof.
  intros owner other ctx returned ty Hdiff Hconsume.
  pose proof
    (Context.consumeLinear_success_exact owner ctx returned ty Hconsume)
    as [_ [_ [Hpreserve [_ [_ Hloans]]]]].
  split.
  - apply Hpreserve; exact Hdiff.
  - rewrite Hloans; reflexivity.
Qed.

Theorem two_owner_start_exact :
  forall owner spectator ownerTy spectatorTy,
    SurfaceBorrowLoanStateCorrespondence.startLinearSharedLoan owner
      (twoOwnerContext owner spectator ownerTy spectatorTy) =
    Some (SurfaceBorrowLoanStateCorrespondence.setCoreLoan owner true
      (twoOwnerContext owner spectator ownerTy spectatorTy)).
Proof.
  intros.
  unfold SurfaceBorrowLoanStateCorrespondence.startLinearSharedLoan,
    twoOwnerContext; simpl.
  rewrite String.eqb_refl.
  reflexivity.
Qed.

Theorem two_owner_loan_start_preserves_spectator :
  forall owner spectator ownerTy spectatorTy,
    String.eqb spectator owner = false ->
    Context.linearBindings
      (SurfaceBorrowLoanStateCorrespondence.setCoreLoan owner true
        (twoOwnerContext owner spectator ownerTy spectatorTy))
      spectator = Some spectatorTy /\
    Context.sharedLoans
      (SurfaceBorrowLoanStateCorrespondence.setCoreLoan owner true
        (twoOwnerContext owner spectator ownerTy spectatorTy))
      spectator = false /\
    Context.sharedLoans
      (SurfaceBorrowLoanStateCorrespondence.setCoreLoan owner true
        (twoOwnerContext owner spectator ownerTy spectatorTy))
      owner = true.
Proof.
  intros owner spectator ownerTy spectatorTy Hdiff.
  split.
  - change (Context.linearBindings
      (twoOwnerContext owner spectator ownerTy spectatorTy)
      spectator = Some spectatorTy).
    apply spectator_present_in_two_owner_context.
    exact Hdiff.
  - split.
    + rewrite (SurfaceBorrowLoanStateCorrespondence.set_core_loan_preserves_other_names
        owner spectator true
        (twoOwnerContext owner spectator ownerTy spectatorTy) Hdiff).
      reflexivity.
    + apply SurfaceBorrowLoanStateCorrespondence.set_core_loan_has_exact_target.
Qed.

Theorem two_owner_borrowed_primary_cannot_be_consumed :
  forall owner spectator ownerTy spectatorTy,
    Context.consumeLinear owner
      (SurfaceBorrowLoanStateCorrespondence.setCoreLoan owner true
        (twoOwnerContext owner spectator ownerTy spectatorTy)) =
    Context.ConsumeError (Context.OwnerBorrowed owner).
Proof.
  intros.
  eapply SurfaceBorrowLoanStateCorrespondence.started_linear_loan_blocks_owner_consumption
    with (context := twoOwnerContext owner spectator ownerTy spectatorTy).
  apply two_owner_start_exact.
Qed.

(* Remaining boundary: the new source evidence is compiled into source-rooted
   exact names and independently reconstructed Core states by a Haskell test.
   These Rocq frame theorems hold for the extensional Context model, not all
   production Map/Set values or a verified two-owner source evaluator. *)
