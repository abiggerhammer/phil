From Stdlib Require Import Strings.String Bool.Bool Lists.List Arith.PeanoNat.
From Phil.Core Require Import Syntax Context.
From Phil.Surface Require Import
  SurfaceObservationWire SurfaceBinderNameEncoding
  SurfaceBorrowLoanStateCorrespondence SurfaceCheckerStateObservation
  SurfaceRepresentedBorrowTrace.

Import ListNotations.
Open Scope string_scope.

(*
  FSEM-01 CONTEXT-V1: an independently decoded, bounded resource-context
  carrier. Production emits the exact four finite collections from its
  traced Core.ResourceContext: unrestricted, affine, linear, shared loans.

  The actual checkpoints occur after lexical-scoped SharedBytes view cleanup;
  they require empty unrestricted and affine maps, one Bytes[8] linear owner
  before consumption, and no foreign loan. Temporary insertion is tested
  separately against Core.Context operations, not implied by a checkpoint. The phase is an independent field; membership is not
  computed from it by the Haskell exporter.

  This proof models checked finite membership extensionally in Core.Context.
  It DOES NOT prove that all Haskell maps, all engine transitions, Unicode
  Name encodings, or arbitrary source programs refine this Rocq model.
*)

Definition contextHeader : string := "PHIL-FSEM01-CONTEXT-V1|".

Record StateArtifact : Type := mkStateArtifact {
  stateHash : string;
  stateRootHex : string;
  stateOwnerHex : string;
  stateViewHex : string;
  stateWords : string;
  stateOutcome : string
}.

Definition fieldsOfState (a : StateArtifact) : list string :=
  [stateHash a; stateRootHex a; stateOwnerHex a; stateViewHex a;
   stateWords a; stateOutcome a].

Lemma state_fields_length :
  forall a, List.length (fieldsOfState a) = 6.
Proof. intros [hash root owner view words outcome]; reflexivity. Qed.

Definition stateOfFields (fields : list string) : option StateArtifact :=
  match fields with
  | [hash; root; owner; view; states; outcome] =>
      Some (mkStateArtifact hash root owner view states outcome)
  | _ => None
  end.

Lemma state_fields_roundtrip :
  forall a, stateOfFields (fieldsOfState a) = Some a.
Proof. intros [? ? ? ? ? ?]; reflexivity. Qed.

(* Every collection is represented, in fixed U/A/L/loan order.
   Empty collections use "-", and an admitted linear map entry includes
   the exact owner name bytes and the type tag, rather than a presence bit. *)
Definition stateWord
  (phase owner : string) (linearPresent loanActive : bool) : string :=
  phase ++ "/-/-/" ++
    (if linearPresent then owner ++ "=Bytes8" else "-") ++ "/" ++
    (if loanActive then owner else "-").

Definition acceptedStates (owner : string) : string :=
  String.concat "," [
    stateWord "B" owner true false;
    stateWord "S" owner true true;
    stateWord "N" owner true true;
    stateWord "C" owner true false;
    stateWord "R" owner false false].

Definition escapeStates (owner : string) : string :=
  String.concat "," [
    stateWord "B" owner true false;
    stateWord "S" owner true true;
    stateWord "E" owner true true;
    stateWord "X" owner true true].

Definition validState (a : StateArtifact) : bool :=
  (Nat.eqb (String.length (stateHash a)) 64 &&
   SurfaceObservationWire.isLowerHex (stateHash a)) &&
  SurfaceObservationWire.canonicalHex (stateRootHex a) &&
  SurfaceObservationWire.canonicalHex (stateOwnerHex a) &&
  SurfaceObservationWire.canonicalHex (stateViewHex a) &&
  ((String.eqb (stateWords a) (acceptedStates (stateOwnerHex a)) &&
    String.eqb (stateOutcome a) "OK:Bytes8") ||
   (String.eqb (stateWords a) (escapeStates (stateOwnerHex a)) &&
    String.eqb (stateOutcome a)
      "ERR:BorrowEscape:shared view escapes its lexical scope")).

Definition encodeState (a : StateArtifact) : string :=
  contextHeader ++
    SurfaceObservationWire.packFieldsWithTail (fieldsOfState a) "".

Definition decodeState (raw : string) : option StateArtifact :=
  match SurfaceBinderNameEncoding.stripPrefix contextHeader raw with
  | None => None
  | Some contents =>
      match SurfaceObservationWire.parseFields 6 contents with
      | Some (fields, EmptyString) =>
          match stateOfFields fields with
          | Some a => if validState a then Some a else None
          | None => None
          end
      | _ => None
      end
  end.

Theorem decode_encode_valid_state :
  forall a, validState a = true ->
    decodeState (encodeState a) = Some a.
Proof.
  intros a Hvalid.
  unfold decodeState, encodeState.
  rewrite SurfaceBinderNameEncoding.strip_prefix_self.
  rewrite <- (state_fields_length a).
  rewrite (SurfaceObservationWire.parse_pack_fields (fieldsOfState a) "").
  rewrite state_fields_roundtrip.
  now rewrite Hvalid.
Qed.

Theorem decoded_state_is_valid :
  forall raw a, decodeState raw = Some a -> validState a = true.
Proof.
  intros raw a Hdecoded.
  unfold decodeState in Hdecoded.
  destruct (SurfaceBinderNameEncoding.stripPrefix contextHeader raw)
    as [payload|]; try discriminate.
  destruct (SurfaceObservationWire.parseFields 6 payload)
    as [[fields trailing]|]; try discriminate.
  destruct trailing; try discriminate.
  destruct (stateOfFields fields) as [record|] eqn:Hrecord;
    try discriminate.
  destruct (validState record) eqn:Hvalid;
    inversion Hdecoded; subst; assumption.
Qed.

(* This relation is an explicit, independently checked provenance and
   observation join to the earlier OBS-V1 artifact. It does not establish
   SHA256 collision resistance or UTF-8 decoding correctness. *)
Definition bindsObservation
  (state : StateArtifact) (obs : SurfaceObservationWire.Artifact) : bool :=
  SurfaceObservationWire.validArtifact obs &&
  String.eqb (stateHash state) (SurfaceObservationWire.sourceHash obs) &&
  String.eqb (stateRootHex state)
    (SurfaceObservationWire.declarationRootHex obs) &&
  String.eqb (stateOwnerHex state) (SurfaceObservationWire.ownerNameHex obs) &&
  String.eqb (stateViewHex state) (SurfaceObservationWire.viewNameHex obs) &&
  String.eqb (stateOutcome state) (SurfaceObservationWire.terminalCode obs) &&
  ((String.eqb (stateWords state) (acceptedStates (stateOwnerHex state)) &&
    String.eqb (SurfaceObservationWire.traceCodes obs)
      "B10,S11,N11,C10,R00") ||
   (String.eqb (stateWords state) (escapeStates (stateOwnerHex state)) &&
    String.eqb (SurfaceObservationWire.traceCodes obs) "B10,S11,E11,X11")).

Theorem bound_evidence_preserves_source_hash :
  forall state obs,
    bindsObservation state obs = true ->
    stateHash state = SurfaceObservationWire.sourceHash obs.
Proof.
  intros state obs H.
  unfold bindsObservation in H.
  repeat rewrite Bool.andb_true_iff in H.
  apply String.eqb_eq.
  tauto.
Qed.

(* Reconstruct the Rocq Context lookups from the admitted finite
   resource state, with actual owner/loan membership as INPUTS.
   Ty remains an abstract parameter; Bytes8 is a checked wire tag. *)
Definition emptyBindings : Context.BindingMap := fun _ => None.

Definition fromResourceBits
  (owner : Syntax.Name) (ty : Syntax.Ty)
  (present loaned : bool) : Context.ResourceContext :=
  Context.mkResourceContext emptyBindings emptyBindings
    (fun candidate =>
       if String.eqb candidate owner
       then if present then Some ty else None
       else None)
    (fun candidate =>
       if String.eqb candidate owner then loaned else false).

Theorem reconstructed_owner_lookup_is_exact :
  forall owner ty present loaned,
    Context.bindingPresent owner
      (Context.linearBindings (fromResourceBits owner ty present loaned)) =
    present.
Proof.
  intros owner ty [|] loaned; unfold fromResourceBits, Context.bindingPresent;
    simpl; rewrite String.eqb_refl; reflexivity.
Qed.

Theorem reconstructed_loan_lookup_is_exact :
  forall owner ty present loaned,
    Context.sharedLoans (fromResourceBits owner ty present loaned) owner =
    loaned.
Proof.
  intros owner ty present loaned; unfold fromResourceBits; simpl.
  now rewrite String.eqb_refl.
Qed.


(* The checker temporarily installs a SharedBytes view as an unrestricted
   binding. Its own type is a second abstract Ty in Rocq; the wire's exact
   SharedBytes tag is checked independently. *)
Definition withScopedView
  (view : Syntax.Name) (viewTy : Syntax.Ty) (live : bool)
  (ctx : Context.ResourceContext) : Context.ResourceContext :=
  Context.mkResourceContext
    (fun candidate =>
       if String.eqb candidate view
       then if live then Some viewTy else None
       else None)
    (Context.affineBindings ctx)
    (Context.linearBindings ctx)
    (Context.sharedLoans ctx).

Theorem scoped_view_lookup_is_exact :
  forall view viewTy live ctx,
    Context.unrestrictedBindings (withScopedView view viewTy live ctx) view =
      if live then Some viewTy else None.
Proof.
  intros view viewTy live ctx.
  unfold withScopedView; simpl.
  now rewrite String.eqb_refl.
Qed.

Theorem scoped_view_preserves_owner_and_loan_lookups :
  forall owner view viewTy live ctx,
    Context.linearBindings (withScopedView view viewTy live ctx) owner =
      Context.linearBindings ctx owner /\
    Context.sharedLoans (withScopedView view viewTy live ctx) owner =
      Context.sharedLoans ctx owner.
Proof. intros; split; reflexivity. Qed.

Definition beforeContext (owner : Syntax.Name) (ty : Syntax.Ty) :=
  fromResourceBits owner ty true false.
Definition startedContext (owner : Syntax.Name) (ty : Syntax.Ty) :=
  SurfaceBorrowLoanStateCorrespondence.setCoreLoan
    owner true (beforeContext owner ty).
Definition closedContext (owner : Syntax.Name) (ty : Syntax.Ty) :=
  SurfaceBorrowLoanStateCorrespondence.setCoreLoan
    owner false (startedContext owner ty).
Definition returnedContext (owner : Syntax.Name) (ty : Syntax.Ty) :=
  Context.mkResourceContext
    (Context.unrestrictedBindings (closedContext owner ty))
    (Context.affineBindings (closedContext owner ty))
    (Context.deleteBinding owner (Context.linearBindings (closedContext owner ty)))
    (Context.sharedLoans (closedContext owner ty)).

Theorem represented_start_replays_context_operation :
  forall owner ty,
    SurfaceBorrowLoanStateCorrespondence.startLinearSharedLoan
      owner (beforeContext owner ty) = Some (startedContext owner ty).
Proof.
  intros owner ty.
  unfold SurfaceBorrowLoanStateCorrespondence.startLinearSharedLoan,
    startedContext, beforeContext, fromResourceBits; simpl.
  rewrite String.eqb_refl.
  reflexivity.
Qed.

Theorem represented_end_replays_context_operation :
  forall owner ty,
    SurfaceBorrowLoanStateCorrespondence.endLinearSharedLoan
      owner (startedContext owner ty) = Some (closedContext owner ty).
Proof.
  intros owner ty.
  unfold SurfaceBorrowLoanStateCorrespondence.endLinearSharedLoan,
    closedContext.
  rewrite SurfaceBorrowLoanStateCorrespondence.set_core_loan_has_exact_target.
  reflexivity.
Qed.

Theorem represented_consume_replays_context_operation :
  forall owner ty,
    Context.consumeLinear owner (closedContext owner ty) =
      Context.Consumed ty (returnedContext owner ty).
Proof.
  intros owner ty.
  unfold Context.consumeLinear, returnedContext, closedContext,
    startedContext, beforeContext, fromResourceBits,
    SurfaceBorrowLoanStateCorrespondence.setCoreLoan; simpl.
  repeat rewrite String.eqb_refl.
  reflexivity.
Qed.


Theorem represented_scoped_escape_cannot_consume_owner :
  forall owner view ty viewTy,
    Context.consumeLinear owner
      (withScopedView view viewTy true (startedContext owner ty)) =
    Context.ConsumeError (Context.OwnerBorrowed owner).
Proof.
  intros owner view ty viewTy.
  unfold Context.consumeLinear, withScopedView; simpl.
  unfold startedContext.
  rewrite SurfaceBorrowLoanStateCorrespondence.set_core_loan_has_exact_target.
  reflexivity.
Qed.

Theorem represented_escape_does_not_consume_owner :
  forall owner ty,
    Context.consumeLinear owner (startedContext owner ty) =
      Context.ConsumeError (Context.OwnerBorrowed owner).
Proof.
  intros owner ty.
  eapply SurfaceBorrowLoanStateCorrespondence.started_linear_loan_blocks_owner_consumption
    with (context := beforeContext owner ty).
  apply represented_start_replays_context_operation.
Qed.

(* These equalities prove bounded Rocq replay over decoded resource bits;
   the CI witness establishes the exact four source-derived CONTEXT-V1
   strings satisfy the independent decoder and agree with OBS-V1.
   Universal Haskell -> Rocq state correspondence remains an obligation. *)
