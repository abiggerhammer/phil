From Stdlib Require Import
  Strings.String Strings.Ascii Lists.List Bool.Bool Arith.PeanoNat.
From Phil.Surface Require Import
  SurfaceBinderNameEncoding SurfaceBorrowStepErrorBridge.

Import ListNotations.
Open Scope string_scope.

(*
  FSEM-01 Observation Wire v1. The byte carrier here is Rocq String,
  corresponding to the ASCII-only wire text. The Haskell producer serializes
  UTF-8 source and names as lowercase hex, so no unrestricted Unicode Text
  is passed directly to this parser.

  The framed decoder is a pure total function. It rejects malformed
  lengths, noncanonical decimal representations, missing/extra fields,
  an unknown version, noncanonical hashes/hex, mismatched trace outcomes,
  and an out-of-order owner/view binder index.

  IMPORTANT: this DOES NOT prove the Haskell producer faithfully represents
  its runtime, the security of SHA256, UTF8 correctness, or catalog provenance.
  CI runs this executable Rocq decoder on the real Haskell-produced artifacts.
*)

Definition wireHeader : string := "PHIL-FSEM01-OBS-V1|".

Definition frameWithTail (field suffix : string) : string :=
  SurfaceBinderNameEncoding.renderNat (String.length field) ++
    (":" ++ (field ++ suffix)).

Definition parseFrame (wire : string) : option (string * string) :=
  match SurfaceBinderNameEncoding.splitFirstColon wire with
  | None => None
  | Some (lengthDigits, contents) =>
      match SurfaceBinderNameEncoding.readNat lengthDigits with
      | None => None
      | Some len =>
          if String.eqb lengthDigits
               (SurfaceBinderNameEncoding.renderNat len)
          then SurfaceBinderNameEncoding.takeChars len contents
          else None
      end
  end.

Theorem parse_frame_roundtrip :
  forall field suffix,
    parseFrame (frameWithTail field suffix) = Some (field, suffix).
Proof.
  intros field suffix.
  unfold parseFrame, frameWithTail.
  rewrite SurfaceBinderNameEncoding.split_render_nat.
  rewrite SurfaceBinderNameEncoding.read_render_nat.
  rewrite String.eqb_refl.
  apply SurfaceBinderNameEncoding.take_exact_root.
Qed.

Fixpoint packFieldsWithTail (fields : list string) (suffix : string) : string :=
  match fields with
  | [] => suffix
  | field :: rest => frameWithTail field (packFieldsWithTail rest suffix)
  end.

Fixpoint parseFields (count : nat) (wire : string)
  : option (list string * string) :=
  match count with
  | O => Some ([], wire)
  | S remaining =>
      match parseFrame wire with
      | None => None
      | Some (field, suffix) =>
          match parseFields remaining suffix with
          | None => None
          | Some (rest, trailing) => Some (field :: rest, trailing)
          end
      end
  end.

Theorem parse_pack_fields :
  forall fields suffix,
    parseFields (List.length fields) (packFieldsWithTail fields suffix) =
      Some (fields, suffix).
Proof.
  induction fields as [|field rest IH]; intro suffix.
  - reflexivity.
  - simpl.
    rewrite parse_frame_roundtrip.
    rewrite IH.
    reflexivity.
Qed.

Record Artifact : Type := mkArtifact {
  sourceHash : string;
  declarationRootHex : string;
  ownerNameHex : string;
  viewNameHex : string;
  ownerOrdinal : string;
  viewOrdinal : string;
  traceCodes : string;
  terminalCode : string
}.

Definition fieldsOf (artifact : Artifact) : list string :=
  [sourceHash artifact; declarationRootHex artifact;
   ownerNameHex artifact; viewNameHex artifact;
   ownerOrdinal artifact; viewOrdinal artifact;
   traceCodes artifact; terminalCode artifact].

Lemma fields_of_length :
  forall artifact, List.length (fieldsOf artifact) = 8.
Proof.
  intros [hash root owner view ownerIndex viewIndex trace outcome].
  reflexivity.
Qed.

Definition recordOfFields (fields : list string) : option Artifact :=
  match fields with
  | [hash; root; owner; view; ownerIndex; viewIndex; trace; outcome] =>
      Some (mkArtifact hash root owner view ownerIndex viewIndex trace outcome)
  | _ => None
  end.

Theorem record_fields_roundtrip :
  forall artifact, recordOfFields (fieldsOf artifact) = Some artifact.
Proof.
  intros [hash root owner view ownerIndex viewIndex trace outcome].
  reflexivity.
Qed.

Definition canonicalNatural (digits : string) : option nat :=
  match SurfaceBinderNameEncoding.readNat digits with
  | None => None
  | Some n =>
      if String.eqb digits (SurfaceBinderNameEncoding.renderNat n)
      then Some n else None
  end.

Definition lowerHexDigits : list ascii :=
  ["0"%char; "1"%char; "2"%char; "3"%char; "4"%char;
   "5"%char; "6"%char; "7"%char; "8"%char; "9"%char;
   "a"%char; "b"%char; "c"%char; "d"%char; "e"%char; "f"%char].

Fixpoint isLowerHex (s : string) : bool :=
  match s with
  | EmptyString => true
  | String digit rest =>
      List.existsb (Ascii.eqb digit) lowerHexDigits && isLowerHex rest
  end.

Definition canonicalHex (s : string) : bool :=
  Nat.even (String.length s) && isLowerHex s.

Definition knownTraceOutcome (artifact : Artifact) : bool :=
  (String.eqb (traceCodes artifact) "B10,S11,N11,C10,R00" &&
   String.eqb (terminalCode artifact) "OK:Bytes8") ||
  (String.eqb (traceCodes artifact) "B10,S11,E11,X11" &&
   String.eqb (terminalCode artifact)
     "ERR:BorrowEscape:shared view escapes its lexical scope").

Definition canonicalOrdinals (artifact : Artifact) : bool :=
  match canonicalNatural (ownerOrdinal artifact),
        canonicalNatural (viewOrdinal artifact) with
  | Some owner, Some view => Nat.ltb owner view
  | _, _ => false
  end.

Definition validArtifact (artifact : Artifact) : bool :=
  (Nat.eqb (String.length (sourceHash artifact)) 64 &&
   isLowerHex (sourceHash artifact)) &&
  canonicalHex (declarationRootHex artifact) &&
  canonicalHex (ownerNameHex artifact) &&
  canonicalHex (viewNameHex artifact) &&
  canonicalOrdinals artifact &&
  knownTraceOutcome artifact.

Definition encodeArtifact (artifact : Artifact) : string :=
  wireHeader ++ packFieldsWithTail (fieldsOf artifact) "".

Definition decodeArtifact (raw : string) : option Artifact :=
  match SurfaceBinderNameEncoding.stripPrefix wireHeader raw with
  | None => None
  | Some payload =>
      match parseFields 8 payload with
      | Some (fields, EmptyString) =>
          match recordOfFields fields with
          | Some artifact =>
              if validArtifact artifact then Some artifact else None
          | None => None
          end
      | _ => None
      end
  end.

Theorem decode_encode_valid_artifact :
  forall artifact,
    validArtifact artifact = true ->
    decodeArtifact (encodeArtifact artifact) = Some artifact.
Proof.
  intros artifact Hvalid.
  unfold decodeArtifact, encodeArtifact.
  rewrite SurfaceBinderNameEncoding.strip_prefix_self.
  rewrite <- (fields_of_length artifact).
  rewrite (parse_pack_fields (fieldsOf artifact) "").
  rewrite record_fields_roundtrip.
  now rewrite Hvalid.
Qed.

Theorem decoded_artifact_is_valid :
  forall raw artifact,
    decodeArtifact raw = Some artifact ->
    validArtifact artifact = true.
Proof.
  intros raw artifact H.
  unfold decodeArtifact in H.
  destruct (SurfaceBinderNameEncoding.stripPrefix wireHeader raw) as [payload|];
    try discriminate.
  destruct (parseFields 8 payload) as [[fields trailing]|];
    try discriminate.
  destruct trailing; try discriminate.
  destruct (recordOfFields fields) as [record|] eqn:Hrecord;
    try discriminate.
  destruct (validArtifact record) eqn:Hvalid;
    inversion H; subst; assumption.
Qed.

Theorem decoder_rejects_wrong_version :
  forall artifact,
    decodeArtifact ("PHIL-FSEM01-OBS-V2|" ++
      packFieldsWithTail (fieldsOf artifact) "") = None.
Proof.
  intros artifact.
  reflexivity.
Qed.

Theorem decoded_artifact_has_consistent_outcome :
  forall raw artifact,
    decodeArtifact raw = Some artifact ->
    knownTraceOutcome artifact = true.
Proof.
  intros raw artifact H.
  apply decoded_artifact_is_valid in H.
  unfold validArtifact in H.
  repeat rewrite Bool.andb_true_iff in H.
  tauto.
Qed.

Theorem decoded_wire_replays_one_terminal_model :
  forall raw artifact owner,
    decodeArtifact raw = Some artifact ->
    (traceCodes artifact = "B10,S11,N11,C10,R00" /\
     terminalCode artifact = "OK:Bytes8" /\
     SurfaceBorrowStepErrorBridge.replay
       (SurfaceBorrowStepErrorBridge.modeledCut owner
         SurfaceRepresentedBorrowTrace.ModelBeforeLoan)
       [SurfaceBorrowStepErrorBridge.EventBegin;
        SurfaceBorrowStepErrorBridge.EventBodySafe;
        SurfaceBorrowStepErrorBridge.EventClose;
        SurfaceBorrowStepErrorBridge.EventReturn] =
       Some (SurfaceBorrowStepErrorBridge.modeledCut owner
         SurfaceRepresentedBorrowTrace.ModelOwnerReturned)) \/
    (traceCodes artifact = "B10,S11,E11,X11" /\
     terminalCode artifact =
       "ERR:BorrowEscape:shared view escapes its lexical scope" /\
     SurfaceBorrowStepErrorBridge.replay
       (SurfaceBorrowStepErrorBridge.modeledCut owner
         SurfaceRepresentedBorrowTrace.ModelBeforeLoan)
       [SurfaceBorrowStepErrorBridge.EventBegin;
        SurfaceBorrowStepErrorBridge.EventBodyEscapes;
        SurfaceBorrowStepErrorBridge.EventRejectBorrowEscape] =
       Some (SurfaceBorrowStepErrorBridge.modeledCut owner
         SurfaceRepresentedBorrowTrace.ModelEscapeRejected)).
Proof.
  intros raw artifact owner Hdecoded.
  pose proof
    (decoded_artifact_has_consistent_outcome raw artifact Hdecoded)
    as Hcodes.
  unfold knownTraceOutcome in Hcodes.
  apply Bool.orb_true_iff in Hcodes.
  destruct Hcodes as [Hsuccess | Hescape].
  - left.
    apply Bool.andb_true_iff in Hsuccess.
    destruct Hsuccess as [Htrace Houtcome].
    apply String.eqb_eq in Htrace.
    apply String.eqb_eq in Houtcome.
    split; [exact Htrace |].
    split; [exact Houtcome |].
    apply SurfaceBorrowStepErrorBridge.accepted_borrow_step_replay.
  - right.
    apply Bool.andb_true_iff in Hescape.
    destruct Hescape as [Htrace Houtcome].
    apply String.eqb_eq in Htrace.
    apply String.eqb_eq in Houtcome.
    split; [exact Htrace |].
    split; [exact Houtcome |].
    apply SurfaceBorrowStepErrorBridge.rejected_borrow_step_replay.
Qed.

(*
  The Haskell producer and a second Python validator are not theorem-proven
  equivalent to this String decoder. CI builds a Rocq witness from the exact
  emitted ASCII bytes and checks it with vm_compute; that establishes that
  the observed specimen really passes this decoder, not a general refinement.
*)
