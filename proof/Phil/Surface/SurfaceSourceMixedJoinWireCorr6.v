From Stdlib Require Import Strings.String Bool.Bool Lists.List Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

From Phil.Core Require Import Syntax.
From Phil.Surface Require Import
  SurfaceBinderNameEncoding SurfaceObservationWire
  SurfaceFiniteContextFrame SurfaceFiniteMixedJoinCorr6.

Module Names := SurfaceBinderNameEncoding.
Module Frames := SurfaceObservationWire.
Module F := SurfaceFiniteContextFrame.
Module J := SurfaceFiniteMixedJoinCorr6.

(*
  CORR-6 exact-source snapshot wire:
     PHIL-FSEM01-CORR6-V1| + 8 canonical decimal length-framed fields:
     source SHA256, declaration root UTF8 hex, flag/permit/payload Core.Name
     UTF8 hex, left/right actual *post-prune* four-zone shape tags, result.

  The Haskell producer separately proves by direct native conformance that
  every profile token corresponds to the authentic source checker state and
  only the selected source-checked Bool/Permit/Bytes[8] modes are admitted.
  Here Syntax.Ty remains an abstract kernel parameter. We do NOT assume
  arbitrary Haskell Ty equality; the fixed common-type source fragment
  permits a reflexive comparator for the shared exact identical types.
  The general type-comparator reflectance boundary stays explicit in
  SurfaceFiniteMixedJoinCorr6.
*)

Definition header : string := "PHIL-FSEM01-CORR6-V1|".

Record SourceJoin : Type := mkSourceJoin {
  sourceDigest : string;
  rootHex : string;
  flagHex : string;
  permitHex : string;
  payloadHex : string;
  leftStatus : string;
  rightStatus : string;
  sourceDisposition : string
}.

Definition fieldsOf (item : SourceJoin) : list string :=
  [sourceDigest item;rootHex item;flagHex item;permitHex item;
   payloadHex item;leftStatus item;rightStatus item;
   sourceDisposition item].

Lemma fields_len : forall a, length (fieldsOf a) = 8.
Proof. intros [a b c d e f g h]. reflexivity. Qed.

Definition ofFields (fields : list string) : option SourceJoin :=
  match fields with
  | [hash;root;flag;permit;payload;leftView;rightView;result] =>
      Some (mkSourceJoin hash root flag permit payload leftView rightView result)
  | _ => None
  end.

Lemma fields_roundtrip : forall a, ofFields (fieldsOf a) = Some a.
Proof. intros [a b c d e f g h]. reflexivity. Qed.

Definition loanFreeDropped : string := "U1A0L1N0".
Definition loanFreeRetained : string := "U1A1L1N0".
Definition noPredecessor : string := "UNREACHED".

Definition caseValid (t : SourceJoin) : bool :=
  let leftView := leftStatus t in
  let rightView := rightStatus t in
  let outcome := sourceDisposition t in
  (String.eqb leftView loanFreeDropped &&
   String.eqb rightView loanFreeRetained &&
     (String.eqb outcome "JOIN_EMPTY" ||
      String.eqb outcome "POSTJOIN_STALE"))
  || (String.eqb leftView loanFreeDropped &&
      String.eqb rightView loanFreeDropped &&
      String.eqb outcome "JOIN_EMPTY")
  || (String.eqb leftView loanFreeRetained &&
      String.eqb rightView loanFreeRetained &&
      String.eqb outcome "JOIN_PERMIT")
  || (String.eqb leftView noPredecessor &&
      String.eqb rightView noPredecessor &&
      String.eqb outcome "PREJOIN_LINEAR").

Definition validSourceJoin (t : SourceJoin) : bool :=
  (Nat.eqb (String.length (sourceDigest t)) 64 &&
   Frames.isLowerHex (sourceDigest t)) &&
  Frames.canonicalHex (rootHex t) &&
  Frames.canonicalHex (flagHex t) &&
  Frames.canonicalHex (permitHex t) &&
  Frames.canonicalHex (payloadHex t) &&
  negb (String.eqb (flagHex t) "") &&
  negb (String.eqb (permitHex t) "") &&
  negb (String.eqb (payloadHex t) "") &&
  negb (String.eqb (flagHex t) (permitHex t)) &&
  negb (String.eqb (flagHex t) (payloadHex t)) &&
  negb (String.eqb (permitHex t) (payloadHex t)) &&
  caseValid t.

Definition encodeJoin (t : SourceJoin) : string :=
  header ++ Frames.packFieldsWithTail (fieldsOf t) "".

Definition decodeJoin (wire : string) : option SourceJoin :=
  match Names.stripPrefix header wire with
  | None => None
  | Some input =>
      match Frames.parseFields 8 input with
      | Some (fields,EmptyString) =>
          match ofFields fields with
          | Some record =>
              if validSourceJoin record then Some record else None
          | None => None
          end
      | _ => None
      end
  end.

Theorem corr6_valid_source_join_decodes :
  forall record, validSourceJoin record = true ->
    decodeJoin (encodeJoin record) = Some record.
Proof.
  intros record Hvalid.
  unfold decodeJoin, encodeJoin.
  rewrite Names.strip_prefix_self.
  rewrite <- (fields_len record).
  rewrite (Frames.parse_pack_fields (fieldsOf record) "").
  rewrite fields_roundtrip.
  now rewrite Hvalid.
Qed.

Theorem corr6_decode_rejects_wrong_version :
  forall fields,
    decodeJoin ("PHIL-FSEM01-CORR6-V2|" ++
      Frames.packFieldsWithTail fields "") = None.
Proof. intros fields. reflexivity. Qed.

Theorem corr6_decoded_source_join_is_valid :
  forall wire record,
    decodeJoin wire = Some record ->
    validSourceJoin record = true.
Proof.
  intros wire record H.
  unfold decodeJoin in H.
  destruct (Names.stripPrefix header wire) as [payload|]; try discriminate.
  destruct (Frames.parseFields 8 payload) as [[fields extra]|];
    try discriminate.
  destruct extra; try discriminate.
  destruct (ofFields fields) as [entry|] eqn:Hentry; try discriminate.
  destruct (validSourceJoin entry) eqn:Hvalid;
    inversion H; subst; exact Hvalid.
Qed.

Definition finitePredecessor
  (boolType permitType bytesType : Syntax.Ty)
  (record : SourceJoin) (status : string) : F.FiniteSnapshot :=
  F.mkFiniteSnapshot
    [(flagHex record,boolType)]
    (if String.eqb status loanFreeRetained then
      [(permitHex record,permitType)] else [])
    [(payloadHex record,bytesType)]
    [].

(* The emitted profiles are a CLOSED and independently source-checked
   same-typed fragment. Every input Type field appears with the same Type
   object in both predecessors; a constant equality decision is not
   general Ty equality authority and must not be used for general joins. *)
Definition sourceJoinCheck
  (boolType permitType bytesType : Syntax.Ty)
  (record : SourceJoin) : bool :=
  if String.eqb (sourceDisposition record) "PREJOIN_LINEAR"
  then andb (String.eqb (leftStatus record) noPredecessor)
            (String.eqb (rightStatus record) noPredecessor)
  else
    let leftContext := finitePredecessor boolType permitType bytesType
      record (leftStatus record) in
    let rightContext := finitePredecessor boolType permitType bytesType
      record (rightStatus record) in
    match J.finiteJoin (fun _ _ => true) leftContext rightContext with
    | J.JoinRejected _ => false
    | J.JoinSuccess result =>
        match F.finiteAffine result with
        | [] =>
            String.eqb (sourceDisposition record) "JOIN_EMPTY" ||
            String.eqb (sourceDisposition record) "POSTJOIN_STALE"
        | [(name,_)] =>
            String.eqb name (permitHex record) &&
            String.eqb (sourceDisposition record) "JOIN_PERMIT"
        | _ => false
        end
    end.

Definition checkWire
  (boolType permitType bytesType : Syntax.Ty)
  (wire : string) : bool :=
  match decodeJoin wire with
  | None => false
  | Some record =>
      sourceJoinCheck boolType permitType bytesType record
  end.

Theorem corr6_checked_wire_has_valid_source_identity :
  forall bt pt lt wire,
    checkWire bt pt lt wire = true ->
    exists record,
      decodeJoin wire = Some record /\
      validSourceJoin record = true.
Proof.
  intros bt pt lt wire Hchecked.
  unfold checkWire in Hchecked.
  destruct (decodeJoin wire) as [record|] eqn:Hdecoded;
    try discriminate.
  exists record. split; [exact Hdecoded|].
  now eapply corr6_decoded_source_join_is_valid.
Qed.

Print Assumptions corr6_valid_source_join_decodes.
Print Assumptions corr6_decode_rejects_wrong_version.
Print Assumptions corr6_decoded_source_join_is_valid.
Print Assumptions corr6_checked_wire_has_valid_source_identity.
