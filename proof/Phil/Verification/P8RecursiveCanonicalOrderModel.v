From Coq Require Import List Bool Arith.PeanoNat.
From Phil.Verification Require Import P8UnicodeUtf8Model.
Import ListNotations.

(* P8-C2: executable octet lexicography and canonical all-pairs keys.
   Octet nat is NOT a native identity encoding; Haskell Text/Ord is NOT
   proved by this model. No axioms or caller-provided proofs. *)
Fixpoint p8_c2_bytes_ltb (left right : list nat) {struct left} : bool :=
  match left, right with
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: tail, b :: rest =>
      if a <? b then true
      else if b <? a then false
      else p8_c2_bytes_ltb tail rest
  end.

Lemma p8_c2_bytes_ltb_irrefl :
  forall bytes, p8_c2_bytes_ltb bytes bytes = false.
Proof.
  induction bytes as [|a tail IH].
  - reflexivity.
  - simpl. rewrite Nat.ltb_irrefl. simpl. exact IH.
Qed.

(* Every key is checked against ALL later keys; no assumed comparator
   transitivity. This is stronger than merely checking neighbors. *)
Fixpoint p8_c2_strict_keys (keys : list (list nat)) : bool :=
  match keys with
  | [] => true
  | key :: tail =>
      forallb (p8_c2_bytes_ltb key) tail && p8_c2_strict_keys tail
  end.

Theorem p8_c2_strict_keys_no_duplicates :
  forall keys, p8_c2_strict_keys keys = true -> NoDup keys.
Proof.
  intros keys. induction keys as [|key tail IH]; simpl.
  - intros _. constructor.
  - intros H.
    apply andb_true_iff in H as [Hhead Htail].
    constructor.
    + intro Hin.
      pose proof
        (proj1 (@forallb_forall (list nat) (p8_c2_bytes_ltb key) tail)
          Hhead key Hin) as Hbad.
      rewrite p8_c2_bytes_ltb_irrefl in Hbad.
      discriminate.
    + apply IH. exact Htail.
Qed.

Inductive P8C2Form : Type :=
| P8C2Atom : list nat -> P8C2Form
| P8C2Ordered : list P8C2Form -> P8C2Form
| P8C2Unordered : list P8C2Form -> P8C2Form
| P8C2Record : list (list nat * P8C2Form) -> P8C2Form.

(* Native deriving Ord ranks: Atom < Ordered < Unordered < Record;
   unlike the byte order of the diagnostic tags a,o,u,r. *)
Definition p8_c2_form_rank (form : P8C2Form) : nat :=
  match form with
  | P8C2Atom _ => 0
  | P8C2Ordered _ => 1
  | P8C2Unordered _ => 2
  | P8C2Record _ => 3
  end.

Definition p8_c2_record_keys
  (fields : list (list nat * P8C2Form)) : list (list nat) :=
  map fst fields.
Definition p8_c2_record_keys_canonical
  (fields : list (list nat * P8C2Form)) : bool :=
  p8_c2_strict_keys (p8_c2_record_keys fields).

Theorem p8_c2_canonical_record_unique_keys :
  forall fields,
    p8_c2_record_keys_canonical fields = true ->
    NoDup (p8_c2_record_keys fields).
Proof.
  intros fields H.
  exact (p8_c2_strict_keys_no_duplicates _ H).
Qed.

Inductive P8C2GenericRole : Type :=
| P8C2Declaration | P8C2Interface
| P8C2ParameterKey | P8C2ParameterValue.

Theorem p8_c2_generic_role_separation :
  P8C2Declaration <> P8C2Interface /\
  P8C2ParameterKey <> P8C2ParameterValue /\
  P8C2Declaration <> P8C2ParameterKey /\
  P8C2Interface <> P8C2ParameterValue.
Proof. repeat split; discriminate. Qed.

Theorem p8_c2_generic_unique_parameter_keys :
  forall keys, p8_c2_strict_keys keys = true -> NoDup keys.
Proof. apply p8_c2_strict_keys_no_duplicates. Qed.

Example p8_c2_sorted_keys_positive :
  p8_c2_strict_keys [[97]; [98]; [195; 169]] = true.
Proof. reflexivity. Qed.
Example p8_c2_duplicate_keys_negative :
  p8_c2_strict_keys [[97]; [97]] = false.
Proof. reflexivity. Qed.
Example p8_c2_reverse_keys_negative :
  p8_c2_strict_keys [[98]; [97]] = false.
Proof. reflexivity. Qed.
Example p8_c2_prefix_keys_distinct :
  p8_c2_bytes_ltb [97] [97; 0] = true.
Proof. reflexivity. Qed.
Example p8_c2_c1_accent_admitted :
  p8_decode_exact_scalar [195; 169] = Some (P8Utf8Two 195 169).
Proof. reflexivity. Qed.
Example p8_c2_c1_surrogate_rejected :
  p8_decode_exact_scalar [237; 160; 128] = None.
Proof. reflexivity. Qed.
(* Concrete FALSE shortcut: native U < R, but wire u > r. *)
Example p8_c2_wire_order_not_native_constructor_order :
  (2 <? 3) = true /\ (117 <? 114) = false.
Proof. split; reflexivity. Qed.

Print Assumptions p8_c2_bytes_ltb_irrefl.
Print Assumptions p8_c2_strict_keys_no_duplicates.
Print Assumptions p8_c2_canonical_record_unique_keys.
Print Assumptions p8_c2_generic_role_separation.
Print Assumptions p8_c2_generic_unique_parameter_keys.
