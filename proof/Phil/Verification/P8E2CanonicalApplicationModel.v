From Coq Require Import List Bool Arith.PeanoNat Lia.
From Phil.Verification Require Import P8D1UnicodeStreamModel P8D2StructuralOrderModel P8E1CanonicalWireModel.
Import ListNotations.

(*
  P8-E2: executable canonical-acceptance verifier for the E1 recursive
  structural codec and a distinct, typed D/V/Q/M GenericApplication wire
  codec. This does NOT assume that Haskell Text/Map/Set/Ord implement this
  Rocq model, and does NOT assume the E1 parser is complete.
  Every theorem below is about the exact executable model functions.
*)

Fixpoint p8_e2_bytes_equal (xs ys : list nat) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: tail, y :: rest => Nat.eqb x y && p8_e2_bytes_equal tail rest
  | _, _ => false
  end.

Lemma p8_e2_bytes_equal_sound :
  forall xs ys, p8_e2_bytes_equal xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; destruct ys as [|y ys]; simpl;
    try discriminate; intros H; try reflexivity.
  apply andb_true_iff in H as [E R].
  apply Nat.eqb_eq in E. subst y.
  f_equal. apply IH. exact R.
Qed.

Lemma p8_e2_bytes_equal_refl :
  forall xs, p8_e2_bytes_equal xs xs = true.
Proof.
  induction xs as [|x xs IH]; simpl; [reflexivity|].
  rewrite Nat.eqb_refl, IH. reflexivity.
Qed.

(* A successful result is the exact canonical E1 wire, checked by
   re-encoding, with D2 strict Unicode and Map/Set structural validation.
   No arbitrary Prop is supplied by the caller. *)
Definition p8_e2_normalize_form (wire : list nat) : option P8D2Form :=
  match p8_e1_decode_form wire with
  | None => None
  | Some form =>
      if p8_d2_valid_form form &&
         p8_e2_bytes_equal (p8_e1_put_form form) wire
      then Some form else None
  end.

Theorem p8_e2_normalized_form_sound :
  forall wire form,
    p8_e2_normalize_form wire = Some form ->
    p8_e1_decode_form wire = Some form /\
    p8_d2_valid_form form = true /\
    p8_e1_put_form form = wire.
Proof.
  intros wire form H.
  unfold p8_e2_normalize_form in H.
  destruct (p8_e1_decode_form wire) as [candidate|] eqn:P;
    try discriminate.
  destruct (p8_d2_valid_form candidate &&
            p8_e2_bytes_equal (p8_e1_put_form candidate) wire)
    eqn:Gate; try discriminate.
  apply andb_true_iff in Gate as [V E].
  apply p8_e2_bytes_equal_sound in E.
  inversion H; subst; clear H.
  repeat split; assumption.
Qed.

Theorem p8_e2_normalized_form_exact_characterization :
  forall wire form,
    p8_e2_normalize_form wire = Some form <->
    p8_e1_decode_form wire = Some form /\
    p8_d2_valid_form form = true /\
    p8_e1_put_form form = wire.
Proof.
  intros wire form. split.
  - apply p8_e2_normalized_form_sound.
  - intros [P [V E]].
    unfold p8_e2_normalize_form. rewrite P, V.
    rewrite E, p8_e2_bytes_equal_refl. reflexivity.
Qed.

(* Q field keys and M form values are represented by distinct wire
   roles, even when D/V/Q text bytes happen to be identical. *)
Definition p8_e2_expect (tag : nat) (wire : list nat)
  : option (list nat) :=
  match wire with
  | [] => None
  | actual :: rest =>
      if actual =? tag then Some rest else None
  end.

Lemma p8_e2_expect_sound :
  forall tag wire suffix,
    p8_e2_expect tag wire = Some suffix ->
    wire = tag :: suffix.
Proof.
  intros tag [|actual rest] suffix H; simpl in H;
    try discriminate.
  destruct (actual =? tag) eqn:E; try discriminate.
  apply Nat.eqb_eq in E. subst actual.
  inversion H; subst. reflexivity.
Qed.

Definition p8_e2_put_argument (key : list nat) (value : P8D2Form)
  : list nat :=
  [81] ++ p8_e1_put_text key ++ [77] ++ p8_e1_put_form value.

Fixpoint p8_e2_put_arguments (fields : P8D2Fields) : list nat :=
  match fields with
  | P8D2FieldNil => []
  | P8D2FieldCons key value rest =>
      p8_e2_put_argument key value ++ p8_e2_put_arguments rest
  end.

Definition p8_e2_put_application (app : P8D2Application) : list nat :=
  [103;68] ++ p8_e1_put_text (p8_d2_declaration app)
  ++ [86] ++ p8_e1_put_text (p8_d2_interface app)
  ++ p8_e1_frame_count (p8_e1_fields_count (p8_d2_arguments app))
  ++ p8_e2_put_arguments (p8_d2_arguments app).

Definition p8_e2_parse_argument (fuel : nat) (wire : list nat)
  : option ((list nat * P8D2Form) * list nat) :=
  match p8_e2_expect 81 wire with
  | None => None
  | Some afterQ =>
      match p8_e1_parse_text afterQ with
      | None => None
      | Some (key, afterKey) =>
          match p8_e2_expect 77 afterKey with
          | None => None
          | Some afterM =>
              match p8_e1_parse_form_fuel fuel afterM with
              | None => None
              | Some (value, suffix) => Some ((key, value), suffix)
              end
          end
      end
  end.

Fixpoint p8_e2_parse_arguments (fuel count : nat) (wire : list nat)
  : option (P8D2Fields * list nat) :=
  match count with
  | 0 => Some (P8D2FieldNil, wire)
  | S remaining =>
      match p8_e2_parse_argument fuel wire with
      | None => None
      | Some ((key, value), afterOne) =>
          match p8_e2_parse_arguments fuel remaining afterOne with
          | None => None
          | Some (rest, suffix) =>
              Some (P8D2FieldCons key value rest, suffix)
          end
      end
  end.

Theorem p8_e2_argument_roles_are_exact :
  forall fuel wire key value suffix,
    p8_e2_parse_argument fuel wire = Some ((key, value), suffix) ->
    exists afterQ afterKey afterM,
      wire = 81 :: afterQ /\
      p8_e1_parse_text afterQ = Some (key, afterKey) /\
      afterKey = 77 :: afterM /\
      p8_e1_parse_form_fuel fuel afterM = Some (value, suffix).
Proof.
  intros fuel wire key value suffix H.
  unfold p8_e2_parse_argument in H.
  destruct (p8_e2_expect 81 wire) as [afterQ|] eqn:Q;
    try discriminate.
  destruct (p8_e1_parse_text afterQ) as [[k afterKey]|] eqn:K;
    try discriminate.
  destruct (p8_e2_expect 77 afterKey) as [afterM|] eqn:M;
    try discriminate.
  destruct (p8_e1_parse_form_fuel fuel afterM) as [[v tail]|] eqn:F;
    try discriminate.
  inversion H; subst; clear H.
  apply p8_e2_expect_sound in Q.
  apply p8_e2_expect_sound in M.
  exists afterQ, afterKey, afterM.
  repeat split; assumption.
Qed.

Theorem p8_e2_argument_count_is_exact :
  forall count fuel wire fields suffix,
    p8_e2_parse_arguments fuel count wire = Some (fields, suffix) ->
    p8_e1_fields_count fields = count.
Proof.
  induction count as [|count IH]; intros fuel wire fields suffix H.
  - cbn [p8_e2_parse_arguments] in H.
    inversion H; subst. reflexivity.
  - cbn [p8_e2_parse_arguments] in H.
    destruct (p8_e2_parse_argument fuel wire)
      as [[[key value] next]|] eqn:A; try discriminate.
    destruct (p8_e2_parse_arguments fuel count next)
      as [[rest trailing]|] eqn:R; try discriminate.
    inversion H; subst; clear H.
    cbn [p8_e1_fields_count].
    pose proof (IH fuel next rest trailing R). lia.
Qed.

(* "g D text V text count : (Q text M form)*". Each role is checked
   before the corresponding payload, not inferred from equal byte values. *)
Definition p8_e2_parse_application_raw (wire : list nat)
  : option (P8D2Application * list nat) :=
  match p8_e2_expect 103 wire with
  | None => None
  | Some afterG =>
      match p8_e2_expect 68 afterG with
      | None => None
      | Some afterD =>
          match p8_e1_parse_text afterD with
          | None => None
          | Some (declaration, afterDeclaration) =>
              match p8_e2_expect 86 afterDeclaration with
              | None => None
              | Some afterV =>
                  match p8_e1_parse_text afterV with
                  | None => None
                  | Some (revision, afterRevision) =>
                      match p8_e1_read_count afterRevision with
                      | None => None
                      | Some (count, afterCount) =>
                          if count <=? length afterCount then
                            match p8_e2_parse_arguments (S (length wire))
                                    count afterCount with
                            | None => None
                            | Some (args, suffix) =>
                                Some ({| p8_d2_declaration := declaration;
                                        p8_d2_interface := revision;
                                        p8_d2_arguments := args |}, suffix)
                            end
                          else None
                      end
                  end
              end
          end
      end
  end.

Definition p8_e2_parse_application_prefix (wire : list nat)
  : option (P8D2Application * list nat) :=
  match p8_e2_parse_application_raw wire with
  | None => None
  | Some (app, suffix) =>
      if p8_d2_valid_application app then Some (app, suffix) else None
  end.

Definition p8_e2_decode_application (wire : list nat)
  : option P8D2Application :=
  match p8_e2_parse_application_prefix wire with
  | Some (app, []) =>
      if p8_e2_bytes_equal (p8_e2_put_application app) wire
      then Some app else None
  | _ => None
  end.

Theorem p8_e2_parsed_application_is_valid :
  forall wire app suffix,
    p8_e2_parse_application_prefix wire = Some (app, suffix) ->
    p8_d2_valid_application app = true.
Proof.
  intros wire app suffix H.
  unfold p8_e2_parse_application_prefix in H.
  destruct (p8_e2_parse_application_raw wire)
    as [[candidate trailing]|] eqn:P; try discriminate.
  destruct (p8_d2_valid_application candidate) eqn:V;
    try discriminate.
  inversion H; subst. exact V.
Qed.

Theorem p8_e2_canonical_application_sound :
  forall wire app,
    p8_e2_decode_application wire = Some app ->
    p8_e2_parse_application_prefix wire = Some (app, []) /\
    p8_d2_valid_application app = true /\
    p8_e2_put_application app = wire.
Proof.
  intros wire app H.
  unfold p8_e2_decode_application in H.
  destruct (p8_e2_parse_application_prefix wire)
    as [[candidate suffix]|] eqn:P; try discriminate.
  destruct suffix as [|trailing rest]; try discriminate.
  destruct (p8_e2_bytes_equal (p8_e2_put_application candidate) wire)
    eqn:Equal; try discriminate.
  apply p8_e2_bytes_equal_sound in Equal.
  inversion H; subst; clear H.
  pose proof (p8_e2_parsed_application_is_valid wire app [] P) as V.
  repeat split; assumption.
Qed.

Theorem p8_e2_wrong_application_role_rejected :
  forall wire,
    p8_e2_parse_application_prefix (77 :: wire) = None.
Proof. intros wire; reflexivity. Qed.

Theorem p8_e2_wrong_argument_role_rejected :
  forall fuel wire,
    p8_e2_parse_argument fuel (77 :: wire) = None.
Proof. intros fuel wire; reflexivity. Qed.

(* Independent executable positives/negatives: not assertions about an
   unproved general Haskell operational-semantics transport. *)
Example p8_e2_empty_application_roundtrip :
  p8_e2_decode_application [103;68;116;48;58;86;116;48;58;48;58] =
  Some {| p8_d2_declaration := [];
          p8_d2_interface := [];
          p8_d2_arguments := P8D2FieldNil |}.
Proof. reflexivity. Qed.

Example p8_e2_one_argument_roundtrip :
  p8_e2_decode_application
    [103;68;116;49;58;97;86;116;49;58;98;49;58;
     81;116;49;58;120;77;97;116;49;58;121] =
  Some {| p8_d2_declaration := [97];
          p8_d2_interface := [98];
          p8_d2_arguments :=
            P8D2FieldCons [120] (P8D2Atom [121]) P8D2FieldNil |}.
Proof. reflexivity. Qed.

Example p8_e2_swapped_D_V_reject :
  p8_e2_decode_application [103;86;116;48;58;68;116;48;58;48;58]
  = None.
Proof. reflexivity. Qed.

Example p8_e2_trailing_application_reject :
  p8_e2_decode_application [103;68;116;48;58;86;116;48;58;48;58;0]
  = None.
Proof. reflexivity. Qed.

Example p8_e2_duplicate_Q_reject :
  p8_e2_decode_application
    [103;68;116;48;58;86;116;48;58;50;58;
     81;116;49;58;97;77;97;116;48;58;
     81;116;49;58;97;77;97;116;48;58] = None.
Proof. reflexivity. Qed.

Example p8_e2_native_order_not_tag_order :
  p8_d2_compare_form (P8D2Unordered P8D2Nil)
                     (P8D2Record P8D2FieldNil) = Lt /\
  (117 <? 114) = false.
Proof. split; reflexivity. Qed.

Print Assumptions p8_e2_bytes_equal_sound.
Print Assumptions p8_e2_normalized_form_sound.
Print Assumptions p8_e2_normalized_form_exact_characterization.
Print Assumptions p8_e2_expect_sound.
Print Assumptions p8_e2_argument_roles_are_exact.
Print Assumptions p8_e2_argument_count_is_exact.
Print Assumptions p8_e2_parsed_application_is_valid.
Print Assumptions p8_e2_canonical_application_sound.
Print Assumptions p8_e2_wrong_application_role_rejected.
Print Assumptions p8_e2_wrong_argument_role_rejected.
