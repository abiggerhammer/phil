From Stdlib Require Import
  Strings.String Strings.Ascii
  Init.Decimal Numbers.DecimalNat Numbers.DecimalString
  Arith.PeanoNat.

From Phil.Core Require Import BindingSemantics.

Open Scope string_scope.

(*
  FSEM-01 -- byte/string-level name serialization for admitted local binders.

  This is the _ASCII/Rocq-string_ model of the Haskell BinderScope encoding:
    "$phil.local:" ++ show(length(root)) ++ ":" ++ root ++ ":" ++ show(ordinal).
  Decimal numbers use the standard library's canonical Nat.to_uint rendering.
  The root length makes embedded colons unambiguous.

  DeclarationKey in the production Haskell implementation is Data.Text,
  whereas a Rocq String is an ASCII-byte chain. Consequently the theorem
  does NOT establish Unicode Text.length/encoding correspondence; that
  concrete representation boundary needs independent validation.

  It also does not certify the Haskell machine-Int range or parser traversal.
  No axiom, admitted result or untrusted generated extraction is used here.
*)

Definition renderNat (n : nat) : string :=
  DecimalString.NilEmpty.string_of_uint (Nat.to_uint n).

Definition readNat (s : string) : option nat :=
  option_map Nat.of_uint (DecimalString.NilEmpty.uint_of_string s).

Lemma read_render_nat : forall n, readNat (renderNat n) = Some n.
Proof.
  intros n.
  unfold readNat, renderNat.
  rewrite DecimalString.NilEmpty.usu.
  simpl.
  now rewrite DecimalNat.Unsigned.of_to.
Qed.

Fixpoint stripPrefix (prefix input : string) : option string :=
  match prefix, input with
  | EmptyString, rest => Some rest
  | String a as_, String b bs =>
      if Ascii.eqb a b then stripPrefix as_ bs else None
  | _, _ => None
  end.

Lemma strip_prefix_self :
  forall prefix suffix, stripPrefix prefix (prefix ++ suffix) = Some suffix.
Proof.
  induction prefix as [|c rest IH]; intro suffix; simpl.
  - reflexivity.
  - rewrite Ascii.eqb_refl.
    exact (IH suffix).
Qed.

Fixpoint splitFirstColon (input : string) : option (string * string) :=
  match input with
  | EmptyString => None
  | String c rest =>
      if Ascii.eqb c ":"%char then Some (EmptyString, rest)
      else
        match splitFirstColon rest with
        | None => None
        | Some (head, suffix) => Some (String c head, suffix)
        end
  end.

Lemma split_first_colon_preserves_digit_prefix :
  forall (digit : ascii) (tail suffix : string),
    Ascii.eqb digit ":"%char = false ->
    splitFirstColon (tail ++ (":" ++ suffix)) = Some (tail, suffix) ->
    splitFirstColon (String digit tail ++ (":" ++ suffix)) =
      Some (String digit tail, suffix).
Proof.
  intros digit tail suffix Hdigit Htail.
  change
    ( (if Ascii.eqb digit ":"%char
       then Some (EmptyString, tail ++ (":" ++ suffix))
       else match splitFirstColon (tail ++ (":" ++ suffix)) with
            | Some (head, rest) => Some (String digit head, rest)
            | None => None
            end)
      = Some (String digit tail, suffix)).
  rewrite Hdigit.
  rewrite Htail.
  reflexivity.
Qed.

Lemma split_render_uint :
  forall (d : Decimal.uint) (suffix : string),
    splitFirstColon
      (DecimalString.NilEmpty.string_of_uint d ++ (":" ++ suffix)) =
    Some (DecimalString.NilEmpty.string_of_uint d, suffix).
Proof.
  induction d; intro suffix.
  - reflexivity.
  all: cbn [DecimalString.NilEmpty.string_of_uint];
       apply split_first_colon_preserves_digit_prefix;
       [reflexivity | apply IHd].
  Show.
Qed.

Lemma split_render_nat :
  forall n suffix,
    splitFirstColon (renderNat n ++ (":" ++ suffix)) =
      Some (renderNat n, suffix).
Proof.
  intros n suffix.
  unfold renderNat.
  apply split_render_uint.
Qed.

Fixpoint takeChars (n : nat) (input : string)
    : option (string * string) :=
  match n with
  | O => Some (EmptyString, input)
  | S next =>
      match input with
      | EmptyString => None
      | String c rest =>
          match takeChars next rest with
          | None => None
          | Some (head, suffix) => Some (String c head, suffix)
          end
      end
  end.

Lemma take_exact_root :
  forall root suffix,
    takeChars (String.length root) (root ++ suffix) = Some (root, suffix).
Proof.
  induction root as [|c rest IH]; intro suffix; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Definition encodeBinderName (root : string) (ordinal : nat) : string :=
  "$phil.local:" ++
    (renderNat (String.length root) ++
      (":" ++ (root ++ (":" ++ renderNat ordinal)))).

Definition decodeBinderName (encoded : string) : option (string * nat) :=
  match stripPrefix "$phil.local:" encoded with
  | None => None
  | Some payload =>
      match splitFirstColon payload with
      | None => None
      | Some (sizeToken, afterSize) =>
          match readNat sizeToken with
          | None => None
          | Some size =>
              match takeChars size afterSize with
              | None => None
              | Some (root, afterRoot) =>
                  match stripPrefix ":" afterRoot with
                  | None => None
                  | Some ordinalToken =>
                      match readNat ordinalToken with
                      | None => None
                      | Some ordinal => Some (root, ordinal)
                      end
                  end
              end
          end
      end
  end.

Theorem decode_encode_binder_name :
  forall root ordinal,
    decodeBinderName (encodeBinderName root ordinal) = Some (root, ordinal).
Proof.
  intros root ordinal.
  unfold decodeBinderName, encodeBinderName.
  rewrite strip_prefix_self.
  rewrite split_render_nat.
  rewrite read_render_nat.
  rewrite take_exact_root.
  rewrite strip_prefix_self.
  now rewrite read_render_nat.
Qed.

Theorem encode_binder_name_injective :
  forall firstRoot firstOrdinal secondRoot secondOrdinal,
    encodeBinderName firstRoot firstOrdinal =
      encodeBinderName secondRoot secondOrdinal ->
    firstRoot = secondRoot /\ firstOrdinal = secondOrdinal.
Proof.
  intros firstRoot firstOrdinal secondRoot secondOrdinal Heq.
  pose proof (f_equal decodeBinderName Heq) as Hdecoded.
  repeat rewrite decode_encode_binder_name in Hdecoded.
  injection Hdecoded as Hpair.
  inversion Hpair; subst.
  split; reflexivity.
Qed.

Definition TextBinderKey := (string * nat)%type.

Definition encodeTextBinderKey (key : TextBinderKey) : string :=
  encodeBinderName (fst key) (snd key).

Corollary encode_text_binder_key_injective :
  forall first second : TextBinderKey,
    encodeTextBinderKey first = encodeTextBinderKey second ->
    first = second.
Proof.
  intros [firstRoot firstOrdinal] [secondRoot secondOrdinal] H.
  unfold encodeTextBinderKey in H; simpl in H.
  apply encode_binder_name_injective in H.
  destruct H as [Hroot Hordinal].
  subst; reflexivity.
Qed.

Section NormalizedBinderKeyBridge.

  (* The prior BindingSemantics.v models declaration identities as nat.
     The actual Haskell DeclarationKey is Text; do not silently assume
     that every nat has an agreed serialized declaration root. *)
  Variable declarationText : BindingSemantics.DeclarationIdentity -> string.
  Hypothesis declarationText_injective :
    forall first second,
      declarationText first = declarationText second -> first = second.

  Definition modelNameOf (key : BindingSemantics.BinderKey) : string :=
    encodeBinderName (declarationText (fst key)) (snd key).

  Theorem model_name_of_injective :
    forall first second : BindingSemantics.BinderKey,
      modelNameOf first = modelNameOf second -> first = second.
  Proof.
    intros [firstDecl firstOrdinal] [secondDecl secondOrdinal] Heq.
    unfold modelNameOf in Heq; simpl in Heq.
    apply encode_binder_name_injective in Heq.
    destruct Heq as [Hroot Hordinal].
    apply declarationText_injective in Hroot.
    subst; reflexivity.
  Qed.

End NormalizedBinderKeyBridge.

Example encoded_empty_root :
  encodeBinderName "" 0 = "$phil.local:0::0".
Proof. reflexivity. Qed.

Example encoded_colon_root :
  encodeBinderName "a:b" 10 = "$phil.local:3:a:b:10".
Proof. reflexivity. Qed.

(* The Name-injectivity hypothesis in SurfaceBorrowLoanStateCorrespondence.v
   can be instantiated with modelNameOf and model_name_of_injective,
   PROVIDED declarationText is injective. The ResourceOwner mapping and
   Haskell Text-to-Rocq string correspondence remain separate obligations. *)
