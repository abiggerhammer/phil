From Stdlib Require Import Strings.String Strings.Ascii Bool.Bool Lists.List Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

From Phil.Core Require Import Syntax.
From Phil.Surface Require Import
  SurfaceBinderNameEncoding SurfaceObservationWire
  SurfaceFiniteContextFrame SurfaceFiniteLinearTraceCorr5.

Module Frames := SurfaceObservationWire.
Module Names := SurfaceBinderNameEncoding.
Module Traces := SurfaceFiniteLinearTraceCorr5.
Module Finite := SurfaceFiniteContextFrame.

(*
  Source-derived CORR-5 v1 wire:
    PHIL-FSEM01-CORR5-V1| then eight canonical decimal length frames:
    exact source SHA256 hex, normalized declaration-root UTF8 hex,
    flag/old/slot/optional alternate Haskell Core.Name UTF8 hex,
    kind (OK,ST,DU,GA,LO), expected (DONE,MISSING,DUPLICATE,GATED,LOAN).

  A Haskell source observer verifies the actual full checker traces and emits
  the bytes; Python independently validates source SHA256, lexical binder
  encodings, names and the literal wire before feeding the SAME bytes to Rocq.
  Here Name is an opaque hex identity token, not a theorem identifying
  arbitrary Haskell Unicode Text with Rocq String. The actual source typing
  predicate for Bytes[8]/Bool is checked in Haskell, not re-proved here.
*)

Definition traceHeader : string := "PHIL-FSEM01-CORR5-V1|".

Record SourceTrace : Type := mkSourceTrace {
  traceSourceHash : string;
  traceRootHex : string;
  traceFlagHex : string;
  traceOldHex : string;
  traceSlotHex : string;
  traceAlternateHex : string;
  traceKind : string;
  traceExpected : string
}.

Definition traceFields (t : SourceTrace) : list string :=
  [traceSourceHash t; traceRootHex t; traceFlagHex t; traceOldHex t;
   traceSlotHex t; traceAlternateHex t; traceKind t; traceExpected t].

Lemma trace_fields_length : forall t, List.length (traceFields t) = 8.
Proof. intros [a b c d e f g h]. reflexivity. Qed.

Definition traceOfFields (fields : list string) : option SourceTrace :=
  match fields with
  | [hash; root; flag; old; slot; alternate; kind; expected] =>
      Some (mkSourceTrace hash root flag old slot alternate kind expected)
  | _ => None
  end.

Lemma trace_fields_roundtrip :
  forall t, traceOfFields (traceFields t) = Some t.
Proof. intros [a b c d e f g h]. reflexivity. Qed.

Definition validSourceTrace (t : SourceTrace) : bool :=
  let alternate := traceAlternateHex t in
  let hasAlternate := negb (String.eqb alternate "-") in
  let hexName (name : string) :=
    negb (String.eqb name "") && Frames.canonicalHex name in
  let distinct :=
    negb (String.eqb (traceFlagHex t) (traceOldHex t)) &&
    negb (String.eqb (traceFlagHex t) (traceSlotHex t)) &&
    negb (String.eqb (traceOldHex t) (traceSlotHex t)) &&
    (negb hasAlternate ||
      (negb (String.eqb alternate (traceFlagHex t)) &&
       negb (String.eqb alternate (traceOldHex t)) &&
       negb (String.eqb alternate (traceSlotHex t)))) in
  (Nat.eqb (String.length (traceSourceHash t)) 64 &&
    Frames.isLowerHex (traceSourceHash t)) &&
  hexName (traceRootHex t) &&
  hexName (traceFlagHex t) &&
  hexName (traceOldHex t) &&
  hexName (traceSlotHex t) &&
  (negb hasAlternate || hexName alternate) &&
  distinct &&
  ( (String.eqb (traceKind t) "OK" &&
      String.eqb (traceExpected t) "DONE")
    || (String.eqb (traceKind t) "ST" &&
        String.eqb (traceExpected t) "MISSING" && negb hasAlternate)
    || (String.eqb (traceKind t) "DU" &&
        String.eqb (traceExpected t) "DUPLICATE" && hasAlternate)
    || (String.eqb (traceKind t) "GA" &&
        String.eqb (traceExpected t) "GATED" && negb hasAlternate)
    || (String.eqb (traceKind t) "LO" &&
        String.eqb (traceExpected t) "LOAN" && negb hasAlternate) ).

Definition encodeTrace (t : SourceTrace) : string :=
  traceHeader ++ Frames.packFieldsWithTail (traceFields t) "".

Definition decodeTrace (raw : string) : option SourceTrace :=
  match Names.stripPrefix traceHeader raw with
  | None => None
  | Some payload =>
      match Frames.parseFields 8 payload with
      | Some (fields, EmptyString) =>
          match traceOfFields fields with
          | Some record =>
              if validSourceTrace record then Some record else None
          | None => None
          end
      | _ => None
      end
  end.

Theorem corr5_valid_trace_decodes_canonical_wire :
  forall t, validSourceTrace t = true ->
    decodeTrace (encodeTrace t) = Some t.
Proof.
  intros t Hvalid.
  unfold decodeTrace, encodeTrace.
  rewrite Names.strip_prefix_self.
  rewrite <- (trace_fields_length t).
  rewrite (Frames.parse_pack_fields (traceFields t) "").
  rewrite trace_fields_roundtrip.
  now rewrite Hvalid.
Qed.

Theorem corr5_decoded_trace_is_valid :
  forall raw t,
    decodeTrace raw = Some t -> validSourceTrace t = true.
Proof.
  intros raw t H.
  unfold decodeTrace in H.
  destruct (Names.stripPrefix traceHeader raw) as [payload|];
    try discriminate.
  destruct (Frames.parseFields 8 payload) as [[fields extra]|];
    try discriminate.
  destruct extra; try discriminate.
  destruct (traceOfFields fields) as [record|] eqn:Hrecord;
    try discriminate.
  destruct (validSourceTrace record) eqn:Hvalid;
    inversion H; subst; assumption.
Qed.

Theorem corr5_wrong_version_is_not_a_trace :
  forall fields,
    decodeTrace
      ("PHIL-FSEM01-CORR5-V2|" ++
        Frames.packFieldsWithTail fields "") = None.
Proof. intros fields. reflexivity. Qed.

Definition initialSnapshot (boolType bytesType : Syntax.Ty)
  (trace : SourceTrace) : Finite.FiniteSnapshot :=
  if String.eqb (traceKind trace) "LO"
  then Finite.mkFiniteSnapshot
    [(traceFlagHex trace, boolType)] []
    [(traceSlotHex trace, bytesType)] [traceSlotHex trace]
  else Finite.mkFiniteSnapshot
    [(traceFlagHex trace, boolType)] []
    ((traceOldHex trace, bytesType) ::
      if String.eqb (traceAlternateHex trace) "-" then []
      else [(traceAlternateHex trace, bytesType)]) [].

Definition sourceCommands (bytesType : Syntax.Ty)
  (trace : SourceTrace) : list Traces.LinearCommand :=
  let consume := Traces.MoveLinear in
  let bind := fun name => Traces.BindLinear name bytesType in
  let old := traceOldHex trace in
  let slot := traceSlotHex trace in
  if String.eqb (traceKind trace) "OK"
  then [consume old; bind slot; consume slot; bind slot]
  else if String.eqb (traceKind trace) "ST"
  then [consume old; bind slot; consume old]
  else if String.eqb (traceKind trace) "DU"
  then [consume old; bind slot; consume (traceAlternateHex trace); bind slot]
  else if String.eqb (traceKind trace) "GA"
  then [consume old; bind slot]
  else if String.eqb (traceKind trace) "LO"
  then [consume slot]
  else [].

Definition traceMatchesExpected
  (trace : SourceTrace)
  (result : Traces.Replay Finite.FiniteSnapshot) : bool :=
  match result with
  | Traces.Finished _ =>
      String.eqb (traceExpected trace) "DONE" ||
        String.eqb (traceExpected trace) "GATED"
  | Traces.Halted index reason _ =>
      match reason with
      | Traces.MissingLinear owner =>
          Nat.eqb index 2 &&
          String.eqb owner (traceOldHex trace) &&
          String.eqb (traceExpected trace) "MISSING"
      | Traces.DuplicateLinear owner =>
          Nat.eqb index 3 &&
          String.eqb owner (traceSlotHex trace) &&
          String.eqb (traceExpected trace) "DUPLICATE"
      | Traces.LoanRefusal owner =>
          Nat.eqb index 0 &&
          String.eqb owner (traceSlotHex trace) &&
          String.eqb (traceExpected trace) "LOAN"
      end
  end.

Definition checkWire
  (boolType bytesType : Syntax.Ty) (raw : string) : bool :=
  match decodeTrace raw with
  | None => false
  | Some t =>
      traceMatchesExpected t
        (Traces.replayFinite
          (sourceCommands bytesType t)
          (initialSnapshot boolType bytesType t))
  end.

(* The proof is about all normalized model traces; concrete emitted source
   bytes are checked by independently generated closed-wire witnesses in CI.
   The GATED result is a successful two-step resource prefix only. Its
   separate source MissingEvidence refusal is checked by the native Haskell
   source checker, never reclassified as a Linear resource failure. *)
Theorem corr5_check_wire_requires_valid_artifact :
  forall boolType bytesType raw,
    checkWire boolType bytesType raw = true ->
    exists t, decodeTrace raw = Some t /\ validSourceTrace t = true.
Proof.
  intros boolType bytesType raw Hcheck.
  unfold checkWire in Hcheck.
  destruct (decodeTrace raw) as [t|] eqn:Hdecoded;
    try discriminate.
  exists t; split; [exact Hdecoded|].
  now apply (corr5_decoded_trace_is_valid raw t).
Qed.

Print Assumptions corr5_valid_trace_decodes_canonical_wire.
Print Assumptions corr5_decoded_trace_is_valid.
Print Assumptions corr5_wrong_version_is_not_a_trace.
Print Assumptions corr5_check_wire_requires_valid_artifact.
