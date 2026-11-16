From Stdlib Require Import Strings.String Bool.Bool Lists.List Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

From Phil.Core Require Import Syntax.
From Phil.Surface Require Import
  SurfaceBinderNameEncoding SurfaceObservationWire
  SurfaceFiniteContextFrame SurfaceFiniteMixedJoinCorr6
  SurfaceFiniteTerminalJoinCorr7.

Module Names := SurfaceBinderNameEncoding.
Module Frames := SurfaceObservationWire.
Module F := SurfaceFiniteContextFrame.
Module J := SurfaceFiniteMixedJoinCorr6.
Module T := SurfaceFiniteTerminalJoinCorr7.

(*
  CORR-7 canonical wire: version + eight length-framed ASCII fields
  (source SHA, root, real flag/payload source binder names, profile,
  left/right source control category, outcome). The independent Python
  consumer checks SHA against real source bytes. This Rocq decoder checks
  strict framing, exact persisted binder identities and computes a SMALL
  finite related-model decision for each admitted source-tested profile.
  It does not certify a universal Haskell control/status serializer.
*)

Definition header : string := "PHIL-FSEM01-CORR7-V1|".

Definition expectedRootHex : string :=
  "6465636c2e6673656d30312e6a316a322e63686f6f7365".
Definition expectedFlagHex : string :=
  "247068696c2e6c6f63616c3a32333a6465636c2e6673656d30312e6a316a322e63686f6f73653a30".
Definition expectedPayloadHex : string :=
  "247068696c2e6c6f63616c3a32333a6465636c2e6673656d30312e6a316a322e63686f6f73653a31".

Record SourcePred : Type := mkSourcePred {
  sourceDigest : string;
  sourceRoot : string;
  sourceFlag : string;
  sourcePayload : string;
  sourceProfile : string;
  sourceLeft : string;
  sourceRight : string;
  sourceDisposition : string
}.

Definition fieldsOf (item : SourcePred) : list string :=
  [sourceDigest item;sourceRoot item;sourceFlag item;sourcePayload item;
   sourceProfile item;sourceLeft item;sourceRight item;sourceDisposition item].

Lemma corr7_fields_length : forall item, length (fieldsOf item) = 8.
Proof. intros [a b c d e f g h]; reflexivity. Qed.

Definition ofFields (fields : list string) : option SourcePred :=
  match fields with
  | [sha;root;flag;payload;profile;left;right;outcome] =>
      Some (mkSourcePred sha root flag payload profile left right outcome)
  | _ => None
  end.

Lemma corr7_fields_roundtrip :
  forall item, ofFields (fieldsOf item) = Some item.
Proof. intros [a b c d e f g h]; reflexivity. Qed.

Definition expectedCategories (profile : string)
  : option (string * string) :=
  if String.eqb profile "accepted" then Some ("CONT","CONT")
  else if String.eqb profile "linear-mismatch" then Some ("CONT","CONT")
  else if String.eqb profile "two-local-owners" then Some ("CONT","CONT")
  else if String.eqb profile "terminal-excluded" then Some ("TERM","CONT")
  else if String.eqb profile "terminal-stale" then Some ("TERM","CONT")
  else if String.eqb profile "terminal-both" then Some ("TERM","TERM")
  else None.

Definition common (ty : Syntax.Ty) : F.FiniteSnapshot :=
  F.mkFiniteSnapshot [] [] [("payload",ty)] [].
Definition moved (ty : Syntax.Ty) : F.FiniteSnapshot :=
  F.mkFiniteSnapshot [] [] [("moved",ty)] [].

Definition modelPaths (ty : Syntax.Ty) (profile : string)
  : list T.Predecessor :=
  if String.eqb profile "accepted" then
    [T.Continuing (common ty);T.Continuing (common ty)]
  else if String.eqb profile "linear-mismatch" then
    [T.Continuing (moved ty);T.Continuing (common ty)]
  else if String.eqb profile "two-local-owners" then
    [T.Continuing (moved ty);T.Continuing (common ty)]
  else if String.eqb profile "terminal-excluded" then
    [T.Terminal;T.Continuing (common ty)]
  else if String.eqb profile "terminal-stale" then
    [T.Terminal;T.Continuing (moved ty)]
  else if String.eqb profile "terminal-both" then
    [T.Terminal;T.Terminal]
  else [].

Definition modelClass (result : T.Outcome) : string :=
  match result with
  | T.NoContinuation => "NO_CONT"
  | T.Joined _ => "JOIN_OK"
  | T.JoinRejected J.JoinLinearMismatch => "JOIN_LINEAR"
  | T.JoinRejected _ => "JOIN_OTHER"
  | T.SourceRejected _ => "SOURCE_FAIL"
  end.

Definition predictedDisposition
    (ty : Syntax.Ty) (profile : string) : string :=
  let result := modelClass (T.replay (fun _ _ => true) (modelPaths ty profile)) in
  if String.eqb profile "terminal-excluded" then
    if String.eqb result "JOIN_OK" then "JOIN_ONE" else "INVALID"
  else if String.eqb profile "terminal-stale" then
    if String.eqb result "JOIN_OK" then "POST_STALE" else "INVALID"
  else result.

Definition categoryAndOutcomeValid (ty : Syntax.Ty) (item : SourcePred)
    : bool :=
  match expectedCategories (sourceProfile item) with
  | None => false
  | Some (left,right) =>
      String.eqb (sourceLeft item) left &&
      String.eqb (sourceRight item) right &&
      String.eqb (sourceDisposition item)
        (predictedDisposition ty (sourceProfile item))
  end.

Definition validSourcePred (ty : Syntax.Ty) (item : SourcePred) : bool :=
  Nat.eqb (String.length (sourceDigest item)) 64 &&
  Frames.isLowerHex (sourceDigest item) &&
  String.eqb (sourceRoot item) expectedRootHex &&
  String.eqb (sourceFlag item) expectedFlagHex &&
  String.eqb (sourcePayload item) expectedPayloadHex &&
  categoryAndOutcomeValid ty item.

Definition encodePred (item : SourcePred) : string :=
  header ++ Frames.packFieldsWithTail (fieldsOf item) "".

Definition decodePred (ty : Syntax.Ty) (wire : string) : option SourcePred :=
  match Names.stripPrefix header wire with
  | None => None
  | Some raw =>
      match Frames.parseFields 8 raw with
      | Some (fields,EmptyString) =>
          match ofFields fields with
          | Some record =>
              if validSourcePred ty record then Some record else None
          | None => None
          end
      | _ => None
      end
  end.

Definition checkWire (ty : Syntax.Ty) (wire : string) : bool :=
  match decodePred ty wire with Some _ => true | None => false end.

Theorem corr7_valid_wire_decodes :
  forall ty item,
    validSourcePred ty item = true ->
    decodePred ty (encodePred item) = Some item.
Proof.
  intros ty item Hvalid.
  unfold decodePred, encodePred.
  rewrite Names.strip_prefix_self.
  rewrite <- (corr7_fields_length item).
  rewrite (Frames.parse_pack_fields (fieldsOf item) "").
  rewrite corr7_fields_roundtrip.
  now rewrite Hvalid.
Qed.

Theorem corr7_decoder_only_accepts_valid_profiles :
  forall ty wire record,
    decodePred ty wire = Some record ->
    validSourcePred ty record = true.
Proof.
  intros ty wire record H.
  unfold decodePred in H.
  destruct (Names.stripPrefix header wire) as [payload|];
    try discriminate.
  destruct (Frames.parseFields 8 payload) as [[fields extra]|];
    try discriminate.
  destruct extra; try discriminate.
  destruct (ofFields fields) as [entry|] eqn:Hentry; try discriminate.
  destruct (validSourcePred ty entry) eqn:Hvalid;
    inversion H; subst; exact Hvalid.
Qed.

Theorem corr7_model_all_terminal_never_joins :
  forall ty,
    T.replay (fun _ _ => true) (modelPaths ty "terminal-both") =
      T.NoContinuation.
Proof. intros ty. reflexivity. Qed.

Theorem corr7_model_linear_mismatch_is_rejected :
  forall ty,
    T.replay (fun _ _ => true) (modelPaths ty "linear-mismatch") =
      T.JoinRejected J.JoinLinearMismatch.
Proof. intros ty. vm_compute. reflexivity. Qed.

Theorem corr7_model_one_terminal_keeps_one_live_successor :
  forall ty,
    T.replay (fun _ _ => true) (modelPaths ty "terminal-excluded") =
      T.Joined (F.mkFiniteSnapshot [] [] [("payload",ty)] []).
Proof. intros ty. reflexivity. Qed.

Print Assumptions corr7_valid_wire_decodes.
Print Assumptions corr7_decoder_only_accepts_valid_profiles.
Print Assumptions corr7_model_all_terminal_never_joins.
Print Assumptions corr7_model_linear_mismatch_is_rejected.
Print Assumptions corr7_model_one_terminal_keeps_one_live_successor.
