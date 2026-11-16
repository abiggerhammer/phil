From Stdlib Require Import Strings.String Bool.Bool Lists.List Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

From Phil.Core Require Import Syntax.
From Phil.Surface Require Import
  SurfaceBinderNameEncoding SurfaceObservationWire
  SurfaceFiniteContextFrame SurfaceFiniteMixedJoinCorr6
  SurfaceFiniteTerminalJoinCorr7 SurfaceSourceFailureCorr8.

Module Names := SurfaceBinderNameEncoding.
Module Frames := SurfaceObservationWire.
Module F := SurfaceFiniteContextFrame.
Module T := SurfaceFiniteTerminalJoinCorr7.
Module C := SurfaceSourceFailureCorr8.

(*
  CORR-8 strict source error-prefix wire, ten length-framed ASCII fields:
  actual source SHA, declaration root, actual flag/owner binder IDs,
  fixture profile, reached left/right loan checkpoints, two PRUNED
  predecessor counts and real checker outcome class. The independent
  Python witness validator binds the SHA to original .phil bytes.
  This decoder rejects false successes, misplaced failures, unexpected
  phases and overwritten source identities. This is NOT a complete
  Haskell parser/checker-state refinement.
*)

Definition header : string := "PHIL-FSEM01-CORR8-V1|".
Definition expectedRootHex : string :=
  "6465636c2e6673656d30312e73636f7065642d6c6f616e2d6a6f696e2e63686f6f7365".
Definition expectedFlagHex : string :=
  "247068696c2e6c6f63616c3a33353a6465636c2e6673656d30312e73636f7065642d6c6f616e2d6a6f696e2e63686f6f73653a30".
Definition expectedOwnerHex : string :=
  "247068696c2e6c6f63616c3a33353a6465636c2e6673656d30312e73636f7065642d6c6f616e2d6a6f696e2e63686f6f73653a31".

Record SourceFailureWire : Type := mkSourceFailureWire {
  sourceDigest : string;
  sourceRoot : string;
  sourceFlag : string;
  sourceOwner : string;
  sourceProfile : string;
  sourceLeftPrefix : string;
  sourceRightPrefix : string;
  sourceLeftPruned : string;
  sourceRightPruned : string;
  sourceResult : string
}.

Definition fieldsOf (item : SourceFailureWire) : list string :=
  [ sourceDigest item; sourceRoot item; sourceFlag item; sourceOwner item;
    sourceProfile item; sourceLeftPrefix item; sourceRightPrefix item;
    sourceLeftPruned item; sourceRightPruned item; sourceResult item ].

Lemma corr8_fields_length :
  forall item, length (fieldsOf item) = 10.
Proof. intros [a b c d e f g h i j]; reflexivity. Qed.

Definition ofFields (fields : list string) : option SourceFailureWire :=
  match fields with
  | [sha;root;flag;owner;profile;lhs;rhs;lp;rp;result] =>
      Some (mkSourceFailureWire sha root flag owner profile lhs rhs lp rp result)
  | _ => None
  end.

Lemma corr8_fields_roundtrip :
  forall item, ofFields (fieldsOf item) = Some item.
Proof. intros [a b c d e f g h i j]; reflexivity. Qed.

Definition expectedPrefix (profile : string)
  : option (string * string * string * string * string) :=
  if String.eqb profile "accepted-left" then
    Some ("BSVC","-","1","1","JOIN_OK")
  else if String.eqb profile "accepted-both" then
    Some ("BSVC","BSVC","1","1","JOIN_OK")
  else if String.eqb profile "escape-left" then
    Some ("BSEX","-","0","0","SOURCE_BORROW")
  else if String.eqb profile "escape-right" then
    Some ("-","BSEX","1","0","SOURCE_BORROW")
  else if String.eqb profile "escape-alias" then
    Some ("BSEX","-","0","0","SOURCE_BORROW")
  else if String.eqb profile "move-while-loaned" then
    Some ("BS","-","0","0","SOURCE_STRUCTURAL")
  else if String.eqb profile "return-inside-borrow" then
    Some ("BSR","-","0","0","SOURCE_LINEAR")
  else if String.eqb profile "borrow-unrestricted" then
    Some ("B","-","0","0","SOURCE_BORROW")
  else None.

Definition modelPaths (profile result : string) : list T.Predecessor :=
  if String.eqb result "JOIN_OK"
  then [T.Continuing C.closedState;T.Continuing C.closedState]
  else if String.eqb profile "escape-right"
  then [T.Continuing C.closedState;T.Failed result]
  else [T.Failed result].

Definition resultClass (outcome : T.Outcome) : string :=
  match outcome with
  | T.Joined _ => "JOIN_OK"
  | T.SourceRejected reason => reason
  | T.NoContinuation => "NO_CONTINUATION"
  | T.JoinRejected _ => "JOIN_ERROR"
  end.

Definition modelResult (item : SourceFailureWire) : string :=
  resultClass (T.replay (fun (_ _ : Syntax.Ty) => true)
    (modelPaths (sourceProfile item) (sourceResult item))).

Definition prefixAndResultValid (item : SourceFailureWire) : bool :=
  match expectedPrefix (sourceProfile item) with
  | None => false
  | Some (lhs,rhs,lp,rp,result) =>
      String.eqb (sourceLeftPrefix item) lhs &&
      String.eqb (sourceRightPrefix item) rhs &&
      String.eqb (sourceLeftPruned item) lp &&
      String.eqb (sourceRightPruned item) rp &&
      String.eqb (sourceResult item) result &&
      String.eqb (sourceResult item) (modelResult item)
  end.

Definition validSourceWire (item : SourceFailureWire) : bool :=
  Nat.eqb (String.length (sourceDigest item)) 64 &&
  Frames.isLowerHex (sourceDigest item) &&
  String.eqb (sourceRoot item) expectedRootHex &&
  String.eqb (sourceFlag item) expectedFlagHex &&
  String.eqb (sourceOwner item) expectedOwnerHex &&
  prefixAndResultValid item.

Definition encodeWire (item : SourceFailureWire) : string :=
  header ++ Frames.packFieldsWithTail (fieldsOf item) "".

Definition decodeWire (wire : string) : option SourceFailureWire :=
  match Names.stripPrefix header wire with
  | None => None
  | Some raw =>
      match Frames.parseFields 10 raw with
      | Some (fields,EmptyString) =>
          match ofFields fields with
          | Some entry =>
              if validSourceWire entry then Some entry else None
          | None => None
          end
      | _ => None
      end
  end.

Definition checkWire (wire : string) : bool :=
  match decodeWire wire with Some _ => true | None => false end.

Theorem corr8_valid_wire_decodes :
  forall item,
    validSourceWire item = true ->
    decodeWire (encodeWire item) = Some item.
Proof.
  intros item Hvalid.
  unfold decodeWire, encodeWire.
  rewrite Names.strip_prefix_self.
  rewrite <- (corr8_fields_length item).
  rewrite (Frames.parse_pack_fields (fieldsOf item) "").
  rewrite corr8_fields_roundtrip.
  now rewrite Hvalid.
Qed.

Theorem corr8_decoder_accepts_only_model_consistent_records :
  forall wire record,
    decodeWire wire = Some record ->
    validSourceWire record = true.
Proof.
  intros wire record H.
  unfold decodeWire in H.
  destruct (Names.stripPrefix header wire) as [payload|];
    try discriminate.
  destruct (Frames.parseFields 10 payload) as [[fields extra]|];
    try discriminate.
  destruct extra; try discriminate.
  destruct (ofFields fields) as [entry|] eqn:Hentry; try discriminate.
  destruct (validSourceWire entry) eqn:Hvalid;
    inversion H; subst; exact Hvalid.
Qed.

Theorem corr8_left_failure_cannot_join :
  forall typeEq reason state result,
    T.replay typeEq [T.Failed reason; T.Continuing state] <>
      T.Joined result.
Proof. intros; discriminate. Qed.

Theorem corr8_right_failure_cannot_join :
  forall typeEq state reason result,
    T.replay typeEq [T.Continuing state;T.Failed reason] <>
      T.Joined result.
Proof. intros; discriminate. Qed.

Print Assumptions corr8_valid_wire_decodes.
Print Assumptions corr8_decoder_accepts_only_model_consistent_records.
Print Assumptions corr8_left_failure_cannot_join.
Print Assumptions corr8_right_failure_cannot_join.
