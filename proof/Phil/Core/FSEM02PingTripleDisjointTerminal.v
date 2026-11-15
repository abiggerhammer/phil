From Stdlib Require Import Arith.PeanoNat.
From Phil.Core Require Import Syntax Context
  FSEM02PingThreeProcessFrame FSEM02PingClosePrefixFaultRetry.

(* FSEM-02 non-normative: site keys are nat surrogates, not certified
   native ProcessKey encodings. Activation, protocol instance, roles,
   terminal disposal and admission are external premises. *)
Definition fsem02WriteTriple
  (a b c : nat) (aClosed bClosed cClosed : ResourceContext)
  (before : fsem02ProcessMap) : fsem02ProcessMap :=
  fsem02WriteOneProcess c cClosed
    (fsem02WriteOneProcess b bClosed
      (fsem02WriteOneProcess a aClosed before)).

Theorem fsem02TripleCloseFramesOutside :
  forall a b c spectator aClosed bClosed cClosed before,
    spectator <> a -> spectator <> b -> spectator <> c ->
    fsem02WriteTriple a b c aClosed bClosed cClosed before spectator =
      before spectator.
Proof.
  intros a b c spectator aClosed bClosed cClosed before Ha Hb Hc.
  unfold fsem02WriteTriple.
  rewrite (fsem02MapCloseSuccessFramesOther c spectator cClosed _ Hc).
  rewrite (fsem02MapCloseSuccessFramesOther b spectator bClosed _ Hb).
  apply fsem02MapCloseSuccessFramesOther. exact Ha.
Qed.

Theorem fsem02TripleCloseRecordsThird :
  forall a b c aClosed bClosed cClosed before,
    fsem02WriteTriple a b c aClosed bClosed cClosed before c =
      Some cClosed.
Proof.
  intros. unfold fsem02WriteTriple.
  apply fsem02MapCloseSuccessRecordsExactSite.
Qed.

Theorem fsem02TripleCloseRecordsFirst :
  forall a b c aClosed bClosed cClosed before,
    a <> b -> a <> c ->
    fsem02WriteTriple a b c aClosed bClosed cClosed before a =
      Some aClosed.
Proof.
  intros a b c aClosed bClosed cClosed before Hab Hac.
  unfold fsem02WriteTriple.
  rewrite (fsem02MapCloseSuccessFramesOther c a cClosed _ Hac).
  rewrite (fsem02MapCloseSuccessFramesOther b a bClosed _ Hab).
  apply fsem02MapCloseSuccessRecordsExactSite.
Qed.

Theorem fsem02TripleCloseFirstTwoSwap :
  forall a b c aClosed bClosed cClosed before,
    a <> b ->
    fsem02WriteTriple a b c aClosed bClosed cClosed before =
      fsem02WriteOneProcess c cClosed
        (fsem02WriteOneProcess a aClosed
          (fsem02WriteOneProcess b bClosed before)).
Proof.
  intros a b c aClosed bClosed cClosed before Hab.
  unfold fsem02WriteTriple.
  rewrite (fsem02DisjointMapCloseWritesCommute
    a b aClosed bClosed before Hab).
  reflexivity.
Qed.

Theorem fsem02TripleCloseLastTwoSwap :
  forall a b c aClosed bClosed cClosed before,
    b <> c ->
    fsem02WriteTriple a b c aClosed bClosed cClosed before =
      fsem02WriteOneProcess b bClosed
        (fsem02WriteOneProcess c cClosed
          (fsem02WriteOneProcess a aClosed before)).
Proof.
  intros a b c aClosed bClosed cClosed before Hbc.
  unfold fsem02WriteTriple.
  apply fsem02DisjointMapCloseWritesCommute.
  exact Hbc.
Qed.

Theorem fsem02TripleRejectedCloseKeepsCommittedPrefix :
  forall a b c rejected aClosed bClosed cClosed rejectedClosed before,
    fsem02TryMapClose false rejected rejectedClosed
      (fsem02WriteTriple a b c aClosed bClosed cClosed before) =
    FSEM02MapCloseRejected
      (fsem02WriteTriple a b c aClosed bClosed cClosed before).
Proof. reflexivity. Qed.

Theorem fsem02TripleRejectedCloseThenValidRetry :
  forall a b c aClosed bClosed cClosed before,
    match fsem02TryMapClose false c cClosed
      (fsem02WriteOneProcess b bClosed
        (fsem02WriteOneProcess a aClosed before)) with
    | FSEM02MapCloseRejected samePrefix =>
        fsem02TryMapClose true c cClosed samePrefix
    | FSEM02MapCloseApplied already =>
        FSEM02MapCloseApplied already
    end =
      FSEM02MapCloseApplied
        (fsem02WriteTriple a b c aClosed bClosed cClosed before).
Proof. reflexivity. Qed.
