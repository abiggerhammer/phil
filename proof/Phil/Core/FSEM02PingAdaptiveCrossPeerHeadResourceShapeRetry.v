From Stdlib Require Import Arith.PeanoNat.
From Phil.Core Require Import
  FSEM02PingAdaptiveCrossPeerHeadOwnerRetry
  FSEM02PingAdaptiveHeadResourcePriorityRetry
  FSEM02PingAdaptiveFreePeerResourceShapeRetry
  FSEM02PingAdaptiveHalfCloseSuffix
  FSEM02PingMixedPrefixFault.

(* FSEM-02, non-normative: remote linear resource SHAPE faults are kept
   separate from the other peer's projected source-head observation. All
   process identities are abstract nat carriers; nominal instance, role,
   activation, partner/root selection, disposal and scheduler authority,
   and native Haskell map correspondence remain external premises. *)

(* Client's bad projected head masks a Server non-endpoint resource.
   Correcting ONLY that head exposes the wrong-type resource error. *)
Theorem fsem02CrossPeerClientHeadServerWrongTypeLadder :
  forall client server ec es bad before,
    ec <> bad ->
    fsem02AdaptiveHeadShapeGate client server ec es bad es
      (FSEM02EndpointResource ec) FSEM02NonEndpointResource before =
      FSEM02HeadMismatch client ec bad /\
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      (FSEM02EndpointResource ec) FSEM02NonEndpointResource before =
      FSEM02ShapeMismatch server FSEM02WrongResourceType.
Proof.
  intros client server ec es bad before Hbad.
  split.
  - apply fsem02AdaptiveClientBadHeadMasksResource; exact Hbad.
  - unfold fsem02AdaptiveHeadShapeGate, fsem02AdaptiveShapeGatedPing,
      fsem02AdaptiveResourceShapeCheck.
    repeat rewrite Nat.eqb_refl.
    reflexivity.
Qed.

(* The other peer's mismatched endpoint resource head remains an independent
   fault even when its projected session head was never changed. *)
Theorem fsem02CrossPeerClientHeadServerWrongSessionLadder :
  forall client server ec es bad resourceHead before,
    ec <> bad -> es <> resourceHead ->
    fsem02AdaptiveHeadShapeGate client server ec es bad es
      (FSEM02EndpointResource ec) (FSEM02EndpointResource resourceHead) before =
      FSEM02HeadMismatch client ec bad /\
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      (FSEM02EndpointResource ec) (FSEM02EndpointResource resourceHead) before =
      FSEM02ShapeMismatch server FSEM02WrongResourceSession.
Proof.
  intros client server ec es bad resourceHead before Hbad Hwrong.
  split.
  - apply fsem02AdaptiveClientBadHeadMasksResource; exact Hbad.
  - unfold fsem02AdaptiveHeadShapeGate, fsem02AdaptiveShapeGatedPing,
      fsem02AdaptiveResourceShapeCheck.
    assert (Hresource : Nat.eqb es resourceHead = false).
    { apply Nat.eqb_neq; exact Hwrong. }
    repeat rewrite Nat.eqb_refl.
    now rewrite Hresource.
Qed.

(* Dual direction: a bad Server projected head takes priority over the
   Client resource shape, because both projected heads are checked first. *)
Theorem fsem02CrossPeerServerHeadClientWrongTypeLadder :
  forall client server ec es bad before,
    es <> bad ->
    fsem02AdaptiveHeadShapeGate client server ec es ec bad
      FSEM02NonEndpointResource (FSEM02EndpointResource es) before =
      FSEM02HeadMismatch server es bad /\
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      FSEM02NonEndpointResource (FSEM02EndpointResource es) before =
      FSEM02ShapeMismatch client FSEM02WrongResourceType.
Proof.
  intros client server ec es bad before Hbad.
  split.
  - apply fsem02AdaptiveServerBadHeadMasksResource; exact Hbad.
  - unfold fsem02AdaptiveHeadShapeGate, fsem02AdaptiveShapeGatedPing,
      fsem02AdaptiveResourceShapeCheck.
    repeat rewrite Nat.eqb_refl.
    reflexivity.
Qed.

Theorem fsem02CrossPeerServerHeadClientWrongSessionLadder :
  forall client server ec es bad resourceHead before,
    es <> bad -> ec <> resourceHead ->
    fsem02AdaptiveHeadShapeGate client server ec es ec bad
      (FSEM02EndpointResource resourceHead) (FSEM02EndpointResource es) before =
      FSEM02HeadMismatch server es bad /\
    fsem02AdaptiveHeadShapeGate client server ec es ec es
      (FSEM02EndpointResource resourceHead) (FSEM02EndpointResource es) before =
      FSEM02ShapeMismatch client FSEM02WrongResourceSession.
Proof.
  intros client server ec es bad resourceHead before Hbad Hwrong.
  split.
  - apply fsem02AdaptiveServerBadHeadMasksResource; exact Hbad.
  - unfold fsem02AdaptiveHeadShapeGate, fsem02AdaptiveShapeGatedPing,
      fsem02AdaptiveResourceShapeCheck.
    assert (Hresource : Nat.eqb ec resourceHead = false).
    { apply Nat.eqb_neq; exact Hwrong. }
    repeat rewrite Nat.eqb_refl.
    now rewrite Hresource.
Qed.

(* Repaired exact suffix remains conditional on the separate phase-map
   preconditions and an externally selected live pair. No native refinement
   or permission to retire either endpoint follows from this equality. *)
Theorem fsem02CrossPeerShapeBothRepairedHalfClose :
  forall priorClient priorServer freeClient freeServer
         priorClientPhase priorServerPhase ec es before,
    freeClient <> priorClient -> freeClient <> priorServer ->
    freeServer <> priorClient -> freeServer <> priorServer ->
    before freeClient = FSEM02AwaitPing ->
    before freeServer = FSEM02AwaitPing ->
    let prefix := fsem02MixWrite priorClient priorClientPhase
      (fsem02MixWrite priorServer priorServerPhase before) in
    fsem02AdaptiveHeadShapeGate freeClient freeServer ec es ec es
      (FSEM02EndpointResource ec) (FSEM02EndpointResource es) prefix =
      FSEM02HeadShapeStep (Some (fsem02MixWrite freeServer FSEM02LiveEnd
        (fsem02MixWrite freeClient FSEM02LiveEnd prefix))).
Proof.
  intros priorClient priorServer freeClient freeServer
    priorClientPhase priorServerPhase ec es before
    Hcc Hcs Hsc Hss Hc Hs.
  exact (fsem02CrossPeerHalfCloseFullyRepaired
    priorClient priorServer freeClient freeServer
    priorClientPhase priorServerPhase ec es before
    Hcc Hcs Hsc Hss Hc Hs).
Qed.
