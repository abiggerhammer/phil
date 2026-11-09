From Stdlib Require Import Strings.String Bool.Bool.
Open Scope string_scope.

(*
  Non-normative FSEM-02 checked-source carrier projection. Production Haskell
  compares full typed rendezvous requests and source-resolved payload names.
  The proof checks only an abstract request identity key and two names;
  injective request encoding, parser fidelity, source authority and Haskell
  record equality correspondence are external premises.
*)
Definition fsem02CloseCarrierMatches
  (expectedRequest actualRequest
   expectedSent actualSent expectedReceived actualReceived : string) : bool :=
  String.eqb expectedRequest actualRequest
    && String.eqb expectedSent actualSent
    && String.eqb expectedReceived actualReceived.

Theorem fsem02CloseCarrierSuccessExact :
  forall expectedRequest actualRequest
         expectedSent actualSent expectedReceived actualReceived,
    fsem02CloseCarrierMatches
      expectedRequest actualRequest expectedSent actualSent
      expectedReceived actualReceived = true ->
    expectedRequest = actualRequest /\
    expectedSent = actualSent /\
    expectedReceived = actualReceived.
Proof.
  intros expectedRequest actualRequest expectedSent actualSent
    expectedReceived actualReceived Hmatch.
  unfold fsem02CloseCarrierMatches in Hmatch.
  apply andb_true_iff in Hmatch as [Hrequest Hrest].
  apply andb_true_iff in Hrest as [Hsent Hreceived].
  apply String.eqb_eq in Hrequest.
  apply String.eqb_eq in Hsent.
  apply String.eqb_eq in Hreceived.
  repeat split; assumption.
Qed.

Theorem fsem02CloseCarrierRejectsWrongRequest :
  forall expectedRequest actualRequest
         expectedSent actualSent expectedReceived actualReceived,
    expectedRequest <> actualRequest ->
    fsem02CloseCarrierMatches
      expectedRequest actualRequest expectedSent actualSent
      expectedReceived actualReceived = false.
Proof.
  intros er ar es as_ ev av Hneq.
  unfold fsem02CloseCarrierMatches.
  apply String.eqb_neq in Hneq.
  rewrite Hneq. reflexivity.
Qed.

Theorem fsem02CloseCarrierRejectsWrongSender :
  forall expectedRequest actualRequest
         expectedSent actualSent expectedReceived actualReceived,
    expectedSent <> actualSent ->
    fsem02CloseCarrierMatches
      expectedRequest actualRequest expectedSent actualSent
      expectedReceived actualReceived = false.
Proof.
  intros er ar es as_ ev av Hneq.
  unfold fsem02CloseCarrierMatches.
  apply String.eqb_neq in Hneq.
  rewrite Hneq. destruct (String.eqb er ar); reflexivity.
Qed.

Theorem fsem02CloseCarrierRejectsWrongReceiver :
  forall expectedRequest actualRequest
         expectedSent actualSent expectedReceived actualReceived,
    expectedReceived <> actualReceived ->
    fsem02CloseCarrierMatches
      expectedRequest actualRequest expectedSent actualSent
      expectedReceived actualReceived = false.
Proof.
  intros er ar es as_ ev av Hneq.
  unfold fsem02CloseCarrierMatches.
  apply String.eqb_neq in Hneq.
  rewrite Hneq.
  destruct (String.eqb er ar), (String.eqb es as_); reflexivity.
Qed.
