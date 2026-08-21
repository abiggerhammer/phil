From Stdlib Require Import Strings.String.

From Phil.Core Require Import Context Recognition.

(*
  The Haskell recognition API permits trusted recognition only while a shared
  raw loan is live, but commitReceive and failPendingRecognition must not consume
  the pending linear owner until that loan has ended.  These theorems compose
  that boundary directly with consumeLinear's fail-closed loan check.
*)

(* PHIL-RECOG-COMMIT-001: live raw access cannot authorize commit/destruction. *)
Theorem commitReceive_live_raw_loan_rejected :
  forall (capability : PendingCapability)
         (successor : Name)
         (parsed : ParsedWitness),
    sharedLoans (capabilityContext capability) (capabilityName capability) = true ->
    commitReceiveModel capability successor parsed = RecognitionRejected.
Proof.
  intros capability successor parsed Hloan.
  destruct capability as [pendingName pending context Howned].
  destruct pending as [source grammar frame binder continuation].
  destruct parsed as [parsedOwner parsedGrammarId parsedFrameId valueName].
  simpl in *.
  unfold commitReceiveModel.
  simpl.
  destruct (String.eqb parsedOwner pendingName) eqn:Howner.
  - destruct (String.eqb parsedGrammarId grammar) eqn:Hgrammar.
    + destruct (String.eqb parsedFrameId frame) eqn:Hframe.
      * destruct (String.eqb pendingName successor) eqn:HpendingSuccessor.
        -- reflexivity.
        -- destruct (String.eqb source successor) eqn:HsourceSuccessor.
           ++ reflexivity.
           ++ unfold consumeLinear.
              rewrite Hloan.
              reflexivity.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

(* PHIL-RECOG-FAIL-001: live raw access cannot destroy the pending capability. *)
Theorem failPendingRecognition_live_raw_loan_rejected :
  forall (capability : PendingCapability)
         (failure : RecognitionFailure),
    sharedLoans (capabilityContext capability) (capabilityName capability) = true ->
    failPendingRecognitionModel capability failure = RecognitionRejected.
Proof.
  intros capability failure Hloan.
  destruct capability as [pendingName pending context Howned].
  destruct pending as [source grammar frame binder continuation].
  destruct failure as [failureOwner failureGrammarId failureFrameId detail].
  simpl in *.
  unfold failPendingRecognitionModel.
  simpl.
  destruct (String.eqb failureOwner pendingName) eqn:Howner.
  - destruct (String.eqb failureGrammarId grammar) eqn:Hgrammar.
    + destruct (String.eqb failureFrameId frame) eqn:Hframe.
      * unfold consumeLinear.
        rewrite Hloan.
        reflexivity.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.
