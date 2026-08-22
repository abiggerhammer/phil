From Stdlib Require Import Strings.String.

From Phil.Core Require Import Syntax Context SessionStep.

(*
  Proof-oriented model of the surface/Core successor-owner bridge.

  The Core session step already proves that a successful non-close transition
  consumes the old linear endpoint and installs a distinct successor owner.
  The surface checker then immediately consumes that synthetic successor from
  Core, carries its endpoint type as a value, and inserts that type under the
  programmer-visible surface name only when that final name is globally fresh.

  This file proves that the bridge never needs two simultaneous owners for the
  same continuation.  Concrete fresh-name generation and the reserved '$...'
  namespace remain implementation correspondence assumptions; successful Core
  insertion itself still enforces actual global freshness.
*)

Inductive SurfaceRebindResult : Type :=
| SurfaceRebindFailed : SurfaceRebindResult
| SurfaceRebindSucceeded :
    Ty ->
    ResourceContext -> (* staged Core successor under synthetic temp *)
    ResourceContext -> (* temp extracted/consumed *)
    ResourceContext -> (* rebound under programmer-visible name *)
    SurfaceRebindResult.

Definition surfaceProgressAndRebind
  (endpoint temp surfaceName : Name)
  (continuation : Session)
  (context : ResourceContext) : SurfaceRebindResult :=
  match continueEndpointResource endpoint temp continuation context with
  | StepFailed => SurfaceRebindFailed
  | StepSucceeded staged =>
      match consumeLinear temp staged with
      | ConsumeError _ => SurfaceRebindFailed
      | Consumed ty extracted =>
          match insertBinding Linear surfaceName ty extracted with
          | InsertError _ => SurfaceRebindFailed
          | Inserted rebound =>
              SurfaceRebindSucceeded ty staged extracted rebound
          end
      end
  end.

(* PHIL-SURFACE-FRESH-001.

   A successful surface bridge has three ownership phases:

   1. staged: old endpoint absent, synthetic temp owns the continuation;
   2. extracted: old endpoint and synthetic temp are both absent;
   3. rebound: the final source name was globally fresh and is the sole newly
      inserted linear owner for the continuation.
*)
Theorem surface_progress_rebind_success_exact :
  forall endpoint temp surfaceName continuation context ty staged extracted rebound,
    surfaceProgressAndRebind
      endpoint temp surfaceName continuation context =
      SurfaceRebindSucceeded ty staged extracted rebound ->
    String.eqb endpoint temp = false /\
    (exists endpointTy : Ty,
      linearBindings context endpoint = Some endpointTy) /\
    linearBindings staged endpoint = None /\
    linearBindings staged temp = Some (endpointType continuation) /\
    ty = endpointType continuation /\
    linearBindings extracted endpoint = None /\
    linearBindings extracted temp = None /\
    unrestrictedBindings extracted surfaceName = None /\
    affineBindings extracted surfaceName = None /\
    linearBindings extracted surfaceName = None /\
    unrestrictedBindings rebound surfaceName = None /\
    affineBindings rebound surfaceName = None /\
    linearBindings rebound surfaceName = Some (endpointType continuation) /\
    (String.eqb temp surfaceName = false ->
      linearBindings rebound temp = None) /\
    (String.eqb endpoint surfaceName = false ->
      linearBindings rebound endpoint = None).
Proof.
  intros endpoint temp surfaceName continuation context ty staged extracted rebound Hsurface.
  unfold surfaceProgressAndRebind in Hsurface.
  destruct (continueEndpointResource endpoint temp continuation context)
    as [| stagedResult] eqn:Hcontinue.
  - discriminate.
  - destruct (consumeLinear temp stagedResult)
      as [consumeError | extractedTy extractedResult] eqn:Hextract.
    + discriminate.
    + destruct (insertBinding Linear surfaceName extractedTy extractedResult)
        as [insertError | reboundResult] eqn:Hinsert.
      * discriminate.
      * inversion Hsurface; subst ty staged extracted rebound; clear Hsurface.
        pose proof
          (continueEndpointResource_success_exact
            endpoint temp continuation context stagedResult Hcontinue)
          as HcontinueExact.
        destruct HcontinueExact as
          [HendpointTemp
            [HendpointOwned
              [HstagedEndpoint
                [HstagedTemp
                  [HstagedOther HstagedLoans]]]]].

        pose proof
          (consumeLinear_success_exact
            temp stagedResult extractedResult extractedTy Hextract)
          as HextractExact.
        destruct HextractExact as
          [HextractOwned
            [HextractedTemp
              [HextractOther
                [HextractU [HextractA HextractLoans]]]]].

        assert (Hty : extractedTy = endpointType continuation).
        { rewrite HstagedTemp in HextractOwned.
          inversion HextractOwned.
          reflexivity. }
        subst extractedTy.

        pose proof (HextractOther endpoint HendpointTemp) as HextractedEndpoint.
        rewrite HstagedEndpoint in HextractedEndpoint.

        pose proof
          (insertBinding_success_exact
            Linear surfaceName (endpointType continuation)
            extractedResult reboundResult Hinsert)
          as HinsertExact.
        destruct HinsertExact as
          [HfreshU
            [HfreshA
              [HfreshL
                [Hinstalled
                  [HinsertOther HinsertLoans]]]]].
        simpl in Hinstalled.
        destruct Hinstalled as [HreboundU [HreboundA HreboundLinear]].

        repeat split.
        -- exact HendpointTemp.
        -- exact HendpointOwned.
        -- exact HstagedEndpoint.
        -- exact HstagedTemp.
        -- reflexivity.
        -- exact HextractedEndpoint.
        -- exact HextractedTemp.
        -- exact HfreshU.
        -- exact HfreshA.
        -- exact HfreshL.
        -- exact HreboundU.
        -- exact HreboundA.
        -- exact HreboundLinear.
        -- intro HtempSurface.
           pose proof (HinsertOther temp HtempSurface) as HtempPreserved.
           destruct HtempPreserved as [_ [_ HtempLinear]].
           rewrite HtempLinear.
           exact HextractedTemp.
        -- intro HendpointSurface.
           pose proof (HinsertOther endpoint HendpointSurface) as HendpointPreserved.
           destruct HendpointPreserved as [_ [_ HendpointLinear]].
           rewrite HendpointLinear.
           exact HextractedEndpoint.
Qed.

(* The final source insertion itself proves that no pre-existing resource at
   that programmer-visible name was silently overwritten. *)
Theorem successful_surface_rebind_requires_final_name_freshness :
  forall endpoint temp surfaceName continuation context ty staged extracted rebound,
    surfaceProgressAndRebind
      endpoint temp surfaceName continuation context =
      SurfaceRebindSucceeded ty staged extracted rebound ->
    unrestrictedBindings extracted surfaceName = None /\
    affineBindings extracted surfaceName = None /\
    linearBindings extracted surfaceName = None.
Proof.
  intros endpoint temp surfaceName continuation context ty staged extracted rebound Hsurface.
  pose proof
    (surface_progress_rebind_success_exact
      endpoint temp surfaceName continuation context
      ty staged extracted rebound Hsurface)
    as H.
  destruct H as
    [_ [_ [_ [_ [_ [_ [_ [HU [HA [HL _]]]]]]]]]].
  repeat split; assumption.
Qed.

(* Immediately before the programmer-visible rebind there is no live Core owner
   under either the old endpoint name or the synthetic temporary name. *)
Theorem successful_surface_rebind_has_no_intermediate_duplicate_owner :
  forall endpoint temp surfaceName continuation context ty staged extracted rebound,
    surfaceProgressAndRebind
      endpoint temp surfaceName continuation context =
      SurfaceRebindSucceeded ty staged extracted rebound ->
    linearBindings extracted endpoint = None /\
    linearBindings extracted temp = None.
Proof.
  intros endpoint temp surfaceName continuation context ty staged extracted rebound Hsurface.
  pose proof
    (surface_progress_rebind_success_exact
      endpoint temp surfaceName continuation context
      ty staged extracted rebound Hsurface)
    as H.
  destruct H as
    [_ [_ [_ [_ [_ [Hendpoint [Htemp _]]]]]]].
  split; assumption.
Qed.
