From Stdlib Require Import Bool.Bool Lists.List.
Import ListNotations.

From Phil.Core Require Import ProviderQualificationImplementationBridge.

(*
  PHIL-PROV-LIFECYCLE-IMPL-001 — finite executable PROV-008 lifecycle checking.

  The kernel owns exact interruption-point domain correspondence, operation
  qualification, and universal checking of every modeled interruption
  observation against the declared public boundary and allowance relation.
*)

Definition ProviderLifecyclePointProjection
  (OperationKey InterruptionKey : Type) : Type :=
  (OperationKey * InterruptionKey)%type.

Definition ProviderLifecycleAllowanceProjection
  (ObservableState CleanupResidue RetryDisposition : Type) : Type :=
  (list ObservableState * (list CleanupResidue * list RetryDisposition))%type.

Definition ProviderLifecycleObservationProjection
  (Boundary ObservableState CleanupResidue RetryDisposition : Type) : Type :=
  (Boundary * (ObservableState * (CleanupResidue * RetryDisposition)))%type.

Fixpoint memberb
  {A : Type}
  (eqA : A -> A -> bool)
  (needle : A)
  (values : list A) : bool :=
  match values with
  | [] => false
  | value :: rest => eqA needle value || memberb eqA needle rest
  end.

Definition lifecyclePointEqualb
  {OperationKey InterruptionKey : Type}
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqInterruption : InterruptionKey -> InterruptionKey -> bool)
  (first second : ProviderLifecyclePointProjection OperationKey InterruptionKey)
  : bool :=
  eqOperation (fst first) (fst second) &&
  eqInterruption (snd first) (snd second).

Definition checkProviderLifecycleObservation
  {Boundary ObservableState CleanupResidue RetryDisposition : Type}
  (eqBoundary : Boundary -> Boundary -> bool)
  (eqObservableState : ObservableState -> ObservableState -> bool)
  (eqCleanupResidue : CleanupResidue -> CleanupResidue -> bool)
  (eqRetryDisposition : RetryDisposition -> RetryDisposition -> bool)
  (contractBoundary : Boundary)
  (allowance
    : ProviderLifecycleAllowanceProjection
        ObservableState CleanupResidue RetryDisposition)
  (observation
    : ProviderLifecycleObservationProjection
        Boundary ObservableState CleanupResidue RetryDisposition) : bool :=
  eqBoundary contractBoundary (fst observation) &&
  memberb eqObservableState
    (fst (snd observation))
    (fst allowance) &&
  memberb eqCleanupResidue
    (fst (snd (snd observation)))
    (fst (snd allowance)) &&
  memberb eqRetryDisposition
    (snd (snd (snd observation)))
    (snd (snd allowance)).

Definition checkProviderLifecyclePoint
  {OperationKey InterruptionKey Boundary ObservableState CleanupResidue
    RetryDisposition : Type}
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqInterruption : InterruptionKey -> InterruptionKey -> bool)
  (eqBoundary : Boundary -> Boundary -> bool)
  (eqObservableState : ObservableState -> ObservableState -> bool)
  (eqCleanupResidue : CleanupResidue -> CleanupResidue -> bool)
  (eqRetryDisposition : RetryDisposition -> RetryDisposition -> bool)
  (qualifiedOperations : list OperationKey)
  (contractBoundary : Boundary)
  (observations
    : list
        (ProviderLifecyclePointProjection OperationKey InterruptionKey *
         list
           (ProviderLifecycleObservationProjection
              Boundary ObservableState CleanupResidue RetryDisposition)))
  (entry
    : ProviderLifecyclePointProjection OperationKey InterruptionKey *
      ProviderLifecycleAllowanceProjection
        ObservableState CleanupResidue RetryDisposition) : bool :=
  let point := fst entry in
  let allowance := snd entry in
  match lookupAssoc
      (lifecyclePointEqualb eqOperation eqInterruption)
      point observations with
  | None => false
  | Some pointObservations =>
      memberb eqOperation (fst point) qualifiedOperations &&
      allFiniteb
        (checkProviderLifecycleObservation
          eqBoundary eqObservableState eqCleanupResidue eqRetryDisposition
          contractBoundary allowance)
        pointObservations
  end.

Definition decideProviderLifecycleQualification
  {OperationKey InterruptionKey Boundary ObservableState CleanupResidue
    RetryDisposition : Type}
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqInterruption : InterruptionKey -> InterruptionKey -> bool)
  (eqBoundary : Boundary -> Boundary -> bool)
  (eqObservableState : ObservableState -> ObservableState -> bool)
  (eqCleanupResidue : CleanupResidue -> CleanupResidue -> bool)
  (eqRetryDisposition : RetryDisposition -> RetryDisposition -> bool)
  (qualifiedOperations : list OperationKey)
  (contractBoundary : Boundary)
  (allowances
    : list
        (ProviderLifecyclePointProjection OperationKey InterruptionKey *
         ProviderLifecycleAllowanceProjection
           ObservableState CleanupResidue RetryDisposition))
  (observations
    : list
        (ProviderLifecyclePointProjection OperationKey InterruptionKey *
         list
           (ProviderLifecycleObservationProjection
              Boundary ObservableState CleanupResidue RetryDisposition))) : bool :=
  sameKeyDomainb
    (lifecyclePointEqualb eqOperation eqInterruption)
    allowances observations &&
  allFiniteb
    (checkProviderLifecyclePoint
      eqOperation eqInterruption eqBoundary eqObservableState
      eqCleanupResidue eqRetryDisposition qualifiedOperations
      contractBoundary observations)
    allowances.

Definition ProviderLifecycleTraversalAccepts
  {OperationKey InterruptionKey Boundary ObservableState CleanupResidue
    RetryDisposition : Type}
  (eqOperation : OperationKey -> OperationKey -> bool)
  (eqInterruption : InterruptionKey -> InterruptionKey -> bool)
  (eqBoundary : Boundary -> Boundary -> bool)
  (eqObservableState : ObservableState -> ObservableState -> bool)
  (eqCleanupResidue : CleanupResidue -> CleanupResidue -> bool)
  (eqRetryDisposition : RetryDisposition -> RetryDisposition -> bool)
  (qualifiedOperations : list OperationKey)
  (contractBoundary : Boundary)
  (allowances
    : list
        (ProviderLifecyclePointProjection OperationKey InterruptionKey *
         ProviderLifecycleAllowanceProjection
           ObservableState CleanupResidue RetryDisposition))
  (observations
    : list
        (ProviderLifecyclePointProjection OperationKey InterruptionKey *
         list
           (ProviderLifecycleObservationProjection
              Boundary ObservableState CleanupResidue RetryDisposition))) : Prop :=
  sameKeyDomainb
    (lifecyclePointEqualb eqOperation eqInterruption)
    allowances observations = true /\
  allFiniteb
    (checkProviderLifecyclePoint
      eqOperation eqInterruption eqBoundary eqObservableState
      eqCleanupResidue eqRetryDisposition qualifiedOperations
      contractBoundary observations)
    allowances = true.

Theorem decide_provider_lifecycle_qualification_true_iff :
  forall
    (OperationKey InterruptionKey Boundary ObservableState CleanupResidue
      RetryDisposition : Type)
    (eqOperation : OperationKey -> OperationKey -> bool)
    (eqInterruption : InterruptionKey -> InterruptionKey -> bool)
    (eqBoundary : Boundary -> Boundary -> bool)
    (eqObservableState : ObservableState -> ObservableState -> bool)
    (eqCleanupResidue : CleanupResidue -> CleanupResidue -> bool)
    (eqRetryDisposition : RetryDisposition -> RetryDisposition -> bool)
    (qualifiedOperations : list OperationKey)
    (contractBoundary : Boundary)
    (allowances
      : list
          (ProviderLifecyclePointProjection OperationKey InterruptionKey *
           ProviderLifecycleAllowanceProjection
             ObservableState CleanupResidue RetryDisposition))
    (observations
      : list
          (ProviderLifecyclePointProjection OperationKey InterruptionKey *
           list
             (ProviderLifecycleObservationProjection
                Boundary ObservableState CleanupResidue RetryDisposition))),
    decideProviderLifecycleQualification
      eqOperation eqInterruption eqBoundary eqObservableState
      eqCleanupResidue eqRetryDisposition qualifiedOperations
      contractBoundary allowances observations = true <->
    ProviderLifecycleTraversalAccepts
      eqOperation eqInterruption eqBoundary eqObservableState
      eqCleanupResidue eqRetryDisposition qualifiedOperations
      contractBoundary allowances observations.
Proof.
  intros OperationKey InterruptionKey Boundary ObservableState CleanupResidue
    RetryDisposition eqOperation eqInterruption eqBoundary eqObservableState
    eqCleanupResidue eqRetryDisposition qualifiedOperations contractBoundary
    allowances observations.
  unfold decideProviderLifecycleQualification,
    ProviderLifecycleTraversalAccepts.
  rewrite Bool.andb_true_iff.
  reflexivity.
Qed.

Theorem missing_provider_lifecycle_observations_reject_point :
  forall
    (OperationKey InterruptionKey Boundary ObservableState CleanupResidue
      RetryDisposition : Type)
    (eqOperation : OperationKey -> OperationKey -> bool)
    (eqInterruption : InterruptionKey -> InterruptionKey -> bool)
    (eqBoundary : Boundary -> Boundary -> bool)
    (eqObservableState : ObservableState -> ObservableState -> bool)
    (eqCleanupResidue : CleanupResidue -> CleanupResidue -> bool)
    (eqRetryDisposition : RetryDisposition -> RetryDisposition -> bool)
    (qualifiedOperations : list OperationKey)
    (contractBoundary : Boundary)
    (observations
      : list
          (ProviderLifecyclePointProjection OperationKey InterruptionKey *
           list
             (ProviderLifecycleObservationProjection
                Boundary ObservableState CleanupResidue RetryDisposition)))
    (point : ProviderLifecyclePointProjection OperationKey InterruptionKey)
    (allowance
      : ProviderLifecycleAllowanceProjection
          ObservableState CleanupResidue RetryDisposition),
    lookupAssoc
      (lifecyclePointEqualb eqOperation eqInterruption)
      point observations = None ->
    checkProviderLifecyclePoint
      eqOperation eqInterruption eqBoundary eqObservableState
      eqCleanupResidue eqRetryDisposition qualifiedOperations
      contractBoundary observations (point, allowance) = false.
Proof.
  intros OperationKey InterruptionKey Boundary ObservableState CleanupResidue
    RetryDisposition eqOperation eqInterruption eqBoundary eqObservableState
    eqCleanupResidue eqRetryDisposition qualifiedOperations contractBoundary
    observations point allowance Hmissing.
  unfold checkProviderLifecyclePoint.
  cbn.
  rewrite Hmissing.
  reflexivity.
Qed.

Theorem wrong_provider_lifecycle_boundary_rejects_observation :
  forall
    (Boundary ObservableState CleanupResidue RetryDisposition : Type)
    (eqBoundary : Boundary -> Boundary -> bool)
    (eqObservableState : ObservableState -> ObservableState -> bool)
    (eqCleanupResidue : CleanupResidue -> CleanupResidue -> bool)
    (eqRetryDisposition : RetryDisposition -> RetryDisposition -> bool)
    (contractBoundary : Boundary)
    (allowance
      : ProviderLifecycleAllowanceProjection
          ObservableState CleanupResidue RetryDisposition)
    (observation
      : ProviderLifecycleObservationProjection
          Boundary ObservableState CleanupResidue RetryDisposition),
    eqBoundary contractBoundary (fst observation) = false ->
    checkProviderLifecycleObservation
      eqBoundary eqObservableState eqCleanupResidue eqRetryDisposition
      contractBoundary allowance observation = false.
Proof.
  intros Boundary ObservableState CleanupResidue RetryDisposition
    eqBoundary eqObservableState eqCleanupResidue eqRetryDisposition
    contractBoundary allowance observation Hboundary.
  unfold checkProviderLifecycleObservation.
  rewrite Hboundary.
  reflexivity.
Qed.
