(*
  FSEM-06 proposed bounded selected Core semantics.  The native selector
  below is extracted into the standalone actual-object admission path.
  The trace relation imports the accepted FSEM-05 *labelled* rules, not
  its label-erasing closure.  Neither native provider authenticity nor
  Haskell/Rocq representation/simulation is asserted by these theorems.
*)
From Stdlib Require Import List Arith Lia Bool.Bool Strings.String Strings.Ascii Extraction.
From Phil.Verification Require Import FSEM05SteveGetSelectedSourceEvents.
Import ListNotations SelectedSteveGetEvents.
Local Open Scope string_scope.
Local Open Scope list_scope.

(* Exact, finite, typed representation of the admitted native selected
   function and complete plan, including map keys and nonsemantic native
   realization/cleanup keys.  Native Map validity precedes this adapter. *)
Definition name := list nat.
Fixpoint nm (s : string) : name :=
  match s with
  | EmptyString => []
  | String c rest => nat_of_ascii c :: nm rest
  end.

Inductive NativeRole :=
| NScalar : name -> NativeRole
| NOwned : name -> NativeRole
| NBorrowed : name -> NativeRole.
Inductive NativeValue :=
| NValue : name -> name -> NativeRole -> option name -> NativeValue.
Inductive NativeOp :=
| NRelease : name -> name -> NativeOp
| NTrace : name -> NativeOp.
Inductive NativeTerm :=
| NChoice : name -> list name -> option name -> list (name * name) -> NativeTerm
| NEnd : name -> NativeTerm.
Inductive NativeBlock :=
| NBlock : name -> name -> list NativeOp -> NativeTerm -> NativeBlock.
Inductive NativeFunction :=
| NFunction : name -> name -> name -> list NativeValue -> list NativeBlock -> NativeFunction.
Inductive NativeArm :=
| NArm : name -> name -> option name -> NativeArm.
Inductive NativeSpec :=
| NSpec : name -> name -> name -> name -> list NativeArm -> NativeSpec.
Inductive NativeSubject :=
| NSubject : name -> name -> name -> name -> NativeFunction ->
    list NativeSpec -> NativeSubject.

Definition name_dec : forall x y : name, {x = y} + {x <> y}.
Proof. apply list_eq_dec. exact Nat.eq_dec. Defined.
Definition names_dec : forall x y : list name, {x = y} + {x <> y}.
Proof. apply list_eq_dec. exact name_dec. Defined.
Definition optional_name_dec : forall x y : option name, {x = y} + {x <> y}.
Proof. decide equality; apply name_dec. Defined.
Definition name_pair_dec : forall x y : name * name, {x = y} + {x <> y}.
Proof. decide equality; apply name_dec. Defined.
Definition name_pairs_dec : forall x y : list (name * name), {x = y} + {x <> y}.
Proof. apply list_eq_dec. exact name_pair_dec. Defined.
Definition role_dec : forall x y : NativeRole, {x = y} + {x <> y}.
Proof. decide equality; apply name_dec. Defined.
Definition value_dec : forall x y : NativeValue, {x = y} + {x <> y}.
Proof. decide equality; first [apply name_dec | apply role_dec | apply optional_name_dec]. Defined.
Definition values_dec : forall x y : list NativeValue, {x = y} + {x <> y}.
Proof. apply list_eq_dec. exact value_dec. Defined.
Definition op_dec : forall x y : NativeOp, {x = y} + {x <> y}.
Proof. decide equality; apply name_dec. Defined.
Definition ops_dec : forall x y : list NativeOp, {x = y} + {x <> y}.
Proof. apply list_eq_dec. exact op_dec. Defined.
Definition term_dec : forall x y : NativeTerm, {x = y} + {x <> y}.
Proof.
  decide equality;
    first [apply name_dec | apply names_dec | apply optional_name_dec | apply name_pairs_dec].
Defined.
Definition block_dec : forall x y : NativeBlock, {x = y} + {x <> y}.
Proof. decide equality; first [apply name_dec | apply ops_dec | apply term_dec]. Defined.
Definition blocks_dec : forall x y : list NativeBlock, {x = y} + {x <> y}.
Proof. apply list_eq_dec. exact block_dec. Defined.
Definition function_dec : forall x y : NativeFunction, {x = y} + {x <> y}.
Proof. decide equality; first [apply name_dec | apply values_dec | apply blocks_dec]. Defined.
Definition arm_dec : forall x y : NativeArm, {x = y} + {x <> y}.
Proof. decide equality; first [apply name_dec | apply optional_name_dec]. Defined.
Definition arms_dec : forall x y : list NativeArm, {x = y} + {x <> y}.
Proof. apply list_eq_dec. exact arm_dec. Defined.
Definition spec_dec : forall x y : NativeSpec, {x = y} + {x <> y}.
Proof. decide equality; first [apply name_dec | apply arms_dec]. Defined.
Definition specs_dec : forall x y : list NativeSpec, {x = y} + {x <> y}.
Proof. apply list_eq_dec. exact spec_dec. Defined.
Definition subject_dec : forall x y : NativeSubject, {x = y} + {x <> y}.
Proof. decide equality; first [apply name_dec | apply function_dec | apply specs_dec]. Defined.

Definition a (label target : string) (payload : option string) : NativeArm :=
  NArm (nm label) (nm target) (option_map nm payload).
Definition spec (fn block : string) (arms : list NativeArm) : NativeSpec :=
  NSpec (nm fn) (nm block) (nm fn) (nm block) arms.
Definition b (key : string) (ops : list NativeOp) (term : NativeTerm) : NativeBlock :=
  NBlock (nm key) (nm key) ops term.
Definition v (key : string) (role : NativeRole) (storage : option string) : NativeValue :=
  NValue (nm key) (nm key) role (option_map nm storage).
Definition arm_target (label target : string) : name * name := (nm label, nm target).
Definition end_block (key label : string) (ops : list NativeOp) : NativeBlock :=
  b key ops (NEnd (nm label)).
Definition release_bytes := NRelease (nm "cleanup") (nm "get.bytes").
Definition trace_commit := NTrace (nm "steve.get.commit").

(* Canonical finite contract, ordered exactly by the actual native Map keys.
   Full Steve program identity is separately checked before selecting this
   function; this representation retains all selected-function fields and
   all four actual plan sites, including the unexecuted StevePut sites. *)
Definition expected_native : NativeSubject :=
  NSubject (nm "decl:steve.get") (nm "inst:phase1.steve")
    (nm "BlobProvider.read") (nm "DigestProvider.check")
    (NFunction (nm "SteveGet") (nm "SteveGet") (nm "get.entry")
      [ v "get.bytes" (NOwned (nm "OwnedBytes")) (Some "steve.read-result");
        v "get.bytes-view" (NBorrowed (nm "get.bytes")) None;
        v "get.id" (NScalar (nm "ContentId[SHA256]")) None ]
      [ b "get.check" []
          (NChoice (nm "DigestProvider.check") [nm "get.id"; nm "get.bytes-view"] None
            [arm_target "accepted" "get.ok"; arm_target "rejected" "get.integrity-failure"]);
        b "get.entry" []
          (NChoice (nm "BlobProvider.read") [nm "get.id"] None
            [arm_target "found" "get.check"; arm_target "not-found" "get.not-found";
             arm_target "storage-failure" "get.failure"]);
        end_block "get.failure" "storage-failure" [];
        end_block "get.integrity-failure" "integrity-failure" [release_bytes];
        end_block "get.not-found" "not-found" [];
        end_block "get.ok" "success" [release_bytes; trace_commit] ])
    [ spec "SteveGet" "get.check"
        [a "accepted" "get.ok" None; a "rejected" "get.integrity-failure" None];
      spec "SteveGet" "get.entry"
        [a "found" "get.check" (Some "get.bytes"); a "not-found" "get.not-found" None;
         a "storage-failure" "get.failure" None];
      spec "StevePut" "put.entry" [a "computed" "put.install" (Some "put.id")];
      spec "StevePut" "put.install"
        [a "already-exists" "put.ok" None; a "installed" "put.ok" None;
         a "storage-failure" "put.failure" None] ].

Definition selected_native_accepts (input : NativeSubject) : bool :=
  if subject_dec input expected_native then true else false.

Theorem selected_native_reflection : forall input,
  selected_native_accepts input = true <-> input = expected_native.
Proof.
  intro input. unfold selected_native_accepts.
  destruct (subject_dec input expected_native); split; intro H;
    try reflexivity; try assumption; try discriminate; contradiction.
Qed.

Definition name_eqb (x y : name) := if name_dec x y then true else false.
Definition names_eqb (x y : list name) := if names_dec x y then true else false.

(* The dynamic rule checks the actual selected block, operation, operands,
   runtime site, control arm and separately supplied plan arm. *)
Definition choice_present (input : NativeSubject)
    (pc operation : string) (operands : list string)
    (label target : string) (payload : option string) : bool :=
  match input with
  | NSubject _ _ _ _ (NFunction _ fn _ _ blocks) specs =>
    let k := nm pc in
    let wanted_arm := a label target payload in
    andb
      (existsb (fun block =>
        match block with
        | NBlock mapkey blockkey [] (NChoice op args None arms) =>
          andb (name_eqb mapkey k)
            (andb (name_eqb blockkey k)
              (andb (name_eqb op (nm operation))
                (andb (names_eqb args (map nm operands))
                  (existsb (fun arm =>
                    if name_pair_dec arm (arm_target label target) then true else false) arms))))
        | _ => false
        end) blocks)
      (existsb (fun plan =>
        match plan with
        | NSpec mapfn mapblock specfn specblock arms =>
          andb (name_eqb mapfn fn)
            (andb (name_eqb mapblock k)
              (andb (name_eqb specfn fn)
                (andb (name_eqb specblock k)
                  (existsb (fun arm => if arm_dec arm wanted_arm then true else false) arms))))
        end) specs)
  end.

Definition end_present (input : NativeSubject) (pc label : string)
    (ops : list NativeOp) : bool :=
  match input with
  | NSubject _ _ _ _ (NFunction _ _ _ _ blocks) _ =>
      existsb (fun block => if block_dec block (end_block pc label ops) then true else false) blocks
  end.

Definition read_choice input label target payload :=
  choice_present input "get.entry" "BlobProvider.read" ["get.id"] label target payload.
Definition digest_choice input label target :=
  choice_present input "get.check" "DigestProvider.check" ["get.id"; "get.bytes-view"]
    label target None.

Theorem accepted_native_has_exact_choices : forall input,
  selected_native_accepts input = true ->
  read_choice input "found" "get.check" (Some "get.bytes") = true /\
  read_choice input "not-found" "get.not-found" None = true /\
  read_choice input "storage-failure" "get.failure" None = true /\
  digest_choice input "accepted" "get.ok" = true /\
  digest_choice input "rejected" "get.integrity-failure" = true /\
  end_present input "get.ok" "success" [release_bytes; trace_commit] = true /\
  end_present input "get.integrity-failure" "integrity-failure" [release_bytes] = true /\
  end_present input "get.not-found" "not-found" [] = true /\
  end_present input "get.failure" "storage-failure" [] = true.
Proof.
  intros input H. apply selected_native_reflection in H. subst input.
  vm_compute. repeat split; reflexivity.
Qed.

Theorem accepted_native_rejects_wrong_destination : forall input,
  selected_native_accepts input = true ->
  read_choice input "found" "get.check" (Some "get.id") = false.
Proof.
  intros input H. apply selected_native_reflection in H. subst input.
  vm_compute. reflexivity.
Qed.

(* A fixed selected binding includes both exact source occurrences, both
   qualified provider revisions, and the original free ContentId.  A reply
   may choose an outcome, not a different binding or an owner/loan origin.
   These are mathematical representation fields; no claim of native
   attestation or Haskell-to-Rocq representation is made. *)
Record selected_binding := Binding {
  binding_declaration : name;
  binding_instance : name;
  binding_read_occurrence : name;
  binding_digest_occurrence : name;
  binding_blob_interface : name;
  binding_blob_implementation : name;
  binding_digest_interface : name;
  binding_digest_implementation : name;
  binding_content_id : name
}.

(* The dynamic binding must name the exact selected declaration and instance.
   The concrete adapter additionally checks the source descriptor's exact spans,
   qualified interface/implementation revisions and the immutable ContentId. *)
Definition binding_matches_native (input : NativeSubject) (binding : selected_binding) : Prop :=
  match input with
  | NSubject dk ik _ _ _ _ =>
      binding_declaration binding = dk /\ binding_instance binding = ik
  end.

Inductive qualified_reply :=
| QFound : selected_binding -> nat -> qualified_reply
| QNotFound : selected_binding -> qualified_reply
| QFailure : selected_binding -> qualified_reply
| QAccepted : selected_binding -> qualified_reply
| QRejected : selected_binding -> qualified_reply.

Definition reply_label (r : qualified_reply) : offered :=
  match r with
  | QFound _ payload => ReadFound payload
  | QNotFound _ => ReadNotFound
  | QFailure _ => ReadFailure
  | QAccepted _ => DigestAccepted
  | QRejected _ => DigestRejected
  end.

Inductive observation :=
| ObsFound : nat -> nat -> observation
| ObsNotFound : observation
| ObsFailure : observation
| ObsBorrow : nat -> nat -> observation
| ObsDigest : nat -> nat -> bool -> observation
| ObsClose : nat -> observation
| ObsRelease : nat -> observation
| ObsDiagnostic : name -> observation
| ObsUnit : unit_branch -> observation.

Definition accepted_branch (decision : bool) :=
  if decision then UnitAccepted else UnitRejected.

(* Target phases correspond to actual Core block boundaries.  The payload
   is carried in the target's owned result through the digest and release
   phases, not inferred from the source's payload-forgetting state. *)
Inductive target_state :=
| TRead : nat -> list nat -> list nat -> target_state
| TDigest : nat -> list nat -> list nat -> nat -> nat -> nat -> target_state
| TRelease : nat -> list nat -> list nat -> nat -> nat -> nat -> bool -> target_state
| TNonfoundEnd : nat -> list nat -> list nat -> unit_branch -> target_state
| TDone : nat -> list nat -> list nat -> unit_branch -> target_state.

Definition source_projection (c : target_state) : state :=
  match c with
  | TRead n issued retired => AwaitRead n issued retired
  | TDigest n issued retired _ owner loan => AwaitDigest n issued retired owner loan
  | TRelease n issued retired _ owner loan decision =>
      AwaitRelease n issued retired owner loan decision
  | TNonfoundEnd n issued retired branch => Done n issued retired branch
  | TDone n issued retired branch => Done n issued retired branch
  end.

Definition pending_unit (c : target_state) : list observation :=
  match c with TNonfoundEnd _ _ _ branch => [ObsUnit branch] | _ => [] end.

Definition erase_diagnostic (events : list observation) : list observation :=
  filter (fun event => match event with ObsDiagnostic _ => false | _ => true end) events.

Definition external_labels (labels : list offered) : list offered :=
  filter (fun label => match label with NoInput => false | _ => true end) labels.

(* Source observations are determined by actual labelled source rules.
   The accepted source state alone cannot distinguish ReadFound p and q. *)
Definition source_observe (s : state) (label : offered) : list observation :=
  match s, label with
  | AwaitRead n _ _, ReadFound payload => [ObsFound payload n]
  | AwaitRead _ _ _, ReadNotFound => [ObsNotFound; ObsUnit UnitNotFound]
  | AwaitRead _ _ _, ReadFailure => [ObsFailure; ObsUnit UnitStorageFailure]
  | AwaitBorrow n _ _ owner, NoInput => [ObsBorrow owner n]
  | AwaitDigest _ _ _ owner loan, DigestAccepted => [ObsDigest owner loan true]
  | AwaitDigest _ _ _ owner loan, DigestRejected => [ObsDigest owner loan false]
  | AwaitClose _ _ _ _ loan _, NoInput => [ObsClose loan]
  | AwaitRelease _ _ _ owner _ decision, NoInput =>
      [ObsRelease owner; ObsUnit (accepted_branch decision)]
  | _, _ => []
  end.

Inductive source_trace : state -> list offered -> list observation -> state -> Prop :=
| SourceTraceNil : forall s, source_trace s [] [] s
| SourceTraceCons : forall s label middle labels observations final,
    selected_source_step s label middle ->
    source_trace middle labels observations final ->
    source_trace s (label :: labels)
      (source_observe s label ++ observations) final.

Fixpoint replay_source (s : state) (labels : list offered)
    : option (state * list observation) :=
  match labels with
  | [] => Some (s, [])
  | label :: rest =>
      match selected_step_fn s label with
      | Advanced middle =>
          match replay_source middle rest with
          | Some (final, observations) => Some (final, source_observe s label ++ observations)
          | None => None
          end
      | _ => None
      end
  end.

Theorem replay_source_is_labelled : forall labels start final observations,
  replay_source start labels = Some (final, observations) ->
  source_trace start labels observations final.
Proof.
  induction labels as [|label rest IH]; intros start final observations H; simpl in H.
  - inversion H; subst; constructor.
  - destruct (selected_step_fn start label) as [middle| |] eqn:Hstep; try discriminate.
    destruct (replay_source middle rest) as [[last events]|] eqn:Hrest; try discriminate.
    inversion H; subst.
    eapply SourceTraceCons.
    + eapply selected_step_sound; exact Hstep.
    + eapply IH; exact Hrest.
Qed.

Lemma source_trace_forget : forall s labels observations final,
  source_trace s labels observations final -> selected_steps s final.
Proof. intros s labels observations final H; induction H; [constructor|econstructor; eauto]. Qed.

Lemma source_trace_append : forall s l1 o1 middle l2 o2 final,
  source_trace s l1 o1 middle ->
  source_trace middle l2 o2 final ->
  source_trace s (l1 ++ l2) (o1 ++ o2) final.
Proof.
  intros s l1 o1 middle l2 o2 final H1 H2.
  induction H1; simpl; [exact H2|].
  rewrite <- app_assoc. econstructor; eauto.
Qed.

(* Independent target rules: each actual-Core choice uses its exact plan;
   the target allocates its own owner/loan from its persistent supply.
   Every external step consumes the head of one fixed qualified E.
   Internal cleanup/end consumes no provider response. *)
Inductive core_step (input : NativeSubject) (binding : selected_binding) :
    target_state -> list qualified_reply -> target_state ->
    list qualified_reply -> list observation -> Prop :=
| CoreFound : forall n issued retired payload rest,
    selected_native_accepts input = true ->
    binding_matches_native input binding ->
    read_choice input "found" "get.check" (Some "get.bytes") = true ->
    core_step input binding (TRead n issued retired) (QFound binding payload :: rest)
      (TDigest (S (S n)) (S n :: n :: issued) retired payload n (S n)) rest
      [ObsFound payload n; ObsBorrow n (S n)]
| CoreNotFound : forall n issued retired rest,
    selected_native_accepts input = true ->
    binding_matches_native input binding ->
    read_choice input "not-found" "get.not-found" None = true ->
    core_step input binding (TRead n issued retired) (QNotFound binding :: rest)
      (TNonfoundEnd n issued retired UnitNotFound) rest [ObsNotFound]
| CoreFailure : forall n issued retired rest,
    selected_native_accepts input = true ->
    binding_matches_native input binding ->
    read_choice input "storage-failure" "get.failure" None = true ->
    core_step input binding (TRead n issued retired) (QFailure binding :: rest)
      (TNonfoundEnd n issued retired UnitStorageFailure) rest [ObsFailure]
| CoreDigestAccepted : forall n issued retired payload owner loan rest,
    selected_native_accepts input = true ->
    binding_matches_native input binding ->
    digest_choice input "accepted" "get.ok" = true ->
    core_step input binding (TDigest n issued retired payload owner loan)
      (QAccepted binding :: rest)
      (TRelease n issued (loan :: retired) payload owner loan true) rest
      [ObsDigest owner loan true; ObsClose loan]
| CoreDigestRejected : forall n issued retired payload owner loan rest,
    selected_native_accepts input = true ->
    binding_matches_native input binding ->
    digest_choice input "rejected" "get.integrity-failure" = true ->
    core_step input binding (TDigest n issued retired payload owner loan)
      (QRejected binding :: rest)
      (TRelease n issued (loan :: retired) payload owner loan false) rest
      [ObsDigest owner loan false; ObsClose loan]
| CoreAcceptedEnd : forall n issued retired payload owner loan rest,
    selected_native_accepts input = true ->
    binding_matches_native input binding ->
    end_present input "get.ok" "success" [release_bytes; trace_commit] = true ->
    core_step input binding (TRelease n issued retired payload owner loan true) rest
      (TDone n issued (owner :: retired) UnitAccepted) rest
      [ObsRelease owner; ObsDiagnostic (nm "steve.get.commit"); ObsUnit UnitAccepted]
| CoreRejectedEnd : forall n issued retired payload owner loan rest,
    selected_native_accepts input = true ->
    binding_matches_native input binding ->
    end_present input "get.integrity-failure" "integrity-failure" [release_bytes] = true ->
    core_step input binding (TRelease n issued retired payload owner loan false) rest
      (TDone n issued (owner :: retired) UnitRejected) rest
      [ObsRelease owner; ObsUnit UnitRejected]
| CoreNotFoundEnd : forall n issued retired rest,
    selected_native_accepts input = true ->
    binding_matches_native input binding ->
    end_present input "get.not-found" "not-found" [] = true ->
    core_step input binding (TNonfoundEnd n issued retired UnitNotFound) rest
      (TDone n issued retired UnitNotFound) rest [ObsUnit UnitNotFound]
| CoreFailureEnd : forall n issued retired rest,
    selected_native_accepts input = true ->
    binding_matches_native input binding ->
    end_present input "get.failure" "storage-failure" [] = true ->
    core_step input binding (TNonfoundEnd n issued retired UnitStorageFailure) rest
      (TDone n issued retired UnitStorageFailure) rest [ObsUnit UnitStorageFailure].

(* Exact labelled replay and observation preservation.  Nonfound Unit may
   be delayed by exactly the target's final empty block.  Borrow-open and
   close are bounded source administrative steps retained as safety
   observations; only the actual CoreTrace diagnostic is erased. *)
Theorem target_step_lifts : forall input binding c e c' e' target_obs,
  core_step input binding c e c' e' target_obs ->
  exists consumed labels source_obs,
    e = consumed ++ e' /\
    external_labels labels = map reply_label consumed /\
    List.length labels <= 2 /\
    source_trace (source_projection c) labels source_obs (source_projection c') /\
    erase_diagnostic target_obs ++ pending_unit c' = pending_unit c ++ source_obs.
Proof.
  intros input binding c e c' e' target_obs H; destruct H.
  - exists [QFound binding payload], [ReadFound payload; NoInput],
      [ObsFound payload n; ObsBorrow n (S n)].
    repeat split; try reflexivity; try (simpl; lia);
      try (apply replay_source_is_labelled; reflexivity).
  - exists [QNotFound binding], [ReadNotFound], [ObsNotFound; ObsUnit UnitNotFound].
    repeat split; try reflexivity; try (simpl; lia);
      try (apply replay_source_is_labelled; reflexivity).
  - exists [QFailure binding], [ReadFailure], [ObsFailure; ObsUnit UnitStorageFailure].
    repeat split; try reflexivity; try (simpl; lia);
      try (apply replay_source_is_labelled; reflexivity).
  - exists [QAccepted binding], [DigestAccepted; NoInput],
      [ObsDigest owner loan true; ObsClose loan].
    repeat split; try reflexivity; try (simpl; lia);
      try (apply replay_source_is_labelled; reflexivity).
  - exists [QRejected binding], [DigestRejected; NoInput],
      [ObsDigest owner loan false; ObsClose loan].
    repeat split; try reflexivity; try (simpl; lia);
      try (apply replay_source_is_labelled; reflexivity).
  - exists [], [NoInput], [ObsRelease owner; ObsUnit UnitAccepted].
    repeat split; try reflexivity; try (simpl; lia);
      try (apply replay_source_is_labelled; reflexivity).
  - exists [], [NoInput], [ObsRelease owner; ObsUnit UnitRejected].
    repeat split; try reflexivity; try (simpl; lia);
      try (apply replay_source_is_labelled; reflexivity).
  - exists [], [], [].
    repeat split; try reflexivity; try (simpl; lia); try constructor.
  - exists [], [], [].
    repeat split; try reflexivity; try (simpl; lia); try constructor.
Qed.

Inductive core_trace (input : NativeSubject) (binding : selected_binding) :
    target_state -> list qualified_reply -> list observation ->
    target_state -> list qualified_reply -> Prop :=
| CoreTraceNil : forall c e, core_trace input binding c e [] c e
| CoreTraceCons : forall c e middle rest events more final remaining,
    core_step input binding c e middle rest events ->
    core_trace input binding middle rest more final remaining ->
    core_trace input binding c e (events ++ more) final remaining.

Theorem target_trace_lifts_fixed_history : forall input binding c e target_obs c' e',
  core_trace input binding c e target_obs c' e' ->
  exists consumed labels source_obs,
    e = consumed ++ e' /\
    external_labels labels = map reply_label consumed /\
    source_trace (source_projection c) labels source_obs (source_projection c') /\
    erase_diagnostic target_obs ++ pending_unit c' = pending_unit c ++ source_obs.
Proof.
  intros input binding c e target_obs c' e' Htrace.
  induction Htrace as [c e|c e middle rest events more final remaining Hstep Hmore IH].
  - exists [], [], []. split; [reflexivity|]. split; [reflexivity|].
    split; [constructor|]. simpl. rewrite app_nil_r. reflexivity.
  - destruct (target_step_lifts _ _ _ _ _ _ _ Hstep)
      as [used1 [labels1 [obs1 [He [Hlabels1 [_ [Hs1 Hobs1]]]]]]].
    destruct IH as [used2 [labels2 [obs2 [Hr [Hlabels2 [Hs2 Hobs2]]]]]].
    exists (used1 ++ used2), (labels1 ++ labels2), (obs1 ++ obs2).
    split.
    + rewrite He, Hr, app_assoc. reflexivity.
    + split.
      * unfold external_labels in *. rewrite filter_app, map_app, Hlabels1, Hlabels2.
        reflexivity.
      * split.
        -- eapply source_trace_append; eauto.
        -- unfold erase_diagnostic in *. rewrite filter_app.
           rewrite <- app_assoc, Hobs2, app_assoc, Hobs1, <- app_assoc.
           reflexivity.
Qed.

Theorem target_step_exact_binding_keys : forall input binding c e c' e' obs,
  core_step input binding c e c' e' obs ->
  binding_declaration binding = nm "decl:steve.get" /\
  binding_instance binding = nm "inst:phase1.steve".
Proof.
  intros input binding c e c' e' obs H.
  assert (Ha : selected_native_accepts input = true) by (destruct H; assumption).
  assert (Hb : binding_matches_native input binding) by (destruct H; assumption).
  apply selected_native_reflection in Ha. subst input. exact Hb.
Qed.

Theorem target_step_preserves_lifecycle : forall input binding c e c' e' obs,
  core_step input binding c e c' e' obs ->
  canonical_lifecycle (source_projection c) ->
  canonical_lifecycle (source_projection c').
Proof.
  intros input binding c e c' e' obs Hstep Hlife.
  destruct (target_step_lifts _ _ _ _ _ _ _ Hstep)
    as [used [labels [source_obs [_ [_ [_ [Hsource _]]]]]]].
  eapply reachable_lifecycle_valid; [eapply source_trace_forget; exact Hsource|exact Hlife].
Qed.

Theorem target_digest_live_owner_loan : forall n issued retired payload owner loan,
  canonical_lifecycle (source_projection (TDigest n issued retired payload owner loan)) ->
  owner <> loan /\ live_issued issued retired owner /\ live_issued issued retired loan.
Proof.
  intros n issued retired payload owner loan [_ [_ [_ Hphase]]].
  simpl in Hphase. tauto.
Qed.

Theorem target_release_after_close : forall n issued retired payload owner loan decision,
  canonical_lifecycle (source_projection
    (TRelease n issued retired payload owner loan decision)) ->
  owner <> loan /\ In loan retired /\ live_issued issued retired owner.
Proof.
  intros n issued retired payload owner loan decision [_ [_ [_ Hphase]]].
  simpl in Hphase. tauto.
Qed.

Theorem target_unit_has_no_live_origin : forall n issued retired branch,
  canonical_lifecycle (source_projection (TDone n issued retired branch)) ->
  forall origin, ~ live_issued issued retired origin.
Proof. intros n issued retired branch [_ [_ [_ Hphase]]]. exact Hphase. Qed.

Definition target_rank (c : target_state) : nat :=
  match c with TRead _ _ _ => 3 | TDigest _ _ _ _ _ _ => 2
  | TRelease _ _ _ _ _ _ _ => 1 | TNonfoundEnd _ _ _ _ => 1 | TDone _ _ _ _ => 0 end.

Theorem target_step_rank_decreases : forall input binding c e c' e' obs,
  core_step input binding c e c' e' obs -> target_rank c' < target_rank c.
Proof. intros input binding c e c' e' obs H; destruct H; simpl; lia. Qed.

Theorem target_no_unanswered_read_step : forall input binding n issued retired c' e' obs,
  ~ core_step input binding (TRead n issued retired) [] c' e' obs.
Proof. intros input binding n issued retired c' e' obs H; inversion H. Qed.

Theorem target_no_unanswered_digest_step : forall input binding n issued retired payload owner loan c' e' obs,
  ~ core_step input binding (TDigest n issued retired payload owner loan) [] c' e' obs.
Proof. intros input binding n issued retired payload owner loan c' e' obs H; inversion H. Qed.

Theorem selected_found_binds_exact_payload : forall input binding n issued retired payload rest c' e' obs,
  core_step input binding (TRead n issued retired) (QFound binding payload :: rest) c' e' obs ->
  c' = TDigest (S (S n)) (S n :: n :: issued) retired payload n (S n) /\
  e' = rest /\ obs = [ObsFound payload n; ObsBorrow n (S n)].
Proof. intros input binding n issued retired payload rest c' e' obs H; inversion H; subst; auto. Qed.

Theorem selected_digest_keeps_read_payload : forall input binding n issued retired payload owner loan rest c' e' obs,
  core_step input binding (TDigest n issued retired payload owner loan) (QAccepted binding :: rest) c' e' obs ->
  c' = TRelease n issued (loan :: retired) payload owner loan true /\
  e' = rest /\ obs = [ObsDigest owner loan true; ObsClose loan].
Proof. intros input binding n issued retired payload owner loan rest c' e' obs H; inversion H; subst; auto. Qed.

(* Model comparison uses exact origin namespace and serial, never content.
   The concrete evaluator uses opaque Origin equality and its private map;
   no relation from concrete Unique to this mathematical nat is presumed. *)
Definition origin_ref := nat * nat.
Definition exact_origin_eq (x y : origin_ref) : bool :=
  andb (Nat.eqb (fst x) (fst y)) (Nat.eqb (snd x) (snd y)).
Definition exact_pair_match (ao al bo bl : origin_ref) : bool :=
  andb (exact_origin_eq ao bo) (exact_origin_eq al bl).

Theorem exact_origin_eq_sound : forall x y, exact_origin_eq x y = true <-> x = y.
Proof.
  intros [xw xs] [yw ys]. unfold exact_origin_eq; simpl.
  rewrite Bool.andb_true_iff, !Nat.eqb_eq. split; [intros [H1 H2]; subst; reflexivity|].
  intro H; inversion H; auto.
Qed.

Theorem exact_pair_match_sound : forall ao al bo bl,
  exact_pair_match ao al bo bl = true <-> ao = bo /\ al = bl.
Proof.
  intros. unfold exact_pair_match.
  rewrite Bool.andb_true_iff, !exact_origin_eq_sound. reflexivity.
Qed.

Theorem other_valid_pair_rejected : forall ao al bo bl,
  (ao <> bo \/ al <> bl) -> exact_pair_match ao al bo bl = false.
Proof.
  intros ao al bo bl H. destruct (exact_pair_match ao al bo bl) eqn:Heq; [|reflexivity].
  apply exact_pair_match_sound in Heq. tauto.
Qed.

Theorem target_trace_preserves_lifecycle : forall input binding c e target_obs c' e',
  core_trace input binding c e target_obs c' e' ->
  canonical_lifecycle (source_projection c) ->
  canonical_lifecycle (source_projection c').
Proof.
  intros input binding c e target_obs c' e' Htrace Hlife.
  destruct (target_trace_lifts_fixed_history _ _ _ _ _ _ _ Htrace)
    as [used [labels [source_obs [_ [_ [Hsource _]]]]]].
  eapply reachable_lifecycle_valid; [eapply source_trace_forget; exact Hsource|exact Hlife].
Qed.

Theorem initial_target_lifecycle :
  canonical_lifecycle (source_projection (TRead 0 [] [])).
Proof.
  apply canonical_lifecycle_reachable.
  eapply StepsNext; [apply RuleStart|constructor].
Qed.

Theorem completed_target_preserves_all_fixed_history_observations :
  forall input binding n issued retired e target_obs n' issued' retired' branch remaining,
  core_trace input binding (TRead n issued retired) e target_obs
    (TDone n' issued' retired' branch) remaining ->
  exists consumed labels,
    e = consumed ++ remaining /\
    external_labels labels = map reply_label consumed /\
    source_trace (AwaitRead n issued retired) labels (erase_diagnostic target_obs)
      (Done n' issued' retired' branch).
Proof.
  intros input binding n issued retired e target_obs n' issued' retired' branch remaining H.
  destruct (target_trace_lifts_fixed_history _ _ _ _ _ _ _ H)
    as [used [labels [source_obs [He [Hlabels [Hsource Hobs]]]]]].
  exists used, labels. split; [exact He|]. split; [exact Hlabels|].
  simpl in Hobs. rewrite app_nil_r in Hobs. rewrite Hobs. exact Hsource.
Qed.

Print Assumptions target_trace_preserves_lifecycle.
Print Assumptions initial_target_lifecycle.
Print Assumptions completed_target_preserves_all_fixed_history_observations.
Print Assumptions selected_native_reflection.
Print Assumptions accepted_native_has_exact_choices.
Print Assumptions accepted_native_rejects_wrong_destination.
Print Assumptions replay_source_is_labelled.
Print Assumptions source_trace_forget.
Print Assumptions source_trace_append.
Print Assumptions target_step_lifts.
Print Assumptions target_step_exact_binding_keys.
Print Assumptions target_trace_lifts_fixed_history.
Print Assumptions target_step_preserves_lifecycle.
Print Assumptions target_digest_live_owner_loan.
Print Assumptions target_release_after_close.
Print Assumptions target_unit_has_no_live_origin.
Print Assumptions target_step_rank_decreases.
Print Assumptions target_no_unanswered_read_step.
Print Assumptions target_no_unanswered_digest_step.
Print Assumptions selected_found_binds_exact_payload.
Print Assumptions selected_digest_keeps_read_payload.
Print Assumptions exact_origin_eq_sound.
Print Assumptions exact_pair_match_sound.
Print Assumptions other_valid_pair_rejected.

(* Ephemeral generated selector, compiled against the actual Haskell
   structural adapter in the dedicated workflow. No checked-in generated
   module, package dependency or new trust premise. *)
Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive list => "[]" [ "[]" "(:)" ].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing" ].
Extract Inductive prod => "(,)" [ "(,)" ].
Extraction "FSEM06SteveGetNativeKernel" selected_native_accepts.
