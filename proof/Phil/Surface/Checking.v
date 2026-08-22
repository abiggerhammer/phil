From Stdlib Require Import Lists.List Arith.PeanoNat.
Import ListNotations.

(*
  Proof-oriented model of the first generic whole-component checking boundary.

  This slice deliberately does not duplicate Core type equality or surface
  parsing.  Instead it isolates two authority-bearing rules introduced by the
  merged whole-component checker:

  - architecture-supplied bindings and type aliases may be used only through
    explicit agreement/lookups;
  - terminal control is monotone under surface sequencing and syntactically
    unconditional terminal statements cannot have a following statement in a
    successful preflight.

  Concrete Text/Map representation, source spans, and compareTypes are the
  implementation correspondence boundary for this file.
*)

(* -------------------------------------------------------------------------- *)
(* PHIL-SURFACE-ARCH-001 — architecture agreement.                            *)
(* -------------------------------------------------------------------------- *)

Inductive SurfaceMode : Type :=
| SurfaceUnrestricted
| SurfaceAffine
| SurfaceLinear.

Definition SurfaceMode_eq_dec :
  forall left right : SurfaceMode, {left = right} + {left <> right}.
Proof. decide equality. Defined.

(* A compact proof-side identity for an already elaborated Core type. *)
Definition CoreTypeId := nat.

Record ArchitectureBinding : Type := {
  architectureMode : SurfaceMode;
  architectureType : CoreTypeId
}.

Inductive ParameterDeclaration : Type :=
| UntypedParameter
| TypedParameter : SurfaceMode -> CoreTypeId -> ParameterDeclaration.

Definition initializeParameter
  (existing : option ArchitectureBinding)
  (declaration : ParameterDeclaration) : option ArchitectureBinding :=
  match existing, declaration with
  | Some binding, UntypedParameter => Some binding
  | Some binding, TypedParameter declaredMode declaredType =>
      if SurfaceMode_eq_dec declaredMode (architectureMode binding)
      then if Nat.eq_dec declaredType (architectureType binding)
           then Some binding
           else None
      else None
  | None, UntypedParameter => None
  | None, TypedParameter declaredMode declaredType =>
      Some {| architectureMode := declaredMode;
              architectureType := declaredType |}
  end.

(* Existing architecture state is authoritative: a matching annotation may
   confirm it, but cannot replace it. *)
Theorem typed_parameter_cannot_override_architecture :
  forall architecture declaredMode declaredType result,
    initializeParameter
      (Some architecture)
      (TypedParameter declaredMode declaredType) = Some result ->
    result = architecture /\
    declaredMode = architectureMode architecture /\
    declaredType = architectureType architecture.
Proof.
  intros architecture declaredMode declaredType result Hinitialize.
  unfold initializeParameter in Hinitialize.
  destruct (SurfaceMode_eq_dec declaredMode (architectureMode architecture))
    as [Hmode | Hmode].
  - destruct (Nat.eq_dec declaredType (architectureType architecture))
      as [Htype | Htype].
    + inversion Hinitialize; subst result.
      repeat split; assumption || reflexivity.
    + discriminate.
  - discriminate.
Qed.

Theorem untyped_parameter_preserves_architecture :
  forall architecture,
    initializeParameter (Some architecture) UntypedParameter = Some architecture.
Proof. reflexivity. Qed.

Theorem untyped_parameter_requires_architecture :
  initializeParameter None UntypedParameter = None.
Proof. reflexivity. Qed.

Theorem typed_parameter_without_architecture_is_exact_source_binding :
  forall declaredMode declaredType,
    initializeParameter None (TypedParameter declaredMode declaredType) =
      Some {| architectureMode := declaredMode;
              architectureType := declaredType |}.
Proof. reflexivity. Qed.

Inductive ResolvedType : Type :=
| OpaqueNamedType : nat -> ResolvedType
| EndpointType : nat -> ResolvedType
| ConcreteType : nat -> ResolvedType.

Definition TypeAliasEnvironment := nat -> option ResolvedType.

Definition resolveNamedType
  (aliases : TypeAliasEnvironment)
  (name : nat) : ResolvedType :=
  match aliases name with
  | Some ty => ty
  | None => OpaqueNamedType name
  end.

Theorem explicit_alias_resolves_exactly :
  forall aliases name ty,
    aliases name = Some ty ->
    resolveNamedType aliases name = ty.
Proof.
  intros aliases name ty Halias.
  unfold resolveNamedType. rewrite Halias. reflexivity.
Qed.

Theorem absent_alias_remains_opaque :
  forall aliases name,
    aliases name = None ->
    resolveNamedType aliases name = OpaqueNamedType name.
Proof.
  intros aliases name Halias.
  unfold resolveNamedType. rewrite Halias. reflexivity.
Qed.

Theorem nondefault_named_resolution_requires_explicit_alias :
  forall aliases name result,
    resolveNamedType aliases name = result ->
    result <> OpaqueNamedType name ->
    aliases name = Some result.
Proof.
  intros aliases name result Hresolve Hnondefault.
  unfold resolveNamedType in Hresolve.
  destruct (aliases name) as [aliased |] eqn:Halias.
  - inversion Hresolve; subst result. reflexivity.
  - inversion Hresolve; subst result. contradiction.
Qed.

(* -------------------------------------------------------------------------- *)
(* PHIL-SURFACE-CTRL-001 — terminal-control monotonicity.                      *)
(* -------------------------------------------------------------------------- *)

Inductive SurfaceControl : Type :=
| SurfaceContinue
| SurfaceReturn
| SurfaceClosed
| SurfaceFailed.

Definition advanceControl
  (next : SurfaceControl)
  (current : SurfaceControl) : SurfaceControl :=
  match current with
  | SurfaceContinue => next
  | SurfaceReturn => SurfaceReturn
  | SurfaceClosed => SurfaceClosed
  | SurfaceFailed => SurfaceFailed
  end.

Theorem noncontinuing_control_is_never_reentered :
  forall next current,
    current <> SurfaceContinue ->
    advanceControl next current = current.
Proof.
  intros next current Hterminal.
  destruct current; try contradiction; reflexivity.
Qed.

Theorem terminal_control_cannot_become_continue :
  forall next current,
    current <> SurfaceContinue ->
    advanceControl next current <> SurfaceContinue.
Proof.
  intros next current Hterminal.
  rewrite noncontinuing_control_is_never_reentered by exact Hterminal.
  exact Hterminal.
Qed.

Definition advanceControls
  (next : SurfaceControl)
  (controls : list SurfaceControl) : list SurfaceControl :=
  map (advanceControl next) controls.

Theorem terminal_path_survives_surface_sequence :
  forall next controls terminal,
    In terminal controls ->
    terminal <> SurfaceContinue ->
    In terminal (advanceControls next controls).
Proof.
  intros next controls terminal Hin Hterminal.
  unfold advanceControls.
  induction controls as [|control rest IH].
  - contradiction.
  - simpl in Hin. simpl.
    destruct Hin as [Heq | Hin].
    + subst control. left.
      apply noncontinuing_control_is_never_reentered. exact Hterminal.
    + right. apply IH. exact Hin.
Qed.

Inductive StatementClass : Type :=
| OrdinaryStatement
| ReturnStatement
| CloseStatement
| FailStatement.

Definition unconditionalTerminal (statement : StatementClass) : bool :=
  match statement with
  | OrdinaryStatement => false
  | ReturnStatement => true
  | CloseStatement => true
  | FailStatement => true
  end.

Fixpoint preflightSequence (statements : list StatementClass) : bool :=
  match statements with
  | [] => true
  | statement :: rest =>
      if unconditionalTerminal statement
      then match rest with
           | [] => true
           | _ :: _ => false
           end
      else preflightSequence rest
  end.

Theorem terminal_head_with_following_statement_rejects :
  forall terminal following rest,
    unconditionalTerminal terminal = true ->
    preflightSequence (terminal :: following :: rest) = false.
Proof.
  intros terminal following rest Hterminal.
  simpl. rewrite Hterminal. reflexivity.
Qed.

Theorem successful_terminal_head_has_no_following_statement :
  forall terminal rest,
    unconditionalTerminal terminal = true ->
    preflightSequence (terminal :: rest) = true ->
    rest = [].
Proof.
  intros terminal rest Hterminal Hpreflight.
  destruct rest as [|following remaining].
  - reflexivity.
  - rewrite terminal_head_with_following_statement_rejects
      with (following := following) (rest := remaining)
      in Hpreflight by exact Hterminal.
    discriminate.
Qed.

Theorem successful_nonterminal_prefix_delegates_to_tail :
  forall statement rest,
    unconditionalTerminal statement = false ->
    preflightSequence (statement :: rest) = preflightSequence rest.
Proof.
  intros statement rest Hordinary.
  simpl. rewrite Hordinary. reflexivity.
Qed.
