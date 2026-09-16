From Stdlib Require Import Arith.PeanoNat Lists.List Strings.String.

From Phil.Surface Require Import
  GrammarAstSourceHeader
  GrammarAstSourceHeaderTotality.

Import ListNotations.
Open Scope string_scope.

(*
  Reusable representation bridge for PHIL-SURFACE-GRAMMAR-CORR-001.

  The proof-side source/header carrier uses nonempty name records because the
  grammar makes qualified names and identifier lists nonempty.  Production
  Haskell uses ordinary lists inside GrammarV1QualifiedName and import
  selections.  This file makes that representation seam explicit and proves
  that flattening the certified nonempty carrier into ordinary list/option
  structure is lossless.

  Top-level declaration payloads are intentionally retained as an explicit
  hole: the implementation view records only their count, while the inverse
  bridge receives the certified top-level ParseTree list separately.  The
  top-level and declaration-family refinement slices can replace that hole
  without reopening module/import/name representation.
*)

Record Phase1SurfaceImplementationImportHeader : Type := {
  phase1_impl_import_name : list string;
  phase1_impl_import_selection : option (list string)
}.

Record Phase1SurfaceImplementationSourceHeader : Type := {
  phase1_impl_source_module : option (list string);
  phase1_impl_source_imports : list Phase1SurfaceImplementationImportHeader;
  phase1_impl_source_top_level_count : nat
}.

Definition phase1_surface_name_list_to_implementation
  (names : Phase1SurfaceNameList) : list string :=
  phase1_name_list_first names :: phase1_name_list_rest names.

Definition phase1_surface_name_list_from_implementation
  (values : list string) : option Phase1SurfaceNameList :=
  match values with
  | [] => None
  | first :: rest =>
      Some
        {| phase1_name_list_first := first;
           phase1_name_list_rest := rest |}
  end.

Theorem phase1_surface_name_list_implementation_round_trip :
  forall names,
    phase1_surface_name_list_from_implementation
      (phase1_surface_name_list_to_implementation names) = Some names.
Proof.
  intros [first rest].
  reflexivity.
Qed.

Theorem phase1_surface_name_list_implementation_nonempty :
  forall names,
    phase1_surface_name_list_to_implementation names <> [].
Proof.
  intros [first rest].
  discriminate.
Qed.

Definition phase1_surface_optional_name_list_to_implementation
  (names : option Phase1SurfaceNameList) : option (list string) :=
  match names with
  | None => None
  | Some value => Some (phase1_surface_name_list_to_implementation value)
  end.

Definition phase1_surface_optional_name_list_from_implementation
  (values : option (list string)) : option (option Phase1SurfaceNameList) :=
  match values with
  | None => Some None
  | Some names =>
      match phase1_surface_name_list_from_implementation names with
      | Some value => Some (Some value)
      | None => None
      end
  end.

Theorem phase1_surface_optional_name_list_implementation_round_trip :
  forall names,
    phase1_surface_optional_name_list_from_implementation
      (phase1_surface_optional_name_list_to_implementation names) = Some names.
Proof.
  intros [[first rest] |]; reflexivity.
Qed.

Definition phase1_surface_import_header_to_implementation
  (header : Phase1SurfaceImportHeader)
  : Phase1SurfaceImplementationImportHeader :=
  {| phase1_impl_import_name :=
       phase1_surface_name_list_to_implementation
         (phase1_import_header_name header);
     phase1_impl_import_selection :=
       phase1_surface_optional_name_list_to_implementation
         (phase1_import_header_selection header) |}.

Definition phase1_surface_import_header_from_implementation
  (header : Phase1SurfaceImplementationImportHeader)
  : option Phase1SurfaceImportHeader :=
  match
    phase1_surface_name_list_from_implementation
      (phase1_impl_import_name header),
    phase1_surface_optional_name_list_from_implementation
      (phase1_impl_import_selection header)
  with
  | Some name, Some selection =>
      Some
        {| phase1_import_header_name := name;
           phase1_import_header_selection := selection |}
  | _, _ => None
  end.

Theorem phase1_surface_import_header_implementation_round_trip :
  forall header,
    phase1_surface_import_header_from_implementation
      (phase1_surface_import_header_to_implementation header) = Some header.
Proof.
  intros [[first rest] [[selection_first selection_rest] |]]; reflexivity.
Qed.

Fixpoint phase1_surface_import_headers_from_implementation
  (headers : list Phase1SurfaceImplementationImportHeader)
  : option (list Phase1SurfaceImportHeader) :=
  match headers with
  | [] => Some []
  | header :: rest =>
      match phase1_surface_import_header_from_implementation header,
            phase1_surface_import_headers_from_implementation rest with
      | Some value, Some values => Some (value :: values)
      | _, _ => None
      end
  end.

Theorem phase1_surface_import_headers_implementation_round_trip :
  forall headers,
    phase1_surface_import_headers_from_implementation
      (map phase1_surface_import_header_to_implementation headers) =
      Some headers.
Proof.
  intros headers.
  induction headers as [|header rest IH].
  - reflexivity.
  - simpl.
    rewrite phase1_surface_import_header_implementation_round_trip.
    rewrite IH.
    reflexivity.
Qed.

Definition phase1_surface_source_header_to_implementation
  (header : Phase1SurfaceSourceHeader)
  : Phase1SurfaceImplementationSourceHeader :=
  {| phase1_impl_source_module :=
       phase1_surface_optional_name_list_to_implementation
         (phase1_source_header_module header);
     phase1_impl_source_imports :=
       map phase1_surface_import_header_to_implementation
         (phase1_source_header_imports header);
     phase1_impl_source_top_level_count :=
       List.length (phase1_source_header_top_levels header) |}.

Definition phase1_surface_source_header_from_implementation
  (header : Phase1SurfaceImplementationSourceHeader)
  (top_levels : list GrammarDerivation.ParseTree)
  : option Phase1SurfaceSourceHeader :=
  if Nat.eqb
      (List.length top_levels)
      (phase1_impl_source_top_level_count header)
  then
    match
      phase1_surface_optional_name_list_from_implementation
        (phase1_impl_source_module header),
      phase1_surface_import_headers_from_implementation
        (phase1_impl_source_imports header)
    with
    | Some module_name, Some imports =>
        Some
          {| phase1_source_header_module := module_name;
             phase1_source_header_imports := imports;
             phase1_source_header_top_levels := top_levels |}
    | _, _ => None
    end
  else None.

Theorem phase1_surface_source_header_implementation_round_trip :
  forall header,
    phase1_surface_source_header_from_implementation
      (phase1_surface_source_header_to_implementation header)
      (phase1_source_header_top_levels header) = Some header.
Proof.
  intros [module_name imports top_levels].
  unfold phase1_surface_source_header_from_implementation,
    phase1_surface_source_header_to_implementation.
  simpl.
  rewrite Nat.eqb_refl.
  rewrite phase1_surface_optional_name_list_implementation_round_trip.
  rewrite phase1_surface_import_headers_implementation_round_trip.
  reflexivity.
Qed.

Theorem phase1_surface_certified_source_header_has_implementation_view :
  forall tokens tree,
    GrammarDerivation.Phase1CompleteDerivation tokens tree ->
    exists header,
      phase1_surface_normalize_source_header_tree tree = Some header /\
      phase1_surface_source_header_from_implementation
        (phase1_surface_source_header_to_implementation header)
        (phase1_source_header_top_levels header) = Some header.
Proof.
  intros tokens tree Hcomplete.
  destruct
    (phase1_surface_normalize_source_header_total tokens tree Hcomplete)
    as [header [Hnormalize Hround]].
  exists header.
  split.
  - exact Hnormalize.
  - apply phase1_surface_source_header_implementation_round_trip.
Qed.
