From Stdlib Require Import Strings.String.
From Stdlib Require Import Init.Datatypes.

Open Scope string_scope.

(*
  Proof-oriented model of the currently needed Phil.Core.Syntax fragments.

  Message types are opaque in the session-duality slice because dualSession
  preserves them unchanged. Branch lists are represented by a mutually
  inductive spine so structural recursion follows the same protocol structure
  as the Haskell Session / Branch representation.
*)

Definition Name := string.
Definition Outcome := string.
Parameter Ty : Type.

Inductive Mode : Type :=
| Unrestricted : Mode
| Affine : Mode
| Linear : Mode.

Inductive Session : Type :=
| Send : Name -> Ty -> Session -> Session
| Receive : Name -> Ty -> Session -> Session
| Select : Branches -> Session
| Offer : Branches -> Session
| End : Outcome -> Session
| Rec : Name -> Session -> Session
| SessionVar : Name -> Session
with Branches : Type :=
| BNil : Branches
| BCons : string -> option (Name * Ty) -> Session -> Branches -> Branches.

Scheme Session_ind' := Induction for Session Sort Prop
with Branches_ind' := Induction for Branches Sort Prop.

Combined Scheme Session_Branches_mutind
  from Session_ind', Branches_ind'.

Inductive Control : Type :=
| Continue : Control
| Return : Ty -> Control
| Closed : Outcome -> Control
| Failed : string -> string -> Control.
