From sflib Require Import sflib.
From Paco Require Import paco.
From Tutorial Require Import Refinement ITreeLib.
From Coq Require Import Strings.String List.

Set Implicit Arguments.


Module Mem.
  (** A simple memory model. *)

  Definition t := nat -> option nat.

  Definition load (m : t) (x : nat) : option nat := (m x).

  Definition store (m : t) (x : nat) (v : nat): t :=
    fun y => if (Nat.eqb x y) then (Some v) else (m y).

  Definition init : t := fun _ => None.

  Variant label : Type :=
    | LLoad (x : nat) (v : nat) : label
    | LStore (x : nat) (v : nat) : label
  .

  Variant memE: Type -> Type :=
    | Load : memE (option nat)
    | Store (x : nat) (v : nat) : memE unit
  .

End Mem.


Module Reg.
  (** A simple register (local environment) for Imp. *)

  Definition t := string -> option nat.

  Definition read (r : t) (x : string) : option nat := (r x).

  Definition write (r : t) (x : string) (v : nat): t :=
    fun y => if (String.eqb x y) then (Some v) else (r y).

  Definition init : t := fun _ => None.

  Variant regE: Type -> Type :=
    | Read : regE (option nat)
    | Write (x : nat) (v : nat) : regE unit
  .

End Reg.

(* Section EVENT. *)

(*   Variant progE: Type -> Type := *)
(*     | Choose (X: Type): progE X *)
(*     | Observe (fn: String.string) (args: list nat): progE nat *)
(*     | Undefined: progE void *)
(*   . *)

(* End EVENT. *)

(* Module Mem. *)

(*   Definition t := nat -> option nat. *)

(*   Definition read (m: t) (loc: nat): option nat := (m loc). *)

(*   Definition write (m: t) (loc: nat) (v: nat): t := *)
(*     fun x => if (Nat.eqb loc x) then (Some v) else (m x). *)

(*   Definition init: t := fun _ => None. *)

(*   Variant memE: Type -> Type := *)
(*     | Read: memE nat *)
(*     | Write (v: nat): memE unit *)
(*   . *)

(* End Mem. *)

(* Section STS. *)

(*   Definition imp_state := (Mem.t * (itree (progE +' Mem.memE) nat))%type. *)

(*   Variant imp_terminates: imp_state -> nat -> Prop := *)
(*     | imp_term_intro *)
(*         m vret *)
(*       : *)
(*       imp_terminates (m, Ret vret) vret. *)

(*   Variant imp_undefined: imp_state -> Prop := *)
(*     | imp_undef_intro *)
(*         m ktr *)
(*       : *)
(*       imp_undefined (m, Vis (inl1 Undefined) ktr). *)

(*   (* TODO: define "step" of this STS. *) *)
(*   Variant imp_step: imp_state -> eventE -> imp_state -> Prop := *)

(* End STS. *)
