From Coq Require Import Classes.RelationClasses.
From sflib Require Import sflib.
From Paco Require Import paco.
From Tutorial Require Import Theory ITreeLib.

Set Implicit Arguments.

Section EVENT.

  Variant progE: Type -> Type :=
    | Choose (X: Type): progE X
    | Observe (fn: String.string) (args: list nat): progE nat
    | Undefined: progE void
  .

End EVENT.

Module Mem.

  Definition t := nat -> option nat.

  Definition read (m: t) (loc: nat): option nat := (m loc).

  Definition write (m: t) (loc: nat) (v: nat): t :=
    fun x => if (Nat.eqb loc x) then (Some v) else (m x).

  Definition init: t := fun _ => None.

  Variant memE: Type -> Type :=
    | Read: memE nat
    | Write (v: nat): memE unit
  .

End Mem.

Section STS.

  Definition imp_state := (Mem.t * (itree (progE +' Mem.memE) nat))%type.

  Variant imp_terminates: imp_state -> nat -> Prop :=
    | imp_term_intro
        m vret
      :
      imp_terminates (m, Ret vret) vret.

  Variant imp_undefined: imp_state -> Prop :=
    | imp_undef_intro
        m ktr
      :
      imp_undefined (m, Vis (inl1 Undefined) ktr).

  (* TODO: define "step" of this STS. *)
  Variant imp_step: imp_state -> eventE -> imp_state -> Prop :=

End STS.
