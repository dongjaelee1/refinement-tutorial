From Tutorial Require Import sflib.
From Paco Require Import paco.
From Tutorial Require Import Refinement ITreeLib Imp.
From Stdlib Require Import Strings.String List.

Set Implicit Arguments.

(** * ITreeLang: ITree-based Semantics for Imp *)

(** This module provides an alternative ITree-based semantics for the Imp language.
    Instead of defining a step relation directly on syntax (as in Imp.v),
    we denote Imp programs as interaction trees and define the STS on ITrees. *)



(** ** Event Types *)

Variant progE: Type -> Type :=
  | Choose (X: Type): progE X
  | Observe (fn: string) (args: list nat): progE nat
  | Undefined: progE void
.

Variant memE: Type -> Type :=
  | MemLoad (loc: nat): memE (option nat)
  | MemStore (loc: nat) (v: nat): memE unit
.

(** The combined event type for ITree Imp programs. *)
Definition Es : Type -> Type := progE +' memE.



(** ** Denotation of Imp into ITrees *)

(** Denote arithmetic expressions.
    Takes a register state and returns a value via an ITree.
    - [AAny] uses [Choose] for nondeterminism.
    - [AId x] triggers [Undefined] if the register is uninitialized. *)
Fixpoint denote_aexp (a: aexp) (r: Reg.t) : itree Es nat :=
  match a with
  | AAny => trigger (Choose nat)
  | ANum n => Ret n
  | AId x =>
      match Reg.read r x with
      | Some v => Ret v
      | None => vd <- trigger Undefined;; match vd : void with end
      end
  | ABinOp op a1 a2 =>
      v1 <- denote_aexp a1 r;;
      v2 <- denote_aexp a2 r;;
      Ret (bin_op_eval op v1 v2)
  end.

(** Denote a list of expressions (for external call arguments). *)
Fixpoint denote_aexps (es: list aexp) (r: Reg.t) : itree Es (list nat) :=
  match es with
  | nil => Ret nil
  | e :: es' =>
      v <- denote_aexp e r;;
      vs <- denote_aexps es' r;;
      Ret (v :: vs)
  end.

(** Denote commands.
    Returns [inl r'] if the command finished normally with updated register state [r'],
    or [inr v] if the command executed a [CRet] with return value [v]. *)
Fixpoint denote_com (c: com) (r: Reg.t) : itree Es (Reg.t + nat) :=
  match c with
  | CSkip => Ret (inl r)
  | CAsgn x a =>
      v <- denote_aexp a r;;
      Ret (inl (Reg.write r x v))
  | CSeq c1 c2 =>
      res <- denote_com c1 r;;
      match res with
      | inl r' => tau;; denote_com c2 r'
      | inr v => Ret (inr v)
      end
  | CIf b c1 c2 =>
      v <- denote_aexp b r;;
      if Nat.eqb v 0 then denote_com c2 r else denote_com c1 r
  | CWhile b c =>
      ITree.iter (fun r0 =>
        v <- denote_aexp b r0;;
        if Nat.eqb v 0
        then Ret (inr (inl r0))
        else
          res <- denote_com c r0;;
          match res with
          | inl r' => Ret (inl r')
          | inr v' => Ret (inr (inr v'))
          end
      ) r
  | CRet a =>
      v <- denote_aexp a r;;
      Ret (inr v)
  | CMemLoad x loc =>
      ov <- trigger (MemLoad loc);;
      match ov with
      | Some v => Ret (inl (Reg.write r x v))
      | None => vd <- trigger Undefined;; match vd : void with end
      end
  | CMemStore loc a =>
      v <- denote_aexp a r;;
      trigger (MemStore loc v);;;
      Ret (inl r)
  | CExternal x name args =>
      vargs <- denote_aexps args r;;
      retv <- trigger (Observe name vargs);;
      Ret (inl (Reg.write r x retv))
  end.

(** Denote a full program: initialize registers and run the command.
    If the command finishes without a [CRet], it is undefined behavior. *)
Definition denote_program (c: com) : itree Es nat :=
  res <- denote_com c Reg.init;;
  match res with
  | inl _ => vd <- trigger Undefined;; match vd : void with end
  | inr v => Ret v
  end.



(** ** ITree-based STS *)

Section STS.

  Definition ITree_state := (Mem.t * itree Es nat)%type.

  (** Classify progE events: [Undefined] leads to UB. *)
  Definition progE_is_undefined {T} (e: progE T) : bool :=
    match e with
    | Choose _ => false
    | Observe _ _ => false
    | Undefined => true
    end.

  (** State sort for ITree states:
      - [Ret v] is a final state with return value [v].
      - [Vis Undefined _] is an undefined (UB) state.
      - Everything else is a normal (steppable) state. *)
  Definition ITree_sort (s: ITree_state) : sort :=
    let '(_, t) := s in
    match observe t with
    | RetF v => final v
    | TauF _ => normal
    | VisF e _ =>
        match e with
        | inl1 e' => if progE_is_undefined e' then undef else normal
        | inr1 _ => normal
        end
    end.

  (** Step relation for ITree states. *)
  Variant ITree_step : ITree_state -> Imp_label -> ITree_state -> Prop :=
    | ITree_step_tau
        m t
      :
      ITree_step (m, tau;; t) (inr LInternal) (m, t)
    | ITree_step_choose
        m X (x: X) (k: X -> itree Es nat)
      :
      ITree_step (m, Vis (inl1 (Choose X)) k) (inr LInternal) (m, k x)
    | ITree_step_observe
        m fn args retv (k: nat -> itree Es nat)
      :
      ITree_step (m, Vis (inl1 (Observe fn args)) k) (inr (LExternal fn args retv)) (m, k retv)
    | ITree_step_load
        m loc v (k: option nat -> itree Es nat)
        (LOAD: Mem.load m loc = Some v)
      :
      ITree_step (m, Vis (inr1 (MemLoad loc)) k) (inl (Mem.LLoad loc v)) (m, k (Some v))
    | ITree_step_load_fail
        m loc (k: option nat -> itree Es nat)
        (LOAD: Mem.load m loc = None)
      :
      ITree_step (m, Vis (inr1 (MemLoad loc)) k) (inr LInternal) (m, k None)
    | ITree_step_store
        m loc v (k: unit -> itree Es nat)
      :
      ITree_step (m, Vis (inr1 (MemStore loc v)) k) (inl (Mem.LStore loc v)) (Mem.store m loc v, k tt)
  .

  Definition ITree_STS (ekind: Imp_label -> kind) : STS :=
    mk_sts (Imp_Event ekind) ITree_step ITree_sort.

  (** Two semantics, mirroring Imp.v: *)

  (** Memory events are observable. *)
  Definition ITree_STS_Mem : STS := ITree_STS ekind_memory.
  Definition ITree_Program_Mem (c: com) : Program ITree_STS_Mem :=
    mk_program ITree_STS_Mem (Mem.init, denote_program c).

  (** Only external events are observable. *)
  Definition ITree_STS_Ext : STS := ITree_STS ekind_external.
  Definition ITree_Program_Ext (c: com) : Program ITree_STS_Ext :=
    mk_program ITree_STS_Ext (Mem.init, denote_program c).

End STS.
