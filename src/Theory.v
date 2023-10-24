From Coq Require Import Classes.RelationClasses.
From sflib Require Import sflib.
From Paco Require Import paco.

Set Implicit Arguments.

(* 
  Program refinement is an approach in program verification, 
  where one verifies that every possible behavior of a program (called the target) 
  is also possible by another program (called the source).
  Usually, behavior of a program is defined as a set of traces, where traces record observable events of a program.
  Observables events can differ by what one wants to verify.
  For example, this tutorial assumes system calls, divergence, and termination with a return value.
*)

(* We first define the trace. *)
Section TRACE.

  Variant syscall: Type :=
    | syscallE (fn: String.string) (args: list nat) (retv: nat)
  .

  CoInductive trace: Type :=
  | term (retv: nat)
  | spin
  | ub
  | cons (hd: syscall) (tl: trace)
  .

End TRACE.

(* We assume a simple state transition system. *)
Section STS.

  Variant eventE: Type :=
    | silentE
    | obsE (e: syscall)
  .

  Record STS: Type :=
    mk_sts {
        state: Type;
        init: state;
        (* step is a relation, not a function, because in general, program execution can be non-deterministic. *)
        step: state -> eventE -> state -> Prop;
        (* We fix return value as nat for simplicity. *)
        terminates: state -> nat -> Prop;
        undefined: state -> Prop;
      }.

End STS.

(* We now define the behavior of a STS. *)
Section BEH.

  Variable prog: STS.
  Local Notation state := prog.(state).
  Local Notation init := prog.(init).
  Local Notation step := prog.(step).
  Local Notation terminates := prog.(terminates).
  Local Notation undefined := prog.(undefined).

  Variant _diverge
          (diverge: state -> Prop)
    :
    state -> Prop :=
    | diverge_silent
        st0 st1
        (STEP: step st0 silentE st1)
        (DIV: diverge st1)
      :
      _diverge diverge st0
  .

  Definition diverge: state -> Prop := paco1 _diverge bot1.

  (* Boilerplate code for paco. *)
  Lemma diverge_mon: monotone1 _diverge.
  Proof.
    ii. inv IN.
    - econs 1; eauto.
      (* eapply diverge_silent; eauto. *)
  Qed.

  (* Behavior is a mixed inductive-coinductive definition.
     Inductive because we only want finite number of silent steps (infinite silent step case is treated as divergence).
 *)
  Inductive _behavior
            (behavior: state -> trace -> Prop)
    :
    state -> trace -> Prop :=
  | beh_term
      st retv
      (TERM: terminates st retv)
    :
    _behavior behavior st (term retv)
  | beh_spin
      st
      (SPIN: diverge st)
    :
    _behavior behavior st spin
  | beh_ub
      st tr
      (UB: undefined st)
    :
    _behavior behavior st tr
  (* Note that silent case is inductive. *)
  | beh_silent
      st0 st1 tr
      (STEP: step st0 silentE st1)
      (NEXT: _behavior behavior st1 tr)
    :
    _behavior behavior st0 tr
  | beh_obs
      st0 st1 hd tl
      (STEP: step st0 (obsE hd) st1)
      (NEXT: behavior st1 tl)
    :
    _behavior behavior st0 (cons hd tl)      
  .

  Definition behavior: state -> trace -> Prop := paco2 _behavior bot2.

  Lemma behavior_mon: monotone2 _behavior.
  Proof.
    ii. induction IN; eauto.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
    - econs 5; eauto.
  Qed.

End BEH.

#[global] Hint Constructors _diverge: core.
#[global] Hint Unfold diverge: core.
#[global] Hint Resolve diverge_mon: paco.
#[global] Hint Resolve cpn1_wcompat: paco.

#[global] Hint Constructors _behavior: core.
#[global] Hint Unfold behavior: core.
#[global] Hint Resolve behavior_mon: paco.
#[global] Hint Resolve cpn2_wcompat: paco.

(* Refinement is set inclusion, thus transitive. *)
Definition refines (tgt src: STS): Prop :=
  forall tr, (behavior _ tgt.(init) tr) -> (behavior _ src.(init) tr).

Lemma refines_trans: Transitive refines.
Proof.
  ii. unfold refines in *. eauto.
Qed.

Section SIM.

  Variable src: STS.
  Variable tgt: STS.

  Inductive _sim
            (sim: forall (RR: nat -> nat -> Prop), bool -> bool -> src.(state) -> tgt.(state) -> Prop)
            (RR: nat -> nat -> Prop) (p_src p_tgt: bool)
    :
    src.(state) -> tgt.(state) -> Prop :=
  | sim_term
      st_src st_tgt r_src r_tgt
      (TERMS: src.(terminates) st_src r_src)
      (TERMT: tgt.(terminates) st_tgt r_tgt)
      (SIM: RR r_src r_tgt)
    :
    _sim sim RR p_src p_tgt st_src st_tgt
  | sim_obs
      ev
      st_src0 st_tgt0
      (SIM: forall st_tgt1, (tgt.(step) st_tgt0 (obsE ev) st_tgt1) ->
                       exists st_src1, (src.(step) st_src0 (obsE ev) st_src1) /\
                                    (_sim sim RR true true st_src1 st_tgt1))
    :
    _sim sim RR p_src p_tgt st_src0 st_tgt0
  | sim_silentL
      st_src0 st_tgt
      (SIM: exists st_src1, (src.(step) st_src0 silentE st_src1)
                       /\ (_sim sim RR true p_tgt st_src1 st_tgt))
    :
    _sim sim RR p_src p_tgt st_src0 st_tgt
  | sim_silentR
      st_src st_tgt0
      (SIM: forall st_tgt1, (tgt.(step) st_tgt0 silentE st_tgt1) ->
                       (_sim sim RR p_src true st_src st_tgt1))
    :
    _sim sim RR p_src p_tgt st_src st_tgt0
  | sim_ub
      st_src st_tgt
      (UB: src.(undefined) st_src)
    :
    _sim sim RR p_src p_tgt st_src st_tgt
  | sim_progress
      st_src st_tgt
      (SIM: sim RR false false st_src st_tgt)
      (PS: p_src = true)
      (PT: p_tgt = true)
    :
    _sim sim RR p_src p_tgt st_src st_tgt.

  (* Coq failed to generate a correct induction lemma. *)
  Lemma _sim_ind2 (sim: forall (RR: nat -> nat -> Prop), bool -> bool -> src.(state) -> tgt.(state) -> Prop)
        (RR: nat -> nat -> Prop)
        (P: bool -> bool -> src.(state) -> tgt.(state) -> Prop)
  (TERM: forall p_src p_tgt st_src st_tgt r_src r_tgt
      (TERMS: src.(terminates) st_src r_src)
      (TERMT: tgt.(terminates) st_tgt r_tgt)
      (SIM: RR r_src r_tgt)
    ,
    P p_src p_tgt st_src st_tgt)
  (OBS: forall p_src p_tgt ev st_src0 st_tgt0
      (SIM: forall st_tgt1, (tgt.(step) st_tgt0 (obsE ev) st_tgt1) ->
                       exists st_src1, (src.(step) st_src0 (obsE ev) st_src1) /\
                                    (_sim sim RR true true st_src1 st_tgt1) /\ (P true true st_src1 st_tgt1))
    ,
    P p_src p_tgt st_src0 st_tgt0)
  (SILENTL: forall p_src p_tgt st_src0 st_tgt
      (SIM: exists st_src1, (src.(step) st_src0 silentE st_src1)
                       /\ (_sim sim RR true p_tgt st_src1 st_tgt) /\ (P true p_tgt st_src1 st_tgt))
    ,
    P p_src p_tgt st_src0 st_tgt)
  (SILENTR: forall p_src p_tgt st_src st_tgt0
      (SIM: forall st_tgt1, (tgt.(step) st_tgt0 silentE st_tgt1) ->
                       (_sim sim RR p_src true st_src st_tgt1) /\ (P p_src true st_src st_tgt1))
    ,
    P p_src p_tgt st_src st_tgt0)
  (UB: forall p_src p_tgt st_src st_tgt
      (UB: src.(undefined) st_src)
    ,
    P p_src p_tgt st_src st_tgt)
  (PROG: forall p_src p_tgt st_src st_tgt
      (SIM: sim RR false false st_src st_tgt)
      (PS: p_src = true)
      (PT: p_tgt = true)
    ,
      P p_src p_tgt st_src st_tgt)
      :
      forall p_src p_tgt st_src st_tgt
        (SIM: _sim sim RR p_src p_tgt st_src st_tgt),
        P p_src p_tgt st_src st_tgt.
  Proof.
    fix IH 5. i. inv SIM.
    - eapply TERM; eauto.
    - eapply OBS; eauto. i. specialize (SIM0 _ H). des; eauto.
    - eapply SILENTL; eauto. des; eauto.
    - eapply SILENTR; eauto.
    - eapply UB; eauto.
    - eapply PROG; eauto.
  Qed.

  Definition sim: forall (RR: nat -> nat -> Prop), bool -> bool -> src.(state) -> tgt.(state) -> Prop := paco5 _sim bot5.

  Lemma sim_mon: monotone5 _sim.
  Proof.
    ii. induction IN using _sim_ind2.
    - econs 1; eauto.
    - econs 2; eauto. i. specialize (SIM _ H). des; eauto.
    - econs 3; eauto. des; eauto.
    - econs 4; eauto. i. specialize (SIM _ H). des; eauto.
    - econs 5; eauto.
    - econs 6; eauto.
  Qed.

  Lemma sim_ind (RR: nat -> nat -> Prop)
        (P: bool -> bool -> src.(state) -> tgt.(state) -> Prop)
  (TERM: forall p_src p_tgt st_src st_tgt r_src r_tgt
      (TERMS: src.(terminates) st_src r_src)
      (TERMT: tgt.(terminates) st_tgt r_tgt)
      (SIM: RR r_src r_tgt)
    ,
    P p_src p_tgt st_src st_tgt)
  (OBS: forall p_src p_tgt ev st_src0 st_tgt0
      (SIM: forall st_tgt1, (tgt.(step) st_tgt0 (obsE ev) st_tgt1) ->
                       exists st_src1, (src.(step) st_src0 (obsE ev) st_src1) /\
                                    (sim RR true true st_src1 st_tgt1) /\ (P true true st_src1 st_tgt1))
    ,
    P p_src p_tgt st_src0 st_tgt0)
  (SILENTL: forall p_src p_tgt st_src0 st_tgt
      (SIM: exists st_src1, (src.(step) st_src0 silentE st_src1)
                       /\ (sim RR true p_tgt st_src1 st_tgt) /\ (P true p_tgt st_src1 st_tgt))
    ,
    P p_src p_tgt st_src0 st_tgt)
  (SILENTR: forall p_src p_tgt st_src st_tgt0
      (SIM: forall st_tgt1, (tgt.(step) st_tgt0 silentE st_tgt1) ->
                       (sim RR p_src true st_src st_tgt1) /\ (P p_src true st_src st_tgt1))
    ,
    P p_src p_tgt st_src st_tgt0)
  (UB: forall p_src p_tgt st_src st_tgt
      (UB: src.(undefined) st_src)
    ,
    P p_src p_tgt st_src st_tgt)
  (PROG: forall p_src p_tgt st_src st_tgt
      (SIM: sim RR false false st_src st_tgt)
      (PS: p_src = true)
      (PT: p_tgt = true)
    ,
      P p_src p_tgt st_src st_tgt)
      :
      forall p_src p_tgt st_src st_tgt
        (SIM: sim RR p_src p_tgt st_src st_tgt),
        P p_src p_tgt st_src st_tgt.
  Proof.
    i. eapply _sim_ind2; i; eauto.
    - eapply OBS; eauto. i. specialize (SIM0 _ H). des. esplits; eauto. pfold. eapply sim_mon; eauto.
    - eapply SILENTL; eauto. des. esplits; eauto. pfold. eapply sim_mon; eauto.
    - eapply SILENTR; eauto. i. specialize (SIM0 _ H). des. splits; eauto. pfold. eapply sim_mon; eauto.
    - punfold SIM. 2: apply sim_mon. eapply sim_mon; eauto. i. pclearbot. auto.
  Qed.

  Definition simulation := forall ps pt, sim (@eq nat) ps pt src.(init) tgt.(init).

End SIM.

Section ADEQ.

  Theorem adequacy
          (src tgt: STS)
          (SIM: simulation src tgt)
    :
    refines src tgt.
  Proof.
  Admitted.

End ADEQ.
