From Coq Require Import Classes.RelationClasses.
From sflib Require Import sflib.
From Paco Require Import paco.
From Coq Require Export ZArith.

Set Implicit Arguments.
Open Scope Z_scope.

(* Program refinement is an approach in program verification, 
   where one verifies that every possible behavior of a program 
   (called the target or the implementation) 
   is also possible by another program (called the source or the spec).
   Usually, behavior of a program is defined as a set of traces, 
   where a trace is a stream of observable events of a program, 
   including divergence (infinite silent execution), termination, and error.
   Observable events can differ by what one wants to verify.
*)

(* We first define the trace. *)
Section TRACE.

  Context {event: Type}.

  Variant observable: Type :=
    | obs (ev: event)
  .

  CoInductive trace: Type :=
  (* Termination can return a value, which is Z for our case. *)
  | term (retv: Z)
  | spin
  | cons (hd: observable) (tl: trace)
  .

End TRACE.

(* We assume a simple state transition system. *)
Section STS.

  Variant kind: Type :=
    | silentE
    | observableE
  .

  Record Label: Type :=
    mk_label {
        event: Type;
        event_kind: event -> kind;
      }.

  Variant sort: Type :=
    | internal
    | final (retv: Z)
    | visible
    | undef
  .

  Record STS {l: Label}: Type :=
    mk_sts {
        state: Type;
        init: state;
        (* Note that step is a relation, not a function. In general, program execution can be non-deterministic. *)
        step: state -> l.(event) -> state -> Prop;
        state_sort: state -> sort;
      }.

End STS.

(* We now define the behavior of a STS. *)
Section BEH.

  Context {label: Label}.
  Local Notation event := label.(event).
  Local Notation ekind := label.(event_kind).

  Context {prog: @STS label}.
  Local Notation state := prog.(state).
  Local Notation init := prog.(init).
  Local Notation step := prog.(step).
  Local Notation ssort := prog.(state_sort).

  Variant _diverge
          (diverge: state -> Prop)
    :
    state -> Prop :=
    | diverge_silent
        st0 ev st1
        (SORT: ssort st0 = internal)
        (KIND: ekind ev = silentE)
        (STEP: step st0 ev st1)
        (DIV: diverge st1)
      :
      _diverge diverge st0
    | diverge_ub
        st
        (SORT: ssort st = undef)
      :
      _diverge diverge st
  .

  Definition diverge: state -> Prop := paco1 _diverge bot1.

  (* Boilerplate code for paco. *)
  Lemma diverge_mon: monotone1 _diverge.
  Proof.
    ii. inv IN.
    - econs 1; eauto.
      (* eapply diverge_silent; eauto. *)
    - econs 2; eauto.
  Qed.

  Hint Constructors _diverge: core.
  Hint Unfold diverge: core.
  Hint Resolve diverge_mon: paco.
  Hint Resolve cpn1_wcompat: paco.

  (* Behavior is a mixed inductive-coinductive definition.
     Inductive because we only want finite number of silent steps (infinite silent step case is treated as divergence).
  *)
  Inductive _behavior
            (behavior: state -> trace -> Prop)
    :
    state -> trace -> Prop :=
  | beh_term
      st retv
      (SORT: ssort st = final retv)
    :
    _behavior behavior st (term retv)
  | beh_spin
      st
      (SPIN: diverge st)
    :
    _behavior behavior st spin
  | beh_ub
      st tr
      (SORT: ssort st = undef)
    :
    _behavior behavior st tr
  (* Silent case is inductive. *)
  | beh_silent
      st0 ev st1 tr
      (SORT: ssort st0 = internal)
      (KIND: ekind ev = silentE)
      (STEP: step st0 ev st1)
      (NEXT: _behavior behavior st1 tr)
    :
    _behavior behavior st0 tr
  | beh_obs
      st0 ev st1 tl
      (SORT: ssort st0 = visible)
      (KIND: ekind ev = observableE)
      (STEP: step st0 ev st1)
      (NEXT: behavior st1 tl)
    :
    _behavior behavior st0 (cons (obs ev) tl)
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

  Hint Constructors _behavior: core.
  Hint Unfold behavior: core.
  Hint Resolve behavior_mon: paco.
  Hint Resolve cpn2_wcompat: paco.

  Lemma behavior_ind:
    forall (P: state -> trace -> Prop)
  (TERM: forall st retv
      (SORT: ssort st = final retv)
    ,
      P st (term retv))
  (SPIN: forall st
      (SPIN: diverge st)
    ,
    P st spin)
  (UB: forall st tr
      (SORT: ssort st = undef)
    ,
    P st tr)
  (SILENT: forall st0 ev st1 tr
      (SORT: ssort st0 = internal)
      (KIND: ekind ev = silentE)
      (STEP: step st0 ev st1)
      (NEXT: behavior st1 tr)
      (IH: P st1 tr)
    ,
    P st0 tr)
  (OBS: forall st0 ev st1 tl
      (SORT: ssort st0 = visible)
      (KIND: ekind ev = observableE)
      (STEP: step st0 ev st1)
      (NEXT: behavior st1 tl)
    ,
      P st0 (cons (obs ev) tl)),
    forall st tr, (behavior st tr) -> P st tr.
  Proof.
    i. eapply _behavior_ind; eauto.
    - i. pclearbot. eapply OBS; eauto.
    - punfold H.
  Qed.

  (* Upto properties. *)

  Variant behavior_indC
          (behavior: state -> trace -> Prop)
    :
    state -> trace -> Prop :=
    | beh_indC_term
        st retv
        (SORT: ssort st = final retv)
      :
      behavior_indC behavior st (term retv)
    | beh_indC_spin
        st
        (SPIN: diverge st)
      :
      behavior_indC behavior st spin
    | beh_indC_ub
        st tr
        (SORT: ssort st = undef)
      :
      behavior_indC behavior st tr
    | beh_indC_silent
        st0 ev st1 tr
        (SORT: ssort st0 = internal)
        (KIND: ekind ev = silentE)
        (STEP: step st0 ev st1)
        (NEXT: behavior st1 tr)
      :
      behavior_indC behavior st0 tr
    | beh_indC_obs
        st0 ev st1 tl
        (SORT: ssort st0 = visible)
        (KIND: ekind ev = observableE)
        (STEP: step st0 ev st1)
        (NEXT: behavior st1 tl)
      :
      behavior_indC behavior st0 (cons (obs ev) tl)
  .

  Lemma behavior_indC_mon: monotone2 behavior_indC.
  Proof.
    ii. inv IN. all: try (econs; eauto; fail).
  Qed.

  Hint Resolve behavior_indC_mon: paco.

  Lemma behavior_indC_wrespectful: wrespectful2 _behavior behavior_indC.
  Proof.
    econs; eauto with paco.
    i. inv PR; eauto.
    - econs 4; eauto. eapply behavior_mon; eauto. i. eapply rclo2_base. auto.
    - econs 5; eauto. eapply rclo2_base. eauto.
  Qed.

  Lemma behavior_indC_spec: behavior_indC <3= gupaco2 _behavior (cpn2 _behavior).
  Proof.
    i. eapply wrespect2_uclo; eauto with paco. eapply behavior_indC_wrespectful.
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

Section REF.

  Context {label: Label}.

  (* Refinement is set inclusion, thus transitive. *)
  Definition refines (tgt src: @STS label): Prop :=
    forall tr, (behavior tgt.(init) tr) -> (behavior src.(init) tr).

  Lemma refines_trans: Transitive refines.
  Proof.
    ii. unfold refines in *. eauto.
  Qed.

End REF.
