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

  Variant sort: Type :=
    | internal
    (* We fix return value as nat for simplicity. *)
    | final (retv: nat)
    | visible
    | undef
  .

  Record STS: Type :=
    mk_sts {
        state: Type;
        init: state;
        (* step is a relation, not a function, because in general, program execution can be non-deterministic. *)
        step: state -> eventE -> state -> Prop;
        state_sort: state -> sort;
      }.

  Record STS_wf (s: STS): Prop :=
    mk_sts_wf {
        vis_wf: forall st0, (s.(state_sort) st0 = visible) -> (forall ev st1, s.(step) st0 ev st1 -> ev <> silentE);
        final_wf: forall st0 retv, (s.(state_sort) st0 = final retv) -> (forall ev st1, ~ s.(step) st0 ev st1);
      }.

End STS.

(* We now define the behavior of a STS. *)
Section BEH.

  Variable prog: STS.
  Local Notation state := prog.(state).
  Local Notation init := prog.(init).
  Local Notation step := prog.(step).
  Local Notation ssort := prog.(state_sort).

  Variant _diverge
          (diverge: state -> Prop)
    :
    state -> Prop :=
    | diverge_silent
        st0 st1
        (SORT: ssort st0 = internal)
        (STEP: step st0 silentE st1)
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
      st0 st1 tr
      (SORT: ssort st0 = internal)
      (STEP: step st0 silentE st1)
      (NEXT: _behavior behavior st1 tr)
    :
    _behavior behavior st0 tr
  | beh_obs
      st0 st1 hd tl
      (SORT: ssort st0 = visible)
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
  (SILENT: forall st0 st1 tr
      (SORT: ssort st0 = internal)
      (STEP: step st0 silentE st1)
      (NEXT: behavior st1 tr)
      (IH: P st1 tr)
    ,
    P st0 tr)
  (OBS: forall st0 st1 hd tl
      (SORT: ssort st0 = visible)
      (STEP: step st0 (obsE hd) st1)
      (NEXT: behavior st1 tl)
    ,
      P st0 (cons hd tl)),
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
        st0 st1 tr
        (SORT: ssort st0 = internal)
        (STEP: step st0 silentE st1)
        (NEXT: behavior st1 tr)
      :
      behavior_indC behavior st0 tr
    | beh_indC_obs
        st0 st1 hd tl
        (SORT: ssort st0 = visible)
        (STEP: step st0 (obsE hd) st1)
        (NEXT: behavior st1 tl)
      :
      behavior_indC behavior st0 (cons hd tl)
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

  (* Refinement is set inclusion, thus transitive. *)
  Definition refines (tgt src: STS): Prop :=
    forall tr, (behavior _ tgt.(init) tr) -> (behavior _ src.(init) tr).

  Lemma refines_trans: Transitive refines.
  Proof.
    ii. unfold refines in *. eauto.
  Qed.

End REF.

Section SIM.

  Variable src: STS.
  Variable tgt: STS.
  Notation sort0 := src.(state_sort).
  Notation sort1 := tgt.(state_sort).

  Inductive _sim
            (sim: forall (RR: nat -> nat -> Prop), bool -> bool -> src.(state) -> tgt.(state) -> Prop)
            (RR: nat -> nat -> Prop) (p_src p_tgt: bool)
    :
    src.(state) -> tgt.(state) -> Prop :=
  | sim_term
      st_src st_tgt r_src r_tgt
      (TERMS: sort0 st_src = final r_src)
      (TERMT: sort1 st_tgt = final r_tgt)
      (SIM: RR r_src r_tgt)
    :
    _sim sim RR p_src p_tgt st_src st_tgt
  | sim_obs
      st_src0 st_tgt0
      (OBSS: sort0 st_src0 = visible)
      (OBST: sort1 st_tgt0 = visible)
      (SIM: forall ev st_tgt1, (tgt.(step) st_tgt0 (obsE ev) st_tgt1) ->
                       exists st_src1, (src.(step) st_src0 (obsE ev) st_src1) /\
                                    (_sim sim RR true true st_src1 st_tgt1))
    :
    _sim sim RR p_src p_tgt st_src0 st_tgt0
  | sim_silentL
      st_src0 st_tgt
      (SORT: sort0 st_src0 = internal)
      (SIM: exists st_src1, (src.(step) st_src0 silentE st_src1)
                       /\ (_sim sim RR true p_tgt st_src1 st_tgt))
    :
    _sim sim RR p_src p_tgt st_src0 st_tgt
  | sim_silentR
      st_src st_tgt0
      (SORT: sort1 st_tgt0 = internal)
      (SIM: forall st_tgt1, (tgt.(step) st_tgt0 silentE st_tgt1) ->
                       (_sim sim RR p_src true st_src st_tgt1))
    :
    _sim sim RR p_src p_tgt st_src st_tgt0
  | sim_ub
      st_src st_tgt
      (SORT: sort0 st_src = undef)
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
      (TERMS: sort0 st_src = final r_src)
      (TERMT: sort1 st_tgt = final r_tgt)
      (SIM: RR r_src r_tgt)
    ,
    P p_src p_tgt st_src st_tgt)
  (OBS: forall p_src p_tgt st_src0 st_tgt0
      (OBSS: sort0 st_src0 = visible)
      (OBST: sort1 st_tgt0 = visible)
      (SIM: forall ev st_tgt1, (tgt.(step) st_tgt0 (obsE ev) st_tgt1) ->
                       exists st_src1, (src.(step) st_src0 (obsE ev) st_src1) /\
                                    (_sim sim RR true true st_src1 st_tgt1) /\ (P true true st_src1 st_tgt1))
    ,
    P p_src p_tgt st_src0 st_tgt0)
  (SILENTL: forall p_src p_tgt st_src0 st_tgt
      (SORT: sort0 st_src0 = internal)
      (SIM: exists st_src1, (src.(step) st_src0 silentE st_src1)
                       /\ (_sim sim RR true p_tgt st_src1 st_tgt) /\ (P true p_tgt st_src1 st_tgt))
    ,
    P p_src p_tgt st_src0 st_tgt)
  (SILENTR: forall p_src p_tgt st_src st_tgt0
      (SORT: sort1 st_tgt0 = internal)
      (SIM: forall st_tgt1, (tgt.(step) st_tgt0 silentE st_tgt1) ->
                       (_sim sim RR p_src true st_src st_tgt1) /\ (P p_src true st_src st_tgt1))
    ,
    P p_src p_tgt st_src st_tgt0)
  (UB: forall p_src p_tgt st_src st_tgt
      (UB: sort0 st_src = undef)
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
    - eapply OBS; eauto. i. specialize (SIM0 _ _ H). des; eauto.
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
    - econs 2; eauto. i. specialize (SIM _ _ H). des; eauto.
    - econs 3; eauto. des; eauto.
    - econs 4; eauto. i. specialize (SIM _ H). des; eauto.
    - econs 5; eauto.
    - econs 6; eauto.
  Qed.

  Lemma sim_ind (RR: nat -> nat -> Prop)
        (P: bool -> bool -> src.(state) -> tgt.(state) -> Prop)
  (TERM: forall p_src p_tgt st_src st_tgt r_src r_tgt
      (TERMS: sort0 st_src = final r_src)
      (TERMT: sort1 st_tgt = final r_tgt)
      (SIM: RR r_src r_tgt)
    ,
    P p_src p_tgt st_src st_tgt)
  (OBS: forall p_src p_tgt st_src0 st_tgt0
      (OBSS: sort0 st_src0 = visible)
      (OBST: sort1 st_tgt0 = visible)
      (SIM: forall ev st_tgt1, (tgt.(step) st_tgt0 (obsE ev) st_tgt1) ->
                       exists st_src1, (src.(step) st_src0 (obsE ev) st_src1) /\
                                    (sim RR true true st_src1 st_tgt1) /\ (P true true st_src1 st_tgt1))
    ,
    P p_src p_tgt st_src0 st_tgt0)
  (SILENTL: forall p_src p_tgt st_src0 st_tgt
      (SORT: sort0 st_src0 = internal)
      (SIM: exists st_src1, (src.(step) st_src0 silentE st_src1)
                       /\ (sim RR true p_tgt st_src1 st_tgt) /\ (P true p_tgt st_src1 st_tgt))
    ,
    P p_src p_tgt st_src0 st_tgt)
  (SILENTR: forall p_src p_tgt st_src st_tgt0
      (SORT: sort1 st_tgt0 = internal)
      (SIM: forall st_tgt1, (tgt.(step) st_tgt0 silentE st_tgt1) ->
                       (sim RR p_src true st_src st_tgt1) /\ (P p_src true st_src st_tgt1))
    ,
    P p_src p_tgt st_src st_tgt0)
  (UB: forall p_src p_tgt st_src st_tgt
      (UB: sort0 st_src = undef)
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
    - eapply OBS; eauto. i. specialize (SIM0 _ _ H). des. esplits; eauto. pfold. eapply sim_mon; eauto.
    - eapply SILENTL; eauto. des. esplits; eauto. pfold. eapply sim_mon; eauto.
    - eapply SILENTR; eauto. i. specialize (SIM0 _ H). des. splits; eauto. pfold. eapply sim_mon; eauto.
    - punfold SIM. 2: apply sim_mon. eapply sim_mon; eauto. i. pclearbot. auto.
  Qed.

  Hint Constructors _sim: core.
  Hint Unfold sim: core.
  Hint Resolve sim_mon: paco.
  Hint Resolve cpn5_wcompat: paco.

  (* Upto properties. *)

  Variant sim_indC
          (sim: forall (RR: nat -> nat -> Prop), bool -> bool -> src.(state) -> tgt.(state) -> Prop)
          (RR: nat -> nat -> Prop) p_src p_tgt
    :
    src.(state) -> tgt.(state) -> Prop :=
    | sim_indC_term
        st_src st_tgt r_src r_tgt
        (TERMS: sort0 st_src = final r_src)
        (TERMT: sort1 st_tgt = final r_tgt)
        (SIM: RR r_src r_tgt)
      :
      sim_indC sim RR p_src p_tgt st_src st_tgt
    | sim_indC_obs
        st_src0 st_tgt0
        (OBSS: sort0 st_src0 = visible)
        (OBST: sort1 st_tgt0 = visible)
        (SIM: forall ev st_tgt1, (tgt.(step) st_tgt0 (obsE ev) st_tgt1) ->
                         exists st_src1, (src.(step) st_src0 (obsE ev) st_src1) /\
                                      (_sim sim RR true true st_src1 st_tgt1))
      :
      sim_indC sim RR p_src p_tgt st_src0 st_tgt0
    | sim_indC_silentL
        st_src0 st_tgt
        (SORT: sort0 st_src0 = internal)
        (SIM: exists st_src1, (src.(step) st_src0 silentE st_src1)
                         /\ (sim RR true p_tgt st_src1 st_tgt))
      :
      sim_indC sim RR p_src p_tgt st_src0 st_tgt
    | sim_indC_silentR
        st_src st_tgt0
        (SORT: sort1 st_tgt0 = internal)
        (SIM: forall st_tgt1, (tgt.(step) st_tgt0 silentE st_tgt1) ->
                         (sim RR p_src true st_src st_tgt1))
      :
      sim_indC sim RR p_src p_tgt st_src st_tgt0
    | sim_indC_ub
        st_src st_tgt
        (UB: sort0 st_src = undef)
      :
      sim_indC sim RR p_src p_tgt st_src st_tgt
    | sim_indC_progress
        st_src st_tgt
        (SIM: sim RR false false st_src st_tgt)
        (PS: p_src = true)
        (PT: p_tgt = true)
      :
      sim_indC sim RR p_src p_tgt st_src st_tgt.

  Lemma sim_indC_mon: monotone5 sim_indC.
  Proof.
    ii. inv IN.
    all: try (econs; eauto; fail).
    - econs 2; auto. i. specialize (SIM _ _ H). des. esplits; eauto. eapply sim_mon; eauto.
    - des. econs 3; eauto.
  Qed.

  Hint Resolve sim_indC_mon: paco.

  Lemma sim_indC_wrespectful: wrespectful5 _sim sim_indC.
  Proof.
    econs; eauto with paco.
    i. inv PR; eauto.
    - econs 2; eauto. i. specialize (SIM _ _ H). des. esplits; eauto. eapply sim_mon; eauto. i. eapply rclo5_base. auto.
    - econs 3; eauto. des. esplits; eauto. eapply sim_mon; eauto. i. eapply rclo5_base. auto.
    - econs 4; eauto. i. specialize (SIM _ H). eapply sim_mon; eauto. i. eapply rclo5_base. auto.
    - eapply sim_mon; eauto. i. eapply rclo5_base. auto.
  Qed.

  Lemma sim_indC_spec: sim_indC <6= gupaco5 _sim (cpn5 _sim).
  Proof.
    i. eapply wrespect5_uclo; eauto with paco. eapply sim_indC_wrespectful.
  Qed.

  Variant sim_progressC
          (sim: forall (RR: nat -> nat -> Prop), bool -> bool -> src.(state) -> tgt.(state) -> Prop)
          (RR: nat -> nat -> Prop)
    :
    bool -> bool -> src.(state) -> tgt.(state) -> Prop :=
    | sim_progressC_intro
        ps0 ps1 pt0 pt1 st_src st_tgt
        (SIM: sim RR ps1 pt1 st_src st_tgt)
        (SRC: ps1 = true -> ps0 = true)
        (TGT: pt1 = true -> pt0 = true)
      :
      sim_progressC sim RR ps0 pt0 st_src st_tgt.

  Lemma sim_progressC_mon: monotone5 sim_progressC.
  Proof.
    ii. inv IN. econs; eauto.
  Qed.

  Hint Resolve sim_progressC_mon: paco.

  Lemma sim_progressC_wrespectful: wrespectful5 _sim sim_progressC.
  Proof.
    econs; eauto with paco.
    i. inv PR. apply GF in SIM.
    generalize dependent x1. generalize dependent x2.
    induction SIM using _sim_ind2; i; eauto.
    - econs 2; auto. i. specialize (SIM _ _ H). des. esplits; eauto.
    - econs 3; auto. des. esplits; eauto.
    - econs 4; auto. i. specialize (SIM _ H). des. auto.
    - clarify.
      hexploit TGT; clear TGT; auto; i; clarify.
      hexploit SRC; clear SRC; auto; i; clarify.
      eapply sim_mon. econs 6; eauto.
      i. eapply rclo5_base. auto.
  Qed.

  Lemma sim_progressC_spec: sim_progressC <6= gupaco5 _sim (cpn5 _sim).
  Proof.
    i. eapply wrespect5_uclo; eauto with paco. eapply sim_progressC_wrespectful.
  Qed.

End SIM.
#[export] Hint Constructors _sim: core.
#[export] Hint Unfold sim: core.
#[export] Hint Resolve sim_mon: paco.
#[export] Hint Resolve cpn5_wcompat: paco.

Definition simulation (src tgt: STS) := forall ps pt, sim src tgt (@eq nat) ps pt src.(init) tgt.(init).

Section ADEQ.

  Lemma adequacy_spin
        (SRC TGT: STS)
        (WF: STS_wf TGT)
        (RR: nat -> nat -> Prop)
        ps pt src tgt
        (SIM: sim SRC TGT RR ps pt src tgt)
        (SPIN: diverge _ tgt)
    :
    diverge _ src.
  Proof.
    ginit. revert_until RR. gcofix CIH. i. revert SPIN.
    induction SIM using sim_ind; i; clarify.
    { exfalso. punfold SPIN. inv SPIN. 1,2: rewrite SORT in TERMT; ss. }
    { exfalso. punfold SPIN. inv SPIN. 1,2: rewrite SORT in OBST; ss. }
    { des. gstep. econs 1; eauto. gfinal. left; eauto. }
    { punfold SPIN. inv SPIN.
      2:{ rewrite SORT0 in SORT; ss. }
      pclearbot. specialize (SIM _ STEP). des. apply SIM0 in DIV; auto.
    }
    { gstep. econs 2. auto. }
    { remember false in SIM at 1. remember false in SIM at 1. clear Heqb0. revert Heqb SPIN.
      induction SIM using sim_ind; i; clarify.
      { exfalso. punfold SPIN. inv SPIN. 1,2: rewrite SORT in TERMT; ss. }
      { exfalso. punfold SPIN. inv SPIN. 1,2: rewrite SORT in OBST; ss. }
      { des. gstep. econs 1; eauto. gfinal. left; eauto. }
      { punfold SPIN. inv SPIN.
        2:{ rewrite SORT0 in SORT; ss. }
        pclearbot. specialize (SIM _ STEP). des. apply SIM0 in DIV; auto.
      }
      { gstep. econs 2. auto. }
    }
  Qed.

  Lemma adequacy_aux
        (SRC TGT: STS)
        (WF: STS_wf TGT)
        (st_src0: SRC.(state))
        (st_tgt0: TGT.(state))
        ps pt
        (SIM: sim _ _ eq ps pt st_src0 st_tgt0)
    :
    forall tr, (behavior _ st_tgt0 tr) -> (behavior _ st_src0 tr).
  Proof.
    revert_until WF. ginit. gcofix CIH. i.
    move H0 before CIH. revert_until H0. induction H0 using behavior_ind; ii.
    { generalize dependent retv. rename st into st_tgt0.
      induction SIM using sim_ind; i; ss; clarify.
      { rewrite SORT in TERMT. inv TERMT. gstep. econs 1. auto. }
      { rewrite SORT in OBST; inv OBST. }
      { des. guclo behavior_indC_spec. econs 4; auto. auto. }
      { rewrite SORT0 in SORT. inv SORT. }
      { gstep. econs 3. auto. }
      { remember false in SIM at 1. remember false in SIM at 1. clear Heqb.
        move SIM before CIH. revert_until SIM. induction SIM using sim_ind; ii; ss; clarify.
        { rewrite SORT in TERMT. inv TERMT. gstep. econs 1. auto. }
        { rewrite SORT in OBST; inv OBST. }
        { des. guclo behavior_indC_spec. econs 4; auto. auto. }
        { rewrite SORT0 in SORT. inv SORT. }
        { gstep. econs 3. auto. }
      }
    }
    { gstep. econs 2. eapply adequacy_spin; eauto. }
    { move SIM before CIH. revert_until SIM. induction SIM using sim_ind; ii; ss; clarify.
      { rewrite SORT in TERMT; inv TERMT. }
      { rewrite SORT in OBST; inv OBST. }
      { des. guclo behavior_indC_spec. econs 4; eauto. }
      { rewrite SORT0 in SORT; inv SORT. }
      { gstep. econs 3; auto. }
      { remember false in SIM at 1. remember false in SIM at 1. clear Heqb.
        move SIM before CIH. revert_until SIM. induction SIM using sim_ind; ii; ss; clarify.
        { rewrite SORT in TERMT; inv TERMT. }
        { rewrite SORT in OBST; inv OBST. }
        { des. guclo behavior_indC_spec. econs 4; eauto. }
        { rewrite SORT0 in SORT; inv SORT. }
        { gstep. econs 3; auto. }
      }
    }
    { move IHbehavior before CIH. move SIM before IHbehavior. revert_until SIM. induction SIM using sim_ind; ii; ss; clarify.
      { rewrite SORT in TERMT; inv TERMT. }
      { rewrite SORT in OBST; inv OBST. }
      { des. guclo behavior_indC_spec. econs 4; eauto. }
      { specialize (SIM _ STEP). des. eapply IHbehavior; eauto. }
      { gstep. econs 3; auto. }
      { remember false in SIM at 1. remember false in SIM at 1. clear Heqb.
        move SIM before CIH. revert_until SIM. induction SIM using sim_ind; ii; ss; clarify.
        { rewrite SORT in TERMT; inv TERMT. }
        { rewrite SORT in OBST; inv OBST. }
        { des. guclo behavior_indC_spec. econs 4; eauto. }
        { specialize (SIM _ STEP). des. eapply IHbehavior; eauto. }
        { gstep. econs 3; auto. }
      }
    }
    { move SIM before CIH. revert_until SIM. induction SIM using sim_ind; ii; ss; clarify.
      { rewrite SORT in TERMT; inv TERMT. }
      { specialize (SIM _ _ STEP). des. gstep. econs 5; eauto. gfinal. left. eauto. }
      { des. guclo behavior_indC_spec. econs 4; eauto. }
      { rewrite SORT0 in SORT; inv SORT. }
      { gstep. econs 3; auto. }
      { remember false in SIM at 1. remember false in SIM at 1. clear Heqb.
        move SIM before CIH. revert_until SIM. induction SIM using sim_ind; ii; ss; clarify.
        { rewrite SORT in TERMT; inv TERMT. }
        { specialize (SIM _ _ STEP). des. gstep. econs 5; eauto. gfinal. left. eauto. }
        { des. guclo behavior_indC_spec. econs 4; eauto. }
        { rewrite SORT0 in SORT; inv SORT. }
        { gstep. econs 3; auto. }
      }
    }
  Qed.

  Theorem adequacy
          (SRC TGT: STS)
          (WF: STS_wf TGT)
          (SIM: simulation SRC TGT)
    :
    refines TGT SRC.
  Proof.
    ii. eapply adequacy_aux; eauto.
    Unshelve. all: exact false.
  Qed.

End ADEQ.
