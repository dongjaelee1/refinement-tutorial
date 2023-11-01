From Coq Require Import Classes.RelationClasses.
From sflib Require Import sflib.
From Paco Require Import paco.
From Tutorial Require Import Refinement.

Set Implicit Arguments.

Section SIM.

  Context {label: Label}.
  Context {src: @STS label}.
  Context {tgt: @STS label}.

  Notation ekind := label.(event_kind).
  Notation ssort := src.(state_sort).
  Notation tsort := tgt.(state_sort).

  Inductive sim
            (RR: Z -> Z -> Prop)
    :
    src.(state) -> tgt.(state) -> Prop :=
  | sim_term
      st_src st_tgt r_src r_tgt
      (TERMS: ssort st_src = final r_src)
      (TERMT: tsort st_tgt = final r_tgt)
      (SIM: RR r_src r_tgt)
    :
    sim RR st_src st_tgt
  | sim_obs
      st_src0 st_tgt0
      (OBSS: ssort st_src0 = visible)
      (OBST: tsort st_tgt0 = visible)
      (SIM: forall ev st_tgt1,
          (tgt.(step) st_tgt0 ev st_tgt1) ->
          (ekind ev = observableE) ->
          exists st_src1, (src.(step) st_src0 ev st_src1) /\
                       (sim RR st_src1 st_tgt1))
    :
    sim RR st_src0 st_tgt0
  | sim_silentS
      st_src0 st_tgt
      (SORT: ssort st_src0 = internal)
      (SIM: exists ev st_src1,
          (src.(step) st_src0 ev st_src1) /\
            (ekind ev = silentE) /\
            (sim RR st_src1 st_tgt))
    :
    sim RR st_src0 st_tgt
  | sim_silentT
      st_src st_tgt0
      (SORT: tsort st_tgt0 = internal)
      (SIM: forall ev st_tgt1,
          (tgt.(step) st_tgt0 ev st_tgt1) ->
          (ekind ev = silentE) ->
          (sim RR st_src st_tgt1))
    :
    sim RR st_src st_tgt0
  | sim_ub
      st_src st_tgt
      (SORT: ssort st_src = undef)
    :
    sim RR st_src st_tgt
  .

  (* Coq fails to generate a correct induction lemma. *)
  Lemma sim_ind2
        (RR: Z -> Z -> Prop)
        (P: src.(state) -> tgt.(state) -> Prop)
        (TERM: forall st_src st_tgt r_src r_tgt
                 (TERMS: ssort st_src = final r_src)
                 (TERMT: tsort st_tgt = final r_tgt)
                 (SIM: RR r_src r_tgt)
          ,
            P st_src st_tgt)
        (OBS: forall st_src0 st_tgt0
                (OBSS: ssort st_src0 = visible)
                (OBST: tsort st_tgt0 = visible)
                (SIM: forall ev st_tgt1,
                    (tgt.(step) st_tgt0 ev st_tgt1) ->
                    (ekind ev = observableE) ->
                    exists st_src1, (src.(step) st_src0 ev st_src1) /\
                                 (sim RR st_src1 st_tgt1) /\ (P st_src1 st_tgt1))
          ,
            P st_src0 st_tgt0)
        (SILENTS: forall st_src0 st_tgt
                    (SORT: ssort st_src0 = internal)
                    (SIM: exists ev st_src1,
                        (src.(step) st_src0 ev st_src1) /\
                          (ekind ev = silentE) /\
                          (sim RR st_src1 st_tgt) /\ (P st_src1 st_tgt))
          ,
            P st_src0 st_tgt)
        (SILENTT: forall st_src st_tgt0
                    (SORT: tsort st_tgt0 = internal)
                    (SIM: forall ev st_tgt1,
                        (tgt.(step) st_tgt0 ev st_tgt1) ->
                        (ekind ev = silentE) ->
                        ((sim RR st_src st_tgt1) /\ (P st_src st_tgt1)))
          ,
            P st_src st_tgt0)
        (UB: forall st_src st_tgt
               (UB: ssort st_src = undef)
          ,
            P st_src st_tgt)
    :
    forall st_src st_tgt
      (SIM: sim RR st_src st_tgt),
      P st_src st_tgt.
  Proof.
    fix IH 3. i. inv SIM.
    - eapply TERM; eauto.
    - eapply OBS; eauto. i. specialize (SIM0 _ _ H H0). des; eauto.
    - eapply SILENTS; eauto. des; eauto. do 2 eexists. splits; eauto.
    - eapply SILENTT; eauto.
    - eapply UB; eauto.
  Qed.

End SIM.
#[export] Hint Constructors sim: core.

Definition simulation {l: Label} (src tgt: @STS l) := sim (@eq Z) src.(init) tgt.(init).

Section ADEQ.

  Context {label: Label}.
  Context {src: @STS label}.
  Context {tgt: @STS label}.

  Lemma adequacy_spin
        (RR: Z -> Z -> Prop)
        (st_src: src.(state))
        (st_tgt: tgt.(state))
        (SIM: sim RR st_src st_tgt)
        (SPIN: diverge st_tgt)
    :
    diverge st_src.
  Proof.
    revert_until SIM. induction SIM using @sim_ind2; ii.
    { punfold SPIN. inv SPIN. 1,2: rewrite SORT in TERMT; ss. }
    { punfold SPIN. inv SPIN. 1,2: rewrite SORT in OBST; ss. }
    { des. pfold. econs 1; eauto. left. apply SIM2. auto. }
    { punfold SPIN. inv SPIN.
      - pclearbot. specialize (SIM _ _ STEP KIND). des. apply SIM0 in DIV; auto.
      - rewrite SORT0 in SORT; ss.
    }
    { pfold. econs 2. auto. }
  Qed.

  Lemma adequacy_aux
        (st_src0: src.(state))
        (st_tgt0: tgt.(state))
        (SIM: sim eq st_src0 st_tgt0)
    :
    forall tr, (behavior st_tgt0 tr) -> (behavior st_src0 tr).
  Proof.
    ginit. revert_until tgt. gcofix CIH. i.
    move H0 before CIH. revert_until H0. induction H0 using @behavior_ind; ii.
    { generalize dependent retv. rename st into st_tgt0.
      induction SIM using @sim_ind2; i; ss; clarify.
      { rewrite SORT in TERMT. inv TERMT. gstep. econs 1. auto. }
      { rewrite SORT in OBST; inv OBST. }
      { des. guclo @behavior_indC_spec. econs 4; eauto. }
      { rewrite SORT0 in SORT. inv SORT. }
      { gstep. econs 3. auto. }
    }
    { gstep. econs 2. eapply adequacy_spin; eauto. }
    { move SIM before CIH. clear CIH. revert_until SIM.
      induction SIM using @sim_ind2; ii; ss; clarify.
      { rewrite SORT in TERMT; inv TERMT. }
      { rewrite SORT in OBST; inv OBST. }
      { des. guclo @behavior_indC_spec. econs 4; eauto. }
      { rewrite SORT0 in SORT; inv SORT. }
      { gstep. econs 3; auto. }
    }
    { move IHbehavior before CIH. clear CIH. move SIM before IHbehavior. revert_until SIM.
      induction SIM using @sim_ind2; ii; ss; clarify.
      { rewrite SORT in TERMT; inv TERMT. }
      { rewrite SORT in OBST; inv OBST. }
      { des. guclo @behavior_indC_spec. econs 4. 4: eauto. 3: eauto. all: auto. }
      { specialize (SIM _ _ STEP KIND). des. eapply IHbehavior; eauto. }
      { gstep. econs 3; auto. }
    }
    { move SIM before CIH. revert_until SIM.
      induction SIM using @sim_ind2; ii; ss; clarify.
      { rewrite SORT in TERMT; inv TERMT. }
      { specialize (SIM _ _ STEP KIND). des. clear SIM1. gstep. econs 5; eauto. gfinal. left. eauto. }
      { clear CIH. des. specialize (SIM2 _ _ _ SORT0 KIND STEP H0). guclo @behavior_indC_spec. econs 4; eauto. }
      { rewrite SORT0 in SORT; inv SORT. }
      { gstep. econs 3; auto. }
    }
  Qed.

  Theorem adequacy
          (SIM: simulation src tgt)
    :
    refines tgt src.
  Proof.
    ii. eapply adequacy_aux; eauto.
  Qed.

End ADEQ.
