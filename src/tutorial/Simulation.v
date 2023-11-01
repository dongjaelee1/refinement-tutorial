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

  Inductive _sim
            (sim: forall (RR: Z -> Z -> Prop), bool -> bool -> src.(state) -> tgt.(state) -> Prop)
            (RR: Z -> Z -> Prop) (p_src p_tgt: bool)
    :
    src.(state) -> tgt.(state) -> Prop :=
  | sim_term
      st_src st_tgt r_src r_tgt
      (TERMS: ssort st_src = final r_src)
      (TERMT: tsort st_tgt = final r_tgt)
      (SIM: RR r_src r_tgt)
    :
    _sim sim RR p_src p_tgt st_src st_tgt
  | sim_obs
      st_src0 st_tgt0
      (OBSS: ssort st_src0 = normal)
      (OBST: tsort st_tgt0 = normal)
      (SIM: forall ev st_tgt1,
          (tgt.(step) st_tgt0 ev st_tgt1) ->
          (ekind ev = observableE) /\
          exists st_src1, (src.(step) st_src0 ev st_src1) /\
                       (_sim sim RR true true st_src1 st_tgt1))
    :
    _sim sim RR p_src p_tgt st_src0 st_tgt0
  | sim_silentS
      st_src0 st_tgt
      (SORT: ssort st_src0 = normal)
      (SIM: exists ev st_src1,
          (src.(step) st_src0 ev st_src1) /\
            (ekind ev = silentE) /\
            (_sim sim RR true p_tgt st_src1 st_tgt))
    :
    _sim sim RR p_src p_tgt st_src0 st_tgt
  | sim_silentR
      st_src st_tgt0
      (SORT: tsort st_tgt0 = normal)
      (SIM: forall ev st_tgt1,
          (tgt.(step) st_tgt0 ev st_tgt1) ->
          (ekind ev = silentE) /\
          (_sim sim RR p_src true st_src st_tgt1))
    :
    _sim sim RR p_src p_tgt st_src st_tgt0
  | sim_ub
      st_src st_tgt
      (SORT: ssort st_src = undef)
    :
    _sim sim RR p_src p_tgt st_src st_tgt
  | sim_progress
      st_src st_tgt
      (SIM: sim RR false false st_src st_tgt)
      (PS: p_src = true)
      (PT: p_tgt = true)
    :
    _sim sim RR p_src p_tgt st_src st_tgt.

  (* Coq fails to generate a correct induction lemma. *)
  Lemma _sim_ind2 (sim: forall (RR: Z -> Z -> Prop), bool -> bool -> src.(state) -> tgt.(state) -> Prop)
        (RR: Z -> Z -> Prop)
        (P: bool -> bool -> src.(state) -> tgt.(state) -> Prop)
  (TERM: forall p_src p_tgt st_src st_tgt r_src r_tgt
      (TERMS: ssort st_src = final r_src)
      (TERMT: tsort st_tgt = final r_tgt)
      (SIM: RR r_src r_tgt)
    ,
    P p_src p_tgt st_src st_tgt)
  (OBS: forall p_src p_tgt st_src0 st_tgt0
      (OBSS: ssort st_src0 = normal)
      (OBST: tsort st_tgt0 = normal)
      (SIM: forall ev st_tgt1, (tgt.(step) st_tgt0 ev st_tgt1) ->
                          (ekind ev = observableE) /\
                       exists st_src1, (src.(step) st_src0 ev st_src1) /\
                                    (_sim sim RR true true st_src1 st_tgt1) /\ (P true true st_src1 st_tgt1))
    ,
    P p_src p_tgt st_src0 st_tgt0)
  (SILENTL: forall p_src p_tgt st_src0 st_tgt
      (SORT: ssort st_src0 = normal)
      (SIM: exists ev st_src1, (src.(step) st_src0 ev st_src1) /\
                            (ekind ev = silentE) /\
                       (_sim sim RR true p_tgt st_src1 st_tgt) /\ (P true p_tgt st_src1 st_tgt))
    ,
    P p_src p_tgt st_src0 st_tgt)
  (SILENTR: forall p_src p_tgt st_src st_tgt0
      (SORT: tsort st_tgt0 = normal)
      (SIM: forall ev st_tgt1, (tgt.(step) st_tgt0 ev st_tgt1) ->
                          (ekind ev = silentE) /\
                       ((_sim sim RR p_src true st_src st_tgt1) /\ (P p_src true st_src st_tgt1)))
    ,
    P p_src p_tgt st_src st_tgt0)
  (UB: forall p_src p_tgt st_src st_tgt
      (UB: ssort st_src = undef)
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
    - eapply OBS; eauto. i. specialize (SIM0 _ _ H). des; esplits; eauto.
    - eapply SILENTL; eauto. des. esplits; eauto.
    - eapply SILENTR; eauto. i. specialize (SIM0 _ _ H). des. splits; auto.
    - eapply UB; eauto.
    - eapply PROG; eauto.
  Qed.

  Definition sim: forall (RR: Z -> Z -> Prop), bool -> bool -> src.(state) -> tgt.(state) -> Prop := paco5 _sim bot5.

  Lemma sim_mon: monotone5 _sim.
  Proof.
    ii. induction IN using _sim_ind2.
    - econs 1; eauto.
    - econs 2; eauto. i. specialize (SIM _ _ H). des; eauto.
    - econs 3; eauto. des; eauto.
    - econs 4; eauto. i. specialize (SIM _ _ H). des; eauto.
    - econs 5; eauto.
    - econs 6; eauto.
  Qed.

  Lemma sim_ind (RR: Z -> Z -> Prop)
        (P: bool -> bool -> src.(state) -> tgt.(state) -> Prop)
  (TERM: forall p_src p_tgt st_src st_tgt r_src r_tgt
      (TERMS: ssort st_src = final r_src)
      (TERMT: tsort st_tgt = final r_tgt)
      (SIM: RR r_src r_tgt)
    ,
    P p_src p_tgt st_src st_tgt)
  (OBS: forall p_src p_tgt st_src0 st_tgt0
      (OBSS: ssort st_src0 = normal)
      (OBST: tsort st_tgt0 = normal)
      (SIM: forall ev st_tgt1, (tgt.(step) st_tgt0 ev st_tgt1) ->
                          (ekind ev = observableE) /\
                       exists st_src1, (src.(step) st_src0 ev st_src1) /\
                                    (sim RR true true st_src1 st_tgt1) /\ (P true true st_src1 st_tgt1))
    ,
    P p_src p_tgt st_src0 st_tgt0)
  (SILENTL: forall p_src p_tgt st_src0 st_tgt
      (SORT: ssort st_src0 = normal)
      (SIM: exists ev st_src1, (src.(step) st_src0 ev st_src1) /\
                            (ekind ev = silentE) /\
                       (sim RR true p_tgt st_src1 st_tgt) /\ (P true p_tgt st_src1 st_tgt))
    ,
    P p_src p_tgt st_src0 st_tgt)
  (SILENTR: forall p_src p_tgt st_src st_tgt0
      (SORT: tsort st_tgt0 = normal)
      (SIM: forall ev st_tgt1, (tgt.(step) st_tgt0 ev st_tgt1) ->
                          (ekind ev = silentE) /\
                       ((sim RR p_src true st_src st_tgt1) /\ (P p_src true st_src st_tgt1)))
    ,
    P p_src p_tgt st_src st_tgt0)
  (UB: forall p_src p_tgt st_src st_tgt
      (UB: ssort st_src = undef)
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
    - eapply SILENTR; eauto. i. specialize (SIM0 _ _ H). des. splits; eauto. pfold. eapply sim_mon; eauto.
    - punfold SIM. 2: apply sim_mon. eapply sim_mon; eauto. i. pclearbot. auto.
  Qed.

  Hint Constructors _sim: core.
  Hint Unfold sim: core.
  Hint Resolve sim_mon: paco.
  Hint Resolve cpn5_wcompat: paco.

  (* Upto properties. *)

  Variant sim_indC
          (sim: forall (RR: Z -> Z -> Prop), bool -> bool -> src.(state) -> tgt.(state) -> Prop)
          (RR: Z -> Z -> Prop) p_src p_tgt
    :
    src.(state) -> tgt.(state) -> Prop :=
    | sim_indC_term
        st_src st_tgt r_src r_tgt
        (TERMS: ssort st_src = final r_src)
        (TERMT: tsort st_tgt = final r_tgt)
        (SIM: RR r_src r_tgt)
      :
      sim_indC sim RR p_src p_tgt st_src st_tgt
    | sim_indC_obs
        st_src0 st_tgt0
        (OBSS: ssort st_src0 = normal)
        (OBST: tsort st_tgt0 = normal)
        (SIM: forall ev st_tgt1, (tgt.(step) st_tgt0 ev st_tgt1) ->
                            (ekind ev = observableE) /\
                         exists st_src1, (src.(step) st_src0 ev st_src1) /\
                                      (_sim sim RR true true st_src1 st_tgt1))
      :
      sim_indC sim RR p_src p_tgt st_src0 st_tgt0
    | sim_indC_silentL
        st_src0 st_tgt
        (SORT: ssort st_src0 = normal)
        (SIM: exists ev st_src1, (src.(step) st_src0 ev st_src1) /\
                              (ekind ev = silentE) /\
                         (sim RR true p_tgt st_src1 st_tgt))
      :
      sim_indC sim RR p_src p_tgt st_src0 st_tgt
    | sim_indC_silentR
        st_src st_tgt0
        (SORT: tsort st_tgt0 = normal)
        (SIM: forall ev st_tgt1, (tgt.(step) st_tgt0 ev st_tgt1) ->
                            (ekind ev = silentE) /\
                         (sim RR p_src true st_src st_tgt1))
      :
      sim_indC sim RR p_src p_tgt st_src st_tgt0
    | sim_indC_ub
        st_src st_tgt
        (UB: ssort st_src = undef)
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
    - des. econs 3; eauto. esplits; eauto.
    - econs 4; auto. i. specialize (SIM _ _ H). des. splits; eauto.
  Qed.

  Hint Resolve sim_indC_mon: paco.

  Lemma sim_indC_wrespectful: wrespectful5 _sim sim_indC.
  Proof.
    econs; eauto with paco.
    i. inv PR; eauto.
    - econs 2; eauto. i. specialize (SIM _ _ H). des. esplits; eauto. eapply sim_mon; eauto. i. eapply rclo5_base. auto.
    - econs 3; eauto. des. esplits; eauto. eapply sim_mon; eauto. i. eapply rclo5_base. auto.
    - econs 4; eauto. i. specialize (SIM _ _ H). des. splits; auto. eapply sim_mon; eauto. i. eapply rclo5_base. auto.
    - eapply sim_mon; eauto. i. eapply rclo5_base. auto.
  Qed.

  Lemma sim_indC_spec: sim_indC <6= gupaco5 _sim (cpn5 _sim).
  Proof.
    i. eapply wrespect5_uclo; eauto with paco. eapply sim_indC_wrespectful.
  Qed.

  Variant sim_progressC
          (sim: forall (RR: Z -> Z -> Prop), bool -> bool -> src.(state) -> tgt.(state) -> Prop)
          (RR: Z -> Z -> Prop)
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
    - econs 4; auto. i. specialize (SIM _ _ H). des. auto.
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

Definition simulation {l: Label} (src tgt: @STS l) := forall ps pt, sim (@eq Z) ps pt src.(init) tgt.(init).

Section ADEQ.

  Context {label: Label}.
  Context {src: @STS label}.
  Context {tgt: @STS label}.

  Lemma adequacy_spin
        (RR: Z -> Z -> Prop)
        ps pt
        (st_src: src.(state))
        (st_tgt: tgt.(state))
        (SIM: sim RR ps pt st_src st_tgt)
        (SPIN: diverge st_tgt)
    :
    diverge st_src.
  Proof.
    ginit. revert_until RR. gcofix CIH. i. revert SPIN.
    induction SIM using @sim_ind; i; clarify.
    { exfalso. punfold SPIN. inv SPIN. 1,2: rewrite SORT in TERMT; ss. }
    { exfalso. punfold SPIN. inv SPIN.
      - specialize (SIM _ _ STEP). des. rewrite SIM in KIND; inv KIND.
      - rewrite SORT in OBST; inv OBST.
    }
    { des. gstep. econs 1; eauto. gfinal. left; eauto. }
    { punfold SPIN. inv SPIN.
      - pclearbot. specialize (SIM _ _ STEP). des. apply SIM1 in DIV; auto.
      - rewrite SORT0 in SORT; ss.
    }
    { gstep. econs 2. auto. }
    { remember false in SIM at 1. remember false in SIM at 1. clear Heqb0. revert Heqb SPIN.
      induction SIM using @sim_ind; i; clarify.
      { exfalso. punfold SPIN. inv SPIN. 1,2: rewrite SORT in TERMT; ss. }
      { exfalso. punfold SPIN. inv SPIN.
        - specialize (SIM _ _ STEP). des. rewrite SIM in KIND; inv KIND.
        - rewrite SORT in OBST; inv OBST.
      }
      { des. gstep. econs 1; eauto. gfinal. left; eauto. }
      { punfold SPIN. inv SPIN.
        - pclearbot. specialize (SIM _ _ STEP). des. apply SIM1 in DIV; auto.
        - rewrite SORT0 in SORT; ss.
      }
      { gstep. econs 2. auto. }
    }
  Qed.

  Lemma adequacy_aux
        (st_src0: src.(state))
        (st_tgt0: tgt.(state))
        ps pt
        (SIM: sim eq ps pt st_src0 st_tgt0)
    :
    forall tr, (behavior st_tgt0 tr) -> (behavior st_src0 tr).
  Proof.
    revert_until tgt. ginit. gcofix CIH. i.
    move H0 before CIH. revert_until H0. induction H0 using @behavior_ind; ii.
    { generalize dependent retv. rename st into st_tgt0.
      induction SIM using @sim_ind; i; ss; clarify.
      { rewrite SORT in TERMT. inv TERMT. gstep. econs 1. auto. }
      { rewrite SORT in OBST; inv OBST. }
      { des. guclo @behavior_indC_spec. econs 4; eauto. }
      { rewrite SORT0 in SORT. inv SORT. }
      { gstep. econs 3. auto. }
      { remember false in SIM at 1. remember false in SIM at 1. clear Heqb.
        move SIM before CIH. revert_until SIM.
        induction SIM using @sim_ind; ii; ss; clarify.
        { rewrite SORT in TERMT. inv TERMT. gstep. econs 1. auto. }
        { rewrite SORT in OBST; inv OBST. }
        { des. guclo @behavior_indC_spec. econs 4; eauto. }
        { rewrite SORT0 in SORT. inv SORT. }
        { gstep. econs 3. auto. }
      }
    }
    { gstep. econs 2. eapply adequacy_spin; eauto. }
    { move SIM before CIH. revert_until SIM.
      induction SIM using @sim_ind; ii; ss; clarify.
      { rewrite SORT in TERMT; inv TERMT. }
      { rewrite SORT in OBST; inv OBST. }
      { des. guclo @behavior_indC_spec. econs 4; eauto. }
      { rewrite SORT0 in SORT; inv SORT. }
      { gstep. econs 3; auto. }
      { remember false in SIM at 1. remember false in SIM at 1. clear Heqb.
        move SIM before CIH. revert_until SIM.
        induction SIM using @sim_ind; ii; ss; clarify.
        { rewrite SORT in TERMT; inv TERMT. }
        { rewrite SORT in OBST; inv OBST. }
        { des. guclo @behavior_indC_spec. econs 4; eauto. }
        { rewrite SORT0 in SORT; inv SORT. }
        { gstep. econs 3; auto. }
      }
    }
    { move IHbehavior before CIH. move SIM before IHbehavior. revert_until SIM.
      induction SIM using @sim_ind; ii; ss; clarify.
      { rewrite SORT in TERMT; inv TERMT. }
      { specialize (SIM _ _ STEP). des. rewrite SIM in KIND; inv KIND. }
      { des. guclo @behavior_indC_spec. econs 4. 3,4: eauto. all: auto. }
      { specialize (SIM _ _ STEP). des. eapply IHbehavior; eauto. }
      { gstep. econs 3; auto. }
      { remember false in SIM at 1. remember false in SIM at 1. clear Heqb.
        move SIM before CIH. revert_until SIM.
        induction SIM using @sim_ind; ii; ss; clarify.
        { rewrite SORT in TERMT; inv TERMT. }
        { specialize (SIM _ _ STEP). des. rewrite SIM in KIND; inv KIND. }
        { des. guclo @behavior_indC_spec. econs 4. 3,4: eauto. all: auto. }
        { specialize (SIM _ _ STEP). des. eapply IHbehavior; eauto. }
        { gstep. econs 3; auto. }
      }
    }
    { move SIM before CIH. revert_until SIM.
      induction SIM using @sim_ind; ii; ss; clarify.
      { rewrite SORT in TERMT; inv TERMT. }
      { specialize (SIM _ _ STEP). des. gstep. econs 5; eauto. gfinal. left. eauto. }
      { des. guclo @behavior_indC_spec. econs 4; eauto. }
      { specialize (SIM _ _ STEP). des. rewrite SIM in KIND; inv KIND. }
      { gstep. econs 3; auto. }
      { remember false in SIM at 1. remember false in SIM at 1. clear Heqb.
        move SIM before CIH. revert_until SIM.
        induction SIM using @sim_ind; ii; ss; clarify.
        { rewrite SORT in TERMT; inv TERMT. }
        { specialize (SIM _ _ STEP). des. gstep. econs 5; eauto. gfinal. left. eauto. }
        { des. guclo @behavior_indC_spec. econs 4; eauto. }
        { specialize (SIM _ _ STEP). des. rewrite SIM in KIND; inv KIND. }
        { gstep. econs 3; auto. }
      }
    }
  Qed.

  Theorem adequacy
          (SIM: simulation src tgt)
    :
    refines tgt src.
  Proof.
    ii. eapply adequacy_aux; eauto.
    Unshelve. all: exact false.
  Qed.

End ADEQ.
