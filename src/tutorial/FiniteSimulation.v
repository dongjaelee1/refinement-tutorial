From sflib Require Import sflib.
From Paco Require Import paco.
From Tutorial Require Import Refinement.

Set Implicit Arguments.

(** Our goal in refinement-based verification is to prove the refines relation between the source and the target program.
    However, refines relation is difficult to prove directly in general.
    A standard approach is to define a relation called simulation, which simplifies the proof by enabling a *step-wise* reasoning.
    In this file, we define a *inductive* simulation, which can be used to prove refinement between programs with *finite* executions.
    To reason about programs which can possibly diverge, we need a coinductive simulation, which will be presented later.
 *)

Section SIM.

  Context {event: Event}.
  Context {sem: @STS event}.

  Notation ekind := event.(label_kind).
  Notation sort := sem.(state_sort).

  (* Inductive simulation. We only have to reason one (source or target) step at a time. *)
  Inductive sim
    :
    sem.(state) -> sem.(state) -> Prop :=
  | sim_term
      st_src st_tgt r_src r_tgt
      (TERMS: sort st_src = final r_src)
      (TERMT: sort st_tgt = final r_tgt)
      (SIM: r_src = r_tgt)
    :
    sim st_src st_tgt
  | sim_obs
      st_src0 st_tgt0
      (OBSS: sort st_src0 = normal)
      (OBST: sort st_tgt0 = normal)
      (SIM: forall ev st_tgt1,
          (sem.(step) st_tgt0 ev st_tgt1) ->
          (ekind ev = observableE) /\
          exists st_src1, (sem.(step) st_src0 ev st_src1) /\
                       (sim st_src1 st_tgt1))
    :
    sim st_src0 st_tgt0
  | sim_silentS
      st_src0 st_tgt
      (SORT: sort st_src0 = normal)
      (SIM: exists ev st_src1,
          (sem.(step) st_src0 ev st_src1) /\
            (ekind ev = silentE) /\
            (sim st_src1 st_tgt))
    :
    sim st_src0 st_tgt
  | sim_silentT
      st_src st_tgt0
      (SORT: sort st_tgt0 = normal)
      (SIM: forall ev st_tgt1,
          (sem.(step) st_tgt0 ev st_tgt1) ->
          (ekind ev = silentE) /\
          (sim st_src st_tgt1))
    :
    sim st_src st_tgt0
  (* If the source can exhibit UB, the proof is done (remember that UB is the set of all traces, thus refines any program). *)
  | sim_ub
      st_src st_tgt
      (SORT: sort st_src = undef)
    :
    sim st_src st_tgt
  .

  (* Because Coq fails to generate a correct induction lemma, we need to make one. *)
  Lemma sim_ind2
        (P: sem.(state) -> sem.(state) -> Prop)
        (TERM: forall st_src st_tgt r_src r_tgt
                 (TERMS: sort st_src = final r_src)
                 (TERMT: sort st_tgt = final r_tgt)
                 (SIM: r_src = r_tgt)
          ,
            P st_src st_tgt)
        (OBS: forall st_src0 st_tgt0
                (OBSS: sort st_src0 = normal)
                (OBST: sort st_tgt0 = normal)
                (SIM: forall ev st_tgt1,
                    (sem.(step) st_tgt0 ev st_tgt1) ->
                    (ekind ev = observableE) /\
                    exists st_src1, (sem.(step) st_src0 ev st_src1) /\
                                 (sim st_src1 st_tgt1) /\ (P st_src1 st_tgt1))
          ,
            P st_src0 st_tgt0)
        (SILENTS: forall st_src0 st_tgt
                    (SORT: sort st_src0 = normal)
                    (SIM: exists ev st_src1,
                        (sem.(step) st_src0 ev st_src1) /\
                          (ekind ev = silentE) /\
                          (sim st_src1 st_tgt) /\ (P st_src1 st_tgt))
          ,
            P st_src0 st_tgt)
        (SILENTT: forall st_src st_tgt0
                    (SORT: sort st_tgt0 = normal)
                    (SIM: forall ev st_tgt1,
                        (sem.(step) st_tgt0 ev st_tgt1) ->
                        (ekind ev = silentE) /\
                        ((sim st_src st_tgt1) /\ (P st_src st_tgt1)))
          ,
            P st_src st_tgt0)
        (UB: forall st_src st_tgt
               (UB: sort st_src = undef)
          ,
            P st_src st_tgt)
    :
    forall st_src st_tgt
      (SIM: sim st_src st_tgt),
      P st_src st_tgt.
  Proof.
    fix IH 3. i. inv SIM.
    - eapply TERM; eauto.
    - eapply OBS; eauto. i. specialize (SIM0 _ _ H). des; esplits; eauto.
    - eapply SILENTS; eauto. des; eauto. do 2 eexists. splits; eauto.
    - eapply SILENTT; eauto. i. specialize (SIM0 _ _ H). des. splits; eauto.
    - eapply UB; eauto.
  Qed.

End SIM.
#[export] Hint Constructors sim: core.

(* A complete simulation relation. *)
Definition simulation {l: Event} {sem: @STS l} (src tgt: Program sem) :=
  sim src.(init) tgt.(init).



(** Of course, we need to prove that a simulation relation is sound, which means simulation implies refinement.
    This sort of theorem is called an adequacy theorem.
    The proof itself should be helpful for building an intuition behind how simulation works, so please follow the proof.
 *)

Section ADEQ.

  Context {event: Event}.
  Context {sem: @STS event}.

  (* First prove the simulation is sound for a silent divergence case.
     In fact, this is almost trivial because our simulation only works for finite programs, which do not divergs.
     However, if the source can exhibit UB, the target can diverge because UB is the set of all trace.
   *)
  Lemma adequacy_spin
        (st_src: sem.(state))
        (st_tgt: sem.(state))
        (SIM: sim st_src st_tgt)
        (SPIN: diverge st_tgt)
    :
    diverge st_src.
  Proof.
    revert_until SIM. induction SIM using @sim_ind2; ii.
    { punfold SPIN. inv SPIN. 1,2: rewrite SORT in TERMT; ss. }
    { punfold SPIN. inv SPIN.
      - pclearbot. specialize (SIM _ _ STEP). des. rewrite SIM in KIND; inv KIND.
      - rewrite SORT in OBST; inv OBST.
    }
    { des. pfold. econs 1; eauto. left. apply SIM2. auto. }
    { punfold SPIN. inv SPIN.
      - pclearbot. specialize (SIM _ _ STEP). des. apply SIM1 in DIV; auto.
      - rewrite SORT0 in SORT; ss.
    }
    { pfold. econs 2. auto. }
  Qed.

  (* Proof for the rest of the cases is basically a proof by induction on the simulation. *)
  Lemma adequacy_aux
        (st_src0: sem.(state))
        (st_tgt0: sem.(state))
        (SIM: sim st_src0 st_tgt0)
    :
    forall tr, (behavior st_tgt0 tr) -> (behavior st_src0 tr).
  Proof.
    ginit. induction SIM using @sim_ind2; ii; clarify.
    { punfold H0. inv H0.
      all: try (rewrite SORT in TERMT; inv TERMT; fail).
      { rewrite SORT in TERMT; inv TERMT. guclo @behavior_indC_spec. econs 1; auto. }
      { punfold SPIN. inv SPIN; rewrite SORT in TERMT; inv TERMT. }
    }
    { punfold H0. inv H0.
      all: try (rewrite SORT in OBST; inv OBST; fail).
      { punfold SPIN. inv SPIN.
        - specialize (SIM _ _ STEP). des. rewrite SIM in KIND; inv KIND.
        - rewrite SORT in OBST; inv OBST.
      }
      { specialize (SIM _ _ STEP). des. rewrite SIM in KIND; inv KIND. }
      { pclearbot. specialize (SIM _ _ STEP). des.
        guclo @behavior_indC_spec. econs 5. 3,4: eauto. all: auto.
      }
    }
    { des. guclo @behavior_indC_spec. econs 4. 3,4: eauto. all: auto. }
    { punfold H0. inv H0.
      all: try (rewrite SORT0 in SORT; inv SORT; fail).
      { punfold SPIN. inv SPIN.
        { pclearbot. specialize (SIM _ _ STEP). des. gstep. econs 2. eapply adequacy_spin; eauto. }
        { rewrite SORT0 in SORT. inv SORT. }
      }
      { specialize (SIM _ _ STEP). des. eauto. }
      { specialize (SIM _ _ STEP). des. rewrite SIM in KIND; inv KIND. }
    }
    { guclo @behavior_indC_spec. econs 3. auto. }
  Qed.

  Theorem adequacy
          (src tgt: Program sem)
          (SIM: simulation src tgt)
    :
    refines src tgt.
  Proof.
    ii. eapply adequacy_aux; eauto.
  Qed.

End ADEQ.
