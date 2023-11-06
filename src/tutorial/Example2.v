From sflib Require Import sflib.
From Paco Require Import paco.
From Tutorial Require Import Refinement.

Set Implicit Arguments.

Section SIM.
  (** We will define a simulation relation that covers diverging programs.
      This kind of simulations are called 'termination sensitive' or 'termination preserving'.
      A correct definition involves coinduction and some nontrivial details.
      So before we get to that, let us examine a *wrong* definition first 
      and practice coinductive proofs.
   *)

  Context {event: Event}.
  Context {sem: @STS event}.

  Notation ekind := event.(label_kind).
  Notation sort := sem.(state_sort).

  (* This definition is almost the same as 'sim' defined in FiniteSimulation.v, 
     but it is a coinductive definition, not an inductive one.
   *)
  Variant _sim
          (sim: forall (RR: Z -> Z -> Prop), sem.(state) -> sem.(state) -> Prop)
          (RR: Z -> Z -> Prop)
    :
    sem.(state) -> sem.(state) -> Prop :=
    | sim_term
        st_src st_tgt r_src r_tgt
        (TERMS: sort st_src = final r_src)
        (TERMT: sort st_tgt = final r_tgt)
        (SIM: RR r_src r_tgt)
      :
      _sim sim RR st_src st_tgt
    | sim_obs
        st_src0 st_tgt0
        (OBSS: sort st_src0 = normal)
        (OBST: sort st_tgt0 = normal)
        (SIM: forall ev st_tgt1,
            (sem.(step) st_tgt0 ev st_tgt1) ->
            (ekind ev = observableE) /\
              exists st_src1, (sem.(step) st_src0 ev st_src1) /\
                           (sim RR st_src1 st_tgt1))
      :
      _sim sim RR st_src0 st_tgt0
    | sim_silentS
        st_src0 st_tgt
        (SORT: sort st_src0 = normal)
        (SIM: exists ev st_src1,
            (sem.(step) st_src0 ev st_src1) /\
              (ekind ev = silentE) /\
              (sim RR st_src1 st_tgt))
      :
      _sim sim RR st_src0 st_tgt
    | sim_silentR
        st_src st_tgt0
        (SORT: sort st_tgt0 = normal)
        (SIM: forall ev st_tgt1,
            (sem.(step) st_tgt0 ev st_tgt1) ->
            (ekind ev = silentE) /\
              (sim RR st_src st_tgt1))
      :
      _sim sim RR st_src st_tgt0
    | sim_ub
        st_src st_tgt
        (SORT: sort st_src = undef)
      :
      _sim sim RR st_src st_tgt.

  Definition sim: forall (RR: Z -> Z -> Prop), sem.(state) -> sem.(state) -> Prop := paco3 _sim bot3.

  Lemma sim_mon: monotone3 _sim.
  Proof.
    ii. inv IN.
    - econs 1; eauto.
    - econs 2; eauto. i. specialize (SIM _ _ H). des; eauto.
    - econs 3; eauto. des; eauto. esplits; eauto.
    - econs 4; eauto. i. specialize (SIM _ _ H). des; eauto.
    - econs 5; eauto.
  Qed.

End SIM.
#[local] Hint Constructors _sim: core.
#[local] Hint Unfold sim: core.
#[local] Hint Resolve sim_mon: paco.
#[local] Hint Resolve cpn3_wcompat: paco.

Definition simulation {l: Event} {sem: @STS l} (src tgt: Program sem) :=
  sim (@eq Z) src.(init) tgt.(init).

From Coq Require Import Strings.String List.
From Tutorial Require Import Imp.

Section EX.
  (** Assuming that the above coinductive simulation is correct (i.e. adequacy theorem holds), 
      we can prove refinement between possibly diverging programs. 
   *)

  Hypothesis adequacy: forall {l: Event} {sem: @STS l} (src tgt: Program sem),
      simulation src tgt -> refines tgt src.

  (* DIV2. Now we can prove the previous example, by coinduction. *)
  Definition src6 : com :=
    <{ "x" := 100;
       while ("x")
       do ("x" := AAny)
       end;
       ret "x"
    }>.

  Definition tgt6 : com :=
    <{ "x" := 100;
       while ("x")
       do ("x" := AAny)
       end;
       ret "x"
    }>.

  (* Solves tgt undef case if tgt is not undef. *)
  Ltac solve_tgt_ub := 
    exfalso;
    match goal with
    | [UNDEF : forall _ _, ~ (ceval _ _ _) |- _] => eapply UNDEF
    end;
    repeat econs.

  (* Makes a tgt step. *)
  Ltac step_tgt_silent0 :=
    match goal with
    | [STEP: ceval _ _ _ |- _] => inv STEP
    end;
    ss; split; auto.

  (* Combines above two tactics. *)
  Ltac step_tgt_silent :=
    try (pfold; econs 4;
         [ss
         | ss; intros ev st_tgt1 STEP0; inv STEP0;
           [step_tgt_silent0; left | solve_tgt_ub]
        ]).

  (* Makes a src silent step. *)
  Ltac step_src_silent :=
    try (pfold; econs 3;
         [ss
         | ss; exists (inr LInternal); eexists; splits; ss; [repeat econs | left]
        ]).

  Goal refines (Imp_Program2 src6) (Imp_Program2 tgt6).
  Proof.
    apply adequacy. unfold simulation, Imp_Program2, Imp_STS2, src6, tgt6, Imp_init. ss.
    (* We can use paco tactics to proceed. *)
    pfold. econs 4. ss.
    ss. i. inv H. 2: solve_tgt_ub. step_tgt_silent0. left.
    (* Of course, we can make a tactic for this. *)
    step_tgt_silent. inv H6. step_tgt_silent. step_tgt_silent.
    (* The target reached a while loop. We take the source side to the loop too. *)
    do 4 step_src_silent.
    (* Now we start a coinductive proof. We first set up a coinductive hypothesis. *)
    remember Reg.init as reg. clear Heqreg.
    remember 100 as n. clear Heqn.
    revert reg n. pcofix CIH. i.
    (* Then make progress. *)
    step_tgt_silent.
    - (* False case; loop terminates. *)
      clear CIH.
      inv H6. inv H1.
      do 2 step_src_silent.
      do 2 step_tgt_silent.
      inv H5. inv H1.
      do 1 step_src_silent.
      pfold. econs; ss.
    - (* True case; loops. *)
      rename H7 into TRUE. inv H6. inv H1.
      step_tgt_silent.
      inv H6.
      step_tgt_silent.
      (* Tactic 'step_src_silent' picks wrong constructor, so we prove manually. *)
      pfold. econs 3; ss. do 2 eexists. splits.
      { econs 1. eapply E_WhileTrue. repeat econs. auto. }
      { ss. }
      left.
      (* AAny introduces nondeterminism. We picks what we need when AAny is in the src. *)
      pfold. econs 3; ss. do 2 eexists. splits.
      { econs 1. eapply E_Asgn. eapply (E_Any _ n). }
      { ss. }
      left.
      (* Now we came back to the start of the while loop. We can end the proof by coinduction. *)
      pfold. econs 3; ss. do 2 eexists. splits.
      { repeat econs. }
      { ss. }
      right. eapply CIH.
      Unshelve. exact 0.
    - (* Leftover undef case. *)
      exfalso. destruct (Z.eqb n 0) eqn:CASES.
      + eapply UNDEF. eapply E_WhileFalse. repeat econs. apply Z.eqb_eq; auto.
      + eapply UNDEF. eapply E_WhileTrue. repeat econs. apply Z.eqb_neq; auto.
  Qed.


  (** However, this simulation is *unsound*, and you can prove refinements that shouldn't hold.
      In other words, the adequacy theorem does not hold.
      Before we define a correct coinductive simulation, here are some counterexamples.
   *)

  (* CEX1. The src terminates, but the tgt diverges. Prove this by coinduction. *)
  Definition src1 : com := <{ ret 0 }>.

  Definition tgt1 : com :=
    <{ while (1)
       do skip
       end;
       ret 1
    }>.

  Goal refines (Imp_Program2 src1) (Imp_Program2 tgt1).
  Proof.
  Admitted.


  (* CEX2. The other way around. Prove this by coinduction. *)
  Goal refines (Imp_Program2 tgt1) (Imp_Program2 src1).
  Proof.
  Admitted.

  (** These counterexamples show that we need a mechanism to prevent *infinite stuttering*.
      Stuttering in simulation means that only one side (src or tgt) makes progress,
      while the other side stutters at the same state.
      Stuttering is an essential feature that allows scalable verifications.
      Therefore, a correct and useful simulation should allow stuttering, but only finite times.
   *)

End EX.
