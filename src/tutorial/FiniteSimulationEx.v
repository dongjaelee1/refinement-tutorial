From sflib Require Import sflib.
From Paco Require Import paco.
From Tutorial Require Import Refinement.
From Coq Require Import Strings.String List.
From Tutorial Require Import Imp FiniteSimulation.

Set Implicit Arguments.

Section EX.

  Definition src : com := <{ ret 0 }>.

  Definition tgt : com := <{ "x" := (1 + 1); "y" := (2 * 1 - "x"); ret "y" }>.

  Goal refines (Imp_STS1 tgt) (Imp_STS1 src).
  Proof.
    apply adequacy. unfold simulation, Imp_STS1, src, tgt. ss. unfold Imp_init.
    (* Same as 'econstructor 4.' or 'eapply sim_silentT.' *)
    econs 4.
    { ss. }
    ss. i. inv H. ss. split; auto.
    econs 4.
    { ss. }
    ss. i. inv H. ss. split; auto.
    inv H7. inv H4. inv H5. ss.
    econs 4.
    { ss. }
    ss. i. inv H. ss. split; auto.
    econs 4.
    { ss. }
    ss. i. inv H. ss. split; auto.
    econs 4.
    { ss. }
    ss. i. inv H. ss. split; auto.
    inv H7. inv H4. inv H5. inv H6. inv H7. inv H1. ss.
    econs 4.
    { ss. }
    ss. i. inv H. ss. split; auto.
    (* Now evaluate return commands. 
       When both src and tgt needs to progress, usually taking tgt step first is better;
       we are usually proving 'forall tgt event, exists src event'.
     *)
    econs 4.
    { ss. }
    ss. i. inv H. ss. split; auto.
    inv H6. inv H1.
    econs 3.
    { ss. }
    ss. exists (inr LInternal). eexists. split.
    { econs. econs.
      (* Coq detects correct constructors for this: 'eapply E_Ret. eapply E_ANum.'. *)
    }
    ss. split; auto.
    (* There is only one possible constructor for this: 'sim_term'. *)
    econs.
    { simpl. eauto. }
    { simpl. eauto. }
    { auto. }
  Qed.

  (* Simulation proofs can be very length, as you can see from this simple example.
     Thus one usually define a tactic that automatically take care of trivial steps.
     Our examples will be simple enough, so you can define yours if you need.
     Note that a tactic defined inside a section can only be used in that section in general.
   *)

  Ltac step_tgt_silents :=
    try (econs 4; [ss | ss; intros ev st_tgt1 STEP; inv STEP; ss; split; auto]).

  Goal refines (Imp_STS1 tgt) (Imp_STS1 src).
  Proof.
    apply adequacy. unfold simulation, Imp_STS1, src, tgt. ss. unfold Imp_init.
    step_tgt_silents.
    step_tgt_silents.
    inv H6. inv H4. inv H5. ss.
    step_tgt_silents.
    step_tgt_silents.
    step_tgt_silents.
    inv H6. inv H4. inv H5. inv H6. inv H7. inv H1. ss.
    step_tgt_silents.
    step_tgt_silents.
    inv H5. inv H1.
    econs 3.
    { ss. }
    ss. exists (inr LInternal). eexists. split.
    { econs. econs. }
    ss. split; auto.
    econs.
    { simpl. eauto. }
    { simpl. eauto. }
    { auto. }
  Qed.

End EX.
