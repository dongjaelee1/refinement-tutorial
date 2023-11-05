From sflib Require Import sflib.
From Paco Require Import paco.
From Tutorial Require Import Refinement.
From Coq Require Import Strings.String List.
From Tutorial Require Import Imp FiniteSimulation.

Set Implicit Arguments.

Section EX.
  (** We will prove that src refines tgt, using the finite simulation. *)

  Definition src0 : com := <{ ret 0 }>.

  Definition tgt0 : com := <{ "x" := (1 + 1); "y" := (2 * 1 - "x"); ret "y" }>.

  Goal refines (Imp_STS1 tgt0) (Imp_STS1 src0).
  Proof.
    apply adequacy. unfold simulation, Imp_STS1, src0, tgt0. ss. unfold Imp_init.
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

  Goal refines (Imp_STS1 tgt0) (Imp_STS1 src0).
  Proof.
    apply adequacy. unfold simulation, Imp_STS1, src0, tgt0. ss. unfold Imp_init.
    do 2 step_tgt_silents.
    inv H6. inv H4. inv H5. ss.
    do 3 step_tgt_silents.
    inv H6. inv H4. inv H5. inv H6. inv H7. inv H1. ss.
    do 2 step_tgt_silents.
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

Section EX.
  (** Prove the following refinements. *)

  (* Ex1. If a loop is guaranteed to terminate, we can prove it by induction. *)

  Definition src1 : com := <{ ret 0 }>.

  Definition tgt1 : com :=
    <{ "x" := 100;
       while ("x")
       do ("x" := ("x" - 1))
       end;
       ret "x"
    }>.

  Goal refines (Imp_STS1 tgt1) (Imp_STS1 src1).
  Proof.
  Admitted.

  (* Ex2. Interactions with the external world is observable, so should be preserved. *)

  Definition src2 : com := <{ "a" :=@ "print" <[0 : aexp]>; ret "a" }>.

  Definition tgt2 : com :=
    <{ "x" := 0; "y" :=@ "print" <["x" : aexp]>; ret "y" }>.

  Goal refines (Imp_STS1 tgt2) (Imp_STS1 src2).
  Proof.
  Admitted.

  (* Ex3. If semantics is given by Imp_STS1, memory accesses are also observable. *)
  Definition src3 : com := <{ &<1> := 5; "a" := &<1>; ret "a" }>.

  Definition tgt3 : com :=
    <{ "x" := 2; &<1> := ("x" + 3); "y" := &<1>; ret "y" }>.

  Goal refines (Imp_STS1 tgt3) (Imp_STS1 src3).
  Proof.
  Admitted.

  (* But, if we want to reason about compiler optimizations for example,
     we do not want to keep memory accesses visible.
     Imp_STS2 is the right semantics for this. 
   *)
  Definition src3' : com := <{ ret 5 }>.

  Goal refines (Imp_STS2 tgt3) (Imp_STS2 src3').
  Proof.
  Admitted.

End EX.

Section DIV.
  (** Simulation in current form can't prove refinement between possibly diverging programs. *)

  (* Ex4. We can prove the following refinement, which always terminates. *)

  Definition src4 : com :=
    <{ "x" := 100;
       while ("x")
       do ("a" :=@ "print" <["x" : aexp]>;
           "x" := ("x" - 1))
       end;
       ret "x"
    }>.

  Definition tgt4 : com :=
    <{ "x" := 100;
       while ("x")
       do ("a" :=@ "print" <["x" : aexp]>;
           "x" := ("x" - 1))
       end;
       ret "x"
    }>.

  Goal refines (Imp_STS2 tgt4) (Imp_STS2 src4).
  Proof.
  Admitted.

  (* Ex5. However, we can't prove the following refinement, because it can diverge.
     Also note that even though src5 and tgt5 are the same programs 
     (thus trivially refines each other), our simulation relation is too weak to prove this.
     Compare this with Ex1 and Ex4.
   *)

  Definition src5 : com :=
    <{ "x" := 100;
       while ("x")
       do ("x" := AAny)
       end;
       ret "x"
    }>.

  Definition tgt5 : com :=
    <{ "x" := 100;
       while ("x")
       do ("x" := AAny)
       end;
       ret "x"
    }>.

  Goal refines (Imp_STS2 tgt5) (Imp_STS2 src5).
  Proof.
    (* We can't prove this right now. *)
  Abort.

End DIV.

Section SIM.
  (** We will define a simulation relation that can work with diverging programs.
      These simulations are called 'termination sensitive' or 'termination preserving'.
   *)

  (* Our first attempt. *)


End SIM.
