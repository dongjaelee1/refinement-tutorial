From Tutorial Require Import sflib.
From Paco Require Import paco.
From Tutorial Require Import Refinement ITreeLib.
From Stdlib Require Import Strings.String List.
From Tutorial Require Import Imp ITreeLang FiniteSimulation.
From Stdlib Require Import Logic.Eqdep.

Set Implicit Arguments.

(** Example 4: ITree version of Example 1.
    We prove the same refinements as in Example1.v,
    but using the ITree-based semantics from ITreeLang.v. *)

(** Normalization tactic for ITree goals.
    [cbn] + repeated rewriting of bind laws and trigger. *)
Ltac norm :=
  cbn;
  repeat (try rewrite bind_trigger;
          try rewrite bind_bind; try rewrite bind_ret_l;
          try rewrite bind_tau; try rewrite bind_vis;
          cbn).

(** Handle dependent equality from [inv] on Vis steps.
    When inverting an [ITree_step] on a [Vis] node, Coq produces
    a [sigT] equality that needs [inj_pair2] (axiom K) to resolve. *)
Ltac dep_subst :=
  repeat match goal with
  | [H: existT _ _ _ = existT _ _ _ |- _] =>
      apply inj_pair2 in H; try subst
  end.


Section DEMO.

  Definition src0 : com := <{ ret 0 }>.
  Definition tgt0 : com := <{ "x" := (1 + 1); "y" := (2 * 1 - "x"); ret "y" }>.

  Goal refines (ITree_Program_Mem src0) (ITree_Program_Mem tgt0).
  Proof.
    apply adequacy.
    unfold simulation, ITree_Program_Mem, ITree_STS_Mem, ITree_STS, src0, tgt0, denote_program.
    norm.
    (* tgt = tau;; tau;; Ret 0, src = Ret 0 *)
    econs 4. { ss. }
    ss. i. inv H. ss. split; auto. norm.
    econs 4. { ss. }
    ss. i. inv H. ss. split; auto. norm.
    econs 1; ss.
  Qed.

End DEMO.

Section EX.

  (* Ex1. External calls are observable. *)
  Definition src1 : com :=
    <{ "a" :=@ "print" <[0 : aexp]>; ret "a" }>.

  Definition tgt1 : com :=
    <{ "x" := 0; "y" :=@ "print" <["x" : aexp]>; ret "y" }>.

  Goal refines (ITree_Program_Mem src1) (ITree_Program_Mem tgt1).
  Proof.
    apply adequacy.
    unfold simulation, ITree_Program_Mem, ITree_STS_Mem, ITree_STS, src1, tgt1, denote_program.
    norm.
    (* tgt = tau;; vis (Observe "print" [0]) ..., src = vis (Observe "print" [0]) ... *)
    econs 4; ss.
    i. inv H. ss. split; auto.
    (* Both have vis (Observe "print" [0]) at head — observable step *)
    econs 2; ss.
    i. inv H. dep_subst.
    ss. split; auto.
    esplits.
    { eapply ITree_step_observe. }
    norm.
    (* sim (Mem.init, tau;; Ret retv) (Mem.init, tau;; Ret retv) *)
    econs 4; ss.
    i. inv H. ss. split; auto.
    econs 3; ss. esplits.
    - econs.
    - ss.
    - econs 1; ss.
  Qed.


  (* Ex2. If semantics is given by ITree_STS_Mem, memory accesses are also observable. *)
  Definition src2 : com :=
    <{ &<1> := 5; "a" := &<1>; ret "a" }>.

  Definition tgt2 : com :=
    <{ "x" := 2; &<1> := ("x" + 3); "y" := &<1>; ret "y" }>.

  Goal refines (ITree_Program_Mem src2) (ITree_Program_Mem tgt2).
  Proof.
    apply adequacy.
    unfold simulation, ITree_Program_Mem, ITree_STS_Mem, ITree_STS, src2, tgt2, denote_program.
    norm.
    econs 4; ss. i. inv H. ss. split; auto. norm.
    econs 2; ss. i. inv H. dep_subst.
    ss. split; auto.
    eexists. split.
    { eapply ITree_step_store. }
    norm.
    econs 4; ss. i. inv H. ss. split; auto. norm.
    econs 3; ss. esplits.
    - econs.
    - ss.
    - norm.
      econs 2; ss. i. inv H. dep_subst.
      + ss. split; auto.
        eexists. split.
        { eapply ITree_step_load. ss. }
        norm.
        econs 4; ss. i. inv H. ss. split; auto. norm.
        econs 3; ss. esplits.
        * econs.
        * ss.
        * norm. econs 1; ss.
      + ss.
  Qed.

  (* Ex2'. With ITree_STS_Ext, memory accesses are silent. *)
  Definition src2' : com :=
    <{ ret 5 }>.

  Goal refines (ITree_Program_Ext src2') (ITree_Program_Ext tgt2).
  Proof.
    apply adequacy.
    unfold simulation, ITree_Program_Ext, ITree_STS_Ext, ITree_STS, src2', tgt2, denote_program.
    norm.
    econs 4; ss. i. inv H. ss. split; auto. norm.
    econs 4; ss. i. inv H. dep_subst. ss. split; auto. norm.
    econs 4; ss. i. inv H. ss. split; auto. norm.
    econs 4; ss. i. inv H; dep_subst; ss; split; auto; norm.
    simpl in LOAD. inv LOAD.
    econs 4; ss. i. inv H. ss. split; auto. norm.
    econs 1; ss.
  Qed.


  (* Ex3. If the source can exhibit UB, refinement always holds. *)
  Definition src3 : com :=
    <{ ret "a" }>.

  Goal forall tgt, refines (ITree_Program_Mem src3) (ITree_Program_Mem tgt).
  Proof.
    i. apply adequacy.
    unfold simulation, ITree_Program_Mem, ITree_STS_Mem, ITree_STS, src3, denote_program.
    norm.
    econs 5. ss.
  Qed.


  (* Ex4. If a loop always terminates, we can prove it by induction. *)
  Definition src4 : com :=
    <{ ret 0 }>.

  Definition tgt4 : com :=
    <{ "x" := 100;
       while ("x")
       do ("x" := ("x" - 1))
       end;
       ret "x"
    }>.

  Goal refines (ITree_Program_Mem src4) (ITree_Program_Mem tgt4).
  Proof.
    apply adequacy.
    unfold simulation, ITree_Program_Mem, ITree_STS_Mem, ITree_STS, src4, tgt4, denote_program.
    norm.
    econs 4; ss. i. inv H. ss. split; auto.
    match goal with
    | |- sim _ (_, ITree.bind (ITree.iter ?body ?init) ?k) =>
        enough (LOOP: forall n r0, Reg.read r0 "x" = Some n ->
          @sim _ ekind_memory _ ITree_step ITree_sort
            (Mem.init, Ret 0) (Mem.init, ITree.bind (ITree.iter body r0) k))
    end.
    { eapply LOOP. ss. }
    induction n; intros r0 Hx.
    - rewrite unfold_iter_eq. norm. rewrite Hx. norm.
      econs 4; ss. i. inv H. ss. split; auto. norm. rewrite Hx. norm.
      econs 1; ss.
    - rewrite unfold_iter_eq. norm. rewrite Hx. norm.
      econs 4; ss. i. inv H. ss. split; auto.
      apply IHn. ss. rewrite PeanoNat.Nat.sub_0_r. ss.
  Qed.

End EX.

Section DIV.

  (* DIV1. We can prove the following refinement, which always terminates. *)
  Definition src5 : com :=
    <{ "x" := 100;
       while ("x")
       do ("a" :=@ "print" <["x" : aexp]>;
           "x" := ("x" - 1))
       end;
       ret "x"
    }>.

  Definition tgt5 : com :=
    <{ "x" := 100;
       while ("x")
       do ("a" :=@ "print" <["x" : aexp]>;
           "x" := ("x" - 1))
       end;
       ret "x"
    }>.

  Goal refines (ITree_Program_Ext src5) (ITree_Program_Ext tgt5).
  Proof.
    apply adequacy.
    unfold simulation, ITree_Program_Ext, ITree_STS_Ext, ITree_STS, src5, tgt5, denote_program.
    norm.
    (* Initial tau: step tgt then src *)
    econs 4; ss. i. inv H. ss. split; auto.
    econs 3; ss. esplits.
    - econs.
    - ss.
    - norm.
      match goal with
      | |- sim (_, ITree.bind (ITree.iter ?body ?init) ?k)
               (_, ITree.bind (ITree.iter ?body' ?init') ?k') =>
          enough (LOOP: forall n r0, Reg.read r0 "x" = Some n ->
            @sim _ ekind_external _ ITree_step ITree_sort
              (Mem.init, ITree.bind (ITree.iter body r0) k)
              (Mem.init, ITree.bind (ITree.iter body' r0) k'))
      end.
      { eapply LOOP. ss. }
      induction n; intros r0 Hx.
      + (* n = 0: loop exits *)
        rewrite !unfold_iter_eq. norm. rewrite Hx. norm.
        econs 4; ss. i. inv H. ss. split; auto.
        econs 3; ss. esplits.
        * econs.
        * ss.
        * norm. rewrite Hx. norm.
          econs 1; ss.
      + (* n = S n: loop body with external call *)
        rewrite !unfold_iter_eq. norm. rewrite Hx. norm.
        (* observable: Observe "print" [S n] *)
        econs 2; ss. i. inv H. dep_subst.
        ss. split; auto.
        esplits.
        { eapply ITree_step_observe. }
        (* After observe, Reg.read was unfolded by cbn, fix Hx *)
        unfold Reg.read in Hx. norm. rewrite Hx. norm.
        (* step both through tau *)
        econs 4; ss. i. inv H. ss. split; auto.
        econs 3; ss. esplits.
        * econs.
        * ss.
        * norm.
          (* step both through another tau *)
          econs 4; ss. i. inv H. ss. split; auto.
          econs 3; ss. esplits.
          { econs. }
          { ss. }
          norm.
          apply IHn.
          unfold Reg.read, Reg.write. ss.
          rewrite PeanoNat.Nat.sub_0_r. ss.
  Qed.


  (* DIV2. We can't prove the following refinement because it can diverge. 
    See Example1.v's DIV2. *)
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

  Goal refines (ITree_Program_Ext src6) (ITree_Program_Ext tgt6).
  Proof.
  (* We can't prove this right now. Try to prove using induction, and see where it fails. *)
  Abort.

End DIV.
