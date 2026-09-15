From Tutorial Require Import sflib.
From Paco Require Import paco.
From Tutorial Require Import Refinement ITreeLib.
From Stdlib Require Import Strings.String List.
From Tutorial Require Import Imp ITreeLang FiniteSimulation.
From Stdlib Require Import Logic.Eqdep.

Set Implicit Arguments.

(** Cross-STS Simulation 1: Imp source ↔ ITree target (finite simulation).

    We prove refinements where the source uses the Imp (direct) STS
    and the target uses the ITree-based STS. This demonstrates that
    the STS abstraction truly normalizes semantics — we can relate
    programs across different semantic representations.

    The key idea: define a "combined" STS using a sum type for states,
    so that the existing [sim] and [adequacy] theorem apply directly.
*)

(** ** Combined STS *)

Definition X_state := (Imp_state + ITree_state)%type.

Variant X_step : X_state -> Imp_label -> X_state -> Prop :=
  | X_step_imp s1 l s2 (STEP: Imp.step s1 l s2)
    : X_step (inl s1) l (inl s2)
  | X_step_itree t1 l t2 (STEP: ITree_step t1 l t2)
    : X_step (inr t1) l (inr t2).

Definition X_sort (st: X_state) : sort :=
  match st with
  | inl s => Imp_sort s
  | inr t => ITree_sort t
  end.

Definition X_STS (ekind: Imp_label -> kind) : @STS (Imp_Event ekind) :=
  @mk_sts (Imp_Event ekind) X_state X_step X_sort.

(** Program constructors wrapping Imp source / ITree target. *)

Definition X_Program_Mem (src: com) (tgt: com) :=
  (@mk_program _ (X_STS ekind_memory) (inl (Imp_init src)),
   @mk_program _ (X_STS ekind_memory) (inr (Mem.init, denote_program tgt))).

Definition X_Program_Ext (src: com) (tgt: com) :=
  (@mk_program _ (X_STS ekind_external) (inl (Imp_init src)),
   @mk_program _ (X_STS ekind_external) (inr (Mem.init, denote_program tgt))).


(** ** Tactics *)

Ltac norm :=
  cbn;
  repeat (try rewrite bind_trigger;
          try rewrite bind_bind; try rewrite bind_ret_l;
          try rewrite bind_tau; try rewrite bind_vis;
          cbn).

Ltac dep_subst :=
  repeat match goal with
  | [H: existT _ _ _ = existT _ _ _ |- _] =>
      apply inj_pair2 in H; try subst
  end.


Section DEMO.

  Definition src0 : com := <{ ret 0 }>.
  Definition tgt0 : com := <{ "x" := (1 + 1); "y" := (2 * 1 - "x"); ret "y" }>.

  Goal refines (fst (X_Program_Mem src0 tgt0)) (snd (X_Program_Mem src0 tgt0)).
  Proof.
    apply adequacy.
    unfold simulation, X_Program_Mem, X_STS, X_sort,
           src0, tgt0, Imp_init, denote_program. ss.
    norm.
    (* Target (ITree): tau;; tau;; Ret 0. Step through taus. *)
    econs 4; ss. i. inv H. inv STEP. ss. split; auto. norm.
    econs 4; ss. i. inv H. inv STEP. ss. split; auto. norm.
    (* Target is now Ret 0 (final 0). Source is Imp Normal (normal).
       Step source to Return 0. *)
    econs 3; ss. esplits.
    - eapply X_step_imp. eapply Step_normal. econs. econs.
    - ss.
    - econs 1; ss.
  Qed.

End DEMO.


Section EX.

  (* Ex1. External calls are observable. *)
  Definition src1 : com :=
    <{ "a" :=@ "print" <[0 : aexp]>; ret "a" }>.

  Definition tgt1 : com :=
    <{ "x" := 0; "y" :=@ "print" <["x" : aexp]>; ret "y" }>.

  Goal refines (fst (X_Program_Mem src1 tgt1)) (snd (X_Program_Mem src1 tgt1)).
  Proof.
    apply adequacy.
    unfold simulation, X_Program_Mem, X_STS, X_sort,
           src1, tgt1, Imp_init, denote_program. ss.
    norm.
    (* tgt tau: "x" := 0 *)
    econs 4; ss. i. inv H. inv STEP. ss. split; auto. norm.
    (* src: E_Seq (silent) to push continuation *)
    econs 3; ss. esplits.
    - eapply X_step_imp. eapply Step_normal. econs.
    - ss.
    - (* observable: Observe "print" [0] *)
      econs 2; ss. i. inv H. inv STEP. dep_subst.
      ss. split; auto.
      esplits.
      { eapply X_step_imp. eapply Step_normal. econs. repeat econs. }
      norm.
      (* tgt tau *)
      econs 4; ss. i. inv H. inv STEP. ss. split; auto. norm.
      (* src: E_Skip *)
      econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal. econs. }
      { ss. }
      (* src: E_Ret *)
      econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal. econs. econs. ss. }
      { ss. }
      econs 1; ss.
  Qed.


  (* Ex2. Memory observable. *)
  Definition src2 : com :=
    <{ &<1> := 5; "a" := &<1>; ret "a" }>.

  Definition tgt2 : com :=
    <{ "x" := 2; &<1> := ("x" + 3); "y" := &<1>; ret "y" }>.

  Goal refines (fst (X_Program_Mem src2 tgt2)) (snd (X_Program_Mem src2 tgt2)).
  Proof.
    apply adequacy.
    unfold simulation, X_Program_Mem, X_STS, X_sort,
           src2, tgt2, Imp_init, denote_program. ss. norm.
    (* tgt tau: "x" := 2 *)
    econs 4; ss. i. inv H. inv STEP. ss. split; auto. norm.
    (* src: E_Seq (silent) *)
    econs 3; ss. esplits.
    - eapply X_step_imp. eapply Step_normal. econs.
    - ss.
    - (* observable: MemStore 1 5 *)
      econs 2; ss. i. inv H. inv STEP. dep_subst.
      ss. split; auto.
      esplits.
      { eapply X_step_imp. eapply Step_normal. econs; econs. }
      norm.
      (* tgt tau *)
      econs 4; ss. i. inv H. inv STEP. ss. split; auto. norm.
      (* src: E_Skip, E_Seq (silent) *)
      econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal. econs. }
      { ss. }
      econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal. econs. }
      { ss. }
      (* observable: MemLoad 1 *)
      econs 2; ss. i. inv H. inv STEP. dep_subst.
      + ss. split; auto.
        esplits.
        { eapply X_step_imp. eapply Step_normal. econs. ss. }
        norm.
        (* tgt tau *)
        econs 4; ss. i. inv H. inv STEP. ss. split; auto. norm.
        (* src: E_Skip, E_Ret *)
        econs 3; ss. esplits.
        { eapply X_step_imp. eapply Step_normal. econs. }
        { ss. }
        econs 3; ss. esplits.
        { eapply X_step_imp. eapply Step_normal. econs. econs. ss. }
        { ss. }
        econs 1; ss.
      + (* load fail — contradiction *)
        ss.
  Qed.

  (* Ex2'. Memory silent (Ext semantics). *)
  Definition src2' : com :=
    <{ ret 5 }>.

  Goal refines (fst (X_Program_Ext src2' tgt2)) (snd (X_Program_Ext src2' tgt2)).
  Proof.
    apply adequacy.
    unfold simulation, X_Program_Ext, X_STS, X_sort,
           src2', tgt2, Imp_init, denote_program. ss. norm.
    (* All tgt steps are silent in Ext semantics *)
    econs 4; ss. i. inv H. inv STEP. ss. split; auto. norm.
    econs 4; ss. i. inv H. inv STEP. dep_subst. ss. split; auto. norm.
    econs 4; ss. i. inv H. inv STEP. ss. split; auto. norm.
    econs 4; ss. i. inv H. inv STEP; dep_subst; ss; split; auto; norm.
    simpl in LOAD. inv LOAD.
    econs 4; ss. i. inv H. inv STEP. ss. split; auto. norm.
    (* tgt is now Ret 5, src is Imp Normal *)
    econs 3; ss. esplits.
    - eapply X_step_imp. eapply Step_normal. econs. econs.
    - ss.
    - econs 1; ss.
  Qed.


  (* Ex3. Source UB. *)
  Definition src3 : com :=
    <{ ret "a" }>.

  Goal forall tgt,
    refines (@mk_program _ (X_STS ekind_memory) (inl (Imp_init src3)))
            (@mk_program _ (X_STS ekind_memory) (inr (Mem.init, denote_program tgt))).
  Proof.
    i. apply adequacy.
    unfold simulation, X_STS, X_sort, src3, Imp_init. ss.
    econs 3; ss. esplits.
    - eapply X_step_imp. eapply Step_undefined. intros e st' CONTRA. inv CONTRA.
      match goal with [H: aeval _ _ _ |- _] => inv H end. ss.
    - ss.
    - econs 5; ss.
  Qed.


  (* Ex4. Terminating loop. *)
  Definition src4 : com :=
    <{ ret 0 }>.

  Definition tgt4 : com :=
    <{ "x" := 100;
       while ("x")
       do ("x" := ("x" - 1))
       end;
       ret "x"
    }>.

  Goal refines (fst (X_Program_Mem src4 tgt4)) (snd (X_Program_Mem src4 tgt4)).
  Proof.
    apply adequacy.
    unfold simulation, X_Program_Mem, X_STS, X_sort,
           src4, tgt4, Imp_init, denote_program. ss. norm.
    (* tgt tau: "x" := 100 *)
    econs 4; ss. i. inv H. inv STEP. ss. split; auto.
    match goal with
    | |- sim _ (inr (_, ITree.bind (ITree.iter ?body ?init) ?k)) =>
        enough (LOOP: forall n r0, Reg.read r0 "x" = Some n ->
          @sim _ ekind_memory _ X_step X_sort
            (inl (Imp_init src4)) (inr (Mem.init, ITree.bind (ITree.iter body r0) k)))
    end.
    { eapply LOOP. ss. }
    induction n; intros r0 Hx.
    - (* n = 0: loop exits *)
      rewrite unfold_iter_eq. norm. rewrite Hx. norm.
      econs 4; ss. i. inv H. inv STEP. ss. split; auto. norm. rewrite Hx. norm.
      econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal. econs. econs. }
      { ss. }
      econs 1; ss.
    - (* n = S n: loop continues *)
      rewrite unfold_iter_eq. norm. rewrite Hx. norm.
      econs 4; ss. i. inv H. inv STEP. ss. split; auto.
      apply IHn. ss. rewrite PeanoNat.Nat.sub_0_r. ss.
  Qed.

End EX.

Section DIV.

  (* DIV1. Terminating loop with external calls. *)
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

  Goal refines (fst (X_Program_Ext src5 tgt5)) (snd (X_Program_Ext src5 tgt5)).
  Proof.
    apply adequacy.
    unfold simulation, X_Program_Ext, X_STS, X_sort,
           src5, tgt5, Imp_init, denote_program. ss. norm.
    (* tgt tau: "x" := 100 *)
    econs 4; ss. i. inv H. inv STEP. ss. split; auto.
    (* src: E_Seq, E_Asgn, E_Skip, E_Seq — step to while loop *)
    econs 3; ss. esplits.
    { eapply X_step_imp. eapply Step_normal. econs. }
    { ss. }
    econs 3; ss. esplits.
    { eapply X_step_imp. eapply Step_normal. econs. econs. }
    { ss. }
    econs 3; ss. esplits.
    { eapply X_step_imp. eapply Step_normal. econs. }
    { ss. }
    econs 3; ss. esplits.
    { eapply X_step_imp. eapply Step_normal. econs. }
    { ss. }
    norm.
    match goal with
    | |- sim (inl (_, Normal _ (CWhile ?b ?c) ?k_imp))
             (inr (_, ITree.bind (ITree.iter ?body _) ?k_itree)) =>
        enough (LOOP: forall n r, Reg.read r "x" = Some n ->
          @sim _ ekind_external _ X_step X_sort
            (inl (Mem.init, Normal r (CWhile b c) k_imp))
            (inr (Mem.init, ITree.bind (ITree.iter body r) k_itree)))
    end.
    { eapply LOOP. ss. }
    induction n; intros r0 Hx.
    - (* n = 0: loop exits *)
      rewrite unfold_iter_eq. norm. rewrite Hx. norm.
      econs 4; ss. i. inv H. inv STEP. ss. split; auto.
      (* src: E_WhileFalse, E_Skip, E_Ret *)
      econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal.
        eapply E_WhileFalse. econs. exact Hx. auto. }
      { ss. }
      econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal. econs. }
      { ss. }
      econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal. eapply E_Ret. econs. exact Hx. }
      { ss. }
      norm. rewrite Hx. norm.
      econs 1; ss.
    - (* n = S n: loop body with external call *)
      rewrite unfold_iter_eq. norm. rewrite Hx. norm.
      (* src: E_WhileTrue, E_Seq *)
      econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal.
        eapply E_WhileTrue. econs. exact Hx. ss. }
      { ss. }
      econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal. econs. }
      { ss. }
      (* observable: Observe "print" [S n] *)
      econs 2; ss. i. inv H. inv STEP. dep_subst.
      ss. split; auto.
      esplits.
      { unfold Reg.read in Hx.
        eapply X_step_imp. eapply Step_normal.
        eapply E_External. econs. eapply E_AId. exact Hx. econs. }
      unfold Reg.read in Hx. norm. rewrite Hx. norm.
      (* tgt tau *)
      econs 4; ss. i. inv H. inv STEP. ss. split; auto. norm.
      (* src: E_Skip, E_Asgn, E_Skip *)
      econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal. econs. }
      { ss. }
      econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal. eapply E_Asgn.
        econs. eapply E_AId. unfold Reg.write. ss. exact Hx. econs. }
      { ss. }
      econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal. econs. }
      { ss. }
      (* tgt tau: iter continue *)
      econs 4; ss. i. inv H. inv STEP. ss. split; auto. norm.
      apply IHn.
      unfold Reg.read, Reg.write. ss. rewrite PeanoNat.Nat.sub_0_r. ss.
  Qed.


  (* DIV2. Can't prove — may diverge. *)
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

  Goal refines (fst (X_Program_Ext src6 tgt6)) (snd (X_Program_Ext src6 tgt6)).
  Proof.
  Abort.

End DIV.
