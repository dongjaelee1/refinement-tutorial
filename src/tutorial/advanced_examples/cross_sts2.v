From Tutorial Require Import sflib.
From Paco Require Import paco.
From Tutorial Require Import Refinement ITreeLib.
From Stdlib Require Import Strings.String List.
From Tutorial Require Import Imp ITreeLang Simulation.
From Stdlib Require Import Logic.Eqdep.

Set Implicit Arguments.

(** Cross-STS Simulation 2: Imp source ↔ ITree target (coinductive simulation).
    Infinite simulation with coinduction, where source uses Imp STS
    and target uses ITree STS. Extends cross_sts1 with coinductive reasoning. *)

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

Definition X_Program_Ext (src tgt: com) :=
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


Section EX.

  (** DIV2. Prove by coinduction (cross-STS version).
      Source is Imp, target is ITree. Both run the same nondeterministic program.
      The loop may diverge, so we need coinductive simulation. *)

  Definition src6 : com :=
    <{ "x" := 100;
       while ("x")
       do ("x" := AAny)
       end;
       ret "x"
    }>.

  Definition tgt6 : com := src6.

  Goal refines (fst (X_Program_Ext src6 tgt6)) (snd (X_Program_Ext src6 tgt6)).
  Proof.
    apply adequacy.
    unfold simulation, X_Program_Ext, X_STS, X_sort,
           src6, tgt6, Imp_init, denote_program. ss.
    norm. intros.
    ginit.
    (* tgt tau: "x" := 100 *)
    guclo @sim_indC_spec. econs 4; ss.
    i. inv H. inv STEP. ss. split; auto.
    (* src: E_Seq, E_Asgn, E_Skip, E_Seq — step to while loop *)
    guclo @sim_indC_spec. econs 3; ss. esplits.
    { eapply X_step_imp. eapply Step_normal. econs. }
    { ss. }
    guclo @sim_indC_spec. econs 3; ss. esplits.
    { eapply X_step_imp. eapply Step_normal. econs. econs. }
    { ss. }
    guclo @sim_indC_spec. econs 3; ss. esplits.
    { eapply X_step_imp. eapply Step_normal. econs. }
    { ss. }
    guclo @sim_indC_spec. econs 3; ss. esplits.
    { eapply X_step_imp. eapply Step_normal. econs. }
    { ss. }
    norm.
    (* Set up coinduction. Generalize the register and ITree iter state. *)
    clear ps pt.
    match goal with
    | |- gpaco4 _ _ _ _ _ _
           (inl (_, Normal ?r (CWhile ?b ?c) ?k_imp))
           (inr (_, ITree.bind (ITree.iter _ ?init) _)) =>
        remember r as r0 eqn:Heqr0; clear Heqr0
    end.
    pose proof true as ps. pose proof true as pt.
    guclo @sim_progressC_spec. econs.
    instantiate (1:=pt). instantiate (1:=ps). 2,3: ss.
    revert r0 ps pt. gcofix CIH. i.
    rewrite !unfold_iter_eq. norm.
    (* Case split on register lookup *)
    destruct (Reg.read r0 "x") as [n|] eqn:Hx.
    2: { (* None: source UB — uninitialized variable *)
         guclo @sim_indC_spec. econs 3; ss. esplits.
         { eapply X_step_imp. eapply Step_undefined.
           intros e st' CONTRA. inv CONTRA;
             match goal with [H: aeval _ _ _ |- _] => inv H end;
             unfold Reg.read in Hx; congruence. }
         { ss. }
         guclo @sim_indC_spec. econs 5. ss. }
    destruct n.
    + (* n = 0: loop exits *)
      norm.
      (* tgt tau: loop exit *)
      guclo @sim_indC_spec. econs 4; ss.
      i. inv H. inv STEP. ss. split; auto.
      (* src: E_WhileFalse, E_Skip, E_Ret *)
      guclo @sim_indC_spec. econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal.
        eapply E_WhileFalse. econs. exact Hx. auto. }
      { ss. }
      guclo @sim_indC_spec. econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal. econs. }
      { ss. }
      guclo @sim_indC_spec. econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal. eapply E_Ret. econs. exact Hx. }
      { ss. }
      norm. rewrite Hx. norm.
      gstep. econs; ss.
    + (* n = S n: loop continues with Choose *)
      norm.
      (* tgt Choose (silent in Ext) *)
      guclo @sim_indC_spec. econs 4; ss.
      i. inv H. inv STEP. dep_subst. ss. split; auto.
      norm.
      (* src: E_WhileTrue, E_Asgn(AAny picks same value), E_Skip *)
      guclo @sim_indC_spec. econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal.
        eapply E_WhileTrue. econs. exact Hx. ss. }
      { ss. }
      guclo @sim_indC_spec. econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal.
        eapply E_Asgn. eapply (E_AAny _ x). }
      { ss. }
      guclo @sim_indC_spec. econs 3; ss. esplits.
      { eapply X_step_imp. eapply Step_normal. econs. }
      { ss. }
      (* tgt tau *)
      guclo @sim_indC_spec. econs 4; ss.
      i. inv H. inv STEP. ss. split; auto.
      norm.
      (* Back at loop start. Apply coinductive hypothesis. *)
      gstep. eapply sim_progress. 2,3: auto.
      gfinal. left. eapply CIH.
  Qed.


  (** EX1. The src terminates, but the tgt diverges.
      Cannot be proven — simulation rejects infinite stuttering. *)
  Definition src1 : com :=
    <{ ret 0 }>.

  Definition tgt1 : com :=
    <{ while (1)
       do skip
       end;
       ret 1
    }>.

  Goal refines (fst (X_Program_Ext src1 tgt1)) (snd (X_Program_Ext src1 tgt1)).
  Proof.
  Abort.

End EX.


Section EXOPT.
  (** Code optimizations — same examples as Example3.v, cross-STS version. *)

  (* OPT1. Store-to-load forwarding. *)
  Definition src_opt1 : com :=
    <{ "c" :=@ "scan" <[]>;
       &<1> := "c";
       "x" := &<1>;
       while ("x")
       do ("x" :=@ "scan" <[]>;
           "a" :=@ "print" <["x" : aexp]>;
           "x" := &<1>)
       end;
       ret 0
    }>.

  Definition tgt_opt1 : com :=
    <{ "c" :=@ "scan" <[]>;
       &<1> := "c";
       "x" := "c";
       while ("x")
       do ("x" :=@ "scan" <[]>;
           "a" :=@ "print" <["x" : aexp]>;
           "x" := "c")
       end;
       ret 0
    }>.

  Goal refines (fst (X_Program_Ext src_opt1 tgt_opt1)) (snd (X_Program_Ext src_opt1 tgt_opt1)).
  Proof.
  Admitted.

  (* OPT2. Load-to-load forwarding. *)
  Definition src_opt2 : com :=
    <{ "a" :=@ "scan" <[]>;
       &<1> := "a";
       "c" := &<1>;
       "x" := &<1>;
       while ("x")
       do ("x" :=@ "scan" <[]>;
           "a" :=@ "print" <["x" : aexp]>;
           "x" := &<1>)
       end;
       ret 0
    }>.

  Definition tgt_opt2 : com :=
    <{ "a" :=@ "scan" <[]>;
       &<1> := "a";
       "c" := &<1>;
       "x" := "c";
       while ("x")
       do ("x" :=@ "scan" <[]>;
           "a" :=@ "print" <["x" : aexp]>;
           "x" := "c")
       end;
       ret 0
    }>.

  Goal refines (fst (X_Program_Ext src_opt2 tgt_opt2)) (snd (X_Program_Ext src_opt2 tgt_opt2)).
  Proof.
  Admitted.

  (* OPT3. Loop invariant code motion. *)
  Definition src_opt3 : com :=
    <{ &<1> := 1;
       while (1)
       do ("x" :=@ "scan" <[]>;
           "a" := &<1>;
           "x" := "x" + "a";
           "a" :=@ "print" <["x" : aexp]>)
       end;
       ret 0
    }>.

  Definition tgt_opt3 : com :=
    <{ &<1> := 1;
       "c" := &<1>;
       while (1)
       do ("x" :=@ "scan" <[]>;
           "a" := "c";
           "x" := "x" + "a";
           "a" :=@ "print" <["x" : aexp]>)
       end;
       ret 0
    }>.

  Goal refines (fst (X_Program_Ext src_opt3 tgt_opt3)) (snd (X_Program_Ext src_opt3 tgt_opt3)).
  Proof.
  Admitted.

End EXOPT.
