From Tutorial Require Import sflib.
From Paco Require Import paco.
From Tutorial Require Import Refinement ITreeLib.
From Stdlib Require Import Strings.String List.
From Tutorial Require Import Imp ITreeLang Simulation.
From Stdlib Require Import Logic.Eqdep.

Set Implicit Arguments.

(** Example 5: ITree version of Example 3.
    Infinite simulation with coinduction, applied to ITree semantics.
    We use the sound simulation from Simulation.v (with progress flags)
    to handle potentially diverging programs. *)

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

  (** DIV2. Prove by coinduction.
      Both source and target are the same nondeterministic program.
      Unlike Example4's DIV1, this loop may diverge (AAny can always return nonzero),
      so we need coinductive simulation, not finite induction. *)

  Definition src6 : com :=
    <{ "x" := 100;
       while ("x")
       do ("x" := AAny)
       end;
       ret "x"
    }>.

  Definition tgt6 : com := src6.

  Goal refines (ITree_Program_Ext src6) (ITree_Program_Ext tgt6).
  Proof.
    apply adequacy.
    unfold simulation, ITree_Program_Ext, ITree_STS_Ext, ITree_STS, src6, tgt6, denote_program.
    norm. intros.
    ginit.
    (* tgt tau: "x" := 100 *)
    guclo @sim_indC_spec. econs 4; ss.
    i. inv H. ss. split; auto.
    (* src tau: "x" := 100 *)
    guclo @sim_indC_spec. econs 3; ss.
    esplits.
    - econs.
    - ss.
    - (* Both sides at while loop iter. Set up coinduction. *)
      (* Generalize the register state for coinduction. *)
      clear ps pt.
      match goal with
      | |- gpaco4 _ _ _ _ _ _
             (_, ITree.bind (ITree.iter _ ?init) _) _ =>
          remember init as r0 eqn:Heqr0; clear Heqr0
      end.
      pose proof true as ps. pose proof true as pt.
      guclo @sim_progressC_spec. econs.
      instantiate (1:=pt). instantiate (1:=ps). 2,3: ss.
      revert r0 ps pt. gcofix CIH. i.
      rewrite !unfold_iter_eq. norm.
      (* Case split on register lookup *)
      destruct (Reg.read r0 "x") as [n|] eqn:Hx.
      2: { (* None: both sides hit UB (Vis Undefined) *)
           guclo @sim_indC_spec. econs 5. ss. }
      destruct n.
      + (* n = 0: loop exits *)
        norm.
        guclo @sim_indC_spec. econs 4; ss.
        i. inv H. ss. split; auto.
        guclo @sim_indC_spec. econs 3; ss.
        esplits. econs. ss.
        norm. rewrite Hx. norm.
        gstep. econs; ss.
      + (* n = S n: loop continues with Choose *)
        norm.
        (* Both sides: Vis (Choose nat) ... — tgt Choose (silent) *)
        guclo @sim_indC_spec. econs 4; ss.
        i. inv H. dep_subst. ss. split; auto.
        norm.
        (* src Choose: pick same value x *)
        guclo @sim_indC_spec. econs 3; ss.
        esplits. eapply ITree_step_choose. ss.
        norm.
        (* Both sides: tau;; iter body (Reg.write r0 "x" x) >>= k *)
        (* tgt tau *)
        guclo @sim_indC_spec. econs 4; ss.
        i. inv H. ss. split; auto.
        (* src tau *)
        guclo @sim_indC_spec. econs 3; ss.
        esplits. econs. ss.
        norm.
        (* Back at loop start with updated register. Apply coinductive hypothesis. *)
        gstep. eapply sim_progress. 2,3: auto.
        gfinal. left. eapply CIH.
  Qed.


  (** EX1. The src terminates, but the tgt diverges.
      This cannot be proven — the simulation correctly rejects infinite stuttering. *)
  Definition src1 : com :=
    <{ ret 0 }>.

  Definition tgt1 : com :=
    <{ while (1)
       do skip
       end;
       ret 1
    }>.

  Goal refines (ITree_Program_Ext src1) (ITree_Program_Ext tgt1).
  Proof.
  Abort.

End EX.


Section EXOPT.
  (** Code optimizations — same examples as Example3.v, using ITree semantics. *)

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

  Goal refines (ITree_Program_Ext src_opt1) (ITree_Program_Ext tgt_opt1).
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

  Goal refines (ITree_Program_Ext src_opt2) (ITree_Program_Ext tgt_opt2).
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

  Goal refines (ITree_Program_Ext src_opt3) (ITree_Program_Ext tgt_opt3).
  Proof.
  Admitted.

End EXOPT.
