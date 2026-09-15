From Tutorial Require Import sflib.
From Paco Require Import paco.
From Tutorial Require Import Refinement ITreeLib.
From Stdlib Require Import Strings.String List.
From Tutorial Require Import Imp ITreeLang Simulation.
From Stdlib Require Import Logic.Eqdep Lia Arith.Wf_nat Logic.Classical.

Set Implicit Arguments.

(** * Memory Handler Refinement

    We prove a general refinement theorem: for any Imp program [c],
    the ITree semantics with memory handled (memE interpreted away)
    refines the Imp small-step semantics with memory-silent labels.

    - Source: ITree with [handle_mem] applied (only [progE] events remain)
    - Target: Imp with memory operations labeled as [inr LInternal]

    This demonstrates that the denotational (ITree) and operational (Imp)
    semantics agree on observable behavior for all programs.
*)



(** ** 1. Memory-silent Imp step relation *)

(** We define a variant of [ceval] where [E_MemLoad] and [E_MemStore]
    use the label [inr LInternal] instead of [inl (Mem.LLoad ...)] / [inl (Mem.LStore ...)]. *)

Inductive ceval_silent : Imp_state -> Imp_label -> Imp_state -> Prop :=
| ES_Skip : forall m r c k,
    ceval_silent (m, Normal r CSkip (Kseq c k)) (inr LInternal) (m, Normal r c k)
| ES_Asgn : forall m r x a k n,
    aeval r a n ->
    ceval_silent (m, Normal r (CAsgn x a) k) (inr LInternal) (m, Normal (Reg.write r x n) CSkip k)
| ES_Seq : forall m r c1 c2 k,
    ceval_silent (m, Normal r (CSeq c1 c2) k) (inr LInternal) (m, Normal r c1 (Kseq c2 k))
| ES_IfTrue : forall m r b c1 c2 k n,
    aeval r b n ->
    n <> 0 ->
    ceval_silent (m, Normal r (CIf b c1 c2) k) (inr LInternal) (m, Normal r c1 k)
| ES_IfFalse : forall m r b c1 c2 k n,
    aeval r b n ->
    n = 0 ->
    ceval_silent (m, Normal r (CIf b c1 c2) k) (inr LInternal) (m, Normal r c2 k)
| ES_WhileFalse : forall m r b c k n,
    aeval r b n ->
    n = 0 ->
    ceval_silent (m, Normal r (CWhile b c) k) (inr LInternal) (m, Normal r CSkip k)
| ES_WhileTrue : forall m r b c k n,
    aeval r b n ->
    n <> 0 ->
    ceval_silent (m, Normal r (CWhile b c) k) (inr LInternal) (m, Normal r c (Kseq (CWhile b c) k))
| ES_Ret : forall m r a k retv,
    aeval r a retv ->
    ceval_silent (m, Normal r (CRet a) k) (inr LInternal) (m, Return retv)
(** Memory operations now have silent labels: *)
| ES_MemLoad : forall m r x loc k v,
    Mem.load m loc = Some v ->
    ceval_silent (m, Normal r (CMemLoad x loc) k) (inr LInternal) (m, Normal (Reg.write r x v) CSkip k)
| ES_MemStore : forall m r loc a k v m',
    aeval r a v ->
    Mem.store m loc v = m' ->
    ceval_silent (m, Normal r (CMemStore loc a) k) (inr LInternal) (m', Normal r CSkip k)
| ES_External : forall m r x name eargs k vargs retv,
    Forall2 (aeval r) eargs vargs ->
    ceval_silent (m, Normal r (CExternal x name eargs) k) (inr (LExternal name vargs retv)) (m, Normal (Reg.write r x retv) CSkip k)
.

(** The memory-silent [step] wraps [ceval_silent] with undefined-step handling. *)
Variant step_silent : Imp_state -> Imp_label -> Imp_state -> Prop :=
  | Step_silent_normal
      st e st'
      (STEP: ceval_silent st e st')
    :
    step_silent st e st'
  | Step_silent_undefined
      m lst
      (UNDEF: forall e st', ~ (ceval_silent (m, lst) e st'))
    :
    step_silent (m, lst) (inr LInternal) (m, Undef).

(** The memory-silent Imp STS uses [ekind_external] since all labels
    are now either [inr LInternal] or [inr (LExternal ...)]. *)
Definition Imp_STS_Silent : STS :=
  mk_sts (Imp_Event ekind_external) step_silent Imp_sort.

Definition Imp_Program_Silent (c: com) : Program Imp_STS_Silent :=
  mk_program Imp_STS_Silent (Imp_init c).



(** ** 2. Memory handler on the ITree side *)

(** [handle_memE] interprets [memE] events using [Mem.t] state. *)
Definition handle_memE : forall T, memE T -> Mem.t -> itree progE (Mem.t * T) :=
  fun _ e m =>
    match e with
    | MemLoad loc => Ret (m, Mem.load m loc)
    | MemStore loc v => Ret (Mem.store m loc v, tt)
    end.

(** [handle_Es] interprets the combined event type [Es = progE +' memE]:
    - [progE] events are re-triggered (passed through)
    - [memE] events are handled using [handle_memE] *)
Definition handle_Es : forall T, Es T -> Mem.t -> itree progE (Mem.t * T) :=
  fun T e m =>
    match e with
    | inl1 pe => v <- trigger pe;; Ret (m, v)
    | inr1 me => handle_memE me m
    end.

(** [handle_mem] interprets away all [memE] events in an ITree,
    threading [Mem.t] state through the computation.
    Result: [itree progE (Mem.t * R)] — memory folded into the return value. *)
Definition handle_mem {R} (t: itree Es R) (m: Mem.t) : itree progE (Mem.t * R) :=
  interp_state handle_Es t m.



(** ** 3. Continuation denotation *)

(** [denote_cont k] denotes an Imp continuation [k] as an ITree function.
    Given a result from a command ([inl r'] for normal completion, [inr v] for return),
    it produces the ITree for the remaining computation. *)
Fixpoint denote_cont (k: cont) : (Reg.t + nat) -> itree Es nat :=
  match k with
  | Kstop => fun res =>
      match res with
      | inl _ => vd <- trigger Undefined;; match vd : void with end
      | inr v => Ret v
      end
  | Kseq c k' => fun res =>
      match res with
      | inl r' => tau;; res' <- denote_com c r';; denote_cont k' res'
      | inr v => Ret v
      end
  end.

(** Key property: [denote_program] equals [denote_com] composed with [denote_cont Kstop]. *)
Lemma denote_program_cont c :
  denote_program c = res <- denote_com c Reg.init;; denote_cont Kstop res.
Proof. unfold denote_program. reflexivity. Qed.



(** ** 4. Handled ITree STS *)

(** After [handle_mem], the state is just [itree progE (Mem.t * nat)].
    Memory is folded into the return value. *)
Definition Handled_state := itree progE (Mem.t * nat).

(** Sort for handled ITree states. *)
Definition Handled_sort (t: Handled_state) : sort :=
  match observe t with
  | RetF (_, v) => final v
  | VisF Undefined _ => undef
  | _ => normal
  end.

(** Step relation for handled ITree states. *)
Inductive silent_star : Handled_state -> Handled_state -> Prop :=
  | ss_refl s : silent_star s s
  | ss_tau t s (STAR: silent_star t s) : silent_star (tau;; t) s
  | ss_choose X (x: X) (k: X -> Handled_state) s (STAR: silent_star (k x) s) :
    silent_star (Vis (Choose X) k) s.

Variant Handled_step : Handled_state -> Imp_label -> Handled_state -> Prop :=
  | HS_tau t:
    Handled_step (tau;; t) (inr LInternal) t
  | HS_choose X (x: X) (k: X -> Handled_state):
    Handled_step (Vis (Choose X) k) (inr LInternal) (k x)
  | HS_observe fn args retv (k: nat -> Handled_state):
    Handled_step (Vis (Observe fn args) k) (inr (LExternal fn args retv)) (k retv)
  | HS_observe_catch_up fn args retv (t: Handled_state) (k: nat -> Handled_state):
    silent_star t (Vis (Observe fn args) k) ->
    Handled_step t (inr (LExternal fn args retv)) (k retv).

(** The handled ITree STS. *)
Definition Handled_STS : STS :=
  mk_sts (Imp_Event ekind_external) Handled_step Handled_sort.

Definition Handled_Program (c: com) : Program Handled_STS :=
  mk_program Handled_STS (handle_mem (denote_program c) Mem.init).



(** ** 5. Combined STS *)

(** To use the simulation framework, we define a combined STS
    with states from both sides. *)

Definition X_state := (Handled_state + Imp_state)%type.

Variant X_step : X_state -> Imp_label -> X_state -> Prop :=
  | X_step_handled t1 l t2 (STEP: Handled_step t1 l t2)
    : X_step (inl t1) l (inl t2)
  | X_step_imp s1 l s2 (STEP: step_silent s1 l s2)
    : X_step (inr s1) l (inr s2).

Definition X_sort (st: X_state) : sort :=
  match st with
  | inl t => Handled_sort t
  | inr s => Imp_sort s
  end.

Definition X_STS : @STS (Imp_Event ekind_external) :=
  @mk_sts (Imp_Event ekind_external) X_state X_step X_sort.

Definition X_Program (c: com) :=
  (@mk_program _ X_STS (inl (handle_mem (denote_program c) Mem.init)),
   @mk_program _ X_STS (inr (Imp_init c))).



(** ** 6. Helper lemmas about [handle_mem] *)

(** These follow from [interp_state] lemmas in ITreeLib.v. *)

Lemma handle_mem_ret : forall R (r: R) m,
  handle_mem (Ret r) m = Ret (m, r).
Proof. intros. unfold handle_mem. rewrite interp_state_ret. reflexivity. Qed.

Lemma handle_mem_tau : forall R (t: itree Es R) m,
  handle_mem (tau;; t) m = tau;; handle_mem t m.
Proof. intros. unfold handle_mem. rewrite interp_state_tau. reflexivity. Qed.

Lemma handle_mem_bind : forall R S (t: itree Es R) (k: R -> itree Es S) m,
  handle_mem (x <- t;; k x) m =
  st <- handle_mem t m;; handle_mem (k (snd st)) (fst st).
Proof. intros. unfold handle_mem. rewrite interp_state_bind. reflexivity. Qed.

Lemma handle_mem_choose : forall X m,
  handle_mem (trigger (Choose X) : itree Es X) m =
  x <- trigger (Choose X);; tau;; Ret (m, x).
Proof.
  intros. unfold handle_mem.
  rewrite interp_state_trigger. cbn. rewrite bind_bind.
  f. f_equiv. intros x. rewrite bind_ret_l. reflexivity.
Qed.

Lemma handle_mem_observe : forall fn args m,
  handle_mem (trigger (Observe fn args) : itree Es nat) m =
  retv <- trigger (Observe fn args);; tau;; Ret (m, retv).
Proof.
  intros. unfold handle_mem.
  rewrite interp_state_trigger. cbn. rewrite bind_bind.
  f. f_equiv. intros x. rewrite bind_ret_l. reflexivity.
Qed.

Lemma handle_mem_undefined : forall m,
  handle_mem (trigger Undefined : itree Es void) m =
  vd <- trigger Undefined;; tau;; Ret (m, vd).
Proof.
  intros. unfold handle_mem.
  rewrite interp_state_trigger. cbn. rewrite bind_bind.
  f. f_equiv. intros x. rewrite bind_ret_l. reflexivity.
Qed.

Lemma handle_mem_load : forall loc m,
  handle_mem (trigger (MemLoad loc) : itree Es (option nat)) m =
  tau;; Ret (m, Mem.load m loc).
Proof.
  intros. unfold handle_mem.
  rewrite interp_state_trigger. cbn. rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma handle_mem_store : forall loc v m,
  handle_mem (trigger (MemStore loc v) : itree Es unit) m =
  tau;; Ret (Mem.store m loc v, tt).
Proof.
  intros. unfold handle_mem.
  rewrite interp_state_trigger. cbn. rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma fold_handle_mem : forall R (t: itree Es R) m,
  interp_state handle_Es t m = handle_mem t m.
Proof. reflexivity. Qed.

Lemma handle_mem_memload_bind : forall loc m R (k: option nat -> itree Es R),
  handle_mem (ov <- trigger (MemLoad loc);; k ov) m =
  tau;; handle_mem (k (Mem.load m loc)) m.
Proof.
  intros. rewrite handle_mem_bind. rewrite handle_mem_load.
  rewrite bind_tau. rewrite bind_ret_l. cbn. reflexivity.
Qed.

Lemma handle_mem_observe_bind : forall fn args m R (k: nat -> itree Es R),
  handle_mem (retv <- trigger (Observe fn args);; k retv) m =
  retv <- trigger (Observe fn args);; tau;; handle_mem (k retv) m.
Proof.
  intros. rewrite handle_mem_bind. rewrite handle_mem_observe.
  rewrite bind_bind. f. f_equiv. intros x.
  rewrite bind_tau. rewrite bind_ret_l. cbn. reflexivity.
Qed.

Lemma handle_mem_memstore_bind : forall loc v m R (k: unit -> itree Es R),
  handle_mem (trigger (MemStore loc v) ;;; k tt) m =
  tau;; handle_mem (k tt) (Mem.store m loc v).
Proof.
  intros. rewrite handle_mem_bind. rewrite handle_mem_store.
  rewrite bind_tau. rewrite bind_ret_l. cbn. reflexivity.
Qed.



(** ** 7. Key structural lemmas *)

(** Return values pass through any continuation unchanged. *)
Lemma denote_cont_ret : forall k v,
  denote_cont k (inr v) = Ret v.
Proof. destruct k; reflexivity. Qed.

(** The denotation of [CSeq c1 c2] with continuation [k] equals
    the denotation of [c1] with continuation [Kseq c2 k]. *)
Lemma denote_seq_cont : forall c1 c2 r k,
  (res <- denote_com (CSeq c1 c2) r;; denote_cont k res) =
  (res <- denote_com c1 r;; denote_cont (Kseq c2 k) res).
Proof.
  intros. cbn. rewrite bind_bind. f. f_equiv. intros [r' | v].
  - rewrite bind_tau. reflexivity.
  - rewrite bind_ret_l. rewrite denote_cont_ret. reflexivity.
Qed.



(** ** 8. Simulation invariant and main theorem *)

(** The simulation invariant relates handled ITree states to Imp states.
    For a normal state [(m, Normal r c k)], the ITree state is
    [handle_mem (denote_com c r >>= denote_cont k) m]. *)

Ltac norm :=
  cbn;
  repeat (try rewrite bind_trigger;
          try rewrite bind_bind; try rewrite bind_ret_l;
          try rewrite bind_tau; try rewrite bind_vis;
          try rewrite handle_mem_ret;
          try rewrite handle_mem_tau;
          try rewrite handle_mem_bind;
          try rewrite handle_mem_choose;
          try rewrite handle_mem_observe;
          try rewrite handle_mem_undefined;
          try rewrite handle_mem_load;
          try rewrite handle_mem_store;
          cbn).

Ltac dep_subst :=
  repeat match goal with
  | [H: existT _ _ _ = existT _ _ _ |- _] =>
      apply inj_pair2 in H; try subst
  end.

(** Bind-level lemma: [handle_mem] with Choose trigger in bind position. *)
Lemma handle_mem_choose_bind :
  forall m R (k: nat -> itree Es R),
    handle_mem (v <- (trigger (Choose nat) : itree Es nat);; k v) m =
    x <- trigger (Choose nat);; tau;; handle_mem (k x) m.
Proof.
  intros.
  rewrite handle_mem_bind. rewrite handle_mem_choose.
  rewrite bind_bind.
  f. f_equiv. intros x.
  rewrite bind_tau. rewrite bind_ret_l. cbn.
  reflexivity.
Qed.

(** Helper: [aeval] and [denote_aexp] agree up to simulation.
    If [aeval r a n], then for any continuation [k],
    [handle_mem (v <- denote_aexp a r;; k v) m] can silently step to
    [handle_mem (k n) m] on the source side of the simulation.

    The quantification over [ps] is needed because source-side steps
    (sim_silentS) set the progress flag to [true]. *)
Lemma aeval_handle_sim :
  forall a r n, aeval r a n ->
  forall m (k: nat -> itree Es nat) pt (st_tgt: X_state),
    (forall ps, @sim _ ekind_external _ X_step X_sort
         ps pt (inl (handle_mem (k n) m)) st_tgt) ->
    forall ps, @sim _ ekind_external _ X_step X_sort
         ps pt (inl (handle_mem (v <- denote_aexp a r;; k v) m)) st_tgt.
Proof.
  induction 1; intros m k0 pt st_tgt CONT ps.
  - (* E_AAny: nondeterministic choice *)
    cbn. rewrite handle_mem_choose_bind. rewrite bind_trigger.
    pfold. econs 3.
    { ss. }
    esplits.
    { eapply X_step_handled. eapply HS_choose with (x := n). }
    { ss. }
    econs 3.
    { ss. }
    esplits.
    { eapply X_step_handled. eapply HS_tau. }
    { ss. }
    specialize (CONT true). punfold CONT.
  - (* E_ANum: immediate *)
    cbn. rewrite bind_ret_l. apply CONT.
  - (* E_AId: register lookup *)
    cbn. unfold Reg.read.
    match goal with [H: _ _ = Some _ |- _] => rewrite H end.
    rewrite bind_ret_l. apply CONT.
  - (* E_ABinOp: recursive *)
    cbn. rewrite bind_bind.
    eapply IHaeval1. intros ps'.
    cbn. rewrite bind_bind.
    (* After IHaeval1, continuation is: fun v2 => v <- Ret (f n1 v2);; k0 v
       Simplify: v <- Ret x;; k0 v = k0 x *)
    match goal with
    | |- context [handle_mem ?t _] =>
        replace t with (v2 <- denote_aexp a2 r;; k0 (bin_op_eval op n1 v2));
        [| f; f_equiv; intros v2; rewrite bind_ret_l; reflexivity]
    end.
    eapply IHaeval2. exact CONT.
Qed.

(** Version of [aeval_handle_sim] for [_sim], usable inside [gcofix] contexts.
    The key difference: works with any [sim_r] (including gpaco's accumulator),
    not just [paco4 _sim bot4]. *)
Lemma aeval_handle_sim' :
  forall a r n, aeval r a n ->
  forall sim_r m (k: nat -> itree Es nat) pt (st_tgt: X_state),
    (forall ps, @_sim _ ekind_external _ X_step X_sort sim_r
         ps pt (inl (handle_mem (k n) m)) st_tgt) ->
    forall ps, @_sim _ ekind_external _ X_step X_sort sim_r
         ps pt (inl (handle_mem (v <- denote_aexp a r;; k v) m)) st_tgt.
Proof.
  induction 1; intros sim_r m k0 pt st_tgt CONT ps.
  - (* E_AAny: nondeterministic choice *)
    cbn. rewrite handle_mem_choose_bind. rewrite bind_trigger.
    econs 3.
    { ss. }
    esplits.
    { eapply X_step_handled. eapply HS_choose with (x := n). }
    { ss. }
    econs 3.
    { ss. }
    esplits.
    { eapply X_step_handled. eapply HS_tau. }
    { ss. }
    apply CONT.
  - (* E_ANum: immediate *)
    cbn. rewrite bind_ret_l. apply CONT.
  - (* E_AId: register lookup *)
    cbn. unfold Reg.read.
    match goal with [H: _ _ = Some _ |- _] => rewrite H end.
    rewrite bind_ret_l. apply CONT.
  - (* E_ABinOp: recursive *)
    cbn. rewrite bind_bind.
    eapply IHaeval1. intros ps'.
    cbn. rewrite bind_bind.
    match goal with
    | |- context [handle_mem ?t _] =>
        replace t with (v2 <- denote_aexp a2 r;; k0 (bin_op_eval op n1 v2));
        [| f; f_equiv; intros v2; rewrite bind_ret_l; reflexivity]
    end.
    eapply IHaeval2. exact CONT.
Qed.

(** Similarly for [aeval_list_handle_sim]. *)
Lemma aeval_list_handle_sim' :
  forall es r vs, Forall2 (aeval r) es vs ->
  forall sim_r m (k: list nat -> itree Es nat) pt (st_tgt: X_state),
    (forall ps, @_sim _ ekind_external _ X_step X_sort sim_r
         ps pt (inl (handle_mem (k vs) m)) st_tgt) ->
    forall ps, @_sim _ ekind_external _ X_step X_sort sim_r
         ps pt (inl (handle_mem (vargs <- denote_aexps es r;; k vargs) m)) st_tgt.
Proof.
  induction 1; intros sim_r m k0 pt st_tgt CONT ps.
  - (* nil *) cbn. rewrite bind_ret_l. apply CONT.
  - (* cons *)
    cbn. rewrite bind_bind.
    eapply aeval_handle_sim'; eauto. intros ps'.
    rewrite bind_bind.
    eapply IHForall2. intros ps''.
    rewrite bind_ret_l. apply CONT.
Qed.

(** gpaco-level version: works inside [gcofix] contexts. *)
Lemma aeval_handle_gpaco :
  forall a r n, aeval r a n ->
  forall rr m (k: nat -> itree Es nat) pt (st_tgt: X_state),
    (forall ps, gpaco4 (@_sim _ ekind_external _ X_step X_sort)
           (cpn4 (@_sim _ ekind_external _ X_step X_sort)) bot4 rr
           ps pt (inl (handle_mem (k n) m)) st_tgt) ->
    forall ps, gpaco4 (@_sim _ ekind_external _ X_step X_sort)
           (cpn4 (@_sim _ ekind_external _ X_step X_sort)) bot4 rr
           ps pt (inl (handle_mem (v <- denote_aexp a r;; k v) m)) st_tgt.
Proof.
  induction 1; intros rr m k0 pt st_tgt CONT ps.
  - (* E_AAny *)
    cbn. rewrite handle_mem_choose_bind. rewrite bind_trigger.
    guclo @sim_indC_spec. econs 3; ss. esplits.
    { eapply X_step_handled. eapply HS_choose with (x := n). }
    { ss. }
    guclo @sim_indC_spec. econs 3; ss. esplits.
    { eapply X_step_handled. eapply HS_tau. }
    { ss. }
    apply CONT.
  - (* E_ANum *)
    cbn. rewrite bind_ret_l. apply CONT.
  - (* E_AId *)
    cbn. unfold Reg.read.
    match goal with [H: _ _ = Some _ |- _] => rewrite H end.
    rewrite bind_ret_l. apply CONT.
  - (* E_ABinOp *)
    cbn. rewrite bind_bind.
    eapply IHaeval1. intros ps'.
    rewrite bind_bind.
    match goal with
    | |- context [handle_mem ?t _] =>
        replace t with (v2 <- denote_aexp a2 r;; k0 (bin_op_eval op n1 v2));
        [| f; f_equiv; intros v2; rewrite bind_ret_l; reflexivity]
    end.
    eapply IHaeval2. exact CONT.
Qed.

(** gpaco-level version for argument lists. *)
Lemma aeval_list_handle_gpaco :
  forall es r vs, Forall2 (aeval r) es vs ->
  forall rr m (k: list nat -> itree Es nat) pt (st_tgt: X_state),
    (forall ps, gpaco4 (@_sim _ ekind_external _ X_step X_sort)
           (cpn4 (@_sim _ ekind_external _ X_step X_sort)) bot4 rr
           ps pt (inl (handle_mem (k vs) m)) st_tgt) ->
    forall ps, gpaco4 (@_sim _ ekind_external _ X_step X_sort)
           (cpn4 (@_sim _ ekind_external _ X_step X_sort)) bot4 rr
           ps pt (inl (handle_mem (vargs <- denote_aexps es r;; k vargs) m)) st_tgt.
Proof.
  induction 1; intros rr m k0 pt st_tgt CONT ps.
  - cbn. rewrite bind_ret_l. apply CONT.
  - cbn. rewrite bind_bind.
    eapply aeval_handle_gpaco; eauto. intros ps'.
    rewrite bind_bind.
    eapply IHForall2. intros ps''.
    rewrite bind_ret_l. apply CONT.
Qed.

(** Solution E: gpaco version that resets flags to [false false] in the continuation.
    This way, [CIH] (which is polymorphic in ps/pt) can be applied directly
    without needing [sim_progress] and its [ps = true] requirement. *)
Lemma aeval_handle_gpaco_reset :
  forall a r n, aeval r a n ->
  forall rr m (k: nat -> itree Es nat) (st_tgt: X_state),
    gpaco4 (@_sim _ ekind_external _ X_step X_sort)
           (cpn4 (@_sim _ ekind_external _ X_step X_sort)) bot4 rr
           false false (inl (handle_mem (k n) m)) st_tgt ->
    forall ps pt,
    gpaco4 (@_sim _ ekind_external _ X_step X_sort)
           (cpn4 (@_sim _ ekind_external _ X_step X_sort)) bot4 rr
           ps pt (inl (handle_mem (v <- denote_aexp a r;; k v) m)) st_tgt.
Proof.
  intros.
  guclo @sim_progressC_spec. eapply sim_progressC_intro with (ps1:=false) (pt1:=false); ss.
  eapply aeval_handle_gpaco; eauto. intros ps'.
  guclo @sim_progressC_spec. eapply sim_progressC_intro with (ps1:=false) (pt1:=false); ss.
Qed.

Lemma aeval_list_handle_gpaco_reset :
  forall es r vs, Forall2 (aeval r) es vs ->
  forall rr m (k: list nat -> itree Es nat) (st_tgt: X_state),
    gpaco4 (@_sim _ ekind_external _ X_step X_sort)
           (cpn4 (@_sim _ ekind_external _ X_step X_sort)) bot4 rr
           false false (inl (handle_mem (k vs) m)) st_tgt ->
    forall ps pt,
    gpaco4 (@_sim _ ekind_external _ X_step X_sort)
           (cpn4 (@_sim _ ekind_external _ X_step X_sort)) bot4 rr
           ps pt (inl (handle_mem (vargs <- denote_aexps es r;; k vargs) m)) st_tgt.
Proof.
  intros.
  guclo @sim_progressC_spec. eapply sim_progressC_intro with (ps1:=false) (pt1:=false); ss.
  eapply aeval_list_handle_gpaco; eauto. intros ps'.
  guclo @sim_progressC_spec. eapply sim_progressC_intro with (ps1:=false) (pt1:=false); ss.
Qed.

(** Helper: Forall2 aeval agrees with denote_aexps. *)
Lemma aeval_list_handle_sim :
  forall es r vs, Forall2 (aeval r) es vs ->
  forall m (k: list nat -> itree Es nat) pt (st_tgt: X_state),
    (forall ps, @sim _ ekind_external _ X_step X_sort
         ps pt (inl (handle_mem (k vs) m)) st_tgt) ->
    forall ps, @sim _ ekind_external _ X_step X_sort
         ps pt (inl (handle_mem (vargs <- denote_aexps es r;; k vargs) m)) st_tgt.
Proof.
  induction 1; intros m k0 pt st_tgt CONT ps.
  - (* nil *) cbn. rewrite bind_ret_l. apply CONT.
  - (* cons *)
    cbn. rewrite bind_bind.
    eapply aeval_handle_sim; eauto. intros ps'.
    rewrite bind_bind.
    eapply IHForall2. intros ps''.
    rewrite bind_ret_l. apply CONT.
Qed.

(** Helper: the sort of a handled ITree [Vis Undefined _] is [undef]. *)
Lemma handled_sort_undefined :
  forall (k: void -> Handled_state),
    Handled_sort (Vis Undefined k) = undef.
Proof. reflexivity. Qed.

(** Helper: after handling [trigger Undefined >>= ...], the state is [Vis Undefined ...]. *)
Lemma handle_mem_undefined_bind :
  forall m R (k: void -> itree Es R),
    handle_mem (vd <- trigger Undefined;; k vd) m =
    vd <- trigger Undefined;; tau;; handle_mem (k vd) m.
Proof.
  intros. rewrite handle_mem_bind. rewrite handle_mem_undefined.
  rewrite bind_bind. f. f_equiv. intros x.
  rewrite bind_tau. rewrite bind_ret_l. cbn. reflexivity.
Qed.

(** The key simulation lemma: relates handled ITree states to Imp states.
    This is the core of the proof, proceeding by coinduction for [CWhile]
    and case analysis on the command for everything else.

    The invariant is:
    - Source: [handle_mem (res <- denote_com c r;; denote_cont k res) m]
    - Target: [(m, Normal r c k)] *)

(** Helper: if no [aeval] holds, then handle_mem of the expression
    reaches UB on the source side. *)
Lemma no_aeval_sim :
  forall a reg, (forall n, ~ aeval reg a n) ->
  forall sim_r m (k: nat -> itree Es nat) ps pt,
    @_sim _ ekind_external _ X_step X_sort sim_r ps pt
      (inl (handle_mem (v <- denote_aexp a reg;; k v) m))
      (inr (m, Undef)).
Proof.
  induction a; intros reg NOEVAL sim_r m k ps pt.
  - exfalso. eapply (NOEVAL 0). econs.
  - exfalso. eapply (NOEVAL n). econs.
  - cbn. destruct (Reg.read reg x) eqn:Hx.
    + exfalso. eapply (NOEVAL n). econs. unfold Reg.read in Hx. auto.
    + norm. econs 5. ss.
  - cbn. rewrite bind_bind.
    destruct (classic (exists n1, aeval reg a1 n1)) as [[n1 Hae1] | Hnae1].
    + eapply aeval_handle_sim'. exact Hae1. intros ps'.
      rewrite bind_bind.
      eapply IHa2. intros n2 Hae2.
      eapply (NOEVAL (bin_op_eval op n1 n2)). econs; eauto.
    + eapply IHa1. intros n1 Hae1. apply Hnae1. eauto.
Qed.

Lemma no_aeval_list_sim :
  forall es reg, (~ exists vs, Forall2 (aeval reg) es vs) ->
  forall sim_r m (k: list nat -> itree Es nat) ps pt,
    @_sim _ ekind_external _ X_step X_sort sim_r ps pt
      (inl (handle_mem (vs <- denote_aexps es reg;; k vs) m))
      (inr (m, Undef)).
Proof.
  induction es; intros reg NOEVAL sim_r m k ps pt.
  - exfalso. apply NOEVAL. exists nil. econs.
  - cbn. rewrite bind_bind.
    destruct (classic (exists n, aeval reg a n)) as [[n Hae] | Hnae].
    + eapply aeval_handle_sim'. exact Hae. intros ps'.
      rewrite bind_bind.
      eapply IHes. intros [vs Hvs]. apply NOEVAL. exists (n :: vs). econs; eauto.
    + eapply no_aeval_sim. intros n Hae. apply Hnae. eauto.
Qed.

Local Notation sim := (@sim _ ekind_external _ X_step X_sort).
Local Notation _sim := (@_sim _ ekind_external _ X_step X_sort).

(** Helper: embed [r] into [gpaco4 ... (bot4 \4/ r) r] inside [_sim].
    After [gstep], [sim_progress] needs its SIM subgoal at [gpaco4 ... (bot4 \4/ r) r].
    [CIH] lives in [r]. This lemma bridges the gap. *)
Lemma apply_CIH (rr: bool -> bool -> X_state -> X_state -> Prop)
    (ps pt: bool) (st_src st_tgt: X_state) :
  rr ps pt st_src st_tgt ->
  gpaco4 (@Simulation._sim _ ekind_external _ X_step X_sort)
         (cpn4 (@Simulation._sim _ ekind_external _ X_step X_sort))
         (bot4 \4/ rr) rr ps pt st_src st_tgt.
Proof. intro. eapply gpaco4_base. auto. Qed.

(** Command size measure for well-founded induction (handles CSeq chains). *)
Fixpoint com_size (c: com) : nat :=
  match c with
  | CSeq c1 c2 => 1 + com_size c1 + com_size c2
  | CIf _ c1 c2 => 1 + com_size c1 + com_size c2
  | CWhile _ c => 1 + com_size c
  | _ => 1
  end.

(** ** 9. Catch-up observation closure *)

(** [silent_star] implies a chain of [Handled_step] with silent labels. *)
Lemma silent_star_trans : forall s1 s2 s3,
  silent_star s1 s2 -> silent_star s2 s3 -> silent_star s1 s3.
Proof. induction 1; intros; eauto using ss_tau, ss_choose. Qed.

Lemma silent_star_sort_normal : forall s1 s2,
  silent_star s1 s2 -> Handled_sort s2 = normal -> Handled_sort s1 = normal.
Proof. induction 1; ss. Qed.

Lemma silent_star_sort_normal_obs : forall s fn args k,
  silent_star s (Vis (Observe fn args) k) -> Handled_sort s = normal.
Proof. intros. eapply silent_star_sort_normal; eauto. Qed.

(** Catch-up observation: a compatible closure that allows source to
    take silent steps before matching an observable target step.
    The key: the silent steps are INSIDE the [forall ev st_tgt1] callback,
    so we see the target's label before choosing source's path. *)
Variant sim_catchupC
        (sim: bool -> bool -> X_state -> X_state -> Prop)
  : bool -> bool -> X_state -> X_state -> Prop :=
  | sim_catchupC_intro ps pt (src_h: Handled_state) st_tgt
      (SORT_S: X_sort (inl src_h) = normal)
      (SORT_T: X_sort st_tgt = normal)
      (SIM: forall ev st_tgt1,
          X_step st_tgt ev st_tgt1 ->
          (ekind_external ev = observableE) /\
          exists fn args retv (k: nat -> Handled_state),
            ev = inr (LExternal fn args retv) /\
            silent_star src_h (Vis (Observe fn args) k) /\
            sim true true (inl (k retv)) st_tgt1)
    : sim_catchupC sim ps pt (inl src_h) st_tgt.

Lemma sim_catchupC_mon: monotone4 sim_catchupC.
Proof.
  ii. inv IN. econs; eauto. i. exploit SIM; eauto. i. des. subst. esplits; eauto.
Qed.

#[local] Hint Resolve sim_catchupC_mon: paco.

(** The closure is wrespectful — each silent step becomes [sim_silentS],
    the final observable step becomes [sim_obs]. *)
Lemma sim_catchupC_wrespectful: wrespectful4 _sim sim_catchupC.
Proof.
  econs; eauto with paco.
  i. inv PR.
  econs 2; eauto.
  i. exploit SIM; eauto. i. des. subst. splits; auto.
  esplits.
  { eapply X_step_handled. eapply HS_observe_catch_up. eauto. }
  apply GF in x6. eapply Simulation.sim_mon; eauto.
  i. eapply rclo4_base. auto.
Qed.

Lemma sim_catchupC_spec: sim_catchupC <5= gupaco4 _sim (cpn4 _sim).
Proof.
  i. eapply wrespect4_uclo; eauto with paco. eapply sim_catchupC_wrespectful.
Qed.

(** Helper: [aeval] implies a [silent_star] for the handled source ITree.
    Given [aeval reg a n], the handled ITree [handle_mem (denote_aexp a reg >>= k) m]
    can silently reach [handle_mem (k n) m]. *)
Lemma aeval_silent_star :
  forall a reg n, aeval reg a n ->
  forall m (k: nat -> itree Es nat),
    silent_star (handle_mem (v <- denote_aexp a reg;; k v) m)
               (handle_mem (k n) m).
Proof.
  induction 1; intros m k0.
  - (* AAny *)
    cbn. rewrite handle_mem_choose_bind. rewrite bind_trigger.
    eapply ss_choose. eapply ss_tau. econs.
  - (* ANum *)
    cbn. rewrite bind_ret_l. econs.
  - (* AId *)
    cbn. unfold Reg.read.
    match goal with [H: _ _ = Some _ |- _] => rewrite H end.
    rewrite bind_ret_l. econs.
  - (* ABinOp *)
    cbn. rewrite bind_bind.
    eapply silent_star_trans.
    { eapply IHaeval1. }
    cbn. rewrite bind_bind.
    match goal with
    | |- context [handle_mem ?t _] =>
        replace t with (v2 <- denote_aexp a2 r;; k0 (bin_op_eval op n1 v2));
        [| f; f_equiv; intros v2; rewrite bind_ret_l; reflexivity]
    end.
    eapply IHaeval2.
Qed.

(** Helper for expression lists. *)
Lemma aeval_list_silent_star :
  forall es reg vs, Forall2 (aeval reg) es vs ->
  forall m (k: list nat -> itree Es nat),
    silent_star (handle_mem (vargs <- denote_aexps es reg;; k vargs) m)
               (handle_mem (k vs) m).
Proof.
  induction 1; intros m k0.
  - cbn. rewrite bind_ret_l. econs.
  - cbn. rewrite bind_bind.
    eapply silent_star_trans.
    { eapply aeval_silent_star. eauto. }
    replace (handle_mem _ m)
      with (handle_mem (vs <- denote_aexps l reg;; k0 (y :: vs)) m).
    2:{ unfold handle_mem. grind. }
    eapply IHForall2.
Qed.

(** Sort helper: if args are evaluable, source sort is normal. *)
Lemma handle_mem_ext_sort_normal :
  forall args reg name x kont mem vargs,
    Forall2 (aeval reg) args vargs ->
    Handled_sort (handle_mem (res <- denote_com (CExternal x name args) reg;; denote_cont kont res) mem) = normal.
Proof.
  intros.
  eapply silent_star_sort_normal.
  { cbn [denote_com]. rewrite !bind_bind.
    eapply silent_star_trans.
    { eapply aeval_list_silent_star. eauto. }
    econs. }
  ss.
Qed.

(** The main refinement theorem. *)
Theorem handle_mem_refinement :
  forall c, refines (fst (X_Program c)) (snd (X_Program c)).
Proof.
  intros c. apply adequacy.
  unfold simulation, X_Program, X_STS, X_sort, Imp_init. ss. intros.
  ginit. rewrite denote_program_cont.
  guclo @sim_progressC_spec. econs. instantiate (1:=pt). instantiate (1:=ps). 2,3: ss.
  remember Reg.init as reg. remember Kstop as kont. remember Mem.init as mem0.
  clear Heqreg Heqkont Heqmem0.
  revert ps pt c reg kont mem0.
  gcofix CIH. intros ps0 pt0 cmd reg kont mem.
  gstep.
  remember (com_size cmd) as sz eqn:Hsz.
  revert cmd reg kont mem ps0 pt0 Hsz.
  induction sz as [sz IHsz] using lt_wf_ind.
  intros cmd reg kont mem ps0 pt0 Hsz.
  (* Tactic: handle Step_silent_undefined for expression-based commands *)
  Local Ltac solve_undef_expr :=
    ss; split; auto; cbn; rewrite bind_bind;
    eapply no_aeval_sim.
  (* Tactic: fold interp_state back to handle_mem and apply CIH *)
  Local Ltac finish_CIH CIH :=
    (* Fold interp_state back to handle_mem if needed *)
    try (match goal with
    | |- context [inl (interp_state handle_Es ?t ?m)] =>
      change (interp_state handle_Es t m) with (handle_mem t m)
    end);
    (* Reconstruct handle_mem (... >>= ...) from the split form *)
    try rewrite <- handle_mem_bind;
    (* Reconstruct denote_com CSkip if needed *)
    try (match goal with
    | |- context [handle_mem (denote_cont ?k (inl ?r)) ?m] =>
      replace (handle_mem (denote_cont k (inl r)) m)
        with (handle_mem (res <- denote_com CSkip r;; denote_cont k res) m)
        by (cbn; rewrite bind_ret_l; reflexivity)
    end);
    econs 6; [gfinal; left; apply CIH | auto | auto].
  destruct cmd.
  - (* CSkip *)
    destruct kont.
    + (* Kstop: no CRet → UB *)
      cbn. rewrite bind_ret_l. cbn.
      rewrite handle_mem_undefined_bind. rewrite bind_trigger. econs 5. ss.
    + (* Kseq c k: step to next command *)
      cbn. rewrite bind_ret_l. cbn. rewrite handle_mem_tau.
      econs 3; [ss|]. esplits; [eapply X_step_handled; eapply HS_tau | ss |].
      econs 4; [ss|]. i.
      match goal with [H: X_step _ _ _ |- _] => inv H end.
      match goal with [H: step_silent _ _ _ |- _] => inv H end; ss.
      * match goal with [H: ceval_silent _ _ _ |- _] => inv H end.
        split; auto. finish_CIH CIH.
      * match goal with [U: forall _ _, ~ ceval_silent _ _ _ |- _] =>
          exfalso; eapply U; econs end.
  - (* CAsgn x a *)
    econs 4; [ss|]. i. inv H. inv STEP.
    + inv STEP0. ss. split; auto. cbn. rewrite bind_bind.
      eapply aeval_handle_sim'; eauto. intros ps'.
      (* After aeval, source = handle_mem (Ret (inl r') >>= denote_cont kont) mem.
         Reduce the Ret bind inside handle_mem, then dispatch on kont. *)
      destruct kont.
      * (* Kstop: source UB *)
        norm. econs 5. ss.
      * (* Kseq: tau + CIH via ES_Skip *)
        norm.
        econs 3; [ss|]; esplits; [eapply X_step_handled; eapply HS_tau | ss |].
        try rewrite fold_handle_mem; rewrite <- handle_mem_bind.
        econs 4; [ss|]; i.
        match goal with [H: X_step _ _ _ |- _] => inv H end.
        match goal with [H: step_silent _ _ _ |- _] => inv H end; ss.
        { match goal with [H: ceval_silent _ _ _ |- _] => inv H end.
          split; auto. finish_CIH CIH. }
        { match goal with [U: forall _ _, ~ ceval_silent _ _ _ |- _] =>
            exfalso; eapply U; econs end. }
    + solve_undef_expr. intros n Hae. eapply UNDEF. econs. exact Hae.
  - (* CSeq cmd1 cmd2 *)
    econs 4; [ss|]. i. inv H. inv STEP.
    + inv STEP0. ss. split; auto.
      match goal with
      | |- context [handle_mem ?t _] =>
        replace t with (res <- denote_com cmd1 reg;; denote_cont (Kseq cmd2 kont) res)
          by (symmetry; apply denote_seq_cont)
      end.
      eapply IHsz. 2: reflexivity. lia.
    + exfalso. eapply UNDEF. econs.
  - (* CIf b cmd1 cmd2 *)
    econs 4; [ss|]. i. inv H. inv STEP.
    + inv STEP0.
      * (* IfTrue *)
        ss. split; auto. cbn. rewrite bind_bind.
        eapply aeval_handle_sim'; eauto. intros ps'.
        destruct (Nat.eqb n 0) eqn:Heq; [apply PeanoNat.Nat.eqb_eq in Heq; lia|].
        eapply IHsz. 2: reflexivity. lia.
      * (* IfFalse *)
        ss. split; auto. cbn. rewrite bind_bind.
        eapply aeval_handle_sim'; eauto. intros ps'. subst.
        rewrite PeanoNat.Nat.eqb_refl.
        eapply IHsz. 2: reflexivity. lia.
    + solve_undef_expr. intros n Hae.
      destruct (PeanoNat.Nat.eq_dec n 0).
      * eapply UNDEF. eapply ES_IfFalse; eauto.
      * eapply UNDEF. eapply ES_IfTrue; eauto.
  - (* CWhile b cmd *)
    cbn. rewrite unfold_iter_eq. rewrite bind_bind.
    econs 4; [ss|]. i. inv H. inv STEP.
    + inv STEP0.
      * (* WhileFalse *)
        ss. split; auto. rewrite bind_bind.
        eapply aeval_handle_sim'; eauto. intros ps'. subst.
        rewrite PeanoNat.Nat.eqb_refl. cbn. rewrite bind_ret_l. cbn.
        destruct kont.
        { cbn. norm. econs 5. ss. }
        { simpl denote_cont. norm.
          econs 3; [ss|]; esplits; [eapply X_step_handled; eapply HS_tau | ss |].
          econs 4; [ss|]; i.
          match goal with [H: X_step _ _ _ |- _] => inv H end.
          match goal with [H: step_silent _ _ _ |- _] => inv H end; ss.
          - match goal with [H: ceval_silent _ _ _ |- _] => inv H end.
            split; auto. try rewrite fold_handle_mem; rewrite <- handle_mem_bind.
            finish_CIH CIH.
          - match goal with [U: forall _ _, ~ ceval_silent _ _ _ |- _] =>
              exfalso; eapply U; econs end. }
      * (* WhileTrue *)
        ss. split; auto. rewrite bind_bind.
        eapply aeval_handle_sim'; eauto. intros ps'.
        destruct (Nat.eqb n 0) eqn:Heq; [apply PeanoNat.Nat.eqb_eq in Heq; lia|].
        cbn. rewrite bind_bind.
        replace (fun r0 : Reg.t + nat => _) with (denote_cont (Kseq (CWhile b cmd) kont))
          by (apply func_ext_dep; intros [r'|v]; cbn;
              repeat (try rewrite bind_bind; try rewrite bind_ret_l;
                      try rewrite bind_tau; try rewrite denote_cont_ret; cbn);
              try reflexivity).
        eapply IHsz. 2: reflexivity. lia.
    + solve_undef_expr. intros n Hae.
      destruct (PeanoNat.Nat.eq_dec n 0).
      * eapply UNDEF. eapply ES_WhileFalse; eauto.
      * eapply UNDEF. eapply ES_WhileTrue; eauto.
  - (* CRet a *)
    econs 4; [ss|]. i. inv H. inv STEP.
    + inv STEP0. ss. split; auto. cbn. rewrite bind_bind.
      eapply aeval_handle_sim'; eauto. intros ps'.
      rewrite bind_ret_l. rewrite denote_cont_ret. norm. econs 1; ss.
    + solve_undef_expr. intros n Hae. eapply UNDEF. econs. exact Hae.
  - (* CMemLoad x loc *)
    econs 4; [ss|]. i. inv H. inv STEP.
    + inv STEP0. ss. split; auto. cbn. rewrite bind_bind.
      rewrite handle_mem_memload_bind.
      match goal with [H: Mem.load _ _ = Some _ |- _] => rewrite H end. cbn.
      rewrite handle_mem_bind. rewrite handle_mem_ret. norm.
      econs 3; [ss|]. esplits; [eapply X_step_handled; eapply HS_tau | ss |].
      destruct kont.
      * norm. econs 5. ss.
      * norm.
        econs 3; [ss|]; esplits; [eapply X_step_handled; eapply HS_tau | ss |].
        econs 4; [ss|]; i.
        match goal with [H: X_step _ _ _ |- _] => inv H end.
        match goal with [H: step_silent _ _ _ |- _] => inv H end; ss.
        { match goal with [H: ceval_silent _ _ _ |- _] => inv H end.
          split; auto. finish_CIH CIH. }
        { match goal with [U: forall _ _, ~ ceval_silent _ _ _ |- _] =>
            exfalso; eapply U; econs end. }
    + (* Step_silent_undefined: Mem.load fails *)
      ss. split; auto. cbn. rewrite bind_bind.
      rewrite handle_mem_memload_bind.
      destruct (Mem.load mem loc) eqn:Hl.
      * exfalso. eapply UNDEF. eapply ES_MemLoad; eauto.
      * cbn. norm.
        econs 3; [ss|]. esplits; [eapply X_step_handled; eapply HS_tau | ss |].
        econs 5. ss.
  - (* CMemStore l a *)
    econs 4; [ss|]. i. inv H. inv STEP.
    + inv STEP0. ss. split; auto. cbn. rewrite bind_bind.
      eapply aeval_handle_sim'; eauto. intros ps'.
      unfold handle_mem. rewrite interp_state_bind.
      rewrite interp_state_bind. rewrite interp_state_trigger. cbn. norm.
      econs 3; [ss|]. esplits; [eapply X_step_handled; eapply HS_tau | ss |].
      destruct kont.
      * norm. econs 5. ss.
      * norm.
        econs 3; [ss|]; esplits; [eapply X_step_handled; eapply HS_tau | ss |].
        try rewrite fold_handle_mem; rewrite <- handle_mem_bind.
        econs 4; [ss|]; i.
        match goal with [H: X_step _ _ _ |- _] => inv H end.
        match goal with [H: step_silent _ _ _ |- _] => inv H end; ss.
        { match goal with [H: ceval_silent _ _ _ |- _] => inv H end.
          split; auto. finish_CIH CIH. }
        { match goal with [U: forall _ _, ~ ceval_silent _ _ _ |- _] =>
            exfalso; eapply U; econs end. }
    + solve_undef_expr. intros n Hae. eapply UNDEF. eapply ES_MemStore; eauto.
  - (* CExternal x name args *)
    (* Use sim_silentS to step source through expression evaluation,
       then sim_obs for the observable Observe step.
       For the non-evaluable case, target goes to Undef. *)
    destruct (classic (exists vargs, Forall2 (aeval reg) args vargs)) as [[vargs Hf] | Hnf].
    + (* Args evaluable: use sim_obs with HS_observe_catch_up *)
      econs 2.
      { eapply handle_mem_ext_sort_normal; eauto. }
      { ss. }
      intros ev st_tgt1 HSTEP. inv HSTEP. inv STEP.
      * inv STEP0. ss. split; auto.
        esplits.
        { (* Use HS_observe_catch_up: silent_star to Vis (Observe name vargs0) then observe *)
          eapply X_step_handled. eapply HS_observe_catch_up.
          cbn [denote_com]. rewrite !bind_bind.
          eapply silent_star_trans.
          { eapply aeval_list_silent_star. eauto. }
          cbn. rewrite bind_bind. rewrite handle_mem_observe_bind.
          rewrite bind_trigger. eapply ss_refl. }
        (* Continuation after observe: source has tau;; handle_mem (...) mem *)
        norm.
        econs 3; [ss|]. esplits; [eapply X_step_handled; eapply HS_tau | ss |].
        norm. finish_CIH CIH.
      * exfalso. eapply UNDEF. eapply ES_External. exact Hf.
    + (* Args not evaluable: target goes to Undef via Step_silent_undefined *)
      econs 4; [ss|]. i. inv H. inv STEP.
      * inv STEP0. exfalso. apply Hnf. eauto.
      * ss. split; auto. cbn [denote_com]. rewrite !bind_bind.
        eapply no_aeval_list_sim. exact Hnf.
  Unshelve. all: exact 0.
Qed.

Corollary handle_mem_refines_imp :
  forall c,
    (forall tr,
      behavior (snd (X_Program c)).(init) tr ->
      behavior (fst (X_Program c)).(init) tr).
Proof.
  intros c. apply handle_mem_refinement.
Qed.
