From ITree Require Export ITree Subevent.

From ITree Require Export
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     EqAxiom (* We use bisimulation_is_eq axiom *)
     HeterogeneousRelations
.
From ExtLib Require Export
     Functor FunctorLaws
     Structures.Maps
.


Module ITreeNotations2.
Notation "t1 >>= k2" := (ITree.bind t1 k2)
  (at level 58, left associativity) : itree_scope.
Notation "x <- t1 ;; t2" := (ITree.bind t1 (fun x => t2))
  (at level 62, t1 at next level, right associativity) : itree_scope.
Notation "` x : t <- t1 ;; t2" := (ITree.bind t1 (fun x : t => t2))
  (at level 62, t at next level, t1 at next level, x ident, right associativity) : itree_scope.
Notation "t1 ;;; t2" := (ITree.bind t1 (fun _ => t2))
  (at level 62, right associativity) : itree_scope.
Notation "' p <- t1 ;; t2" :=
  (ITree.bind t1 (fun x_ => match x_ with p => t2 end))
  (at level 62, t1 at next level, p pattern, right associativity) : itree_scope.
Infix ">=>" := ITree.cat (at level 62, right associativity) : itree_scope.
Notation "f <$> x" := (@fmap _ _ _ _ f x) (at level 61, left associativity).
End ITreeNotations2.


Export SumNotations.
(* Export ITreeNotations. *)
Export Monads.
(* Export MonadNotation. *)
(* Export FunctorNotation. *)
Export CatNotations.
Export ITreeNotations2.
Open Scope cat_scope.
Open Scope monad_scope.
Open Scope itree_scope.

Require Import Program.
From sflib Require Import sflib.
From Paco Require Import paco.

Require ClassicalFacts.
Require FunctionalExtensionality.

Set Implicit Arguments.

Lemma func_ext_dep {A} {B: A -> Type} (f g: forall x, B x): (forall x, f x = g x) -> f = g.
Proof.
  apply @FunctionalExtensionality.functional_extensionality_dep.
Qed.



Global Instance function_Map (K V: Type) (dec: forall k0 k1, {k0=k1} + {k0<>k1}): (Map K V (K -> option V)) :=
  Build_Map
    (fun _ => None)
    (fun k0 v m => fun k1 => if dec k0 k1 then Some v else m k1)
    (fun k0 m => fun k1 => if dec k0 k1 then None else m k1)
    (fun k m => m k)
    (fun m0 m1 => fun k => match (m0 k) with
                           | Some v => Some v
                           | _ => m1 k
                           end)
.



Lemma eq_is_bisim: forall E R (t1 t2 : itree E R), t1 = t2 -> t1 ≅ t2.
Proof. ii. clarify. reflexivity. Qed.
Lemma bisim_is_eq: forall E R (t1 t2 : itree E R), t1 ≅ t2 -> t1 = t2.
Proof. ii. eapply bisimulation_is_eq; eauto. Qed.


Ltac f := first [eapply bisim_is_eq|eapply eq_is_bisim].
Tactic Notation "f" "in" hyp(H) := first [eapply bisim_is_eq in H|eapply eq_is_bisim in H].
Ltac ides itr :=
  let T := fresh "T" in
  destruct (observe itr) eqn:T;
  symmetry in T; apply simpobs in T; apply bisim_is_eq in T; rewrite T in *; clarify.
Ltac csc := clarify; simpl_depind; clarify.

Notation "tau;; t2" := (Tau t2)
  (at level 200, right associativity) : itree_scope.



(*** COPIED FROM MASTER BRANCH. REMOVE LATER ***)
(*** COPIED FROM MASTER BRANCH. REMOVE LATER ***)
(*** COPIED FROM MASTER BRANCH. REMOVE LATER ***)
Lemma eutt_eq_bind : forall E R U (t1 t2: itree E U) (k1 k2: U -> itree E R), t1 ≈ t2 -> (forall u, k1 u ≈ k2 u) -> ITree.bind t1 k1 ≈ ITree.bind t2 k2.
Proof.
  intros.
  eapply eutt_clo_bind with (UU := Logic.eq); [eauto |].
  intros ? ? ->. apply H0.
Qed.
Ltac f_equiv := first [eapply eutt_eq_bind|eapply eqit_VisF|Morphisms.f_equiv].
(* eapply eqit_bind'| *)

#[export] Hint Rewrite @bind_trigger : itree.
#[export] Hint Rewrite @tau_eutt : itree.
#[export] Hint Rewrite @bind_tau : itree.

(* Tactic Notation "irw" "in" ident(H) := repeat (autorewrite with itree in H; cbn in H). *)
(* Tactic Notation "irw" := repeat (autorewrite with itree; cbn). *)

(*** TODO: IDK why but (1) ?UNUSNED is needed (2) "fold" tactic does not work. WHY????? ***)
Ltac fold_eutt :=
  repeat multimatch goal with
         | [ H: eqit eq true true ?A ?B |- ?UNUSED ] =>
           let name := fresh "tmp" in
           assert(tmp: eutt eq A B) by apply H; clear H; rename tmp into H
         end
.

Lemma bind_ret_map {E R1 R2} (u : itree E R1) (f : R1 -> R2) :
  (r <- u ;; Ret (f r)) = f <$> u.
Proof.
  f.
  rewrite <- (bind_ret_r u) at 2. apply eqit_bind.
  - rewrite bind_ret_r. reflexivity.
  - hnf. intros. apply eqit_Ret. auto.
Qed.

Lemma map_vis {E R1 R2 X} (e: E X) (k: X -> itree E R1) (f: R1 -> R2) :
  (* (f <$> (Vis e k)) ≅ Vis e (fun x => f <$> (k x)). *)
  ITree.map f (Vis e k) = Vis e (fun x => f <$> (k x)).
Proof.
  f.
  cbn.
  unfold ITree.map.
  autorewrite with itree. reflexivity.
Qed.




(*** TODO: move to SIRCommon ***)
Lemma unfold_interp_mrec :
forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T)
  (R : Type) (t : itree (D +' E) R), interp_mrec ctx t = _interp_mrec ctx (observe t).
Proof.
  i. f. eapply unfold_interp_mrec; eauto.
Qed.

Lemma bind_ret_l : forall (E : Type -> Type) (R S : Type) (r : R) (k : R -> itree E S),
    x <- Ret r;; k x = k r.
Proof.
  i. f. eapply bind_ret_l.
Qed.

Lemma bind_ret_r : forall (E : Type -> Type) (R : Type) (s : itree E R), x <- s;; Ret x = s.
Proof.
  i. f. eapply bind_ret_r.
Qed.

Lemma bind_ret_r_rev : forall (E : Type -> Type) (R : Type) (s : itree E R), s = x <- s;; Ret x.
Proof.
  i. symmetry. apply bind_ret_r.
Qed.

Lemma bind_tau : forall (E : Type -> Type) (R U : Type) (t : itree E U) (k : U -> itree E R),
  x <- Tau t;; k x = Tau (x <- t;; k x).
Proof.
  i. f. eapply bind_tau.
Qed.

Lemma bind_vis: forall (E : Type -> Type) (R U V : Type) (e : E V) (ek : V -> itree E U) (k : U -> itree E R),
  x <- Vis e ek;; k x = Vis e (fun x : V => x <- ek x;; k x).
Proof.
  i. f. eapply bind_vis.
Qed.

Lemma bind_trigger: forall (E : Type -> Type) (R U : Type) (e : E U) (k : U -> itree E R),
    x <- ITree.trigger e;; k x = Vis e (fun x : U => k x).
Proof. i. f. eapply bind_trigger. Qed.

Lemma bind_bind : forall (E : Type -> Type) (R S T : Type) (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    x <- (x <- s;; k x);; h x = r <- s;; x <- k r;; h x.
Proof. i. f. eapply bind_bind. Qed.

(* Lemma unfold_bind : *)
(* forall (E : Type -> Type) (R S : Type) (t : itree E R) (k : R -> itree E S), *)
(* x <- t;; k x = ITree._bind k (fun t0 : itree E R => x <- t0;; k x) (observe t). *)
(* Proof. i. f. apply unfold_bind. Qed. *)

Lemma interp_mrec_bind:
  forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T)
         (U T : Type) (t : itree (D +' E) U) (k : U -> itree (D +' E) T),
    interp_mrec ctx (x <- t;; k x) = x <- interp_mrec ctx t;; interp_mrec ctx (k x)
.
Proof. ii. f. eapply interp_mrec_bind. Qed.


#[export] Hint Rewrite unfold_interp_mrec : itree_axiom.
#[export] Hint Rewrite bind_ret_l : itree_axiom.
#[export] Hint Rewrite bind_ret_r : itree_axiom.
#[export] Hint Rewrite bind_tau : itree_axiom.
#[export] Hint Rewrite bind_vis : itree_axiom.
#[export] Hint Rewrite bind_trigger : itree_axiom.
#[export] Hint Rewrite bind_bind : itree_axiom.
Tactic Notation "irw" "in" ident(H) := repeat (autorewrite with itree_axiom in H; cbn in H).
Tactic Notation "irw" := repeat (autorewrite with itree_axiom; cbn).

Lemma interp_state_bind:
  forall (E F : Type -> Type) (A B S : Type) (f : forall T : Type, E T -> S -> itree F (S * T)) (t : itree E A)
         (k : A -> itree E B) (s : S),
    interp_state f (x <- t;; k x) s = st <- interp_state f t s;; interp_state f (k (snd st)) (fst st)
.
Proof. i. f. apply interp_state_bind. Qed.

Lemma interp_state_vis:
  forall (E F : Type -> Type) (S T U : Type) (e : E T) (k : T -> itree E U) (h : forall T0 : Type, E T0 -> stateT S (itree F) T0)
         (s : S), interp_state h (Vis e k) s = sx <- h T e s;; (tau;; interp_state h (k (snd sx)) (fst sx))
.
Proof.
  i. f. apply interp_state_vis.
Qed.

Lemma interp_state_tau :
  forall (E F : Type -> Type) (S T : Type) (t : itree E T) (h : forall T0 : Type, E T0 -> stateT S (itree F) T0) (s : S),
    interp_state h (tau;; t) s = (tau;; interp_state h t s)
.
Proof.
  i. f. apply interp_state_tau.
Qed.

Lemma interp_state_ret:
  forall (E F : Type -> Type) (R S : Type) (f : forall T : Type, E T -> S -> itree F (S * T)) (s : S) (r : R),
    interp_state f (Ret r) s = Ret (s, r)
.
Proof.
  i. f. apply interp_state_ret.
Qed.

Lemma unfold_interp:
  forall (E F : Type -> Type) (R : Type) (f : forall T : Type, E T -> itree F T) (t : itree E R),
    interp f t = _interp f (observe t)
.
Proof.
  i. f. apply unfold_interp.
Qed.
Lemma interp_ret:
  forall (E F : Type -> Type) (R : Type) (f : forall T : Type, E T -> itree F T) (x : R), interp f (Ret x) = Ret x.
Proof. i. f. apply interp_ret. Qed.

Lemma interp_tau:
  forall {E F : Type -> Type} {R : Type} {f : forall T : Type, E T -> itree F T} (t : itree E R),
    interp f (tau;; t) = (tau;; interp f t)
.
Proof. i. f. apply interp_tau. Qed.

(*** Original name: interp_state_trigger_eqit ***)
Lemma interp_state_trigger:
  forall (E F : Type -> Type) (R S : Type) (e : E R) (f : forall T : Type, E T -> stateT S (itree F) T) (s : S),
    interp_state f (ITree.trigger e) s = x <- f R e s;; (tau;; Ret x)
.
Proof. i. f. apply interp_state_trigger_eqit. Qed.

(*** TODO: interp_trigger_eqit does not exist. report to itree people? ***)
Lemma interp_trigger:
  forall (E F : Type -> Type) (R : Type) (e : E R) (f : E ~> itree F),
    interp f (ITree.trigger e) = x <- f R e;; tau;; Ret x
.
Proof. i. f. rewrite unfold_interp. ss. f_equiv; ii. rewrite interp_ret. reflexivity. Qed.

Lemma interp_bind :
forall {E F : Type -> Type} {R S : Type} (f : forall T : Type, E T -> itree F T)
  (t : itree E R) (k : R -> itree E S),
interp f (x <- t;; k x) = r <- interp f t;; interp f (k r).
Proof. i. f. apply interp_bind. Qed.

Lemma interp_mrec_hit:
  forall (D E : Type -> Type) (ctx : forall T : Type, D T -> itree (D +' E) T) (U : Type) (a : D U),
    interp_mrec ctx (trigger a) = (tau;; interp_mrec ctx (ctx _ a))
.
Proof.
  i. rewrite unfold_interp_mrec. ss.
  unfold resum, ReSum_id, id_, Id_IFun. rewrite bind_ret_r. ss.
Qed.

(*** TODO: I don't want "F" here, but it is technically needed. Report it to itree people? ***)
Lemma interp_mrec_miss:
  (* forall (D E F: Type -> Type) `{F -< E} (ctx : forall T : Type, D T -> itree (D +' E) T) (U : Type) (a : F U), *)
  forall (D E F: Type -> Type) `{F -< E} (ctx : forall T : Type, D T -> itree (D +' E) T) (U : Type) (a : F U),
    interp_mrec ctx (trigger a) = x <- (trigger a);; tau;; Ret x
(* (trigger a) >>= tauK *)
.
Proof.
  i. rewrite unfold_interp_mrec. cbn.
  unfold trigger. irw.
  f; repeat (f_equiv; ii; des_ifs); f.
  irw. ss.
Qed.

Lemma interp_mrec_tau
      D E
      (ctx : forall T : Type, D T -> itree (D +' E) T)
      U
      (itr: itree (D +' E) U)
  :
    interp_mrec ctx (tau;; itr) = (tau;; interp_mrec ctx itr)
.
Proof. rewrite unfold_interp_mrec at 1. cbn. reflexivity. Qed.

Lemma interp_mrec_ret
      D E
      (ctx : forall T : Type, D T -> itree (D +' E) T)
      U
      (u: U)
  :
    interp_mrec ctx (Ret u) = Ret u
.
Proof. rewrite unfold_interp_mrec at 1. cbn. reflexivity. Qed.

Lemma interp_interp:
  forall {E F G : Type -> Type} {R : Type} (f : forall T : Type, E T -> itree F T) (g : forall T : Type, F T -> itree G T) (t : itree E R),
    interp g (interp f t) = interp (fun (T : Type) (e : (fun H : Type => E H) T) => interp g (f T e)) t.
Proof. i. f. apply interp_interp. Qed.

Ltac iby3 TAC :=
  first [
      instantiate (1:= fun _ _ _ => _); TAC|
      instantiate (1:= fun _ _ _ => _ <- _ ;; _); TAC|
      instantiate (1:= fun _ _ _ => _ <- (_ <- _ ;; _) ;; _); TAC|
      instantiate (1:= fun _ _ _ => _ <- (_ <- (_ <- _ ;; _) ;; _) ;; _); TAC|
      instantiate (1:= fun _ _ _ => _ <- (_ <- (_ <- (_ <- _ ;; _) ;; _) ;; _) ;; _); TAC|
      instantiate (1:= fun _ _ _ => _ <- (_ <- (_ <- (_ <- (_ <- _ ;; _) ;; _) ;; _) ;; _) ;; _); TAC|
      fail
    ]
.

Ltac iby1 TAC :=
  first [
      instantiate (1:= fun '(_, (_, _)) => _); TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- _ ;; _); TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- (_ <- _ ;; _) ;; _); TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- (_ <- (_ <- _ ;; _) ;; _) ;; _); TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- (_ <- (_ <- (_ <- _ ;; _) ;; _) ;; _) ;; _); TAC|
      instantiate (1:= fun '(_, (_, _)) => _ <- (_ <- (_ <- (_ <- (_ <- _ ;; _) ;; _) ;; _) ;; _) ;; _); TAC|
      fail
    ]
.

(* Ltac grind :=  f; repeat (f_equiv; ii; des_ifs_safe); f. *)

Ltac ired := repeat (try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r; try rewrite bind_tau; try rewrite bind_vis;
                     (* try rewrite interp_vis; *)
                     try rewrite interp_ret;
                     try rewrite interp_tau;
                     (* try rewrite interp_trigger *)
                     try rewrite interp_bind;

                     try rewrite interp_mrec_hit;
                     try rewrite interp_mrec_miss;
                     try rewrite interp_mrec_bind;
                     try rewrite interp_mrec_tau;
                     try rewrite interp_mrec_ret;

                     try rewrite interp_state_trigger;
                     try rewrite interp_state_bind;
                     try rewrite interp_state_tau;
                     try rewrite interp_state_ret;
                     cbn
                    ).
(* first [eapply eqit_VisF|f_equiv] *)
(* Ltac grind := repeat (ired; f; repeat (f_equiv; match goal with [ |- context[going] ] => fail | _ => idtac end; ii; des_ifs_safe); f). *)
(* Ltac grind := repeat (ired; f; repeat (Morphisms.f_equiv; ii; des_ifs_safe); f). *)
Ltac grind := repeat (ired; match goal with
                            (* | [ |- tau;; ?a = tau;; ?b ] => do 2 f_equal *)
                            | [ |- (go (TauF ?a)) = (go (TauF ?b)) ] => do 2 f_equal
                            | [ |- (_ <- _ ;; _) = (_ <- _ ;; _) ] => Morphisms.f_equiv; apply func_ext_dep; i
                            | _ => idtac
                            end; ii; des_ifs).
(*** simple regression tests ***)
Goal forall E R (itr: itree E R), (tau;; tau;; tau;; itr) = (tau;; tau;; itr). i. grind. Abort.
Goal forall E X Y (itr: itree E X) (ktr: X -> itree E Y), ((x <- itr;; tau;; tau;; Ret x) >>= ktr) = ((x <- itr;; tau;; Ret x) >>= ktr).
  i. progress grind. (*** it should progress ***)
Abort.







Definition resum_itr E F `{E -< F}: itree E ~> itree F := fun _ itr => interp (fun _ e => trigger e) itr.

Definition tauK {E R}: R -> itree E R := fun r => tau;; Ret r.
#[export] Hint Unfold tauK: core.

Definition idK {E R}: R -> itree E R := fun r => Ret r.
#[export] Hint Unfold idK: core.

Lemma idK_spec E R (i0: itree E R): i0 = i0 >>= idK. Proof. unfold idK. irw. reflexivity. Qed.

Lemma observe_eta E R (itr0 itr1: itree E R)
      (EQ: _observe itr0 = _observe itr1)
  :
    itr0 = itr1.
Proof.
  erewrite (itree_eta_ itr0).
  erewrite (itree_eta_ itr1).
  f_equal. auto.
Qed.

Ltac destruct_itree itr :=
  let E := fresh "E" in
  destruct (observe itr) eqn: E;
  symmetry in E;
  apply simpobs in E;
  apply bisim_is_eq in E;
  subst itr.

Lemma unfold_iter_eq A E B
  : forall (f : A -> itree E (A + B)) (x : A),
    ITree.iter f x = lr <- f x;; match lr with
                                 | inl l => Tau (ITree.iter f l)
                                 | inr r0 => Ret r0
                                 end.
Proof.
  i. eapply bisim_is_eq. eapply unfold_iter.
Qed.
