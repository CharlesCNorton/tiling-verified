(******************************************************************************)
(*                                                                            *)
(*  First-order arithmetic layer (todo item #1).                             *)
(*                                                                            *)
(*  Arithmetic over the standard model N:                                     *)
(*    - terms over 0, S, +, * ; formulas over = with Bot, Impl, forall        *)
(*      (Neg, And, Or, Ex as macros);                                         *)
(*    - the satisfaction relation [sat : env -> fm -> Prop] interpreting      *)
(*      formulas in N;                                                        *)
(*    - a deductive system [Pr]: classical first-order logic with the         *)
(*      Robinson Q equational axioms;                                         *)
(*    - [Pr_sound : Pr A -> forall e, sat e A] and                            *)
(*      [Pr_consistent : ~ Pr fbot].                                          *)
(*                                                                            *)
(*  Phase 1: syntax, model, numeral substitution and its semantics, the       *)
(*  deductive system, soundness.  Phase 2: provable numeral arithmetic,       *)
(*  Sigma_1 (Diophantine) completeness, Goedel numbering.                     *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical.
Import ListNotations.

(** ** First-order syntax. *)

Inductive tm : Type :=
  | tv : nat -> tm           (* variable *)
  | tz : tm                  (* zero *)
  | ts : tm -> tm            (* successor *)
  | tp : tm -> tm -> tm      (* plus *)
  | tt : tm -> tm -> tm.     (* times *)

Inductive fm : Type :=
  | feq  : tm -> tm -> fm
  | fbot : fm
  | fimp : fm -> fm -> fm
  | fall : nat -> fm -> fm.

Definition fneg (A : fm) : fm := fimp A fbot.
Definition ftop : fm := fimp fbot fbot.
Definition fand (A B : fm) : fm := fneg (fimp A (fneg B)).
Definition for_ (A B : fm) : fm := fimp (fneg A) B.
Definition fex (x : nat) (A : fm) : fm := fneg (fall x (fneg A)).

(** Numerals. *)

Fixpoint num (k : nat) : tm :=
  match k with O => tz | S k' => ts (num k') end.

(** ** The standard model N. *)

Definition env := nat -> nat.
Definition update (e : env) (x v : nat) : env :=
  fun y => if Nat.eqb y x then v else e y.

Fixpoint eval_tm (e : env) (t : tm) : nat :=
  match t with
  | tv n => e n
  | tz => 0
  | ts a => S (eval_tm e a)
  | tp a b => eval_tm e a + eval_tm e b
  | tt a b => eval_tm e a * eval_tm e b
  end.

Fixpoint sat (e : env) (A : fm) : Prop :=
  match A with
  | feq a b => eval_tm e a = eval_tm e b
  | fbot => False
  | fimp A B => sat e A -> sat e B
  | fall x A => forall v, sat (update e x v) A
  end.

Lemma eval_num : forall e k, eval_tm e (num k) = k.
Proof. intros e k. induction k as [|k IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

(** Extensional respect for the environment. *)

Lemma eval_ext : forall t e1 e2,
  (forall n, e1 n = e2 n) -> eval_tm e1 t = eval_tm e2 t.
Proof.
  induction t; intros e1 e2 H; cbn.
  - apply H.
  - reflexivity.
  - rewrite (IHt e1 e2 H); reflexivity.
  - rewrite (IHt1 e1 e2 H), (IHt2 e1 e2 H); reflexivity.
  - rewrite (IHt1 e1 e2 H), (IHt2 e1 e2 H); reflexivity.
Qed.

Lemma sat_ext : forall A e1 e2,
  (forall n, e1 n = e2 n) -> (sat e1 A <-> sat e2 A).
Proof.
  induction A as [a b | | A IHA B IHB | x A IHA]; intros e1 e2 H; cbn.
  - rewrite (eval_ext a e1 e2 H), (eval_ext b e1 e2 H). reflexivity.
  - reflexivity.
  - rewrite (IHA e1 e2 H), (IHB e1 e2 H). reflexivity.
  - split; intros Hf v; specialize (Hf v).
    + rewrite <- (IHA (update e1 x v) (update e2 x v)); [exact Hf|].
      intro n. unfold update. destruct (Nat.eqb n x); [reflexivity | apply H].
    + rewrite (IHA (update e1 x v) (update e2 x v)); [exact Hf|].
      intro n. unfold update. destruct (Nat.eqb n x); [reflexivity | apply H].
Qed.

Lemma update_comm : forall e x y u w n,
  x <> y -> update (update e x u) y w n = update (update e y w) x u n.
Proof.
  intros e x y u w n Hxy. unfold update.
  destruct (Nat.eqb n y) eqn:Ey; destruct (Nat.eqb n x) eqn:Ex; try reflexivity.
  apply Nat.eqb_eq in Ey, Ex. subst. contradiction.
Qed.

Lemma update_shadow : forall e x u w n,
  update (update e x u) x w n = update e x w n.
Proof.
  intros e x u w n. unfold update. destruct (Nat.eqb n x); reflexivity.
Qed.

(** ** Numeral substitution and its semantic correctness. *)

Fixpoint subst_tm (x k : nat) (t : tm) : tm :=
  match t with
  | tv y => if Nat.eqb y x then num k else tv y
  | tz => tz
  | ts a => ts (subst_tm x k a)
  | tp a b => tp (subst_tm x k a) (subst_tm x k b)
  | tt a b => tt (subst_tm x k a) (subst_tm x k b)
  end.

Fixpoint subst_num (x k : nat) (A : fm) : fm :=
  match A with
  | feq a b => feq (subst_tm x k a) (subst_tm x k b)
  | fbot => fbot
  | fimp A B => fimp (subst_num x k A) (subst_num x k B)
  | fall y A => if Nat.eqb y x then fall y A else fall y (subst_num x k A)
  end.

Lemma eval_subst_tm : forall t x k e,
  eval_tm e (subst_tm x k t) = eval_tm (update e x k) t.
Proof.
  induction t; intros x k e; cbn.
  - destruct (Nat.eqb n x) eqn:E.
    + rewrite eval_num. unfold update. rewrite E. reflexivity.
    + cbn. unfold update. rewrite E. reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma sat_subst_num : forall A x k e,
  sat e (subst_num x k A) <-> sat (update e x k) A.
Proof.
  induction A as [a b | | A IHA B IHB | y A IHA]; intros x k e; cbn.
  - rewrite (eval_subst_tm a), (eval_subst_tm b). reflexivity.
  - reflexivity.
  - rewrite IHA, IHB. reflexivity.
  - destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst y. cbn.
      split; intros Hf v; specialize (Hf v).
      * rewrite (sat_ext A (update (update e x k) x v) (update e x v)
                  (update_shadow e x k v)). exact Hf.
      * rewrite <- (sat_ext A (update (update e x k) x v) (update e x v)
                  (update_shadow e x k v)). exact Hf.
    + apply Nat.eqb_neq in E. cbn.
      split; intros Hf v; specialize (Hf v).
      * rewrite (IHA x k (update e y v)) in Hf.
        rewrite (sat_ext A (update (update e x k) y v) (update (update e y v) x k)
                  (fun n => update_comm e x y k v n (fun H => E (eq_sym H)))).
        exact Hf.
      * rewrite (IHA x k (update e y v)).
        rewrite (sat_ext A (update (update e y v) x k) (update (update e x k) y v)
                  (fun n => update_comm e y x v k n E)). exact Hf.
Qed.

(** ** The deductive system: classical first-order logic + Robinson Q. *)

Inductive Pr : fm -> Prop :=
  (* classical propositional logic *)
  | p_K : forall A B, Pr (fimp A (fimp B A))
  | p_S : forall A B C,
      Pr (fimp (fimp A (fimp B C)) (fimp (fimp A B) (fimp A C)))
  | p_DN : forall A, Pr (fimp (fneg (fneg A)) A)
  | p_MP : forall A B, Pr (fimp A B) -> Pr A -> Pr B
  (* first-order quantifier rules (numeral instantiation) *)
  | p_gen : forall x A, Pr A -> Pr (fall x A)
  | p_all_elim : forall x k A, Pr (fimp (fall x A) (subst_num x k A))
  (* equality *)
  | p_refl : forall t, Pr (feq t t)
  | p_eq_sym : forall a b, Pr (fimp (feq a b) (feq b a))
  | p_eq_trans : forall a b c,
      Pr (fimp (feq a b) (fimp (feq b c) (feq a c)))
  | p_cong_s : forall a b, Pr (fimp (feq a b) (feq (ts a) (ts b)))
  | p_cong_p : forall a b c d,
      Pr (fimp (feq a b) (fimp (feq c d) (feq (tp a c) (tp b d))))
  | p_cong_t : forall a b c d,
      Pr (fimp (feq a b) (fimp (feq c d) (feq (tt a c) (tt b d))))
  (* Robinson Q (equational fragment) *)
  | q_succ_neq_zero : forall x,
      Pr (fall x (fneg (feq (ts (tv x)) tz)))
  | q_succ_inj : forall x y,
      Pr (fall x (fall y (fimp (feq (ts (tv x)) (ts (tv y))) (feq (tv x) (tv y)))))
  | q_plus_zero : forall x, Pr (fall x (feq (tp (tv x) tz) (tv x)))
  | q_plus_succ : forall x y,
      Pr (fall x (fall y (feq (tp (tv x) (ts (tv y))) (ts (tp (tv x) (tv y))))))
  | q_mult_zero : forall x, Pr (fall x (feq (tt (tv x) tz) tz))
  | q_mult_succ : forall x y,
      Pr (fall x (fall y (feq (tt (tv x) (ts (tv y))) (tp (tt (tv x) (tv y)) (tv x))))).

(** ** Soundness against the standard model. *)

Theorem Pr_sound : forall A, Pr A -> forall e, sat e A.
Proof.
  intros A H. induction H; intro e; cbn in *.
  - intros HA _. exact HA.
  - intros Hf Hg Ha. apply Hf; [exact Ha | apply Hg; exact Ha].
  - intro Hnn. apply NNPP. exact Hnn.
  - exact (IHPr1 e (IHPr2 e)).
  - intro v. exact (IHPr (update e x v)).
  - intro Hf. apply (sat_subst_num A x k e). exact (Hf k).
  - reflexivity.
  - intro Hab. symmetry. exact Hab.
  - intros Hab Hbc. rewrite Hab. exact Hbc.
  - intro Hab. rewrite Hab. reflexivity.
  - intros Hab Hcd. rewrite Hab, Hcd. reflexivity.
  - intros Hab Hcd. rewrite Hab, Hcd. reflexivity.
  - intros v Hv. lia.
  - intros v w Hvw. lia.
  - intro v. lia.
  - intros v w. lia.
  - intro v. lia.
  - intros v w. cbn. lia.
Qed.

Theorem Pr_consistent : ~ Pr fbot.
Proof.
  intro H. exact (Pr_sound fbot H (fun _ => 0)).
Qed.
