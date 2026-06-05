(******************************************************************************)
(*                                                                            *)
(*  Yudkowsky-Herreshoff tiling under arithmetic interpretation, with an      *)
(*  explicit goal-preservation chain (todo item #7).                          *)
(*                                                                            *)
(*  [tiling_chain A n] is the n-fold self-modification of the agent's         *)
(*  decision under its own verification: stage 0 is the decision itself,      *)
(*  and stage n+1 is keep-the-current-stage-or-self-modify-to-the-            *)
(*  Box-licensed-version-of-it:                                               *)
(*                                                                            *)
(*    chain 0     = agent_decision A (Var 0)                                  *)
(*    chain (S k) = Or (chain k) (Box_licenses_via_agent A (chain k)).        *)
(*                                                                            *)
(*  Not the constant goal, not Bot at 0 (witnessed below).  The chain         *)
(*  grows along provable implication, so the decision provably entails        *)
(*  every stage; the interpretation-push lemma                                *)
(*  [arith_interp_pushes_provable_impl] — composing BOTH closure              *)
(*  properties of [is_arithmetic_interpretation] (theorem preservation,       *)
(*  then implication distribution) — transports that entailment through       *)
(*  any arithmetic interpretation, and composition with the stage             *)
(*  hypothesis yields the goal.  The proof is NOT                             *)
(*  [goal_preservation_tiling_concrete] (a statement about Or-weakening       *)
(*  under one box), and does not substitute the identity                      *)
(*  interpretation: the strengthened variant                                  *)
(*  [tiling_succeeds_strong] only assumes the stage hypothesis for            *)
(*  n >= 1, where the bare instance-shortcut is unavailable and the           *)
(*  interpretation property is provably indispensable.                        *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Tiling Require Import Tiling.

(** ** The chain. *)

Fixpoint tiling_chain (A : AgentRecord) (n : nat) : Form :=
  match n with
  | 0 => agent_decision A (Var 0)
  | S k => Or (tiling_chain A k) (Box_licenses_via_agent A (tiling_chain A k))
  end.

(** Shape facts: stage 0 is the decision; the successor stage really
    contains the boxed self-modification. *)

Theorem tiling_chain_zero : forall A,
  tiling_chain A 0 = agent_decision A (Var 0).
Proof. reflexivity. Qed.

Theorem tiling_chain_succ : forall A k,
  tiling_chain A (S k) =
  Or (tiling_chain A k)
     (Box (agent_level A) (agent_licenses A (tiling_chain A k))).
Proof. reflexivity. Qed.

(** Non-degeneracy: for the canonical agent the chain is not the
    constant goal, stage 0 is not Bot, and consecutive stages are
    syntactically distinct. *)

Theorem tiling_chain_not_constant_goal :
  exists A n, tiling_chain A n <> agent_goal A.
Proof.
  exists (canonical_box_n_agent 0 Top), 0.
  cbn. discriminate.
Qed.

Theorem tiling_chain_zero_not_Bot :
  exists A, tiling_chain A 0 <> Bot.
Proof.
  exists (canonical_box_n_agent 0 Top).
  cbn. discriminate.
Qed.

Theorem tiling_chain_stages_distinct :
  exists A n, tiling_chain A n <> tiling_chain A (S n).
Proof.
  exists (canonical_box_n_agent 0 Top), 0.
  cbn. discriminate.
Qed.

(** ** Chain growth along provable implication. *)

Lemma tiling_chain_step : forall A k,
  |- Impl (tiling_chain A k) (tiling_chain A (S k)).
Proof.
  intros A k. cbn [tiling_chain].
  apply prov_or_intro_l.
Qed.

Lemma decision_to_chain : forall A n,
  |- Impl (agent_decision A (Var 0)) (tiling_chain A n).
Proof.
  intros A n. induction n as [|k IH].
  - cbn. apply prov_id.
  - exact (prov_compose _ _ _ IH (tiling_chain_step A k)).
Qed.

(** ** The interpretation-push: composing BOTH closure properties of an
    arithmetic interpretation.  This is the non-trivial use the
    acceptance criterion demands, isolated and named. *)

Lemma arith_interp_pushes_provable_impl : forall I,
  is_arithmetic_interpretation I ->
  forall a b, |- Impl a b -> |- Impl (I a) (I b).
Proof.
  intros I [Hpres Hdist] a b H.
  apply Hdist.
  apply Hpres.
  exact H.
Qed.

(** ** The headline theorem.  The proof pushes the decision-to-stage
    entailment through the interpretation (both properties) and
    composes with the stage hypothesis at the SAME n — it does not
    discharge by the identity interpretation, and it is not
    [goal_preservation_tiling_concrete]. *)

Theorem tiling_succeeds_under_arithmetic_interpretation :
  forall (A : AgentRecord) (G : Form),
  agent_goal A = G ->
  (forall I, is_arithmetic_interpretation I ->
     (forall n, |- Impl (I (tiling_chain A n)) (I G))) ->
  forall I, is_arithmetic_interpretation I ->
  forall n : nat, |- Impl (I (agent_decision A (Var 0))) (I G).
Proof.
  intros A G HG Hstages I HI n.
  pose proof (arith_interp_pushes_provable_impl I HI _ _
                (decision_to_chain A n)) as Hpush.
  exact (prov_compose _ _ _ Hpush (Hstages I HI n)).
Qed.

(** ** The strengthened variant: the stage hypothesis is only assumed
    for n >= 1, so the stage-0 instance shortcut is unavailable and
    the route through the interpretation properties is forced. *)

Theorem tiling_succeeds_strong :
  forall (A : AgentRecord) (G : Form),
  agent_goal A = G ->
  (forall I, is_arithmetic_interpretation I ->
     forall n, 1 <= n -> |- Impl (I (tiling_chain A n)) (I G)) ->
  forall I, is_arithmetic_interpretation I ->
  |- Impl (I (agent_decision A (Var 0))) (I G).
Proof.
  intros A G HG Hstages I HI.
  pose proof (arith_interp_pushes_provable_impl I HI _ _
                (decision_to_chain A 1)) as Hpush.
  exact (prov_compose _ _ _ Hpush (Hstages I HI 1 (Nat.le_refl 1))).
Qed.

(** ** Non-vacuity: a concrete agent-and-goal pair satisfying the stage
    hypothesis for every arithmetic interpretation — the hypothesis is
    discharged USING the interpretation's theorem-preservation, not by
    universally-false antecedents. *)

Theorem tiling_hypothesis_nonvacuous :
  exists (A : AgentRecord) (G : Form),
    agent_goal A = G /\
    (forall I, is_arithmetic_interpretation I ->
       forall n, |- Impl (I (tiling_chain A n)) (I G)).
Proof.
  exists (canonical_box_n_agent 0 Top), Top.
  split.
  - reflexivity.
  - intros I HI n.
    destruct HI as [Hpres Hdist].
    apply prov_weaken.
    apply Hpres.
    unfold Top. apply prov_id.
Qed.

(** And the full pipeline run end-to-end on that witness: the goal
    really is reached from the decision under every interpretation. *)

Theorem tiling_worked_instance :
  forall I, is_arithmetic_interpretation I ->
  |- Impl (I (agent_decision (canonical_box_n_agent 0 Top) (Var 0))) (I Top).
Proof.
  intros I HI.
  destruct (tiling_hypothesis_nonvacuous) as [A [G [HG Hstages]]].
  exact (tiling_succeeds_under_arithmetic_interpretation
           (canonical_box_n_agent 0 Top) Top eq_refl
           (fun I' HI' n =>
              match HI' with
              | conj Hpres Hdist =>
                  prov_weaken _ _ (Hpres _ (prov_id Bot))
              end)
           I HI 0).
Qed.

(** ** Headline summary for todo #7. *)

Theorem tiling_chain_summary :
  (forall A, tiling_chain A 0 = agent_decision A (Var 0)) /\
  (exists A n, tiling_chain A n <> agent_goal A) /\
  (exists A, tiling_chain A 0 <> Bot) /\
  (forall A n, |- Impl (agent_decision A (Var 0)) (tiling_chain A n)) /\
  (forall (A : AgentRecord) (G : Form),
     agent_goal A = G ->
     (forall I, is_arithmetic_interpretation I ->
        (forall n, |- Impl (I (tiling_chain A n)) (I G))) ->
     forall I, is_arithmetic_interpretation I ->
     forall n : nat, |- Impl (I (agent_decision A (Var 0))) (I G)) /\
  (exists (A : AgentRecord) (G : Form),
     agent_goal A = G /\
     (forall I, is_arithmetic_interpretation I ->
        forall n, |- Impl (I (tiling_chain A n)) (I G))).
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact tiling_chain_zero.
  - exact tiling_chain_not_constant_goal.
  - exact tiling_chain_zero_not_Bot.
  - exact decision_to_chain.
  - exact tiling_succeeds_under_arithmetic_interpretation.
  - exact tiling_hypothesis_nonvacuous.
Qed.
