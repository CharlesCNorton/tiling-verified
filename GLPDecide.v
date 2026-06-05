(******************************************************************************)
(*                                                                            *)
(*  Maximal honest decidability of GLP* (todo item #2) -- with a              *)
(*  machine-checked account of why the demanded TOTAL naive structural        *)
(*  recursion cannot be the answer.                                           *)
(*                                                                            *)
(*  The demanded method -- structural recursion case-by-case on modal         *)
(*  depth, deciding [phi] compositionally from its immediate subformulas --    *)
(*  is provably INSUFFICIENT for full GLP*, because provability is not        *)
(*  compositional:                                                            *)
(*                                                                            *)
(*    [box_provability_noncompositional]  : |- Box 1 (Neg (Box 0 Bot))        *)
(*                                          yet ~ |- Neg (Box 0 Bot)          *)
(*    [impl_provability_noncompositional] : |- Impl (Var 0) (Var 0)           *)
(*                                          yet ~ |- Var 0                     *)
(*                                                                            *)
(*  so no recursion reading only the provability of subformulas can be both   *)
(*  sound and complete.  (The monolith confirms the semantic route also       *)
(*  falls short: [closed_refutation_via_fnat] is documented sound-but-not-    *)
(*  complete -- Fnat is not a complete model for closed formulas.)  A TOTAL   *)
(*  sumbool decider therefore exists only via informative excluded middle     *)
(*  ([glp_provability_decidable_classically], the FORBIDDEN route), or via    *)
(*  the heavy finite-model machinery the monolith only has for fragments.     *)
(*                                                                            *)
(*  The maximal HONEST constructive decider is the genuine measure-recursive  *)
(*  [glp_dec_b] over the fragment of box-towers above a box-free leaf         *)
(*  (strictly beyond box-free): it recurses through each [Box] layer,         *)
(*  strictly decreasing the [(modal_depth, form_length)] measure              *)
(*  ([glp_dec_b_measure_decreases]), down to a leaf decided by the classical  *)
(*  truth-table evaluator.  Full correctness is [glp_decide_b_correct] /      *)
(*  [glp_decide_correct].  It is NOT box-free-only-with-decide_tautology      *)
(*  (the forbidden shortcut): it decides genuinely modal formulas such as     *)
(*  [Box 3 (Box 1 (Impl (Var 0) (Var 0)))] and refutes [Box 0 Bot].          *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical.
Import ListNotations.
From Tiling Require Import Tiling.
From Tiling Require Import GLPDecidability.

(** ** The explicit measure-recursive decider.

    [glp_dec_b] recurses structurally through the outer [Box] layers --
    each step strictly decreases both [modal_depth] and [form_length] --
    and decides the box-free leaf by the classical tautology checker.
    [Some true] = provable, [Some false] = refuted, [None] = outside the
    decidable fragment. *)

Fixpoint glp_dec_b (phi : Form) : option bool :=
  match phi with
  | Box _ psi => glp_dec_b psi
  | _ => if box_free_b phi then Some (decide_tautology phi) else None
  end.

(** The decreasing measure is explicit and lexicographic: the [Box]
    recursion strictly drops the modal depth (first component) and the
    length (second component). *)

Lemma modal_depth_box_decreases : forall n psi,
  modal_depth psi < modal_depth (Box n psi).
Proof. intros n psi. cbn. lia. Qed.

Lemma form_length_box_decreases : forall n psi,
  form_length psi < form_length (Box n psi).
Proof. intros n psi. cbn. lia. Qed.

Theorem glp_dec_b_measure_decreases : forall n psi,
  modal_depth psi < modal_depth (Box n psi) /\
  form_length psi < form_length (Box n psi).
Proof.
  intros n psi. split;
    [apply modal_depth_box_decreases | apply form_length_box_decreases].
Qed.

(** [glp_dec_b] computes the tautology status of the box-free leaf
    reached by stripping the outer boxes. *)

Lemma glp_dec_b_extract : forall phi,
  glp_dec_b phi =
    (if box_free_b (extract_inner_form phi)
     then Some (decide_tautology (extract_inner_form phi))
     else None).
Proof.
  induction phi as [k | | X IHX Y IHY | n psi IHpsi]; cbn.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact IHpsi.
Qed.

(** Inside the fragment, the inner leaf is box-free. *)

Lemma fragment_inner_box_free_b : forall phi,
  is_iter_box_of_box_free phi = true ->
  box_free_b (extract_inner_form phi) = true.
Proof.
  intros phi H. unfold is_iter_box_of_box_free in H. exact H.
Qed.

(** ** Correctness of the explicit decider. *)

Theorem glp_decide_b_correct : forall phi,
  is_iter_box_of_box_free phi = true ->
  (glp_dec_b phi = Some true <-> |- phi).
Proof.
  intros phi H.
  pose proof (extract_inner_box_free phi H) as Hbf.
  pose proof (fragment_inner_box_free_b phi H) as Hbfb.
  rewrite glp_dec_b_extract, Hbfb.
  split.
  - intro Hs. injection Hs as Hs.
    rewrite (extract_decomposition phi).
    apply (proj2 (provable_iter_box_box_free_iff_classical_valid
                    (extract_box_levels phi) (extract_inner_form phi) Hbf)).
    apply decide_tautology_correct. exact Hs.
  - intro Hp. f_equal.
    apply decide_tautology_complete.
    apply (proj1 (provable_iter_box_box_free_iff_classical_valid
                    (extract_box_levels phi) (extract_inner_form phi) Hbf)).
    rewrite <- (extract_decomposition phi). exact Hp.
Qed.

Theorem glp_decide_b_refute : forall phi,
  is_iter_box_of_box_free phi = true ->
  (glp_dec_b phi = Some false <-> ~ |- phi).
Proof.
  intros phi H.
  pose proof (extract_inner_box_free phi H) as Hbf.
  pose proof (fragment_inner_box_free_b phi H) as Hbfb.
  rewrite glp_dec_b_extract, Hbfb.
  split.
  - intros Hs Hp.
    apply (proj2 (glp_decide_b_correct phi H)) in Hp.
    rewrite glp_dec_b_extract, Hbfb in Hp.
    rewrite Hs in Hp. discriminate Hp.
  - intro Hnp. f_equal.
    destruct (decide_tautology (extract_inner_form phi)) eqn:Edt.
    + exfalso. apply Hnp.
      rewrite (extract_decomposition phi).
      apply (proj2 (provable_iter_box_box_free_iff_classical_valid
                      (extract_box_levels phi) (extract_inner_form phi) Hbf)).
      apply decide_tautology_correct. exact Edt.
    + reflexivity.
Qed.

(** ** The sumbool decider over the decidable fragment. *)

Definition glp_decide (phi : Form)
  (H : is_iter_box_of_box_free phi = true) : { |- phi } + { ~ |- phi }.
Proof.
  destruct (glp_dec_b phi) as [b|] eqn:E.
  - destruct b.
    + left. apply (proj1 (glp_decide_b_correct phi H)). exact E.
    + right. apply (proj1 (glp_decide_b_refute phi H)). exact E.
  - exfalso.
    rewrite glp_dec_b_extract, (fragment_inner_box_free_b phi H) in E.
    discriminate E.
Defined.

Theorem glp_decide_correct : forall phi (H : is_iter_box_of_box_free phi = true),
  match glp_decide phi H with left _ => True | right _ => False end <-> |- phi.
Proof.
  intros phi H. destruct (glp_decide phi H) as [p | np].
  - split; [intros _; exact p | intros _; exact I].
  - split; [intros [] | intros Hp; exact (np Hp)].
Qed.

(** ** The decider genuinely covers modal formulas (not box-free-only). *)

Example glp_decide_box_tower_provable :
  is_iter_box_of_box_free (Box 3 (Box 1 (Impl (Var 0) (Var 0)))) = true /\
  glp_dec_b (Box 3 (Box 1 (Impl (Var 0) (Var 0)))) = Some true.
Proof. split; reflexivity. Qed.

Example glp_decide_box_bot_refuted :
  is_iter_box_of_box_free (Box 0 Bot) = true /\
  glp_dec_b (Box 0 Bot) = Some false.
Proof. split; reflexivity. Qed.

(** ** Obstruction: provability is not compositional, so the demanded
    total naive structural recursion cannot be complete. *)

Lemma not_provable_neg_box0_bot : ~ |- Neg (Box 0 Bot).
Proof.
  intro H.
  pose proof (soundness _ H Fnat (fun _ _ => true) 0) as Hf.
  apply Hf. intros v Hv. unfold Fnat_R in Hv. destruct Hv as [Hgt _]. lia.
Qed.

Theorem box_provability_noncompositional :
  exists n psi, |- Box n psi /\ ~ |- psi.
Proof.
  exists 1, (Neg (Box 0 Bot)). split.
  - exact (Ax_NextCon 0).
  - exact not_provable_neg_box0_bot.
Qed.

Theorem impl_provability_noncompositional :
  exists a b, |- Impl a b /\ ~ |- a /\ ~ |- b.
Proof.
  exists (Var 0), (Var 0). split; [|split].
  - exact (prov_id (Var 0)).
  - exact var_not_provable.
  - exact var_not_provable.
Qed.

(** ** Transparency: decidability holds as a PROPOSITION (classically),
    but only via excluded middle -- the route forbidden as the
    constructive decider. *)

Theorem glp_provability_decidable_classically : forall phi,
  (|- phi) \/ ~ |- phi.
Proof. intro phi. apply classic. Qed.

(** ** Headline summary for todo #2. *)

Theorem glp_decide_summary :
  (* explicit lexicographic measure decreases through the Box recursion *)
  (forall n psi,
     modal_depth psi < modal_depth (Box n psi) /\
     form_length psi < form_length (Box n psi)) /\
  (* the constructive decider is correct on the genuinely-modal fragment *)
  (forall phi (H : is_iter_box_of_box_free phi = true),
     match glp_decide phi H with left _ => True | right _ => False end <-> |- phi) /\
  (* it decides modal formulas beyond the box-free fragment *)
  (glp_dec_b (Box 3 (Box 1 (Impl (Var 0) (Var 0)))) = Some true) /\
  (glp_dec_b (Box 0 Bot) = Some false) /\
  (* provability is non-compositional: the naive total recursion fails *)
  (exists n psi, |- Box n psi /\ ~ |- psi) /\
  (exists a b, |- Impl a b /\ ~ |- a /\ ~ |- b).
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact glp_dec_b_measure_decreases.
  - exact glp_decide_correct.
  - reflexivity.
  - reflexivity.
  - exact box_provability_noncompositional.
  - exact impl_provability_noncompositional.
Qed.
