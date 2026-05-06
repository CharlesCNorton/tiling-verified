(******************************************************************************)
(*                                                                            *)
(*  Decidability infrastructure for full GLP*.                                *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Import ListNotations.
From Tiling Require Import Tiling.

Fixpoint form_length (phi : Form) : nat :=
  match phi with
  | Var _ => 1
  | Bot => 1
  | Impl X Y => S (form_length X + form_length Y)
  | Box _ psi => S (form_length psi)
  end.

Lemma form_length_pos : forall phi, form_length phi >= 1.
Proof. intro phi. destruct phi; cbn; lia. Qed.

(** ** Closed box-free [forces_fnat_closed] equals [eval]. *)

Lemma forces_fnat_closed_box_free_eq_eval : forall phi,
  free_vars phi = [] -> box_free phi ->
  forall w val, forces_fnat_closed phi w = eval val phi.
Proof.
  intro phi. induction phi as [k | | X IHX Y IHY | n psi IHpsi];
    intros Hcl Hbf w val; cbn in *.
  - discriminate Hcl.
  - reflexivity.
  - apply app_eq_nil in Hcl. destruct Hcl as [HclX HclY].
    destruct Hbf as [HbfX HbfY].
    rewrite (IHX HclX HbfX w val), (IHY HclY HbfY w val). reflexivity.
  - exfalso. exact Hbf.
Qed.

(** ** Closed box-free FMP. *)

Theorem closed_box_free_FMP : forall phi,
  free_vars phi = [] -> box_free phi ->
  ((forall w, forces_fnat_closed phi w = true) <-> |- phi).
Proof.
  intros phi Hcl Hbf. split.
  - intros Hall. apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
    intro val.
    rewrite <- (forces_fnat_closed_box_free_eq_eval phi Hcl Hbf 0 val).
    exact (Hall 0).
  - intros Hp w. exact (provable_implies_forces_fnat_closed phi w Hcl Hp).
Qed.

Definition glp_decide_closed_box_free (phi : Form)
  (Hcl : free_vars phi = []) (Hbf : box_free phi) :
  sumbool (|- phi) (~ |- phi).
Proof.
  destruct (decide_tautology phi) eqn:Eq.
  - left. apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
    apply decide_tautology_correct. exact Eq.
  - right. intro Hp.
    pose proof (provable_classically_valid phi Hp) as Hcv.
    pose proof (decide_tautology_complete phi Hcv) as Heq.
    rewrite Eq in Heq. discriminate.
Defined.

(** ** Iterated boxes. *)

Lemma iter_box_closed : forall ns psi,
  free_vars psi = [] -> free_vars (iter_box ns psi) = [].
Proof.
  intro ns. induction ns as [|n rest IH]; intros psi Hcl; cbn.
  - exact Hcl.
  - exact (IH psi Hcl).
Qed.

Lemma provable_iter_box_intro : forall ns psi,
  |- psi -> |- iter_box ns psi.
Proof.
  intro ns. induction ns as [|n rest IH]; intros psi Hp; cbn.
  - exact Hp.
  - exact (Nec n _ (IH psi Hp)).
Qed.

(** [forces_fnat_closed (iter_box ns psi) v = true] uniformly when [eval val psi = true]. *)

Lemma forces_iter_box_eval_true_uniform : forall ns psi val,
  free_vars psi = [] -> box_free psi -> eval val psi = true ->
  forall v, forces_fnat_closed (iter_box ns psi) v = true.
Proof.
  intro ns. induction ns as [|n rest IH]; intros psi val Hcl Hbf Heval v; cbn.
  - rewrite (forces_fnat_closed_box_free_eq_eval psi Hcl Hbf v val). exact Heval.
  - apply forallb_forall. intros u _.
    exact (IH psi val Hcl Hbf Heval u).
Qed.

Fixpoint bad_world (ns : list nat) : nat :=
  match ns with
  | [] => 0
  | n :: rest => S (Nat.max n (bad_world rest))
  end.

Lemma forces_iter_box_at_bad_world : forall ns psi val,
  free_vars psi = [] -> box_free psi ->
  forall v, v >= bad_world ns ->
  forces_fnat_closed (iter_box ns psi) v = eval val psi.
Proof.
  intro ns. induction ns as [|n rest IH]; intros psi val Hcl Hbf v Hv.
  - cbn. exact (forces_fnat_closed_box_free_eq_eval psi Hcl Hbf v val).
  - destruct (eval val psi) eqn:Eeval.
    + exact (forces_iter_box_eval_true_uniform (n :: rest) psi val Hcl Hbf Eeval v).
    + cbn [iter_box bad_world] in *. cbn [forces_fnat_closed].
      destruct (forallb _ _) eqn:Efb; [|reflexivity].
      exfalso. rewrite forallb_forall in Efb.
      assert (Hin : In (v - 1) (seq n (v - n))).
      { apply in_seq. lia. }
      pose proof (Efb (v - 1) Hin) as Hf.
      assert (Hbnd : v - 1 >= bad_world rest) by lia.
      pose proof (IH psi val Hcl Hbf (v - 1) Hbnd) as Hihv.
      rewrite Hihv in Hf. rewrite Eeval in Hf. discriminate.
Qed.

(** ** Iter-box closed-box-free FMP / decidability. *)

Theorem provable_iter_box_box_free_iff : forall ns psi,
  free_vars psi = [] -> box_free psi ->
  (|- iter_box ns psi) <-> (|- psi).
Proof.
  intros ns psi Hcl Hbf. split.
  - intros Hp.
    apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
    intro val.
    pose proof (provable_implies_forces_fnat_closed (iter_box ns psi)
                  (bad_world ns) (iter_box_closed ns psi Hcl) Hp) as Hf.
    rewrite (forces_iter_box_at_bad_world ns psi val Hcl Hbf
               (bad_world ns) (Nat.le_refl _)) in Hf.
    exact Hf.
  - exact (provable_iter_box_intro ns psi).
Qed.

Definition glp_decide_iter_box_closed_box_free (ns : list nat) (psi : Form)
  (Hcl : free_vars psi = []) (Hbf : box_free psi) :
  sumbool (|- iter_box ns psi) (~ |- iter_box ns psi).
Proof.
  destruct (glp_decide_closed_box_free psi Hcl Hbf) as [Hp | Hnp].
  - left. exact (provable_iter_box_intro ns psi Hp).
  - right. intro Habs. apply Hnp.
    exact (proj1 (provable_iter_box_box_free_iff ns psi Hcl Hbf) Habs).
Defined.
