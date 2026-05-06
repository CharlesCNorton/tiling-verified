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

(** ** Carlson-generalised unprovability of [Neg (Box n X)] for any closed [X].
    Carlson's polymodal second-incompleteness corresponds to [X = Bot]; the
    same Fnat-at-world-0 argument refutes [|- Neg (Box n X)] for arbitrary
    closed [X], because [forces_fnat_closed (Box n X) 0] is vacuously [true]. *)

Theorem closed_neg_box_unprovable : forall n X,
  free_vars X = [] -> ~ |- Neg (Box n X).
Proof.
  intros n X Hcl Hp.
  assert (Hclneg : free_vars (Neg (Box n X)) = []).
  { unfold Neg. cbn. rewrite app_nil_r. exact Hcl. }
  pose proof (provable_implies_forces_fnat_closed (Neg (Box n X)) 0 Hclneg Hp) as Hf.
  cbn in Hf. discriminate.
Qed.

(** ** Decidability of [Neg (Box n X)] for closed [X]: always [right]. *)

Definition glp_decide_neg_box_closed (n : nat) (X : Form)
  (Hcl : free_vars X = []) :
  sumbool (|- Neg (Box n X)) (~ |- Neg (Box n X)).
Proof.
  right. exact (closed_neg_box_unprovable n X Hcl).
Defined.

(** ** Decidability composition for And: combine two decidability results. *)

Definition glp_decide_and (phi psi : Form)
  (Dphi : sumbool (|- phi) (~ |- phi))
  (Dpsi : sumbool (|- psi) (~ |- psi)) :
  sumbool (|- And phi psi) (~ |- And phi psi).
Proof.
  destruct Dphi as [Hphi | Hphi]; destruct Dpsi as [Hpsi | Hpsi].
  - left. exact (prov_and_intro_meta phi psi Hphi Hpsi).
  - right. intro Hand. apply Hpsi. exact (prov_and_elim_r_meta phi psi Hand).
  - right. intro Hand. apply Hphi. exact (prov_and_elim_l_meta phi psi Hand).
  - right. intro Hand. apply Hphi. exact (prov_and_elim_l_meta phi psi Hand).
Defined.

(** ** Decidability composition for Iff: both directions decidable. *)

Definition glp_decide_iff (phi psi : Form)
  (Dfwd : sumbool (|- Impl phi psi) (~ |- Impl phi psi))
  (Dbwd : sumbool (|- Impl psi phi) (~ |- Impl psi phi)) :
  sumbool (|- Iff phi psi) (~ |- Iff phi psi).
Proof.
  unfold Iff. exact (glp_decide_and (Impl phi psi) (Impl psi phi) Dfwd Dbwd).
Defined.

(** ** Decidability of [Impl phi psi] when the consequent is provable. *)

Definition glp_decide_impl_consequent_provable (phi psi : Form)
  (Hpsi : |- psi) :
  sumbool (|- Impl phi psi) (~ |- Impl phi psi).
Proof.
  left. exact (MP _ _ (Ax_K psi phi) Hpsi).
Defined.

(** ** Decidability of [Impl phi psi] when the antecedent is provable
    and the consequent's provability status is decidable. *)

Definition glp_decide_impl_antecedent_provable (phi psi : Form)
  (Hphi : |- phi)
  (Dpsi : sumbool (|- psi) (~ |- psi)) :
  sumbool (|- Impl phi psi) (~ |- Impl phi psi).
Proof.
  destruct Dpsi as [Hpsi | Hnpsi].
  - left. exact (MP _ _ (Ax_K psi phi) Hpsi).
  - right. intro Himp. apply Hnpsi. exact (MP _ _ Himp Hphi).
Defined.

(** ** Decidability for [Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2)]
    when [psi_2] is provable: the consequent is provable, so the implication
    is provable by [Ax_K]. *)

Definition glp_decide_impl_iter_box_via_consequent_provable
  (ns_1 ns_2 : list nat) (psi_1 psi_2 : Form)
  (Hp_2 : |- psi_2) :
  sumbool (|- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2))
          (~ |- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2)).
Proof.
  left.
  exact (MP _ _ (Ax_K _ (iter_box ns_1 psi_1))
                (provable_iter_box_intro ns_2 psi_2 Hp_2)).
Defined.

(** ** Decidability for [Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2)]
    when [psi_1] is provable but [psi_2] is not (with [psi_2] closed
    box-free): the antecedent is provable and consequent is not, so
    the implication cannot be provable (would yield [|- iter_box ns_2 psi_2]
    via MP, contradicting [~ |- psi_2] under [provable_iter_box_box_free_iff]). *)

Definition glp_decide_impl_iter_box_via_antecedent_provable_consequent_not
  (ns_1 ns_2 : list nat) (psi_1 psi_2 : Form)
  (Hcl_2 : free_vars psi_2 = []) (Hbf_2 : box_free psi_2)
  (Hp_1 : |- psi_1) (Hnp_2 : ~ |- psi_2) :
  sumbool (|- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2))
          (~ |- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2)).
Proof.
  right. intro Himp. apply Hnp_2.
  apply (proj1 (provable_iter_box_box_free_iff ns_2 psi_2 Hcl_2 Hbf_2)).
  apply (MP _ _ Himp).
  exact (provable_iter_box_intro ns_1 psi_1 Hp_1).
Defined.

(** ** [And] of two iterated-box closed-box-free formulas: provable iff both
    inner formulas are classically valid. *)

Definition glp_decide_and_iter_box_box_free
  (ns_1 ns_2 : list nat) (psi_1 psi_2 : Form)
  (Hcl_1 : free_vars psi_1 = []) (Hbf_1 : box_free psi_1)
  (Hcl_2 : free_vars psi_2 = []) (Hbf_2 : box_free psi_2) :
  sumbool (|- And (iter_box ns_1 psi_1) (iter_box ns_2 psi_2))
          (~ |- And (iter_box ns_1 psi_1) (iter_box ns_2 psi_2)).
Proof.
  apply glp_decide_and.
  - exact (glp_decide_iter_box_closed_box_free ns_1 psi_1 Hcl_1 Hbf_1).
  - exact (glp_decide_iter_box_closed_box_free ns_2 psi_2 Hcl_2 Hbf_2).
Defined.

(** ** [Iff] of two iterated-box closed-box-free formulas: each direction
    is decidable when one of the cases (valid consequent, or
    valid antecedent + invalid consequent) applies. *)

(** ** [forces_fnat_closed (Box k Bot)] reduces to [Nat.leb w k]. *)

Lemma forces_box_bot_eq_leb : forall k w,
  forces_fnat_closed (Box k Bot) w = Nat.leb w k.
Proof.
  intros k w. cbn.
  destruct (Nat.leb w k) eqn:Eq.
  - apply Nat.leb_le in Eq.
    assert (Hempty : seq k (w - k) = []).
    { assert (w - k = 0) by lia. rewrite H. reflexivity. }
    rewrite Hempty. reflexivity.
  - apply Nat.leb_nle in Eq.
    destruct (forallb _ _) eqn:Efb; [|reflexivity].
    rewrite forallb_forall in Efb.
    assert (Hin : In k (seq k (w - k))).
    { apply in_seq. lia. }
    pose proof (Efb k Hin) as H. cbn in H. discriminate.
Qed.

(** ** [Impl (Box k_1 Bot) (Box k_2 Bot)] decidable: provable iff [k_1 <= k_2]. *)

Lemma decide_impl_box_bot_box_bot_le : forall k_1 k_2,
  k_1 <= k_2 -> |- Impl (Box k_1 Bot) (Box k_2 Bot).
Proof.
  intros k_1 k_2 Hle. exact (prov_box_mon_le k_1 k_2 Bot Hle).
Qed.

Lemma decide_impl_box_bot_box_bot_gt : forall k_1 k_2,
  k_1 > k_2 -> ~ |- Impl (Box k_1 Bot) (Box k_2 Bot).
Proof.
  intros k_1 k_2 Hgt Hp.
  pose proof (soundness _ Hp Fnat (fun _ _ => true) (S k_2)) as Hf.
  cbn in Hf.
  assert (Hk1 : forall v, Fnat_R k_1 (S k_2) v -> False).
  { intros v Hr. unfold Fnat_R in Hr. lia. }
  apply (Hf (fun v Hr => False_ind _ (Hk1 v Hr)) k_2).
  unfold Fnat_R. split; lia.
Qed.

Definition glp_decide_impl_box_bot_box_bot (k_1 k_2 : nat) :
  sumbool (|- Impl (Box k_1 Bot) (Box k_2 Bot))
          (~ |- Impl (Box k_1 Bot) (Box k_2 Bot)).
Proof.
  destruct (le_gt_dec k_1 k_2) as [Hle | Hgt].
  - left. exact (decide_impl_box_bot_box_bot_le k_1 k_2 Hle).
  - right. exact (decide_impl_box_bot_box_bot_gt k_1 k_2 Hgt).
Defined.

(** ** Eval of closed box-free formulas is independent of the valuation. *)

Lemma eval_box_free_closed_const : forall phi val_1 val_2,
  free_vars phi = [] -> box_free phi ->
  eval val_1 phi = eval val_2 phi.
Proof.
  intros phi val_1 val_2 Hcl Hbf.
  rewrite <- (forces_fnat_closed_box_free_eq_eval phi Hcl Hbf 0 val_1).
  rewrite <- (forces_fnat_closed_box_free_eq_eval phi Hcl Hbf 0 val_2).
  reflexivity.
Qed.

(** ** Decidability of [Impl (Box k_1 psi) (Box k_2 psi)] for closed box-free
    [psi].  Provable iff [|- psi] OR [k_1 <= k_2]; refuted by Fnat-soundness
    when [psi] is unprovable and [k_1 > k_2]. *)

Definition glp_decide_impl_box_box_box_free_same_psi
  (k_1 k_2 : nat) (psi : Form)
  (Hcl : free_vars psi = []) (Hbf : box_free psi) :
  sumbool (|- Impl (Box k_1 psi) (Box k_2 psi))
          (~ |- Impl (Box k_1 psi) (Box k_2 psi)).
Proof.
  destruct (glp_decide_closed_box_free psi Hcl Hbf) as [Hp | Hnp].
  - left. exact (MP _ _ (Ax_K (Box k_2 psi) (Box k_1 psi)) (Nec k_2 psi Hp)).
  - destruct (le_gt_dec k_1 k_2) as [Hle | Hgt].
    + left. exact (prov_box_mon_le k_1 k_2 psi Hle).
    + right. intro Himp.
      pose proof (soundness _ Himp Fnat (fun _ _ => true) (S k_2)) as Hf.
      cbn in Hf.
      assert (Hbox1 : forall v, Fnat_R k_1 (S k_2) v ->
                       forces Fnat (fun _ _ => true) v psi).
      { intros v Hr. unfold Fnat_R in Hr. lia. }
      pose proof (Hf Hbox1) as Hbox2.
      assert (Hr : Fnat_R k_2 (S k_2) k_2) by (unfold Fnat_R; split; lia).
      pose proof (Hbox2 k_2 Hr) as Hpsi_at_k2.
      apply Hnp.
      apply trivial_in_provable.
      apply prop_completeness; [exact Hbf|].
      intro val.
      apply (proj1 (forces_const_box_free Fnat (fun _ : nat => true) k_2 psi Hbf))
        in Hpsi_at_k2.
      pose proof (eval_box_free_closed_const psi val (fun _ => true) Hcl Hbf) as Heq.
      rewrite Heq. exact Hpsi_at_k2.
Defined.
