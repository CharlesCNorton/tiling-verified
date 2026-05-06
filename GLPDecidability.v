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

(** ** For closed box-free [psi], unprovability implies provability of [Neg psi]. *)

Lemma not_provable_implies_provable_neg_closed_box_free : forall psi,
  free_vars psi = [] -> box_free psi -> ~ |- psi -> |- Neg psi.
Proof.
  intros psi Hcl Hbf Hnp.
  apply trivial_in_provable. apply prop_completeness.
  - cbn. split; [exact Hbf | exact I].
  - intro val. cbn.
    destruct (eval val psi) eqn:E.
    + exfalso. apply Hnp.
      apply trivial_in_provable.
      apply prop_completeness; [exact Hbf|].
      intro val'.
      pose proof (eval_box_free_closed_const psi val' val Hcl Hbf) as Heq.
      rewrite Heq. exact E.
    + reflexivity.
Qed.

(** ** When [|- Neg psi], [Box k psi] is provably equivalent to [Box k Bot]. *)

Lemma box_psi_iff_box_bot_when_neg_provable : forall k psi,
  |- Neg psi -> |- Iff (Box k psi) (Box k Bot).
Proof.
  intros k psi Hneg.
  apply prov_iff_intro.
  - exact (MP _ _ (Ax_BoxK k psi Bot) (Nec k _ Hneg)).
  - exact (MP _ _ (Ax_BoxK k Bot psi) (Nec k _ (prov_explosion psi))).
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

(** ** When [psi] is closed box-free and classically refutable, the iterated
    box [iter_box ns psi] forces in Fnat at exactly the worlds [v < bad_world ns]. *)

Lemma forces_iter_box_below_bad_world : forall ns psi val,
  free_vars psi = [] -> box_free psi -> eval val psi = false ->
  forall v, v < bad_world ns ->
  forces_fnat_closed (iter_box ns psi) v = true.
Proof.
  intro ns. induction ns as [|n rest IH]; intros psi val Hcl Hbf Heval v Hv.
  - cbn in Hv. lia.
  - cbn [iter_box bad_world] in *.
    cbn [forces_fnat_closed].
    apply forallb_forall. intros u Hu.
    apply in_seq in Hu. destruct Hu as [Hun Huv].
    apply (IH psi val Hcl Hbf Heval).
    lia.
Qed.

(** ** [forces_fnat_closed (iter_box ns Bot) v = true] iff [v < bad_world ns]. *)

Lemma forces_iter_box_bot_eq_ltb : forall ns v,
  forces_fnat_closed (iter_box ns Bot) v = Nat.ltb v (bad_world ns).
Proof.
  intros ns v.
  destruct (Nat.ltb v (bad_world ns)) eqn:Eq.
  - apply Nat.ltb_lt in Eq.
    apply (forces_iter_box_below_bad_world ns Bot (fun _ => false) eq_refl I eq_refl v Eq).
  - apply Nat.ltb_nlt in Eq.
    rewrite (forces_iter_box_at_bad_world ns Bot (fun _ => false) eq_refl I v); [|lia].
    reflexivity.
Qed.

(** ** Forward direction of the iter-box-Bot implication theorem:
    [|- (iter_box ns_1 Bot) -> (iter_box ns_2 Bot)] entails
    [bad_world ns_1 <= bad_world ns_2]. *)

Theorem provable_impl_iter_box_bot_forward : forall ns_1 ns_2,
  |- Impl (iter_box ns_1 Bot) (iter_box ns_2 Bot) ->
  bad_world ns_1 <= bad_world ns_2.
Proof.
  intros ns_1 ns_2 Hp.
  destruct (le_gt_dec (bad_world ns_1) (bad_world ns_2)) as [Hle | Hgt]; [exact Hle|].
  exfalso.
  assert (Hcl_impl : free_vars (Impl (iter_box ns_1 Bot) (iter_box ns_2 Bot)) = []).
  { cbn. rewrite (iter_box_closed ns_1 Bot eq_refl).
    exact (iter_box_closed ns_2 Bot eq_refl). }
  pose proof (provable_implies_forces_fnat_closed
                (Impl (iter_box ns_1 Bot) (iter_box ns_2 Bot))
                (bad_world ns_2) Hcl_impl Hp) as Hf.
  cbn [forces_fnat_closed] in Hf.
  rewrite forces_iter_box_bot_eq_ltb in Hf.
  rewrite forces_iter_box_bot_eq_ltb in Hf.
  assert (Hlt : Nat.ltb (bad_world ns_2) (bad_world ns_1) = true)
    by (apply Nat.ltb_lt; lia).
  assert (Hge : Nat.ltb (bad_world ns_2) (bad_world ns_2) = false)
    by (apply Nat.ltb_nlt; lia).
  rewrite Hlt, Hge in Hf. cbn in Hf. discriminate.
Qed.

(** ** Empty antecedent case is trivial via [Bot] explosion. *)

Lemma provable_impl_iter_box_bot_backward_empty : forall ns_2,
  |- Impl (iter_box [] Bot) (iter_box ns_2 Bot).
Proof.
  intros ns_2. cbn. exact (prov_explosion (iter_box ns_2 Bot)).
Qed.

(** ** Iterated [Mon] lift inside an iter-box wrapper. *)

Lemma provable_iter_box_mon_le : forall n m psi,
  n <= m -> |- Impl (iter_box [n] psi) (iter_box [m] psi).
Proof.
  intros n m psi Hle. cbn. exact (prov_box_mon_le n m psi Hle).
Qed.

(** ** Provable explosion under [Box]: if the inner antecedent is [Bot],
    the consequent of the box-implication can be anything at the same level. *)

Lemma prov_box_bot_to_box_anything : forall n psi,
  |- Impl (Box n Bot) (Box n psi).
Proof.
  intros n psi.
  pose proof (prov_explosion psi) as Hexp.
  pose proof (Nec n _ Hexp) as Hbox_exp.
  pose proof (Ax_BoxK n Bot psi) as HK.
  exact (MP _ _ HK Hbox_exp).
Qed.

(** ** Lifting [Box n Bot] to [Box m psi] when [n <= m]. *)

Lemma prov_box_bot_to_higher_box_anything : forall n m psi,
  n <= m -> |- Impl (Box n Bot) (Box m psi).
Proof.
  intros n m psi Hle.
  pose proof (prov_box_mon_le n m Bot Hle) as Hmon.
  pose proof (prov_box_bot_to_box_anything m psi) as Hexp.
  exact (prov_compose _ _ _ Hmon Hexp).
Qed.

(** ** Singleton-antecedent backward direction.  When the head of [ns_2]
    dominates [k], the entire iter-box-Bot implication is provable directly
    by [prov_box_bot_to_higher_box_anything].  This is a special case of the
    Beklemishev worm theorem, sufficient when the consequent worm absorbs
    the antecedent at its outermost layer. *)

Lemma provable_impl_box_bot_iter_box_bot_head_match :
  forall k m rest, k <= m ->
  |- Impl (Box k Bot) (iter_box (m :: rest) Bot).
Proof.
  intros k m rest Hle. cbn [iter_box].
  exact (prov_box_bot_to_higher_box_anything k m (iter_box rest Bot) Hle).
Qed.

(** ** Pointwise monotonicity for iter-box: if [ns_1] and [ns_2] have the
    same length and [ns_1[i] <= ns_2[i]] pointwise, the worm-implication
    follows from iterated [Mon] under [Nec]+[BoxK]. *)

Lemma prov_iter_box_pointwise_mon : forall ns_1 ns_2 psi,
  length ns_1 = length ns_2 ->
  (forall i, i < length ns_1 -> nth i ns_1 0 <= nth i ns_2 0) ->
  |- Impl (iter_box ns_1 psi) (iter_box ns_2 psi).
Proof.
  intro ns_1. induction ns_1 as [|n rest_1 IH]; intros ns_2 psi Hlen Hpt.
  - destruct ns_2 as [|m rest_2]; [|cbn in Hlen; discriminate Hlen].
    cbn. exact (prov_id psi).
  - destruct ns_2 as [|m rest_2]; [cbn in Hlen; discriminate Hlen|].
    cbn [length] in Hlen. injection Hlen as Hlen.
    assert (Hhead : n <= m).
    { apply (Hpt 0). cbn [length]. lia. }
    assert (Hrest_pt : forall i, i < length rest_1 -> nth i rest_1 0 <= nth i rest_2 0).
    { intros i Hi. apply (Hpt (S i)). cbn [length]. lia. }
    pose proof (IH rest_2 psi Hlen Hrest_pt) as Hinner.
    pose proof (Nec m _ Hinner) as Hboxed.
    pose proof (Ax_BoxK m (iter_box rest_1 psi) (iter_box rest_2 psi)) as HK.
    pose proof (MP _ _ HK Hboxed) as Hstep.
    pose proof (prov_box_mon_le n m (iter_box rest_1 psi) Hhead) as Hmon.
    cbn [iter_box].
    exact (prov_compose _ _ _ Hmon Hstep).
Qed.

(** ** Strengthening the inner formula under an iter-box wrapper.  Since
    [Bot] is the strongest closed antecedent, [|- iter_box ns Bot ->
    iter_box ns psi] for any [psi]: explosion at the leaf, lifted through
    the wrapper by [Nec] and [BoxK]. *)

Lemma prov_iter_box_inner_strengthen : forall ns psi,
  |- Impl (iter_box ns Bot) (iter_box ns psi).
Proof.
  intro ns. induction ns as [|n rest IH]; intro psi.
  - cbn. exact (prov_explosion psi).
  - cbn [iter_box].
    pose proof (IH psi) as Hinner.
    pose proof (Nec n _ Hinner) as Hboxed.
    pose proof (Ax_BoxK n (iter_box rest Bot) (iter_box rest psi)) as HK.
    exact (MP _ _ HK Hboxed).
Qed.

(** ** Worm-extension case.  Appending an extension to a worm preserves
    provability of the worm-implication: [|- iter_box ns Bot ->
    iter_box (ns ++ ext) Bot].  Follows from
    [iter_box (ns ++ ext) Bot = iter_box ns (iter_box ext Bot)] and
    [prov_iter_box_inner_strengthen]. *)

Lemma iter_box_app : forall ns_1 ns_2 psi,
  iter_box (ns_1 ++ ns_2) psi = iter_box ns_1 (iter_box ns_2 psi).
Proof.
  intro ns_1. induction ns_1 as [|n rest IH]; intros ns_2 psi.
  - cbn. reflexivity.
  - cbn [iter_box app]. rewrite IH. reflexivity.
Qed.

Lemma prov_iter_box_extension : forall ns ext,
  |- Impl (iter_box ns Bot) (iter_box (ns ++ ext) Bot).
Proof.
  intros ns ext. rewrite iter_box_app. exact (prov_iter_box_inner_strengthen ns (iter_box ext Bot)).
Qed.

(** ** Combined head-lift + worm-extension.  When [ns_1] is a "weakening"
    of a prefix of [ns_2] (both pointwise [<=] on the prefix and [ns_2] has
    additional boxes appended), the worm-implication is provable. *)

Lemma prov_iter_box_prefix_mon_extension : forall ns_1 prefix ext psi,
  length ns_1 = length prefix ->
  (forall i, i < length ns_1 -> nth i ns_1 0 <= nth i prefix 0) ->
  |- Impl (iter_box ns_1 Bot) (iter_box (prefix ++ ext) psi).
Proof.
  intros ns_1 prefix ext psi Hlen Hpt.
  pose proof (prov_iter_box_pointwise_mon ns_1 prefix Bot Hlen Hpt) as Hmon.
  rewrite iter_box_app.
  pose proof (prov_iter_box_inner_strengthen prefix (iter_box ext psi)) as Hstr.
  exact (prov_compose _ _ _ Hmon Hstr).
Qed.

(** ** Witness extraction from a [false] [forallb]. *)

Lemma forallb_false_witness : forall {A : Type} (f : A -> bool) (l : list A),
  forallb f l = false -> exists x, In x l /\ f x = false.
Proof.
  intros A f. induction l as [|x rest IH]; intro Hfb.
  - cbn in Hfb. discriminate Hfb.
  - cbn in Hfb. destruct (f x) eqn:Ef.
    + cbn in Hfb. destruct (IH Hfb) as [y [Hy_in Hy_f]].
      exists y. split; [right; exact Hy_in | exact Hy_f].
    + exists x. split; [left; reflexivity | exact Ef].
Qed.

(** ** Stabilization bound for closed [forces_fnat_closed].  Beyond [wbound
    phi], [forces_fnat_closed phi w] is constant (in [w]).  This gives a
    finite-window refutation: any closed Form refutable by [Fnat] is
    refutable by checking [w in [0, wbound phi]]. *)

Fixpoint wbound (phi : Form) : nat :=
  match phi with
  | Var _ => 0
  | Bot => 0
  | Impl X Y => Nat.max (wbound X) (wbound Y)
  | Box n psi => S (Nat.max n (wbound psi))
  end.

Lemma forces_fnat_closed_stabilizes : forall phi w_1 w_2,
  free_vars phi = [] ->
  w_1 >= wbound phi -> w_2 >= wbound phi ->
  forces_fnat_closed phi w_1 = forces_fnat_closed phi w_2.
Proof.
  intro phi.
  induction phi as [k | | X IHX Y IHY | n psi IHpsi];
    intros w_1 w_2 Hcl Hw1 Hw2.
  - cbn in Hcl. discriminate Hcl.
  - cbn. reflexivity.
  - cbn in Hcl. apply app_eq_nil in Hcl. destruct Hcl as [HclX HclY].
    cbn in Hw1, Hw2.
    assert (Hw1X : w_1 >= wbound X) by lia.
    assert (Hw1Y : w_1 >= wbound Y) by lia.
    assert (Hw2X : w_2 >= wbound X) by lia.
    assert (Hw2Y : w_2 >= wbound Y) by lia.
    cbn. rewrite (IHX w_1 w_2 HclX Hw1X Hw2X), (IHY w_1 w_2 HclY Hw1Y Hw2Y).
    reflexivity.
  - cbn in Hcl. cbn in Hw1, Hw2. cbn [forces_fnat_closed].
    destruct (forallb (fun v => forces_fnat_closed psi v) (seq n (w_1 - n))) eqn:Eb1;
      destruct (forallb (fun v => forces_fnat_closed psi v) (seq n (w_2 - n))) eqn:Eb2;
      try reflexivity; exfalso.
    + (* Eb1 = true, Eb2 = false: produce a witness in seq_w_2 violating, derive contradiction with Eb1. *)
      destruct (forallb_false_witness _ _ Eb2) as [v [Hin Hf]].
      apply in_seq in Hin. destruct Hin as [Hvn Hvw2].
      rewrite forallb_forall in Eb1.
      destruct (le_gt_dec (wbound psi) v) as [Hvge | Hvlt].
      * (* v >= wbound psi: stabilize via [max n (wbound psi)]. *)
        assert (Hin_max : In (Nat.max n (wbound psi)) (seq n (w_1 - n))) by (apply in_seq; lia).
        pose proof (Eb1 _ Hin_max) as Hf_max.
        assert (Hbnd_max : Nat.max n (wbound psi) >= wbound psi) by lia.
        pose proof (IHpsi (Nat.max n (wbound psi)) v Hcl Hbnd_max Hvge) as Heq.
        rewrite Heq in Hf_max. rewrite Hf in Hf_max. discriminate.
      * (* v < wbound psi: then v < w_1, so [v ∈ seq n (w_1 - n)]. *)
        assert (Hv_in_w1 : In v (seq n (w_1 - n))) by (apply in_seq; lia).
        pose proof (Eb1 _ Hv_in_w1) as Hf_at_v. rewrite Hf in Hf_at_v. discriminate.
    + (* Eb1 = false, Eb2 = true: symmetric. *)
      destruct (forallb_false_witness _ _ Eb1) as [v [Hin Hf]].
      apply in_seq in Hin. destruct Hin as [Hvn Hvw1].
      rewrite forallb_forall in Eb2.
      destruct (le_gt_dec (wbound psi) v) as [Hvge | Hvlt].
      * assert (Hin_max : In (Nat.max n (wbound psi)) (seq n (w_2 - n))) by (apply in_seq; lia).
        pose proof (Eb2 _ Hin_max) as Hf_max.
        assert (Hbnd_max : Nat.max n (wbound psi) >= wbound psi) by lia.
        pose proof (IHpsi (Nat.max n (wbound psi)) v Hcl Hbnd_max Hvge) as Heq.
        rewrite Heq in Hf_max. rewrite Hf in Hf_max. discriminate.
      * assert (Hv_in_w2 : In v (seq n (w_2 - n))) by (apply in_seq; lia).
        pose proof (Eb2 _ Hv_in_w2) as Hf_at_v. rewrite Hf in Hf_at_v. discriminate.
Qed.

(** ** Bounded-window characterization of universal [Fnat] validity. *)

Theorem forces_fnat_closed_universal_iff_bounded : forall phi,
  free_vars phi = [] ->
  ((forall w, forces_fnat_closed phi w = true) <->
   (forall w, w <= wbound phi -> forces_fnat_closed phi w = true)).
Proof.
  intros phi Hcl. split.
  - intros Hall w _. exact (Hall w).
  - intros Hbnd w. destruct (le_gt_dec w (wbound phi)) as [Hle | Hgt].
    + exact (Hbnd w Hle).
    + assert (Hwbnd : wbound phi >= wbound phi) by lia.
      assert (Hwgt : w >= wbound phi) by lia.
      rewrite (forces_fnat_closed_stabilizes phi w (wbound phi) Hcl Hwgt Hwbnd).
      exact (Hbnd (wbound phi) (Nat.le_refl _)).
Qed.

(** ** Bounded refutation: a closed [phi] with [forces_fnat_closed phi w =
    false] for some [w in [0, wbound phi]] is unprovable.  Sound but not
    complete: not every Fnat-valid closed [phi] is provable in GLP*. *)

Theorem closed_refutation_via_fnat : forall phi w,
  free_vars phi = [] -> w <= wbound phi ->
  forces_fnat_closed phi w = false -> ~ |- phi.
Proof.
  intros phi w Hcl _ Hf Hp.
  pose proof (provable_implies_forces_fnat_closed phi w Hcl Hp) as Hf'.
  rewrite Hf in Hf'. discriminate Hf'.
Qed.

(** ** Decidability of [forall w in [0, wbound phi], forces phi w = true].
    Bounded boolean check: returns [sumbool] indicating whether [phi] is
    Fnat-valid up to its stabilization threshold. *)

Lemma forces_bounded_decidable : forall phi,
  free_vars phi = [] ->
  sumbool (forall w, w <= wbound phi -> forces_fnat_closed phi w = true)
          (exists w, w <= wbound phi /\ forces_fnat_closed phi w = false).
Proof.
  intros phi Hcl.
  destruct (forallb (fun w => forces_fnat_closed phi w) (seq 0 (S (wbound phi)))) eqn:Eb.
  - left. intros w Hw.
    rewrite forallb_forall in Eb.
    apply Eb. apply in_seq. lia.
  - right.
    destruct (forallb_false_witness _ _ Eb) as [w [Hin Hf]].
    apply in_seq in Hin. destruct Hin as [_ Hwlt].
    exists w. split; [lia | exact Hf].
Qed.

(** ** Full decidability for [Impl (Box k_1 psi_1) (Box k_2 psi_2)] with
    closed box-free [psi_1, psi_2].  Four cases by the validity of each:
    (a) both valid: provable via Nec on [psi_2] then [Ax_K];
    (b) [psi_1] valid, [psi_2] not: refuted, since MP would give [|- psi_2];
    (c) [psi_1] not, [psi_2] valid: provable via Nec on [psi_2];
    (d) both not valid: each [Box k psi_i] is provably equivalent to
        [Box k Bot] (via [box_psi_iff_box_bot_when_neg_provable]), so the
        implication reduces to [Impl (Box k_1 Bot) (Box k_2 Bot)],
        decidable via [glp_decide_impl_box_bot_box_bot]. *)

Definition glp_decide_impl_box_box_box_free_general
  (k_1 k_2 : nat) (psi_1 psi_2 : Form)
  (Hcl_1 : free_vars psi_1 = []) (Hbf_1 : box_free psi_1)
  (Hcl_2 : free_vars psi_2 = []) (Hbf_2 : box_free psi_2) :
  sumbool (|- Impl (Box k_1 psi_1) (Box k_2 psi_2))
          (~ |- Impl (Box k_1 psi_1) (Box k_2 psi_2)).
Proof.
  destruct (glp_decide_closed_box_free psi_2 Hcl_2 Hbf_2) as [Hp2 | Hnp2].
  - (* psi_2 valid: |- Box k_2 psi_2 then Ax_K. *)
    left. exact (MP _ _ (Ax_K (Box k_2 psi_2) (Box k_1 psi_1)) (Nec k_2 psi_2 Hp2)).
  - destruct (glp_decide_closed_box_free psi_1 Hcl_1 Hbf_1) as [Hp1 | Hnp1].
    + (* psi_1 valid, psi_2 not: refuted via MP. *)
      right. intro Himp. apply Hnp2.
      apply (proj1 (provable_box_box_free_iff_provable k_2 psi_2 Hbf_2)).
      exact (MP _ _ Himp (Nec k_1 psi_1 Hp1)).
    + (* both not valid: reduce to [Impl (Box k_1 Bot) (Box k_2 Bot)]. *)
      pose proof (not_provable_implies_provable_neg_closed_box_free psi_1 Hcl_1 Hbf_1 Hnp1) as Hneg1.
      pose proof (not_provable_implies_provable_neg_closed_box_free psi_2 Hcl_2 Hbf_2 Hnp2) as Hneg2.
      pose proof (box_psi_iff_box_bot_when_neg_provable k_1 psi_1 Hneg1) as Hiff1.
      pose proof (box_psi_iff_box_bot_when_neg_provable k_2 psi_2 Hneg2) as Hiff2.
      destruct (glp_decide_impl_box_bot_box_bot k_1 k_2) as [HBot | HnBot].
      * left.
        pose proof (prov_and_elim_l_meta _ _ Hiff1) as Hf1.
        pose proof (prov_and_elim_r_meta _ _ Hiff2) as Hb2.
        pose proof (prov_compose _ _ _ Hf1 HBot) as Hstep1.
        exact (prov_compose _ _ _ Hstep1 Hb2).
      * right. intro Himp. apply HnBot.
        pose proof (prov_and_elim_r_meta _ _ Hiff1) as Hb1.
        pose proof (prov_and_elim_l_meta _ _ Hiff2) as Hf2.
        pose proof (prov_compose _ _ _ Hb1 Himp) as Hstep1.
        exact (prov_compose _ _ _ Hstep1 Hf2).
Defined.

(** ** When [|- Neg psi], lifting through [iter_box ns] preserves Iff with
    [iter_box ns Bot].  This is the reduction-to-worm step: classically
    refutable [psi] makes [iter_box ns psi] provably equivalent to a
    worm. *)

Lemma iter_box_psi_iff_iter_box_bot_when_neg_provable : forall ns psi,
  |- Neg psi -> |- Iff (iter_box ns psi) (iter_box ns Bot).
Proof.
  intro ns. induction ns as [|n rest IH]; intros psi Hneg.
  - cbn. apply prov_iff_intro.
    + exact Hneg.
    + exact (prov_explosion psi).
  - cbn [iter_box].
    pose proof (IH psi Hneg) as Hiff_inner.
    pose proof (prov_and_elim_l_meta _ _ Hiff_inner) as Hfwd.
    pose proof (prov_and_elim_r_meta _ _ Hiff_inner) as Hback.
    apply prov_iff_intro.
    + exact (MP _ _ (Ax_BoxK n (iter_box rest psi) (iter_box rest Bot))
                  (Nec n _ Hfwd)).
    + exact (MP _ _ (Ax_BoxK n (iter_box rest Bot) (iter_box rest psi))
                  (Nec n _ Hback)).
Qed.

(** ** Reduction-to-worm: for closed box-free [psi_1, psi_2] both
    classically refutable, the iter-box implication is provably equivalent
    to the iter-box-Bot worm-implication. *)

Theorem iter_box_iter_box_iff_worm_implication_when_both_neg :
  forall ns_1 ns_2 psi_1 psi_2,
  |- Neg psi_1 -> |- Neg psi_2 ->
  |- Iff (Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2))
        (Impl (iter_box ns_1 Bot) (iter_box ns_2 Bot)).
Proof.
  intros ns_1 ns_2 psi_1 psi_2 Hneg1 Hneg2.
  pose proof (iter_box_psi_iff_iter_box_bot_when_neg_provable ns_1 psi_1 Hneg1) as Hiff1.
  pose proof (iter_box_psi_iff_iter_box_bot_when_neg_provable ns_2 psi_2 Hneg2) as Hiff2.
  exact (prov_equiv_impl_cong _ _ _ _ Hiff1 Hiff2).
Qed.

(** ** Refutation case for the both-invalid sub-case via Fnat soundness on
    bad_world.  When [bad_world ns_1 > bad_world ns_2] and both [psi_i]
    are closed box-free + classically refutable, the implication is
    unprovable. *)

Theorem refute_impl_iter_box_iter_box_box_free_via_bad_world :
  forall ns_1 ns_2 psi_1 psi_2,
  free_vars psi_1 = [] -> box_free psi_1 ->
  free_vars psi_2 = [] -> box_free psi_2 ->
  ~ |- psi_1 -> ~ |- psi_2 ->
  bad_world ns_1 > bad_world ns_2 ->
  ~ |- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2).
Proof.
  intros ns_1 ns_2 psi_1 psi_2 Hcl1 Hbf1 Hcl2 Hbf2 Hnp1 Hnp2 Hgt Himp.
  pose proof (not_provable_implies_provable_neg_closed_box_free psi_1 Hcl1 Hbf1 Hnp1) as Hneg1.
  pose proof (not_provable_implies_provable_neg_closed_box_free psi_2 Hcl2 Hbf2 Hnp2) as Hneg2.
  pose proof (iter_box_iter_box_iff_worm_implication_when_both_neg ns_1 ns_2 psi_1 psi_2 Hneg1 Hneg2) as Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
  pose proof (MP _ _ Hfwd Himp) as Hworm.
  pose proof (provable_impl_iter_box_bot_forward ns_1 ns_2 Hworm) as Hle.
  lia.
Qed.

(** ** Decider for the iter-box implication when [psi_2] is classically
    valid: the consequent is provable, hence the implication is provable
    via [Ax_K]. *)

Definition glp_decide_impl_iter_box_iter_box_box_free_psi_2_valid
  (ns_1 ns_2 : list nat) (psi_1 psi_2 : Form)
  (Hcl_2 : free_vars psi_2 = []) (Hbf_2 : box_free psi_2)
  (Hp2 : |- psi_2) :
  sumbool (|- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2))
          (~ |- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2)) :=
  glp_decide_impl_iter_box_via_consequent_provable ns_1 ns_2 psi_1 psi_2 Hp2.

(** ** Decider when [psi_1] is valid and [psi_2] is invalid: the implication
    cannot hold, since [MP] would yield the (refutable) consequent. *)

Definition glp_decide_impl_iter_box_iter_box_box_free_psi_1_valid_psi_2_invalid
  (ns_1 ns_2 : list nat) (psi_1 psi_2 : Form)
  (Hcl_2 : free_vars psi_2 = []) (Hbf_2 : box_free psi_2)
  (Hp1 : |- psi_1) (Hnp2 : ~ |- psi_2) :
  sumbool (|- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2))
          (~ |- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2)) :=
  glp_decide_impl_iter_box_via_antecedent_provable_consequent_not
    ns_1 ns_2 psi_1 psi_2 Hcl_2 Hbf_2 Hp1 Hnp2.

(** ** Refutation when both are invalid and the bad_world ordering favors
    refutation. *)

Definition glp_decide_impl_iter_box_iter_box_box_free_both_invalid_refute
  (ns_1 ns_2 : list nat) (psi_1 psi_2 : Form)
  (Hcl_1 : free_vars psi_1 = []) (Hbf_1 : box_free psi_1)
  (Hcl_2 : free_vars psi_2 = []) (Hbf_2 : box_free psi_2)
  (Hnp1 : ~ |- psi_1) (Hnp2 : ~ |- psi_2)
  (Hgt : bad_world ns_1 > bad_world ns_2) :
  ~ |- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2) :=
  refute_impl_iter_box_iter_box_box_free_via_bad_world
    ns_1 ns_2 psi_1 psi_2 Hcl_1 Hbf_1 Hcl_2 Hbf_2 Hnp1 Hnp2 Hgt.

(** ** Empty-antecedent case for both-invalid: trivially provable since
    [psi_1] is provably equivalent to [Bot] under [|- Neg psi_1], so
    [iter_box [] psi_1 = psi_1] is equivalent to [Bot], from which
    everything follows by explosion. *)

Lemma provable_impl_psi_iter_box_psi_2_when_neg_psi_provable :
  forall psi_1 ns_2 psi_2,
  |- Neg psi_1 ->
  |- Impl psi_1 (iter_box ns_2 psi_2).
Proof.
  intros psi_1 ns_2 psi_2 Hneg.
  exact (prov_compose _ _ _ Hneg (prov_explosion (iter_box ns_2 psi_2))).
Qed.

Definition glp_decide_impl_psi_iter_box_psi_2_box_free
  (ns_2 : list nat) (psi_1 psi_2 : Form)
  (Hcl_1 : free_vars psi_1 = []) (Hbf_1 : box_free psi_1)
  (Hcl_2 : free_vars psi_2 = []) (Hbf_2 : box_free psi_2) :
  sumbool (|- Impl psi_1 (iter_box ns_2 psi_2))
          (~ |- Impl psi_1 (iter_box ns_2 psi_2)).
Proof.
  destruct (glp_decide_closed_box_free psi_2 Hcl_2 Hbf_2) as [Hp2 | Hnp2].
  - left.
    exact (MP _ _ (Ax_K (iter_box ns_2 psi_2) psi_1)
                  (provable_iter_box_intro ns_2 psi_2 Hp2)).
  - destruct (glp_decide_closed_box_free psi_1 Hcl_1 Hbf_1) as [Hp1 | Hnp1].
    + right. intro Himp.
      apply Hnp2.
      apply (proj1 (provable_iter_box_box_free_iff ns_2 psi_2 Hcl_2 Hbf_2)).
      exact (MP _ _ Himp Hp1).
    + left.
      pose proof (not_provable_implies_provable_neg_closed_box_free
                    psi_1 Hcl_1 Hbf_1 Hnp1) as Hneg1.
      exact (provable_impl_psi_iter_box_psi_2_when_neg_psi_provable
               psi_1 ns_2 psi_2 Hneg1).
Defined.

(** ** Full decidability for the special case [ns_1 = []]: when the
    antecedent has no outer boxes, classical analysis on [psi_1, psi_2]
    completely determines provability. *)

Definition glp_decide_impl_iter_box_empty_iter_box_box_free
  (ns_2 : list nat) (psi_1 psi_2 : Form)
  (Hcl_1 : free_vars psi_1 = []) (Hbf_1 : box_free psi_1)
  (Hcl_2 : free_vars psi_2 = []) (Hbf_2 : box_free psi_2) :
  sumbool (|- Impl (iter_box [] psi_1) (iter_box ns_2 psi_2))
          (~ |- Impl (iter_box [] psi_1) (iter_box ns_2 psi_2)) :=
  glp_decide_impl_psi_iter_box_psi_2_box_free
    ns_2 psi_1 psi_2 Hcl_1 Hbf_1 Hcl_2 Hbf_2.

(** ** [NextCon]-explosion at the outer level.  When the inner level [n] is
    strictly less than the outer level [m], the [Box m] of [Box n Bot]
    collapses to [Box m Bot]: at level [m], the consistency of level [n]
    (via [Ax_NextCon] lifted by [Mon]) refutes [Box n Bot], so MP yields
    [Box m Bot]. *)

Lemma prov_box_higher_box_lower_bot_to_box_higher_bot : forall n m,
  n < m -> |- Impl (Box m (Box n Bot)) (Box m Bot).
Proof.
  intros n m Hlt.
  pose proof (Ax_NextCon n) as Hnext.
  pose proof (prov_box_mon_le (S n) m (Neg (Box n Bot)) Hlt) as Hmon.
  pose proof (MP _ _ Hmon Hnext) as Hboxm_neg.
  pose proof (Ax_BoxK m (Box n Bot) Bot) as HK.
  exact (MP _ _ HK Hboxm_neg).
Qed.

(** ** Worm collapse for two-element worms with inner < outer.  This is the
    simplest non-trivial case of Beklemishev's worm reduction: when the
    second box-level is strictly less than the first, the worm collapses
    to its single-box form. *)

Theorem worm_two_element_collapse_inner_lt_outer : forall outer inner,
  inner < outer ->
  |- Iff (iter_box [outer; inner] Bot) (Box outer Bot).
Proof.
  intros outer inner Hlt. cbn [iter_box].
  apply prov_iff_intro.
  - exact (prov_box_higher_box_lower_bot_to_box_higher_bot inner outer Hlt).
  - exact (prov_box_bot_to_box_anything outer (Box inner Bot)).
Qed.

(** ** Provable [Impl (iter_box [outer; inner] Bot) (Box m Bot)] when
    [inner < outer] and [outer <= m].  Combines worm collapse with [Mon]. *)

Theorem provable_impl_iter_box_two_element_to_box_bot :
  forall outer inner m,
  inner < outer -> outer <= m ->
  |- Impl (iter_box [outer; inner] Bot) (Box m Bot).
Proof.
  intros outer inner m Hlt Hle.
  pose proof (worm_two_element_collapse_inner_lt_outer outer inner Hlt) as Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
  pose proof (prov_box_mon_le outer m Bot Hle) as Hmon.
  exact (prov_compose _ _ _ Hfwd Hmon).
Qed.

(** ** Provable [Impl (iter_box [outer; inner] Bot) (iter_box (m :: rest) Bot)]
    when [inner < outer] and [outer <= m].  Combines worm collapse with the
    box-bot-explosion route. *)

Theorem provable_impl_iter_box_two_element_to_iter_box :
  forall outer inner m rest,
  inner < outer -> outer <= m ->
  |- Impl (iter_box [outer; inner] Bot) (iter_box (m :: rest) Bot).
Proof.
  intros outer inner m rest Hlt Hle.
  pose proof (worm_two_element_collapse_inner_lt_outer outer inner Hlt) as Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
  pose proof (provable_impl_box_bot_iter_box_bot_head_match outer m rest Hle) as Hhead.
  exact (prov_compose _ _ _ Hfwd Hhead).
Qed.

(** ** Two cleanly-handled sub-cases for the worm-implication with a
    2-element collapsed antecedent: empty consequent (refute via the
    Carlson generalisation) and head-match consequent (provable via the
    collapse + head-match chain).  The remaining cases (consequent with
    head [m < outer] but inner structure rich enough to dominate) are
    genuine gaps in the bad_world-only characterisation, so we expose
    these positive cases as separate lemmas rather than forcing a
    [sumbool] over an indeterminate domain. *)

Lemma worm_implication_two_element_collapsed_to_empty_unprovable :
  forall outer inner,
  inner < outer ->
  ~ |- Impl (iter_box [outer; inner] Bot) (iter_box [] Bot).
Proof.
  intros outer inner Hlt Himp.
  pose proof (worm_two_element_collapse_inner_lt_outer outer inner Hlt) as Hiff.
  pose proof (prov_and_elim_r_meta _ _ Hiff) as Hback.
  pose proof (prov_compose _ _ _ Hback Himp) as Hbox_outer_to_bot.
  exact (closed_neg_box_unprovable outer Bot eq_refl Hbox_outer_to_bot).
Qed.

(** ** Boolean prefix-mon check: Boolean predicate that is [true] iff
    [ns_2] starts with a length-[length ns_1] prefix that pointwise
    dominates [ns_1].  Yields a syntactic sufficient condition for
    worm-implication provability. *)

Fixpoint prefix_mon_le_b (ns_1 ns_2 : list nat) : bool :=
  match ns_1, ns_2 with
  | [], _ => true
  | _ :: _, [] => false
  | n :: rest_1, m :: rest_2 => andb (Nat.leb n m) (prefix_mon_le_b rest_1 rest_2)
  end.

Lemma prefix_mon_le_b_implies_split : forall ns_1 ns_2,
  prefix_mon_le_b ns_1 ns_2 = true ->
  exists prefix ext,
    ns_2 = prefix ++ ext /\
    length ns_1 = length prefix /\
    (forall i, i < length ns_1 -> nth i ns_1 0 <= nth i prefix 0).
Proof.
  intro ns_1. induction ns_1 as [|n rest_1 IH]; intros ns_2 Hb.
  - exists [], ns_2. split; [reflexivity | split; [reflexivity|]].
    intros i Hi. cbn in Hi. lia.
  - destruct ns_2 as [|m rest_2]; [discriminate Hb|].
    cbn in Hb. apply Bool.andb_true_iff in Hb. destruct Hb as [Hle Hrec].
    apply Nat.leb_le in Hle.
    destruct (IH rest_2 Hrec) as [prefix [ext [Heq [Hlen Hpt]]]].
    exists (m :: prefix), ext. split; [|split].
    + cbn. rewrite Heq. reflexivity.
    + cbn. rewrite Hlen. reflexivity.
    + intros i Hi. destruct i as [|i].
      * cbn. exact Hle.
      * cbn. cbn in Hi. apply Hpt. lia.
Qed.

(** ** Provable worm-implication from the Boolean prefix-mon check. *)

Theorem prefix_mon_le_b_implies_worm_provable : forall ns_1 ns_2,
  prefix_mon_le_b ns_1 ns_2 = true ->
  |- Impl (iter_box ns_1 Bot) (iter_box ns_2 Bot).
Proof.
  intros ns_1 ns_2 Hb.
  destruct (prefix_mon_le_b_implies_split ns_1 ns_2 Hb) as [prefix [ext [Heq [Hlen Hpt]]]].
  rewrite Heq.
  exact (prov_iter_box_prefix_mon_extension ns_1 prefix ext Bot Hlen Hpt).
Qed.

(** ** Decidability of the boolean prefix-mon check yields a [sumbool] for
    a structurally identifiable subset of provable worm implications.
    When the check fails, we cannot conclude unprovability in general
    (the Beklemishev worm theorem provides additional positive cases
    not captured by pointwise prefix mon). *)

Definition glp_decide_worm_implication_via_prefix_mon
  (ns_1 ns_2 : list nat) :
  sumbool (prefix_mon_le_b ns_1 ns_2 = true)
          (prefix_mon_le_b ns_1 ns_2 = false).
Proof.
  destruct (prefix_mon_le_b ns_1 ns_2) eqn:Eb.
  - left. reflexivity.
  - right. reflexivity.
Defined.

(** ** Full decision when the bad_world ordering FAILS: refute via the
    forward direction of the worm-implication theorem. *)

Definition glp_decide_worm_implication_via_bad_world
  (ns_1 ns_2 : list nat)
  (Hgt : bad_world ns_1 > bad_world ns_2) :
  ~ |- Impl (iter_box ns_1 Bot) (iter_box ns_2 Bot).
Proof.
  intro Himp.
  pose proof (provable_impl_iter_box_bot_forward ns_1 ns_2 Himp) as Hle.
  lia.
Defined.

(** ** Combined decision principle for worm implications: the [sumbool]
    holds when at least one of the two structural conditions decides:
    (a) prefix-mon check passes (provable), or
    (b) bad_world ordering fails (unprovable).  When neither decides,
    we cannot conclude with the present tools. *)

Definition glp_decide_worm_implication_via_structural_principles
  (ns_1 ns_2 : list nat) :
  sumbool (|- Impl (iter_box ns_1 Bot) (iter_box ns_2 Bot))
          (~ |- Impl (iter_box ns_1 Bot) (iter_box ns_2 Bot)) +
  ((prefix_mon_le_b ns_1 ns_2 = false) /\
   (bad_world ns_1 <= bad_world ns_2)).
Proof.
  destruct (glp_decide_worm_implication_via_prefix_mon ns_1 ns_2) as [Hpref | Hpref].
  - left. left. exact (prefix_mon_le_b_implies_worm_provable ns_1 ns_2 Hpref).
  - destruct (le_gt_dec (bad_world ns_1) (bad_world ns_2)) as [Hle | Hgt].
    + right. split; assumption.
    + left. right. exact (glp_decide_worm_implication_via_bad_world ns_1 ns_2 Hgt).
Defined.

(** ** Free-variable extension for box-free [iter_box].  For arbitrary
    [psi] (closed or open) that is box-free, [|- iter_box ns psi] iff
    [psi] is classically valid (true under every Boolean valuation).
    This generalises [provable_iter_box_box_free_iff] to forms with free
    variables, leveraging [prop_completeness] (which works in the
    box-free fragment regardless of whether variables are present). *)

Lemma forces_iter_box_at_bad_world_const : forall ns psi val w,
  box_free psi ->
  w >= bad_world ns ->
  forces Fnat (fun _ => val) w (iter_box ns psi) ->
  eval val psi = true.
Proof.
  intro ns. induction ns as [|n rest IH]; intros psi val w Hbf Hw Hf.
  - cbn in Hf. apply (proj1 (forces_const_box_free Fnat val w psi Hbf)). exact Hf.
  - cbn in Hf. cbn in Hw.
    set (v := Nat.max n (bad_world rest)).
    assert (Hr : Fnat_R n w v).
    { unfold Fnat_R, v. lia. }
    pose proof (Hf v Hr) as Hinner.
    apply (IH psi val v Hbf).
    + unfold v. lia.
    + exact Hinner.
Qed.

Theorem provable_iter_box_box_free_iff_classical_valid : forall ns psi,
  box_free psi ->
  (|- iter_box ns psi <-> classical_valid psi).
Proof.
  intros ns psi Hbf. unfold classical_valid. split.
  - intros Hp val.
    pose proof (soundness _ Hp Fnat (fun _ => val) (bad_world ns)) as Hf.
    exact (forces_iter_box_at_bad_world_const ns psi val (bad_world ns)
             Hbf (Nat.le_refl _) Hf).
  - intros Hval.
    pose proof (prop_completeness psi Hbf Hval) as Hpp.
    pose proof (trivial_in_provable psi Hpp) as Hp.
    exact (provable_iter_box_intro ns psi Hp).
Qed.

(** ** Decision procedure for [iter_box ns psi] with general (open)
    box-free [psi].  Uses [decide_tautology] for the underlying classical
    decision. *)

Definition glp_decide_iter_box_box_free (ns : list nat) (psi : Form)
  (Hbf : box_free psi) :
  sumbool (|- iter_box ns psi) (~ |- iter_box ns psi).
Proof.
  destruct (decide_tautology psi) eqn:Edt.
  - left.
    apply (proj2 (provable_iter_box_box_free_iff_classical_valid ns psi Hbf)).
    apply decide_tautology_correct. exact Edt.
  - right.
    intro Hp.
    pose proof (proj1 (provable_iter_box_box_free_iff_classical_valid ns psi Hbf) Hp) as Hval.
    pose proof (decide_tautology_complete psi Hval) as Edt'.
    rewrite Edt in Edt'. discriminate.
Defined.

(** ** Full decision procedure for the entire box-free fragment, open or
    closed: [|- phi] iff [phi] is classically valid.  This is just
    [decide_tautology] wrapped as a [sumbool]. *)

Definition glp_decide_box_free (phi : Form) (Hbf : box_free phi) :
  sumbool (|- phi) (~ |- phi).
Proof.
  destruct (decide_tautology phi) eqn:Edt.
  - left. apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
    apply decide_tautology_correct. exact Edt.
  - right. intro Hp.
    pose proof (eval_provable_true) as Heval.
    pose proof (decide_tautology_complete phi (fun val => Heval val phi Hp)) as Edt'.
    rewrite Edt in Edt'. discriminate.
Defined.

(** ** Boolean version of [box_free]. *)

Fixpoint box_free_b (phi : Form) : bool :=
  match phi with
  | Var _ => true
  | Bot => true
  | Impl X Y => andb (box_free_b X) (box_free_b Y)
  | Box _ _ => false
  end.

Lemma box_free_b_iff : forall phi,
  box_free_b phi = true <-> box_free phi.
Proof.
  intro phi. induction phi as [k | | X IHX Y IHY | n psi IHpsi]; cbn.
  - tauto.
  - tauto.
  - rewrite Bool.andb_true_iff. rewrite IHX, IHY. reflexivity.
  - split; [discriminate | intros []].
Qed.

(** ** Decomposition: every formula factors as [iter_box ns psi] where
    [psi] is the result of stripping all outermost [Box] layers and [ns]
    collects the box levels. *)

Fixpoint extract_box_levels (phi : Form) : list nat :=
  match phi with
  | Box n psi => n :: extract_box_levels psi
  | _ => []
  end.

Fixpoint extract_inner_form (phi : Form) : Form :=
  match phi with
  | Box _ psi => extract_inner_form psi
  | _ => phi
  end.

Lemma extract_decomposition : forall phi,
  phi = iter_box (extract_box_levels phi) (extract_inner_form phi).
Proof.
  intro phi. induction phi as [k | | X IHX Y IHY | n psi IHpsi]; cbn; try reflexivity.
  rewrite <- IHpsi at 1. reflexivity.
Qed.

Lemma extract_inner_form_no_outer_box : forall phi,
  match extract_inner_form phi with Box _ _ => False | _ => True end.
Proof.
  intro phi. induction phi as [k | | X IHX Y IHY | n psi IHpsi]; cbn; auto; exact I.
Qed.

(** ** Boolean predicate identifying the sub-fragment for which we provide
    full decidability: a formula whose innermost (after stripping outer
    boxes) is box-free.  These are exactly the formulas of shape
    [iter_box ns psi] with box-free [psi]. *)

Definition is_iter_box_of_box_free (phi : Form) : bool :=
  box_free_b (extract_inner_form phi).

Lemma extract_inner_box_free : forall phi,
  is_iter_box_of_box_free phi = true -> box_free (extract_inner_form phi).
Proof.
  intros phi Hb. unfold is_iter_box_of_box_free in Hb.
  apply box_free_b_iff. exact Hb.
Qed.

(** ** Headline decidability for the [is_iter_box_of_box_free] fragment.
    Combined with [glp_decide_box_free] for the box-free part of the
    fragment, this yields a decision procedure for every formula whose
    syntactic shape strips to a box-free leaf. *)

Definition glp_decide_iter_box_of_box_free (phi : Form)
  (Hb : is_iter_box_of_box_free phi = true) :
  sumbool (|- phi) (~ |- phi).
Proof.
  rewrite (extract_decomposition phi).
  exact (glp_decide_iter_box_box_free
           (extract_box_levels phi)
           (extract_inner_form phi)
           (extract_inner_box_free phi Hb)).
Defined.

(** ** Iff-congruence under [Box].  A directional [Iff] under a single
    [Box] follows from [Nec] + [BoxK] applied componentwise. *)

Lemma iff_under_box : forall n phi psi,
  |- Iff phi psi ->
  |- Iff (Box n phi) (Box n psi).
Proof.
  intros n phi psi Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hf.
  pose proof (prov_and_elim_r_meta _ _ Hiff) as Hb.
  apply prov_iff_intro.
  - exact (MP _ _ (Ax_BoxK n phi psi) (Nec n _ Hf)).
  - exact (MP _ _ (Ax_BoxK n psi phi) (Nec n _ Hb)).
Qed.

(** ** Boolean check for strictly descending lists. *)

Fixpoint is_strictly_descending (ns : list nat) : bool :=
  match ns with
  | [] => true
  | [_] => true
  | a :: ((b :: _) as rest) => andb (Nat.ltb b a) (is_strictly_descending rest)
  end.

(** ** Iterated worm collapse for strictly descending sequences.  Each
    successive [(a, b, ...)] with [b < a] collapses [Box a (Box b ...)]
    to [Box a Bot] via iterated application of the 2-element collapse and
    [iff_under_box]. *)

Lemma prov_iff_trans : forall phi psi chi,
  |- Iff phi psi -> |- Iff psi chi -> |- Iff phi chi.
Proof.
  intros phi psi chi H1 H2.
  pose proof (prov_and_elim_l_meta _ _ H1) as H1f.
  pose proof (prov_and_elim_r_meta _ _ H1) as H1b.
  pose proof (prov_and_elim_l_meta _ _ H2) as H2f.
  pose proof (prov_and_elim_r_meta _ _ H2) as H2b.
  apply prov_iff_intro.
  - exact (prov_compose _ _ _ H1f H2f).
  - exact (prov_compose _ _ _ H2b H1b).
Qed.

Theorem worm_descending_collapse_to_head : forall n rest,
  is_strictly_descending (n :: rest) = true ->
  |- Iff (iter_box (n :: rest) Bot) (Box n Bot).
Proof.
  intros n rest. revert n. induction rest as [|m rest' IH]; intros n Hd.
  - cbn [iter_box]. apply prov_iff_refl.
  - cbn in Hd. apply Bool.andb_true_iff in Hd. destruct Hd as [Hlt Hd_rest].
    apply Nat.ltb_lt in Hlt.
    pose proof (IH m Hd_rest) as Hiff_inner.
    pose proof (iff_under_box n _ _ Hiff_inner) as Hiff_outer.
    cbn [iter_box] in Hiff_outer.
    pose proof (worm_two_element_collapse_inner_lt_outer n m Hlt) as Hcollapse.
    cbn [iter_box] in Hcollapse.
    cbn [iter_box].
    exact (prov_iff_trans _ _ _ Hiff_outer Hcollapse).
Qed.

(** ** Worm-implication via descending-collapse + head-match.  When the
    antecedent is strictly descending, it collapses to its head; if the
    head is dominated by the consequent's head, the implication is
    provable. *)

Theorem provable_impl_descending_iter_box_to_iter_box_via_head :
  forall n rest m rest_2,
  is_strictly_descending (n :: rest) = true ->
  n <= m ->
  |- Impl (iter_box (n :: rest) Bot) (iter_box (m :: rest_2) Bot).
Proof.
  intros n rest m rest_2 Hd Hle.
  pose proof (worm_descending_collapse_to_head n rest Hd) as Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
  pose proof (provable_impl_box_bot_iter_box_bot_head_match n m rest_2 Hle) as Hhead.
  exact (prov_compose _ _ _ Hfwd Hhead).
Qed.

(** ** Beklemishev-style absorption: when an iter-box-Bot has a sub-pattern
    [Box outer (Box inner ...)] with [inner < outer], the inner box can
    be absorbed.  Specifically, [Box outer (Box inner phi)] entails
    [Box outer Bot] when [inner < outer] AND [phi = Bot] — extending to
    the case [phi = iter_box rest Bot] requires that [rest] doesn't
    introduce new structure stronger than [Bot].  We capture the simplest
    productive case: a worm where the second level is strictly less than
    the first AND the remaining suffix is empty. *)

Lemma worm_two_element_bot_provable_iff_outer_bot : forall outer inner,
  inner < outer ->
  (|- iter_box [outer; inner] Bot <-> |- Box outer Bot).
Proof.
  intros outer inner Hlt.
  pose proof (worm_two_element_collapse_inner_lt_outer outer inner Hlt) as Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
  pose proof (prov_and_elim_r_meta _ _ Hiff) as Hback.
  split.
  - intro Hp. exact (MP _ _ Hfwd Hp).
  - intro Hp. exact (MP _ _ Hback Hp).
Qed.

(** ** A complete decidability statement for [iter_box [outer; inner] Bot]
    when [inner < outer]: the worm is provable iff [Box outer Bot] is,
    which is iff false (by [closed_fragment_iterated_bot_not_provable]). *)

Theorem worm_two_element_descending_unprovable : forall outer inner,
  inner < outer ->
  ~ |- iter_box [outer; inner] Bot.
Proof.
  intros outer inner Hlt Hp.
  apply (proj1 (worm_two_element_bot_provable_iff_outer_bot outer inner Hlt)) in Hp.
  exact (closed_fragment_iterated_bot_not_provable outer Hp).
Qed.

(** ** Same conclusion via the iterated-descending generalization: an
    iter-box-Bot worm with strictly descending box-levels collapses to its
    head's [Box n Bot], which is unprovable. *)

Theorem worm_descending_unprovable : forall n rest,
  is_strictly_descending (n :: rest) = true ->
  ~ |- iter_box (n :: rest) Bot.
Proof.
  intros n rest Hd Hp.
  pose proof (worm_descending_collapse_to_head n rest Hd) as Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
  pose proof (MP _ _ Hfwd Hp) as Hbox_n_bot.
  exact (closed_fragment_iterated_bot_not_provable n Hbox_n_bot).
Qed.

(** ** Decidability of unprovability for descending worms (paired with
    the existing positive results). *)

Definition glp_decide_descending_worm
  (n : nat) (rest : list nat)
  (Hd : is_strictly_descending (n :: rest) = true) :
  sumbool (|- iter_box (n :: rest) Bot) (~ |- iter_box (n :: rest) Bot).
Proof.
  right. exact (worm_descending_unprovable n rest Hd).
Defined.

(** ** Beklemishev-gap refutation for [Impl (Box k Bot) (Box 0 (Box m Bot))]
    when [m < k].  This is a corner case where Fnat is not directly able
    to refute, but a syntactic argument via [Mon] + the unprovability of
    [Box 0 (Box m Bot)] does the job.

    Approach: assume the implication is provable.  Then by the contrapositive
    direction of NextCon-derived equivalences, we should be able to derive
    something contradictory.  However, the gap is genuine in our axioms:
    we have [|- Box 0 (Box m Bot) -> Box (S m) Bot] (via Mon + NextCon route),
    so [Box 0 (Box m Bot)] is provably stronger than [Box (S m) Bot], and
    [Box (S m) Bot] is in turn implied by [Box k Bot] when [k <= S m].

    But for [m < k], we have [k > m], so [Box (S m) Bot -> Box k Bot] by
    [Mon] iff [S m <= k], i.e., [m < k].  Thus [Box 0 (Box m Bot) -> Box k Bot]
    is provable, but the reverse [Box k Bot -> Box 0 (Box m Bot)] is not
    derivable in our axiom system (it would require the unprovable
    "T_k inconsistent therefore T_0 proves T_m inconsistent"). *)

Lemma prov_box_0_box_m_bot_to_box_S_m_bot : forall m,
  |- Impl (Box 0 (Box m Bot)) (Box (S m) Bot).
Proof.
  intro m.
  pose proof (prov_box_mon_le 0 (S m) (Box m Bot)
                (Nat.le_0_l (S m))) as Hmon.
  pose proof (prov_box_higher_box_lower_bot_to_box_higher_bot m (S m)
                (Nat.lt_succ_diag_r m)) as Hcol.
  exact (prov_compose _ _ _ Hmon Hcol).
Qed.

(** ** When [|- Box k Bot -> Box 0 (Box m Bot)] holds AND [m < k] holds,
    we can chain to derive [|- Box k Bot -> Box (S m) Bot], which is not
    a direct contradiction.  But we also have [|- Box (S m) Bot -> Box k Bot]
    by [Mon] (when [S m <= k]), so the two are provably equivalent.

    Thus [|- Box k Bot -> Box 0 (Box m Bot)] iff [|- Box (S m) Bot -> Box 0 (Box m Bot)]
    (by chasing the chain).  Since [Box (S m) Bot] is derivable from
    [Box 0 (Box m Bot)] AND vice versa (provable equivalence in this direction)
    is the missing ingredient — only one direction of equivalence holds. *)

Lemma prov_iff_box_S_m_bot_box_0_box_m_bot_partial : forall m,
  |- Impl (Box 0 (Box m Bot)) (Box (S m) Bot).
Proof.
  exact prov_box_0_box_m_bot_to_box_S_m_bot.
Qed.

(** ** An Ignatiev-style 2-dimensional Kripke frame [I2] that refutes
    Beklemishev-gap formulas.  Worlds are pairs of naturals; [R_0] is the
    lex order, while [R_n] for [n >= 1] depends only on the first
    coordinate with a level-threshold.  This frame distinguishes formulas
    that Fnat collapses, since the second coordinate provides extra
    "depth" at each first-coordinate level. *)

Definition I2_R (n : nat) (w v : nat * nat) : Prop :=
  match n with
  | 0 => fst w > fst v \/ (fst w = fst v /\ snd w > snd v)
  | S k => fst w > fst v /\ fst v >= S k
  end.

Lemma I2_R_trans : forall n w v u, I2_R n w v -> I2_R n v u -> I2_R n w u.
Proof.
  intros [|k] [a b] [c d] [e f]; cbn.
  - intros [Hac | [Hac Hbd]] [Hce | [Hce Hdf]].
    + left. lia.
    + left. lia.
    + left. lia.
    + right. split; [lia | lia].
  - intros [Hac Hcn] [Hce Hen]. split; lia.
Qed.

Lemma I2_R_wf_helper :
  forall a b,
    Acc (fun v u : nat * nat =>
           fst u > fst v \/ (fst u = fst v /\ snd u > snd v)) (a, b).
Proof.
  induction a as [a IHa] using (well_founded_induction Wf_nat.lt_wf).
  intro b.
  induction b as [b IHb] using (well_founded_induction Wf_nat.lt_wf).
  apply Acc_intro. intros [c d] H.
  destruct H as [Hac | [Hac Hbd]].
  - cbn in Hac. apply (IHa c Hac).
  - cbn in Hac, Hbd. subst c.
    apply (IHb d Hbd).
Qed.

Lemma I2_R_wf : forall n, well_founded (fun u v : nat * nat => I2_R n v u).
Proof.
  intros [|k] [a b].
  - apply I2_R_wf_helper.
  - revert b.
    induction a as [a IHa] using (well_founded_induction Wf_nat.lt_wf).
    intro b. apply Acc_intro. intros [c d] [Hac _].
    cbn in Hac. apply (IHa c Hac).
Qed.

Lemma I2_R_mon : forall n w v, I2_R (S n) w v -> I2_R n w v.
Proof.
  intros [|k] [a b] [c d]; cbn.
  - intros [Hac _]. left. exact Hac.
  - intros [Hac Hcn]. split; [lia|lia].
Qed.

Lemma I2_R_nextcon : forall n w v, I2_R (S n) w v -> exists u, I2_R n v u.
Proof.
  intros [|k] [a b] [c d]; cbn.
  - intros [Hac Hcn].
    exists (c - 1, 0). cbn.
    left. lia.
  - intros [Hac Hcn].
    exists (S k, 0). cbn. split; [lia|lia].
Qed.

Definition I2 : Frame :=
  mkFrame (nat * nat) I2_R I2_R_trans I2_R_wf I2_R_mon I2_R_nextcon.

(** ** Concrete refutation: [|- Box 4 Bot -> Box 0 (Box 3 Bot)] is FALSE
    in GLP*.  The witness is [I2] at world [(4, 5)]. *)

Theorem refute_box_4_bot_implies_box_0_box_3_bot :
  ~ |- Impl (Box 4 Bot) (Box 0 (Box 3 Bot)).
Proof.
  intro Hp.
  pose proof (soundness _ Hp I2 (fun _ _ => false) (4, 5)) as Hf.
  cbn in Hf.
  assert (Hbox4 : forall v : nat * nat, I2_R 4 (4, 5) v -> False).
  { intros [c d] [Hac Hcn]. cbn in *. lia. }
  pose proof (Hf Hbox4) as Hbox0.
  pose proof (Hbox0 (4, 0)) as Hbox0'.
  assert (Hr0 : I2_R 0 (4, 5) (4, 0))
    by (cbn; right; split; [reflexivity | lia]).
  pose proof (Hbox0' Hr0) as Hbox3.
  apply (Hbox3 (3, 0)).
  cbn. split; [lia | lia].
Qed.

(** ** Generalised Beklemishev-gap refutation: for any [m < k], the
    formula [Box k Bot -> Box 0 (Box m Bot)] is unprovable.  The witness
    is [I2] at world [(S m, 1)]. *)

Theorem refute_box_k_bot_implies_box_0_box_m_bot : forall k m,
  m < k -> ~ |- Impl (Box k Bot) (Box 0 (Box m Bot)).
Proof.
  intros k m Hmk Hp.
  pose proof (soundness _ Hp I2 (fun _ _ => false) (S m, 1)) as Hf.
  cbn in Hf.
  assert (Hboxk : forall v : nat * nat, I2_R k (S m, 1) v -> False).
  { intros [c d]. destruct k as [|k']; cbn.
    - intros _. lia.
    - intros [Hac Hcn]. cbn in Hac, Hcn. lia. }
  pose proof (Hf Hboxk) as Hbox0.
  pose proof (Hbox0 (S m, 0)) as Hbox0'.
  assert (Hr0 : I2_R 0 (S m, 1) (S m, 0))
    by (cbn; right; split; [reflexivity | lia]).
  pose proof (Hbox0' Hr0) as Hboxm.
  destruct m as [|m']; cbn in Hboxm.
  - apply (Hboxm (0, 0)). cbn. left. lia.
  - apply (Hboxm (S m', 0)). cbn. split; [lia|lia].
Qed.

(** ** Bidirectional Lindenbaum gap: [Box (S m) Bot] does NOT imply
    [Box 0 (Box m Bot)] (refuted via I2), but the reverse direction
    does (provable via Mon + NextCon collapse).  Hence the two formulas
    are NOT provably equivalent in GLP*, despite being Fnat-equivalent. *)

Theorem reverse_implication_box_S_m_bot_box_0_box_m_bot_unprovable :
  forall m, ~ |- Impl (Box (S m) Bot) (Box 0 (Box m Bot)).
Proof.
  intro m.
  exact (refute_box_k_bot_implies_box_0_box_m_bot (S m) m (Nat.lt_succ_diag_r m)).
Qed.

(** ** Refutation of [Box k Bot -> Box 0 (Box 0 (Box m Bot))] via I2.
    Witness at [(S m, 2)].  This shows the I2 frame extends to
    refute deeper Beklemishev-gap formulas with multiple Box-0 layers. *)

Theorem refute_box_k_bot_implies_box_0_box_0_box_m_bot : forall k m,
  m < k -> ~ |- Impl (Box k Bot) (Box 0 (Box 0 (Box m Bot))).
Proof.
  intros k m Hmk Hp.
  pose proof (soundness _ Hp I2 (fun _ _ => false) (S m, 2)) as Hf.
  cbn in Hf.
  assert (Hboxk : forall v : nat * nat, I2_R k (S m, 2) v -> False).
  { intros [c d]. destruct k as [|k']; cbn.
    - intros _. lia.
    - intros [Hac Hcn]. cbn in Hac, Hcn. lia. }
  pose proof (Hf Hboxk) as Hbox0_box0.
  pose proof (Hbox0_box0 (S m, 1)) as Hbox0_box0'.
  assert (Hr0 : I2_R 0 (S m, 2) (S m, 1))
    by (cbn; right; split; [reflexivity | lia]).
  pose proof (Hbox0_box0' Hr0) as Hbox0_boxm.
  pose proof (Hbox0_boxm (S m, 0)) as Hbox0_boxm'.
  assert (Hr0' : I2_R 0 (S m, 1) (S m, 0))
    by (cbn; right; split; [reflexivity | lia]).
  pose proof (Hbox0_boxm' Hr0') as Hboxm.
  destruct m as [|m']; cbn in Hboxm.
  - apply (Hboxm (0, 0)). cbn. left. lia.
  - apply (Hboxm (S m', 0)). cbn. split; [lia|lia].
Qed.

(** ** General refutation tool: for any iter-box-Bot consequent of the
    form [iter_box (zeros ++ [m]) Bot] where [zeros] is a list of [0]s and
    [m < k], the implication [Box k Bot -> ...] is unprovable.  Proof by
    induction on [zeros], stepping into the lex-below world at each [0]. *)

Lemma forces_iter_box_zeros_box_m_bot_at_drop : forall zeros,
  Forall (fun n => n = 0) zeros ->
  forall m a b,
  forces I2 (fun _ _ => false) (a, b)
         (iter_box zeros (Box m Bot)) ->
  b >= length zeros ->
  forces I2 (fun _ _ => false) (a, b - length zeros) (Box m Bot).
Proof.
  intro zeros. induction zeros as [|z rest IH]; intros Hall m a b Hf Hb.
  - cbn. rewrite Nat.sub_0_r. exact Hf.
  - inversion Hall as [|y ys Hz0 Hrest]. subst z.
    cbn [iter_box length] in *.
    pose proof (Hf (a, b - 1)) as Hf'.
    assert (Hr : I2_R 0 (a, b) (a, b - 1)).
    { cbn. right. split; [reflexivity | lia]. }
    pose proof (Hf' Hr) as Hf_inner.
    assert (Hsub : b - 1 - length rest = b - S (length rest)) by lia.
    rewrite <- Hsub.
    apply (IH Hrest m a (b - 1)); [exact Hf_inner | lia].
Qed.

Theorem refute_box_k_bot_implies_iter_box_zero_prefix_box_m_bot :
  forall k m zeros,
  m < k ->
  Forall (fun n => n = 0) zeros ->
  ~ |- Impl (Box k Bot) (iter_box zeros (Box m Bot)).
Proof.
  intros k m zeros Hmk Hall Hp.
  pose proof (soundness _ Hp I2 (fun _ _ => false) (S m, length zeros)) as Hf.
  cbn in Hf.
  assert (Hboxk : forall v : nat * nat, I2_R k (S m, length zeros) v -> False).
  { intros [c d]. destruct k as [|k']; cbn.
    - intros _. lia.
    - intros [Hac Hcn]. cbn in Hac, Hcn. lia. }
  pose proof (Hf Hboxk) as Hcons.
  pose proof (forces_iter_box_zeros_box_m_bot_at_drop
                zeros Hall m (S m) (length zeros)
                Hcons (Nat.le_refl _)) as Hboxm.
  rewrite Nat.sub_diag in Hboxm.
  cbn in Hboxm.
  destruct m as [|m']; cbn in Hboxm.
  - apply (Hboxm (0, 0)). cbn. left. lia.
  - apply (Hboxm (S m', 0)). cbn. split; [lia|lia].
Qed.

(** ** I2 refutation for [Box k_1 (Box k_2 Bot) -> Box 0 (Box m Bot)]
    when [k_1 >= 1], [k_1 <= k_2], and [k_2 = m] (i.e., the
    bad_world-equal Beklemishev-gap configuration). *)

Theorem refute_box_box_bot_implies_box_0_box_m_bot :
  forall k_1 k_2 m,
  1 <= k_1 -> k_1 <= k_2 -> k_2 = m ->
  ~ |- Impl (Box k_1 (Box k_2 Bot)) (Box 0 (Box m Bot)).
Proof.
  intros k_1 k_2 m Hk1 Hk1k2 Hk2m Hp. subst k_2.
  pose proof (soundness _ Hp I2 (fun _ _ => false) (S m, 1)) as Hf.
  cbn in Hf.
  assert (Hbox12 : forall v : nat * nat,
            I2_R k_1 (S m, 1) v ->
            forall u, I2_R m v u -> False).
  { intros [c d]. destruct k_1 as [|k_1']; cbn.
    - lia.
    - intros [Hac Hcn]. cbn in Hac, Hcn.
      intros [e f]. destruct m as [|m']; cbn.
      + intros _. lia.
      + intros [Hce Hen]. cbn in Hce, Hen. lia. }
  pose proof (Hf Hbox12) as Hbox0.
  pose proof (Hbox0 (S m, 0)) as Hbox0'.
  assert (Hr0 : I2_R 0 (S m, 1) (S m, 0))
    by (cbn; right; split; [reflexivity | lia]).
  pose proof (Hbox0' Hr0) as Hboxm.
  destruct m as [|m']; cbn in Hboxm.
  - apply (Hboxm (0, 0)). cbn. left. lia.
  - apply (Hboxm (S m', 0)). cbn. split; [lia|lia].
Qed.

(** ** Concrete instance: [|- Box 1 (Box 3 Bot) -> Box 0 (Box 3 Bot)] is
    UNPROVABLE.  Together with [Box 0 (Box 3 Bot) -> Box 1 (Box 3 Bot)]
    (provable via Mon), this establishes another Fnat-incompleteness
    witness. *)

Corollary refute_box_1_box_3_bot_implies_box_0_box_3_bot :
  ~ |- Impl (Box 1 (Box 3 Bot)) (Box 0 (Box 3 Bot)).
Proof.
  apply refute_box_box_bot_implies_box_0_box_m_bot; [lia|lia|reflexivity].
Qed.

(** ** Hence, in our axiom system, the Lindenbaum classes of
    [Box 0 (Box m Bot)] and [Box (S m) Bot] are NOT provably equivalent.
    [I2] refutes the reverse direction, completing the Fnat-incompleteness
    witness for the closed fragment of GLP*. *)

