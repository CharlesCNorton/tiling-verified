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
