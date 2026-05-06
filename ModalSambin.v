(******************************************************************************)
(*                                                                            *)
(*  Sambin uniqueness for arbitrary modalised contexts.                       *)
(*                                                                            *)
(*  [sambin_uniqueness_modalised]: every C : Form -> Form arising by          *)
(*  substitution in some [phi] with [modalized p phi] (every occurrence of    *)
(*  the bound variable under at least one Box) admits at most one fixed       *)
(*  point up to provable equivalence.                                         *)
(*                                                                            *)
(*  Proof: structural induction on phi (Form-size strictly decreases at every *)
(*  sub-call), Loeb at level 0 used once for the outer descent, with the      *)
(*  Box case handled via a Master Lemma [box_subst_iff_lift] proved itself    *)
(*  by structural induction on chi without modalisation hypothesis.           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Tiling Require Import Tiling.

(** ** The (Form -> Form) modalised-context predicate. *)

Definition modalised_in_p (C : Form -> Form) : Prop :=
  exists (p : nat) (phi : Form),
    modalized p phi /\ forall psi, C psi = Subst p psi phi.

(** ** Structural Subst-rewrite lemmas. *)

Lemma Subst_Var_explicit : forall p k psi,
  Subst p psi (Var k) = (if Nat.eqb k p then psi else Var k).
Proof. intros. unfold Subst. simpl. reflexivity. Qed.

Lemma Subst_Impl_eq : forall p psi X Y,
  Subst p psi (Impl X Y) = Impl (Subst p psi X) (Subst p psi Y).
Proof. intros. unfold Subst. simpl. reflexivity. Qed.

Lemma Subst_Box_eq : forall p psi i chi,
  Subst p psi (Box i chi) = Box i (Subst p psi chi).
Proof. intros. unfold Subst. simpl. reflexivity. Qed.

Lemma Subst_Bot_eq : forall p psi, Subst p psi Bot = Bot.
Proof. intros. reflexivity. Qed.

(** ** Combinators for chaining implications and box-distribution. *)

Lemma prov_box_chain_internal : forall A B C j,
  |- Impl A (Box j B) ->
  |- Impl A (Box j (Impl B C)) ->
  |- Impl A (Box j C).
Proof.
  intros A B C j HB HBC.
  pose proof (Ax_BoxK j B C) as HK.
  pose proof (prov_compose _ _ _ HBC HK) as HBC2.
  pose proof (Ax_S A (Box j B) (Box j C)) as Hs.
  pose proof (MP _ _ Hs HBC2) as HSBC.
  exact (MP _ _ HSBC HB).
Qed.

Lemma prov_impl_chain_S : forall A B C,
  |- Impl A (Impl B C) -> |- Impl A B -> |- Impl A C.
Proof.
  intros A B C HABC HAB.
  pose proof (Ax_S A B C) as Hs.
  pose proof (MP _ _ Hs HABC) as Hs2.
  exact (MP _ _ Hs2 HAB).
Qed.

Lemma prov_box_0_to_box_j_box_0 : forall j phi,
  |- Impl (Box 0 phi) (Box j (Box 0 phi)).
Proof.
  intros j phi.
  pose proof (Ax_Box4 0 phi) as H4.
  pose proof (prov_box_mon_le 0 j (Box 0 phi) (Nat.le_0_l j)) as Hmon.
  exact (prov_compose _ _ _ H4 Hmon).
Qed.

(** ** Internal versions of two propositional facts via uniform substitution. *)

Lemma iff_trans_atomic :
  |- Impl (Iff (Var 0) (Var 1))
       (Impl (Iff (Var 1) (Var 2)) (Iff (Var 0) (Var 2))).
Proof.
  apply trivial_in_provable. apply prop_completeness.
  - cbn. unfold Iff, And, Neg. cbn. tauto.
  - intro val. cbn. unfold Iff, And, Neg. cbn.
    destruct (val 0), (val 1), (val 2); reflexivity.
Qed.

Lemma iff_trans_internal : forall a b c,
  |- Impl (Iff a b) (Impl (Iff b c) (Iff a c)).
Proof.
  intros a b c.
  pose proof (subst_provable
    (fun n => match n with | 0 => a | 1 => b | _ => c end)
    _ iff_trans_atomic) as H.
  cbn in H. exact H.
Qed.

Lemma impl_iff_compat_atomic :
  |- Impl (Iff (Var 0) (Var 1))
       (Impl (Iff (Var 2) (Var 3))
             (Iff (Impl (Var 0) (Var 2)) (Impl (Var 1) (Var 3)))).
Proof.
  apply trivial_in_provable. apply prop_completeness.
  - cbn. unfold Iff, And, Neg. cbn. tauto.
  - intro val. cbn. unfold Iff, And, Neg. cbn.
    destruct (val 0), (val 1), (val 2), (val 3); reflexivity.
Qed.

Lemma impl_iff_compat_internal : forall X1 X2 Y1 Y2,
  |- Impl (Iff X1 X2)
       (Impl (Iff Y1 Y2)
             (Iff (Impl X1 Y1) (Impl X2 Y2))).
Proof.
  intros X1 X2 Y1 Y2.
  pose proof (subst_provable
    (fun n => match n with
              | 0 => X1 | 1 => X2 | 2 => Y1 | _ => Y2 end)
    _ impl_iff_compat_atomic) as H.
  cbn in H. exact H.
Qed.

(** Iff-chaining under a common antecedent. *)

Lemma iff_chain_under : forall A a b c,
  |- Impl A (Iff a b) ->
  |- Impl A (Iff b c) ->
  |- Impl A (Iff a c).
Proof.
  intros A a b c Hab Hbc.
  pose proof (iff_trans_internal a b c) as Htrans.
  pose proof (prov_compose _ _ _ Hab Htrans) as Hstep1.
  exact (prov_impl_chain_S A (Iff b c) (Iff a c) Hstep1 Hbc).
Qed.

(** ** Master Lemma: box-substitution congruence.
    For any [chi] (no modalisation hypothesis required) and any level [j],
    [Box 0 (Iff psi1 psi2)] entails [Box j (Iff (chi[psi1]) (chi[psi2]))].
    Proved by structural induction on [chi]; the [Form]-size of [chi] is
    the explicit decreasing measure. *)

Lemma box_subst_iff_lift : forall (p : nat) (psi1 psi2 : Form) (chi : Form) (j : nat),
  |- Impl (Box 0 (Iff psi1 psi2))
          (Box j (Iff (Subst p psi1 chi) (Subst p psi2 chi))).
Proof.
  intros p psi1 psi2 chi.
  induction chi as [k | | X IHX Y IHY | i chi' IHchi]; intro j.
  - (* chi = Var k *)
    rewrite !Subst_Var_explicit.
    destruct (Nat.eqb k p) eqn:Ekp.
    + exact (prov_box_mon_le 0 j (Iff psi1 psi2) (Nat.le_0_l j)).
    + pose proof (prov_iff_refl (Var k)) as Hrefl.
      pose proof (Nec j _ Hrefl) as Hnec.
      exact (prov_weaken _ (Box 0 (Iff psi1 psi2)) Hnec).
  - (* chi = Bot *)
    rewrite !Subst_Bot_eq.
    pose proof (prov_iff_refl Bot) as Hrefl.
    pose proof (Nec j _ Hrefl) as Hnec.
    exact (prov_weaken _ (Box 0 (Iff psi1 psi2)) Hnec).
  - (* chi = Impl X Y *)
    rewrite !Subst_Impl_eq.
    pose proof (IHX j) as IH_X.
    pose proof (IHY j) as IH_Y.
    pose proof (impl_iff_compat_internal
                  (Subst p psi1 X) (Subst p psi2 X)
                  (Subst p psi1 Y) (Subst p psi2 Y)) as Hcompat.
    pose proof (Nec j _ Hcompat) as HcompatN.
    pose proof (Ax_BoxK j (Iff (Subst p psi1 X) (Subst p psi2 X))
                  (Impl (Iff (Subst p psi1 Y) (Subst p psi2 Y))
                        (Iff (Impl (Subst p psi1 X) (Subst p psi1 Y))
                             (Impl (Subst p psi2 X) (Subst p psi2 Y))))) as HK1.
    pose proof (MP _ _ HK1 HcompatN) as Hstep1.
    pose proof (prov_compose _ _ _ IH_X Hstep1) as Hstep2.
    exact (prov_box_chain_internal _ _ _ _ IH_Y Hstep2).
  - (* chi = Box i chi' *)
    rewrite !Subst_Box_eq.
    pose proof (IHchi i) as IH.
    pose proof (Nec j _ IH) as IHN.
    pose proof (Ax_BoxK j (Box 0 (Iff psi1 psi2))
                  (Box i (Iff (Subst p psi1 chi') (Subst p psi2 chi')))) as HK1.
    pose proof (MP _ _ HK1 IHN) as Hstep1.
    pose proof (prov_box_0_to_box_j_box_0 j (Iff psi1 psi2)) as HB0Bj.
    pose proof (prov_compose _ _ _ HB0Bj Hstep1) as Hstep2.
    pose proof (box_iff_distrib i (Subst p psi1 chi') (Subst p psi2 chi')) as Hdist.
    pose proof (Nec j _ Hdist) as HdistN.
    pose proof (Ax_BoxK j (Box i (Iff (Subst p psi1 chi') (Subst p psi2 chi')))
                  (Iff (Box i (Subst p psi1 chi')) (Box i (Subst p psi2 chi')))) as HK2.
    pose proof (MP _ _ HK2 HdistN) as Hstep3.
    exact (prov_compose _ _ _ Hstep2 Hstep3).
Qed.

(** ** Outer Lemma: with the modalisation hypothesis on phi, the substituted
    iff is provable directly (no outer Box) under [Box 0 (Iff psi1 psi2)].
    Proved by structural induction on phi (using modalisation hypothesis).
    The Box case appeals to the Master Lemma; other cases are propositional. *)

Lemma outer_subst_iff : forall (p : nat) (psi1 psi2 : Form) (phi : Form),
  modalized p phi ->
  |- Impl (Box 0 (Iff psi1 psi2))
          (Iff (Subst p psi1 phi) (Subst p psi2 phi)).
Proof.
  intros p psi1 psi2 phi.
  induction phi as [k | | X IHX Y IHY | i chi IHchi]; intro Hmod; cbn in Hmod.
  - (* Var k, must have k <> p *)
    rewrite !Subst_Var_explicit.
    destruct (Nat.eqb k p) eqn:Ekp.
    + apply Nat.eqb_eq in Ekp. subst k. exfalso. apply Hmod. reflexivity.
    + pose proof (prov_iff_refl (Var k)) as Hrefl.
      exact (prov_weaken _ (Box 0 (Iff psi1 psi2)) Hrefl).
  - (* Bot *)
    rewrite !Subst_Bot_eq.
    pose proof (prov_iff_refl Bot) as Hrefl.
    exact (prov_weaken _ (Box 0 (Iff psi1 psi2)) Hrefl).
  - (* Impl X Y *)
    destruct Hmod as [HmX HmY].
    pose proof (IHX HmX) as IH_X.
    pose proof (IHY HmY) as IH_Y.
    rewrite !Subst_Impl_eq.
    pose proof (impl_iff_compat_internal
                  (Subst p psi1 X) (Subst p psi2 X)
                  (Subst p psi1 Y) (Subst p psi2 Y)) as Hcompat.
    pose proof (prov_compose _ _ _ IH_X Hcompat) as Hstep1.
    exact (prov_impl_chain_S _ _ _ Hstep1 IH_Y).
  - (* Box i chi: modalisation on chi unnecessary; use Master Lemma. *)
    rewrite !Subst_Box_eq.
    pose proof (box_subst_iff_lift p psi1 psi2 chi i) as Hmaster.
    pose proof (box_iff_distrib i (Subst p psi1 chi) (Subst p psi2 chi)) as Hdist.
    exact (prov_compose _ _ _ Hmaster Hdist).
Qed.

(** ** Headline theorem: Sambin uniqueness for arbitrary modalised contexts. *)

Theorem sambin_uniqueness_modalised : forall (C : Form -> Form),
  modalised_in_p C ->
  forall psi1 psi2,
    |- Iff psi1 (C psi1) ->
    |- Iff psi2 (C psi2) ->
    |- Iff psi1 psi2.
Proof.
  intros C HC psi1 psi2 Hfp1 Hfp2.
  destruct HC as [p [phi [Hmod Heq]]].
  rewrite Heq in Hfp1, Hfp2.
  apply (loeb_metatheorem 0 (Iff psi1 psi2)).
  pose proof (outer_subst_iff p psi1 psi2 phi Hmod) as Houter.
  pose proof (prov_weaken _ (Box 0 (Iff psi1 psi2)) Hfp1) as Hfp1_w.
  pose proof (prov_iff_sym _ _ Hfp2) as Hfp2_sym.
  pose proof (prov_weaken _ (Box 0 (Iff psi1 psi2)) Hfp2_sym) as Hfp2_w.
  pose proof (iff_chain_under _ psi1 (Subst p psi1 phi) (Subst p psi2 phi)
                Hfp1_w Houter) as Hstep1.
  exact (iff_chain_under _ psi1 (Subst p psi2 phi) psi2 Hstep1 Hfp2_w).
Qed.

(** ** Sanity checks: the headline subsumes the existing single-class
    uniqueness theorems for Box-atomic and Loeb-form contexts.  Both choose
    the dummy substitution variable [0]; the choice is immaterial since
    [Subst 0 psi (Box n (Var 0)) = Box n psi] and similarly for the
    Loeb-form context when [0 ∉ free_vars X]. *)

Corollary sambin_uniqueness_modalised_box_atomic : forall n psi1 psi2,
  |- Iff psi1 (Box n psi1) ->
  |- Iff psi2 (Box n psi2) ->
  |- Iff psi1 psi2.
Proof.
  intros n psi1 psi2 H1 H2.
  apply (sambin_uniqueness_modalised (fun X => Box n X)).
  - exists 0, (Box n (Var 0)). split.
    + cbn. exact I.
    + intro psi. unfold Subst. simpl. reflexivity.
  - exact H1.
  - exact H2.
Qed.

Corollary sambin_uniqueness_modalised_loeb_form : forall n X psi1 psi2,
  ~ In 0 (free_vars X) ->
  |- Iff psi1 (Box n (Impl psi1 X)) ->
  |- Iff psi2 (Box n (Impl psi2 X)) ->
  |- Iff psi1 psi2.
Proof.
  intros n X psi1 psi2 HnoX H1 H2.
  apply (sambin_uniqueness_modalised (fun Y => Box n (Impl Y X))).
  - exists 0, (Box n (Impl (Var 0) X)). split.
    + cbn. exact I.
    + intro psi. unfold Subst. simpl.
      pose proof (Subst_no_occurrence 0 psi X HnoX) as HX.
      unfold Subst in HX. rewrite HX. reflexivity.
  - exact H1.
  - exact H2.
Qed.
