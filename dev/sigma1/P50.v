From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41
  P42 P43 P44 P45 P46 P47 P48 P49.
Open Scope fo_scope.

(** ** Patterns of a formula with a variable renamed to a slot name. *)

Lemma cpat_tm_subst_var : forall t v y rho j, FOin_tm y t = false -> rho y = Some j ->
  cpat_tm rho (FOsubst_t v (FOVar y) t) = cpat_tm (rho_sub (Some v) j rho) t.
Proof.
  induction t as [z| |a IH|a IHa b IHb|a IHa b IHb]; intros v y rho j Hy Hj;
    cbn [FOsubst_t cpat_tm].
  - unfold rho_sub. destruct (Nat.eqb_spec z v) as [->|Hzv].
    + cbn [cpat_tm]. rewrite Hj. reflexivity.
    + reflexivity.
  - reflexivity.
  - rewrite (IH v y rho j Hy Hj). reflexivity.
  - cbn [FOin_tm] in Hy. apply Bool.orb_false_iff in Hy as [H1 H2].
    rewrite (IHa v y rho j H1 Hj), (IHb v y rho j H2 Hj). reflexivity.
  - cbn [FOin_tm] in Hy. apply Bool.orb_false_iff in Hy as [H1 H2].
    rewrite (IHa v y rho j H1 Hj), (IHb v y rho j H2 Hj). reflexivity.
Qed.

Lemma cpat_f_subst_var : forall A v y rho j, FOvars_max A < y -> rho y = Some j ->
  cpat_f rho (FOsubst_f v (FOVar y) A) = cpat_f (rho_sub (Some v) j rho) A.
Proof.
  induction A as [a b| |B IHB C IHC|z B IHB|z B IHB]; intros v y rho j Hy Hj;
    cbn [FOvars_max] in Hy.
  - cbn [FOsubst_f cpat_f].
    rewrite (cpat_tm_subst_var a v y rho j), (cpat_tm_subst_var b v y rho j)
      by (first [apply FOin_tm_above; lia | exact Hj]).
    reflexivity.
  - reflexivity.
  - cbn [FOsubst_f cpat_f]. rewrite (IHB v y rho j), (IHC v y rho j) by (lia || exact Hj).
    reflexivity.
  - destruct (Nat.eqb_spec z v) as [->|Hzv].
    + rewrite FOsubst_f_all_self. cbn [cpat_f]. f_equal.
      apply cpat_f_ext. intros z0. symmetry. apply rho_hide_sub_self.
    + rewrite FOsubst_f_all_ne by exact Hzv. cbn [cpat_f]. f_equal.
      rewrite (IHB v y (rho_hide z rho) j) by
        (lia || (unfold rho_hide; rewrite (proj2 (Nat.eqb_neq y z) ltac:(lia)); exact Hj)).
      apply cpat_f_ext. intros z0. apply rho_sub_hide. cbn [ox_eq].
      apply Nat.eqb_neq. exact Hzv.
  - destruct (Nat.eqb_spec z v) as [->|Hzv].
    + rewrite FOsubst_f_ex_self. cbn [cpat_f]. f_equal.
      apply cpat_f_ext. intros z0. symmetry. apply rho_hide_sub_self.
    + rewrite FOsubst_f_ex_ne by exact Hzv. cbn [cpat_f]. f_equal.
      rewrite (IHB v y (rho_hide z rho) j) by
        (lia || (unfold rho_hide; rewrite (proj2 (Nat.eqb_neq y z) ltac:(lia)); exact Hj)).
      apply cpat_f_ext. intros z0. apply rho_sub_hide. cbn [ox_eq].
      apply Nat.eqb_neq. exact Hzv.
Qed.

(** ** Bounded quantifiers: facts of the object theory. *)

Lemma FOfree_in_neg_all_self : forall v X, FOfree_in v (FONeg (FOForall v X)) = false.
Proof. intros v X. unfold FONeg. cbn [FOfree_in]. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma FOfree_in_neg_ex_self : forall v X, FOfree_in v (FONeg (FOExists v X)) = false.
Proof. intros v X. unfold FONeg. cbn [FOfree_in]. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma FOPr_ltv_zero : forall n v, FOProvesTn n (FONeg (FOltv v FOZero)).
Proof.
  intros n v. change (FOPrH n [] (FONeg (FOltv v FOZero))). unfold FONeg. apply FOPrH_intro.
  unfold FOltv.
  refine (FOPrH_ex_elim n ([] ++ [FOExists (S v) (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
            FOZero)]) (S v) _ _ _ _ (FOPrH_last _ _ _) _);
    [apply FOfree_ctx_cons; [apply FOfree_in_ex_self | apply FOfree_ctx_nil] | reflexivity |].
  apply (FOPrH_Q_succ_nonzero _ _ (FOPlus (FOVar v) (FOVar (S v)))).
  apply (FOPrH_eq_trans _ _ _ (FOPlus (FOVar v) (FOSucc (FOVar (S v)))));
    [apply FOPrH_eq_sym; apply FOPrH_Q_plus_succ | apply FOPrH_last].
Qed.

Lemma FOPr_ltv_succ : forall n v t, FOin_tm (S v) t = false ->
  FOProvesTn n (FOImplF (FOltv v t) (FOltv v (FOSucc t))).
Proof.
  intros n v t Ht. change (FOPrH n [] (FOImplF (FOltv v t) (FOltv v (FOSucc t)))).
  apply FOPrH_intro. unfold FOltv at 1.
  refine (FOPrH_ex_elim n ([] ++ [FOExists (S v) (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
            t)]) (S v) _ _ _ _ (FOPrH_last _ _ _) _);
    [apply FOfree_ctx_cons; [apply FOfree_in_ex_self | apply FOfree_ctx_nil]
    | unfold FOltv; apply FOfree_in_ex_self |].
  unfold FOltv. apply (FOPrH_ex_intro _ _ (S v) (FOSucc (FOVar (S v))));
    [reflexivity|].
  cbn [FOsubst_f FOsubst_t]. rewrite Nat.eqb_refl.
  rewrite (proj2 (Nat.eqb_neq v (S v)) ltac:(lia)).
  rewrite (FOsubst_t_not_in t (S v) _ Ht).
  apply (FOPrH_eq_trans _ _ _ (FOSucc (FOPlus (FOVar v) (FOSucc (FOVar (S v)))))).
  - apply FOPrH_Q_plus_succ.
  - apply FOPrH_congS. apply FOPrH_last.
Qed.

Lemma FOPr_ltv_self : forall n v t, FOin_tm (S v) t = false ->
  FOProvesTn n (FOExists (S v) (FOEq (FOPlus t (FOSucc (FOVar (S v)))) (FOSucc t))).
Proof.
  intros n v t Ht.
  change (FOPrH n [] (FOExists (S v) (FOEq (FOPlus t (FOSucc (FOVar (S v)))) (FOSucc t)))).
  apply (FOPrH_ex_intro _ _ (S v) FOZero); [reflexivity|].
  cbn [FOsubst_f FOsubst_t]. rewrite Nat.eqb_refl. rewrite (FOsubst_t_not_in t (S v) _ Ht).
  apply FOPrH_ring. fo_ring.
Qed.

Lemma FOPr_not_all : forall n v X,
  FOProvesTn n (FOImplF (FONeg (FOForall v X)) (FOExists v (FONeg X))).
Proof.
  intros n v X. change (FOPrH n [] (FOImplF (FONeg (FOForall v X)) (FOExists v (FONeg X)))).
  apply FOPrH_intro. cbn [app].
  apply (FOPrH_or_elim n _ (FOExists v (FONeg X)) (FONeg (FOExists v (FONeg X))) _
           (FOPrH_em _ _ _)); [apply FOPrH_last|].
  apply FOPrH_efq.
  apply (FOPrH_mp _ _ (FOForall v X)); [apply FOPrH_assum; left; reflexivity|].
  apply FOPrH_all_intro.
  { apply FOfree_ctx_cons; [apply FOfree_in_neg_all_self|].
    apply FOfree_ctx_cons; [apply FOfree_in_neg_ex_self | apply FOfree_ctx_nil]. }
  apply (FOPrH_or_elim n _ X (FONeg X) _ (FOPrH_em _ _ _)); [apply FOPrH_last|].
  apply FOPrH_efq.
  apply (FOPrH_mp _ _ (FOExists v (FONeg X)));
    [apply FOPrH_assum; apply in_or_app; left; right; left; reflexivity|].
  apply (FOPrH_ex_intro _ _ v (FOVar v)); [apply FOsubst_ok_var_self|].
  rewrite FOsubst_f_id. apply FOPrH_last.
Qed.

Lemma FOPr_not_ex_and : forall n v L X,
  FOProvesTn n (FOImplF (FONeg (FOExists v (FOAnd L X))) (FOForall v (FOImplF L (FONeg X)))).
Proof.
  intros n v L X.
  change (FOPrH n [] (FOImplF (FONeg (FOExists v (FOAnd L X))) (FOForall v (FOImplF L (FONeg X))))).
  apply FOPrH_intro. cbn [app].
  apply FOPrH_all_intro.
  { apply FOfree_ctx_cons; [apply FOfree_in_neg_ex_self | apply FOfree_ctx_nil]. }
  apply FOPrH_intro. unfold FONeg at 2. apply FOPrH_intro.
  apply (FOPrH_mp _ _ (FOExists v (FOAnd L X))); [apply FOPrH_assum; left; reflexivity|].
  apply (FOPrH_ex_intro _ _ v (FOVar v)); [apply FOsubst_ok_var_self|].
  rewrite FOsubst_f_id. apply FOPrH_and_intro.
  - apply FOPrH_assum. right. left. reflexivity.
  - apply FOPrH_last.
Qed.
