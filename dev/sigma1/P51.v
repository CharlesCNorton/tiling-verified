From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41
  P42 P43 P44 P45 P46 P47 P48 P49 P50.
Open Scope fo_scope.

(** ** Closed theorems for bounded quantifiers. *)

Lemma FOsubst_f_ltv_var : forall y s v, y <> v -> y <> S v ->
  FOsubst_f y s (FOltv v (FOVar y)) = FOltv v s.
Proof.
  intros y s v H1 H2. unfold FOltv.
  rewrite FOsubst_f_ex_ne by lia. rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_succ.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne by lia. reflexivity.
Qed.

Lemma FOsubst_ok_ltv : forall x s v t, FOin_tm (S v) s = false ->
  FOsubst_ok x s (FOltv v t) = true.
Proof. intros x s v t H. unfold FOltv. apply FOsubst_ok_ex; [exact H | apply FOsubst_ok_eq]. Qed.

Lemma FOPr_ball_base : forall v y D, y <> v -> y <> S v ->
  FOProvesTn 0 (FOImplF (FOEq FOZero (FOVar y)) (FOForall v (FOImplF (FOltv v (FOVar y)) D))).
Proof.
  intros v y D H1 H2.
  change (FOPrH 0 [] (FOImplF (FOEq FOZero (FOVar y)) (FOForall v (FOImplF (FOltv v (FOVar y)) D)))).
  apply FOPrH_intro.
  apply FOPrH_all_intro.
  { apply FOfree_ctx_app_inv; [apply FOfree_ctx_nil|].
    apply FOfree_ctx_cons; [|apply FOfree_ctx_nil]. cbn [FOfree_in FOin_tm].
    rewrite (proj2 (Nat.eqb_neq y v) H1). reflexivity. }
  apply FOPrH_intro. apply FOPrH_efq.
  assert (E0 : FOPrH 0 (([] ++ [FOEq FOZero (FOVar y)]) ++ [FOltv v (FOVar y)])
                 (FOEq FOZero (FOVar y))) by wk_in.
  pose proof (FOPrH_leibniz 0 (([] ++ [FOEq FOZero (FOVar y)]) ++ [FOltv v (FOVar y)]) y
                (FOVar y) FOZero (FOltv v (FOVar y)) (FOsubst_ok_var_self _ _)
                (FOsubst_ok_ltv y FOZero v (FOVar y) eq_refl)
                (FOPrH_eq_sym _ _ _ _ E0)) as L.
  rewrite FOsubst_f_id, FOsubst_f_ltv_var in L by assumption.
  exact (FOPrH_mp _ _ _ _ (FOPrH_thm _ _ _ (FOPr_ltv_zero 0 v)) (L (FOPrH_last _ _ _))).
Qed.

Lemma FOPr_ball_step : forall v y D, FOvars_max D < y -> S v < y ->
  FOProvesTn 0 (FOImplF (FOsubst_f v (FOVar y) D)
    (FOImplF (FOForall v (FOImplF (FOltv v (FOVar y)) D))
       (FOForall v (FOImplF (FOltv v (FOSucc (FOVar y))) D)))).
Proof.
  intros v y D HD Hv.
  change (FOPrH 0 [] (FOImplF (FOsubst_f v (FOVar y) D)
    (FOImplF (FOForall v (FOImplF (FOltv v (FOVar y)) D))
       (FOForall v (FOImplF (FOltv v (FOSucc (FOVar y))) D))))).
  apply FOPrH_intro. apply FOPrH_intro.
  apply FOPrH_all_intro.
  { apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv; [apply FOfree_ctx_nil|]|].
    - apply FOfree_ctx_cons; [apply FOfree_in_subst_away; lia | apply FOfree_ctx_nil].
    - apply FOfree_ctx_cons; [apply FOfree_in_all_self | apply FOfree_ctx_nil]. }
  apply FOPrH_intro.
  lazymatch goal with |- FOPrH _ ?G1 _ =>
    assert (H1 : FOPrH 0 G1 (FOsubst_f v (FOVar y) D)) by wk_in;
    assert (H2 : FOPrH 0 G1 (FOForall v (FOImplF (FOltv v (FOVar y)) D))) by wk_in;
    assert (H3 : FOPrH 0 G1 (FOltv v (FOSucc (FOVar y)))) by wk_in;
    assert (HG1 : forall w, S y <= w -> FOfree_ctx w G1)
  end.
  { intros w Hw.
    apply FOfree_ctx_app_inv;
      [apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv; [apply FOfree_ctx_nil|]|]|];
      (apply FOfree_ctx_cons; [|apply FOfree_ctx_nil]).
    - destruct (FOfree_in w (FOsubst_f v (FOVar y) D)) eqn:E; [|reflexivity].
      destruct (FOfree_in_subst_gen D w v (FOVar y) E) as [[_ Hf]|Hf].
      + rewrite FOfree_in_above in Hf by lia. discriminate.
      + cbn [FOin_tm] in Hf. apply Nat.eqb_eq in Hf. lia.
    - apply FOfree_in_above. cbn [FOvars_max FOmax_var_tm]. unfold FOltv.
      cbn [FOvars_max FOmax_var_tm]. lia.
    - apply FOfree_in_above. unfold FOltv. cbn [FOvars_max FOmax_var_tm]. lia. }
  refine (FOPrH_ex_elim_fresh 0 _ (S v) (S y)
            (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) (FOSucc (FOVar y))) D
            (HG1 (S y) (le_n _)) _ _ _ H3 _);
    [apply FOfree_in_above; lia | cbn [FOfree_in FOin_tm]; nat_eqb_simpl; reflexivity
    | reflexivity |].
  cbn [FOsubst_f FOsubst_t]. nat_eqb_simpl.
  lazymatch goal with |- FOPrH _ ?G2 _ =>
    assert (E1 : FOPrH 0 G2 (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S y)))) (FOSucc (FOVar y))))
      by apply FOPrH_last;
    assert (H1' : FOPrH 0 G2 (FOsubst_f v (FOVar y) D)) by wk H1;
    assert (H2' : FOPrH 0 G2 (FOForall v (FOImplF (FOltv v (FOVar y)) D))) by wk H2;
    assert (HG2 : FOfree_ctx (S (S y)) G2)
  end.
  { apply FOfree_ctx_app_inv; [apply HG1; lia|]. apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
    cbn [FOfree_in FOin_tm]. nat_eqb_simpl. reflexivity. }
  lazymatch type of E1 with FOPrH _ ?G2 _ =>
    assert (E2 : FOPrH 0 G2 (FOEq (FOPlus (FOVar v) (FOVar (S y))) (FOVar y)))
  end.
  { apply FOPrH_Q_succ_inj.
    exact (FOPrH_eq_trans _ _ _ _ _ (FOPrH_eq_sym _ _ _ _ (FOPrH_Q_plus_succ _ _ _ _)) E1). }
  apply (FOPrH_cases_zs 0 _ (FOVar (S y)) (S (S y)) D ltac:(lia)
           ltac:(cbn [FOin_tm]; apply Nat.eqb_neq; lia) HG2
           ltac:(apply FOfree_in_above; lia) ltac:(cbn [FOin_tm]; apply Nat.eqb_neq; lia)).
  - lazymatch goal with |- FOPrH _ ?G3 _ =>
      assert (Eu : FOPrH 0 G3 (FOEq (FOVar (S y)) FOZero)) by apply FOPrH_last;
      assert (Evy : FOPrH 0 G3 (FOEq (FOVar y) (FOVar v)))
    end.
    { apply FOPrH_eq_sym.
      apply (FOPrH_eq_trans _ _ _ (FOPlus (FOVar v) FOZero));
        [apply FOPrH_eq_sym; apply FOPrH_Q_plus_zero|].
      apply (FOPrH_eq_trans _ _ _ (FOPlus (FOVar v) (FOVar (S y)))).
      - apply FOPrH_congPlus; [apply FOPrH_refl | apply FOPrH_eq_sym; exact Eu].
      - apply FOPrH_weak_app. exact E2. }
    pose proof (FOPrH_leibniz 0 _ v (FOVar y) (FOVar v) D
                  (FOsubst_ok_above D v y ltac:(lia)) (FOsubst_ok_var_self D v) Evy) as L.
    rewrite FOsubst_f_id in L. apply L. apply FOPrH_weak_app. exact H1'.
  - lazymatch goal with |- FOPrH _ ?G3 _ =>
      assert (Eu : FOPrH 0 G3 (FOEq (FOVar (S y)) (FOSucc (FOVar (S (S y))))))
        by apply FOPrH_last;
      assert (Lv : FOPrH 0 G3 (FOltv v (FOVar y)))
    end.
    { unfold FOltv. apply (FOPrH_ex_intro _ _ (S v) (FOVar (S (S y)))); [reflexivity|].
      cbn [FOsubst_f FOsubst_t]. nat_eqb_simpl.
      apply (FOPrH_eq_trans _ _ _ (FOPlus (FOVar v) (FOVar (S y)))).
      - apply FOPrH_congPlus; [apply FOPrH_refl | apply FOPrH_eq_sym; exact Eu].
      - apply FOPrH_weak_app. exact E2. }
    exact (FOPrH_mp _ _ _ _ (FOPrH_all_same _ _ _ _ (FOPrH_weak_app _ _ _ _ H2')) Lv).
Qed.

Lemma FOsubst_f_ball_y : forall v y t A, v <> y -> S v <> y -> FOfree_in y A = false ->
  FOsubst_f y t (FOForall v (FOImplF (FOltv v (FOVar y)) A)) = FOForall v (FOImplF (FOltv v t) A).
Proof.
  intros v y t A H1 H2 HA. rewrite FOsubst_f_all_ne by lia. rewrite FOsubst_f_impl.
  rewrite FOsubst_f_ltv_var by lia. rewrite (FOsubst_f_not_free A y t HA). reflexivity.
Qed.

Lemma FOsubst_ok_ball_y : forall v y t A, FOin_tm v t = false -> FOin_tm (S v) t = false ->
  FOfree_in y A = false ->
  FOsubst_ok y t (FOForall v (FOImplF (FOltv v (FOVar y)) A)) = true.
Proof.
  intros v y t A H1 H2 HA. apply FOsubst_ok_all; [exact H1|]. apply FOsubst_ok_impl;
    [apply FOsubst_ok_ltv; exact H2 | apply FOsubst_ok_not_free; exact HA].
Qed.

Lemma FOPr_ball_final : forall v y t A,
  FOin_tm v t = false -> FOin_tm (S v) t = false -> FOfree_in y A = false ->
  v <> y -> S v <> y ->
  FOProvesTn 0 (FOImplF (FOEq t (FOVar y))
    (FOImplF (FOForall v (FOImplF (FOltv v (FOVar y)) A)) (FOForall v (FOImplF (FOltv v t) A)))).
Proof.
  intros v y t A Hv HSv HA H1 H2.
  change (FOPrH 0 [] (FOImplF (FOEq t (FOVar y))
    (FOImplF (FOForall v (FOImplF (FOltv v (FOVar y)) A)) (FOForall v (FOImplF (FOltv v t) A))))).
  apply FOPrH_intro. apply FOPrH_intro.
  pose proof (FOPrH_leibniz 0 (([] ++ [FOEq t (FOVar y)]) ++
                [FOForall v (FOImplF (FOltv v (FOVar y)) A)]) y (FOVar y) t
                (FOForall v (FOImplF (FOltv v (FOVar y)) A)) (FOsubst_ok_var_self _ _)
                (FOsubst_ok_ball_y v y t A Hv HSv HA)) as L.
  rewrite FOsubst_f_id, FOsubst_f_ball_y in L by assumption.
  apply L; [apply FOPrH_eq_sym; wk_in | apply FOPrH_last].
Qed.

Lemma FOPr_bexneg_final : forall v y t A,
  FOin_tm v t = false -> FOin_tm (S v) t = false -> FOfree_in y A = false ->
  v <> y -> S v <> y -> FOin_tm v (FOVar y) = false ->
  FOProvesTn 0 (FOImplF (FOEq t (FOVar y))
    (FOImplF (FOForall v (FOImplF (FOltv v (FOVar y)) (FONeg A)))
       (FONeg (FOExists v (FOAnd (FOltv v t) A))))).
Proof.
  intros v y t A Hv HSv HA H1 H2 Hvy.
  change (FOPrH 0 [] (FOImplF (FOEq t (FOVar y))
    (FOImplF (FOForall v (FOImplF (FOltv v (FOVar y)) (FONeg A)))
       (FONeg (FOExists v (FOAnd (FOltv v t) A)))))).
  apply FOPrH_intro. apply FOPrH_intro.
  assert (HNA : FOfree_in y (FONeg A) = false)
    by (unfold FONeg; cbn [FOfree_in]; rewrite HA; reflexivity).
  pose proof (FOPrH_leibniz 0 (([] ++ [FOEq t (FOVar y)]) ++
                [FOForall v (FOImplF (FOltv v (FOVar y)) (FONeg A))]) y (FOVar y) t
                (FOForall v (FOImplF (FOltv v (FOVar y)) (FONeg A))) (FOsubst_ok_var_self _ _)
                (FOsubst_ok_ball_y v y t (FONeg A) Hv HSv HNA)) as L.
  rewrite FOsubst_f_id, FOsubst_f_ball_y in L by assumption.
  assert (H3 : FOPrH 0 (([] ++ [FOEq t (FOVar y)]) ++
                 [FOForall v (FOImplF (FOltv v (FOVar y)) (FONeg A))])
                 (FOForall v (FOImplF (FOltv v t) (FONeg A))))
    by (apply L; [apply FOPrH_eq_sym; wk_in | apply FOPrH_last]).
  unfold FONeg at 2. apply FOPrH_intro.
  refine (FOPrH_ex_elim 0 _ v _ FOFalseF _ _ (FOPrH_last _ _ _) _).
  - apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv|]|].
    + apply FOfree_ctx_nil.
    + apply FOfree_ctx_cons; [|apply FOfree_ctx_nil]. cbn [FOfree_in].
      rewrite Hv, Hvy. reflexivity.
    + apply FOfree_ctx_cons; [apply FOfree_in_all_self | apply FOfree_ctx_nil].
    + apply FOfree_ctx_cons; [apply FOfree_in_ex_self | apply FOfree_ctx_nil].
  - reflexivity.
  - lazymatch goal with |- FOPrH _ ?G4 _ =>
      assert (H4 : FOPrH 0 G4 (FOForall v (FOImplF (FOltv v t) (FONeg A)))) by wk H3;
      assert (H5 : FOPrH 0 G4 (FOAnd (FOltv v t) A)) by apply FOPrH_last
    end.
    apply FOPrH_all_same in H4. unfold FONeg in H4.
    exact (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ H4 (FOPrH_and_l _ _ _ _ H5)) (FOPrH_and_r _ _ _ _ H5)).
Qed.

Lemma FOPr_ball_neg : forall v u t A, u <> S v -> FOin_tm (S v) t = false ->
  FOProvesTn 0 (FOImplF (FOEq (FOPlus (FOVar v) (FOSucc (FOVar u))) t)
    (FOImplF (FONeg A) (FONeg (FOForall v (FOImplF (FOltv v t) A))))).
Proof.
  intros v u t A H1 H2.
  change (FOPrH 0 [] (FOImplF (FOEq (FOPlus (FOVar v) (FOSucc (FOVar u))) t)
    (FOImplF (FONeg A) (FONeg (FOForall v (FOImplF (FOltv v t) A)))))).
  apply FOPrH_intro. apply FOPrH_intro. unfold FONeg at 2. apply FOPrH_intro.
  lazymatch goal with |- FOPrH _ ?G1 _ =>
    assert (E : FOPrH 0 G1 (FOEq (FOPlus (FOVar v) (FOSucc (FOVar u))) t)) by wk_in;
    assert (NA : FOPrH 0 G1 (FONeg A)) by wk_in;
    assert (HA : FOPrH 0 G1 (FOForall v (FOImplF (FOltv v t) A))) by apply FOPrH_last;
    assert (L : FOPrH 0 G1 (FOltv v t))
  end.
  { unfold FOltv. apply (FOPrH_ex_intro _ _ (S v) (FOVar u)); [reflexivity|].
    cbn [FOsubst_f FOsubst_t]. rewrite Nat.eqb_refl.
    rewrite (proj2 (Nat.eqb_neq v (S v)) ltac:(lia)). rewrite (FOsubst_t_not_in t (S v) _ H2).
    exact E. }
  unfold FONeg in NA.
  exact (FOPrH_mp _ _ _ _ NA (FOPrH_mp _ _ _ _ (FOPrH_all_same _ _ _ _ HA) L)).
Qed.

Lemma FOPr_bex_pos : forall v u t A, u <> S v -> FOin_tm (S v) t = false ->
  FOProvesTn 0 (FOImplF (FOEq (FOPlus (FOVar v) (FOSucc (FOVar u))) t)
    (FOImplF A (FOExists v (FOAnd (FOltv v t) A)))).
Proof.
  intros v u t A H1 H2.
  change (FOPrH 0 [] (FOImplF (FOEq (FOPlus (FOVar v) (FOSucc (FOVar u))) t)
    (FOImplF A (FOExists v (FOAnd (FOltv v t) A))))).
  apply FOPrH_intro. apply FOPrH_intro.
  apply (FOPrH_ex_intro _ _ v (FOVar v)); [apply FOsubst_ok_var_self|]. rewrite FOsubst_f_id.
  apply FOPrH_and_intro; [|apply FOPrH_last].
  unfold FOltv. apply (FOPrH_ex_intro _ _ (S v) (FOVar u)); [reflexivity|].
  cbn [FOsubst_f FOsubst_t]. rewrite Nat.eqb_refl.
  rewrite (proj2 (Nat.eqb_neq v (S v)) ltac:(lia)). rewrite (FOsubst_t_not_in t (S v) _ H2).
  wk_in.
Qed.
