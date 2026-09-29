From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23.
Open Scope fo_scope.

(** ** Rows rewritten along equations of their last two fields. *)

Lemma FOPrH_tblex_cong : forall n G tg a1 a2 a3 r a3' r',
  FOPrH n G (FOTBLEX tg a1 a2 a3 r) ->
  FOPrH n G (FOEq a3 a3') -> FOPrH n G (FOEq r r') ->
  FOtms_avoid [tg; a1; a2; a3; r; a3'; r'] 2 1000 ->
  FOPrH n G (FOTBLEX tg a1 a2 a3' r').
Proof.
  intros n G tg a1 a2 a3 r a3' r' H E1 E2 Hav.
  assert (K1 : forall t, FOtm_avoid t 2 1000 ->
             FOsubst_f 999 t (FOTBLEX tg a1 a2 (FOVar 999) r) = FOTBLEX tg a1 a2 t r).
  { intros t Ht. rewrite FOsubst_f_TBLEX by lia. rewrite FOsubst_t_var_eq'.
    rewrite !(FOsubst_t_not_in _ 999 t) by fr_tm. reflexivity. }
  assert (K2 : forall t, FOtm_avoid t 2 1000 ->
             FOsubst_f 999 t (FOTBLEX tg a1 a2 a3' (FOVar 999)) = FOTBLEX tg a1 a2 a3' t).
  { intros t Ht. rewrite FOsubst_f_TBLEX by lia. rewrite FOsubst_t_var_eq'.
    rewrite !(FOsubst_t_not_in _ 999 t) by fr_tm. reflexivity. }
  assert (V3 : FOtm_avoid a3 2 1000) by avoid_tm.
  assert (V3' : FOtm_avoid a3' 2 1000) by avoid_tm.
  assert (Vr : FOtm_avoid r 2 1000) by avoid_tm.
  assert (Vr' : FOtm_avoid r' 2 1000) by avoid_tm.
  pose proof (FOPrH_leibniz n G 999 a3 a3' (FOTBLEX tg a1 a2 (FOVar 999) r)
                ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm])
                ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm]) E1) as L1.
  rewrite (K1 a3 V3), (K1 a3' V3') in L1. specialize (L1 H).
  pose proof (FOPrH_leibniz n G 999 r r' (FOTBLEX tg a1 a2 a3' (FOVar 999))
                ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm])
                ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm]) E2) as L2.
  rewrite (K2 r Vr), (K2 r' Vr') in L2. exact (L2 L1).
Qed.

(** ** The rows a numeral code carries. *)

Lemma FOPrH_numr_row2 : forall n G w m X s,
  FOPrH n G (FONUMR w m) -> FOtms_avoid [m; X; s] 2 1000 ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s m m).
Proof.
  intros n G w m X s H Hav.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ H)) as H2.
  apply (FOPrH_inst n G 802 X) in H2;
    [| apply FOsubst_ok_all; [fr_tm|]; apply FOsubst_ok_TBLEX; [lia | avoid_tm]].
  rewrite FOsubst_f_all_ne, FOsubst_f_TBLEX in H2 by lia.
  rewrite FOsubst_t_var_eq', FOsubst_t_var_ne, FOsubst_t_numeral in H2 by lia.
  rewrite (FOsubst_t_not_in m 802 X) in H2 by fr_tm.
  apply (FOPrH_inst n G 803 s) in H2; [| apply FOsubst_ok_TBLEX; [lia | avoid_tm]].
  rewrite FOsubst_f_TBLEX in H2 by lia.
  rewrite FOsubst_t_var_eq', FOsubst_t_numeral in H2.
  rewrite (FOsubst_t_not_in X 803 s), (FOsubst_t_not_in m 803 s) in H2 by fr_tm.
  exact H2.
Qed.

Lemma FOPrH_numr_row0 : forall n G w m y,
  FOPrH n G (FONUMR w m) -> FOtms_avoid [m; y] 2 1000 ->
  FOPrH n G (FOTBLEX FOZero y m FOZero FOZero).
Proof.
  intros n G w m y H Hav.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ H)) as H0.
  apply (FOPrH_inst n G 804 y) in H0; [| apply FOsubst_ok_TBLEX; [lia | avoid_tm]].
  rewrite FOsubst_f_TBLEX in H0 by lia.
  rewrite FOsubst_t_var_eq', FOsubst_t_zero in H0.
  rewrite (FOsubst_t_not_in m 804 y) in H0 by fr_tm.
  exact H0.
Qed.

(** ** Pattern nodes of the code shapes. *)

Lemma FOPrH_patf_leaf_elim : forall n G B env k y d C,
  FOPrH n G (FOPATF B env (CPair (CLit k) (CLit y)) d) ->
  500 <= B -> FOctx_avoid G B (B + 4) ->
  (forall w, B <= w -> w < B + 4 -> FOfree_in w C = false) ->
  FOtms_avoid (d :: env) B (B + 4) ->
  FOPrH n (G ++ [FOcpairF (FOnumeral k) (FOnumeral y) d]) C ->
  FOPrH n G C.
Proof.
  intros n G B env k y d C H HB HG HC Hav H0.
  apply (FOPrH_patf_lit_elim n G B env k (CLit y) d C H HB HG HC Hav).
  lazymatch goal with |- FOPrH _ ?G1 _ =>
    assert (H1 : FOPrH n G1 (FOcpairF (FOnumeral k) (FOVar (B + 2)) d)) by wk_in;
    assert (H2 : FOPrH n G1 (FOEq (FOVar (B + 2)) (FOnumeral y))) by wk_in
  end.
  refine (FOPrH_cut _ _ _ C (FOPrH_cpairF_cong _ _ _ _ _ _ _ _ (FOPrH_refl _ _ _) H2
                                (FOPrH_refl _ _ _) H1) _).
  refine (FOPrH_weaken n _ _ C _ H0).
  intros Y HY. apply in_app_or in HY. destruct HY as [HY|[<-|[]]].
  - apply in_or_app. left. apply in_or_app. left. exact HY.
  - apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPrH_patf_bin_elim : forall n G B env k P Q d C,
  FOPrH n G (FOPATF B env (CPair (CLit k) (CPair P Q)) d) ->
  500 <= B -> FOctx_avoid G B (B + cpat_span (CPair (CLit k) (CPair P Q))) ->
  (forall w, B <= w -> w < B + cpat_span (CPair (CLit k) (CPair P Q)) ->
     FOfree_in w C = false) ->
  FOtms_avoid (d :: env) B (B + cpat_span (CPair (CLit k) (CPair P Q))) ->
  FOPrH n (G ++ [FOcpairF (FOnumeral k) (FOVar (B + 2)) d;
                 FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2));
                 FOPATF (B + 8) env P (FOVar (B + 4));
                 FOPATF (B + 8 + 4 * cpat_pairs P) env Q (FOVar (B + 6))]) C ->
  FOPrH n G C.
Proof.
  intros n G B env k P Q d C H HB HG HC Hav H0.
  pose proof (cpat_span_le P) as HsP.
  apply (FOPrH_patf_lit_elim n G B env k (CPair P Q) d C H HB HG HC Hav).
  cbn [cpat_span cpat_pairs] in HG, HC, Hav.
  lazymatch goal with |- FOPrH _ ?G1 _ =>
    assert (H1 : FOPrH n G1 (FOPATF (B + 4) env (CPair P Q) (FOVar (B + 2)))) by wk_in
  end.
  apply (FOPrH_patf_pair_elim_self n _ (B + 4) env P Q (FOVar (B + 2)) C H1 ltac:(lia));
    [cbn [cpat_span]; ctx_list | intros w Hw1 Hw2; cbn [cpat_span] in Hw2; apply HC; lia
    | cbn [cpat_span]; avoid_tms |].
  replace (B + 4 + 4) with (B + 8) by lia.
  replace (B + 4 + 2) with (B + 6) by lia.
  replace (B + 8 + 4 * cpat_pairs P) with (B + 8 + 4 * cpat_pairs P) by lia.
  lazymatch goal with |- FOPrH _ (?G2 ++ [?X]) _ =>
    pose proof (FOPrH_last n G2 X) as HX
  end.
  refine (FOPrH_cut _ _ _ C (FOPrH_and_l _ _ _ _ HX) _).
  refine (FOPrH_cut _ _ _ C (FOPrH_weak_app _ _ _ _
            (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ HX))) _).
  refine (FOPrH_cut _ _ _ C (FOPrH_weak_app _ _ _ _ (FOPrH_weak_app _ _ _ _
            (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ HX)))) _).
  refine (FOPrH_weaken n _ _ C _ H0).
  intros Y HY. rewrite <- !app_assoc in *. cbn [app] in *.
  apply in_app_or in HY. destruct HY as [HY|HY]; [apply in_or_app; left; exact HY|].
  apply in_or_app. right. cbn [In] in HY |- *. tauto.
Qed.

Lemma FOPrH_patf_quant_elim : forall n G B env k y P d C,
  FOPrH n G (FOPATF B env (CPair (CLit k) (CPair (CLit y) P)) d) ->
  500 <= B -> FOctx_avoid G B (B + cpat_span (CPair (CLit k) (CPair (CLit y) P))) ->
  (forall w, B <= w -> w < B + cpat_span (CPair (CLit k) (CPair (CLit y) P)) ->
     FOfree_in w C = false) ->
  FOtms_avoid (d :: env) B (B + cpat_span (CPair (CLit k) (CPair (CLit y) P))) ->
  FOPrH n (G ++ [FOcpairF (FOnumeral k) (FOVar (B + 2)) d;
                 FOcpairF (FOnumeral y) (FOVar (B + 6)) (FOVar (B + 2));
                 FOPATF (B + 8) env P (FOVar (B + 6))]) C ->
  FOPrH n G C.
Proof.
  intros n G B env k y P d C H HB HG HC Hav H0.
  apply (FOPrH_patf_lit_elim n G B env k (CPair (CLit y) P) d C H HB HG HC Hav).
  cbn [cpat_span cpat_pairs] in HG, HC, Hav.
  lazymatch goal with |- FOPrH _ ?G1 _ =>
    assert (H1 : FOPrH n G1 (FOPATF (B + 4) env (CPair (CLit y) P) (FOVar (B + 2)))) by wk_in
  end.
  apply (FOPrH_patf_lit_elim n _ (B + 4) env y P (FOVar (B + 2)) C H1 ltac:(lia));
    [cbn [cpat_span cpat_pairs]; ctx_list
    | intros w Hw1 Hw2; cbn [cpat_span cpat_pairs] in Hw2; apply HC; lia
    | cbn [cpat_span cpat_pairs]; avoid_tms |].
  replace (B + 4 + 4) with (B + 8) by lia.
  replace (B + 4 + 2) with (B + 6) by lia.
  refine (FOPrH_weaken n _ _ C _ H0).
  intros Y HY. rewrite <- !app_assoc in *. cbn [app] in *.
  apply in_app_or in HY. destruct HY as [HY|HY]; [apply in_or_app; left; exact HY|].
  apply in_or_app. right. cbn [In] in HY |- *. tauto.
Qed.
