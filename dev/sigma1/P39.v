From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38.
Open Scope fo_scope.

(** ** Numeral codes are unique. *)

Definition FONUMU : FOFormula :=
  FOForall 1001 (FOForall 1002
    (FOTBLEX (FOnumeral 5) (FOVar 1000) FOZero FOZero (FOVar 1001) .->
     FOTBLEX (FOnumeral 5) (FOVar 1000) FOZero FOZero (FOVar 1002) .->
     FOEq (FOVar 1001) (FOVar 1002))).

Lemma FOsubst_f_NUMU : forall t, FOtms_avoid [t] 2 50 -> FOtms_avoid [t] 1001 1003 ->
  FOsubst_f 1000 t FONUMU =
  FOForall 1001 (FOForall 1002
    (FOTBLEX (FOnumeral 5) t FOZero FOZero (FOVar 1001) .->
     FOTBLEX (FOnumeral 5) t FOZero FOZero (FOVar 1002) .->
     FOEq (FOVar 1001) (FOVar 1002))).
Proof.
  intros t H1 H2. unfold FONUMU.
  rewrite !FOsubst_f_all_ne, !FOsubst_f_impl, !FOsubst_f_TBLEX, FOsubst_f_eq by lia.
  rewrite !FOsubst_t_var_eq', !FOsubst_t_var_ne, !FOsubst_t_numeral, !FOsubst_t_zero by lia.
  reflexivity.
Qed.

Lemma FOsubst_ok_NUMU : forall t, FOtms_avoid [t] 2 50 -> FOtms_avoid [t] 1001 1003 ->
  FOsubst_ok 1000 t FONUMU = true.
Proof.
  intros t H1 H2. unfold FONUMU.
  apply FOsubst_ok_all; [fr_tm|]. apply FOsubst_ok_all; [fr_tm|].
  apply FOsubst_ok_impl; [apply FOsubst_ok_TBLEX; [lia | avoid_tm]|].
  apply FOsubst_ok_impl; [apply FOsubst_ok_TBLEX; [lia | avoid_tm] | apply FOsubst_ok_eq].
Qed.

Theorem FOPr_num5_unique : forall n, FOProvesTn n (FOForall 1000 FONUMU).
Proof.
  intro n. change (FOPrH n [] (FOForall 1000 FONUMU)).
  apply FOPrH_ind; [apply FOfree_ctx_nil| |].
  - rewrite FOsubst_f_NUMU by avoid_tms.
    apply FOPrH_all_intro; [apply FOfree_ctx_nil|]. apply FOPrH_all_intro; [apply FOfree_ctx_nil|].
    apply FOPrH_intro. apply FOPrH_intro.
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (HGc : FOctx_avoid Gc 2 1000) by ctx_list end.
    pose proof (FOPrH_num5_inv0 n _ (FOVar 1001) HGc ltac:(avoid_tms) ltac:(wk_in)) as C1.
    pose proof (FOPrH_num5_inv0 n _ (FOVar 1002) HGc ltac:(avoid_tms) ltac:(wk_in)) as C2.
    exact (FOPrH_cpair_fun n _ _ _ (FOVar 1001) (FOVar 1002) ltac:(avoid_tms) C1 C2).
  - rewrite FOsubst_f_NUMU by avoid_tms.
    apply FOPrH_all_intro; [apply FOfree_ctx_b; vm_compute; reflexivity|].
    apply FOPrH_all_intro; [apply FOfree_ctx_b; vm_compute; reflexivity|].
    apply FOPrH_intro. apply FOPrH_intro.
    unfold FONUMU at 1.
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (HGc : FOctx_avoid Gc 2 1000) by ctx_list;
      assert (T1 : FOPrH n Gc (FOTBLEX (FOnumeral 5) (FOSucc (FOVar 1000)) FOZero FOZero
                                 (FOVar 1001))) by wk_in;
      assert (T2 : FOPrH n Gc (FOTBLEX (FOnumeral 5) (FOSucc (FOVar 1000)) FOZero FOZero
                                 (FOVar 1002))) by wk_in
    end.
    apply (FOPrH_num5_invS n _ (FOVar 1000) (FOVar 1001) 1003 (FOEq (FOVar 1001) (FOVar 1002))
             HGc ltac:(avoid_tms) ltac:(lia)
             ltac:(free_ctx) ltac:(reflexivity) ltac:(avoid_tms)
             ltac:(intros v ? ?; cbn [FOfree_in FOin_tm]; apply Bool.orb_false_iff; split;
                   apply Nat.eqb_neq; lia) T1).
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (HGc2 : FOctx_avoid Gc 2 1000) by ctx_list;
      assert (T2' : FOPrH n Gc (FOTBLEX (FOnumeral 5) (FOSucc (FOVar 1000)) FOZero FOZero
                                  (FOVar 1002))) by wk T2
    end.
    apply (FOPrH_num5_invS n _ (FOVar 1000) (FOVar 1002) 1004 (FOEq (FOVar 1001) (FOVar 1002))
             HGc2 ltac:(avoid_tms) ltac:(lia)
             ltac:(free_ctx) ltac:(reflexivity) ltac:(avoid_tms)
             ltac:(intros v ? ?; cbn [FOfree_in FOin_tm]; apply Bool.orb_false_iff; split;
                   apply Nat.eqb_neq; lia) T2').
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (C1 : FOPrH n Gc (FOcpairF (FOnumeral 2) (FOVar 1003) (FOVar 1001))) by wk_in;
      assert (U1 : FOPrH n Gc (FOTBLEX (FOnumeral 5) (FOVar 1000) FOZero FOZero (FOVar 1003)))
        by wk_in;
      assert (C2 : FOPrH n Gc (FOcpairF (FOnumeral 2) (FOVar 1004) (FOVar 1002))) by wk_in;
      assert (U2 : FOPrH n Gc (FOTBLEX (FOnumeral 5) (FOVar 1000) FOZero FOZero (FOVar 1004)))
        by wk_in;
      assert (IH : FOPrH n Gc FONUMU) by wk_in
    end.
    unfold FONUMU in IH.
    apply (FOPrH_inst _ _ 1001 (FOVar 1003)) in IH;
      [| apply FOsubst_ok_all; [fr_tm|]; apply FOsubst_ok_impl;
         [apply FOsubst_ok_TBLEX; [lia | avoid_tm]|];
         apply FOsubst_ok_impl; [apply FOsubst_ok_TBLEX; [lia | avoid_tm] | apply FOsubst_ok_eq]].
    rewrite FOsubst_f_all_ne, !FOsubst_f_impl, !FOsubst_f_TBLEX, FOsubst_f_eq in IH by lia.
    rewrite !FOsubst_t_var_eq', !FOsubst_t_var_ne, !FOsubst_t_numeral, !FOsubst_t_zero in IH
      by lia.
    apply (FOPrH_inst _ _ 1002 (FOVar 1004)) in IH;
      [| apply FOsubst_ok_impl; [apply FOsubst_ok_TBLEX; [lia | avoid_tm]|];
         apply FOsubst_ok_impl; [apply FOsubst_ok_TBLEX; [lia | avoid_tm] | apply FOsubst_ok_eq]].
    rewrite !FOsubst_f_impl, !FOsubst_f_TBLEX, FOsubst_f_eq in IH by lia.
    rewrite !FOsubst_t_var_eq', !FOsubst_t_var_ne, !FOsubst_t_numeral, !FOsubst_t_zero in IH
      by lia.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ IH U1) U2) as E34.
    pose proof (FOPrH_cpairF_cong _ _ _ _ _ _ _ _ (FOPrH_refl _ _ _) E34 (FOPrH_refl _ _ _) C1)
      as C1'.
    exact (FOPrH_cpair_fun n _ _ _ (FOVar 1001) (FOVar 1002) ltac:(avoid_tms) C1' C2).
Qed.

Lemma FOPrH_num5_unique : forall n G a m m',
  FOPrH n G (FOTBLEX (FOnumeral 5) a FOZero FOZero m) ->
  FOPrH n G (FOTBLEX (FOnumeral 5) a FOZero FOZero m') ->
  FOtms_avoid [a; m; m'] 2 50 -> FOtms_avoid [a; m; m'] 440 442 ->
  FOtms_avoid [a; m; m'] 1001 1003 ->
  FOPrH n G (FOEq m m').
Proof.
  intros n G a m m' H1 H2 Hav1 Hav2 Hav3.
  pose proof (FOPrH_thm n G _ (FOPr_num5_unique n)) as U.
  apply (FOPrH_inst n G 1000 a) in U; [|apply FOsubst_ok_NUMU; avoid_tms].
  rewrite FOsubst_f_NUMU in U by avoid_tms.
  apply (FOPrH_inst _ _ 1001 m) in U;
    [| apply FOsubst_ok_all; [fr_tm|]; apply FOsubst_ok_impl;
       [apply FOsubst_ok_TBLEX; [lia | avoid_tm]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_TBLEX; [lia | avoid_tm] | apply FOsubst_ok_eq]].
  rewrite FOsubst_f_all_ne, !FOsubst_f_impl, !FOsubst_f_TBLEX, FOsubst_f_eq in U by lia.
  rewrite !FOsubst_t_var_eq', !FOsubst_t_var_ne, !FOsubst_t_numeral, !FOsubst_t_zero in U
    by lia.
  rewrite (FOsubst_t_not_in a 1001 m) in U by fr_tm.
  apply (FOPrH_inst _ _ 1002 m') in U;
    [| apply FOsubst_ok_impl; [apply FOsubst_ok_TBLEX; [lia | avoid_tm]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_TBLEX; [lia | avoid_tm] | apply FOsubst_ok_eq]].
  rewrite !FOsubst_f_impl, !FOsubst_f_TBLEX, FOsubst_f_eq in U by lia.
  rewrite !FOsubst_t_var_eq', !FOsubst_t_numeral, !FOsubst_t_zero in U.
  rewrite (FOsubst_t_not_in a 1002 m'), (FOsubst_t_not_in m 1002 m') in U by fr_tm.
  exact (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ U H1) H2).
Qed.
