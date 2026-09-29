From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27.
Open Scope fo_scope.

(** ** Free-occurrence rows for the code of a formula (tag [1]). *)

Lemma FOPrH_free_f : forall n x A G rho env B a,
  SlotCtx n env G -> (forall z i, rho z = Some i -> i < length env) ->
  FOPrH n G (FOPATF B env (cpat_f rho A) a) ->
  1000 <= B -> FOctx_avoid G B (B + cpat_span (cpat_f rho A)) ->
  FOtms_avoid (a :: env) B (B + cpat_span (cpat_f rho A)) ->
  FOtms_avoid (a :: env) 2 1000 ->
  FOPrH n G (FOTBLEX (FOnumeral 1) (FOnumeral x) a FOZero (bnum (lit_free_f rho x A))).
Proof.
  intros n x A.
  induction A as [u w| |P IHP Q IHQ|y P IHP|y P IHP];
    intros G rho env B a HS Hrho Ha HB HGs Havs Hlo; pose proof HS as [HG Hslot].
  - cbn [cpat_f lit_free_f pEqP] in *.
    pose proof (cpat_span_le (cpat_tm rho u)) as Hsu.
    span_h HGs. span_h Havs.
    apply (FOPrH_patf_bin_elim n G B env 0 _ _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 0) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G1 (FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hua : FOPrH n G1 (FOPATF (B + 8) env (cpat_tm rho u) (FOVar (B + 4)))) by wk_in;
      assert (Hwa : FOPrH n G1 (FOPATF (B + 8 + 4 * cpat_pairs (cpat_tm rho u)) env
                                  (cpat_tm rho w) (FOVar (B + 6)))) by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    pose proof (FOPrH_occ_tm n x u _ rho env (B + 8) (FOVar (B + 4)) HS1 Hrho Hua ltac:(lia)
                  ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms)) as Ru.
    destruct (lit_occ_tm rho x u) eqn:Eu; cbn [orb].
    + exact (FOPrH_N1_eq_one n _ (FOnumeral x) a (FOVar (B + 2)) (FOVar (B + 4))
               (FOVar (B + 6)) ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) Ru Hka Hpa).
    + pose proof (FOPrH_occ_tm n x w _ rho env (B + 8 + 4 * cpat_pairs (cpat_tm rho u))
                    (FOVar (B + 6)) HS1 Hrho Hwa ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms)
                    ltac:(avoid_tms)) as Rw.
      exact (FOPrH_N1_eq_zero n _ (FOnumeral x) a (bnum (lit_occ_tm rho x w)) (FOVar (B + 2))
               (FOVar (B + 4)) (FOVar (B + 6)) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Ru Rw Hka Hpa).
  - cbn [cpat_f lit_free_f] in *. span_h HGs. span_h Havs.
    apply (FOPrH_patf_leaf_elim n G B env 1 0 a _ Ha ltac:(lia) HGs);
      [intros w1 H1 H2; free_fm | avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hca : FOPrH n G1 (FOcpairF (FOnumeral 1) (FOnumeral 0) a)) by apply FOPrH_last;
      assert (HG1 : FOctx_avoid G1 2 1000) by ctx_list
    end.
    exact (FOPrH_N1_false n _ (FOnumeral x) a ltac:(intros w1 ? ?; apply HG1; lia)
             ltac:(avoid_tms) Hca).
  - cbn [cpat_f lit_free_f pImpP] in *.
    pose proof (cpat_span_le (cpat_f rho P)) as Hsu.
    span_h HGs. span_h Havs.
    apply (FOPrH_patf_bin_elim n G B env 2 _ _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 2) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G1 (FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hua : FOPrH n G1 (FOPATF (B + 8) env (cpat_f rho P) (FOVar (B + 4)))) by wk_in;
      assert (Hwa : FOPrH n G1 (FOPATF (B + 8 + 4 * cpat_pairs (cpat_f rho P)) env
                                  (cpat_f rho Q) (FOVar (B + 6)))) by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    pose proof (IHP _ rho env (B + 8) (FOVar (B + 4)) HS1 Hrho Hua ltac:(lia) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms)) as Ru.
    destruct (lit_free_f rho x P) eqn:Eu; cbn [orb].
    + exact (FOPrH_N1_impl_one n _ (FOnumeral x) a (FOVar (B + 2)) (FOVar (B + 4))
               (FOVar (B + 6)) ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) Ru Hka Hpa).
    + pose proof (IHQ _ rho env (B + 8 + 4 * cpat_pairs (cpat_f rho P)) (FOVar (B + 6)) HS1
                    Hrho Hwa ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms)) as Rw.
      exact (FOPrH_N1_impl_zero n _ (FOnumeral x) a (bnum (lit_free_f rho x Q)) (FOVar (B + 2))
               (FOVar (B + 4)) (FOVar (B + 6)) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Ru Rw Hka Hpa).
  - cbn [cpat_f lit_free_f pAllP] in *. span_h HGs. span_h Havs.
    apply (FOPrH_patf_quant_elim n G B env 3 y _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 3) (FOVar (B + 2)) a)) by wk_in;
      assert (Hya : FOPrH n G1 (FOcpairF (FOnumeral y) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hpa : FOPrH n G1 (FOPATF (B + 8) env (cpat_f (rho_hide y rho) P) (FOVar (B + 6))))
        by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    destruct (Nat.eqb_spec y x) as [->|Hne].
    + exact (FOPrH_N1_quant_eq n _ (FOnumeral x) a 3 (FOVar (B + 2)) (FOnumeral x)
               (FOVar (B + 6)) (or_introl eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Hka Hya (FOPrH_refl _ _ _)).
    + assert (Hrho' : forall z i, rho_hide y rho z = Some i -> i < length env).
      { intros z i Hz. unfold rho_hide in Hz. destruct (Nat.eqb z y); [discriminate|].
        exact (Hrho z i Hz). }
      pose proof (IHP _ (rho_hide y rho) env (B + 8) (FOVar (B + 6)) HS1 Hrho' Hpa ltac:(lia)
                    ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms)) as R.
      exact (FOPrH_N1_quant_ne n _ (FOnumeral x) a (bnum (lit_free_f (rho_hide y rho) x P)) 3
               (FOVar (B + 2)) (FOnumeral y) (FOVar (B + 6)) (or_introl eq_refl)
               ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) R Hka Hya
               (FOPrH_num_neq n _ y x Hne)).
  - cbn [cpat_f lit_free_f pExP] in *. span_h HGs. span_h Havs.
    apply (FOPrH_patf_quant_elim n G B env 4 y _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 4) (FOVar (B + 2)) a)) by wk_in;
      assert (Hya : FOPrH n G1 (FOcpairF (FOnumeral y) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hpa : FOPrH n G1 (FOPATF (B + 8) env (cpat_f (rho_hide y rho) P) (FOVar (B + 6))))
        by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    destruct (Nat.eqb_spec y x) as [->|Hne].
    + exact (FOPrH_N1_quant_eq n _ (FOnumeral x) a 4 (FOVar (B + 2)) (FOnumeral x)
               (FOVar (B + 6)) (or_intror eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Hka Hya (FOPrH_refl _ _ _)).
    + assert (Hrho' : forall z i, rho_hide y rho z = Some i -> i < length env).
      { intros z i Hz. unfold rho_hide in Hz. destruct (Nat.eqb z y); [discriminate|].
        exact (Hrho z i Hz). }
      pose proof (IHP _ (rho_hide y rho) env (B + 8) (FOVar (B + 6)) HS1 Hrho' Hpa ltac:(lia)
                    ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms)) as R.
      exact (FOPrH_N1_quant_ne n _ (FOnumeral x) a (bnum (lit_free_f (rho_hide y rho) x P)) 4
               (FOVar (B + 2)) (FOnumeral y) (FOVar (B + 6)) (or_intror eq_refl)
               ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) R Hka Hya
               (FOPrH_num_neq n _ y x Hne)).
Qed.
