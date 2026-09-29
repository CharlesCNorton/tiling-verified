From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28.
Open Scope fo_scope.

(** ** Capture-test rows (tag [4]) for the substitution of a numeral code.

    A numeral code [m] contains no variable, so it is free for every
    variable in every formula: the row value is [1]. *)

Lemma FOPrH_cap_f : forall n x m A G rho env B a,
  SlotCtx n env G -> (exists w, FOPrH n G (FONUMR w m)) ->
  (forall z i, rho z = Some i -> i < length env) ->
  FOPrH n G (FOPATF B env (cpat_f rho A) a) ->
  1000 <= B -> FOctx_avoid G B (B + cpat_span (cpat_f rho A)) ->
  FOtms_avoid (a :: m :: env) B (B + cpat_span (cpat_f rho A)) ->
  FOtms_avoid (a :: m :: env) 2 1000 ->
  FOPrH n G (FOTBLEX (FOnumeral 4) (FOnumeral x) m a (FOnumeral 1)).
Proof.
  intros n x m A.
  induction A as [u w| |P IHP Q IHQ|y P IHP|y P IHP];
    intros G rho env B a HS [wm Hm] Hrho Ha HB HGs Havs Hlo; pose proof HS as [HG Hslot].
  - cbn [cpat_f pEqP] in *. span_h HGs. span_h Havs.
    apply (FOPrH_patf_lit_elim n G B env 0 _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 0) (FOVar (B + 2)) a)) by wk_in;
      assert (HG1 : FOctx_avoid G1 2 1000) by ctx_list
    end.
    exact (FOPrH_N4_eq n _ (FOnumeral x) m a (FOVar (B + 2))
             ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) Hka).
  - cbn [cpat_f] in *. span_h HGs. span_h Havs.
    apply (FOPrH_patf_leaf_elim n G B env 1 0 a _ Ha ltac:(lia) HGs);
      [intros w1 H1 H2; free_fm | avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hca : FOPrH n G1 (FOcpairF (FOnumeral 1) (FOnumeral 0) a)) by apply FOPrH_last;
      assert (HG1 : FOctx_avoid G1 2 1000) by ctx_list
    end.
    exact (FOPrH_N4_false n _ (FOnumeral x) m a ltac:(intros w1 ? ?; apply HG1; lia)
             ltac:(avoid_tms) Hca).
  - cbn [cpat_f pImpP] in *.
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
      assert (Hm1 : FOPrH n G1 (FONUMR wm m)) by wk Hm;
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    pose proof (IHP _ rho env (B + 8) (FOVar (B + 4)) HS1 (ex_intro _ wm Hm1) Hrho Hua
                  ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms)) as Ru.
    pose proof (IHQ _ rho env (B + 8 + 4 * cpat_pairs (cpat_f rho P)) (FOVar (B + 6)) HS1
                  (ex_intro _ wm Hm1) Hrho Hwa ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms)
                  ltac:(avoid_tms)) as Rw.
    exact (FOPrH_N4_impl n _ (FOnumeral x) m a (FOnumeral 1) (FOVar (B + 2)) (FOVar (B + 4))
             (FOVar (B + 6)) ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms)
             Ru Rw Hka Hpa).
  - cbn [cpat_f pAllP] in *. span_h HGs. span_h Havs.
    apply (FOPrH_patf_quant_elim n G B env 3 y _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 3) (FOVar (B + 2)) a)) by wk_in;
      assert (Hya : FOPrH n G1 (FOcpairF (FOnumeral y) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hpa : FOPrH n G1 (FOPATF (B + 8) env (cpat_f (rho_hide y rho) P) (FOVar (B + 6))))
        by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (Hm1 : FOPrH n G1 (FONUMR wm m)) by wk Hm;
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    destruct (Nat.eqb_spec y x) as [->|Hne].
    + exact (FOPrH_N4_quant_eq n _ (FOnumeral x) m a 3 (FOVar (B + 2)) (FOnumeral x)
               (FOVar (B + 6)) (or_introl eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Hka Hya (FOPrH_refl _ _ _)).
    + assert (Hrho' : forall z i, rho_hide y rho z = Some i -> i < length env).
      { intros z i Hz. unfold rho_hide in Hz. destruct (Nat.eqb z y); [discriminate|].
        exact (Hrho z i Hz). }
      assert (Vm : FOtms_avoid [m] 2 1000) by avoid_tms.
      pose proof (FOPrH_free_f n x P _ (rho_hide y rho) env (B + 8) (FOVar (B + 6)) HS1 Hrho'
                    Hpa ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms)) as Rf.
      destruct (lit_free_f (rho_hide y rho) x P) eqn:Ef.
      * pose proof (FOPrH_numr_row0 n _ wm m (FOnumeral y) Hm1 ltac:(avoid_tms)) as R0.
        pose proof (IHP _ (rho_hide y rho) env (B + 8) (FOVar (B + 6)) HS1 (ex_intro _ wm Hm1)
                      Hrho' Hpa ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms))
          as R4.
        exact (FOPrH_N4_quant_fr n _ (FOnumeral x) m a (FOnumeral 1) 3 (FOVar (B + 2))
                 (FOnumeral y) (FOVar (B + 6)) (or_introl eq_refl)
                 ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) Rf R0 R4 Hka Hya
                 (FOPrH_num_neq n _ y x Hne)).
      * exact (FOPrH_N4_quant_nf n _ (FOnumeral x) m a 3 (FOVar (B + 2)) (FOnumeral y)
                 (FOVar (B + 6)) (or_introl eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
                 ltac:(avoid_tms) Rf Hka Hya (FOPrH_num_neq n _ y x Hne)).
  - cbn [cpat_f pExP] in *. span_h HGs. span_h Havs.
    apply (FOPrH_patf_quant_elim n G B env 4 y _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 4) (FOVar (B + 2)) a)) by wk_in;
      assert (Hya : FOPrH n G1 (FOcpairF (FOnumeral y) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hpa : FOPrH n G1 (FOPATF (B + 8) env (cpat_f (rho_hide y rho) P) (FOVar (B + 6))))
        by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (Hm1 : FOPrH n G1 (FONUMR wm m)) by wk Hm;
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    destruct (Nat.eqb_spec y x) as [->|Hne].
    + exact (FOPrH_N4_quant_eq n _ (FOnumeral x) m a 4 (FOVar (B + 2)) (FOnumeral x)
               (FOVar (B + 6)) (or_intror eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Hka Hya (FOPrH_refl _ _ _)).
    + assert (Hrho' : forall z i, rho_hide y rho z = Some i -> i < length env).
      { intros z i Hz. unfold rho_hide in Hz. destruct (Nat.eqb z y); [discriminate|].
        exact (Hrho z i Hz). }
      assert (Vm : FOtms_avoid [m] 2 1000) by avoid_tms.
      pose proof (FOPrH_free_f n x P _ (rho_hide y rho) env (B + 8) (FOVar (B + 6)) HS1 Hrho'
                    Hpa ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms)) as Rf.
      destruct (lit_free_f (rho_hide y rho) x P) eqn:Ef.
      * pose proof (FOPrH_numr_row0 n _ wm m (FOnumeral y) Hm1 ltac:(avoid_tms)) as R0.
        pose proof (IHP _ (rho_hide y rho) env (B + 8) (FOVar (B + 6)) HS1 (ex_intro _ wm Hm1)
                      Hrho' Hpa ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms))
          as R4.
        exact (FOPrH_N4_quant_fr n _ (FOnumeral x) m a (FOnumeral 1) 4 (FOVar (B + 2))
                 (FOnumeral y) (FOVar (B + 6)) (or_intror eq_refl)
                 ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) Rf R0 R4 Hka Hya
                 (FOPrH_num_neq n _ y x Hne)).
      * exact (FOPrH_N4_quant_nf n _ (FOnumeral x) m a 4 (FOVar (B + 2)) (FOnumeral y)
                 (FOVar (B + 6)) (or_intror eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
                 ltac:(avoid_tms) Rf Hka Hya (FOPrH_num_neq n _ y x Hne)).
Qed.
