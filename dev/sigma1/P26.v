From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25.
Open Scope fo_scope.

(** ** Slots of the code patterns. *)

Lemma cpat_tm_slots : forall t rho s, cpat_occurs s (cpat_tm rho t) = true ->
  exists z, rho z = Some s.
Proof.
  induction t as [y| |u IH|u IHu w IHw|u IHu w IHw]; intros rho s H;
    cbn [cpat_tm cpat_occurs tVarP tZeroP tSuccP tPlusP tMultP orb] in H.
  - destruct (rho y) as [i|] eqn:Ey; cbn [cpat_occurs orb] in H; [|discriminate].
    apply Nat.eqb_eq in H. subst i. exists y. exact Ey.
  - discriminate.
  - exact (IH rho s H).
  - apply Bool.orb_true_iff in H. destruct H as [H|H]; [exact (IHu rho s H) | exact (IHw rho s H)].
  - apply Bool.orb_true_iff in H. destruct H as [H|H]; [exact (IHu rho s H) | exact (IHw rho s H)].
Qed.

Lemma cpat_f_slots : forall A rho s, cpat_occurs s (cpat_f rho A) = true ->
  exists z, rho z = Some s.
Proof.
  induction A as [u w| |P IHP Q IHQ|y P IHP|y P IHP]; intros rho s H;
    cbn [cpat_f cpat_occurs pEqP pFlsP pImpP pAllP pExP orb] in H.
  - apply Bool.orb_true_iff in H. destruct H as [H|H];
      [exact (cpat_tm_slots u rho s H) | exact (cpat_tm_slots w rho s H)].
  - discriminate.
  - apply Bool.orb_true_iff in H. destruct H as [H|H]; [exact (IHP rho s H) | exact (IHQ rho s H)].
  - destruct (IHP _ s H) as [z Hz]. unfold rho_hide in Hz.
    destruct (Nat.eqb z y); [discriminate | exists z; exact Hz].
  - destruct (IHP _ s H) as [z Hz]. unfold rho_hide in Hz.
    destruct (Nat.eqb z y); [discriminate | exists z; exact Hz].
Qed.

Lemma FOPATF_env_eq : forall p B env env' d,
  (forall s, cpat_occurs s p = true -> nth s env' FOZero = nth s env FOZero) ->
  FOPATF B env' p d = FOPATF B env p d.
Proof.
  induction p as [k|i|q IH|a IHa b IHb]; intros B env env' d H;
    cbn [FOPATF cpat_occurs] in *.
  - reflexivity.
  - rewrite H; [reflexivity|]. apply Nat.eqb_refl.
  - rewrite (IH (B + 2) env env' (FOVar B)); [reflexivity|]. exact H.
  - rewrite (IHa (B + 4) env env' (FOVar B)), (IHb (B + 4 + 4 * cpat_pairs a) env env' (FOVar (B + 2)));
      [reflexivity| |]; intros s Hs; apply H; rewrite Hs;
      first [reflexivity | apply Bool.orb_true_r].
Qed.

Ltac span_g := cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP
                      pAllP pExP].
Ltac span_h H := cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP
                        pAllP pExP] in H.
Ltac span_std H1 H2 H3 H4 H5 := span_h H1; span_h H2; span_h H3; span_h H4; span_h H5.

(** ** Substitution rows for the code of a formula. *)

Lemma FOPrH_rows_f : forall n ox X Xb s env env' j A G rho B B' a c,
  RowEnv ox X Xb s env env' j -> RowCtx n ox X Xb env G ->
  (forall z i, rho z = Some i -> i < length env) ->
  match ox with Some x => rho x = None | None => True end ->
  FOPrH n G (FOPATF B env (cpat_f rho A) a) ->
  FOPrH n G (FOPATF B' env' (cpat_f (rho_sub ox j rho) A) c) ->
  FOPrH n G (FOle (FOSucc a) Xb) ->
  1000 <= B -> 1000 <= B' ->
  B + cpat_span (cpat_f rho A) <= B' \/ B' + cpat_span (cpat_f (rho_sub ox j rho) A) <= B ->
  FOctx_avoid G B (B + cpat_span (cpat_f rho A)) ->
  FOctx_avoid G B' (B' + cpat_span (cpat_f (rho_sub ox j rho) A)) ->
  FOtms_avoid (a :: c :: X :: Xb :: s :: env ++ env') B (B + cpat_span (cpat_f rho A)) ->
  FOtms_avoid (a :: c :: X :: Xb :: s :: env ++ env') B'
    (B' + cpat_span (cpat_f (rho_sub ox j rho) A)) ->
  FOtms_avoid [a; c] 2 1000 ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X s a c).
Proof.
  intros n ox X Xb s env env' j A.
  induction A as [u w| |P IHP Q IHQ|y P IHP|y P IHP];
    intros G rho B B' a c HE HC Hrho Hrx Ha Hc Hb HB HB' Hdis HGs HGt Havs Havt Hac;
    pose proof HE as [Henv [Hj [HX Hlo]]]; pose proof HC as [HG [Hslot Hlit]].
  - (* equation *)
    cbn [cpat_f pEqP] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    pose proof (cpat_span_le (cpat_tm rho u)) as Hsu.
    pose proof (cpat_span_le (cpat_tm (rho_sub ox j rho) u)) as Hsu'.
    span_std Hdis HGs HGt Havs Havt.
    apply (FOPrH_patf_bin_elim n G B env 0 _ _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    apply (FOPrH_patf_bin_elim n _ B' env' 0 _ _ c _ (FOPrH_weak_app _ _ _ _ Hc) ltac:(lia));
      [span_g; ctx_list | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G2 _ =>
      assert (Hka : FOPrH n G2 (FOcpairF (FOnumeral 0) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G2 (FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hua : FOPrH n G2 (FOPATF (B + 8) env (cpat_tm rho u) (FOVar (B + 4)))) by wk_in;
      assert (Hwa : FOPrH n G2 (FOPATF (B + 8 + 4 * cpat_pairs (cpat_tm rho u)) env
                                  (cpat_tm rho w) (FOVar (B + 6)))) by wk_in;
      assert (Hkc : FOPrH n G2 (FOcpairF (FOnumeral 0) (FOVar (B' + 2)) c)) by wk_in;
      assert (Hpc : FOPrH n G2 (FOcpairF (FOVar (B' + 4)) (FOVar (B' + 6)) (FOVar (B' + 2))))
        by wk_in;
      assert (Huc : FOPrH n G2 (FOPATF (B' + 8) env' (cpat_tm (rho_sub ox j rho) u)
                                  (FOVar (B' + 4)))) by wk_in;
      assert (Hwc : FOPrH n G2 (FOPATF (B' + 8 + 4 * cpat_pairs (cpat_tm (rho_sub ox j rho) u))
                                  env' (cpat_tm (rho_sub ox j rho) w) (FOVar (B' + 6)))) by wk_in;
      assert (HC2 : RowCtx n ox X Xb env G2)
        by (apply RowCtx_ext; [apply RowCtx_ext; [exact HC | ctx_list] | ctx_list]);
      assert (Hb2 : FOPrH n G2 (FOle (FOSucc a) Xb)) by wk Hb;
      assert (HG2 : FOctx_avoid G2 2 1000) by (destruct HC2; tauto)
    end.
    destruct (FOPrH_cpair_le_cf n _ (FOnumeral 0) (FOVar (B + 2)) a ltac:(avoid_tms) Hka)
      as [_ Hpa'].
    destruct (FOPrH_cpair_le_cf n _ (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))
                ltac:(avoid_tms) Hpa) as [Hup Hwp].
    pose proof (FOPrH_le_below n _ _ _ _ Hpa' Hb2 ltac:(avoid_tms)) as Hpb.
    pose proof (FOPrH_rows_tm n ox X Xb s env env' j u _ rho (B + 8) (B' + 8) (FOVar (B + 4))
                  (FOVar (B' + 4)) HE HC2 Hrho Hrx
                  Hua Huc (FOPrH_le_below n _ _ _ _ Hup Hpb ltac:(avoid_tms))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Ru.
    pose proof (FOPrH_rows_tm n ox X Xb s env env' j w _ rho
                  (B + 8 + 4 * cpat_pairs (cpat_tm rho u))
                  (B' + 8 + 4 * cpat_pairs (cpat_tm (rho_sub ox j rho) u))
                  (FOVar (B + 6)) (FOVar (B' + 6)) HE HC2 Hrho Hrx
                  Hwa Hwc (FOPrH_le_below n _ _ _ _ Hwp Hpb ltac:(avoid_tms))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Rw.
    exact (FOPrH_N3_eq n _ X s a c (FOVar (B + 2)) (FOVar (B + 4)) (FOVar (B + 6))
             (FOVar (B' + 4)) (FOVar (B' + 6)) (FOVar (B' + 2))
             ltac:(intros w1 ? ?; apply HG2; lia) ltac:(avoid_tms) Ru Rw Hka Hpa Hpc Hkc).
  - (* falsum *)
    cbn [cpat_f] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    span_std Hdis HGs HGt Havs Havt.
    apply (FOPrH_patf_leaf_elim n G B env 1 0 a _ Ha ltac:(lia) HGs);
      [intros w1 H1 H2; free_fm | avoid_tms |].
    apply (FOPrH_patf_leaf_elim n _ B' env' 1 0 c _ (FOPrH_weak_app _ _ _ _ Hc) ltac:(lia));
      [ctx_list | intros w1 H1 H2; free_fm | avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G2 _ =>
      assert (Hcc : FOPrH n G2 (FOcpairF (FOnumeral 1) (FOnumeral 0) c)) by apply FOPrH_last;
      assert (Hca : FOPrH n G2 (FOcpairF (FOnumeral 1) (FOnumeral 0) a)) by wk_in;
      assert (HG2 : FOctx_avoid G2 2 1000) by ctx_list
    end.
    pose proof (FOPrH_cpair_fun n _ _ _ a c ltac:(avoid_tms) Hca Hcc) as Eac.
    pose proof (FOPrH_N3_false n _ X s a ltac:(intros w1 ? ?; apply HG2; lia)
                  ltac:(avoid_tms) Hca) as R.
    exact (FOPrH_tblex_cong n _ _ _ _ _ _ _ _ R (FOPrH_refl _ _ _) Eac ltac:(avoid_tms)).
  - (* implication *)
    cbn [cpat_f pImpP] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    pose proof (cpat_span_le (cpat_f rho P)) as Hsu.
    pose proof (cpat_span_le (cpat_f (rho_sub ox j rho) P)) as Hsu'.
    span_std Hdis HGs HGt Havs Havt.
    apply (FOPrH_patf_bin_elim n G B env 2 _ _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    apply (FOPrH_patf_bin_elim n _ B' env' 2 _ _ c _ (FOPrH_weak_app _ _ _ _ Hc) ltac:(lia));
      [span_g; ctx_list | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G2 _ =>
      assert (Hka : FOPrH n G2 (FOcpairF (FOnumeral 2) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G2 (FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hua : FOPrH n G2 (FOPATF (B + 8) env (cpat_f rho P) (FOVar (B + 4)))) by wk_in;
      assert (Hwa : FOPrH n G2 (FOPATF (B + 8 + 4 * cpat_pairs (cpat_f rho P)) env
                                  (cpat_f rho Q) (FOVar (B + 6)))) by wk_in;
      assert (Hkc : FOPrH n G2 (FOcpairF (FOnumeral 2) (FOVar (B' + 2)) c)) by wk_in;
      assert (Hpc : FOPrH n G2 (FOcpairF (FOVar (B' + 4)) (FOVar (B' + 6)) (FOVar (B' + 2))))
        by wk_in;
      assert (Huc : FOPrH n G2 (FOPATF (B' + 8) env' (cpat_f (rho_sub ox j rho) P)
                                  (FOVar (B' + 4)))) by wk_in;
      assert (Hwc : FOPrH n G2 (FOPATF (B' + 8 + 4 * cpat_pairs (cpat_f (rho_sub ox j rho) P))
                                  env' (cpat_f (rho_sub ox j rho) Q) (FOVar (B' + 6)))) by wk_in;
      assert (HC2 : RowCtx n ox X Xb env G2)
        by (apply RowCtx_ext; [apply RowCtx_ext; [exact HC | ctx_list] | ctx_list]);
      assert (Hb2 : FOPrH n G2 (FOle (FOSucc a) Xb)) by wk Hb;
      assert (HG2 : FOctx_avoid G2 2 1000) by (destruct HC2; tauto)
    end.
    destruct (FOPrH_cpair_le_cf n _ (FOnumeral 2) (FOVar (B + 2)) a ltac:(avoid_tms) Hka)
      as [_ Hpa'].
    destruct (FOPrH_cpair_le_cf n _ (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))
                ltac:(avoid_tms) Hpa) as [Hup Hwp].
    pose proof (FOPrH_le_below n _ _ _ _ Hpa' Hb2 ltac:(avoid_tms)) as Hpb.
    pose proof (IHP _ rho (B + 8) (B' + 8) (FOVar (B + 4)) (FOVar (B' + 4)) HE HC2 Hrho Hrx
                  Hua Huc (FOPrH_le_below n _ _ _ _ Hup Hpb ltac:(avoid_tms))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Ru.
    pose proof (IHQ _ rho (B + 8 + 4 * cpat_pairs (cpat_f rho P))
                  (B' + 8 + 4 * cpat_pairs (cpat_f (rho_sub ox j rho) P))
                  (FOVar (B + 6)) (FOVar (B' + 6)) HE HC2 Hrho Hrx
                  Hwa Hwc (FOPrH_le_below n _ _ _ _ Hwp Hpb ltac:(avoid_tms))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Rw.
    exact (FOPrH_N3_impl n _ X s a c (FOVar (B + 2)) (FOVar (B + 4)) (FOVar (B + 6))
             (FOVar (B' + 4)) (FOVar (B' + 6)) (FOVar (B' + 2))
             ltac:(intros w1 ? ?; apply HG2; lia) ltac:(avoid_tms) Ru Rw Hka Hpa Hpc Hkc).
  - (* universal *)
    cbn [cpat_f pAllP] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    pose proof (cpat_span_le (cpat_f (rho_hide y rho) P)) as Hsu.
    destruct (ox_eq ox y) eqn:Eo.
    + destruct ox as [x|]; cbn [ox_eq] in Eo; [|discriminate].
      apply Nat.eqb_eq in Eo. subst y. subst X.
      assert (Ep : cpat_f (rho_hide x (rho_sub (Some x) j rho)) P = cpat_f (rho_hide x rho) P)
        by (apply cpat_f_ext; apply rho_hide_sub_self).
      rewrite Ep in Hc, HGt, Havt, Hdis.
      assert (Ee : FOPATF B' env' (pAllP (CLit x) (cpat_f (rho_hide x rho) P)) c
                 = FOPATF B' env (pAllP (CLit x) (cpat_f (rho_hide x rho) P)) c).
      { apply FOPATF_env_eq. intros s0 Hs0. cbn [pAllP cpat_occurs orb] in Hs0.
        destruct (cpat_f_slots P _ s0 Hs0) as [z Hz]. unfold rho_hide in Hz.
        destruct (Nat.eqb z x); [discriminate|]. apply Henv. exact (Hrho z s0 Hz). }
      rewrite Ee in Hc.
      span_std Hdis HGs HGt Havs Havt.
      pose proof (FOPrH_patf_unique _ n G B B' env a c Ha Hc ltac:(lia) ltac:(lia)
                    ltac:(span_g; lia) ltac:(span_g; exact HGs) ltac:(span_g; exact HGt)
                    ltac:(span_g; avoid_tms) ltac:(span_g; avoid_tms) ltac:(avoid_tms)) as Eac.
      apply (FOPrH_patf_quant_elim n G B env 3 x _ a _ Ha ltac:(lia));
        [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
      lazymatch goal with |- FOPrH _ ?G1 _ =>
        assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 3) (FOVar (B + 2)) a)) by wk_in;
        assert (Hya : FOPrH n G1 (FOcpairF (FOnumeral x) (FOVar (B + 6)) (FOVar (B + 2))))
          by wk_in;
        assert (Eac1 : FOPrH n G1 (FOEq a c)) by wk Eac;
        assert (HG1 : FOctx_avoid G1 2 1000) by ctx_list
      end.
      pose proof (FOPrH_N3_quant_eq n _ (FOnumeral x) s a 3 (FOVar (B + 2)) (FOnumeral x)
                    (FOVar (B + 6)) (or_introl eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
                    ltac:(avoid_tms) Hka Hya (FOPrH_refl _ _ _)) as R.
      exact (FOPrH_tblex_cong n _ _ _ _ _ _ _ _ R (FOPrH_refl _ _ _) Eac1 ltac:(avoid_tms)).
    + assert (Ep : cpat_f (rho_hide y (rho_sub ox j rho)) P
                   = cpat_f (rho_sub ox j (rho_hide y rho)) P).
      { apply cpat_f_ext. intros z. symmetry. apply rho_sub_hide. exact Eo. }
      rewrite Ep in Hc, HGt, Havt, Hdis.
      pose proof (cpat_span_le (cpat_f (rho_sub ox j (rho_hide y rho)) P)) as Hsu'.
      span_std Hdis HGs HGt Havs Havt.
      apply (FOPrH_patf_quant_elim n G B env 3 y _ a _ Ha ltac:(lia));
        [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
      apply (FOPrH_patf_quant_elim n _ B' env' 3 y _ c _ (FOPrH_weak_app _ _ _ _ Hc)
               ltac:(lia));
        [span_g; ctx_list | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
      lazymatch goal with |- FOPrH _ ?G2 _ =>
        assert (Hka : FOPrH n G2 (FOcpairF (FOnumeral 3) (FOVar (B + 2)) a)) by wk_in;
        assert (Hya : FOPrH n G2 (FOcpairF (FOnumeral y) (FOVar (B + 6)) (FOVar (B + 2))))
          by wk_in;
        assert (Hpa : FOPrH n G2 (FOPATF (B + 8) env (cpat_f (rho_hide y rho) P)
                                    (FOVar (B + 6)))) by wk_in;
        assert (Hkc : FOPrH n G2 (FOcpairF (FOnumeral 3) (FOVar (B' + 2)) c)) by wk_in;
        assert (Hyc : FOPrH n G2 (FOcpairF (FOnumeral y) (FOVar (B' + 6)) (FOVar (B' + 2))))
          by wk_in;
        assert (Hpc : FOPrH n G2 (FOPATF (B' + 8) env' (cpat_f (rho_sub ox j (rho_hide y rho)) P)
                                    (FOVar (B' + 6)))) by wk_in;
        assert (HC2 : RowCtx n ox X Xb env G2)
          by (apply RowCtx_ext; [apply RowCtx_ext; [exact HC | ctx_list] | ctx_list]);
        assert (Hb2 : FOPrH n G2 (FOle (FOSucc a) Xb)) by wk Hb;
        assert (HG2 : FOctx_avoid G2 2 1000) by (destruct HC2; tauto)
      end.
      destruct (FOPrH_cpair_le_cf n _ (FOnumeral 3) (FOVar (B + 2)) a ltac:(avoid_tms) Hka)
        as [_ Hpa'].
      destruct (FOPrH_cpair_le_cf n _ (FOnumeral y) (FOVar (B + 6)) (FOVar (B + 2))
                  ltac:(avoid_tms) Hya) as [Hyp Hbp].
      pose proof (FOPrH_le_below n _ _ _ _ Hpa' Hb2 ltac:(avoid_tms)) as Hpb.
      assert (Hrho' : forall z i, rho_hide y rho z = Some i -> i < length env).
      { intros z i Hz. unfold rho_hide in Hz. destruct (Nat.eqb z y); [discriminate|].
        exact (Hrho z i Hz). }
      assert (Hrx' : match ox with Some x => rho_hide y rho x = None | None => True end).
      { destruct ox as [x|]; [|exact I]. unfold rho_hide. destruct (Nat.eqb x y);
          [reflexivity | exact Hrx]. }
      pose proof (IHP _ (rho_hide y rho) (B + 8) (B' + 8) (FOVar (B + 6)) (FOVar (B' + 6)) HE
                    HC2 Hrho' Hrx' Hpa Hpc (FOPrH_le_below n _ _ _ _ Hbp Hpb ltac:(avoid_tms))
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                    ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as R.
      destruct HC2 as [_ [_ Hlit2]].
      pose proof (Hlit2 _ y (fun Y HY => HY) (FOPrH_le_below n _ _ _ _ Hyp Hpb ltac:(avoid_tms))
                    Eo) as Hne.
      exact (FOPrH_N3_quant_ne n _ X s a c 3 (FOVar (B + 2)) (FOnumeral y) (FOVar (B + 6))
               (FOVar (B' + 6)) (FOVar (B' + 2)) (or_introl eq_refl)
               ltac:(intros w1 ? ?; apply HG2; lia) ltac:(avoid_tms) R Hka Hya Hne Hyc Hkc).
  - (* existential *)
    cbn [cpat_f pExP] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    pose proof (cpat_span_le (cpat_f (rho_hide y rho) P)) as Hsu.
    destruct (ox_eq ox y) eqn:Eo.
    + destruct ox as [x|]; cbn [ox_eq] in Eo; [|discriminate].
      apply Nat.eqb_eq in Eo. subst y. subst X.
      assert (Ep : cpat_f (rho_hide x (rho_sub (Some x) j rho)) P = cpat_f (rho_hide x rho) P)
        by (apply cpat_f_ext; apply rho_hide_sub_self).
      rewrite Ep in Hc, HGt, Havt, Hdis.
      assert (Ee : FOPATF B' env' (pExP (CLit x) (cpat_f (rho_hide x rho) P)) c
                 = FOPATF B' env (pExP (CLit x) (cpat_f (rho_hide x rho) P)) c).
      { apply FOPATF_env_eq. intros s0 Hs0. cbn [pExP cpat_occurs orb] in Hs0.
        destruct (cpat_f_slots P _ s0 Hs0) as [z Hz]. unfold rho_hide in Hz.
        destruct (Nat.eqb z x); [discriminate|]. apply Henv. exact (Hrho z s0 Hz). }
      rewrite Ee in Hc.
      span_std Hdis HGs HGt Havs Havt.
      pose proof (FOPrH_patf_unique _ n G B B' env a c Ha Hc ltac:(lia) ltac:(lia)
                    ltac:(span_g; lia) ltac:(span_g; exact HGs) ltac:(span_g; exact HGt)
                    ltac:(span_g; avoid_tms) ltac:(span_g; avoid_tms) ltac:(avoid_tms)) as Eac.
      apply (FOPrH_patf_quant_elim n G B env 4 x _ a _ Ha ltac:(lia));
        [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
      lazymatch goal with |- FOPrH _ ?G1 _ =>
        assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 4) (FOVar (B + 2)) a)) by wk_in;
        assert (Hya : FOPrH n G1 (FOcpairF (FOnumeral x) (FOVar (B + 6)) (FOVar (B + 2))))
          by wk_in;
        assert (Eac1 : FOPrH n G1 (FOEq a c)) by wk Eac;
        assert (HG1 : FOctx_avoid G1 2 1000) by ctx_list
      end.
      pose proof (FOPrH_N3_quant_eq n _ (FOnumeral x) s a 4 (FOVar (B + 2)) (FOnumeral x)
                    (FOVar (B + 6)) (or_intror eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
                    ltac:(avoid_tms) Hka Hya (FOPrH_refl _ _ _)) as R.
      exact (FOPrH_tblex_cong n _ _ _ _ _ _ _ _ R (FOPrH_refl _ _ _) Eac1 ltac:(avoid_tms)).
    + assert (Ep : cpat_f (rho_hide y (rho_sub ox j rho)) P
                   = cpat_f (rho_sub ox j (rho_hide y rho)) P).
      { apply cpat_f_ext. intros z. symmetry. apply rho_sub_hide. exact Eo. }
      rewrite Ep in Hc, HGt, Havt, Hdis.
      pose proof (cpat_span_le (cpat_f (rho_sub ox j (rho_hide y rho)) P)) as Hsu'.
      span_std Hdis HGs HGt Havs Havt.
      apply (FOPrH_patf_quant_elim n G B env 4 y _ a _ Ha ltac:(lia));
        [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
      apply (FOPrH_patf_quant_elim n _ B' env' 4 y _ c _ (FOPrH_weak_app _ _ _ _ Hc)
               ltac:(lia));
        [span_g; ctx_list | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
      lazymatch goal with |- FOPrH _ ?G2 _ =>
        assert (Hka : FOPrH n G2 (FOcpairF (FOnumeral 4) (FOVar (B + 2)) a)) by wk_in;
        assert (Hya : FOPrH n G2 (FOcpairF (FOnumeral y) (FOVar (B + 6)) (FOVar (B + 2))))
          by wk_in;
        assert (Hpa : FOPrH n G2 (FOPATF (B + 8) env (cpat_f (rho_hide y rho) P)
                                    (FOVar (B + 6)))) by wk_in;
        assert (Hkc : FOPrH n G2 (FOcpairF (FOnumeral 4) (FOVar (B' + 2)) c)) by wk_in;
        assert (Hyc : FOPrH n G2 (FOcpairF (FOnumeral y) (FOVar (B' + 6)) (FOVar (B' + 2))))
          by wk_in;
        assert (Hpc : FOPrH n G2 (FOPATF (B' + 8) env' (cpat_f (rho_sub ox j (rho_hide y rho)) P)
                                    (FOVar (B' + 6)))) by wk_in;
        assert (HC2 : RowCtx n ox X Xb env G2)
          by (apply RowCtx_ext; [apply RowCtx_ext; [exact HC | ctx_list] | ctx_list]);
        assert (Hb2 : FOPrH n G2 (FOle (FOSucc a) Xb)) by wk Hb;
        assert (HG2 : FOctx_avoid G2 2 1000) by (destruct HC2; tauto)
      end.
      destruct (FOPrH_cpair_le_cf n _ (FOnumeral 4) (FOVar (B + 2)) a ltac:(avoid_tms) Hka)
        as [_ Hpa'].
      destruct (FOPrH_cpair_le_cf n _ (FOnumeral y) (FOVar (B + 6)) (FOVar (B + 2))
                  ltac:(avoid_tms) Hya) as [Hyp Hbp].
      pose proof (FOPrH_le_below n _ _ _ _ Hpa' Hb2 ltac:(avoid_tms)) as Hpb.
      assert (Hrho' : forall z i, rho_hide y rho z = Some i -> i < length env).
      { intros z i Hz. unfold rho_hide in Hz. destruct (Nat.eqb z y); [discriminate|].
        exact (Hrho z i Hz). }
      assert (Hrx' : match ox with Some x => rho_hide y rho x = None | None => True end).
      { destruct ox as [x|]; [|exact I]. unfold rho_hide. destruct (Nat.eqb x y);
          [reflexivity | exact Hrx]. }
      pose proof (IHP _ (rho_hide y rho) (B + 8) (B' + 8) (FOVar (B + 6)) (FOVar (B' + 6)) HE
                    HC2 Hrho' Hrx' Hpa Hpc (FOPrH_le_below n _ _ _ _ Hbp Hpb ltac:(avoid_tms))
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                    ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as R.
      destruct HC2 as [_ [_ Hlit2]].
      pose proof (Hlit2 _ y (fun Y HY => HY) (FOPrH_le_below n _ _ _ _ Hyp Hpb ltac:(avoid_tms))
                    Eo) as Hne.
      exact (FOPrH_N3_quant_ne n _ X s a c 4 (FOVar (B + 2)) (FOnumeral y) (FOVar (B + 6))
               (FOVar (B' + 6)) (FOVar (B' + 2)) (or_intror eq_refl)
               ltac:(intros w1 ? ?; apply HG2; lia) ltac:(avoid_tms) R Hka Hya Hne Hyc Hkc).
Qed.
