From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24.
Open Scope fo_scope.

(** ** Substitution rows for the code of a term.

    [ox = Some x]: the row substitutes the code [s] (a new slot [j] of
    the target) for the variable [x]; [ox = None]: the row substitutes
    at a variable [X] above every variable of the code, and source and
    target coincide.  [Xb] bounds the source code from above; every
    literal variable [y] below [Xb] other than [x] differs from [X]. *)

Definition rho_sub (ox : option nat) (j : nat) (rho : nat -> option nat) : nat -> option nat :=
  match ox with
  | Some x => fun z => if Nat.eqb z x then Some j else rho z
  | None => rho
  end.

Definition ox_eq (ox : option nat) (y : nat) : bool :=
  match ox with Some x => Nat.eqb y x | None => false end.

Lemma rho_sub_hide : forall ox j rho y, ox_eq ox y = false ->
  forall z, rho_sub ox j (rho_hide y rho) z = rho_hide y (rho_sub ox j rho) z.
Proof.
  intros [x|] j rho y H z; cbn [rho_sub ox_eq] in *; unfold rho_hide; [|reflexivity].
  destruct (Nat.eqb z y) eqn:Ezy; destruct (Nat.eqb z x) eqn:Ezx; try reflexivity.
  apply Nat.eqb_eq in Ezy, Ezx. subst. rewrite Nat.eqb_refl in H. discriminate.
Qed.

Lemma rho_hide_sub_self : forall x j rho z,
  rho_hide x (rho_sub (Some x) j rho) z = rho_hide x rho z.
Proof.
  intros x j rho z. unfold rho_hide, rho_sub. destruct (Nat.eqb_spec z x); reflexivity.
Qed.

Definition RowEnv (ox : option nat) (X Xb s : FOTerm) (env env' : list FOTerm) (j : nat)
  : Prop :=
  (forall i, i < length env -> nth i env' FOZero = nth i env FOZero) /\
  (match ox with Some _ => nth j env' FOZero = s | None => True end) /\
  (match ox with Some x => X = FOnumeral x | None => True end) /\
  FOtms_avoid (X :: Xb :: s :: env ++ env') 2 1000.

Definition RowCtx (n : nat) (ox : option nat) (X Xb : FOTerm) (env : list FOTerm)
    (G : list FOFormula) : Prop :=
  FOctx_avoid G 2 1000 /\
  (forall i, i < length env -> exists w, FOPrH n G (FONUMR w (nth i env FOZero))) /\
  (forall G' y, (forall Y, In Y G -> In Y G') ->
     FOPrH n G' (FOle (FOSucc (FOnumeral y)) Xb) -> ox_eq ox y = false ->
     FOPrH n G' (FONeg (FOEq (FOnumeral y) X))).

Lemma RowCtx_ext : forall n ox X Xb env G L,
  RowCtx n ox X Xb env G -> FOctx_avoid L 2 1000 -> RowCtx n ox X Xb env (G ++ L).
Proof.
  intros n ox X Xb env G L [H1 [H2 H3]] HL. split; [|split].
  - intros w ? ?. apply FOfree_ctx_app_inv; [apply H1 | apply HL]; lia.
  - intros i Hi. destruct (H2 i Hi) as [w Hw]. exists w. apply FOPrH_weak_app. exact Hw.
  - intros G' y Hinc. apply H3. intros Y HY. apply Hinc. apply in_or_app. left. exact HY.
Qed.

Lemma FOPrH_le_below : forall n G u a Xb,
  FOPrH n G (FOle u a) -> FOPrH n G (FOle (FOSucc a) Xb) ->
  FOtms_avoid [u; a; Xb] 2 1000 -> FOPrH n G (FOle (FOSucc u) Xb).
Proof.
  intros n G u a Xb H1 H2 Hav.
  apply (FOPrH_le_trans n G (FOSucc u) (FOSucc a) Xb); [| exact H2 | avoid_tms].
  apply FOPrH_le_succ_of_le; [exact H1 | avoid_tms].
Qed.

Ltac rows_ctx := ctx_list.

Lemma FOPrH_rows_tm : forall n ox X Xb s env env' j t G rho B B' a c,
  RowEnv ox X Xb s env env' j -> RowCtx n ox X Xb env G ->
  (forall z i, rho z = Some i -> i < length env) ->
  match ox with Some x => rho x = None | None => True end ->
  FOPrH n G (FOPATF B env (cpat_tm rho t) a) ->
  FOPrH n G (FOPATF B' env' (cpat_tm (rho_sub ox j rho) t) c) ->
  FOPrH n G (FOle (FOSucc a) Xb) ->
  1000 <= B -> 1000 <= B' ->
  B + cpat_span (cpat_tm rho t) <= B' \/ B' + cpat_span (cpat_tm (rho_sub ox j rho) t) <= B ->
  FOctx_avoid G B (B + cpat_span (cpat_tm rho t)) ->
  FOctx_avoid G B' (B' + cpat_span (cpat_tm (rho_sub ox j rho) t)) ->
  FOtms_avoid (a :: c :: X :: Xb :: s :: env ++ env') B (B + cpat_span (cpat_tm rho t)) ->
  FOtms_avoid (a :: c :: X :: Xb :: s :: env ++ env') B'
    (B' + cpat_span (cpat_tm (rho_sub ox j rho) t)) ->
  FOtms_avoid [a; c] 2 1000 ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s a c).
Proof.
  intros n ox X Xb s env env' j t.
  induction t as [y| |u IH|u IHu w IHw|u IHu w IHw];
    intros G rho B B' a c HE HC Hrho Hrx Ha Hc Hb HB HB' Hdis HGs HGt Havs Havt Hac;
    pose proof HE as [Henv [Hj [HX Hlo]]]; pose proof HC as [HG [Hslot Hlit]].
  - (* a variable *)
    cbn [cpat_tm] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    destruct (rho y) as [i|] eqn:Ey.
    + assert (Et : rho_sub ox j rho y = Some i).
      { destruct ox as [x|]; cbn [rho_sub]; [|exact Ey].
        destruct (Nat.eqb_spec y x) as [->|Hne]; [rewrite Hrx in Ey; discriminate | exact Ey]. }
      rewrite Et in Hc. cbn [FOPATF] in Ha, Hc.
      rewrite (Henv i (Hrho y i Ey)) in Hc.
      destruct (Hslot i (Hrho y i Ey)) as [wv Hw].
      assert (Vi : FOtms_avoid [nth i env FOZero] 2 1000).
      { apply FOtms_avoid_cons; [|apply FOtms_avoid_nil]. apply Hlo.
        right. right. right. apply in_or_app. left. apply nth_In. exact (Hrho y i Ey). }
      pose proof (FOPrH_numr_row2 n G wv (nth i env FOZero) X s Hw ltac:(avoid_tms)) as R.
      exact (FOPrH_tblex_cong n G _ _ _ _ _ _ _ R (FOPrH_eq_sym _ _ _ _ Ha)
               (FOPrH_eq_sym _ _ _ _ Hc) ltac:(avoid_tms)).
    + cbn [cpat_span cpat_pairs tVarP] in Hdis, HGs, Havs.
      apply (FOPrH_patf_leaf_elim n G B env 0 y a _ Ha ltac:(lia) HGs);
        [intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm | avoid_tms |].
      lazymatch goal with |- FOPrH _ ?G1 _ =>
        assert (Hca : FOPrH n G1 (FOcpairF (FOnumeral 0) (FOnumeral y) a)) by apply FOPrH_last;
        assert (HC1 : RowCtx n ox X Xb env G1) by (apply RowCtx_ext; [exact HC | ctx_list])
      end.
      pose proof HC1 as [HG1 _].
      destruct (ox_eq ox y) eqn:Eo.
      * destruct ox as [x|]; cbn [ox_eq] in Eo; [|discriminate].
        apply Nat.eqb_eq in Eo. subst y.
        cbn [rho_sub] in Hc. rewrite Nat.eqb_refl in Hc. cbn [FOPATF] in Hc.
        rewrite Hj in Hc. subst X.
        pose proof (FOPrH_N2_var_eq n _ (FOnumeral x) s a (FOnumeral x)
                      ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) Hca
                      (FOPrH_refl _ _ _)) as R.
        exact (FOPrH_tblex_cong n _ _ _ _ _ _ _ _ R (FOPrH_refl _ _ _)
                 (FOPrH_eq_sym _ _ _ _ (FOPrH_weak_app _ _ _ _ Hc)) ltac:(avoid_tms)).
      * assert (Et : rho_sub ox j rho y = None).
        { destruct ox as [x|]; cbn [rho_sub ox_eq] in *; [|exact Ey].
          rewrite Eo. exact Ey. }
        rewrite Et in Hc, HGt, Havt, Hdis. cbn beta iota in Hc, HGt, Havt, Hdis.
        cbn [cpat_span cpat_pairs tVarP] in Hdis, HGt, Havt.
        apply (FOPrH_patf_leaf_elim n _ B' env' 0 y c _ (FOPrH_weak_app _ _ _ _ Hc)
                 ltac:(lia));
          [ctx_list | intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm | avoid_tms |].
        lazymatch goal with |- FOPrH _ ?G2 _ =>
          assert (Hcc : FOPrH n G2 (FOcpairF (FOnumeral 0) (FOnumeral y) c)) by apply FOPrH_last;
          assert (Hca2 : FOPrH n G2 (FOcpairF (FOnumeral 0) (FOnumeral y) a)) by wk_in;
          assert (HC2 : RowCtx n ox X Xb env G2) by (apply RowCtx_ext; [exact HC1 | ctx_list]);
          assert (Hb2 : FOPrH n G2 (FOle (FOSucc a) Xb)) by wk Hb
        end.
        pose proof (FOPrH_cpair_fun n _ _ _ a c ltac:(avoid_tms) Hca2 Hcc) as Eac.
        destruct (FOPrH_cpair_le_cf n _ (FOnumeral 0) (FOnumeral y) a ltac:(avoid_tms) Hca2)
          as [_ Hya].
        pose proof (FOPrH_le_below n _ _ _ _ Hya Hb2 ltac:(avoid_tms)) as Hyb.
        destruct HC2 as [HG2 [_ Hlit2]].
        pose proof (Hlit2 _ y (fun Y HY => HY) Hyb Eo) as Hne.
        pose proof (FOPrH_N2_var_ne n _ X s a (FOnumeral y) ltac:(intros w1 ? ?; apply HG2; lia)
                      ltac:(avoid_tms) Hca2 Hne) as R.
        exact (FOPrH_tblex_cong n _ _ _ _ _ _ _ _ R (FOPrH_refl _ _ _) Eac ltac:(avoid_tms)).
  - (* zero *)
    cbn [cpat_tm] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    cbn [cpat_span cpat_pairs tZeroP] in Hdis, HGs, HGt, Havs, Havt.
    apply (FOPrH_patf_leaf_elim n G B env 1 0 a _ Ha ltac:(lia) HGs);
      [intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm | avoid_tms |].
    apply (FOPrH_patf_leaf_elim n _ B' env' 1 0 c _ (FOPrH_weak_app _ _ _ _ Hc)
             ltac:(lia));
      [ctx_list | intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm | avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G2 _ =>
      assert (Hcc : FOPrH n G2 (FOcpairF (FOnumeral 1) (FOnumeral 0) c)) by apply FOPrH_last;
      assert (Hca : FOPrH n G2 (FOcpairF (FOnumeral 1) (FOnumeral 0) a)) by wk_in;
      assert (HG2 : FOctx_avoid G2 2 1000) by ctx_list
    end.
    pose proof (FOPrH_cpair_fun n _ _ _ a c ltac:(avoid_tms) Hca Hcc) as Eac.
    pose proof (FOPrH_N2_zero n _ X s a ltac:(intros w1 ? ?; apply HG2; lia)
                  ltac:(avoid_tms) Hca) as R.
    exact (FOPrH_tblex_cong n _ _ _ _ _ _ _ _ R (FOPrH_refl _ _ _) Eac ltac:(avoid_tms)).
  - (* successor *)
    cbn [cpat_tm tSuccP] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in Hdis, HGs, HGt, Havs, Havt.
    apply (FOPrH_patf_lit_elim n G B env 2 _ a _ Ha ltac:(lia));
      [cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; exact HGs | intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm
      | cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; avoid_tms |].
    apply (FOPrH_patf_lit_elim n _ B' env' 2 _ c _ (FOPrH_weak_app _ _ _ _ Hc) ltac:(lia));
      [cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; ctx_list | intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm
      | cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G2 _ =>
      assert (Hca : FOPrH n G2 (FOcpairF (FOnumeral 2) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G2 (FOPATF (B + 4) env (cpat_tm rho u) (FOVar (B + 2)))) by wk_in;
      assert (Hcc : FOPrH n G2 (FOcpairF (FOnumeral 2) (FOVar (B' + 2)) c)) by wk_in;
      assert (Hpc : FOPrH n G2 (FOPATF (B' + 4) env' (cpat_tm (rho_sub ox j rho) u)
                                  (FOVar (B' + 2)))) by wk_in;
      assert (HC2 : RowCtx n ox X Xb env G2)
        by (apply RowCtx_ext; [apply RowCtx_ext; [exact HC | ctx_list] | ctx_list]);
      assert (Hb2 : FOPrH n G2 (FOle (FOSucc a) Xb)) by wk Hb;
      assert (HG2 : FOctx_avoid G2 2 1000) by (destruct HC2; tauto)
    end.
    destruct (FOPrH_cpair_le_cf n _ (FOnumeral 2) (FOVar (B + 2)) a ltac:(avoid_tms) Hca)
      as [_ Hua].
    pose proof (IH _ rho (B + 4) (B' + 4) (FOVar (B + 2)) (FOVar (B' + 2)) HE HC2 Hrho Hrx
                  Hpa Hpc (FOPrH_le_below n _ _ _ _ Hua Hb2 ltac:(avoid_tms))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as R.
    exact (FOPrH_N2_succ n _ X s (FOVar (B + 2)) (FOVar (B' + 2)) a c
             ltac:(intros w1 ? ?; apply HG2; lia) ltac:(avoid_tms) R Hca Hcc).
  - (* sum *)
    cbn [cpat_tm tPlusP] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    pose proof (cpat_span_le (cpat_tm rho u)) as Hsu.
    pose proof (cpat_span_le (cpat_tm (rho_sub ox j rho) u)) as Hsu'.
    cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in Hdis, HGs, HGt, Havs, Havt.
    apply (FOPrH_patf_bin_elim n G B env 3 _ _ a _ Ha ltac:(lia));
      [cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; exact HGs | intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm
      | cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; avoid_tms |].
    apply (FOPrH_patf_bin_elim n _ B' env' 3 _ _ c _ (FOPrH_weak_app _ _ _ _ Hc) ltac:(lia));
      [cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; ctx_list | intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm
      | cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G2 _ =>
      assert (Hka : FOPrH n G2 (FOcpairF (FOnumeral 3) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G2 (FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hua : FOPrH n G2 (FOPATF (B + 8) env (cpat_tm rho u) (FOVar (B + 4)))) by wk_in;
      assert (Hwa : FOPrH n G2 (FOPATF (B + 8 + 4 * cpat_pairs (cpat_tm rho u)) env
                                  (cpat_tm rho w) (FOVar (B + 6)))) by wk_in;
      assert (Hkc : FOPrH n G2 (FOcpairF (FOnumeral 3) (FOVar (B' + 2)) c)) by wk_in;
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
    destruct (FOPrH_cpair_le_cf n _ (FOnumeral 3) (FOVar (B + 2)) a ltac:(avoid_tms) Hka)
      as [_ Hpa'].
    destruct (FOPrH_cpair_le_cf n _ (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))
                ltac:(avoid_tms) Hpa) as [Hup Hwp].
    pose proof (FOPrH_le_below n _ _ _ _ Hpa' Hb2 ltac:(avoid_tms)) as Hpb.
    pose proof (IHu _ rho (B + 8) (B' + 8) (FOVar (B + 4)) (FOVar (B' + 4)) HE HC2 Hrho Hrx
                  Hua Huc (FOPrH_le_below n _ _ _ _ Hup Hpb ltac:(avoid_tms))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Ru.
    pose proof (IHw _ rho (B + 8 + 4 * cpat_pairs (cpat_tm rho u))
                  (B' + 8 + 4 * cpat_pairs (cpat_tm (rho_sub ox j rho) u))
                  (FOVar (B + 6)) (FOVar (B' + 6)) HE HC2 Hrho Hrx
                  Hwa Hwc (FOPrH_le_below n _ _ _ _ Hwp Hpb ltac:(avoid_tms))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Rw.
    exact (FOPrH_N2_bin n _ X s a c 3 (FOVar (B + 2)) (FOVar (B + 4)) (FOVar (B + 6))
             (FOVar (B' + 4)) (FOVar (B' + 6)) (FOVar (B' + 2)) ltac:(lia)
             ltac:(intros w1 ? ?; apply HG2; lia) ltac:(avoid_tms) Ru Rw Hka Hpa Hpc Hkc).
  - (* product *)
    cbn [cpat_tm tMultP] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    pose proof (cpat_span_le (cpat_tm rho u)) as Hsu.
    pose proof (cpat_span_le (cpat_tm (rho_sub ox j rho) u)) as Hsu'.
    cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in Hdis, HGs, HGt, Havs, Havt.
    apply (FOPrH_patf_bin_elim n G B env 4 _ _ a _ Ha ltac:(lia));
      [cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; exact HGs | intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm
      | cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; avoid_tms |].
    apply (FOPrH_patf_bin_elim n _ B' env' 4 _ _ c _ (FOPrH_weak_app _ _ _ _ Hc) ltac:(lia));
      [cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; ctx_list | intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm
      | cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G2 _ =>
      assert (Hka : FOPrH n G2 (FOcpairF (FOnumeral 4) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G2 (FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hua : FOPrH n G2 (FOPATF (B + 8) env (cpat_tm rho u) (FOVar (B + 4)))) by wk_in;
      assert (Hwa : FOPrH n G2 (FOPATF (B + 8 + 4 * cpat_pairs (cpat_tm rho u)) env
                                  (cpat_tm rho w) (FOVar (B + 6)))) by wk_in;
      assert (Hkc : FOPrH n G2 (FOcpairF (FOnumeral 4) (FOVar (B' + 2)) c)) by wk_in;
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
    destruct (FOPrH_cpair_le_cf n _ (FOnumeral 4) (FOVar (B + 2)) a ltac:(avoid_tms) Hka)
      as [_ Hpa'].
    destruct (FOPrH_cpair_le_cf n _ (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))
                ltac:(avoid_tms) Hpa) as [Hup Hwp].
    pose proof (FOPrH_le_below n _ _ _ _ Hpa' Hb2 ltac:(avoid_tms)) as Hpb.
    pose proof (IHu _ rho (B + 8) (B' + 8) (FOVar (B + 4)) (FOVar (B' + 4)) HE HC2 Hrho Hrx
                  Hua Huc (FOPrH_le_below n _ _ _ _ Hup Hpb ltac:(avoid_tms))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Ru.
    pose proof (IHw _ rho (B + 8 + 4 * cpat_pairs (cpat_tm rho u))
                  (B' + 8 + 4 * cpat_pairs (cpat_tm (rho_sub ox j rho) u))
                  (FOVar (B + 6)) (FOVar (B' + 6)) HE HC2 Hrho Hrx
                  Hwa Hwc (FOPrH_le_below n _ _ _ _ Hwp Hpb ltac:(avoid_tms))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Rw.
    exact (FOPrH_N2_bin n _ X s a c 4 (FOVar (B + 2)) (FOVar (B + 4)) (FOVar (B + 6))
             (FOVar (B' + 4)) (FOVar (B' + 6)) (FOVar (B' + 2)) ltac:(lia)
             ltac:(intros w1 ? ?; apply HG2; lia) ltac:(avoid_tms) Ru Rw Hka Hpa Hpc Hkc).
Qed.
