From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26.
Open Scope fo_scope.

(** ** Occurrence of a variable in the literal part of a pattern. *)

Fixpoint lit_occ_tm (rho : nat -> option nat) (x : nat) (t : FOTerm) : bool :=
  match t with
  | FOVar y => match rho y with Some _ => false | None => Nat.eqb y x end
  | FOZero => false
  | FOSucc u => lit_occ_tm rho x u
  | FOPlus u w => lit_occ_tm rho x u || lit_occ_tm rho x w
  | FOMult u w => lit_occ_tm rho x u || lit_occ_tm rho x w
  end.

Fixpoint lit_free_f (rho : nat -> option nat) (x : nat) (A : FOFormula) : bool :=
  match A with
  | FOEq u w => lit_occ_tm rho x u || lit_occ_tm rho x w
  | FOFalseF => false
  | FOImplF P Q => lit_free_f rho x P || lit_free_f rho x Q
  | FOForall y P => if Nat.eqb y x then false else lit_free_f (rho_hide y rho) x P
  | FOExists y P => if Nat.eqb y x then false else lit_free_f (rho_hide y rho) x P
  end.

Notation bnum b := (FOnumeral (if b then 1 else 0)).

(** ** Closed facts about numerals. *)

Lemma FOPrH_num_neq : forall n G y x, y <> x ->
  FOPrH n G (FONeg (FOEq (FOnumeral y) (FOnumeral x))).
Proof.
  intros n G y x H. apply FOPrH_empty. apply FOPrH_true_closed.
  - apply FOs1_d0. apply FOd0_impl; [apply FOd0_eq | apply FOd0_false].
  - intros v. unfold FONeg. cbn [FOfree_in]. rewrite !FOin_tm_numeral. reflexivity.
  - unfold FONeg. cbn [FOsat]. rewrite !FOeval_numeral. exact H.
Qed.

(** ** A row rewritten along an equation of its third field. *)

Lemma FOPrH_tblex_cong_a2 : forall n G tg a1 a2 a3 r a2',
  FOPrH n G (FOTBLEX tg a1 a2 a3 r) -> FOPrH n G (FOEq a2 a2') ->
  FOtms_avoid [tg; a1; a2; a3; r; a2'] 2 1000 ->
  FOPrH n G (FOTBLEX tg a1 a2' a3 r).
Proof.
  intros n G tg a1 a2 a3 r a2' H E Hav.
  assert (K : forall t, FOtm_avoid t 2 1000 ->
             FOsubst_f 999 t (FOTBLEX tg a1 (FOVar 999) a3 r) = FOTBLEX tg a1 t a3 r).
  { intros t Ht. rewrite FOsubst_f_TBLEX by lia. rewrite FOsubst_t_var_eq'.
    rewrite !(FOsubst_t_not_in _ 999 t) by fr_tm. reflexivity. }
  assert (V2 : FOtm_avoid a2 2 1000) by avoid_tm.
  assert (V2' : FOtm_avoid a2' 2 1000) by avoid_tm.
  pose proof (FOPrH_leibniz n G 999 a2 a2' (FOTBLEX tg a1 (FOVar 999) a3 r)
                ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm])
                ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm]) E) as L.
  rewrite (K a2 V2), (K a2' V2') in L. exact (L H).
Qed.

(** ** Contexts carrying the rows of the slot codes. *)

Definition SlotCtx (n : nat) (env : list FOTerm) (G : list FOFormula) : Prop :=
  FOctx_avoid G 2 1000 /\
  (forall i, i < length env -> exists w, FOPrH n G (FONUMR w (nth i env FOZero))).

Lemma SlotCtx_ext : forall n env G L,
  SlotCtx n env G -> FOctx_avoid L 2 1000 -> SlotCtx n env (G ++ L).
Proof.
  intros n env G L [H1 H2] HL. split.
  - intros w ? ?. apply FOfree_ctx_app_inv; [apply H1 | apply HL]; lia.
  - intros i Hi. destruct (H2 i Hi) as [w Hw]. exists w. apply FOPrH_weak_app. exact Hw.
Qed.

Ltac span_g := cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP
                      pAllP pExP].
Ltac span_h H := cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP
                        pAllP pExP] in H.

(** ** Occurrence rows for the code of a term (tag [0]). *)

Lemma FOPrH_occ_tm : forall n x t G rho env B a,
  SlotCtx n env G -> (forall z i, rho z = Some i -> i < length env) ->
  FOPrH n G (FOPATF B env (cpat_tm rho t) a) ->
  1000 <= B -> FOctx_avoid G B (B + cpat_span (cpat_tm rho t)) ->
  FOtms_avoid (a :: env) B (B + cpat_span (cpat_tm rho t)) ->
  FOtms_avoid (a :: env) 2 1000 ->
  FOPrH n G (FOTBLEX FOZero (FOnumeral x) a FOZero (bnum (lit_occ_tm rho x t))).
Proof.
  intros n x t.
  induction t as [y| |u IH|u IHu w IHw|u IHu w IHw];
    intros G rho env B a HS Hrho Ha HB HGs Havs Hlo; pose proof HS as [HG Hslot].
  - cbn [cpat_tm lit_occ_tm] in *.
    destruct (rho y) as [i|] eqn:Ey.
    + cbn [FOPATF] in Ha. destruct (Hslot i (Hrho y i Ey)) as [wv Hw].
      assert (Vi : FOtms_avoid [nth i env FOZero] 2 1000).
      { apply FOtms_avoid_cons; [|apply FOtms_avoid_nil]. apply Hlo.
        right. apply nth_In. exact (Hrho y i Ey). }
      pose proof (FOPrH_numr_row0 n G wv (nth i env FOZero) (FOnumeral x) Hw ltac:(avoid_tms))
        as R.
      exact (FOPrH_tblex_cong_a2 n G _ _ _ _ _ _ R (FOPrH_eq_sym _ _ _ _ Ha) ltac:(avoid_tms)).
    + span_h HGs. span_h Havs.
      apply (FOPrH_patf_leaf_elim n G B env 0 y a _ Ha ltac:(lia) HGs);
        [intros w1 H1 H2; free_fm | avoid_tms |].
      lazymatch goal with |- FOPrH _ ?G1 _ =>
        assert (Hca : FOPrH n G1 (FOcpairF (FOnumeral 0) (FOnumeral y) a)) by apply FOPrH_last;
        assert (HG1 : FOctx_avoid G1 2 1000) by ctx_list
      end.
      destruct (Nat.eqb_spec y x) as [->|Hne].
      * exact (FOPrH_N0_var_eq n _ (FOnumeral x) a (FOnumeral x)
                 ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) Hca (FOPrH_refl _ _ _)).
      * exact (FOPrH_N0_var_ne n _ (FOnumeral x) a (FOnumeral y)
                 ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) Hca
                 (FOPrH_num_neq n _ y x Hne)).
  - cbn [cpat_tm lit_occ_tm] in *. span_h HGs. span_h Havs.
    apply (FOPrH_patf_leaf_elim n G B env 1 0 a _ Ha ltac:(lia) HGs);
      [intros w1 H1 H2; free_fm | avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hca : FOPrH n G1 (FOcpairF (FOnumeral 1) (FOnumeral 0) a)) by apply FOPrH_last;
      assert (HG1 : FOctx_avoid G1 2 1000) by ctx_list
    end.
    exact (FOPrH_N0_zero n _ (FOnumeral x) a ltac:(intros w1 ? ?; apply HG1; lia)
             ltac:(avoid_tms) Hca).
  - cbn [cpat_tm lit_occ_tm tSuccP] in *. span_h HGs. span_h Havs.
    apply (FOPrH_patf_lit_elim n G B env 2 _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hca : FOPrH n G1 (FOcpairF (FOnumeral 2) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G1 (FOPATF (B + 4) env (cpat_tm rho u) (FOVar (B + 2)))) by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    pose proof (IH _ rho env (B + 4) (FOVar (B + 2)) HS1 Hrho Hpa ltac:(lia) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms)) as R.
    exact (FOPrH_N0_succ n _ (FOnumeral x) (FOVar (B + 2)) a (bnum (lit_occ_tm rho x u))
             ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) R Hca).
  - cbn [cpat_tm lit_occ_tm tPlusP] in *.
    pose proof (cpat_span_le (cpat_tm rho u)) as Hsu.
    span_h HGs. span_h Havs.
    apply (FOPrH_patf_bin_elim n G B env 3 _ _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 3) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G1 (FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hua : FOPrH n G1 (FOPATF (B + 8) env (cpat_tm rho u) (FOVar (B + 4)))) by wk_in;
      assert (Hwa : FOPrH n G1 (FOPATF (B + 8 + 4 * cpat_pairs (cpat_tm rho u)) env
                                  (cpat_tm rho w) (FOVar (B + 6)))) by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    pose proof (IHu _ rho env (B + 8) (FOVar (B + 4)) HS1 Hrho Hua ltac:(lia) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms)) as Ru.
    destruct (lit_occ_tm rho x u) eqn:Eu; cbn [orb].
    + exact (FOPrH_N0_bin_one n _ (FOnumeral x) a 3 (FOVar (B + 2)) (FOVar (B + 4))
               (FOVar (B + 6)) (or_introl eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Ru Hka Hpa).
    + pose proof (IHw _ rho env (B + 8 + 4 * cpat_pairs (cpat_tm rho u)) (FOVar (B + 6)) HS1
                    Hrho Hwa ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms)) as Rw.
      exact (FOPrH_N0_bin_zero n _ (FOnumeral x) a (bnum (lit_occ_tm rho x w)) 3
               (FOVar (B + 2)) (FOVar (B + 4))
               (FOVar (B + 6)) (or_introl eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Ru Rw Hka Hpa).
  - cbn [cpat_tm lit_occ_tm tMultP] in *.
    pose proof (cpat_span_le (cpat_tm rho u)) as Hsu.
    span_h HGs. span_h Havs.
    apply (FOPrH_patf_bin_elim n G B env 4 _ _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 4) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G1 (FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hua : FOPrH n G1 (FOPATF (B + 8) env (cpat_tm rho u) (FOVar (B + 4)))) by wk_in;
      assert (Hwa : FOPrH n G1 (FOPATF (B + 8 + 4 * cpat_pairs (cpat_tm rho u)) env
                                  (cpat_tm rho w) (FOVar (B + 6)))) by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    pose proof (IHu _ rho env (B + 8) (FOVar (B + 4)) HS1 Hrho Hua ltac:(lia) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms)) as Ru.
    destruct (lit_occ_tm rho x u) eqn:Eu; cbn [orb].
    + exact (FOPrH_N0_bin_one n _ (FOnumeral x) a 4 (FOVar (B + 2)) (FOVar (B + 4))
               (FOVar (B + 6)) (or_intror eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Ru Hka Hpa).
    + pose proof (IHw _ rho env (B + 8 + 4 * cpat_pairs (cpat_tm rho u)) (FOVar (B + 6)) HS1
                    Hrho Hwa ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms)) as Rw.
      exact (FOPrH_N0_bin_zero n _ (FOnumeral x) a (bnum (lit_occ_tm rho x w)) 4
               (FOVar (B + 2)) (FOVar (B + 4))
               (FOVar (B + 6)) (or_intror eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Ru Rw Hka Hpa).
Qed.
