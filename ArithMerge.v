(******************************************************************************)
(*                                                                            *)
(*           Parametric Provability: Bypassing the Loebian Obstacle           *)
(*                                                                            *)
(*     Part 6 of 9. Merging two checked derivations and their tables.         *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer.
Open Scope fo_scope.

(** ** Every justification code has a shift. *)

Lemma FOPrH_em : forall n G A, FOPrH n G (FOOr A (FONeg A)).
Proof. intros n G A. exact (FOPrH_imp_refl n G (FONeg A)). Qed.

Ltac fo_inst_as H t H' :=
  lazymatch type of H with
  | FOPrH ?k ?G (FOForall ?x ?A) =>
      let A' := eval lazy in (FOsubst_f x t A) in
      pose proof (FOPrH_inst' k G x t A A' H ltac:(vm_compute; exact eq_refl)
                    ltac:(vm_compute; exact eq_refl)) as H'
  end.

(** Two premises discharged from the context, the conclusion added to
    it. *)

Ltac fo_mp2 H :=
  lazymatch goal with
  | |- FOPrH ?k ?G ?C =>
      lazymatch type of H with
      | FOPrH _ _ (FOImplF ?P1 (FOImplF ?P2 ?Q)) =>
          refine (FOPrH_cut k G Q C (FOPrH_mp k G P2 Q (FOPrH_mp k G P1 _ H _) _) _);
          [fo_hyp | fo_hyp |]
      end
  end.

Ltac fo_mp1 H :=
  lazymatch goal with
  | |- FOPrH ?k ?G ?C =>
      lazymatch type of H with
      | FOPrH _ _ (FOImplF ?P1 ?Q) =>
          refine (FOPrH_cut k G Q C (FOPrH_mp k G P1 Q H _) _); [fo_hyp |]
      end
  end.

(** The decomposition of the code [#601] is [#700, #701]; a second
    decomposition [#606, #607] agrees with it. *)

Ltac inj_decomp k :=
  let I := fresh "HI" in fo_ctx_thm I (FOPr_cpair_inj k);
  let I1 := fresh "HI" in fo_inst_as I (#606) I1;
  let I2 := fresh "HI" in fo_inst_as I1 (#607) I2;
  let I3 := fresh "HI" in fo_inst_as I2 (#700) I3;
  let I4 := fresh "HI" in fo_inst_as I3 (#701) I4;
  let I5 := fresh "HI" in fo_inst_as I4 (#601) I5;
  clear I I1 I2 I3 I4; fo_mp2 I5; clear I5;
  fo_split (#606 .= #700) (#607 .= #701).

Lemma FOPr_shift_total : forall n,
  FOProvesTn n (.A 420, .A 421, .E 422, .A 423, .A 424,
    FOcpairF #423 #424 #421 .-> FOSHIFTC #420 #423 #424 #422).
Proof.
  intro n.
  change (FOPrH n [] (.A 420, .A 421, .E 422, .A 423, .A 424,
    FOcpairF #423 #424 #421 .-> FOSHIFTC #420 #423 #424 #422)).
  fo_norm_goal. fo_all_as 600. fo_all_as 601.
  fo_ctx_thm HS (FOPr_cpair_surj n). fo_inst_as HS (#601) HS1. clear HS.
  fo_exe_from HS1 700. clear HS1. fo_exe 451 701.
  apply (FOPrH_or_elim n _ (#700 .= FOnumeral 4) (FONeg (#700 .= FOnumeral 4)) _
           (FOPrH_em _ _ _)).
  - (* modus ponens: the payload is a pair of indices *)
    fo_ctx_thm HS (FOPr_cpair_surj n). fo_inst_as HS (#701) HS1. clear HS.
    fo_exe_from HS1 702. clear HS1. fo_exe 451 703.
    fo_ctx_thm HT (FOPr_cpair_total n). fo_inst_as HT (#600 .+ #702) HT1.
    fo_inst_as HT1 (#600 .+ #703) HT2. clear HT HT1. fo_exe_from HT2 704. clear HT2.
    fo_ctx_thm HU (FOPr_cpair_total n). fo_inst_as HU (FOnumeral 4) HU1.
    fo_inst_as HU1 (#704) HU2. clear HU HU1. fo_exe_from HU2 705. clear HU2.
    fo_exi (#705). fo_all_as 606. fo_all_as 607. fo_intro.
    inj_decomp n.
    apply FOPrH_or_intro_l. apply FOPrH_and_intro.
    + eapply FOPrH_eq_trans; fo_hyp.
    + fo_all_as 608. fo_all_as 609. fo_intro.
      fo_assert C1 (FOcpairF #608 #609 #701).
      { apply (FOPrH_cpairF_cong _ _ (#608) (#609) (#607));
          [apply FOPrH_refl | apply FOPrH_refl | fo_hyp | fo_hyp]. }
      fo_have C1.
      fo_ctx_thm HJ (FOPr_cpair_inj n).
      fo_inst_as HJ (#608) HJ1. fo_inst_as HJ1 (#609) HJ2. fo_inst_as HJ2 (#702) HJ3.
      fo_inst_as HJ3 (#703) HJ4. fo_inst_as HJ4 (#701) HJ5. clear HJ HJ1 HJ2 HJ3 HJ4.
      fo_mp2 HJ5. clear HJ5.
      fo_split (#608 .= #702) (#609 .= #703).
      fo_exi (#704). apply FOPrH_and_intro; [|fo_hyp].
      apply (FOPrH_cpairF_cong _ _ (#600 .+ #702) (#600 .+ #703) (#704));
        [fo_lin [(.S .0, #608, #702)] | fo_lin [(.S .0, #609, #703)] | apply FOPrH_refl
        | fo_hyp].
  - apply (FOPrH_or_elim n _ (#700 .= FOnumeral 5) (FONeg (#700 .= FOnumeral 5)) _
             (FOPrH_em _ _ _)).
    + (* generalization: the payload is an index *)
      fo_ctx_thm HT (FOPr_cpair_total n). fo_inst_as HT (FOnumeral 5) HT1.
      fo_inst_as HT1 (#600 .+ #701) HT2. clear HT HT1. fo_exe_from HT2 702. clear HT2.
      fo_exi (#702). fo_all_as 606. fo_all_as 607. fo_intro.
      inj_decomp n.
      apply FOPrH_or_intro_r. apply FOPrH_or_intro_l. apply FOPrH_and_intro.
      * eapply FOPrH_eq_trans; fo_hyp.
      * apply (FOPrH_cpairF_cong _ _ (FOnumeral 5) (#600 .+ #701) (#702));
          [apply FOPrH_refl | fo_lin [(.S .0, #607, #701)] | apply FOPrH_refl | fo_hyp].
    + apply (FOPrH_or_elim n _ (#700 .= FOnumeral 6) (FONeg (#700 .= FOnumeral 6)) _
               (FOPrH_em _ _ _)).
      * (* Loeb: the payload is an index *)
        fo_ctx_thm HT (FOPr_cpair_total n). fo_inst_as HT (FOnumeral 6) HT1.
        fo_inst_as HT1 (#600 .+ #701) HT2. clear HT HT1. fo_exe_from HT2 702. clear HT2.
        fo_exi (#702). fo_all_as 606. fo_all_as 607. fo_intro.
        inj_decomp n.
        apply FOPrH_or_intro_r. apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
        apply FOPrH_and_intro.
        -- eapply FOPrH_eq_trans; fo_hyp.
        -- apply (FOPrH_cpairF_cong _ _ (FOnumeral 6) (#600 .+ #701) (#702));
             [apply FOPrH_refl | fo_lin [(.S .0, #607, #701)] | apply FOPrH_refl | fo_hyp].
      * (* every other code shifts to itself *)
        fo_exi (#601). fo_all_as 606. fo_all_as 607. fo_intro.
        inj_decomp n.
        apply FOPrH_or_intro_r. apply FOPrH_or_intro_r. apply FOPrH_or_intro_r.
        apply FOPrH_and_intro; [|apply FOPrH_and_intro; [|apply FOPrH_and_intro; [|fo_hyp]]].
        -- apply FOPrH_intro. apply FOPrH_efq.
           apply (FOPrH_mp _ _ (#700 .= FOnumeral 4)); [fo_hyp|].
           apply (FOPrH_eq_trans _ _ _ (#606)); [apply FOPrH_eq_sym; fo_hyp | fo_hyp].
        -- apply FOPrH_intro. apply FOPrH_efq.
           apply (FOPrH_mp _ _ (#700 .= FOnumeral 5)); [fo_hyp|].
           apply (FOPrH_eq_trans _ _ _ (#606)); [apply FOPrH_eq_sym; fo_hyp | fo_hyp].
        -- apply FOPrH_intro. apply FOPrH_efq.
           apply (FOPrH_mp _ _ (#700 .= FOnumeral 6)); [fo_hyp|].
           apply (FOPrH_eq_trans _ _ _ (#606)); [apply FOPrH_eq_sym; fo_hyp | fo_hyp].
Qed.

(** ** A track of shifted codes.

    For every track [c, d] and length [l] there is a track whose code
    at each position below [l] is the shift of the code at the same
    position of [c, d]; built by induction on [l], extending by one
    shifted code at each step. *)

Lemma FOPr_shift_map : forall n,
  FOProvesTn n (.A 430, .A 431, .A 432, .A 433, .E 434, .E 435,
    .A 436, (.E 437, #436 .+ .S #437 .= #433) .->
      FOSHROW #430 #431 #432 #434 #435 #436 #436).
Proof.
  intro n.
  change (FOPrH n [] (.A 430, .A 431, .A 432, .A 433, .E 434, .E 435,
    .A 436, (.E 437, #436 .+ .S #437 .= #433) .->
      FOSHROW #430 #431 #432 #434 #435 #436 #436)).
  do 3 fo_all. fo_ind.
  - fo_exi (.0). fo_exi (.0). fo_all. fo_intro. fo_exe 437 700. apply FOPrH_efq.
    apply (FOPrH_Q_succ_nonzero _ _ (#436 .+ #700)).
    fo_lin [(.S .0, .0, #436 .+ .S #700)].
  - fo_exe 434 700. fo_exe 435 701.
    fo_ctx_thm HB (FOPr_beta_total n). fo_inst_as HB (#431) HB1. fo_inst_as HB1 (#432) HB2.
    fo_inst_as HB2 (#433) HB3. clear HB HB1 HB2. fo_exe_from HB3 702. clear HB3.
    fo_ctx_thm HS (FOPr_shift_total n). fo_inst_as HS (#430) HS1.
    fo_inst_as HS1 (#702) HS2. clear HS HS1. fo_exe_from HS2 703. clear HS2.
    fo_ctx_thm HE (FOPr_beta_extend n). fo_inst_as HE (#700) HE1. fo_inst_as HE1 (#701) HE2.
    fo_inst_as HE2 (#433) HE3. fo_inst_as HE3 (#703) HE4. fo_inst_as HE4 (.0) HE5.
    clear HE HE1 HE2 HE3 HE4. fo_exe_from HE5 704. clear HE5. fo_exe 467 705.
    fo_split (.E 468, .0 .+ #468 .= #704)
             (FOAnd (FOAGR (#433) (#700) (#701) (#704) (#705))
                    (FObetaF 488 #704 #705 #433 #703)).
    fo_split (FOAGR (#433) (#700) (#701) (#704) (#705)) (FObetaF 488 #704 #705 #433 #703).
    fo_exi (#704). fo_exi (#705). fo_all_as 706. fo_intro. fo_exe 437 707.
    fo_cases (#707) 708.
    + fo_assert Ek (#433 .= #706).
      { fo_lin [(.S .0, #706 .+ .S #707, .S #433); (.S .0, .0, #707)]. }
      fo_have Ek.
      refine (FOPrH_leibniz n _ 999 (#433) (#706)
                (FOSHROW #430 #431 #432 #704 #705 #999 #999) _ _ _ _);
        [vm_compute; reflexivity | vm_compute; reflexivity | fo_hyp |].
      fo_norm_goal. fo_all_as 709. fo_all_as 710. fo_all_as 711. do 2 fo_intro.
      fo_ctx_thm HF (FOPr_beta_fun n). fo_inst_as HF (#431) HF1. fo_inst_as HF1 (#432) HF2.
      fo_inst_as HF2 (#433) HF3. fo_inst_as HF3 (#711) HF4. fo_inst_as HF4 (#702) HF5.
      clear HF HF1 HF2 HF3 HF4. fo_mp2 HF5. clear HF5.
      fo_assert C1 (FOcpairF #709 #710 #702).
      { apply (FOPrH_cpairF_cong _ _ (#709) (#710) (#711));
          [apply FOPrH_refl | apply FOPrH_refl | fo_hyp | fo_hyp]. }
      fo_have C1.
      fo_assert HT (.A 423, .A 424, FOcpairF #423 #424 #702 .->
                      FOSHIFTC #430 #423 #424 #703). { fo_hyp. }
      fo_inst_as HT (#709) HT1. fo_inst_as HT1 (#710) HT2. clear HT HT1.
      fo_mp1 HT2. clear HT2.
      fo_exi (#703). apply FOPrH_and_intro; [|fo_hyp].
      fo_ctx_thm HR (FOPr_beta_488_484 n). fo_inst_as HR (#704) HR1. fo_inst_as HR1 (#705) HR2.
      fo_inst_as HR2 (#433) HR3. fo_inst_as HR3 (#703) HR4. clear HR HR1 HR2 HR3.
      apply (FOPrH_mp _ _ _ _ HR4). fo_hyp.
    + fo_assert Lk (.E 437, #706 .+ .S #437 .= #433).
      { fo_exi (#708). fo_lin [(.S .0, .S #433, #706 .+ .S #707); (.S .0, #707, .S #708)]. }
      fo_have Lk.
      fo_assert Lk' (.E 470, #706 .+ .S #470 .= #433).
      { fo_exi (#708). fo_lin [(.S .0, .S #433, #706 .+ .S #707); (.S .0, #707, .S #708)]. }
      fo_have Lk'.
      fo_assert HI (.A 436, (.E 437, #436 .+ .S #437 .= #433) .->
                      FOSHROW #430 #431 #432 #700 #701 #436 #436). { fo_hyp. }
      fo_inst_as HI (#706) HI1. clear HI. fo_mp1 HI1. clear HI1.
      fo_all_as 709. fo_all_as 710. fo_all_as 711. do 2 fo_intro.
      fo_assert HO (FOSHROW #430 #431 #432 #700 #701 #706 #706). { fo_hyp. }
      fo_inst_as HO (#709) HO1. fo_inst_as HO1 (#710) HO2. fo_inst_as HO2 (#711) HO3.
      clear HO HO1 HO2. fo_mp2 HO3. clear HO3.
      fo_exe 448 712.
      fo_split (FObetaF 484 #700 #701 #706 #712) (FOSHIFTC #430 #709 #710 #712).
      fo_exi (#712). apply FOPrH_and_intro; [|fo_hyp].
      fo_assert HA (FOAGR (#433) (#700) (#701) (#704) (#705)). { fo_hyp. }
      fo_inst_as HA (#706) HA1. clear HA. fo_mp1 HA1. clear HA1.
      fo_assert HA2 (.A 471, FObetaF 480 #700 #701 #706 #471 .->
                       FObetaF 484 #704 #705 #706 #471). { fo_hyp. }
      fo_inst_as HA2 (#712) HA3. clear HA2.
      apply (FOPrH_mp _ _ _ _ HA3).
      fo_ctx_thm HR (FOPr_beta_484_480 n). fo_inst_as HR (#700) HR1. fo_inst_as HR1 (#701) HR2.
      fo_inst_as HR2 (#706) HR3. fo_inst_as HR3 (#712) HR4. clear HR HR1 HR2 HR3.
      apply (FOPrH_mp _ _ _ _ HR4). fo_hyp.
Qed.

(** ** Agreements: reading rows, composing, shifting. *)

Lemma FOPrH_all_same : forall n G x A, FOPrH n G (FOForall x A) -> FOPrH n G A.
Proof.
  intros n G x A H.
  pose proof (FOPrH_all_elim n G x (FOVar x) A (FOsubst_ok_var_self A x) H) as H1.
  rewrite FOsubst_f_id in H1. exact H1.
Qed.

Lemma FOPrH_agr_row : forall n G L c d c' d' k,
  FOPrH n G (FOAGR L c d c' d') -> FOPrH n G (FOlt470 k L) ->
  FOtms_avoid [L; c; d; c'; d'] 420 500 -> FOtms_avoid [k] 470 500 ->
  FOPrH n G (FOROWAG c d c' d' k k).
Proof.
  intros n G L c d c' d' k HA Hk Hav Hk2.
  assert (Vk : FOtm_avoid k 470 500) by avoid_tm.
  unfold FOAGR in HA. fo_inst_f HA k Vk Hav.
  exact (FOPrH_mp _ _ _ _ HA Hk).
Qed.

Lemma FOPrH_agrs_row : forall n G L Lb c d c' d' k,
  FOPrH n G (FOAGRS L Lb c d c' d') -> FOPrH n G (FOlt470 k Lb) ->
  FOtms_avoid [L; Lb; c; d; c'; d'] 420 500 -> FOtms_avoid [k] 470 500 ->
  FOPrH n G (FOROWAG c d c' d' k (FOPlus L k)).
Proof.
  intros n G L Lb c d c' d' k HA Hk Hav Hk2.
  assert (Vk : FOtm_avoid k 470 500) by avoid_tm.
  unfold FOAGRS in HA. fo_inst_f HA k Vk Hav.
  exact (FOPrH_mp _ _ _ _ HA Hk).
Qed.

Lemma FOPrH_shrow_trans : forall n G L c d c' d' c'' d'' i i' i'',
  FOPrH n G (FOSHROW L c d c' d' i i') -> FOPrH n G (FOROWAG c' d' c'' d'' i' i'') ->
  FOctx_avoid G 420 500 ->
  FOtms_avoid [L; c; d; c'; d'; c''; d''; i; i'; i''] 420 500 ->
  FOPrH n G (FOSHROW L c d c'' d'' i i'').
Proof.
  intros n G L c d c' d' c'' d'' i i' i'' H1 H2 HG Hav.
  unfold FOSHROW.
  apply FOPrH_all_intro; [apply HG; lia|].
  apply FOPrH_all_intro; [apply HG; lia|].
  apply FOPrH_all_intro; [apply HG; lia|].
  apply FOPrH_intro. apply FOPrH_intro.
  lazymatch goal with
  | |- FOPrH _ ?Gc _ =>
      assert (H1w : FOPrH n Gc (FOSHROW L c d c' d' i i')) by wk H1;
      assert (P1 : FOPrH n Gc (FObetaF 480 c d i (FOVar 447))) by wk_in;
      assert (P2 : FOPrH n Gc (FOcpairF (FOVar 445) (FOVar 446) (FOVar 447))) by wk_in
  end.
  unfold FOSHROW in H1w.
  pose proof (FOPrH_all_same _ _ _ _ (FOPrH_all_same _ _ _ _ (FOPrH_all_same _ _ _ _ H1w)))
    as E.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ E P1) P2) as E1.
  clear E H1w P1 P2.
  refine (FOPrH_ex_elim _ _ 448 _ _ _ (FOfree_in_ex_self _ _) E1 _); [free_ctx|].
  apply FOPrH_ex_same.
  lazymatch goal with
  | |- FOPrH _ (?Gc ++ [?A]) _ => pose proof (FOPrH_last n Gc A) as E2
  end.
  apply FOPrH_and_intro; [|exact (FOPrH_and_r _ _ _ _ E2)].
  assert (V : FOtm_avoid (FOVar 448) 480 488) by (apply FOtm_avoid_var; lia).
  lazymatch goal with
  | |- FOPrH _ ?Gc _ => assert (R : FOPrH n Gc (FOROWAG c' d' c'' d'' i' i'')) by wk H2
  end.
  unfold FOROWAG in R. fo_inst_f R (FOVar 448) V Hav.
  refine (FOPrH_mp _ _ _ _ R _).
  apply (FOPrH_rebase_cf n _ 484 480); [lia | avoid_tms | avoid_tms|].
  exact (FOPrH_and_l _ _ _ _ E2).
Qed.

(** Strict and weak bounds combined. *)

Lemma FOPrH_lt470_le : forall n G t L L',
  FOPrH n G (FOlt470 t L) -> FOPrH n G (FOle L L') ->
  FOtms_avoid [t; L; L'] 470 499 ->
  FOPrH n G (FOlt470 t L').
Proof.
  intros n G t L L' H1 H2 Hav.
  refine (FOPrH_ctxfree2 n G _ _ _ _ H1 H2).
  unfold FOlt470, FOle.
  refine (FOPrH_ex_elim n _ 470 (FOEq (FOPlus t (FOSucc (FOVar 470))) L) _ _
            (FOfree_in_ex_self _ _) _ _); [free_ctx | wk_in |].
  refine (FOPrH_ex_elim n _ 498 (FOEq (FOPlus L (FOVar 498)) L') _ _ _ _ _);
    [free_ctx | | wk_in |].
  { cbn [FOfree_in FOin_tm]. nat_eqb_simpl.
    repeat match goal with
           | |- context [FOin_tm 498 ?u] =>
               rewrite (Hav u ltac:(in_list) 498 ltac:(lia) ltac:(lia))
           end.
    reflexivity. }
  apply (FOPrH_ex_intro _ _ 470 (FOPlus (FOVar 470) (FOVar 498)));
    [cbn [FOsubst_ok]; reflexivity|].
  rewrite FOsubst_f_eq, !FOsubst_t_plus, FOsubst_t_succ, FOsubst_t_var_eq'.
  subst_avoid_h Hav.
  fo_lin [(.S .0, L', L .+ #498); (.S .0, L, t .+ .S #470)].
Qed.

Lemma FOPrH_lt470_plus : forall n G k Lb L L',
  FOPrH n G (FOlt470 k Lb) -> FOPrH n G (FOle (FOPlus L Lb) L') ->
  FOtms_avoid [k; Lb; L; L'] 470 499 ->
  FOPrH n G (FOlt470 (FOPlus L k) L').
Proof.
  intros n G k Lb L L' H1 H2 Hav.
  refine (FOPrH_ctxfree2 n G _ _ _ _ H1 H2).
  unfold FOlt470, FOle.
  refine (FOPrH_ex_elim n _ 470 (FOEq (FOPlus k (FOSucc (FOVar 470))) Lb) _ _
            (FOfree_in_ex_self _ _) _ _); [free_ctx | wk_in |].
  refine (FOPrH_ex_elim n _ 498 (FOEq (FOPlus (FOPlus L Lb) (FOVar 498)) L') _ _ _ _ _);
    [free_ctx | | wk_in |].
  { cbn [FOfree_in FOin_tm]. nat_eqb_simpl.
    repeat match goal with
           | |- context [FOin_tm 498 ?u] =>
               rewrite (Hav u ltac:(in_list) 498 ltac:(lia) ltac:(lia))
           end.
    reflexivity. }
  apply (FOPrH_ex_intro _ _ 470 (FOPlus (FOVar 470) (FOVar 498)));
    [cbn [FOsubst_ok]; reflexivity|].
  rewrite FOsubst_f_eq, !FOsubst_t_plus, FOsubst_t_succ, FOsubst_t_var_eq'.
  subst_avoid_h Hav.
  fo_lin [(.S .0, L', L .+ Lb .+ #498); (.S .0, Lb, k .+ .S #470)].
Qed.

(** ** Agreements composed. *)

Lemma FOPrH_agr_trans : forall n G L L' c d c' d' c'' d'',
  FOPrH n G (FOAGR L c d c' d') -> FOPrH n G (FOAGR L' c' d' c'' d'') ->
  FOPrH n G (FOle L L') ->
  FOctx_avoid G 420 500 -> FOtms_avoid [L; L'; c; d; c'; d'; c''; d''] 420 500 ->
  FOPrH n G (FOAGR L c d c'' d'').
Proof.
  intros n G L L' c d c' d' c'' d'' H1 H2 Hle HG Hav.
  unfold FOAGR.
  apply FOPrH_all_intro; [apply HG; lia|]. apply FOPrH_intro.
  apply FOPrH_all_intro; [free_ctx|]. apply FOPrH_intro.
  lazymatch goal with
  | |- FOPrH _ ?Gc _ =>
      assert (A1 : FOPrH n Gc (FOAGR L c d c' d')) by wk H1;
      assert (A2 : FOPrH n Gc (FOAGR L' c' d' c'' d'')) by wk H2;
      assert (P1 : FOPrH n Gc (FOlt470 (FOVar 469) L)) by wk_in;
      assert (P2 : FOPrH n Gc (FObetaF 480 c d (FOVar 469) (FOVar 471))) by wk_in;
      assert (P3 : FOPrH n Gc (FOle L L')) by wk Hle
  end.
  unfold FOAGR in A1, A2.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_all_same _ _ _ _
                (FOPrH_mp _ _ _ _ (FOPrH_all_same _ _ _ _ A1) P1)) P2) as B1.
  refine (FOPrH_mp _ _ _ _ (FOPrH_all_same _ _ _ _
            (FOPrH_mp _ _ _ _ (FOPrH_all_same _ _ _ _ A2) _)) _).
  - apply (FOPrH_lt470_le _ _ _ L); [exact P1 | exact P3 | avoid_tms].
  - apply (FOPrH_rebase_cf n _ 484 480); [lia | avoid_tms | avoid_tms | exact B1].
Qed.

Lemma FOPrH_agrs_agr : forall n G L Lb L' c d c' d' c'' d'',
  FOPrH n G (FOAGRS L Lb c d c' d') -> FOPrH n G (FOAGR L' c' d' c'' d'') ->
  FOPrH n G (FOle (FOPlus L Lb) L') ->
  FOctx_avoid G 420 500 -> FOtms_avoid [L; Lb; L'; c; d; c'; d'; c''; d''] 420 500 ->
  FOPrH n G (FOAGRS L Lb c d c'' d'').
Proof.
  intros n G L Lb L' c d c' d' c'' d'' H1 H2 Hle HG Hav.
  unfold FOAGRS.
  apply FOPrH_all_intro; [apply HG; lia|]. apply FOPrH_intro.
  apply FOPrH_all_intro; [free_ctx|]. apply FOPrH_intro.
  lazymatch goal with
  | |- FOPrH _ ?Gc _ =>
      assert (A1 : FOPrH n Gc (FOAGRS L Lb c d c' d')) by wk H1;
      assert (A2 : FOPrH n Gc (FOAGR L' c' d' c'' d'')) by wk H2;
      assert (P1 : FOPrH n Gc (FOlt470 (FOVar 469) Lb)) by wk_in;
      assert (P2 : FOPrH n Gc (FObetaF 480 c d (FOVar 469) (FOVar 471))) by wk_in;
      assert (P3 : FOPrH n Gc (FOle (FOPlus L Lb) L')) by wk Hle
  end.
  unfold FOAGRS in A1.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_all_same _ _ _ _
                (FOPrH_mp _ _ _ _ (FOPrH_all_same _ _ _ _ A1) P1)) P2) as B1.
  pose proof (FOPrH_lt470_plus _ _ _ Lb L L' P1 P3 ltac:(avoid_tms)) as Hlt.
  pose proof (FOPrH_agr_row n _ L' c' d' c'' d'' _ A2 Hlt ltac:(avoid_tms) ltac:(avoid_tms))
    as R.
  unfold FOROWAG in R.
  refine (FOPrH_mp _ _ _ _ (FOPrH_all_same _ _ _ _ R) _).
  apply (FOPrH_rebase_cf n _ 484 480); [lia | avoid_tms | avoid_tms | exact B1].
Qed.

(** ** Bounded universals instantiated and split. *)

Lemma FOPrH_ltv_of_lt470 : forall n G v t s,
  FOPrH n G (FOlt470 s t) -> v < 420 ->
  FOtms_avoid [s; t] (S v) (S (S v)) -> FOtms_avoid [s; t] 470 471 ->
  FOPrH n G (FOExists (S v) (FOEq (FOPlus s (FOSucc (FOVar (S v)))) t)).
Proof.
  intros n G v t s H Hv Hav1 Hav2.
  refine (FOPrH_mp _ _ _ _ _ H). apply FOPrH_exeq_rename; [lia | fr_tm | fr_tm | fr_tm | fr_tm].
Qed.

Lemma FOPrH_ball_inst : forall n G v t s P,
  FOPrH n G (FOBallC v t P) -> FOPrH n G (FOlt470 s t) -> v < 420 ->
  FOsubst_ok v s P = true ->
  FOtms_avoid [s; t] (S v) (S (S v)) -> FOtms_avoid [s; t] 470 471 ->
  FOtms_avoid [t] v (S v) ->
  FOPrH n G (FOsubst_f v s P).
Proof.
  intros n G v t s P H Hlt Hv Hok Hav1 Hav2 Hav3.
  rewrite FOBallC_ltv in H.
  assert (Ok : FOsubst_ok v s (FOImplF (FOltv v t) P) = true).
  { apply FOsubst_ok_impl; [|exact Hok]. unfold FOltv.
    apply FOsubst_ok_ex; [fr_tm | apply FOsubst_ok_eq]. }
  pose proof (FOPrH_all_elim n G v s _ Ok H) as H1.
  rewrite FOsubst_f_impl in H1. refine (FOPrH_mp _ _ _ _ H1 _).
  unfold FOltv. rewrite FOsubst_f_ex_ne by lia.
  rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_var_eq', FOsubst_t_succ,
    FOsubst_t_var_ne by lia.
  rewrite (FOsubst_t_not_in t v s ltac:(fr_tm)).
  apply FOPrH_ltv_of_lt470; [exact Hlt | lia | exact Hav1 | exact Hav2].
Qed.

(** ** The sequence constructions at terms, with their witnesses named.

    Each lemma instantiates a closed construction theorem at argument
    terms and names the witnesses it produces by fresh variables, so a
    derivation using it adds one conjunction to its context. *)

Definition FOCATF (b l1 c1 d1 l2 c2 d2 c' d' : FOTerm) : FOFormula :=
  FOAnd (FOExists 468 (FOEq (FOPlus b (FOVar 468)) c'))
    (FOAnd (FOAGR l1 c1 d1 c' d') (FOAGRS l1 l2 c2 d2 c' d')).

Definition FOEXTF (b l c d x c' d' : FOTerm) : FOFormula :=
  FOAnd (FOExists 468 (FOEq (FOPlus b (FOVar 468)) c'))
    (FOAnd (FOAGR l c d c' d') (FObetaF 488 c' d' l x)).

Definition FOMAPF (L c d l c' d' : FOTerm) : FOFormula :=
  FOForall 436 (FOImplF (FOExists 437 (FOEq (FOPlus (FOVar 436) (FOSucc (FOVar 437))) l))
    (FOSHROW L c d c' d' (FOVar 436) (FOVar 436))).

(** Instantiation and substitution through a single top-down pass of
    the substitution rewrites. *)

Ltac fo_inst_g H t V Hav :=
  lazymatch type of H with
  | FOPrH ?k ?G (FOForall ?x ?A) =>
      let H1 := fresh "HI" in
      pose proof (FOPrH_inst k G x t A H ltac:(ok_fast V)) as H1;
      rewrite_strat (topdown (hints fosubf)) in H1; subst_avoid_hin Hav H1;
      clear H; rename H1 into H
  end.

Ltac subst_goal Hav :=
  (rewrite_strat (topdown (hints fosubf))); subst_avoid_h Hav.

Ltac exe_named H w :=
  lazymatch type of H with
  | FOPrH ?k ?G (FOExists ?z ?A) =>
      refine (FOPrH_exe k G z w A _ H _ _ _ _ _);
      [ free_ctx | assumption | free_fm
      | let V := fresh "V" in
        assert (V : FOtm_avoid (FOVar w) 420 500) by (apply FOtm_avoid_var; lia);
        ok_fast V
      | ]
  end.

Lemma FOPrH_concat_elim : forall n G c1 d1 l1 c2 d2 l2 b w1 w2 C,
  FOctx_avoid G 420 500 ->
  FOtms_avoid [c1; d1; l1; c2; d2; l2; b] 420 500 ->
  2 <= w1 -> w1 < 420 -> 2 <= w2 -> w2 < 420 -> w1 <> w2 ->
  FOfree_ctx w1 G -> FOfree_ctx w2 G -> FOfree_in w1 C = false -> FOfree_in w2 C = false ->
  FOtms_avoid [c1; d1; l1; c2; d2; l2; b] w1 (S w1) ->
  FOtms_avoid [c1; d1; l1; c2; d2; l2; b] w2 (S w2) ->
  FOPrH n (G ++ [FOCATF b l1 c1 d1 l2 c2 d2 (FOVar w1) (FOVar w2)]) C ->
  FOPrH n G C.
Proof.
  intros n G c1 d1 l1 c2 d2 l2 b w1 w2 C HG Hav Hw1 Hw1' Hw2 Hw2' Hw12 HG1 HG2 HC1 HC2
    Hav1 Hav2 H0.
  pose proof (FOPrH_thm n G _ (FOPr_beta_concat n)) as H.
  assert (V1 : FOtm_avoid c1 420 500) by avoid_tm.
  assert (V2 : FOtm_avoid d1 420 500) by avoid_tm.
  assert (V3 : FOtm_avoid l1 420 500) by avoid_tm.
  assert (V4 : FOtm_avoid c2 420 500) by avoid_tm.
  assert (V5 : FOtm_avoid d2 420 500) by avoid_tm.
  assert (V6 : FOtm_avoid l2 420 500) by avoid_tm.
  assert (V7 : FOtm_avoid b 420 500) by avoid_tm.
  fo_inst_g H c1 V1 Hav. fo_inst_g H d1 V2 Hav. fo_inst_g H l1 V3 Hav.
  fo_inst_g H c2 V4 Hav. fo_inst_g H d2 V5 Hav. fo_inst_g H l2 V6 Hav.
  fo_inst_g H b V7 Hav.
  exe_named H w1.
  subst_goal Hav.
  lazymatch goal with
  | |- FOPrH _ (?Gc ++ [FOExists ?z ?A]) _ =>
      pose proof (FOPrH_last n Gc (FOExists z A)) as H'
  end.
  exe_named H' w2.
  subst_goal Hav.
  refine (FOPrH_weaken n _ _ _ _ H0).
  intros X HX. apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
  - apply in_or_app. left. apply in_or_app. left. exact HX.
  - apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPrH_extend_elim : forall n G c d l x b w1 w2 C,
  FOctx_avoid G 420 500 ->
  FOtms_avoid [c; d; l; x; b] 420 500 ->
  2 <= w1 -> w1 < 420 -> 2 <= w2 -> w2 < 420 -> w1 <> w2 ->
  FOfree_ctx w1 G -> FOfree_ctx w2 G -> FOfree_in w1 C = false -> FOfree_in w2 C = false ->
  FOtms_avoid [c; d; l; x; b] w1 (S w1) ->
  FOtms_avoid [c; d; l; x; b] w2 (S w2) ->
  FOPrH n (G ++ [FOEXTF b l c d x (FOVar w1) (FOVar w2)]) C ->
  FOPrH n G C.
Proof.
  intros n G c d l x b w1 w2 C HG Hav Hw1 Hw1' Hw2 Hw2' Hw12 HG1 HG2 HC1 HC2
    Hav1 Hav2 H0.
  pose proof (FOPrH_thm n G _ (FOPr_beta_extend n)) as H.
  assert (V1 : FOtm_avoid c 420 500) by avoid_tm.
  assert (V2 : FOtm_avoid d 420 500) by avoid_tm.
  assert (V3 : FOtm_avoid l 420 500) by avoid_tm.
  assert (V4 : FOtm_avoid x 420 500) by avoid_tm.
  assert (V5 : FOtm_avoid b 420 500) by avoid_tm.
  fo_inst_g H c V1 Hav. fo_inst_g H d V2 Hav. fo_inst_g H l V3 Hav.
  fo_inst_g H x V4 Hav. fo_inst_g H b V5 Hav.
  exe_named H w1.
  subst_goal Hav.
  lazymatch goal with
  | |- FOPrH _ (?Gc ++ [FOExists ?z ?A]) _ =>
      pose proof (FOPrH_last n Gc (FOExists z A)) as H'
  end.
  exe_named H' w2.
  subst_goal Hav.
  refine (FOPrH_weaken n _ _ _ _ H0).
  intros X HX. apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
  - apply in_or_app. left. apply in_or_app. left. exact HX.
  - apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOsubst_f_SHROW : forall x s L cj dj cj' dj' i i', x < 440 ->
  FOsubst_f x s (FOSHROW L cj dj cj' dj' i i') =
  FOSHROW (FOsubst_t x s L) (FOsubst_t x s cj) (FOsubst_t x s dj) (FOsubst_t x s cj')
    (FOsubst_t x s dj') (FOsubst_t x s i) (FOsubst_t x s i').
Proof. intros. unfold FOSHROW. autorewrite with fosubf. reflexivity. Qed.

Hint Rewrite FOsubst_f_SHROW using nat_fast : fosubf.

Lemma FOsubst_ok_SHROW : forall x s L cj dj cj' dj' i i', FOtm_avoid s 440 490 ->
  FOsubst_ok x s (FOSHROW L cj dj cj' dj' i i') = true.
Proof.
  intros. unfold FOSHROW.
  repeat (apply FOsubst_ok_all; [match goal with H : FOtm_avoid _ _ _ |- _ => apply H; lia end|]).
  apply FOsubst_ok_impl; [apply FOsubst_ok_betaF; refine (FOtm_avoid_sub _ _ _ _ _ H _ _); lia|].
  apply FOsubst_ok_impl; [apply FOsubst_ok_cpairF|].
  apply FOsubst_ok_ex; [apply H; lia|].
  apply FOsubst_ok_and; [apply FOsubst_ok_betaF; refine (FOtm_avoid_sub _ _ _ _ _ H _ _); lia|].
  apply FOsubst_ok_SHIFTC. refine (FOtm_avoid_sub _ _ _ _ _ H _ _); lia.
Qed.

Ltac ok_fast_leaf V ::=
  lazymatch goal with
  | |- FOsubst_ok _ _ (FOROWAG _ _ _ _ _ _) = true =>
      apply FOsubst_ok_ROWAG; refine (FOtm_avoid_sub _ _ _ _ _ V _ _); lia
  | |- FOsubst_ok _ _ (FOcpairF _ _ _) = true => apply FOsubst_ok_cpairF
  | |- FOsubst_ok _ _ (FOSHIFTC _ _ _ _) = true =>
      apply FOsubst_ok_SHIFTC; refine (FOtm_avoid_sub _ _ _ _ _ V _ _); lia
  | |- FOsubst_ok _ _ (FOSHIFTMP _ _ _) = true =>
      apply FOsubst_ok_SHIFTMP; refine (FOtm_avoid_sub _ _ _ _ _ V _ _); lia
  | |- FOsubst_ok _ _ (FOSHROW _ _ _ _ _ _ _) = true =>
      apply FOsubst_ok_SHROW; refine (FOtm_avoid_sub _ _ _ _ _ V _ _); lia
  end.

Lemma FOPrH_map_elim : forall n G L c d l w1 w2 C,
  FOctx_avoid G 420 500 ->
  FOtms_avoid [L; c; d; l] 420 500 ->
  2 <= w1 -> w1 < 420 -> 2 <= w2 -> w2 < 420 -> w1 <> w2 ->
  FOfree_ctx w1 G -> FOfree_ctx w2 G -> FOfree_in w1 C = false -> FOfree_in w2 C = false ->
  FOtms_avoid [L; c; d; l] w1 (S w1) ->
  FOtms_avoid [L; c; d; l] w2 (S w2) ->
  FOPrH n (G ++ [FOMAPF L c d l (FOVar w1) (FOVar w2)]) C ->
  FOPrH n G C.
Proof.
  intros n G L c d l w1 w2 C HG Hav Hw1 Hw1' Hw2 Hw2' Hw12 HG1 HG2 HC1 HC2
    Hav1 Hav2 H0.
  pose proof (FOPrH_thm n G _ (FOPr_shift_map n)) as H.
  assert (V1 : FOtm_avoid L 420 500) by avoid_tm.
  assert (V2 : FOtm_avoid c 420 500) by avoid_tm.
  assert (V3 : FOtm_avoid d 420 500) by avoid_tm.
  assert (V4 : FOtm_avoid l 420 500) by avoid_tm.
  fo_inst_g H L V1 Hav. fo_inst_g H c V2 Hav. fo_inst_g H d V3 Hav.
  fo_inst_g H l V4 Hav.
  exe_named H w1.
  subst_goal Hav.
  lazymatch goal with
  | |- FOPrH _ (?Gc ++ [FOExists ?z ?A]) _ =>
      pose proof (FOPrH_last n Gc (FOExists z A)) as H'
  end.
  exe_named H' w2.
  subst_goal Hav.
  refine (FOPrH_weaken n _ _ _ _ H0).
  intros X HX. apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
  - apply in_or_app. left. apply in_or_app. left. exact HX.
  - apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPrH_cpair_elim : forall n G a b w C,
  FOctx_avoid G 420 500 ->
  FOtms_avoid [a; b] 420 500 ->
  2 <= w -> w < 420 ->
  FOfree_ctx w G -> FOfree_in w C = false ->
  FOtms_avoid [a; b] w (S w) ->
  FOPrH n (G ++ [FOcpairF a b (FOVar w)]) C ->
  FOPrH n G C.
Proof.
  intros n G a b w C HG Hav Hw1 Hw1' HGw HCw Hav1 H0.
  pose proof (FOPrH_thm n G _ (FOPr_cpair_total n)) as H.
  assert (V1 : FOtm_avoid a 420 500) by avoid_tm.
  assert (V2 : FOtm_avoid b 420 500) by avoid_tm.
  fo_inst_g H a V1 Hav. fo_inst_g H b V2 Hav.
  exe_named H w.
  subst_goal Hav.
  exact H0.
Qed.

(** ** A bounded universal over [a + b], the second range indexed by a
    chosen variable [w]. *)

Lemma FOPrH_ball_split_w : forall n G v a b P w,
  FOPrH n G (FOBallC v a P) ->
  FOPrH n G (FOForall w (FOImplF (FOlt470 (FOVar w) b)
                                  (FOsubst_f v (FOPlus a (FOVar w)) P))) ->
  FOsubst_ok v (FOPlus a (FOVar w)) P = true ->
  2 <= v -> v < 399 -> 2 <= w -> w < 420 -> w <> v -> w <> S v ->
  FOfree_ctx v G -> FOfree_ctx (S v) G -> FOfree_ctx w G -> FOctx_avoid G 420 500 ->
  FOfree_in w P = false -> FOfree_in (S v) P = false ->
  FOtms_avoid [a; b] v (S (S v)) -> FOtms_avoid [a; b] 400 500 ->
  FOtms_avoid [a; b] w (S w) ->
  FOPrH n G (FOBallC v (FOPlus a b) P).
Proof.
  intros n G v a b P w H1 H2 Hok Hv1 Hv2 Hw1 Hw2 Hwv HwSv HGv HGSv HGw HG FP FSP
    Hav1 Hav2 Hav3.
  rewrite FOBallC_ltv. apply FOPrH_all_intro; [exact HGv|]. apply FOPrH_intro.
  pose proof (FOPrH_thm n (G ++ [FOltv v (FOPlus a b)]) _ (FOPr_total n)) as T0.
  assert (Va : FOtm_avoid a 400 500) by avoid_tm.
  assert (Vv : FOtm_avoid (FOVar v) 400 500) by (apply FOtm_avoid_var; lia).
  assert (Hav4 : FOtms_avoid [a] 400 500) by avoid_tms.
  fo_inst_f T0 a Va Hav4. fo_inst_f T0 (FOVar v) Vv Hav4.
  apply (FOPrH_or_elim _ _ _ _ _ T0).
  - refine (FOPrH_exe _ _ 450 w _ _ (FOPrH_last _ _ _) _ _ _ _ _);
      [free_ctx | exact FP
      | cbn [FOfree_in FOin_tm]; nat_eqb_simpl;
        rewrite (Hav3 a ltac:(in_list) w ltac:(lia) ltac:(lia)); reflexivity
      | cbn [FOsubst_ok]; reflexivity |].
    rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_var_eq', FOsubst_t_var_ne by lia.
    rewrite (FOsubst_t_not_in a 450 _ ltac:(fr_tm)).
    refine (FOPrH_ex_elim _ _ (S v) (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                                         (FOPlus a b)) _ _ FSP _ _);
      [free_ctx | unfold FOltv; wk_in |].
    lazymatch goal with
    | |- FOPrH _ ?Gc _ =>
        assert (E1 : FOPrH n Gc (FOEq (FOPlus a (FOVar w)) (FOVar v))) by wk_in;
        assert (H2w : FOPrH n Gc (FOForall w (FOImplF (FOlt470 (FOVar w) b)
                                   (FOsubst_f v (FOPlus a (FOVar w)) P)))) by wk H2;
        assert (Lt : FOPrH n Gc (FOlt470 (FOVar w) b))
    end.
    { unfold FOlt470.
      apply (FOPrH_ex_intro _ _ 470 (FOVar (S v))); [cbn [FOsubst_ok]; reflexivity|].
      rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_succ, FOsubst_t_var_eq',
        FOsubst_t_var_ne by lia.
      rewrite (FOsubst_t_not_in b 470 _ ltac:(fr_tm)).
      apply (FOPrH_add_cancel _ _ _ _ a).
      fo_lin [(.S .0, #v, a .+ #w); (.S .0, a .+ b, #v .+ .S (FOVar (S v)))]. }
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_all_same _ _ _ _ H2w) Lt) as E2.
    pose proof (FOPrH_leibniz _ _ v (FOPlus a (FOVar w)) (FOVar v) P Hok
                  (FOsubst_ok_var_self P v) E1 E2) as E3.
    rewrite FOsubst_f_id in E3. exact E3.
  - lazymatch goal with
    | |- FOPrH _ ?Gc _ => assert (H1w : FOPrH n Gc (FOBallC v a P)) by wk H1
    end.
    rewrite FOBallC_ltv in H1w.
    refine (FOPrH_mp _ _ _ _ (FOPrH_all_same _ _ _ _ H1w) _).
    unfold FOltv.
    refine (FOPrH_mp _ _ _ _ (FOPrH_exeq_rename _ _ 450 (S v) (FOVar v) a _ _ _ _ _) _);
      [lia | fr_tm | fr_tm | fr_tm | fr_tm | apply FOPrH_last].
Qed.

(** ** Freshness of the construction formulas at any variable. *)

Lemma FOfree_in_AGR_any : forall w L c d c' d',
  2 <= w -> FOtms_avoid [L; c; d; c'; d'] w (S w) ->
  FOfree_in w (FOAGR L c d c' d') = false.
Proof.
  intros w L c d c' d' Hw Hav.
  assert (A : forall u, In u [L; c; d; c'; d'] -> FOin_tm w u = false)
    by (intros u Hu; exact (Hav u Hu w ltac:(lia) ltac:(lia))).
  unfold FOAGR.
  destruct (Nat.eq_dec w 469) as [->|H1]; [apply FOfree_in_all_self|].
  rewrite FOfree_in_all_ne, FOfree_in_impl by lia.
  apply Bool.orb_false_iff. split.
  - destruct (Nat.eq_dec w 470) as [->|H2]; [apply FOfree_in_ex_self|].
    rewrite FOfree_in_FOExists_neq by lia. cbn [FOfree_in FOin_tm].
    rewrite (A L ltac:(in_list)). nat_eqb_simpl. reflexivity.
  - destruct (Nat.eq_dec w 471) as [->|H3]; [apply FOfree_in_all_self|].
    rewrite FOfree_in_all_ne, FOfree_in_impl by lia.
    rewrite !FOfree_in_betaF_not; try reflexivity; try lia;
      first [ apply A; in_list | apply FOin_tm_var_ne; lia ].
Qed.

Lemma FOfree_in_ex468_any : forall w b c,
  FOin_tm w b = false -> FOin_tm w c = false ->
  FOfree_in w (FOExists 468 (FOEq (FOPlus b (FOVar 468)) c)) = false.
Proof.
  intros w b c Hb Hc. cbn [FOfree_in FOin_tm]. rewrite Hb, Hc. free_any_close.
Qed.

Definition FOM3F (c1 d1 l1 c2 d2 l2 c3 d3 l3 c' d' : FOTerm) : FOFormula :=
  FOAnd (FOle (FOSucc c1) (FOSucc c'))
  (FOAnd (FOle (FOSucc c2) (FOSucc c'))
  (FOAnd (FOle (FOSucc c3) (FOSucc c'))
  (FOAnd (FOAGR l1 c1 d1 c' d')
  (FOAnd (FOAGRS l1 l2 c2 d2 c' d')
         (FOAGRS (FOPlus l1 l2) l3 c3 d3 c' d'))))).

Ltac free_fm ::=
  lazymatch goal with
  | |- FOfree_in _ (FOltv _ _) = false => apply FOfree_in_ltv; [lia | fr_tm]
  | |- FOfree_in _ (FObetaF _ _ _ _ _) = false =>
      apply FOfree_in_betaF_not; [lia | fr_tm | fr_tm | fr_tm | fr_tm]
  | |- FOfree_in _ (FOcpairF _ _ _) = false =>
      rewrite FOfree_in_FOcpairF; apply Bool.orb_false_iff; split;
      [apply Bool.orb_false_iff; split|]; fr_tm
  | |- FOfree_in _ (FOle _ _) = false => apply FOfree_in_le_any; fr_tm
  | |- FOfree_in _ (FOlt470 _ _) = false => apply FOfree_in_lt470_any; fr_tm
  | |- FOfree_in _ (FOSHIFTMP _ _ _) = false => apply FOfree_in_SHIFTMP_any; fr_tm
  | |- FOfree_in _ (FOSHIFTC _ _ _ _) = false => apply FOfree_in_SHIFTC_any; fr_tm
  | |- FOfree_in _ (FOROWAG _ _ _ _ _ _) = false =>
      apply FOfree_in_ROWAG_any; [lia | avoid_tms]
  | |- FOfree_in _ (FOAGRS _ _ _ _ _ _) = false =>
      apply FOfree_in_AGRS_any; [lia | avoid_tms]
  | |- FOfree_in _ (FOAGR _ _ _ _ _) = false =>
      apply FOfree_in_AGR_any; [lia | avoid_tms]
  | |- FOfree_in _ (FOSHROW _ _ _ _ _ _ _) = false =>
      apply FOfree_in_SHROW_any; [lia | avoid_tms]
  | |- FOfree_in _ (FOExists 468 (FOEq (FOPlus _ (FOVar 468)) _)) = false =>
      apply FOfree_in_ex468_any; fr_tm
  | |- FOfree_in _ (FOCATF _ _ _ _ _ _ _ _ _) = false => unfold FOCATF; free_fm
  | |- FOfree_in _ (FOEXTF _ _ _ _ _ _ _) = false => unfold FOEXTF; free_fm
  | |- FOfree_in _ (FOM3F _ _ _ _ _ _ _ _ _ _ _) = false => unfold FOM3F; free_fm
  | |- FOfree_in _ (FOEq _ _) = false =>
      cbn [FOfree_in]; apply Bool.orb_false_iff; split; fr_tm
  | |- FOfree_in _ (FONeg _) = false => rewrite FOfree_in_FONeg; free_fm
  | |- FOfree_in _ (FOAnd _ _) = false =>
      rewrite FOfree_in_FOAnd; apply Bool.orb_false_iff; split; free_fm
  | |- FOfree_in _ (FOOr _ _) = false =>
      rewrite FOfree_in_FOOr; apply Bool.orb_false_iff; split; free_fm
  | |- FOfree_in _ (FOImplF _ _) = false =>
      rewrite FOfree_in_impl; apply Bool.orb_false_iff; split; free_fm
  | |- FOfree_in ?w (FOExists ?y _) = false =>
      first [ constr_eq w y; apply FOfree_in_ex_self
            | rewrite FOfree_in_FOExists_neq by lia; free_fm ]
  | |- FOfree_in ?w (FOForall ?y _) = false =>
      first [ constr_eq w y; apply FOfree_in_all_self
            | rewrite FOfree_in_all_ne by lia; free_fm ]
  | |- FOfree_in _ FOFalseF = false => reflexivity
  end.

(** ** Code bounds through two concatenations. *)

Lemma FOPrH_bound3 : forall n G c1 c2 c3 x w,
  FOPrH n G (FOExists 468 (FOEq (FOPlus (FOPlus c1 c2) (FOVar 468)) x)) ->
  FOPrH n G (FOExists 468 (FOEq (FOPlus (FOPlus x c3) (FOVar 468)) w)) ->
  FOtms_avoid [c1; c2; c3; x; w] 420 500 ->
  FOPrH n G (FOle (FOSucc c1) (FOSucc w)) /\ FOPrH n G (FOle (FOSucc c2) (FOSucc w)) /\
  FOPrH n G (FOle (FOSucc c3) (FOSucc w)).
Proof.
  intros n G c1 c2 c3 x w H1 H2 Hav.
  assert (K : forall t k, FOtms_avoid [t] 420 500 ->
            FOPrH n [FOEq (FOPlus (FOPlus c1 c2) (FOVar 468)) x;
                     FOEq (FOPlus (FOPlus x c3) (FOVar 499)) w]
              (FOEq (FOPlus (FOSucc t) k) (FOSucc w)) ->
            FOPrH n G (FOle (FOSucc t) (FOSucc w))).
  { intros t k Havk HK.
    refine (FOPrH_ctxfree2 n G _ _ _ _ H1 H2).
    refine (FOPrH_ex_elim n _ 468 (FOEq (FOPlus (FOPlus c1 c2) (FOVar 468)) x) _ _ _ _ _);
      [free_ctx | free_fm | wk_in |].
    refine (FOPrH_exe n _ 468 499 (FOEq (FOPlus (FOPlus x c3) (FOVar 468)) w) _ _ _ _ _ _ _);
      [wk_in | free_ctx | free_fm | free_fm | cbn [FOsubst_ok]; reflexivity |].
    rewrite FOsubst_f_eq, !FOsubst_t_plus, FOsubst_t_var_eq'. subst_avoid_h Hav.
    unfold FOle. apply (FOPrH_ex_intro _ _ 498 k); [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_eq, FOsubst_t_plus, !FOsubst_t_succ, FOsubst_t_var_eq'.
    subst_avoid_h Hav. subst_avoid_h Havk.
    refine (FOPrH_weaken n _ _ _ _ HK).
    intros X [<-|[<-|[]]]; [apply in_or_app; left; apply in_or_app; right; left; reflexivity
                           | apply in_or_app; right; left; reflexivity]. }
  split; [|split].
  - apply (K c1 (FOPlus (FOPlus (FOPlus c2 (FOVar 468)) c3) (FOVar 499))); [avoid_tms|].
    fo_lin [(.S .0, w, x .+ c3 .+ #499); (.S .0, x, c1 .+ c2 .+ #468)].
  - apply (K c2 (FOPlus (FOPlus (FOPlus c1 (FOVar 468)) c3) (FOVar 499))); [avoid_tms|].
    fo_lin [(.S .0, w, x .+ c3 .+ #499); (.S .0, x, c1 .+ c2 .+ #468)].
  - apply (K c3 (FOPlus x (FOVar 499))); [avoid_tms|].
    fo_lin [(.S .0, w, x .+ c3 .+ #499)].
Qed.

(** ** One column of the merged table: three sequences concatenated. *)

Lemma FOPrH_merge3_elim : forall n G c1 d1 l1 c2 d2 l2 c3 d3 l3 x1 x2 w1 w2 C,
  FOctx_avoid G 420 500 ->
  FOtms_avoid [c1; d1; l1; c2; d2; l2; c3; d3; l3] 420 500 ->
  2 <= x1 -> x1 < 420 -> 2 <= x2 -> x2 < 420 -> 2 <= w1 -> w1 < 420 -> 2 <= w2 -> w2 < 420 ->
  x1 <> x2 -> x1 <> w1 -> x1 <> w2 -> x2 <> w1 -> x2 <> w2 -> w1 <> w2 ->
  FOfree_ctx x1 G -> FOfree_ctx x2 G -> FOfree_ctx w1 G -> FOfree_ctx w2 G ->
  FOfree_in x1 C = false -> FOfree_in x2 C = false ->
  FOfree_in w1 C = false -> FOfree_in w2 C = false ->
  FOtms_avoid [c1; d1; l1; c2; d2; l2; c3; d3; l3] x1 (S x1) ->
  FOtms_avoid [c1; d1; l1; c2; d2; l2; c3; d3; l3] x2 (S x2) ->
  FOtms_avoid [c1; d1; l1; c2; d2; l2; c3; d3; l3] w1 (S w1) ->
  FOtms_avoid [c1; d1; l1; c2; d2; l2; c3; d3; l3] w2 (S w2) ->
  FOPrH n (G ++ [FOM3F c1 d1 l1 c2 d2 l2 c3 d3 l3 (FOVar w1) (FOVar w2)]) C ->
  FOPrH n G C.
Proof.
  intros n G c1 d1 l1 c2 d2 l2 c3 d3 l3 x1 x2 w1 w2 C HG Hav
    Hx1 Hx1' Hx2 Hx2' Hw1 Hw1' Hw2 Hw2' D1 D2 D3 D4 D5 D6 G1 G2 G3 G4 C1 C2 C3 C4
    A1 A2 A3 A4 H0.
  apply (FOPrH_concat_elim n G c1 d1 l1 c2 d2 l2 (FOPlus c1 c2) x1 x2 C);
    try assumption; try lia; try avoid_tms.
  apply (FOPrH_concat_elim n _ (FOVar x1) (FOVar x2) (FOPlus l1 l2) c3 d3 l3
           (FOPlus (FOVar x1) c3) w1 w2 C);
    try assumption; try lia; try avoid_tms; try ctx_list; try free_ctx.
  lazymatch goal with
  | |- FOPrH _ ?Gc _ =>
      assert (K1 : FOPrH n Gc (FOCATF (FOPlus c1 c2) l1 c1 d1 l2 c2 d2 (FOVar x1) (FOVar x2)))
        by wk_in;
      assert (K2 : FOPrH n Gc (FOCATF (FOPlus (FOVar x1) c3) (FOPlus l1 l2) (FOVar x1)
                                 (FOVar x2) l3 c3 d3 (FOVar w1) (FOVar w2))) by wk_in
  end.
  unfold FOCATF in K1, K2.
  pose proof (FOPrH_and_l _ _ _ _ K1) as B1.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ K1)) as AG1.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ K1)) as AS1.
  pose proof (FOPrH_and_l _ _ _ _ K2) as B2.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ K2)) as AG2.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ K2)) as AS2.
  assert (Havx : FOtms_avoid [c1; d1; l1; c2; d2; l2; c3; d3; l3; FOVar x1; FOVar x2;
                              FOVar w1; FOVar w2] 420 500) by avoid_tms.
  destruct (FOPrH_bound3 _ _ c1 c2 c3 (FOVar x1) (FOVar w1) B1 B2 ltac:(avoid_tms))
    as [Bd1 [Bd2 Bd3]].
  refine (FOPrH_cut _ _ (FOM3F c1 d1 l1 c2 d2 l2 c3 d3 l3 (FOVar w1) (FOVar w2)) _ _ _).
  - unfold FOM3F.
    apply FOPrH_and_intro; [exact Bd1|]. apply FOPrH_and_intro; [exact Bd2|].
    apply FOPrH_and_intro; [exact Bd3|].
    apply FOPrH_and_intro.
    { apply (FOPrH_agr_trans _ _ l1 (FOPlus l1 l2) c1 d1 (FOVar x1) (FOVar x2));
        [exact AG1 | exact AG2 | | ctx_list | avoid_tms].
      unfold FOle. apply (FOPrH_ex_intro _ _ 498 l2); [cbn [FOsubst_ok]; reflexivity|].
      rewrite FOsubst_f_eq, !FOsubst_t_plus, FOsubst_t_var_eq'. subst_avoid_h Havx.
      apply FOPrH_refl. }
    apply FOPrH_and_intro; [|exact AS2].
    apply (FOPrH_agrs_agr _ _ l1 l2 (FOPlus l1 l2) c2 d2 (FOVar x1) (FOVar x2));
      [exact AS1 | exact AG2 | | ctx_list | avoid_tms].
    unfold FOle. apply (FOPrH_ex_intro _ _ 498 FOZero); [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_eq, !FOsubst_t_plus, FOsubst_t_var_eq'. subst_avoid_h Havx.
    apply FOPrH_Q_plus_zero.
  - refine (FOPrH_weaken n _ _ _ _ H0).
    intros X HX. apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
    + apply in_or_app. left. apply in_or_app. left. apply in_or_app. left. exact HX.
    + apply in_or_app. right. left. reflexivity.
Qed.

(** Substitution into any listed term that avoids the variable. *)

Ltac subst_avoid_h Hav ::=
  repeat match goal with
  | |- context [FOsubst_t ?w ?s ?t] =>
      rewrite (FOsubst_t_not_in t w s (Hav t ltac:(in_list) w ltac:(nat_fast) ltac:(nat_fast)))
  end.

Ltac subst_avoid_hin Hav H ::=
  repeat match type of H with
  | context [FOsubst_t ?w ?s ?t] =>
      rewrite (FOsubst_t_not_in t w s (Hav t ltac:(in_list) w ltac:(nat_fast) ltac:(nat_fast)))
        in H
  end.

(** ** Rows of a component table are rows of the merged table. *)

Lemma FOPrH_lt470_rename : forall n G z t a,
  FOPrH n G (FOlt470 t a) -> z <> 470 ->
  FOtms_avoid [t; a] z (S z) -> FOtms_avoid [t; a] 470 471 ->
  FOPrH n G (FOExists z (FOEq (FOPlus t (FOSucc (FOVar z))) a)).
Proof.
  intros n G z t a H Hz Hav1 Hav2.
  refine (FOPrH_mp _ _ _ _ _ H). apply FOPrH_exeq_rename; [lia | fr_tm | fr_tm | fr_tm | fr_tm].
Qed.

Lemma FOPrH_incl_agr : forall n G T T',
  FOPrH n G (FOAGR (tlen T) (tct T) (tdt T) (tct T') (tdt T')) ->
  FOPrH n G (FOAGR (tlen T) (tc1 T) (td1 T) (tc1 T') (td1 T')) ->
  FOPrH n G (FOAGR (tlen T) (tc2 T) (td2 T) (tc2 T') (td2 T')) ->
  FOPrH n G (FOAGR (tlen T) (tc3 T) (td3 T) (tc3 T') (td3 T')) ->
  FOPrH n G (FOAGR (tlen T) (tcr T) (tdr T) (tcr T') (tdr T')) ->
  FOPrH n G (FOle (tlen T) (tlen T')) ->
  FOctx_avoid G 420 500 -> FOtms_avoid (FOtab_terms T ++ FOtab_terms T') 420 500 ->
  FOPrH n G (FOINCL T T').
Proof.
  intros n G T T' A1 A2 A3 A4 A5 Hle HG Hav.
  unfold FOINCL.
  apply FOPrH_all_intro; [apply HG; lia|]. apply FOPrH_intro.
  assert (Lt : FOPrH n (G ++ [FOExists 461 (FOEq (FOPlus (FOVar 460) (FOSucc (FOVar 461)))
                                                 (tlen T))])
                 (FOlt470 (FOVar 460) (tlen T))).
  { unfold FOlt470. refine (FOPrH_mp _ _ _ _ _ (FOPrH_last _ _ _)).
    apply FOPrH_exeq_rename; [lia | fr_tm | fr_tm | fr_tm | fr_tm]. }
  assert (V : FOtm_avoid (FOVar 460) 461 500) by (apply FOtm_avoid_var; lia).
  apply (FOPrH_ex_intro _ _ 462 (FOVar 460)); [unfold FOROWMAP; ok_fast V|].
  unfold FOROWMAP. subst_goal Hav.
  apply FOPrH_and_intro.
  - apply FOPrH_lt470_rename; [| lia | avoid_tms | avoid_tms].
    apply (FOPrH_lt470_le _ _ _ (tlen T)); [exact Lt | wk Hle | avoid_tms].
  - repeat apply FOPrH_and_intro;
      (apply (FOPrH_agr_row _ _ (tlen T)); [wk A1 || wk A2 || wk A3 || wk A4 || wk A5
                                           | exact Lt | avoid_tms | avoid_tms]).
Qed.

Lemma FOPrH_incl_agrs : forall n G O T T',
  FOPrH n G (FOAGRS O (tlen T) (tct T) (tdt T) (tct T') (tdt T')) ->
  FOPrH n G (FOAGRS O (tlen T) (tc1 T) (td1 T) (tc1 T') (td1 T')) ->
  FOPrH n G (FOAGRS O (tlen T) (tc2 T) (td2 T) (tc2 T') (td2 T')) ->
  FOPrH n G (FOAGRS O (tlen T) (tc3 T) (td3 T) (tc3 T') (td3 T')) ->
  FOPrH n G (FOAGRS O (tlen T) (tcr T) (tdr T) (tcr T') (tdr T')) ->
  FOPrH n G (FOle (FOPlus O (tlen T)) (tlen T')) ->
  FOctx_avoid G 420 500 -> FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [O]) 420 500 ->
  FOPrH n G (FOINCL T T').
Proof.
  intros n G O T T' A1 A2 A3 A4 A5 Hle HG Hav.
  unfold FOINCL.
  apply FOPrH_all_intro; [apply HG; lia|]. apply FOPrH_intro.
  assert (Lt : FOPrH n (G ++ [FOExists 461 (FOEq (FOPlus (FOVar 460) (FOSucc (FOVar 461)))
                                                 (tlen T))])
                 (FOlt470 (FOVar 460) (tlen T))).
  { unfold FOlt470. refine (FOPrH_mp _ _ _ _ _ (FOPrH_last _ _ _)).
    apply FOPrH_exeq_rename; [lia | fr_tm | fr_tm | fr_tm | fr_tm]. }
  assert (V : FOtm_avoid (FOPlus O (FOVar 460)) 461 500) by avoid_tm.
  apply (FOPrH_ex_intro _ _ 462 (FOPlus O (FOVar 460))); [unfold FOROWMAP; ok_fast V|].
  unfold FOROWMAP. subst_goal Hav.
  apply FOPrH_and_intro.
  - apply FOPrH_lt470_rename; [| lia | avoid_tms | avoid_tms].
    apply (FOPrH_lt470_plus _ _ _ (tlen T)); [exact Lt | wk Hle | avoid_tms].
  - repeat apply FOPrH_and_intro;
      (apply (FOPrH_agrs_row _ _ O (tlen T)); [wk A1 || wk A2 || wk A3 || wk A4 || wk A5
                                              | exact Lt | avoid_tms | avoid_tms]).
Qed.

(** ** The merged table.

    [FOTABM3 T1 T2 TB T']: every column of [T'] is the concatenation of
    the columns of [T1], [T2] and [TB], in that order. *)

Definition FOTABM3 (T1 T2 TB T' : FOtab) : FOFormula :=
  FOAnd (FOM3F (tct T1) (tdt T1) (tlen T1) (tct T2) (tdt T2) (tlen T2)
               (tct TB) (tdt TB) (tlen TB) (tct T') (tdt T'))
  (FOAnd (FOM3F (tc1 T1) (td1 T1) (tlen T1) (tc1 T2) (td1 T2) (tlen T2)
                (tc1 TB) (td1 TB) (tlen TB) (tc1 T') (td1 T'))
  (FOAnd (FOM3F (tc2 T1) (td2 T1) (tlen T1) (tc2 T2) (td2 T2) (tlen T2)
                (tc2 TB) (td2 TB) (tlen TB) (tc2 T') (td2 T'))
  (FOAnd (FOM3F (tc3 T1) (td3 T1) (tlen T1) (tc3 T2) (td3 T2) (tlen T2)
                (tc3 TB) (td3 TB) (tlen TB) (tc3 T') (td3 T'))
         (FOM3F (tcr T1) (tdr T1) (tlen T1) (tcr T2) (tdr T2) (tlen T2)
                (tcr TB) (tdr TB) (tlen TB) (tcr T') (tdr T'))))).

Lemma FOPrH_m3_split : forall n G c1 d1 l1 c2 d2 l2 c3 d3 l3 c' d',
  FOPrH n G (FOM3F c1 d1 l1 c2 d2 l2 c3 d3 l3 c' d') ->
  FOPrH n G (FOle (FOSucc c1) (FOSucc c')) /\ FOPrH n G (FOle (FOSucc c2) (FOSucc c')) /\
  FOPrH n G (FOle (FOSucc c3) (FOSucc c')) /\ FOPrH n G (FOAGR l1 c1 d1 c' d') /\
  FOPrH n G (FOAGRS l1 l2 c2 d2 c' d') /\ FOPrH n G (FOAGRS (FOPlus l1 l2) l3 c3 d3 c' d').
Proof.
  intros n G c1 d1 l1 c2 d2 l2 c3 d3 l3 c' d' H. unfold FOM3F in H.
  pose proof (FOPrH_and_l _ _ _ _ H) as P1. apply FOPrH_and_r in H.
  pose proof (FOPrH_and_l _ _ _ _ H) as P2. apply FOPrH_and_r in H.
  pose proof (FOPrH_and_l _ _ _ _ H) as P3. apply FOPrH_and_r in H.
  pose proof (FOPrH_and_l _ _ _ _ H) as P4. apply FOPrH_and_r in H.
  pose proof (FOPrH_and_l _ _ _ _ H) as P5. apply FOPrH_and_r in H.
  repeat split; assumption.
Qed.

Lemma FOPrH_le_plus_r : forall n G a b,
  FOtms_avoid [a; b] 498 499 -> FOPrH n G (FOle a (FOPlus a b)).
Proof.
  intros n G a b Hav. unfold FOle.
  apply (FOPrH_ex_intro _ _ 498 b); [cbn [FOsubst_ok]; reflexivity|].
  rewrite FOsubst_f_eq, !FOsubst_t_plus, FOsubst_t_var_eq'. subst_avoid_h Hav.
  apply FOPrH_refl.
Qed.

Lemma FOPrH_tabm3_mono : forall n G T1 T2 TB T',
  FOPrH n G (FOTABM3 T1 T2 TB T') ->
  tlen T' = FOPlus (FOPlus (tlen T1) (tlen T2)) (tlen TB) ->
  FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T1 ++ FOtab_terms T2 ++ FOtab_terms TB ++ FOtab_terms T')
    420 500 ->
  FOTabMono n G T1 T' /\ FOTabMono n G T2 T' /\ FOTabMono n G TB T'.
Proof.
  intros n G T1 T2 TB T' H Hlen HG Hav.
  unfold FOTABM3 in H.
  pose proof (FOPrH_and_l _ _ _ _ H) as Mt.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ H)) as M1.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ H))) as M2.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ H)))) as M3.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ H)))) as Mr.
  clear H.
  apply FOPrH_m3_split in Mt. destruct Mt as (Bt1 & Bt2 & Bt3 & At & St & Ut).
  apply FOPrH_m3_split in M1. destruct M1 as (B11 & B12 & B13 & A1 & S1 & U1).
  apply FOPrH_m3_split in M2. destruct M2 as (B21 & B22 & B23 & A2 & S2 & U2).
  apply FOPrH_m3_split in M3. destruct M3 as (B31 & B32 & B33 & A3 & S3 & U3).
  apply FOPrH_m3_split in Mr. destruct Mr as (Br1 & Br2 & Br3 & Ar & Sr & Ur).
  split; [|split].
  - split; [|repeat split; assumption].
    unfold FOTabAgree. apply FOPrH_incl_agr; try assumption; [|avoid_tms].
    rewrite Hlen.
    unfold FOle. apply (FOPrH_ex_intro _ _ 498 (FOPlus (tlen T2) (tlen TB)));
      [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_eq, !FOsubst_t_plus, FOsubst_t_var_eq'. subst_avoid_h Hav.
    apply FOPrH_ring. fo_ring.
  - split; [|repeat split; assumption].
    unfold FOTabAgree. apply (FOPrH_incl_agrs _ _ (tlen T1)); try assumption.
    + rewrite Hlen. apply FOPrH_le_plus_r. avoid_tms.
    + avoid_tms.
  - split; [|repeat split; assumption].
    unfold FOTabAgree. apply (FOPrH_incl_agrs _ _ (FOPlus (tlen T1) (tlen T2))); try assumption.
    + rewrite Hlen. unfold FOle. apply (FOPrH_ex_intro _ _ 498 FOZero);
        [cbn [FOsubst_ok]; reflexivity|].
      rewrite FOsubst_f_eq, !FOsubst_t_plus, FOsubst_t_var_eq'. subst_avoid_h Hav.
      apply FOPrH_Q_plus_zero.
    + avoid_tms.
Qed.

Lemma FOSTEPDISPATCH_free : forall w B ct dt c1 d1 c2 d2 c3 d3 cr dr len j,
  FOfree_in w (FOSTEPDISPATCH B ct dt c1 d1 c2 d2 c3 d3 cr dr len j) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true \/ FOin_tm w j = true \/ w < 2.
Proof.
  intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len j H.
  unfold FOSTEPDISPATCH, FOSTEP0, FOSTEP1, FOSTEP2, FOSTEP3, FOSTEP4, FOSTEP5,
    FOSTEP_bin, FOSTEP_quant0, FOSTEP_substbin, FOSTEP_substquant, FOSTEP_subokbin,
    FOSTEP_subokquant in H.
  ffree_walk; ffin.
Qed.

Ltac rows_agr A0 A1 A2 A3 A4 Lt :=
  refine (FOPrH_agr_row _ _ _ _ _ _ _ _ A0 Lt _ _); [avoid_tms | avoid_tms].

(** ** Validity of the merged table. *)

Lemma FOPrH_tblvalid_merge : forall n G T1 T2 TB T' w1 w2,
  FOPrH n G (FOTABM3 T1 T2 TB T') ->
  tlen T' = FOPlus (FOPlus (tlen T1) (tlen T2)) (tlen TB) ->
  FOPrH n G (FOTBLVALID 18 (tct T1) (tdt T1) (tc1 T1) (td1 T1) (tc2 T1) (td2 T1) (tc3 T1)
               (td3 T1) (tcr T1) (tdr T1) (tlen T1)) ->
  FOPrH n G (FOTBLVALID 18 (tct T2) (tdt T2) (tc1 T2) (td1 T2) (tc2 T2) (td2 T2) (tc3 T2)
               (td3 T2) (tcr T2) (tdr T2) (tlen T2)) ->
  FOPrH n G (FOTBLVALID 18 (tct TB) (tdt TB) (tc1 TB) (td1 TB) (tc2 TB) (td2 TB) (tc3 TB)
               (td3 TB) (tcr TB) (tdr TB) (tlen TB)) ->
  260 <= w1 -> w1 < 400 -> 260 <= w2 -> w2 < 400 -> w1 <> w2 ->
  FOfree_ctx w1 G -> FOfree_ctx w2 G ->
  FOctx_avoid G 18 122 -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T1 ++ FOtab_terms T2 ++ FOtab_terms TB ++ FOtab_terms T') 18 122 ->
  FOtms_avoid (FOtab_terms T1 ++ FOtab_terms T2 ++ FOtab_terms TB ++ FOtab_terms T') 400 500 ->
  FOtms_avoid (FOtab_terms T1 ++ FOtab_terms T2 ++ FOtab_terms TB ++ FOtab_terms T') w1 (S w1) ->
  FOtms_avoid (FOtab_terms T1 ++ FOtab_terms T2 ++ FOtab_terms TB ++ FOtab_terms T') w2 (S w2) ->
  FOPrH n G (FOTBLVALID 18 (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T')).
Proof.
  intros n G T1 T2 TB T' w1 w2 HM Hlen HV1 HV2 HVB Hw1 Hw1' Hw2 Hw2' Hw12 HG1 HG2 HG HG2'
    Hav1 Hav2 Hav3 Hav4.
  assert (Hav : FOtms_avoid (FOtab_terms T1 ++ FOtab_terms T2 ++ FOtab_terms TB ++
                             FOtab_terms T') 420 500) by avoid_tms.
  destruct (FOPrH_tabm3_mono n G T1 T2 TB T' HM Hlen HG2' Hav) as (Hm1 & Hm2 & HmB).
  unfold FOTABM3 in HM.
  pose proof (FOPrH_and_l _ _ _ _ HM) as Mt.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ HM)) as M1.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ HM))) as M2.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ HM)))) as M3.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ HM)))) as Mr.
  clear HM.
  apply FOPrH_m3_split in Mt. destruct Mt as (_ & _ & _ & At & St & Ut).
  apply FOPrH_m3_split in M1. destruct M1 as (_ & _ & _ & A1 & S1 & U1).
  apply FOPrH_m3_split in M2. destruct M2 as (_ & _ & _ & A2 & S2 & U2).
  apply FOPrH_m3_split in M3. destruct M3 as (_ & _ & _ & A3 & S3 & U3).
  apply FOPrH_m3_split in Mr. destruct Mr as (_ & _ & _ & Ar & Sr & Ur).
  assert (FD : forall w, 18 <= w -> w < 122 \/ (260 <= w /\ w < 400) ->
            FOtms_avoid (FOtab_terms T') w (S w) -> w <> 18 ->
            FOfree_in w (FOSTEPDISPATCH 20 (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T')
                           (td2 T') (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T')
                           (FOVar 18)) = false).
  { intros w Hw1a Hw1b HavT Hw18. free_by FOSTEPDISPATCH_free. }
  unfold FOTBLVALID in *. rewrite Hlen.
  apply (FOPrH_ball_split_w n G 18 (FOPlus (tlen T1) (tlen T2)) (tlen TB) _ w2);
    [ | | apply FOsubst_ok_STEPDISPATCH; avoid_tm | lia | lia | lia | lia | lia | lia
      | apply HG; lia | apply HG; lia | exact HG2 | exact HG2'
      | rewrite <- Hlen; apply FD; [lia | lia | avoid_tms | lia]
      | rewrite <- Hlen; apply FD; [lia | lia | avoid_tms | lia]
      | avoid_tms | avoid_tms | avoid_tms ].
  - apply (FOPrH_ball_split_w n G 18 (tlen T1) (tlen T2) _ w1);
      [ | | apply FOsubst_ok_STEPDISPATCH; avoid_tm | lia | lia | lia | lia | lia | lia
        | apply HG; lia | apply HG; lia | exact HG1 | exact HG2'
        | rewrite <- Hlen; apply FD; [lia | lia | avoid_tms | lia]
        | rewrite <- Hlen; apply FD; [lia | lia | avoid_tms | lia]
        | avoid_tms | avoid_tms | avoid_tms ].
    + refine (FOPrH_mp _ _ _ _ _ HV1).
      apply FOPrH_ball_mono; [apply HG; lia | apply FOPrH_imp_refl|].
      apply FOPrH_intro.
      assert (Lt : FOPrH n (G ++ [FOltv 18 (tlen T1)]) (FOlt470 (FOVar 18) (tlen T1))).
      { refine (FOPrH_mp _ _ _ _ (FOPrH_ltv_470 _ _ 18 (tlen T1) _ _ _ _) (FOPrH_last _ _ _));
          [lia | lia | avoid_tm | avoid_tm]. }
      rewrite <- Hlen.
      apply (FOtr_DISPATCH n _ 20 T1 T' (FOVar 18) (FOVar 18));
        [ apply FOTabMono_weak; exact Hm1
        | refine (FOPrH_agr_row _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ At) Lt _ _);
            [avoid_tms | avoid_tms]
        | refine (FOPrH_agr_row _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ A1) Lt _ _);
            [avoid_tms | avoid_tms]
        | refine (FOPrH_agr_row _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ A2) Lt _ _);
            [avoid_tms | avoid_tms]
        | refine (FOPrH_agr_row _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ A3) Lt _ _);
            [avoid_tms | avoid_tms]
        | refine (FOPrH_agr_row _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ Ar) Lt _ _);
            [avoid_tms | avoid_tms]
        | lia | ctx_list | ctx_list | avoid_tms | avoid_tms ].
    + apply FOPrH_all_intro; [exact HG1|]. apply FOPrH_intro. rewrite <- Hlen.
      rewrite FOsubst_f_STEPDISPATCH by lia. rewrite FOsubst_t_var_eq'. subst_avoid_h Hav1.
      assert (Lt : FOPrH n (G ++ [FOlt470 (FOVar w1) (tlen T2)]) (FOlt470 (FOVar w1) (tlen T2)))
        by apply FOPrH_last.
      pose proof (FOPrH_ball_inst n _ 18 (tlen T2) (FOVar w1) _ (FOPrH_weak_app _ _ _ _ HV2) Lt
                    ltac:(lia) ltac:(apply FOsubst_ok_STEPDISPATCH; avoid_tm)
                    ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as D2.
      rewrite FOsubst_f_STEPDISPATCH, FOsubst_t_var_eq' in D2 by lia. subst_avoid_hin Hav1 D2.
      refine (FOPrH_mp _ _ _ _ _ D2).
      apply (FOtr_DISPATCH n _ 20 T2 T' (FOVar w1) (FOPlus (tlen T1) (FOVar w1)));
        [ apply FOTabMono_weak; exact Hm2
        | refine (FOPrH_agrs_row _ _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ St) Lt _ _);
            [avoid_tms | avoid_tms]
        | refine (FOPrH_agrs_row _ _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ S1) Lt _ _);
            [avoid_tms | avoid_tms]
        | refine (FOPrH_agrs_row _ _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ S2) Lt _ _);
            [avoid_tms | avoid_tms]
        | refine (FOPrH_agrs_row _ _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ S3) Lt _ _);
            [avoid_tms | avoid_tms]
        | refine (FOPrH_agrs_row _ _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ Sr) Lt _ _);
            [avoid_tms | avoid_tms]
        | lia | ctx_list | ctx_list | avoid_tms | avoid_tms ].
  - apply FOPrH_all_intro; [exact HG2|]. apply FOPrH_intro. rewrite <- Hlen.
    rewrite FOsubst_f_STEPDISPATCH by lia. rewrite FOsubst_t_var_eq'. subst_avoid_h Hav1.
    assert (Lt : FOPrH n (G ++ [FOlt470 (FOVar w2) (tlen TB)]) (FOlt470 (FOVar w2) (tlen TB)))
      by apply FOPrH_last.
    pose proof (FOPrH_ball_inst n _ 18 (tlen TB) (FOVar w2) _ (FOPrH_weak_app _ _ _ _ HVB) Lt
                  ltac:(lia) ltac:(apply FOsubst_ok_STEPDISPATCH; avoid_tm)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as D3.
    rewrite FOsubst_f_STEPDISPATCH, FOsubst_t_var_eq' in D3 by lia. subst_avoid_hin Hav1 D3.
    refine (FOPrH_mp _ _ _ _ _ D3).
    apply (FOtr_DISPATCH n _ 20 TB T' (FOVar w2)
             (FOPlus (FOPlus (tlen T1) (tlen T2)) (FOVar w2)));
      [ apply FOTabMono_weak; exact HmB
      | refine (FOPrH_agrs_row _ _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ Ut) Lt _ _);
          [avoid_tms | avoid_tms]
      | refine (FOPrH_agrs_row _ _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ U1) Lt _ _);
          [avoid_tms | avoid_tms]
      | refine (FOPrH_agrs_row _ _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ U2) Lt _ _);
          [avoid_tms | avoid_tms]
      | refine (FOPrH_agrs_row _ _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ U3) Lt _ _);
          [avoid_tms | avoid_tms]
      | refine (FOPrH_agrs_row _ _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ Ur) Lt _ _);
          [avoid_tms | avoid_tms]
      | lia | ctx_list | ctx_list | avoid_tms | avoid_tms ].
Qed.

(** ** Checks introduced at given witnesses. *)

Lemma FOPrH_JUSTCK_intro_t : forall n G B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds cj dj i vd y,
  2 <= B -> B + 232 <= 498 ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; cs; ds; cj; dj; i] B (B + 232) ->
  FOtms_avoid [vd] (B + 1) (B + 232) -> FOtms_avoid [y] (B + 3) (B + 232) ->
  FOtms_avoid [cs; cj; vd; y] 498 499 ->
  FOPrH n G (FOle (FOSucc vd) (FOSucc cs)) ->
  FOPrH n G (FObetaF (B + 4) cs ds i vd) ->
  FOPrH n G (FOle (FOSucc y) (FOSucc cj)) ->
  FOPrH n G (FObetaF (B + 8) cj dj i y) ->
  FOPrH n G (FOCHK B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd y) ->
  FOPrH n G (FOJUSTCK B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds cj dj i).
Proof.
  intros n G B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds cj dj i vd y
    HB HB2 Hav Hvd Hy Hav2 H1 H2 H3 H4 H5.
  rewrite FOJUSTCK_split.
  apply (FOPrH_bex_intro_t n G B (FOSucc cs) vd); try lia; try avoid_tm; [exact H1 | |].
  { apply FOsubst_ok_bex; [fr_tm | fr_tm|].
    apply FOsubst_ok_and; [apply FOsubst_ok_betaF; avoid_tm|].
    apply FOsubst_ok_and; [apply FOsubst_ok_betaF; avoid_tm|].
    apply FOsubst_ok_CHK. avoid_tm. }
  rewrite FOsubst_f_bex, !FOsubst_f_and, !FOsubst_f_betaF, FOsubst_f_CHK by lia.
  rewrite !FOsubst_t_var_eq', !FOsubst_t_var_ne by lia.
  rewrite ?FOsubst_t_succ. subst_avoid_h Hav.
  apply (FOPrH_bex_intro_t n G (B + 2) (FOSucc cj) y); try lia; try avoid_tm;
    [exact H3 | |].
  { apply FOsubst_ok_and; [apply FOsubst_ok_betaF; avoid_tm|].
    apply FOsubst_ok_and; [apply FOsubst_ok_betaF; avoid_tm|].
    apply FOsubst_ok_CHK. avoid_tm. }
  rewrite !FOsubst_f_and, !FOsubst_f_betaF, FOsubst_f_CHK by lia.
  rewrite FOsubst_t_var_eq'.
  rewrite ?FOsubst_t_succ. subst_avoid_h Hav. subst_avoid_h Hvd.
  apply FOPrH_and_intro; [exact H2|]. apply FOPrH_and_intro; [exact H4 | exact H5].
Qed.

Lemma FOPrH_CHK_intro_t : forall n G B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds i vd y tg p,
  B + 232 <= 498 ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; cs; ds; i; vd; y]
    (B + 12) (B + 232) ->
  FOtms_avoid [tg] (B + 13) (B + 232) -> FOtms_avoid [p] (B + 15) (B + 232) ->
  FOtms_avoid [y; tg; p] 498 499 ->
  FOPrH n G (FOle (FOSucc tg) (FOSucc y)) -> FOPrH n G (FOle (FOSucc p) (FOSucc y)) ->
  FOPrH n G (FOcpairF tg p y) ->
  FOPrH n G (FOJDISJ B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd tg p) ->
  FOPrH n G (FOCHK B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd y).
Proof.
  intros n G B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd y tg p
    HB Hav Htg Hp Hav2 H1 H2 H3 H4.
  unfold FOCHK.
  apply (FOPrH_bex_intro_t n G (B + 12) (FOSucc y) tg); try lia; try avoid_tm;
    [exact H1 | |].
  { apply FOsubst_ok_bex; [fr_tm | fr_tm|].
    apply FOsubst_ok_and; [apply FOsubst_ok_cpairF|].
    apply FOsubst_ok_JDISJ. avoid_tm. }
  rewrite FOsubst_f_bex, FOsubst_f_and, FOsubst_f_cpairF, FOsubst_f_JDISJ by lia.
  rewrite !FOsubst_t_var_eq', !FOsubst_t_var_ne by lia.
  rewrite ?FOsubst_t_succ. subst_avoid_h Hav.
  apply (FOPrH_bex_intro_t n G (B + 14) (FOSucc y) p); try lia; try avoid_tm;
    [exact H2 | |].
  { apply FOsubst_ok_and; [apply FOsubst_ok_cpairF|].
    apply FOsubst_ok_JDISJ. avoid_tm. }
  rewrite FOsubst_f_and, FOsubst_f_cpairF, FOsubst_f_JDISJ by lia.
  rewrite FOsubst_t_var_eq'.
  rewrite ?FOsubst_t_succ. subst_avoid_h Hav. subst_avoid_h Htg.
  apply FOPrH_and_intro; assumption.
Qed.

Lemma FOPrH_JMPREST_intro : forall n G B cs ds vd a b x y,
  B + 24 <= 498 ->
  FOtms_avoid [cs; ds; vd; a; b] (B + 4) (B + 24) ->
  FOtms_avoid [x] (B + 5) (B + 24) -> FOtms_avoid [y] (B + 7) (B + 24) ->
  FOtms_avoid [cs; x; y] 498 499 ->
  FOPrH n G (FOle (FOSucc x) (FOSucc cs)) -> FOPrH n G (FOle (FOSucc y) (FOSucc cs)) ->
  FOPrH n G (FObetaF (B + 8) cs ds a x) -> FOPrH n G (FObetaF (B + 12) cs ds b y) ->
  FOPrH n G (FOPATF (B + 16) [y; vd] cpatImpl01 x) ->
  FOPrH n G (FOJMPREST B cs ds vd a b).
Proof.
  intros n G B cs ds vd a b x y HB Hav Hx Hy Hav2 H1 H2 H3 H4 H5.
  unfold FOJMPREST.
  apply (FOPrH_bex_intro_t n G (B + 4) (FOSucc cs) x); try lia; try avoid_tm;
    [exact H1 | |].
  { apply FOsubst_ok_bex; [fr_tm | fr_tm|].
    apply FOsubst_ok_and; [apply FOsubst_ok_betaF; avoid_tm|].
    apply FOsubst_ok_and; [apply FOsubst_ok_betaF; avoid_tm|].
    apply FOsubst_ok_PATF. change (cpat_span cpatImpl01) with 8. avoid_tm. }
  rewrite FOsubst_f_bex, !FOsubst_f_and, !FOsubst_f_betaF, FOsubst_f_PATF by lia.
  rewrite !FOsubst_map_cons, FOsubst_map_nil.
  rewrite !FOsubst_t_var_eq', !FOsubst_t_var_ne by lia.
  rewrite ?FOsubst_t_succ. subst_avoid_h Hav.
  apply (FOPrH_bex_intro_t n G (B + 6) (FOSucc cs) y); try lia; try avoid_tm;
    [exact H2 | |].
  { apply FOsubst_ok_and; [apply FOsubst_ok_betaF; avoid_tm|].
    apply FOsubst_ok_and; [apply FOsubst_ok_betaF; avoid_tm|].
    apply FOsubst_ok_PATF. change (cpat_span cpatImpl01) with 8. avoid_tm. }
  rewrite !FOsubst_f_and, !FOsubst_f_betaF, FOsubst_f_PATF by lia.
  rewrite !FOsubst_map_cons, FOsubst_map_nil.
  rewrite FOsubst_t_var_eq'.
  rewrite ?FOsubst_t_succ. subst_avoid_h Hav. subst_avoid_h Hx.
  apply FOPrH_and_intro; [exact H3|]. apply FOPrH_and_intro; [exact H4 | exact H5].
Qed.

Lemma FOPrH_GUARDC_intro_t : forall n G B T cs ds i vd r,
  B + 30 <= 498 ->
  FOtms_avoid (FOtab_terms T ++ [cs; ds; i]) B (B + 30) ->
  FOtms_avoid [vd] (B + 1) (B + 30) -> FOtms_avoid [r] (B + 7) (B + 30) ->
  FOtms_avoid [cs; tcr T; vd; r] 498 499 ->
  FOPrH n G (FOle (FOSucc vd) (FOSucc cs)) ->
  FOPrH n G (FObetaF (B + 2) cs ds i vd) ->
  FOPrH n G (FOle (FOSucc r) (FOSucc (tcr T))) ->
  FOPrH n G (FOlookup (B + 8) (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) (FOnumeral 3) (FOSucc vd) FOZero vd r) ->
  FOPrH n G (FOGUARDC B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) cs ds i).
Proof.
  intros n G B T cs ds i vd r HB Hav Hvd Hr Hav2 H1 H2 H3 H4.
  unfold FOGUARDC.
  apply (FOPrH_bex_intro_t n G B (FOSucc cs) vd); try lia; try avoid_tm;
    [exact H1 | |].
  { apply FOsubst_ok_and; [apply FOsubst_ok_betaF; avoid_tm|].
    apply FOsubst_ok_bex; [fr_tm | fr_tm|].
    apply FOsubst_ok_lookup. avoid_tm. }
  rewrite FOsubst_f_and, FOsubst_f_betaF, FOsubst_f_bex, FOsubst_f_lookup by lia.
  rewrite !FOsubst_t_succ, !FOsubst_t_var_eq', !FOsubst_t_var_ne, FOsubst_t_numeral,
    FOsubst_t_zero by lia.
  rewrite ?FOsubst_t_succ. subst_avoid_h Hav.
  apply FOPrH_and_intro; [exact H2|].
  apply (FOPrH_bex_intro_t n G (B + 6) (FOSucc (tcr T)) r); try lia; try avoid_tm;
    [exact H3 | |].
  { apply FOsubst_ok_lookup. avoid_tm. }
  rewrite FOsubst_f_lookup by lia.
  rewrite !FOsubst_t_succ, FOsubst_t_var_eq', FOsubst_t_numeral, FOsubst_t_zero.
  rewrite ?FOsubst_t_succ. subst_avoid_h Hav. subst_avoid_h Hvd.
  exact H4.
Qed.

Lemma FOPrH_le_trans : forall n G a b c,
  FOPrH n G (FOle a b) -> FOPrH n G (FOle b c) ->
  FOtms_avoid [a; b; c] 498 500 ->
  FOPrH n G (FOle a c).
Proof.
  intros n G a b c H1 H2 Hav.
  refine (FOPrH_ctxfree2 n G _ _ _ _ H1 H2). unfold FOle.
  refine (FOPrH_ex_elim n _ 498 (FOEq (FOPlus a (FOVar 498)) b) _ _ (FOfree_in_ex_self _ _)
            _ _); [free_ctx | wk_in |].
  refine (FOPrH_exe n _ 498 499 (FOEq (FOPlus b (FOVar 498)) c) _ _ _ _ _ _ _);
    [wk_in | free_ctx | free_fm | free_fm | cbn [FOsubst_ok]; reflexivity |].
  rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_var_eq'. subst_avoid_h Hav.
  apply (FOPrH_ex_intro _ _ 498 (FOPlus (FOVar 498) (FOVar 499)));
    [cbn [FOsubst_ok]; reflexivity|].
  rewrite FOsubst_f_eq, !FOsubst_t_plus, FOsubst_t_var_eq'. subst_avoid_h Hav.
  fo_lin [(.S .0, c, b .+ #499); (.S .0, b, a .+ #498)].
Qed.

(** ** The last position of the merged derivation: modus ponens from the
    last entries of the two derivations. *)

Lemma FOPrH_mp_check : forall n G cores T' cs' ds' cj' dj' L1 L2 m1 m2 a b c q jc,
  FOPrH n G (FObetaF 488 cs' ds' (FOPlus L1 L2) c) ->
  FOPrH n G (FObetaF 480 cs' ds' m1 a) ->
  FOPrH n G (FObetaF 480 cs' ds' (FOPlus L1 m2) b) ->
  FOPrH n G (FOPATF 52 [b; c] cpatImpl01 a) ->
  FOPrH n G (FOcpairF m1 (FOPlus L1 m2) q) ->
  FOPrH n G (FOcpairF (FOnumeral 4) q jc) ->
  FOPrH n G (FObetaF 488 cj' dj' (FOPlus L1 L2) jc) ->
  FOPrH n G (FOEq L1 (FOSucc m1)) -> FOPrH n G (FOEq L2 (FOSucc m2)) ->
  FOtms_avoid (FOtab_terms T' ++ [cs'; ds'; cj'; dj'; L1; L2; m1; m2; a; b; c; q; jc])
    20 260 ->
  FOtms_avoid (FOtab_terms T' ++ [cs'; ds'; cj'; dj'; L1; L2; m1; m2; a; b; c; q; jc])
    400 500 ->
  FOPrH n G (FOJUSTCK 20 cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T')
               (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' cj' dj' (FOPlus L1 L2)).
Proof.
  intros n G cores T' cs' ds' cj' dj' L1 L2 m1 m2 a b c q jc Hs Ha Hb Hp Hq Hj Hjc
    E1 E2 Hav1 Hav2.
  assert (Lc : FOPrH n G (FOle c cs'))
    by (apply (FOPrH_beta_le_cf n G 488 cs' ds' (FOPlus L1 L2) c); [exact Hs | lia | lia
                                                                   | avoid_tms | avoid_tms]).
  assert (Ljc : FOPrH n G (FOle jc cj'))
    by (apply (FOPrH_beta_le_cf n G 488 cj' dj' (FOPlus L1 L2) jc); [exact Hjc | lia | lia
                                                                     | avoid_tms | avoid_tms]).
  assert (La : FOPrH n G (FOle a cs'))
    by (apply (FOPrH_beta_le_cf n G 480 cs' ds' m1 a); [exact Ha | lia | lia
                                                       | avoid_tms | avoid_tms]).
  assert (Lb : FOPrH n G (FOle b cs'))
    by (apply (FOPrH_beta_le_cf n G 480 cs' ds' (FOPlus L1 m2) b); [exact Hb | lia | lia
                                                                   | avoid_tms | avoid_tms]).
  assert (Hc4 : FOtms_avoid [FOnumeral 4; q; jc] 420 500) by avoid_tms.
  destruct (FOPrH_cpair_le_cf n G _ _ _ Hc4 Hj) as [L4 Lq].
  apply (FOPrH_JUSTCK_intro_t n G 20 cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T')
           (td2 T') (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' cj' dj'
           (FOPlus L1 L2) c jc); try lia; try avoid_tms.
  - apply FOPrH_le_succ_cf; [avoid_tms | exact Lc].
  - apply (FOPrH_rebase_cf n G 488 (20 + 4)); [lia | avoid_tms | avoid_tms | exact Hs].
  - apply FOPrH_le_succ_cf; [avoid_tms | exact Ljc].
  - apply (FOPrH_rebase_cf n G 488 (20 + 8)); [lia | avoid_tms | avoid_tms | exact Hjc].
  - apply (FOPrH_CHK_intro_t n G 20 cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T')
             (td2 T') (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' (FOPlus L1 L2)
             c jc (FOnumeral 4) q); try lia; try avoid_tms.
    + apply FOPrH_le_succ_cf; [avoid_tms | exact L4].
    + apply FOPrH_le_succ_cf; [avoid_tms | exact Lq].
    + exact Hj.
    + unfold FOJDISJ. do 4 apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
      apply FOPrH_and_intro; [apply FOPrH_refl|].
      apply (FOPrH_JMP_intro n G (20 + 16) cs' ds' c q (FOPlus L1 L2) m1 (FOPlus L1 m2));
        try lia; try avoid_tms; [| | exact Hq |].
      * unfold FOle. apply (FOPrH_ex_intro _ _ 498 L2); [cbn [FOsubst_ok]; reflexivity|].
        rewrite FOsubst_f_eq.
        repeat (first [rewrite FOsubst_t_plus | rewrite FOsubst_t_succ
                      | rewrite FOsubst_t_var_eq']).
        subst_avoid_h Hav2. fo_lin [(.S .0, L1, .S m1)]. exact E1.
      * unfold FOle. apply (FOPrH_ex_intro _ _ 498 FOZero); [cbn [FOsubst_ok]; reflexivity|].
        rewrite FOsubst_f_eq.
        repeat (first [rewrite FOsubst_t_plus | rewrite FOsubst_t_succ
                      | rewrite FOsubst_t_var_eq']).
        subst_avoid_h Hav2. fo_lin [(.S .0, L2, .S m2)]. exact E2.
      * apply (FOPrH_JMPREST_intro n G (20 + 16) cs' ds' c m1 (FOPlus L1 m2) a b);
          try lia; try avoid_tms.
        -- apply FOPrH_le_succ_cf; [avoid_tms | exact La].
        -- apply FOPrH_le_succ_cf; [avoid_tms | exact Lb].
        -- apply (FOPrH_rebase_cf n G 480 (20 + 16 + 8)); [lia | avoid_tms | avoid_tms | exact Ha].
        -- apply (FOPrH_rebase_cf n G 480 (20 + 16 + 12)); [lia | avoid_tms | avoid_tms | exact Hb].
        -- exact Hp.
Qed.

(** The guard at the last position: the guard row of [B] in the table
    [TB], a part of the merged table. *)

Lemma FOPrH_guard_last : forall n G TB T' cs' ds' L1 L2 c r,
  FOTabMono n G TB T' ->
  FOPrH n G (FObetaF 488 cs' ds' (FOPlus L1 L2) c) ->
  FOPrH n G (FOle (FOSucc r) (FOSucc (tcr TB))) ->
  FOPrH n G (FOlookup 28 (tct TB) (tdt TB) (tc1 TB) (td1 TB) (tc2 TB) (td2 TB) (tc3 TB)
               (td3 TB) (tcr TB) (tdr TB) (tlen TB) (FOnumeral 3) (FOSucc c) FOZero c r) ->
  FOctx_avoid G 28 50 -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms TB ++ FOtab_terms T' ++ [cs'; ds'; L1; L2; c; r]) 20 260 ->
  FOtms_avoid (FOtab_terms TB ++ FOtab_terms T' ++ [cs'; ds'; L1; L2; c; r]) 400 500 ->
  FOPrH n G (FOGUARDC 20 (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' (FOPlus L1 L2)).
Proof.
  intros n G TB T' cs' ds' L1 L2 c r Hm Hs Hr Hl HG1 HG2 Hav1 Hav2.
  pose proof Hm as (HmA & Hct & Hc1 & Hc2 & Hc3 & Hcr).
  apply (FOPrH_GUARDC_intro_t n G 20 T' cs' ds' (FOPlus L1 L2) c r); try lia; try avoid_tms.
  - apply FOPrH_le_succ_cf; [avoid_tms|].
    apply (FOPrH_beta_le_cf n G 488 cs' ds' (FOPlus L1 L2) c); [exact Hs | lia | lia
                                                               | avoid_tms | avoid_tms].
  - apply (FOPrH_rebase_cf n G 488 (20 + 2)); [lia | avoid_tms | avoid_tms | exact Hs].
  - apply (FOPrH_le_trans _ _ _ (FOSucc (tcr TB))); [exact Hr | exact Hcr | avoid_tms].
  - refine (FOPrH_mp _ _ _ _ _ Hl).
    apply (FOPrH_lookup_tr' n G 28 TB T'); [exact Hm | lia | exact HG1 | exact HG2
                                            | avoid_tms | avoid_tms].
Qed.

(** ** Strict bounds weakened; a position below one is zero. *)

Lemma FOPrH_le_of_lt470 : forall n G t L,
  FOPrH n G (FOlt470 t L) -> FOtms_avoid [t; L] 470 499 -> FOPrH n G (FOle t L).
Proof.
  intros n G t L H Hav.
  refine (FOPrH_ctxfree n G _ _ _ H). unfold FOlt470, FOle.
  refine (FOPrH_ex_elim n _ 470 (FOEq (FOPlus t (FOSucc (FOVar 470))) L) _ _ _ _ _);
    [free_ctx | free_fm | wk_in |].
  apply (FOPrH_ex_intro _ _ 498 (FOSucc (FOVar 470))); [cbn [FOsubst_ok]; reflexivity|].
  rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_var_eq'. subst_avoid_h Hav.
  fo_lin [(.S .0, L, t .+ .S #470)].
Qed.

Lemma FOPrH_lt1_zero : forall n G t,
  FOPrH n G (FOlt470 t (FOSucc FOZero)) -> FOtms_avoid [t] 470 471 ->
  FOPrH n G (FOEq t FOZero).
Proof.
  intros n G t H Hav.
  refine (FOPrH_ctxfree n G _ _ _ H). unfold FOlt470.
  refine (FOPrH_ex_elim n _ 470 (FOEq (FOPlus t (FOSucc (FOVar 470))) (FOSucc FOZero)) _ _ _
            _ _); [free_ctx | free_fm | wk_in |].
  apply (FOPrH_add_zero_l _ _ _ (FOVar 470)).
  apply FOPrH_Q_succ_inj.
  fo_lin [(.S .0, .S .0, t .+ .S #470)].
Qed.

(** Shifted justification codes at every position of the second
    derivation, indexed by the variable [W]. *)

Definition FOSHMAP (L Lb cj dj cj' dj' : FOTerm) (W : nat) : FOFormula :=
  FOForall W (FOImplF (FOlt470 (FOVar W) Lb)
    (FOSHROW L cj dj cj' dj' (FOVar W) (FOPlus L (FOVar W)))).

(** ** The justification checks of the merged derivation. *)

Lemma FOPrH_merged_justck : forall n G cores T1 T2 T' cs1 ds1 cj1 dj1 cs2 ds2 cj2 dj2
    cs' ds' cj' dj' L1 L2 m1 m2 a b c q jc wD wL,
  FOPrH n G (FOBallC 18 L1 (FOJUSTCK 20 cores (tct T1) (tdt T1) (tc1 T1) (td1 T1) (tc2 T1)
               (td2 T1) (tc3 T1) (td3 T1) (tcr T1) (tdr T1) (tlen T1) cs1 ds1 cj1 dj1
               (FOVar 18))) ->
  FOPrH n G (FOBallC 18 L2 (FOJUSTCK 20 cores (tct T2) (tdt T2) (tc1 T2) (td1 T2) (tc2 T2)
               (td2 T2) (tc3 T2) (td3 T2) (tcr T2) (tdr T2) (tlen T2) cs2 ds2 cj2 dj2
               (FOVar 18))) ->
  FOTabMono n G T1 T' -> FOTabMono n G T2 T' ->
  FOPrH n G (FOAGR L1 cs1 ds1 cs' ds') -> FOPrH n G (FOAGRS L1 L2 cs2 ds2 cs' ds') ->
  FOPrH n G (FOle (FOSucc cs1) (FOSucc cs')) -> FOPrH n G (FOle (FOSucc cs2) (FOSucc cs')) ->
  FOPrH n G (FOAGR L1 cj1 dj1 cj' dj') -> FOPrH n G (FOSHMAP L1 L2 cj2 dj2 cj' dj' wD) ->
  FOPrH n G (FOle (FOSucc cj1) (FOSucc cj')) ->
  FOPrH n G (FObetaF 488 cs' ds' (FOPlus L1 L2) c) ->
  FOPrH n G (FObetaF 480 cs' ds' m1 a) ->
  FOPrH n G (FObetaF 480 cs' ds' (FOPlus L1 m2) b) ->
  FOPrH n G (FOPATF 52 [b; c] cpatImpl01 a) ->
  FOPrH n G (FOcpairF m1 (FOPlus L1 m2) q) ->
  FOPrH n G (FOcpairF (FOnumeral 4) q jc) ->
  FOPrH n G (FObetaF 488 cj' dj' (FOPlus L1 L2) jc) ->
  FOPrH n G (FOEq L1 (FOSucc m1)) -> FOPrH n G (FOEq L2 (FOSucc m2)) ->
  260 <= wD -> wD < 400 -> 260 <= wL -> wL < 400 -> wD <> wL ->
  FOfree_ctx wD G -> FOfree_ctx wL G ->
  FOctx_avoid G 18 260 -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T1 ++ FOtab_terms T2 ++ FOtab_terms T' ++
     [cs1; ds1; cj1; dj1; cs2; ds2; cj2; dj2; cs'; ds'; cj'; dj'; L1; L2; m1; m2;
      a; b; c; q; jc]) 18 260 ->
  FOtms_avoid (FOtab_terms T1 ++ FOtab_terms T2 ++ FOtab_terms T' ++
     [cs1; ds1; cj1; dj1; cs2; ds2; cj2; dj2; cs'; ds'; cj'; dj'; L1; L2; m1; m2;
      a; b; c; q; jc]) 400 500 ->
  FOtms_avoid (FOtab_terms T1 ++ FOtab_terms T2 ++ FOtab_terms T' ++
     [cs1; ds1; cj1; dj1; cs2; ds2; cj2; dj2; cs'; ds'; cj'; dj'; L1; L2; m1; m2;
      a; b; c; q; jc]) wD (S wD) ->
  FOtms_avoid (FOtab_terms T1 ++ FOtab_terms T2 ++ FOtab_terms T' ++
     [cs1; ds1; cj1; dj1; cs2; ds2; cj2; dj2; cs'; ds'; cj'; dj'; L1; L2; m1; m2;
      a; b; c; q; jc]) wL (S wL) ->
  FOPrH n G (FOBallC 18 (FOPlus (FOPlus L1 L2) (FOSucc FOZero))
               (FOJUSTCK 20 cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T')
                  (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' cj' dj' (FOVar 18))).
Proof.
  intros n G cores T1 T2 T' cs1 ds1 cj1 dj1 cs2 ds2 cj2 dj2 cs' ds' cj' dj' L1 L2 m1 m2
    a b c q jc wD wL J1 J2 Hm1 Hm2 F1 F2 B1 B2 K1 K2 B3 Hs Ha Hb Hp Hq Hj Hjc E1 E2
    HwD HwD' HwL HwL' HwDL HGD HGL HG HG2 Hav1 Hav2 Hav3 Hav4.
  assert (FJ : forall w, (19 <= w /\ w < 260) \/ w = wD \/ w = wL ->
            FOfree_in w (FOJUSTCK 20 cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T')
                           (td2 T') (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds'
                           cj' dj' (FOVar 18)) = false).
  { intros w Hw. destruct Hw as [Hw | [ -> | -> ] ]; free_by FOJUSTCK_free. }
  apply (FOPrH_ball_split_w n G 18 (FOPlus L1 L2) (FOSucc FOZero) _ wL);
    [ | | apply FOsubst_ok_JUSTCK; avoid_tm | lia | lia | lia | lia | lia | lia
      | apply HG; lia | apply HG; lia | exact HGL | exact HG2
      | apply FJ; lia | apply FJ; lia | avoid_tms | avoid_tms | avoid_tms ].
  - apply (FOPrH_ball_split_w n G 18 L1 L2 _ wD);
      [ | | apply FOsubst_ok_JUSTCK; avoid_tm | lia | lia | lia | lia | lia | lia
        | apply HG; lia | apply HG; lia | exact HGD | exact HG2
        | apply FJ; lia | apply FJ; lia | avoid_tms | avoid_tms | avoid_tms ].
    + refine (FOPrH_mp _ _ _ _ _ J1).
      apply FOPrH_ball_mono; [apply HG; lia | apply FOPrH_imp_refl|].
      apply FOPrH_intro.
      assert (Lt : FOPrH n (G ++ [FOltv 18 L1]) (FOlt470 (FOVar 18) L1)).
      { refine (FOPrH_mp _ _ _ _ (FOPrH_ltv_470 _ _ 18 L1 _ _ _ _) (FOPrH_last _ _ _));
          [lia | lia | avoid_tm | avoid_tm]. }
      apply (FOtr_JUSTCK n _ 20 cores T1 T' cs1 ds1 cj1 dj1 cs' ds' cj' dj' (FOVar 18) L1);
        [ apply FOTabMono_weak; exact Hm1
        | refine (FOPrH_agr_row _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ F1) Lt _ _);
            [avoid_tms | avoid_tms]
        | refine (FOPrH_agr_row _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ K1) Lt _ _);
            [avoid_tms | avoid_tms]
        | wk B1 | wk B3 | wk F1
        | apply FOPrH_le_of_lt470; [exact Lt | avoid_tms]
        | lia | ctx_list | ctx_list | avoid_tms | avoid_tms ].
    + apply FOPrH_all_intro; [exact HGD|]. apply FOPrH_intro.
      rewrite FOsubst_f_JUSTCK by lia.
      rewrite FOsubst_t_var_eq'. subst_avoid_h Hav1.
      assert (Lt : FOPrH n (G ++ [FOlt470 (FOVar wD) L2]) (FOlt470 (FOVar wD) L2))
        by apply FOPrH_last.
      pose proof (FOPrH_ball_inst n _ 18 L2 (FOVar wD) _ (FOPrH_weak_app _ _ _ _ J2) Lt
                    ltac:(lia) ltac:(apply FOsubst_ok_JUSTCK; avoid_tm)
                    ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as D2.
      rewrite FOsubst_f_JUSTCK, FOsubst_t_var_eq' in D2 by lia. subst_avoid_hin Hav1 D2.
      refine (FOPrH_mp _ _ _ _ _ D2).
      assert (SH : FOPrH n (G ++ [FOlt470 (FOVar wD) L2])
                     (FOSHROW L1 cj2 dj2 cj' dj' (FOVar wD) (FOPlus L1 (FOVar wD)))).
      { unfold FOSHMAP in K2.
        exact (FOPrH_mp _ _ _ _ (FOPrH_all_same _ _ _ _ (FOPrH_weak_app _ _ _ _ K2)) Lt). }
      apply (FOtr_JUSTCK_sh n _ 20 cores T2 T' cs2 ds2 cj2 dj2 cs' ds' cj' dj' (FOVar wD)
               L1 L2);
        [ apply FOTabMono_weak; exact Hm2
        | refine (FOPrH_agrs_row _ _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ F2) Lt _ _);
            [avoid_tms | avoid_tms]
        | exact SH | wk B2 | wk F2
        | apply FOPrH_le_of_lt470; [exact Lt | avoid_tms]
        | lia | lia | ctx_list | ctx_list | avoid_tms | avoid_tms ].
  - apply FOPrH_all_intro; [exact HGL|]. apply FOPrH_intro.
    assert (Z : FOPrH n (G ++ [FOlt470 (FOVar wL) (FOSucc FOZero)]) (FOEq (FOVar wL) FOZero))
      by (apply FOPrH_lt1_zero; [apply FOPrH_last | avoid_tms]).
    apply (FOPrH_leibniz _ _ 18 (FOPlus L1 L2) (FOPlus (FOPlus L1 L2) (FOVar wL)));
      [ apply FOsubst_ok_JUSTCK; avoid_tm | apply FOsubst_ok_JUSTCK; avoid_tm
      | fo_lin [(.S .0, #wL, .0)]; exact Z |].
    rewrite FOsubst_f_JUSTCK by lia.
    rewrite FOsubst_t_var_eq'. subst_avoid_h Hav1.
    apply (FOPrH_mp_check n _ cores T' cs' ds' cj' dj' L1 L2 m1 m2 a b c q jc);
      try (wk Hs || wk Ha || wk Hb || wk Hp || wk Hq || wk Hj || wk Hjc || wk E1 || wk E2);
      avoid_tms.
Qed.

(** ** The entry-code guards of the merged derivation. *)

Lemma FOPrH_merged_guard : forall n G T1 T2 TB T' cs1 ds1 cs2 ds2 cs' ds' L1 L2 c r wD wL,
  FOPrH n G (FOBallC 18 L1 (FOGUARDC 20 (tct T1) (tdt T1) (tc1 T1) (td1 T1) (tc2 T1)
               (td2 T1) (tc3 T1) (td3 T1) (tcr T1) (tdr T1) (tlen T1) cs1 ds1 (FOVar 18))) ->
  FOPrH n G (FOBallC 18 L2 (FOGUARDC 20 (tct T2) (tdt T2) (tc1 T2) (td1 T2) (tc2 T2)
               (td2 T2) (tc3 T2) (td3 T2) (tcr T2) (tdr T2) (tlen T2) cs2 ds2 (FOVar 18))) ->
  FOTabMono n G T1 T' -> FOTabMono n G T2 T' -> FOTabMono n G TB T' ->
  FOPrH n G (FOAGR L1 cs1 ds1 cs' ds') -> FOPrH n G (FOAGRS L1 L2 cs2 ds2 cs' ds') ->
  FOPrH n G (FOle (FOSucc cs1) (FOSucc cs')) -> FOPrH n G (FOle (FOSucc cs2) (FOSucc cs')) ->
  FOPrH n G (FObetaF 488 cs' ds' (FOPlus L1 L2) c) ->
  FOPrH n G (FOle (FOSucc r) (FOSucc (tcr TB))) ->
  FOPrH n G (FOlookup 28 (tct TB) (tdt TB) (tc1 TB) (td1 TB) (tc2 TB) (td2 TB) (tc3 TB)
               (td3 TB) (tcr TB) (tdr TB) (tlen TB) (FOnumeral 3) (FOSucc c) FOZero c r) ->
  260 <= wD -> wD < 400 -> 260 <= wL -> wL < 400 -> wD <> wL ->
  FOfree_ctx wD G -> FOfree_ctx wL G ->
  FOctx_avoid G 18 260 -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T1 ++ FOtab_terms T2 ++ FOtab_terms TB ++ FOtab_terms T' ++
     [cs1; ds1; cs2; ds2; cs'; ds'; L1; L2; c; r]) 18 260 ->
  FOtms_avoid (FOtab_terms T1 ++ FOtab_terms T2 ++ FOtab_terms TB ++ FOtab_terms T' ++
     [cs1; ds1; cs2; ds2; cs'; ds'; L1; L2; c; r]) 400 500 ->
  FOtms_avoid (FOtab_terms T1 ++ FOtab_terms T2 ++ FOtab_terms TB ++ FOtab_terms T' ++
     [cs1; ds1; cs2; ds2; cs'; ds'; L1; L2; c; r]) wD (S wD) ->
  FOtms_avoid (FOtab_terms T1 ++ FOtab_terms T2 ++ FOtab_terms TB ++ FOtab_terms T' ++
     [cs1; ds1; cs2; ds2; cs'; ds'; L1; L2; c; r]) wL (S wL) ->
  FOPrH n G (FOBallC 18 (FOPlus (FOPlus L1 L2) (FOSucc FOZero))
               (FOGUARDC 20 (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
                  (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' (FOVar 18))).
Proof.
  intros n G T1 T2 TB T' cs1 ds1 cs2 ds2 cs' ds' L1 L2 c r wD wL GD1 GD2 Hm1 Hm2 HmB
    F1 F2 B1 B2 Hs Hr Hl HwD HwD' HwL HwL' HwDL HGD HGL HG HG2 Hav1 Hav2 Hav3 Hav4.
  assert (FJ : forall w, (19 <= w /\ w < 260) \/ w = wD \/ w = wL ->
            FOfree_in w (FOGUARDC 20 (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T')
                           (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds'
                           (FOVar 18)) = false).
  { intros w Hw. destruct Hw as [Hw | [ -> | -> ] ]; free_by FOGUARDC_free. }
  apply (FOPrH_ball_split_w n G 18 (FOPlus L1 L2) (FOSucc FOZero) _ wL);
    [ | | apply FOsubst_ok_GUARDC; avoid_tm | lia | lia | lia | lia | lia | lia
      | apply HG; lia | apply HG; lia | exact HGL | exact HG2
      | apply FJ; lia | apply FJ; lia | avoid_tms | avoid_tms | avoid_tms ].
  - apply (FOPrH_ball_split_w n G 18 L1 L2 _ wD);
      [ | | apply FOsubst_ok_GUARDC; avoid_tm | lia | lia | lia | lia | lia | lia
        | apply HG; lia | apply HG; lia | exact HGD | exact HG2
        | apply FJ; lia | apply FJ; lia | avoid_tms | avoid_tms | avoid_tms ].
    + refine (FOPrH_mp _ _ _ _ _ GD1).
      apply FOPrH_ball_mono; [apply HG; lia | apply FOPrH_imp_refl|].
      apply FOPrH_intro.
      assert (Lt : FOPrH n (G ++ [FOltv 18 L1]) (FOlt470 (FOVar 18) L1)).
      { refine (FOPrH_mp _ _ _ _ (FOPrH_ltv_470 _ _ 18 L1 _ _ _ _) (FOPrH_last _ _ _));
          [lia | lia | avoid_tm | avoid_tm]. }
      apply (FOtr_GUARDC n _ 20 T1 T' cs1 ds1 cs' ds' (FOVar 18) (FOVar 18));
        [ apply FOTabMono_weak; exact Hm1
        | refine (FOPrH_agr_row _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ F1) Lt _ _);
            [avoid_tms | avoid_tms]
        | wk B1 | lia | ctx_list | ctx_list | avoid_tms | avoid_tms ].
    + apply FOPrH_all_intro; [exact HGD|]. apply FOPrH_intro.
      rewrite FOsubst_f_GUARDC by lia.
      rewrite FOsubst_t_var_eq'. subst_avoid_h Hav1.
      assert (Lt : FOPrH n (G ++ [FOlt470 (FOVar wD) L2]) (FOlt470 (FOVar wD) L2))
        by apply FOPrH_last.
      pose proof (FOPrH_ball_inst n _ 18 L2 (FOVar wD) _ (FOPrH_weak_app _ _ _ _ GD2) Lt
                    ltac:(lia) ltac:(apply FOsubst_ok_GUARDC; avoid_tm)
                    ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as D2.
      rewrite FOsubst_f_GUARDC, FOsubst_t_var_eq' in D2 by lia. subst_avoid_hin Hav1 D2.
      refine (FOPrH_mp _ _ _ _ _ D2).
      apply (FOtr_GUARDC n _ 20 T2 T' cs2 ds2 cs' ds' (FOVar wD) (FOPlus L1 (FOVar wD)));
        [ apply FOTabMono_weak; exact Hm2
        | refine (FOPrH_agrs_row _ _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ F2) Lt _ _);
            [avoid_tms | avoid_tms]
        | wk B2 | lia | ctx_list | ctx_list | avoid_tms | avoid_tms ].
  - apply FOPrH_all_intro; [exact HGL|]. apply FOPrH_intro.
    assert (Z : FOPrH n (G ++ [FOlt470 (FOVar wL) (FOSucc FOZero)]) (FOEq (FOVar wL) FOZero))
      by (apply FOPrH_lt1_zero; [apply FOPrH_last | avoid_tms]).
    apply (FOPrH_leibniz _ _ 18 (FOPlus L1 L2) (FOPlus (FOPlus L1 L2) (FOVar wL)));
      [ apply FOsubst_ok_GUARDC; avoid_tm | apply FOsubst_ok_GUARDC; avoid_tm
      | fo_lin [(.S .0, #wL, .0)]; exact Z |].
    rewrite FOsubst_f_GUARDC by lia.
    rewrite FOsubst_t_var_eq'. subst_avoid_h Hav1.
    apply (FOPrH_guard_last n _ TB T' cs' ds' L1 L2 c r);
      [ apply FOTabMono_weak; exact HmB | wk Hs | wk Hr | wk Hl | ctx_list | ctx_list
      | avoid_tms | avoid_tms ].
Qed.

Lemma FOfree_in_MAPF_any : forall w L c d l c' d',
  2 <= w -> FOtms_avoid [L; c; d; l; c'; d'] w (S w) ->
  FOfree_in w (FOMAPF L c d l c' d') = false.
Proof.
  intros w L c d l c' d' Hw Hav. unfold FOMAPF.
  destruct (Nat.eq_dec w 436) as [->|H1]; [apply FOfree_in_all_self|].
  rewrite FOfree_in_all_ne, FOfree_in_impl by lia.
  apply Bool.orb_false_iff. split.
  - destruct (Nat.eq_dec w 437) as [->|H2]; [apply FOfree_in_ex_self|].
    rewrite FOfree_in_FOExists_neq by lia. cbn [FOfree_in FOin_tm].
    rewrite (Hav l ltac:(in_list) w ltac:(lia) ltac:(lia)). nat_eqb_simpl. reflexivity.
  - apply FOfree_in_SHROW_any; [lia | avoid_tms].
Qed.

Ltac free_fm ::=
  lazymatch goal with
  | |- FOfree_in _ (FOMAPF _ _ _ _ _ _) = false =>
      apply FOfree_in_MAPF_any; [lia | avoid_tms]
  | |- FOfree_in _ (FOltv _ _) = false => apply FOfree_in_ltv; [lia | fr_tm]
  | |- FOfree_in _ (FObetaF _ _ _ _ _) = false =>
      apply FOfree_in_betaF_not; [lia | fr_tm | fr_tm | fr_tm | fr_tm]
  | |- FOfree_in _ (FOcpairF _ _ _) = false =>
      rewrite FOfree_in_FOcpairF; apply Bool.orb_false_iff; split;
      [apply Bool.orb_false_iff; split|]; fr_tm
  | |- FOfree_in _ (FOle _ _) = false => apply FOfree_in_le_any; fr_tm
  | |- FOfree_in _ (FOlt470 _ _) = false => apply FOfree_in_lt470_any; fr_tm
  | |- FOfree_in _ (FOSHIFTMP _ _ _) = false => apply FOfree_in_SHIFTMP_any; fr_tm
  | |- FOfree_in _ (FOSHIFTC _ _ _ _) = false => apply FOfree_in_SHIFTC_any; fr_tm
  | |- FOfree_in _ (FOROWAG _ _ _ _ _ _) = false =>
      apply FOfree_in_ROWAG_any; [lia | avoid_tms]
  | |- FOfree_in _ (FOAGRS _ _ _ _ _ _) = false =>
      apply FOfree_in_AGRS_any; [lia | avoid_tms]
  | |- FOfree_in _ (FOAGR _ _ _ _ _) = false =>
      apply FOfree_in_AGR_any; [lia | avoid_tms]
  | |- FOfree_in _ (FOSHROW _ _ _ _ _ _ _) = false =>
      apply FOfree_in_SHROW_any; [lia | avoid_tms]
  | |- FOfree_in _ (FOExists 468 (FOEq (FOPlus _ (FOVar 468)) _)) = false =>
      apply FOfree_in_ex468_any; fr_tm
  | |- FOfree_in _ (FOCATF _ _ _ _ _ _ _ _ _) = false => unfold FOCATF; free_fm
  | |- FOfree_in _ (FOEXTF _ _ _ _ _ _ _) = false => unfold FOEXTF; free_fm
  | |- FOfree_in _ (FOM3F _ _ _ _ _ _ _ _ _ _ _) = false => unfold FOM3F; free_fm
  | |- FOfree_in _ (FOEq _ _) = false =>
      cbn [FOfree_in]; apply Bool.orb_false_iff; split; fr_tm
  | |- FOfree_in _ (FONeg _) = false => rewrite FOfree_in_FONeg; free_fm
  | |- FOfree_in _ (FOAnd _ _) = false =>
      rewrite FOfree_in_FOAnd; apply Bool.orb_false_iff; split; free_fm
  | |- FOfree_in _ (FOOr _ _) = false =>
      rewrite FOfree_in_FOOr; apply Bool.orb_false_iff; split; free_fm
  | |- FOfree_in _ (FOImplF _ _) = false =>
      rewrite FOfree_in_impl; apply Bool.orb_false_iff; split; free_fm
  | |- FOfree_in ?w (FOExists ?y _) = false =>
      first [ constr_eq w y; apply FOfree_in_ex_self
            | rewrite FOfree_in_FOExists_neq by lia; free_fm ]
  | |- FOfree_in ?w (FOForall ?y _) = false =>
      first [ constr_eq w y; apply FOfree_in_all_self
            | rewrite FOfree_in_all_ne by lia; free_fm ]
  | |- FOfree_in _ FOFalseF = false => reflexivity
  end.

(** Bounds through a concatenation and an extension. *)

Lemma FOPrH_bound2 : forall n G c1 c2 x w,
  FOPrH n G (FOExists 468 (FOEq (FOPlus (FOPlus c1 c2) (FOVar 468)) x)) ->
  FOPrH n G (FOExists 468 (FOEq (FOPlus x (FOVar 468)) w)) ->
  FOtms_avoid [c1; c2; x; w] 420 500 ->
  FOPrH n G (FOle (FOSucc c1) (FOSucc w)) /\ FOPrH n G (FOle (FOSucc c2) (FOSucc w)).
Proof.
  intros n G c1 c2 x w H1 H2 Hav.
  assert (K : forall t k, FOtms_avoid [t] 420 500 ->
            FOPrH n [FOEq (FOPlus (FOPlus c1 c2) (FOVar 468)) x;
                     FOEq (FOPlus x (FOVar 499)) w]
              (FOEq (FOPlus (FOSucc t) k) (FOSucc w)) ->
            FOPrH n G (FOle (FOSucc t) (FOSucc w))).
  { intros t k Havk HK.
    refine (FOPrH_ctxfree2 n G _ _ _ _ H1 H2).
    refine (FOPrH_ex_elim n _ 468 (FOEq (FOPlus (FOPlus c1 c2) (FOVar 468)) x) _ _ _ _ _);
      [free_ctx | free_fm | wk_in |].
    refine (FOPrH_exe n _ 468 499 (FOEq (FOPlus x (FOVar 468)) w) _ _ _ _ _ _ _);
      [wk_in | free_ctx | free_fm | free_fm | cbn [FOsubst_ok]; reflexivity |].
    rewrite FOsubst_f_eq, !FOsubst_t_plus, FOsubst_t_var_eq'. subst_avoid_h Hav.
    unfold FOle. apply (FOPrH_ex_intro _ _ 498 k); [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_eq, FOsubst_t_plus, !FOsubst_t_succ, FOsubst_t_var_eq'.
    subst_avoid_h Hav. subst_avoid_h Havk.
    refine (FOPrH_weaken n _ _ _ _ HK).
    intros X [<-|[<-|[]]]; [apply in_or_app; left; apply in_or_app; right; left; reflexivity
                           | apply in_or_app; right; left; reflexivity]. }
  split.
  - apply (K c1 (FOPlus (FOPlus c2 (FOVar 468)) (FOVar 499))); [avoid_tms|].
    fo_lin [(.S .0, w, x .+ #499); (.S .0, x, c1 .+ c2 .+ #468)].
  - apply (K c2 (FOPlus (FOPlus c1 (FOVar 468)) (FOVar 499))); [avoid_tms|].
    fo_lin [(.S .0, w, x .+ #499); (.S .0, x, c1 .+ c2 .+ #468)].
Qed.

(** ** The formula track of the merged derivation. *)

Definition FOFTRACK (cs1 ds1 L1 cs2 ds2 L2 c cs' ds' : FOTerm) : FOFormula :=
  FOAnd (FOAGR L1 cs1 ds1 cs' ds')
  (FOAnd (FOAGRS L1 L2 cs2 ds2 cs' ds')
  (FOAnd (FObetaF 488 cs' ds' (FOPlus L1 L2) c)
  (FOAnd (FOle (FOSucc cs1) (FOSucc cs'))
         (FOle (FOSucc cs2) (FOSucc cs'))))).

Lemma FOPrH_ftrack_elim : forall n G cs1 ds1 L1 cs2 ds2 L2 c y1 y2 w1 w2 C,
  FOctx_avoid G 420 500 ->
  FOtms_avoid [cs1; ds1; L1; cs2; ds2; L2; c] 420 500 ->
  2 <= y1 -> y1 < 420 -> 2 <= y2 -> y2 < 420 -> 2 <= w1 -> w1 < 420 -> 2 <= w2 -> w2 < 420 ->
  y1 <> y2 -> y1 <> w1 -> y1 <> w2 -> y2 <> w1 -> y2 <> w2 -> w1 <> w2 ->
  FOfree_ctx y1 G -> FOfree_ctx y2 G -> FOfree_ctx w1 G -> FOfree_ctx w2 G ->
  FOfree_in y1 C = false -> FOfree_in y2 C = false ->
  FOfree_in w1 C = false -> FOfree_in w2 C = false ->
  FOtms_avoid [cs1; ds1; L1; cs2; ds2; L2; c] y1 (S y1) ->
  FOtms_avoid [cs1; ds1; L1; cs2; ds2; L2; c] y2 (S y2) ->
  FOtms_avoid [cs1; ds1; L1; cs2; ds2; L2; c] w1 (S w1) ->
  FOtms_avoid [cs1; ds1; L1; cs2; ds2; L2; c] w2 (S w2) ->
  FOPrH n (G ++ [FOFTRACK cs1 ds1 L1 cs2 ds2 L2 c (FOVar w1) (FOVar w2)]) C ->
  FOPrH n G C.
Proof.
  intros n G cs1 ds1 L1 cs2 ds2 L2 c y1 y2 w1 w2 C HG Hav
    Hy1 Hy1' Hy2 Hy2' Hw1 Hw1' Hw2 Hw2' D1 D2 D3 D4 D5 D6 G1 G2 G3 G4 C1 C2 C3 C4
    A1 A2 A3 A4 H0.
  apply (FOPrH_concat_elim n G cs1 ds1 L1 cs2 ds2 L2 (FOPlus cs1 cs2) y1 y2 C);
    try assumption; try lia; try avoid_tms.
  apply (FOPrH_extend_elim n _ (FOVar y1) (FOVar y2) (FOPlus L1 L2) c (FOVar y1) w1 w2 C);
    try assumption; try lia; try avoid_tms; try ctx_list; try free_ctx.
  lazymatch goal with
  | |- FOPrH _ ?Gc _ =>
      assert (K1 : FOPrH n Gc (FOCATF (FOPlus cs1 cs2) L1 cs1 ds1 L2 cs2 ds2 (FOVar y1)
                                 (FOVar y2))) by wk_in;
      assert (K2 : FOPrH n Gc (FOEXTF (FOVar y1) (FOPlus L1 L2) (FOVar y1) (FOVar y2) c
                                 (FOVar w1) (FOVar w2))) by wk_in
  end.
  unfold FOCATF in K1. unfold FOEXTF in K2.
  pose proof (FOPrH_and_l _ _ _ _ K1) as B1.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ K1)) as AG1.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ K1)) as AS1.
  pose proof (FOPrH_and_l _ _ _ _ K2) as B2.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ K2)) as AG2.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ K2)) as BE.
  assert (Havx : FOtms_avoid [cs1; ds1; L1; cs2; ds2; L2; c; FOVar y1; FOVar y2;
                              FOVar w1; FOVar w2] 420 500) by avoid_tms.
  destruct (FOPrH_bound2 _ _ cs1 cs2 (FOVar y1) (FOVar w1) B1 B2 ltac:(avoid_tms))
    as [Bd1 Bd2].
  refine (FOPrH_cut _ _ (FOFTRACK cs1 ds1 L1 cs2 ds2 L2 c (FOVar w1) (FOVar w2)) _ _ _).
  - unfold FOFTRACK.
    apply FOPrH_and_intro.
    { apply (FOPrH_agr_trans _ _ L1 (FOPlus L1 L2) cs1 ds1 (FOVar y1) (FOVar y2));
        [exact AG1 | exact AG2 | apply FOPrH_le_plus_r; avoid_tms | ctx_list | avoid_tms]. }
    apply FOPrH_and_intro.
    { apply (FOPrH_agrs_agr _ _ L1 L2 (FOPlus L1 L2) cs2 ds2 (FOVar y1) (FOVar y2));
        [exact AS1 | exact AG2 | | ctx_list | avoid_tms].
      unfold FOle. apply (FOPrH_ex_intro _ _ 498 FOZero); [cbn [FOsubst_ok]; reflexivity|].
      rewrite FOsubst_f_eq, !FOsubst_t_plus, FOsubst_t_var_eq'. subst_avoid_h Havx.
      apply FOPrH_Q_plus_zero. }
    apply FOPrH_and_intro; [exact BE|].
    apply FOPrH_and_intro; [exact Bd1 | exact Bd2].
  - refine (FOPrH_weaken n _ _ _ _ H0).
    intros X HX. apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
    + apply in_or_app. left. apply in_or_app. left. apply in_or_app. left. exact HX.
    + apply in_or_app. right. left. reflexivity.
Qed.

(** ** The justification track of the merged derivation.

    The codes of the first derivation, then the shifted codes of the
    second, then the modus ponens code joining their last entries.  The
    witnesses are named by consecutive variables from [k]. *)

Definition FOJTRACK (cj1 dj1 L1 cj2 dj2 L2 m1 m2 q jc cj' dj' : FOTerm) (W : nat)
    : FOFormula :=
  FOAnd (FOAGR L1 cj1 dj1 cj' dj')
  (FOAnd (FOSHMAP L1 L2 cj2 dj2 cj' dj' W)
  (FOAnd (FOle (FOSucc cj1) (FOSucc cj'))
  (FOAnd (FOcpairF m1 (FOPlus L1 m2) q)
  (FOAnd (FOcpairF (FOnumeral 4) q jc)
         (FObetaF 488 cj' dj' (FOPlus L1 L2) jc))))).

Lemma FOPrH_jtrack_elim : forall n G cj1 dj1 L1 cj2 dj2 L2 m1 m2 k C,
  FOctx_avoid G 420 500 -> FOctx_avoid G k (k + 9) -> 2 <= k -> k + 9 <= 420 ->
  (forall w, k <= w -> w < k + 9 -> FOfree_in w C = false) ->
  FOtms_avoid [cj1; dj1; L1; cj2; dj2; L2; m1; m2] 420 500 ->
  FOtms_avoid [cj1; dj1; L1; cj2; dj2; L2; m1; m2] k (k + 9) ->
  FOPrH n (G ++ [FOJTRACK cj1 dj1 L1 cj2 dj2 L2 m1 m2 (FOVar (k + 5)) (FOVar (k + 6))
                   (FOVar (k + 7)) (FOVar (k + 8)) k]) C ->
  FOPrH n G C.
Proof.
  intros n G cj1 dj1 L1 cj2 dj2 L2 m1 m2 k C HG HGk Hk Hk' HC Hav Havk H0.
  apply (FOPrH_map_elim n G L1 cj2 dj2 L2 (k + 1) (k + 2) C);
    try (apply HGk; lia); try (apply HC; lia); try lia; try avoid_tms; try assumption.
  apply (FOPrH_concat_elim n _ cj1 dj1 L1 (FOVar (k + 1)) (FOVar (k + 2)) L2
           (FOPlus cj1 (FOVar (k + 1))) (k + 3) (k + 4) C);
    try (apply HC; lia); try lia; try avoid_tms; try ctx_list; try free_ctx.
  apply (FOPrH_cpair_elim n _ m1 (FOPlus L1 m2) (k + 5) C);
    try (apply HC; lia); try lia; try avoid_tms; try ctx_list; try free_ctx.
  apply (FOPrH_cpair_elim n _ (FOnumeral 4) (FOVar (k + 5)) (k + 6) C);
    try (apply HC; lia); try lia; try avoid_tms; try ctx_list; try free_ctx.
  apply (FOPrH_extend_elim n _ (FOVar (k + 3)) (FOVar (k + 4)) (FOPlus L1 L2) (FOVar (k + 6))
           (FOVar (k + 3)) (k + 7) (k + 8) C);
    try (apply HC; lia); try lia; try avoid_tms; try ctx_list; try free_ctx.
  lazymatch goal with
  | |- FOPrH _ ?Gc _ =>
      assert (KM : FOPrH n Gc (FOMAPF L1 cj2 dj2 L2 (FOVar (k + 1)) (FOVar (k + 2))))
        by wk_in;
      assert (K1 : FOPrH n Gc (FOCATF (FOPlus cj1 (FOVar (k + 1))) L1 cj1 dj1 L2
                                 (FOVar (k + 1)) (FOVar (k + 2)) (FOVar (k + 3))
                                 (FOVar (k + 4)))) by wk_in;
      assert (Kq : FOPrH n Gc (FOcpairF m1 (FOPlus L1 m2) (FOVar (k + 5)))) by wk_in;
      assert (Kj : FOPrH n Gc (FOcpairF (FOnumeral 4) (FOVar (k + 5)) (FOVar (k + 6))))
        by wk_in;
      assert (K2 : FOPrH n Gc (FOEXTF (FOVar (k + 3)) (FOPlus L1 L2) (FOVar (k + 3))
                                 (FOVar (k + 4)) (FOVar (k + 6)) (FOVar (k + 7))
                                 (FOVar (k + 8)))) by wk_in
  end.
  unfold FOCATF in K1. unfold FOEXTF in K2.
  pose proof (FOPrH_and_l _ _ _ _ K1) as B1.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ K1)) as AG1.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ K1)) as AS1.
  pose proof (FOPrH_and_l _ _ _ _ K2) as B2.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ K2)) as AG2.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ K2)) as BE.
  assert (Havx : FOtms_avoid [cj1; dj1; L1; cj2; dj2; L2; m1; m2; FOVar (k + 1);
                              FOVar (k + 2); FOVar (k + 3); FOVar (k + 4); FOVar (k + 5);
                              FOVar (k + 6); FOVar (k + 7); FOVar (k + 8)] 420 500)
    by avoid_tms.
  destruct (FOPrH_bound2 _ _ cj1 (FOVar (k + 1)) (FOVar (k + 3)) (FOVar (k + 7)) B1 B2
              ltac:(avoid_tms)) as [Bd1 _].
  lazymatch goal with
  | |- FOPrH _ ?Gc _ =>
      assert (AS2 : FOPrH n Gc (FOAGRS L1 L2 (FOVar (k + 1)) (FOVar (k + 2)) (FOVar (k + 7))
                                  (FOVar (k + 8))))
  end.
  { apply (FOPrH_agrs_agr _ _ L1 L2 (FOPlus L1 L2) (FOVar (k + 1)) (FOVar (k + 2))
             (FOVar (k + 3)) (FOVar (k + 4))); [exact AS1 | exact AG2 | | ctx_list | avoid_tms].
    unfold FOle. apply (FOPrH_ex_intro _ _ 498 FOZero); [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_eq, !FOsubst_t_plus, FOsubst_t_var_eq'. subst_avoid_h Havx.
    apply FOPrH_Q_plus_zero. }
  refine (FOPrH_cut _ _ (FOJTRACK cj1 dj1 L1 cj2 dj2 L2 m1 m2 (FOVar (k + 5)) (FOVar (k + 6))
                          (FOVar (k + 7)) (FOVar (k + 8)) k) _ _ _).
  - unfold FOJTRACK.
    apply FOPrH_and_intro.
    { apply (FOPrH_agr_trans _ _ L1 (FOPlus L1 L2) cj1 dj1 (FOVar (k + 3)) (FOVar (k + 4)));
        [exact AG1 | exact AG2 | apply FOPrH_le_plus_r; avoid_tms | ctx_list | avoid_tms]. }
    apply FOPrH_and_intro.
    { unfold FOSHMAP. apply FOPrH_all_intro; [free_ctx|]. apply FOPrH_intro.
      lazymatch goal with
      | |- FOPrH _ ?Gc _ =>
          assert (KM' : FOPrH n Gc (FOMAPF L1 cj2 dj2 L2 (FOVar (k + 1)) (FOVar (k + 2))))
            by wk KM;
          assert (AS2' : FOPrH n Gc (FOAGRS L1 L2 (FOVar (k + 1)) (FOVar (k + 2))
                                       (FOVar (k + 7)) (FOVar (k + 8)))) by wk AS2;
          assert (Lt : FOPrH n Gc (FOlt470 (FOVar k) L2)) by apply FOPrH_last
      end.
      assert (VW : FOtm_avoid (FOVar k) 420 500) by (apply FOtm_avoid_var; lia).
      unfold FOMAPF in KM'. fo_inst_g KM' (FOVar k) VW Havx.
      pose proof (FOPrH_mp _ _ _ _ KM'
                    (FOPrH_lt470_rename _ _ 437 _ _ Lt ltac:(lia) ltac:(avoid_tms)
                       ltac:(avoid_tms))) as SH.
      apply (FOPrH_shrow_trans _ _ L1 cj2 dj2 (FOVar (k + 1)) (FOVar (k + 2))
               (FOVar (k + 7)) (FOVar (k + 8)) (FOVar k) (FOVar k) (FOPlus L1 (FOVar k)));
        [exact SH | | ctx_list | avoid_tms].
      exact (FOPrH_agrs_row _ _ L1 L2 _ _ _ _ _ AS2' Lt ltac:(avoid_tms) ltac:(avoid_tms)). }
    apply FOPrH_and_intro; [exact Bd1|].
    apply FOPrH_and_intro; [exact Kq|].
    apply FOPrH_and_intro; [exact Kj | exact BE].
  - refine (FOPrH_weaken n _ _ _ _ H0).
    intros X HX. apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
    + do 6 (apply in_or_app; left). exact HX.
    + apply in_or_app. right. left. reflexivity.
Qed.
