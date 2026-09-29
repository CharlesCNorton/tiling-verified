(******************************************************************************)
(*                                                                            *)
(*           Parametric Provability: Bypassing the Loebian Obstacle           *)
(*                                                                            *)
(*     Part 7 of 9. The second derivability condition inside T_0.             *)
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

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge.
Open Scope fo_scope.

(** ** The checker body at terms.

    [FOPRDERp cores x T cs ds cj dj L]: the derivation checker with the
    target code [x], the table [T], the two tracks and the length given
    as terms.  The checker itself is the instance at the variables
    [1] through [17]; the matrix binds [2] through [17]. *)

Definition FOPRDERp (cores : list nat) (x : FOTerm) (T : FOtab)
    (cs ds cj dj L : FOTerm) : FOFormula :=
  FOAnd (FOTBLVALID 18 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T) (td3 T)
           (tcr T) (tdr T) (tlen T))
  (FOAnd (FOBexC 18 L (FOAnd (FOEq L (FOSucc (FOVar 18))) (FObetaF 20 cs ds (FOVar 18) x)))
  (FOAnd (FOBallC 18 L (FOJUSTCK 20 cores (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T)
                          (tc3 T) (td3 T) (tcr T) (tdr T) (tlen T) cs ds cj dj (FOVar 18)))
         (FOBallC 18 L (FOGUARDC 20 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T)
                          (tc3 T) (td3 T) (tcr T) (tdr T) (tlen T) cs ds (FOVar 18))))).

Definition FOtabv (k : nat) : FOtab :=
  mkTab (FOVar k) (FOVar (k + 1)) (FOVar (k + 2)) (FOVar (k + 3)) (FOVar (k + 4))
    (FOVar (k + 5)) (FOVar (k + 6)) (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9))
    (FOVar (k + 10)).

Definition FOtab_subst (v : nat) (s : FOTerm) (T : FOtab) : FOtab :=
  mkTab (FOsubst_t v s (tct T)) (FOsubst_t v s (tdt T)) (FOsubst_t v s (tc1 T))
    (FOsubst_t v s (td1 T)) (FOsubst_t v s (tc2 T)) (FOsubst_t v s (td2 T))
    (FOsubst_t v s (tc3 T)) (FOsubst_t v s (td3 T)) (FOsubst_t v s (tcr T))
    (FOsubst_t v s (tdr T)) (FOsubst_t v s (tlen T)).

Lemma FOPRDER_p : forall cores,
  FOPRDER cores = FOPRDERp cores (FOVar 1) (FOtabv 2) (FOVar 13) (FOVar 14) (FOVar 15)
                    (FOVar 16) (FOVar 17).
Proof. reflexivity. Qed.

Lemma FOsubst_f_PRDERp : forall v s cores x T cs ds cj dj L, 0 < v -> v < 18 ->
  FOsubst_f v s (FOPRDERp cores x T cs ds cj dj L) =
  FOPRDERp cores (FOsubst_t v s x) (FOtab_subst v s T) (FOsubst_t v s cs) (FOsubst_t v s ds)
    (FOsubst_t v s cj) (FOsubst_t v s dj) (FOsubst_t v s L).
Proof.
  intros. unfold FOPRDERp, FOtab_subst. autorewrite with fosubst. reflexivity.
Qed.

Lemma FOsubst_ok_PRDERp : forall v s cores x T cs ds cj dj L,
  FOtm_avoid s 18 252 ->
  FOsubst_ok v s (FOPRDERp cores x T cs ds cj dj L) = true.
Proof. intros. unfold FOPRDERp. auto 100 with fook. Qed.

Lemma FOPRDERp_free : forall cores w x T cs ds cj dj L,
  FOfree_in w (FOPRDERp cores x T cs ds cj dj L) = true ->
  FOin_tm w x = true \/ FOin_tm w (tct T) = true \/ FOin_tm w (tdt T) = true
  \/ FOin_tm w (tc1 T) = true \/ FOin_tm w (td1 T) = true \/ FOin_tm w (tc2 T) = true
  \/ FOin_tm w (td2 T) = true \/ FOin_tm w (tc3 T) = true \/ FOin_tm w (td3 T) = true
  \/ FOin_tm w (tcr T) = true \/ FOin_tm w (tdr T) = true \/ FOin_tm w (tlen T) = true
  \/ FOin_tm w cs = true \/ FOin_tm w ds = true \/ FOin_tm w cj = true
  \/ FOin_tm w dj = true \/ FOin_tm w L = true \/ w < 2 \/ w = 18.
Proof.
  intros cores w x T cs ds cj dj L H. unfold FOPRDERp in H.
  repeat first [arm_prder | arm_betaF | ffree_leaf]; ffin.
Qed.

(** ** The matrix with the target code substituted. *)

Definition FOPRMATx (cores : list nat) (x : FOTerm) : FOFormula :=
  FOExists 2 (FOExists 3 (FOExists 4 (FOExists 5 (FOExists 6
  (FOExists 7 (FOExists 8 (FOExists 9 (FOExists 10 (FOExists 11
  (FOExists 12 (FOExists 13 (FOExists 14 (FOExists 15 (FOExists 16
  (FOExists 17 (FOPRDERp cores x (FOtabv 2) (FOVar 13) (FOVar 14) (FOVar 15) (FOVar 16)
                  (FOVar 17))))))))))))))))).

Lemma FOsubst_f_PRMAT1 : forall cores s, FOtm_avoid s 1 18 ->
  FOsubst_f 1 s (FOPRMAT cores) = FOPRMATx cores s.
Proof.
  intros cores s Hs. unfold FOPRMAT, FOPRMATx. rewrite FOPRDER_p.
  rewrite !FOsubst_f_ex_ne by lia. rewrite FOsubst_f_PRDERp by lia.
  unfold FOtab_subst, FOtabv. cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen].
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne by lia. reflexivity.
Qed.

(** ** The matrix: its existentials eliminated and introduced. *)

Lemma FOPrH_imp_exl_rename : forall n G z w A C,
  FOfree_ctx w G -> FOfree_in w C = false -> FOfree_in w A = false ->
  FOsubst_ok z (FOVar w) A = true ->
  FOPrH n G (FOsubst_f z (FOVar w) A .-> C) -> FOPrH n G (FOExists z A .-> C).
Proof.
  intros n G z w A C HG HC HA Hok H. apply FOPrH_intro.
  apply (FOPrH_exe n (G ++ [FOExists z A]) z w A C (FOPrH_last _ _ _)); try assumption.
  - apply FOfree_ctx_app1; [exact HG|].
    cbn [FOfree_in]. destruct (Nat.eqb z w); [reflexivity | exact HA].
  - apply (FOPrH_mp _ _ _ _ (FOPrH_weak_app _ _ _ _ (FOPrH_weak_app _ _ _ _ H))).
    apply FOPrH_last.
Qed.

(** One renaming step: the outermost existential at [z] of the matrix
    tail becomes the variable [w]. *)

Ltac prmat_rename_step x Hx w :=
  lazymatch goal with
  | |- FOPrH _ _ (FOImplF (FOExists ?z ?A) _) =>
      apply (FOPrH_imp_exl_rename _ _ z w A);
      [ solve [match goal with HG : FOctx_avoid _ _ _ |- _ => apply HG; lia end]
      | solve [match goal with HC : forall w, _ -> _ -> FOfree_in w _ = false |- _ =>
                                     apply HC; lia end]
      | repeat rewrite FOfree_in_FOExists_neq by lia;
        let E := fresh "E" in
        match goal with |- FOfree_in ?w' ?X = false =>
          destruct (FOfree_in w' X) eqn:E; [exfalso | reflexivity];
          apply FOPRDERp_free in E; unfold FOtabv in E;
          cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen] in E;
          repeat match type of E with _ \/ _ => destruct E as [E|E] end;
          first [ lia
                | rewrite (Hx x ltac:(in_list) w' ltac:(lia) ltac:(lia)) in E; discriminate E
                | cbn [FOin_tm] in E; apply Nat.eqb_eq in E; lia ]
        end
      | repeat (apply FOsubst_ok_ex; [apply FOin_tm_var_ne; lia|]);
        apply FOsubst_ok_PRDERp; apply FOtm_avoid_var; lia
      | repeat rewrite FOsubst_f_ex_ne by lia; rewrite FOsubst_f_PRDERp by lia;
        unfold FOtab_subst, FOtabv; cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen];
        rewrite ?FOsubst_t_var_eq', ?FOsubst_t_var_ne by lia;
        rewrite (FOsubst_t_not_in x z _ (Hx x ltac:(in_list) z ltac:(lia) ltac:(lia))) ]
  end.

Lemma FOPrH_PRMAT_elim_rename : forall n G cores x k C,
  252 <= k -> k + 16 <= 420 ->
  FOctx_avoid G k (k + 16) ->
  (forall w, k <= w -> w < k + 16 -> FOfree_in w C = false) ->
  FOtms_avoid [x] 1 420 ->
  FOPrH n (G ++ [FOPRDERp cores x (FOtabv k) (FOVar (k + 11)) (FOVar (k + 12))
                   (FOVar (k + 13)) (FOVar (k + 14)) (FOVar (k + 15))]) C ->
  FOPrH n G (FOPRMATx cores x .-> C).
Proof.
  intros n G cores x k C Hk Hk' HG HC Hx H. unfold FOPRMATx.
  prmat_rename_step x Hx k. prmat_rename_step x Hx (k + 1).
  prmat_rename_step x Hx (k + 2). prmat_rename_step x Hx (k + 3).
  prmat_rename_step x Hx (k + 4). prmat_rename_step x Hx (k + 5).
  prmat_rename_step x Hx (k + 6). prmat_rename_step x Hx (k + 7).
  prmat_rename_step x Hx (k + 8). prmat_rename_step x Hx (k + 9).
  prmat_rename_step x Hx (k + 10). prmat_rename_step x Hx (k + 11).
  prmat_rename_step x Hx (k + 12). prmat_rename_step x Hx (k + 13).
  prmat_rename_step x Hx (k + 14). prmat_rename_step x Hx (k + 15).
  apply FOPrH_intro. exact H.
Qed.

Ltac prmat_intro_step t Hav :=
  lazymatch goal with
  | |- FOPrH _ _ (FOExists ?z ?A) =>
      apply (FOPrH_ex_intro _ _ z t);
      [ repeat (apply FOsubst_ok_ex; [fr_tm|]); apply FOsubst_ok_PRDERp; avoid_tm
      | repeat rewrite FOsubst_f_ex_ne by lia; rewrite FOsubst_f_PRDERp by lia;
        unfold FOtab_subst, FOtabv; cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen];
        cbn [Nat.add];
        rewrite ?FOsubst_t_var_eq', ?FOsubst_t_var_ne by lia; subst_avoid_h Hav ]
  end.

(** The matrix introduced at witnesses for its sixteen variables.  The
    length witness [t12] may mention the variables up to [12]. *)

Lemma FOPrH_PRMAT_intro : forall n G cores x t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13
    t14 t15 t16 t17,
  FOtms_avoid [x; t2; t3; t4; t5; t6; t7; t8; t9; t10; t11; t13; t14; t15; t16; t17]
    2 252 ->
  FOtms_avoid [t12] 13 252 ->
  FOPrH n G (FOPRDERp cores x (mkTab t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12) t13 t14 t15 t16 t17) ->
  FOPrH n G (FOPRMATx cores x).
Proof.
  intros n G cores x t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 Hav H12 H.
  unfold FOPRMATx.
  prmat_intro_step t2 Hav. prmat_intro_step t3 Hav. prmat_intro_step t4 Hav.
  prmat_intro_step t5 Hav. prmat_intro_step t6 Hav. prmat_intro_step t7 Hav.
  prmat_intro_step t8 Hav. prmat_intro_step t9 Hav. prmat_intro_step t10 Hav.
  prmat_intro_step t11 Hav. prmat_intro_step t12 Hav.
  prmat_intro_step t13 Hav; subst_avoid_h H12.
  prmat_intro_step t14 Hav; subst_avoid_h H12.
  prmat_intro_step t15 Hav; subst_avoid_h H12.
  prmat_intro_step t16 Hav; subst_avoid_h H12.
  prmat_intro_step t17 Hav; subst_avoid_h H12.
  exact H.
Qed.

(** A position below a successor length. *)

Lemma FOPrH_lt_succ : forall n G m L,
  FOPrH n G (FOEq L (FOSucc m)) -> FOtms_avoid [m; L] 470 471 ->
  FOPrH n G (FOlt470 m L).
Proof.
  intros n G m L H Hav. unfold FOlt470.
  apply (FOPrH_ex_intro _ _ 470 FOZero); [cbn [FOsubst_ok]; reflexivity|].
  rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_succ, FOsubst_t_var_eq'.
  subst_avoid_h Hav.
  fo_lin [(.S .0, L, .S m)]. exact H.
Qed.

(** ** The merged derivation is accepted by the checker. *)

Lemma FOPrH_D2_body : forall n G cores T1 T2 TB T' cs1 ds1 cj1 dj1 L1 cs2 ds2 cj2 dj2 L2
    cs' ds' cj' dj' m1 m2 a b c q jc r W wL wD' wL' w1 w2,
  FOPrH n G (FOPRDERp cores a T1 cs1 ds1 cj1 dj1 L1) ->
  FOPrH n G (FOPRDERp cores b T2 cs2 ds2 cj2 dj2 L2) ->
  FOPrH n G (FOTBLVALID 18 (tct TB) (tdt TB) (tc1 TB) (td1 TB) (tc2 TB) (td2 TB) (tc3 TB)
               (td3 TB) (tcr TB) (tdr TB) (tlen TB)) ->
  FOPrH n G (FOle (FOSucc r) (FOSucc (tcr TB))) ->
  FOPrH n G (FOlookup 28 (tct TB) (tdt TB) (tc1 TB) (td1 TB) (tc2 TB) (td2 TB) (tc3 TB)
               (td3 TB) (tcr TB) (tdr TB) (tlen TB) (FOnumeral 3) (FOSucc c) FOZero c r) ->
  FOPrH n G (FOEq L1 (FOSucc m1)) -> FOPrH n G (FObetaF 20 cs1 ds1 m1 a) ->
  FOPrH n G (FOEq L2 (FOSucc m2)) -> FOPrH n G (FObetaF 20 cs2 ds2 m2 b) ->
  FOPrH n G (FOPATF 52 [b; c] cpatImpl01 a) ->
  FOPrH n G (FOTABM3 T1 T2 TB T') ->
  tlen T' = FOPlus (FOPlus (tlen T1) (tlen T2)) (tlen TB) ->
  FOPrH n G (FOFTRACK cs1 ds1 L1 cs2 ds2 L2 c cs' ds') ->
  FOPrH n G (FOJTRACK cj1 dj1 L1 cj2 dj2 L2 m1 m2 q jc cj' dj' W) ->
  260 <= W -> W < 400 -> 260 <= wL -> wL < 400 -> 260 <= wD' -> wD' < 400 ->
  260 <= wL' -> wL' < 400 -> 260 <= w1 -> w1 < 400 -> 260 <= w2 -> w2 < 400 ->
  W <> wL -> wD' <> wL' -> w1 <> w2 ->
  FOfree_ctx W G -> FOfree_ctx wL G -> FOfree_ctx wD' G -> FOfree_ctx wL' G ->
  FOfree_ctx w1 G -> FOfree_ctx w2 G ->
  FOctx_avoid G 18 260 -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T1 ++ FOtab_terms T2 ++ FOtab_terms TB ++ FOtab_terms T' ++
     [cs1; ds1; cj1; dj1; L1; cs2; ds2; cj2; dj2; L2; cs'; ds'; cj'; dj'; m1; m2;
      a; b; c; q; jc; r]) 18 260 ->
  FOtms_avoid (FOtab_terms T1 ++ FOtab_terms T2 ++ FOtab_terms TB ++ FOtab_terms T' ++
     [cs1; ds1; cj1; dj1; L1; cs2; ds2; cj2; dj2; L2; cs'; ds'; cj'; dj'; m1; m2;
      a; b; c; q; jc; r]) 400 500 ->
  (forall v, In v [W; wL; wD'; wL'; w1; w2] ->
     FOtms_avoid (FOtab_terms T1 ++ FOtab_terms T2 ++ FOtab_terms TB ++ FOtab_terms T' ++
       [cs1; ds1; cj1; dj1; L1; cs2; ds2; cj2; dj2; L2; cs'; ds'; cj'; dj'; m1; m2;
        a; b; c; q; jc; r]) v (S v)) ->
  FOPrH n G (FOPRDERp cores c T' cs' ds' cj' dj' (FOPlus (FOPlus L1 L2) (FOSucc FOZero))).
Proof.
  intros n G cores T1 T2 TB T' cs1 ds1 cj1 dj1 L1 cs2 ds2 cj2 dj2 L2 cs' ds' cj' dj' m1 m2
    a b c q jc r W wL wD' wL' w1 w2 HD1 HD2 HVB Hr Hl E1 Ha E2 Hb Hp HM Hlen HF HJ
    HW HW' HwL HwL' HwD HwD' HwL2 HwL2' Hw1 Hw1' Hw2 Hw2' D1 D2 D3
    GW GwL GwD GwL2 Gw1 Gw2 HG HG2 Hav1 Hav2 AV.
  pose proof (AV W ltac:(in_list)) as AW. pose proof (AV wL ltac:(in_list)) as AwL.
  pose proof (AV wD' ltac:(in_list)) as AwD. pose proof (AV wL' ltac:(in_list)) as AwL2.
  pose proof (AV w1 ltac:(in_list)) as Aw1. pose proof (AV w2 ltac:(in_list)) as Aw2.
  clear AV.
  unfold FOPRDERp in HD1, HD2.
  pose proof (FOPrH_and_l _ _ _ _ HD1) as V1.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ HD1))) as J1.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ HD1))) as GD1.
  pose proof (FOPrH_and_l _ _ _ _ HD2) as V2.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ HD2))) as J2.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ HD2))) as GD2.
  clear HD1 HD2.
  unfold FOFTRACK in HF.
  pose proof (FOPrH_and_l _ _ _ _ HF) as F1.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ HF)) as F2.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ HF))) as F3.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ HF)))) as B1.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ HF)))) as B2.
  clear HF.
  unfold FOJTRACK in HJ.
  pose proof (FOPrH_and_l _ _ _ _ HJ) as K1. apply FOPrH_and_r in HJ.
  pose proof (FOPrH_and_l _ _ _ _ HJ) as K2. apply FOPrH_and_r in HJ.
  pose proof (FOPrH_and_l _ _ _ _ HJ) as B3. apply FOPrH_and_r in HJ.
  pose proof (FOPrH_and_l _ _ _ _ HJ) as Hq. apply FOPrH_and_r in HJ.
  pose proof (FOPrH_and_l _ _ _ _ HJ) as Hj. apply FOPrH_and_r in HJ.
  rename HJ into Hjc.
  destruct (FOPrH_tabm3_mono n G T1 T2 TB T' HM Hlen HG2 ltac:(avoid_tms))
    as (Hm1 & Hm2 & HmB).
  (* the last entries of the two derivations, read in the merged track *)
  assert (Ha' : FOPrH n G (FObetaF 480 cs' ds' m1 a)).
  { pose proof (FOPrH_lt_succ _ _ _ _ E1 ltac:(avoid_tms)) as Lt1.
    pose proof (FOPrH_agr_row _ _ _ _ _ _ _ _ F1 Lt1 ltac:(avoid_tms) ltac:(avoid_tms)) as R1.
    apply (FOPrH_rebase_cf n G 20 480); [lia | avoid_tms | avoid_tms|].
    apply (FOPrH_row_cf n G cs1 ds1 cs' ds' m1 m1 a 20); [exact R1 | exact Ha | lia | lia
                                                         | avoid_tms | avoid_tms]. }
  assert (Hb' : FOPrH n G (FObetaF 480 cs' ds' (FOPlus L1 m2) b)).
  { pose proof (FOPrH_lt_succ _ _ _ _ E2 ltac:(avoid_tms)) as Lt2.
    pose proof (FOPrH_agrs_row _ _ _ _ _ _ _ _ _ F2 Lt2 ltac:(avoid_tms) ltac:(avoid_tms))
      as R2.
    apply (FOPrH_rebase_cf n G 20 480); [lia | avoid_tms | avoid_tms|].
    apply (FOPrH_row_cf n G cs2 ds2 cs' ds' m2 (FOPlus L1 m2) b 20);
      [exact R2 | exact Hb | lia | lia | avoid_tms | avoid_tms]. }
  unfold FOPRDERp.
  apply FOPrH_and_intro.
  { apply (FOPrH_tblvalid_merge n G T1 T2 TB T' w1 w2); try assumption; try lia;
      try (intros ? ? ?; apply HG; lia); try avoid_tms. }
  apply FOPrH_and_intro.
  { apply (FOPrH_bex_intro_t n G 18 (FOPlus (FOPlus L1 L2) (FOSucc FOZero)) (FOPlus L1 L2));
      try lia; try avoid_tm.
    - unfold FOle. apply (FOPrH_ex_intro _ _ 498 FOZero); [cbn [FOsubst_ok]; reflexivity|].
      rewrite FOsubst_f_eq. repeat (first [rewrite FOsubst_t_plus | rewrite FOsubst_t_succ
                                          | rewrite FOsubst_t_var_eq' | rewrite FOsubst_t_zero]).
      subst_avoid_h Hav2. apply FOPrH_ring. fo_ring.
    - apply FOsubst_ok_and; [apply FOsubst_ok_eq | apply FOsubst_ok_betaF; avoid_tm].
    - rewrite FOsubst_f_and, FOsubst_f_eq, FOsubst_f_betaF by lia.
      repeat (first [rewrite FOsubst_t_plus | rewrite FOsubst_t_succ
                    | rewrite FOsubst_t_var_eq' | rewrite FOsubst_t_zero]).
      subst_avoid_h Hav1.
      apply FOPrH_and_intro; [apply FOPrH_ring; fo_ring|].
      apply (FOPrH_rebase_cf n G 488 20); [lia | avoid_tms | avoid_tms | exact F3]. }
  apply FOPrH_and_intro.
  { apply (FOPrH_merged_justck n G cores T1 T2 T' cs1 ds1 cj1 dj1 cs2 ds2 cj2 dj2 cs' ds' cj'
             dj' L1 L2 m1 m2 a b c q jc W wL); try assumption; try lia; try avoid_tms. }
  apply (FOPrH_merged_guard n G T1 T2 TB T' cs1 ds1 cs2 ds2 cs' ds' L1 L2 c r wD' wL');
    try assumption; try lia; try avoid_tms.
Qed.

(** ** The guard rows of the conclusion.

    [FOGUARDB c]: some valid table has a substitution row at the
    shadow variable [S c] of [c], as the entry-code guard of a
    derivation ending in [c] requires.  The table sits at the variables
    [2] through [12] and the row's result at [13]. *)

Definition FOGUARDB (c : FOTerm) : FOFormula :=
  FOExists 2 (FOExists 3 (FOExists 4 (FOExists 5 (FOExists 6 (FOExists 7
  (FOExists 8 (FOExists 9 (FOExists 10 (FOExists 11 (FOExists 12
    (FOAnd (FOTBLVALID 18 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
              (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12))
       (FOBexC 13 (FOSucc (FOVar 10))
          (FOlookup 28 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
             (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
             (FOnumeral 3) (FOSucc c) FOZero c (FOVar 13)))))))))))))).

(** Freshness of the construction facts in the context.  The variable
    [18] is bound in every conjunct of the checker body that is not a
    table check. *)

Lemma FOPRDERp_free' : forall cores w x T cs ds cj dj L,
  FOfree_in w (FOPRDERp cores x T cs ds cj dj L) = true ->
  FOin_tm w x = true \/ FOin_tm w (tct T) = true \/ FOin_tm w (tdt T) = true
  \/ FOin_tm w (tc1 T) = true \/ FOin_tm w (td1 T) = true \/ FOin_tm w (tc2 T) = true
  \/ FOin_tm w (td2 T) = true \/ FOin_tm w (tc3 T) = true \/ FOin_tm w (td3 T) = true
  \/ FOin_tm w (tcr T) = true \/ FOin_tm w (tdr T) = true \/ FOin_tm w (tlen T) = true
  \/ FOin_tm w cs = true \/ FOin_tm w ds = true \/ FOin_tm w cj = true
  \/ FOin_tm w dj = true \/ FOin_tm w L = true \/ w < 2.
Proof.
  intros cores w x T cs ds cj dj L H.
  destruct (Nat.eq_dec w 18) as [->|Hne].
  - unfold FOPRDERp, FOBexC, FOBallC in H.
    rewrite !FOfree_in_FOAnd, FOfree_in_ex_self, !FOfree_in_all_self in H.
    rewrite !Bool.orb_false_r in H.
    apply FOTBLVALID_free in H. tauto.
  - apply FOPRDERp_free in H. tauto.
Qed.

Lemma FOfree_in_PRMATx : forall cores w x,
  18 <= w -> FOtms_avoid [x] w (S w) -> FOfree_in w (FOPRMATx cores x) = false.
Proof.
  intros cores w x Hw Hav. unfold FOPRMATx.
  repeat rewrite FOfree_in_FOExists_neq by lia.
  match goal with |- FOfree_in ?w' ?X = false =>
    let E := fresh "E" in
    destruct (FOfree_in w' X) eqn:E; [exfalso | reflexivity];
    apply FOPRDERp_free' in E; unfold FOtabv in E;
    cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen] in E;
    repeat match type of E with _ \/ _ => destruct E as [E|E] end;
    first [ lia
          | rewrite (Hav x ltac:(in_list) w ltac:(lia) ltac:(lia)) in E; discriminate E
          | cbn [FOin_tm] in E; apply Nat.eqb_eq in E; lia ]
  end.
Qed.

Lemma FOfree_in_PRMATx_bound : forall cores w x,
  2 <= w -> w < 18 -> FOtms_avoid [x] w (S w) -> FOfree_in w (FOPRMATx cores x) = false.
Proof.
  intros cores w x Hw1 Hw2 Hav. unfold FOPRMATx.
  cbn [FOfree_in].
  repeat match goal with
         | |- context [Nat.eqb ?k w] =>
             let E := fresh "E" in destruct (Nat.eqb k w) eqn:E;
             [reflexivity | apply Nat.eqb_neq in E]
         end.
  lia.
Qed.

Ltac fr_tm ::=
  lazymatch goal with
  | |- FOin_tm _ (FOVar _) = false => apply FOin_tm_var_ne; nat_fast
  | |- FOin_tm _ (FOnumeral _) = false => apply FOin_tm_numeral
  | |- FOin_tm _ FOZero = false => reflexivity
  | |- FOin_tm _ (FOSucc _) = false => rewrite FOin_tm_succ_eq; fr_tm
  | |- FOin_tm _ (FOPlus _ _) = false =>
      rewrite FOin_tm_plus_eq; apply Bool.orb_false_iff; split; fr_tm
  | |- FOin_tm _ (FOMult _ _) = false =>
      rewrite FOin_tm_mult_eq; apply Bool.orb_false_iff; split; fr_tm
  | |- FOin_tm ?w ?t = false =>
      match goal with H : FOtms_avoid ?L ?lo ?hi |- _ =>
        apply (H t ltac:(in_list) w); nat_fast end
  end.

Lemma FOtm_avoid_var_b : forall v lo hi, (Nat.ltb v lo || Nat.leb hi v)%bool = true ->
  FOtm_avoid (FOVar v) lo hi.
Proof.
  intros v lo hi H. apply FOtm_avoid_var.
  apply Bool.orb_true_iff in H. destruct H as [H|H];
    [left; apply Nat.ltb_lt; exact H | right; apply Nat.leb_le; exact H].
Qed.

Ltac avoid_tm ::=
  lazymatch goal with
  | |- FOtm_avoid (FOnumeral _) _ _ => apply FOtm_avoid_numeral
  | |- FOtm_avoid FOZero _ _ => apply FOtm_avoid_zero
  | |- FOtm_avoid (FOSucc _) _ _ => apply FOtm_avoid_succ; avoid_tm
  | |- FOtm_avoid (FOPlus _ _) _ _ => apply FOtm_avoid_plus; avoid_tm
  | |- FOtm_avoid (FOMult _ _) _ _ => apply FOtm_avoid_mult; avoid_tm
  | |- FOtm_avoid (FOVar _) _ _ =>
      first [ apply FOtm_avoid_var_b; vm_compute; reflexivity
            | apply FOtm_avoid_var; lia ]
  | |- FOtm_avoid ?t ?lo ?hi =>
      match goal with
      | H : FOtms_avoid ?L ?lo' ?hi' |- _ =>
          apply (FOtm_avoid_sub t lo' hi' lo hi); [apply H; in_list | nat_fast | nat_fast]
      end
  end.

Ltac free_ctx ::=
  lazymatch goal with
  | |- FOfree_ctx _ (_ ++ _) => apply FOfree_ctx_app_inv; free_ctx
  | |- FOfree_ctx _ (_ :: _) => apply FOfree_ctx_cons; [free_fm | free_ctx]
  | |- FOfree_ctx _ [] => apply FOfree_ctx_nil
  | |- FOfree_ctx ?w _ =>
      first [ assumption
            | match goal with HG : FOctx_avoid _ ?lo ?hi |- _ => apply HG; nat_fast end ]
  end.

Ltac free_prder :=
  lazymatch goal with
  | |- FOfree_in ?w ?X = false =>
      let E := fresh "E" in
      destruct (FOfree_in w X) eqn:E; [exfalso | reflexivity];
      apply FOPRDERp_free' in E; try unfold FOtabv in E;
      cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen] in E;
      destruct E as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]];
      lazymatch type of E with
      | FOin_tm _ ?t = true =>
          let F := fresh in
          assert (F : FOin_tm w t = false) by fr_tm;
          rewrite F in E; discriminate E
      | _ => lia
      end
  end.

Ltac free_by lem ::=
  lazymatch goal with
  | |- FOfree_in ?w ?X = false =>
      let E := fresh "E" in
      destruct (FOfree_in w X) eqn:E; [exfalso | reflexivity];
      apply lem in E;
      repeat match type of E with
             | _ \/ _ => destruct E as [E|E]
             end;
      lazymatch type of E with
      | FOin_tm _ ?t = true =>
          let F := fresh in
          assert (F : FOin_tm w t = false) by fr_tm;
          rewrite F in E; discriminate E
      | _ => lia
      end
  end.

Ltac free_fm_core :=
  lazymatch goal with
  | |- FOfree_in _ (FOPRDERp _ _ _ _ _ _ _ _) = false => free_prder
  | |- FOfree_in _ (FOPRMATx _ _) = false =>
      first [ apply FOfree_in_PRMATx; [nat_fast | avoid_tms]
            | apply FOfree_in_PRMATx_bound; [nat_fast | nat_fast | avoid_tms] ]
  | |- FOfree_in _ (FOTBLVALID _ _ _ _ _ _ _ _ _ _ _ _) = false => free_by FOTBLVALID_free
  | |- FOfree_in _ (FOlookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOlookup_free
  | |- FOfree_in _ (FOFTRACK _ _ _ _ _ _ _ _ _) = false => unfold FOFTRACK; free_fm
  | |- FOfree_in _ (FOJTRACK _ _ _ _ _ _ _ _ _ _ _ _ _) = false => unfold FOJTRACK; free_fm
  | |- FOfree_in ?w (FOSHMAP _ _ _ _ _ _ ?W) = false =>
      first [ constr_eq w W; unfold FOSHMAP; apply FOfree_in_all_self
            | unfold FOSHMAP; free_fm ]
  | |- FOfree_in _ (FOTABM3 _ _ _ _) = false => unfold FOTABM3; free_fm
  | |- FOfree_in _ (FOMAPF _ _ _ _ _ _) = false =>
      apply FOfree_in_MAPF_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOltv _ _) = false => apply FOfree_in_ltv; [nat_fast | fr_tm]
  | |- FOfree_in _ (FObetaF _ _ _ _ _) = false =>
      apply FOfree_in_betaF_not; [nat_fast | fr_tm | fr_tm | fr_tm | fr_tm]
  | |- FOfree_in _ (FOcpairF _ _ _) = false =>
      rewrite FOfree_in_FOcpairF; apply Bool.orb_false_iff; split;
      [apply Bool.orb_false_iff; split|]; fr_tm
  | |- FOfree_in _ (FOle _ _) = false => apply FOfree_in_le_any; fr_tm
  | |- FOfree_in _ (FOlt470 _ _) = false => apply FOfree_in_lt470_any; fr_tm
  | |- FOfree_in _ (FOSHIFTMP _ _ _) = false => apply FOfree_in_SHIFTMP_any; fr_tm
  | |- FOfree_in _ (FOSHIFTC _ _ _ _) = false => apply FOfree_in_SHIFTC_any; fr_tm
  | |- FOfree_in _ (FOROWAG _ _ _ _ _ _) = false =>
      apply FOfree_in_ROWAG_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOAGRS _ _ _ _ _ _) = false =>
      apply FOfree_in_AGRS_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOAGR _ _ _ _ _) = false =>
      apply FOfree_in_AGR_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOSHROW _ _ _ _ _ _ _) = false =>
      apply FOfree_in_SHROW_any; [nat_fast | avoid_tms]
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
            | rewrite FOfree_in_FOExists_neq by nat_fast; free_fm ]
  | |- FOfree_in ?w (FOForall ?y _) = false =>
      first [ constr_eq w y; apply FOfree_in_all_self
            | rewrite FOfree_in_all_ne by nat_fast; free_fm ]
  | |- FOfree_in _ FOFalseF = false => reflexivity
  end.

Ltac free_fm ::= free_fm_core.

(** The merged columns and the two tracks, each at one step. *)

Lemma FOfree_in_M3F_any : forall w c1 d1 l1 c2 d2 l2 c3 d3 l3 c' d',
  2 <= w -> FOtms_avoid [c1; d1; l1; c2; d2; l2; c3; d3; l3; c'; d'] w (S w) ->
  FOfree_in w (FOM3F c1 d1 l1 c2 d2 l2 c3 d3 l3 c' d') = false.
Proof. intros. free_fm. Qed.

Lemma FOfree_in_FTRACK_any : forall w cs1 ds1 L1 cs2 ds2 L2 c cs' ds',
  2 <= w -> FOtms_avoid [cs1; ds1; L1; cs2; ds2; L2; c; cs'; ds'] w (S w) ->
  FOfree_in w (FOFTRACK cs1 ds1 L1 cs2 ds2 L2 c cs' ds') = false.
Proof. intros. free_fm. Qed.

Lemma FOfree_in_SHMAP_any : forall w L Lb cj dj cj' dj' W,
  2 <= w -> FOtms_avoid [L; Lb; cj; dj; cj'; dj'] w (S w) ->
  FOfree_in w (FOSHMAP L Lb cj dj cj' dj' W) = false.
Proof.
  intros w L Lb cj dj cj' dj' W Hw Hav. unfold FOSHMAP.
  destruct (Nat.eq_dec W w) as [<-|Hne]; [apply FOfree_in_all_self|].
  rewrite FOfree_in_all_ne by exact Hne. free_fm.
Qed.

Lemma FOfree_in_JTRACK_any : forall w cj1 dj1 L1 cj2 dj2 L2 m1 m2 q jc cj' dj' W,
  2 <= w -> FOtms_avoid [cj1; dj1; L1; cj2; dj2; L2; m1; m2; q; jc; cj'; dj'] w (S w) ->
  FOfree_in w (FOJTRACK cj1 dj1 L1 cj2 dj2 L2 m1 m2 q jc cj' dj' W) = false.
Proof.
  intros w cj1 dj1 L1 cj2 dj2 L2 m1 m2 q jc cj' dj' W Hw Hav. unfold FOJTRACK.
  rewrite FOfree_in_FOAnd; apply Bool.orb_false_iff; split; [free_fm|].
  rewrite FOfree_in_FOAnd; apply Bool.orb_false_iff; split;
    [apply FOfree_in_SHMAP_any; [exact Hw | avoid_tms] | free_fm].
Qed.

Ltac free_fm ::=
  lazymatch goal with
  | |- FOfree_in _ (FOM3F _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_M3F_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOFTRACK _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_FTRACK_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOJTRACK _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_JTRACK_any; [nat_fast | avoid_tms]
  | |- _ => free_fm_core
  end.

(** The final entry of a checked derivation, at a named position. *)

Lemma FOPrH_final_elim : forall n G L cs ds x w C,
  FOPrH n G (FOBexC 18 L (FOAnd (FOEq L (FOSucc (FOVar 18)))
                                (FObetaF 20 cs ds (FOVar 18) x))) ->
  FOfree_ctx w G -> FOfree_in w C = false -> 24 <= w ->
  FOtms_avoid [L; cs; ds; x] 18 24 -> FOtms_avoid [L; cs; ds; x] w (S w) ->
  FOPrH n (G ++ [FOAnd (FOEq L (FOSucc (FOVar w))) (FObetaF 20 cs ds (FOVar w) x)]) C ->
  FOPrH n G C.
Proof.
  intros n G L cs ds x w C H HG HC Hw Hav1 Hav2 H0.
  rewrite FOBexC_ltv in H.
  refine (FOPrH_exe n G 18 w _ C H HG HC _ _ _).
  - free_fm.
  - assert (V : FOtm_avoid (FOVar w) 19 24) by (apply FOtm_avoid_var; lia). ok_fast V.
  - refine (FOPrH_cut _ _ (FOAnd (FOEq L (FOSucc (FOVar w))) (FObetaF 20 cs ds (FOVar w) x))
              _ _ _).
    + rewrite FOsubst_f_and. autorewrite with fosubf. subst_avoid_h Hav1.
      exact (FOPrH_and_r _ _ _ _ (FOPrH_last _ _ _)).
    + refine (FOPrH_weaken n _ _ _ _ H0). intros X HX.
      apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
      * apply in_or_app. left. apply in_or_app. left. exact HX.
      * apply in_or_app. right. left. reflexivity.
Qed.

(** Side conditions of the eliminations, dispatched by their shape. *)

Ltac side :=
  lazymatch goal with
  | |- FOctx_avoid _ _ _ => ctx_list
  | |- FOtms_avoid _ _ _ => avoid_tms
  | |- FOfree_ctx _ _ => free_ctx
  | |- FOfree_in _ _ = false => free_fm
  | |- forall w, _ -> _ -> FOfree_in w _ = false =>
      let w := fresh "w" in intros w ? ?; free_fm
  | |- _ => nat_fast
  end.

Ltac tab_avoid :=
  cbn [FOtab_terms FOtabv tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen app]; avoid_tms.

(** ** Modus ponens under the matrix, in the empty context.

    The first derivation is renamed to [330]..[345], the second to
    [260]..[275]; the guard table keeps [2]..[12] with its row at
    [13]; the final entries are [290] and [291], the merged columns
    [292]..[311], the formula track [312]..[315] and the justification
    track [316]..[324]. *)

Lemma FOPrH_D2_open : forall n cores a b c,
  FOPrH n [] (FOPATF 52 [b; c] cpatImpl01 a) ->
  FOPrH n [] (FOGUARDB c) ->
  FOtms_avoid [a; b; c] 1 500 ->
  FOPrH n [] (FOPRMATx cores a .-> FOPRMATx cores b .-> FOPRMATx cores c).
Proof.
  intros n cores a b c HP HB Hav.
  apply (FOPrH_PRMAT_elim_rename n [] cores a 330);
    [lia | lia | intros w _ _; apply FOfree_ctx_nil | side | avoid_tms |].
  cbn [app Nat.add].
  apply (FOPrH_PRMAT_elim_rename n _ cores b 260); [lia | lia | side | side | avoid_tms |].
  cbn [app Nat.add].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (D1 : FOPrH n Gc (FOPRDERp cores a (FOtabv 330) (FOVar 341) (FOVar 342)
                               (FOVar 343) (FOVar 344) (FOVar 345))) by wk_in;
    assert (D2 : FOPrH n Gc (FOPRDERp cores b (FOtabv 260) (FOVar 271) (FOVar 272)
                               (FOVar 273) (FOVar 274) (FOVar 275))) by wk_in;
    assert (A0 : FOctx_avoid Gc 2 18) by ctx_list;
    assert (A1 : FOctx_avoid Gc 18 260) by ctx_list;
    assert (A2 : FOctx_avoid Gc 276 330) by ctx_list;
    assert (A3 : FOctx_avoid Gc 346 500) by ctx_list;
    set (G0 := Gc) in *
  end.
  clearbody G0.
  refine (FOPrH_mp _ _ (FOGUARDB c) _ _
            (FOPrH_weaken n [] _ _ (fun X HX => match HX with end) HB)).
  unfold FOGUARDB.
  do 11 (apply FOPrH_imp_exl; [free_ctx | free_fm |]).
  apply FOPrH_imp_andl. apply FOPrH_intro.
  apply FOPrH_imp_bexl; [free_ctx | free_fm |]. apply FOPrH_intro.
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (D1' : FOPrH n Gc (FOPRDERp cores a (FOtabv 330) (FOVar 341) (FOVar 342)
                                (FOVar 343) (FOVar 344) (FOVar 345))) by wk D1;
    assert (D2' : FOPrH n Gc (FOPRDERp cores b (FOtabv 260) (FOVar 271) (FOVar 272)
                                (FOVar 273) (FOVar 274) (FOVar 275))) by wk D2;
    assert (VB : FOPrH n Gc (FOTBLVALID 18 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5)
                               (FOVar 6) (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10)
                               (FOVar 11) (FOVar 12))) by wk_in;
    assert (LK : FOPrH n Gc (FOlookup 28 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5)
                               (FOVar 6) (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10)
                               (FOVar 11) (FOVar 12) (FOnumeral 3) (FOSucc c) FOZero c
                               (FOVar 13))) by wk_in;
    assert (Le : FOPrH n Gc (FOle (FOSucc (FOVar 13)) (FOSucc (FOVar 10))))
      by (apply FOPrH_le_of_ltv; [free_ctx | lia | lia | avoid_tm | avoid_tm | wk_in]);
    assert (B1 : FOctx_avoid Gc 18 260) by ctx_list;
    assert (B2 : FOctx_avoid Gc 276 330) by ctx_list;
    assert (B3 : FOctx_avoid Gc 346 500) by ctx_list;
    set (G1 := Gc) in *
  end.
  clearbody G1. clear D1 D2 A0 A1 A2 A3.
  (* the final entries *)
  pose proof D1' as E1. unfold FOPRDERp in E1.
  apply FOPrH_and_r, FOPrH_and_l in E1.
  pose proof D2' as E2. unfold FOPRDERp in E2.
  apply FOPrH_and_r, FOPrH_and_l in E2.
  apply (FOPrH_final_elim n _ (FOVar 345) (FOVar 341) (FOVar 342) a 290 _ E1);
    [side | side | lia | side | side |].
  apply (FOPrH_final_elim n _ (FOVar 275) (FOVar 271) (FOVar 272) b 291);
    [wk E2 | side | side | lia | side | side |].
  (* the merged columns *)
  apply (FOPrH_merge3_elim n _ (FOVar 330) (FOVar 331) (FOVar 340) (FOVar 260) (FOVar 261)
           (FOVar 270) (FOVar 2) (FOVar 3) (FOVar 12) 292 293 294 295); [side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 332) (FOVar 333) (FOVar 340) (FOVar 262) (FOVar 263)
           (FOVar 270) (FOVar 4) (FOVar 5) (FOVar 12) 296 297 298 299); [side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 334) (FOVar 335) (FOVar 340) (FOVar 264) (FOVar 265)
           (FOVar 270) (FOVar 6) (FOVar 7) (FOVar 12) 300 301 302 303); [side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 336) (FOVar 337) (FOVar 340) (FOVar 266) (FOVar 267)
           (FOVar 270) (FOVar 8) (FOVar 9) (FOVar 12) 304 305 306 307); [side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 338) (FOVar 339) (FOVar 340) (FOVar 268) (FOVar 269)
           (FOVar 270) (FOVar 10) (FOVar 11) (FOVar 12) 308 309 310 311); [side.. |].
  (* the tracks *)
  apply (FOPrH_ftrack_elim n _ (FOVar 341) (FOVar 342) (FOVar 345) (FOVar 271) (FOVar 272)
           (FOVar 275) c 312 313 314 315); [side.. |].
  apply (FOPrH_jtrack_elim n _ (FOVar 343) (FOVar 344) (FOVar 345) (FOVar 273) (FOVar 274)
           (FOVar 275) (FOVar 290) (FOVar 291) 316); [side.. |].
  cbn [Nat.add].
  (* the merged derivation *)
  apply (FOPrH_PRMAT_intro n _ cores c (FOVar 294) (FOVar 295) (FOVar 298) (FOVar 299)
           (FOVar 302) (FOVar 303) (FOVar 306) (FOVar 307) (FOVar 310) (FOVar 311)
           (FOPlus (FOPlus (FOVar 340) (FOVar 270)) (FOVar 12)) (FOVar 314) (FOVar 315)
           (FOVar 323) (FOVar 324) (FOPlus (FOPlus (FOVar 345) (FOVar 275)) (FOSucc FOZero)));
    [avoid_tms | avoid_tms |].
  apply (FOPrH_D2_body n _ cores (FOtabv 330) (FOtabv 260) (FOtabv 2)
           (mkTab (FOVar 294) (FOVar 295) (FOVar 298) (FOVar 299) (FOVar 302) (FOVar 303)
              (FOVar 306) (FOVar 307) (FOVar 310) (FOVar 311)
              (FOPlus (FOPlus (FOVar 340) (FOVar 270)) (FOVar 12)))
           (FOVar 341) (FOVar 342) (FOVar 343) (FOVar 344) (FOVar 345)
           (FOVar 271) (FOVar 272) (FOVar 273) (FOVar 274) (FOVar 275)
           (FOVar 314) (FOVar 315) (FOVar 323) (FOVar 324) (FOVar 290) (FOVar 291)
           a b c (FOVar 321) (FOVar 322) (FOVar 13) 316 325 326 327 328 329).
  all: lazymatch goal with
       | |- FOPrH _ _ _ => idtac
       | |- FOtms_avoid _ _ _ => tab_avoid
       | |- forall v, In v _ -> _ =>
           let v := fresh "v" in let Hv := fresh "Hv" in
           intros v Hv; simpl in Hv;
           destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; tab_avoid
       | |- _ = _ => reflexivity
       | |- _ => side
       end.
  - wk D1'.
  - wk D2'.
  - wk VB.
  - wk Le.
  - wk LK.
  - apply (FOPrH_and_l _ _ _ (FObetaF 20 (FOVar 341) (FOVar 342) (FOVar 290) a)). wk_in.
  - apply (FOPrH_and_r _ _ (FOEq (FOVar 345) (FOSucc (FOVar 290)))). wk_in.
  - apply (FOPrH_and_l _ _ _ (FObetaF 20 (FOVar 271) (FOVar 272) (FOVar 291) b)). wk_in.
  - apply (FOPrH_and_r _ _ (FOEq (FOVar 275) (FOSucc (FOVar 291)))). wk_in.
  - exact (FOPrH_weaken n [] _ _ (fun X HX => match HX with end) HP).
  - unfold FOTABM3.
    apply FOPrH_and_intro; [wk_in|].
    apply FOPrH_and_intro; [wk_in|].
    apply FOPrH_and_intro; [wk_in|].
    apply FOPrH_and_intro; wk_in.
  - wk_in.
  - wk_in.
Qed.

(** ** Closed facts by evaluation.

    A formula whose variables stay below [N] has no free variable
    outside those that one evaluated scan below [N] reports. *)

Lemma FOfree_check : forall A N (ok : nat -> bool),
  FOvars_max A < N ->
  forallb (fun v => orb (ok v) (negb (FOfree_in v A))) (seq 0 N) = true ->
  forall v, ok v = false -> FOfree_in v A = false.
Proof.
  intros A N ok HN Hall v Hv.
  destruct (Nat.lt_ge_cases v N) as [Hlt|Hge].
  - rewrite forallb_forall in Hall.
    specialize (Hall v (proj2 (in_seq N 0 v) (conj (Nat.le_0_l v) Hlt))).
    rewrite Hv in Hall. cbn in Hall.
    destruct (FOfree_in v A); [discriminate Hall | reflexivity].
  - apply FOfree_in_above. lia.
Qed.

Lemma FOPrH_true_closed : forall n A,
  FOsigma1 A -> (forall v, FOfree_in v A = false) -> FOsat (fun _ => 0) A ->
  FOPrH n [] A.
Proof.
  intros n A HS Hc Hs. unfold FOPrH. cbn [FOimps].
  exact (FOsigma1_completeness_closed A HS Hc Hs n).
Qed.

(** ** The guard at the code of a formula. *)

Lemma FOGUARDB_num : forall k,
  FOGUARDB (FOnumeral k) = FOsubst_num 1 k (FOGUARDB (FOVar 1)).
Proof.
  intros k. rewrite <- FOsubst_f_num. unfold FOGUARDB.
  autorewrite with fosubst. rewrite ?FOsubst_t_var_eq'. reflexivity.
Qed.

Lemma FOGUARDB_closed : forall k v, FOfree_in v (FOGUARDB (FOnumeral k)) = false.
Proof.
  intros k v. rewrite FOGUARDB_num, FOfree_in_subst_num.
  destruct (Nat.eqb_spec v 1) as [->|Hv]; [reflexivity|].
  apply (FOfree_check _ 122 (fun v => Nat.eqb v 1));
    [apply Nat.ltb_lt; vm_compute; reflexivity | vm_compute; reflexivity |].
  apply Nat.eqb_neq. exact Hv.
Qed.

Lemma FOGUARDB_sigma1 : forall k, FOsigma1 (FOGUARDB (FOnumeral k)).
Proof.
  intros k. unfold FOGUARDB. do 11 apply FOs1_ex. apply FOs1_d0.
  apply FOdelta0_and.
  - apply FOdelta0_FOTBLVALID. unfold tbl_below. cbn. lia.
  - apply FOdelta0_FOBexC; [reflexivity | reflexivity |].
    apply FOdelta0_FOlookup;
      [unfold tbl_below; cbn; lia | cbn; lia | cbn; rewrite FOmax_var_numeral; lia
      | cbn; lia | rewrite FOmax_var_numeral; lia | cbn; lia].
Qed.

Lemma FOGUARDB_sat : forall B,
  FOsat (fun _ => 0) (FOGUARDB (FOnumeral (FOcode_f B))).
Proof.
  intros B.
  destruct (table_realize (trace3 (S (FOcode_f B)) (FOVar 0) B)
              (trace3_ok (S (FOcode_f B)) (FOVar 0) B _ (incl_refl _)))
    as [vct [vdt [vc1 [vd1 [vc2 [vd2 [vc3 [vd3 [vcr [vdr [HIFF Hdisp]]]]]]]]]]].
  assert (Hrow : tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr
                   (length (trace3 (S (FOcode_f B)) (FOVar 0) B))
                   3 (S (FOcode_f B)) 0 (FOcode_f B)
                   (FOcode_f (FOsubst_f (S (FOcode_f B)) (FOVar 0) B))).
  { apply HIFF. unfold listL.
    pose proof (trace3_seed (S (FOcode_f B)) (FOVar 0) B
                  (FOcode_f (FOsubst_f (S (FOcode_f B)) (FOVar 0) B)) eq_refl) as H.
    change (FOcode_tm (FOVar 0)) with 0 in H. exact H. }
  unfold FOGUARDB. cbn [FOsat].
  exists vct, vdt, vc1, vd1, vc2, vd2, vc3, vd3, vcr, vdr,
    (length (trace3 (S (FOcode_f B)) (FOVar 0) B)).
  apply FOsat_FOAnd. split.
  - apply (proj2 (FOsat_FOTBLVALID _ 18 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
                    (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
                    ltac:(unfold tbl_below; cbn; lia))).
    cbn [FOeval FOupdate Nat.eqb]. exact Hdisp.
  - apply (proj2 (FOsat_FOBexC _ 13 (FOSucc (FOVar 10)) _ eq_refl eq_refl)).
    exists (FOcode_f (FOsubst_f (S (FOcode_f B)) (FOVar 0) B)). split.
    + cbn [FOeval FOupdate Nat.eqb].
      destruct Hrow as [j [_ [_ [_ [_ [_ Hr]]]]]]. unfold beta in Hr.
      pose proof (Nat.Div0.mod_le vcr (vdr * S j + 1)). lia.
    + apply (proj2 (FOsat_FOlookup _ 28 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
                      (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
                      (FOnumeral 3) (FOSucc (FOnumeral (FOcode_f B))) FOZero
                      (FOnumeral (FOcode_f B)) (FOVar 13)
                      ltac:(unfold tbl_below; cbn; lia) ltac:(cbn; lia)
                      ltac:(cbn; rewrite FOmax_var_numeral; lia) ltac:(cbn; lia)
                      ltac:(rewrite FOmax_var_numeral; lia) ltac:(cbn; lia))).
      cbn [FOeval FOupdate Nat.eqb]. rewrite !FOeval_numeral. exact Hrow.
Qed.

(** ** The implication pattern at codes. *)

Lemma FOPATF_impl_num : forall a b c,
  FOPATF 52 [FOnumeral b; FOnumeral c] cpatImpl01 (FOnumeral a) =
  FOsubst_num 0 a (FOsubst_num 1 b (FOsubst_num 2 c
    (FOPATF 52 [FOVar 1; FOVar 2] cpatImpl01 (FOVar 0)))).
Proof.
  intros a b c. rewrite <- !FOsubst_f_num. autorewrite with fosubf. reflexivity.
Qed.

Lemma FOPATF_impl_closed : forall a b c v,
  FOfree_in v (FOPATF 52 [FOnumeral b; FOnumeral c] cpatImpl01 (FOnumeral a)) = false.
Proof.
  intros a b c v. rewrite FOPATF_impl_num, !FOfree_in_subst_num.
  destruct (Nat.eqb_spec v 0) as [_|H0]; [reflexivity|].
  destruct (Nat.eqb_spec v 1) as [_|H1]; [reflexivity|].
  destruct (Nat.eqb_spec v 2) as [_|H2]; [reflexivity|].
  apply (FOfree_check _ 60 (fun v => Nat.leb v 2));
    [apply Nat.ltb_lt; vm_compute; reflexivity | vm_compute; reflexivity |].
  apply Nat.leb_gt. lia.
Qed.

Lemma FOPATF_impl_sigma1 : forall a b c,
  FOsigma1 (FOPATF 52 [FOnumeral b; FOnumeral c] cpatImpl01 (FOnumeral a)).
Proof.
  intros a b c. apply FOs1_d0. apply FOdelta0_FOPATF.
  - apply Forall_cons; [rewrite FOmax_var_numeral; lia|].
    apply Forall_cons; [rewrite FOmax_var_numeral; lia|]. apply Forall_nil.
  - rewrite FOmax_var_numeral. lia.
Qed.

Lemma FOPATF_impl_sat : forall A B,
  FOsat (fun _ => 0) (FOPATF 52 [FOnumeral (FOcode_f A); FOnumeral (FOcode_f B)] cpatImpl01
                        (FOnumeral (FOcode_f (FOImplF A B)))).
Proof.
  intros A B.
  apply (proj2 (FOsat_FOPATF cpatImpl01 (fun _ => 0) 52 _ _
                  ltac:(apply Forall_cons; [rewrite FOmax_var_numeral; lia|];
                        apply Forall_cons; [rewrite FOmax_var_numeral; lia|];
                        apply Forall_nil)
                  ltac:(rewrite FOmax_var_numeral; lia))).
  cbn [cpat_sem cpatImpl01 pImpP nth]. rewrite !FOeval_numeral. reflexivity.
Qed.

(** ** Numeral substitutions at distinct variables commute. *)

Lemma FOsubst_tm_comm : forall t x y k m, x <> y ->
  FOsubst_tm x k (FOsubst_tm y m t) = FOsubst_tm y m (FOsubst_tm x k t).
Proof.
  induction t as [v| |a IH|a IHa b IHb|a IHa b IHb]; intros x y k m Hxy; cbn.
  - destruct (Nat.eqb_spec v y) as [Ey|Ey]; destruct (Nat.eqb_spec v x) as [Ex|Ex].
    + subst. contradiction.
    + rewrite FOsubst_tm_numeral. cbn. rewrite (proj2 (Nat.eqb_eq v y) Ey). reflexivity.
    + rewrite FOsubst_tm_numeral. cbn. rewrite (proj2 (Nat.eqb_eq v x) Ex). reflexivity.
    + cbn. rewrite (proj2 (Nat.eqb_neq v x) Ex), (proj2 (Nat.eqb_neq v y) Ey). reflexivity.
  - reflexivity.
  - rewrite IH by exact Hxy. reflexivity.
  - rewrite IHa, IHb by exact Hxy. reflexivity.
  - rewrite IHa, IHb by exact Hxy. reflexivity.
Qed.

Lemma FOsubst_num_comm : forall A x y k m, x <> y ->
  FOsubst_num x k (FOsubst_num y m A) = FOsubst_num y m (FOsubst_num x k A).
Proof.
  induction A as [a b | | B IHB C IHC | z B IHB | z B IHB]; intros x y k m Hxy; cbn.
  - rewrite (FOsubst_tm_comm a), (FOsubst_tm_comm b) by exact Hxy. reflexivity.
  - reflexivity.
  - rewrite IHB, IHC by exact Hxy. reflexivity.
  - destruct (Nat.eqb z y) eqn:Ey; destruct (Nat.eqb z x) eqn:Ex; cbn;
      rewrite ?Ey, ?Ex; try reflexivity. rewrite IHB by exact Hxy. reflexivity.
  - destruct (Nat.eqb z y) eqn:Ey; destruct (Nat.eqb z x) eqn:Ex; cbn;
      rewrite ?Ey, ?Ex; try reflexivity. rewrite IHB by exact Hxy. reflexivity.
Qed.

(** ** The second derivability condition, proved inside [T_0]. *)

Lemma FOPRMATx_num : forall cores k,
  FOPRMATx cores (FOnumeral k) = FOsubst_num 1 k (FOPRMAT cores).
Proof.
  intros cores k. rewrite <- FOsubst_f_num. symmetry. apply FOsubst_f_PRMAT1.
  apply FOtm_avoid_numeral.
Qed.

Theorem FOHBL2_internal : forall k A B,
  FOProvesTn 0 (FOImplF (FOProvSentence k (FOImplF A B))
                  (FOImplF (FOProvSentence k A) (FOProvSentence k B))).
Proof.
  intros k A B.
  pose proof (FOPrH_D2_open 0 (FOPrCores k) (FOnumeral (FOcode_f (FOImplF A B)))
                (FOnumeral (FOcode_f A)) (FOnumeral (FOcode_f B))
                (FOPrH_true_closed 0 _ (FOPATF_impl_sigma1 _ _ _)
                   (FOPATF_impl_closed _ _ _) (FOPATF_impl_sat A B))
                (FOPrH_true_closed 0 _ (FOGUARDB_sigma1 _) (FOGUARDB_closed _)
                   (FOGUARDB_sat B))
                ltac:(apply FOtms_avoid_cons; [apply FOtm_avoid_numeral|];
                      apply FOtms_avoid_cons; [apply FOtm_avoid_numeral|];
                      apply FOtms_avoid_cons; [apply FOtm_avoid_numeral|];
                      apply FOtms_avoid_nil)) as H.
  apply (FOPrH_all_intro 0 [] 0 _ (FOfree_ctx_nil 0)) in H.
  apply (FOPrH_inst 0 [] 0 (FOnumeral (FOcode_f (FOPRMAT (FOPrCores k))))) in H;
    [| apply FOsubst_ok_numeral].
  unfold FOPrH in H. cbn [FOimps] in H.
  rewrite FOsubst_f_num in H. cbn [FOsubst_num] in H.
  rewrite !FOPRMATx_num in H.
  unfold FOProvSentence.
  rewrite !(FOsubst_num_comm (FOPRMAT (FOPrCores k)) 1 0) by lia.
  exact H.
Qed.
