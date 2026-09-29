From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36.
Open Scope fo_scope.

(** ** The beta function is functional at every base. *)

Ltac ok_leaf :=
  repeat first [ apply FOsubst_ok_all; [fr_tm|]
               | apply FOsubst_ok_impl
               | apply FOsubst_ok_betaF; avoid_tm
               | apply FOsubst_ok_eq ].

Lemma FOPrH_beta_fun_at : forall n G v c d i x y,
  FOPrH n G (FObetaF v c d i x) -> FOPrH n G (FObetaF v c d i y) ->
  2 <= v -> v + 4 <= 420 ->
  FOtms_avoid [c; d; i; x; y] v (v + 4) -> FOtms_avoid [c; d; i; x; y] 420 490 ->
  FOPrH n G (FOEq x y).
Proof.
  intros n G v c d i x y H1 H2 Hv1 Hv2 Hav Hav2.
  pose proof (FOPrH_rebase_cf n G v 480 c d i x ltac:(lia) ltac:(avoid_tms) ltac:(avoid_tms) H1)
    as K1.
  pose proof (FOPrH_rebase_cf n G v 480 c d i y ltac:(lia) ltac:(avoid_tms) ltac:(avoid_tms) H2)
    as K2.
  pose proof (FOPrH_thm n G _ (FOPr_beta_fun n)) as F.
  apply (FOPrH_inst n G 420 c) in F; [|ok_leaf].
  rewrite !FOsubst_f_all_ne, FOsubst_f_impl, FOsubst_f_impl, !FOsubst_f_betaF, FOsubst_f_eq
    in F by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in F by lia.
  apply (FOPrH_inst n G 421 d) in F; [|ok_leaf].
  rewrite !FOsubst_f_all_ne, FOsubst_f_impl, FOsubst_f_impl, !FOsubst_f_betaF, FOsubst_f_eq
    in F by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in F by lia.
  rewrite (FOsubst_t_not_in c 421 d) in F by fr_tm.
  apply (FOPrH_inst n G 422 i) in F; [|ok_leaf].
  rewrite !FOsubst_f_all_ne, FOsubst_f_impl, FOsubst_f_impl, !FOsubst_f_betaF, FOsubst_f_eq
    in F by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in F by lia.
  rewrite (FOsubst_t_not_in c 422 i), (FOsubst_t_not_in d 422 i) in F by fr_tm.
  apply (FOPrH_inst n G 423 x) in F; [|ok_leaf].
  rewrite !FOsubst_f_all_ne, FOsubst_f_impl, FOsubst_f_impl, !FOsubst_f_betaF, FOsubst_f_eq
    in F by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in F by lia.
  rewrite (FOsubst_t_not_in c 423 x), (FOsubst_t_not_in d 423 x), (FOsubst_t_not_in i 423 x)
    in F by fr_tm.
  apply (FOPrH_inst n G 424 y) in F; [|ok_leaf].
  rewrite FOsubst_f_impl, FOsubst_f_impl, !FOsubst_f_betaF, FOsubst_f_eq in F by lia.
  rewrite FOsubst_t_var_eq' in F.
  rewrite (FOsubst_t_not_in c 424 y), (FOsubst_t_not_in d 424 y), (FOsubst_t_not_in i 424 y),
    (FOsubst_t_not_in x 424 y) in F by fr_tm.
  exact (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ F K1) K2).
Qed.

(** ** Substitution into the dispatch cases. *)

Lemma FOsubst_f_DISPCASES : forall x s ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r,
  x < 50 ->
  FOsubst_f x s (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r) =
  FODISPCASES (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1) (FOsubst_t x s d1)
    (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3) (FOsubst_t x s d3)
    (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s tg) (FOsubst_t x s a1) (FOsubst_t x s a2) (FOsubst_t x s a3)
    (FOsubst_t x s r).
Proof. intros. unfold FODISPCASES. autorewrite with fosubst. reflexivity. Qed.

Lemma FOsubst_ok_DISPCASES : forall x s ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r,
  FOtm_avoid s 50 122 ->
  FOsubst_ok x s (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r) = true.
Proof.
  intros x s ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r V.
  assert (V' : FOtm_avoid s 50 (50 + 72)) by exact V.
  unfold FODISPCASES. auto 100 with fook.
Qed.

Ltac free_fm ::=
  lazymatch goal with
  | |- FOfree_in _ (FOTBLVALID _ _ _ _ _ _ _ _ _ _ _ _) = false => free_by FOTBLVALID_free
  | |- FOfree_in _ (FOlookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOlookup_free
  | |- FOfree_in _ (FOPRu _ _ _) = false => apply FOfree_in_PRu; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOTBLEX3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_TBLEX3_any; [nat_fast | avoid_tms]
  | |- FOfree_in ?w (FOBexC ?v _ _) = false =>
      first [ constr_eq w v; apply FOfree_in_FOBexC_self
            | rewrite FOBexC_ltv; free_fm ]
  | |- FOfree_in _ (FOJUSTCK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOJUSTCK_free
  | |- FOfree_in _ (FOGUARDC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOGUARDC_free
  | |- FOfree_in _ (FONUMR _ _) = false => unfold FONUMR; free_fm
  | |- FOfree_in _ (FOTBLEX _ _ _ _ _) = false =>
      apply FOfree_in_TBLEX_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOM3F _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_M3F_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOFTRACK _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_FTRACK_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOJTRACK _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_JTRACK_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOPATF _ _ _ _) = false =>
      first [ apply FOfree_in_PATF_any; [nat_fast | avoid_tms]
            | apply FOfree_in_PATF_lo; [nat_fast | avoid_tms] ]
  | |- FOfree_in _ (FOGUARDB _) = false =>
      apply FOfree_in_GUARDB_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOTEXT _ _ _ _ _ _ _) = false => unfold FOTEXT; free_fm
  | |- FOfree_in _ (FOTBLNEW _ _ _ _ _ _ _) = false => unfold FOTBLNEW; free_fm
  | |- FOfree_in _ (FOINCL _ _) = false =>
      apply FOfree_in_INCL_any; [nat_fast | avoid_tms]
  | |- _ => free_fm_core
  end.

(** ** A row of a valid table satisfies its step clause.

    The table is renamed to [122 .. 132]; the continuation receives
    the validity of the table and the dispatch cases at the row. *)

Lemma FOPrH_tblex_inv : forall n G tg a1 a2 a3 r C,
  FOctx_avoid G 2 1000 -> FOtms_avoid [tg; a1; a2; a3; r] 2 1000 ->
  (forall w, 2 <= w -> w < 1000 -> FOfree_in w C = false) ->
  FOPrH n G (FOTBLEX tg a1 a2 a3 r) ->
  FOPrH n (G ++ [FOTBLVALID 18 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                   (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132);
                 FODISPCASES (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                   (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                   tg a1 a2 a3 r]) C ->
  FOPrH n G C.
Proof.
  intros n G tg a1 a2 a3 r C HG Hav HC H H0.
  refine (FOPrH_mp _ _ _ _ (FOPrH_tblex_elim n G tg a1 a2 a3 r 122 C _ _ _ _ _ _ _) H);
    [lia | lia | intros w ? ?; apply HG; lia | intros w ? ?; apply HC; lia | avoid_tms
    | avoid_tms |].
  cbn [Nat.add].
  lazymatch goal with |- FOPrH _ (_ ++ [?X]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G X)) as KV;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G X)) as KL
  end.
  unfold FOlookup in KL. rewrite FOBexC_ltv in KL.
  set (T := [FOVar 122; FOVar 123; FOVar 124; FOVar 125; FOVar 126; FOVar 127; FOVar 128;
             FOVar 129; FOVar 130; FOVar 131; FOVar 132]).
  assert (HavT : FOtms_avoid (T ++ [tg; a1; a2; a3; r]) 2 122)
    by (unfold T; avoid_tms).
  assert (HavT2 : FOtms_avoid (T ++ [tg; a1; a2; a3; r]) 133 1000)
    by (unfold T; avoid_tms).
  refine (FOPrH_exe_clean n _ 28 140 _
            (FOAnd (FOExists 29 (FOEq (FOPlus (FOVar 140) (FOSucc (FOVar 29))) (FOVar 132)))
            (FOAnd (FObetaF 30 (FOVar 122) (FOVar 123) (FOVar 140) tg)
            (FOAnd (FObetaF 34 (FOVar 124) (FOVar 125) (FOVar 140) a1)
            (FOAnd (FObetaF 38 (FOVar 126) (FOVar 127) (FOVar 140) a2)
            (FOAnd (FObetaF 42 (FOVar 128) (FOVar 129) (FOVar 140) a3)
                   (FObetaF 46 (FOVar 130) (FOVar 131) (FOVar 140) r))))))
            C KL _ _ _ _ _ _);
    [free_ctx | apply HC; lia | free_fm | solve [auto 100 with fook] | |].
  { unfold FOltv. autorewrite with fosubst. rewrite ?FOsubst_t_var_eq'.
    subst_avoid_h HavT. apply FOPrH_assum; left; reflexivity. }
  lazymatch goal with |- FOPrH _ (?G2 ++ [?Y]) _ =>
    pose proof (FOPrH_last n G2 Y) as KJ;
    pose proof (FOPrH_weak_app _ _ [Y] _ KV) as KV2
  end.
  pose proof (FOPrH_and_l _ _ _ _ KJ) as Lt29.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ KJ)) as B0.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ KJ))) as B1.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ KJ)))) as B2.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ KJ))))) as B3.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ KJ))))) as B4.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_exeq_rename n _ 29 470 (FOVar 140) (FOVar 132)
                ltac:(lia) ltac:(fr_tm) ltac:(fr_tm) ltac:(fr_tm) ltac:(fr_tm)) Lt29) as Lt470.
  pose proof (FOPrH_ball_inst n _ 18 (FOVar 132) (FOVar 140)
                (FOSTEPDISPATCH 20 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                   (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                   (FOVar 18)) KV2 Lt470 ltac:(lia)
                ltac:(assert (V : FOtm_avoid (FOVar 140) 20 (20 + 102)) by avoid_tm;
                      auto 100 with fook)
                ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as KD.
  rewrite FOsubst_f_STEPDISPATCH in KD by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in KD by lia.
  refine (FOPrH_ex_elim n _ 20 _ C _ _ KD _); [free_ctx | apply HC; lia |].
  cbn [Nat.add].
  lazymatch goal with |- FOPrH _ (?G3 ++ [?Y]) _ =>
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G3 Y)) as KD1 end.
  refine (FOPrH_ex_elim n _ 22 _ C _ _ KD1 _); [free_ctx | apply HC; lia |].
  cbn [Nat.add].
  lazymatch goal with |- FOPrH _ (?G3 ++ [?Y]) _ =>
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G3 Y)) as KD2 end.
  refine (FOPrH_ex_elim n _ 24 _ C _ _ KD2 _); [free_ctx | apply HC; lia |].
  cbn [Nat.add].
  lazymatch goal with |- FOPrH _ (?G3 ++ [?Y]) _ =>
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G3 Y)) as KD3 end.
  refine (FOPrH_ex_elim n _ 26 _ C _ _ KD3 _); [free_ctx | apply HC; lia |].
  cbn [Nat.add].
  lazymatch goal with |- FOPrH _ (?G3 ++ [?Y]) _ =>
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G3 Y)) as KD4 end.
  refine (FOPrH_ex_elim n _ 28 _ C _ _ KD4 _); [free_ctx | apply HC; lia |].
  cbn [Nat.add].
  lazymatch goal with |- FOPrH _ (?G3 ++ [?Y]) _ =>
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G3 Y)) as KE end.
  pose proof (FOPrH_and_l _ _ _ _ KE) as D0.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ KE)) as D1.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ KE))) as D2.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ KE)))) as D3.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ KE))))) as D4.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ KE))))) as CS.
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (B0' : FOPrH n Gc (FObetaF 30 (FOVar 122) (FOVar 123) (FOVar 140) tg)) by wk B0;
    assert (B1' : FOPrH n Gc (FObetaF 34 (FOVar 124) (FOVar 125) (FOVar 140) a1)) by wk B1;
    assert (B2' : FOPrH n Gc (FObetaF 38 (FOVar 126) (FOVar 127) (FOVar 140) a2)) by wk B2;
    assert (B3' : FOPrH n Gc (FObetaF 42 (FOVar 128) (FOVar 129) (FOVar 140) a3)) by wk B3;
    assert (B4' : FOPrH n Gc (FObetaF 46 (FOVar 130) (FOVar 131) (FOVar 140) r)) by wk B4;
    assert (KV' : FOPrH n Gc (FOTBLVALID 18 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125)
                    (FOVar 126) (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131)
                    (FOVar 132))) by wk KV
  end.
  pose proof (FOPrH_beta_fun_at n _ 30 _ _ _ _ _ D0 B0' ltac:(lia) ltac:(lia) ltac:(avoid_tms)
                ltac:(avoid_tms)) as E0.
  pose proof (FOPrH_beta_fun_at n _ 34 _ _ _ _ _ D1 B1' ltac:(lia) ltac:(lia) ltac:(avoid_tms)
                ltac:(avoid_tms)) as E1.
  pose proof (FOPrH_beta_fun_at n _ 38 _ _ _ _ _ D2 B2' ltac:(lia) ltac:(lia) ltac:(avoid_tms)
                ltac:(avoid_tms)) as E2.
  pose proof (FOPrH_beta_fun_at n _ 42 _ _ _ _ _ D3 B3' ltac:(lia) ltac:(lia) ltac:(avoid_tms)
                ltac:(avoid_tms)) as E3.
  pose proof (FOPrH_beta_fun_at n _ 46 _ _ _ _ _ D4 B4' ltac:(lia) ltac:(lia) ltac:(avoid_tms)
                ltac:(avoid_tms)) as E4.
  assert (Vtg : FOtm_avoid tg 50 122) by avoid_tm.
  assert (Va1 : FOtm_avoid a1 50 122) by avoid_tm.
  assert (Va2 : FOtm_avoid a2 50 122) by avoid_tm.
  assert (Va3 : FOtm_avoid a3 50 122) by avoid_tm.
  assert (Vr : FOtm_avoid r 50 122) by avoid_tm.
  pose proof (FOPrH_leibniz n _ 20 (FOVar 20) tg
                (FODISPCASES (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                   (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                   (FOVar 20) (FOVar 22) (FOVar 24) (FOVar 26) (FOVar 28))
                ltac:(apply FOsubst_ok_var_self) ltac:(apply FOsubst_ok_DISPCASES; exact Vtg)
                E0) as L0.
  rewrite FOsubst_f_id in L0. specialize (L0 CS).
  rewrite FOsubst_f_DISPCASES in L0 by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in L0 by lia.
  pose proof (FOPrH_leibniz n _ 22 (FOVar 22) a1
                (FODISPCASES (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                   (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                   tg (FOVar 22) (FOVar 24) (FOVar 26) (FOVar 28))
                ltac:(apply FOsubst_ok_var_self) ltac:(apply FOsubst_ok_DISPCASES; exact Va1)
                E1) as L1.
  rewrite FOsubst_f_id in L1. specialize (L1 L0).
  rewrite FOsubst_f_DISPCASES in L1 by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in L1 by lia.
  rewrite (FOsubst_t_not_in tg 22 a1) in L1 by fr_tm.
  pose proof (FOPrH_leibniz n _ 24 (FOVar 24) a2
                (FODISPCASES (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                   (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                   tg a1 (FOVar 24) (FOVar 26) (FOVar 28))
                ltac:(apply FOsubst_ok_var_self) ltac:(apply FOsubst_ok_DISPCASES; exact Va2)
                E2) as L2.
  rewrite FOsubst_f_id in L2. specialize (L2 L1).
  rewrite FOsubst_f_DISPCASES in L2 by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in L2 by lia.
  rewrite (FOsubst_t_not_in tg 24 a2), (FOsubst_t_not_in a1 24 a2) in L2 by fr_tm.
  pose proof (FOPrH_leibniz n _ 26 (FOVar 26) a3
                (FODISPCASES (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                   (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                   tg a1 a2 (FOVar 26) (FOVar 28))
                ltac:(apply FOsubst_ok_var_self) ltac:(apply FOsubst_ok_DISPCASES; exact Va3)
                E3) as L3.
  rewrite FOsubst_f_id in L3. specialize (L3 L2).
  rewrite FOsubst_f_DISPCASES in L3 by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in L3 by lia.
  rewrite (FOsubst_t_not_in tg 26 a3), (FOsubst_t_not_in a1 26 a3), (FOsubst_t_not_in a2 26 a3)
    in L3 by fr_tm.
  pose proof (FOPrH_leibniz n _ 28 (FOVar 28) r
                (FODISPCASES (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                   (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                   tg a1 a2 a3 (FOVar 28))
                ltac:(apply FOsubst_ok_var_self) ltac:(apply FOsubst_ok_DISPCASES; exact Vr)
                E4) as L4.
  rewrite FOsubst_f_id in L4. specialize (L4 L3).
  rewrite FOsubst_f_DISPCASES in L4 by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in L4 by lia.
  rewrite (FOsubst_t_not_in tg 28 r), (FOsubst_t_not_in a1 28 r), (FOsubst_t_not_in a2 28 r),
    (FOsubst_t_not_in a3 28 r) in L4 by fr_tm.
  refine (FOPrH_cut _ _ _ C KV' _).
  refine (FOPrH_cut _ _ _ C (FOPrH_weak_app _ _ _ _ L4) _).
  refine (FOPrH_weaken n _ _ C _ H0).
  intros Y HY. apply in_app_or in HY. destruct HY as [HY|[<-|[<-|[]]]].
  - do 2 (apply in_or_app; left). repeat (apply in_or_app; left). exact HY.
  - apply in_or_app. left. apply in_or_app. right. left. reflexivity.
  - apply in_or_app. right. left. reflexivity.
Qed.
