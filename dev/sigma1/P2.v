From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1.
Open Scope fo_scope.

(** ** A bounded universal extended by its last position. *)

Lemma FOPrH_ball_snoc : forall n G v L P w,
  FOPrH n G (FOBallC v L P) -> FOPrH n G (FOsubst_f v L P) ->
  FOsubst_ok v L P = true ->
  2 <= v -> v < 399 -> 1 < w -> w <> v -> w <> S v ->
  FOfree_ctx v G -> FOfree_ctx (S v) G -> FOfree_ctx w G ->
  FOfree_in (S v) P = false -> FOfree_in w P = false ->
  FOtms_avoid [L] v (S (S v)) -> FOtms_avoid [L] w (S w) -> FOtms_avoid [L] 400 500 ->
  FOPrH n G (FOBallC v (FOSucc L) P).
Proof.
  intros n G v L P w H1 H2 Hok Hv1 Hv2 Hw1 Hwv HwSv HGv HGSv HGw FSP FwP Hav1 Hav2 Hav3.
  rewrite FOBallC_ltv. apply FOPrH_all_intro; [exact HGv|]. apply FOPrH_intro.
  refine (FOPrH_ex_elim _ _ (S v) (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) (FOSucc L))
            _ _ FSP _ _); [free_ctx | unfold FOltv; apply FOPrH_last |].
  apply (FOPrH_cases_zs _ _ (FOVar (S v)) w P); [lia | fr_tm | free_ctx | exact FwP | fr_tm | |].
  - lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (Z : FOPrH n Gc (FOEq (FOVar (S v)) FOZero)) by wk_in;
      assert (H2w : FOPrH n Gc (FOsubst_f v L P)) by wk H2;
      assert (E2 : FOPrH n Gc (FOEq L (FOVar v)))
    end.
    { pose proof (FOPrH_eq_sym _ _ _ _ Z) as Z'.
      fo_lin [(.S .0, #v .+ .S (FOVar (S v)), .S L); (.S .0, .0, FOVar (S v))]; exact Z'. }
    pose proof (FOPrH_leibniz _ _ v L (FOVar v) P Hok (FOsubst_ok_var_self P v) E2 H2w) as E3.
    rewrite FOsubst_f_id in E3. exact E3.
  - lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (E1 : FOPrH n Gc (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) (FOSucc L)))
        by wk_in;
      assert (H1w : FOPrH n Gc (FOBallC v L P)) by wk H1
    end.
    pose proof (FOPrH_eq_sym _ _ _ _ E1) as E1'.
    rewrite FOBallC_ltv in H1w. apply FOPrH_all_same in H1w.
    refine (FOPrH_mp _ _ _ _ H1w _).
    unfold FOltv. apply (FOPrH_ex_intro _ _ (S v) (FOVar w)); [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_succ, FOsubst_t_var_eq',
      FOsubst_t_var_ne by lia.
    rewrite (FOsubst_t_not_in L (S v) _ (Hav1 L ltac:(in_list) (S v) ltac:(lia) ltac:(lia))).
    fo_lin [(.S .0, .S L, #v .+ .S (FOVar (S v))); (.S .0, FOVar (S v), .S (FOVar w))];
      exact E1'.
Qed.

(** ** A table extended by one row.

    [FOTEXT T T' tg a1 a2 a3 r]: every column of [T'] extends the
    column of [T] by one entry, the entries forming the row
    [(tg, a1, a2, a3, r)]; the length of [T'] is one more. *)

Definition FOTEXT (T T' : FOtab) (tg a1 a2 a3 r : FOTerm) : FOFormula :=
  FOAnd (FOEXTF (tct T) (tlen T) (tct T) (tdt T) tg (tct T') (tdt T'))
  (FOAnd (FOEXTF (tc1 T) (tlen T) (tc1 T) (td1 T) a1 (tc1 T') (td1 T'))
  (FOAnd (FOEXTF (tc2 T) (tlen T) (tc2 T) (td2 T) a2 (tc2 T') (td2 T'))
  (FOAnd (FOEXTF (tc3 T) (tlen T) (tc3 T) (td3 T) a3 (tc3 T') (td3 T'))
         (FOEXTF (tcr T) (tlen T) (tcr T) (tdr T) r (tcr T') (tdr T'))))).

Lemma FOPrH_ex468_le : forall n G b c,
  FOPrH n G (FOExists 468 (FOEq (FOPlus b (FOVar 468)) c)) ->
  FOtms_avoid [b; c] 420 500 ->
  FOPrH n G (FOle (FOSucc b) (FOSucc c)).
Proof.
  intros n G b c H Hav.
  refine (FOPrH_ctxfree n G _ _ _ H).
  refine (FOPrH_ex_elim n [FOExists 468 (FOEq (FOPlus b (FOVar 468)) c)] 468
            (FOEq (FOPlus b (FOVar 468)) c) _ _ _ _ _);
    [free_ctx | free_fm | apply FOPrH_assum; left; reflexivity |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (E : FOPrH n Gc (FOEq c (FOPlus b (FOVar 468)))) by (apply FOPrH_eq_sym; wk_in)
  end.
  unfold FOle. apply (FOPrH_ex_intro _ _ 498 (FOVar 468)); [cbn [FOsubst_ok]; reflexivity|].
  rewrite FOsubst_f_eq, FOsubst_t_plus, !FOsubst_t_succ, FOsubst_t_var_eq'. subst_avoid_h Hav.
  fo_lin [(.S .0, c, b .+ #468)]; exact E.
Qed.

Ltac text_split H :=
  unfold FOTEXT, FOEXTF in H;
  let Xt := fresh "Xt" in let X1 := fresh "X1" in let X2 := fresh "X2" in
  let X3 := fresh "X3" in let Xr := fresh "Xr" in
  pose proof (FOPrH_and_l _ _ _ _ H) as Xt;
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ H)) as X1;
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ H))) as X2;
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ H)))) as X3;
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ H)))) as Xr.

Lemma FOPrH_text_mono : forall n G T T' tg a1 a2 a3 r,
  FOPrH n G (FOTEXT T T' tg a1 a2 a3 r) -> tlen T' = FOSucc (tlen T) ->
  FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r]) 420 500 ->
  FOTabMono n G T T'.
Proof.
  intros n G T T' tg a1 a2 a3 r H Hlen HG Hav.
  text_split H.
  split.
  - unfold FOTabAgree. apply FOPrH_incl_agr;
      [ exact (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ Xt))
      | exact (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ X1))
      | exact (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ X2))
      | exact (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ X3))
      | exact (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ Xr))
      | | exact HG | avoid_tms ].
    rewrite Hlen. unfold FOle.
    apply (FOPrH_ex_intro _ _ 498 (FOSucc FOZero)); [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_eq, FOsubst_t_plus, ?FOsubst_t_succ, FOsubst_t_var_eq'.
    subst_avoid_h Hav. apply FOPrH_ring. fo_ring.
  - repeat split; apply FOPrH_ex468_le;
      first [ exact (FOPrH_and_l _ _ _ _ Xt) | exact (FOPrH_and_l _ _ _ _ X1)
            | exact (FOPrH_and_l _ _ _ _ X2) | exact (FOPrH_and_l _ _ _ _ X3)
            | exact (FOPrH_and_l _ _ _ _ Xr) | avoid_tms ].
Qed.

Lemma FOPrH_text_lookup : forall n G B T T' tg a1 a2 a3 r,
  FOPrH n G (FOTEXT T T' tg a1 a2 a3 r) -> tlen T' = FOSucc (tlen T) ->
  2 <= B -> B + 22 <= 420 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r]) B (B + 22) ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r]) 420 500 ->
  FOPrH n G (FOlookup B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') tg a1 a2 a3 r).
Proof.
  intros n G B T T' tg a1 a2 a3 r H Hlen HB1 HB2 Hav1 Hav2.
  text_split H.
  unfold FOlookup. rewrite Hlen.
  apply (FOPrH_bex_intro_t _ _ B (FOSucc (tlen T)) (tlen T)); [lia | lia | avoid_tm | avoid_tm
    | avoid_tm | avoid_tm | | | ].
  - unfold FOle. apply (FOPrH_ex_intro _ _ 498 FOZero); [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_eq, FOsubst_t_plus, !FOsubst_t_succ, FOsubst_t_var_eq'.
    subst_avoid_h Hav2. apply FOPrH_Q_plus_zero.
  - repeat (apply FOsubst_ok_and; [apply FOsubst_ok_betaF; avoid_tm|]);
      apply FOsubst_ok_betaF; avoid_tm.
  - rewrite !FOsubst_f_and, !FOsubst_f_betaF by lia. rewrite !FOsubst_t_var_eq'.
    subst_avoid_h Hav1.
    repeat (apply FOPrH_and_intro;
            [ first [ refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
                               (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ Xt)));
                      [lia | avoid_tms | avoid_tms]
                    | refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
                               (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ X1)));
                      [lia | avoid_tms | avoid_tms]
                    | refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
                               (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ X2)));
                      [lia | avoid_tms | avoid_tms]
                    | refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
                               (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ X3)));
                      [lia | avoid_tms | avoid_tms] ] |]).
    refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
              (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ Xr)));
      [lia | avoid_tms | avoid_tms].
Qed.

(** A valid table extended by a row whose dispatch clause holds at the
    new position is valid. *)

Lemma FOPrH_tbl_extend : forall n G T T' tg a1 a2 a3 r,
  FOPrH n G (FOTBLVALID 18 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T)) ->
  FOPrH n G (FOTEXT T T' tg a1 a2 a3 r) -> tlen T' = FOSucc (tlen T) ->
  FOPrH n G (FOSTEPDISPATCH 20 (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T')
               (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') (tlen T)) ->
  FOctx_avoid G 18 122 -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r]) 18 122 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r]) 400 500 ->
  FOPrH n G (FOTBLVALID 18 (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T')).
Proof.
  intros n G T T' tg a1 a2 a3 r HV HX Hlen HD HG HG2 Hav1 Hav2.
  assert (Hav : FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r])
                  420 500) by avoid_tms.
  pose proof (FOPrH_text_mono n G T T' tg a1 a2 a3 r HX Hlen HG2 Hav) as Hm.
  text_split HX.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ Xt)) as At.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ X1)) as A1.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ X2)) as A2.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ X3)) as A3.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ Xr)) as Ar.
  clear Xt X1 X2 X3 Xr.
  unfold FOTBLVALID in *. rewrite Hlen at 1.
  apply (FOPrH_ball_snoc n G 18 (tlen T) _ 21);
    [ | | apply FOsubst_ok_STEPDISPATCH; avoid_tm | lia | lia | lia | lia | lia
      | apply HG; lia | apply HG; lia | apply HG; lia
      | free_by FOSTEPDISPATCH_free | free_by FOSTEPDISPATCH_free
      | avoid_tms | avoid_tms | avoid_tms ].
  - refine (FOPrH_mp _ _ _ _ _ HV).
    apply FOPrH_ball_mono; [apply HG; lia | apply FOPrH_imp_refl|].
    apply FOPrH_intro.
    assert (Lt : FOPrH n (G ++ [FOltv 18 (tlen T)]) (FOlt470 (FOVar 18) (tlen T))).
    { refine (FOPrH_mp _ _ _ _ (FOPrH_ltv_470 _ _ 18 (tlen T) _ _ _ _) (FOPrH_last _ _ _));
        [lia | lia | avoid_tm | avoid_tm]. }
    apply (FOtr_DISPATCH n _ 20 T T' (FOVar 18) (FOVar 18));
      [ apply FOTabMono_weak; exact Hm
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
  - rewrite FOsubst_f_STEPDISPATCH by lia. rewrite FOsubst_t_var_eq'. subst_avoid_h Hav1.
    exact HD.
Qed.
