From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8.
Open Scope fo_scope.

(** ** A row from rows of two tables.

    The two tables are renamed to [130] .. [140] and [151] .. [161],
    merged column by column at [162] .. [181], and the merged table is
    extended by the new row at [182] .. [191]. *)

Definition FOtabM : FOtab :=
  mkTab (FOVar 164) (FOVar 165) (FOVar 168) (FOVar 169) (FOVar 172) (FOVar 173)
    (FOVar 176) (FOVar 177) (FOVar 180) (FOVar 181)
    (FOPlus (FOPlus (FOVar 140) (FOVar 161)) FOZero).

Ltac tab_avoid ::=
  try unfold FOtabM; try unfold FOtab_terms; try unfold FOtabv; try unfold FOtabx;
  try unfold FOtab0; cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen app]; avoid_tms.

Lemma FOPrH_tblex_join : forall n G tg1 a11 a21 a31 r1 tg2 a12 a22 a32 r2 tg a1 a2 a3 r,
  FOctx_avoid G 2 500 ->
  FOtms_avoid [tg1; a11; a21; a31; r1; tg2; a12; a22; a32; r2; tg; a1; a2; a3; r] 2 500 ->
  FOPrH n G (FOTBLEX tg1 a11 a21 a31 r1) -> FOPrH n G (FOTBLEX tg2 a12 a22 a32 r2) ->
  (forall G', (forall X, In X G -> In X G') ->
     FOPrH n G' (FOlookup 28 (FOVar 182) (FOVar 183) (FOVar 184) (FOVar 185) (FOVar 186)
                   (FOVar 187) (FOVar 188) (FOVar 189) (FOVar 190) (FOVar 191)
                   (FOSucc (tlen FOtabM)) tg1 a11 a21 a31 r1) ->
     FOPrH n G' (FOlookup 28 (FOVar 182) (FOVar 183) (FOVar 184) (FOVar 185) (FOVar 186)
                   (FOVar 187) (FOVar 188) (FOVar 189) (FOVar 190) (FOVar 191)
                   (FOSucc (tlen FOtabM)) tg2 a12 a22 a32 r2) ->
     FOPrH n G' (FODISPCASES (FOVar 182) (FOVar 183) (FOVar 184) (FOVar 185) (FOVar 186)
                   (FOVar 187) (FOVar 188) (FOVar 189) (FOVar 190) (FOVar 191)
                   (FOSucc (tlen FOtabM)) tg a1 a2 a3 r)) ->
  FOPrH n G (FOTBLEX tg a1 a2 a3 r).
Proof.
  intros n G tg1 a11 a21 a31 r1 tg2 a12 a22 a32 r2 tg a1 a2 a3 r HG Hav HE1 HE2 HP.
  refine (FOPrH_mp _ _ _ _ (FOPrH_tblex_elim n G tg1 a11 a21 a31 r1 130 _ _ _ _ _ _ _ _) HE1);
    [lia | lia | tab_side | tab_side | tab_side | tab_side |].
  refine (FOPrH_mp _ _ _ _ (FOPrH_tblex_elim n _ tg2 a12 a22 a32 r2 151 _ _ _ _ _ _ _ _)
            (FOPrH_weak_app _ _ _ _ HE2));
    [lia | lia | tab_side | tab_side | tab_side | tab_side |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (K1 : FOPrH n Gc (FOAnd (FOTBLVALID 18 (FOVar 130) (FOVar 131) (FOVar 132)
                   (FOVar 133) (FOVar 134) (FOVar 135) (FOVar 136) (FOVar 137) (FOVar 138)
                   (FOVar 139) (FOVar 140))
                 (FOlookup 28 (FOVar 130) (FOVar 131) (FOVar 132) (FOVar 133) (FOVar 134)
                   (FOVar 135) (FOVar 136) (FOVar 137) (FOVar 138) (FOVar 139) (FOVar 140)
                   tg1 a11 a21 a31 r1))) by wk_in;
    assert (K2 : FOPrH n Gc (FOAnd (FOTBLVALID 18 (FOVar 151) (FOVar 152) (FOVar 153)
                   (FOVar 154) (FOVar 155) (FOVar 156) (FOVar 157) (FOVar 158) (FOVar 159)
                   (FOVar 160) (FOVar 161))
                 (FOlookup 28 (FOVar 151) (FOVar 152) (FOVar 153) (FOVar 154) (FOVar 155)
                   (FOVar 156) (FOVar 157) (FOVar 158) (FOVar 159) (FOVar 160) (FOVar 161)
                   tg2 a12 a22 a32 r2))) by wk_in
  end.
  apply (FOPrH_merge3_elim n _ (FOVar 130) (FOVar 131) (FOVar 140) (FOVar 151) (FOVar 152)
           (FOVar 161) FOZero FOZero FOZero 162 163 164 165); [tab_side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 132) (FOVar 133) (FOVar 140) (FOVar 153) (FOVar 154)
           (FOVar 161) FOZero FOZero FOZero 166 167 168 169); [tab_side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 134) (FOVar 135) (FOVar 140) (FOVar 155) (FOVar 156)
           (FOVar 161) FOZero FOZero FOZero 170 171 172 173); [tab_side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 136) (FOVar 137) (FOVar 140) (FOVar 157) (FOVar 158)
           (FOVar 161) FOZero FOZero FOZero 174 175 176 177); [tab_side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 138) (FOVar 139) (FOVar 140) (FOVar 159) (FOVar 160)
           (FOVar 161) FOZero FOZero FOZero 178 179 180 181); [tab_side.. |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (HM : FOPrH n Gc (FOTABM3 (FOtabv 130) (FOtabv 151) FOtab0 FOtabM));
    [ unfold FOTABM3; apply FOPrH_and_intro; [wk_in|]; apply FOPrH_and_intro; [wk_in|];
      apply FOPrH_and_intro; [wk_in|]; apply FOPrH_and_intro; wk_in |];
    assert (HC1 : FOctx_avoid Gc 18 122) by tab_side;
    assert (HC2 : FOctx_avoid Gc 420 500) by tab_side;
    assert (K1' : FOPrH n Gc (FOAnd (FOTBLVALID 18 (FOVar 130) (FOVar 131) (FOVar 132)
                   (FOVar 133) (FOVar 134) (FOVar 135) (FOVar 136) (FOVar 137) (FOVar 138)
                   (FOVar 139) (FOVar 140))
                 (FOlookup 28 (FOVar 130) (FOVar 131) (FOVar 132) (FOVar 133) (FOVar 134)
                   (FOVar 135) (FOVar 136) (FOVar 137) (FOVar 138) (FOVar 139) (FOVar 140)
                   tg1 a11 a21 a31 r1))) by wk K1;
    assert (K2' : FOPrH n Gc (FOAnd (FOTBLVALID 18 (FOVar 151) (FOVar 152) (FOVar 153)
                   (FOVar 154) (FOVar 155) (FOVar 156) (FOVar 157) (FOVar 158) (FOVar 159)
                   (FOVar 160) (FOVar 161))
                 (FOlookup 28 (FOVar 151) (FOVar 152) (FOVar 153) (FOVar 154) (FOVar 155)
                   (FOVar 156) (FOVar 157) (FOVar 158) (FOVar 159) (FOVar 160) (FOVar 161)
                   tg2 a12 a22 a32 r2))) by wk K2
  end.
  clear K1 K2.
  assert (HavT : FOtms_avoid (FOtab_terms (FOtabv 130) ++ FOtab_terms (FOtabv 151) ++
                              FOtab_terms FOtab0 ++ FOtab_terms FOtabM) 420 500)
    by (unfold FOtabM; tab_side).
  destruct (FOPrH_tabm3_mono n _ _ _ _ _ HM eq_refl HC2 HavT) as (Hm1 & Hm2 & _).
  pose proof (FOPrH_tblvalid_merge n _ (FOtabv 130) (FOtabv 151) FOtab0 FOtabM 390 391 HM
                eq_refl (FOPrH_and_l _ _ _ _ K1') (FOPrH_and_l _ _ _ _ K2')
                (FOPrH_tbl_empty n _ ltac:(tab_side) ltac:(tab_side))
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(tab_side) ltac:(tab_side) HC1 HC2
                ltac:(unfold FOtabM; tab_side) ltac:(unfold FOtabM; tab_side)
                ltac:(unfold FOtabM; tab_side) ltac:(unfold FOtabM; tab_side)) as HVM.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n _ 28 (FOtabv 130) FOtabM tg1 a11 a21 a31 r1
                Hm1 ltac:(lia) ltac:(tab_side) HC2 ltac:(unfold FOtabM; tab_side)
                ltac:(unfold FOtabM; tab_side))
                (FOPrH_and_r _ _ _ _ K1')) as L1.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n _ 28 (FOtabv 151) FOtabM tg2 a12 a22 a32 r2
                Hm2 ltac:(lia) ltac:(tab_side) HC2 ltac:(unfold FOtabM; tab_side)
                ltac:(unfold FOtabM; tab_side))
                (FOPrH_and_r _ _ _ _ K2')) as L2.
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (HGinc : forall X, In X G -> In X Gc)
      by (intros X HX; repeat (apply in_or_app; left); exact HX)
  end.
  apply (FOPrH_row_new n _ FOtabM tg a1 a2 a3 r 182 _);
    [ exact HVM
    | intros G' Hinc HA1 HA2 Hm;
      apply (HP G' (fun X HX => Hinc X (HGinc X HX)));
      [ refine (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n G' 28 FOtabM _ tg1 a11 a21 a31 r1 Hm
                                    ltac:(lia) _ HA2 _ _) (FOPrH_weaken n _ G' _ Hinc L1));
        [intros w ? ?; apply HA1; lia | unfold FOtabM; tab_side | unfold FOtabM; tab_side]
      | refine (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n G' 28 FOtabM _ tg2 a12 a22 a32 r2 Hm
                                    ltac:(lia) _ HA2 _ _) (FOPrH_weaken n _ G' _ Hinc L2));
        [intros w ? ?; apply HA1; lia | unfold FOtabM; tab_side | unfold FOtabM; tab_side] ]
    | exact HC1 | exact HC2 | tab_side | lia | lia | tab_side
    | unfold FOtabM; tab_side | unfold FOtabM; tab_side | unfold FOtabM; tab_side |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (N : FOPrH n Gc (FOTBLNEW FOtabM (FOtabx 182 (FOSucc (tlen FOtabM)))
                              tg a1 a2 a3 r)) by apply FOPrH_last
  end.
  unfold FOTBLNEW in N.
  apply (FOPrH_tblex_intro n _ (FOtabx 182 (FOSucc (tlen FOtabM))) tg a1 a2 a3 r
           (FOPrH_and_l _ _ _ _ N) (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ N))).
  unfold FOtabM. tab_side.
Qed.
