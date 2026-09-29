From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13.
Open Scope fo_scope.

(** ** Three rows of three tables in one table.

    The tables are renamed to [130] .. [140], [151] .. [161] and
    [192] .. [202] and merged column by column at [162] .. [181]. *)

Definition FOtabM3 : FOtab :=
  mkTab (FOVar 164) (FOVar 165) (FOVar 168) (FOVar 169) (FOVar 172) (FOVar 173)
    (FOVar 176) (FOVar 177) (FOVar 180) (FOVar 181)
    (FOPlus (FOPlus (FOVar 140) (FOVar 161)) (FOVar 202)).

Lemma FOfree_in_TBLEX3_any : forall w tg a1 a2 a3 r tg' a1' a2' a3' r'
    tg'' a1'' a2'' a3'' r'',
  2 <= w ->
  FOtms_avoid [tg; a1; a2; a3; r; tg'; a1'; a2'; a3'; r'; tg''; a1''; a2''; a3''; r'']
    w (S w) ->
  FOfree_in w (FOTBLEX3 tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'') = false.
Proof.
  intros w tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'' Hw Hav.
  unfold FOTBLEX3.
  repeat match goal with
         | |- FOfree_in _ (FOExists ?y _) = false =>
             destruct (Nat.eq_dec y w) as [<-|?];
             [apply FOfree_in_ex_self | rewrite FOfree_in_FOExists_neq by assumption]
         end.
  rewrite !FOfree_in_FOAnd. repeat (apply Bool.orb_false_iff; split).
  - free_by FOTBLVALID_free.
  - free_by FOlookup_free.
  - free_by FOlookup_free.
  - free_by FOlookup_free.
Qed.

Ltac free_fm ::=
  lazymatch goal with
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
      apply FOfree_in_PATF_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOGUARDB _) = false =>
      apply FOfree_in_GUARDB_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOTEXT _ _ _ _ _ _ _) = false => unfold FOTEXT; free_fm
  | |- FOfree_in _ (FOTBLNEW _ _ _ _ _ _ _) = false => unfold FOTBLNEW; free_fm
  | |- FOfree_in _ (FOINCL _ _) = false =>
      apply FOfree_in_INCL_any; [nat_fast | avoid_tms]
  | |- _ => free_fm_core
  end.

Ltac tab_avoid ::=
  try unfold FOtabM3; try unfold FOtabM; try unfold FOtab_terms; try unfold FOtabv;
  try unfold FOtabx; try unfold FOtab0;
  cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen app]; avoid_tms.

Lemma FOPrH_tblex_join3 : forall n G tg1 a11 a21 a31 r1 tg2 a12 a22 a32 r2
    tg3 a13 a23 a33 r3,
  FOctx_avoid G 2 500 ->
  FOtms_avoid [tg1; a11; a21; a31; r1; tg2; a12; a22; a32; r2; tg3; a13; a23; a33; r3]
    2 500 ->
  FOPrH n G (FOTBLEX tg1 a11 a21 a31 r1) -> FOPrH n G (FOTBLEX tg2 a12 a22 a32 r2) ->
  FOPrH n G (FOTBLEX tg3 a13 a23 a33 r3) ->
  FOPrH n G (FOTBLEX3 tg1 a11 a21 a31 r1 tg2 a12 a22 a32 r2 tg3 a13 a23 a33 r3).
Proof.
  intros n G tg1 a11 a21 a31 r1 tg2 a12 a22 a32 r2 tg3 a13 a23 a33 r3 HG Hav HE1 HE2 HE3.
  refine (FOPrH_mp _ _ _ _ (FOPrH_tblex_elim n G tg1 a11 a21 a31 r1 130 _ _ _ _ _ _ _ _) HE1);
    [lia | lia | tab_side | tab_side | tab_side | tab_side |].
  refine (FOPrH_mp _ _ _ _ (FOPrH_tblex_elim n _ tg2 a12 a22 a32 r2 151 _ _ _ _ _ _ _ _)
            (FOPrH_weak_app _ _ _ _ HE2));
    [lia | lia | tab_side | tab_side | tab_side | tab_side |].
  refine (FOPrH_mp _ _ _ _ (FOPrH_tblex_elim n _ tg3 a13 a23 a33 r3 192 _ _ _ _ _ _ _ _)
            (FOPrH_weak_app _ _ _ _ (FOPrH_weak_app _ _ _ _ HE3)));
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
                   tg2 a12 a22 a32 r2))) by wk_in;
    assert (K3 : FOPrH n Gc (FOAnd (FOTBLVALID 18 (FOVar 192) (FOVar 193) (FOVar 194)
                   (FOVar 195) (FOVar 196) (FOVar 197) (FOVar 198) (FOVar 199) (FOVar 200)
                   (FOVar 201) (FOVar 202))
                 (FOlookup 28 (FOVar 192) (FOVar 193) (FOVar 194) (FOVar 195) (FOVar 196)
                   (FOVar 197) (FOVar 198) (FOVar 199) (FOVar 200) (FOVar 201) (FOVar 202)
                   tg3 a13 a23 a33 r3))) by wk_in
  end.
  apply (FOPrH_merge3_elim n _ (FOVar 130) (FOVar 131) (FOVar 140) (FOVar 151) (FOVar 152)
           (FOVar 161) (FOVar 192) (FOVar 193) (FOVar 202) 162 163 164 165); [tab_side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 132) (FOVar 133) (FOVar 140) (FOVar 153) (FOVar 154)
           (FOVar 161) (FOVar 194) (FOVar 195) (FOVar 202) 166 167 168 169); [tab_side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 134) (FOVar 135) (FOVar 140) (FOVar 155) (FOVar 156)
           (FOVar 161) (FOVar 196) (FOVar 197) (FOVar 202) 170 171 172 173); [tab_side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 136) (FOVar 137) (FOVar 140) (FOVar 157) (FOVar 158)
           (FOVar 161) (FOVar 198) (FOVar 199) (FOVar 202) 174 175 176 177); [tab_side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 138) (FOVar 139) (FOVar 140) (FOVar 159) (FOVar 160)
           (FOVar 161) (FOVar 200) (FOVar 201) (FOVar 202) 178 179 180 181); [tab_side.. |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (HM : FOPrH n Gc (FOTABM3 (FOtabv 130) (FOtabv 151) (FOtabv 192) FOtabM3));
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
                   tg2 a12 a22 a32 r2))) by wk K2;
    assert (K3' : FOPrH n Gc (FOAnd (FOTBLVALID 18 (FOVar 192) (FOVar 193) (FOVar 194)
                   (FOVar 195) (FOVar 196) (FOVar 197) (FOVar 198) (FOVar 199) (FOVar 200)
                   (FOVar 201) (FOVar 202))
                 (FOlookup 28 (FOVar 192) (FOVar 193) (FOVar 194) (FOVar 195) (FOVar 196)
                   (FOVar 197) (FOVar 198) (FOVar 199) (FOVar 200) (FOVar 201) (FOVar 202)
                   tg3 a13 a23 a33 r3))) by wk K3
  end.
  clear K1 K2 K3.
  assert (HavT : FOtms_avoid (FOtab_terms (FOtabv 130) ++ FOtab_terms (FOtabv 151) ++
                              FOtab_terms (FOtabv 192) ++ FOtab_terms FOtabM3) 420 500)
    by (unfold FOtabM3; tab_side).
  destruct (FOPrH_tabm3_mono n _ _ _ _ _ HM eq_refl HC2 HavT) as (Hm1 & Hm2 & Hm3).
  pose proof (FOPrH_tblvalid_merge n _ (FOtabv 130) (FOtabv 151) (FOtabv 192) FOtabM3 390 391
                HM eq_refl (FOPrH_and_l _ _ _ _ K1') (FOPrH_and_l _ _ _ _ K2')
                (FOPrH_and_l _ _ _ _ K3')
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(tab_side) ltac:(tab_side) HC1 HC2
                ltac:(unfold FOtabM3; tab_side) ltac:(unfold FOtabM3; tab_side)
                ltac:(unfold FOtabM3; tab_side) ltac:(unfold FOtabM3; tab_side)) as HVM.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n _ 28 (FOtabv 130) FOtabM3 tg1 a11 a21 a31 r1
                Hm1 ltac:(lia) ltac:(tab_side) HC2 ltac:(unfold FOtabM3; tab_side)
                ltac:(unfold FOtabM3; tab_side))
                (FOPrH_and_r _ _ _ _ K1')) as L1.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n _ 28 (FOtabv 151) FOtabM3 tg2 a12 a22 a32 r2
                Hm2 ltac:(lia) ltac:(tab_side) HC2 ltac:(unfold FOtabM3; tab_side)
                ltac:(unfold FOtabM3; tab_side))
                (FOPrH_and_r _ _ _ _ K2')) as L2.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n _ 28 (FOtabv 192) FOtabM3 tg3 a13 a23 a33 r3
                Hm3 ltac:(lia) ltac:(tab_side) HC2 ltac:(unfold FOtabM3; tab_side)
                ltac:(unfold FOtabM3; tab_side))
                (FOPrH_and_r _ _ _ _ K3')) as L3.
  apply (FOPrH_tblex3_intro n _ FOtabM3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HVM L1 L2 L3).
  unfold FOtabM3. tab_side.
Qed.
