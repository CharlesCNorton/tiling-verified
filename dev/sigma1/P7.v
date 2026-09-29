From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6.
Open Scope fo_scope.

(** ** The empty table. *)

Definition FOtab0 : FOtab :=
  mkTab FOZero FOZero FOZero FOZero FOZero FOZero FOZero FOZero FOZero FOZero FOZero.

Lemma FOPrH_tbl_empty : forall n G,
  FOfree_ctx 18 G -> FOfree_ctx 19 G ->
  FOPrH n G (FOTBLVALID 18 (tct FOtab0) (tdt FOtab0) (tc1 FOtab0) (td1 FOtab0) (tc2 FOtab0)
               (td2 FOtab0) (tc3 FOtab0) (td3 FOtab0) (tcr FOtab0) (tdr FOtab0)
               (tlen FOtab0)).
Proof.
  intros n G HG HG'. cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen FOtab0].
  unfold FOTBLVALID. rewrite FOBallC_ltv. apply FOPrH_all_intro; [exact HG|].
  apply FOPrH_intro. apply FOPrH_efq. unfold FOltv.
  refine (FOPrH_ex_elim _ _ 19 (FOEq (FOPlus (FOVar 18) (FOSucc (FOVar 19))) FOZero)
            _ _ _ _ _); [| reflexivity | apply FOPrH_last |].
  { apply FOfree_ctx_app_inv; [exact HG'|].
    apply FOfree_ctx_cons; [|apply FOfree_ctx_nil]. apply FOfree_in_ex_self. }
  apply (FOPrH_Q_succ_nonzero _ _ (FOPlus (FOVar 18) (FOVar 19))).
  apply (FOPrH_eq_trans _ _ _ (FOPlus (FOVar 18) (FOSucc (FOVar 19))));
    [apply FOPrH_eq_sym; apply FOPrH_Q_plus_succ | apply FOPrH_last].
Qed.

Lemma FOPrH_cpair_one : forall n G, FOPrH n G (FOcpairF (FOnumeral 1) FOZero (FOnumeral 1)).
Proof. intros n G. unfold FOcpairF. cbn [FOnumeral]. apply FOPrH_ring. fo_ring. Qed.

(** ** Rows of the numerals.

    For each numeral code, some valid table has its tag-[5] row, its
    tag-[2] row for every substitution, and its tag-[0] row for every
    variable; the successor rows extend a table holding the row of the
    predecessor. *)

Lemma FOfree_in_TBLEX_any : forall w tg a1 a2 a3 r,
  2 <= w -> FOtms_avoid [tg; a1; a2; a3; r] w (S w) ->
  FOfree_in w (FOTBLEX tg a1 a2 a3 r) = false.
Proof.
  intros w tg a1 a2 a3 r Hw Hav. unfold FOTBLEX.
  repeat match goal with
         | |- FOfree_in _ (FOExists ?y _) = false =>
             destruct (Nat.eq_dec y w) as [<-|?];
             [apply FOfree_in_ex_self | rewrite FOfree_in_FOExists_neq by assumption]
         end.
  rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
  - free_by FOTBLVALID_free.
  - free_by FOlookup_free.
Qed.

Ltac free_fm ::=
  lazymatch goal with
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
  try unfold FOtab_terms; try unfold FOtabv; try unfold FOtabx; try unfold FOtab0;
  cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen app]; avoid_tms.

Ltac tab_side :=
  lazymatch goal with
  | |- FOctx_avoid _ _ _ => ctx_list
  | |- FOtms_avoid _ _ _ => tab_avoid
  | |- FOfree_ctx _ _ => free_ctx
  | |- FOfree_in _ _ = false => free_fm
  | |- forall w, _ -> _ -> FOfree_in w _ = false =>
      let w := fresh "w" in intros w ? ?; free_fm
  | |- _ => nat_fast
  end.

Lemma FOPrH_tab_base : forall n G tg a1 a2 a3 r,
  FOctx_avoid G 2 500 -> FOtms_avoid [tg; a1; a2; a3; r] 2 500 ->
  FOPrH n G (FODISPCASES (FOVar 141) (FOVar 142) (FOVar 143) (FOVar 144) (FOVar 145)
               (FOVar 146) (FOVar 147) (FOVar 148) (FOVar 149) (FOVar 150)
               (FOSucc FOZero) tg a1 a2 a3 r) ->
  FOPrH n G (FOTBLEX tg a1 a2 a3 r).
Proof.
  intros n G tg a1 a2 a3 r HG Hav HD.
  apply (FOPrH_row_new n G FOtab0 tg a1 a2 a3 r 141 _);
    [ apply FOPrH_tbl_empty; apply HG; lia
    | intros G' Hinc _ _ _; exact (FOPrH_weaken n G G' _ Hinc HD)
    | tab_side .. |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (N : FOPrH n Gc (FOTBLNEW FOtab0 (FOtabx 141 (FOSucc (tlen FOtab0)))
                              tg a1 a2 a3 r)) by apply FOPrH_last
  end.
  unfold FOTBLNEW in N.
  apply (FOPrH_tblex_intro n _ (FOtabx 141 (FOSucc (tlen FOtab0))) tg a1 a2 a3 r
           (FOPrH_and_l _ _ _ _ N) (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ N))).
  tab_side.
Qed.

Lemma FOPrH_tab_step : forall n G tg a1 a2 a3 r tg' a1' a2' a3' r',
  FOctx_avoid G 2 500 ->
  FOtms_avoid [tg; a1; a2; a3; r; tg'; a1'; a2'; a3'; r'] 2 500 ->
  FOPrH n G (FOTBLEX tg a1 a2 a3 r) ->
  (forall G', (forall X, In X G -> In X G') ->
     FOPrH n G' (FOlookup 28 (FOVar 141) (FOVar 142) (FOVar 143) (FOVar 144) (FOVar 145)
                   (FOVar 146) (FOVar 147) (FOVar 148) (FOVar 149) (FOVar 150)
                   (FOSucc (FOVar 140)) tg a1 a2 a3 r) ->
     FOPrH n G' (FODISPCASES (FOVar 141) (FOVar 142) (FOVar 143) (FOVar 144) (FOVar 145)
                   (FOVar 146) (FOVar 147) (FOVar 148) (FOVar 149) (FOVar 150)
                   (FOSucc (FOVar 140)) tg' a1' a2' a3' r')) ->
  FOPrH n G (FOTBLEX tg' a1' a2' a3' r').
Proof.
  intros n G tg a1 a2 a3 r tg' a1' a2' a3' r' HG Hav HE HP.
  refine (FOPrH_mp _ _ _ _ (FOPrH_tblex_elim n G tg a1 a2 a3 r 130 _ _ _ _ _ _ _ _) HE);
    [lia | lia | tab_side | tab_side | tab_side | tab_side |].
  lazymatch goal with |- FOPrH _ ?G1 _ =>
    assert (K : FOPrH n G1 (FOAnd (FOTBLVALID 18 (tct (FOtabv 130)) (tdt (FOtabv 130))
                   (tc1 (FOtabv 130)) (td1 (FOtabv 130)) (tc2 (FOtabv 130)) (td2 (FOtabv 130))
                   (tc3 (FOtabv 130)) (td3 (FOtabv 130)) (tcr (FOtabv 130)) (tdr (FOtabv 130))
                   (tlen (FOtabv 130)))
                 (FOlookup 28 (tct (FOtabv 130)) (tdt (FOtabv 130))
                   (tc1 (FOtabv 130)) (td1 (FOtabv 130)) (tc2 (FOtabv 130)) (td2 (FOtabv 130))
                   (tc3 (FOtabv 130)) (td3 (FOtabv 130)) (tcr (FOtabv 130)) (tdr (FOtabv 130))
                   (tlen (FOtabv 130)) tg a1 a2 a3 r))) by apply FOPrH_last;
    assert (HGinc : forall X, In X G -> In X G1)
      by (intros X HX; apply in_or_app; left; exact HX)
  end.
  apply (FOPrH_row_new n _ (FOtabv 130) tg' a1' a2' a3' r' 141 _);
    [ exact (FOPrH_and_l _ _ _ _ K)
    | intros G' Hinc HA1 HA2 Hm;
      refine (HP G' (fun X HX => Hinc X (HGinc X HX)) _);
      refine (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n G' 28 (FOtabv 130) _ tg a1 a2 a3 r Hm
                                  ltac:(lia) _ _ _ _)
                (FOPrH_weaken n _ G' _ Hinc (FOPrH_and_r _ _ _ _ K)));
      [ intros w ? ?; apply HA1; lia
      | exact HA2
      | tab_side | tab_side ]
    | tab_side .. |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (N : FOPrH n Gc (FOTBLNEW (FOtabv 130) (FOtabx 141 (FOSucc (tlen (FOtabv 130))))
                              tg' a1' a2' a3' r')) by apply FOPrH_last
  end.
  unfold FOTBLNEW in N.
  apply (FOPrH_tblex_intro n _ (FOtabx 141 (FOSucc (tlen (FOtabv 130)))) tg' a1' a2' a3' r'
           (FOPrH_and_l _ _ _ _ N) (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ N))).
  tab_side.
Qed.
