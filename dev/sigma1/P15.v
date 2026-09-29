From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14.
Open Scope fo_scope.

(** ** One-line derivations whose check reads the table.

    The table holds the guard row of [d] and two further rows; the
    justification code pairs the tag with the payload [pl]. *)

Lemma FOPrH_one_line3 : forall n G cores d tgn pl r0 tg' a1' a2' a3' r'
    tg'' a1'' a2'' a3'' r'',
  FOctx_avoid G 2 500 ->
  FOtms_avoid [d; pl; r0; tg'; a1'; a2'; a3'; r'; tg''; a1''; a2''; a3''; r''] 2 500 ->
  FOPrH n G (FOTBLEX3 (FOnumeral 3) (FOSucc d) FOZero d r0 tg' a1' a2' a3' r'
               tg'' a1'' a2'' a3'' r'') ->
  (forall G', (forall X, In X G -> In X G') ->
     FOPrH n G' (FOlookup 28 (FOVar 260) (FOVar 261) (FOVar 262) (FOVar 263) (FOVar 264)
                   (FOVar 265) (FOVar 266) (FOVar 267) (FOVar 268) (FOVar 269) (FOVar 270)
                   tg' a1' a2' a3' r') ->
     FOPrH n G' (FOlookup 28 (FOVar 260) (FOVar 261) (FOVar 262) (FOVar 263) (FOVar 264)
                   (FOVar 265) (FOVar 266) (FOVar 267) (FOVar 268) (FOVar 269) (FOVar 270)
                   tg'' a1'' a2'' a3'' r'') ->
     FOPrH n G' (FOJDISJ 20 cores (FOVar 260) (FOVar 261) (FOVar 262) (FOVar 263)
                   (FOVar 264) (FOVar 265) (FOVar 266) (FOVar 267) (FOVar 268) (FOVar 269)
                   (FOVar 270) d d FOZero d (FOnumeral tgn) pl)) ->
  FOPrH n G (FOPRMATx cores d).
Proof.
  intros n G cores d tgn pl r0 tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'' HG Hd HE HJ.
  refine (FOPrH_mp _ _ _ _ _ HE).
  apply (FOPrH_tblex3_elim n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 260); [lia | lia
    | intros w H1 H2; apply HG; lia | intros w H1 H2; free_fm | avoid_tms | avoid_tms |].
  cbn [Nat.add].
  lazymatch goal with |- FOPrH _ (_ ++ [?X]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G X)) as VT;
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_last n G X))) as LK1;
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _
                  (FOPrH_and_r _ _ _ _ (FOPrH_last n G X)))) as LK2;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                  (FOPrH_and_r _ _ _ _ (FOPrH_last n G X)))) as LK3
  end.
  apply (FOPrH_cpair_elim n _ (FOnumeral tgn) pl 280); [ctx_list | avoid_tms | lia | lia
    | free_ctx | free_fm | avoid_tms |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (CP : FOPrH n Gc (FOcpairF (FOnumeral tgn) pl (FOVar 280))) by apply FOPrH_last;
    assert (Hinc : forall X, In X G -> In X Gc)
      by (intros X HX; repeat (apply in_or_app; left); exact HX);
    pose proof (HJ Gc Hinc (FOPrH_weak_app _ _ _ _ LK2) (FOPrH_weak_app _ _ _ _ LK3)) as HJ'
  end.
  destruct (FOPrH_cpair_le_cf n _ (FOnumeral tgn) pl (FOVar 280) ltac:(avoid_tms) CP)
    as [Ltg Lpl].
  apply (FOPrH_PRMAT_intro n _ cores d (FOVar 260) (FOVar 261) (FOVar 262) (FOVar 263)
           (FOVar 264) (FOVar 265) (FOVar 266) (FOVar 267) (FOVar 268) (FOVar 269)
           (FOVar 270) d d (FOVar 280) (FOVar 280) (FOSucc FOZero));
    [avoid_tms | avoid_tms |].
  unfold FOPRDERp. cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen].
  apply FOPrH_and_intro; [wk VT|].
  apply FOPrH_and_intro.
  { apply (FOPrH_bex_intro_t _ _ 18 (FOSucc FOZero) FOZero); [lia | lia | avoid_tm
      | avoid_tm | avoid_tm | avoid_tm | | ok0 |].
    - apply FOPrH_le_refl. avoid_tm.
    - autorewrite with fosubst. subst_avoid_h Hd.
      apply FOPrH_and_intro; [apply FOPrH_ring; fo_ring|].
      apply FOPrH_beta_self0; [lia | lia | avoid_tms | avoid_tms]. }
  apply FOPrH_and_intro.
  - apply (FOPrH_ball_one _ _ 18 _ 250); [| ok0 | lia | lia | lia | lia | lia
      | free_ctx | free_ctx | free_ctx | free_fm | free_fm].
    autorewrite with fosubst. subst_avoid_h Hd.
    apply (FOPrH_JUSTCK_intro_t _ _ 20 cores _ _ _ _ _ _ _ _ _ _ _ d d
             (FOVar 280) (FOVar 280) FOZero d (FOVar 280));
      [lia | lia | avoid_tms | avoid_tms | avoid_tms | avoid_tms | | | | |].
    + apply FOPrH_le_refl. avoid_tm.
    + apply FOPrH_beta_self0; [lia | lia | avoid_tms | avoid_tms].
    + apply FOPrH_le_refl. avoid_tm.
    + apply FOPrH_beta_self0; [lia | lia | avoid_tms | avoid_tms].
    + apply (FOPrH_CHK_intro_t _ _ 20 cores _ _ _ _ _ _ _ _ _ _ _ d d FOZero d
               (FOVar 280) (FOnumeral tgn) pl);
        [lia | avoid_tms | avoid_tms | avoid_tms | avoid_tms | | | |].
      * apply FOPrH_le_succ_of_le; [exact Ltg | avoid_tms].
      * apply FOPrH_le_succ_of_le; [exact Lpl | avoid_tms].
      * exact CP.
      * exact HJ'.
  - apply (FOPrH_ball_one _ _ 18 _ 250); [| ok0 | lia | lia | lia | lia | lia
      | free_ctx | free_ctx | free_ctx | free_fm | free_fm].
    autorewrite with fosubst. subst_avoid_h Hd.
    apply (FOPrH_GUARDC_intro_t _ _ 20 (FOtabv 260) d d FOZero d r0);
      [lia | tab_avoid | avoid_tms | avoid_tms | tab_avoid | | | |].
    + apply FOPrH_le_refl. avoid_tm.
    + apply FOPrH_beta_self0; [lia | lia | avoid_tms | avoid_tms].
    + cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen FOtabv Nat.add].
      apply FOPrH_le_succ_of_le; [|avoid_tms].
      apply (FOPrH_lookup_res_le _ _ 28 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ LK1));
        [lia | lia | ctx_list | avoid_tms | avoid_tms].
    + cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen FOtabv Nat.add].
      exact (FOPrH_weak_app _ _ _ _ LK1).
Qed.
