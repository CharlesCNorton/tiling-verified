From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39.
Open Scope fo_scope.

(** ** Numeral codes: existence, uniqueness, inversion, successor. *)

Lemma FOsubst_ok_NUMR : forall x s a m, 13 <= x ->
  FOtms_avoid [s] 2 50 -> FOtms_avoid [s] 802 805 ->
  FOsubst_ok x s (FONUMR a m) = true.
Proof.
  intros x s a m Hx H1 H2. unfold FONUMR.
  apply FOsubst_ok_and; [apply FOsubst_ok_TBLEX; [lia | avoid_tm]|].
  apply FOsubst_ok_and.
  - apply FOsubst_ok_all; [fr_tm|]. apply FOsubst_ok_all; [fr_tm|].
    apply FOsubst_ok_TBLEX; [lia | avoid_tm].
  - apply FOsubst_ok_all; [fr_tm|]. apply FOsubst_ok_TBLEX; [lia | avoid_tm].
Qed.

Lemma FOPrH_numr_exists : forall n G t w C,
  FOtms_avoid [t] 2 1000 -> 1000 <= w -> FOfree_ctx w G -> FOfree_in w C = false ->
  FOtms_avoid [t] w (S w) ->
  FOPrH n (G ++ [FONUMR t (FOVar w)]) C -> FOPrH n G C.
Proof.
  intros n G t w C Ht Hw HGw HCw Htw H0.
  pose proof (FOPrH_thm n G _ (FOPr_numr n)) as H.
  apply (FOPrH_inst n G 800 t) in H;
    [| apply FOsubst_ok_ex; [fr_tm | apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]]].
  rewrite FOsubst_f_ex_ne, FOsubst_f_NUMR in H by (lia || avoid_tms).
  rewrite FOsubst_t_var_eq', FOsubst_t_var_ne in H by lia.
  refine (FOPrH_exe_clean n G 801 w _ (FONUMR t (FOVar w)) C H HGw HCw _ _ _ H0).
  - free_fm.
  - apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms].
  - rewrite FOsubst_f_NUMR by (lia || avoid_tms).
    rewrite FOsubst_t_var_eq', (FOsubst_t_not_in t 801 (FOVar w)) by fr_tm.
    apply FOPrH_assum. left. reflexivity.
Qed.

Lemma FOPrH_numr_unique : forall n G a m m',
  FOPrH n G (FONUMR a m) -> FOPrH n G (FONUMR a m') ->
  FOtms_avoid [a; m; m'] 2 1000 -> FOtms_avoid [a; m; m'] 1001 1003 ->
  FOPrH n G (FOEq m m').
Proof.
  intros n G a m m' H1 H2 Hav Hav2.
  exact (FOPrH_num5_unique n G a m m' (FOPrH_and_l _ _ _ _ H1) (FOPrH_and_l _ _ _ _ H2)
           ltac:(avoid_tms) ltac:(avoid_tms) Hav2).
Qed.

Lemma FOPrH_numr_cong : forall n G a m m',
  FOPrH n G (FONUMR a m) -> FOPrH n G (FOEq m m') -> FOtms_avoid [a; m; m'] 2 1000 ->
  FOPrH n G (FONUMR a m').
Proof.
  intros n G a m m' H E Hav.
  assert (K : forall t, FOtm_avoid t 2 1000 ->
             FOsubst_f 999 t (FONUMR a (FOVar 999)) = FONUMR a t).
  { intros t Ht.
    assert (Ht' : FOtms_avoid [t] 2 1000)
      by (apply FOtms_avoid_cons; [exact Ht | apply FOtms_avoid_nil]).
    rewrite FOsubst_f_NUMR by (lia || avoid_tms).
    rewrite FOsubst_t_var_eq', (FOsubst_t_not_in a 999 t) by fr_tm. reflexivity. }
  assert (V : FOtm_avoid m 2 1000) by avoid_tm.
  assert (V' : FOtm_avoid m' 2 1000) by avoid_tm.
  pose proof (FOPrH_leibniz n G 999 m m' (FONUMR a (FOVar 999))
                ltac:(apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]) ltac:(apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms])
                E) as L.
  rewrite (K m V), (K m' V') in L. exact (L H).
Qed.

Lemma FOPrH_numr_of5 : forall n G a m w,
  FOPrH n G (FOTBLEX (FOnumeral 5) a FOZero FOZero m) ->
  FOtms_avoid [a; m] 2 1000 -> FOtms_avoid [a; m] 1001 1003 -> 1003 <= w ->
  FOfree_ctx w G -> FOtms_avoid [a; m] w (S w) ->
  FOPrH n G (FONUMR a m).
Proof.
  intros n G a m w H Hav Hav2 Hw HGw Havw.
  apply (FOPrH_numr_exists n G a w (FONUMR a m) ltac:(avoid_tms) ltac:(lia) HGw ltac:(free_fm)
           ltac:(avoid_tms)).
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (Hw' : FOPrH n Gc (FONUMR a (FOVar w))) by apply FOPrH_last end.
  pose proof (FOPrH_num5_unique n _ a (FOVar w) m (FOPrH_and_l _ _ _ _ Hw')
                (FOPrH_weak_app _ _ _ _ H) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms))
    as E.
  exact (FOPrH_numr_cong n _ a (FOVar w) m Hw' E ltac:(avoid_tms)).
Qed.

Lemma FOPrH_numr_inv0 : forall n G m,
  FOctx_avoid G 2 1000 -> FOtms_avoid [m] 2 1000 ->
  FOPrH n G (FONUMR FOZero m) -> FOPrH n G (FOcpairF (FOnumeral 1) FOZero m).
Proof.
  intros n G m HG Hm H. exact (FOPrH_num5_inv0 n G m HG Hm (FOPrH_and_l _ _ _ _ H)).
Qed.

Lemma FOPrH_numr_invS : forall n G a m w C,
  FOctx_avoid G 2 1000 -> FOtms_avoid [a; m] 2 1000 -> FOtms_avoid [a; m] 1001 1003 ->
  1003 <= w -> FOfree_ctx w G -> FOfree_ctx (S w) G -> FOfree_in w C = false ->
  FOtms_avoid [a; m] w (S (S w)) ->
  (forall v, 2 <= v -> v < 1000 -> FOfree_in v C = false) ->
  FOPrH n G (FONUMR (FOSucc a) m) ->
  FOPrH n (G ++ [FOcpairF (FOnumeral 2) (FOVar w) m; FONUMR a (FOVar w)]) C ->
  FOPrH n G C.
Proof.
  intros n G a m w C HG Hav Hav2 Hw HGw HGw' HCw Havw HCv H H0.
  apply (FOPrH_num5_invS n G a m w C HG Hav ltac:(lia) HGw HCw ltac:(avoid_tms) HCv
           (FOPrH_and_l _ _ _ _ H)).
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (T : FOPrH n Gc (FOTBLEX (FOnumeral 5) a FOZero FOZero (FOVar w))) by wk_in;
    assert (Cw : FOPrH n Gc (FOcpairF (FOnumeral 2) (FOVar w) m)) by wk_in;
    assert (HGw2 : FOfree_ctx (S w) Gc) by free_ctx
  end.
  pose proof (FOPrH_numr_of5 n _ a (FOVar w) (S w) T ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(lia) HGw2 ltac:(avoid_tms)) as Na.
  refine (FOPrH_cut _ _ _ C Na _).
  refine (FOPrH_weaken n _ _ C _ H0).
  intros Y HY. apply in_app_or in HY. destruct HY as [HY|[<-|[<-|[]]]].
  - repeat (apply in_or_app; left). exact HY.
  - apply in_or_app. left. apply in_or_app. right. left. reflexivity.
  - apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPrH_numr_succ : forall n G a m m',
  FOctx_avoid G 2 1000 -> FOtms_avoid [a; m; m'] 2 1000 ->
  FOPrH n G (FONUMR a m) -> FOPrH n G (FOcpairF (FOnumeral 2) m m') ->
  FOPrH n G (FONUMR (FOSucc a) m').
Proof.
  intros n G a m m' HG Hav H HC.
  assert (HG5 : FOctx_avoid G 2 500) by (intros w ? ?; apply HG; lia).
  unfold FONUMR in H |- *.
  apply FOPrH_and_intro;
    [exact (FOPrH_num5_succ n G a m m' HG5 ltac:(avoid_tms) (FOPrH_and_l _ _ _ _ H) HC)|].
  apply FOPrH_and_intro.
  - apply FOPrH_all_intro; [apply HG; lia|]. apply FOPrH_all_intro; [apply HG; lia|].
    pose proof (FOPrH_all_same _ _ _ _ (FOPrH_all_same _ _ _ _
                  (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ H)))) as I2.
    exact (FOPrH_num2_succ n G (FOVar 802) (FOVar 803) m m' HG5 ltac:(avoid_tms) I2 HC).
  - apply FOPrH_all_intro; [apply HG; lia|].
    pose proof (FOPrH_all_same _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ H))) as I0.
    exact (FOPrH_num0_succ n G (FOVar 804) m m' HG5 ltac:(avoid_tms) I0 HC).
Qed.
