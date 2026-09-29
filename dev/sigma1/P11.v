From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10.
Open Scope fo_scope.

Ltac free_fm ::=
  lazymatch goal with
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

(** ** The guard rows of a code, with the table renamed. *)

Lemma FOPrH_guardb_elim : forall n G d k C,
  122 <= k -> k + 11 <= 420 ->
  FOctx_avoid G k (k + 11) ->
  (forall w, k <= w -> w < k + 11 -> FOfree_in w C = false) ->
  FOtms_avoid [d] 2 122 -> FOtms_avoid [d] k (k + 11) ->
  FOPrH n (G ++ [FOAnd (FOTBLVALID 18 (FOVar k) (FOVar (k + 1)) (FOVar (k + 2))
                          (FOVar (k + 3)) (FOVar (k + 4)) (FOVar (k + 5)) (FOVar (k + 6))
                          (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9)) (FOVar (k + 10)))
                       (FOBexC 13 (FOSucc (FOVar (k + 8)))
                          (FOlookup 28 (FOVar k) (FOVar (k + 1)) (FOVar (k + 2))
                             (FOVar (k + 3)) (FOVar (k + 4)) (FOVar (k + 5)) (FOVar (k + 6))
                             (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9)) (FOVar (k + 10))
                             (FOnumeral 3) (FOSucc d) FOZero d (FOVar 13)))]) C ->
  FOPrH n G (FOGUARDB d .-> C).
Proof.
  intros n G d k C Hk Hk' HG HC Hr Hrk H.
  unfold FOGUARDB.
  tblex_rename_step Hr k. tblex_rename_step Hr (k + 1). tblex_rename_step Hr (k + 2).
  tblex_rename_step Hr (k + 3). tblex_rename_step Hr (k + 4). tblex_rename_step Hr (k + 5).
  tblex_rename_step Hr (k + 6). tblex_rename_step Hr (k + 7). tblex_rename_step Hr (k + 8).
  tblex_rename_step Hr (k + 9). tblex_rename_step Hr (k + 10).
  apply FOPrH_intro. exact H.
Qed.

(** ** Small facts: [<=] from an equation, the one-element beta code,
    bounded universals over [0] and [1]. *)

Lemma FOPrH_le_of_eq : forall n G a b c,
  FOPrH n G (FOEq (FOPlus a c) b) -> FOtms_avoid [a; b] 498 499 ->
  FOPrH n G (FOle a b).
Proof.
  intros n G a b c H Hav. unfold FOle.
  apply (FOPrH_ex_intro _ _ 498 c); [reflexivity|].
  rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_var_eq'.
  rewrite (FOsubst_t_not_in a 498 c (Hav a ltac:(in_list) 498 ltac:(lia) ltac:(lia))).
  rewrite (FOsubst_t_not_in b 498 c (Hav b ltac:(in_list) 498 ltac:(lia) ltac:(lia))).
  exact H.
Qed.

Lemma FOPrH_beta_self0 : forall n G v d,
  2 <= v -> v + 4 <= 420 ->
  FOtms_avoid [d] v (v + 4) -> FOtms_avoid [d] 420 500 ->
  FOPrH n G (FObetaF v d d FOZero d).
Proof.
  intros n G v d Hv Hv' Hd1 Hd2. unfold FObetaF.
  apply (FOPrH_bex_intro_t _ _ v (FOSucc d) FOZero); [lia | lia | avoid_tm | avoid_tm
    | avoid_tm | avoid_tm | | fo_ok_solve | ].
  - apply (FOPrH_le_of_eq _ _ _ _ d); [apply FOPrH_ring; fo_ring | avoid_tms].
  - autorewrite with fosubst. subst_avoid_h Hd1.
    apply FOPrH_and_intro; [apply FOPrH_ring; fo_ring|].
    apply (FOPrH_bex_intro_t _ _ (S (S v)) (FOSucc (FOMult d (FOSucc FOZero))) FOZero);
      [lia | lia | avoid_tm | avoid_tm | avoid_tm | avoid_tm | | fo_ok_solve | ].
    + apply (FOPrH_le_of_eq _ _ _ _ (FOMult d (FOSucc FOZero)));
        [apply FOPrH_ring; fo_ring | avoid_tms].
    + autorewrite with fosubst. subst_avoid_h Hd1. apply FOPrH_ring. fo_ring.
Qed.

Lemma FOPrH_ball_zero : forall n G v P,
  FOfree_ctx v G -> FOfree_ctx (S v) G ->
  FOPrH n G (FOBallC v FOZero P).
Proof.
  intros n G v P HG HG'.
  rewrite FOBallC_ltv. apply FOPrH_all_intro; [exact HG|].
  apply FOPrH_intro. apply FOPrH_efq. unfold FOltv.
  refine (FOPrH_ex_elim _ _ (S v) (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) FOZero)
            _ _ _ _ _); [| reflexivity | apply FOPrH_last |].
  { apply FOfree_ctx_app_inv; [exact HG'|].
    apply FOfree_ctx_cons; [|apply FOfree_ctx_nil]. apply FOfree_in_ex_self. }
  apply (FOPrH_Q_succ_nonzero _ _ (FOPlus (FOVar v) (FOVar (S v)))).
  apply (FOPrH_eq_trans _ _ _ (FOPlus (FOVar v) (FOSucc (FOVar (S v)))));
    [apply FOPrH_eq_sym; apply FOPrH_Q_plus_succ | apply FOPrH_last].
Qed.

Lemma FOPrH_ball_one : forall n G v P w,
  FOPrH n G (FOsubst_f v FOZero P) -> FOsubst_ok v FOZero P = true ->
  2 <= v -> v < 399 -> 1 < w -> w <> v -> w <> S v ->
  FOfree_ctx v G -> FOfree_ctx (S v) G -> FOfree_ctx w G ->
  FOfree_in (S v) P = false -> FOfree_in w P = false ->
  FOPrH n G (FOBallC v (FOSucc FOZero) P).
Proof.
  intros n G v P w H Hok Hv Hv' Hw Hwv HwSv HG HG' HGw FSv Fw.
  apply (FOPrH_ball_snoc n G v FOZero P w); try assumption.
  - apply FOPrH_ball_zero; assumption.
  - intros t Ht u Hu1 Hu2. destruct Ht as [<-|[]]. reflexivity.
  - intros t Ht u Hu1 Hu2. destruct Ht as [<-|[]]. reflexivity.
  - intros t Ht u Hu1 Hu2. destruct Ht as [<-|[]]. reflexivity.
Qed.

(** ** Derivations of one line.

    A code whose guard rows exist and which passes the justification
    check of tag [0] (a theory axiom) or [1] (a logical axiom) with
    payload [0] is derivable in one line: the guard's table, the
    one-element formula track [d], and the one-element justification
    track holding the tag, which is its own code. *)

Ltac ok0 :=
  let V := fresh "V" in
  assert (V : FOtm_avoid FOZero 2 500) by (intros ? ? ?; reflexivity);
  solve [auto 100 with fook].

Lemma FOPrH_one_line : forall n G cores d tgn,
  FOctx_avoid G 2 500 -> FOtms_avoid [d] 2 500 -> tgn <= 1 ->
  FOPrH n G (FOGUARDB d) ->
  (forall T, FOPrH n G (FOJDISJ 20 cores (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T)
                          (tc3 T) (td3 T) (tcr T) (tdr T) (tlen T) d d FOZero d
                          (FOnumeral tgn) FOZero)) ->
  FOPrH n G (FOPRMATx cores d).
Proof.
  intros n G cores d tgn HG Hd Htg HB HJ.
  refine (FOPrH_mp _ _ (FOGUARDB d) _ _ HB).
  apply (FOPrH_guardb_elim n G d 260); [lia | lia | intros w H1 H2; apply HG; lia
    | intros w H1 H2; free_fm | avoid_tms | avoid_tms |].
  lazymatch goal with |- FOPrH _ (_ ++ [?GB]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G GB)) as VT;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G GB)) as BX
  end.
  refine (FOPrH_mp _ _ _ _ _ BX).
  apply FOPrH_imp_bexl; [free_ctx | free_fm |].
  apply FOPrH_intro.
  apply (FOPrH_PRMAT_intro n _ cores d (FOVar 260) (FOVar 261) (FOVar 262) (FOVar 263)
           (FOVar 264) (FOVar 265) (FOVar 266) (FOVar 267) (FOVar 268) (FOVar 269)
           (FOVar 270) d d (FOnumeral tgn) (FOnumeral tgn) (FOSucc FOZero));
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
             (FOnumeral tgn) (FOnumeral tgn) FOZero d (FOnumeral tgn));
      [lia | lia | avoid_tms | avoid_tms | avoid_tms | avoid_tms | | | | |].
    + apply FOPrH_le_refl. avoid_tm.
    + apply FOPrH_beta_self0; [lia | lia | avoid_tms | avoid_tms].
    + apply FOPrH_le_refl. avoid_tm.
    + apply FOPrH_beta_self0; [lia | lia | avoid_tms | avoid_tms].
    + apply (FOPrH_CHK_intro_t _ _ 20 cores _ _ _ _ _ _ _ _ _ _ _ d d FOZero d
               (FOnumeral tgn) (FOnumeral tgn) FOZero);
        [lia | avoid_tms | avoid_tms | avoid_tms | avoid_tms | | | |].
      * apply FOPrH_le_refl. avoid_tm.
      * destruct tgn as [|[|]]; [apply FOPrH_le_refl; avoid_tm | | lia].
        apply (FOPrH_le_of_eq _ _ _ _ (FOSucc FOZero));
          [cbn [FOnumeral]; apply FOPrH_ring; fo_ring | avoid_tms].
      * destruct tgn as [|[|]]; [| | lia]; unfold FOcpairF; cbn [FOnumeral];
          apply FOPrH_ring; fo_ring.
      * pose proof (HJ (FOtabv 260)) as HJ'. cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr
          tlen FOtabv Nat.add] in HJ'. wk HJ'.
  - apply (FOPrH_ball_one _ _ 18 _ 250); [| ok0 | lia | lia | lia | lia | lia
      | free_ctx | free_ctx | free_ctx | free_fm | free_fm].
    autorewrite with fosubst. subst_avoid_h Hd.
    apply (FOPrH_GUARDC_intro_t _ _ 20 (FOtabv 260) d d FOZero d (FOVar 13));
      [lia | tab_avoid | avoid_tms | avoid_tms | tab_avoid | | | |].
    + apply FOPrH_le_refl. avoid_tm.
    + apply FOPrH_beta_self0; [lia | lia | avoid_tms | avoid_tms].
    + cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen FOtabv Nat.add].
      apply FOPrH_le_of_ltv; [free_ctx | lia | lia | avoid_tm | avoid_tm |].
      apply FOPrH_assum. in_app.
    + cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen FOtabv Nat.add].
      apply FOPrH_last.
Qed.
