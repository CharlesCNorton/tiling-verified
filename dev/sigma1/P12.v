From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11.
Open Scope fo_scope.

(** ** A lookup's result is at most the code of its result column. *)

Lemma FOPrH_lookup_res_le : forall n G B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r,
  FOPrH n G (FOlookup B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r) ->
  2 <= B -> B + 22 <= 420 ->
  FOctx_avoid G B (B + 22) ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; tg; a1; a2; a3; r] B (B + 22) ->
  FOtms_avoid [cr; dr; r] 498 499 ->
  FOPrH n G (FOle r cr).
Proof.
  intros n G B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r H HB HB' HG Hav Hav2.
  unfold FOlookup in H.
  refine (FOPrH_mp _ _ _ _ _ H).
  apply FOPrH_imp_bexl; [free_ctx | free_fm |].
  apply FOPrH_intro.
  lazymatch goal with |- FOPrH _ (_ ++ [?X]) _ =>
    pose proof (FOPrH_last n (G ++ [FOltv B len]) X) as L0
  end.
  apply FOPrH_and_r, FOPrH_and_r, FOPrH_and_r, FOPrH_and_r in L0.
  refine (FOPrH_mp _ _ _ _ (FOPrH_beta_le _ _ (B + 18) cr dr (FOVar B) r _ _ _ _) L0);
    [ctx_list | lia | avoid_tms | avoid_tms].
Qed.

(** ** The guard rows of [d] from a table row substituting at [S d]
    inside [d]. *)

Lemma FOPrH_guard_of_row : forall n G d r,
  FOctx_avoid G 2 500 -> FOtms_avoid [d; r] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 3) (FOSucc d) FOZero d r) -> FOPrH n G (FOGUARDB d).
Proof.
  intros n G d r HG Hdr H.
  refine (FOPrH_mp _ _ _ _ _ H).
  apply (FOPrH_tblex_elim n G _ _ _ _ _ 260); [lia | lia | intros w H1 H2; apply HG; lia
    | intros w H1 H2; free_fm | avoid_tms | avoid_tms |].
  lazymatch goal with |- FOPrH _ (_ ++ [?X]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G X)) as VT;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G X)) as LK
  end.
  assert (Hav : FOtms_avoid [FOVar 260; FOVar 261; FOVar 262; FOVar 263; FOVar 264;
                  FOVar 265; FOVar 266; FOVar 267; FOVar 268; FOVar 269; FOVar 270; d; r]
                  2 122) by avoid_tms.
  unfold FOGUARDB.
  tblex_intro_step (FOVar 260) Hav. tblex_intro_step (FOVar 261) Hav.
  tblex_intro_step (FOVar 262) Hav. tblex_intro_step (FOVar 263) Hav.
  tblex_intro_step (FOVar 264) Hav. tblex_intro_step (FOVar 265) Hav.
  tblex_intro_step (FOVar 266) Hav. tblex_intro_step (FOVar 267) Hav.
  tblex_intro_step (FOVar 268) Hav. tblex_intro_step (FOVar 269) Hav.
  tblex_intro_step (FOVar 270) Hav.
  cbn [Nat.add] in VT, LK.
  apply FOPrH_and_intro; [exact VT|].
  apply (FOPrH_bex_intro_t _ _ 13 (FOSucc (FOVar 268)) r); [lia | lia | avoid_tm | avoid_tm
    | avoid_tm | avoid_tm | | | ].
  - apply FOPrH_le_succ_of_le; [|avoid_tms].
    apply (FOPrH_lookup_res_le _ _ 28 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LK);
      [lia | lia | ctx_list | avoid_tms | avoid_tms].
  - let V := fresh "V" in assert (V : FOtm_avoid r 2 122) by avoid_tm;
    solve [auto 100 with fook].
  - autorewrite with fosubst. rewrite ?FOsubst_t_var_eq'. subst_avoid_h Hav. exact LK.
Qed.
