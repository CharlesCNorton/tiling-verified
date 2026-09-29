From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16.
Open Scope fo_scope.

(** ** One-line derivations of substitution instances.

    [d] codes [forall x A -> B] (tag [2]) or [B -> exists x A] (tag
    [3]), with [a], [b] the codes of [A], [B]; the table holds the guard
    row of [d], the capture test of [s] for [x] in [a] and the
    substitution row giving [b]; the payload pairs [x] and [s]. *)

Lemma FOPrH_subst_line : forall n G cores d pat tgn pl r0 x s a b,
  (pat = cpatAllElim /\ tgn = 2) \/ (pat = cpatExIntro /\ tgn = 3) ->
  FOctx_avoid G 2 500 ->
  FOtms_avoid [d; pl; r0; x; s; a; b] 2 500 ->
  FOPrH n G (FOTBLEX3 (FOnumeral 3) (FOSucc d) FOZero d r0
               (FOnumeral 4) x s a (FOnumeral 1) (FOnumeral 3) x s a b) ->
  FOPrH n G (FOcpairF x s pl) ->
  FOPrH n G (FOle a d) -> FOPrH n G (FOle b d) ->
  FOPrH n G (FOPATF 44 [x; a; b] pat d) ->
  FOPrH n G (FOPRMATx cores d).
Proof.
  intros n G cores d pat tgn pl r0 x s a b Hpt HG Hav HT HC Ha Hb HP.
  apply (FOPrH_one_line3 n G cores d tgn pl r0 (FOnumeral 4) x s a (FOnumeral 1)
           (FOnumeral 3) x s a b HG ltac:(avoid_tms) HT).
  intros G' Hinc L4 L3.
  assert (J : FOPrH n G' (FOJSUBST 36 (FOVar 260) (FOVar 261) (FOVar 262) (FOVar 263)
                            (FOVar 264) (FOVar 265) (FOVar 266) (FOVar 267) (FOVar 268)
                            (FOVar 269) (FOVar 270) pat d pl)).
  { apply (FOPrH_jsubst_intro n G' _ _ _ _ _ _ _ _ _ _ _ pat d pl x s a b);
      [apply (FOPrH_weaken n G G' _ Hinc HC) | apply (FOPrH_weaken n G G' _ Hinc Ha)
      | apply (FOPrH_weaken n G G' _ Hinc Hb) | apply (FOPrH_weaken n G G' _ Hinc HP)
      | exact L4 | exact L3 | | avoid_tms | avoid_tms].
    destruct Hpt as [[-> _]|[-> _]]; vm_compute; lia. }
  destruct Hpt as [[-> ->]|[-> ->]].
  - apply FOPrH_jdisj_allelim. exact J.
  - apply FOPrH_jdisj_exintro. exact J.
Qed.
