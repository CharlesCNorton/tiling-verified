From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20.
Open Scope fo_scope.

(** ** Capture-test rows (tag [4]): [(4, X, s, pc, r)], [r = 1] when [s]
    is free for [X] in the formula coded by [pc]. *)

Lemma FOPrH_N4_eq : forall n G X s pc p,
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc; p] 2 500 ->
  FOPrH n G (FOcpairF FOZero p pc) ->
  FOPrH n G (FOTBLEX (FOnumeral 4) X s pc (FOnumeral 1)).
Proof.
  intros n G X s pc p HG Hav Hc.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp4. exact (FOPrH_step4_eq n G FOtabB X s pc p Hc ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N4_false : forall n G X s pc,
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc] 2 500 ->
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero pc) ->
  FOPrH n G (FOTBLEX (FOnumeral 4) X s pc (FOnumeral 1)).
Proof.
  intros n G X s pc HG Hav Hc.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp4. apply FOPrH_step4_false. exact Hc.
Qed.

Lemma FOPrH_N4_impl : forall n G X s pc r p a b,
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc; r; p; a; b] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 4) X s a (FOnumeral 1)) ->
  FOPrH n G (FOTBLEX (FOnumeral 4) X s b r) ->
  FOPrH n G (FOcpairF (FOnumeral 2) p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOTBLEX (FOnumeral 4) X s pc r).
Proof.
  intros n G X s pc r p a b HG Hav Ha Hb Hc Hp.
  refine (FOPrH_tblex_join n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG _ Ha Hb _); [tab_side|].
  intros G' Hinc La Lb.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp1.
  disp4. unfold FOSTEP4. alt3.
  exact (FOPrH_subokbin_one n G' FOtabJ X s pc r p a b Hc1 Hp1 La Lb
           ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N4_quant_eq : forall n G X s pc k p y bb,
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc; p; y; bb] 2 500 ->
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FOEq y X) ->
  FOPrH n G (FOTBLEX (FOnumeral 4) X s pc (FOnumeral 1)).
Proof.
  intros n G X s pc k p y bb Hk HG Hav Hc Hp E.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp4. unfold FOSTEP4.
  destruct Hk as [->| ->]; [alt4 | alt5];
    exact (FOPrH_subokquant_eq n G FOtabB X s pc _ p y bb Hc Hp E
             ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N4_quant_nf : forall n G X s pc k p y bb,
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc; p; y; bb] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 1) X bb FOZero FOZero) ->
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FONeg (FOEq y X)) ->
  FOPrH n G (FOTBLEX (FOnumeral 4) X s pc (FOnumeral 1)).
Proof.
  intros n G X s pc k p y bb Hk HG Hav HE Hc Hp E.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp1.
  pose proof (FOPrH_weaken n G G' _ Hinc E) as E1.
  disp4. unfold FOSTEP4.
  destruct Hk as [->| ->]; [alt4 | alt5];
    exact (FOPrH_subokquant_nf n G' FOtabS X s pc _ p y bb Hc1 Hp1 E1 HL
             ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N4_quant_fr : forall n G X s pc r k p y bb,
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc; r; p; y; bb] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 1) X bb FOZero (FOnumeral 1)) ->
  FOPrH n G (FOTBLEX FOZero y s FOZero FOZero) ->
  FOPrH n G (FOTBLEX (FOnumeral 4) X s bb r) ->
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FONeg (FOEq y X)) ->
  FOPrH n G (FOTBLEX (FOnumeral 4) X s pc r).
Proof.
  intros n G X s pc r k p y bb Hk HG Hav H1 H0 H4 Hc Hp E.
  assert (H3 : FOPrH n G (FOTBLEX3 (FOnumeral 1) X bb FOZero (FOnumeral 1)
                            FOZero y s FOZero FOZero (FOnumeral 4) X s bb r)).
  { refine (FOPrH_tblex_join3 n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG _ H1 H0 H4). tab_side. }
  refine (FOPrH_tab_step3 n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG _ H3 _);
    [tab_side|].
  intros G' Hinc L1 L0 L4.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp1.
  pose proof (FOPrH_weaken n G G' _ Hinc E) as E1.
  disp4. unfold FOSTEP4.
  destruct Hk as [->| ->]; [alt4 | alt5];
    exact (FOPrH_subokquant_fr n G' FOtabS X s pc r _ p y bb Hc1 Hp1 E1 L1 L0 L4
             ltac:(tab_side) ltac:(tab_side)).
Qed.
