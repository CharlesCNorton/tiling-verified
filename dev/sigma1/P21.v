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

(** ** Substitution rows into terms (tag [2]): [(2, X, s, tc, r)]. *)

Lemma FOPrH_N2_var_eq : forall n G X s tc y,
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; tc; y] 2 500 ->
  FOPrH n G (FOcpairF FOZero y tc) -> FOPrH n G (FOEq y X) ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s tc s).
Proof.
  intros n G X s tc y HG Hav Hc E.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp2. exact (FOPrH_step2_var_eq n G FOtabB X s tc y Hc E ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N2_var_ne : forall n G X s tc y,
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; tc; y] 2 500 ->
  FOPrH n G (FOcpairF FOZero y tc) -> FOPrH n G (FONeg (FOEq y X)) ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s tc tc).
Proof.
  intros n G X s tc y HG Hav Hc E.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp2. exact (FOPrH_step2_var_ne n G FOtabB X s tc y Hc E ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N2_zero : forall n G X s tc,
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; tc] 2 500 ->
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero tc) ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s tc tc).
Proof.
  intros n G X s tc HG Hav Hc.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  apply FOPrH_case2_zero. exact Hc.
Qed.

Lemma FOPrH_N2_succ : forall n G X s t t' tc r,
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; t; t'; tc; r] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s t t') ->
  FOPrH n G (FOcpairF (FOnumeral 2) t tc) -> FOPrH n G (FOcpairF (FOnumeral 2) t' r) ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s tc r).
Proof.
  intros n G X s t t' tc r HG Hav HE HC HC'.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  apply (FOPrH_case2_succ n G' _ _ _ _ _ _ _ _ _ _ _ X s t t' tc r);
    [ apply (FOPrH_lookup_rebase _ _ 28 54);
      [exact HL | lia | lia | lia | lia | lia | tab_side | tab_side]
    | exact (FOPrH_weaken n G G' _ Hinc HC) | exact (FOPrH_weaken n G G' _ Hinc HC')
    | tab_side | tab_side ].
Qed.

Lemma FOPrH_N2_bin : forall n G X s tc r k p a b a' b' p',
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; tc; r; p; a; b; a'; b'; p'] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s a a') ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s b b') ->
  FOPrH n G (FOcpairF (FOnumeral k) p tc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOcpairF a' b' p') -> FOPrH n G (FOcpairF (FOnumeral k) p' r) ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s tc r).
Proof.
  intros n G X s tc r k p a b a' b' p' Hk HG Hav Ha Hb Hc Hp Hp' Hr.
  refine (FOPrH_tblex_join n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG _ Ha Hb _); [tab_side|].
  intros G' Hinc La Lb.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp') as Hp2.
  pose proof (FOPrH_weaken n G G' _ Hinc Hr) as Hr1.
  disp2. unfold FOSTEP2.
  destruct Hk as [->| ->]; [alt4 | alt5];
    exact (FOPrH_substbin_intro n G' FOtabJ X s tc r _ 2 _ p a b a' b' p' Hc1 Hp1 La Lb
             Hp2 Hr1 ltac:(tab_side) ltac:(tab_side)).
Qed.

(** ** Substitution rows into formulas (tag [3]): [(3, X, s, pc, r)]. *)

Lemma FOPrH_N3_eq : forall n G X s pc r p a b a' b' p',
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc; r; p; a; b; a'; b'; p'] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s a a') ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s b b') ->
  FOPrH n G (FOcpairF FOZero p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOcpairF a' b' p') -> FOPrH n G (FOcpairF FOZero p' r) ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X s pc r).
Proof.
  intros n G X s pc r p a b a' b' p' HG Hav Ha Hb Hc Hp Hp' Hr.
  refine (FOPrH_tblex_join n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG _ Ha Hb _); [tab_side|].
  intros G' Hinc La Lb.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp') as Hp2.
  pose proof (FOPrH_weaken n G G' _ Hinc Hr) as Hr1.
  disp3. unfold FOSTEP3. alt1.
  exact (FOPrH_substbin_intro n G' FOtabJ X s pc r 0 2 0 p a b a' b' p' Hc1 Hp1 La Lb
           Hp2 Hr1 ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N3_false : forall n G X s pc,
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc] 2 500 ->
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero pc) ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X s pc pc).
Proof.
  intros n G X s pc HG Hav Hc.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp3. apply FOPrH_step3_false. exact Hc.
Qed.

Lemma FOPrH_N3_impl : forall n G X s pc r p a b a' b' p',
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc; r; p; a; b; a'; b'; p'] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X s a a') ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X s b b') ->
  FOPrH n G (FOcpairF (FOnumeral 2) p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOcpairF a' b' p') -> FOPrH n G (FOcpairF (FOnumeral 2) p' r) ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X s pc r).
Proof.
  intros n G X s pc r p a b a' b' p' HG Hav Ha Hb Hc Hp Hp' Hr.
  refine (FOPrH_tblex_join n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG _ Ha Hb _); [tab_side|].
  intros G' Hinc La Lb.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp') as Hp2.
  pose proof (FOPrH_weaken n G G' _ Hinc Hr) as Hr1.
  disp3. unfold FOSTEP3. alt3.
  exact (FOPrH_substbin_intro n G' FOtabJ X s pc r 2 3 2 p a b a' b' p' Hc1 Hp1 La Lb
           Hp2 Hr1 ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N3_quant_eq : forall n G X s pc k p y bb,
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc; p; y; bb] 2 500 ->
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FOEq y X) ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X s pc pc).
Proof.
  intros n G X s pc k p y bb Hk HG Hav Hc Hp E.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp3. unfold FOSTEP3.
  destruct Hk as [->| ->]; [alt4 | alt5];
    exact (FOPrH_substquant_eq n G FOtabB X s pc _ p y bb Hc Hp E
             ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N3_quant_ne : forall n G X s pc r k p y bb bb' p',
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc; r; p; y; bb; bb'; p'] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X s bb bb') ->
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FONeg (FOEq y X)) ->
  FOPrH n G (FOcpairF y bb' p') -> FOPrH n G (FOcpairF (FOnumeral k) p' r) ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X s pc r).
Proof.
  intros n G X s pc r k p y bb bb' p' Hk HG Hav HE Hc Hp E Hp' Hr.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp1.
  pose proof (FOPrH_weaken n G G' _ Hinc E) as E1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp') as Hp2.
  pose proof (FOPrH_weaken n G G' _ Hinc Hr) as Hr1.
  disp3. unfold FOSTEP3.
  destruct Hk as [->| ->]; [alt4 | alt5].
  - exact (FOPrH_substquant_ne n G' FOtabS X s pc r 3 p y bb bb' p' ltac:(lia) Hc1 Hp1 E1 HL
             Hp2 Hr1 ltac:(tab_side) ltac:(tab_side)).
  - exact (FOPrH_substquant_ne n G' FOtabS X s pc r 4 p y bb bb' p' ltac:(lia) Hc1 Hp1 E1 HL
             Hp2 Hr1 ltac:(tab_side) ltac:(tab_side)).
Qed.
