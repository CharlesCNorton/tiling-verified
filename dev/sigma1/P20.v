From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19.
Open Scope fo_scope.

(** ** The tables the row constructions extend.

    [FOtabB]: a fresh one-row table, [FOtabS]: one table extended by a
    row, [FOtabJ]: two merged tables extended by a row. *)

Definition FOtabB : FOtab :=
  mkTab (FOVar 141) (FOVar 142) (FOVar 143) (FOVar 144) (FOVar 145) (FOVar 146)
    (FOVar 147) (FOVar 148) (FOVar 149) (FOVar 150) (FOSucc FOZero).
Definition FOtabS : FOtab :=
  mkTab (FOVar 141) (FOVar 142) (FOVar 143) (FOVar 144) (FOVar 145) (FOVar 146)
    (FOVar 147) (FOVar 148) (FOVar 149) (FOVar 150) (FOSucc (FOVar 140)).
Definition FOtabJ : FOtab :=
  mkTab (FOVar 182) (FOVar 183) (FOVar 184) (FOVar 185) (FOVar 186) (FOVar 187)
    (FOVar 188) (FOVar 189) (FOVar 190) (FOVar 191) (FOSucc (tlen FOtabM)).

Ltac tab_avoid ::=
  try unfold FOtabB; try unfold FOtabS; try unfold FOtabJ; try unfold FOtabM;
  try unfold FOtab_terms; try unfold FOtabv; try unfold FOtabx; try unfold FOtab0;
  cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen app]; avoid_tms.

Ltac disp0 := unfold FODISPCASES; apply FOPrH_or_intro_l;
  apply FOPrH_and_intro; [apply FOPrH_refl|].
Ltac disp1 := unfold FODISPCASES; apply FOPrH_or_intro_r; apply FOPrH_or_intro_l;
  apply FOPrH_and_intro; [apply FOPrH_refl|].
Ltac disp2 := unfold FODISPCASES; do 2 apply FOPrH_or_intro_r; apply FOPrH_or_intro_l;
  apply FOPrH_and_intro; [apply FOPrH_refl|].
Ltac disp3 := unfold FODISPCASES; do 3 apply FOPrH_or_intro_r; apply FOPrH_or_intro_l;
  apply FOPrH_and_intro; [apply FOPrH_refl|].
Ltac disp4 := unfold FODISPCASES; do 4 apply FOPrH_or_intro_r; apply FOPrH_or_intro_l;
  apply FOPrH_and_intro; [apply FOPrH_refl|].
Ltac alt1 := apply FOPrH_or_intro_l.
Ltac alt2 := apply FOPrH_or_intro_r; apply FOPrH_or_intro_l.
Ltac alt3 := do 2 apply FOPrH_or_intro_r; apply FOPrH_or_intro_l.
Ltac alt4 := do 3 apply FOPrH_or_intro_r; apply FOPrH_or_intro_l.
Ltac alt5 := do 4 apply FOPrH_or_intro_r.

(** ** A row from rows of one table holding three given rows. *)

Lemma FOPrH_tab_step3 : forall n G tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r''
    tgn a1n a2n a3n rn,
  FOctx_avoid G 2 500 ->
  FOtms_avoid [tg; a1; a2; a3; r; tg'; a1'; a2'; a3'; r'; tg''; a1''; a2''; a3''; r'';
               tgn; a1n; a2n; a3n; rn] 2 500 ->
  FOPrH n G (FOTBLEX3 tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'') ->
  (forall G', (forall X, In X G -> In X G') ->
     FOPrH n G' (FOlookupT 28 FOtabS tg a1 a2 a3 r) ->
     FOPrH n G' (FOlookupT 28 FOtabS tg' a1' a2' a3' r') ->
     FOPrH n G' (FOlookupT 28 FOtabS tg'' a1'' a2'' a3'' r'') ->
     FOPrH n G' (FODISPCASES (FOVar 141) (FOVar 142) (FOVar 143) (FOVar 144) (FOVar 145)
                   (FOVar 146) (FOVar 147) (FOVar 148) (FOVar 149) (FOVar 150)
                   (FOSucc (FOVar 140)) tgn a1n a2n a3n rn)) ->
  FOPrH n G (FOTBLEX tgn a1n a2n a3n rn).
Proof.
  intros n G tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'' tgn a1n a2n a3n rn
    HG Hav HE HP.
  refine (FOPrH_mp _ _ _ _ (FOPrH_tblex3_elim n G tg a1 a2 a3 r tg' a1' a2' a3' r'
                              tg'' a1'' a2'' a3'' r'' 130 _ _ _ _ _ _ _ _) HE);
    [lia | lia | tab_side | tab_side | tab_side | tab_side |].
  lazymatch goal with |- FOPrH _ ?G1 _ =>
    assert (K : FOPrH n G1 (FOAnd (FOTBLVALID 18 (tct (FOtabv 130)) (tdt (FOtabv 130))
                   (tc1 (FOtabv 130)) (td1 (FOtabv 130)) (tc2 (FOtabv 130)) (td2 (FOtabv 130))
                   (tc3 (FOtabv 130)) (td3 (FOtabv 130)) (tcr (FOtabv 130)) (tdr (FOtabv 130))
                   (tlen (FOtabv 130)))
                 (FOAnd (FOlookupT 28 (FOtabv 130) tg a1 a2 a3 r)
                 (FOAnd (FOlookupT 28 (FOtabv 130) tg' a1' a2' a3' r')
                        (FOlookupT 28 (FOtabv 130) tg'' a1'' a2'' a3'' r''))))) by apply FOPrH_last;
    assert (HGinc : forall X, In X G -> In X G1)
      by (intros X HX; apply in_or_app; left; exact HX)
  end.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ K)) as K1.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ K))) as K2.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ K))) as K3.
  apply (FOPrH_row_new n _ (FOtabv 130) tgn a1n a2n a3n rn 141 _);
    [ exact (FOPrH_and_l _ _ _ _ K)
    | intros G' Hinc HA1 HA2 Hm;
      refine (HP G' (fun X HX => Hinc X (HGinc X HX)) _ _ _);
      [ refine (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n G' 28 (FOtabv 130) _ tg a1 a2 a3 r Hm
                                    ltac:(lia) _ _ _ _)
                  (FOPrH_weaken n _ G' _ Hinc K1));
        [ intros w ? ?; apply HA1; lia | exact HA2 | tab_side | tab_side ]
      | refine (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n G' 28 (FOtabv 130) _ tg' a1' a2' a3' r'
                                    Hm ltac:(lia) _ _ _ _)
                  (FOPrH_weaken n _ G' _ Hinc K2));
        [ intros w ? ?; apply HA1; lia | exact HA2 | tab_side | tab_side ]
      | refine (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n G' 28 (FOtabv 130) _ tg'' a1'' a2'' a3''
                                    r'' Hm ltac:(lia) _ _ _ _)
                  (FOPrH_weaken n _ G' _ Hinc K3));
        [ intros w ? ?; apply HA1; lia | exact HA2 | tab_side | tab_side ] ]
    | tab_side .. |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (N : FOPrH n Gc (FOTBLNEW (FOtabv 130) (FOtabx 141 (FOSucc (tlen (FOtabv 130))))
                              tgn a1n a2n a3n rn)) by apply FOPrH_last
  end.
  unfold FOTBLNEW in N.
  apply (FOPrH_tblex_intro n _ (FOtabx 141 (FOSucc (tlen (FOtabv 130)))) tgn a1n a2n a3n rn
           (FOPrH_and_l _ _ _ _ N) (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ N))).
  tab_side.
Qed.

(** ** Occurrence rows (tag [0]): [(0, w, tc, 0, r)], [r] the occurrence
    of the variable [w] in the term coded by [tc]. *)

Lemma FOPrH_N0_var_eq : forall n G w tc y,
  FOctx_avoid G 2 500 -> FOtms_avoid [w; tc; y] 2 500 ->
  FOPrH n G (FOcpairF FOZero y tc) -> FOPrH n G (FOEq y w) ->
  FOPrH n G (FOTBLEX FOZero w tc FOZero (FOnumeral 1)).
Proof.
  intros n G w tc y HG Hav Hc E.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp0. exact (FOPrH_step0_var_eq n G FOtabB w tc y Hc E ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N0_var_ne : forall n G w tc y,
  FOctx_avoid G 2 500 -> FOtms_avoid [w; tc; y] 2 500 ->
  FOPrH n G (FOcpairF FOZero y tc) -> FOPrH n G (FONeg (FOEq y w)) ->
  FOPrH n G (FOTBLEX FOZero w tc FOZero FOZero).
Proof.
  intros n G w tc y HG Hav Hc E.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp0. exact (FOPrH_step0_var_ne n G FOtabB w tc y Hc E ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N0_zero : forall n G w tc,
  FOctx_avoid G 2 500 -> FOtms_avoid [w; tc] 2 500 ->
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero tc) ->
  FOPrH n G (FOTBLEX FOZero w tc FOZero FOZero).
Proof.
  intros n G w tc HG Hav Hc.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  apply FOPrH_case0_zero. exact Hc.
Qed.

Lemma FOPrH_N0_succ : forall n G w t tc r,
  FOctx_avoid G 2 500 -> FOtms_avoid [w; t; tc; r] 2 500 ->
  FOPrH n G (FOTBLEX FOZero w t FOZero r) -> FOPrH n G (FOcpairF (FOnumeral 2) t tc) ->
  FOPrH n G (FOTBLEX FOZero w tc FOZero r).
Proof.
  intros n G w t tc r HG Hav HE HC.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  apply (FOPrH_case0_succ n G' _ _ _ _ _ _ _ _ _ _ _ w t tc r);
    [ apply (FOPrH_lookup_rebase _ _ 28 52);
      [exact HL | lia | lia | lia | lia | lia | tab_side | tab_side]
    | exact (FOPrH_weaken n G G' _ Hinc HC) | tab_side | tab_side ].
Qed.

Lemma FOPrH_N0_bin_one : forall n G w tc k p a b,
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [w; tc; p; a; b] 2 500 ->
  FOPrH n G (FOTBLEX FOZero w a FOZero (FOnumeral 1)) ->
  FOPrH n G (FOcpairF (FOnumeral k) p tc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOTBLEX FOZero w tc FOZero (FOnumeral 1)).
Proof.
  intros n G w tc k p a b Hk HG Hav HE Hc Hp.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc'.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp'.
  disp0. unfold FOSTEP0.
  destruct Hk as [->| ->]; [alt4 | alt5];
    exact (FOPrH_stepbin_one n G' FOtabS w tc _ 0 p a b Hc' Hp' HL
             ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N0_bin_zero : forall n G w tc r k p a b,
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [w; tc; r; p; a; b] 2 500 ->
  FOPrH n G (FOTBLEX FOZero w a FOZero FOZero) ->
  FOPrH n G (FOTBLEX FOZero w b FOZero r) ->
  FOPrH n G (FOcpairF (FOnumeral k) p tc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOTBLEX FOZero w tc FOZero r).
Proof.
  intros n G w tc r k p a b Hk HG Hav Ha Hb Hc Hp.
  refine (FOPrH_tblex_join n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG _ Ha Hb _); [tab_side|].
  intros G' Hinc La Lb.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc'.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp'.
  disp0. unfold FOSTEP0.
  destruct Hk as [->| ->]; [alt4 | alt5];
    exact (FOPrH_stepbin_zero n G' FOtabJ w tc r _ 0 p a b Hc' Hp' La Lb
             ltac:(tab_side) ltac:(tab_side)).
Qed.

(** ** Free-occurrence rows (tag [1]): [(1, w, pc, 0, r)]. *)

Lemma FOPrH_N1_eq_one : forall n G w pc p a b,
  FOctx_avoid G 2 500 -> FOtms_avoid [w; pc; p; a; b] 2 500 ->
  FOPrH n G (FOTBLEX FOZero w a FOZero (FOnumeral 1)) ->
  FOPrH n G (FOcpairF FOZero p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w pc FOZero (FOnumeral 1)).
Proof.
  intros n G w pc p a b HG Hav HE Hc Hp.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc'.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp'.
  disp1. unfold FOSTEP1. alt1.
  exact (FOPrH_stepbin_one n G' FOtabS w pc 0 0 p a b Hc' Hp' HL
           ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N1_eq_zero : forall n G w pc r p a b,
  FOctx_avoid G 2 500 -> FOtms_avoid [w; pc; r; p; a; b] 2 500 ->
  FOPrH n G (FOTBLEX FOZero w a FOZero FOZero) ->
  FOPrH n G (FOTBLEX FOZero w b FOZero r) ->
  FOPrH n G (FOcpairF FOZero p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w pc FOZero r).
Proof.
  intros n G w pc r p a b HG Hav Ha Hb Hc Hp.
  refine (FOPrH_tblex_join n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG _ Ha Hb _); [tab_side|].
  intros G' Hinc La Lb.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc'.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp'.
  disp1. unfold FOSTEP1. alt1.
  exact (FOPrH_stepbin_zero n G' FOtabJ w pc r 0 0 p a b Hc' Hp' La Lb
           ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N1_false : forall n G w pc,
  FOctx_avoid G 2 500 -> FOtms_avoid [w; pc] 2 500 ->
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero pc) ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w pc FOZero FOZero).
Proof.
  intros n G w pc HG Hav Hc.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp1. apply FOPrH_step1_false. exact Hc.
Qed.

Lemma FOPrH_N1_impl_one : forall n G w pc p a b,
  FOctx_avoid G 2 500 -> FOtms_avoid [w; pc; p; a; b] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w a FOZero (FOnumeral 1)) ->
  FOPrH n G (FOcpairF (FOnumeral 2) p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w pc FOZero (FOnumeral 1)).
Proof.
  intros n G w pc p a b HG Hav HE Hc Hp.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc'.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp'.
  disp1. unfold FOSTEP1. alt3.
  exact (FOPrH_stepbin_one n G' FOtabS w pc 2 1 p a b Hc' Hp' HL
           ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N1_impl_zero : forall n G w pc r p a b,
  FOctx_avoid G 2 500 -> FOtms_avoid [w; pc; r; p; a; b] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w a FOZero FOZero) ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w b FOZero r) ->
  FOPrH n G (FOcpairF (FOnumeral 2) p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w pc FOZero r).
Proof.
  intros n G w pc r p a b HG Hav Ha Hb Hc Hp.
  refine (FOPrH_tblex_join n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG _ Ha Hb _); [tab_side|].
  intros G' Hinc La Lb.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc'.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp'.
  disp1. unfold FOSTEP1. alt3.
  exact (FOPrH_stepbin_zero n G' FOtabJ w pc r 2 1 p a b Hc' Hp' La Lb
           ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N1_quant_eq : forall n G w pc k p y bb,
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [w; pc; p; y; bb] 2 500 ->
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FOEq y w) ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w pc FOZero FOZero).
Proof.
  intros n G w pc k p y bb Hk HG Hav Hc Hp E.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp1. unfold FOSTEP1.
  destruct Hk as [->| ->]; [alt4 | alt5];
    exact (FOPrH_quant0_eq n G FOtabB w pc _ 1 p y bb Hc Hp E
             ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N1_quant_ne : forall n G w pc r k p y bb,
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [w; pc; r; p; y; bb] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w bb FOZero r) ->
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FONeg (FOEq y w)) ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w pc FOZero r).
Proof.
  intros n G w pc r k p y bb Hk HG Hav HE Hc Hp E.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc'.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp'.
  pose proof (FOPrH_weaken n G G' _ Hinc E) as E'.
  disp1. unfold FOSTEP1.
  destruct Hk as [->| ->]; [alt4 | alt5];
    exact (FOPrH_quant0_ne n G' FOtabS w pc r _ 1 p y bb Hc' Hp' E' HL
             ltac:(tab_side) ltac:(tab_side)).
Qed.
