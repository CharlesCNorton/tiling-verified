From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15.
Open Scope fo_scope.

(** ** Code patterns introduced at a low base. *)

Lemma FOPrH_patf_pair_intro_lo : forall n G B env a b d u w,
  FOPrH n G (FOcpairF u w d) ->
  FOPrH n G (FOPATF (B + 4) env a u) ->
  FOPrH n G (FOPATF (B + 4 + 4 * cpat_pairs a) env b w) ->
  2 <= B -> B + cpat_span (CPair a b) <= 420 ->
  FOtms_avoid (d :: u :: w :: env) B (B + cpat_span (CPair a b)) ->
  FOtms_avoid [d; u; w] 420 500 ->
  FOPrH n G (FOPATF B env (CPair a b) d).
Proof.
  intros n G B env a b d u w HC Ha Hb HB HB' Hav Hav2.
  pose proof (cpat_span_le a) as Hsa. cbn [cpat_span] in Hav, HB'.
  destruct (FOPrH_cpair_le_cf n G u w d ltac:(avoid_tms) HC) as [Hud Hwd].
  cbn [FOPATF].
  apply (FOPrH_bex_intro_t _ _ B (FOSucc d) u); [lia | lia | avoid_tm | avoid_tm | avoid_tm
    | avoid_tm | apply FOPrH_le_succ_of_le; [exact Hud | avoid_tms] | | ].
  - apply FOsubst_ok_bex; [apply (Hav u); [right; left; reflexivity | lia | lia]
                         | apply (Hav u); [right; left; reflexivity | lia | lia] |].
    apply FOsubst_ok_and; [apply FOsubst_ok_cpairF|].
    apply FOsubst_ok_and; apply FOsubst_ok_PATF;
      apply (FOtm_avoid_sub u B (B + (4 + 4 * cpat_pairs a + cpat_span b)));
      try (apply Hav; right; left; reflexivity); lia.
  - rewrite FOsubst_f_bex by lia. rewrite FOsubst_f_and, FOsubst_f_cpairF, FOsubst_f_and,
      !FOsubst_f_PATF by lia.
    rewrite FOsubst_t_succ, FOsubst_t_var_eq', !FOsubst_t_var_ne by lia.
    rewrite (FOsubst_t_not_in d B _ (Hav d (or_introl eq_refl) B ltac:(lia) ltac:(lia))).
    rewrite (FOsubst_map_avoid B u env).
    2:{ intros t Ht. apply (Hav t); [right; right; right; exact Ht | lia | lia]. }
    apply (FOPrH_bex_intro_t _ _ (B + 2) (FOSucc d) w); [lia | lia | avoid_tm | avoid_tm
      | avoid_tm | avoid_tm | apply FOPrH_le_succ_of_le; [exact Hwd | avoid_tms] | | ].
    + apply FOsubst_ok_and; [apply FOsubst_ok_cpairF|].
      apply FOsubst_ok_and; apply FOsubst_ok_PATF;
        apply (FOtm_avoid_sub w B (B + (4 + 4 * cpat_pairs a + cpat_span b)));
        try (apply Hav; right; right; left; reflexivity); lia.
    + rewrite FOsubst_f_and, FOsubst_f_cpairF, FOsubst_f_and, !FOsubst_f_PATF by lia.
      rewrite FOsubst_t_var_eq'. rewrite ?FOsubst_t_var_ne by lia.
      rewrite (FOsubst_t_not_in d (B + 2) _ (Hav d (or_introl eq_refl) (B + 2) ltac:(lia)
                                               ltac:(lia))).
      rewrite (FOsubst_t_not_in u (B + 2) _ (Hav u (or_intror (or_introl eq_refl)) (B + 2)
                                               ltac:(lia) ltac:(lia))).
      rewrite (FOsubst_map_avoid (B + 2) w env).
      2:{ intros t Ht. apply (Hav t); [right; right; right; exact Ht | lia | lia]. }
      apply FOPrH_and_intro; [exact HC|]. apply FOPrH_and_intro; [exact Ha | exact Hb].
Qed.

Lemma FOPrH_patf_lit : forall n G B env k, FOPrH n G (FOPATF B env (CLit k) (FOnumeral k)).
Proof. intros. cbn [FOPATF]. apply FOPrH_thm. apply FOProvesTn_EqRefl. Qed.

Lemma FOPrH_patf_slot : forall n G B env i,
  FOPrH n G (FOPATF B env (CVarP i) (nth i env FOZero)).
Proof. intros. cbn [FOPATF]. apply FOPrH_thm. apply FOProvesTn_EqRefl. Qed.

(** ** The substitution justification at the checker's base. *)

Ltac jbex s H :=
  apply (FOPrH_bex_intro_t _ _ _ _ s);
  [ lia | lia | avoid_tm | avoid_tm | avoid_tm | avoid_tm |
  | let V := fresh "V" in assert (V : FOtm_avoid s 36 110) by avoid_tm;
    solve [auto 100 with fook]
  | autorewrite with fosubst; subst_avoid_h H ].

Lemma FOPrH_jsubst_intro : forall n G ct dt c1 d1 c2 d2 c3 d3 cr dr len pat vd pl x s a b,
  FOPrH n G (FOcpairF x s pl) ->
  FOPrH n G (FOle a vd) -> FOPrH n G (FOle b vd) ->
  FOPrH n G (FOPATF 44 [x; a; b] pat vd) ->
  FOPrH n G (FOlookup 28 ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 4) x s a
               (FOnumeral 1)) ->
  FOPrH n G (FOlookup 28 ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 3) x s a b) ->
  44 + cpat_span pat <= 66 ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; vd; pl; x; s; a; b] 28 110 ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; vd; pl; x; s; a; b] 420 500 ->
  FOPrH n G (FOJSUBST 36 ct dt c1 d1 c2 d2 c3 d3 cr dr len pat vd pl).
Proof.
  intros n G ct dt c1 d1 c2 d2 c3 d3 cr dr len pat vd pl x s a b HC Ha Hb HP L4 L3 Hsp
    Hav Hav2.
  destruct (FOPrH_cpair_le_cf n G x s pl ltac:(avoid_tms) HC) as [Hx Hs].
  unfold FOJSUBST.
  jbex x Hav; [apply FOPrH_le_succ_of_le; [exact Hx | avoid_tms]|].
  jbex s Hav; [apply FOPrH_le_succ_of_le; [exact Hs | avoid_tms]|].
  apply FOPrH_and_intro; [exact HC|].
  jbex a Hav; [apply FOPrH_le_succ_of_le; [exact Ha | avoid_tms]|].
  jbex b Hav; [apply FOPrH_le_succ_of_le; [exact Hb | avoid_tms]|].
  apply FOPrH_and_intro; [exact HP|].
  apply FOPrH_and_intro.
  - apply (FOPrH_lookup_rebase n G 28 66 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L4);
      [lia | lia | lia | lia | lia | avoid_tms | avoid_tms].
  - apply (FOPrH_lookup_rebase n G 28 88 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L3);
      [lia | lia | lia | lia | lia | avoid_tms | avoid_tms].
Qed.

Lemma FOPrH_jdisj_allelim : forall n G cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd pl,
  FOPrH n G (FOJSUBST 36 ct dt c1 d1 c2 d2 c3 d3 cr dr len cpatAllElim vd pl) ->
  FOPrH n G (FOJDISJ 20 cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd
               (FOnumeral 2) pl).
Proof.
  intros. unfold FOJDISJ.
  apply FOPrH_or_intro_r. apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [apply FOPrH_thm; apply FOProvesTn_EqRefl | exact H].
Qed.

Lemma FOPrH_jdisj_exintro : forall n G cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd pl,
  FOPrH n G (FOJSUBST 36 ct dt c1 d1 c2 d2 c3 d3 cr dr len cpatExIntro vd pl) ->
  FOPrH n G (FOJDISJ 20 cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd
               (FOnumeral 3) pl).
Proof.
  intros. unfold FOJDISJ.
  apply FOPrH_or_intro_r. apply FOPrH_or_intro_r. apply FOPrH_or_intro_r.
  apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [apply FOPrH_thm; apply FOProvesTn_EqRefl | exact H].
Qed.
