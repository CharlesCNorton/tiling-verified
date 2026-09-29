From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3.
Open Scope fo_scope.

(** ** A lookup at another base. *)

Lemma FOPrH_lookup_rebase : forall n G B B' ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r,
  FOPrH n G (FOlookup B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r) ->
  2 <= B -> 2 <= B' -> B + 22 <= 420 -> B' + 22 <= 420 ->
  B + 22 <= B' \/ B' + 22 <= B ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; tg; a1; a2; a3; r] B (B + 22) ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; tg; a1; a2; a3; r] B' (B' + 22) ->
  FOPrH n G (FOlookup B' ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r).
Proof.
  intros n G B B' ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r H HB1 HB2 HB3 HB4 HBB
    Hav Hav'.
  refine (FOPrH_mp _ _ _ _ _ H). apply FOPrH_empty.
  unfold FOlookup. rewrite !FOBexC_ltv.
  assert (V : FOtm_avoid (FOVar B') B (B + 22)) by (apply FOtm_avoid_var; lia).
  refine (FOPrH_imp_trans _ _ _ _ _ (FOPrH_thm _ _ _ (FOPr_ex_rename n B B' _ _ _)) _).
  - unfold FOltv. rewrite !FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
    + rewrite FOfree_in_FOExists_neq by lia. cbn [FOfree_in]. apply Bool.orb_false_iff.
      split; fr_tm.
    + repeat (apply Bool.orb_false_iff; split; [apply FOfree_in_betaF_not; [lia | fr_tm..]|]).
      apply FOfree_in_betaF_not; [lia | fr_tm..].
  - unfold FOltv.
    repeat (apply FOsubst_ok_and; [first [apply FOsubst_ok_betaF; avoid_tm
                                         | apply FOsubst_ok_ex; [fr_tm | apply FOsubst_ok_eq]]
                                  |]).
    apply FOsubst_ok_betaF; avoid_tm.
  - apply FOPrH_ex_imp; [apply FOfree_ctx_nil|].
    apply (FOPrH_ex_intro _ _ B' (FOVar B')); [apply FOsubst_ok_var_self|].
    rewrite FOsubst_f_id.
    unfold FOltv.
    rewrite !FOsubst_f_and, FOsubst_f_ex_ne by lia.
    rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_succ, FOsubst_t_var_eq',
      FOsubst_t_var_ne by lia.
    rewrite !FOsubst_f_betaF by lia. rewrite !FOsubst_t_var_eq'. subst_avoid_h Hav.
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      pose proof (FOPrH_last n [] (FOAnd (FOExists (S B) (FOEq (FOPlus (FOVar B')
                    (FOSucc (FOVar (S B)))) len)) (FOAnd (FObetaF (B + 2) ct dt (FOVar B') tg)
                    (FOAnd (FObetaF (B + 6) c1 d1 (FOVar B') a1)
                    (FOAnd (FObetaF (B + 10) c2 d2 (FOVar B') a2)
                    (FOAnd (FObetaF (B + 14) c3 d3 (FOVar B') a3)
                           (FObetaF (B + 18) cr dr (FOVar B') r))))))) as K
    end.
    cbn [app] in K.
    apply FOPrH_and_intro.
    { refine (FOPrH_mp _ _ _ _ (FOPrH_exeq_rename _ _ (S B) (S B') (FOVar B') len _ _ _ _ _)
                (FOPrH_and_l _ _ _ _ K)); [lia | fr_tm | fr_tm | fr_tm | fr_tm]. }
    apply FOPrH_and_r in K.
    do 4 (apply FOPrH_and_intro;
          [ refine (FOPrH_rebase_cf _ _ _ _ _ _ _ _ _ _ _ (FOPrH_and_l _ _ _ _ K));
            [lia | avoid_tms | avoid_tms] | apply FOPrH_and_r in K ]).
    refine (FOPrH_rebase_cf _ _ _ _ _ _ _ _ _ _ _ K); [lia | avoid_tms | avoid_tms].
Qed.

(** ** Order facts for the step witnesses. *)

Lemma FOPrH_le_refl : forall n G a, FOtm_avoid a 498 499 -> FOPrH n G (FOle a a).
Proof.
  intros n G a Ha. unfold FOle.
  apply (FOPrH_ex_intro _ _ 498 FOZero); [cbn [FOsubst_ok]; reflexivity|].
  rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_var_eq'.
  rewrite (FOsubst_t_not_in a 498 _ (Ha 498 ltac:(lia) ltac:(lia))).
  apply FOPrH_Q_plus_zero.
Qed.

Lemma FOPrH_cpair_lt : forall n G a b c,
  FOPrH n G (FOcpairF (FOSucc a) b c) ->
  FOtms_avoid [a; b; c] 420 500 ->
  FOPrH n G (FOle (FOSucc b) c).
Proof.
  intros n G a b c H Hav.
  refine (FOPrH_ctxfree n G _ _ _ H).
  destruct (FOPrH_cpair_le_cf n [FOcpairF (FOSucc a) b c] (FOSucc a) b c ltac:(avoid_tms)
              (FOPrH_assum n [FOcpairF (FOSucc a) b c] (FOcpairF (FOSucc a) b c)
                 (or_introl eq_refl))) as [_ Hb].
  unfold FOle in Hb.
  refine (FOPrH_ex_elim n _ 498 (FOEq (FOPlus b (FOVar 498)) c) _ _ _ Hb _);
    [free_ctx | free_fm |].
  apply (FOPrH_cases_zs _ _ (FOVar 498) 499 _); [lia | fr_tm | free_ctx | free_fm | fr_tm | |].
  - apply FOPrH_efq.
    apply (FOPrH_Q_succ_nonzero _ _ (FOPlus (FOMult (FOPlus (FOSucc a) b) (FOPlus (FOSucc a) b))
                                         (FOPlus a b))).
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (Z : FOPrH n Gc (FOEq FOZero (FOVar 498))) by (apply FOPrH_eq_sym; wk_in)
    end.
    unfold FOcpairF in *.
    fo_lin [(.S .0, c .+ c,
             FOPlus (FOMult (FOPlus (FOSucc a) b) (FOSucc (FOPlus (FOSucc a) b))) (b .+ b));
            (.S (.S .0), b .+ #498, c); (.S (.S .0), .0, #498)]; exact Z.
  - lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (E : FOPrH n Gc (FOEq c (FOPlus b (FOVar 498)))) by (apply FOPrH_eq_sym; wk_in)
    end.
    unfold FOle. apply (FOPrH_ex_intro _ _ 498 (FOVar 499)); [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_eq, FOsubst_t_plus, !FOsubst_t_succ, FOsubst_t_var_eq'.
    subst_avoid_h Hav.
    fo_lin [(.S .0, c, b .+ #498); (.S .0, #498, .S #499)]; exact E.
Qed.

(** ** The step clauses of the numeral rows.

    Tag [5] computes the code of a numeral, tag [0] the occurrence of a
    variable in a term and tag [2] the substitution into a term; on the
    code [1] of [0] and the code [cpair 2 t] of a successor each clause
    holds from the row of [t]. *)

Ltac ok_row :=
  lazymatch goal with
  | |- FOsubst_ok _ ?s _ = true =>
      let V := fresh "V" in assert (V : FOtm_avoid s 20 122) by avoid_tm;
      solve [auto 100 with fook]
  end.

Ltac row_bex s :=
  lazymatch goal with
  | |- FOPrH _ _ (FOBexC ?x ?t _) =>
      apply (FOPrH_bex_intro_t _ _ x t s);
      [lia | lia | avoid_tm | avoid_tm | avoid_tm | avoid_tm | | ok_row |
       autorewrite with fosubst; subst_avoid_h_all ]
  end
with subst_avoid_h_all :=
  repeat match goal with
         | H : FOtms_avoid _ _ _ |- _ => progress subst_avoid_h H
         end.

Section NumRows.
Variables (n : nat) (G : list FOFormula) (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm).

Lemma FOPrH_case5_zero : forall r,
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero r) ->
  FOPrH n G (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 5) FOZero FOZero
               FOZero r).
Proof.
  intros r H. unfold FODISPCASES. do 5 apply FOPrH_or_intro_r.
  apply FOPrH_and_intro; [apply FOPrH_refl|].
  unfold FOSTEP5. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [apply FOPrH_refl | exact H].
Qed.

Lemma FOPrH_case5_succ : forall x r r',
  FOPrH n G (FOlookup 54 ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 5) x FOZero FOZero r) ->
  FOPrH n G (FOcpairF (FOnumeral 2) r r') ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; x; r; r'] 20 122 ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; x; r; r'] 420 500 ->
  FOPrH n G (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 5) (FOSucc x) FOZero
               FOZero r').
Proof.
  intros x r r' HL HC Hav Hav2. unfold FODISPCASES. do 5 apply FOPrH_or_intro_r.
  apply FOPrH_and_intro; [apply FOPrH_refl|].
  unfold FOSTEP5. apply FOPrH_or_intro_r.
  row_bex x; [apply FOPrH_le_refl; avoid_tm|].
  apply FOPrH_and_intro; [apply FOPrH_refl|].
  row_bex r; [exact (FOPrH_cpair_lt _ _ _ _ _ HC ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact HL | exact HC].
Qed.

Lemma FOPrH_case0_zero : forall w tc,
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero tc) ->
  FOPrH n G (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len FOZero w tc FOZero FOZero).
Proof.
  intros w tc H. unfold FODISPCASES. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [apply FOPrH_refl|].
  unfold FOSTEP0. apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [exact H | apply FOPrH_refl].
Qed.

Lemma FOPrH_case0_succ : forall w t tc r,
  FOPrH n G (FOlookup 52 ct dt c1 d1 c2 d2 c3 d3 cr dr len FOZero w t FOZero r) ->
  FOPrH n G (FOcpairF (FOnumeral 2) t tc) ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; w; t; tc; r] 20 122 ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; w; t; tc; r] 420 500 ->
  FOPrH n G (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len FOZero w tc FOZero r).
Proof.
  intros w t tc r HL HC Hav Hav2. unfold FODISPCASES. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [apply FOPrH_refl|].
  unfold FOSTEP0. do 2 apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  row_bex t.
  { destruct (FOPrH_cpair_le_cf n G (FOnumeral 2) t tc ltac:(avoid_tms) HC) as [_ Hle].
    unfold FOle in Hle |- *.
    refine (FOPrH_mp _ _ _ _ _ Hle). apply FOPrH_empty. apply FOPrH_intro.
    refine (FOPrH_ex_elim _ _ 498 (FOEq (FOPlus t (FOVar 498)) tc) _ _ _ _ _);
      [free_ctx | free_fm | apply FOPrH_last |].
    apply (FOPrH_ex_intro _ _ 498 (FOVar 498)); [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_id.
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (E : FOPrH n Gc (FOEq tc (FOPlus t (FOVar 498)))) by (apply FOPrH_eq_sym; wk_in)
    end.
    fo_lin [(.S .0, tc, t .+ #498)]; exact E. }
  apply FOPrH_and_intro; [exact HC | exact HL].
Qed.

Lemma FOPrH_case2_zero : forall x sc tc,
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero tc) ->
  FOPrH n G (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 2) x sc tc tc).
Proof.
  intros x sc tc H. unfold FODISPCASES. do 2 apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [apply FOPrH_refl|].
  unfold FOSTEP2. apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [exact H | apply FOPrH_refl].
Qed.

Lemma FOPrH_case2_succ : forall x sc t t' tc r,
  FOPrH n G (FOlookup 54 ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 2) x sc t t') ->
  FOPrH n G (FOcpairF (FOnumeral 2) t tc) -> FOPrH n G (FOcpairF (FOnumeral 2) t' r) ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; x; sc; t; t'; tc; r] 20 122 ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; x; sc; t; t'; tc; r] 420 500 ->
  FOPrH n G (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 2) x sc tc r).
Proof.
  intros x sc t t' tc r HL HC HC' Hav Hav2. unfold FODISPCASES.
  do 2 apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [apply FOPrH_refl|].
  unfold FOSTEP2. do 2 apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  row_bex t.
  { destruct (FOPrH_cpair_le_cf n G (FOnumeral 2) t tc ltac:(avoid_tms) HC) as [_ Hle].
    unfold FOle in Hle |- *.
    refine (FOPrH_mp _ _ _ _ _ Hle). apply FOPrH_empty. apply FOPrH_intro.
    refine (FOPrH_ex_elim _ _ 498 (FOEq (FOPlus t (FOVar 498)) tc) _ _ _ _ _);
      [free_ctx | free_fm | apply FOPrH_last |].
    apply (FOPrH_ex_intro _ _ 498 (FOVar 498)); [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_id.
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (E : FOPrH n Gc (FOEq tc (FOPlus t (FOVar 498)))) by (apply FOPrH_eq_sym; wk_in)
    end.
    fo_lin [(.S .0, tc, t .+ #498)]; exact E. }
  apply FOPrH_and_intro; [exact HC|].
  row_bex t'; [exact (FOPrH_cpair_lt _ _ _ _ _ HC' ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact HL | exact HC'].
Qed.

End NumRows.
