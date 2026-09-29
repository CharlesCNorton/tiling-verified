From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32.
Open Scope fo_scope.

(** ** Entries of a term list. *)

Lemma FOtm_avoid_nth : forall s env lo hi,
  FOtms_avoid env lo hi -> FOtm_avoid (nth s env FOZero) lo hi.
Proof.
  intros s env lo hi H. destruct (nth_in_or_default s env FOZero) as [Hin| ->];
    [exact (H _ Hin) | apply FOtm_avoid_zero].
Qed.

Ltac avoid_tm ::=
  lazymatch goal with
  | |- FOtm_avoid (nth _ _ _) _ _ => apply FOtm_avoid_nth; avoid_tms
  | |- FOtm_avoid (FOnumeral _) _ _ => apply FOtm_avoid_numeral
  | |- FOtm_avoid FOZero _ _ => apply FOtm_avoid_zero
  | |- FOtm_avoid (FOSucc _) _ _ => apply FOtm_avoid_succ; avoid_tm
  | |- FOtm_avoid (FOPlus _ _) _ _ => apply FOtm_avoid_plus; avoid_tm
  | |- FOtm_avoid (FOMult _ _) _ _ => apply FOtm_avoid_mult; avoid_tm
  | |- FOtm_avoid (FOVar _) _ _ =>
      first [ apply FOtm_avoid_var_b; vm_compute; reflexivity
            | apply FOtm_avoid_var; lia ]
  | |- FOtm_avoid ?t ?lo ?hi =>
      match goal with
      | H : FOtms_avoid ?L ?lo' ?hi' |- _ =>
          apply (FOtm_avoid_sub t lo' hi' lo hi); [apply H; in_list | nat_fast | nat_fast]
      end
  end.

Ltac fr_tm ::=
  lazymatch goal with
  | |- FOin_tm ?w (nth _ _ _) = false =>
      apply (FOtm_avoid_nth _ _ w (S w)); [avoid_tms | lia | lia]
  | |- FOin_tm _ (FOVar _) = false => apply FOin_tm_var_ne; nat_fast
  | |- FOin_tm _ (FOnumeral _) = false => apply FOin_tm_numeral
  | |- FOin_tm _ FOZero = false => reflexivity
  | |- FOin_tm _ (FOSucc _) = false => rewrite FOin_tm_succ_eq; fr_tm
  | |- FOin_tm _ (FOPlus _ _) = false =>
      rewrite FOin_tm_plus_eq; apply Bool.orb_false_iff; split; fr_tm
  | |- FOin_tm _ (FOMult _ _) = false =>
      rewrite FOin_tm_mult_eq; apply Bool.orb_false_iff; split; fr_tm
  | |- FOin_tm ?w ?t = false =>
      match goal with H : FOtms_avoid ?L ?lo ?hi |- _ =>
        apply (H t ltac:(in_list) w); nat_fast end
  end.

(** ** Patterns with the same code.

    [CPrel G env env' p p']: the patterns [p] over [env] and [p'] over
    [env'] have the same code, slot by slot: equal slot values, a slot
    whose value codes [0] against the pattern of [0], a slot whose
    value codes a successor against the successor pattern of a slot. *)

Inductive CPrel (n : nat) (G : list FOFormula) (env env' : list FOTerm) : CPat -> CPat -> Prop :=
  | cpr_lit : forall k, CPrel n G env env' (CLit k) (CLit k)
  | cpr_slot : forall s s',
      FOPrH n G (FOEq (nth s env FOZero) (nth s' env' FOZero)) ->
      CPrel n G env env' (CVarP s) (CVarP s')
  | cpr_zero_l : forall s,
      FOPrH n G (FOcpairF (FOnumeral 1) FOZero (nth s env FOZero)) ->
      CPrel n G env env' (CVarP s) tZeroP
  | cpr_zero_r : forall s',
      FOPrH n G (FOcpairF (FOnumeral 1) FOZero (nth s' env' FOZero)) ->
      CPrel n G env env' tZeroP (CVarP s')
  | cpr_succ_l : forall s s',
      FOPrH n G (FOcpairF (FOnumeral 2) (nth s' env' FOZero) (nth s env FOZero)) ->
      CPrel n G env env' (CVarP s) (tSuccP (CVarP s'))
  | cpr_succ_r : forall s s',
      FOPrH n G (FOcpairF (FOnumeral 2) (nth s env FOZero) (nth s' env' FOZero)) ->
      CPrel n G env env' (tSuccP (CVarP s)) (CVarP s')
  | cpr_csucc : forall a a', CPrel n G env env' a a' ->
      CPrel n G env env' (CSuccP a) (CSuccP a')
  | cpr_pair : forall a b a' b', CPrel n G env env' a a' -> CPrel n G env env' b b' ->
      CPrel n G env env' (CPair a b) (CPair a' b').

Lemma CPrel_weaken : forall n G G' env env' p p',
  (forall X, In X G -> In X G') -> CPrel n G env env' p p' -> CPrel n G' env env' p p'.
Proof.
  intros n G G' env env' p p' Hinc H.
  induction H; constructor; try assumption; exact (FOPrH_weaken n G G' _ Hinc H).
Qed.

Lemma CPrel_refl : forall n G env p, (forall s, cpat_occurs s p = true -> True) ->
  CPrel n G env env p p.
Proof.
  intros n G env p _. induction p as [k|s|q IH|a IHa b IHb].
  - constructor.
  - constructor. apply FOPrH_refl.
  - constructor. exact IH.
  - constructor; assumption.
Qed.

Lemma cpat_span_tZeroP : cpat_span tZeroP = 4.
Proof. reflexivity. Qed.

Lemma cpat_span_tSuccP_slot : forall s, cpat_span (tSuccP (CVarP s)) = 4.
Proof. reflexivity. Qed.

(** ** Pattern facts converted along [CPrel]. *)

Lemma FOPrH_patf_conv : forall n G env env' p p',
  CPrel n G env env' p p' ->
  forall G' B B' d, (forall X, In X G -> In X G') ->
  FOPrH n G' (FOPATF B' env' p' d) ->
  500 <= B -> 500 <= B' -> B + cpat_span p <= B' \/ B' + cpat_span p' <= B ->
  FOctx_avoid G' B' (B' + cpat_span p') ->
  FOtms_avoid (d :: env ++ env') B (B + cpat_span p) ->
  FOtms_avoid (d :: env ++ env') B' (B' + cpat_span p') ->
  FOtms_avoid (d :: env ++ env') 420 500 ->
  FOPrH n G' (FOPATF B env p d).
Proof.
  intros n G env env' p p' HR.
  induction HR as [k|s s' E|s E|s' E|s s' E|s s' E|a a' HR IH|a b a' b' HRa IHa HRb IHb];
    intros G' B B' d Hinc H HB HB' Hdis HG Hav Hav' Hlo.
  - exact H.
  - cbn [FOPATF] in H |- *.
    exact (FOPrH_eq_trans _ _ _ _ _ H (FOPrH_eq_sym _ _ _ _ (FOPrH_weaken n G G' _ Hinc E))).
  - cbn [FOPATF]. unfold tZeroP in *. cbn [cpat_span cpat_pairs] in *.
    apply (FOPrH_patf_leaf_elim n G' B' env' 1 0 d _ H ltac:(lia) HG);
      [intros w ? ?; free_fm | avoid_tms |].
    lazymatch goal with |- FOPrH _ (?G1 ++ [?X]) _ =>
      exact (FOPrH_cpair_fun n (G1 ++ [X]) _ _ d (nth s env FOZero) ltac:(avoid_tms)
               (FOPrH_last n G1 X)
               (FOPrH_weak_app _ _ _ _ (FOPrH_weaken n G G' _ Hinc E)))
    end.
  - cbn [FOPATF] in H. unfold tZeroP in *. cbn [cpat_span cpat_pairs] in *.
    pose proof (FOPrH_cpairF_cong _ _ _ _ _ _ _ _ (FOPrH_refl _ _ _) (FOPrH_refl _ _ _)
                  (FOPrH_eq_sym _ _ _ _ H) (FOPrH_weaken n G G' _ Hinc E)) as Hc.
    apply (FOPrH_patf_pair_intro n G' B env (CLit 1) (CLit 0) d (FOnumeral 1) FOZero Hc
             (FOPrH_patf_lit _ _ _ _ _) (FOPrH_patf_lit _ _ _ _ 0) HB);
      [cbn [cpat_span cpat_pairs] in Hav |- *; avoid_tms | avoid_tms].
  - cbn [FOPATF]. unfold tSuccP in *. cbn [cpat_span cpat_pairs] in *.
    apply (FOPrH_patf_lit_elim n G' B' env' 2 (CVarP s') d _ H ltac:(lia) HG);
      [intros w ? ?; cbn [cpat_span cpat_pairs] in *; free_fm
      | cbn [cpat_span cpat_pairs]; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (H1 : FOPrH n G1 (FOcpairF (FOnumeral 2) (FOVar (B' + 2)) d)) by wk_in;
      assert (H2 : FOPrH n G1 (FOEq (FOVar (B' + 2)) (nth s' env' FOZero))) by wk_in;
      pose proof (FOPrH_cpairF_cong _ _ _ _ _ _ _ _ (FOPrH_refl _ _ _) H2 (FOPrH_refl _ _ _) H1)
        as H3;
      exact (FOPrH_cpair_fun n G1 _ _ d (nth s env FOZero) ltac:(avoid_tms) H3
               (FOPrH_weak_app _ _ _ _ (FOPrH_weaken n G G' _ Hinc E)))
    end.
  - cbn [FOPATF] in H. unfold tSuccP in *. cbn [cpat_span cpat_pairs] in *.
    pose proof (FOPrH_cpairF_cong _ _ _ _ _ _ _ _ (FOPrH_refl _ _ _) (FOPrH_refl _ _ _)
                  (FOPrH_eq_sym _ _ _ _ H) (FOPrH_weaken n G G' _ Hinc E)) as Hc.
    apply (FOPrH_patf_pair_intro n G' B env (CLit 2) (CVarP s) d (FOnumeral 2)
             (nth s env FOZero) Hc (FOPrH_patf_lit _ _ _ _ _) (FOPrH_patf_slot _ _ _ _ s) HB);
      [cbn [cpat_span cpat_pairs] in Hav |- *; avoid_tms | avoid_tms].
  - cbn [cpat_span] in Hdis, HG, Hav, Hav'.
    apply (FOPrH_patf_succ_elim_self n G' B' env' a' d _ H HB');
      [cbn [cpat_span]; exact HG | intros w H1 H2; cbn [cpat_span] in H2; free_fm
      | cbn [cpat_span]; avoid_tms |].
    lazymatch goal with |- FOPrH _ (?G0 ++ [?X]) _ => pose proof (FOPrH_last n G0 X) as HX end.
    pose proof (IH _ (B + 2) (B' + 2) (FOVar B')
                  (fun X HX0 => in_or_app _ _ _ (or_introl (Hinc X HX0)))
                  (FOPrH_and_r _ _ _ _ HX) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms))
      as Hq.
    exact (FOPrH_patf_succ_intro n _ B env a d (FOVar B') (FOPrH_and_l _ _ _ _ HX) Hq HB
             ltac:(cbn [cpat_span]; avoid_tms) ltac:(avoid_tms)).
  - pose proof (cpat_span_le a) as Hsa. pose proof (cpat_span_le a') as Hsa'.
    cbn [cpat_span] in Hdis, HG, Hav, Hav'.
    apply (FOPrH_patf_pair_elim_self n G' B' env' a' b' d _ H HB');
      [cbn [cpat_span]; exact HG | intros w H1 H2; cbn [cpat_span] in H2; free_fm
      | cbn [cpat_span]; avoid_tms |].
    lazymatch goal with |- FOPrH _ (?G0 ++ [?X]) _ => pose proof (FOPrH_last n G0 X) as HX end.
    assert (Hinc' : forall X, In X G -> In X (G' ++ [FOAnd (FOcpairF (FOVar B') (FOVar (B' + 2)) d)
                   (FOAnd (FOPATF (B' + 4) env' a' (FOVar B'))
                      (FOPATF (B' + 4 + 4 * cpat_pairs a') env' b' (FOVar (B' + 2))))]))
      by (intros X HX0; apply in_or_app; left; exact (Hinc X HX0)).
    pose proof (IHa _ (B + 4) (B' + 4) (FOVar B') Hinc'
                  (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ HX)) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms))
      as Ha.
    pose proof (IHb _ (B + 4 + 4 * cpat_pairs a) (B' + 4 + 4 * cpat_pairs a') (FOVar (B' + 2))
                  Hinc' (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ HX)) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms))
      as Hb.
    exact (FOPrH_patf_pair_intro n _ B env a b d (FOVar B') (FOVar (B' + 2))
             (FOPrH_and_l _ _ _ _ HX) Ha Hb HB ltac:(cbn [cpat_span]; avoid_tms)
             ltac:(avoid_tms)).
Qed.
