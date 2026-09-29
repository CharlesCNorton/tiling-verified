From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7.
Open Scope fo_scope.

(** ** Substitution at a variable outside a builder's binders. *)

Lemma FOsubst_ok_not_free : forall A x s, FOfree_in x A = false -> FOsubst_ok x s A = true.
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB]; intros x s H; cbn in *.
  - reflexivity.
  - reflexivity.
  - apply Bool.orb_false_iff in H. destruct H as [H1 H2].
    rewrite (IHB x s H1), (IHC x s H2). reflexivity.
  - destruct (Nat.eqb y x); [reflexivity|]. rewrite H. reflexivity.
  - destruct (Nat.eqb y x); [reflexivity|]. rewrite H. reflexivity.
Qed.

Lemma FOsubst_f_bex_ne : forall x s v t A, x <> v -> x <> S v ->
  FOsubst_f x s (FOBexC v t A) = FOBexC v (FOsubst_t x s t) (FOsubst_f x s A).
Proof.
  intros x s v t A H1 H2. unfold FOBexC, FOAnd, FONeg. cbn [FOsubst_f FOsubst_t].
  nat_eqb_simpl. reflexivity.
Qed.

Lemma FOsubst_f_betaF_ne : forall x s v c d i y, x < v \/ v + 4 <= x ->
  FOsubst_f x s (FObetaF v c d i y) =
  FObetaF v (FOsubst_t x s c) (FOsubst_t x s d) (FOsubst_t x s i) (FOsubst_t x s y).
Proof.
  intros x s v c d i y H. unfold FObetaF.
  rewrite FOsubst_f_bex_ne by lia. rewrite FOsubst_f_and, FOsubst_f_eq.
  rewrite FOsubst_f_bex_ne by lia. rewrite FOsubst_f_eq.
  rewrite !FOsubst_t_plus, !FOsubst_t_mult, !FOsubst_t_succ, !FOsubst_t_var_ne by lia.
  reflexivity.
Qed.

Lemma FOsubst_f_lookup_ne : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r,
  x < B \/ B + 22 <= x ->
  FOsubst_f x s (FOlookup B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r) =
  FOlookup B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1) (FOsubst_t x s d1)
    (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3) (FOsubst_t x s d3)
    (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s tg) (FOsubst_t x s a1) (FOsubst_t x s a2) (FOsubst_t x s a3)
    (FOsubst_t x s r).
Proof.
  intros. unfold FOlookup.
  rewrite FOsubst_f_bex_ne by lia. rewrite !FOsubst_f_and.
  rewrite !FOsubst_f_betaF_ne by lia. rewrite FOsubst_t_var_ne by lia. reflexivity.
Qed.

Lemma FOsubst_f_TBLEX : forall x s tg a1 a2 a3 r, 13 <= x -> x < 28 \/ 50 <= x ->
  FOsubst_f x s (FOTBLEX tg a1 a2 a3 r) =
  FOTBLEX (FOsubst_t x s tg) (FOsubst_t x s a1) (FOsubst_t x s a2) (FOsubst_t x s a3)
    (FOsubst_t x s r).
Proof.
  intros x s tg a1 a2 a3 r H1 H2. unfold FOTBLEX.
  rewrite !FOsubst_f_ex_ne by lia. rewrite FOsubst_f_and.
  rewrite (FOsubst_f_not_free (FOTBLVALID 18 _ _ _ _ _ _ _ _ _ _ _) x s).
  - rewrite FOsubst_f_lookup_ne by lia. rewrite !FOsubst_t_var_ne by lia. reflexivity.
  - destruct (FOfree_in x (FOTBLVALID 18 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5)
                             (FOVar 6) (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11)
                             (FOVar 12))) eqn:E; [exfalso|reflexivity].
    apply FOTBLVALID_free in E. cbn [FOin_tm] in E.
    repeat match type of E with
           | _ \/ _ => destruct E as [E|E]; [apply Nat.eqb_eq in E; lia|]
           end.
    lia.
Qed.

Lemma FOsubst_ok_TBLEX : forall x s tg a1 a2 a3 r, 13 <= x ->
  FOtm_avoid s 2 50 -> FOsubst_ok x s (FOTBLEX tg a1 a2 a3 r) = true.
Proof.
  intros x s tg a1 a2 a3 r Hx V. unfold FOTBLEX.
  repeat (apply FOsubst_ok_ex; [apply V; lia|]).
  apply FOsubst_ok_and.
  - apply FOsubst_ok_not_free.
    destruct (FOfree_in x (FOTBLVALID 18 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5)
                             (FOVar 6) (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11)
                             (FOVar 12))) eqn:E; [exfalso|reflexivity].
    apply FOTBLVALID_free in E. cbn [FOin_tm] in E.
    repeat match type of E with
           | _ \/ _ => destruct E as [E|E]; [apply Nat.eqb_eq in E; lia|]
           end.
    lia.
  - apply FOsubst_ok_lookup. intros w ? ?. apply V; lia.
Qed.

(** ** The rows of each numeral. *)

Lemma FOPrH_num5_zero : forall n G, FOctx_avoid G 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 5) FOZero FOZero FOZero (FOnumeral 1)).
Proof.
  intros n G HG. apply FOPrH_tab_base; [exact HG | tab_side |].
  apply FOPrH_case5_zero. apply FOPrH_cpair_one.
Qed.

Lemma FOPrH_num5_succ : forall n G x m m',
  FOctx_avoid G 2 500 -> FOtms_avoid [x; m; m'] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 5) x FOZero FOZero m) ->
  FOPrH n G (FOcpairF (FOnumeral 2) m m') ->
  FOPrH n G (FOTBLEX (FOnumeral 5) (FOSucc x) FOZero FOZero m').
Proof.
  intros n G x m m' HG Hav HE HC.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  apply (FOPrH_case5_succ n G' _ _ _ _ _ _ _ _ _ _ _ x m m');
    [ apply (FOPrH_lookup_rebase _ _ 28 54);
      [exact HL | lia | lia | lia | lia | lia | tab_side | tab_side]
    | exact (FOPrH_weaken n G G' _ Hinc HC) | tab_side | tab_side ].
Qed.

Lemma FOPrH_num2_zero : forall n G v s, FOctx_avoid G 2 500 -> FOtms_avoid [v; s] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 2) v s (FOnumeral 1) (FOnumeral 1)).
Proof.
  intros n G v s HG Hav. apply FOPrH_tab_base; [exact HG | tab_side |].
  apply FOPrH_case2_zero. apply FOPrH_cpair_one.
Qed.

Lemma FOPrH_num2_succ : forall n G v s m m',
  FOctx_avoid G 2 500 -> FOtms_avoid [v; s; m; m'] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 2) v s m m) ->
  FOPrH n G (FOcpairF (FOnumeral 2) m m') ->
  FOPrH n G (FOTBLEX (FOnumeral 2) v s m' m').
Proof.
  intros n G v s m m' HG Hav HE HC.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  pose proof (FOPrH_weaken n G G' _ Hinc HC) as HC'.
  apply (FOPrH_case2_succ n G' _ _ _ _ _ _ _ _ _ _ _ v s m m m' m');
    [ apply (FOPrH_lookup_rebase _ _ 28 54);
      [exact HL | lia | lia | lia | lia | lia | tab_side | tab_side]
    | exact HC' | exact HC' | tab_side | tab_side ].
Qed.

Lemma FOPrH_num0_zero : forall n G y, FOctx_avoid G 2 500 -> FOtms_avoid [y] 2 500 ->
  FOPrH n G (FOTBLEX FOZero y (FOnumeral 1) FOZero FOZero).
Proof.
  intros n G y HG Hav. apply FOPrH_tab_base; [exact HG | tab_side |].
  apply FOPrH_case0_zero. apply FOPrH_cpair_one.
Qed.

Lemma FOPrH_num0_succ : forall n G y m m',
  FOctx_avoid G 2 500 -> FOtms_avoid [y; m; m'] 2 500 ->
  FOPrH n G (FOTBLEX FOZero y m FOZero FOZero) ->
  FOPrH n G (FOcpairF (FOnumeral 2) m m') ->
  FOPrH n G (FOTBLEX FOZero y m' FOZero FOZero).
Proof.
  intros n G y m m' HG Hav HE HC.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  apply (FOPrH_case0_succ n G' _ _ _ _ _ _ _ _ _ _ _ y m m' FOZero);
    [ apply (FOPrH_lookup_rebase _ _ 28 52);
      [exact HL | lia | lia | lia | lia | lia | tab_side | tab_side]
    | exact (FOPrH_weaken n G G' _ Hinc HC) | tab_side | tab_side ].
Qed.

Lemma FOPrH_cpair_elim_hi : forall n G a b w C,
  FOctx_avoid G 420 500 ->
  FOtms_avoid [a; b] 420 500 ->
  500 <= w ->
  FOfree_ctx w G -> FOfree_in w C = false ->
  FOtms_avoid [a; b] w (S w) ->
  FOPrH n (G ++ [FOcpairF a b (FOVar w)]) C ->
  FOPrH n G C.
Proof.
  intros n G a b w C HG Hav Hw HGw HCw Hav1 H0.
  pose proof (FOPrH_thm n G _ (FOPr_cpair_total n)) as H.
  assert (V1 : FOtm_avoid a 420 500) by avoid_tm.
  assert (V2 : FOtm_avoid b 420 500) by avoid_tm.
  fo_inst_g H a V1 Hav. fo_inst_g H b V2 Hav.
  exe_named H w.
  subst_goal Hav.
  exact H0.
Qed.

(** ** Every number has a numeral code with its rows.

    [FONUMR x m]: [m] is the tag-[5] row value at [x], every
    substitution into [m] has its tag-[2] row, and every variable has
    its tag-[0] row in [m]. *)

Definition FONUMR (x m : FOTerm) : FOFormula :=
  FOAnd (FOTBLEX (FOnumeral 5) x FOZero FOZero m)
  (FOAnd (FOForall 802 (FOForall 803 (FOTBLEX (FOnumeral 2) (FOVar 802) (FOVar 803) m m)))
         (FOForall 804 (FOTBLEX FOZero (FOVar 804) m FOZero FOZero))).

Ltac free_fm ::=
  lazymatch goal with
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

Lemma FOsubst_f_NUMR : forall z s x m, 13 <= z -> 50 <= z -> z <> 802 -> z <> 803 ->
  z <> 804 -> FOtms_avoid [s] 802 805 ->
  FOsubst_f z s (FONUMR x m) = FONUMR (FOsubst_t z s x) (FOsubst_t z s m).
Proof.
  intros z s x m H1 H2 H3 H4 H5 Hs. unfold FONUMR.
  rewrite !FOsubst_f_and, !FOsubst_f_all_ne by lia. rewrite !FOsubst_f_TBLEX by lia.
  rewrite !FOsubst_t_var_ne by lia. rewrite !FOsubst_t_zero, !FOsubst_t_numeral.
  reflexivity.
Qed.

Theorem FOPr_numr : forall n,
  FOProvesTn n (FOForall 800 (FOExists 801 (FONUMR (FOVar 800) (FOVar 801)))).
Proof.
  intro n. change (FOPrH n [] (FOForall 800 (FOExists 801 (FONUMR (FOVar 800) (FOVar 801))))).
  apply FOPrH_ind; [apply FOfree_ctx_nil|..].
  - rewrite FOsubst_f_ex_ne by lia. rewrite FOsubst_f_NUMR by (lia || avoid_tms).
    rewrite FOsubst_t_var_eq', FOsubst_t_var_ne by lia.
    apply (FOPrH_ex_intro _ _ 801 (FOnumeral 1)); [apply FOsubst_ok_numeral|].
    rewrite FOsubst_f_NUMR by (lia || avoid_tms).
    rewrite FOsubst_t_zero, FOsubst_t_var_eq'.
    unfold FONUMR. apply FOPrH_and_intro; [apply FOPrH_num5_zero; tab_side|].
    apply FOPrH_and_intro.
    + apply FOPrH_all_intro; [apply FOfree_ctx_nil|].
      apply FOPrH_all_intro; [apply FOfree_ctx_nil|].
      apply FOPrH_num2_zero; tab_side.
    + apply FOPrH_all_intro; [apply FOfree_ctx_nil|].
      apply FOPrH_num0_zero; tab_side.
  - rewrite FOsubst_f_ex_ne by lia. rewrite FOsubst_f_NUMR by (lia || avoid_tms).
    rewrite FOsubst_t_var_eq', FOsubst_t_var_ne by lia.
    refine (FOPrH_ex_elim _ _ 801 (FONUMR (FOVar 800) (FOVar 801)) _ _ _ _ _);
      [free_ctx | free_fm | apply FOPrH_last |].
    apply (FOPrH_cpair_elim_hi n _ (FOnumeral 2) (FOVar 801) 805);
      [tab_side | tab_side | lia | tab_side | tab_side | tab_side |].
    apply (FOPrH_ex_intro _ _ 801 (FOVar 805)).
    { assert (V : FOtm_avoid (FOVar 805) 2 50) by avoid_tm.
      unfold FONUMR. apply FOsubst_ok_and; [apply FOsubst_ok_TBLEX; [lia | exact V]|].
      apply FOsubst_ok_and.
      - apply FOsubst_ok_all; [fr_tm|]. apply FOsubst_ok_all; [fr_tm|].
        apply FOsubst_ok_TBLEX; [lia | exact V].
      - apply FOsubst_ok_all; [fr_tm|]. apply FOsubst_ok_TBLEX; [lia | exact V]. }
    rewrite FOsubst_f_NUMR by (lia || avoid_tms).
    rewrite FOsubst_t_succ, !FOsubst_t_var_eq', FOsubst_t_var_ne by lia.
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (IH : FOPrH n Gc (FONUMR (FOVar 800) (FOVar 801))) by wk_in;
      assert (HC : FOPrH n Gc (FOcpairF (FOnumeral 2) (FOVar 801) (FOVar 805))) by wk_in;
      assert (HGc : FOctx_avoid Gc 2 500) by tab_side
    end.
    unfold FONUMR in IH |- *.
    apply FOPrH_and_intro;
      [exact (FOPrH_num5_succ n _ (FOVar 800) (FOVar 801) (FOVar 805) HGc ltac:(tab_side)
                (FOPrH_and_l _ _ _ _ IH) HC)|].
    apply FOPrH_and_intro.
    + apply FOPrH_all_intro; [tab_side|]. apply FOPrH_all_intro; [tab_side|].
      pose proof (FOPrH_all_same _ _ _ _ (FOPrH_all_same _ _ _ _
                    (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ IH)))) as I2.
      exact (FOPrH_num2_succ n _ (FOVar 802) (FOVar 803) (FOVar 801) (FOVar 805)
               ltac:(tab_side) ltac:(tab_side) I2 HC).
    + apply FOPrH_all_intro; [tab_side|].
      pose proof (FOPrH_all_same _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ IH)))
        as I0.
      exact (FOPrH_num0_succ n _ (FOVar 804) (FOVar 801) (FOVar 805)
               ltac:(tab_side) ltac:(tab_side) I0 HC).
Qed.
