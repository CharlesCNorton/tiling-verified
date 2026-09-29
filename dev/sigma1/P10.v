From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9.
Open Scope fo_scope.

(** ** Code patterns inside the tower.

    A pattern node [CPair a b] matched at base [B] names its two
    components by bounded witnesses; elimination renames them to
    fresh variables, introduction supplies them. *)

Lemma FOsubst_map_avoid : forall x s env,
  (forall t, In t env -> FOin_tm x t = false) -> map (FOsubst_t x s) env = env.
Proof.
  intros x s env H. induction env as [|t env IH]; [reflexivity|].
  cbn [map]. rewrite (FOsubst_t_not_in t x s (H t (or_introl eq_refl))).
  rewrite IH; [reflexivity|]. intros t' Ht'. apply H. right. exact Ht'.
Qed.

Lemma FOtms_avoid_env : forall env lo hi x, FOtms_avoid env lo hi -> lo <= x -> x < hi ->
  forall t, In t env -> FOin_tm x t = false.
Proof. intros env lo hi x H H1 H2 t Ht. exact (H t Ht x H1 H2). Qed.

(** Existential elimination at a renamed variable, the body cleaned by
    a separate computation before the continuation sees it. *)

Lemma FOPrH_exe_clean : forall n G z w A A' C,
  FOPrH n G (FOExists z A) ->
  FOfree_ctx w G -> FOfree_in w C = false -> FOfree_in w A = false ->
  FOsubst_ok z (FOVar w) A = true ->
  FOPrH n [FOsubst_f z (FOVar w) A] A' ->
  FOPrH n (G ++ [A']) C -> FOPrH n G C.
Proof.
  intros n G z w A A' C H HG HC HA Hok HK H0.
  refine (FOPrH_exe n G z w A C H HG HC HA Hok _).
  refine (FOPrH_cut _ _ A' _ _ _).
  - refine (FOPrH_ctxfree _ _ _ _ HK (FOPrH_last _ _ _)).
  - refine (FOPrH_weaken n _ _ _ _ H0).
    intros X HX. apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
    + apply in_or_app. left. apply in_or_app. left. exact HX.
    + apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPrH_patf_pair_elim : forall n G B env a b d u w C,
  FOPrH n G (FOPATF B env (CPair a b) d) ->
  2 <= u -> 2 <= w -> u <> w ->
  (u < B \/ B + cpat_span (CPair a b) <= u) -> (w < B \/ B + cpat_span (CPair a b) <= w) ->
  FOfree_ctx u G -> FOfree_ctx w G -> FOfree_in u C = false -> FOfree_in w C = false ->
  FOtms_avoid (d :: env) B (B + cpat_span (CPair a b)) ->
  FOtms_avoid (d :: env) u (S u) -> FOtms_avoid (d :: env) w (S w) ->
  FOPrH n (G ++ [FOAnd (FOcpairF (FOVar u) (FOVar w) d)
                   (FOAnd (FOPATF (B + 4) env a (FOVar u))
                          (FOPATF (B + 4 + 4 * cpat_pairs a) env b (FOVar w)))]) C ->
  FOPrH n G C.
Proof.
  intros n G B env a b d u w C H Hu Hw Huw HuB HwB HGu HGw HCu HCw Hav Havu Havw H0.
  pose proof (cpat_span_le a) as Ha. cbn [cpat_span] in HuB, HwB, Hav.
  assert (Henv : FOtms_avoid env B (B + (4 + 4 * cpat_pairs a + cpat_span b))).
  { intros t Ht. apply Hav. right. exact Ht. }
  assert (Hd : FOtm_avoid d B (B + (4 + 4 * cpat_pairs a + cpat_span b))).
  { apply Hav. left. reflexivity. }
  assert (Henvu : FOtms_avoid env u (S u)) by (intros t Ht; apply Havu; right; exact Ht).
  assert (Henvw : FOtms_avoid env w (S w)) by (intros t Ht; apply Havw; right; exact Ht).
  assert (Hdu : FOtm_avoid d u (S u)) by (apply Havu; left; reflexivity).
  assert (Hdw : FOtm_avoid d w (S w)) by (apply Havw; left; reflexivity).
  cbn [FOPATF] in H. rewrite FOBexC_ltv in H.
  set (Clean1 := FOBexC (B + 2) (FOSucc d)
                   (FOAnd (FOcpairF (FOVar u) (FOVar (B + 2)) d)
                      (FOAnd (FOPATF (B + 4) env a (FOVar u))
                         (FOPATF (B + 4 + 4 * cpat_pairs a) env b (FOVar (B + 2)))))).
  refine (FOPrH_exe_clean n G B u _ Clean1 C H HGu HCu _ _ _ _).
  { rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
    - apply FOfree_in_ltv; [lia | fr_tm].
    - rewrite FOBexC_ltv. rewrite FOfree_in_FOExists_neq by lia.
      rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split;
        [apply FOfree_in_ltv; [lia | fr_tm]|].
      rewrite !FOfree_in_FOAnd. apply Bool.orb_false_iff. split; [free_fm|].
      apply Bool.orb_false_iff. split; apply FOfree_in_PATF_any; try lia;
        (apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia | exact Henvu]). }
  { apply FOsubst_ok_and.
    - unfold FOltv. apply FOsubst_ok_ex; [apply FOin_tm_var_ne; lia | apply FOsubst_ok_eq].
    - apply FOsubst_ok_bex; [apply FOin_tm_var_ne; lia | apply FOin_tm_var_ne; lia|].
      apply FOsubst_ok_and; [apply FOsubst_ok_cpairF|].
      apply FOsubst_ok_and; apply FOsubst_ok_PATF; apply FOtm_avoid_var; lia. }
  { unfold Clean1.
    rewrite FOsubst_f_and, FOsubst_f_bex by lia.
    rewrite FOsubst_f_and, FOsubst_f_cpairF, FOsubst_f_and, !FOsubst_f_PATF by lia.
    rewrite !FOsubst_t_succ, FOsubst_t_var_eq', FOsubst_t_var_ne by lia.
    rewrite (FOsubst_t_not_in d B _ (Hd B ltac:(lia) ltac:(lia))).
    rewrite (FOsubst_map_avoid B _ env (FOtms_avoid_env env _ _ B Henv ltac:(lia) ltac:(lia))).
    apply (FOPrH_and_r n _ (FOsubst_f B (FOVar u) (FOltv B (FOSucc d)))).
    apply FOPrH_assum. left. reflexivity. }
  assert (HC1 : FOPrH n (G ++ [Clean1]) Clean1) by apply FOPrH_last.
  unfold Clean1 in HC1. rewrite FOBexC_ltv in HC1.
  refine (FOPrH_exe_clean n _ (B + 2) w _ _ C HC1 _ HCw _ _ _ _).
  { apply FOfree_ctx_app_inv; [exact HGw|].
    apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
    try unfold Clean1; try rewrite FOBexC_ltv. rewrite FOfree_in_FOExists_neq by lia.
    rewrite !FOfree_in_FOAnd. apply Bool.orb_false_iff. split;
      [apply FOfree_in_ltv; [lia | fr_tm]|].
    apply Bool.orb_false_iff. split; [free_fm|].
    apply Bool.orb_false_iff. split; apply FOfree_in_PATF_any; try lia;
      (apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia | exact Henvw]). }
  { rewrite !FOfree_in_FOAnd. apply Bool.orb_false_iff. split;
      [apply FOfree_in_ltv; [lia | fr_tm]|].
    apply Bool.orb_false_iff. split; [free_fm|].
    apply Bool.orb_false_iff. split; apply FOfree_in_PATF_any; try lia;
      (apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia | exact Henvw]). }
  { apply FOsubst_ok_and.
    - unfold FOltv. apply FOsubst_ok_ex; [apply FOin_tm_var_ne; lia | apply FOsubst_ok_eq].
    - apply FOsubst_ok_and; [apply FOsubst_ok_cpairF|].
      apply FOsubst_ok_and; apply FOsubst_ok_PATF; apply FOtm_avoid_var; lia. }
  { rewrite FOsubst_f_and. rewrite FOsubst_f_and, FOsubst_f_cpairF, FOsubst_f_and,
      !FOsubst_f_PATF by lia.
    rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne by lia.
    rewrite (FOsubst_t_not_in d (B + 2) _ (Hd (B + 2) ltac:(lia) ltac:(lia))).
    rewrite (FOsubst_map_avoid (B + 2) _ env
               (FOtms_avoid_env env _ _ (B + 2) Henv ltac:(lia) ltac:(lia))).
    apply (FOPrH_and_r n _ (FOsubst_f (B + 2) (FOVar w) (FOltv (B + 2) (FOSucc d)))).
    apply FOPrH_assum. left. reflexivity. }
  refine (FOPrH_weaken n _ _ _ _ H0).
  intros X HX. apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
  - apply in_or_app. left. apply in_or_app. left. exact HX.
  - apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPrH_le_succ_of_le : forall n G a b,
  FOPrH n G (FOle a b) -> FOtms_avoid [a; b] 498 499 -> FOPrH n G (FOle (FOSucc a) (FOSucc b)).
Proof.
  intros n G a b H Hav. unfold FOle in *.
  refine (FOPrH_mp _ _ _ _ _ H). apply FOPrH_empty. apply FOPrH_intro.
  refine (FOPrH_ex_elim _ _ 498 (FOEq (FOPlus a (FOVar 498)) b) _ _ _ _ _);
    [free_ctx | free_fm | apply FOPrH_last |].
  apply (FOPrH_ex_intro _ _ 498 (FOVar 498)); [cbn [FOsubst_ok]; reflexivity|].
  rewrite FOsubst_f_id.
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (E : FOPrH n Gc (FOEq b (FOPlus a (FOVar 498)))) by (apply FOPrH_eq_sym; wk_in)
  end.
  fo_lin [(.S .0, b, a .+ #498)]; exact E.
Qed.

Lemma FOPrH_patf_pair_intro : forall n G B env a b d u w,
  FOPrH n G (FOcpairF u w d) ->
  FOPrH n G (FOPATF (B + 4) env a u) ->
  FOPrH n G (FOPATF (B + 4 + 4 * cpat_pairs a) env b w) ->
  500 <= B ->
  FOtms_avoid (d :: u :: w :: env) B (B + cpat_span (CPair a b)) ->
  FOtms_avoid [d; u; w] 420 500 ->
  FOPrH n G (FOPATF B env (CPair a b) d).
Proof.
  intros n G B env a b d u w HC Ha Hb HB Hav Hav2.
  pose proof (cpat_span_le a) as Hsa. cbn [cpat_span] in Hav.
  assert (Henv : forall x, B <= x -> x < B + (4 + 4 * cpat_pairs a + cpat_span b) ->
            map (FOsubst_t x (FOVar 0)) env = env) by
    (intros x H1 H2; apply FOsubst_map_avoid; intros t Ht; apply (Hav t); [right; right; right; exact Ht | lia | lia]).
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
