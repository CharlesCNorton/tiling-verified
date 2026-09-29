From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41
  P42 P43 P44 P45 P46 P47 P48 P49 P50 P51 P52 P53 P54.
Open Scope fo_scope.

(** ** Bounded quantifiers in the main induction. *)

Lemma fv_ltv : forall x v t, FOin_tm (S v) t = false ->
  FOfree_in x (FOltv v t) = (Nat.eqb v x || FOin_tm x t)%bool.
Proof.
  intros x v t HSv. unfold FOltv. cbn [FOfree_in FOin_tm].
  destruct (Nat.eqb_spec (S v) x) as [<-|HSvx].
  - rewrite HSv, (proj2 (Nat.eqb_neq v (S v)) ltac:(lia)). reflexivity.
  - rewrite Bool.orb_false_r. reflexivity.
Qed.

Lemma fv_bq : forall v t A x, FOin_tm v t = false -> FOin_tm (S v) t = false ->
  (FOfree_in x (FOForall v (FOImplF (FOltv v t) A)) = true <->
   FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) /\
  (FOfree_in x (FOExists v (FOAnd (FOltv v t) A)) = true <->
   FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)).
Proof.
  intros v t A x Hv HSv.
  assert (K : FOfree_in x (FOImplF (FOltv v t) A) = FOfree_in x (FOAnd (FOltv v t) A)).
  { unfold FOAnd, FONeg. cbn [FOfree_in]. rewrite !Bool.orb_false_r. reflexivity. }
  assert (M : forall X, (FOfree_in x X = FOfree_in x (FOImplF (FOltv v t) A)) ->
            (FOfree_in x (FOForall v X) = true <->
             FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) /\
            (FOfree_in x (FOExists v X) = true <->
             FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v))).
  { intros X HX. cbn [FOfree_in]. rewrite HX. cbn [FOfree_in]. rewrite (fv_ltv x v t HSv).
    destruct (Nat.eqb_spec v x) as [->|Hvx].
    - split; split; intros H; try discriminate;
        destruct H as [H|[_ H]]; try (rewrite Hv in H; discriminate); exfalso; exact (H eq_refl).
    - cbn [orb]. split; split; intros H.
      + apply Bool.orb_true_iff in H. destruct H as [H|H]; [left; exact H | right; split; [exact H | lia]].
      + apply Bool.orb_true_iff. destruct H as [H|[H _]]; [left; exact H | right; exact H].
      + apply Bool.orb_true_iff in H. destruct H as [H|H]; [left; exact H | right; split; [exact H | lia]].
      + apply Bool.orb_true_iff. destruct H as [H|[H _]]; [left; exact H | right; exact H]. }
  split.
  - exact (proj1 (M _ eq_refl)).
  - exact (proj2 (M _ (eq_sym K))).
Qed.

Lemma hsub_ball : forall h v t A, FOin_tm v t = false -> FOin_tm (S v) t = false ->
  hsub_f h (FOForall v (FOImplF (FOltv v t) A)) =
  FOForall v (FOImplF (FOltv v (hsub_tm h t)) (hsub_f (h_hide v h) A)).
Proof. intros h v t A H1 H2. cbn [hsub_f]. rewrite hsub_ltv by assumption. reflexivity. Qed.

Lemma hsub_bex : forall h v t A, FOin_tm v t = false -> FOin_tm (S v) t = false ->
  hsub_f h (FOExists v (FOAnd (FOltv v t) A)) =
  FOExists v (FOAnd (FOltv v (hsub_tm h t)) (hsub_f (h_hide v h) A)).
Proof.
  intros h v t A H1 H2. unfold FOAnd, FONeg. cbn [hsub_f]. rewrite hsub_ltv by assumption.
  reflexivity.
Qed.

Lemma bq_bounds : forall v t A W, FOvars_max (FOForall v (FOImplF (FOltv v t) A)) < W ->
  S v < W /\ FOvars_max A < W /\ FOmax_var_tm t < W.
Proof. intros v t A W H. unfold FOltv in H. cbn [FOvars_max FOmax_var_tm] in H. lia. Qed.

Lemma bq_bounds' : forall v t A W, FOvars_max (FOExists v (FOAnd (FOltv v t) A)) < W ->
  S v < W /\ FOvars_max A < W /\ FOmax_var_tm t < W.
Proof.
  intros v t A W H. unfold FOAnd, FONeg, FOltv in H. cbn [FOvars_max FOmax_var_tm] in H. lia.
Qed.

Lemma fv_neg : forall x A, FOfree_in x (FONeg A) = FOfree_in x A.
Proof. intros x A. unfold FONeg. cbn [FOfree_in]. apply Bool.orb_false_r. Qed.

Lemma hA_free : forall n G V h rho env v A w,
  (forall x, FOfree_in x A = true -> x <> v -> HOK n G V h rho env x) ->
  (w < 1000 \/ V <= w) -> w <> v -> FOfree_in w (hsub_f (h_hide v h) A) = false.
Proof.
  intros n G V h rho env v A w Hh Hw Hwv.
  destruct (FOfree_in w (hsub_f (h_hide v h) A)) eqn:E; [|reflexivity].
  destruct (FOfree_in_hsub A (h_hide v h) w E) as [x [Hx Ex]]. unfold h_hide in Ex.
  destruct (Nat.eqb_spec x v) as [->|Hxv]; [congruence|].
  pose proof (HOK_range n G V h rho env x (Hh x Hx Hxv)). lia.
Qed.

Lemma D0P_ball : forall n k W v t A, FOin_tm v t = false -> FOin_tm (S v) t = false ->
  D0P n k W A -> D0P n k W (FOForall v (FOImplF (FOltv v t) A)).
Proof.
  intros n k W v t A Hvt HSvt IHA HW V G h rho env HI Hhw.
  destruct (bq_bounds v t A W HW) as [HWv [HWA HWt]].
  assert (HS : forall x, FOfree_in x (FOForall v (FOImplF (FOltv v t) A)) = true <->
               FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v))
    by (intros x; exact (proj1 (fv_bq v t A x Hvt HSvt))).
  pose proof (Inv_weaken n V G h rho env _
                (fun x => FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) HI
                ltac:(intros x Hx; apply HS; exact Hx)) as HI'.
  assert (Hhw' : forall x, FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v) -> W <= h x)
    by (intros x Hx; apply Hhw; apply HS; exact Hx).
  pose proof HI' as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (Hht : forall x, FOin_tm x t = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; left; exact Hx).
  assert (HhA : forall x, FOfree_in x A = true -> x <> v -> HOK n G V h rho env x)
    by (intros x Hx Hxv; apply Hh; right; split; assumption).
  destruct (hsub_facts t n G V h rho env Hht) as [Ht0 Htv].
  assert (HtW : forall w, w < W -> FOin_tm w (hsub_tm h t) = false).
  { intros w Hw. destruct (FOin_tm w (hsub_tm h t)) eqn:E; [|reflexivity].
    destruct (FOin_tm_hsub t h w E) as [x [Hx <-]]. specialize (Hhw' x (or_introl Hx)). lia. }
  assert (HWA' : FOfree_in W A = false) by (apply FOfree_in_above; lia).
  assert (HWt' : FOin_tm W t = false) by (apply FOin_tm_above; lia).
  rewrite !hsub_ball by assumption.
  split.
  - intros HB.
    refine (PRI_numr_ex n _ _ V W G _ env (hsub_tm h t) _ _ _ _ _ _);
      [lia | avoid_tms | intros w' ?; fr_tm | avoid_tms | above_tac |].
    intros w Hw HWw.
    lazymatch goal with |- PRI _ _ _ _ ?G2 _ _ =>
      assert (HG2 : FOctx_avoid G2 0 1000) by (intros w' ? ?; free_ctx);
      assert (HG2V : forall w', S w <= w' -> FOfree_ctx w' G2) by (intros w' ?; free_ctx);
      assert (Hinc2 : forall X, In X G -> In X G2)
        by (intros X HX; apply in_or_app; left; exact HX);
      assert (N2 : FOPrH n G2 (FONUMR (hsub_tm h t) (FOVar w))) by wk_in;
      assert (HB2 : FOPrH n G2 (FOForall v (FOImplF (FOltv v (hsub_tm h t))
                                              (hsub_f (h_hide v h) A)))) by wk HB
    end.
    pose proof (Inv_move n V (S w) G _ h rho env _ HI' Hinc2 ltac:(lia) HG2 HG2V) as HIm.
    pose proof (BALL_GEN n k W v A HWA HWv
                  (fun V' G' h' rho' env' HI0 Hh0 HD =>
                     proj1 (IHA HWA V' G' h' rho' env' HI0 Hh0) HD)
                  (S w) _ h rho env (hsub_tm h t) (FOVar w) W ltac:(lia) (le_n W)
                  (Inv_weaken n (S w) _ h rho env _ _ HIm ltac:(intros x Hx; right; exact Hx))
                  ltac:(intros x Hx Hxv; apply Hhw'; right; split; assumption)
                  ltac:(avoid_tms) ltac:(above_tac) HtW N2 HB2) as PB.
    unfold ballQ in PB.
    pose proof (Inv_slot n (S w) _ h rho env _ (hsub_tm h t) (FOVar w) W HIm N2 ltac:(avoid_tms)
                  ltac:(intros s [<-|[]] w' Hw'; apply FOin_tm_var_ne; lia)
                  ltac:(intros x [Hx|[Hx _]] E; subst x; congruence)) as HI3.
    destruct HI3 as [HV3 [HG03 [HGV3 [HE3 [Henv3 [Hr3 Hh3]]]]]].
    pose proof (PRI_teval t n k (S w) _ h _ _ W (length env) HV3 HG03 HGV3 HE3 Henv3 Hr3
                  ltac:(intros x Hx; apply Hh3; left; exact Hx) HWt'
                  (rho_sub_eq W (length env) rho) ltac:(rewrite length_app; cbn [length]; lia)
                  ltac:(rewrite nth_snoc_len; exact N2)) as TT.
    pose proof (PRI_thm_open n k (S w) _ _ (rho_sub (Some W) (length env) rho) _
                  (FOPr_ball_final v W t A Hvt HSvt HWA' ltac:(lia) ltac:(lia)) HE3) as T.
    specialize (T ltac:(intros x Hx; fv_cases Hx;
                        first [ exists (length env); split;
                                [apply rho_sub_eq | rewrite length_app; cbn [length]; lia]
                              | destruct (Hh3 x (or_introl Hx)) as [i [Hxi [Hi _]]];
                                exists i; split; assumption
                              | assert (Hxv : x <> v)
                                  by (intro Exv; subst x; rewrite Nat.eqb_refl in *; discriminate);
                                destruct (Hh3 x (or_intror (conj Hx Hxv))) as [i [Hxi [Hi _]]];
                                exists i; split; assumption ])).
    pose proof (PRI_mp n _ _ (S w) _ _ _ _ _ HE3 Hr3 T TT) as T1.
    pose proof (PRI_mp n _ _ (S w) _ _ _ _ _ HE3 Hr3 T1 PB) as T2.
    refine (PRI_reslot n _ _ (S w) _ _ _ rho _ env _ _ _ _ T2); [| above_tac | avoid_tms | lia].
    intros x Hx. unfold SlotAgree. apply HS in Hx.
    assert (HxW : x <> W) by (destruct Hx as [Hx|[Hx _]]; intro E; subst x; congruence).
    rewrite (rho_sub_ne W (length env) rho x HxW).
    destruct (Hh x Hx) as [i [Hxi [Hi _]]]. rewrite Hxi, (nth_app_lt env [FOVar w] i Hi).
    apply FOPrH_refl.
  - intros Hn.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_thm _ _ _ (FOPr_not_all n v
                  (FOImplF (FOltv v (hsub_tm h t)) (hsub_f (h_hide v h) A)))) Hn) as HX.
    refine (PRI_exe n _ _ V W G _ env v (FONeg (FOImplF (FOltv v (hsub_tm h t))
              (hsub_f (h_hide v h) A))) HX _ _ _ _ _ _ _); [lia | avoid_tms | above_tac | | | |].
    + intros w Hw Hwv. rewrite fv_neg. cbn [FOfree_in]. rewrite fv_ltv by (apply HtW; lia).
      rewrite (hA_free n G V h rho env v A w HhA ltac:(lia) Hwv).
      rewrite (proj2 (Nat.eqb_neq v w) ltac:(lia)). rewrite Bool.orb_false_r. cbn [orb]. fr_tm.
    + intros w Hw Hwv. rewrite fv_neg. cbn [FOfree_in]. rewrite fv_ltv by (apply HtW; lia).
      rewrite (hA_free n G V h rho env v A w HhA ltac:(lia) Hwv).
      rewrite (proj2 (Nat.eqb_neq v w) ltac:(lia)). rewrite Bool.orb_false_r. cbn [orb].
      apply Htv; [left; reflexivity | exact Hw].
    + intros w Hw HWw. apply FOsubst_ok_neg. apply FOsubst_ok_impl;
        [apply FOsubst_ok_ltv; apply FOin_tm_var_ne; lia
        | apply (hsub_f_ok A (h_hide v h) v (FOVar w) W HWA);
          intros w' Hw'; cbn [FOin_tm] in Hw'; apply Nat.eqb_eq in Hw'; lia].
    + intros w0 Hw0 HWw0.
      rewrite FOsubst_f_neg, FOsubst_f_impl, FOsubst_f_ltv_self by (apply HtW; lia).
      rewrite hsub_f_inst by (intros z Hz Hz'; pose proof (Hhw' z (or_intror (conj Hz' Hz))); lia).
      lazymatch goal with |- PRI _ _ _ _ ?G2 _ _ =>
        assert (HX2 : FOPrH n G2 (FONeg (FOImplF (FOExists (S v) (FOEq (FOPlus (FOVar w0)
                        (FOSucc (FOVar (S v)))) (hsub_tm h t))) (hsub_f (h_upd v w0 h) A))))
          by apply FOPrH_last;
        assert (Hinc2 : forall X, In X G -> In X G2)
          by (intros X HX'; apply in_or_app; left; exact HX');
        assert (HG2 : FOctx_avoid G2 0 1000);
        [| assert (HG2V : forall w', S w0 <= w' -> FOfree_ctx w' G2)]
      end.
      { intros w' ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|].
        apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
        rewrite fv_neg. cbn [FOfree_in]. apply Bool.orb_false_iff. split.
        - destruct (Nat.eqb_spec (S v) w') as [_|HSw]; [reflexivity|].
          cbn [FOin_tm]. apply Bool.orb_false_iff.
          split; [apply Bool.orb_false_iff; split; apply Nat.eqb_neq; lia | fr_tm].
        - destruct (FOfree_in w' (hsub_f (h_upd v w0 h) A)) eqn:E; [|reflexivity].
          destruct (FOfree_in_hsub A (h_upd v w0 h) w' E) as [x [Hx Ex]]. unfold h_upd in Ex.
          destruct (Nat.eqb_spec x v) as [->|Hxv]; [lia|].
          pose proof (HOK_range n G V h rho env x (HhA x Hx Hxv)). lia. }
      { intros w' ?. apply FOfree_ctx_app_inv; [apply HGV; lia|].
        apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
        rewrite fv_neg. cbn [FOfree_in]. apply Bool.orb_false_iff. split.
        - destruct (Nat.eqb_spec (S v) w') as [_|HSw]; [reflexivity|].
          cbn [FOin_tm]. apply Bool.orb_false_iff.
          split; [apply Bool.orb_false_iff; split; apply Nat.eqb_neq; lia
                 | apply Htv; [left; reflexivity | lia]].
        - destruct (FOfree_in w' (hsub_f (h_upd v w0 h) A)) eqn:E; [|reflexivity].
          destruct (FOfree_in_hsub A (h_upd v w0 h) w' E) as [x [Hx Ex]]. unfold h_upd in Ex.
          destruct (Nat.eqb_spec x v) as [->|Hxv]; [lia|].
          pose proof (HOK_range n G V h rho env x (HhA x Hx Hxv)). lia. }
      refine (WITNESS n k W v t A (FONeg A) (FONeg (FOForall v (FOImplF (FOltv v t) A)))
                HSvt Hvt HWA HWv HWt ltac:(intros x Hx; rewrite fv_neg in Hx; exact Hx)
                (fun V' G' h' rho' env' HI0 Hh0 HD => proj2 (IHA HWA V' G' h' rho' env' HI0 Hh0) HD)
                (FOPr_ball_neg v W t A ltac:(lia) HSvt)
                ltac:(intros x Hx; rewrite fv_neg in Hx; apply HS; exact Hx)
                (S w0) _ h rho env w0
                (Inv_move n V (S w0) G _ h rho env _ HI' Hinc2 ltac:(lia) HG2 HG2V)
                Hhw' HWw0 ltac:(lia) ltac:(lia)
                (FOPrH_nimp_l _ _ _ _ HX2) (FOPrH_nimp_r _ _ _ _ HX2)).
Qed.

Lemma fv_and : forall x X Y, FOfree_in x (FOAnd X Y) = (FOfree_in x X || FOfree_in x Y)%bool.
Proof. intros x X Y. unfold FOAnd, FONeg. cbn [FOfree_in]. rewrite !Bool.orb_false_r. reflexivity. Qed.

Lemma D0P_bex : forall n k W v t A, FOin_tm v t = false -> FOin_tm (S v) t = false ->
  D0P n k W A -> D0P n k W (FOExists v (FOAnd (FOltv v t) A)).
Proof.
  intros n k W v t A Hvt HSvt IHA HW V G h rho env HI Hhw.
  destruct (bq_bounds' v t A W HW) as [HWv [HWA HWt]].
  assert (HS : forall x, FOfree_in x (FOExists v (FOAnd (FOltv v t) A)) = true <->
               FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v))
    by (intros x; exact (proj2 (fv_bq v t A x Hvt HSvt))).
  pose proof (Inv_weaken n V G h rho env _
                (fun x => FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) HI
                ltac:(intros x Hx; apply HS; exact Hx)) as HI'.
  assert (Hhw' : forall x, FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v) -> W <= h x)
    by (intros x Hx; apply Hhw; apply HS; exact Hx).
  pose proof HI' as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (Hht : forall x, FOin_tm x t = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; left; exact Hx).
  assert (HhA : forall x, FOfree_in x A = true -> x <> v -> HOK n G V h rho env x)
    by (intros x Hx Hxv; apply Hh; right; split; assumption).
  destruct (hsub_facts t n G V h rho env Hht) as [Ht0 Htv].
  assert (HtW : forall w, w < W -> FOin_tm w (hsub_tm h t) = false).
  { intros w Hw. destruct (FOin_tm w (hsub_tm h t)) eqn:E; [|reflexivity].
    destruct (FOin_tm_hsub t h w E) as [x [Hx <-]]. specialize (Hhw' x (or_introl Hx)). lia. }
  assert (HWA' : FOfree_in W A = false) by (apply FOfree_in_above; lia).
  assert (HWt' : FOin_tm W t = false) by (apply FOin_tm_above; lia).
  rewrite !hsub_bex by assumption.
  split.
  - intros HB.
    refine (PRI_exe n _ _ V W G _ env v (FOAnd (FOltv v (hsub_tm h t)) (hsub_f (h_hide v h) A))
              HB _ _ _ _ _ _ _); [lia | avoid_tms | above_tac | | | |].
    + intros w Hw Hwv. rewrite fv_and, fv_ltv by (apply HtW; lia).
      rewrite (hA_free n G V h rho env v A w HhA ltac:(lia) Hwv).
      rewrite (proj2 (Nat.eqb_neq v w) ltac:(lia)). rewrite Bool.orb_false_r. cbn [orb]. fr_tm.
    + intros w Hw Hwv. rewrite fv_and, fv_ltv by (apply HtW; lia).
      rewrite (hA_free n G V h rho env v A w HhA ltac:(lia) Hwv).
      rewrite (proj2 (Nat.eqb_neq v w) ltac:(lia)). rewrite Bool.orb_false_r. cbn [orb].
      apply Htv; [left; reflexivity | exact Hw].
    + intros w Hw HWw. apply FOsubst_ok_and;
        [apply FOsubst_ok_ltv; apply FOin_tm_var_ne; lia
        | apply (hsub_f_ok A (h_hide v h) v (FOVar w) W HWA);
          intros w' Hw'; cbn [FOin_tm] in Hw'; apply Nat.eqb_eq in Hw'; lia].
    + intros w0 Hw0 HWw0.
      rewrite FOsubst_f_and, FOsubst_f_ltv_self by (apply HtW; lia).
      rewrite hsub_f_inst by (intros z Hz Hz'; pose proof (Hhw' z (or_intror (conj Hz' Hz))); lia).
      lazymatch goal with |- PRI _ _ _ _ ?G2 _ _ =>
        assert (HX2 : FOPrH n G2 (FOAnd (FOExists (S v) (FOEq (FOPlus (FOVar w0)
                        (FOSucc (FOVar (S v)))) (hsub_tm h t))) (hsub_f (h_upd v w0 h) A)))
          by apply FOPrH_last;
        assert (Hinc2 : forall X, In X G -> In X G2)
          by (intros X HX'; apply in_or_app; left; exact HX');
        assert (HG2 : FOctx_avoid G2 0 1000);
        [| assert (HG2V : forall w', S w0 <= w' -> FOfree_ctx w' G2)]
      end.
      { intros w' ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|].
        apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
        rewrite fv_and. cbn [FOfree_in]. apply Bool.orb_false_iff. split.
        - destruct (Nat.eqb_spec (S v) w') as [_|HSw]; [reflexivity|].
          cbn [FOin_tm]. apply Bool.orb_false_iff.
          split; [apply Bool.orb_false_iff; split; apply Nat.eqb_neq; lia | fr_tm].
        - destruct (FOfree_in w' (hsub_f (h_upd v w0 h) A)) eqn:E; [|reflexivity].
          destruct (FOfree_in_hsub A (h_upd v w0 h) w' E) as [x [Hx Ex]]. unfold h_upd in Ex.
          destruct (Nat.eqb_spec x v) as [->|Hxv]; [lia|].
          pose proof (HOK_range n G V h rho env x (HhA x Hx Hxv)). lia. }
      { intros w' ?. apply FOfree_ctx_app_inv; [apply HGV; lia|].
        apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
        rewrite fv_and. cbn [FOfree_in]. apply Bool.orb_false_iff. split.
        - destruct (Nat.eqb_spec (S v) w') as [_|HSw]; [reflexivity|].
          cbn [FOin_tm]. apply Bool.orb_false_iff.
          split; [apply Bool.orb_false_iff; split; apply Nat.eqb_neq; lia
                 | apply Htv; [left; reflexivity | lia]].
        - destruct (FOfree_in w' (hsub_f (h_upd v w0 h) A)) eqn:E; [|reflexivity].
          destruct (FOfree_in_hsub A (h_upd v w0 h) w' E) as [x [Hx Ex]]. unfold h_upd in Ex.
          destruct (Nat.eqb_spec x v) as [->|Hxv]; [lia|].
          pose proof (HOK_range n G V h rho env x (HhA x Hx Hxv)). lia. }
      refine (WITNESS n k W v t A A (FOExists v (FOAnd (FOltv v t) A))
                HSvt Hvt HWA HWv HWt (fun x Hx => Hx)
                (fun V' G' h' rho' env' HI0 Hh0 HD => proj1 (IHA HWA V' G' h' rho' env' HI0 Hh0) HD)
                (FOPr_bex_pos v W t A ltac:(lia) HSvt)
                ltac:(intros x Hx; apply HS; exact Hx)
                (S w0) _ h rho env w0
                (Inv_move n V (S w0) G _ h rho env _ HI' Hinc2 ltac:(lia) HG2 HG2V)
                Hhw' HWw0 ltac:(lia) ltac:(lia)
                (FOPrH_and_l _ _ _ _ HX2) (FOPrH_and_r _ _ _ _ HX2)).
  - intros Hn.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_thm _ _ _ (FOPr_not_ex_and n v
                  (FOltv v (hsub_tm h t)) (hsub_f (h_hide v h) A))) Hn) as HB.
    refine (PRI_numr_ex n _ _ V W G _ env (hsub_tm h t) _ _ _ _ _ _);
      [lia | avoid_tms | intros w' ?; fr_tm | avoid_tms | above_tac |].
    intros w Hw HWw.
    lazymatch goal with |- PRI _ _ _ _ ?G2 _ _ =>
      assert (HG2 : FOctx_avoid G2 0 1000) by (intros w' ? ?; free_ctx);
      assert (HG2V : forall w', S w <= w' -> FOfree_ctx w' G2) by (intros w' ?; free_ctx);
      assert (Hinc2 : forall X, In X G -> In X G2)
        by (intros X HX; apply in_or_app; left; exact HX);
      assert (N2 : FOPrH n G2 (FONUMR (hsub_tm h t) (FOVar w))) by wk_in;
      assert (HB2 : FOPrH n G2 (FOForall v (FOImplF (FOltv v (hsub_tm h t))
                                              (FONeg (hsub_f (h_hide v h) A))))) by wk HB
    end.
    pose proof (Inv_move n V (S w) G _ h rho env _ HI' Hinc2 ltac:(lia) HG2 HG2V) as HIm.
    assert (HWNA : FOvars_max (FONeg A) < W) by (unfold FONeg; cbn [FOvars_max]; lia).
    assert (IHD : forall V' G' h' rho' env',
              Inv n V' G' h' rho' env' (fun x => FOfree_in x (FONeg A) = true) ->
              (forall x, FOfree_in x (FONeg A) = true -> W <= h' x) ->
              FOPrH n G' (hsub_f h' (FONeg A)) ->
              PRI n (FOPrCores k) (FOu0 k) V' G' (cpat_f rho' (FONeg A)) env').
    { intros V' G' h' rho' env' HI0 Hh0 HD.
      apply (proj2 (IHA HWA V' G' h' rho' env'
                      (Inv_weaken n V' G' h' rho' env' _ (fun x => FOfree_in x A = true) HI0
                         (fun x Hx => eq_trans (fv_neg x A) Hx))
                      (fun x Hx => Hh0 x (eq_trans (fv_neg x A) Hx)))).
      exact HD. }
    lazymatch type of HG2 with FOctx_avoid ?G2 _ _ =>
      assert (HIm' : Inv n (S w) G2 h rho env (fun x => FOfree_in x (FONeg A) = true /\ x <> v))
        by (apply (Inv_weaken n (S w) _ h rho env _ _ HIm); intros x Hx; cbn beta in Hx |- *;
            destruct Hx as [Hx Hxv]; rewrite fv_neg in Hx; right; split; assumption)
    end.
    pose proof (BALL_GEN n k W v (FONeg A) HWNA HWv IHD
                  (S w) _ h rho env (hsub_tm h t) (FOVar w) W ltac:(lia) (le_n W) HIm'
                  ltac:(intros x Hx Hxv; rewrite fv_neg in Hx; apply Hhw'; right; split;
                        assumption)
                  ltac:(avoid_tms) ltac:(above_tac) HtW N2 HB2) as PB.
    unfold ballQ in PB.
    pose proof (Inv_slot n (S w) _ h rho env _ (hsub_tm h t) (FOVar w) W HIm N2 ltac:(avoid_tms)
                  ltac:(intros s [<-|[]] w' Hw'; apply FOin_tm_var_ne; lia)
                  ltac:(intros x [Hx|[Hx _]] E; subst x; congruence)) as HI3.
    destruct HI3 as [HV3 [HG03 [HGV3 [HE3 [Henv3 [Hr3 Hh3]]]]]].
    pose proof (PRI_teval t n k (S w) _ h _ _ W (length env) HV3 HG03 HGV3 HE3 Henv3 Hr3
                  ltac:(intros x Hx; apply Hh3; left; exact Hx) HWt'
                  (rho_sub_eq W (length env) rho) ltac:(rewrite length_app; cbn [length]; lia)
                  ltac:(rewrite nth_snoc_len; exact N2)) as TT.
    pose proof (PRI_thm_open n k (S w) _ _ (rho_sub (Some W) (length env) rho) _
                  (FOPr_bexneg_final v W t A Hvt HSvt HWA' ltac:(lia) ltac:(lia)
                     ltac:(apply FOin_tm_var_ne; lia)) HE3) as T.
    specialize (T ltac:(intros x Hx; fv_cases Hx;
                        first [ exists (length env); split;
                                [apply rho_sub_eq | rewrite length_app; cbn [length]; lia]
                              | destruct (Hh3 x (or_introl Hx)) as [i [Hxi [Hi _]]];
                                exists i; split; assumption
                              | assert (Hxv : x <> v)
                                  by (intro Exv; subst x; rewrite Nat.eqb_refl in *; discriminate);
                                destruct (Hh3 x (or_intror (conj Hx Hxv))) as [i [Hxi [Hi _]]];
                                exists i; split; assumption ])).
    pose proof (PRI_mp n _ _ (S w) _ _ _ _ _ HE3 Hr3 T TT) as T1.
    pose proof (PRI_mp n _ _ (S w) _ _ _ _ _ HE3 Hr3 T1 PB) as T2.
    refine (PRI_reslot n _ _ (S w) _ _ _ rho _ env _ _ _ _ T2); [| above_tac | avoid_tms | lia].
    intros x Hx. unfold SlotAgree. rewrite fv_neg in Hx. apply HS in Hx.
    assert (HxW : x <> W) by (destruct Hx as [Hx|[Hx _]]; intro E; subst x; congruence).
    rewrite (rho_sub_ne W (length env) rho x HxW).
    destruct (Hh x Hx) as [i [Hxi [Hi _]]]. rewrite Hxi, (nth_app_lt env [FOVar w] i Hi).
    apply FOPrH_refl.
Qed.

(** ** Bounded formulas. *)

Theorem D0P_all : forall n k W A, FOdelta0 A -> D0P n k W A.
Proof.
  intros n k W A HA.
  induction HA as [a b | | B C HB IHB HC IHC | v t A' Hv HSv HA' IHA' | v t A' Hv HSv HA' IHA'].
  - apply D0P_eq.
  - apply D0P_false.
  - apply D0P_impl; assumption.
  - exact (D0P_ball n k W v t A' Hv HSv IHA').
  - exact (D0P_bex n k W v t A' Hv HSv IHA').
Qed.
