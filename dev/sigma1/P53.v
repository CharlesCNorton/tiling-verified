From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41
  P42 P43 P44 P45 P46 P47 P48 P49 P50 P51 P52.
Open Scope fo_scope.

(** ** Moving the invariant. *)

Lemma Inv_move : forall n V V' G G' h rho env Sv,
  Inv n V G h rho env Sv -> (forall X, In X G -> In X G') -> V <= V' ->
  FOctx_avoid G' 0 1000 -> (forall w, V' <= w -> FOfree_ctx w G') ->
  Inv n V' G' h rho env Sv.
Proof.
  intros n V V' G G' h rho env Sv [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]] Hinc HVV HG0' HGV'.
  split; [lia|]. split; [exact HG0'|]. split; [exact HGV'|].
  split; [apply (EnvOK_mono n V V' G G' env HE Hinc); [intros w ? ?; apply HG0'; lia | lia]|].
  split; [exact Henv|]. split; [exact Hr|].
  intros x Hx. refine (HOK_ext n G G' V V' h rho rho env env x (Hh x Hx) Hinc HVV _ _ _);
    [intros i Hi; exact Hi | lia | intros i Hi; reflexivity].
Qed.

Lemma Inv_slot : forall n V G h rho env Sv t m z,
  Inv n V G h rho env Sv -> FOPrH n G (FONUMR t m) ->
  FOtms_avoid [m] 0 1100 -> (forall s, In s [m] -> forall w, V <= w -> FOin_tm w s = false) ->
  (forall x, Sv x -> x <> z) ->
  Inv n V G h (rho_sub (Some z) (length env) rho) (env ++ [m]) Sv.
Proof.
  intros n V G h rho env Sv t m z [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]] Hm Hm0 Hmv Hz.
  split; [exact HV|]. split; [exact HG0|]. split; [exact HGV|].
  split; [apply (EnvOK_snoc n V G env m t HE Hm); [avoid_tms | intros w Hw; apply (Hmv m); [left; reflexivity | exact Hw]]|].
  split; [avoid_tms|]. split.
  - intros z0 i Hz0. rewrite length_app. cbn [length]. unfold rho_sub in Hz0.
    destruct (Nat.eqb z0 z); [injection Hz0 as <-; lia | specialize (Hr z0 i Hz0); lia].
  - intros x Hx. refine (HOK_ext n G G V V h rho _ env _ x (Hh x Hx) (fun X HX => HX) _ _ _ _);
      [ lia | intros i Hi; rewrite (rho_sub_ne z (length env) rho x (Hz x Hx)); exact Hi
      | rewrite length_app; lia | intros i Hi; apply nth_app_lt; exact Hi ].
Qed.

Lemma Inv_holder : forall n V G h rho env Sv v N m,
  Inv n V G h rho env (fun x => Sv x /\ x <> v) -> FOPrH n G (FONUMR (FOVar N) m) ->
  1100 <= N -> N < V ->
  FOtms_avoid [m] 0 1100 -> (forall s, In s [m] -> forall w, V <= w -> FOin_tm w s = false) ->
  Inv n V G (h_upd v N h) (rho_sub (Some v) (length env) rho) (env ++ [m]) Sv.
Proof.
  intros n V G h rho env Sv v N m HI Hm HN1 HN2 Hm0 Hmv.
  pose proof (Inv_slot n V G h rho env _ (FOVar N) m v HI Hm Hm0 Hmv
                ltac:(intros x [_ Hx]; exact Hx)) as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  split; [exact HV|]. split; [exact HG0|]. split; [exact HGV|]. split; [exact HE|].
  split; [exact Henv|]. split; [exact Hr|].
  intros x Hx. destruct (Nat.eqb_spec x v) as [->|Hxv].
  - exists (length env). rewrite rho_sub_eq. split; [reflexivity|].
    split; [rewrite length_app; cbn [length]; lia|].
    unfold h_upd. rewrite Nat.eqb_refl, nth_snoc_len. split; [exact Hm | lia].
  - destruct (Hh x (conj Hx Hxv)) as [i [Hxi [Hi [HNx [H1 H2]]]]].
    exists i. unfold h_upd. rewrite (proj2 (Nat.eqb_neq x v) Hxv). split; [exact Hxi|].
    split; [exact Hi|]. split; [exact HNx | lia].
Qed.

Lemma hsub_ltv : forall h v t, FOin_tm v t = false -> FOin_tm (S v) t = false ->
  hsub_f (h_hide v h) (FOltv v t) = FOltv v (hsub_tm h t).
Proof.
  intros h v t H1 H2. unfold FOltv. cbn [hsub_f hsub_tm].
  unfold h_hide at 1 2. rewrite Nat.eqb_refl.
  rewrite (proj2 (Nat.eqb_neq v (S v)) ltac:(lia)). unfold h_hide at 1. rewrite Nat.eqb_refl.
  f_equal. f_equal. apply hsub_tm_ext. intros z Hz. unfold h_hide.
  destruct (Nat.eqb_spec z (S v)) as [->|H3]; [congruence|].
  destruct (Nat.eqb_spec z v) as [->|H4]; [congruence | reflexivity].
Qed.

Ltac fv_cases H ::=
  repeat match type of H with
  | FOfree_in _ (FONeg _) = true => unfold FONeg in H
  | FOfree_in _ (FOAnd _ _) = true => unfold FOAnd, FONeg in H
  | FOfree_in _ (FOltv _ _) = true => unfold FOltv in H
  | FOfree_in _ (FOImplF _ _) = true => cbn [FOfree_in] in H
  | FOfree_in _ (FOEq _ _) = true => cbn [FOfree_in] in H
  | FOfree_in _ (FOForall _ _) = true => cbn [FOfree_in] in H
  | FOfree_in _ (FOExists _ _) = true => cbn [FOfree_in] in H
  | FOfree_in _ FOFalseF = true => discriminate H
  | (if ?c then false else _) = true =>
      let E := fresh "E" in destruct c eqn:E; [discriminate H|]
  | (_ || _)%bool = true => apply Bool.orb_true_iff in H; destruct H as [H|H]
  | FOin_tm _ (FOSucc _) = true => cbn [FOin_tm] in H
  | FOin_tm _ (FOPlus _ _) = true => cbn [FOin_tm] in H
  | FOin_tm _ (FOMult _ _) = true => cbn [FOin_tm] in H
  | FOin_tm _ (opT _ _ _) = true => rewrite FOin_tm_opT_eq in H
  | FOin_tm _ FOZero = true => discriminate H
  | FOin_tm ?x (FOVar _) = true => cbn [FOin_tm] in H; apply Nat.eqb_eq in H; subst x
  | Nat.eqb _ ?x = true => apply Nat.eqb_eq in H; subst x
  | false = true => discriminate H
  end;
  try (match goal with E : Nat.eqb ?a ?a = false |- _ =>
         rewrite Nat.eqb_refl in E; discriminate E end).

Definition ballQ (v y : nat) (D : FOFormula) : FOFormula :=
  FOForall v (FOImplF (FOltv v (FOVar y)) D).

Lemma free_ball_hD : forall v Tt h D V w,
  (forall x, FOfree_in x D = true -> x <> v -> 1100 <= h x < V) ->
  (w < 1000 \/ V <= w) -> FOin_tm w Tt = false ->
  FOfree_in w (FOForall v (FOImplF (FOltv v Tt) (hsub_f (h_hide v h) D))) = false.
Proof.
  intros v Tt h D V w Hh Hw HT. cbn [FOfree_in].
  destruct (Nat.eqb_spec v w) as [_|Hvw]; [reflexivity|].
  apply Bool.orb_false_iff. split; [apply FOfree_in_ltv; [lia | exact HT]|].
  destruct (FOfree_in w (hsub_f (h_hide v h) D)) eqn:E; [|reflexivity].
  destruct (FOfree_in_hsub D (h_hide v h) w E) as [x [Hx Ex]]. unfold h_hide in Ex.
  destruct (Nat.eqb_spec x v) as [->|Hxv]; [congruence|].
  specialize (Hh x Hx Hxv). lia.
Qed.

Lemma BALL_base : forall n k W v D V G h rho env y,
  Inv n V G h rho env (fun x => FOfree_in x D = true /\ x <> v) ->
  FOvars_max D < W -> S v < W -> W <= V -> W <= y ->
  PRI n (FOPrCores k) (FOu0 k) (V + 2)
    ((G ++ [FONUMR FOZero (FOVar (V + 1))]) ++
       [FOForall v (FOImplF (FOltv v FOZero) (hsub_f (h_hide v h) D))])
    (cpat_f (rho_sub (Some y) (length env) rho) (ballQ v y D)) (env ++ [FOVar (V + 1)]).
Proof.
  intros n k W v D V G h rho env y HI HWD HWv HWV HWy.
  pose proof HI as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (Hhr : forall x, FOfree_in x D = true -> x <> v -> 1100 <= h x < V)
    by (intros x Hx Hxv; exact (HOK_range n G V h rho env x (Hh x (conj Hx Hxv)))).
  lazymatch goal with |- PRI _ _ _ _ ?G1 _ _ =>
    assert (HG1 : FOctx_avoid G1 0 1000);
    [| assert (HG1V : forall w, V + 2 <= w -> FOfree_ctx w G1)]
  end.
  { intros w ? ?. apply FOfree_ctx_app_inv; [free_ctx|].
    apply FOfree_ctx_cons; [apply (free_ball_hD v FOZero h D V w Hhr); [lia | reflexivity]|].
    apply FOfree_ctx_nil. }
  { intros w ?. apply FOfree_ctx_app_inv; [free_ctx|].
    apply FOfree_ctx_cons; [apply (free_ball_hD v FOZero h D V w Hhr); [lia | reflexivity]|].
    apply FOfree_ctx_nil. }
  pose proof (Inv_move n V (V + 2) G _ h rho env _ HI
                ltac:(intros X HX; apply in_or_app; left; apply in_or_app; left; exact HX)
                ltac:(lia) HG1 HG1V) as HI1.
  lazymatch type of HG1 with FOctx_avoid ?G1 _ _ =>
    assert (N0 : FOPrH n G1 (FONUMR FOZero (FOVar (V + 1)))) by wk_in
  end.
  assert (Hxy : forall x, FOfree_in x D = true /\ x <> v -> x <> y).
  { intros x [Hx _] E. subst x. pose proof (fv_small D y Hx). lia. }
  pose proof (Inv_slot n (V + 2) _ h rho env _ FOZero (FOVar (V + 1)) y HI1 N0
                ltac:(avoid_tms) ltac:(intros s [<-|[]] w Hw; apply FOin_tm_var_ne; lia) Hxy)
    as HI2.
  destruct HI2 as [HV2 [HG02 [HGV2 [HE2 [Henv2 [Hr2 Hh2]]]]]].
  pose proof (PRI_teval FOZero n k (V + 2) _ h _ _ y (length env) HV2 HG02 HGV2 HE2 Henv2 Hr2
                ltac:(intros x Hx; discriminate Hx) eq_refl (rho_sub_eq y (length env) rho)
                ltac:(rewrite length_app; cbn [length]; lia)
                ltac:(rewrite nth_snoc_len; exact N0)) as T0.
  pose proof (PRI_thm_open n k (V + 2) _ _ (rho_sub (Some y) (length env) rho) _
                (FOPr_ball_base v y D ltac:(lia) ltac:(lia)) HE2) as T.
  specialize (T ltac:(intros x Hx; fv_cases Hx;
                      first [ exists (length env); split;
                              [apply rho_sub_eq | rewrite length_app; cbn [length]; lia]
                            | assert (Hxv : x <> v)
                                by (intro Exv; subst x; rewrite Nat.eqb_refl in *; discriminate);
                              destruct (Hh2 x (conj Hx Hxv)) as [i [Hxi [Hi _]]];
                              exists i; split; assumption ])).
  exact (PRI_mp n _ _ (V + 2) _ _ _ _ _ HE2 Hr2 T T0).
Qed.

Lemma free_PhiBall : forall cores u0 B0 m v hD env P Nt w,
  FOfree_in w (FOForall v (FOImplF (FOltv v Nt) hD)) = false -> w <> m -> 2 <= B0 ->
  FOtms_avoid [Nt] w (S w) -> FOtms_avoid [Nt] 13 18 -> FOtms_avoid [Nt] 802 805 ->
  18 <= m -> m < 802 \/ 805 <= m -> FOtms_avoid env w (S w) ->
  FOfree_in w (PhiBall cores u0 B0 m v hD env P Nt) = false.
Proof.
  intros cores u0 B0 m v hD env P Nt w HY Hwm HB HNt1 HNt2 HNt3 Hm1 Hm2 Henv.
  unfold PhiBall. cbn [FOfree_in]. rewrite (proj2 (Nat.eqb_neq m w) ltac:(lia)).
  apply Bool.orb_false_iff. split; [apply FOfree_in_NUMR_all; avoid_tms|].
  apply Bool.orb_false_iff. split; [exact HY|].
  apply FOfree_in_PRIf; [exact HB | avoid_tms].
Qed.

Lemma fv_Ds : forall x v y D, FOfree_in x (FOsubst_f v (FOVar y) D) = true ->
  (FOfree_in x D = true /\ x <> v) \/ x = y.
Proof.
  intros x v y D H. destruct (FOfree_in_subst_gen D x v (FOVar y) H) as [[H1 H2]|H1].
  - left. split; assumption.
  - right. cbn [FOin_tm] in H1. apply Nat.eqb_eq in H1. symmetry. exact H1.
Qed.

Lemma BALL_step : forall n k W v D V G h rho env y,
  FOvars_max D < W -> S v < W -> W <= V -> W <= y ->
  (forall V' G' h' rho' env', Inv n V' G' h' rho' env' (fun x => FOfree_in x D = true) ->
     (forall x, FOfree_in x D = true -> W <= h' x) ->
     FOPrH n G' (hsub_f h' D) -> PRI n (FOPrCores k) (FOu0 k) V' G' (cpat_f rho' D) env') ->
  Inv n V G h rho env (fun x => FOfree_in x D = true /\ x <> v) ->
  (forall x, FOfree_in x D = true -> x <> v -> W <= h x) ->
  PRI n (FOPrCores k) (FOu0 k) (V + 2)
    (((G ++ [PhiBall (FOPrCores k) (FOu0 k) (V + 2) (V + 1) v (hsub_f (h_hide v h) D) env
               (cpat_f (rho_sub (Some y) (length env) rho) (ballQ v y D)) (FOVar V)])
       ++ [FONUMR (FOSucc (FOVar V)) (FOVar (V + 1))])
       ++ [FOForall v (FOImplF (FOltv v (FOSucc (FOVar V))) (hsub_f (h_hide v h) D))])
    (cpat_f (rho_sub (Some y) (length env) rho) (ballQ v y D)) (env ++ [FOVar (V + 1)]).
Proof.
  intros n k W v D V G h rho env y HWD HWv HWV HWy IHD HI Hhw.
  pose proof HI as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (Hhr : forall x, FOfree_in x D = true -> x <> v -> 1100 <= h x < V)
    by (intros x Hx Hxv; exact (HOK_range n G V h rho env x (Hh x (conj Hx Hxv)))).
  assert (HyD : FOvars_max D < y) by lia.
  assert (Hxy : forall x, FOfree_in x D = true -> x <> y).
  { intros x Hx E. subst x. pose proof (fv_small D y Hx). lia. }
  assert (HhD : forall w, (w < 1000 \/ V <= w) -> w <> v ->
            FOfree_in w (hsub_f (h_hide v h) D) = false).
  { intros w Hw Hwv. destruct (FOfree_in w (hsub_f (h_hide v h) D)) eqn:E; [|reflexivity].
    destruct (FOfree_in_hsub D (h_hide v h) w E) as [x [Hx Ex]]. unfold h_hide in Ex.
    destruct (Nat.eqb_spec x v) as [->|Hxv]; [congruence|]. specialize (Hhr x Hx Hxv). lia. }
  set (P := cpat_f (rho_sub (Some y) (length env) rho) (ballQ v y D)).
  set (hD := hsub_f (h_hide v h) D).
  assert (HPsp : forall w, V + 2 + cpat_span P < w -> V + 2 + cpat_span P < w) by (intros; lia).
  lazymatch goal with |- PRI _ _ _ _ ?G1 _ _ =>
    assert (HG1 : FOctx_avoid G1 0 1000);
    [| assert (HG1V : forall w, V + 2 <= w -> FOfree_ctx w G1)]
  end.
  { intros w ? ?. apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv|]|].
    - apply HG0; lia.
    - apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
      apply free_PhiBall; try (avoid_tms || lia).
      apply (free_ball_hD v (FOVar V) h D V w Hhr); [lia | apply FOin_tm_var_ne; lia].
    - free_ctx.
    - apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
      apply (free_ball_hD v (FOSucc (FOVar V)) h D V w Hhr); [lia | fr_tm]. }
  { intros w ?. apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv|]|].
    - apply HGV; lia.
    - apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
      apply free_PhiBall; try (avoid_tms || lia).
      apply (free_ball_hD v (FOVar V) h D V w Hhr); [lia | apply FOin_tm_var_ne; lia].
    - free_ctx.
    - apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
      apply (free_ball_hD v (FOSucc (FOVar V)) h D V w Hhr); [lia | fr_tm]. }
  lazymatch type of HG1 with FOctx_avoid ?G1 _ _ =>
    assert (HN1 : FOPrH n G1 (FONUMR (FOSucc (FOVar V)) (FOVar (V + 1)))) by wk_in
  end.
  refine (PRI_numr_invS n _ _ (V + 2) (V + 2 + cpat_span P + 1) _ P _ (FOVar V) (FOVar (V + 1))
            HN1 _ _ _ _ _ _); [lia | avoid_tms | above_tac | avoid_tms | above_tac |].
  intros w Hw HR.
  lazymatch goal with |- PRI _ _ _ _ ?G2 _ _ =>
    assert (HPhi2 : FOPrH n G2 (PhiBall (FOPrCores k) (FOu0 k) (V + 2) (V + 1) v hD env P
                                  (FOVar V))) by wk_in;
    assert (HS2 : FOPrH n G2 (FOForall v (FOImplF (FOltv v (FOSucc (FOVar V))) hD))) by wk_in;
    assert (Cw : FOPrH n G2 (FOcpairF (FOnumeral 2) (FOVar w) (FOVar (V + 1)))) by wk_in;
    assert (Nw : FOPrH n G2 (FONUMR (FOVar V) (FOVar w))) by wk_in;
    assert (Hinc2 : forall X, In X G -> In X G2)
      by (intros X HX; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left;
          apply in_or_app; left; exact HX);
    assert (HG2 : FOctx_avoid G2 0 1000)
      by (intros w' ? ?; apply FOfree_ctx_app_inv; [apply HG1; lia | free_ctx]);
    assert (HG2V : forall w', S w <= w' -> FOfree_ctx w' G2)
      by (intros w' ?; apply FOfree_ctx_app_inv; [apply HG1V; lia | free_ctx])
  end.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_thm _ _ _ (FOPr_ball_mono n v (FOVar V) hD
                ltac:(apply FOin_tm_var_ne; lia))) HS2) as Hmono.
  pose proof (PhiBall_inst n _ _ _ (V + 2) (V + 1) v hD env P (FOVar V) (FOVar w) HPhi2
                ltac:(lia) ltac:(lia) ltac:(apply FOin_tm_var_ne; lia)
                ltac:(apply HhD; lia) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(lia) ltac:(lia)) as IH.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ IH Nw) Hmono) as IHf.
  pose proof (PRIf_to_PRI n _ _ (S w) _ (env ++ [FOVar w]) P (V + 2) IHf ltac:(lia)
                ltac:(avoid_tms) ltac:(lia) ltac:(avoid_tms) ltac:(above_tac)) as IHP.
  lazymatch type of HG2 with FOctx_avoid ?G2 _ _ =>
    assert (HDN : FOPrH n G2 (hsub_f (h_upd v V h) D))
  end.
  { apply (FOPrH_inst n _ v (FOVar V)) in HS2;
      [| apply FOsubst_ok_impl;
         [apply FOsubst_ok_ltv; apply FOin_tm_var_ne; lia
         | apply (hsub_f_ok D (h_hide v h) v (FOVar V) W HWD);
           intros w' Hw'; cbn [FOin_tm] in Hw'; apply Nat.eqb_eq in Hw'; lia]].
    rewrite FOsubst_f_impl, FOsubst_f_ltv_self in HS2 by fr_tm.
    unfold hD in HS2. rewrite hsub_f_inst in HS2.
    - exact (FOPrH_mp _ _ _ _ HS2 (FOPrH_thm _ _ _ (FOPr_ltv_self n v (FOVar V)
                                                     ltac:(apply FOin_tm_var_ne; lia)))).
    - intros z Hz Hz'. pose proof (Hhw z Hz' Hz). lia. }
  lazymatch type of HG2 with FOctx_avoid ?G2 _ _ =>
    assert (HI4 : Inv n (S w) G2 (h_upd v V h) (rho_sub (Some v) (length env)
                                                  (rho_sub (Some y) (length env) rho))
                    (env ++ [FOVar w]) (fun x => FOfree_in x D = true))
  end.
  { pose proof (Inv_move n V (S w) G _ h rho env _ HI Hinc2 ltac:(lia) HG2 HG2V) as HIm.
    destruct HIm as [HVm [HG0m [HGVm [HEm [Henvm [Hrm Hhm]]]]]].
    split; [exact HVm|]. split; [exact HG0m|]. split; [exact HGVm|].
    split; [apply (EnvOK_snoc n (S w) _ env (FOVar w) (FOVar V) HEm Nw); [avoid_tms
             | intros w' Hw'; apply FOin_tm_var_ne; lia]|].
    split; [avoid_tms|]. split.
    - intros z0 i Hz0. rewrite length_app. cbn [length]. unfold rho_sub in Hz0.
      destruct (Nat.eqb z0 v); [injection Hz0 as <-; lia|].
      destruct (Nat.eqb z0 y); [injection Hz0 as <-; lia | specialize (Hrm z0 i Hz0); lia].
    - intros x Hx. destruct (Nat.eqb_spec x v) as [->|Hxv].
      + exists (length env). rewrite rho_sub_eq. split; [reflexivity|].
        split; [rewrite length_app; cbn [length]; lia|].
        unfold h_upd. rewrite Nat.eqb_refl, nth_snoc_len. split; [exact Nw | lia].
      + destruct (Hhm x (conj Hx Hxv)) as [i [Hxi [Hi [HNx [H1 H2]]]]].
        exists i. rewrite (rho_sub_ne v (length env) _ x Hxv),
          (rho_sub_ne y (length env) rho x (Hxy x Hx)).
        unfold h_upd. rewrite (proj2 (Nat.eqb_neq x v) Hxv).
        split; [exact Hxi|]. split; [rewrite length_app; lia|].
        rewrite nth_app_lt by exact Hi. split; [exact HNx | lia]. }
  pose proof (IHD (S w) _ _ _ _ HI4
                ltac:(intros x Hx; unfold h_upd; destruct (Nat.eqb_spec x v);
                      [lia | exact (Hhw x Hx n0)]) HDN) as TD.
  rewrite <- (cpat_f_subst_var D v y (rho_sub (Some y) (length env) rho) (length env) HyD
                (rho_sub_eq y (length env) rho)) in TD.
  pose proof (Inv_slot n (S w) _ h rho env _ (FOVar V) (FOVar w) y
                (Inv_move n V (S w) G _ h rho env _ HI Hinc2 ltac:(lia) HG2 HG2V) Nw
                ltac:(avoid_tms) ltac:(intros s [<-|[]] w' Hw'; apply FOin_tm_var_ne; lia)
                ltac:(intros x [Hx _]; exact (Hxy x Hx))) as HI5.
  destruct HI5 as [HV5 [HG05 [HGV5 [HE5 [Henv5 [Hr5 Hh5]]]]]].
  pose proof (PRI_thm_open n k (S w) _ _ (rho_sub (Some y) (length env) rho) _
                (FOPr_ball_step v y D HyD ltac:(lia)) HE5) as T.
  specialize (T ltac:(intros x Hx; fv_cases Hx;
                      first [ exists (length env); split;
                              [apply rho_sub_eq | rewrite length_app; cbn [length]; lia]
                            | destruct (fv_Ds x v y D Hx) as [[Hx1 Hx2]|Hx1];
                              [ destruct (Hh5 x (conj Hx1 Hx2)) as [i [Hxi [Hi _]]];
                                exists i; split; assumption
                              | subst x; exists (length env); split;
                                [apply rho_sub_eq | rewrite length_app; cbn [length]; lia] ]
                            | assert (Hxv : x <> v)
                                by (intro Exv; subst x; rewrite Nat.eqb_refl in *; discriminate);
                              destruct (Hh5 x (conj Hx Hxv)) as [i [Hxi [Hi _]]];
                              exists i; split; assumption ])).
  pose proof (PRI_mp n _ _ (S w) _ _ _ _ _ HE5 Hr5 T TD) as T1.
  pose proof (PRI_mp n _ _ (S w) _ _ _ _ _ HE5 Hr5 T1 IHP) as T2.
  refine (PRI_conv n _ _ (S w) _ _ _ _ _ _ _ _ _ T2); [| above_tac | avoid_tms | lia].
  intros G' Hinc. unfold P, ballQ.
  apply (CPrel_ball_succ n G' v y D (rho_sub (Some y) (length env) rho) env (FOVar w)
           (FOVar (V + 1))); [| lia | lia | apply rho_sub_eq | exact (FOPrH_weaken n _ G' _ Hinc Cw)].
  intros z Hz Hzv. destruct (Hh z (conj Hz Hzv)) as [i [Hzi [Hi _]]]. exists i.
  rewrite (rho_sub_ne y (length env) rho z (Hxy z Hz)). split; assumption.
Qed.

(** ** The bounded universal closure. *)

Lemma BALL_GEN : forall n k W v D,
  FOvars_max D < W -> S v < W ->
  (forall V' G' h' rho' env', Inv n V' G' h' rho' env' (fun x => FOfree_in x D = true) ->
     (forall x, FOfree_in x D = true -> W <= h' x) ->
     FOPrH n G' (hsub_f h' D) -> PRI n (FOPrCores k) (FOu0 k) V' G' (cpat_f rho' D) env') ->
  forall V G h rho env T mu y,
  W <= V -> W <= y ->
  Inv n V G h rho env (fun x => FOfree_in x D = true /\ x <> v) ->
  (forall x, FOfree_in x D = true -> x <> v -> W <= h x) ->
  FOtms_avoid [T; mu] 0 1100 ->
  (forall s, In s [T; mu] -> forall w, V <= w -> FOin_tm w s = false) ->
  (forall w, w < W -> FOin_tm w T = false) ->
  FOPrH n G (FONUMR T mu) ->
  FOPrH n G (FOForall v (FOImplF (FOltv v T) (hsub_f (h_hide v h) D))) ->
  PRI n (FOPrCores k) (FOu0 k) V G
    (cpat_f (rho_sub (Some y) (length env) rho) (ballQ v y D)) (env ++ [mu]).
Proof.
  intros n k W v D HWD HWv IHD V G h rho env T mu y HWV HWy HI Hhw HTm0 HTmv HTW HN HB.
  pose proof HI as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (Hhr : forall x, FOfree_in x D = true -> x <> v -> 1100 <= h x < V)
    by (intros x Hx Hxv; exact (HOK_range n G V h rho env x (Hh x (conj Hx Hxv)))).
  assert (HhD : forall w, (w < 1000 \/ V <= w) -> w <> v ->
            FOfree_in w (hsub_f (h_hide v h) D) = false).
  { intros w Hw Hwv. destruct (FOfree_in w (hsub_f (h_hide v h) D)) eqn:E; [|reflexivity].
    destruct (FOfree_in_hsub D (h_hide v h) w E) as [x [Hx Ex]]. unfold h_hide in Ex.
    destruct (Nat.eqb_spec x v) as [->|Hxv]; [congruence|]. specialize (Hhr x Hx Hxv). lia. }
  set (P := cpat_f (rho_sub (Some y) (length env) rho) (ballQ v y D)).
  set (hD := hsub_f (h_hide v h) D).
  assert (HPhi : FOPrH n G (FOForall V (PhiBall (FOPrCores k) (FOu0 k) (V + 2) (V + 1) v hD env P
                                          (FOVar V)))).
  { apply FOPrH_ind; [apply HGV; lia | |].
    - rewrite PhiBall_subst by first [lia | avoid_tms | apply HhD; lia].
      unfold PhiBall.
      apply FOPrH_all_intro; [apply HGV; lia|]. apply FOPrH_intro. apply FOPrH_intro.
      apply (PRI_to_PRIf n _ _ (V + 2) _ (env ++ [FOVar (V + 1)]) P (V + 2)
               (BALL_base n k W v D V G h rho env y HI HWD HWv HWV HWy)); [lia | lia | | | avoid_tms
                                                                    | above_tac].
      + intros w ? ?. apply FOfree_ctx_app_inv; [free_ctx|].
        apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
        apply (free_ball_hD v FOZero h D V w Hhr); [lia | reflexivity].
      + intros w ?. apply FOfree_ctx_app_inv; [free_ctx|].
        apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
        apply (free_ball_hD v FOZero h D V w Hhr); [lia | reflexivity].
    - rewrite PhiBall_subst by first [lia | avoid_tms | apply HhD; lia].
      unfold PhiBall at 2.
      apply FOPrH_all_intro.
      { apply FOfree_ctx_app_inv; [apply HGV; lia|].
        apply FOfree_ctx_cons; [|apply FOfree_ctx_nil]. unfold PhiBall.
        apply FOfree_in_all_self. }
      apply FOPrH_intro. apply FOPrH_intro.
      apply (PRI_to_PRIf n _ _ (V + 2) _ (env ++ [FOVar (V + 1)]) P (V + 2)
               (BALL_step n k W v D V G h rho env y HWD HWv HWV HWy IHD HI Hhw));
        [lia | lia | | | avoid_tms | above_tac].
      + intros w ? ?.
        apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv|]|].
        * apply HG0; lia.
        * apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
          apply free_PhiBall; try (avoid_tms || lia).
          apply (free_ball_hD v (FOVar V) h D V w Hhr); [lia | apply FOin_tm_var_ne; lia].
        * free_ctx.
        * apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
          apply (free_ball_hD v (FOSucc (FOVar V)) h D V w Hhr); [lia | fr_tm].
      + intros w ?.
        apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv|]|].
        * apply HGV; lia.
        * apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
          apply free_PhiBall; try (avoid_tms || lia).
          apply (free_ball_hD v (FOVar V) h D V w Hhr); [lia | apply FOin_tm_var_ne; lia].
        * free_ctx.
        * apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
          apply (free_ball_hD v (FOSucc (FOVar V)) h D V w Hhr); [lia | fr_tm]. }
  apply (FOPrH_inst n G V T) in HPhi;
    [| unfold PhiBall; apply FOsubst_ok_all; [fr_tm|]; apply FOsubst_ok_impl;
       [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_impl;
       [ apply FOsubst_ok_all; [apply HTW; lia|]; apply FOsubst_ok_impl;
         [apply FOsubst_ok_ltv; apply HTW; lia
         | apply FOsubst_ok_not_free; apply HhD; lia]
       | apply FOsubst_ok_PRIf; [lia | fr_tm | avoid_tm] ]].
  rewrite PhiBall_subst in HPhi by first [lia | avoid_tms | apply HhD; lia].
  pose proof (PhiBall_inst n G _ _ (V + 2) (V + 1) v hD env P T mu HPhi ltac:(lia) ltac:(lia)
                ltac:(fr_tm) ltac:(apply HhD; lia) ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(avoid_tms) ltac:(lia) ltac:(lia)) as H1.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ H1 HN) HB) as H2.
  exact (PRIf_to_PRI n _ _ V G (env ++ [mu]) P (V + 2) H2 ltac:(lia) ltac:(avoid_tms) ltac:(lia)
           ltac:(avoid_tms) ltac:(above_tac)).
Qed.
