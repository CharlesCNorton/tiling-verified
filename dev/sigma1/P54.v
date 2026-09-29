From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41
  P42 P43 P44 P45 P46 P47 P48 P49 P50 P51 P52 P53.
Open Scope fo_scope.

(** ** A witness below the bound. *)

Lemma hsub_tm_upd_out : forall t h v N, FOin_tm v t = false ->
  hsub_tm (h_upd v N h) t = hsub_tm h t.
Proof.
  intros t h v N Hv. apply hsub_tm_ext. intros z Hz. unfold h_upd.
  destruct (Nat.eqb_spec z v) as [->|_]; [congruence | reflexivity].
Qed.

Lemma hsub_f_upd_out : forall A h v N, FOfree_in v A = false ->
  hsub_f (h_upd v N h) A = hsub_f h A.
Proof.
  intros A h v N Hv. apply hsub_f_ext. intros z Hz. unfold h_upd.
  destruct (Nat.eqb_spec z v) as [->|_]; [congruence | reflexivity].
Qed.

Lemma WITNESS : forall n k W v t A Ap C,
  FOin_tm (S v) t = false -> FOin_tm v t = false ->
  FOvars_max A < W -> S v < W -> FOmax_var_tm t < W ->
  (forall x, FOfree_in x Ap = true -> FOfree_in x A = true) ->
  (forall V' G' h' rho' env', Inv n V' G' h' rho' env' (fun x => FOfree_in x A = true) ->
     (forall x, FOfree_in x A = true -> W <= h' x) ->
     FOPrH n G' (hsub_f h' Ap) -> PRI n (FOPrCores k) (FOu0 k) V' G' (cpat_f rho' Ap) env') ->
  FOProvesTn 0 (FOImplF (FOEq (FOPlus (FOVar v) (FOSucc (FOVar W))) t) (FOImplF Ap C)) ->
  (forall x, FOfree_in x C = true -> FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) ->
  forall V G h rho env w0,
  Inv n V G h rho env (fun x => FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) ->
  (forall x, FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v) -> W <= h x) ->
  W <= w0 -> 1100 <= w0 -> w0 < V ->
  FOPrH n G (FOExists (S v) (FOEq (FOPlus (FOVar w0) (FOSucc (FOVar (S v)))) (hsub_tm h t))) ->
  FOPrH n G (hsub_f (h_upd v w0 h) Ap) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho C) env.
Proof.
  intros n k W v t A Ap C HSvt Hvt HWA HWv HWt HApA IHAp HTh HC V G h rho env w0 HI Hhw
    HWw0 Hw01 Hw02 HL HAp.
  pose proof HI as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (Hht : forall x, FOin_tm x t = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; left; exact Hx).
  destruct (hsub_facts t n G V h rho env Hht) as [Ht0 Htv].
  assert (HtW : forall w, w < W -> FOin_tm w (hsub_tm h t) = false).
  { intros w Hw. destruct (FOin_tm w (hsub_tm h t)) eqn:E; [|reflexivity].
    destruct (FOin_tm_hsub t h w E) as [x [Hx <-]]. specialize (Hhw x (or_introl Hx)). lia. }
  refine (PRI_exe n _ _ V W G _ env (S v)
            (FOEq (FOPlus (FOVar w0) (FOSucc (FOVar (S v)))) (hsub_tm h t)) HL _ _ _ _ _ _ _);
    [lia | avoid_tms | above_tac | | | |].
  { intros w Hw Hwv. cbn [FOfree_in FOin_tm]. apply Bool.orb_false_iff. split.
    - apply Bool.orb_false_iff. split; apply Nat.eqb_neq; lia.
    - fr_tm. }
  { intros w Hw Hwv. cbn [FOfree_in FOin_tm]. apply Bool.orb_false_iff. split.
    - apply Bool.orb_false_iff. split; apply Nat.eqb_neq; lia.
    - apply Htv; [left; reflexivity | lia]. }
  { intros w Hw HWw. reflexivity. }
  intros u0 Hu0 HWu0.
  rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_succ, FOsubst_t_var_eq',
    FOsubst_t_var_ne by lia.
  rewrite (FOsubst_t_not_in (hsub_tm h t) (S v) (FOVar u0)) by (apply HtW; lia).
  refine (PRI_numr_ex n _ _ (S u0) 0 _ _ env (FOVar w0) _ _ _ _ _ _);
    [lia | avoid_tms | intros w' ?; apply FOin_tm_var_ne; lia | avoid_tms | above_tac |].
  intros w1 Hw1 _.
  refine (PRI_numr_ex n _ _ (S w1) 0 _ _ env (FOVar u0) _ _ _ _ _ _);
    [lia | avoid_tms | intros w' ?; apply FOin_tm_var_ne; lia | avoid_tms | above_tac |].
  intros w2 Hw2 _.
  lazymatch goal with |- PRI _ _ _ _ ?G5 _ _ =>
    assert (HG5 : FOctx_avoid G5 0 1000)
      by (intros w' ? ?; apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv;
          [apply FOfree_ctx_app_inv; [apply HG0; lia|]|]|]; free_ctx);
    assert (HG5V : forall w', S w2 <= w' -> FOfree_ctx w' G5)
      by (intros w' ?; apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv;
          [apply FOfree_ctx_app_inv; [apply HGV; lia|]|]|]; free_ctx);
    assert (Hinc5 : forall X, In X G -> In X G5)
      by (intros X HX; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left;
          exact HX);
    assert (E5 : FOPrH n G5 (FOEq (FOPlus (FOVar w0) (FOSucc (FOVar u0))) (hsub_tm h t)))
      by wk_in;
    assert (N1 : FOPrH n G5 (FONUMR (FOVar w0) (FOVar w1))) by wk_in;
    assert (N2 : FOPrH n G5 (FONUMR (FOVar u0) (FOVar w2))) by wk_in;
    assert (HAp5 : FOPrH n G5 (hsub_f (h_upd v w0 h) Ap))
      by exact (FOPrH_weaken n G G5 _ Hinc5 HAp)
  end.
  pose proof (Inv_move n V (S w2) G _ h rho env _ HI Hinc5 ltac:(lia) HG5 HG5V) as HIm.
  pose proof (Inv_weaken n (S w2) _ h rho env _
                (fun x => ((FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) \/ x = v)
                          /\ x <> v) HIm
                ltac:(intros x Hx; cbn beta in Hx; destruct Hx as [[Hx|Hx] Hxv];
                      [exact Hx | exfalso; exact (Hxv Hx)])) as HI0'.
  pose proof (Inv_holder n (S w2) _ h rho env
                (fun x => (FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) \/ x = v)
                v w0 (FOVar w1) HI0' N1 ltac:(lia) ltac:(lia) ltac:(avoid_tms)
                ltac:(intros s [<-|[]] w Hw; apply FOin_tm_var_ne; lia)) as HI1.
  pose proof (Inv_weaken n (S w2) _ _ _ _ _
                (fun x => (((FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) \/ x = v)
                           \/ x = W) /\ x <> W) HI1
                ltac:(intros x Hx; cbn beta in Hx; destruct Hx as [[Hx|Hx] HxW];
                      [exact Hx | exfalso; exact (HxW Hx)])) as HI1'.
  pose proof (Inv_holder n (S w2) _ (h_upd v w0 h) _ _
                (fun x => ((FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) \/ x = v)
                          \/ x = W)
                W u0 (FOVar w2) HI1' N2 ltac:(lia) ltac:(lia) ltac:(avoid_tms)
                ltac:(intros s [<-|[]] w Hw; apply FOin_tm_var_ne; lia)) as HI2.
  assert (HWx : forall x, FOfree_in x A = true -> x < W)
    by (intros x Hx; pose proof (fv_small A x Hx); lia).
  assert (Htx : forall x, FOin_tm x t = true -> x < W).
  { intros x Hx. destruct (Nat.le_gt_cases W x) as [Hle|Hlt]; [|exact Hlt].
    rewrite FOin_tm_above in Hx by lia. discriminate. }
  lazymatch type of HG5 with FOctx_avoid ?G5 _ _ =>
    assert (HIE : Inv n (S w2) G5 (h_upd W u0 (h_upd v w0 h))
                    (rho_sub (Some W) (length (env ++ [FOVar w1]))
                       (rho_sub (Some v) (length env) rho))
                    ((env ++ [FOVar w1]) ++ [FOVar w2])
                    (fun x => FOfree_in x (FOEq (FOPlus (FOVar v) (FOSucc (FOVar W))) t) = true))
      by (apply (Inv_weaken n (S w2) _ _ _ _ _ _ HI2); intros x Hx; cbn beta in Hx |- *;
          fv_cases Hx; [left; right; reflexivity | right; reflexivity | left; left; left; exact Hx]);
    assert (HIA : Inv n (S w2) G5 (h_upd W u0 (h_upd v w0 h))
                    (rho_sub (Some W) (length (env ++ [FOVar w1]))
                       (rho_sub (Some v) (length env) rho))
                    ((env ++ [FOVar w1]) ++ [FOVar w2]) (fun x => FOfree_in x A = true))
      by (apply (Inv_weaken n (S w2) _ _ _ _ _ _ HI2); intros x Hx; cbn beta in Hx |- *; left;
          destruct (Nat.eqb_spec x v) as [->|Hxv]; [right; reflexivity|];
          left; right; split; assumption)
  end.
  pose proof (PRI_eq_pos n k (FOPlus (FOVar v) (FOSucc (FOVar W))) t (S w2) _ _ _ _ HIE) as TE.
  assert (Hh5e : hsub_tm (h_upd W u0 (h_upd v w0 h)) (FOPlus (FOVar v) (FOSucc (FOVar W))) =
                 FOPlus (FOVar w0) (FOSucc (FOVar u0))).
  { cbn [hsub_tm]. unfold h_upd. rewrite (proj2 (Nat.eqb_neq v W) ltac:(lia)), !Nat.eqb_refl.
    reflexivity. }
  rewrite Hh5e in TE.
  rewrite (hsub_tm_upd_out t _ W u0) in TE by (apply FOin_tm_above; lia).
  rewrite (hsub_tm_upd_out t h v w0 Hvt) in TE.
  specialize (TE E5).
  assert (HWAp : FOfree_in W Ap = false).
  { destruct (FOfree_in W Ap) eqn:E; [|reflexivity]. specialize (HWx W (HApA W E)). lia. }
  pose proof (IHAp (S w2) _ _ _ _ HIA
                ltac:(intros x Hx; unfold h_upd;
                      destruct (Nat.eqb_spec x W) as [->|_]; [specialize (HWx W Hx); lia|];
                      destruct (Nat.eqb_spec x v) as [->|Hxv]; [exact HWw0|];
                      apply Hhw; right; split; assumption)
                ltac:(rewrite (hsub_f_upd_out Ap _ W u0 HWAp); exact HAp5)) as TA.
  pose proof HIE as [_ [_ [_ [HE5 [_ [Hr5 Hh5]]]]]].
  pose proof HI2 as [_ [_ [_ [_ [_ [_ Hh2]]]]]].
  pose proof (PRI_thm_open n k (S w2) _ _ (rho_sub (Some W) (length (env ++ [FOVar w1]))
                (rho_sub (Some v) (length env) rho)) _ HTh HE5) as T.
  specialize (T ltac:(intros x Hx; fv_cases Hx;
                      first [ destruct (Hh2 v ltac:(left; right; reflexivity))
                                as [i [Hxi [Hi _]]]; exists i; split; assumption
                            | destruct (Hh2 W ltac:(right; reflexivity))
                                as [i [Hxi [Hi _]]]; exists i; split; assumption
                            | destruct (Hh2 x ltac:(left; left; left; exact Hx))
                                as [i [Hxi [Hi _]]]; exists i; split; assumption
                            | destruct (Nat.eqb_spec x v) as [->|Hxv];
                              [ destruct (Hh2 v ltac:(left; right; reflexivity))
                                  as [i [Hxi [Hi _]]]; exists i; split; assumption
                              | first [ destruct (Hh2 x ltac:(left; left; right; split;
                                          [apply HApA; exact Hx | exact Hxv]))
                                          as [i [Hxi [Hi _]]]; exists i; split; assumption
                                      | destruct (HC x Hx) as [Hc|[Hc Hcv]];
                                        [ destruct (Hh2 x ltac:(left; left; left; exact Hc))
                                            as [i [Hxi [Hi _]]]; exists i; split; assumption
                                        | destruct (Hh2 x ltac:(left; left; right; split;
                                            assumption)) as [i [Hxi [Hi _]]];
                                          exists i; split; assumption ] ] ] ])).
  pose proof (PRI_mp n _ _ (S w2) _ _ _ _ _ HE5 Hr5 T TE) as T1.
  pose proof (PRI_mp n _ _ (S w2) _ _ _ _ _ HE5 Hr5 T1 TA) as T2.
  refine (PRI_reslot n _ _ (S w2) _ _ _ rho _ env _ _ _ _ T2); [| above_tac | avoid_tms | lia].
  intros x Hx. unfold SlotAgree.
  assert (HxS : FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) by exact (HC x Hx).
  assert (Hxv : x <> v) by (destruct HxS as [Hc|[_ Hc]]; [intro; subst x; congruence | exact Hc]).
  assert (HxW : x <> W) by (destruct HxS as [Hc|[Hc _]];
                              [pose proof (Htx x Hc); lia | pose proof (HWx x Hc); lia]).
  rewrite (rho_sub_ne W _ _ x HxW), (rho_sub_ne v _ rho x Hxv).
  destruct (Hh x HxS) as [i [Hxi [Hi _]]]. rewrite Hxi.
  rewrite (nth_app_lt (env ++ [FOVar w1]) [FOVar w2] i) by (rewrite length_app; lia).
  rewrite (nth_app_lt env [FOVar w1] i Hi). apply FOPrH_refl.
Qed.
