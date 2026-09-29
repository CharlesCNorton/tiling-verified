From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41
  P42 P43 P44 P45 P46 P47 P48 P49 P50 P51.
Open Scope fo_scope.

(** ** The bounded universal closure, inside the provability predicate.

    [PhiBall Nt]: every numeral code [m] of [Nt], under the hypothesis
    that the body holds below [Nt], gives a provable instance of [P]
    over [env ++ [m]]. *)

Definition PhiBall (cores : list nat) (u0 B0 m v : nat) (hD : FOFormula) (env : list FOTerm)
    (P : CPat) (Nt : FOTerm) : FOFormula :=
  FOForall m (FOImplF (FONUMR Nt (FOVar m))
    (FOImplF (FOForall v (FOImplF (FOltv v Nt) hD))
       (PRIf cores u0 B0 (env ++ [FOVar m]) P))).

Lemma PhiBall_subst : forall cores u0 B0 m v hD env P N s,
  N <> m -> N <> v -> N <> S v -> 1000 <= N -> N < B0 -> FOtms_avoid [s] 802 805 ->
  FOfree_in N hD = false -> FOtms_avoid env N (S N) ->
  FOsubst_f N s (PhiBall cores u0 B0 m v hD env P (FOVar N)) = PhiBall cores u0 B0 m v hD env P s.
Proof.
  intros cores u0 B0 m v hD env P N s Hm Hv HSv HN HB Hs HhD Henv. unfold PhiBall.
  rewrite (FOsubst_f_all_ne N s m) by lia. rewrite !FOsubst_f_impl, FOsubst_f_NUMR by (lia || avoid_tms).
  rewrite (FOsubst_f_all_ne N s v) by lia. rewrite FOsubst_f_impl, FOsubst_f_ltv_var by lia.
  rewrite (FOsubst_f_not_free hD N s HhD). rewrite FOsubst_f_PRIf by lia.
  rewrite FOsubst_t_var_eq', FOsubst_t_var_ne by lia. rewrite map_app. cbn [map].
  rewrite FOsubst_t_var_ne by lia.
  rewrite (FOsubst_map_avoid N s env) by (intros t Ht; apply (Henv t Ht); lia). reflexivity.
Qed.

Lemma PhiBall_inst : forall n G cores u0 B0 m v hD env P Nt tm,
  FOPrH n G (PhiBall cores u0 B0 m v hD env P Nt) ->
  1000 <= m -> m < B0 -> FOin_tm m Nt = false -> FOfree_in m hD = false ->
  FOtms_avoid env m (S m) -> FOtms_avoid [tm] 0 1000 -> FOtms_avoid [tm] B0 (B0 + cpat_span P) ->
  m <> v -> m <> S v ->
  FOPrH n G (FOImplF (FONUMR Nt tm)
    (FOImplF (FOForall v (FOImplF (FOltv v Nt) hD)) (PRIf cores u0 B0 (env ++ [tm]) P))).
Proof.
  intros n G cores u0 B0 m v hD env P Nt tm H Hm HmB HNt HhD Henv Htm0 HtmB Hmv HmSv.
  unfold PhiBall in H.
  assert (Hfr : FOfree_in m (FOForall v (FOImplF (FOltv v Nt) hD)) = false).
  { cbn [FOfree_in]. destruct (Nat.eqb v m); [reflexivity|].
    apply Bool.orb_false_iff. split; [|exact HhD].
    apply FOfree_in_ltv; [lia | exact HNt]. }
  apply (FOPrH_inst n G m tm) in H;
    [| apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_not_free; exact Hfr|];
       apply FOsubst_ok_PRIf; [lia | fr_tm | avoid_tm]].
  rewrite !FOsubst_f_impl, FOsubst_f_NUMR in H by (lia || avoid_tms).
  rewrite (FOsubst_f_not_free _ m tm Hfr) in H.
  rewrite FOsubst_f_PRIf in H by lia. rewrite map_app in H. cbn [map] in H.
  rewrite FOsubst_t_var_eq', (FOsubst_t_not_in Nt m tm HNt) in H.
  rewrite (FOsubst_map_avoid m tm env) in H by (intros t Ht; apply (Henv t Ht); lia).
  exact H.
Qed.

Lemma FOPr_ball_mono : forall n v t X, FOin_tm (S v) t = false ->
  FOProvesTn n (FOImplF (FOForall v (FOImplF (FOltv v (FOSucc t)) X))
                  (FOForall v (FOImplF (FOltv v t) X))).
Proof.
  intros n v t X Ht.
  change (FOPrH n [] (FOImplF (FOForall v (FOImplF (FOltv v (FOSucc t)) X))
                  (FOForall v (FOImplF (FOltv v t) X)))).
  apply FOPrH_intro. apply FOPrH_all_intro.
  { apply FOfree_ctx_app_inv; [apply FOfree_ctx_nil|].
    apply FOfree_ctx_cons; [apply FOfree_in_all_self | apply FOfree_ctx_nil]. }
  apply FOPrH_intro.
  apply (FOPrH_mp _ _ (FOltv v (FOSucc t))).
  - apply FOPrH_all_same with (x := v). apply FOPrH_assum. apply in_or_app. left.
    apply in_or_app. right. left. reflexivity.
  - apply (FOPrH_mp _ _ (FOltv v t)); [apply FOPrH_thm; apply FOPr_ltv_succ; exact Ht|].
    apply FOPrH_last.
Qed.

Lemma CPrel_ball_succ : forall n G v y D rho env a b,
  (forall z, FOfree_in z D = true -> z <> v -> exists i, rho z = Some i /\ i < length env) ->
  y <> v -> y <> S v -> rho y = Some (length env) ->
  FOPrH n G (FOcpairF (FOnumeral 2) a b) ->
  CPrel n G (env ++ [a]) (env ++ [b])
    (cpat_f rho (FOForall v (FOImplF (FOltv v (FOSucc (FOVar y))) D)))
    (cpat_f rho (FOForall v (FOImplF (FOltv v (FOVar y)) D))).
Proof.
  intros n G v y D rho env a b HD Hyv HySv Hy C.
  assert (C' : FOPrH n G (FOcpairF (FOnumeral 2) (nth (length env) (env ++ [a]) FOZero)
                                    (nth (length env) (env ++ [b]) FOZero)))
    by (rewrite !nth_snoc_len; exact C).
  assert (Ry : rho_hide (S v) (rho_hide v rho) y = Some (length env)).
  { unfold rho_hide. rewrite (proj2 (Nat.eqb_neq y (S v)) HySv),
      (proj2 (Nat.eqb_neq y v) Hyv). exact Hy. }
  assert (Rv : rho_hide (S v) (rho_hide v rho) v = None).
  { unfold rho_hide. rewrite (proj2 (Nat.eqb_neq v (S v)) ltac:(lia)), Nat.eqb_refl.
    reflexivity. }
  assert (RSv : rho_hide (S v) (rho_hide v rho) (S v) = None).
  { unfold rho_hide. rewrite Nat.eqb_refl. reflexivity. }
  cbn [cpat_f]. unfold FOltv. cbn [cpat_f cpat_tm]. rewrite Ry, Rv, RSv.
  unfold pAllP, pImpP. apply cpr_pair; [apply cpr_lit|]. apply cpr_pair; [apply cpr_lit|].
  apply cpr_pair; [apply cpr_lit|]. apply cpr_pair.
  - cprel_tac.
  - apply CPrel_cpat_f. intros z Hz. unfold SlotAgree, rho_hide.
    destruct (Nat.eqb_spec z v) as [->|Hzv]; [exact I|].
    destruct (HD z Hz Hzv) as [i [Hzi Hi]]. rewrite Hzi.
    rewrite !nth_app_lt by exact Hi. apply FOPrH_refl.
Qed.
