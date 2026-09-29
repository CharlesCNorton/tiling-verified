From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41
  P42 P43 P44 P45 P46 P47 P48.
Open Scope fo_scope.

(** ** The statement of the main induction.

    [D0P n k W A]: for a formula whose variables lie below [W] and
    holders at or above [W], a derivation of the holder instance of [A]
    (of its negation) gives provable instances of the code of [A] (of
    its negation). *)

Definition D0P (n k W : nat) (A : FOFormula) : Prop :=
  FOvars_max A < W ->
  forall V G h rho env,
  Inv n V G h rho env (fun x => FOfree_in x A = true) ->
  (forall x, FOfree_in x A = true -> W <= h x) ->
  (FOPrH n G (hsub_f h A) -> PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho A) env) /\
  (FOPrH n G (FONeg (hsub_f h A)) ->
     PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho (FONeg A)) env).

Lemma hsub_free_range : forall A h lo hi, (forall x, FOfree_in x A = true -> lo <= h x < hi) ->
  forall w, FOfree_in w (hsub_f h A) = true -> lo <= w < hi.
Proof.
  intros A h lo hi H w Hw. destruct (FOfree_in_hsub A h w Hw) as [x [Hx <-]]. exact (H x Hx).
Qed.

Lemma Inv_ext : forall n V G h rho env Sv X,
  Inv n V G h rho env Sv ->
  (forall w, w < 1000 -> FOfree_in w X = false) -> (forall w, V <= w -> FOfree_in w X = false) ->
  Inv n V (G ++ [X]) h rho env Sv.
Proof.
  intros n V G h rho env Sv X [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]] HX0 HXV.
  assert (Hinc : forall Y, In Y G -> In Y (G ++ [X]))
    by (intros Y HY; apply in_or_app; left; exact HY).
  assert (HG1 : FOctx_avoid (G ++ [X]) 0 1000).
  { intros w ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|].
    apply FOfree_ctx_cons; [apply HX0; lia | apply FOfree_ctx_nil]. }
  split; [exact HV|]. split; [exact HG1|].
  split; [intros w Hw; apply FOfree_ctx_app_inv; [apply HGV; lia|];
          apply FOfree_ctx_cons; [apply HXV; lia | apply FOfree_ctx_nil]|].
  split; [apply (EnvOK_mono n V V G); [exact HE | exact Hinc | intros w ? ?; apply HG1; lia | lia]|].
  split; [exact Henv|]. split; [exact Hr|].
  intros x Hx. refine (HOK_ext n G _ V V h rho rho env env x (Hh x Hx) Hinc _ _ _ _);
    [lia | intros i Hi; exact Hi | lia | intros i Hi; reflexivity].
Qed.

Lemma Inv_hsub_free : forall n V G h rho env A,
  Inv n V G h rho env (fun x => FOfree_in x A = true) ->
  (forall w, w < 1000 -> FOfree_in w (hsub_f h A) = false) /\
  (forall w, V <= w -> FOfree_in w (hsub_f h A) = false).
Proof.
  intros n V G h rho env A [_ [_ [_ [_ [_ [_ Hh]]]]]].
  assert (Hr : forall x, FOfree_in x A = true -> 1100 <= h x < V)
    by (intros x Hx; exact (HOK_range n G V h rho env x (Hh x Hx))).
  split; intros w Hw; destruct (FOfree_in w (hsub_f h A)) eqn:E; try reflexivity;
    pose proof (hsub_free_range A h 1100 V Hr w E); lia.
Qed.

(** ** Propositional facts. *)

Lemma FOPrH_nimp_l : forall n G X Y, FOPrH n G (FONeg (FOImplF X Y)) -> FOPrH n G X.
Proof.
  intros n G X Y H.
  apply (FOPrH_or_elim n G X (FONeg X) X (FOPrH_em n G X)); [apply FOPrH_last|].
  apply FOPrH_efq. unfold FONeg in H |- *.
  apply (FOPrH_mp _ _ _ _ (FOPrH_weak_app _ _ _ _ H)). apply FOPrH_intro.
  apply FOPrH_efq. apply (FOPrH_mp _ _ X); [apply FOPrH_assum; apply in_or_app; left;
    apply in_or_app; right; left; reflexivity | apply FOPrH_last].
Qed.

Lemma FOPrH_nimp_r : forall n G X Y, FOPrH n G (FONeg (FOImplF X Y)) -> FOPrH n G (FONeg Y).
Proof.
  intros n G X Y H. unfold FONeg in H |- *. apply FOPrH_intro.
  apply (FOPrH_mp _ _ _ _ (FOPrH_weak_app _ _ _ _ H)). apply FOPrH_intro.
  apply FOPrH_assum. apply in_or_app. left. apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPr_K : forall B C, FOProvesTn 0 (FOImplF C (FOImplF B C)).
Proof.
  intros B C. change (FOPrH 0 [] (FOImplF C (FOImplF B C))).
  apply FOPrH_intro. apply FOPrH_intro. apply FOPrH_assum. left. reflexivity.
Qed.

Lemma FOPr_neg_imp : forall B C, FOProvesTn 0 (FOImplF (FONeg B) (FOImplF B C)).
Proof.
  intros B C. change (FOPrH 0 [] (FOImplF (FONeg B) (FOImplF B C))).
  apply FOPrH_intro. apply FOPrH_intro. apply FOPrH_efq. cbn [app]. unfold FONeg.
  apply (FOPrH_mp _ _ B); apply FOPrH_assum; [left | right; left]; reflexivity.
Qed.

Lemma FOPr_imp_neg : forall B C,
  FOProvesTn 0 (FOImplF B (FOImplF (FONeg C) (FONeg (FOImplF B C)))).
Proof.
  intros B C. change (FOPrH 0 [] (FOImplF B (FOImplF (FONeg C) (FONeg (FOImplF B C))))).
  unfold FONeg. apply FOPrH_intro. apply FOPrH_intro. apply FOPrH_intro. cbn [app].
  apply (FOPrH_mp _ _ C); [apply FOPrH_assum; right; left; reflexivity|].
  apply (FOPrH_mp _ _ B); apply FOPrH_assum; [right; right; left | left]; reflexivity.
Qed.

Lemma FOPr_neg_false : FOProvesTn 0 (FONeg FOFalseF).
Proof.
  change (FOPrH 0 [] (FONeg FOFalseF)). unfold FONeg. apply FOPrH_intro.
  apply FOPrH_assum. left. reflexivity.
Qed.

(** ** Equations, falsity and implication. *)

Lemma D0P_eq : forall n k W a b, D0P n k W (FOEq a b).
Proof.
  intros n k W a b HW V G h rho env HI Hhw. split.
  - intros H. exact (PRI_eq_pos n k a b V G h rho env HI H).
  - intros H. exact (PRI_eq_neg n k a b V G h rho env HI H).
Qed.

Lemma D0P_false : forall n k W, D0P n k W FOFalseF.
Proof.
  intros n k W HW V G h rho env HI Hhw. split.
  - intros H. apply PRI_efq. exact H.
  - intros _. destruct HI as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
    exact (PRI_thm_open n k V G _ rho env FOPr_neg_false HE
             ltac:(intros x Hx; unfold FONeg in Hx; cbn in Hx; discriminate)).
Qed.

Lemma D0P_impl : forall n k W B C, D0P n k W B -> D0P n k W C -> D0P n k W (FOImplF B C).
Proof.
  intros n k W B C HB HC HW V G h rho env HI Hhw. cbn [FOvars_max] in HW.
  assert (HWB : FOvars_max B < W) by lia. assert (HWC : FOvars_max C < W) by lia.
  pose proof HI as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  assert (HIB : Inv n V G h rho env (fun x => FOfree_in x B = true))
    by (apply (Inv_weaken n V G h rho env _ _ HI); intros x Hx; cbn [FOfree_in]; rewrite Hx;
        reflexivity).
  assert (HIC : Inv n V G h rho env (fun x => FOfree_in x C = true))
    by (apply (Inv_weaken n V G h rho env _ _ HI); intros x Hx; cbn [FOfree_in]; rewrite Hx;
        apply Bool.orb_true_r).
  assert (HhB : forall x, FOfree_in x B = true -> W <= h x)
    by (intros x Hx; apply Hhw; cbn [FOfree_in]; rewrite Hx; reflexivity).
  assert (HhC : forall x, FOfree_in x C = true -> W <= h x)
    by (intros x Hx; apply Hhw; cbn [FOfree_in]; rewrite Hx; apply Bool.orb_true_r).
  assert (Hfv : forall A', (forall x, FOfree_in x A' = true -> FOfree_in x (FOImplF B C) = true) ->
            forall x, FOfree_in x A' = true -> exists j, rho x = Some j /\ j < length env).
  { intros A' HA' x Hx. destruct (Hh x (HA' x Hx)) as [i [Hxi [Hi _]]]. exists i.
    split; assumption. }
  destruct (Inv_hsub_free n V G h rho env B HIB) as [HB0 HBV].
  split.
  - intros Himp. cbn [hsub_f] in Himp.
    apply (PRI_cases n _ _ V G _ env (hsub_f h B) HB0 HBV).
    + pose proof (Inv_ext n V G h rho env _ _ HIC HB0 HBV) as HIC'.
      pose proof (proj1 (HC HWC V _ h rho env HIC' HhC)
                    (FOPrH_mp _ _ _ _ (FOPrH_weak_app _ _ _ _ Himp) (FOPrH_last _ _ _))) as TC.
      pose proof HIC' as [_ [_ [_ [HE' _]]]].
      pose proof (PRI_thm_open n k V _ _ rho env (FOPr_K B C) HE'
                    (Hfv (FOImplF C (FOImplF B C))
                       ltac:(intros x Hx; fv_cases Hx; cbn [FOfree_in]; rewrite Hx;
                                 first [reflexivity | apply Bool.orb_true_r]))) as T.
      exact (PRI_mp n _ _ V _ rho _ _ env HE' Hr T TC).
    + assert (HNB0 : forall w, w < 1000 -> FOfree_in w (FONeg (hsub_f h B)) = false)
        by (intros w Hw; unfold FONeg; cbn [FOfree_in]; rewrite HB0 by exact Hw; reflexivity).
      assert (HNBV : forall w, V <= w -> FOfree_in w (FONeg (hsub_f h B)) = false)
        by (intros w Hw; unfold FONeg; cbn [FOfree_in]; rewrite HBV by exact Hw; reflexivity).
      pose proof (Inv_ext n V G h rho env _ _ HIB HNB0 HNBV) as HIB'.
      pose proof (proj2 (HB HWB V _ h rho env HIB' HhB) (FOPrH_last _ _ _)) as TB.
      pose proof HIB' as [_ [_ [_ [HE' _]]]].
      pose proof (PRI_thm_open n k V _ _ rho env (FOPr_neg_imp B C) HE'
                    (Hfv (FOImplF (FONeg B) (FOImplF B C))
                       ltac:(intros x Hx; fv_cases Hx; cbn [FOfree_in]; rewrite Hx;
                                 first [reflexivity | apply Bool.orb_true_r]))) as T.
      exact (PRI_mp n _ _ V _ rho _ _ env HE' Hr T TB).
  - intros Hn. cbn [hsub_f] in Hn.
    pose proof (proj1 (HB HWB V G h rho env HIB HhB) (FOPrH_nimp_l _ _ _ _ Hn)) as TB.
    pose proof (proj2 (HC HWC V G h rho env HIC HhC) (FOPrH_nimp_r _ _ _ _ Hn)) as TC.
    pose proof (PRI_thm_open n k V G _ rho env (FOPr_imp_neg B C) HE
                  (Hfv (FOImplF B (FOImplF (FONeg C) (FONeg (FOImplF B C))))
                     ltac:(intros x Hx; fv_cases Hx; cbn [FOfree_in]; rewrite Hx;
                               first [reflexivity | apply Bool.orb_true_r]))) as T.
    exact (PRI_mp n _ _ V G rho _ _ env HE Hr (PRI_mp n _ _ V G rho _ _ env HE Hr T TB) TC).
Qed.
