From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41
  P42 P43 P44 P45 P46 P47.
Open Scope fo_scope.

(** ** The invariant of the main induction.

    [Inv n V G h rho env Sv]: the context lies in [1000 .. V), the slot
    values carry numeral codes, and every variable in [Sv] has a holder
    with its code in the slot [rho] gives it. *)

Definition Inv (n V : nat) (G : list FOFormula) (h : nat -> nat) (rho : nat -> option nat)
    (env : list FOTerm) (Sv : nat -> Prop) : Prop :=
  2000 <= V /\ FOctx_avoid G 0 1000 /\ (forall w, V <= w -> FOfree_ctx w G) /\
  EnvOK n V G env /\ FOtms_avoid env 0 1100 /\ (forall z i, rho z = Some i -> i < length env) /\
  (forall x, Sv x -> HOK n G V h rho env x).

Lemma rho_sub_eq : forall z j rho, rho_sub (Some z) j rho z = Some j.
Proof. intros z j rho. unfold rho_sub. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma rho_sub_ne : forall z j rho x, x <> z -> rho_sub (Some z) j rho x = rho x.
Proof. intros z j rho x H. unfold rho_sub. rewrite (proj2 (Nat.eqb_neq x z) H). reflexivity. Qed.

Lemma Inv_snoc : forall n V G h rho env Sv t w z,
  Inv n V G h rho env Sv -> V <= w ->
  FOtms_avoid [t] 0 1100 -> (forall s, In s [t] -> forall w', V <= w' -> FOin_tm w' s = false) ->
  (forall x, Sv x -> x <> z) ->
  Inv n (S w) (G ++ [FONUMR t (FOVar w)]) h (rho_sub (Some z) (length env) rho)
    (env ++ [FOVar w]) Sv.
Proof.
  intros n V G h rho env Sv t w z [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]] Hw Ht0 Htv Hz.
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (HG1 : FOctx_avoid (G ++ [FONUMR t (FOVar w)]) 0 1000) by (intros w' ? ?; free_ctx).
  assert (Hinc : forall X, In X G -> In X (G ++ [FONUMR t (FOVar w)]))
    by (intros X HX; apply in_or_app; left; exact HX).
  split; [lia|]. split; [exact HG1|]. split; [intros w' Hw'; free_ctx|].
  split.
  { apply (EnvOK_snoc n (S w) _ env (FOVar w) t);
      [ apply (EnvOK_mono n V (S w) G);
        [exact HE | exact Hinc | intros w' ? ?; apply HG1; lia | lia]
      | apply FOPrH_last | avoid_tms | intros w' Hw'; apply FOin_tm_var_ne; lia ]. }
  split; [avoid_tms|]. split.
  - intros z0 i Hz0. rewrite length_app. cbn [length]. unfold rho_sub in Hz0.
    destruct (Nat.eqb z0 z); [injection Hz0 as <-; lia | specialize (Hr z0 i Hz0); lia].
  - intros x Hx.
    refine (HOK_ext n G _ V (S w) h rho _ env _ x (Hh x Hx) Hinc _ _ _ _);
      [ lia | intros i Hi; rewrite (rho_sub_ne z (length env) rho x (Hz x Hx)); exact Hi
      | rewrite length_app; lia | intros i Hi; apply nth_app_lt; exact Hi ].
Qed.

Lemma Inv_weaken : forall n V G h rho env Sv Sv',
  Inv n V G h rho env Sv -> (forall x, Sv' x -> Sv x) -> Inv n V G h rho env Sv'.
Proof.
  intros n V G h rho env Sv Sv' [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]] HS.
  split; [exact HV|]. split; [exact HG0|]. split; [exact HGV|]. split; [exact HE|].
  split; [exact Henv|]. split; [exact Hr|]. intros x Hx. apply Hh. apply HS. exact Hx.
Qed.

Lemma HOK_range : forall n G V h rho env x, HOK n G V h rho env x -> 1100 <= h x < V.
Proof. intros n G V h rho env x [i [_ [_ [_ [H1 H2]]]]]. lia. Qed.

Lemma hsub_facts : forall t n G V h rho env,
  (forall x, FOin_tm x t = true -> HOK n G V h rho env x) ->
  FOtms_avoid [hsub_tm h t] 0 1100 /\
  (forall s, In s [hsub_tm h t] -> forall w, V <= w -> FOin_tm w s = false).
Proof.
  intros t n G V h rho env H. split.
  - intros s [<-|[]]. apply (hsub_tm_avoid t h 1100 1100); [|lia].
    intros x Hx. exact (proj1 (HOK_range n G V h rho env x (H x Hx))).
  - intros s [<-|[]] w Hw. apply (hsub_tm_below t h V); [|exact Hw].
    intros x Hx. exact (proj2 (HOK_range n G V h rho env x (H x Hx))).
Qed.

Ltac fv_cases H ::=
  repeat match type of H with
  | FOfree_in _ (FONeg _) = true => unfold FONeg in H
  | FOfree_in _ (FOAnd _ _) = true => unfold FOAnd, FONeg in H
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
  end.

(** ** Equations. *)

Lemma FOPr_eq_via : forall a b z,
  FOProvesTn 0 (FOImplF (FOEq a (FOVar z)) (FOImplF (FOEq b (FOVar z)) (FOEq a b))).
Proof.
  intros a b z.
  change (FOPrH 0 [] (FOImplF (FOEq a (FOVar z)) (FOImplF (FOEq b (FOVar z)) (FOEq a b)))).
  apply FOPrH_intro. apply FOPrH_intro. cbn [app].
  apply (FOPrH_eq_trans _ _ _ (FOVar z)); [apply FOPrH_assum; left; reflexivity|].
  apply FOPrH_eq_sym. apply FOPrH_assum. right. left. reflexivity.
Qed.

Lemma FOPr_neq_via : forall a b z1 z2,
  FOProvesTn 0 (FOImplF (FOEq a (FOVar z1)) (FOImplF (FOEq b (FOVar z2))
    (FOImplF (FONeg (FOEq (FOVar z1) (FOVar z2))) (FONeg (FOEq a b))))).
Proof.
  intros a b z1 z2.
  change (FOPrH 0 [] (FOImplF (FOEq a (FOVar z1)) (FOImplF (FOEq b (FOVar z2))
    (FOImplF (FONeg (FOEq (FOVar z1) (FOVar z2))) (FONeg (FOEq a b)))))).
  unfold FONeg. apply FOPrH_intro. apply FOPrH_intro. apply FOPrH_intro. apply FOPrH_intro.
  cbn [app].
  apply (FOPrH_mp _ _ (FOEq (FOVar z1) (FOVar z2))); [apply FOPrH_assum; right; right; left; reflexivity|].
  apply (FOPrH_eq_trans _ _ _ a); [apply FOPrH_eq_sym; apply FOPrH_assum; left; reflexivity|].
  apply (FOPrH_eq_trans _ _ _ b); [apply FOPrH_assum; right; right; right; left; reflexivity|].
  apply FOPrH_assum. right. left. reflexivity.
Qed.

Lemma PRI_eq_pos : forall n k a b V G h rho env,
  Inv n V G h rho env (fun x => FOfree_in x (FOEq a b) = true) ->
  FOPrH n G (FOEq (hsub_tm h a) (hsub_tm h b)) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho (FOEq a b)) env.
Proof.
  intros n k a b V G h rho env HI Hab.
  pose proof HI as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (Hha : forall x, FOin_tm x a = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; cbn [FOfree_in]; rewrite Hx; reflexivity).
  assert (Hhb : forall x, FOin_tm x b = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; cbn [FOfree_in]; rewrite Hx; apply Bool.orb_true_r).
  destruct (hsub_facts a n G V h rho env Hha) as [Ha0 Hav].
  destruct (hsub_facts b n G V h rho env Hhb) as [Hb0 Hbv].
  refine (PRI_numr_ex n _ _ V 0 G _ env (hsub_tm h a) _ _ _ _ _ _);
    [lia | avoid_tms | intros w' ?; fr_tm | avoid_tms | above_tac |].
  intros w Hw _.
  remember (S (FOvars_max (FOEq a b))) as z eqn:Ez.
  cbn [FOvars_max] in Ez.
  assert (Hza : FOin_tm z a = false) by (apply FOin_tm_above; lia).
  assert (Hzb : FOin_tm z b = false) by (apply FOin_tm_above; lia).
  assert (Hxz : forall x, FOfree_in x (FOEq a b) = true -> x <> z).
  { intros x Hx E. subst x. cbn [FOfree_in] in Hx. rewrite Hza, Hzb in Hx. discriminate. }
  pose proof (Inv_snoc n V G h rho env _ (hsub_tm h a) w z HI Hw Ha0 Hav Hxz) as HI2.
  destruct HI2 as [HV2 [HG02 [HGV2 [HE2 [Henv2 [Hr2 Hh2]]]]]].
  assert (Na : FOPrH n (G ++ [FONUMR (hsub_tm h a) (FOVar w)]) (FONUMR (hsub_tm h a) (FOVar w)))
    by apply FOPrH_last.
  pose proof (FOPrH_numr_cong1 n _ (hsub_tm h a) (hsub_tm h b) (FOVar w) Na
                (FOPrH_weak_app _ _ _ _ Hab) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms))
    as Nb.
  pose proof (PRI_teval a n k (S w) _ h _ _ z (length env) HV2 HG02 HGV2 HE2 Henv2 Hr2
                ltac:(intros x Hx; apply Hh2; cbn [FOfree_in]; rewrite Hx; reflexivity)
                Hza (rho_sub_eq z (length env) rho) ltac:(rewrite length_app; cbn [length]; lia)
                ltac:(rewrite nth_snoc_len; exact Na)) as TA.
  pose proof (PRI_teval b n k (S w) _ h _ _ z (length env) HV2 HG02 HGV2 HE2 Henv2 Hr2
                ltac:(intros x Hx; apply Hh2; cbn [FOfree_in]; rewrite Hx; apply Bool.orb_true_r)
                Hzb (rho_sub_eq z (length env) rho) ltac:(rewrite length_app; cbn [length]; lia)
                ltac:(rewrite nth_snoc_len; exact Nb)) as TB.
  pose proof (PRI_thm_open n k (S w) _ _ (rho_sub (Some z) (length env) rho) _
                (FOPr_eq_via a b z) HE2) as T.
  specialize (T ltac:(intros x Hx; fv_cases Hx;
                      first [ assert (Hx' : FOfree_in x (FOEq a b) = true)
                                by (cbn [FOfree_in]; rewrite Hx; first [reflexivity
                                                                     | apply Bool.orb_true_r]);
                              destruct (Hh2 x Hx') as [i [Hxi [Hi _]]]; exists i;
                              split; assumption
                            | exists (length env); split;
                              [apply rho_sub_eq | rewrite length_app; cbn [length]; lia] ])).
  pose proof (PRI_mp n _ _ (S w) _ _ _ _ _ HE2 Hr2 T TA) as T1.
  pose proof (PRI_mp n _ _ (S w) _ _ _ _ _ HE2 Hr2 T1 TB) as T2.
  refine (PRI_reslot n _ _ (S w) _ _ _ rho _ env _ _ _ _ T2); [| above_tac | avoid_tms | lia].
  intros x Hx. unfold SlotAgree. rewrite (rho_sub_ne z (length env) rho x (Hxz x Hx)).
  destruct (Hh x Hx) as [i [Hxi [Hi _]]]. rewrite Hxi, (nth_app_lt env [FOVar w] i Hi).
  apply FOPrH_refl.
Qed.

Lemma PRI_eq_neg : forall n k a b V G h rho env,
  Inv n V G h rho env (fun x => FOfree_in x (FOEq a b) = true) ->
  FOPrH n G (FONeg (FOEq (hsub_tm h a) (hsub_tm h b))) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho (FONeg (FOEq a b))) env.
Proof.
  intros n k a b V G h rho env HI Hab.
  pose proof HI as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (Hha : forall x, FOin_tm x a = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; cbn [FOfree_in]; rewrite Hx; reflexivity).
  assert (Hhb : forall x, FOin_tm x b = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; cbn [FOfree_in]; rewrite Hx; apply Bool.orb_true_r).
  destruct (hsub_facts a n G V h rho env Hha) as [Ha0 Hav].
  destruct (hsub_facts b n G V h rho env Hhb) as [Hb0 Hbv].
  remember (S (FOvars_max (FOEq a b))) as z1 eqn:Ez1.
  cbn [FOvars_max] in Ez1.
  assert (Hz1a : FOin_tm z1 a = false) by (apply FOin_tm_above; lia).
  assert (Hz1b : FOin_tm z1 b = false) by (apply FOin_tm_above; lia).
  assert (Hz2a : FOin_tm (S z1) a = false) by (apply FOin_tm_above; lia).
  assert (Hz2b : FOin_tm (S z1) b = false) by (apply FOin_tm_above; lia).
  assert (Hxz1 : forall x, FOfree_in x (FOEq a b) = true -> x <> z1).
  { intros x Hx E. subst x. cbn [FOfree_in] in Hx. rewrite Hz1a, Hz1b in Hx. discriminate. }
  assert (Hxz2 : forall x, FOfree_in x (FOEq a b) = true -> x <> S z1).
  { intros x Hx E. subst x. cbn [FOfree_in] in Hx. rewrite Hz2a, Hz2b in Hx. discriminate. }
  refine (PRI_numr_ex n _ _ V 0 G _ env (hsub_tm h a) _ _ _ _ _ _);
    [lia | avoid_tms | intros w' ?; fr_tm | avoid_tms | above_tac |].
  intros w1 Hw1 _.
  pose proof (Inv_snoc n V G h rho env _ (hsub_tm h a) w1 z1 HI Hw1 Ha0 Hav Hxz1) as HI2.
  pose proof HI2 as [HV2 [HG02 [HGV2 [HE2 [Henv2 [Hr2 Hh2]]]]]].
  pose proof HE2 as [_ [_ [_ Henvv2]]].
  refine (PRI_numr_ex n _ _ (S w1) 0 _ _ _ (hsub_tm h b) _ _ _ _ _ _);
    [lia | avoid_tms | intros w' ?; fr_tm | avoid_tms | above_tac |].
  intros w2 Hw2 _.
  pose proof (Inv_snoc n (S w1) _ h _ _ _ (hsub_tm h b) w2 (S z1) HI2 Hw2 Hb0
                ltac:(intros s [<-|[]] w' Hw'; apply Hbv; [left; reflexivity | lia]) Hxz2) as HI3.
  pose proof HI3 as [HV3 [HG03 [HGV3 [HE3 [Henv3 [Hr3 Hh3]]]]]].
  pose proof HE3 as [_ [_ [_ Henvv3]]].
  assert (R1 : rho_sub (Some (S z1)) (length (env ++ [FOVar w1]))
                 (rho_sub (Some z1) (length env) rho) z1 = Some (length env)).
  { rewrite rho_sub_ne by lia. apply rho_sub_eq. }
  assert (R2 : rho_sub (Some (S z1)) (length (env ++ [FOVar w1]))
                 (rho_sub (Some z1) (length env) rho) (S z1) = Some (length (env ++ [FOVar w1])))
    by apply rho_sub_eq.
  assert (N1 : nth (length env) ((env ++ [FOVar w1]) ++ [FOVar w2]) FOZero = FOVar w1).
  { rewrite nth_app_lt by (rewrite length_app; cbn [length]; lia). apply nth_snoc_len. }
  assert (N2 : nth (length (env ++ [FOVar w1])) ((env ++ [FOVar w1]) ++ [FOVar w2]) FOZero =
               FOVar w2) by apply nth_snoc_len.
  lazymatch type of HG03 with FOctx_avoid ?G3 _ _ =>
    assert (Na : FOPrH n G3 (FONUMR (hsub_tm h a) (FOVar w1))) by wk_in;
    assert (Nb : FOPrH n G3 (FONUMR (hsub_tm h b) (FOVar w2))) by wk_in;
    assert (Hab3 : FOPrH n G3 (FONeg (FOEq (hsub_tm h a) (hsub_tm h b)))) by wk Hab
  end.
  pose proof (PRI_teval a n k (S w2) _ h _ _ z1 (length env) HV3 HG03 HGV3 HE3 Henv3 Hr3
                ltac:(intros x Hx; apply Hh3; cbn [FOfree_in]; rewrite Hx; reflexivity)
                Hz1a R1 ltac:(rewrite !length_app; cbn [length]; lia)
                ltac:(rewrite N1; exact Na)) as TA.
  pose proof (PRI_teval b n k (S w2) _ h _ _ (S z1) (length (env ++ [FOVar w1])) HV3 HG03
                HGV3 HE3 Henv3 Hr3
                ltac:(intros x Hx; apply Hh3; cbn [FOfree_in]; rewrite Hx; apply Bool.orb_true_r)
                Hz2b R2 ltac:(rewrite !length_app; cbn [length]; lia)
                ltac:(rewrite N2; exact Nb)) as TB.
  pose proof (PRI_neq_gen n k (S w2) _ _ _ z1 (S z1) (length env) (length (env ++ [FOVar w1]))
                (hsub_tm h a) (hsub_tm h b) HV3 HG03 HGV3 HE3 Henv3 ltac:(avoid_tms)
                ltac:(above_tac) R1 R2 Hab3 ltac:(rewrite N1; exact Na)
                ltac:(rewrite N2; exact Nb)) as NE.
  pose proof (PRI_thm_open n k (S w2) _ _ (rho_sub (Some (S z1)) (length (env ++ [FOVar w1]))
                (rho_sub (Some z1) (length env) rho)) _ (FOPr_neq_via a b z1 (S z1)) HE3) as T.
  specialize (T ltac:(intros x Hx; fv_cases Hx;
                      first [ assert (Hx' : FOfree_in x (FOEq a b) = true)
                                by (cbn [FOfree_in]; rewrite Hx; first [reflexivity
                                                                     | apply Bool.orb_true_r]);
                              destruct (Hh3 x Hx') as [i [Hxi [Hi _]]]; exists i;
                              split; assumption
                            | exists (length env); split;
                              [exact R1 | rewrite !length_app; cbn [length]; lia]
                            | exists (length (env ++ [FOVar w1])); split;
                              [exact R2 | rewrite !length_app; cbn [length]; lia] ])).
  pose proof (PRI_mp n _ _ (S w2) _ _ _ _ _ HE3 Hr3 T TA) as T1.
  pose proof (PRI_mp n _ _ (S w2) _ _ _ _ _ HE3 Hr3 T1 TB) as T2.
  pose proof (PRI_mp n _ _ (S w2) _ _ _ _ _ HE3 Hr3 T2 NE) as T3.
  refine (PRI_reslot n _ _ (S w2) _ _ _ rho _ env _ _ _ _ T3); [| above_tac | avoid_tms | lia].
  intros x Hx. unfold SlotAgree.
  assert (Hx' : FOfree_in x (FOEq a b) = true)
    by (unfold FONeg in Hx; cbn [FOfree_in] in Hx |- *; rewrite Bool.orb_false_r in Hx; exact Hx).
  rewrite (rho_sub_ne (S z1) _ _ x (Hxz2 x Hx')), (rho_sub_ne z1 (length env) rho x (Hxz1 x Hx')).
  destruct (Hh x Hx') as [i [Hxi [Hi _]]]. rewrite Hxi.
  rewrite (nth_app_lt (env ++ [FOVar w1]) [FOVar w2] i) by (rewrite length_app; lia).
  rewrite (nth_app_lt env [FOVar w1] i Hi). apply FOPrH_refl.
Qed.
