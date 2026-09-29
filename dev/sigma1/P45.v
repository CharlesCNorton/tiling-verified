From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41
  P42 P43 P44.
Open Scope fo_scope.

(** ** Products. *)

Definition fTimes3 : FOFormula := FOEq (FOMult (FOVar 0) (FOVar 1)) (FOVar 2).

Lemma FOPr_times_zero : FOProvesTn 0 (FOEq (FOMult (FOVar 0) FOZero) FOZero).
Proof.
  change (FOPrH 0 [] (FOEq (FOMult (FOVar 0) FOZero) FOZero)). apply FOPrH_ring. fo_ring.
Qed.

Lemma FOPr_times_step :
  FOProvesTn 0 (FOImplF (FOEq (FOMult (FOVar 0) (FOVar 1)) (FOVar 3))
                  (FOImplF (FOEq (FOPlus (FOVar 3) (FOVar 0)) (FOVar 2))
                     (FOEq (FOMult (FOVar 0) (FOSucc (FOVar 1))) (FOVar 2)))).
Proof.
  change (FOPrH 0 [] (FOImplF (FOEq (FOMult (FOVar 0) (FOVar 1)) (FOVar 3))
                  (FOImplF (FOEq (FOPlus (FOVar 3) (FOVar 0)) (FOVar 2))
                     (FOEq (FOMult (FOVar 0) (FOSucc (FOVar 1))) (FOVar 2))))).
  apply FOPrH_intro. apply FOPrH_intro. cbn [app].
  apply (FOPrH_eq_trans _ _ _ (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOVar 0)));
    [apply FOPrH_ring; fo_ring|].
  apply (FOPrH_eq_trans _ _ _ (FOPlus (FOVar 3) (FOVar 0))).
  - apply FOPrH_congPlus; [apply FOPrH_assum; left; reflexivity | apply FOPrH_refl].
  - apply FOPrH_assum. right. left. reflexivity.
Qed.

Lemma PRI_times : forall n k V G x y m1 m2 m3,
  2000 <= V -> FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  FOtms_avoid [x; m1; y; m2; m3] 0 1100 ->
  (forall t, In t [x; m1; y; m2; m3] -> forall w, V <= w -> FOin_tm w t = false) ->
  FOPrH n G (FONUMR x m1) -> FOPrH n G (FONUMR y m2) -> FOPrH n G (FONUMR (FOMult x y) m3) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f (rhoN 3) fTimes3) [m1; m2; m3].
Proof.
  intros n k V G x y m1 m2 m3 HV HG0 HGV Hav0 Havv Hx Hy Hxy.
  apply (PRI_opind n k V G false x m1 y m2 m3 _ HV HG0 HGV Hav0 Havv Hy Hxy).
  - lazymatch goal with |- PRI _ _ _ _ ?G1 _ _ =>
      assert (HG1 : FOctx_avoid G1 0 1000) by (intros w ? ?; free_ctx);
      assert (Ha : FOPrH n G1 (FONUMR FOZero (FOVar (V + 1)))) by wk_in;
      assert (Hb : FOPrH n G1 (FONUMR (FOMult x FOZero) (FOVar (V + 2)))) by wk_in;
      assert (Hx1 : FOPrH n G1 (FONUMR x m1)) by wk Hx
    end.
    pose proof (FOPrH_numr_cong1 n _ (FOMult x FOZero) FOZero (FOVar (V + 2)) Hb
                  ltac:(apply FOPrH_ring; fo_ring) ltac:(avoid_tms) ltac:(avoid_tms)
                  ltac:(avoid_tms)) as Hb0.
    pose proof (FOPrH_numr_inv0 n _ (FOVar (V + 1)) ltac:(intros w ? ?; apply HG1; lia)
                  ltac:(avoid_tms) Ha) as Ca.
    pose proof (FOPrH_numr_inv0 n _ (FOVar (V + 2)) ltac:(intros w ? ?; apply HG1; lia)
                  ltac:(avoid_tms) Hb0) as Cb.
    assert (HE : EnvOK n (V + 3) ((G ++ [FONUMR FOZero (FOVar (V + 1))]) ++
                   [FONUMR (opT false x FOZero) (FOVar (V + 2))])
                   [m1; FOVar (V + 1); FOVar (V + 2)])
      by (apply (EnvOK3 n _ _ _ _ _ x FOZero (FOMult x FOZero));
          [intros w ? ?; apply HG1; lia | exact Hx1 | exact Ha | exact Hb | avoid_tms | lia
          | above_tac]).
    pose proof (PRI_thm_open n k (V + 3) _ (FOEq (FOMult (FOVar 0) FOZero) FOZero) (rhoN 3)
                  _ FOPr_times_zero HE
                  (rhoN_fv 3 (FOEq (FOMult (FOVar 0) FOZero) FOZero)
                     ltac:(apply Nat.ltb_lt; vm_compute; reflexivity))) as T0.
    refine (PRI_conv n _ _ (V + 3) _ _ _ _ _ _ _ _ _ T0); [| above_tac | avoid_tms | lia].
    intros G' Hinc.
    pose proof (FOPrH_weaken n _ G' _ Hinc Ca) as Ca'.
    pose proof (FOPrH_weaken n _ G' _ Hinc Cb) as Cb'.
    unfold fTimes3, rhoN. cbn [cpat_f cpat_tm Nat.ltb Nat.leb]. cprel_tac.
  - lazymatch goal with |- PRI _ _ _ _ ?G1 _ _ =>
      assert (HG1 : FOctx_avoid G1 0 1000) by (intros w ? ?; free_ctx);
      assert (HPhi : FOPrH n G1 (PhiOp (FOPrCores k) (FOu0 k) (V + 3) (V + 1) (V + 2) false x m1
                                  (cpat_f (rhoN 3) fTimes3) (FOVar V))) by wk_in;
      assert (Ha : FOPrH n G1 (FONUMR (FOSucc (FOVar V)) (FOVar (V + 1)))) by wk_in;
      assert (Hb : FOPrH n G1 (FONUMR (FOMult x (FOSucc (FOVar V))) (FOVar (V + 2)))) by wk_in;
      assert (Hx1 : FOPrH n G1 (FONUMR x m1)) by wk Hx
    end.
    refine (PRI_numr_invS n _ _ (V + 3) (V + 3 + cpat_span (cpat_f (rhoN 3) fTimes3) + 1) _ _ _
              (FOVar V) (FOVar (V + 1)) Ha _ _ _ _ _ _);
      [lia | avoid_tms | above_tac | avoid_tms | above_tac |].
    intros w Hw HR.
    refine (PRI_numr_ex n _ _ (S w) (V + 3 + cpat_span (cpat_f (rhoN 3) fTimes3) + 1) _ _ _
              (FOMult x (FOVar V)) _ _ _ _ _ _);
      [lia | avoid_tms | intros w' ?; fr_tm | avoid_tms | above_tac |].
    intros w2 Hw2 HR2.
    lazymatch goal with |- PRI _ _ _ _ ?G3 _ _ =>
      assert (HG3 : FOctx_avoid G3 0 1000) by (intros w'' ? ?; free_ctx);
      assert (Cw : FOPrH n G3 (FOcpairF (FOnumeral 2) (FOVar w) (FOVar (V + 1)))) by wk_in;
      assert (Nw : FOPrH n G3 (FONUMR (FOVar V) (FOVar w))) by wk_in;
      assert (N2 : FOPrH n G3 (FONUMR (FOMult x (FOVar V)) (FOVar w2))) by wk_in;
      assert (HPhi3 : FOPrH n G3 (PhiOp (FOPrCores k) (FOu0 k) (V + 3) (V + 1) (V + 2) false x m1
                                   (cpat_f (rhoN 3) fTimes3) (FOVar V))) by wk HPhi;
      assert (Hb3 : FOPrH n G3 (FONUMR (FOMult x (FOSucc (FOVar V))) (FOVar (V + 2)))) by wk Hb;
      assert (Hx3 : FOPrH n G3 (FONUMR x m1)) by wk Hx1
    end.
    pose proof (PhiOp_inst n _ _ _ (V + 3) (V + 1) (V + 2) false x m1 _ (FOVar V) (FOVar w)
                  (FOVar w2) HPhi3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as IH.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ IH Nw) N2) as IHf.
    pose proof (PRIf_to_PRI n _ _ (S w2) _ _ _ (V + 3) IHf ltac:(lia) ltac:(avoid_tms) ltac:(lia)
                  ltac:(avoid_tms) ltac:(above_tac)) as IHP.
    pose proof (FOPrH_numr_cong1 n _ (FOMult x (FOSucc (FOVar V)))
                  (FOPlus (FOMult x (FOVar V)) x) (FOVar (V + 2)) Hb3
                  ltac:(apply FOPrH_ring; fo_ring) ltac:(avoid_tms) ltac:(avoid_tms)
                  ltac:(avoid_tms)) as Hb4.
    pose proof (PRI_plus n k (S w2) _ (FOMult x (FOVar V)) x (FOVar w2) m1 (FOVar (V + 2))
                  ltac:(lia) HG3 ltac:(intros w'' ?; free_ctx) ltac:(avoid_tms) ltac:(above_tac)
                  N2 Hx3 Hb4) as PL.
    lazymatch type of HG3 with FOctx_avoid ?G3 _ _ =>
      assert (HE4 : EnvOK n (S w2) G3 [m1; FOVar w; FOVar (V + 2); FOVar w2])
        by (apply (EnvOK4 n _ _ _ _ _ _ x (FOVar V) (FOMult x (FOSucc (FOVar V)))
                     (FOMult x (FOVar V)));
            [intros w'' ? ?; apply HG3; lia | exact Hx3 | exact Nw | exact Hb3 | exact N2
            | avoid_tms | lia | above_tac]);
      assert (IH4 : PRI n (FOPrCores k) (FOu0 k) (S w2) G3
                      (cpat_f (rhoN 4) (FOEq (FOMult (FOVar 0) (FOVar 1)) (FOVar 3)))
                      [m1; FOVar w; FOVar (V + 2); FOVar w2])
    end.
    { refine (PRI_conv n _ _ (S w2) _ _ _ _ _ _ _ _ _ IHP); [| above_tac | avoid_tms | lia].
      intros G' Hinc. unfold fTimes3, rhoN. cbn [cpat_f cpat_tm Nat.ltb Nat.leb]. cprel_tac. }
    lazymatch type of HG3 with FOctx_avoid ?G3 _ _ =>
      assert (PL4 : PRI n (FOPrCores k) (FOu0 k) (S w2) G3
                      (cpat_f (rhoN 4) (FOEq (FOPlus (FOVar 3) (FOVar 0)) (FOVar 2)))
                      [m1; FOVar w; FOVar (V + 2); FOVar w2])
    end.
    { refine (PRI_conv n _ _ (S w2) _ _ _ _ _ _ _ _ _ PL); [| above_tac | avoid_tms | lia].
      intros G' Hinc. unfold fPlus3, rhoN. cbn [cpat_f cpat_tm Nat.ltb Nat.leb]. cprel_tac. }
    pose proof (PRI_thm_open n k (S w2) _ _ (rhoN 4) _ FOPr_times_step HE4
                  (rhoN_fv 4 (FOImplF (FOEq (FOMult (FOVar 0) (FOVar 1)) (FOVar 3))
                               (FOImplF (FOEq (FOPlus (FOVar 3) (FOVar 0)) (FOVar 2))
                                  (FOEq (FOMult (FOVar 0) (FOSucc (FOVar 1))) (FOVar 2))))
                     ltac:(apply Nat.ltb_lt; vm_compute; reflexivity))) as T1.
    pose proof (PRI_mp n _ _ (S w2) _ (rhoN 4) _ _ _ HE4 (rhoN_range 4) T1 IH4) as T2.
    pose proof (PRI_mp n _ _ (S w2) _ (rhoN 4) _ _ _ HE4 (rhoN_range 4) T2 PL4) as T3.
    refine (PRI_conv n _ _ (S w2) _ _ _ _ _ _ _ _ _ T3); [| above_tac | avoid_tms | lia].
    intros G' Hinc.
    pose proof (FOPrH_weaken n _ G' _ Hinc Cw) as C1.
    unfold fTimes3, rhoN. cbn [cpat_f cpat_tm Nat.ltb Nat.leb]. cprel_tac.
Qed.
