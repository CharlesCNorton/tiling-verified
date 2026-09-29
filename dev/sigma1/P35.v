From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34.
Open Scope fo_scope.

(** ** Modus ponens on provable instances. *)

Lemma PRI_mp : forall n cores u0 V G rho A1 A2 env,
  EnvOK n V G env -> (forall z i, rho z = Some i -> i < length env) ->
  PRI n cores u0 V G (cpat_f rho (FOImplF A1 A2)) env ->
  PRI n cores u0 V G (cpat_f rho A1) env ->
  PRI n cores u0 V G (cpat_f rho A2) env.
Proof.
  intros n cores u0 V G rho A1 A2 env [HS [Henv0 [HV Henv]]] Hrho HI H1.
  intros G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  pose proof (cpat_span_le (cpat_f rho A1)) as Hs1.
  assert (Hs12 : cpat_span (cpat_f rho (FOImplF A1 A2))
                 = 8 + 4 * cpat_pairs (cpat_f rho A1) + cpat_span (cpat_f rho A2))
    by (cbn [cpat_f pImpP cpat_span cpat_pairs]; lia).
  remember (cpat_span (cpat_f rho A2)) as s2 eqn:Es2.
  remember (cpat_pairs (cpat_f rho A1)) as p1 eqn:Ep1.
  assert (HGT : FOctx_avoid G' B (B + 4 * s2 + 4 * p1 + 100))
    by (intros w ? ?; apply HGc; lia).
  assert (HcT : FOtms_avoid (c :: env) B (B + 4 * s2 + 4 * p1 + 100)).
  { intros t Ht w ? ?. destruct Ht as [<-|Ht];
      [apply (Hcc c (or_introl eq_refl)); lia | apply (Henv t Ht); lia]. }
  assert (HS' : SlotCtx n env G')
    by (apply (SlotCtx_mono n env G G' Hinc); [intros w ? ?; apply HG0; lia | exact HS]).
  assert (Hc02 : FOtms_avoid (c :: env) 0 1000) by avoid_tms.
  pose proof (FOPrH_guard_code n G' A2 rho env B c HS' Hrho Hc ltac:(lia)
                ltac:(intros w ? ?; apply HGT; lia) ltac:(avoid_tms) ltac:(avoid_tms)) as Gc.
  (* a code of the implication, named [z] *)
  pose proof (FOPrH_patf_total (cpat_f rho (FOImplF A1 A2)) n G' (B + 2 * s2 + 3) env
                (B + 2 * s2) ltac:(lia) ltac:(lia) ltac:(intros w ? ?; apply HGT; lia)
                ltac:(intros w ? ?; apply HG0; lia) ltac:(rewrite Hs12; avoid_tms)
                ltac:(avoid_tms) ltac:(avoid_tms)) as Ht.
  refine (FOPrH_ex_elim n G' (B + 2 * s2) _ _ _ _ Ht _); [apply HGT; lia | free_fm |].
  lazymatch goal with |- FOPrH _ ?G2 _ =>
    assert (Hpz : FOPrH n G2 (FOPATF (B + 2 * s2 + 3) env (cpat_f rho (FOImplF A1 A2))
                               (FOVar (B + 2 * s2)))) by apply FOPrH_last;
    assert (HG20 : FOctx_avoid G2 0 1000) by ctx_list;
    assert (Hinc2 : forall X, In X G -> In X G2)
      by (intros X HX; apply in_or_app; left; exact (Hinc X HX))
  end.
  assert (Hcl2 : Clean (G' ++ [FOPATF (B + 2 * s2 + 3) env (cpat_f rho (FOImplF A1 A2))
                                  (FOVar (B + 2 * s2))]) [FOVar (B + 2 * s2)] (B + 2 * s2 + 3)).
  { split.
    - intros w Hw.
      assert (Hew : FOtms_avoid env w (S w))
        by (intros t Ht0 w' ? ?; apply (Henv t Ht0); lia).
      apply FOfree_ctx_app_inv; [apply HGc; lia|].
      apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
      apply FOfree_in_PATF_any; [lia|]. apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
      exact Hew.
    - intros t Ht0 w Hw. destruct Ht0 as [<-|[]]. apply FOin_tm_var_ne. lia. }
  pose proof (HI _ (B + 2 * s2 + 3) (FOVar (B + 2 * s2)) Hinc2 HG20 ltac:(avoid_tms) ltac:(lia)
                Hcl2 Hpz) as Hpr.
  cbn [cpat_f pImpP] in Hpz.
  apply (FOPrH_patf_bin_elim n _ (B + 2 * s2 + 3) env 2 (cpat_f rho A1) (cpat_f rho A2)
           (FOVar (B + 2 * s2)) _ Hpz ltac:(lia));
    [cbn [cpat_span cpat_pairs]; ctx_list | intros w ? ?; cbn [cpat_span cpat_pairs] in *; free_fm
    | cbn [cpat_span cpat_pairs]; avoid_tms |].
  set (B1 := B + 2 * s2 + 3).
  lazymatch goal with |- FOPrH _ ?G3 _ =>
    assert (Hk : FOPrH n G3 (FOcpairF (FOnumeral 2) (FOVar (B1 + 2)) (FOVar (B + 2 * s2))))
      by wk_in;
    assert (Hp : FOPrH n G3 (FOcpairF (FOVar (B1 + 4)) (FOVar (B1 + 6)) (FOVar (B1 + 2))))
      by wk_in;
    assert (Ha1 : FOPrH n G3 (FOPATF (B1 + 8) env (cpat_f rho A1) (FOVar (B1 + 4)))) by wk_in;
    assert (Ha2 : FOPrH n G3 (FOPATF (B1 + 8 + 4 * cpat_pairs (cpat_f rho A1)) env
                                (cpat_f rho A2) (FOVar (B1 + 6)))) by wk_in;
    assert (HG30 : FOctx_avoid G3 0 1000) by ctx_list;
    assert (Hinc3 : forall X, In X G -> In X G3)
      by (intros X HX; apply in_or_app; left; apply in_or_app; left; exact (Hinc X HX));
    assert (Hc3 : FOPrH n G3 (FOPATF B env (cpat_f rho A2) c)) by wk Hc;
    assert (Gc3 : FOPrH n G3 (FOGUARDB c)) by wk Gc;
    assert (Hpr3 : FOPrH n G3 (FOPRu cores u0 (FOVar (B + 2 * s2)))) by wk Hpr;
    assert (Hcl3 : Clean G3 [FOVar (B1 + 4)] (B1 + 8))
      by (split;
          [ intros w Hw;
            assert (Hew : FOtms_avoid env w (S w))
              by (intros t Ht0 w' ? ?; apply (Henv t Ht0); unfold B1 in *; lia);
            apply FOfree_ctx_app_inv;
            [ apply FOfree_ctx_app_inv; [apply HGc; unfold B1 in *; lia | free_ctx]
            | free_ctx ]
          | intros t Ht0 w Hw; destruct Ht0 as [<-|[]]; apply FOin_tm_var_ne; lia ])
  end.
  pose proof (H1 _ (B1 + 8) (FOVar (B1 + 4)) Hinc3 HG30 ltac:(avoid_tms) ltac:(unfold B1; lia)
                Hcl3 Ha1) as Hpb.
  pose proof (FOPrH_patf_unique (cpat_f rho A2) n _ (B1 + 8 + 4 * cpat_pairs (cpat_f rho A1)) B
                env (FOVar (B1 + 6)) c Ha2 Hc3 ltac:(lia) ltac:(lia) ltac:(unfold B1; lia)
                ltac:(unfold B1 in *; ctx_list) ltac:(unfold B1 in *; ctx_list)
                ltac:(unfold B1 in *; avoid_tms) ltac:(unfold B1 in *; avoid_tms)
                ltac:(avoid_tms)) as Ec.
  pose proof (FOPrH_cpairF_cong _ _ _ _ _ _ _ _ (FOPrH_refl _ _ _) Ec (FOPrH_refl _ _ _) Hp)
    as Hp'.
  pose proof (FOPrH_patf_impl01 n _ (FOVar (B + 2 * s2)) (FOVar (B1 + 4)) c (FOVar (B1 + 2))
                Hk Hp' ltac:(avoid_tms) ltac:(avoid_tms)) as HP52.
  exact (FOPrH_mpu n _ cores u0 (FOVar (B + 2 * s2)) (FOVar (B1 + 4)) c
           ltac:(intros w ? ?; apply HG30; lia) HP52 Gc3 ltac:(avoid_tms) Hpr3 Hpb).
Qed.
