From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35.
Open Scope fo_scope.

(** ** Instantiation of provable instances. *)

Lemma PRI_inst : forall n cores u0 V V' G rho x th env m wm,
  EnvOK n V G env -> (forall z i, rho z = Some i -> i < length env) ->
  FOPrH n G (FONUMR wm m) -> FOtms_avoid [m] 0 1000 -> V <= V' ->
  (forall w, V' <= w -> FOin_tm w m = false) ->
  PRI n cores u0 V G (cpat_f rho (FOForall x th)) env ->
  PRI n cores u0 V' G (cpat_f (rho_sub (Some x) (length env) rho) th) (env ++ [m]).
Proof.
  intros n cores u0 V V' G rho x th env m wm [HS [Henv0 [HV Henv]]] Hrho Hm Hm0 HVV' Hmv HI.
  intros G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  remember (cpat_span (cpat_f (rho_sub (Some x) (length env) rho) th)) as s1 eqn:Es1.
  remember (cpat_span (cpat_f rho (FOForall x th))) as s0 eqn:Es0.
  assert (HGT : FOctx_avoid G' B (B + s1 + 8 + 2 * s0 + 2 * s1 + 10))
    by (intros w ? ?; apply HGc; lia).
  assert (HT : FOtms_avoid (c :: m :: env) B (B + s1 + 8 + 2 * s0 + 2 * s1 + 10)).
  { intros t Ht0 w ? ?. destruct Ht0 as [<-|[<-|Ht0]];
      [apply (Hcc c (or_introl eq_refl)); lia | apply Hmv; lia | apply (Henv t Ht0); lia]. }
  assert (HS' : SlotCtx n env G')
    by (apply (SlotCtx_mono n env G G' Hinc); [intros w ? ?; apply HG0; lia | exact HS]).
  assert (Hm' : FOPrH n G' (FONUMR wm m)) by exact (FOPrH_weaken n G G' _ Hinc Hm).
  assert (Hc02 : FOtms_avoid (c :: m :: env) 0 1000) by avoid_tms.
  pose proof (FOPrH_patf_total (cpat_f rho (FOForall x th)) n G' (B + s1 + 4) env (B + s1)
                ltac:(lia) ltac:(lia) ltac:(intros w ? ?; apply HGT; lia)
                ltac:(intros w ? ?; apply HG0; lia) ltac:(rewrite <- Es0; avoid_tms)
                ltac:(avoid_tms) ltac:(avoid_tms)) as Ht.
  refine (FOPrH_ex_elim n G' (B + s1) _ _ _ _ Ht _); [apply HGT; lia | free_fm |].
  lazymatch goal with |- FOPrH _ ?G2 _ =>
    assert (Hpz : FOPrH n G2 (FOPATF (B + s1 + 4) env (cpat_f rho (FOForall x th))
                               (FOVar (B + s1)))) by apply FOPrH_last;
    assert (HG20 : FOctx_avoid G2 0 1000) by ctx_list;
    assert (Hinc2 : forall X, In X G -> In X G2)
      by (intros X HX; apply in_or_app; left; exact (Hinc X HX));
    assert (Hcl2 : Clean G2 [FOVar (B + s1)] (B + s1 + 4))
      by (split;
          [ intros w Hw;
            assert (Hew : FOtms_avoid env w (S w))
              by (intros t Ht0 w' ? ?; apply (Henv t Ht0); lia);
            apply FOfree_ctx_app_inv; [apply HGc; lia | free_ctx]
          | intros t Ht0 w Hw; destruct Ht0 as [<-|[]]; apply FOin_tm_var_ne; lia ]);
    assert (Hc2 : FOPrH n G2 (FOPATF B (env ++ [m])
                               (cpat_f (rho_sub (Some x) (length env) rho) th) c)) by wk Hc;
    assert (HS2 : SlotCtx n env G2)
      by (apply (SlotCtx_mono n env G' G2); [intros X HX; apply in_or_app; left; exact HX
                                             | intros w ? ?; apply HG20; lia | exact HS']);
    assert (Hm2 : FOPrH n G2 (FONUMR wm m)) by wk Hm'
  end.
  pose proof (HI _ (B + s1 + 4) (FOVar (B + s1)) Hinc2 HG20 ltac:(avoid_tms) ltac:(lia)
                Hcl2 Hpz) as Hpr.
  pose proof (FOPrH_patf_rebase _ n _ B (B + s1 + 4 + 2 * s0) (env ++ [m]) c Hc2 ltac:(lia)
                ltac:(lia) ltac:(rewrite <- Es1; lia) ltac:(rewrite <- Es1; ctx_list)
                ltac:(rewrite <- Es1; avoid_tms) ltac:(rewrite <- Es1; avoid_tms)
                ltac:(avoid_tms)) as Hc1.
  exact (FOPrH_inst_code n _ cores u0 x th rho env m wm (B + s1 + 4) (FOVar (B + s1))
           (B + s1 + 4 + 2 * s0) c (B + s1 + 1) HS2 Hrho Hm2 Hpz Hc1 Hpr HG20 ltac:(lia)
           ltac:(ctx_list) ltac:(lia) ltac:(rewrite <- Es0; lia)
           ltac:(rewrite <- Es0; ctx_list) ltac:(rewrite <- Es1; ctx_list)
           ltac:(avoid_tms) ltac:(avoid_tms) ltac:(rewrite <- Es0; avoid_tms)
           ltac:(rewrite <- Es1; avoid_tms)).
Qed.

(** ** Instantiation of a theorem. *)

Lemma PRI_inst_closed : forall n k V G x th m wm,
  FOProvesTn 0 (FOForall x th) ->
  FOctx_avoid G 0 1000 -> FOPrH n G (FONUMR wm m) -> FOtms_avoid [m] 0 1000 -> 1000 <= V ->
  (forall w, V <= w -> FOin_tm w m = false) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f (rho_sub (Some x) 0 (fun _ => None)) th) [m].
Proof.
  intros n k V G x th m wm Hthm HG Hm Hm0 HV Hmv.
  intros G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  remember (cpat_span (cpat_f (rho_sub (Some x) 0 (fun _ => None)) th)) as s1 eqn:Es1.
  remember (cpat_span (cpat_f (fun _ => None) (FOForall x th))) as s0 eqn:Es0.
  assert (HGT : FOctx_avoid G' B (B + s1 + 3 + 2 * s0 + 2 * s1 + 10))
    by (intros w ? ?; apply HGc; lia).
  assert (HT : FOtms_avoid [c; m] B (B + s1 + 3 + 2 * s0 + 2 * s1 + 10)).
  { intros t Ht0 w ? ?. destruct Ht0 as [<-|[<-|[]]];
      [apply (Hcc c (or_introl eq_refl)); lia | apply Hmv; lia]. }
  assert (Hm' : FOPrH n G' (FONUMR wm m)) by exact (FOPrH_weaken n G G' _ Hinc Hm).
  assert (HS' : SlotCtx n [] G') by (split; [intros w ? ?; apply HG0; lia | intros i Hi; cbn in Hi; lia]).
  pose proof (FOPrH_patf_closed_code n G' (FOForall x th) (B + s1 + 3) ltac:(lia)) as Hd0.
  pose proof (FOPrH_pru_thm n G' k (FOForall x th) Hthm) as Hpr.
  pose proof (FOPrH_patf_rebase _ n _ B (B + s1 + 3 + 2 * s0) ([] ++ [m]) c Hc ltac:(lia)
                ltac:(lia) ltac:(rewrite <- Es1; lia) ltac:(rewrite <- Es1; ctx_list)
                ltac:(rewrite <- Es1; cbn [app]; avoid_tms)
                ltac:(rewrite <- Es1; cbn [app]; avoid_tms)
                ltac:(cbn [app]; avoid_tms)) as Hc1.
  exact (FOPrH_inst_code n G' (FOPrCores k) (FOu0 k) x th (fun _ => None) [] m wm (B + s1 + 3)
           (FOnumeral (FOcode_f (FOForall x th))) (B + s1 + 3 + 2 * s0) c B HS'
           ltac:(intros z i Hz; discriminate) Hm' Hd0 Hc1 Hpr HG0 ltac:(lia)
           ltac:(intros w ? ?; apply HGT; lia) ltac:(lia) ltac:(rewrite <- Es0; lia)
           ltac:(rewrite <- Es0; intros w ? ?; apply HGT; lia)
           ltac:(cbn [length]; rewrite <- Es1; intros w ? ?; apply HGT; lia)
           ltac:(avoid_tms) ltac:(avoid_tms) ltac:(rewrite <- Es0; avoid_tms)
           ltac:(cbn [length]; rewrite <- Es1; avoid_tms)).
Qed.

(** ** Provable instances converted along [CPrel]. *)

Lemma PRI_conv : forall n cores u0 V G p p' env env',
  (forall G', (forall X, In X G -> In X G') -> CPrel n G' env env' p p') ->
  (forall t, In t (env ++ env') -> forall w, V <= w -> FOin_tm w t = false) ->
  FOtms_avoid (env ++ env') 0 1000 -> 1000 <= V ->
  PRI n cores u0 V G p env -> PRI n cores u0 V G p' env'.
Proof.
  intros n cores u0 V G p p' env env' HR Habove Hlo HV HI.
  intros G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  assert (HGT : FOctx_avoid G' B (B + cpat_span p' + cpat_span p + 1))
    by (intros w ? ?; apply HGc; lia).
  assert (HT : FOtms_avoid (c :: env ++ env') B (B + cpat_span p' + cpat_span p + 1)).
  { intros t Ht0 w ? ?. destruct Ht0 as [<-|Ht0];
      [apply (Hcc c (or_introl eq_refl)); lia | apply (Habove t Ht0); lia]. }
  pose proof (FOPrH_patf_conv n G' env env' p p' (HR G' Hinc) G' (B + cpat_span p') B c
                (fun X HX => HX) Hc ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(intros w ? ?; apply HGT; lia) ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(apply (FOtms_avoid_sub _ 0 1000); [|lia|lia]; avoid_tms)) as Hc'.
  assert (Hcl : Clean G' [c] (B + cpat_span p')).
  { split; [intros w Hw; apply HGc; lia | intros t Ht0 w Hw; apply (Hcc t Ht0); lia]. }
  exact (HI G' (B + cpat_span p') c Hinc HG0 Hc0 ltac:(lia) Hcl Hc').
Qed.
