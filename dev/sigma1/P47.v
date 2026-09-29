From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41
  P42 P43 P44 P45 P46.
Open Scope fo_scope.

(** ** Zero or successor, for provable instances. *)

Lemma PRI_zs : forall n cores u0 V R G p env t,
  1000 <= V -> FOtms_avoid [t] 0 1000 -> (forall w, V <= w -> FOin_tm w t = false) ->
  FOtms_avoid env 0 1000 -> (forall s, In s env -> forall w, V <= w -> FOin_tm w s = false) ->
  PRI n cores u0 V (G ++ [FOEq t FOZero]) p env ->
  (forall w, V <= w -> R <= w ->
     PRI n cores u0 (S w) (G ++ [FOEq t (FOSucc (FOVar w))]) p env) ->
  PRI n cores u0 V G p env.
Proof.
  intros n cores u0 V R G p env t HV Ht0 Htv Henv0 Henv H0 HS.
  intros G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  remember (B + cpat_span p + R + 1) as w eqn:Ew.
  assert (Hcz : FOtms_avoid [c] B (S (S w + cpat_span p))).
  { intros s [<-|[]] w' ? ?. apply (Hcc c (or_introl eq_refl)). lia. }
  assert (Henvz : FOtms_avoid env V (S (S w + cpat_span p))).
  { intros s Hs w' ? ?. apply (Henv s Hs). lia. }
  assert (Htz : FOtms_avoid [t] V (S (S w + cpat_span p))).
  { intros s [<-|[]] w' ? ?. apply Htv. lia. }
  apply (FOPrH_cases_zs n G' t w (FOPRu cores u0 c) ltac:(lia) ltac:(fr_tm)
           ltac:(apply HGc; lia) ltac:(free_fm) ltac:(fr_tm)).
  - apply (H0 (G' ++ [FOEq t FOZero]) B c).
    + intros Y HY. apply in_app_or in HY. destruct HY as [HY|HY]; apply in_or_app;
        [left; exact (Hinc Y HY) | right; exact HY].
    + intros w' ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|]. free_ctx.
    + exact Hc0.
    + exact HBV.
    + split; [|exact Hcc]. intros w' Hw'. apply FOfree_ctx_app_inv; [apply HGc; lia|].
      apply FOfree_ctx_cons; [|apply FOfree_ctx_nil]. cbn [FOfree_in].
      rewrite (Htv w' ltac:(lia)). reflexivity.
    + apply FOPrH_weak_app. exact Hc.
  - pose proof (FOPrH_patf_rebase p n G' B (S w) env c Hc ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(intros w' ? ?; apply HGc; lia) ltac:(avoid_tms) ltac:(avoid_tms)
                  ltac:(avoid_tms)) as Hc1.
    apply (HS w ltac:(lia) ltac:(lia) (G' ++ [FOEq t (FOSucc (FOVar w))]) (S w) c).
    + intros Y HY. apply in_app_or in HY. destruct HY as [HY|HY]; apply in_or_app;
        [left; exact (Hinc Y HY) | right; exact HY].
    + intros w' ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|]. free_ctx.
    + exact Hc0.
    + lia.
    + split.
      * intros w' Hw'. apply FOfree_ctx_app_inv; [apply HGc; lia|].
        apply FOfree_ctx_cons; [|apply FOfree_ctx_nil]. cbn [FOfree_in FOin_tm].
        rewrite (Htv w' ltac:(lia)). cbn. apply Nat.eqb_neq. lia.
      * intros s [<-|[]] w' Hw'. apply (Hcc c (or_introl eq_refl)). lia.
    + apply FOPrH_weak_app. exact Hc1.
Qed.

(** ** Distinct numbers, inside the provability predicate.

    [PhiNeq Xt]: for every [Y] other than [Xt] and all numeral codes
    [a] of [Xt] and [b] of [Y], the disequation of the codes is provable. *)

Definition fNeq2 : FOFormula := FONeg (FOEq (FOVar 0) (FOVar 1)).

Definition PhiNeq (cores : list nat) (u0 B0 Y a b : nat) (P : CPat) (Xt : FOTerm) : FOFormula :=
  FOForall Y (FOForall a (FOForall b
    (FOImplF (FONeg (FOEq Xt (FOVar Y)))
      (FOImplF (FONUMR Xt (FOVar a))
        (FOImplF (FONUMR (FOVar Y) (FOVar b)) (PRIf cores u0 B0 [FOVar a; FOVar b] P)))))).

Lemma PhiNeq_subst : forall cores u0 B0 Y a b P N s,
  N <> Y -> N <> a -> N <> b -> 1000 <= N -> N < B0 -> FOtms_avoid [s] 802 805 ->
  FOsubst_f N s (PhiNeq cores u0 B0 Y a b P (FOVar N)) = PhiNeq cores u0 B0 Y a b P s.
Proof.
  intros cores u0 B0 Y a b P N s HY Ha Hb HN HB Hs. unfold PhiNeq.
  rewrite (FOsubst_f_all_ne N s Y) by lia. rewrite (FOsubst_f_all_ne N s a) by lia.
  rewrite (FOsubst_f_all_ne N s b) by lia.
  rewrite !FOsubst_f_impl, FOsubst_f_neg, FOsubst_f_eq, !FOsubst_f_NUMR by (lia || avoid_tms).
  rewrite FOsubst_f_PRIf by lia. cbn [map].
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne by lia. reflexivity.
Qed.

Lemma PhiNeq_inst : forall n G cores u0 B0 Y a b P Xt ty ta tb,
  FOPrH n G (PhiNeq cores u0 B0 Y a b P Xt) ->
  Y <> a -> Y <> b -> a <> b -> 1000 <= Y -> 1000 <= a -> 1000 <= b ->
  Y < B0 -> a < B0 -> b < B0 ->
  FOtms_avoid [Xt] Y (S Y) -> FOtms_avoid [Xt; ty] a (S a) -> FOtms_avoid [Xt; ty; ta] b (S b) ->
  FOtms_avoid [ty; ta; tb] 0 1000 -> FOtms_avoid [ty; ta; tb] B0 (B0 + cpat_span P) ->
  FOPrH n G (FOImplF (FONeg (FOEq Xt ty)) (FOImplF (FONUMR Xt ta)
    (FOImplF (FONUMR ty tb) (PRIf cores u0 B0 [ta; tb] P)))).
Proof.
  intros n G cores u0 B0 Y a b P Xt ty ta tb H HYa HYb Hab HY Ha Hb HYB HaB HbB
    HavY Hava Havb Hav0 HavB.
  unfold PhiNeq in H.
  apply (FOPrH_inst n G Y ty) in H;
    [| apply FOsubst_ok_all; [fr_tm|]; apply FOsubst_ok_all; [fr_tm|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_neg; apply FOsubst_ok_eq|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_PRIf; [lia | fr_tm | avoid_tm]].
  rewrite (FOsubst_f_all_ne Y ty a) in H by lia. rewrite (FOsubst_f_all_ne Y ty b) in H by lia.
  rewrite !FOsubst_f_impl, FOsubst_f_neg, FOsubst_f_eq, !FOsubst_f_NUMR in H by (lia || avoid_tms).
  rewrite FOsubst_f_PRIf in H by lia. cbn [map] in H.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in H by lia.
  rewrite (FOsubst_t_not_in Xt Y ty) in H by fr_tm.
  apply (FOPrH_inst n G a ta) in H;
    [| apply FOsubst_ok_all; [fr_tm|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_neg; apply FOsubst_ok_eq|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_PRIf; [lia | fr_tm | avoid_tm]].
  rewrite (FOsubst_f_all_ne a ta b) in H by lia.
  rewrite !FOsubst_f_impl, FOsubst_f_neg, FOsubst_f_eq, !FOsubst_f_NUMR in H by (lia || avoid_tms).
  rewrite FOsubst_f_PRIf in H by lia. cbn [map] in H.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in H by lia.
  rewrite (FOsubst_t_not_in Xt a ta), (FOsubst_t_not_in ty a ta) in H by fr_tm.
  apply (FOPrH_inst n G b tb) in H;
    [| apply FOsubst_ok_impl; [apply FOsubst_ok_neg; apply FOsubst_ok_eq|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_PRIf; [lia | fr_tm | avoid_tm]].
  rewrite !FOsubst_f_impl, FOsubst_f_neg, FOsubst_f_eq, !FOsubst_f_NUMR in H by (lia || avoid_tms).
  rewrite FOsubst_f_PRIf in H by lia. cbn [map] in H.
  rewrite FOsubst_t_var_eq' in H.
  rewrite (FOsubst_t_not_in Xt b tb), (FOsubst_t_not_in ty b tb), (FOsubst_t_not_in ta b tb)
    in H by fr_tm.
  exact H.
Qed.

Ltac free_fm ::=
  lazymatch goal with
  | |- FOfree_in _ (PhiNeq _ _ _ _ _ _ _ _) = false => unfold PhiNeq; free_fm
  | |- FOfree_in _ (PhiOp _ _ _ _ _ _ _ _ _ _) = false => unfold PhiOp; free_fm
  | |- FOfree_in _ (PRIf _ _ _ _ _) = false => apply FOfree_in_PRIf; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FODISPCASES _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FODISPCASES_free
  | |- FOfree_in _ (FOSTEP5 _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false => free_by FOSTEP5_free
  | |- FOfree_in _ (FOTBLVALID _ _ _ _ _ _ _ _ _ _ _ _) = false => free_by FOTBLVALID_free
  | |- FOfree_in _ (FOlookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOlookup_free
  | |- FOfree_in _ (FOPRu _ _ _) = false =>
      first [ apply FOfree_in_PRu; [nat_fast | avoid_tms]
            | apply FOfree_in_PRu_all; [avoid_tms | avoid_tm] ]
  | |- FOfree_in _ (FOTBLEX3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_TBLEX3_any; [nat_fast | avoid_tms]
  | |- FOfree_in ?w (FOBexC ?v _ _) = false =>
      first [ constr_eq w v; apply FOfree_in_FOBexC_self
            | rewrite FOBexC_ltv; free_fm ]
  | |- FOfree_in _ (FOJUSTCK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOJUSTCK_free
  | |- FOfree_in _ (FOGUARDC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOGUARDC_free
  | |- FOfree_in _ (FONUMR _ _) = false =>
      first [ apply FOfree_in_NUMR_all; avoid_tms | unfold FONUMR; free_fm ]
  | |- FOfree_in _ (FOTBLEX _ _ _ _ _) = false =>
      first [ apply FOfree_in_TBLEX_any; [nat_fast | avoid_tms]
            | apply FOfree_in_TBLEX_all; [avoid_tms | avoid_tms] ]
  | |- FOfree_in _ (FOM3F _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_M3F_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOFTRACK _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_FTRACK_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOJTRACK _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_JTRACK_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOPATF _ _ _ _) = false =>
      first [ apply FOfree_in_PATF_any; [nat_fast | avoid_tms]
            | apply FOfree_in_PATF_lo; [nat_fast | avoid_tms] ]
  | |- FOfree_in _ (FOGUARDB _) = false =>
      apply FOfree_in_GUARDB_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOTEXT _ _ _ _ _ _ _) = false => unfold FOTEXT; free_fm
  | |- FOfree_in _ (FOTBLNEW _ _ _ _ _ _ _) = false => unfold FOTBLNEW; free_fm
  | |- FOfree_in _ (FOINCL _ _) = false =>
      apply FOfree_in_INCL_any; [nat_fast | avoid_tms]
  | |- _ => free_fm_core
  end.

Lemma FOPr_zero_ne_succ : FOProvesTn 0 (FONeg (FOEq FOZero (FOSucc (FOVar 0)))).
Proof.
  change (FOPrH 0 [] (FONeg (FOEq FOZero (FOSucc (FOVar 0))))). unfold FONeg.
  apply FOPrH_intro. apply (FOPrH_Q_succ_nonzero _ _ (FOVar 0)). apply FOPrH_eq_sym.
  apply FOPrH_assum. left. reflexivity.
Qed.

Lemma FOPr_succ_ne_zero : FOProvesTn 0 (FONeg (FOEq (FOSucc (FOVar 0)) FOZero)).
Proof.
  change (FOPrH 0 [] (FONeg (FOEq (FOSucc (FOVar 0)) FOZero))). unfold FONeg.
  apply FOPrH_intro. apply (FOPrH_Q_succ_nonzero _ _ (FOVar 0)).
  apply FOPrH_assum. left. reflexivity.
Qed.

Lemma FOPr_succ_ne : FOProvesTn 0 (FOImplF (FONeg (FOEq (FOVar 0) (FOVar 1)))
                                   (FONeg (FOEq (FOSucc (FOVar 0)) (FOSucc (FOVar 1))))).
Proof.
  change (FOPrH 0 [] (FOImplF (FONeg (FOEq (FOVar 0) (FOVar 1)))
                                   (FONeg (FOEq (FOSucc (FOVar 0)) (FOSucc (FOVar 1)))))).
  unfold FONeg. apply FOPrH_intro. apply FOPrH_intro. cbn [app].
  apply (FOPrH_mp _ _ (FOEq (FOVar 0) (FOVar 1))); [apply FOPrH_assum; left; reflexivity|].
  apply FOPrH_Q_succ_inj. apply FOPrH_assum. right. left. reflexivity.
Qed.

Lemma EnvOK1 : forall n V G a wa, FOctx_avoid G 2 1000 -> FOPrH n G (FONUMR wa a) ->
  FOtms_avoid [a] 0 1000 -> 1000 <= V ->
  (forall t, In t [a] -> forall w, V <= w -> FOin_tm w t = false) -> EnvOK n V G [a].
Proof.
  intros n V G a wa HG Ha H0 HV Hab.
  split; [split; [exact HG|] | split; [exact H0 | split; [exact HV | exact Hab]]].
  intros [|i] Hi; cbn [nth]; [exists wa; exact Ha | cbn in Hi; lia].
Qed.

Lemma EnvOK2 : forall n V G a b wa wb, FOctx_avoid G 2 1000 ->
  FOPrH n G (FONUMR wa a) -> FOPrH n G (FONUMR wb b) ->
  FOtms_avoid [a; b] 0 1000 -> 1000 <= V ->
  (forall t, In t [a; b] -> forall w, V <= w -> FOin_tm w t = false) -> EnvOK n V G [a; b].
Proof.
  intros n V G a b wa wb HG Ha Hb H0 HV Hab.
  split; [split; [exact HG|] | split; [exact H0 | split; [exact HV | exact Hab]]].
  intros [|[|i]] Hi; cbn [nth]; [exists wa; exact Ha | exists wb; exact Hb | cbn in Hi; lia].
Qed.

Lemma NEQ_base : forall n k V G,
  2000 <= V -> FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  PRI n (FOPrCores k) (FOu0 k) (V + 4)
    (((G ++ [FONeg (FOEq FOZero (FOVar (V + 1)))]) ++ [FONUMR FOZero (FOVar (V + 2))])
       ++ [FONUMR (FOVar (V + 1)) (FOVar (V + 3))])
    (cpat_f (rhoN 2) fNeq2) [FOVar (V + 2); FOVar (V + 3)].
Proof.
  intros n k V G HV HG0 HGV.
  lazymatch goal with |- PRI _ _ _ _ ?G1 _ _ =>
    assert (HG1 : FOctx_avoid G1 0 1000) by (intros w ? ?; free_ctx);
    assert (Hne : FOPrH n G1 (FONeg (FOEq FOZero (FOVar (V + 1))))) by wk_in;
    assert (Ha : FOPrH n G1 (FONUMR FOZero (FOVar (V + 2)))) by wk_in;
    assert (Hb : FOPrH n G1 (FONUMR (FOVar (V + 1)) (FOVar (V + 3)))) by wk_in
  end.
  pose proof (FOPrH_numr_inv0 n _ (FOVar (V + 2)) ltac:(intros w ? ?; apply HG1; lia)
                ltac:(avoid_tms) Ha) as Ca.
  refine (PRI_zs n _ _ (V + 4) (V + 4 + cpat_span (cpat_f (rhoN 2) fNeq2) + 1) _ _ _
            (FOVar (V + 1)) _ _ _ _ _ _ _);
    [lia | avoid_tms | intros w ?; fr_tm | avoid_tms | above_tac | |].
  - apply PRI_efq. unfold FONeg in Hne.
    apply (FOPrH_mp _ _ _ _ (FOPrH_weak_app _ _ _ _ Hne)). apply FOPrH_eq_sym. apply FOPrH_last.
  - intros w Hw HR.
    lazymatch goal with |- PRI _ _ _ _ ?G2 _ _ =>
      assert (HG2 : FOctx_avoid G2 0 1000) by (intros w' ? ?; free_ctx);
      assert (HY : FOPrH n G2 (FOEq (FOVar (V + 1)) (FOSucc (FOVar w)))) by wk_in;
      assert (Hb2 : FOPrH n G2 (FONUMR (FOVar (V + 1)) (FOVar (V + 3)))) by wk Hb;
      assert (Ca2 : FOPrH n G2 (FOcpairF (FOnumeral 1) FOZero (FOVar (V + 2)))) by wk Ca
    end.
    pose proof (FOPrH_numr_cong1 n _ (FOVar (V + 1)) (FOSucc (FOVar w)) (FOVar (V + 3)) Hb2 HY
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Hb3.
    refine (PRI_numr_invS n _ _ (S w) 0 _ _ _ (FOVar w) (FOVar (V + 3)) Hb3 _ _ _ _ _ _);
      [lia | avoid_tms | above_tac | avoid_tms | above_tac |].
    intros w' Hw' _.
    lazymatch goal with |- PRI _ _ _ _ ?G3 _ _ =>
      assert (HG3 : FOctx_avoid G3 0 1000) by (intros w'' ? ?; free_ctx);
      assert (Cb : FOPrH n G3 (FOcpairF (FOnumeral 2) (FOVar w') (FOVar (V + 3)))) by wk_in;
      assert (Nw : FOPrH n G3 (FONUMR (FOVar w) (FOVar w'))) by wk_in;
      assert (Ca3 : FOPrH n G3 (FOcpairF (FOnumeral 1) FOZero (FOVar (V + 2)))) by wk Ca2;
      assert (HE : EnvOK n (S w') G3 [FOVar w'])
        by (apply (EnvOK1 n _ _ _ (FOVar w)); [intros w'' ? ?; apply HG3; lia | exact Nw
                                              | avoid_tms | lia | above_tac])
    end.
    pose proof (PRI_thm_open n k (S w') _ _ (rhoN 1) _ FOPr_zero_ne_succ HE
                  (rhoN_fv 1 (FONeg (FOEq FOZero (FOSucc (FOVar 0))))
                     ltac:(apply Nat.ltb_lt; vm_compute; reflexivity))) as T.
    refine (PRI_conv n _ _ (S w') _ _ _ _ _ _ _ _ _ T); [| above_tac | avoid_tms | lia].
    intros G' Hinc.
    pose proof (FOPrH_weaken n _ G' _ Hinc Ca3) as C1.
    pose proof (FOPrH_weaken n _ G' _ Hinc Cb) as C2.
    unfold fNeq2, rhoN, FONeg. cbn [cpat_f cpat_tm Nat.ltb Nat.leb]. cprel_tac.
Qed.

Lemma NEQ_step : forall n k V G,
  2000 <= V -> FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  PRI n (FOPrCores k) (FOu0 k) (V + 4)
    ((((G ++ [PhiNeq (FOPrCores k) (FOu0 k) (V + 4) (V + 1) (V + 2) (V + 3)
                (cpat_f (rhoN 2) fNeq2) (FOVar V)])
        ++ [FONeg (FOEq (FOSucc (FOVar V)) (FOVar (V + 1)))])
        ++ [FONUMR (FOSucc (FOVar V)) (FOVar (V + 2))])
        ++ [FONUMR (FOVar (V + 1)) (FOVar (V + 3))])
    (cpat_f (rhoN 2) fNeq2) [FOVar (V + 2); FOVar (V + 3)].
Proof.
  intros n k V G HV HG0 HGV.
  set (R := V + 4 + cpat_span (cpat_f (rhoN 2) fNeq2) + 1).
  lazymatch goal with |- PRI _ _ _ _ ?G1 _ _ =>
    assert (HG1 : FOctx_avoid G1 0 1000) by (intros w ? ?; free_ctx);
    assert (HPhi : FOPrH n G1 (PhiNeq (FOPrCores k) (FOu0 k) (V + 4) (V + 1) (V + 2) (V + 3)
                                (cpat_f (rhoN 2) fNeq2) (FOVar V))) by wk_in;
    assert (Hne : FOPrH n G1 (FONeg (FOEq (FOSucc (FOVar V)) (FOVar (V + 1))))) by wk_in;
    assert (Ha : FOPrH n G1 (FONUMR (FOSucc (FOVar V)) (FOVar (V + 2)))) by wk_in;
    assert (Hb : FOPrH n G1 (FONUMR (FOVar (V + 1)) (FOVar (V + 3)))) by wk_in
  end.
  refine (PRI_numr_invS n _ _ (V + 4) R _ _ _ (FOVar V) (FOVar (V + 2)) Ha _ _ _ _ _ _);
    [lia | avoid_tms | above_tac | avoid_tms | above_tac |].
  intros w1 Hw1 HR1.
  lazymatch goal with |- PRI _ _ _ _ ?G2 _ _ =>
    assert (HG2 : FOctx_avoid G2 0 1000) by (intros w ? ?; free_ctx);
    assert (Ca : FOPrH n G2 (FOcpairF (FOnumeral 2) (FOVar w1) (FOVar (V + 2)))) by wk_in;
    assert (N1 : FOPrH n G2 (FONUMR (FOVar V) (FOVar w1))) by wk_in;
    assert (HPhi2 : FOPrH n G2 (PhiNeq (FOPrCores k) (FOu0 k) (V + 4) (V + 1) (V + 2) (V + 3)
                                  (cpat_f (rhoN 2) fNeq2) (FOVar V))) by wk HPhi;
    assert (Hne2 : FOPrH n G2 (FONeg (FOEq (FOSucc (FOVar V)) (FOVar (V + 1))))) by wk Hne;
    assert (Hb2 : FOPrH n G2 (FONUMR (FOVar (V + 1)) (FOVar (V + 3)))) by wk Hb
  end.
  refine (PRI_zs n _ _ (S w1) R _ _ _ (FOVar (V + 1)) _ _ _ _ _ _ _);
    [lia | avoid_tms | intros w ?; fr_tm | avoid_tms | above_tac | |].
  - lazymatch goal with |- PRI _ _ _ _ ?G3 _ _ =>
      assert (HG3 : FOctx_avoid G3 0 1000) by (intros w ? ?; free_ctx);
      assert (HY : FOPrH n G3 (FOEq (FOVar (V + 1)) FOZero)) by wk_in;
      assert (Hb3 : FOPrH n G3 (FONUMR (FOVar (V + 1)) (FOVar (V + 3)))) by wk Hb2;
      assert (Ca3 : FOPrH n G3 (FOcpairF (FOnumeral 2) (FOVar w1) (FOVar (V + 2)))) by wk Ca;
      assert (N13 : FOPrH n G3 (FONUMR (FOVar V) (FOVar w1))) by wk N1
    end.
    pose proof (FOPrH_numr_cong1 n _ (FOVar (V + 1)) FOZero (FOVar (V + 3)) Hb3 HY
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Hb0.
    pose proof (FOPrH_numr_inv0 n _ (FOVar (V + 3)) ltac:(intros w ? ?; apply HG3; lia)
                  ltac:(avoid_tms) Hb0) as Cb.
    lazymatch type of HG3 with FOctx_avoid ?G3 _ _ =>
      assert (HE : EnvOK n (S w1) G3 [FOVar w1])
        by (apply (EnvOK1 n _ _ _ (FOVar V)); [intros w ? ?; apply HG3; lia | exact N13
                                             | avoid_tms | lia | above_tac])
    end.
    pose proof (PRI_thm_open n k (S w1) _ _ (rhoN 1) _ FOPr_succ_ne_zero HE
                  (rhoN_fv 1 (FONeg (FOEq (FOSucc (FOVar 0)) FOZero))
                     ltac:(apply Nat.ltb_lt; vm_compute; reflexivity))) as T.
    refine (PRI_conv n _ _ (S w1) _ _ _ _ _ _ _ _ _ T); [| above_tac | avoid_tms | lia].
    intros G' Hinc.
    pose proof (FOPrH_weaken n _ G' _ Hinc Ca3) as C1.
    pose proof (FOPrH_weaken n _ G' _ Hinc Cb) as C2.
    unfold fNeq2, rhoN, FONeg. cbn [cpat_f cpat_tm Nat.ltb Nat.leb]. cprel_tac.
  - intros w2 Hw2 HR2.
    lazymatch goal with |- PRI _ _ _ _ ?G3 _ _ =>
      assert (HG3 : FOctx_avoid G3 0 1000) by (intros w ? ?; free_ctx);
      assert (HY : FOPrH n G3 (FOEq (FOVar (V + 1)) (FOSucc (FOVar w2)))) by wk_in;
      assert (Hb3 : FOPrH n G3 (FONUMR (FOVar (V + 1)) (FOVar (V + 3)))) by wk Hb2
    end.
    pose proof (FOPrH_numr_cong1 n _ (FOVar (V + 1)) (FOSucc (FOVar w2)) (FOVar (V + 3)) Hb3 HY
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Hb4.
    refine (PRI_numr_invS n _ _ (S w2) R _ _ _ (FOVar w2) (FOVar (V + 3)) Hb4 _ _ _ _ _ _);
      [lia | avoid_tms | above_tac | avoid_tms | above_tac |].
    intros w3 Hw3 HR3.
    lazymatch goal with |- PRI _ _ _ _ ?G4 _ _ =>
      assert (HG4 : FOctx_avoid G4 0 1000) by (intros w ? ?; free_ctx);
      assert (Cb : FOPrH n G4 (FOcpairF (FOnumeral 2) (FOVar w3) (FOVar (V + 3)))) by wk_in;
      assert (N3 : FOPrH n G4 (FONUMR (FOVar w2) (FOVar w3))) by wk_in;
      assert (HY4 : FOPrH n G4 (FOEq (FOVar (V + 1)) (FOSucc (FOVar w2)))) by wk HY;
      assert (Ca4 : FOPrH n G4 (FOcpairF (FOnumeral 2) (FOVar w1) (FOVar (V + 2)))) by wk Ca;
      assert (N14 : FOPrH n G4 (FONUMR (FOVar V) (FOVar w1))) by wk N1;
      assert (HPhi4 : FOPrH n G4 (PhiNeq (FOPrCores k) (FOu0 k) (V + 4) (V + 1) (V + 2)
                                    (V + 3) (cpat_f (rhoN 2) fNeq2) (FOVar V))) by wk HPhi2;
      assert (Hne4 : FOPrH n G4 (FONeg (FOEq (FOSucc (FOVar V)) (FOVar (V + 1))))) by wk Hne2
    end.
    lazymatch type of HG4 with FOctx_avoid ?G4 _ _ =>
      assert (Hvw : FOPrH n G4 (FONeg (FOEq (FOVar V) (FOVar w2))))
    end.
    { unfold FONeg. apply FOPrH_intro.
      apply (FOPrH_mp _ _ _ _ (FOPrH_weak_app _ _ _ _ Hne4)).
      apply (FOPrH_eq_trans _ _ _ (FOSucc (FOVar w2))).
      - apply FOPrH_congS. apply FOPrH_last.
      - apply FOPrH_eq_sym. apply FOPrH_weak_app. exact HY4. }
    pose proof (PhiNeq_inst n _ _ _ (V + 4) (V + 1) (V + 2) (V + 3) _ (FOVar V) (FOVar w2)
                  (FOVar w1) (FOVar w3) HPhi4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(avoid_tms)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as IH.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ IH Hvw) N14) N3) as IHf.
    pose proof (PRIf_to_PRI n _ _ (S w3) _ _ _ (V + 4) IHf ltac:(lia) ltac:(avoid_tms) ltac:(lia)
                  ltac:(avoid_tms) ltac:(above_tac)) as IHP.
    lazymatch type of HG4 with FOctx_avoid ?G4 _ _ =>
      assert (HE : EnvOK n (S w3) G4 [FOVar w1; FOVar w3])
        by (apply (EnvOK2 n _ _ _ _ (FOVar V) (FOVar w2));
            [intros w ? ?; apply HG4; lia | exact N14 | exact N3 | avoid_tms | lia
            | above_tac])
    end.
    pose proof (PRI_thm_open n k (S w3) _ _ (rhoN 2) _ FOPr_succ_ne HE
                  (rhoN_fv 2 (FOImplF (FONeg (FOEq (FOVar 0) (FOVar 1)))
                                (FONeg (FOEq (FOSucc (FOVar 0)) (FOSucc (FOVar 1)))))
                     ltac:(apply Nat.ltb_lt; vm_compute; reflexivity))) as T.
    pose proof (PRI_mp n _ _ (S w3) _ (rhoN 2) _ _ _ HE (rhoN_range 2) T IHP) as T2.
    refine (PRI_conv n _ _ (S w3) _ _ _ _ _ _ _ _ _ T2); [| above_tac | avoid_tms | lia].
    intros G' Hinc.
    pose proof (FOPrH_weaken n _ G' _ Hinc Ca4) as C1.
    pose proof (FOPrH_weaken n _ G' _ Hinc Cb) as C2.
    unfold fNeq2, rhoN, FONeg. cbn [cpat_f cpat_tm Nat.ltb Nat.leb]. cprel_tac.
Qed.

Lemma PRI_neq : forall n k V G x y m1 m2,
  2000 <= V -> FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  FOtms_avoid [x; y; m1; m2] 0 1100 ->
  (forall t, In t [x; y; m1; m2] -> forall w, V <= w -> FOin_tm w t = false) ->
  FOPrH n G (FONeg (FOEq x y)) -> FOPrH n G (FONUMR x m1) -> FOPrH n G (FONUMR y m2) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f (rhoN 2) fNeq2) [m1; m2].
Proof.
  intros n k V G x y m1 m2 HV HG0 HGV Hav0 Havv Hne Hx Hy.
  assert (HI : FOPrH n G (FOForall V (PhiNeq (FOPrCores k) (FOu0 k) (V + 4) (V + 1) (V + 2)
                                        (V + 3) (cpat_f (rhoN 2) fNeq2) (FOVar V)))).
  { apply FOPrH_ind; [apply HGV; lia | |].
    - rewrite PhiNeq_subst by first [lia | avoid_tms].
      unfold PhiNeq.
      apply FOPrH_all_intro; [apply HGV; lia|]. apply FOPrH_all_intro; [apply HGV; lia|].
      apply FOPrH_all_intro; [apply HGV; lia|].
      apply FOPrH_intro. apply FOPrH_intro. apply FOPrH_intro.
      apply (PRI_to_PRIf n _ _ (V + 4) _ [FOVar (V + 2); FOVar (V + 3)] _ (V + 4)
               (NEQ_base n k V G HV HG0 HGV));
        [lia | lia | intros w ? ?; free_ctx | intros w ?; free_ctx | avoid_tms | above_tac].
    - rewrite PhiNeq_subst by first [lia | avoid_tms].
      unfold PhiNeq at 2.
      apply FOPrH_all_intro; [free_ctx|]. apply FOPrH_all_intro; [free_ctx|].
      apply FOPrH_all_intro; [free_ctx|].
      apply FOPrH_intro. apply FOPrH_intro. apply FOPrH_intro.
      apply (PRI_to_PRIf n _ _ (V + 4) _ [FOVar (V + 2); FOVar (V + 3)] _ (V + 4)
               (NEQ_step n k V G HV HG0 HGV));
        [lia | lia | intros w ? ?; free_ctx | intros w ?; free_ctx | avoid_tms | above_tac]. }
  apply (FOPrH_inst n G V x) in HI;
    [| unfold PhiNeq; apply FOsubst_ok_all; [fr_tm|]; apply FOsubst_ok_all; [fr_tm|];
       apply FOsubst_ok_all; [fr_tm|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_neg; apply FOsubst_ok_eq|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_PRIf; [lia | fr_tm | avoid_tm]].
  rewrite PhiNeq_subst in HI by first [lia | avoid_tms].
  pose proof (PhiNeq_inst n G _ _ (V + 4) (V + 1) (V + 2) (V + 3) _ x y m1 m2 HI ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(avoid_tms)) as HI2.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ HI2 Hne) Hx) Hy) as HP.
  exact (PRIf_to_PRI n _ _ V G [m1; m2] _ (V + 4) HP ltac:(lia) ltac:(avoid_tms) ltac:(lia)
           ltac:(avoid_tms) ltac:(above_tac)).
Qed.

Lemma PRI_neq_gen : forall n k V G rho env z1 z2 j1 j2 x y,
  2000 <= V -> FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  EnvOK n V G env -> FOtms_avoid env 0 1100 -> FOtms_avoid [x; y] 0 1100 ->
  (forall t, In t [x; y] -> forall w, V <= w -> FOin_tm w t = false) ->
  rho z1 = Some j1 -> rho z2 = Some j2 ->
  FOPrH n G (FONeg (FOEq x y)) -> FOPrH n G (FONUMR x (nth j1 env FOZero)) ->
  FOPrH n G (FONUMR y (nth j2 env FOZero)) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho (FONeg (FOEq (FOVar z1) (FOVar z2)))) env.
Proof.
  intros n k V G rho env z1 z2 j1 j2 x y HV HG0 HGV HE Henv Hxy Hxyv Hz1 Hz2 Hne H1 H2.
  pose proof HE as [_ [_ [_ Henvv]]].
  pose proof (PRI_neq n k V G x y (nth j1 env FOZero) (nth j2 env FOZero) HV HG0 HGV
                ltac:(avoid_tms) ltac:(above_tac) Hne H1 H2) as T.
  refine (PRI_conv n _ _ V G _ _ _ _ _ _ _ _ T); [| above_tac | avoid_tms | lia].
  intros G' Hinc. unfold fNeq2, rhoN, FONeg. cbn [cpat_f cpat_tm Nat.ltb Nat.leb].
  rewrite Hz1, Hz2. cprel_tac.
Qed.
