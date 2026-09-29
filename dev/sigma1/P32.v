From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31.
Open Scope fo_scope.

(** ** Pattern facts have no free variable below their base other than
    those of their terms. *)

Lemma FOfree_in_PATF_lo : forall p w B env d,
  w < B -> FOtms_avoid (d :: env) w (S w) -> FOfree_in w (FOPATF B env p d) = false.
Proof.
  induction p as [k|i|q IH|a IHa b IHb]; intros w B env d Hw Hav; cbn [FOPATF].
  - cbn [FOfree_in]. rewrite (Hav d (or_introl eq_refl) w ltac:(lia) ltac:(lia)).
    rewrite FOin_tm_numeral. reflexivity.
  - cbn [FOfree_in]. rewrite (Hav d (or_introl eq_refl) w ltac:(lia) ltac:(lia)).
    destruct (nth_in_or_default i env FOZero) as [Hin| ->].
    + rewrite (Hav _ (or_intror Hin) w ltac:(lia) ltac:(lia)). reflexivity.
    + reflexivity.
  - rewrite FOBexC_ltv, FOfree_in_FOExists_neq by lia.
    rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
    + apply FOfree_in_ltv; [lia | apply (Hav d (or_introl eq_refl)); lia].
    + rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
      * cbn [FOfree_in FOin_tm]. rewrite (Hav d (or_introl eq_refl) w ltac:(lia) ltac:(lia)).
        cbn [orb]. apply Nat.eqb_neq. lia.
      * apply IH; [lia|]. intros t Ht. destruct Ht as [<-|Ht].
        -- apply FOtm_avoid_var. lia.
        -- apply Hav. right. exact Ht.
  - rewrite FOBexC_ltv, FOfree_in_FOExists_neq by lia.
    rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
    + apply FOfree_in_ltv; [lia|]. rewrite FOin_tm_succ_eq.
      apply (Hav d (or_introl eq_refl)); lia.
    + rewrite FOBexC_ltv, FOfree_in_FOExists_neq by lia.
      rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
      * apply FOfree_in_ltv; [lia|]. rewrite FOin_tm_succ_eq.
        apply (Hav d (or_introl eq_refl)); lia.
      * rewrite !FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
        -- rewrite FOfree_in_FOcpairF. cbn [FOin_tm].
           rewrite (Hav d (or_introl eq_refl) w ltac:(lia) ltac:(lia)).
           rewrite (proj2 (Nat.eqb_neq B w) ltac:(lia)),
             (proj2 (Nat.eqb_neq (B + 2) w) ltac:(lia)). reflexivity.
        -- apply Bool.orb_false_iff. split.
           ++ apply IHa; [lia|]. intros t Ht. destruct Ht as [<-|Ht].
              ** apply FOtm_avoid_var. lia.
              ** apply Hav. right. exact Ht.
           ++ apply IHb; [lia|]. intros t Ht. destruct Ht as [<-|Ht].
              ** apply FOtm_avoid_var. lia.
              ** apply Hav. right. exact Ht.
Qed.

Ltac free_fm ::=
  lazymatch goal with
  | |- FOfree_in _ (FOPRu _ _ _) = false => apply FOfree_in_PRu; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOTBLEX3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_TBLEX3_any; [nat_fast | avoid_tms]
  | |- FOfree_in ?w (FOBexC ?v _ _) = false =>
      first [ constr_eq w v; apply FOfree_in_FOBexC_self
            | rewrite FOBexC_ltv; free_fm ]
  | |- FOfree_in _ (FOJUSTCK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOJUSTCK_free
  | |- FOfree_in _ (FOGUARDC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOGUARDC_free
  | |- FOfree_in _ (FONUMR _ _) = false => unfold FONUMR; free_fm
  | |- FOfree_in _ (FOTBLEX _ _ _ _ _) = false =>
      apply FOfree_in_TBLEX_any; [nat_fast | avoid_tms]
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

(** ** Instantiation inside the provability predicate.

    From the provability of the code [d0] of [forall x th] (with slot
    map [rho] over [env]) follows the provability of the code [c] of
    [th] with [x] turned into a new slot holding the numeral code [m]:
    a one-line universal-elimination derivation of [d0 -> c], whose
    substitution, capture and guard rows are built by the row
    recursions, followed by internal modus ponens.  The names [N],
    [N + 1], [N + 2] hold the pairing codes of the implication and the
    payload. *)

Lemma FOPrH_inst_code : forall n G cores u0 x th rho env m wm B0 d0 B1 c N,
  SlotCtx n env G ->
  (forall z i, rho z = Some i -> i < length env) ->
  FOPrH n G (FONUMR wm m) ->
  FOPrH n G (FOPATF B0 env (cpat_f rho (FOForall x th)) d0) ->
  FOPrH n G (FOPATF B1 (env ++ [m]) (cpat_f (rho_sub (Some x) (length env) rho) th) c) ->
  FOPrH n G (FOPRu cores u0 d0) ->
  FOctx_avoid G 0 1000 ->
  1000 <= N -> FOctx_avoid G N (N + 3) ->
  N + 3 <= B0 ->
  B0 + 2 * cpat_span (cpat_f rho (FOForall x th)) <= B1 ->
  FOctx_avoid G B0 (B0 + 2 * cpat_span (cpat_f rho (FOForall x th))) ->
  FOctx_avoid G B1 (B1 + 2 * cpat_span (cpat_f (rho_sub (Some x) (length env) rho) th)) ->
  FOtms_avoid (d0 :: c :: m :: env) 0 1000 ->
  FOtms_avoid (d0 :: c :: m :: env) N (N + 3) ->
  FOtms_avoid (d0 :: c :: m :: env) B0 (B0 + 2 * cpat_span (cpat_f rho (FOForall x th))) ->
  FOtms_avoid (d0 :: c :: m :: env) B1
    (B1 + 2 * cpat_span (cpat_f (rho_sub (Some x) (length env) rho) th)) ->
  FOPrH n G (FOPRu cores u0 c).
Proof.
  intros n G cores u0 x th rho env m wm B0 d0 B1 c N HS Hrho Hm Hd0 Hc Hpr HG0 HN HGN HNB
    HB01 HGB0 HGB1 Hlo HavN Hav0 Hav1.
  assert (Hsp : cpat_span (cpat_f rho (FOForall x th))
                = 8 + cpat_span (cpat_f (rho_hide x rho) th)).
  { cbn [cpat_f pAllP cpat_span cpat_pairs]. lia. }
  rewrite Hsp in HB01, HGB0, Hav0.
  (* the pairing codes of the implication [d0 -> c] *)
  apply (FOPrH_cpair_elim_hi n G d0 c N);
    [intros w ? ?; apply HG0; lia | avoid_tms | lia | apply HGN; lia | free_fm | avoid_tms |].
  apply (FOPrH_cpair_elim_hi n _ (FOnumeral 2) (FOVar N) (N + 1));
    [ctx_list | avoid_tms | lia | free_ctx | free_fm | avoid_tms |].
  lazymatch goal with |- FOPrH _ ?G2 _ =>
    assert (Hq : FOPrH n G2 (FOcpairF d0 c (FOVar N))) by wk_in;
    assert (Hd : FOPrH n G2 (FOcpairF (FOnumeral 2) (FOVar N) (FOVar (N + 1))))
      by apply FOPrH_last;
    assert (HS2 : SlotCtx n env G2) by (apply SlotCtx_ext; [apply SlotCtx_ext;
                                          [exact HS | ctx_list] | ctx_list]);
    assert (Hm2 : FOPrH n G2 (FONUMR wm m)) by wk Hm;
    assert (Hd02 : FOPrH n G2 (FOPATF B0 env (cpat_f rho (FOForall x th)) d0)) by wk Hd0;
    assert (Hc2 : FOPrH n G2 (FOPATF B1 (env ++ [m])
                               (cpat_f (rho_sub (Some x) (length env) rho) th) c)) by wk Hc;
    assert (Hpr2 : FOPrH n G2 (FOPRu cores u0 d0)) by wk Hpr;
    assert (HG02 : FOctx_avoid G2 0 1000) by ctx_list;
    assert (HGB02 : FOctx_avoid G2 B0
                      (B0 + 2 * (8 + cpat_span (cpat_f (rho_hide x rho) th)))) by ctx_list;
    assert (HGB12 : FOctx_avoid G2 B1
                      (B1 + 2 * cpat_span (cpat_f (rho_sub (Some x) (length env) rho) th)))
      by ctx_list;
    assert (HGN2 : FOctx_avoid G2 (N + 2) (N + 3)) by ctx_list
  end.
  destruct (FOPrH_cpair_le_cf n _ d0 c (FOVar N) ltac:(avoid_tms) Hq) as [Ld0q Lcq].
  destruct (FOPrH_cpair_le_cf n _ (FOnumeral 2) (FOVar N) (FOVar (N + 1)) ltac:(avoid_tms) Hd)
    as [_ Lqd].
  pose proof (FOPrH_le_trans n _ d0 (FOVar N) (FOVar (N + 1)) Ld0q Lqd ltac:(avoid_tms)) as Ld0d.
  pose proof (FOPrH_le_trans n _ c (FOVar N) (FOVar (N + 1)) Lcq Lqd ltac:(avoid_tms)) as Lcd.
  pose proof (FOPrH_le_succ_of_le n _ d0 (FOVar (N + 1)) Ld0d ltac:(avoid_tms)) as Sd0.
  pose proof (FOPrH_le_succ_of_le n _ c (FOVar (N + 1)) Lcd ltac:(avoid_tms)) as Sc.
  (* guard rows of the implication code *)
  pose proof (FOPrH_guard_rows n _ (FOForall x th) rho env B0 d0 (FOSucc (FOVar (N + 1)))
                HS2 Hrho Hd02 Sd0 ltac:(lia) ltac:(rewrite Hsp; exact HGB02)
                ltac:(rewrite Hsp; avoid_tms) ltac:(avoid_tms)) as R0.
  pose proof (SlotCtx_snoc n env _ m wm HS2 Hm2) as HS2'.
  assert (Hrc : forall z i, rho_sub (Some x) (length env) rho z = Some i ->
                  i < length (env ++ [m])).
  { intros z i Hz. unfold rho_sub in Hz. rewrite length_app. cbn [length].
    destruct (Nat.eqb z x); [injection Hz as <-; lia | pose proof (Hrho z i Hz); lia]. }
  pose proof (FOPrH_guard_rows n _ th (rho_sub (Some x) (length env) rho) (env ++ [m]) B1 c
                (FOSucc (FOVar (N + 1))) HS2' Hrc Hc2 Sc ltac:(lia) HGB12 ltac:(avoid_tms)
                ltac:(avoid_tms)) as Rc.
  pose proof (FOPrH_N3_impl n _ (FOSucc (FOVar (N + 1))) FOZero (FOVar (N + 1)) (FOVar (N + 1))
                (FOVar N) d0 c d0 c (FOVar N) ltac:(intros w ? ?; apply HG02; lia)
                ltac:(avoid_tms) R0 Rc Hd Hq Hq Hd) as Rd.
  pose proof (FOPrH_guard_code n _ th (rho_sub (Some x) (length env) rho) (env ++ [m]) B1 c
                HS2' Hrc Hc2 ltac:(lia) HGB12 ltac:(avoid_tms) ltac:(avoid_tms)) as Gc.
  (* the body of the universal *)
  apply (FOPrH_patf_quant_elim n _ B0 env 3 x (cpat_f (rho_hide x rho) th) d0 _ Hd02 ltac:(lia));
    [cbn [cpat_span cpat_pairs]; intros w ? ?; apply HGB02; lia
    | intros w ? ?; cbn [cpat_span cpat_pairs] in *; free_fm
    | cbn [cpat_span cpat_pairs]; avoid_tms |].
  lazymatch goal with |- FOPrH _ ?G3 _ =>
    assert (Hk0 : FOPrH n G3 (FOcpairF (FOnumeral 3) (FOVar (B0 + 2)) d0)) by wk_in;
    assert (Hx0 : FOPrH n G3 (FOcpairF (FOnumeral x) (FOVar (B0 + 6)) (FOVar (B0 + 2))))
      by wk_in;
    assert (Hb0 : FOPrH n G3 (FOPATF (B0 + 8) env (cpat_f (rho_hide x rho) th)
                                (FOVar (B0 + 6)))) by wk_in;
    assert (HS3 : SlotCtx n env G3) by (apply SlotCtx_ext; [exact HS2 | ctx_list]);
    assert (Hm3 : FOPrH n G3 (FONUMR wm m)) by wk Hm2;
    assert (Hc3 : FOPrH n G3 (FOPATF B1 (env ++ [m])
                               (cpat_f (rho_sub (Some x) (length env) (rho_hide x rho)) th) c))
      by (rewrite (cpat_f_ext th _ _ (rho_sub_hide_self x (length env) rho)); wk Hc2);
    assert (Rd3 : FOPrH n G3 (FOTBLEX (FOnumeral 3) (FOSucc (FOVar (N + 1))) FOZero
                                (FOVar (N + 1)) (FOVar (N + 1)))) by wk Rd;
    assert (Gc3 : FOPrH n G3 (FOGUARDB c)) by wk Gc;
    assert (Hpr3 : FOPrH n G3 (FOPRu cores u0 d0)) by wk Hpr2;
    assert (Hq3 : FOPrH n G3 (FOcpairF d0 c (FOVar N))) by wk Hq;
    assert (Hd3 : FOPrH n G3 (FOcpairF (FOnumeral 2) (FOVar N) (FOVar (N + 1)))) by wk Hd;
    assert (Ld0d3 : FOPrH n G3 (FOle d0 (FOVar (N + 1)))) by wk Ld0d;
    assert (Lcd3 : FOPrH n G3 (FOle c (FOVar (N + 1)))) by wk Lcd;
    assert (HG03 : FOctx_avoid G3 0 1000) by ctx_list;
    assert (HGB13 : FOctx_avoid G3 B1
                      (B1 + 2 * cpat_span (cpat_f (rho_sub (Some x) (length env) rho) th)))
      by ctx_list;
    assert (HGb3 : FOctx_avoid G3 (B0 + 8) (B0 + 8 + cpat_span (cpat_f (rho_hide x rho) th)))
      by ctx_list;
    assert (HGN3 : FOctx_avoid G3 (N + 2) (N + 3)) by ctx_list
  end.
  destruct (FOPrH_cpair_le_cf n _ (FOnumeral 3) (FOVar (B0 + 2)) d0 ltac:(avoid_tms) Hk0)
    as [_ Lp0].
  destruct (FOPrH_cpair_le_cf n _ (FOnumeral x) (FOVar (B0 + 6)) (FOVar (B0 + 2))
              ltac:(avoid_tms) Hx0) as [_ Lap].
  pose proof (FOPrH_le_trans n _ (FOVar (B0 + 6)) (FOVar (B0 + 2)) d0 Lap Lp0 ltac:(avoid_tms))
    as La0.
  pose proof (FOPrH_le_succ_of_le n _ (FOVar (B0 + 6)) d0 La0 ltac:(avoid_tms)) as Sa0.
  (* substitution and capture rows *)
  assert (HE : RowEnv (Some x) (FOnumeral x) (FOSucc d0) m env (env ++ [m]) (length env)).
  { split; [intros i Hi; apply app_nth1; exact Hi|].
    split; [rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity|].
    split; [reflexivity | avoid_tms]. }
  lazymatch goal with |- FOPrH _ ?G3 _ =>
    assert (HC : RowCtx n (Some x) (FOnumeral x) (FOSucc d0) env G3)
      by (split; [intros w ? ?; apply HG03; lia|]; split; [destruct HS3 as [_ Hs3]; exact Hs3|];
          intros G' y _ _ Hne; apply FOPrH_num_neq; cbn [ox_eq] in Hne;
          apply Nat.eqb_neq; exact Hne)
  end.
  assert (Hrho' : forall z i, rho_hide x rho z = Some i -> i < length env).
  { intros z i Hz. unfold rho_hide in Hz. destruct (Nat.eqb z x); [discriminate|].
    exact (Hrho z i Hz). }
  assert (Hrx : rho_hide x rho x = None) by (unfold rho_hide; rewrite Nat.eqb_refl; reflexivity).
  pose proof (FOPrH_rows_f n (Some x) (FOnumeral x) (FOSucc d0) m env (env ++ [m]) (length env)
                th _ (rho_hide x rho) (B0 + 8) B1 (FOVar (B0 + 6)) c HE HC Hrho' Hrx Hb0 Hc3 Sa0
                ltac:(lia) ltac:(lia)
                ltac:(left; rewrite (cpat_f_ext th _ _ (rho_sub_hide_self x (length env) rho))
                           in *; lia)
                HGb3
                ltac:(rewrite (cpat_f_ext th _ _ (rho_sub_hide_self x (length env) rho));
                      intros w ? ?; apply HGB13; lia)
                ltac:(avoid_tms)
                ltac:(rewrite (cpat_f_ext th _ _ (rho_sub_hide_self x (length env) rho));
                      avoid_tms)
                ltac:(avoid_tms)) as R3.
  pose proof (FOPrH_cap_f n x m th _ (rho_hide x rho) env (B0 + 8) (FOVar (B0 + 6)) HS3
                (ex_intro _ wm Hm3) Hrho' Hb0 ltac:(lia) HGb3 ltac:(avoid_tms)
                ltac:(avoid_tms)) as R4.
  pose proof (FOPrH_tblex_join3 n _ (FOnumeral 3) (FOSucc (FOVar (N + 1))) FOZero (FOVar (N + 1))
                (FOVar (N + 1)) (FOnumeral 4) (FOnumeral x) m (FOVar (B0 + 6)) (FOnumeral 1)
                (FOnumeral 3) (FOnumeral x) m (FOVar (B0 + 6)) c
                ltac:(intros w ? ?; apply HG03; lia) ltac:(avoid_tms) Rd3 R4 R3) as H3.
  (* the payload and the one-line derivation *)
  apply (FOPrH_cpair_elim_hi n _ (FOnumeral x) m (N + 2));
    [ctx_list | avoid_tms | lia | apply HGN3; lia | free_fm | avoid_tms |].
  pose proof (FOPrH_le_trans n _ (FOVar (B0 + 6)) d0 (FOVar (N + 1)) La0 Ld0d3 ltac:(avoid_tms))
    as Lad.
  lazymatch goal with |- FOPrH _ ?G4 _ =>
    assert (Hpl : FOPrH n G4 (FOcpairF (FOnumeral x) m (FOVar (N + 2)))) by apply FOPrH_last;
    assert (HG04 : FOctx_avoid G4 0 1000) by ctx_list;
    pose proof (FOPrH_patf_allelim n G4 (FOnumeral x) (FOVar (B0 + 6)) c (FOVar (N + 1))
                  (FOVar N) d0 (FOVar (B0 + 2)) (FOPrH_weak_app _ _ _ _ Hd3)
                  (FOPrH_weak_app _ _ _ _ Hq3) (FOPrH_weak_app _ _ _ _ Hk0)
                  (FOPrH_weak_app _ _ _ _ Hx0) ltac:(avoid_tms) ltac:(avoid_tms)) as HP44;
    pose proof (FOPrH_subst_line n G4 cores (FOVar (N + 1)) cpatAllElim 2 (FOVar (N + 2))
                  (FOVar (N + 1)) (FOnumeral x) m (FOVar (B0 + 6)) c
                  (or_introl (conj eq_refl eq_refl)) ltac:(intros w ? ?; apply HG04; lia)
                  ltac:(avoid_tms) (FOPrH_weak_app _ _ _ _ H3) Hpl
                  (FOPrH_weak_app _ _ _ _ Lad) (FOPrH_weak_app _ _ _ _ Lcd3) HP44) as Hline;
    pose proof (FOPrH_fix0 n G4 u0 _ ltac:(apply HG04; lia) Hline) as Hdu;
    pose proof (FOPrH_patf_impl01 n G4 (FOVar (N + 1)) d0 c (FOVar N)
                  (FOPrH_weak_app _ _ _ _ Hd3) (FOPrH_weak_app _ _ _ _ Hq3)
                  ltac:(avoid_tms) ltac:(avoid_tms)) as HP52;
    exact (FOPrH_mpu n G4 cores u0 (FOVar (N + 1)) d0 c ltac:(intros w ? ?; apply HG04; lia)
             HP52 (FOPrH_weak_app _ _ _ _ Gc3) ltac:(avoid_tms) Hdu
             (FOPrH_weak_app _ _ _ _ Hpr3))
  end.
Qed.
