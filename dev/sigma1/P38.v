From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37.
Open Scope fo_scope.

(** ** Free variables of the dispatch cases. *)

Lemma FODISPCASES_free : forall w ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r,
  FOfree_in w (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true \/ FOin_tm w tg = true
  \/ FOin_tm w a1 = true \/ FOin_tm w a2 = true \/ FOin_tm w a3 = true
  \/ FOin_tm w r = true \/ w < 2.
Proof.
  intros w ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r H.
  unfold FODISPCASES, FOSTEP0, FOSTEP1, FOSTEP2, FOSTEP3, FOSTEP4, FOSTEP5,
    FOSTEP_bin, FOSTEP_quant0, FOSTEP_substbin, FOSTEP_substquant, FOSTEP_subokbin,
    FOSTEP_subokquant in H.
  ffree_walk; ffin.
Qed.

Lemma FOSTEP5_free : forall w B ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 r,
  FOfree_in w (FOSTEP5 B ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 r) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true \/ FOin_tm w a1 = true
  \/ FOin_tm w r = true \/ w < 2.
Proof.
  intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 r H.
  unfold FOSTEP5 in H. ffree_walk; ffin.
Qed.

Ltac free_fm ::=
  lazymatch goal with
  | |- FOfree_in _ (FODISPCASES _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FODISPCASES_free
  | |- FOfree_in _ (FOSTEP5 _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false => free_by FOSTEP5_free
  | |- FOfree_in _ (FOTBLVALID _ _ _ _ _ _ _ _ _ _ _ _) = false => free_by FOTBLVALID_free
  | |- FOfree_in _ (FOlookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOlookup_free
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

(** ** The dispatch cases at tag [5]. *)

Ltac disp_kill k :=
  apply FOPrH_efq;
  exact (FOPrH_mp _ _ _ _ (FOPrH_num_neq _ _ 5 k ltac:(lia))
           (FOPrH_and_l _ _ _ _ (FOPrH_last _ _ _))).

Lemma FOPrH_disp_tag5 : forall n G ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 a3 r,
  FOPrH n G (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 5) a1 a2 a3 r) ->
  FOPrH n G (FOSTEP5 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 r).
Proof.
  intros n G ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 a3 r H. unfold FODISPCASES in H.
  refine (FOPrH_or_elim _ _ _ _ _ H _ _); [disp_kill 0|].
  refine (FOPrH_or_elim _ _ _ _ _ (FOPrH_last _ _ _) _ _); [disp_kill 1|].
  refine (FOPrH_or_elim _ _ _ _ _ (FOPrH_last _ _ _) _ _); [disp_kill 2|].
  refine (FOPrH_or_elim _ _ _ _ _ (FOPrH_last _ _ _) _ _); [disp_kill 3|].
  refine (FOPrH_or_elim _ _ _ _ _ (FOPrH_last _ _ _) _ _); [disp_kill 4|].
  refine (FOPrH_weaken n _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_last _ _ _))).
  intros X HX. exact HX.
Qed.

(** ** A row rewritten along an equation of its second field. *)

Lemma FOPrH_tblex_cong_a1 : forall n G tg a1 a2 a3 r a1',
  FOPrH n G (FOTBLEX tg a1 a2 a3 r) -> FOPrH n G (FOEq a1 a1') ->
  FOtms_avoid [tg; a1; a2; a3; r; a1'] 2 1000 ->
  FOPrH n G (FOTBLEX tg a1' a2 a3 r).
Proof.
  intros n G tg a1 a2 a3 r a1' H E Hav.
  assert (K : forall t, FOtm_avoid t 2 1000 ->
             FOsubst_f 999 t (FOTBLEX tg (FOVar 999) a2 a3 r) = FOTBLEX tg t a2 a3 r).
  { intros t Ht. rewrite FOsubst_f_TBLEX by lia. rewrite FOsubst_t_var_eq'.
    rewrite !(FOsubst_t_not_in _ 999 t) by fr_tm. reflexivity. }
  assert (V1 : FOtm_avoid a1 2 1000) by avoid_tm.
  assert (V1' : FOtm_avoid a1' 2 1000) by avoid_tm.
  pose proof (FOPrH_leibniz n G 999 a1 a1' (FOTBLEX tg (FOVar 999) a2 a3 r)
                ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm])
                ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm]) E) as L.
  rewrite (K a1 V1), (K a1' V1') in L. exact (L H).
Qed.

(** ** Inversion of the numeral rows. *)

Lemma FOPrH_num5_inv0 : forall n G m,
  FOctx_avoid G 2 1000 -> FOtms_avoid [m] 2 1000 ->
  FOPrH n G (FOTBLEX (FOnumeral 5) FOZero FOZero FOZero m) ->
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero m).
Proof.
  intros n G m HG Hm H.
  apply (FOPrH_tblex_inv n G (FOnumeral 5) FOZero FOZero FOZero m
           (FOcpairF (FOnumeral 1) FOZero m) HG ltac:(avoid_tms)
           ltac:(intros w ? ?; free_fm) H).
  lazymatch goal with |- FOPrH _ (?Gx ++ [?V; ?D]) _ =>
    pose proof (FOPrH_disp_tag5 n (Gx ++ [V; D]) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  (FOPrH_assum n (Gx ++ [V; D]) D ltac:(apply in_or_app; right; cbn [In]; right; left; reflexivity)))
      as S5
  end.
  unfold FOSTEP5 in S5.
  refine (FOPrH_or_elim _ _ _ _ _ S5 _ _).
  - exact (FOPrH_and_r _ _ _ _ (FOPrH_last _ _ _)).
  - apply FOPrH_efq.
    lazymatch goal with |- FOPrH _ (?Gx ++ [?Y]) _ => pose proof (FOPrH_last n Gx Y) as K end.
    refine (FOPrH_ex_elim n _ 50 _ FOFalseF _ eq_refl K _); [free_ctx|].
    lazymatch goal with |- FOPrH _ (?Gx ++ [?Y]) _ =>
      pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_last n Gx Y))) as E end.
    exact (FOPrH_Q_succ_nonzero n _ (FOVar 50) (FOPrH_eq_sym _ _ _ _ E)).
Qed.

Lemma FOPrH_num5_invS : forall n G a m w C,
  FOctx_avoid G 2 1000 -> FOtms_avoid [a; m] 2 1000 -> 1000 <= w ->
  FOfree_ctx w G -> FOfree_in w C = false -> FOtms_avoid [a; m] w (S w) ->
  (forall v, 2 <= v -> v < 1000 -> FOfree_in v C = false) ->
  FOPrH n G (FOTBLEX (FOnumeral 5) (FOSucc a) FOZero FOZero m) ->
  FOPrH n (G ++ [FOcpairF (FOnumeral 2) (FOVar w) m;
                 FOTBLEX (FOnumeral 5) a FOZero FOZero (FOVar w)]) C ->
  FOPrH n G C.
Proof.
  intros n G a m w C HG Hav Hw HGw HCw Havw HCv H H0.
  apply (FOPrH_tblex_inv n G (FOnumeral 5) (FOSucc a) FOZero FOZero m C HG ltac:(avoid_tms)
           HCv H).
  lazymatch goal with |- FOPrH _ (?Gx ++ [?V; ?D]) _ =>
    pose proof (FOPrH_disp_tag5 n (Gx ++ [V; D]) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  (FOPrH_assum n (Gx ++ [V; D]) D ltac:(apply in_or_app; right; cbn [In]; right; left; reflexivity)))
      as S5;
    pose proof (FOPrH_assum n (Gx ++ [V; D]) V ltac:(apply in_or_app; right; cbn [In]; left; reflexivity)) as KV
  end.
  unfold FOSTEP5 in S5.
  refine (FOPrH_or_elim _ _ _ _ _ S5 _ _).
  - apply FOPrH_efq.
    exact (FOPrH_Q_succ_nonzero n _ a (FOPrH_and_l _ _ _ _ (FOPrH_last _ _ _))).
  - lazymatch goal with |- FOPrH _ (?Gx ++ [?Y]) _ => pose proof (FOPrH_last n Gx Y) as K end.
    refine (FOPrH_ex_elim n _ 50 _ C _ _ K _); [free_ctx | apply HCv; lia |].
    lazymatch goal with |- FOPrH _ (?Gx ++ [?Y]) _ =>
      pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_last n Gx Y))) as E;
      pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_last n Gx Y))) as K2
    end.
    pose proof (FOPrH_Q_succ_inj n _ a (FOVar 50) E) as Ea.
    refine (FOPrH_exe_clean n _ 52 w _
              (FOAnd (FOlookup 54 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                        (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                        (FOnumeral 5) (FOVar 50) FOZero FOZero (FOVar w))
                     (FOcpairF (FOnumeral 2) (FOVar w) m))
              C K2 _ _ _ _ _ _);
      [free_ctx | exact HCw | free_fm
      | apply FOsubst_ok_and;
        [ apply FOsubst_ok_ex; [fr_tm | apply FOsubst_ok_eq]
        | apply FOsubst_ok_and; [apply FOsubst_ok_lookup; avoid_tm | apply FOsubst_ok_cpairF] ]
      | |].
    { unfold FOltv. autorewrite with fosubst. rewrite ?FOsubst_t_var_eq'.
      subst_avoid_h Hav.
      refine (FOPrH_and_r _ _ _ _ _). apply FOPrH_assum. left. reflexivity. }
    lazymatch goal with |- FOPrH _ (?Gx ++ [?Y]) _ =>
      pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n Gx Y)) as L54;
      pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n Gx Y)) as Cw;
      assert (KV3 : FOPrH n (Gx ++ [Y]) (FOTBLVALID 18 (FOVar 122) (FOVar 123) (FOVar 124)
                      (FOVar 125) (FOVar 126) (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130)
                      (FOVar 131) (FOVar 132))) by wk KV;
      assert (Ea3 : FOPrH n (Gx ++ [Y]) (FOEq a (FOVar 50))) by wk Ea
    end.
    pose proof (FOPrH_lookup_rebase n _ 54 28 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L54 ltac:(lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(avoid_tms) ltac:(avoid_tms))
      as L28.
    assert (Va : FOtm_avoid a 28 50) by avoid_tm.
    pose proof (FOPrH_leibniz n _ 27 (FOVar 50) a
                  (FOlookup 28 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                     (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                     (FOnumeral 5) (FOVar 27) FOZero FOZero (FOVar w))
                  ltac:(apply FOsubst_ok_lookup; avoid_tm) ltac:(apply FOsubst_ok_lookup; exact Va)
                  (FOPrH_eq_sym _ _ _ _ Ea3)) as La.
    rewrite !FOsubst_f_lookup in La by lia.
    rewrite !FOsubst_t_var_eq', !FOsubst_t_var_ne, !FOsubst_t_numeral, !FOsubst_t_zero in La
      by lia.
    pose proof (FOPrH_tblex_intro n _ (FOtabv 122) (FOnumeral 5) a FOZero FOZero
                  (FOVar w) KV3 (La L28)
                  ltac:(unfold FOtabv, FOtab_terms;
                        cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen Nat.add app];
                        avoid_tms)) as Ta.
    refine (FOPrH_cut _ _ _ C Cw _).
    refine (FOPrH_cut _ _ _ C (FOPrH_weak_app _ _ _ _ Ta) _).
    refine (FOPrH_weaken n _ _ C _ H0).
    intros Y HY. apply in_app_or in HY. destruct HY as [HY|[<-|[<-|[]]]].
    + repeat (apply in_or_app; left). exact HY.
    + apply in_or_app. left. apply in_or_app. right. left. reflexivity.
    + apply in_or_app. right. left. reflexivity.
Qed.
