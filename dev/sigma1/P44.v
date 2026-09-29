From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41
  P42 P43.
Open Scope fo_scope.

(** ** Side conditions from bounds above a level. *)

Definition opT (f : bool) (a b : FOTerm) : FOTerm := if f then FOPlus a b else FOMult a b.

Lemma FOsubst_t_opT : forall f x s a b,
  FOsubst_t x s (opT f a b) = opT f (FOsubst_t x s a) (FOsubst_t x s b).
Proof. intros [|]; reflexivity. Qed.

Lemma FOtm_avoid_opT : forall f a b lo hi, FOtm_avoid a lo hi -> FOtm_avoid b lo hi ->
  FOtm_avoid (opT f a b) lo hi.
Proof. intros [|] a b lo hi Ha Hb; [apply FOtm_avoid_plus | apply FOtm_avoid_mult]; assumption. Qed.

Lemma FOin_tm_opT : forall f w a b, FOin_tm w a = false -> FOin_tm w b = false ->
  FOin_tm w (opT f a b) = false.
Proof. intros [|] w a b Ha Hb; cbn [opT FOin_tm]; rewrite Ha, Hb; reflexivity. Qed.

Ltac avoid_tm ::=
  lazymatch goal with
  | |- FOtm_avoid (opT _ _ _) _ _ => apply FOtm_avoid_opT; avoid_tm
  | |- FOtm_avoid (nth _ _ _) _ _ => apply FOtm_avoid_nth; avoid_tms
  | |- FOtm_avoid (FOnumeral _) _ _ => apply FOtm_avoid_numeral
  | |- FOtm_avoid FOZero _ _ => apply FOtm_avoid_zero
  | |- FOtm_avoid (FOSucc _) _ _ => apply FOtm_avoid_succ; avoid_tm
  | |- FOtm_avoid (FOPlus _ _) _ _ => apply FOtm_avoid_plus; avoid_tm
  | |- FOtm_avoid (FOMult _ _) _ _ => apply FOtm_avoid_mult; avoid_tm
  | |- FOtm_avoid (FOVar _) _ _ =>
      first [ apply FOtm_avoid_var_b; vm_compute; reflexivity
            | apply FOtm_avoid_var; lia ]
  | |- FOtm_avoid ?t ?lo ?hi =>
      first
        [ match goal with
          | H : FOtms_avoid ?L ?lo' ?hi' |- _ =>
              apply (FOtm_avoid_sub t lo' hi' lo hi); [apply H; in_list | nat_fast | nat_fast]
          end
        | match goal with
          | H : forall s, In s ?L -> forall w, ?V <= w -> FOin_tm w s = false |- _ =>
              let w := fresh "w" in let H1 := fresh "Hw" in let H2 := fresh "Hw" in
              intros w H1 H2; apply (H t ltac:(in_list) w); nat_fast
          end ]
  end.

Ltac fr_tm ::=
  lazymatch goal with
  | |- FOin_tm _ (opT _ _ _) = false => apply FOin_tm_opT; fr_tm
  | |- FOin_tm ?w (nth _ _ _) = false =>
      apply (FOtm_avoid_nth _ _ w (S w)); [avoid_tms | lia | lia]
  | |- FOin_tm _ (FOVar _) = false => apply FOin_tm_var_ne; nat_fast
  | |- FOin_tm _ (FOnumeral _) = false => apply FOin_tm_numeral
  | |- FOin_tm _ FOZero = false => reflexivity
  | |- FOin_tm _ (FOSucc _) = false => rewrite FOin_tm_succ_eq; fr_tm
  | |- FOin_tm _ (FOPlus _ _) = false =>
      rewrite FOin_tm_plus_eq; apply Bool.orb_false_iff; split; fr_tm
  | |- FOin_tm _ (FOMult _ _) = false =>
      rewrite FOin_tm_mult_eq; apply Bool.orb_false_iff; split; fr_tm
  | |- FOin_tm ?w ?t = false =>
      first
        [ match goal with H : FOtms_avoid ?L ?lo ?hi |- _ =>
            apply (H t ltac:(in_list) w); nat_fast end
        | match goal with
          | H : forall s, In s ?L -> forall w, ?V <= w -> FOin_tm w s = false |- _ =>
              apply (H t ltac:(in_list) w); nat_fast
          end ]
  end.

Ltac free_ctx ::=
  lazymatch goal with
  | |- FOfree_ctx _ (_ ++ _) => apply FOfree_ctx_app_inv; free_ctx
  | |- FOfree_ctx _ (_ :: _) => apply FOfree_ctx_cons; [free_fm | free_ctx]
  | |- FOfree_ctx _ [] => apply FOfree_ctx_nil
  | |- FOfree_ctx ?w ?G =>
      first [ assumption
            | match goal with HG : FOctx_avoid G ?lo ?hi |- _ => apply HG; nat_fast end
            | match goal with HG : forall w, ?V <= w -> FOfree_ctx w G |- _ =>
                apply HG; nat_fast end ]
  end.

(** ** Numeral codes along an equation of their numbers. *)

Lemma FOPrH_numr_cong1 : forall n G a b m,
  FOPrH n G (FONUMR a m) -> FOPrH n G (FOEq a b) ->
  FOtms_avoid [a; b; m] 2 50 -> FOtms_avoid [a; b; m] 802 805 -> FOtms_avoid [m] 999 1000 ->
  FOPrH n G (FONUMR b m).
Proof.
  intros n G a b m H E Hav Hav2 Hm.
  assert (K : forall t, FOtms_avoid [t] 2 50 -> FOtms_avoid [t] 802 805 ->
             FOsubst_f 999 t (FONUMR (FOVar 999) m) = FONUMR t m).
  { intros t Ht1 Ht2. rewrite FOsubst_f_NUMR by (lia || avoid_tms).
    rewrite FOsubst_t_var_eq', (FOsubst_t_not_in m 999 t) by fr_tm. reflexivity. }
  pose proof (FOPrH_leibniz n G 999 a b (FONUMR (FOVar 999) m)
                ltac:(apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms])
                ltac:(apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]) E) as L.
  rewrite (K a), (K b) in L by avoid_tms. exact (L H).
Qed.

(** ** Sums and products of numerals, inside the provability predicate.

    [PhiOp]: every numeral code [a] of [Nt] and code [b] of [x op Nt]
    give a provable instance of the pattern [P] over [m1; a; b]. *)

Definition PhiOp (cores : list nat) (u0 B0 a b : nat) (f : bool) (x m1 : FOTerm) (P : CPat)
    (Nt : FOTerm) : FOFormula :=
  FOForall a (FOForall b (FOImplF (FONUMR Nt (FOVar a))
    (FOImplF (FONUMR (opT f x Nt) (FOVar b)) (PRIf cores u0 B0 [m1; FOVar a; FOVar b] P)))).

Lemma PhiOp_subst : forall cores u0 B0 a b f x m1 P N s,
  N <> a -> N <> b -> 1000 <= N -> N < B0 -> FOtms_avoid [s] 802 805 ->
  FOin_tm N x = false -> FOin_tm N m1 = false ->
  FOsubst_f N s (PhiOp cores u0 B0 a b f x m1 P (FOVar N)) = PhiOp cores u0 B0 a b f x m1 P s.
Proof.
  intros cores u0 B0 a b f x m1 P N s Ha Hb HN HB Hs Hx Hm1. unfold PhiOp.
  rewrite (FOsubst_f_all_ne N s a) by lia. rewrite (FOsubst_f_all_ne N s b) by lia.
  rewrite !FOsubst_f_impl, !FOsubst_f_NUMR by (lia || avoid_tms).
  rewrite FOsubst_f_PRIf by lia. cbn [map].
  rewrite FOsubst_t_opT, FOsubst_t_var_eq', !FOsubst_t_var_ne by lia.
  rewrite (FOsubst_t_not_in x N s Hx), (FOsubst_t_not_in m1 N s Hm1). reflexivity.
Qed.

Lemma PhiOp_inst : forall n G cores u0 B0 a b f x m1 P Nt ta tb,
  FOPrH n G (PhiOp cores u0 B0 a b f x m1 P Nt) ->
  a <> b -> 1000 <= a -> 1000 <= b -> a < B0 -> b < B0 ->
  FOtms_avoid [Nt; x; m1] a (S a) -> FOtms_avoid [Nt; x; m1; ta] b (S b) ->
  FOtms_avoid [ta; tb] 0 1000 -> FOtms_avoid [ta; tb] B0 (B0 + cpat_span P) ->
  FOPrH n G (FOImplF (FONUMR Nt ta)
    (FOImplF (FONUMR (opT f x Nt) tb) (PRIf cores u0 B0 [m1; ta; tb] P))).
Proof.
  intros n G cores u0 B0 a b f x m1 P Nt ta tb H Hab Ha Hb HaB HbB Hava Havb Hav0 HavB.
  unfold PhiOp in H.
  apply (FOPrH_inst n G a ta) in H;
    [| apply FOsubst_ok_all; [fr_tm|]; apply FOsubst_ok_impl;
       [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_PRIf; [lia | fr_tm | avoid_tm]].
  rewrite (FOsubst_f_all_ne a ta b) in H by lia.
  rewrite !FOsubst_f_impl, !FOsubst_f_NUMR in H by (lia || avoid_tms).
  rewrite FOsubst_f_PRIf in H by lia. cbn [map] in H.
  rewrite FOsubst_t_opT, FOsubst_t_var_eq', FOsubst_t_var_ne in H by lia.
  rewrite (FOsubst_t_not_in Nt a ta), (FOsubst_t_not_in x a ta), (FOsubst_t_not_in m1 a ta)
    in H by fr_tm.
  apply (FOPrH_inst n G b tb) in H;
    [| apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_PRIf; [lia | fr_tm | avoid_tm]].
  rewrite !FOsubst_f_impl, !FOsubst_f_NUMR in H by (lia || avoid_tms).
  rewrite FOsubst_f_PRIf in H by lia. cbn [map] in H.
  rewrite FOsubst_t_opT, FOsubst_t_var_eq' in H.
  rewrite (FOsubst_t_not_in Nt b tb), (FOsubst_t_not_in x b tb), (FOsubst_t_not_in m1 b tb),
    (FOsubst_t_not_in ta b tb) in H by fr_tm.
  exact H.
Qed.

Ltac free_fm ::=
  lazymatch goal with
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

(** ** Slot maps and small environments. *)

Definition rhoN (k : nat) : nat -> option nat := fun z => if Nat.ltb z k then Some z else None.

Lemma rhoN_range : forall k z i, rhoN k z = Some i -> i < k.
Proof.
  intros k z i H. unfold rhoN in H.
  destruct (Nat.ltb_spec z k); [injection H as <-; lia | discriminate].
Qed.

Lemma fv_small : forall A z, FOfree_in z A = true -> z <= FOvars_max A.
Proof.
  intros A z H. destruct (Nat.le_gt_cases z (FOvars_max A)) as [Hle|Hgt]; [exact Hle|].
  rewrite (FOfree_in_above A z Hgt) in H. discriminate.
Qed.

Lemma rhoN_fv : forall k A, FOvars_max A < k ->
  forall z, FOfree_in z A = true -> exists j, rhoN k z = Some j /\ j < k.
Proof.
  intros k A HA z Hz. pose proof (fv_small A z Hz). exists z. unfold rhoN.
  destruct (Nat.ltb_spec z k); [split; [reflexivity | lia] | lia].
Qed.

Lemma EnvOK3 : forall n V G a b c wa wb wc, FOctx_avoid G 2 1000 ->
  FOPrH n G (FONUMR wa a) -> FOPrH n G (FONUMR wb b) -> FOPrH n G (FONUMR wc c) ->
  FOtms_avoid [a; b; c] 0 1000 -> 1000 <= V ->
  (forall t, In t [a; b; c] -> forall w, V <= w -> FOin_tm w t = false) ->
  EnvOK n V G [a; b; c].
Proof.
  intros n V G a b c wa wb wc HG Ha Hb Hc H0 HV Hab.
  split; [split; [exact HG|] | split; [exact H0 | split; [exact HV | exact Hab]]].
  intros [|[|[|i]]] Hi; cbn [nth];
    [exists wa; exact Ha | exists wb; exact Hb | exists wc; exact Hc | cbn in Hi; lia].
Qed.

Lemma EnvOK4 : forall n V G a b c d wa wb wc wd, FOctx_avoid G 2 1000 ->
  FOPrH n G (FONUMR wa a) -> FOPrH n G (FONUMR wb b) -> FOPrH n G (FONUMR wc c) ->
  FOPrH n G (FONUMR wd d) ->
  FOtms_avoid [a; b; c; d] 0 1000 -> 1000 <= V ->
  (forall t, In t [a; b; c; d] -> forall w, V <= w -> FOin_tm w t = false) ->
  EnvOK n V G [a; b; c; d].
Proof.
  intros n V G a b c d wa wb wc wd HG Ha Hb Hc Hd H0 HV Hab.
  split; [split; [exact HG|] | split; [exact H0 | split; [exact HV | exact Hab]]].
  intros [|[|[|[|i]]]] Hi; cbn [nth];
    [exists wa; exact Ha | exists wb; exact Hb | exists wc; exact Hc | exists wd; exact Hd
    | cbn in Hi; lia].
Qed.

Ltac cprel_tac :=
  repeat first
    [ apply cpr_lit
    | apply cpr_slot; cbn [nth]; first [apply FOPrH_refl | eassumption]
    | apply cpr_zero_r; cbn [nth]; eassumption
    | apply cpr_zero_l; cbn [nth]; eassumption
    | apply cpr_succ_r; cbn [nth]; eassumption
    | apply cpr_succ_l; cbn [nth]; eassumption
    | apply cpr_pair ].

Ltac above_tac :=
  let t := fresh "t" in let Ht := fresh "Ht" in let w0 := fresh "w0" in
  let Hw0 := fresh "Hw0" in
  intros t Ht w0 Hw0; cbn [In app] in Ht;
  repeat match type of Ht with
         | _ \/ _ => destruct Ht as [<-|Ht]; [fr_tm|]
         | False => destruct Ht
         end.

(** ** The induction on the second summand or factor. *)

Lemma PRI_opind : forall n k V G f x m1 y m2 m3 P,
  2000 <= V -> FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  FOtms_avoid [x; m1; y; m2; m3] 0 1100 ->
  (forall t, In t [x; m1; y; m2; m3] -> forall w, V <= w -> FOin_tm w t = false) ->
  FOPrH n G (FONUMR y m2) -> FOPrH n G (FONUMR (opT f x y) m3) ->
  PRI n (FOPrCores k) (FOu0 k) (V + 3)
    ((G ++ [FONUMR FOZero (FOVar (V + 1))]) ++ [FONUMR (opT f x FOZero) (FOVar (V + 2))])
    P [m1; FOVar (V + 1); FOVar (V + 2)] ->
  PRI n (FOPrCores k) (FOu0 k) (V + 3)
    (((G ++ [PhiOp (FOPrCores k) (FOu0 k) (V + 3) (V + 1) (V + 2) f x m1 P (FOVar V)])
       ++ [FONUMR (FOSucc (FOVar V)) (FOVar (V + 1))])
       ++ [FONUMR (opT f x (FOSucc (FOVar V))) (FOVar (V + 2))])
    P [m1; FOVar (V + 1); FOVar (V + 2)] ->
  PRI n (FOPrCores k) (FOu0 k) V G P [m1; m2; m3].
Proof.
  intros n k V G f x m1 y m2 m3 P HV HG0 HGV Hav0 Havv Hy Hxy Hbase Hstep.
  assert (HI : FOPrH n G (FOForall V
            (PhiOp (FOPrCores k) (FOu0 k) (V + 3) (V + 1) (V + 2) f x m1 P (FOVar V)))).
  { apply FOPrH_ind; [apply HGV; lia | |].
    - rewrite PhiOp_subst by first [lia | avoid_tms | fr_tm].
      unfold PhiOp.
      apply FOPrH_all_intro; [apply HGV; lia|]. apply FOPrH_all_intro; [apply HGV; lia|].
      apply FOPrH_intro. apply FOPrH_intro.
      apply (PRI_to_PRIf n _ _ (V + 3) _ [m1; FOVar (V + 1); FOVar (V + 2)] P (V + 3) Hbase);
        [lia | lia | intros w ? ?; free_ctx | intros w ?; free_ctx | avoid_tms | above_tac].
    - rewrite PhiOp_subst by first [lia | avoid_tms | fr_tm].
      unfold PhiOp at 2.
      apply FOPrH_all_intro; [free_ctx|].
      apply FOPrH_all_intro; [free_ctx|].
      apply FOPrH_intro. apply FOPrH_intro.
      apply (PRI_to_PRIf n _ _ (V + 3) _ [m1; FOVar (V + 1); FOVar (V + 2)] P (V + 3) Hstep);
        [lia | lia | intros w ? ?; free_ctx | intros w ?; free_ctx | avoid_tms | above_tac]. }
  apply (FOPrH_inst n G V y) in HI;
    [| unfold PhiOp; apply FOsubst_ok_all; [fr_tm|]; apply FOsubst_ok_all; [fr_tm|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_PRIf; [lia | fr_tm | avoid_tm]].
  rewrite PhiOp_subst in HI by first [lia | avoid_tms | fr_tm].
  pose proof (PhiOp_inst n G _ _ (V + 3) (V + 1) (V + 2) f x m1 P y m2 m3 HI ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(avoid_tms) ltac:(avoid_tms)) as HI2.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ HI2 Hy) Hxy) as HP.
  exact (PRIf_to_PRI n _ _ V G [m1; m2; m3] P (V + 3) HP ltac:(lia) ltac:(avoid_tms)
           ltac:(lia) ltac:(avoid_tms) ltac:(above_tac)).
Qed.

(** ** Sums. *)

Definition fPlus3 : FOFormula := FOEq (FOPlus (FOVar 0) (FOVar 1)) (FOVar 2).

Lemma FOPr_plus_step :
  FOProvesTn 0 (FOImplF fPlus3 (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 1))) (FOSucc (FOVar 2)))).
Proof.
  change (FOPrH 0 [] (FOImplF fPlus3
            (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 1))) (FOSucc (FOVar 2))))).
  apply FOPrH_intro. cbn [app]. unfold fPlus3.
  eapply FOPrH_eq_trans; [apply FOPrH_Q_plus_succ|]. apply FOPrH_congS.
  apply FOPrH_assum. left. reflexivity.
Qed.

Lemma PRI_plus : forall n k V G x y m1 m2 m3,
  2000 <= V -> FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  FOtms_avoid [x; m1; y; m2; m3] 0 1100 ->
  (forall t, In t [x; m1; y; m2; m3] -> forall w, V <= w -> FOin_tm w t = false) ->
  FOPrH n G (FONUMR x m1) -> FOPrH n G (FONUMR y m2) -> FOPrH n G (FONUMR (FOPlus x y) m3) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f (rhoN 3) fPlus3) [m1; m2; m3].
Proof.
  intros n k V G x y m1 m2 m3 HV HG0 HGV Hav0 Havv Hx Hy Hxy.
  apply (PRI_opind n k V G true x m1 y m2 m3 _ HV HG0 HGV Hav0 Havv Hy Hxy).
  - lazymatch goal with |- PRI _ _ _ _ ?G1 _ _ =>
      assert (HG1 : FOctx_avoid G1 0 1000) by (intros w ? ?; free_ctx);
      assert (Ha : FOPrH n G1 (FONUMR FOZero (FOVar (V + 1)))) by wk_in;
      assert (Hb : FOPrH n G1 (FONUMR (FOPlus x FOZero) (FOVar (V + 2)))) by wk_in;
      assert (Hx1 : FOPrH n G1 (FONUMR x m1)) by wk Hx
    end.
    pose proof (FOPrH_numr_cong1 n _ (FOPlus x FOZero) x (FOVar (V + 2)) Hb
                  (FOPrH_Q_plus_zero n _ x) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms))
      as E1.
    pose proof (FOPrH_numr_unique n _ x m1 (FOVar (V + 2)) Hx1 E1 ltac:(avoid_tms)
                  ltac:(avoid_tms)) as E2.
    pose proof (FOPrH_numr_inv0 n _ (FOVar (V + 1)) ltac:(intros w ? ?; apply HG1; lia)
                  ltac:(avoid_tms) Ha) as C0.
    assert (HE : EnvOK n (V + 3) ((G ++ [FONUMR FOZero (FOVar (V + 1))]) ++
                   [FONUMR (opT true x FOZero) (FOVar (V + 2))])
                   [m1; FOVar (V + 1); FOVar (V + 2)])
      by (apply (EnvOK3 n _ _ _ _ _ x FOZero (FOPlus x FOZero));
          [intros w ? ?; apply HG1; lia | exact Hx1 | exact Ha | exact Hb | avoid_tms | lia
          | above_tac]).
    pose proof (PRI_thm_open n k (V + 3) _ (FOEq (FOPlus (FOVar 0) FOZero) (FOVar 0)) (rhoN 3)
                  _ ltac:(change (FOPrH 0 [] (FOEq (FOPlus (FOVar 0) FOZero) (FOVar 0)));
                          apply FOPrH_Q_plus_zero)
                  HE (rhoN_fv 3 (FOEq (FOPlus (FOVar 0) FOZero) (FOVar 0))
                        ltac:(apply Nat.ltb_lt; vm_compute; reflexivity))) as T0.
    refine (PRI_conv n _ _ (V + 3) _ _ _ _ _ _ _ _ _ T0); [| above_tac | avoid_tms | lia].
    intros G' Hinc.
    pose proof (FOPrH_weaken n _ G' _ Hinc C0) as C0'.
    pose proof (FOPrH_weaken n _ G' _ Hinc E2) as E2'.
    unfold fPlus3, rhoN. cbn [cpat_f cpat_tm Nat.ltb Nat.leb]. cprel_tac.
  - lazymatch goal with |- PRI _ _ _ _ ?G1 _ _ =>
      assert (HG1 : FOctx_avoid G1 0 1000) by (intros w ? ?; free_ctx);
      assert (HG1V : forall w, V + 3 <= w -> FOfree_ctx w G1) by (intros w ?; free_ctx);
      assert (HPhi : FOPrH n G1 (PhiOp (FOPrCores k) (FOu0 k) (V + 3) (V + 1) (V + 2) true x m1
                                  (cpat_f (rhoN 3) fPlus3) (FOVar V))) by wk_in;
      assert (Ha : FOPrH n G1 (FONUMR (FOSucc (FOVar V)) (FOVar (V + 1)))) by wk_in;
      assert (Hb : FOPrH n G1 (FONUMR (FOPlus x (FOSucc (FOVar V))) (FOVar (V + 2)))) by wk_in;
      assert (Hx1 : FOPrH n G1 (FONUMR x m1)) by wk Hx
    end.
    refine (PRI_numr_invS n _ _ (V + 3) (V + 3 + cpat_span (cpat_f (rhoN 3) fPlus3) + 1) _ _ _
              (FOVar V) (FOVar (V + 1)) Ha _ _ _ _ _ _);
      [lia | avoid_tms | above_tac | avoid_tms | above_tac |].
    intros w Hw HR.
    lazymatch goal with |- PRI _ _ _ _ ?G2 _ _ =>
      assert (HG2 : FOctx_avoid G2 0 1000) by (intros w' ? ?; free_ctx);
      assert (Cw : FOPrH n G2 (FOcpairF (FOnumeral 2) (FOVar w) (FOVar (V + 1)))) by wk_in;
      assert (Nw : FOPrH n G2 (FONUMR (FOVar V) (FOVar w))) by wk_in;
      assert (Hb2 : FOPrH n G2 (FONUMR (FOPlus x (FOSucc (FOVar V))) (FOVar (V + 2)))) by wk Hb
    end.
    pose proof (FOPrH_numr_cong1 n _ (FOPlus x (FOSucc (FOVar V))) (FOSucc (FOPlus x (FOVar V)))
                  (FOVar (V + 2)) Hb2 (FOPrH_Q_plus_succ n _ x (FOVar V)) ltac:(avoid_tms)
                  ltac:(avoid_tms) ltac:(avoid_tms)) as Hb3.
    refine (PRI_numr_invS n _ _ (S w) (V + 3 + cpat_span (cpat_f (rhoN 3) fPlus3) + 1) _ _ _
              (FOPlus x (FOVar V)) (FOVar (V + 2)) Hb3 _ _ _ _ _ _);
      [lia | avoid_tms | above_tac | avoid_tms | above_tac |].
    intros w' Hw' HR'.
    lazymatch goal with |- PRI _ _ _ _ ?G3 _ _ =>
      assert (HG3 : FOctx_avoid G3 0 1000) by (intros w'' ? ?; free_ctx);
      assert (Cw' : FOPrH n G3 (FOcpairF (FOnumeral 2) (FOVar w') (FOVar (V + 2)))) by wk_in;
      assert (Nw' : FOPrH n G3 (FONUMR (FOPlus x (FOVar V)) (FOVar w'))) by wk_in;
      assert (Cw3 : FOPrH n G3 (FOcpairF (FOnumeral 2) (FOVar w) (FOVar (V + 1)))) by wk Cw;
      assert (Nw3 : FOPrH n G3 (FONUMR (FOVar V) (FOVar w))) by wk Nw;
      assert (HPhi3 : FOPrH n G3 (PhiOp (FOPrCores k) (FOu0 k) (V + 3) (V + 1) (V + 2) true x m1
                                   (cpat_f (rhoN 3) fPlus3) (FOVar V))) by wk HPhi;
      assert (Hx3 : FOPrH n G3 (FONUMR x m1)) by wk Hx1
    end.
    pose proof (PhiOp_inst n _ _ _ (V + 3) (V + 1) (V + 2) true x m1 _ (FOVar V) (FOVar w)
                  (FOVar w') HPhi3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as IH.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ IH Nw3) Nw') as IHf.
    pose proof (PRIf_to_PRI n _ _ (S w') _ _ _ (V + 3) IHf ltac:(lia) ltac:(avoid_tms) ltac:(lia)
                  ltac:(avoid_tms) ltac:(above_tac)) as IHP.
    assert (HE : EnvOK n (S w') _ [m1; FOVar w; FOVar w'])
      by (apply (EnvOK3 n _ _ _ _ _ x (FOVar V) (FOPlus x (FOVar V)));
          [intros w'' ? ?; apply HG3; lia | exact Hx3 | exact Nw3 | exact Nw' | avoid_tms | lia
          | above_tac]).
    pose proof (PRI_thm_open n k (S w') _ _ (rhoN 3) _ FOPr_plus_step HE
                  (rhoN_fv 3 (FOImplF fPlus3 (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 1)))
                                                 (FOSucc (FOVar 2))))
                     ltac:(apply Nat.ltb_lt; vm_compute; reflexivity))) as T1.
    pose proof (PRI_mp n _ _ (S w') _ (rhoN 3) _ _ _ HE (rhoN_range 3) T1 IHP) as T2.
    refine (PRI_conv n _ _ (S w') _ _ _ _ _ _ _ _ _ T2); [| above_tac | avoid_tms | lia].
    intros G' Hinc.
    pose proof (FOPrH_weaken n _ G' _ Hinc Cw3) as C1.
    pose proof (FOPrH_weaken n _ G' _ Hinc Cw') as C2.
    unfold fPlus3, rhoN. cbn [cpat_f cpat_tm Nat.ltb Nat.leb]. cprel_tac.
Qed.
