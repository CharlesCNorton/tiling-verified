From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41
  P42.
Open Scope fo_scope.

(** ** Free variables of a substitution instance. *)

Lemma FOin_tm_subst_gen : forall u w p s, FOin_tm w (FOsubst_t p s u) = true ->
  (w <> p /\ FOin_tm w u = true) \/ FOin_tm w s = true.
Proof.
  induction u as [z| |a IH|a IHa b IHb|a IHa b IHb]; intros w p s H; cbn [FOsubst_t] in H.
  - destruct (Nat.eqb_spec z p) as [->|Hzp]; [right; exact H|].
    left. cbn [FOin_tm] in H |- *. apply Nat.eqb_eq in H. subst z. split; [exact Hzp|].
    apply Nat.eqb_refl.
  - discriminate H.
  - cbn [FOin_tm] in H |- *. exact (IH w p s H).
  - cbn [FOin_tm] in H |- *. apply Bool.orb_true_iff in H. destruct H as [H|H].
    + destruct (IHa w p s H) as [[H1 H2]|H2]; [left; split; [exact H1|] | right; exact H2].
      rewrite H2. reflexivity.
    + destruct (IHb w p s H) as [[H1 H2]|H2]; [left; split; [exact H1|] | right; exact H2].
      rewrite H2. apply Bool.orb_true_r.
  - cbn [FOin_tm] in H |- *. apply Bool.orb_true_iff in H. destruct H as [H|H].
    + destruct (IHa w p s H) as [[H1 H2]|H2]; [left; split; [exact H1|] | right; exact H2].
      rewrite H2. reflexivity.
    + destruct (IHb w p s H) as [[H1 H2]|H2]; [left; split; [exact H1|] | right; exact H2].
      rewrite H2. apply Bool.orb_true_r.
Qed.

Lemma FOfree_in_subst_gen : forall A w p s, FOfree_in w (FOsubst_f p s A) = true ->
  (w <> p /\ FOfree_in w A = true) \/ FOin_tm w s = true.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros w p s H.
  - cbn [FOsubst_f FOfree_in] in H |- *. apply Bool.orb_true_iff in H. destruct H as [H|H].
    + destruct (FOin_tm_subst_gen a w p s H) as [[H1 H2]|H2]; [left; split; [exact H1|]
        | right; exact H2]. rewrite H2. reflexivity.
    + destruct (FOin_tm_subst_gen b w p s H) as [[H1 H2]|H2]; [left; split; [exact H1|]
        | right; exact H2]. rewrite H2. apply Bool.orb_true_r.
  - discriminate H.
  - cbn [FOsubst_f FOfree_in] in H |- *. apply Bool.orb_true_iff in H. destruct H as [H|H].
    + destruct (IHB w p s H) as [[H1 H2]|H2]; [left; split; [exact H1|] | right; exact H2].
      rewrite H2. reflexivity.
    + destruct (IHC w p s H) as [[H1 H2]|H2]; [left; split; [exact H1|] | right; exact H2].
      rewrite H2. apply Bool.orb_true_r.
  - destruct (Nat.eqb_spec y p) as [->|Hyp].
    + rewrite FOsubst_f_all_self in H. left. split; [|exact H].
      intro E. subst w. cbn [FOfree_in] in H. rewrite Nat.eqb_refl in H. discriminate.
    + rewrite FOsubst_f_all_ne in H by exact Hyp. cbn [FOfree_in] in H |- *.
      destruct (Nat.eqb y w); [discriminate H|]. exact (IHB w p s H).
  - destruct (Nat.eqb_spec y p) as [->|Hyp].
    + rewrite FOsubst_f_ex_self in H. left. split; [|exact H].
      intro E. subst w. cbn [FOfree_in] in H. rewrite Nat.eqb_refl in H. discriminate.
    + rewrite FOsubst_f_ex_ne in H by exact Hyp. cbn [FOfree_in] in H |- *.
      destruct (Nat.eqb y w); [discriminate H|]. exact (IHB w p s H).
Qed.

Lemma FOfree_in_subst_false : forall A w p s, FOfree_in w A = false -> FOin_tm w s = false ->
  FOfree_in w (FOsubst_f p s A) = false.
Proof.
  intros A w p s H1 H2. destruct (FOfree_in w (FOsubst_f p s A)) eqn:E; [|reflexivity].
  destruct (FOfree_in_subst_gen A w p s E) as [[_ H]|H]; congruence.
Qed.

Lemma FOfree_in_TBLEX_lo : forall w tg a1 a2 a3 r, w < 2 ->
  FOtms_avoid [tg; a1; a2; a3; r] w (S w) -> FOtms_avoid [tg; a1; a2; a3; r] 13 18 ->
  FOfree_in w (FOTBLEX tg a1 a2 a3 r) = false.
Proof.
  intros w tg a1 a2 a3 r Hw Hav Hav2.
  assert (E : FOTBLEX tg a1 a2 a3 r =
              FOsubst_f 13 tg (FOsubst_f 14 a1 (FOsubst_f 15 a2 (FOsubst_f 16 a3 (FOsubst_f 17 r
                (FOTBLEX (FOVar 13) (FOVar 14) (FOVar 15) (FOVar 16) (FOVar 17))))))).
  { rewrite !FOsubst_f_TBLEX by lia.
    rewrite ?FOsubst_t_var_eq', ?FOsubst_t_var_ne by lia.
    rewrite (FOsubst_t_not_in r 16 a3), (FOsubst_t_not_in r 15 a2), (FOsubst_t_not_in r 14 a1),
      (FOsubst_t_not_in r 13 tg), (FOsubst_t_not_in a3 15 a2), (FOsubst_t_not_in a3 14 a1),
      (FOsubst_t_not_in a3 13 tg), (FOsubst_t_not_in a2 14 a1), (FOsubst_t_not_in a2 13 tg),
      (FOsubst_t_not_in a1 13 tg) by fr_tm.
    reflexivity. }
  rewrite E.
  repeat (apply FOfree_in_subst_false; [|fr_tm]).
  destruct w as [|[|w]]; [vm_compute; reflexivity | vm_compute; reflexivity | lia].
Qed.

Lemma FOfree_in_TBLEX_all : forall w tg a1 a2 a3 r,
  FOtms_avoid [tg; a1; a2; a3; r] w (S w) -> FOtms_avoid [tg; a1; a2; a3; r] 13 18 ->
  FOfree_in w (FOTBLEX tg a1 a2 a3 r) = false.
Proof.
  intros w tg a1 a2 a3 r Hav Hav2. destruct (Nat.lt_ge_cases w 2) as [Hw|Hw].
  - exact (FOfree_in_TBLEX_lo w tg a1 a2 a3 r Hw Hav Hav2).
  - exact (FOfree_in_TBLEX_any w tg a1 a2 a3 r Hw Hav).
Qed.

Lemma FOfree_in_NUMR_all : forall w a m, FOtms_avoid [a; m] w (S w) ->
  FOtms_avoid [a; m] 13 18 -> FOtms_avoid [a; m] 802 805 ->
  FOfree_in w (FONUMR a m) = false.
Proof.
  intros w a m Hav H13 H802. unfold FONUMR. rewrite !FOfree_in_FOAnd.
  apply Bool.orb_false_iff. split; [apply FOfree_in_TBLEX_all; avoid_tms|].
  apply Bool.orb_false_iff. split.
  - cbn [FOfree_in]. destruct (Nat.eqb_spec 802 w) as [_|E1]; [reflexivity|].
    destruct (Nat.eqb_spec 803 w) as [_|E2]; [reflexivity|].
    apply FOfree_in_TBLEX_all; avoid_tms.
  - cbn [FOfree_in]. destruct (Nat.eqb_spec 804 w) as [_|E3]; [reflexivity|].
    apply FOfree_in_TBLEX_all; avoid_tms.
Qed.

Lemma FOfree_in_PRu_all : forall cores u0 w c, FOtms_avoid [c] w (S w) -> FOtm_avoid c 1 18 ->
  FOfree_in w (FOPRu cores u0 c) = false.
Proof.
  intros cores u0 w c Hav H1.
  rewrite (FOPRu_as_subst cores u0 c (or_intror H1)).
  destruct (FOfree_in w (FOsubst_f 0 (FOnumeral u0) (FOsubst_f 1 c (FOPRMAT cores)))) eqn:E;
    [|reflexivity].
  destruct (FOfree_in_subst_gen _ w 0 (FOnumeral u0) E) as [[Hw0 Hf]|Hn];
    [| rewrite FOin_tm_numeral in Hn; discriminate].
  destruct (FOfree_in_subst_gen _ w 1 c Hf) as [[Hw1 Hf']|Hc].
  - rewrite FOPRMAT_free in Hf' by lia. discriminate.
  - assert (Hc' : FOin_tm w c = false) by fr_tm. congruence.
Qed.

Ltac free_fm ::=
  lazymatch goal with
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

(** ** Fresh numeral codes for provable instances. *)

Lemma PRI_numr_ex : forall n cores u0 V R G p env t,
  1000 <= V -> FOtms_avoid [t] 0 1000 -> (forall w, V <= w -> FOin_tm w t = false) ->
  FOtms_avoid env 0 1000 -> (forall s, In s env -> forall w, V <= w -> FOin_tm w s = false) ->
  (forall w, V <= w -> R <= w -> PRI n cores u0 (S w) (G ++ [FONUMR t (FOVar w)]) p env) ->
  PRI n cores u0 V G p env.
Proof.
  intros n cores u0 V R G p env t HV Ht0 Htv Henv0 Henv HK.
  pose proof (FOPrH_thm n G _ (FOPr_numr n)) as H.
  apply (FOPrH_inst n G 800 t) in H;
    [| apply FOsubst_ok_ex; [fr_tm | apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]]].
  rewrite FOsubst_f_ex_ne, FOsubst_f_NUMR in H by (lia || avoid_tms).
  rewrite FOsubst_t_var_eq', FOsubst_t_var_ne in H by lia.
  apply (PRI_exe n cores u0 V R G p env 801 (FONUMR t (FOVar 801)) H HV Henv0 Henv).
  - intros w Hw Hw'. free_fm.
  - intros w Hw Hw'. assert (Htw : FOtms_avoid [t] w (S w))
      by (intros s [<-|[]] w' ? ?; apply Htv; lia).
    free_fm.
  - intros w Hw _. apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms].
  - intros w Hw HR. assert (Htw : FOtms_avoid [t] w (S w))
      by (intros s [<-|[]] w' ? ?; apply Htv; lia).
    rewrite FOsubst_f_NUMR by (lia || avoid_tms).
    rewrite FOsubst_t_var_eq', (FOsubst_t_not_in t 801 (FOVar w)) by fr_tm.
    exact (HK w Hw HR).
Qed.

Lemma PRI_numr_invS : forall n cores u0 V R G p env a m,
  FOPrH n G (FONUMR (FOSucc a) m) -> 1100 <= V ->
  FOtms_avoid [a; m] 0 1100 -> (forall t, In t [a; m] -> forall w, V <= w -> FOin_tm w t = false) ->
  FOtms_avoid env 0 1000 -> (forall s, In s env -> forall w, V <= w -> FOin_tm w s = false) ->
  (forall w, V <= w -> R <= w ->
     PRI n cores u0 (S w) (G ++ [FOcpairF (FOnumeral 2) (FOVar w) m; FONUMR a (FOVar w)]) p env) ->
  PRI n cores u0 V G p env.
Proof.
  intros n cores u0 V R G p env a m H HV Ham0 Hamv Henv0 Henv HK.
  intros G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  remember (B + cpat_span p + R + 1) as w eqn:Ew.
  assert (Hcz : FOtms_avoid [c] B (S (S (S w) + cpat_span p))).
  { intros t [<-|[]] w' ? ?. apply (Hcc c (or_introl eq_refl)). lia. }
  assert (Henvz : FOtms_avoid env V (S (S (S w) + cpat_span p))).
  { intros t Ht w' ? ?. apply (Henv t Ht). lia. }
  assert (Hamz : FOtms_avoid [a; m] V (S (S (S w) + cpat_span p))).
  { intros t Ht w' ? ?. apply (Hamv t Ht). lia. }
  pose proof (FOPrH_patf_rebase p n G' B (S w) env c Hc ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(intros w' ? ?; apply HGc; lia) ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(avoid_tms)) as Hc1.
  refine (FOPrH_numr_invS n G' a m w (FOPRu cores u0 c)
            ltac:(intros w' ? ?; apply HG0; lia) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(lia)
            ltac:(apply HGc; lia) ltac:(apply HGc; lia) ltac:(free_fm) ltac:(avoid_tms)
            ltac:(intros v ? ?; free_fm) (FOPrH_weaken n G G' _ Hinc H) _).
  refine (HK w ltac:(lia) ltac:(lia) _ (S w) c _ _ Hc0 (le_n _) _ (FOPrH_weak_app _ _ _ _ Hc1)).
  - intros Y HY. apply in_app_or in HY. destruct HY as [HY|HY]; apply in_or_app;
      [left; exact (Hinc Y HY) | right; exact HY].
  - intros w' ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|].
    apply FOfree_ctx_cons; [free_fm|]. apply FOfree_ctx_cons; [free_fm | apply FOfree_ctx_nil].
  - split.
    + intros w' Hw'. assert (Haw : FOtms_avoid [a; m] w' (S w'))
        by (intros t Ht w'' ? ?; apply (Hamv t Ht); lia).
      apply FOfree_ctx_app_inv; [apply HGc; lia|].
      apply FOfree_ctx_cons; [free_fm|]. apply FOfree_ctx_cons; [free_fm | apply FOfree_ctx_nil].
    + intros t [<-|[]] w' Hw'. apply (Hcc c (or_introl eq_refl)). lia.
Qed.

(** ** Instances of theorems with free variables. *)

Lemma FOForalls_gen : forall xs A, FOProvesTn 0 A -> FOProvesTn 0 (FOForalls xs A).
Proof.
  induction xs as [|x xs IH]; intros A H; [exact H|].
  cbn [FOForalls]. apply FOProvesTn_Gen. exact (IH A H).
Qed.

Lemma PRI_thm_open : forall n k V G A rho env,
  FOProvesTn 0 A -> EnvOK n V G env ->
  (forall x, FOfree_in x A = true -> exists j, rho x = Some j /\ j < length env) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho A) env.
Proof.
  intros n k V G A rho env HA HE Hx.
  apply (PRI_thm n k V G (fvs A) A rho env (FOForalls_gen (fvs A) A HA) (fvs_nodup A)).
  - intros x Hx'. apply fvs_spec. exact Hx'.
  - exact HE.
  - intros x Hx'. apply Hx. apply fvs_spec. exact Hx'.
Qed.

(** ** Holders: free variables renamed to holder variables. *)

Fixpoint hsub_tm (h : nat -> nat) (t : FOTerm) : FOTerm :=
  match t with
  | FOVar y => FOVar (h y)
  | FOZero => FOZero
  | FOSucc a => FOSucc (hsub_tm h a)
  | FOPlus a b => FOPlus (hsub_tm h a) (hsub_tm h b)
  | FOMult a b => FOMult (hsub_tm h a) (hsub_tm h b)
  end.

Definition h_hide (y : nat) (h : nat -> nat) : nat -> nat :=
  fun z => if Nat.eqb z y then y else h z.

Definition h_upd (y N : nat) (h : nat -> nat) : nat -> nat :=
  fun z => if Nat.eqb z y then N else h z.

Fixpoint hsub_f (h : nat -> nat) (A : FOFormula) : FOFormula :=
  match A with
  | FOEq a b => FOEq (hsub_tm h a) (hsub_tm h b)
  | FOFalseF => FOFalseF
  | FOImplF B C => FOImplF (hsub_f h B) (hsub_f h C)
  | FOForall y B => FOForall y (hsub_f (h_hide y h) B)
  | FOExists y B => FOExists y (hsub_f (h_hide y h) B)
  end.

Lemma hsub_tm_ext : forall t h h', (forall z, FOin_tm z t = true -> h z = h' z) ->
  hsub_tm h t = hsub_tm h' t.
Proof.
  induction t as [y| |a IH|a IHa b IHb|a IHa b IHb]; intros h h' H; cbn [hsub_tm].
  - rewrite (H y ltac:(cbn [FOin_tm]; apply Nat.eqb_refl)). reflexivity.
  - reflexivity.
  - rewrite (IH h h' H). reflexivity.
  - rewrite (IHa h h'), (IHb h h'); [reflexivity| |];
      intros z Hz; apply H; cbn [FOin_tm]; rewrite Hz; [apply Bool.orb_true_r | reflexivity].
  - rewrite (IHa h h'), (IHb h h'); [reflexivity| |];
      intros z Hz; apply H; cbn [FOin_tm]; rewrite Hz; [apply Bool.orb_true_r | reflexivity].
Qed.

Lemma hsub_f_ext : forall A h h', (forall z, FOfree_in z A = true -> h z = h' z) ->
  hsub_f h A = hsub_f h' A.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros h h' H; cbn [hsub_f].
  - rewrite (hsub_tm_ext a h h'), (hsub_tm_ext b h h'); [reflexivity| |];
      intros z Hz; apply H; cbn [FOfree_in]; rewrite Hz; [apply Bool.orb_true_r | reflexivity].
  - reflexivity.
  - rewrite (IHB h h'), (IHC h h'); [reflexivity| |];
      intros z Hz; apply H; cbn [FOfree_in]; rewrite Hz; [apply Bool.orb_true_r | reflexivity].
  - f_equal. apply IHB. intros z Hz. unfold h_hide.
    destruct (Nat.eqb_spec z y) as [->|Hzy]; [reflexivity|].
    apply H. cbn [FOfree_in]. rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz.
  - f_equal. apply IHB. intros z Hz. unfold h_hide.
    destruct (Nat.eqb_spec z y) as [->|Hzy]; [reflexivity|].
    apply H. cbn [FOfree_in]. rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz.
Qed.

Lemma FOin_tm_hsub : forall t h w, FOin_tm w (hsub_tm h t) = true ->
  exists z, FOin_tm z t = true /\ h z = w.
Proof.
  induction t as [y| |a IH|a IHa b IHb|a IHa b IHb]; intros h w H; cbn [hsub_tm FOin_tm] in H.
  - exists y. split; [cbn [FOin_tm]; apply Nat.eqb_refl | apply Nat.eqb_eq; exact H].
  - discriminate H.
  - exact (IH h w H).
  - apply Bool.orb_true_iff in H. destruct H as [H|H].
    + destruct (IHa h w H) as [z [Hz Ez]]. exists z. split; [|exact Ez].
      cbn [FOin_tm]. rewrite Hz. reflexivity.
    + destruct (IHb h w H) as [z [Hz Ez]]. exists z. split; [|exact Ez].
      cbn [FOin_tm]. rewrite Hz. apply Bool.orb_true_r.
  - apply Bool.orb_true_iff in H. destruct H as [H|H].
    + destruct (IHa h w H) as [z [Hz Ez]]. exists z. split; [|exact Ez].
      cbn [FOin_tm]. rewrite Hz. reflexivity.
    + destruct (IHb h w H) as [z [Hz Ez]]. exists z. split; [|exact Ez].
      cbn [FOin_tm]. rewrite Hz. apply Bool.orb_true_r.
Qed.

Lemma FOfree_in_hsub : forall A h w, FOfree_in w (hsub_f h A) = true ->
  exists z, FOfree_in z A = true /\ h z = w.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros h w H; cbn [hsub_f FOfree_in] in H.
  - apply Bool.orb_true_iff in H. destruct H as [H|H].
    + destruct (FOin_tm_hsub a h w H) as [z [Hz Ez]]. exists z. split; [|exact Ez].
      cbn [FOfree_in]. rewrite Hz. reflexivity.
    + destruct (FOin_tm_hsub b h w H) as [z [Hz Ez]]. exists z. split; [|exact Ez].
      cbn [FOfree_in]. rewrite Hz. apply Bool.orb_true_r.
  - discriminate H.
  - apply Bool.orb_true_iff in H. destruct H as [H|H].
    + destruct (IHB h w H) as [z [Hz Ez]]. exists z. split; [|exact Ez].
      cbn [FOfree_in]. rewrite Hz. reflexivity.
    + destruct (IHC h w H) as [z [Hz Ez]]. exists z. split; [|exact Ez].
      cbn [FOfree_in]. rewrite Hz. apply Bool.orb_true_r.
  - destruct (Nat.eqb_spec y w) as [->|Hyw]; [discriminate H|].
    destruct (IHB (h_hide y h) w H) as [z [Hz Ez]]. unfold h_hide in Ez.
    destruct (Nat.eqb_spec z y) as [->|Hzy]; [congruence|].
    exists z. split; [|exact Ez]. cbn [FOfree_in].
    rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz.
  - destruct (Nat.eqb_spec y w) as [->|Hyw]; [discriminate H|].
    destruct (IHB (h_hide y h) w H) as [z [Hz Ez]]. unfold h_hide in Ez.
    destruct (Nat.eqb_spec z y) as [->|Hzy]; [congruence|].
    exists z. split; [|exact Ez]. cbn [FOfree_in].
    rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz.
Qed.

Lemma h_hide_comm : forall y v h z, y <> v ->
  h_hide y (h_hide v h) z = h_hide v (h_hide y h) z.
Proof.
  intros y v h z Hyv. unfold h_hide.
  destruct (Nat.eqb_spec z y) as [Ezy|Ezy]; destruct (Nat.eqb_spec z v) as [Ezv|Ezv];
    subst; [lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma h_upd_hide_comm : forall y v N h z, y <> v ->
  h_upd v N (h_hide y h) z = h_hide y (h_upd v N h) z.
Proof.
  intros y v N h z Hyv. unfold h_hide, h_upd.
  destruct (Nat.eqb_spec z y) as [Ezy|Ezy]; destruct (Nat.eqb_spec z v) as [Ezv|Ezv];
    subst; [lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma hsub_tm_inst : forall t v N h, (forall z, z <> v -> FOin_tm z t = true -> h z <> v) ->
  FOsubst_t v (FOVar N) (hsub_tm (h_hide v h) t) = hsub_tm (h_upd v N h) t.
Proof.
  induction t as [y| |a IH|a IHa b IHb|a IHa b IHb]; intros v N h H; cbn [hsub_tm].
  - unfold h_hide, h_upd. destruct (Nat.eqb_spec y v) as [->|Hyv].
    + apply FOsubst_t_var_eq'.
    + apply FOsubst_t_var_ne. apply H; [exact Hyv | cbn [FOin_tm]; apply Nat.eqb_refl].
  - reflexivity.
  - rewrite FOsubst_t_succ, IH by exact H. reflexivity.
  - rewrite FOsubst_t_plus, IHa, IHb; [reflexivity| |];
      intros z Hz Hz'; apply H; try exact Hz; cbn [FOin_tm]; rewrite Hz';
      [apply Bool.orb_true_r | reflexivity].
  - rewrite FOsubst_t_mult, IHa, IHb; [reflexivity| |];
      intros z Hz Hz'; apply H; try exact Hz; cbn [FOin_tm]; rewrite Hz';
      [apply Bool.orb_true_r | reflexivity].
Qed.

Lemma hsub_f_inst : forall A v N h, (forall z, z <> v -> FOfree_in z A = true -> h z <> v) ->
  FOsubst_f v (FOVar N) (hsub_f (h_hide v h) A) = hsub_f (h_upd v N h) A.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros v N h H; cbn [hsub_f].
  - rewrite FOsubst_f_eq, !hsub_tm_inst; [reflexivity| |];
      intros z Hz Hz'; apply H; try exact Hz; cbn [FOfree_in]; rewrite Hz';
      [apply Bool.orb_true_r | reflexivity].
  - reflexivity.
  - rewrite FOsubst_f_impl, IHB, IHC; [reflexivity| |];
      intros z Hz Hz'; apply H; try exact Hz; cbn [FOfree_in]; rewrite Hz';
      [apply Bool.orb_true_r | reflexivity].
  - destruct (Nat.eqb_spec y v) as [->|Hyv].
    + rewrite FOsubst_f_all_self. f_equal. apply hsub_f_ext. intros z _.
      unfold h_hide, h_upd. destruct (Nat.eqb z v); reflexivity.
    + rewrite FOsubst_f_all_ne by exact Hyv. f_equal.
      rewrite (hsub_f_ext B (h_hide y (h_hide v h)) (h_hide v (h_hide y h)))
        by (intros z _; apply h_hide_comm; exact Hyv).
      rewrite IHB.
      * apply hsub_f_ext. intros z _. apply h_upd_hide_comm. exact Hyv.
      * intros z Hz Hz'. unfold h_hide. destruct (Nat.eqb_spec z y) as [->|Hzy]; [exact Hyv|].
        apply H; [exact Hz|]. cbn [FOfree_in].
        rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz'.
  - destruct (Nat.eqb_spec y v) as [->|Hyv].
    + rewrite FOsubst_f_ex_self. f_equal. apply hsub_f_ext. intros z _.
      unfold h_hide, h_upd. destruct (Nat.eqb z v); reflexivity.
    + rewrite FOsubst_f_ex_ne by exact Hyv. f_equal.
      rewrite (hsub_f_ext B (h_hide y (h_hide v h)) (h_hide v (h_hide y h)))
        by (intros z _; apply h_hide_comm; exact Hyv).
      rewrite IHB.
      * apply hsub_f_ext. intros z _. apply h_upd_hide_comm. exact Hyv.
      * intros z Hz Hz'. unfold h_hide. destruct (Nat.eqb_spec z y) as [->|Hzy]; [exact Hyv|].
        apply H; [exact Hz|]. cbn [FOfree_in].
        rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz'.
Qed.

Lemma hsub_f_ok : forall A h x s W, FOvars_max A < W ->
  (forall w, FOin_tm w s = true -> W <= w) -> FOsubst_ok x s (hsub_f h A) = true.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros h x s W HA Hs;
    cbn [hsub_f FOvars_max] in *.
  - reflexivity.
  - reflexivity.
  - apply FOsubst_ok_impl; [apply (IHB h x s W) | apply (IHC h x s W)]; try exact Hs; lia.
  - apply FOsubst_ok_all; [|apply (IHB (h_hide y h) x s W); [lia | exact Hs]].
    destruct (FOin_tm y s) eqn:E; [|reflexivity]. specialize (Hs y E). lia.
  - apply FOsubst_ok_ex; [|apply (IHB (h_hide y h) x s W); [lia | exact Hs]].
    destruct (FOin_tm y s) eqn:E; [|reflexivity]. specialize (Hs y E). lia.
Qed.
