From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41.
Open Scope fo_scope.

(** ** Provable instances: monotonicity. *)

Lemma PRI_mono : forall n cores u0 V V' G G' p env, V <= V' ->
  (forall X, In X G -> In X G') ->
  PRI n cores u0 V G p env -> PRI n cores u0 V' G' p env.
Proof.
  intros n cores u0 V V' G G' p env HV Hinc HI G'' B c Hinc' HG0 Hc0 HBV Hcl Hc.
  exact (HI G'' B c (fun X HX => Hinc' X (Hinc X HX)) HG0 Hc0 ltac:(lia) Hcl Hc).
Qed.

Lemma PRI_efq : forall n cores u0 V G p env,
  FOPrH n G FOFalseF -> PRI n cores u0 V G p env.
Proof.
  intros n cores u0 V G p env HF G' B c Hinc _ _ _ _ _.
  apply FOPrH_efq. exact (FOPrH_weaken n G G' _ Hinc HF).
Qed.

(** ** Pattern facts under substitution above their region. *)

Lemma FOsubst_f_bex_ne : forall x s v t A, x <> v -> x <> S v ->
  FOsubst_f x s (FOBexC v t A) = FOBexC v (FOsubst_t x s t) (FOsubst_f x s A).
Proof.
  intros x s v t A H1 H2. rewrite !FOBexC_ltv. unfold FOltv.
  rewrite FOsubst_f_ex_ne by lia. rewrite FOsubst_f_and, FOsubst_f_ex_ne by lia.
  rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_succ, !FOsubst_t_var_ne by lia.
  reflexivity.
Qed.

Lemma FOsubst_f_PATF_hi : forall p x s B env d, B + cpat_span p <= x ->
  FOsubst_f x s (FOPATF B env p d) =
  FOPATF B (map (FOsubst_t x s) env) p (FOsubst_t x s d).
Proof.
  induction p as [k|j|q IH|a IHa b IHb]; intros x s B env d H;
    cbn [FOPATF cpat_span] in *.
  - rewrite FOsubst_f_eq, FOsubst_t_numeral. reflexivity.
  - rewrite FOsubst_f_eq, FOsubst_t_nth. reflexivity.
  - rewrite FOsubst_f_bex_ne by lia. rewrite FOsubst_f_and, FOsubst_f_eq, FOsubst_t_succ.
    rewrite IH by lia. rewrite !FOsubst_t_var_ne by lia. reflexivity.
  - pose proof (cpat_span_le a) as Ha.
    rewrite FOsubst_f_bex_ne by lia. rewrite FOsubst_f_bex_ne by lia.
    rewrite FOsubst_f_and, FOsubst_f_cpairF, FOsubst_f_and, !FOsubst_t_succ.
    rewrite IHa, IHb by lia. rewrite !FOsubst_t_var_ne by lia. reflexivity.
Qed.

(** ** Provable instances and their internal form. *)

Lemma PRIf_to_PRI : forall n cores u0 V G env p B0,
  FOPrH n G (PRIf cores u0 B0 env p) -> 500 <= B0 -> FOtms_avoid env B0 (B0 + cpat_span p) ->
  1000 <= V ->
  FOtms_avoid env 0 1000 -> (forall t, In t env -> forall w, V <= w -> FOin_tm w t = false) ->
  PRI n cores u0 V G p env.
Proof.
  intros n cores u0 V G env p B0 HI HB0 HenvB HV Henv0 Henv.
  intros G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  remember (B + B0 + cpat_span p + 1) as z eqn:Ez.
  assert (Hcz : FOtms_avoid [c] B (S (S z + cpat_span p))).
  { intros t [<-|[]] w ? ?. apply (Hcc c (or_introl eq_refl)). lia. }
  assert (Henvz : FOtms_avoid env V (S (S z + cpat_span p))).
  { intros t Ht w ? ?. apply (Henv t Ht). lia. }
  pose proof (FOPrH_patf_rebase p n G' B (S z) env c Hc ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(intros w ? ?; apply HGc; lia) ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(avoid_tms)) as Hc1.
  assert (Hex : FOPrH n G' (FOExists z (FOEq (FOVar z) c))).
  { apply (FOPrH_ex_intro n G' z c); [apply FOsubst_ok_eq|].
    rewrite FOsubst_f_eq, FOsubst_t_var_eq', (FOsubst_t_not_in c z c) by fr_tm.
    apply FOPrH_refl. }
  refine (FOPrH_ex_elim n G' z _ _ _ _ Hex _); [apply HGc; lia | free_fm |].
  lazymatch goal with |- FOPrH _ ?G2 _ =>
    assert (E : FOPrH n G2 (FOEq (FOVar z) c)) by apply FOPrH_last;
    assert (Hc2 : FOPrH n G2 (FOPATF (S z) env p c)) by wk Hc1;
    assert (HI2 : FOPrH n G2 (PRIf cores u0 B0 env p))
      by exact (FOPrH_weaken n G G2 _
                  (fun X HX => in_or_app _ _ _ (or_introl (Hinc X HX))) HI);
    assert (HG2 : FOctx_avoid G2 (S z) (S z + cpat_span p))
      by (intros w ? ?; apply FOfree_ctx_app_inv; [apply HGc; lia | free_ctx])
  end.
  assert (Hpz : FOPrH n (G' ++ [FOEq (FOVar z) c]) (FOPATF (S z) env p (FOVar z))).
  { pose proof (FOPrH_leibniz n _ z c (FOVar z) (FOPATF (S z) env p (FOVar z))
                  ltac:(apply FOsubst_ok_PATF; avoid_tm) ltac:(apply FOsubst_ok_PATF; avoid_tm)
                  (FOPrH_eq_sym _ _ _ _ E)) as L.
    rewrite !FOsubst_f_PATF in L by lia.
    rewrite !FOsubst_t_var_eq', (FOsubst_map_avoid z c env), (FOsubst_map_avoid z (FOVar z) env)
      in L by (intros t Ht; apply (Henv t Ht); lia).
    exact (L Hc2). }
  pose proof (FOPrH_patf_rebase p n _ (S z) B0 env (FOVar z) Hpz ltac:(lia) ltac:(lia)
                ltac:(lia) HG2 ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Hp0.
  pose proof (FOPrH_prif_elim n _ cores u0 B0 env p (FOVar z) HI2 Hp0 ltac:(lia)
                ltac:(avoid_tms) ltac:(avoid_tm) ltac:(avoid_tm)) as Hpr.
  pose proof (FOPrH_leibniz n _ z (FOVar z) c (FOPRu cores u0 (FOVar z))
                ltac:(apply FOsubst_ok_PRu; [lia | avoid_tm | right; avoid_tm | avoid_tm])
                ltac:(apply FOsubst_ok_PRu; [lia | avoid_tm | right; avoid_tm | avoid_tm]) E)
    as L.
  rewrite FOsubst_f_id, FOsubst_f_PRu, FOsubst_t_var_eq' in L by first [lia | avoid_tms].
  exact (L Hpr).
Qed.

Lemma PRI_to_PRIf : forall n cores u0 V G env p B0,
  PRI n cores u0 V G p env -> V <= B0 -> 1000 <= V ->
  FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  FOtms_avoid env 0 1000 -> (forall t, In t env -> forall w, V <= w -> FOin_tm w t = false) ->
  FOPrH n G (PRIf cores u0 B0 env p).
Proof.
  intros n cores u0 V G env p B0 HI HVB HV HG0 HGV Henv0 Henv.
  remember (B0 + cpat_span p + 1) as z eqn:Ez.
  assert (Henvz : FOtms_avoid env V (S (S z + cpat_span p))).
  { intros t Ht w ? ?. apply (Henv t Ht). lia. }
  assert (Hz : FOPrH n G (FOForall z (FOImplF (FOPATF B0 env p (FOVar z))
                                        (FOPRu cores u0 (FOVar z))))).
  { apply FOPrH_all_intro; [apply HGV; lia|]. apply FOPrH_intro.
    assert (HP : forall w, 2 <= w -> w <> z -> (w < 1000 \/ V <= w) ->
               FOfree_in w (FOPATF B0 env p (FOVar z)) = false).
    { intros w Hw Hwz Hw'. apply FOfree_in_PATF_any; [lia|].
      apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
      intros t Ht w' ? ?. destruct Hw' as [Hw'|Hw'];
        [apply (Henv0 t Ht); lia | apply (Henv t Ht); lia]. }
    assert (HP0 : forall w, w < 2 -> FOfree_in w (FOPATF B0 env p (FOVar z)) = false).
    { intros w Hw. apply FOfree_in_PATF_lo; [lia|].
      apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
      intros t Ht w' ? ?. apply (Henv0 t Ht); lia. }
    assert (Hp : FOPrH n (G ++ [FOPATF B0 env p (FOVar z)]) (FOPATF B0 env p (FOVar z)))
      by apply FOPrH_last.
    pose proof (FOPrH_patf_rebase p n _ B0 (S z) env (FOVar z) Hp ltac:(lia) ltac:(lia)
                  ltac:(lia)
                  ltac:(intros w ? ?; apply FOfree_ctx_app_inv;
                        [apply HGV; lia | apply FOfree_ctx_cons;
                                          [apply HP; lia | apply FOfree_ctx_nil]])
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Hp1.
    refine (HI _ (S z) (FOVar z) (fun X HX => in_or_app _ _ _ (or_introl HX)) _
              ltac:(avoid_tms) ltac:(lia) _ Hp1).
    - intros w ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|].
      apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
      destruct (Nat.lt_ge_cases w 2) as [Hw2|Hw2]; [apply HP0; lia | apply HP; lia].
    - split.
      + intros w Hw. apply FOfree_ctx_app_inv; [apply HGV; lia|].
        apply FOfree_ctx_cons; [apply HP; lia | apply FOfree_ctx_nil].
      + intros t [<-|[]] w Hw. apply FOin_tm_var_ne. lia. }
  unfold PRIf. apply FOPrH_all_intro; [apply HG0; lia|].
  apply (FOPrH_inst n G z (FOVar 1)) in Hz;
    [| apply FOsubst_ok_impl;
       [apply FOsubst_ok_PATF; apply FOtm_avoid_var; lia
       | apply FOsubst_ok_PRu; [lia | avoid_tm | right; avoid_tm | avoid_tm]]].
  rewrite FOsubst_f_impl, FOsubst_f_PATF_hi in Hz by lia.
  rewrite (FOsubst_map_avoid z (FOVar 1) env) in Hz by (intros t Ht; apply (Henv t Ht); lia).
  rewrite (FOsubst_f_PRu_gen cores u0 z (FOVar 1) (FOVar z)) in Hz;
    [| lia | reflexivity | avoid_tm | right; avoid_tm | left; apply FOsubst_t_var_eq'].
  rewrite !FOsubst_t_var_eq' in Hz. exact Hz.
Qed.

(** ** Existential elimination for provable instances. *)

Lemma PRI_exe : forall n cores u0 V R G p env x X,
  FOPrH n G (FOExists x X) -> 1000 <= V ->
  FOtms_avoid env 0 1000 -> (forall t, In t env -> forall w, V <= w -> FOin_tm w t = false) ->
  (forall w, w < 1000 -> w <> x -> FOfree_in w X = false) ->
  (forall w, V <= w -> w <> x -> FOfree_in w X = false) ->
  (forall w, V <= w -> R <= w -> FOsubst_ok x (FOVar w) X = true) ->
  (forall w, V <= w -> R <= w -> PRI n cores u0 (S w) (G ++ [FOsubst_f x (FOVar w) X]) p env) ->
  PRI n cores u0 V G p env.
Proof.
  intros n cores u0 V R G p env x X HE HV Henv0 Henv HXlo HXhi HXok HK.
  intros G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  remember (B + x + cpat_span p + R + 1) as w eqn:Ew.
  assert (Hcz : FOtms_avoid [c] B (S (S w + cpat_span p))).
  { intros t [<-|[]] w' ? ?. apply (Hcc c (or_introl eq_refl)). lia. }
  assert (Henvz : FOtms_avoid env V (S (S w + cpat_span p))).
  { intros t Ht w' ? ?. apply (Henv t Ht). lia. }
  assert (HXw : forall w', FOfree_in w' (FOsubst_f x (FOVar w) X) = true ->
            w' = w \/ (w' <> x /\ FOfree_in w' X = true)).
  { intros w' H. destruct (Nat.eqb_spec w' w) as [->|Hne]; [left; reflexivity|right].
    split.
    - intro E. subst w'. rewrite FOfree_in_subst_away in H by lia. discriminate.
    - exact (FOfree_in_subst_closed X w' x (FOVar w) ltac:(apply FOin_tm_var_ne; lia) H). }
  pose proof (FOPrH_patf_rebase p n G' B (S w) env c Hc ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(intros w' ? ?; apply HGc; lia) ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(avoid_tms)) as Hc1.
  refine (FOPrH_ex_elim_fresh n G' x w X _ _ _ _ _ (FOPrH_weaken n G G' _ Hinc HE) _).
  - apply HGc. lia.
  - free_fm.
  - apply HXhi; lia.
  - apply HXok; lia.
  - refine (HK w ltac:(lia) ltac:(lia) _ (S w) c _ _ Hc0 (le_n _) _
              (FOPrH_weak_app _ _ _ _ Hc1)).
    + intros Y HY. apply in_app_or in HY. destruct HY as [HY|HY]; apply in_or_app;
        [left; exact (Hinc Y HY) | right; exact HY].
    + intros w' ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|].
      apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
      destruct (FOfree_in w' (FOsubst_f x (FOVar w) X)) eqn:E; [exfalso|reflexivity].
      destruct (HXw w' E) as [->|[Hne Hf]]; [lia|]. rewrite HXlo in Hf by lia. discriminate.
    + split.
      * intros w' Hw'. apply FOfree_ctx_app_inv; [apply HGc; lia|].
        apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
        destruct (FOfree_in w' (FOsubst_f x (FOVar w) X)) eqn:E; [exfalso|reflexivity].
        destruct (HXw w' E) as [->|[Hne Hf]]; [lia|]. rewrite HXhi in Hf by lia. discriminate.
      * intros t [<-|[]] w' Hw'. apply (Hcc c (or_introl eq_refl)). lia.
Qed.

(** ** Case analysis on a formula. *)

Lemma PRI_cases : forall n cores u0 V G p env X,
  (forall w, w < 1000 -> FOfree_in w X = false) -> (forall w, V <= w -> FOfree_in w X = false) ->
  PRI n cores u0 V (G ++ [X]) p env -> PRI n cores u0 V (G ++ [FONeg X]) p env ->
  PRI n cores u0 V G p env.
Proof.
  intros n cores u0 V G p env X HX0 HXV H1 H2 G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  assert (HN0 : forall w, w < 1000 -> FOfree_in w (FONeg X) = false).
  { intros w Hw. unfold FONeg. cbn [FOfree_in]. rewrite HX0 by exact Hw. reflexivity. }
  assert (HNV : forall w, V <= w -> FOfree_in w (FONeg X) = false).
  { intros w Hw. unfold FONeg. cbn [FOfree_in]. rewrite HXV by exact Hw. reflexivity. }
  apply (FOPrH_or_elim n G' X (FONeg X) _ (FOPrH_em n G' X)).
  - apply (H1 (G' ++ [X]) B c).
    + intros Y HY. apply in_app_or in HY. destruct HY as [HY|HY]; apply in_or_app;
        [left; exact (Hinc Y HY) | right; exact HY].
    + intros w ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|].
      apply FOfree_ctx_cons; [apply HX0; lia | apply FOfree_ctx_nil].
    + exact Hc0.
    + exact HBV.
    + split; [|exact Hcc]. intros w Hw. apply FOfree_ctx_app_inv; [apply HGc; lia|].
      apply FOfree_ctx_cons; [apply HXV; lia | apply FOfree_ctx_nil].
    + apply FOPrH_weak_app. exact Hc.
  - apply (H2 (G' ++ [FONeg X]) B c).
    + intros Y HY. apply in_app_or in HY. destruct HY as [HY|HY]; apply in_or_app;
        [left; exact (Hinc Y HY) | right; exact HY].
    + intros w ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|].
      apply FOfree_ctx_cons; [apply HN0; lia | apply FOfree_ctx_nil].
    + exact Hc0.
    + exact HBV.
    + split; [|exact Hcc]. intros w Hw. apply FOfree_ctx_app_inv; [apply HGc; lia|].
      apply FOfree_ctx_cons; [apply HNV; lia | apply FOfree_ctx_nil].
    + apply FOPrH_weak_app. exact Hc.
Qed.

(** ** Theorems. *)

Lemma FOPrH_pru_eq : forall n G cores u0 a b, FOPrH n G (FOEq a b) ->
  FOtms_avoid [a; b] 0 252 ->
  FOPrH n G (FOPRu cores u0 a) -> FOPrH n G (FOPRu cores u0 b).
Proof.
  intros n G cores u0 a b E Hav Ha.
  pose proof (FOPrH_leibniz n G 300 a b (FOPRu cores u0 (FOVar 300))
                ltac:(apply FOsubst_ok_PRu; [lia | avoid_tm | right; avoid_tm | avoid_tm])
                ltac:(apply FOsubst_ok_PRu; [lia | avoid_tm | right; avoid_tm | avoid_tm]) E) as L.
  rewrite !FOsubst_f_PRu, !FOsubst_t_var_eq' in L by first [lia | avoid_tms].
  exact (L Ha).
Qed.

Lemma PRI_closed : forall n k V G A, FOProvesTn 0 A -> 1000 <= V ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f (fun _ => None) A) [].
Proof.
  intros n k V G A HA HV G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  assert (Hcz : FOtms_avoid [c] B (B + 2 * cpat_span (cpat_f (fun _ => None) A) + 1)).
  { intros t [<-|[]] w ? ?. apply (Hcc c (or_introl eq_refl)). lia. }
  pose proof (FOPrH_patf_closed_code n G' A (B + cpat_span (cpat_f (fun _ => None) A))
                ltac:(lia)) as Hd.
  pose proof (FOPrH_patf_unique (cpat_f (fun _ => None) A) n G' B
                (B + cpat_span (cpat_f (fun _ => None) A)) [] c (FOnumeral (FOcode_f A)) Hc Hd
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros w ? ?; apply HGc; lia)
                ltac:(intros w ? ?; apply HGc; lia) ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(avoid_tms)) as E.
  exact (FOPrH_pru_eq n G' _ _ _ _ (FOPrH_eq_sym _ _ _ _ E) ltac:(avoid_tms)
           (FOPrH_pru_thm n G' k A HA)).
Qed.

Lemma EnvOK_snoc : forall n V G env m w, EnvOK n V G env -> FOPrH n G (FONUMR w m) ->
  FOtms_avoid [m] 0 1000 -> (forall w', V <= w' -> FOin_tm w' m = false) ->
  EnvOK n V G (env ++ [m]).
Proof.
  intros n V G env m w [HS [H0 [HV Hab]]] Hm Hm0 Hmv.
  split; [exact (SlotCtx_snoc n env G m w HS Hm)|]. split; [avoid_tms|]. split; [exact HV|].
  intros t Ht w' Hw'. apply in_app_or in Ht.
  destruct Ht as [Ht|[<-|[]]]; [exact (Hab t Ht w' Hw') | exact (Hmv w' Hw')].
Qed.

Lemma EnvOK_nil : forall n V G env, EnvOK n V G env -> EnvOK n V G [].
Proof.
  intros n V G env [[HG _] [_ [HV _]]]. split; [split; [exact HG | intros i Hi; cbn in Hi; lia]|].
  split; [apply FOtms_avoid_nil|]. split; [exact HV | intros t []].
Qed.

Fixpoint FOForalls (xs : list nat) (A : FOFormula) : FOFormula :=
  match xs with [] => A | x :: xs' => FOForall x (FOForalls xs' A) end.

Fixpoint rho_seq (xs : list nat) (k : nat) (rho : nat -> option nat) : nat -> option nat :=
  match xs with [] => rho | x :: xs' => rho_seq xs' (S k) (rho_sub (Some x) k rho) end.

Lemma rho_seq_out : forall xs k rho x, ~ In x xs -> rho_seq xs k rho x = rho x.
Proof.
  induction xs as [|y xs IH]; intros k rho x Hx; [reflexivity|].
  cbn [rho_seq]. rewrite IH by (intro H; apply Hx; right; exact H).
  unfold rho_sub. destruct (Nat.eqb_spec x y) as [->|Hne]; [|reflexivity].
  exfalso. apply Hx. left. reflexivity.
Qed.

Lemma rho_seq_nth : forall xs k rho i x, NoDup xs -> nth_error xs i = Some x ->
  rho_seq xs k rho x = Some (k + i).
Proof.
  induction xs as [|y xs IH]; intros k rho i x Hnd Hi; [destruct i; discriminate|].
  inversion Hnd as [|y' xs' Hy Hnd']. subst y' xs'.
  cbn [rho_seq]. destruct i as [|i]; cbn [nth_error] in Hi.
  - injection Hi as <-. rewrite rho_seq_out by exact Hy. unfold rho_sub.
    rewrite Nat.eqb_refl. f_equal. lia.
  - rewrite (IH (S k) _ i x Hnd' Hi). f_equal. lia.
Qed.

Lemma rho_seq_range : forall xs k rho, (forall z i, rho z = Some i -> i < k) ->
  forall z i, rho_seq xs k rho z = Some i -> i < k + length xs.
Proof.
  induction xs as [|y xs IH]; intros k rho Hr z i Hz; cbn [rho_seq length] in *.
  - specialize (Hr z i Hz). lia.
  - specialize (IH (S k) (rho_sub (Some y) k rho)).
    assert (Hr' : forall z i, rho_sub (Some y) k rho z = Some i -> i < S k).
    { intros z' i' Hz'. unfold rho_sub in Hz'. destruct (Nat.eqb z' y);
        [injection Hz' as <-; lia | specialize (Hr z' i' Hz'); lia]. }
    specialize (IH Hr' z i Hz). lia.
Qed.

Lemma PRI_insts : forall xs ms n cores u0 V G rho env A,
  length ms = length xs ->
  EnvOK n V G env -> (forall z i, rho z = Some i -> i < length env) ->
  (forall m, In m ms -> exists w, FOPrH n G (FONUMR w m)) ->
  FOtms_avoid ms 0 1000 -> (forall m, In m ms -> forall w, V <= w -> FOin_tm w m = false) ->
  PRI n cores u0 V G (cpat_f rho (FOForalls xs A)) env ->
  PRI n cores u0 V G (cpat_f (rho_seq xs (length env) rho) A) (env ++ ms).
Proof.
  induction xs as [|x xs IH]; intros ms n cores u0 V G rho env A Hlen HE Hrho Hnum Hm0 Hmv HI.
  - destruct ms; [|discriminate]. rewrite app_nil_r. exact HI.
  - destruct ms as [|m ms]; [discriminate|]. cbn [length] in Hlen. injection Hlen as Hlen.
    destruct (Hnum m (or_introl eq_refl)) as [w Hw].
    cbn [FOForalls] in HI.
    assert (Hm1 : FOtms_avoid [m] 0 1000) by avoid_tms.
    pose proof (PRI_inst n cores u0 V V G rho x (FOForalls xs A) env m w HE Hrho Hw Hm1
                  (le_n V) (Hmv m (or_introl eq_refl)) HI) as H1.
    replace (env ++ m :: ms) with ((env ++ [m]) ++ ms) by (rewrite <- app_assoc; reflexivity).
    cbn [rho_seq].
    replace (S (length env)) with (length (env ++ [m])) by (rewrite length_app; cbn; lia).
    apply IH; try assumption.
    + exact (EnvOK_snoc n V G env m w HE Hw Hm1 (Hmv m (or_introl eq_refl))).
    + intros z i Hz. rewrite length_app. cbn [length]. unfold rho_sub in Hz.
      destruct (Nat.eqb z x); [injection Hz as <-; lia | specialize (Hrho z i Hz); lia].
    + intros m' Hm'. apply Hnum. right. exact Hm'.
    + avoid_tms.
    + intros m' Hm'. apply Hmv. right. exact Hm'.
Qed.

(** ** Same formula, agreeing slots. *)

Definition SlotAgree (n : nat) (G : list FOFormula) (rho rho' : nat -> option nat)
    (env env' : list FOTerm) (z : nat) : Prop :=
  match rho z, rho' z with
  | Some i, Some j => FOPrH n G (FOEq (nth i env FOZero) (nth j env' FOZero))
  | None, None => True
  | _, _ => False
  end.

Lemma SlotAgree_weaken : forall n G G' rho rho' env env' z,
  (forall X, In X G -> In X G') ->
  SlotAgree n G rho rho' env env' z -> SlotAgree n G' rho rho' env env' z.
Proof.
  intros n G G' rho rho' env env' z Hinc H. unfold SlotAgree in *.
  destruct (rho z); destruct (rho' z); try exact H.
  exact (FOPrH_weaken n G G' _ Hinc H).
Qed.

Lemma CPrel_cpat_tm : forall t n G rho rho' env env',
  (forall z, FOin_tm z t = true -> SlotAgree n G rho rho' env env' z) ->
  CPrel n G env env' (cpat_tm rho t) (cpat_tm rho' t).
Proof.
  induction t as [y| |a IH|a IHa b IHb|a IHa b IHb]; intros n G rho rho' env env' H;
    cbn [cpat_tm].
  - specialize (H y ltac:(cbn [FOin_tm]; apply Nat.eqb_refl)). unfold SlotAgree in H.
    destruct (rho y) as [i|]; destruct (rho' y) as [j|]; try contradiction.
    + apply cpr_slot. exact H.
    + repeat (first [apply cpr_pair | apply cpr_lit]).
  - repeat (first [apply cpr_pair | apply cpr_lit]).
  - unfold tSuccP. apply cpr_pair; [apply cpr_lit|]. apply IH. intros z Hz. apply H. exact Hz.
  - unfold tPlusP. apply cpr_pair; [apply cpr_lit|]. apply cpr_pair.
    + apply IHa. intros z Hz. apply H. cbn [FOin_tm]. rewrite Hz. reflexivity.
    + apply IHb. intros z Hz. apply H. cbn [FOin_tm]. rewrite Hz. apply Bool.orb_true_r.
  - unfold tMultP. apply cpr_pair; [apply cpr_lit|]. apply cpr_pair.
    + apply IHa. intros z Hz. apply H. cbn [FOin_tm]. rewrite Hz. reflexivity.
    + apply IHb. intros z Hz. apply H. cbn [FOin_tm]. rewrite Hz. apply Bool.orb_true_r.
Qed.

Lemma CPrel_cpat_f : forall A n G rho rho' env env',
  (forall z, FOfree_in z A = true -> SlotAgree n G rho rho' env env' z) ->
  CPrel n G env env' (cpat_f rho A) (cpat_f rho' A).
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros n G rho rho' env env' H;
    cbn [cpat_f].
  - unfold pEqP. apply cpr_pair; [apply cpr_lit|]. apply cpr_pair.
    + apply CPrel_cpat_tm. intros z Hz. apply H. cbn [FOfree_in]. rewrite Hz. reflexivity.
    + apply CPrel_cpat_tm. intros z Hz. apply H. cbn [FOfree_in]. rewrite Hz.
      apply Bool.orb_true_r.
  - repeat (first [apply cpr_pair | apply cpr_lit]).
  - unfold pImpP. apply cpr_pair; [apply cpr_lit|]. apply cpr_pair.
    + apply IHB. intros z Hz. apply H. cbn [FOfree_in]. rewrite Hz. reflexivity.
    + apply IHC. intros z Hz. apply H. cbn [FOfree_in]. rewrite Hz. apply Bool.orb_true_r.
  - unfold pAllP. apply cpr_pair; [apply cpr_lit|]. apply cpr_pair; [apply cpr_lit|].
    apply IHB. intros z Hz. unfold SlotAgree, rho_hide.
    destruct (Nat.eqb_spec z y) as [->|Hzy]; [exact I|].
    apply H. cbn [FOfree_in]. rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz.
  - unfold pExP. apply cpr_pair; [apply cpr_lit|]. apply cpr_pair; [apply cpr_lit|].
    apply IHB. intros z Hz. unfold SlotAgree, rho_hide.
    destruct (Nat.eqb_spec z y) as [->|Hzy]; [exact I|].
    apply H. cbn [FOfree_in]. rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz.
Qed.

Lemma PRI_reslot : forall n cores u0 V G A rho rho' env env',
  (forall z, FOfree_in z A = true -> SlotAgree n G rho rho' env env' z) ->
  (forall t, In t (env ++ env') -> forall w, V <= w -> FOin_tm w t = false) ->
  FOtms_avoid (env ++ env') 0 1000 -> 1000 <= V ->
  PRI n cores u0 V G (cpat_f rho A) env -> PRI n cores u0 V G (cpat_f rho' A) env'.
Proof.
  intros n cores u0 V G A rho rho' env env' H Hab H0 HV HI.
  apply (PRI_conv n cores u0 V G (cpat_f rho A) (cpat_f rho' A) env env'); try assumption.
  intros G' Hinc. apply CPrel_cpat_f. intros z Hz. exact (SlotAgree_weaken n G G' _ _ _ _ z Hinc (H z Hz)).
Qed.

(** ** Instances of theorems. *)

Definition fvs (A : FOFormula) : list nat :=
  filter (fun x => FOfree_in x A) (seq 0 (S (FOvars_max A))).

Lemma fvs_spec : forall A x, In x (fvs A) <-> FOfree_in x A = true.
Proof.
  intros A x. unfold fvs. rewrite filter_In, in_seq. split; [intros [_ H]; exact H|].
  intros H. split; [|exact H]. split; [lia|].
  destruct (Nat.le_gt_cases x (FOvars_max A)) as [Hle|Hgt]; [lia|].
  rewrite (FOfree_in_above A x Hgt) in H. discriminate.
Qed.

Lemma fvs_nodup : forall A, NoDup (fvs A).
Proof. intros A. apply NoDup_filter, seq_NoDup. Qed.

Definition slotval (rho : nat -> option nat) (env : list FOTerm) (x : nat) : FOTerm :=
  match rho x with Some j => nth j env FOZero | None => FOZero end.

Lemma PRI_thm : forall n k V G xs A rho env,
  FOProvesTn 0 (FOForalls xs A) -> NoDup xs ->
  (forall x, FOfree_in x A = true -> In x xs) ->
  EnvOK n V G env ->
  (forall x, In x xs -> exists j, rho x = Some j /\ j < length env) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho A) env.
Proof.
  intros n k V G xs A rho env Hthm Hnd Hfv HE Hxs.
  pose proof HE as [[HG2 HS] [Henv0 [HV Henv]]].
  assert (Hms : forall m, In m (map (slotval rho env) xs) -> In m env).
  { intros m Hm. apply in_map_iff in Hm. destruct Hm as [x [<- Hx]].
    destruct (Hxs x Hx) as [j [Hj Hjl]]. unfold slotval. rewrite Hj. apply nth_In. exact Hjl. }
  pose proof (PRI_closed n k V G (FOForalls xs A) Hthm HV) as H0.
  pose proof (PRI_insts xs (map (slotval rho env) xs) n (FOPrCores k) (FOu0 k) V G
                (fun _ => None) [] A ltac:(apply length_map) (EnvOK_nil n V G env HE)
                ltac:(intros z i Hz; discriminate)
                ltac:(intros m Hm; apply in_map_iff in Hm; destruct Hm as [x [<- Hx]];
                      destruct (Hxs x Hx) as [j [Hj Hjl]]; unfold slotval; rewrite Hj;
                      exact (HS j Hjl))
                ltac:(intros t Ht; apply Henv0; exact (Hms t Ht))
                ltac:(intros m Hm; exact (Henv m (Hms m Hm))) H0) as H1.
  cbn [length app] in H1.
  refine (PRI_reslot n _ _ V G A _ rho _ env _ _ _ HV H1).
  - intros z Hz. unfold SlotAgree.
    destruct (In_nth_error xs z (Hfv z Hz)) as [i Hi].
    rewrite (rho_seq_nth xs 0 _ i z Hnd Hi). cbn [Nat.add].
    destruct (Hxs z (Hfv z Hz)) as [j [Hj _]]. rewrite Hj.
    rewrite (nth_error_nth (map (slotval rho env) xs) i FOZero (x := slotval rho env z))
      by (rewrite nth_error_map, Hi; reflexivity).
    unfold slotval. rewrite Hj. apply FOPrH_refl.
  - intros t Ht. apply in_app_or in Ht. destruct Ht as [Ht|Ht]; [exact (Henv t (Hms t Ht)) | exact (Henv t Ht)].
  - intros t Ht. apply in_app_or in Ht. destruct Ht as [Ht|Ht]; [exact (Henv0 t (Hms t Ht)) | exact (Henv0 t Ht)].
Qed.
