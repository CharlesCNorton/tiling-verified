From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40.
Open Scope fo_scope.

(** ** Substitution of a term that does not mention the variable. *)

Lemma FOin_tm_subst_closed : forall u x y t, FOin_tm x t = false ->
  FOin_tm x (FOsubst_t y t u) = true -> FOin_tm x u = true.
Proof.
  induction u as [z| |a IH|a IHa b IHb|a IHa b IHb]; intros x y t Ht H; cbn in H |- *.
  - destruct (Nat.eqb z y); [rewrite Ht in H; discriminate | exact H].
  - exact H.
  - exact (IH x y t Ht H).
  - apply Bool.orb_true_iff in H. apply Bool.orb_true_iff.
    destruct H as [H|H]; [left; exact (IHa x y t Ht H) | right; exact (IHb x y t Ht H)].
  - apply Bool.orb_true_iff in H. apply Bool.orb_true_iff.
    destruct H as [H|H]; [left; exact (IHa x y t Ht H) | right; exact (IHb x y t Ht H)].
Qed.

Lemma FOfree_in_subst_closed : forall A x y t, FOin_tm x t = false ->
  FOfree_in x (FOsubst_f y t A) = true -> FOfree_in x A = true.
Proof.
  induction A as [a b| |B IHB C IHC|z B IHB|z B IHB]; intros x y t Ht H; cbn in H |- *.
  - apply Bool.orb_true_iff in H. apply Bool.orb_true_iff.
    destruct H as [H|H];
      [left; exact (FOin_tm_subst_closed a x y t Ht H)
      | right; exact (FOin_tm_subst_closed b x y t Ht H)].
  - exact H.
  - apply Bool.orb_true_iff in H. apply Bool.orb_true_iff.
    destruct H as [H|H]; [left; exact (IHB x y t Ht H) | right; exact (IHC x y t Ht H)].
  - destruct (Nat.eqb z y); [exact H|]. cbn in H.
    destruct (Nat.eqb z x); [exact H | exact (IHB x y t Ht H)].
  - destruct (Nat.eqb z y); [exact H|]. cbn in H.
    destruct (Nat.eqb z x); [exact H | exact (IHB x y t Ht H)].
Qed.

Lemma FOsubst_ok_subst_closed : forall A x s y t, FOin_tm x t = false ->
  FOsubst_ok x s A = true -> FOsubst_ok x s (FOsubst_f y t A) = true.
Proof.
  induction A as [a b| |B IHB C IHC|z B IHB|z B IHB]; intros x s y t Ht H; cbn in H |- *.
  - reflexivity.
  - reflexivity.
  - apply Bool.andb_true_iff in H as [H1 H2].
    rewrite (IHB x s y t Ht H1), (IHC x s y t Ht H2). reflexivity.
  - destruct (Nat.eqb z y); [exact H|]. cbn.
    destruct (Nat.eqb z x); [reflexivity|].
    destruct (FOfree_in x (FOsubst_f y t B)) eqn:E; [|reflexivity].
    rewrite (FOfree_in_subst_closed B x y t Ht E) in H.
    apply Bool.andb_true_iff in H as [H1 H2]. rewrite H1, (IHB x s y t Ht H2). reflexivity.
  - destruct (Nat.eqb z y); [exact H|]. cbn.
    destruct (Nat.eqb z x); [reflexivity|].
    destruct (FOfree_in x (FOsubst_f y t B)) eqn:E; [|reflexivity].
    rewrite (FOfree_in_subst_closed B x y t Ht E) in H.
    apply Bool.andb_true_iff in H as [H1 H2]. rewrite H1, (IHB x s y t Ht H2). reflexivity.
Qed.

(** ** Substitution into a substituted term. *)

Lemma FOsubst_t_subst_into : forall u x y s t, FOin_tm x u = false ->
  FOsubst_t x s (FOsubst_t y t u) = FOsubst_t y (FOsubst_t x s t) u.
Proof.
  induction u as [z| |a IH|a IHa b IHb|a IHa b IHb]; intros x y s t Hu; cbn in Hu |- *.
  - destruct (Nat.eqb z y); [reflexivity|]. cbn. rewrite Hu. reflexivity.
  - reflexivity.
  - rewrite (IH x y s t Hu). reflexivity.
  - apply Bool.orb_false_iff in Hu as [H1 H2].
    rewrite (IHa x y s t H1), (IHb x y s t H2). reflexivity.
  - apply Bool.orb_false_iff in Hu as [H1 H2].
    rewrite (IHa x y s t H1), (IHb x y s t H2). reflexivity.
Qed.

Lemma FOsubst_f_all_self : forall x s A, FOsubst_f x s (FOForall x A) = FOForall x A.
Proof. intros x s A. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma FOsubst_f_ex_self : forall x s A, FOsubst_f x s (FOExists x A) = FOExists x A.
Proof. intros x s A. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma FOsubst_f_subst_into : forall A x y s t, FOfree_in x A = false ->
  FOsubst_ok y t A = true ->
  FOsubst_f x s (FOsubst_f y t A) = FOsubst_f y (FOsubst_t x s t) A.
Proof.
  induction A as [a b| |B IHB C IHC|z B IHB|z B IHB]; intros x y s t Hx Hok.
  - cbn in Hx. apply Bool.orb_false_iff in Hx as [H1 H2]. cbn.
    rewrite (FOsubst_t_subst_into a x y s t H1), (FOsubst_t_subst_into b x y s t H2).
    reflexivity.
  - reflexivity.
  - cbn in Hx, Hok. apply Bool.orb_false_iff in Hx as [H1 H2].
    apply Bool.andb_true_iff in Hok as [K1 K2].
    cbn [FOsubst_f]. rewrite (IHB x y s t H1 K1), (IHC x y s t H2 K2). reflexivity.
  - destruct (Nat.eqb_spec z y) as [Ezy|Ezy].
    + subst z. rewrite !FOsubst_f_all_self. exact (FOsubst_f_not_free _ x s Hx).
    + rewrite (FOsubst_f_all_ne y t z B Ezy), (FOsubst_f_all_ne y (FOsubst_t x s t) z B Ezy).
      cbn [FOsubst_ok] in Hok. rewrite (proj2 (Nat.eqb_neq z y) Ezy) in Hok.
      destruct (Nat.eqb_spec z x) as [Ezx|Ezx].
      * subst z. rewrite FOsubst_f_all_self. f_equal.
        destruct (FOfree_in y B) eqn:Ey.
        -- apply Bool.andb_true_iff in Hok as [K1 _]. apply Bool.negb_true_iff in K1.
           rewrite (FOsubst_t_not_in t x s K1). reflexivity.
        -- rewrite !(FOsubst_f_not_free B y) by exact Ey. reflexivity.
      * rewrite FOsubst_f_all_ne by exact Ezx. f_equal.
        cbn [FOfree_in] in Hx. rewrite (proj2 (Nat.eqb_neq z x) Ezx) in Hx.
        destruct (FOfree_in y B) eqn:Ey.
        -- apply Bool.andb_true_iff in Hok as [_ K2]. exact (IHB x y s t Hx K2).
        -- rewrite !(FOsubst_f_not_free B y) by exact Ey.
           exact (FOsubst_f_not_free B x s Hx).
  - destruct (Nat.eqb_spec z y) as [Ezy|Ezy].
    + subst z. rewrite !FOsubst_f_ex_self. exact (FOsubst_f_not_free _ x s Hx).
    + rewrite (FOsubst_f_ex_ne y t z B Ezy), (FOsubst_f_ex_ne y (FOsubst_t x s t) z B Ezy).
      cbn [FOsubst_ok] in Hok. rewrite (proj2 (Nat.eqb_neq z y) Ezy) in Hok.
      destruct (Nat.eqb_spec z x) as [Ezx|Ezx].
      * subst z. rewrite FOsubst_f_ex_self. f_equal.
        destruct (FOfree_in y B) eqn:Ey.
        -- apply Bool.andb_true_iff in Hok as [K1 _]. apply Bool.negb_true_iff in K1.
           rewrite (FOsubst_t_not_in t x s K1). reflexivity.
        -- rewrite !(FOsubst_f_not_free B y) by exact Ey. reflexivity.
      * rewrite FOsubst_f_ex_ne by exact Ezx. f_equal.
        cbn [FOfree_in] in Hx. rewrite (proj2 (Nat.eqb_neq z x) Ezx) in Hx.
        destruct (FOfree_in y B) eqn:Ey.
        -- apply Bool.andb_true_iff in Hok as [_ K2]. exact (IHB x y s t Hx K2).
        -- rewrite !(FOsubst_f_not_free B y) by exact Ey.
           exact (FOsubst_f_not_free B x s Hx).
Qed.

Lemma FOsubst_ok_subst_into : forall A x y s t, FOfree_in x A = false ->
  FOsubst_ok y t A = true -> FOsubst_ok y s A = true ->
  FOsubst_ok x s (FOsubst_f y t A) = true.
Proof.
  induction A as [a b| |B IHB C IHC|z B IHB|z B IHB]; intros x y s t Hx Hok Hoks.
  - reflexivity.
  - reflexivity.
  - cbn in Hx, Hok, Hoks. apply Bool.orb_false_iff in Hx as [H1 H2].
    apply Bool.andb_true_iff in Hok as [K1 K2]. apply Bool.andb_true_iff in Hoks as [L1 L2].
    cbn [FOsubst_f FOsubst_ok]. rewrite (IHB x y s t H1 K1 L1), (IHC x y s t H2 K2 L2).
    reflexivity.
  - destruct (Nat.eqb_spec z y) as [Ezy|Ezy].
    + subst z. rewrite FOsubst_f_all_self. exact (FOsubst_ok_not_free _ x s Hx).
    + rewrite (FOsubst_f_all_ne y t z B Ezy).
      cbn [FOsubst_ok] in Hok, Hoks |- *.
      rewrite (proj2 (Nat.eqb_neq z y) Ezy) in Hok, Hoks.
      destruct (Nat.eqb_spec z x) as [Ezx|Ezx]; [reflexivity|].
      cbn [FOfree_in] in Hx. rewrite (proj2 (Nat.eqb_neq z x) Ezx) in Hx.
      destruct (FOfree_in x (FOsubst_f y t B)) eqn:E; [|reflexivity].
      destruct (FOfree_in y B) eqn:Ey.
      * apply Bool.andb_true_iff in Hok as [_ K2]. apply Bool.andb_true_iff in Hoks as [L1 L2].
        rewrite L1. exact (IHB x y s t Hx K2 L2).
      * rewrite (FOsubst_f_not_free B y t Ey), Hx in E. discriminate E.
  - destruct (Nat.eqb_spec z y) as [Ezy|Ezy].
    + subst z. rewrite FOsubst_f_ex_self. exact (FOsubst_ok_not_free _ x s Hx).
    + rewrite (FOsubst_f_ex_ne y t z B Ezy).
      cbn [FOsubst_ok] in Hok, Hoks |- *.
      rewrite (proj2 (Nat.eqb_neq z y) Ezy) in Hok, Hoks.
      destruct (Nat.eqb_spec z x) as [Ezx|Ezx]; [reflexivity|].
      cbn [FOfree_in] in Hx. rewrite (proj2 (Nat.eqb_neq z x) Ezx) in Hx.
      destruct (FOfree_in x (FOsubst_f y t B)) eqn:E; [|reflexivity].
      destruct (FOfree_in y B) eqn:Ey.
      * apply Bool.andb_true_iff in Hok as [_ K2]. apply Bool.andb_true_iff in Hoks as [L1 L2].
        rewrite L1. exact (IHB x y s t Hx K2 L2).
      * rewrite (FOsubst_f_not_free B y t Ey), Hx in E. discriminate E.
Qed.

(** ** Substitutions at distinct variables commute. *)

Lemma FOsubst_t_comm_gen : forall u x y s t, x <> y -> FOin_tm x t = false ->
  FOin_tm y s = false ->
  FOsubst_t x s (FOsubst_t y t u) = FOsubst_t y t (FOsubst_t x s u).
Proof.
  induction u as [z| |a IH|a IHa b IHb|a IHa b IHb]; intros x y s t Hxy Ht Hs.
  - cbn [FOsubst_t].
    destruct (Nat.eqb_spec z y) as [Ezy|Ezy]; destruct (Nat.eqb_spec z x) as [Ezx|Ezx].
    + lia.
    + subst z. rewrite (FOsubst_t_not_in t x s Ht), FOsubst_t_var_eq'. reflexivity.
    + subst z. rewrite (FOsubst_t_not_in s y t Hs), FOsubst_t_var_eq'. reflexivity.
    + rewrite !FOsubst_t_var_ne by assumption. reflexivity.
  - reflexivity.
  - cbn. rewrite (IH x y s t Hxy Ht Hs). reflexivity.
  - cbn. rewrite (IHa x y s t Hxy Ht Hs), (IHb x y s t Hxy Ht Hs). reflexivity.
  - cbn. rewrite (IHa x y s t Hxy Ht Hs), (IHb x y s t Hxy Ht Hs). reflexivity.
Qed.

Lemma FOsubst_f_comm_gen : forall A x y s t, x <> y -> FOin_tm x t = false ->
  FOin_tm y s = false ->
  FOsubst_f x s (FOsubst_f y t A) = FOsubst_f y t (FOsubst_f x s A).
Proof.
  induction A as [a b| |B IHB C IHC|z B IHB|z B IHB]; intros x y s t Hxy Ht Hs.
  - cbn. rewrite !(FOsubst_t_comm_gen _ x y s t Hxy Ht Hs). reflexivity.
  - reflexivity.
  - cbn [FOsubst_f]. rewrite (IHB x y s t Hxy Ht Hs), (IHC x y s t Hxy Ht Hs). reflexivity.
  - destruct (Nat.eqb_spec z y) as [Ezy|Ezy]; destruct (Nat.eqb_spec z x) as [Ezx|Ezx].
    + lia.
    + subst z. rewrite FOsubst_f_all_self, (FOsubst_f_all_ne x s y) by exact Ezx.
      rewrite FOsubst_f_all_self. reflexivity.
    + subst z. rewrite FOsubst_f_all_self, (FOsubst_f_all_ne y t x) by exact Ezy.
      rewrite FOsubst_f_all_self. reflexivity.
    + rewrite !FOsubst_f_all_ne by assumption. rewrite (IHB x y s t Hxy Ht Hs). reflexivity.
  - destruct (Nat.eqb_spec z y) as [Ezy|Ezy]; destruct (Nat.eqb_spec z x) as [Ezx|Ezx].
    + lia.
    + subst z. rewrite FOsubst_f_ex_self, (FOsubst_f_ex_ne x s y) by exact Ezx.
      rewrite FOsubst_f_ex_self. reflexivity.
    + subst z. rewrite FOsubst_f_ex_self, (FOsubst_f_ex_ne y t x) by exact Ezy.
      rewrite FOsubst_f_ex_self. reflexivity.
    + rewrite !FOsubst_f_ex_ne by assumption. rewrite (IHB x y s t Hxy Ht Hs). reflexivity.
Qed.

(** ** The provability matrix under substitution. *)

Lemma FOsubst_ok_PRMAT1 : forall cores s, FOtm_avoid s 2 252 ->
  FOsubst_ok 1 s (FOPRMAT cores) = true.
Proof.
  intros cores s Hs. unfold FOPRMAT. rewrite FOPRDER_p.
  do 16 (apply FOsubst_ok_ex; [apply Hs; lia|]).
  apply FOsubst_ok_PRDERp. apply (FOtm_avoid_sub s 2 252); [exact Hs | lia | lia].
Qed.

Lemma FOPRu_var1 : forall cores u0,
  FOPRu cores u0 (FOVar 1) = FOsubst_f 0 (FOnumeral u0) (FOPRMAT cores).
Proof. intros cores u0. unfold FOPRu, FOPRMATx, FOPRMAT. rewrite FOPRDER_p. reflexivity. Qed.

Definition PRuOK (c : FOTerm) : Prop := c = FOVar 1 \/ FOtm_avoid c 1 18.

Lemma FOPRu_as_subst : forall cores u0 c, PRuOK c ->
  FOPRu cores u0 c = FOsubst_f 0 (FOnumeral u0) (FOsubst_f 1 c (FOPRMAT cores)).
Proof.
  intros cores u0 c [->|Hc].
  - rewrite FOsubst_f_id. apply FOPRu_var1.
  - unfold FOPRu. rewrite FOsubst_f_PRMAT1 by exact Hc. reflexivity.
Qed.

Lemma FOsubst_f_PRu_gen : forall cores u0 x s c, 2 <= x -> FOin_tm 0 s = false ->
  FOtm_avoid c 2 252 -> PRuOK c -> PRuOK (FOsubst_t x s c) ->
  FOsubst_f x s (FOPRu cores u0 c) = FOPRu cores u0 (FOsubst_t x s c).
Proof.
  intros cores u0 x s c Hx Hs Hc Hc1 Hc2.
  rewrite (FOPRu_as_subst cores u0 c Hc1), (FOPRu_as_subst cores u0 _ Hc2).
  rewrite (FOsubst_f_comm_gen _ x 0 s (FOnumeral u0)) by (lia || apply FOin_tm_numeral || exact Hs).
  rewrite (FOsubst_f_subst_into (FOPRMAT cores) x 1 s c);
    [reflexivity | apply FOPRMAT_free; lia | apply FOsubst_ok_PRMAT1; exact Hc].
Qed.

Lemma FOsubst_f_PRu : forall cores u0 x s c, 2 <= x ->
  FOtms_avoid [s; c] 0 252 ->
  FOsubst_f x s (FOPRu cores u0 c) = FOPRu cores u0 (FOsubst_t x s c).
Proof.
  intros cores u0 x s c Hx Hav.
  apply FOsubst_f_PRu_gen; [exact Hx | fr_tm | avoid_tm | right; avoid_tm |].
  right. intros w Hw1 Hw2. destruct (FOin_tm w (FOsubst_t x s c)) eqn:E; [|reflexivity].
  destruct (FOin_tm x c) eqn:Ex.
  - exfalso. assert (Hs : FOin_tm w s = false) by fr_tm.
    assert (Hc : FOin_tm w c = false) by fr_tm.
    rewrite (FOin_tm_subst_closed c w x s Hs E) in Hc. discriminate.
  - rewrite (FOsubst_t_not_in c x s Ex) in E. assert (Hc : FOin_tm w c = false) by fr_tm.
    rewrite Hc in E. discriminate.
Qed.

Lemma FOsubst_f_PRu_var1 : forall cores u0 s, FOtm_avoid s 0 18 ->
  FOsubst_f 1 s (FOPRu cores u0 (FOVar 1)) = FOPRu cores u0 s.
Proof.
  intros cores u0 s Hs. rewrite FOPRu_var1.
  rewrite (FOsubst_f_comm_gen _ 1 0 s (FOnumeral u0))
    by first [lia | apply FOin_tm_numeral | apply Hs; lia].
  rewrite FOsubst_f_PRMAT1 by (apply (FOtm_avoid_sub s 0 18); [exact Hs | lia | lia]).
  reflexivity.
Qed.

Lemma FOsubst_ok_PRu : forall cores u0 x s c, 2 <= x ->
  FOtm_avoid c 2 252 -> PRuOK c -> FOtm_avoid s 2 252 ->
  FOsubst_ok x s (FOPRu cores u0 c) = true.
Proof.
  intros cores u0 x s c Hx Hc Hc1 Hs.
  rewrite (FOPRu_as_subst cores u0 c Hc1).
  apply FOsubst_ok_subst_closed; [apply FOin_tm_numeral|].
  apply FOsubst_ok_subst_into;
    [apply FOPRMAT_free; lia | apply FOsubst_ok_PRMAT1; exact Hc
    | apply FOsubst_ok_PRMAT1; exact Hs].
Qed.

Lemma FOsubst_ok_PRu_var1 : forall cores u0 s, FOtm_avoid s 2 252 ->
  FOsubst_ok 1 s (FOPRu cores u0 (FOVar 1)) = true.
Proof.
  intros cores u0 s Hs. rewrite FOPRu_var1.
  apply FOsubst_ok_subst_closed; [apply FOin_tm_numeral | apply FOsubst_ok_PRMAT1; exact Hs].
Qed.

Lemma FOfree_in_PRu_var1 : forall cores u0 w, w <> 1 ->
  FOfree_in w (FOPRu cores u0 (FOVar 1)) = false.
Proof.
  intros cores u0 w Hw. rewrite FOPRu_var1, FOsubst_f_num, FOfree_in_subst_num.
  destruct (Nat.eqb_spec w 0) as [->|Hw0]; [reflexivity|].
  apply FOPRMAT_free. lia.
Qed.

(** ** Provable instances as a formula.

    [PRIf cores u0 B0 env p]: every code of [p] over [env], described
    at base [B0], is provable. *)

Definition PRIf (cores : list nat) (u0 B0 : nat) (env : list FOTerm) (p : CPat) : FOFormula :=
  FOForall 1 (FOImplF (FOPATF B0 env p (FOVar 1)) (FOPRu cores u0 (FOVar 1))).

Lemma FOfree_in_PRIf : forall cores u0 B0 env p w, 2 <= B0 ->
  FOtms_avoid env w (S w) -> FOfree_in w (PRIf cores u0 B0 env p) = false.
Proof.
  intros cores u0 B0 env p w HB Hav. unfold PRIf. cbn [FOfree_in].
  destruct (Nat.eqb_spec 1 w) as [E|E]; [reflexivity|].
  apply Bool.orb_false_iff. split.
  - destruct (Nat.lt_ge_cases w 2) as [Hw|Hw].
    + apply FOfree_in_PATF_lo; [lia|]. apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
      exact Hav.
    + apply FOfree_in_PATF_any; [lia|]. apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
      exact Hav.
  - apply FOfree_in_PRu_var1. lia.
Qed.

Lemma FOsubst_f_PRIf : forall cores u0 B0 env p x s, 2 <= x -> x < B0 ->
  FOsubst_f x s (PRIf cores u0 B0 env p) = PRIf cores u0 B0 (map (FOsubst_t x s) env) p.
Proof.
  intros cores u0 B0 env p x s Hx HB. unfold PRIf.
  rewrite FOsubst_f_all_ne by lia. rewrite FOsubst_f_impl, FOsubst_f_PATF by lia.
  rewrite FOsubst_t_var_ne by lia.
  rewrite (FOsubst_f_not_free (FOPRu cores u0 (FOVar 1))) by (apply FOfree_in_PRu_var1; lia).
  reflexivity.
Qed.

Lemma FOsubst_ok_PRIf : forall cores u0 B0 env p x s, 2 <= x ->
  FOin_tm 1 s = false -> FOtm_avoid s B0 (B0 + cpat_span p) ->
  FOsubst_ok x s (PRIf cores u0 B0 env p) = true.
Proof.
  intros cores u0 B0 env p x s Hx H1 Hs. unfold PRIf.
  apply FOsubst_ok_all; [exact H1|]. apply FOsubst_ok_impl; [apply FOsubst_ok_PATF; exact Hs|].
  apply FOsubst_ok_not_free. apply FOfree_in_PRu_var1. lia.
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

(** ** Using an internal provable-instance fact. *)

Lemma FOPrH_prif_elim : forall n G cores u0 B0 env p c,
  FOPrH n G (PRIf cores u0 B0 env p) -> FOPrH n G (FOPATF B0 env p c) ->
  2 <= B0 -> FOtms_avoid env 1 2 -> FOtm_avoid c B0 (B0 + cpat_span p) ->
  FOtm_avoid c 0 252 ->
  FOPrH n G (FOPRu cores u0 c).
Proof.
  intros n G cores u0 B0 env p c H Hp HB Henv Hc Hc0.
  assert (Hc18 : FOtm_avoid c 0 18) by (apply (FOtm_avoid_sub c 0 252); [exact Hc0 | lia | lia]).
  assert (Hc2 : FOtm_avoid c 2 252) by (apply (FOtm_avoid_sub c 0 252); [exact Hc0 | lia | lia]).
  unfold PRIf in H.
  apply (FOPrH_inst n G 1 c) in H;
    [| apply FOsubst_ok_impl; [apply FOsubst_ok_PATF; exact Hc |
                               apply FOsubst_ok_PRu_var1; exact Hc2]].
  rewrite FOsubst_f_impl, FOsubst_f_PATF, FOsubst_t_var_eq', FOsubst_f_PRu_var1 in H
    by first [lia | exact Hc18].
  rewrite (FOsubst_map_avoid 1 c env) in H by (intros t Ht; apply (Henv t Ht); lia).
  exact (FOPrH_mp _ _ _ _ H Hp).
Qed.
