(******************************************************************************)
(*                                                                            *)
(*           Parametric Provability: Bypassing the Loebian Obstacle           *)
(*                                                                            *)
(*     Part 5 of 9. Substitution and transfer through the checker's builders. *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal.
Open Scope fo_scope.

(** ** Reasoning about folded formulas.

    The rules below take formulas as parameters, so they apply to the
    checker's builders without unfolding them.  Monotonicity is stated
    as a derivable implication in a fixed context. *)

Ltac nat_eqb_simpl :=
  repeat match goal with
  | |- context [Nat.eqb ?a ?b] =>
      first [ rewrite (proj2 (Nat.eqb_eq a b)) by lia
            | rewrite (proj2 (Nat.eqb_neq a b)) by lia ]
  end.

Lemma FOPrH_weak_app : forall n G L A, FOPrH n G A -> FOPrH n (G ++ L) A.
Proof.
  intros n G L A H.
  apply (FOPrH_weaken n G); [intros X Hin; apply in_or_app; left; exact Hin | exact H].
Qed.

Lemma FOPrH_last : forall n G A, FOPrH n (G ++ [A]) A.
Proof. intros n G A. apply FOPrH_assum. apply in_or_app. right. left. reflexivity. Qed.

Lemma FOPrH_imp_refl : forall n G A, FOPrH n G (A .-> A).
Proof. intros n G A. apply FOPrH_intro. apply FOPrH_last. Qed.

Lemma FOPrH_imp_trans : forall n G A B C,
  FOPrH n G (A .-> B) -> FOPrH n G (B .-> C) -> FOPrH n G (A .-> C).
Proof.
  intros n G A B C H1 H2. apply FOPrH_intro.
  exact (FOPrH_mp _ _ _ _ (FOPrH_weak_app n G _ _ H2)
           (FOPrH_mp _ _ _ _ (FOPrH_weak_app n G _ _ H1) (FOPrH_last n G A))).
Qed.

Lemma FOPrH_and_mono : forall n G A A' B B',
  FOPrH n G (A .-> A') -> FOPrH n G (B .-> B') ->
  FOPrH n G (FOAnd A B .-> FOAnd A' B').
Proof.
  intros n G A A' B B' HA HB. apply FOPrH_intro.
  pose proof (FOPrH_last n G (FOAnd A B)) as H.
  apply FOPrH_and_intro.
  - exact (FOPrH_mp _ _ _ _ (FOPrH_weak_app n G _ _ HA) (FOPrH_and_l _ _ _ _ H)).
  - exact (FOPrH_mp _ _ _ _ (FOPrH_weak_app n G _ _ HB) (FOPrH_and_r _ _ _ _ H)).
Qed.

Lemma FOPrH_or_mono : forall n G A A' B B',
  FOPrH n G (A .-> A') -> FOPrH n G (B .-> B') ->
  FOPrH n G (FOOr A B .-> FOOr A' B').
Proof.
  intros n G A A' B B' HA HB. apply FOPrH_intro.
  apply (FOPrH_or_elim n (G ++ [FOOr A B]) A B); [apply FOPrH_last | |].
  - apply FOPrH_or_intro_l.
    exact (FOPrH_mp _ _ _ _ (FOPrH_weak_app n _ _ _ (FOPrH_weak_app n G _ _ HA))
             (FOPrH_last _ _ _)).
  - apply FOPrH_or_intro_r.
    exact (FOPrH_mp _ _ _ _ (FOPrH_weak_app n _ _ _ (FOPrH_weak_app n G _ _ HB))
             (FOPrH_last _ _ _)).
Qed.

(** The bound conjunct of the bounded quantifiers. *)

Definition FOltv (v : nat) (t : FOTerm) : FOFormula :=
  FOExists (S v) (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) t).

Lemma FOBexC_ltv : forall v t A, FOBexC v t A = FOExists v (FOAnd (FOltv v t) A).
Proof. reflexivity. Qed.

Lemma FOBallC_ltv : forall v t A, FOBallC v t A = FOForall v (FOImplF (FOltv v t) A).
Proof. reflexivity. Qed.

Lemma FOfree_in_ex_self : forall v A, FOfree_in v (FOExists v A) = false.
Proof. intros v A. cbn [FOfree_in]. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma FOfree_in_all_self : forall v A, FOfree_in v (FOForall v A) = false.
Proof. intros v A. cbn [FOfree_in]. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma FOfree_ctx_app1 : forall v G A,
  FOfree_ctx v G -> FOfree_in v A = false -> FOfree_ctx v (G ++ [A]).
Proof.
  intros v G A HG HA H Hin. apply in_app_or in Hin.
  destruct Hin as [Hin|[<-|[]]]; [exact (HG H Hin) | exact HA].
Qed.

Lemma FOPrH_bex_mono : forall n G v t t' A A',
  FOfree_ctx v G ->
  FOPrH n G (FOltv v t .-> FOltv v t') ->
  FOPrH n G (FOltv v t .-> A .-> A') ->
  FOPrH n G (FOBexC v t A .-> FOBexC v t' A').
Proof.
  intros n G v t t' A A' Hv Ht HA. apply FOPrH_intro.
  change (FOPrH n (G ++ [FOExists v (FOAnd (FOltv v t) A)])
            (FOExists v (FOAnd (FOltv v t') A'))).
  apply (FOPrH_ex_elim n (G ++ [FOExists v (FOAnd (FOltv v t) A)]) v (FOAnd (FOltv v t) A));
    [apply FOfree_ctx_app1; [exact Hv | apply FOfree_in_ex_self]
    | apply FOfree_in_ex_self | apply FOPrH_last |].
  apply (FOPrH_ex_intro _ _ v (FOVar v)); [apply FOsubst_ok_var_self|].
  rewrite FOsubst_f_id.
  pose proof (FOPrH_last n (G ++ [FOExists v (FOAnd (FOltv v t) A)])
                (FOAnd (FOltv v t) A)) as H.
  apply FOPrH_and_intro.
  - exact (FOPrH_mp _ _ _ _ (FOPrH_weak_app n _ _ _ (FOPrH_weak_app n G _ _ Ht))
             (FOPrH_and_l _ _ _ _ H)).
  - exact (FOPrH_mp _ _ _ _
             (FOPrH_mp _ _ _ _ (FOPrH_weak_app n _ _ _ (FOPrH_weak_app n G _ _ HA))
                (FOPrH_and_l _ _ _ _ H))
             (FOPrH_and_r _ _ _ _ H)).
Qed.

Lemma FOPrH_ball_mono : forall n G v t t' A A',
  FOfree_ctx v G ->
  FOPrH n G (FOltv v t' .-> FOltv v t) ->
  FOPrH n G (FOltv v t' .-> A .-> A') ->
  FOPrH n G (FOBallC v t A .-> FOBallC v t' A').
Proof.
  intros n G v t t' A A' Hv Ht HA. apply FOPrH_intro.
  change (FOPrH n (G ++ [FOForall v (FOImplF (FOltv v t) A)])
            (FOForall v (FOImplF (FOltv v t') A'))).
  apply FOPrH_all_intro; [apply FOfree_ctx_app1; [exact Hv | apply FOfree_in_all_self]|].
  apply FOPrH_intro.
  set (G1 := G ++ [FOForall v (FOImplF (FOltv v t) A)]).
  pose proof (FOPrH_all_elim n G1 v (FOVar v) _ (FOsubst_ok_var_self _ v)
                (FOPrH_last n G _)) as H1.
  rewrite FOsubst_f_id in H1.
  pose proof (FOPrH_last n G1 (FOltv v t')) as H2.
  apply (FOPrH_mp _ _ A A').
  - exact (FOPrH_mp _ _ _ _ (FOPrH_weak_app n G1 _ _ (FOPrH_weak_app n G _ _ HA)) H2).
  - apply (FOPrH_mp _ _ (FOltv v t) A); [exact (FOPrH_weak_app n G1 _ _ H1)|].
    exact (FOPrH_mp _ _ _ _ (FOPrH_weak_app n G1 _ _ (FOPrH_weak_app n G _ _ Ht)) H2).
Qed.

(** Renaming the variable of a bounded existential. *)

Lemma FOsubst_f_ltv_self : forall w w' t,
  FOin_tm w t = false ->
  FOsubst_f w (FOVar w') (FOltv w t) =
  FOExists (S w) (FOEq (FOPlus (FOVar w') (FOSucc (FOVar (S w)))) t).
Proof.
  intros w w' t Ht. unfold FOltv. cbn [FOsubst_f FOsubst_t].
  nat_eqb_simpl. rewrite (FOsubst_t_not_in t w (FOVar w') Ht). reflexivity.
Qed.

Lemma FOPrH_bex_rename : forall n G w w' t A,
  FOfree_ctx w' G -> w' <> w -> w' <> S w ->
  FOin_tm w t = false -> FOin_tm (S w) t = false ->
  FOin_tm w' t = false -> FOin_tm (S w') t = false ->
  FOfree_in w' A = false -> FOsubst_ok w (FOVar w') A = true ->
  FOPrH n G (FOBexC w t A .-> FOBexC w' t (FOsubst_f w (FOVar w') A)).
Proof.
  intros n G w w' t A HG Hw1 Hw2 Ht1 Ht2 Ht3 Ht4 HA Hok.
  apply FOPrH_intro.
  set (A' := FOsubst_f w (FOVar w') A).
  change (FOPrH n (G ++ [FOExists w (FOAnd (FOltv w t) A)])
            (FOExists w' (FOAnd (FOltv w' t) A'))).
  assert (Hlt : FOfree_in w' (FOltv w t) = false).
  { unfold FOltv. cbn [FOfree_in FOin_tm]. nat_eqb_simpl. rewrite Ht3. reflexivity. }
  assert (HAnd : FOfree_in w' (FOAnd (FOltv w t) A) = false).
  { rewrite FOfree_in_FOAnd, Hlt, HA. reflexivity. }
  apply (FOPrH_ex_elim_fresh n (G ++ [FOExists w (FOAnd (FOltv w t) A)]) w w'
           (FOAnd (FOltv w t) A)).
  - apply FOfree_ctx_app1; [exact HG|].
    cbn [FOfree_in]. nat_eqb_simpl. exact HAnd.
  - apply FOfree_in_ex_self.
  - exact HAnd.
  - unfold FOAnd, FONeg. cbn [FOsubst_ok]. rewrite Hok.
    unfold FOltv. cbn [FOsubst_ok FOfree_in FOin_tm]. nat_eqb_simpl.
    cbn. try rewrite Bool.andb_true_r. reflexivity.
  - apply FOPrH_last.
  - assert (E : FOsubst_f w (FOVar w') (FOAnd (FOltv w t) A)
                = FOAnd (FOExists (S w) (FOEq (FOPlus (FOVar w') (FOSucc (FOVar (S w)))) t)) A').
    { unfold FOAnd, FONeg. cbn [FOsubst_f].
      rewrite (FOsubst_f_ltv_self w w' t Ht1). reflexivity. }
    rewrite E.
    apply (FOPrH_ex_intro _ _ w' (FOVar w')); [apply FOsubst_ok_var_self|].
    rewrite FOsubst_f_id.
    set (G2 := (G ++ [FOExists w (FOAnd (FOltv w t) A)]) ++
               [FOAnd (FOExists (S w) (FOEq (FOPlus (FOVar w') (FOSucc (FOVar (S w)))) t)) A']).
    pose proof (FOPrH_last n (G ++ [FOExists w (FOAnd (FOltv w t) A)])
                  (FOAnd (FOExists (S w) (FOEq (FOPlus (FOVar w') (FOSucc (FOVar (S w)))) t)) A'))
      as H.
    fold G2 in H.
    apply FOPrH_and_intro; [|exact (FOPrH_and_r _ _ _ _ H)].
    pose proof (FOPr_ex_rename n (S w) (S w')
                  (FOEq (FOPlus (FOVar w') (FOSucc (FOVar (S w)))) t)) as R.
    assert (R1 : FOfree_in (S w') (FOEq (FOPlus (FOVar w') (FOSucc (FOVar (S w)))) t) = false).
    { cbn [FOfree_in FOin_tm]. nat_eqb_simpl. rewrite Ht4. reflexivity. }
    specialize (R R1 eq_refl).
    assert (R2 : FOsubst_f (S w) (FOVar (S w'))
                   (FOEq (FOPlus (FOVar w') (FOSucc (FOVar (S w)))) t)
                 = FOEq (FOPlus (FOVar w') (FOSucc (FOVar (S w')))) t).
    { cbn [FOsubst_f FOsubst_t]. nat_eqb_simpl.
      rewrite (FOsubst_t_not_in t (S w) (FOVar (S w')) Ht2). reflexivity. }
    rewrite R2 in R.
    exact (FOPrH_mp _ _ _ _ (FOPrH_thm n G2 _ R) (FOPrH_and_l _ _ _ _ H)).
Qed.

Lemma FOPrH_imp_weaken : forall n G P A B,
  FOPrH n G (A .-> B) -> FOPrH n G (P .-> A .-> B).
Proof. intros n G P A B H. apply FOPrH_intro. exact (FOPrH_weak_app n G [P] _ H). Qed.

(** Variables kept out of an interval. *)

Definition FOtm_avoid (t : FOTerm) (lo hi : nat) : Prop :=
  forall w, lo <= w -> w < hi -> FOin_tm w t = false.

Definition FOctx_avoid (G : list FOFormula) (lo hi : nat) : Prop :=
  forall w, lo <= w -> w < hi -> FOfree_ctx w G.

Ltac in_tm_simpl :=
  repeat match goal with
  | Ha : FOtm_avoid ?t ?lo ?hi |- context [FOin_tm ?w ?t] =>
      rewrite (Ha w ltac:(lia) ltac:(lia))
  end.

Ltac subst_t_simpl :=
  repeat match goal with
  | Ha : FOtm_avoid ?t ?lo ?hi |- context [FOsubst_t ?w ?s ?t] =>
      rewrite (FOsubst_t_not_in t w s (Ha w ltac:(lia) ltac:(lia)))
  end.

(** ** Moving the binders of the beta formula. *)

Definition FObetaBody (v : nat) (c d i x : FOTerm) : FOFormula :=
  FOAnd (FOEq c (FOPlus (FOMult (FOVar v) (FOSucc (FOMult d (FOSucc i)))) x))
        (FOBexC (S (S v)) (FOSucc (FOMult d (FOSucc i)))
           (FOEq (FOPlus x (FOSucc (FOVar (S (S v))))) (FOSucc (FOMult d (FOSucc i))))).

Lemma FObetaF_body : forall v c d i x,
  FObetaF v c d i x = FOBexC v (FOSucc c) (FObetaBody v c d i x).
Proof. reflexivity. Qed.

Lemma FOPrH_beta_rebase : forall n G v v' c d i x,
  v + 4 <= v' \/ v' + 4 <= v ->
  FOctx_avoid G v' (v' + 4) ->
  FOtm_avoid c v (v + 4) -> FOtm_avoid c v' (v' + 4) ->
  FOtm_avoid d v (v + 4) -> FOtm_avoid d v' (v' + 4) ->
  FOtm_avoid i v (v + 4) -> FOtm_avoid i v' (v' + 4) ->
  FOtm_avoid x v (v + 4) -> FOtm_avoid x v' (v' + 4) ->
  FOPrH n G (FObetaF v c d i x .-> FObetaF v' c d i x).
Proof.
  intros n G v v' c d i x Hvv HG Hc Hc' Hd Hd' Hi Hi' Hx Hx'.
  set (N := FOSucc (FOMult d (FOSucc i))).
  set (MB := FOAnd (FOEq c (FOPlus (FOMult (FOVar v') N) x))
                   (FOBexC (S (S v)) N (FOEq (FOPlus x (FOSucc (FOVar (S (S v))))) N))).
  assert (E1 : FOsubst_f v (FOVar v') (FObetaBody v c d i x) = MB).
  { unfold MB, N, FObetaBody, FOBexC, FOAnd, FONeg.
    cbn [FOsubst_f FOsubst_t]. nat_eqb_simpl. subst_t_simpl. reflexivity. }
  assert (F1 : FOfree_in v' (FObetaBody v c d i x) = false).
  { unfold FObetaBody, FOBexC, FOAnd, FONeg.
    cbn [FOfree_in FOin_tm]. nat_eqb_simpl. in_tm_simpl. reflexivity. }
  assert (O1 : FOsubst_ok v (FOVar v') (FObetaBody v c d i x) = true).
  { unfold FObetaBody, FOBexC, FOAnd, FONeg.
    cbn [FOsubst_ok FOfree_in FOin_tm]. nat_eqb_simpl. in_tm_simpl. reflexivity. }
  pose proof (FOPrH_bex_rename n G v v' (FOSucc c) (FObetaBody v c d i x)
                (HG v' ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)
                ltac:(cbn [FOin_tm]; in_tm_simpl; reflexivity)
                ltac:(cbn [FOin_tm]; in_tm_simpl; reflexivity)
                ltac:(cbn [FOin_tm]; in_tm_simpl; reflexivity)
                ltac:(cbn [FOin_tm]; in_tm_simpl; reflexivity)
                F1 O1) as R1.
  rewrite E1 in R1.
  rewrite !FObetaF_body.
  apply (FOPrH_imp_trans n G _ _ _ R1).
  apply FOPrH_bex_mono; [exact (HG v' ltac:(lia) ltac:(lia)) | apply FOPrH_imp_refl |].
  apply FOPrH_imp_weaken.
  unfold MB, FObetaBody. fold N.
  apply FOPrH_and_mono; [apply FOPrH_imp_refl|].
  set (E2 := FOEq (FOPlus x (FOSucc (FOVar (S (S v))))) N).
  assert (E3 : FOsubst_f (S (S v)) (FOVar (S (S v'))) E2
               = FOEq (FOPlus x (FOSucc (FOVar (S (S v'))))) N).
  { unfold E2, N. cbn [FOsubst_f FOsubst_t]. nat_eqb_simpl. subst_t_simpl. reflexivity. }
  pose proof (FOPrH_bex_rename n G (S (S v)) (S (S v')) N E2
                (HG (S (S v')) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)
                ltac:(unfold N; cbn [FOin_tm]; in_tm_simpl; reflexivity)
                ltac:(unfold N; cbn [FOin_tm]; in_tm_simpl; reflexivity)
                ltac:(unfold N; cbn [FOin_tm]; in_tm_simpl; reflexivity)
                ltac:(unfold N; cbn [FOin_tm]; in_tm_simpl; reflexivity)
                ltac:(unfold E2, N; cbn [FOfree_in FOin_tm]; nat_eqb_simpl; in_tm_simpl;
                      reflexivity)
                eq_refl) as R2.
  rewrite E3 in R2. exact R2.
Qed.

(** ** Substitution through the checker's builders.

    A variable below every binder of a builder is replaced inside the
    builder's arguments only.  The equations are collected in the
    rewrite database [fosubst], each builder's equation proved from
    those of its parts. *)

Lemma FOsubst_t_zero : forall x s, FOsubst_t x s FOZero = FOZero.
Proof. reflexivity. Qed.
Lemma FOsubst_t_succ : forall x s a, FOsubst_t x s (FOSucc a) = FOSucc (FOsubst_t x s a).
Proof. reflexivity. Qed.
Lemma FOsubst_t_plus : forall x s a b,
  FOsubst_t x s (FOPlus a b) = FOPlus (FOsubst_t x s a) (FOsubst_t x s b).
Proof. reflexivity. Qed.
Lemma FOsubst_t_mult : forall x s a b,
  FOsubst_t x s (FOMult a b) = FOMult (FOsubst_t x s a) (FOsubst_t x s b).
Proof. reflexivity. Qed.
Lemma FOsubst_t_var_ne : forall x s y, y <> x -> FOsubst_t x s (FOVar y) = FOVar y.
Proof. intros x s y H. cbn. rewrite (proj2 (Nat.eqb_neq y x) H). reflexivity. Qed.
Lemma FOsubst_t_numeral : forall x s k, FOsubst_t x s (FOnumeral k) = FOnumeral k.
Proof. intros x s k. induction k as [|k IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma FOsubst_f_eq : forall x s a b,
  FOsubst_f x s (FOEq a b) = FOEq (FOsubst_t x s a) (FOsubst_t x s b).
Proof. reflexivity. Qed.
Lemma FOsubst_f_false : forall x s, FOsubst_f x s FOFalseF = FOFalseF.
Proof. reflexivity. Qed.
Lemma FOsubst_f_impl : forall x s A B,
  FOsubst_f x s (FOImplF A B) = FOImplF (FOsubst_f x s A) (FOsubst_f x s B).
Proof. reflexivity. Qed.
Lemma FOsubst_f_neg : forall x s A, FOsubst_f x s (FONeg A) = FONeg (FOsubst_f x s A).
Proof. reflexivity. Qed.
Lemma FOsubst_f_and : forall x s A B,
  FOsubst_f x s (FOAnd A B) = FOAnd (FOsubst_f x s A) (FOsubst_f x s B).
Proof. reflexivity. Qed.
Lemma FOsubst_f_or : forall x s A B,
  FOsubst_f x s (FOOr A B) = FOOr (FOsubst_f x s A) (FOsubst_f x s B).
Proof. reflexivity. Qed.
Lemma FOsubst_f_ex_ne : forall x s v A, v <> x ->
  FOsubst_f x s (FOExists v A) = FOExists v (FOsubst_f x s A).
Proof. intros x s v A H. cbn. rewrite (proj2 (Nat.eqb_neq v x) H). reflexivity. Qed.
Lemma FOsubst_f_all_ne : forall x s v A, v <> x ->
  FOsubst_f x s (FOForall v A) = FOForall v (FOsubst_f x s A).
Proof. intros x s v A H. cbn. rewrite (proj2 (Nat.eqb_neq v x) H). reflexivity. Qed.
Lemma FOsubst_f_bex : forall x s v t A, x < v ->
  FOsubst_f x s (FOBexC v t A) = FOBexC v (FOsubst_t x s t) (FOsubst_f x s A).
Proof.
  intros x s v t A H. unfold FOBexC, FOAnd, FONeg. cbn [FOsubst_f FOsubst_t].
  nat_eqb_simpl. reflexivity.
Qed.
Lemma FOsubst_f_ball : forall x s v t A, x < v ->
  FOsubst_f x s (FOBallC v t A) = FOBallC v (FOsubst_t x s t) (FOsubst_f x s A).
Proof.
  intros x s v t A H. unfold FOBallC. cbn [FOsubst_f FOsubst_t].
  nat_eqb_simpl. reflexivity.
Qed.
Lemma FOsubst_f_cpairF : forall x s a b c,
  FOsubst_f x s (FOcpairF a b c) =
  FOcpairF (FOsubst_t x s a) (FOsubst_t x s b) (FOsubst_t x s c).
Proof. reflexivity. Qed.

Create HintDb fosubst.
Hint Rewrite FOsubst_t_zero FOsubst_t_succ FOsubst_t_plus FOsubst_t_mult
  FOsubst_t_numeral FOsubst_f_eq FOsubst_f_false FOsubst_f_impl FOsubst_f_neg
  FOsubst_f_and FOsubst_f_or FOsubst_f_cpairF : fosubst.
Hint Rewrite FOsubst_t_var_ne FOsubst_f_ex_ne FOsubst_f_all_ne FOsubst_f_bex
  FOsubst_f_ball using lia : fosubst.

Ltac fo_subst_solve := intros; autorewrite with fosubst; reflexivity.

Lemma FOsubst_f_betaF : forall x s v c d i y, x < v ->
  FOsubst_f x s (FObetaF v c d i y) =
  FObetaF v (FOsubst_t x s c) (FOsubst_t x s d) (FOsubst_t x s i) (FOsubst_t x s y).
Proof. intros. unfold FObetaF. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_betaF using lia : fosubst.

Lemma FOsubst_f_lookup : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r,
  x < B ->
  FOsubst_f x s (FOlookup B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r) =
  FOlookup B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1) (FOsubst_t x s d1)
    (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3) (FOsubst_t x s d3)
    (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s tg) (FOsubst_t x s a1) (FOsubst_t x s a2) (FOsubst_t x s a3)
    (FOsubst_t x s r).
Proof. intros. unfold FOlookup. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_lookup using lia : fosubst.

Lemma FOsubst_t_nth : forall x s k env,
  FOsubst_t x s (nth k env FOZero) = nth k (map (FOsubst_t x s) env) FOZero.
Proof.
  intros x s k env. revert k. induction env as [|a env IH]; intros [|k]; cbn;
    [reflexivity | reflexivity | reflexivity | apply IH].
Qed.

Lemma FOsubst_f_PATF : forall p x s B env d, x < B ->
  FOsubst_f x s (FOPATF B env p d) =
  FOPATF B (map (FOsubst_t x s) env) p (FOsubst_t x s d).
Proof.
  induction p as [k|j|q IH|a IHa b IHb]; intros x s B env d H; cbn [FOPATF].
  - autorewrite with fosubst. reflexivity.
  - rewrite FOsubst_f_eq, FOsubst_t_nth. reflexivity.
  - autorewrite with fosubst. rewrite IH by lia. autorewrite with fosubst. reflexivity.
  - autorewrite with fosubst. rewrite IHa, IHb by lia. autorewrite with fosubst.
    reflexivity.
Qed.
Hint Rewrite FOsubst_f_PATF using lia : fosubst.

(** The table-step builders. *)

Lemma FOsubst_f_STEP0 : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len w tc r,
  x < B ->
  FOsubst_f x s (FOSTEP0 B ct dt c1 d1 c2 d2 c3 d3 cr dr len w tc r) =
  FOSTEP0 B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1) (FOsubst_t x s d1)
    (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3) (FOsubst_t x s d3)
    (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s w) (FOsubst_t x s tc) (FOsubst_t x s r).
Proof. intros. unfold FOSTEP0. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_STEP0 using lia : fosubst.

Lemma FOsubst_f_STEP_bin : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r k tg,
  x < B ->
  FOsubst_f x s (FOSTEP_bin B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r k tg) =
  FOSTEP_bin B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1) (FOsubst_t x s d1)
    (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3) (FOsubst_t x s d3)
    (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s w) (FOsubst_t x s pc) (FOsubst_t x s r) k tg.
Proof. intros. unfold FOSTEP_bin. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_STEP_bin using lia : fosubst.

Lemma FOsubst_f_STEP_quant0 : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r k tg,
  x < B ->
  FOsubst_f x s (FOSTEP_quant0 B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r k tg) =
  FOSTEP_quant0 B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1) (FOsubst_t x s d1)
    (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3) (FOsubst_t x s d3)
    (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s w) (FOsubst_t x s pc) (FOsubst_t x s r) k tg.
Proof. intros. unfold FOSTEP_quant0. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_STEP_quant0 using lia : fosubst.

Lemma FOsubst_f_STEP1 : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r,
  x < B ->
  FOsubst_f x s (FOSTEP1 B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r) =
  FOSTEP1 B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1) (FOsubst_t x s d1)
    (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3) (FOsubst_t x s d3)
    (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s w) (FOsubst_t x s pc) (FOsubst_t x s r).
Proof. intros. unfold FOSTEP1. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_STEP1 using lia : fosubst.

Lemma FOsubst_f_STEP5 : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 r,
  x < B ->
  FOsubst_f x s (FOSTEP5 B ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 r) =
  FOSTEP5 B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1) (FOsubst_t x s d1)
    (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3) (FOsubst_t x s d3)
    (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s a1) (FOsubst_t x s r).
Proof. intros. unfold FOSTEP5. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_STEP5 using lia : fosubst.

Lemma FOsubst_f_STEP_substbin : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    y sc tc r ktag lktag rtag,
  x < B ->
  FOsubst_f x s (FOSTEP_substbin B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc tc r
                   ktag lktag rtag) =
  FOSTEP_substbin B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s y) (FOsubst_t x s sc) (FOsubst_t x s tc) (FOsubst_t x s r)
    ktag lktag rtag.
Proof. intros. unfold FOSTEP_substbin. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_STEP_substbin using lia : fosubst.

Lemma FOsubst_f_STEP2 : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc tc r,
  x < B ->
  FOsubst_f x s (FOSTEP2 B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc tc r) =
  FOSTEP2 B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1) (FOsubst_t x s d1)
    (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3) (FOsubst_t x s d3)
    (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s y) (FOsubst_t x s sc) (FOsubst_t x s tc) (FOsubst_t x s r).
Proof. intros. unfold FOSTEP2. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_STEP2 using lia : fosubst.

Lemma FOsubst_f_STEP_substquant : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    y sc pc r ktag,
  x < B ->
  FOsubst_f x s (FOSTEP_substquant B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc pc r ktag) =
  FOSTEP_substquant B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s y) (FOsubst_t x s sc) (FOsubst_t x s pc) (FOsubst_t x s r) ktag.
Proof. intros. unfold FOSTEP_substquant. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_STEP_substquant using lia : fosubst.

Lemma FOsubst_f_STEP3 : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc pc r,
  x < B ->
  FOsubst_f x s (FOSTEP3 B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc pc r) =
  FOSTEP3 B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1) (FOsubst_t x s d1)
    (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3) (FOsubst_t x s d3)
    (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s y) (FOsubst_t x s sc) (FOsubst_t x s pc) (FOsubst_t x s r).
Proof. intros. unfold FOSTEP3. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_STEP3 using lia : fosubst.

Lemma FOsubst_f_STEP_subokbin : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc pc r,
  x < B ->
  FOsubst_f x s (FOSTEP_subokbin B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc pc r) =
  FOSTEP_subokbin B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s y) (FOsubst_t x s sc) (FOsubst_t x s pc) (FOsubst_t x s r).
Proof. intros. unfold FOSTEP_subokbin. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_STEP_subokbin using lia : fosubst.

Lemma FOsubst_f_STEP_subokquant : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    y sc pc r k,
  x < B ->
  FOsubst_f x s (FOSTEP_subokquant B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc pc r k) =
  FOSTEP_subokquant B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s y) (FOsubst_t x s sc) (FOsubst_t x s pc) (FOsubst_t x s r) k.
Proof. intros. unfold FOSTEP_subokquant. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_STEP_subokquant using lia : fosubst.

Lemma FOsubst_f_STEP4 : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc pc r,
  x < B ->
  FOsubst_f x s (FOSTEP4 B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc pc r) =
  FOSTEP4 B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1) (FOsubst_t x s d1)
    (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3) (FOsubst_t x s d3)
    (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s y) (FOsubst_t x s sc) (FOsubst_t x s pc) (FOsubst_t x s r).
Proof. intros. unfold FOSTEP4. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_STEP4 using lia : fosubst.

Lemma FOsubst_f_STEPDISPATCH : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len j,
  x < B ->
  FOsubst_f x s (FOSTEPDISPATCH B ct dt c1 d1 c2 d2 c3 d3 cr dr len j) =
  FOSTEPDISPATCH B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s j).
Proof. intros. unfold FOSTEPDISPATCH. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_STEPDISPATCH using lia : fosubst.

Lemma FOsubst_f_TBLVALID : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len,
  x < B ->
  FOsubst_f x s (FOTBLVALID B ct dt c1 d1 c2 d2 c3 d3 cr dr len) =
  FOTBLVALID B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len).
Proof. intros. unfold FOTBLVALID. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_TBLVALID using lia : fosubst.

Lemma FOsubst_map_cons : forall x s a l,
  map (FOsubst_t x s) (a :: l) = FOsubst_t x s a :: map (FOsubst_t x s) l.
Proof. reflexivity. Qed.
Lemma FOsubst_map_nil : forall x s, map (FOsubst_t x s) [] = [].
Proof. reflexivity. Qed.
Hint Rewrite FOsubst_map_cons FOsubst_map_nil : fosubst.

(** The justification builders. *)

Lemma FOsubst_f_AXQc : forall x s B d, x < B ->
  FOsubst_f x s (FOAXQc B d) = FOAXQc B (FOsubst_t x s d).
Proof.
  intros. unfold FOAXQc, FOAXQ1c, FOAXQ2c, FOAXQ3c, FOAXQ4c, FOAXQ5c, FOAXQ6c, FOAXQ7c.
  autorewrite with fosubst. reflexivity.
Qed.
Hint Rewrite FOsubst_f_AXQc using lia : fosubst.

Lemma FOsubst_f_LOGc : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len d, x < B ->
  FOsubst_f x s (FOLOGc B ct dt c1 d1 c2 d2 c3 d3 cr dr len d) =
  FOLOGc B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s d).
Proof.
  intros. unfold FOLOGc, FOLOG1c, FOLOG2c, FOLOG3c, FOLOG4c, FOLOG5c, FOLOG6c,
    FOLOG7c, FOLOG8c, FOLOG9c, FOLOG10c, FOLOG11c, FOLOG12c.
  autorewrite with fosubst. reflexivity.
Qed.
Hint Rewrite FOsubst_f_LOGc using lia : fosubst.

Lemma FOsubst_f_AXREFLc : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d, x < B ->
  FOsubst_f x s (FOAXREFLc B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d) =
  FOAXREFLc B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    c (FOsubst_t x s d).
Proof. intros. unfold FOAXREFLc. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_AXREFLc using lia : fosubst.

Lemma FOsubst_f_REFLSc : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d, x < B ->
  FOsubst_f x s (FOREFLSc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) =
  FOREFLSc B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    cores (FOsubst_t x s d).
Proof.
  intros x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d H.
  induction cores as [|c rest IH]; cbn [FOREFLSc].
  - reflexivity.
  - rewrite FOsubst_f_or, IH. autorewrite with fosubst. reflexivity.
Qed.
Hint Rewrite FOsubst_f_REFLSc using lia : fosubst.

Lemma FOsubst_f_THAXc : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d, x < B ->
  FOsubst_f x s (FOTHAXc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) =
  FOTHAXc B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    cores (FOsubst_t x s d).
Proof. intros. unfold FOTHAXc. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_THAXc using lia : fosubst.

Lemma FOsubst_f_JSUBST : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len pat vd pl,
  x < B ->
  FOsubst_f x s (FOJSUBST B ct dt c1 d1 c2 d2 c3 d3 cr dr len pat vd pl) =
  FOJSUBST B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    pat (FOsubst_t x s vd) (FOsubst_t x s pl).
Proof. intros. unfold FOJSUBST. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_JSUBST using lia : fosubst.

Lemma FOsubst_f_JIND : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len vd pl, x < B ->
  FOsubst_f x s (FOJIND B ct dt c1 d1 c2 d2 c3 d3 cr dr len vd pl) =
  FOJIND B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s vd) (FOsubst_t x s pl).
Proof. intros. unfold FOJIND. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_JIND using lia : fosubst.

Lemma FOsubst_f_JMP : forall x s B cs ds vd pl ipos, x < B ->
  FOsubst_f x s (FOJMP B cs ds vd pl ipos) =
  FOJMP B (FOsubst_t x s cs) (FOsubst_t x s ds) (FOsubst_t x s vd)
    (FOsubst_t x s pl) (FOsubst_t x s ipos).
Proof. intros. unfold FOJMP. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_JMP using lia : fosubst.

Lemma FOsubst_f_JGEN : forall x s B cs ds vd pl ipos, x < B ->
  FOsubst_f x s (FOJGEN B cs ds vd pl ipos) =
  FOJGEN B (FOsubst_t x s cs) (FOsubst_t x s ds) (FOsubst_t x s vd)
    (FOsubst_t x s pl) (FOsubst_t x s ipos).
Proof. intros. unfold FOJGEN. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_JGEN using lia : fosubst.

Lemma FOsubst_f_JLOEB : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd pl ipos,
  0 < x -> x < B ->
  FOsubst_f x s (FOJLOEB B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd pl ipos) =
  FOJLOEB B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s cs) (FOsubst_t x s ds) (FOsubst_t x s vd) (FOsubst_t x s pl)
    (FOsubst_t x s ipos).
Proof. intros. unfold FOJLOEB. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_JLOEB using lia : fosubst.

Lemma FOsubst_f_PROVAT : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len c z p, x < B ->
  FOsubst_f x s (FOPROVAT B ct dt c1 d1 c2 d2 c3 d3 cr dr len c z p) =
  FOPROVAT B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    c (FOsubst_t x s z) (FOsubst_t x s p).
Proof. intros. unfold FOPROVAT. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_PROVAT using lia : fosubst.

Lemma FOsubst_f_GENF : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len z, x < B ->
  FOsubst_f x s (FOGENF B ct dt c1 d1 c2 d2 c3 d3 cr dr len z) =
  FOGENF B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s z).
Proof. intros. unfold FOGENF. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_GENF using lia : fosubst.

Lemma FOsubst_f_D2c : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d, x < B ->
  FOsubst_f x s (FOD2c B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d) =
  FOD2c B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    c (FOsubst_t x s d).
Proof. intros. unfold FOD2c. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_D2c using lia : fosubst.

Lemma FOsubst_f_D3c : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d, x < B ->
  FOsubst_f x s (FOD3c B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d) =
  FOD3c B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    c (FOsubst_t x s d).
Proof. intros. unfold FOD3c. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_D3c using lia : fosubst.

Lemma FOsubst_f_DMONc : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len c c' d, x < B ->
  FOsubst_f x s (FODMONc B ct dt c1 d1 c2 d2 c3 d3 cr dr len c c' d) =
  FODMONc B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    c c' (FOsubst_t x s d).
Proof. intros. unfold FODMONc. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_DMONc using lia : fosubst.

Lemma FOsubst_f_D2Sc : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d, x < B ->
  FOsubst_f x s (FOD2Sc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) =
  FOD2Sc B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    cores (FOsubst_t x s d).
Proof.
  intros x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d H.
  induction cores as [|c rest IH]; cbn [FOD2Sc].
  - reflexivity.
  - rewrite FOsubst_f_or, IH. autorewrite with fosubst. reflexivity.
Qed.
Hint Rewrite FOsubst_f_D2Sc using lia : fosubst.

Lemma FOsubst_f_D3Sc : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d, x < B ->
  FOsubst_f x s (FOD3Sc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) =
  FOD3Sc B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    cores (FOsubst_t x s d).
Proof.
  intros x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d H.
  induction cores as [|c rest IH]; cbn [FOD3Sc].
  - reflexivity.
  - rewrite FOsubst_f_or, IH. autorewrite with fosubst. reflexivity.
Qed.
Hint Rewrite FOsubst_f_D3Sc using lia : fosubst.

Lemma FOsubst_f_DMONS1 : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len c cs d, x < B ->
  FOsubst_f x s (FODMONS1 B ct dt c1 d1 c2 d2 c3 d3 cr dr len c cs d) =
  FODMONS1 B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    c cs (FOsubst_t x s d).
Proof.
  intros x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len c cs d H.
  induction cs as [|c' rest IH]; cbn [FODMONS1].
  - reflexivity.
  - rewrite FOsubst_f_or, IH. autorewrite with fosubst. reflexivity.
Qed.
Hint Rewrite FOsubst_f_DMONS1 using lia : fosubst.

Lemma FOsubst_f_DMONSc : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d, x < B ->
  FOsubst_f x s (FODMONSc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) =
  FODMONSc B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    cores (FOsubst_t x s d).
Proof.
  intros x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d H.
  induction cores as [|c rest IH]; cbn [FODMONSc].
  - reflexivity.
  - rewrite FOsubst_f_or, IH. autorewrite with fosubst. reflexivity.
Qed.
Hint Rewrite FOsubst_f_DMONSc using lia : fosubst.

Lemma FOsubst_f_JUSTCK : forall x s B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds cj dj i,
  0 < x -> x < B ->
  FOsubst_f x s (FOJUSTCK B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds cj dj i) =
  FOJUSTCK B cores (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s cs) (FOsubst_t x s ds) (FOsubst_t x s cj) (FOsubst_t x s dj)
    (FOsubst_t x s i).
Proof. intros. unfold FOJUSTCK. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_JUSTCK using lia : fosubst.

Lemma FOsubst_f_GUARDC : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i,
  x < B ->
  FOsubst_f x s (FOGUARDC B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i) =
  FOGUARDC B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s cs) (FOsubst_t x s ds) (FOsubst_t x s i).
Proof. intros. unfold FOGUARDC. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_GUARDC using lia : fosubst.

(** ** Capture-freedom inside the checker's builders.

    A term none of whose variables lies in a builder's binder range can
    be substituted into the builder's arguments without capture.  The
    lemmas below are collected in the hint database [fook]. *)

Lemma FOtm_avoid_sub : forall s lo hi lo' hi',
  FOtm_avoid s lo hi -> lo <= lo' -> hi' <= hi -> FOtm_avoid s lo' hi'.
Proof. intros s lo hi lo' hi' H H1 H2 w Hw1 Hw2. apply H; lia. Qed.

Lemma FOsubst_ok_eq : forall x s a b, FOsubst_ok x s (FOEq a b) = true.
Proof. reflexivity. Qed.
Lemma FOsubst_ok_false : forall x s, FOsubst_ok x s FOFalseF = true.
Proof. reflexivity. Qed.
Lemma FOsubst_ok_impl : forall x s A B,
  FOsubst_ok x s A = true -> FOsubst_ok x s B = true -> FOsubst_ok x s (FOImplF A B) = true.
Proof. intros x s A B HA HB. cbn. rewrite HA, HB. reflexivity. Qed.
Lemma FOsubst_ok_neg : forall x s A,
  FOsubst_ok x s A = true -> FOsubst_ok x s (FONeg A) = true.
Proof. intros x s A HA. unfold FONeg. apply FOsubst_ok_impl; [exact HA | reflexivity]. Qed.
Lemma FOsubst_ok_and : forall x s A B,
  FOsubst_ok x s A = true -> FOsubst_ok x s B = true -> FOsubst_ok x s (FOAnd A B) = true.
Proof.
  intros x s A B HA HB. unfold FOAnd.
  apply FOsubst_ok_neg, FOsubst_ok_impl; [exact HA | apply FOsubst_ok_neg; exact HB].
Qed.
Lemma FOsubst_ok_or : forall x s A B,
  FOsubst_ok x s A = true -> FOsubst_ok x s B = true -> FOsubst_ok x s (FOOr A B) = true.
Proof.
  intros x s A B HA HB. unfold FOOr.
  apply FOsubst_ok_impl; [apply FOsubst_ok_neg; exact HA | exact HB].
Qed.
Lemma FOsubst_ok_ex : forall x s v A,
  FOin_tm v s = false -> FOsubst_ok x s A = true -> FOsubst_ok x s (FOExists v A) = true.
Proof.
  intros x s v A Hv HA. cbn. destruct (Nat.eqb v x); [reflexivity|].
  destruct (FOfree_in x A); [rewrite Hv, HA; reflexivity | reflexivity].
Qed.
Lemma FOsubst_ok_all : forall x s v A,
  FOin_tm v s = false -> FOsubst_ok x s A = true -> FOsubst_ok x s (FOForall v A) = true.
Proof.
  intros x s v A Hv HA. cbn. destruct (Nat.eqb v x); [reflexivity|].
  destruct (FOfree_in x A); [rewrite Hv, HA; reflexivity | reflexivity].
Qed.
Lemma FOsubst_ok_bex : forall x s v t A,
  FOin_tm v s = false -> FOin_tm (S v) s = false -> FOsubst_ok x s A = true ->
  FOsubst_ok x s (FOBexC v t A) = true.
Proof.
  intros x s v t A H1 H2 HA. unfold FOBexC.
  apply FOsubst_ok_ex; [exact H1|]. apply FOsubst_ok_and; [|exact HA].
  apply FOsubst_ok_ex; [exact H2 | apply FOsubst_ok_eq].
Qed.
Lemma FOsubst_ok_ball : forall x s v t A,
  FOin_tm v s = false -> FOin_tm (S v) s = false -> FOsubst_ok x s A = true ->
  FOsubst_ok x s (FOBallC v t A) = true.
Proof.
  intros x s v t A H1 H2 HA. unfold FOBallC.
  apply FOsubst_ok_all; [exact H1|]. apply FOsubst_ok_impl; [|exact HA].
  apply FOsubst_ok_ex; [exact H2 | apply FOsubst_ok_eq].
Qed.
Lemma FOsubst_ok_cpairF : forall x s a b c, FOsubst_ok x s (FOcpairF a b c) = true.
Proof. reflexivity. Qed.

Create HintDb fook.
Hint Resolve FOsubst_ok_eq FOsubst_ok_false FOsubst_ok_impl FOsubst_ok_neg FOsubst_ok_and
  FOsubst_ok_or FOsubst_ok_ex FOsubst_ok_all FOsubst_ok_bex FOsubst_ok_ball
  FOsubst_ok_cpairF : fook.
Hint Extern 1 (FOin_tm _ _ = false) =>
  match goal with Ha : FOtm_avoid _ _ _ |- _ => apply Ha; lia end : fook.
Hint Extern 1 (FOtm_avoid _ _ _) =>
  match goal with Ha : FOtm_avoid _ _ _ |- _ =>
    apply (FOtm_avoid_sub _ _ _ _ _ Ha); lia end : fook.

Ltac fo_ok_solve := intros; auto 100 with fook.

Lemma FOsubst_ok_betaF : forall x s v c d i y, FOtm_avoid s v (v + 4) ->
  FOsubst_ok x s (FObetaF v c d i y) = true.
Proof. intros. unfold FObetaF. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_betaF : fook.

Lemma FOsubst_ok_lookup : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r,
  FOtm_avoid s B (B + 22) ->
  FOsubst_ok x s (FOlookup B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r) = true.
Proof. intros. unfold FOlookup. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_lookup : fook.

(** The binder span of a pattern formula. *)

Fixpoint cpat_span (p : CPat) : nat :=
  match p with
  | CLit _ => 0
  | CVarP _ => 0
  | CSuccP q => 2 + cpat_span q
  | CPair a b => 4 + 4 * cpat_pairs a + cpat_span b
  end.

Lemma cpat_span_le : forall p, cpat_span p <= 4 * cpat_pairs p.
Proof. induction p; cbn [cpat_span cpat_pairs]; lia. Qed.

Lemma FOsubst_ok_PATF : forall p x s B env d, FOtm_avoid s B (B + cpat_span p) ->
  FOsubst_ok x s (FOPATF B env p d) = true.
Proof.
  induction p as [k|j|q IH|a IHa b IHb]; intros x s B env d H; cbn [FOPATF cpat_span] in *.
  - apply FOsubst_ok_eq.
  - apply FOsubst_ok_eq.
  - apply FOsubst_ok_bex; [apply H; lia | apply H; lia|].
    apply FOsubst_ok_and; [apply FOsubst_ok_eq|]. apply IH.
    apply (FOtm_avoid_sub _ _ _ _ _ H); lia.
  - pose proof (cpat_span_le a) as Ha.
    apply FOsubst_ok_bex; [apply H; lia | apply H; lia|].
    apply FOsubst_ok_bex; [apply H; lia | apply H; lia|].
    apply FOsubst_ok_and; [apply FOsubst_ok_cpairF|].
    apply FOsubst_ok_and; [apply IHa | apply IHb];
      apply (FOtm_avoid_sub _ _ _ _ _ H); lia.
Qed.
Hint Resolve FOsubst_ok_PATF : fook.

Hint Extern 2 (FOtm_avoid _ _ _) =>
  match goal with Ha : FOtm_avoid _ _ _ |- _ =>
    apply (FOtm_avoid_sub _ _ _ _ _ Ha); simpl; lia end : fook.

Lemma FOsubst_ok_STEP0 : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len w tc r,
  FOtm_avoid s B (B + 50) ->
  FOsubst_ok x s (FOSTEP0 B ct dt c1 d1 c2 d2 c3 d3 cr dr len w tc r) = true.
Proof. intros. unfold FOSTEP0. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_STEP0 : fook.

Lemma FOsubst_ok_STEP_bin : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r k tg,
  FOtm_avoid s B (B + 50) ->
  FOsubst_ok x s (FOSTEP_bin B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r k tg) = true.
Proof. intros. unfold FOSTEP_bin. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_STEP_bin : fook.

Lemma FOsubst_ok_STEP_quant0 : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r k tg,
  FOtm_avoid s B (B + 28) ->
  FOsubst_ok x s (FOSTEP_quant0 B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r k tg) = true.
Proof. intros. unfold FOSTEP_quant0. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_STEP_quant0 : fook.

Lemma FOsubst_ok_STEP1 : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r,
  FOtm_avoid s B (B + 50) ->
  FOsubst_ok x s (FOSTEP1 B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r) = true.
Proof. intros. unfold FOSTEP1. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_STEP1 : fook.

Lemma FOsubst_ok_STEP5 : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 r,
  FOtm_avoid s B (B + 26) ->
  FOsubst_ok x s (FOSTEP5 B ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 r) = true.
Proof. intros. unfold FOSTEP5. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_STEP5 : fook.

Lemma FOsubst_ok_STEP_substbin : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    y sc tc r ktag lktag rtag,
  FOtm_avoid s B (B + 56) ->
  FOsubst_ok x s (FOSTEP_substbin B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc tc r
                    ktag lktag rtag) = true.
Proof. intros. unfold FOSTEP_substbin. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_STEP_substbin : fook.

Lemma FOsubst_ok_STEP2 : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc tc r,
  FOtm_avoid s B (B + 56) ->
  FOsubst_ok x s (FOSTEP2 B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc tc r) = true.
Proof. intros. unfold FOSTEP2. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_STEP2 : fook.

Lemma FOsubst_ok_STEP_substquant : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    y sc pc r ktag,
  FOtm_avoid s B (B + 32) ->
  FOsubst_ok x s (FOSTEP_substquant B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc pc r ktag)
  = true.
Proof. intros. unfold FOSTEP_substquant. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_STEP_substquant : fook.

Lemma FOsubst_ok_STEP3 : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc pc r,
  FOtm_avoid s B (B + 56) ->
  FOsubst_ok x s (FOSTEP3 B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc pc r) = true.
Proof. intros. unfold FOSTEP3. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_STEP3 : fook.

Lemma FOsubst_ok_STEP_subokbin : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc pc r,
  FOtm_avoid s B (B + 50) ->
  FOsubst_ok x s (FOSTEP_subokbin B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc pc r) = true.
Proof. intros. unfold FOSTEP_subokbin. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_STEP_subokbin : fook.

Lemma FOsubst_ok_STEP_subokquant : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    y sc pc r k,
  FOtm_avoid s B (B + 72) ->
  FOsubst_ok x s (FOSTEP_subokquant B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc pc r k)
  = true.
Proof. intros. unfold FOSTEP_subokquant. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_STEP_subokquant : fook.

Lemma FOsubst_ok_STEP4 : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc pc r,
  FOtm_avoid s B (B + 72) ->
  FOsubst_ok x s (FOSTEP4 B ct dt c1 d1 c2 d2 c3 d3 cr dr len y sc pc r) = true.
Proof. intros. unfold FOSTEP4. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_STEP4 : fook.

Lemma FOsubst_ok_STEPDISPATCH : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len j,
  FOtm_avoid s B (B + 102) ->
  FOsubst_ok x s (FOSTEPDISPATCH B ct dt c1 d1 c2 d2 c3 d3 cr dr len j) = true.
Proof. intros. unfold FOSTEPDISPATCH. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_STEPDISPATCH : fook.

Lemma FOsubst_ok_TBLVALID : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len,
  FOtm_avoid s B (B + 104) ->
  FOsubst_ok x s (FOTBLVALID B ct dt c1 d1 c2 d2 c3 d3 cr dr len) = true.
Proof. intros. unfold FOTBLVALID. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_TBLVALID : fook.

Lemma FOsubst_ok_AXQc : forall x s B d, FOtm_avoid s B (B + 72) ->
  FOsubst_ok x s (FOAXQc B d) = true.
Proof.
  intros. unfold FOAXQc, FOAXQ1c, FOAXQ2c, FOAXQ3c, FOAXQ4c, FOAXQ5c, FOAXQ6c, FOAXQ7c.
  auto 100 with fook.
Qed.
Hint Resolve FOsubst_ok_AXQc : fook.

Lemma FOsubst_ok_LOGc : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len d,
  FOtm_avoid s B (B + 82) ->
  FOsubst_ok x s (FOLOGc B ct dt c1 d1 c2 d2 c3 d3 cr dr len d) = true.
Proof.
  intros. unfold FOLOGc, FOLOG1c, FOLOG2c, FOLOG3c, FOLOG4c, FOLOG5c, FOLOG6c,
    FOLOG7c, FOLOG8c, FOLOG9c, FOLOG10c, FOLOG11c, FOLOG12c.
  auto 100 with fook.
Qed.
Hint Resolve FOsubst_ok_LOGc : fook.

Lemma FOsubst_ok_AXREFLc : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d,
  FOtm_avoid s B (B + 58) ->
  FOsubst_ok x s (FOAXREFLc B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d) = true.
Proof. intros. unfold FOAXREFLc. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_AXREFLc : fook.

Lemma FOsubst_ok_REFLSc : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d,
  FOtm_avoid s B (B + 58) ->
  FOsubst_ok x s (FOREFLSc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) = true.
Proof.
  intros x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d H.
  induction cores as [|c rest IH]; cbn [FOREFLSc]; auto 100 with fook.
Qed.
Hint Resolve FOsubst_ok_REFLSc : fook.

Lemma FOsubst_ok_THAXc : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d,
  FOtm_avoid s B (B + 72) ->
  FOsubst_ok x s (FOTHAXc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) = true.
Proof. intros. unfold FOTHAXc. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_THAXc : fook.

Lemma FOsubst_ok_JSUBST : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len pat vd pl,
  FOtm_avoid s B (B + 74 + cpat_span pat) ->
  FOsubst_ok x s (FOJSUBST B ct dt c1 d1 c2 d2 c3 d3 cr dr len pat vd pl) = true.
Proof. intros. unfold FOJSUBST. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_JSUBST : fook.

Lemma FOsubst_ok_JIND : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len vd pl,
  FOtm_avoid s B (B + 140) ->
  FOsubst_ok x s (FOJIND B ct dt c1 d1 c2 d2 c3 d3 cr dr len vd pl) = true.
Proof. intros. unfold FOJIND. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_JIND : fook.

Lemma FOsubst_ok_JMP : forall x s B cs ds vd pl ipos, FOtm_avoid s B (B + 24) ->
  FOsubst_ok x s (FOJMP B cs ds vd pl ipos) = true.
Proof. intros. unfold FOJMP. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_JMP : fook.

Lemma FOsubst_ok_JGEN : forall x s B cs ds vd pl ipos, FOtm_avoid s B (B + 18) ->
  FOsubst_ok x s (FOJGEN B cs ds vd pl ipos) = true.
Proof. intros. unfold FOJGEN. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_JGEN : fook.

Lemma FOsubst_ok_JLOEB : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd pl ipos,
  FOtm_avoid s B (B + 112) ->
  FOsubst_ok x s (FOJLOEB B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd pl ipos) = true.
Proof. intros. unfold FOJLOEB. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_JLOEB : fook.

Lemma FOsubst_ok_PROVAT : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len c z p,
  FOtm_avoid s B (B + 46) ->
  FOsubst_ok x s (FOPROVAT B ct dt c1 d1 c2 d2 c3 d3 cr dr len c z p) = true.
Proof. intros. unfold FOPROVAT. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_PROVAT : fook.

Lemma FOsubst_ok_GENF : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len z,
  FOtm_avoid s B (B + 24) ->
  FOsubst_ok x s (FOGENF B ct dt c1 d1 c2 d2 c3 d3 cr dr len z) = true.
Proof. intros. unfold FOGENF. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_GENF : fook.

Lemma FOsubst_ok_D2c : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d,
  FOtm_avoid s B (B + 216) ->
  FOsubst_ok x s (FOD2c B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d) = true.
Proof. intros. unfold FOD2c. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_D2c : fook.

Lemma FOsubst_ok_D3c : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d,
  FOtm_avoid s B (B + 130) ->
  FOsubst_ok x s (FOD3c B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d) = true.
Proof. intros. unfold FOD3c. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_D3c : fook.

Lemma FOsubst_ok_DMONc : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len c c' d,
  FOtm_avoid s B (B + 130) ->
  FOsubst_ok x s (FODMONc B ct dt c1 d1 c2 d2 c3 d3 cr dr len c c' d) = true.
Proof. intros. unfold FODMONc. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_DMONc : fook.

Lemma FOsubst_ok_D2Sc : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d,
  FOtm_avoid s B (B + 216) ->
  FOsubst_ok x s (FOD2Sc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) = true.
Proof.
  intros x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d H.
  induction cores as [|c rest IH]; cbn [FOD2Sc]; auto 100 with fook.
Qed.
Hint Resolve FOsubst_ok_D2Sc : fook.

Lemma FOsubst_ok_D3Sc : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d,
  FOtm_avoid s B (B + 130) ->
  FOsubst_ok x s (FOD3Sc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) = true.
Proof.
  intros x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d H.
  induction cores as [|c rest IH]; cbn [FOD3Sc]; auto 100 with fook.
Qed.
Hint Resolve FOsubst_ok_D3Sc : fook.

Lemma FOsubst_ok_DMONS1 : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len c cs d,
  FOtm_avoid s B (B + 130) ->
  FOsubst_ok x s (FODMONS1 B ct dt c1 d1 c2 d2 c3 d3 cr dr len c cs d) = true.
Proof.
  intros x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len c cs d H.
  induction cs as [|c' rest IH]; cbn [FODMONS1]; auto 100 with fook.
Qed.
Hint Resolve FOsubst_ok_DMONS1 : fook.

Lemma FOsubst_ok_DMONSc : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d,
  FOtm_avoid s B (B + 130) ->
  FOsubst_ok x s (FODMONSc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) = true.
Proof.
  intros x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d H.
  induction cores as [|c rest IH]; cbn [FODMONSc]; auto 100 with fook.
Qed.
Hint Resolve FOsubst_ok_DMONSc : fook.

Lemma FOsubst_ok_JUSTCK : forall x s B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds cj dj i,
  FOtm_avoid s B (B + 232) ->
  FOsubst_ok x s (FOJUSTCK B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds cj dj i) = true.
Proof. intros. unfold FOJUSTCK. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_JUSTCK : fook.

Lemma FOsubst_ok_GUARDC : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i,
  FOtm_avoid s B (B + 30) ->
  FOsubst_ok x s (FOGUARDC B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i) = true.
Proof. intros. unfold FOGUARDC. auto 100 with fook. Qed.
Hint Resolve FOsubst_ok_GUARDC : fook.

(** ** Agreement of beta-coded sequences, and table lookups under it.

    [FOAGR L c d c' d']: below [L] every element of [c, d] is the
    element of [c', d'] at the same position, in the form the
    concatenation lemma produces.  From it a beta formula at any base
    transfers, and from agreement of all five tracks a table lookup
    transfers. *)

Definition FOAGR (L c d c' d' : FOTerm) : FOFormula :=
  FOForall 469 (FOImplF (FOExists 470 (FOEq (FOPlus (FOVar 469) (FOSucc (FOVar 470))) L))
    (FOForall 471 (FOImplF (FObetaF 480 c d (FOVar 469) (FOVar 471))
                           (FObetaF 484 c' d' (FOVar 469) (FOVar 471))))).

Definition FOlt470 (t L : FOTerm) : FOFormula :=
  FOExists 470 (FOEq (FOPlus t (FOSucc (FOVar 470))) L).

Definition FOle (a b : FOTerm) : FOFormula :=
  FOExists 498 (FOEq (FOPlus a (FOVar 498)) b).

Lemma FOsubst_t_var_eq': forall x s, FOsubst_t x s (FOVar x) = s.
Proof. intros x s. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.
Hint Rewrite FOsubst_t_var_eq' : fosubst.

(** The beta formula at base [v] transfers along an agreement. *)

Lemma FOPrH_agr_beta : forall n G L c d c' d' t x v,
  FOPrH n G (FOAGR L c d c' d') -> FOPrH n G (FOlt470 t L) ->
  v + 4 <= 420 -> FOctx_avoid G v (v + 4) -> FOctx_avoid G 480 488 ->
  FOtm_avoid c 420 500 -> FOtm_avoid d 420 500 -> FOtm_avoid c' 420 500 ->
  FOtm_avoid d' 420 500 -> FOtm_avoid L 420 500 ->
  FOtm_avoid t 420 500 -> FOtm_avoid x 420 500 ->
  FOtm_avoid c v (v + 4) -> FOtm_avoid d v (v + 4) -> FOtm_avoid c' v (v + 4) ->
  FOtm_avoid d' v (v + 4) -> FOtm_avoid t v (v + 4) -> FOtm_avoid x v (v + 4) ->
  FOPrH n G (FObetaF v c d t x .-> FObetaF v c' d' t x).
Proof.
  intros n G L c d c' d' t x v HA Hlt Hv HG1 HG2 Hc Hd Hc' Hd' HL Ht Hx
    Hcv Hdv Hc'v Hd'v Htv Hxv.
  (* instantiate the agreement at t and x *)
  assert (O1 : FOsubst_ok 469 t
                 (FOImplF (FOExists 470 (FOEq (FOPlus (FOVar 469) (FOSucc (FOVar 470))) L))
                    (FOForall 471 (FOImplF (FObetaF 480 c d (FOVar 469) (FOVar 471))
                                           (FObetaF 484 c' d' (FOVar 469) (FOVar 471)))))
               = true).
  { apply FOsubst_ok_impl; [apply FOsubst_ok_ex; [apply Ht; lia | apply FOsubst_ok_eq]|].
    apply FOsubst_ok_all; [apply Ht; lia|].
    apply FOsubst_ok_impl; apply FOsubst_ok_betaF;
      apply (FOtm_avoid_sub _ _ _ _ _ Ht); lia. }
  pose proof (FOPrH_all_elim n G 469 t _ O1 HA) as H1.
  autorewrite with fosubst in H1. subst_t_simpl.
  repeat rewrite (FOsubst_t_not_in _ 469 t) in H1 by (match goal with
    | Ha : FOtm_avoid ?u _ _ |- FOin_tm 469 ?u = false => apply Ha; lia end).
  pose proof (FOPrH_mp n G _ _ H1 Hlt) as H2. clear H1.
  assert (O2 : FOsubst_ok 471 x
                 (FOImplF (FObetaF 480 c d t (FOVar 471)) (FObetaF 484 c' d' t (FOVar 471)))
               = true).
  { apply FOsubst_ok_impl; apply FOsubst_ok_betaF;
      apply (FOtm_avoid_sub _ _ _ _ _ Hx); lia. }
  pose proof (FOPrH_all_elim n G 471 x _ O2 H2) as H3. clear H2.
  autorewrite with fosubst in H3.
  repeat rewrite (FOsubst_t_not_in _ 471 x) in H3 by (match goal with
    | Ha : FOtm_avoid ?u _ _ |- FOin_tm 471 ?u = false => apply Ha; lia end).
  (* move the binders to 480 and back *)
  assert (S1 : forall u, FOtm_avoid u 420 500 -> FOtm_avoid u 480 (480 + 4))
    by (intros u Hu; exact (FOtm_avoid_sub u 420 500 480 (480 + 4) Hu ltac:(lia) ltac:(lia))).
  assert (S2 : forall u, FOtm_avoid u 420 500 -> FOtm_avoid u 484 (484 + 4))
    by (intros u Hu; exact (FOtm_avoid_sub u 420 500 484 (484 + 4) Hu ltac:(lia) ltac:(lia))).
  apply (FOPrH_imp_trans n G _ (FObetaF 480 c d t x)).
  { apply (FOPrH_beta_rebase n G v 480 c d t x ltac:(lia)
             (fun w H1 H2 => HG2 w ltac:(lia) ltac:(lia))
             Hcv (S1 c Hc) Hdv (S1 d Hd) Htv (S1 t Ht) Hxv (S1 x Hx)). }
  apply (FOPrH_imp_trans n G _ (FObetaF 484 c' d' t x)); [exact H3|].
  apply (FOPrH_beta_rebase n G 484 v c' d' t x ltac:(lia) HG1
           (S2 c' Hc') Hc'v (S2 d' Hd') Hd'v (S2 t Ht) Htv (S2 x Hx) Hxv).
Qed.

(** Bounds [v < a] rename to the agreement's binder and grow with [a]. *)

Lemma FOPrH_ltv_470 : forall n G v a,
  v <> 470 -> S v <> 470 -> FOtm_avoid a 470 471 -> FOtm_avoid a (S v) (S (S v)) ->
  FOPrH n G (FOltv v a .-> FOlt470 (FOVar v) a).
Proof.
  intros n G v a H1 H2 Ha1 Ha2. unfold FOltv, FOlt470.
  pose proof (FOPr_ex_rename n (S v) 470
                (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) a)) as R.
  specialize (R ltac:(cbn [FOfree_in FOin_tm]; nat_eqb_simpl; in_tm_simpl; reflexivity)
                eq_refl).
  autorewrite with fosubst in R.
  rewrite (FOsubst_t_not_in a (S v) (FOVar 470) (Ha2 (S v) ltac:(lia) ltac:(lia))) in R.
  exact (FOPrH_thm n G _ R).
Qed.

Lemma FOfree_ctx_app_inv : forall v G L,
  FOfree_ctx v G -> FOfree_ctx v L -> FOfree_ctx v (G ++ L).
Proof.
  intros v G L HG HL H Hin. apply in_app_or in Hin.
  destruct Hin as [Hin|Hin]; [exact (HG H Hin) | exact (HL H Hin)].
Qed.

Lemma FOPrH_ltv_le : forall n G v a b,
  FOPrH n G (FOle a b) ->
  FOfree_ctx (S v) G -> FOfree_ctx 498 G -> v < 400 ->
  FOtm_avoid a (S v) (S (S v)) -> FOtm_avoid b (S v) (S (S v)) ->
  FOtm_avoid a 498 499 -> FOtm_avoid b 498 499 ->
  FOPrH n G (FOltv v a .-> FOltv v b).
Proof.
  intros n G v a b Hle HG1 HG2 Hv Ha1 Hb1 Ha2 Hb2.
  apply FOPrH_intro.
  assert (Fa : FOfree_in 498 (FOltv v a) = false).
  { unfold FOltv. cbn [FOfree_in FOin_tm]. nat_eqb_simpl. in_tm_simpl. reflexivity. }
  assert (Fb : FOfree_in 498 (FOltv v b) = false).
  { unfold FOltv. cbn [FOfree_in FOin_tm]. nat_eqb_simpl. in_tm_simpl. reflexivity. }
  apply (FOPrH_ex_elim n (G ++ [FOltv v a]) 498 (FOEq (FOPlus a (FOVar 498)) b));
    [apply FOfree_ctx_app1; [exact HG2 | exact Fa] | exact Fb
    | exact (FOPrH_weak_app n G _ _ Hle) |].
  apply (FOPrH_ex_elim n ((G ++ [FOltv v a]) ++ [FOEq (FOPlus a (FOVar 498)) b]) (S v)
           (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) a)).
  - apply FOfree_ctx_app1; [apply FOfree_ctx_app1; [exact HG1|]|].
    + unfold FOltv. apply FOfree_in_ex_self.
    + cbn [FOfree_in FOin_tm]. nat_eqb_simpl. in_tm_simpl. reflexivity.
  - unfold FOltv. apply FOfree_in_ex_self.
  - apply FOPrH_assum. apply in_or_app. left. apply in_or_app. right. left.
    reflexivity.
  - unfold FOltv.
    apply (FOPrH_ex_intro _ _ (S v) (FOPlus (FOVar (S v)) (FOVar 498))); [reflexivity|].
    autorewrite with fosubst.
    rewrite (FOsubst_t_not_in b (S v) _ (Hb1 (S v) ltac:(lia) ltac:(lia))).
    fo_lin [(.S .0, a, FOPlus (FOVar v) (FOSucc (FOVar (S v))));
            (.S .0, b, FOPlus a (FOVar 498))].
Qed.

(** ** Tables. *)

Record FOtab : Type := mkTab {
  tct : FOTerm; tdt : FOTerm; tc1 : FOTerm; td1 : FOTerm; tc2 : FOTerm; td2 : FOTerm;
  tc3 : FOTerm; td3 : FOTerm; tcr : FOTerm; tdr : FOTerm; tlen : FOTerm }.

Definition FOlookupT (B : nat) (T : FOtab) (tg a1 a2 a3 r : FOTerm) : FOFormula :=
  FOlookup B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T) (td3 T)
    (tcr T) (tdr T) (tlen T) tg a1 a2 a3 r.

Definition FOtab_terms (T : FOtab) : list FOTerm :=
  [tct T; tdt T; tc1 T; td1 T; tc2 T; td2 T; tc3 T; td3 T; tcr T; tdr T; tlen T].

Definition FOtms_avoid (ts : list FOTerm) (lo hi : nat) : Prop :=
  forall t, In t ts -> FOtm_avoid t lo hi.

Lemma FOtms_avoid_nil : forall lo hi, FOtms_avoid [] lo hi.
Proof. intros lo hi t []. Qed.
Lemma FOtms_avoid_cons : forall t L lo hi,
  FOtm_avoid t lo hi -> FOtms_avoid L lo hi -> FOtms_avoid (t :: L) lo hi.
Proof. intros t L lo hi Ht HL u [<-|Hin]; [exact Ht | exact (HL u Hin)]. Qed.
Lemma FOtms_avoid_app : forall L1 L2 lo hi,
  FOtms_avoid L1 lo hi -> FOtms_avoid L2 lo hi -> FOtms_avoid (L1 ++ L2) lo hi.
Proof.
  intros L1 L2 lo hi H1 H2 u Hin. apply in_app_or in Hin.
  destruct Hin as [Hin|Hin]; [exact (H1 u Hin) | exact (H2 u Hin)].
Qed.
Lemma FOtms_avoid_sub : forall L lo hi lo' hi',
  FOtms_avoid L lo hi -> lo <= lo' -> hi' <= hi -> FOtms_avoid L lo' hi'.
Proof. intros L lo hi lo' hi' H H1 H2 t Hin. exact (FOtm_avoid_sub t lo hi lo' hi' (H t Hin) H1 H2). Qed.

Lemma FOtm_avoid_numeral : forall k lo hi, FOtm_avoid (FOnumeral k) lo hi.
Proof.
  intros k lo hi w _ _. induction k as [|k IH]; cbn; [reflexivity | exact IH].
Qed.
Lemma FOtm_avoid_var : forall v lo hi, v < lo \/ hi <= v -> FOtm_avoid (FOVar v) lo hi.
Proof. intros v lo hi H w H1 H2. cbn. apply Nat.eqb_neq. lia. Qed.
Lemma FOtm_avoid_zero : forall lo hi, FOtm_avoid FOZero lo hi.
Proof. intros lo hi w _ _. reflexivity. Qed.
Lemma FOtm_avoid_succ : forall t lo hi, FOtm_avoid t lo hi -> FOtm_avoid (FOSucc t) lo hi.
Proof. intros t lo hi H w H1 H2. cbn. exact (H w H1 H2). Qed.

(** Discharging avoidance: literals directly, argument terms from the
    hypotheses in the context. *)

Ltac avoid_tm :=
  lazymatch goal with
  | |- FOtm_avoid (FOnumeral _) _ _ => apply FOtm_avoid_numeral
  | |- FOtm_avoid FOZero _ _ => apply FOtm_avoid_zero
  | |- FOtm_avoid (FOSucc _) _ _ => apply FOtm_avoid_succ; avoid_tm
  | |- FOtm_avoid (FOVar _) _ _ => apply FOtm_avoid_var; lia
  | |- FOtm_avoid ?t ?lo ?hi =>
      match goal with
      | H : FOtms_avoid ?L ?lo' ?hi' |- _ =>
          apply (FOtm_avoid_sub t lo' hi' lo hi); [apply H; simpl; tauto | lia | lia]
      end
  end.

Ltac avoid_tms :=
  lazymatch goal with
  | |- FOtms_avoid (_ ++ _) _ _ => apply FOtms_avoid_app; avoid_tms
  | |- FOtms_avoid (_ :: _) _ _ => apply FOtms_avoid_cons; [avoid_tm | avoid_tms]
  | |- FOtms_avoid [] _ _ => apply FOtms_avoid_nil
  | |- FOtms_avoid (FOtab_terms ?T) ?lo ?hi =>
      match goal with
      | H : FOtms_avoid ?L ?lo' ?hi' |- _ =>
          apply (FOtms_avoid_sub _ lo' hi' lo hi); [|lia|lia];
          intros u Hu; apply H; simpl in Hu |- *; tauto
      end
  end.

(** Tactics for symbolic side conditions: list membership by a
    linear scan, capture-freedom by the head of the formula, and a
    rewrite database restricted to the connectives. *)

Ltac in_list := solve [simpl; repeat (first [left; reflexivity | right])].

Ltac ok_fast_leaf V := fail.

Ltac ok_fast V :=
  lazymatch goal with
  | |- FOsubst_ok _ _ (FOAnd _ _) = true => apply FOsubst_ok_and; ok_fast V
  | |- FOsubst_ok _ _ (FOOr _ _) = true => apply FOsubst_ok_or; ok_fast V
  | |- FOsubst_ok _ _ (FONeg _) = true => apply FOsubst_ok_neg; ok_fast V
  | |- FOsubst_ok _ _ (FOImplF _ _) = true => apply FOsubst_ok_impl; ok_fast V
  | |- FOsubst_ok _ _ FOFalseF = true => apply FOsubst_ok_false
  | |- FOsubst_ok _ _ (FOEq _ _) = true => apply FOsubst_ok_eq
  | |- FOsubst_ok _ _ (FOExists _ _) = true =>
      apply FOsubst_ok_ex; [apply V; lia | ok_fast V]
  | |- FOsubst_ok _ _ (FOForall _ _) = true =>
      apply FOsubst_ok_all; [apply V; lia | ok_fast V]
  | |- FOsubst_ok _ _ (FObetaF _ _ _ _ _) = true =>
      apply FOsubst_ok_betaF; refine (FOtm_avoid_sub _ _ _ _ _ V _ _); lia
  | |- FOsubst_ok _ _ (FOltv _ _) = true => unfold FOltv; ok_fast V
  | |- _ => ok_fast_leaf V
  end.

Create HintDb fosub0.
Hint Rewrite FOsubst_t_zero FOsubst_t_succ FOsubst_t_plus FOsubst_t_mult
  FOsubst_t_numeral FOsubst_f_eq FOsubst_f_false FOsubst_f_impl FOsubst_f_neg
  FOsubst_f_and FOsubst_f_or FOsubst_f_cpairF FOsubst_t_var_eq' : fosub0.
Hint Rewrite FOsubst_t_var_ne FOsubst_f_ex_ne FOsubst_f_all_ne FOsubst_f_bex
  FOsubst_f_ball FOsubst_f_betaF using lia : fosub0.

Ltac subst_avoid :=
  repeat match goal with
  | Hav : FOtms_avoid ?L ?lo ?hi |- context [FOsubst_t ?w ?s ?t] =>
      is_var t;
      rewrite (FOsubst_t_not_in t w s (Hav t ltac:(in_list) w ltac:(lia) ltac:(lia)))
  | Hav : FOtms_avoid ?L ?lo ?hi, H : context [FOsubst_t ?w ?s ?t] |- _ =>
      is_var t;
      rewrite (FOsubst_t_not_in t w s (Hav t ltac:(in_list) w ltac:(lia) ltac:(lia))) in H
  end.

Ltac av H :=
  lazymatch goal with
  | |- FOtm_avoid ?t ?lo ?hi =>
      lazymatch type of H with
      | FOtms_avoid ?L ?lo' ?hi' =>
          apply (FOtm_avoid_sub t lo' hi' lo hi); [apply H; simpl; tauto | lia | lia]
      end
  end.

Lemma FOctx_avoid_app1 : forall G A lo hi,
  FOctx_avoid G lo hi -> (forall w, lo <= w -> w < hi -> FOfree_in w A = false) ->
  FOctx_avoid (G ++ [A]) lo hi.
Proof.
  intros G A lo hi HG HA w H1 H2. apply FOfree_ctx_app1; [apply HG | apply HA]; lia.
Qed.

Lemma FOfree_in_ltv : forall w v a,
  w <> v -> FOin_tm w a = false -> FOfree_in w (FOltv v a) = false.
Proof.
  intros w v a H1 H2. unfold FOltv. cbn [FOfree_in FOin_tm].
  destruct (Nat.eqb (S v) w); [reflexivity|].
  rewrite (proj2 (Nat.eqb_neq v w) ltac:(lia)), H2.
  destruct (Nat.eqb (S v) w); reflexivity.
Qed.

Lemma FOtm_avoid_in : forall L t lo hi lo' hi',
  FOtms_avoid L lo hi -> In t L -> lo <= lo' -> hi' <= hi -> FOtm_avoid t lo' hi'.
Proof.
  intros L t lo hi lo' hi' H Hin H1 H2.
  exact (FOtm_avoid_sub t lo hi lo' hi' (H t Hin) H1 H2).
Qed.

(** Renaming the binder of an existential over an equation. *)

Lemma FOPrH_exeq_rename : forall n G z z' t a,
  z <> z' -> FOin_tm z' t = false -> FOin_tm z' a = false ->
  FOin_tm z t = false -> FOin_tm z a = false ->
  FOPrH n G (FOExists z (FOEq (FOPlus t (FOSucc (FOVar z))) a) .->
             FOExists z' (FOEq (FOPlus t (FOSucc (FOVar z'))) a)).
Proof.
  intros n G z z' t a Hz H1 H2 H3 H4.
  pose proof (FOPr_ex_rename n z z' (FOEq (FOPlus t (FOSucc (FOVar z))) a)) as R.
  specialize (R ltac:(cbn [FOfree_in FOin_tm]; rewrite H1, H2; nat_eqb_simpl; reflexivity)
                eq_refl).
  autorewrite with fosubst in R.
  rewrite (FOsubst_t_not_in t z _ H3), (FOsubst_t_not_in a z _ H4) in R.
  exact (FOPrH_thm n G _ R).
Qed.

(** ** Reads at one position.

    [FOROWAG c d c' d' j j']: the element of [c, d] at [j] is the
    element of [c', d'] at [j']. *)

Definition FOROWAG (c d c' d' j j' : FOTerm) : FOFormula :=
  FOForall 471 (FOImplF (FObetaF 480 c d j (FOVar 471)) (FObetaF 484 c' d' j' (FOVar 471))).

Lemma FOsubst_f_ROWAG : forall x s c d c' d' j j', x < 471 ->
  FOsubst_f x s (FOROWAG c d c' d' j j') =
  FOROWAG (FOsubst_t x s c) (FOsubst_t x s d) (FOsubst_t x s c') (FOsubst_t x s d')
    (FOsubst_t x s j) (FOsubst_t x s j').
Proof. intros. unfold FOROWAG. autorewrite with fosubst. reflexivity. Qed.
Hint Rewrite FOsubst_f_ROWAG using lia : fosubst.

Lemma FOsubst_ok_ROWAG : forall x s c d c' d' j j', FOtm_avoid s 471 488 ->
  FOsubst_ok x s (FOROWAG c d c' d' j j') = true.
Proof.
  intros x s c d c' d' j j' H. unfold FOROWAG.
  apply FOsubst_ok_all; [apply H; lia|].
  apply FOsubst_ok_impl; apply FOsubst_ok_betaF;
    refine (FOtm_avoid_sub s 471 488 _ _ H _ _); lia.
Qed.

Hint Rewrite FOsubst_f_ROWAG using lia : fosub0.

Ltac ok_fast_leaf V ::=
  lazymatch goal with
  | |- FOsubst_ok _ _ (FOROWAG _ _ _ _ _ _) = true =>
      apply FOsubst_ok_ROWAG; refine (FOtm_avoid_sub _ _ _ _ _ V _ _); lia
  end.

Lemma FOPrH_row_beta : forall n G c d c' d' j j' x v,
  FOPrH n G (FOROWAG c d c' d' j j') ->
  v + 4 <= 420 -> FOctx_avoid G v (v + 4) -> FOctx_avoid G 480 488 ->
  FOtms_avoid [c; d; c'; d'; j; j'; x] 471 488 ->
  FOtms_avoid [c; d; c'; d'; j; j'; x] v (v + 4) ->
  FOPrH n G (FObetaF v c d j x .-> FObetaF v c' d' j' x).
Proof.
  intros n G c d c' d' j j' x v HR Hv HG1 HG2 Hav1 Hav2.
  assert (A1 : forall u, In u [c; d; c'; d'; j; j'; x] -> FOtm_avoid u 480 (480 + 4)).
  { intros u Hu. exact (FOtm_avoid_in _ u 471 488 480 (480 + 4) Hav1 Hu ltac:(lia) ltac:(lia)). }
  assert (A2 : forall u, In u [c; d; c'; d'; j; j'; x] -> FOtm_avoid u 484 (484 + 4)).
  { intros u Hu. exact (FOtm_avoid_in _ u 471 488 484 (484 + 4) Hav1 Hu ltac:(lia) ltac:(lia)). }
  assert (A3 : forall u, In u [c; d; c'; d'; j; j'; x] -> FOin_tm 471 u = false).
  { intros u Hu. exact (Hav1 u Hu 471 ltac:(lia) ltac:(lia)). }
  assert (O : FOsubst_ok 471 x (FOImplF (FObetaF 480 c d j (FOVar 471))
                                        (FObetaF 484 c' d' j' (FOVar 471))) = true).
  { apply FOsubst_ok_impl; apply FOsubst_ok_betaF;
      [apply A1 | apply A2]; simpl; tauto. }
  pose proof (FOPrH_all_elim n G 471 x _ O HR) as H1.
  autorewrite with fosubst in H1.
  repeat rewrite (FOsubst_t_not_in _ 471 x) in H1 by (apply A3; simpl; tauto).
  apply (FOPrH_imp_trans n G _ (FObetaF 480 c d j x)).
  { apply (FOPrH_beta_rebase n G v 480 c d j x ltac:(lia)
             (fun w H1 H2 => HG2 w ltac:(lia) ltac:(lia)));
      first [apply Hav2; simpl; tauto | apply A1; simpl; tauto]. }
  apply (FOPrH_imp_trans n G _ (FObetaF 484 c' d' j' x)); [exact H1|].
  apply (FOPrH_beta_rebase n G 484 v c' d' j' x ltac:(lia) HG1);
    first [apply Hav2; simpl; tauto | apply A2; simpl; tauto].
Qed.

(** ** Row inclusion.

    [FOINCL T T']: every row of [T] is a row of [T']. *)

Definition FOROWMAP (T T' : FOtab) (j j' : FOTerm) : FOFormula :=
  FOAnd (FOROWAG (tct T) (tdt T) (tct T') (tdt T') j j')
  (FOAnd (FOROWAG (tc1 T) (td1 T) (tc1 T') (td1 T') j j')
  (FOAnd (FOROWAG (tc2 T) (td2 T) (tc2 T') (td2 T') j j')
  (FOAnd (FOROWAG (tc3 T) (td3 T) (tc3 T') (td3 T') j j')
         (FOROWAG (tcr T) (tdr T) (tcr T') (tdr T') j j')))).

Definition FOINCL (T T' : FOtab) : FOFormula :=
  FOForall 460 (FOImplF (FOExists 461 (FOEq (FOPlus (FOVar 460) (FOSucc (FOVar 461))) (tlen T)))
    (FOExists 462 (FOAnd (FOExists 463 (FOEq (FOPlus (FOVar 462) (FOSucc (FOVar 463)))
                                              (tlen T')))
                         (FOROWMAP T T' (FOVar 460) (FOVar 462))))).

Definition FOTabAgree (n : nat) (G : list FOFormula) (T T' : FOtab) : Prop :=
  FOPrH n G (FOINCL T T').

Lemma FOTabAgree_weak : forall n G L T T',
  FOTabAgree n G T T' -> FOTabAgree n (G ++ L) T T'.
Proof. intros n G L T T' H. exact (FOPrH_weak_app n G L _ H). Qed.

Ltac subst_tab :=
  repeat match goal with
  | Hav : FOtms_avoid ?L 420 500 |- context [FOsubst_t ?w ?s ?t] =>
      (constr_eq w 460 || constr_eq w 462 || constr_eq w 499 || constr_eq w 463 ||
       constr_eq w 461);
      rewrite (FOsubst_t_not_in t w s (Hav t ltac:(simpl; tauto) w ltac:(lia) ltac:(lia)))
  end.


(** Freshness of a variable outside every argument. *)

Lemma FOfree_in_betaF_not : forall w v c d i x,
  2 <= w -> FOin_tm w c = false -> FOin_tm w d = false -> FOin_tm w i = false ->
  FOin_tm w x = false -> FOfree_in w (FObetaF v c d i x) = false.
Proof.
  intros w v c d i x H0 H1 H2 H3 H4.
  destruct (FOfree_in w (FObetaF v c d i x)) eqn:E; [|reflexivity].
  apply FObetaF_free in E. destruct E as [E|[E|[E|[E|E]]]]; congruence || lia.
Qed.

Lemma FOfree_in_all_ne : forall w y X, y <> w -> FOfree_in w (FOForall y X) = FOfree_in w X.
Proof. intros w y X H. cbn [FOfree_in]. rewrite (proj2 (Nat.eqb_neq y w) H). reflexivity. Qed.

Lemma FOfree_in_impl : forall w A B,
  FOfree_in w (FOImplF A B) = (FOfree_in w A || FOfree_in w B)%bool.
Proof. reflexivity. Qed.

Lemma FOin_tm_var_ne : forall w y, y <> w -> FOin_tm w (FOVar y) = false.
Proof. intros w y H. cbn [FOin_tm]. apply Nat.eqb_neq. exact H. Qed.

Lemma FOfree_in_ROWAG_not : forall w c d c' d' j j',
  2 <= w -> w <> 471 -> FOtms_avoid [c; d; c'; d'; j; j'] w (S w) ->
  FOfree_in w (FOROWAG c d c' d' j j') = false.
Proof.
  intros w c d c' d' j j' H1 H2 Hav. unfold FOROWAG.
  rewrite FOfree_in_all_ne by lia. rewrite FOfree_in_impl.
  assert (V : FOin_tm w (FOVar 471) = false) by (apply FOin_tm_var_ne; lia).
  assert (A : forall u, In u [c; d; c'; d'; j; j'] -> FOin_tm w u = false)
    by (intros u Hu; exact (Hav u Hu w ltac:(lia) ltac:(lia))).
  rewrite (FOfree_in_betaF_not w 480 c d j (FOVar 471) H1), (FOfree_in_betaF_not w 484 c' d' j'
    (FOVar 471) H1); try reflexivity; try exact V; apply A; simpl; tauto.
Qed.

Lemma FOfree_in_exeq_not : forall w z t a,
  FOin_tm w t = false -> FOin_tm w a = false ->
  FOfree_in w (FOExists z (FOEq (FOPlus t (FOSucc (FOVar z))) a)) = false.
Proof.
  intros w z t a H1 H2. cbn [FOfree_in FOin_tm].
  destruct (Nat.eqb z w) eqn:E; [reflexivity|]. rewrite H1, H2. reflexivity.
Qed.

Lemma FOPrH_ex_imp : forall n G x A C,
  FOfree_ctx x G -> FOPrH n (G ++ [A]) (FOExists x C) ->
  FOPrH n G (FOExists x A .-> FOExists x C).
Proof.
  intros n G x A C Hx H. apply FOPrH_intro.
  apply (FOPrH_ex_elim n (G ++ [FOExists x A]) x A);
    [apply FOfree_ctx_app1; [exact Hx | apply FOfree_in_ex_self]
    | apply FOfree_in_ex_self | apply FOPrH_last |].
  apply (FOPrH_weaken n (G ++ [A])); [|exact H].
  intros Y Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - apply in_or_app. left. apply in_or_app. left. exact Hin.
  - apply in_or_app. right. exact Hin.
Qed.


Ltac in_T H1 H2 :=
  lazymatch goal with
  | |- FOin_tm ?w (FOVar ?y) = false => apply FOin_tm_var_ne; lia
  | |- FOin_tm ?w ?t = false =>
      first [ apply (H1 t ltac:(in_list)); lia | apply (H2 t ltac:(in_list)); lia ]
  end.

Ltac rowb HR HG3a HG3b H1 H2 v :=
  apply (FOPrH_row_beta _ _ _ _ _ _ _ _ _ v HR ltac:(lia) (HG3a v ltac:(lia) ltac:(lia)) HG3b);
  repeat (apply FOtms_avoid_cons;
          [ first [ apply FOtm_avoid_var; lia
                  | match goal with |- FOtm_avoid ?t ?lo ?hi =>
                      match type of H1 with FOtms_avoid _ ?l1 ?h1 =>
                      match type of H2 with FOtms_avoid _ ?l2 ?h2 =>
                        first [ exact (FOtm_avoid_sub t l1 h1 lo hi (H1 t ltac:(in_list))
                                         ltac:(lia) ltac:(lia))
                              | exact (FOtm_avoid_sub t l2 h2 lo hi (H2 t ltac:(in_list))
                                         ltac:(lia) ltac:(lia)) ]
                      end end end ]
          |]);
  apply FOtms_avoid_nil.

(** A lookup in [T] is a lookup in [T'] when the rows of [T] are rows
    of [T']. *)

Lemma FOPrH_lookup_tr : forall n G B T T' tg a1 a2 a3 r,
  FOPrH n G (FOINCL T T') -> B + 22 <= 420 ->
  FOctx_avoid G B (B + 22) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r]) B (B + 22) ->
  FOPrH n G (FOlookupT B T tg a1 a2 a3 r .-> FOlookupT B T' tg a1 a2 a3 r).
Proof.
  intros n G B T T' tg a1 a2 a3 r HI HB HG HG2 Hav1 Hav2.
  destruct T as [ct dt c1 d1 c2 d2 c3 d3 cr dr len].
  destruct T' as [ct' dt' c1' d1' c2' d2' c3' d3' cr' dr' len'].
  unfold FOlookupT, FOtab_terms, FOINCL, FOROWMAP in *.
  cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen app] in *.
  unfold FOlookup, FOBexC. fold (FOltv B len). fold (FOltv B len').
  apply FOPrH_ex_imp; [apply HG; lia|].
  set (A1 := FOAnd (FOltv B len)
               (FOAnd (FObetaF (B + 2) ct dt (FOVar B) tg)
               (FOAnd (FObetaF (B + 6) c1 d1 (FOVar B) a1)
               (FOAnd (FObetaF (B + 10) c2 d2 (FOVar B) a2)
               (FOAnd (FObetaF (B + 14) c3 d3 (FOVar B) a3)
                      (FObetaF (B + 18) cr dr (FOVar B) r)))))).
  assert (FA1 : forall w, 2 <= w -> w <> B ->
                  (forall t, In t [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len;
                                   tg; a1; a2; a3; r] -> FOin_tm w t = false) ->
                  FOfree_in w A1 = false).
  { intros w W1 W2 WT. unfold A1. repeat rewrite FOfree_in_FOAnd.
    rewrite FOfree_in_ltv by (lia || (apply WT; in_list)).
    repeat rewrite FOfree_in_betaF_not; try reflexivity; try lia;
      first [ apply FOin_tm_var_ne; lia | apply WT; in_list ]. }
  assert (Hb : FOPrH n (G ++ [A1])
                 (FOExists 461 (FOEq (FOPlus (FOVar B) (FOSucc (FOVar 461))) len))).
  { apply (FOPrH_mp _ _ _ _ (FOPrH_exeq_rename n _ (S B) 461 (FOVar B) len ltac:(lia)
             ltac:(apply FOin_tm_var_ne; lia) ltac:(in_T Hav1 Hav2)
             ltac:(apply FOin_tm_var_ne; lia) ltac:(in_T Hav1 Hav2))).
    exact (FOPrH_and_l _ _ _ _ (FOPrH_last n G A1)). }
  assert (VB : FOtm_avoid (FOVar B) 420 500) by (apply FOtm_avoid_var; lia).
  assert (V9 : FOtm_avoid (FOVar 499) 0 499) by (apply FOtm_avoid_var; lia).
  (* the inclusion at [B] *)
  pose proof (FOPrH_weak_app n G [A1] _ HI) as HI1.
  lazymatch type of HI1 with
  | FOPrH _ _ (FOForall 460 ?BD) =>
      assert (O1 : FOsubst_ok 460 (FOVar B) BD = true) by ok_fast VB;
      pose proof (FOPrH_all_elim n (G ++ [A1]) 460 (FOVar B) BD O1 HI1) as H1
  end.
  autorewrite with fosub0 in H1. subst_avoid.
  pose proof (FOPrH_mp _ _ _ _ H1 Hb) as H2. clear H1 HI1.
  assert (RW : forall w jp, 2 <= w -> w <> 471 -> w <> B -> FOin_tm w jp = false ->
                 (forall t, In t [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr;
                                  ct'; dt'; c1'; d1'; c2'; d2'; c3'; d3'; cr'; dr']
                            -> FOin_tm w t = false) ->
                 FOfree_in w (FOAnd (FOROWAG ct dt ct' dt' (FOVar B) jp)
                              (FOAnd (FOROWAG c1 d1 c1' d1' (FOVar B) jp)
                              (FOAnd (FOROWAG c2 d2 c2' d2' (FOVar B) jp)
                              (FOAnd (FOROWAG c3 d3 c3' d3' (FOVar B) jp)
                                     (FOROWAG cr dr cr' dr' (FOVar B) jp))))) = false).
  { intros w jp W1 W2 W3 W4 WT. repeat rewrite FOfree_in_FOAnd.
    repeat rewrite FOfree_in_ROWAG_not; try reflexivity; try lia;
      intros u Hu w' H1' H2'; replace w' with w by lia; simpl in Hu;
      repeat (destruct Hu as [<-|Hu]; [first [ exact W4 | apply WT; in_list
                                             | apply FOin_tm_var_ne; lia]|]);
      destruct Hu. }
  lazymatch type of H2 with
  | FOPrH _ _ (FOExists 462 ?A) =>
      apply (FOPrH_ex_elim_fresh n (G ++ [A1]) 462 499 A); [| | | | exact H2 |]
  end.
  - apply FOfree_ctx_app1; [apply HG2; lia | apply FA1; [lia | lia|]].
    intros t Ht. apply (Hav1 t ltac:(simpl in Ht |- *; tauto)); lia.
  - cbn [FOfree_in]. rewrite (proj2 (Nat.eqb_neq B 499) ltac:(lia)).
    rewrite FOfree_in_FOAnd, FOfree_in_ltv by (lia || in_T Hav1 Hav2).
    repeat rewrite FOfree_in_FOAnd.
    repeat rewrite FOfree_in_betaF_not; try reflexivity; try lia; in_T Hav1 Hav2.
  - rewrite FOfree_in_FOAnd, FOfree_in_exeq_not by (in_T Hav1 Hav2).
    rewrite RW; [reflexivity | lia | lia | lia | apply FOin_tm_var_ne; lia |].
    intros t Ht. apply (Hav1 t ltac:(simpl in Ht |- *; tauto)); lia.
  - ok_fast V9.
  - autorewrite with fosub0. subst_avoid.
    unfold FOltv.
    apply (FOPrH_ex_intro _ _ B (FOVar 499)); [ok_fast V9|].
    autorewrite with fosub0. subst_avoid.
    match goal with |- FOPrH _ ((G ++ [A1]) ++ [?X]) _ =>
      pose proof (FOPrH_last n (G ++ [A1]) X) as HA2;
      set (A2 := X) in *; set (G3 := (G ++ [A1]) ++ [A2]) in *
    end.
    assert (HA1 : FOPrH n G3 A1) by (apply FOPrH_weak_app; apply FOPrH_last).
    assert (FA2 : forall w, 2 <= w -> w <> 471 -> w <> B -> w <> 499 -> w <> 463 ->
                    (forall t, In t [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len';
                                     ct'; dt'; c1'; d1'; c2'; d2'; c3'; d3'; cr'; dr']
                               -> FOin_tm w t = false) ->
                    FOfree_in w A2 = false).
    { intros w W1 W2 W3 W4 W5 WT. unfold A2.
      rewrite FOfree_in_FOAnd, FOfree_in_exeq_not;
        [| apply FOin_tm_var_ne; lia | apply WT; in_list].
      rewrite RW; [reflexivity | lia | lia | lia | apply FOin_tm_var_ne; lia |].
      intros t Ht. apply WT. simpl in Ht |- *. tauto. }
    apply FOPrH_and_intro.
    + apply (FOPrH_mp _ _ _ _ (FOPrH_exeq_rename n G3 463 (S B) (FOVar 499) len' ltac:(lia)
               ltac:(apply FOin_tm_var_ne; lia) ltac:(in_T Hav1 Hav2)
               ltac:(apply FOin_tm_var_ne; lia) ltac:(in_T Hav1 Hav2))).
      exact (FOPrH_and_l _ _ _ _ HA2).
    + pose proof (FOPrH_and_r _ _ _ _ HA2) as HR.
      pose proof (FOPrH_and_r _ _ _ _ HA1) as HB1.
      assert (HG3a : forall v, B + 2 <= v -> v + 4 <= B + 22 -> FOctx_avoid G3 v (v + 4)).
      { intros v Hv1 Hv2 w Hw1 Hw2. unfold G3.
        apply FOfree_ctx_app1; [apply FOfree_ctx_app1; [apply HG; lia|]|].
        - apply FA1; [lia | lia|]. intros t Ht. apply (Hav2 t ltac:(simpl in Ht |- *; tauto)); lia.
        - apply FA2; try lia.
          intros t Ht. apply (Hav2 t ltac:(simpl in Ht |- *; tauto)); lia. }
      assert (HG3b : FOctx_avoid G3 480 488).
      { intros w Hw1 Hw2. unfold G3.
        apply FOfree_ctx_app1; [apply FOfree_ctx_app1; [apply HG2; lia|]|].
        - apply FA1; [lia | lia|]. intros t Ht. apply (Hav1 t ltac:(simpl in Ht |- *; tauto)); lia.
        - apply FA2; try lia.
          intros t Ht. apply (Hav1 t ltac:(simpl in Ht |- *; tauto)); lia. }
      refine (FOPrH_mp _ _ _ _ _ HB1).
      apply FOPrH_and_mono; [rowb (FOPrH_and_l _ _ _ _ HR) HG3a HG3b Hav1 Hav2 (B + 2)|].
      pose proof (FOPrH_and_r _ _ _ _ HR) as HR1.
      apply FOPrH_and_mono; [rowb (FOPrH_and_l _ _ _ _ HR1) HG3a HG3b Hav1 Hav2 (B + 6)|].
      pose proof (FOPrH_and_r _ _ _ _ HR1) as HR2.
      apply FOPrH_and_mono; [rowb (FOPrH_and_l _ _ _ _ HR2) HG3a HG3b Hav1 Hav2 (B + 10)|].
      pose proof (FOPrH_and_r _ _ _ _ HR2) as HR3.
      apply FOPrH_and_mono; [rowb (FOPrH_and_l _ _ _ _ HR3) HG3a HG3b Hav1 Hav2 (B + 14)|].
      rowb (FOPrH_and_r _ _ _ _ HR3) HG3a HG3b Hav1 Hav2 (B + 18).
Qed.

(** ** Transfer of the table-dependent builders.

    [FOTabMono n G T T']: the rows of [T] are rows of [T'] and each code
    of [T] is at most the corresponding code of [T'], derivably in [G].
    Every builder that consults the table through lookups and bounds its
    witnesses by table codes transfers from [T] to [T']. *)

Definition FOTabMono (n : nat) (G : list FOFormula) (T T' : FOtab) : Prop :=
  FOTabAgree n G T T' /\
  FOPrH n G (FOle (FOSucc (tct T)) (FOSucc (tct T'))) /\
  FOPrH n G (FOle (FOSucc (tc1 T)) (FOSucc (tc1 T'))) /\
  FOPrH n G (FOle (FOSucc (tc2 T)) (FOSucc (tc2 T'))) /\
  FOPrH n G (FOle (FOSucc (tc3 T)) (FOSucc (tc3 T'))) /\
  FOPrH n G (FOle (FOSucc (tcr T)) (FOSucc (tcr T'))).


(** The leaf rules. *)

Lemma FOPrH_lookup_tr' : forall n G B T T' tg a1 a2 a3 r,
  FOTabMono n G T T' -> B + 22 <= 420 ->
  FOctx_avoid G B (B + 22) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r]) B (B + 22) ->
  FOPrH n G (FOlookup B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T) (td3 T)
               (tcr T) (tdr T) (tlen T) tg a1 a2 a3 r .->
             FOlookup B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') tg a1 a2 a3 r).
Proof.
  intros n G B T T' tg a1 a2 a3 r [HA _] HB HG HG2 H1 H2.
  exact (FOPrH_lookup_tr n G B T T' tg a1 a2 a3 r HA HB HG HG2 H1 H2).
Qed.

Lemma FOPrH_code_tr : forall n G v c c',
  FOPrH n G (FOle (FOSucc c) (FOSucc c')) -> v < 400 ->
  FOfree_ctx (S v) G -> FOctx_avoid G 420 500 ->
  FOtm_avoid c (S v) (S (S v)) -> FOtm_avoid c' (S v) (S (S v)) ->
  FOtm_avoid c 420 500 -> FOtm_avoid c' 420 500 ->
  FOPrH n G (FOltv v (FOSucc c) .-> FOltv v (FOSucc c')).
Proof.
  intros n G v c c' Hle Hv HG1 HG2 Hc1 Hc2 Hc3 Hc4.
  apply FOPrH_ltv_le; [exact Hle | exact HG1 | exact (HG2 498 ltac:(lia) ltac:(lia)) | lia
    | apply FOtm_avoid_succ; exact Hc1 | apply FOtm_avoid_succ; exact Hc2
    | apply FOtm_avoid_succ; exact (FOtm_avoid_sub c 420 500 498 499 Hc3 ltac:(lia) ltac:(lia))
    | apply FOtm_avoid_succ; exact (FOtm_avoid_sub c' 420 500 498 499 Hc4 ltac:(lia) ltac:(lia))].
Qed.

Ltac mono_code :=
  match goal with
  | Hm : FOTabMono _ _ ?T ?T' |- FOPrH _ _ (FOltv ?v (FOSucc ?c) .-> FOltv ?v (FOSucc ?c')) =>
      destruct Hm as (Hm0 & Hct & Hc1 & Hc2 & Hc3 & Hcr);
      first [ apply (FOPrH_code_tr _ _ v _ _ Hct) | apply (FOPrH_code_tr _ _ v _ _ Hc1)
            | apply (FOPrH_code_tr _ _ v _ _ Hc2) | apply (FOPrH_code_tr _ _ v _ _ Hc3)
            | apply (FOPrH_code_tr _ _ v _ _ Hcr) ];
      [ lia | match goal with HG : FOctx_avoid _ ?lo ?hi |- _ => apply HG; lia end
      | match goal with HG : FOctx_avoid _ 420 500 |- _ => exact HG end
      | avoid_tm | avoid_tm | avoid_tm | avoid_tm ]
  end.

(** The structural transfer.  [fo_tr_leaf] is extended with each
    builder's transfer lemma once it is proved; [tr_side] discharges
    the hypotheses shared by all of them. *)

Ltac tr_side :=
  lazymatch goal with
  | |- FOTabMono _ _ _ _ => assumption
  | |- _ <= _ => lia
  | |- FOctx_avoid _ _ _ =>
      first [ assumption
            | intros ? ? ?; match goal with HG : FOctx_avoid _ ?lo ?hi |- _ =>
                              apply HG; lia end ]
  | |- FOtms_avoid _ _ _ => avoid_tms
  end.

Ltac fo_tr_leaf := fail.

Ltac fo_tr :=
  lazymatch goal with
  | |- FOPrH _ _ (FOImplF ?A ?A') =>
      first [ constr_eq A A'; apply FOPrH_imp_refl
            | lazymatch A with
              | FOOr _ _ => apply FOPrH_or_mono; fo_tr
              | FOAnd _ _ => apply FOPrH_and_mono; fo_tr
              | FOBexC ?v _ _ =>
                  apply FOPrH_bex_mono;
                  [ match goal with HG : FOctx_avoid _ ?lo ?hi |- _ => apply HG; lia end
                  | first [ apply FOPrH_imp_refl | mono_code ]
                  | apply FOPrH_imp_weaken; fo_tr ]
              | FOlookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                  apply FOPrH_lookup_tr'; [assumption | lia
                    | intros ? ? ?; match goal with HG : FOctx_avoid _ ?lo ?hi |- _ =>
                                      apply HG; lia end
                    | assumption | avoid_tms | avoid_tms]
              | _ => fo_tr_leaf
              end ]
  end.

Lemma FOtr_STEP0 : forall n G B T T' w tc r,
  FOTabMono n G T T' -> B + 50 <= 420 ->
  FOctx_avoid G B (B + 50) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [w; tc; r]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [w; tc; r]) B (B + 50) ->
  FOPrH n G (FOSTEP0 B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T) (td3 T)
               (tcr T) (tdr T) (tlen T) w tc r .->
             FOSTEP0 B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') w tc r).
Proof. intros. unfold FOSTEP0. fo_tr. Qed.


Lemma FOtr_STEP_bin : forall n G B T T' w pc r k tg,
  FOTabMono n G T T' -> B + 50 <= 420 ->
  FOctx_avoid G B (B + 50) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [w; pc; r]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [w; pc; r]) B (B + 50) ->
  FOPrH n G (FOSTEP_bin B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T) (td3 T)
               (tcr T) (tdr T) (tlen T) w pc r k tg .->
             FOSTEP_bin B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') w pc r k tg).
Proof. intros. unfold FOSTEP_bin. fo_tr. Qed.

Lemma FOtr_STEP_quant0 : forall n G B T T' w pc r k tg,
  FOTabMono n G T T' -> B + 28 <= 420 ->
  FOctx_avoid G B (B + 28) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [w; pc; r]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [w; pc; r]) B (B + 28) ->
  FOPrH n G (FOSTEP_quant0 B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) w pc r k tg .->
             FOSTEP_quant0 B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') w pc r k tg).
Proof. intros. unfold FOSTEP_quant0. fo_tr. Qed.

Ltac fo_tr_leaf ::=
  lazymatch goal with
  | |- FOPrH _ _ (FOImplF ?A _) =>
      lazymatch A with
      | FOSTEP_bin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP_bin; tr_side
      | FOSTEP_quant0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP_quant0; tr_side
      end
  end.

Lemma FOtr_STEP1 : forall n G B T T' w pc r,
  FOTabMono n G T T' -> B + 50 <= 420 ->
  FOctx_avoid G B (B + 50) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [w; pc; r]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [w; pc; r]) B (B + 50) ->
  FOPrH n G (FOSTEP1 B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T) (td3 T)
               (tcr T) (tdr T) (tlen T) w pc r .->
             FOSTEP1 B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') w pc r).
Proof. intros. unfold FOSTEP1. fo_tr. Qed.

Lemma FOtr_STEP5 : forall n G B T T' a1 r,
  FOTabMono n G T T' -> B + 26 <= 420 ->
  FOctx_avoid G B (B + 26) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [a1; r]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [a1; r]) B (B + 26) ->
  FOPrH n G (FOSTEP5 B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T) (td3 T)
               (tcr T) (tdr T) (tlen T) a1 r .->
             FOSTEP5 B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') a1 r).
Proof. intros. unfold FOSTEP5. fo_tr. Qed.

Lemma FOtr_STEP_substbin : forall n G B T T' y sc tc r ktag lktag rtag,
  FOTabMono n G T T' -> B + 56 <= 420 ->
  FOctx_avoid G B (B + 56) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [y; sc; tc; r]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [y; sc; tc; r]) B (B + 56) ->
  FOPrH n G (FOSTEP_substbin B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) y sc tc r ktag lktag rtag .->
             FOSTEP_substbin B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T')
               (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') y sc tc r ktag lktag rtag).
Proof. intros. unfold FOSTEP_substbin. fo_tr. Qed.

Ltac fo_tr_leaf ::=
  lazymatch goal with
  | |- FOPrH _ _ (FOImplF ?A _) =>
      lazymatch A with
      | FOSTEP_substbin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          apply FOtr_STEP_substbin; tr_side
      end
  end.

Lemma FOtr_STEP2 : forall n G B T T' y sc tc r,
  FOTabMono n G T T' -> B + 56 <= 420 ->
  FOctx_avoid G B (B + 56) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [y; sc; tc; r]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [y; sc; tc; r]) B (B + 56) ->
  FOPrH n G (FOSTEP2 B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T) (td3 T)
               (tcr T) (tdr T) (tlen T) y sc tc r .->
             FOSTEP2 B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') y sc tc r).
Proof. intros. unfold FOSTEP2. fo_tr. Qed.

Lemma FOtr_STEP_substquant : forall n G B T T' y sc pc r ktag,
  FOTabMono n G T T' -> B + 32 <= 420 ->
  FOctx_avoid G B (B + 32) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [y; sc; pc; r]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [y; sc; pc; r]) B (B + 32) ->
  FOPrH n G (FOSTEP_substquant B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) y sc pc r ktag .->
             FOSTEP_substquant B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T')
               (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') y sc pc r ktag).
Proof. intros. unfold FOSTEP_substquant. fo_tr. Qed.

Ltac fo_tr_leaf ::=
  lazymatch goal with
  | |- FOPrH _ _ (FOImplF ?A _) =>
      lazymatch A with
      | FOSTEP_substbin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          apply FOtr_STEP_substbin; tr_side
      | FOSTEP_substquant _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          apply FOtr_STEP_substquant; tr_side
      end
  end.

Lemma FOtr_STEP3 : forall n G B T T' y sc pc r,
  FOTabMono n G T T' -> B + 56 <= 420 ->
  FOctx_avoid G B (B + 56) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [y; sc; pc; r]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [y; sc; pc; r]) B (B + 56) ->
  FOPrH n G (FOSTEP3 B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T) (td3 T)
               (tcr T) (tdr T) (tlen T) y sc pc r .->
             FOSTEP3 B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') y sc pc r).
Proof. intros. unfold FOSTEP3. fo_tr. Qed.

Lemma FOtr_STEP_subokbin : forall n G B T T' y sc pc r,
  FOTabMono n G T T' -> B + 50 <= 420 ->
  FOctx_avoid G B (B + 50) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [y; sc; pc; r]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [y; sc; pc; r]) B (B + 50) ->
  FOPrH n G (FOSTEP_subokbin B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) y sc pc r .->
             FOSTEP_subokbin B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T')
               (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') y sc pc r).
Proof. intros. unfold FOSTEP_subokbin. fo_tr. Qed.

Lemma FOtr_STEP_subokquant : forall n G B T T' y sc pc r k,
  FOTabMono n G T T' -> B + 72 <= 420 ->
  FOctx_avoid G B (B + 72) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [y; sc; pc; r]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [y; sc; pc; r]) B (B + 72) ->
  FOPrH n G (FOSTEP_subokquant B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) y sc pc r k .->
             FOSTEP_subokquant B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T')
               (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') y sc pc r k).
Proof. intros. unfold FOSTEP_subokquant. fo_tr. Qed.

Ltac fo_tr_leaf ::=
  lazymatch goal with
  | |- FOPrH _ _ (FOImplF ?A _) =>
      lazymatch A with
      | FOSTEP_subokbin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          apply FOtr_STEP_subokbin; tr_side
      | FOSTEP_subokquant _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          apply FOtr_STEP_subokquant; tr_side
      end
  end.

Lemma FOtr_STEP4 : forall n G B T T' y sc pc r,
  FOTabMono n G T T' -> B + 72 <= 420 ->
  FOctx_avoid G B (B + 72) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [y; sc; pc; r]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [y; sc; pc; r]) B (B + 72) ->
  FOPrH n G (FOSTEP4 B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T) (td3 T)
               (tcr T) (tdr T) (tlen T) y sc pc r .->
             FOSTEP4 B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') y sc pc r).
Proof. intros. unfold FOSTEP4. fo_tr. Qed.

Ltac fo_tr_leaf ::=
  lazymatch goal with
  | |- FOPrH _ _ (FOImplF ?A _) =>
      lazymatch A with
      | FOSTEP0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP0; tr_side
      | FOSTEP1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP1; tr_side
      | FOSTEP2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP2; tr_side
      | FOSTEP3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP3; tr_side
      | FOSTEP4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP4; tr_side
      | FOSTEP5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP5; tr_side
      end
  end.

(** Justification builders that consult only the table. *)

Lemma FOtr_LOGc : forall n G B T T' d,
  FOTabMono n G T T' -> B + 82 <= 420 ->
  FOctx_avoid G B (B + 82) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) B (B + 82) ->
  FOPrH n G (FOLOGc B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T) (td3 T)
               (tcr T) (tdr T) (tlen T) d .->
             FOLOGc B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') d).
Proof. intros. unfold FOLOGc, FOLOG10c, FOLOG12c. fo_tr. Qed.

Lemma FOtr_AXREFLc : forall n G B T T' c d,
  FOTabMono n G T T' -> B + 58 <= 420 ->
  FOctx_avoid G B (B + 58) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) B (B + 58) ->
  FOPrH n G (FOAXREFLc B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) c d .->
             FOAXREFLc B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') c d).
Proof. intros. unfold FOAXREFLc. fo_tr. Qed.

Lemma FOtr_REFLSc : forall n G B T T' cores d,
  FOTabMono n G T T' -> B + 58 <= 420 ->
  FOctx_avoid G B (B + 58) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) B (B + 58) ->
  FOPrH n G (FOREFLSc B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) cores d .->
             FOREFLSc B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') cores d).
Proof.
  intros n G B T T' cores d Hm HB HG HG2 Hav1 Hav2.
  induction cores as [|c rest IH]; cbn [FOREFLSc]; [apply FOPrH_imp_refl|].
  apply FOPrH_or_mono; [apply FOtr_AXREFLc; tr_side | exact IH].
Qed.

Lemma FOtr_THAXc : forall n G B T T' cores d,
  FOTabMono n G T T' -> B + 72 <= 420 ->
  FOctx_avoid G B (B + 72) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) B (B + 72) ->
  FOPrH n G (FOTHAXc B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) cores d .->
             FOTHAXc B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') cores d).
Proof.
  intros. unfold FOTHAXc.
  apply FOPrH_or_mono; [apply FOPrH_imp_refl | apply FOtr_REFLSc; tr_side].
Qed.

Lemma FOtr_JSUBST : forall n G B T T' pat vd pl,
  FOTabMono n G T T' -> B + 74 + cpat_span pat <= 420 ->
  FOctx_avoid G B (B + 74 + cpat_span pat) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [vd; pl]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [vd; pl]) B (B + 74 + cpat_span pat) ->
  FOPrH n G (FOJSUBST B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) pat vd pl .->
             FOJSUBST B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') pat vd pl).
Proof. intros. unfold FOJSUBST. fo_tr. Qed.

Lemma FOtr_JIND : forall n G B T T' vd pl,
  FOTabMono n G T T' -> B + 140 <= 420 ->
  FOctx_avoid G B (B + 140) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [vd; pl]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [vd; pl]) B (B + 140) ->
  FOPrH n G (FOJIND B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) vd pl .->
             FOJIND B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') vd pl).
Proof. intros. unfold FOJIND. fo_tr. Qed.

Lemma FOtr_PROVAT : forall n G B T T' c z p,
  FOTabMono n G T T' -> B + 46 <= 420 ->
  FOctx_avoid G B (B + 46) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [z; p]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [z; p]) B (B + 46) ->
  FOPrH n G (FOPROVAT B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) c z p .->
             FOPROVAT B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') c z p).
Proof. intros. unfold FOPROVAT. fo_tr. Qed.

Lemma FOtr_GENF : forall n G B T T' z,
  FOTabMono n G T T' -> B + 24 <= 420 ->
  FOctx_avoid G B (B + 24) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [z]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [z]) B (B + 24) ->
  FOPrH n G (FOGENF B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) z .->
             FOGENF B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') z).
Proof. intros. unfold FOGENF. fo_tr. Qed.

Ltac fo_tr_leaf ::=
  lazymatch goal with
  | |- FOPrH _ _ (FOImplF ?A _) =>
      lazymatch A with
      | FOPROVAT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_PROVAT; tr_side
      | FOGENF _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_GENF; tr_side
      end
  end.

Lemma FOtr_D2c : forall n G B T T' c d,
  FOTabMono n G T T' -> B + 216 <= 420 ->
  FOctx_avoid G B (B + 216) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) B (B + 216) ->
  FOPrH n G (FOD2c B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) c d .->
             FOD2c B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') c d).
Proof. intros. unfold FOD2c. fo_tr. Qed.

Lemma FOtr_D3c : forall n G B T T' c d,
  FOTabMono n G T T' -> B + 130 <= 420 ->
  FOctx_avoid G B (B + 130) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) B (B + 130) ->
  FOPrH n G (FOD3c B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) c d .->
             FOD3c B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') c d).
Proof. intros. unfold FOD3c. fo_tr. Qed.

Lemma FOtr_DMONc : forall n G B T T' c c' d,
  FOTabMono n G T T' -> B + 130 <= 420 ->
  FOctx_avoid G B (B + 130) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) B (B + 130) ->
  FOPrH n G (FODMONc B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) c c' d .->
             FODMONc B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') c c' d).
Proof. intros. unfold FODMONc. fo_tr. Qed.

Lemma FOtr_D2Sc : forall n G B T T' cores d,
  FOTabMono n G T T' -> B + 216 <= 420 ->
  FOctx_avoid G B (B + 216) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) B (B + 216) ->
  FOPrH n G (FOD2Sc B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) cores d .->
             FOD2Sc B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') cores d).
Proof.
  intros n G B T T' cores d Hm HB HG HG2 Hav1 Hav2.
  induction cores as [|c rest IH]; cbn [FOD2Sc]; [apply FOPrH_imp_refl|].
  apply FOPrH_or_mono; [apply FOtr_D2c; tr_side | exact IH].
Qed.

Lemma FOtr_D3Sc : forall n G B T T' cores d,
  FOTabMono n G T T' -> B + 130 <= 420 ->
  FOctx_avoid G B (B + 130) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) B (B + 130) ->
  FOPrH n G (FOD3Sc B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) cores d .->
             FOD3Sc B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') cores d).
Proof.
  intros n G B T T' cores d Hm HB HG HG2 Hav1 Hav2.
  induction cores as [|c rest IH]; cbn [FOD3Sc]; [apply FOPrH_imp_refl|].
  apply FOPrH_or_mono; [apply FOtr_D3c; tr_side | exact IH].
Qed.

Lemma FOtr_DMONS1 : forall n G B T T' c cs d,
  FOTabMono n G T T' -> B + 130 <= 420 ->
  FOctx_avoid G B (B + 130) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) B (B + 130) ->
  FOPrH n G (FODMONS1 B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) c cs d .->
             FODMONS1 B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') c cs d).
Proof.
  intros n G B T T' c cs d Hm HB HG HG2 Hav1 Hav2.
  induction cs as [|c' rest IH]; cbn [FODMONS1]; [apply FOPrH_imp_refl|].
  apply FOPrH_or_mono; [apply FOtr_DMONc; tr_side | exact IH].
Qed.

Lemma FOtr_DMONSc : forall n G B T T' cores d,
  FOTabMono n G T T' -> B + 130 <= 420 ->
  FOctx_avoid G B (B + 130) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [d]) B (B + 130) ->
  FOPrH n G (FODMONSc B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) cores d .->
             FODMONSc B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') cores d).
Proof.
  intros n G B T T' cores d Hm HB HG HG2 Hav1 Hav2.
  induction cores as [|c rest IH]; cbn [FODMONSc]; [apply FOPrH_imp_refl|].
  apply FOPrH_or_mono; [apply FOtr_DMONS1; tr_side | exact IH].
Qed.
(** Code bounds from any hypothesis of the context, and reads through
    any matching agreement. *)

Ltac mono_code' :=
  match goal with
  | H : FOPrH _ _ (FOle (FOSucc ?c) (FOSucc ?c'))
    |- FOPrH _ _ (FOltv ?v (FOSucc ?c) .-> FOltv ?v (FOSucc ?c')) =>
      apply (FOPrH_code_tr _ _ v c c' H);
      [ lia | match goal with HG : FOctx_avoid _ ?lo ?hi |- _ => apply HG; lia end
      | match goal with HG : FOctx_avoid _ 420 500 |- _ => exact HG end
      | avoid_tm | avoid_tm | avoid_tm | avoid_tm ]
  end.

Ltac mono_row :=
  match goal with
  | H : FOPrH _ _ (FOROWAG ?c ?d ?c' ?d' ?j ?j')
    |- FOPrH _ _ (FObetaF ?v ?c ?d ?j ?x .-> FObetaF ?v ?c' ?d' ?j' ?x) =>
      apply (FOPrH_row_beta _ _ c d c' d' j j' x v H);
      [ lia | intros ? ? ?; match goal with HG : FOctx_avoid _ ?lo ?hi |- _ =>
                              apply HG; lia end
      | intros ? ? ?; match goal with HG : FOctx_avoid _ ?lo ?hi |- _ =>
                        apply HG; lia end
      | avoid_tms | avoid_tms ]
  end.

Ltac fo_tr2 :=
  lazymatch goal with
  | |- FOPrH _ _ (FOImplF ?A ?A') =>
      first [ constr_eq A A'; apply FOPrH_imp_refl
            | lazymatch A with
              | FOOr _ _ => apply FOPrH_or_mono; fo_tr2
              | FOAnd _ _ => apply FOPrH_and_mono; fo_tr2
              | FOBexC ?v _ _ =>
                  apply FOPrH_bex_mono;
                  [ match goal with HG : FOctx_avoid _ ?lo ?hi |- _ => apply HG; lia end
                  | first [ apply FOPrH_imp_refl | mono_code' ]
                  | apply FOPrH_imp_weaken; fo_tr2 ]
              | FObetaF _ _ _ _ _ => mono_row
              | FOlookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                  apply FOPrH_lookup_tr'; [assumption | lia
                    | intros ? ? ?; match goal with HG : FOctx_avoid _ ?lo ?hi |- _ =>
                                      apply HG; lia end
                    | assumption | avoid_tms | avoid_tms]
              | _ => fo_tr_leaf
              end ]
  end.

Ltac fo_tr_leaf ::=
  lazymatch goal with
  | |- FOPrH _ _ (FOImplF ?A _) =>
      lazymatch A with
      | FOSTEP0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP0; tr_side
      | FOSTEP1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP1; tr_side
      | FOSTEP2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP2; tr_side
      | FOSTEP3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP3; tr_side
      | FOSTEP4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP4; tr_side
      | FOSTEP5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP5; tr_side
      | FOTHAXc _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_THAXc; tr_side
      | FOLOGc _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_LOGc; tr_side
      | FOJSUBST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_JSUBST; tr_side
      | FOJIND _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_JIND; tr_side
      | FOD2Sc _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_D2Sc; tr_side
      | FOD3Sc _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_D3Sc; tr_side
      | FODMONSc _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_DMONSc; tr_side
      | FOPROVAT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_PROVAT; tr_side
      | FOGENF _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_GENF; tr_side
      end
  end.

(** The table step at row [j] of [T] is the table step at row [j'] of
    [T'] when the two rows agree. *)

Lemma FOtr_DISPATCH : forall n G B T T' j j',
  FOTabMono n G T T' ->
  FOPrH n G (FOROWAG (tct T) (tdt T) (tct T') (tdt T') j j') ->
  FOPrH n G (FOROWAG (tc1 T) (td1 T) (tc1 T') (td1 T') j j') ->
  FOPrH n G (FOROWAG (tc2 T) (td2 T) (tc2 T') (td2 T') j j') ->
  FOPrH n G (FOROWAG (tc3 T) (td3 T) (tc3 T') (td3 T') j j') ->
  FOPrH n G (FOROWAG (tcr T) (tdr T) (tcr T') (tdr T') j j') ->
  B + 102 <= 420 ->
  FOctx_avoid G B (B + 102) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [j; j']) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [j; j']) B (B + 102) ->
  FOPrH n G (FOSTEPDISPATCH B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) j .->
             FOSTEPDISPATCH B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T')
               (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') j').
Proof.
  intros n G B T T' j j' Hm R0 R1 R2 R3 R4 HB HG HG2 Hav1 Hav2.
  pose proof Hm as (HmA & Hct & Hc1 & Hc2 & Hc3 & Hcr).
  unfold FOSTEPDISPATCH. fo_tr2.
Qed.

(** ** Transfer of the builders that read the derivation tracks.

    A premise read below the current position [ipos] transfers when the
    formula tracks agree below some [L >= ipos]. *)

Lemma FOPrH_lt_from_ltv : forall n G v ipos L,
  FOPrH n G (FOltv v ipos) -> FOPrH n G (FOle ipos L) ->
  FOfree_ctx (S v) G -> FOctx_avoid G 420 500 -> v < 400 ->
  FOtm_avoid ipos (S v) (S (S v)) -> FOtm_avoid L (S v) (S (S v)) ->
  FOtm_avoid ipos 420 500 -> FOtm_avoid L 420 500 ->
  FOPrH n G (FOlt470 (FOVar v) L).
Proof.
  intros n G v ipos L H1 H2 HG1 HG2 Hv Hi1 HL1 Hi2 HL2.
  pose proof (FOPrH_mp _ _ _ _
                (FOPrH_ltv_le n G v ipos L H2 HG1 (HG2 498 ltac:(lia) ltac:(lia)) Hv
                   Hi1 HL1 (FOtm_avoid_sub ipos 420 500 498 499 Hi2 ltac:(lia) ltac:(lia))
                   (FOtm_avoid_sub L 420 500 498 499 HL2 ltac:(lia) ltac:(lia))) H1) as H3.
  exact (FOPrH_mp _ _ _ _
           (FOPrH_ltv_470 n G v L ltac:(lia) ltac:(lia)
              (FOtm_avoid_sub L 420 500 470 471 HL2 ltac:(lia) ltac:(lia)) HL1) H3).
Qed.

Lemma FOctx_avoid_ltv : forall G v t lo hi,
  FOctx_avoid G lo hi -> (v < lo \/ hi <= v) -> FOtm_avoid t lo hi ->
  FOctx_avoid (G ++ [FOltv v t]) lo hi.
Proof.
  intros G v t lo hi HG Hv Ht. apply FOctx_avoid_app1; [exact HG|].
  intros w H1 H2. apply FOfree_in_ltv; [lia | apply Ht; lia].
Qed.

(** Contexts extended by bounds: avoidance and freshness. *)

Ltac ctx_avoid_tac :=
  lazymatch goal with
  | |- FOctx_avoid (_ ++ [FOltv _ _]) _ _ =>
      apply FOctx_avoid_ltv; [ctx_avoid_tac | lia | avoid_tm]
  | |- FOctx_avoid _ ?lo ?hi =>
      first [ assumption
            | intros ? ? ?; match goal with HG : FOctx_avoid _ ?lo' ?hi' |- _ =>
                              apply HG; lia end ]
  end.

Ltac ctx_free :=
  lazymatch goal with
  | |- FOfree_ctx _ (_ ++ [FOltv _ _]) =>
      apply FOfree_ctx_app1;
      [ctx_free | apply FOfree_in_ltv; [lia | match goal with
          | H : FOtms_avoid ?L ?lo ?hi |- FOin_tm ?w ?t = false =>
              apply (H t ltac:(simpl; tauto)); lia end]]
  | |- FOfree_ctx ?w _ =>
      match goal with HG : FOctx_avoid _ ?lo ?hi |- _ => apply HG; lia end
  end.

Lemma FOtr_JMP : forall n G B cs ds cs' ds' vd pl ipos L,
  FOPrH n G (FOAGR L cs ds cs' ds') -> FOPrH n G (FOle ipos L) ->
  FOPrH n G (FOle (FOSucc cs) (FOSucc cs')) ->
  B + 24 <= 400 -> FOctx_avoid G B (B + 24) -> FOctx_avoid G 420 500 ->
  FOtms_avoid [cs; ds; cs'; ds'; vd; pl; ipos; L] 420 500 ->
  FOtms_avoid [cs; ds; cs'; ds'; vd; pl; ipos; L] B (B + 24) ->
  FOPrH n G (FOJMP B cs ds vd pl ipos .-> FOJMP B cs' ds' vd pl ipos).
Proof.
  intros n G B cs ds cs' ds' vd pl ipos L HA Hle Hcs HB HG HG2 Hav1 Hav2.
  unfold FOJMP.
  apply FOPrH_bex_mono; [apply HG; lia | apply FOPrH_imp_refl|]. apply FOPrH_intro.
  apply FOPrH_bex_mono; [ctx_free | apply FOPrH_imp_refl|]. apply FOPrH_intro.
  set (G2 := (G ++ [FOltv B ipos]) ++ [FOltv (B + 2) ipos]).
  assert (W : forall X, FOPrH n G X -> FOPrH n G2 X)
    by (intros X HX; exact (FOPrH_weak_app n _ _ _ (FOPrH_weak_app n G _ _ HX))).
  assert (L0 : FOPrH n G2 (FOlt470 (FOVar B) L)).
  { apply (FOPrH_lt_from_ltv n G2 B ipos L);
      [ apply FOPrH_assum; apply in_or_app; left; apply in_or_app; right; left;
        reflexivity
      | apply W; exact Hle | unfold G2; ctx_free | unfold G2; ctx_avoid_tac | lia
      | avoid_tm | avoid_tm | avoid_tm | avoid_tm ]. }
  assert (L2 : FOPrH n G2 (FOlt470 (FOVar (B + 2)) L)).
  { apply (FOPrH_lt_from_ltv n G2 (B + 2) ipos L);
      [ apply FOPrH_last | apply W; exact Hle | unfold G2; ctx_free
      | unfold G2; ctx_avoid_tac | lia | avoid_tm | avoid_tm | avoid_tm | avoid_tm ]. }
  apply FOPrH_and_mono; [apply FOPrH_imp_refl|].
  apply FOPrH_bex_mono; [unfold G2; ctx_free | | apply FOPrH_imp_weaken].
  { apply (FOPrH_code_tr n G2 (B + 4) cs cs' (W _ Hcs)); [lia | unfold G2; ctx_free
      | unfold G2; ctx_avoid_tac | avoid_tm | avoid_tm | avoid_tm | avoid_tm]. }
  apply FOPrH_bex_mono; [unfold G2; ctx_free | | apply FOPrH_imp_weaken].
  { apply (FOPrH_code_tr n G2 (B + 6) cs cs' (W _ Hcs)); [lia | unfold G2; ctx_free
      | unfold G2; ctx_avoid_tac | avoid_tm | avoid_tm | avoid_tm | avoid_tm]. }
  apply FOPrH_and_mono; [|apply FOPrH_and_mono; [|apply FOPrH_imp_refl]].
  - apply (FOPrH_agr_beta n G2 L cs ds cs' ds' (FOVar B) (FOVar (B + 4)) (B + 8)
             (W _ HA) L0 ltac:(lia)); unfold G2;
      first [ ctx_avoid_tac | avoid_tm ].
  - apply (FOPrH_agr_beta n G2 L cs ds cs' ds' (FOVar (B + 2)) (FOVar (B + 6)) (B + 12)
             (W _ HA) L2 ltac:(lia)); unfold G2;
      first [ ctx_avoid_tac | avoid_tm ].
Qed.

Lemma FOTabMono_weak : forall n G L T T', FOTabMono n G T T' -> FOTabMono n (G ++ L) T T'.
Proof.
  intros n G L T T' (HA & H1 & H2 & H3 & H4 & H5).
  split; [apply FOTabAgree_weak; exact HA|].
  repeat split; apply FOPrH_weak_app; assumption.
Qed.

Lemma FOtr_JGEN : forall n G B cs ds cs' ds' vd pl ipos L,
  FOPrH n G (FOAGR L cs ds cs' ds') -> FOPrH n G (FOle ipos L) ->
  FOPrH n G (FOle (FOSucc cs) (FOSucc cs')) ->
  B + 18 <= 400 -> FOctx_avoid G B (B + 18) -> FOctx_avoid G 420 500 ->
  FOtms_avoid [cs; ds; cs'; ds'; vd; pl; ipos; L] 420 500 ->
  FOtms_avoid [cs; ds; cs'; ds'; vd; pl; ipos; L] B (B + 18) ->
  FOPrH n G (FOJGEN B cs ds vd pl ipos .-> FOJGEN B cs' ds' vd pl ipos).
Proof.
  intros n G B cs ds cs' ds' vd pl ipos L HA Hle Hcs HB HG HG2 Hav1 Hav2.
  unfold FOJGEN.
  apply FOPrH_bex_mono; [apply HG; lia | apply FOPrH_imp_refl|]. apply FOPrH_intro.
  set (G1 := G ++ [FOltv B ipos]).
  assert (W : forall X, FOPrH n G X -> FOPrH n G1 X)
    by (intros X HX; exact (FOPrH_weak_app n G _ _ HX)).
  assert (L0 : FOPrH n G1 (FOlt470 (FOVar B) L)).
  { apply (FOPrH_lt_from_ltv n G1 B ipos L);
      [ apply FOPrH_last | apply W; exact Hle | unfold G1; ctx_free
      | unfold G1; ctx_avoid_tac | lia | avoid_tm | avoid_tm | avoid_tm | avoid_tm ]. }
  apply FOPrH_and_mono; [apply FOPrH_imp_refl|].
  apply FOPrH_bex_mono; [unfold G1; ctx_free | | apply FOPrH_imp_weaken].
  { apply (FOPrH_code_tr n G1 (B + 2) cs cs' (W _ Hcs)); [lia | unfold G1; ctx_free
      | unfold G1; ctx_avoid_tac | avoid_tm | avoid_tm | avoid_tm | avoid_tm]. }
  apply FOPrH_and_mono; [|apply FOPrH_imp_refl].
  apply (FOPrH_agr_beta n G1 L cs ds cs' ds' (FOVar B) (FOVar (B + 2)) (B + 4)
           (W _ HA) L0 ltac:(lia)); unfold G1; first [ ctx_avoid_tac | avoid_tm ].
Qed.

Lemma FOtr_JLOEB : forall n G B T T' cs ds cs' ds' vd pl ipos L,
  FOTabMono n G T T' ->
  FOPrH n G (FOAGR L cs ds cs' ds') -> FOPrH n G (FOle ipos L) ->
  FOPrH n G (FOle (FOSucc cs) (FOSucc cs')) ->
  B + 112 <= 400 -> FOctx_avoid G B (B + 112) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [cs; ds; cs'; ds'; vd; pl; ipos; L])
    420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [cs; ds; cs'; ds'; vd; pl; ipos; L])
    B (B + 112) ->
  FOPrH n G (FOJLOEB B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T) (td3 T)
               (tcr T) (tdr T) (tlen T) cs ds vd pl ipos .->
             FOJLOEB B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' vd pl ipos).
Proof.
  intros n G B T T' cs ds cs' ds' vd pl ipos L Hm HA Hle Hcs HB HG HG2 Hav1 Hav2.
  unfold FOJLOEB.
  apply FOPrH_bex_mono; [apply HG; lia | apply FOPrH_imp_refl|]. apply FOPrH_intro.
  set (G1 := G ++ [FOltv B ipos]).
  assert (W : forall X, FOPrH n G X -> FOPrH n G1 X)
    by (intros X HX; exact (FOPrH_weak_app n G _ _ HX)).
  assert (L0 : FOPrH n G1 (FOlt470 (FOVar B) L)).
  { apply (FOPrH_lt_from_ltv n G1 B ipos L);
      [ apply FOPrH_last | apply W; exact Hle | unfold G1; ctx_free
      | unfold G1; ctx_avoid_tac | lia | avoid_tm | avoid_tm | avoid_tm | avoid_tm ]. }
  assert (HG1 : FOctx_avoid G1 (B + 2) (B + 112)) by (unfold G1; ctx_avoid_tac).
  assert (HG1' : FOctx_avoid G1 420 500) by (unfold G1; ctx_avoid_tac).
  pose proof (FOTabMono_weak n G [FOltv B ipos] T T' Hm) as Hm1. fold G1 in Hm1.
  pose proof Hm1 as (HmA & Hct & Hc1 & Hc2 & Hc3 & Hcr).
  pose proof (W _ Hcs) as Hcs1.
  clear HG HG2 Hm W Hcs.
  apply FOPrH_and_mono; [apply FOPrH_imp_refl|].
  apply FOPrH_bex_mono; [apply HG1; lia | mono_code' | apply FOPrH_imp_weaken].
  apply FOPrH_and_mono.
  - apply (FOPrH_agr_beta n G1 L cs ds cs' ds' (FOVar B) (FOVar (B + 2)) (B + 4)
             (FOPrH_weak_app n G _ _ HA) L0 ltac:(lia));
      first [ intros ? ? ?; match goal with H : FOctx_avoid G1 ?lo ?hi |- _ =>
                              apply H; lia end
            | avoid_tm ].
  - fo_tr2.
Qed.

Lemma FOtr_GUARDC : forall n G B T T' cs ds cs' ds' i i',
  FOTabMono n G T T' ->
  FOPrH n G (FOROWAG cs ds cs' ds' i i') ->
  FOPrH n G (FOle (FOSucc cs) (FOSucc cs')) ->
  B + 30 <= 400 -> FOctx_avoid G B (B + 30) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [cs; ds; cs'; ds'; i; i']) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [cs; ds; cs'; ds'; i; i']) B (B + 30) ->
  FOPrH n G (FOGUARDC B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T) (td3 T)
               (tcr T) (tdr T) (tlen T) cs ds i .->
             FOGUARDC B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' i').
Proof.
  intros n G B T T' cs ds cs' ds' i i' Hm HR Hcs HB HG HG2 Hav1 Hav2.
  pose proof Hm as (HmA & Hct & Hc1 & Hc2 & Hc3 & Hcr).
  unfold FOGUARDC. fo_tr2.
Qed.

Ltac tr_side' := first [ eassumption | tr_side ].

Ltac fo_tr_leaf ::=
  lazymatch goal with
  | |- FOPrH _ _ (FOImplF ?A _) =>
      lazymatch A with
      | FOSTEP0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP0; tr_side
      | FOSTEP1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP1; tr_side
      | FOSTEP2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP2; tr_side
      | FOSTEP3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP3; tr_side
      | FOSTEP4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP4; tr_side
      | FOSTEP5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_STEP5; tr_side
      | FOTHAXc _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_THAXc; tr_side
      | FOLOGc _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_LOGc; tr_side
      | FOJSUBST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
          apply FOtr_JSUBST;
          cbn [cpat_span cpat_pairs cpatAllElim cpatExIntro pImpP pAllP pExP];
          tr_side
      | FOJIND _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_JIND; tr_side
      | FOD2Sc _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_D2Sc; tr_side
      | FOD3Sc _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_D3Sc; tr_side
      | FODMONSc _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_DMONSc; tr_side
      | FOPROVAT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_PROVAT; tr_side
      | FOGENF _ _ _ _ _ _ _ _ _ _ _ _ _ => apply FOtr_GENF; tr_side
      | FOJMP _ _ _ _ _ _ => eapply FOtr_JMP; tr_side'
      | FOJGEN _ _ _ _ _ _ => eapply FOtr_JGEN; tr_side'
      | FOJLOEB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eapply FOtr_JLOEB; tr_side'
      end
  end.

(** The justification check at a position of the first derivation. *)

Lemma FOtr_JUSTCK : forall n G B cores T T' cs ds cj dj cs' ds' cj' dj' i L,
  FOTabMono n G T T' ->
  FOPrH n G (FOROWAG cs ds cs' ds' i i) -> FOPrH n G (FOROWAG cj dj cj' dj' i i) ->
  FOPrH n G (FOle (FOSucc cs) (FOSucc cs')) -> FOPrH n G (FOle (FOSucc cj) (FOSucc cj')) ->
  FOPrH n G (FOAGR L cs ds cs' ds') -> FOPrH n G (FOle i L) ->
  B + 232 <= 400 -> FOctx_avoid G B (B + 232) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++
                 [cs; ds; cj; dj; cs'; ds'; cj'; dj'; i; L]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++
                 [cs; ds; cj; dj; cs'; ds'; cj'; dj'; i; L]) B (B + 232) ->
  FOPrH n G (FOJUSTCK B cores (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) cs ds cj dj i .->
             FOJUSTCK B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T')
               (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' cj' dj' i).
Proof.
  intros n G B cores T T' cs ds cj dj cs' ds' cj' dj' i L Hm R1 R2 Hcs Hcj HA Hle
    HB HG HG2 Hav1 Hav2.
  pose proof Hm as (HmA & Hct & Hc1 & Hc2 & Hc3 & Hcr).
  unfold FOJUSTCK. fo_tr2.
Qed.

(** ** Sequent rules on derivable implications.

    A premise of an implication is decomposed in place: an existential
    premise gives an eigenvariable of the same name, a conjunction two
    premises, a disjunction two cases.  An existential conclusion is
    introduced at its own variable, or at a term by substitution. *)

Lemma FOPrH_imp_exl : forall n G x A C,
  FOfree_ctx x G -> FOfree_in x C = false ->
  FOPrH n G (A .-> C) -> FOPrH n G (FOExists x A .-> C).
Proof.
  intros n G x A C Hx HC H. apply FOPrH_intro.
  apply (FOPrH_ex_elim n (G ++ [FOExists x A]) x A);
    [apply FOfree_ctx_app1; [exact Hx | apply FOfree_in_ex_self] | exact HC
    | apply FOPrH_last |].
  apply (FOPrH_mp _ _ A C); [|apply FOPrH_last].
  do 2 apply FOPrH_weak_app. exact H.
Qed.

Lemma FOPrH_imp_andl : forall n G A B C,
  FOPrH n G (A .-> B .-> C) -> FOPrH n G (FOAnd A B .-> C).
Proof.
  intros n G A B C H. apply FOPrH_intro.
  pose proof (FOPrH_last n G (FOAnd A B)) as HAB.
  exact (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ (FOPrH_weak_app n G _ _ H)
           (FOPrH_and_l _ _ _ _ HAB)) (FOPrH_and_r _ _ _ _ HAB)).
Qed.

Lemma FOPrH_imp_orl : forall n G A B C,
  FOPrH n G (A .-> C) -> FOPrH n G (B .-> C) -> FOPrH n G (FOOr A B .-> C).
Proof.
  intros n G A B C HA HB. apply FOPrH_intro.
  apply (FOPrH_or_elim n (G ++ [FOOr A B]) A B C (FOPrH_last n G _)).
  - apply (FOPrH_mp _ _ A C); [|apply FOPrH_last]. do 2 apply FOPrH_weak_app. exact HA.
  - apply (FOPrH_mp _ _ B C); [|apply FOPrH_last]. do 2 apply FOPrH_weak_app. exact HB.
Qed.

Lemma FOPrH_imp_bexl : forall n G x t A C,
  FOfree_ctx x G -> FOfree_in x C = false ->
  FOPrH n (G ++ [FOltv x t]) (A .-> C) -> FOPrH n G (FOBexC x t A .-> C).
Proof.
  intros n G x t A C Hx HC H. rewrite FOBexC_ltv.
  apply FOPrH_imp_exl; [exact Hx | exact HC |].
  apply FOPrH_imp_andl. apply FOPrH_intro. exact H.
Qed.

Lemma FOPrH_ex_same : forall n G x A, FOPrH n G A -> FOPrH n G (FOExists x A).
Proof.
  intros n G x A H. apply (FOPrH_ex_intro _ _ x (FOVar x)); [apply FOsubst_ok_var_self|].
  rewrite FOsubst_f_id. exact H.
Qed.

Lemma FOPrH_bex_same : forall n G x t A,
  FOPrH n G (FOltv x t) -> FOPrH n G A -> FOPrH n G (FOBexC x t A).
Proof.
  intros n G x t A H1 H2. rewrite FOBexC_ltv. apply FOPrH_ex_same.
  apply FOPrH_and_intro; assumption.
Qed.

(** Sums and products in the avoidance tactics. *)

Lemma FOtm_avoid_plus : forall a b lo hi,
  FOtm_avoid a lo hi -> FOtm_avoid b lo hi -> FOtm_avoid (FOPlus a b) lo hi.
Proof.
  intros a b lo hi Ha Hb w H1 H2. cbn [FOin_tm]. rewrite (Ha w H1 H2), (Hb w H1 H2).
  reflexivity.
Qed.

Lemma FOtm_avoid_mult : forall a b lo hi,
  FOtm_avoid a lo hi -> FOtm_avoid b lo hi -> FOtm_avoid (FOMult a b) lo hi.
Proof.
  intros a b lo hi Ha Hb w H1 H2. cbn [FOin_tm]. rewrite (Ha w H1 H2), (Hb w H1 H2).
  reflexivity.
Qed.

Ltac avoid_tm ::=
  lazymatch goal with
  | |- FOtm_avoid (FOnumeral _) _ _ => apply FOtm_avoid_numeral
  | |- FOtm_avoid FOZero _ _ => apply FOtm_avoid_zero
  | |- FOtm_avoid (FOSucc _) _ _ => apply FOtm_avoid_succ; avoid_tm
  | |- FOtm_avoid (FOPlus _ _) _ _ => apply FOtm_avoid_plus; avoid_tm
  | |- FOtm_avoid (FOMult _ _) _ _ => apply FOtm_avoid_mult; avoid_tm
  | |- FOtm_avoid (FOVar _) _ _ => apply FOtm_avoid_var; lia
  | |- FOtm_avoid ?t ?lo ?hi =>
      match goal with
      | H : FOtms_avoid ?L ?lo' ?hi' |- _ =>
          apply (FOtm_avoid_sub t lo' hi' lo hi); [apply H; in_list | lia | lia]
      end
  end.

(** ** Strict bounds as [FOle (S s) t]. *)

Lemma FOPrH_ltv_of_le : forall n G x t,
  FOfree_ctx 498 G -> x <> 498 -> S x <> 498 ->
  FOtm_avoid t 498 499 -> FOtm_avoid t (S x) (S (S x)) ->
  FOPrH n G (FOle (FOSucc (FOVar x)) t) -> FOPrH n G (FOltv x t).
Proof.
  intros n G x t HG H1 H2 Ht1 Ht2 H.
  assert (F : FOfree_in 498 (FOltv x t) = false).
  { unfold FOltv. cbn [FOfree_in FOin_tm]. nat_eqb_simpl.
    rewrite (Ht1 498 ltac:(lia) ltac:(lia)). reflexivity. }
  unfold FOle in H.
  apply (FOPrH_ex_elim n G 498 _ _ HG F H).
  unfold FOltv. apply (FOPrH_ex_intro _ _ (S x) (FOVar 498)); [reflexivity|].
  cbn [FOsubst_f FOsubst_t]. nat_eqb_simpl.
  rewrite (FOsubst_t_not_in t (S x) (FOVar 498) (Ht2 (S x) ltac:(lia) ltac:(lia))).
  fo_lin [(.S .0, t, .S (#x) .+ #498)].
Qed.

Lemma FOPrH_le_of_ltv : forall n G x t,
  FOfree_ctx (S x) G -> x <> 498 -> S x <> 498 ->
  FOtm_avoid t 498 499 -> FOtm_avoid t (S x) (S (S x)) ->
  FOPrH n G (FOltv x t) -> FOPrH n G (FOle (FOSucc (FOVar x)) t).
Proof.
  intros n G x t HG H1 H2 Ht1 Ht2 H.
  assert (F : FOfree_in (S x) (FOle (FOSucc (FOVar x)) t) = false).
  { unfold FOle. cbn [FOfree_in FOin_tm]. nat_eqb_simpl.
    rewrite (Ht2 (S x) ltac:(lia) ltac:(lia)). reflexivity. }
  unfold FOltv in H.
  apply (FOPrH_ex_elim n G (S x) _ _ HG F H).
  unfold FOle. apply (FOPrH_ex_intro _ _ 498 (FOVar (S x))); [reflexivity|].
  cbn [FOsubst_f FOsubst_t]. nat_eqb_simpl.
  rewrite (FOsubst_t_not_in t 498 (FOVar (S x)) (Ht1 498 ltac:(lia) ltac:(lia))).
  fo_lin [(.S .0, t, #x .+ .S (#(S x)))].
Qed.

Lemma FOPrH_le_succ : forall n G a b,
  FOfree_ctx 498 G -> FOtm_avoid a 498 499 -> FOtm_avoid b 498 499 ->
  FOPrH n G (FOle a b) -> FOPrH n G (FOle (FOSucc a) (FOSucc b)).
Proof.
  intros n G a b HG Ha Hb H.
  assert (F : FOfree_in 498 (FOle (FOSucc a) (FOSucc b)) = false).
  { unfold FOle. apply FOfree_in_ex_self. }
  unfold FOle in H |- *.
  apply (FOPrH_ex_elim n G 498 _ _ HG F H).
  apply FOPrH_ex_same. fo_lin [(.S .0, b, a .+ #498)].
Qed.

(** A beta value is at most the modulus code. *)

Lemma FOPrH_beta_le : forall n G v c d i x,
  FOctx_avoid G v (v + 4) -> v + 4 <= 498 ->
  FOtms_avoid [c; d; i; x] v (v + 4) -> FOtms_avoid [c; d; i; x] 498 499 ->
  FOPrH n G (FObetaF v c d i x .-> FOle x c).
Proof.
  intros n G v c d i x HG Hv Hav1 Hav2.
  rewrite FObetaF_body. apply FOPrH_imp_bexl.
  - apply HG; lia.
  - unfold FOle. cbn [FOfree_in FOin_tm]. nat_eqb_simpl.
    rewrite (Hav1 x ltac:(in_list) v ltac:(lia) ltac:(lia)),
            (Hav1 c ltac:(in_list) v ltac:(lia) ltac:(lia)).
    reflexivity.
  - apply FOPrH_intro.
    pose proof (FOPrH_last n (G ++ [FOltv v (FOSucc c)]) (FObetaBody v c d i x)) as E.
    unfold FObetaBody in E. apply FOPrH_and_l in E.
    unfold FOle.
    apply (FOPrH_ex_intro _ _ 498 (FOMult (FOVar v) (FOSucc (FOMult d (FOSucc i)))));
      [reflexivity|].
    cbn [FOsubst_f]. rewrite FOsubst_t_plus, FOsubst_t_var_eq'.
    rewrite (FOsubst_t_not_in x 498 _ (Hav2 x ltac:(in_list) 498 ltac:(lia) ltac:(lia))),
            (FOsubst_t_not_in c 498 _ (Hav2 c ltac:(in_list) 498 ltac:(lia) ltac:(lia))).
    fo_lin [(.S .0, c, FOPlus (FOMult (FOVar v) (FOSucc (FOMult d (FOSucc i)))) x)].
    exact E.
Qed.

(** Distinct numerals are refuted. *)

Lemma FOPrH_numeral_neq : forall k m n G,
  k <> m -> FOPrH n G (FOEq (FOnumeral k) (FOnumeral m)) -> FOPrH n G FOFalseF.
Proof.
  induction k as [|k IH]; intros m n G Hkm H; destruct m as [|m].
  - lia.
  - apply (FOPrH_Q_succ_nonzero n G (FOnumeral m)). apply FOPrH_eq_sym. exact H.
  - exact (FOPrH_Q_succ_nonzero n G (FOnumeral k) H).
  - apply (IH m n G ltac:(lia)). apply FOPrH_Q_succ_inj. exact H.
Qed.

Lemma FOPrH_tag_absurd : forall n G t k m,
  k <> m -> FOPrH n G (FOEq t (FOnumeral k)) -> FOPrH n G (FOEq t (FOnumeral m)) ->
  FOPrH n G FOFalseF.
Proof.
  intros n G t k m Hkm H1 H2.
  apply (FOPrH_numeral_neq k m n G Hkm).
  exact (FOPrH_eq_trans _ _ _ _ _ (FOPrH_eq_sym _ _ _ _ H1) H2).
Qed.

(** Pairing: congruence and the two component bounds at terms. *)

Lemma FOPrH_cpairF_cong : forall n G a b c a' b' c',
  FOPrH n G (a .= a') -> FOPrH n G (b .= b') -> FOPrH n G (c .= c') ->
  FOPrH n G (FOcpairF a b c) -> FOPrH n G (FOcpairF a' b' c').
Proof.
  intros n G a b c a' b' c' Ha Hb Hc H. unfold FOcpairF in *.
  assert (Hab : FOPrH n G (a .+ b .= a' .+ b')) by (apply FOPrH_congPlus; assumption).
  eapply FOPrH_eq_trans; [apply FOPrH_eq_sym; apply FOPrH_congPlus; exact Hc|].
  eapply FOPrH_eq_trans; [exact H|].
  apply FOPrH_congPlus; [apply FOPrH_congMult; [exact Hab | apply FOPrH_congS; exact Hab]|].
  apply FOPrH_congPlus; exact Hb.
Qed.

Ltac ok_fast_leaf V ::=
  lazymatch goal with
  | |- FOsubst_ok _ _ (FOROWAG _ _ _ _ _ _) = true =>
      apply FOsubst_ok_ROWAG; refine (FOtm_avoid_sub _ _ _ _ _ V _ _); lia
  | |- FOsubst_ok _ _ (FOcpairF _ _ _) = true => apply FOsubst_ok_cpairF
  end.

(** Instantiation of a universal at a term avoiding the library
    binders, with the substitution carried out. *)

Ltac fo_inst_s H t V :=
  lazymatch type of H with
  | FOPrH ?k ?G (FOForall ?x ?A) =>
      let H1 := fresh "HI" in
      pose proof (FOPrH_inst k G x t A H ltac:(ok_fast V)) as H1;
      autorewrite with fosub0 in H1; subst_avoid; clear H; rename H1 into H
  end.

Lemma FOPrH_ex450_le : forall n G t c,
  FOctx_avoid G 420 500 -> FOtm_avoid t 420 500 -> FOtm_avoid c 420 500 ->
  FOPrH n G (FOExists 450 (FOEq (FOPlus t (FOVar 450)) c)) -> FOPrH n G (FOle t c).
Proof.
  intros n G t c HG Vt Vc E.
  refine (FOPrH_ex_elim n G 450 (FOEq (FOPlus t (FOVar 450)) c) _
            (HG 450 ltac:(lia) ltac:(lia)) _ E _).
  - unfold FOle. cbn [FOfree_in FOin_tm]. nat_eqb_simpl.
    rewrite (Vt 450), (Vc 450) by lia. reflexivity.
  - unfold FOle. apply (FOPrH_ex_intro _ _ 498 (FOVar 450)); [reflexivity|].
    cbn [FOsubst_f]. rewrite FOsubst_t_plus, FOsubst_t_var_eq'.
    rewrite (FOsubst_t_not_in t 498 _ (Vt 498 ltac:(lia) ltac:(lia))),
            (FOsubst_t_not_in c 498 _ (Vc 498 ltac:(lia) ltac:(lia))).
    apply FOPrH_last.
Qed.

Lemma FOPrH_cpair_le : forall n G a b c,
  FOtms_avoid [a; b; c] 420 500 -> FOctx_avoid G 420 500 ->
  FOPrH n G (FOcpairF a b c) -> FOPrH n G (FOle a c) /\ FOPrH n G (FOle b c).
Proof.
  intros n G a b c Hav HG H.
  assert (Va : FOtm_avoid a 420 500) by avoid_tm.
  assert (Vb : FOtm_avoid b 420 500) by avoid_tm.
  assert (Vc : FOtm_avoid c 420 500) by avoid_tm.
  split; apply FOPrH_ex450_le; try assumption.
  - pose proof (FOPrH_thm n G _ (FOPr_cpair_le_l n)) as T0.
    fo_inst_s T0 a Va. fo_inst_s T0 b Vb. fo_inst_s T0 c Vc.
    exact (FOPrH_mp _ _ _ _ T0 H).
  - pose proof (FOPrH_thm n G _ (FOPr_cpair_le_r n)) as T0.
    fo_inst_s T0 a Va. fo_inst_s T0 b Vb. fo_inst_s T0 c Vc.
    exact (FOPrH_mp _ _ _ _ T0 H).
Qed.

(** ** The justification check split at its payload.

    [FOJDISJ] is the disjunction over the eleven justification kinds
    with the entry code [vd], the tag [tg] and the payload [pl] as
    terms; [FOCHK] binds the tag and the payload below the
    justification code [jc]. *)

Definition FOJDISJ (B : nat) (cores : list nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (cs ds i vd tg pl : FOTerm) : FOFormula :=
  FOOr (FOAnd (FOEq tg FOZero)
          (FOTHAXc (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len cores vd))
  (FOOr (FOAnd (FOEq tg (FOnumeral 1))
          (FOLOGc (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len vd))
  (FOOr (FOAnd (FOEq tg (FOnumeral 2))
          (FOJSUBST (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len cpatAllElim vd pl))
  (FOOr (FOAnd (FOEq tg (FOnumeral 3))
          (FOJSUBST (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len cpatExIntro vd pl))
  (FOOr (FOAnd (FOEq tg (FOnumeral 4)) (FOJMP (B+16) cs ds vd pl i))
  (FOOr (FOAnd (FOEq tg (FOnumeral 5)) (FOJGEN (B+16) cs ds vd pl i))
  (FOOr (FOAnd (FOEq tg (FOnumeral 6))
          (FOJLOEB (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd pl i))
  (FOOr (FOAnd (FOEq tg (FOnumeral 7))
          (FOD2Sc (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len cores vd))
  (FOOr (FOAnd (FOEq tg (FOnumeral 8))
          (FOD3Sc (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len cores vd))
  (FOOr (FOAnd (FOEq tg (FOnumeral 9))
          (FODMONSc (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len cores vd))
        (FOAnd (FOEq tg (FOnumeral 10))
          (FOJIND (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len vd pl))))))))))).

Definition FOCHK (B : nat) (cores : list nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (cs ds i vd jc : FOTerm) : FOFormula :=
  FOBexC (B+12) (FOSucc jc) (FOBexC (B+14) (FOSucc jc)
    (FOAnd (FOcpairF (FOVar (B+12)) (FOVar (B+14)) jc)
       (FOJDISJ B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd
          (FOVar (B+12)) (FOVar (B+14))))).

Lemma FOJUSTCK_split : forall B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds cj dj i,
  FOJUSTCK B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds cj dj i =
  FOBexC B (FOSucc cs) (FOBexC (B+2) (FOSucc cj)
    (FOAnd (FObetaF (B+4) cs ds i (FOVar B))
    (FOAnd (FObetaF (B+8) cj dj i (FOVar (B+2)))
       (FOCHK B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i (FOVar B) (FOVar (B+2)))))).
Proof. reflexivity. Qed.

Lemma FOsubst_f_JDISJ : forall x s B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds i vd tg pl,
  0 < x -> x < B + 16 ->
  FOsubst_f x s (FOJDISJ B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd tg pl) =
  FOJDISJ B cores (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s cs) (FOsubst_t x s ds) (FOsubst_t x s i) (FOsubst_t x s vd)
    (FOsubst_t x s tg) (FOsubst_t x s pl).
Proof. intros. unfold FOJDISJ. autorewrite with fosubst. reflexivity. Qed.

Lemma FOsubst_f_CHK : forall x s B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds i vd jc,
  0 < x -> x < B + 12 ->
  FOsubst_f x s (FOCHK B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd jc) =
  FOCHK B cores (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s cs) (FOsubst_t x s ds) (FOsubst_t x s i) (FOsubst_t x s vd)
    (FOsubst_t x s jc).
Proof.
  intros. unfold FOCHK. rewrite !FOsubst_f_bex by lia.
  rewrite FOsubst_f_and, FOsubst_f_cpairF, FOsubst_f_JDISJ by lia.
  rewrite !FOsubst_t_var_ne by lia. reflexivity.
Qed.

Lemma FOsubst_ok_JDISJ : forall x s B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds i vd tg pl,
  FOtm_avoid s (B + 16) (B + 232) ->
  FOsubst_ok x s (FOJDISJ B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd tg pl) = true.
Proof.
  intros. unfold FOJDISJ. auto 100 with fook.
Qed.

Lemma FOsubst_ok_CHK : forall x s B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds i vd jc,
  FOtm_avoid s (B + 12) (B + 232) ->
  FOsubst_ok x s (FOCHK B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd jc) = true.
Proof.
  intros x s B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd jc V.
  unfold FOCHK.
  apply FOsubst_ok_bex; [apply V; lia | apply V; lia|].
  apply FOsubst_ok_bex; [apply V; lia | apply V; lia|].
  apply FOsubst_ok_and; [apply FOsubst_ok_cpairF|].
  apply FOsubst_ok_JDISJ. refine (FOtm_avoid_sub _ _ _ _ _ V _ _); lia.
Qed.

Lemma FOJDISJ_free : forall cores w B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds i vd tg pl,
  FOfree_in w (FOJDISJ B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd tg pl)
  = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true \/ FOin_tm w cs = true
  \/ FOin_tm w ds = true \/ FOin_tm w i = true \/ FOin_tm w vd = true
  \/ FOin_tm w tg = true \/ FOin_tm w pl = true \/ w < 2.
Proof.
  intros cores w B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd tg pl H.
  unfold FOJDISJ in H.
  repeat first [arm_recog | arm_dsc | arm_lookup | arm_betaF | arm_patf | ffree_leaf]; ffin.
Qed.

(** ** Arithmetic side conditions.

    Comparisons of numerals are decided by evaluation, comparisons of
    offsets from a symbolic base by [lia].  The substitution rewrites
    and the capture checks below use this solver. *)

Ltac nat_fast :=
  first [ solve [apply Nat.eqb_neq; vm_compute; reflexivity]
        | solve [apply Nat.ltb_lt; vm_compute; reflexivity]
        | solve [apply Nat.leb_le; vm_compute; reflexivity]
        | lia ].

Ltac ok_fast V ::=
  lazymatch goal with
  | |- FOsubst_ok _ _ (FOAnd _ _) = true => apply FOsubst_ok_and; ok_fast V
  | |- FOsubst_ok _ _ (FOOr _ _) = true => apply FOsubst_ok_or; ok_fast V
  | |- FOsubst_ok _ _ (FONeg _) = true => apply FOsubst_ok_neg; ok_fast V
  | |- FOsubst_ok _ _ (FOImplF _ _) = true => apply FOsubst_ok_impl; ok_fast V
  | |- FOsubst_ok _ _ FOFalseF = true => apply FOsubst_ok_false
  | |- FOsubst_ok _ _ (FOEq _ _) = true => apply FOsubst_ok_eq
  | |- FOsubst_ok _ _ (FOExists _ _) = true =>
      apply FOsubst_ok_ex; [apply V; nat_fast | ok_fast V]
  | |- FOsubst_ok _ _ (FOForall _ _) = true =>
      apply FOsubst_ok_all; [apply V; nat_fast | ok_fast V]
  | |- FOsubst_ok _ _ (FObetaF _ _ _ _ _) = true =>
      apply FOsubst_ok_betaF; refine (FOtm_avoid_sub _ _ _ _ _ V _ _); nat_fast
  | |- FOsubst_ok _ _ (FOltv _ _) = true => unfold FOltv; ok_fast V
  | |- _ => ok_fast_leaf V
  end.

Create HintDb fosubf.
Hint Rewrite FOsubst_t_zero FOsubst_t_succ FOsubst_t_plus FOsubst_t_mult
  FOsubst_t_numeral FOsubst_f_eq FOsubst_f_false FOsubst_f_impl FOsubst_f_neg
  FOsubst_f_and FOsubst_f_or FOsubst_f_cpairF FOsubst_t_var_eq'
  FOsubst_map_cons FOsubst_map_nil : fosubf.
Hint Rewrite FOsubst_t_var_ne FOsubst_f_ex_ne FOsubst_f_all_ne FOsubst_f_bex
  FOsubst_f_ball FOsubst_f_betaF FOsubst_f_ROWAG FOsubst_f_PATF
  using nat_fast : fosubf.

Ltac subst_avoid_h Hav :=
  repeat match goal with
  | |- context [FOsubst_t ?w ?s ?t] =>
      is_var t;
      rewrite (FOsubst_t_not_in t w s (Hav t ltac:(in_list) w ltac:(nat_fast) ltac:(nat_fast)))
  end.

Ltac subst_avoid_hin Hav H :=
  repeat match type of H with
  | context [FOsubst_t ?w ?s ?t] =>
      is_var t;
      rewrite (FOsubst_t_not_in t w s (Hav t ltac:(in_list) w ltac:(nat_fast) ltac:(nat_fast)))
        in H
  end.

(** Instantiation of a universal at a term [t] with [t] avoiding the
    library binders ([V]) and the remaining terms avoiding the
    instantiated variable ([Hav]). *)

Ltac fo_inst_f H t V Hav :=
  lazymatch type of H with
  | FOPrH ?k ?G (FOForall ?x ?A) =>
      let H1 := fresh "HI" in
      pose proof (FOPrH_inst k G x t A H ltac:(ok_fast V)) as H1;
      autorewrite with fosubf in H1; subst_avoid_hin Hav H1; clear H; rename H1 into H
  end.

(** ** Freshness of small formulas, decided at their heads. *)

Lemma FOin_tm_succ_eq : forall w a, FOin_tm w (FOSucc a) = FOin_tm w a.
Proof. reflexivity. Qed.

Lemma FOin_tm_plus_eq : forall w a b,
  FOin_tm w (FOPlus a b) = (FOin_tm w a || FOin_tm w b)%bool.
Proof. reflexivity. Qed.

Lemma FOin_tm_mult_eq : forall w a b,
  FOin_tm w (FOMult a b) = (FOin_tm w a || FOin_tm w b)%bool.
Proof. reflexivity. Qed.

Ltac fr_tm :=
  lazymatch goal with
  | |- FOin_tm _ (FOVar _) = false => apply FOin_tm_var_ne; lia
  | |- FOin_tm _ (FOnumeral _) = false => apply FOin_tm_numeral
  | |- FOin_tm _ FOZero = false => reflexivity
  | |- FOin_tm _ (FOSucc _) = false => rewrite FOin_tm_succ_eq; fr_tm
  | |- FOin_tm _ (FOPlus _ _) = false =>
      rewrite FOin_tm_plus_eq; apply Bool.orb_false_iff; split; fr_tm
  | |- FOin_tm _ (FOMult _ _) = false =>
      rewrite FOin_tm_mult_eq; apply Bool.orb_false_iff; split; fr_tm
  | |- FOin_tm ?w ?t = false =>
      match goal with H : FOtms_avoid ?L ?lo ?hi |- _ => apply (H t ltac:(in_list) w); lia end
  end.

Ltac free_fm :=
  lazymatch goal with
  | |- FOfree_in _ (FOltv _ _) = false => apply FOfree_in_ltv; [lia | fr_tm]
  | |- FOfree_in _ (FObetaF _ _ _ _ _) = false =>
      apply FOfree_in_betaF_not; [lia | fr_tm | fr_tm | fr_tm | fr_tm]
  | |- FOfree_in _ (FOcpairF _ _ _) = false =>
      rewrite FOfree_in_FOcpairF; apply Bool.orb_false_iff; split;
      [apply Bool.orb_false_iff; split|]; fr_tm
  | |- FOfree_in _ (FOEq _ _) = false =>
      cbn [FOfree_in]; apply Bool.orb_false_iff; split; fr_tm
  | |- FOfree_in _ (FONeg _) = false => rewrite FOfree_in_FONeg; free_fm
  | |- FOfree_in _ (FOAnd _ _) = false =>
      rewrite FOfree_in_FOAnd; apply Bool.orb_false_iff; split; free_fm
  | |- FOfree_in _ (FOOr _ _) = false =>
      rewrite FOfree_in_FOOr; apply Bool.orb_false_iff; split; free_fm
  | |- FOfree_in _ (FOImplF _ _) = false =>
      rewrite FOfree_in_impl; apply Bool.orb_false_iff; split; free_fm
  | |- FOfree_in ?w (FOExists ?y _) = false =>
      first [ constr_eq w y; apply FOfree_in_ex_self
            | rewrite FOfree_in_FOExists_neq by lia; free_fm ]
  | |- FOfree_in ?w (FOForall ?y _) = false =>
      first [ constr_eq w y; apply FOfree_in_all_self
            | rewrite FOfree_in_all_ne by lia; free_fm ]
  | |- FOfree_in _ FOFalseF = false => reflexivity
  end.

Lemma FOfree_ctx_cons : forall v A L,
  FOfree_in v A = false -> FOfree_ctx v L -> FOfree_ctx v (A :: L).
Proof. intros v A L HA HL H [<-|Hin]; [exact HA | exact (HL H Hin)]. Qed.

Lemma FOfree_ctx_nil : forall v, FOfree_ctx v [].
Proof. intros v H []. Qed.

Ltac free_ctx :=
  lazymatch goal with
  | |- FOfree_ctx _ (_ ++ _) => apply FOfree_ctx_app_inv; free_ctx
  | |- FOfree_ctx _ (_ :: _) => apply FOfree_ctx_cons; [free_fm | free_ctx]
  | |- FOfree_ctx _ [] => apply FOfree_ctx_nil
  | |- FOfree_ctx ?w _ =>
      match goal with HG : FOctx_avoid _ ?lo ?hi |- _ => apply HG; lia end
  end.

(** ** Agreement with a shift of position. *)

Definition FOAGRS (L Lb c d c' d' : FOTerm) : FOFormula :=
  FOForall 469 (FOImplF (FOExists 470 (FOEq (FOPlus (FOVar 469) (FOSucc (FOVar 470))) Lb))
    (FOForall 471 (FOImplF (FObetaF 480 c d (FOVar 469) (FOVar 471))
                           (FObetaF 484 c' d' (FOPlus L (FOVar 469)) (FOVar 471))))).

Lemma FOPrH_agrs_beta : forall n G L Lb c d c' d' t x v,
  FOPrH n G (FOAGRS L Lb c d c' d') -> FOPrH n G (FOlt470 t Lb) ->
  v + 4 <= 420 -> FOctx_avoid G v (v + 4) -> FOctx_avoid G 480 488 ->
  FOtms_avoid [L; Lb; c; d; c'; d'; t; x] 420 500 ->
  FOtms_avoid [L; Lb; c; d; c'; d'; t; x] v (v + 4) ->
  FOPrH n G (FObetaF v c d t x .-> FObetaF v c' d' (FOPlus L t) x).
Proof.
  intros n G L Lb c d c' d' t x v HA Hlt Hv HG1 HG2 Hav1 Hav2.
  assert (Vt : FOtm_avoid t 420 500) by avoid_tm.
  assert (Vx : FOtm_avoid x 420 500) by avoid_tm.
  unfold FOAGRS in HA.
  fo_inst_f HA t Vt Hav1.
  pose proof (FOPrH_mp _ _ _ _ HA Hlt) as H2. clear HA.
  fo_inst_f H2 x Vx Hav1.
  apply (FOPrH_imp_trans n G _ (FObetaF 480 c d t x)).
  { apply (FOPrH_beta_rebase n G v 480 c d t x ltac:(lia)
             (fun w H1 H3 => HG2 w ltac:(lia) ltac:(lia))); avoid_tm. }
  apply (FOPrH_imp_trans n G _ (FObetaF 484 c' d' (FOPlus L t) x)); [exact H2|].
  apply (FOPrH_beta_rebase n G 484 v c' d' (FOPlus L t) x ltac:(lia) HG1); avoid_tm.
Qed.

(** ** The shift of a justification code.

    For a derivation placed after [L] entries, the premise indices of
    modus ponens, generalization and Loeb entries move up by [L]; every
    other code is unchanged.  [FOSHIFTC L t p y]: the code with tag [t]
    and payload [p] shifts to [y].  [FOSHROW]: the code at position [i]
    of one track shifts to the code at position [i'] of another. *)

Definition FOSHIFTMP (L p y : FOTerm) : FOFormula :=
  FOForall 440 (FOForall 441 (FOImplF (FOcpairF (FOVar 440) (FOVar 441) p)
    (FOExists 442 (FOAnd (FOcpairF (FOPlus L (FOVar 440)) (FOPlus L (FOVar 441)) (FOVar 442))
                          (FOcpairF (FOnumeral 4) (FOVar 442) y))))).

Definition FOSHIFTC (L t p y : FOTerm) : FOFormula :=
  FOOr (FOAnd (FOEq t (FOnumeral 4)) (FOSHIFTMP L p y))
  (FOOr (FOAnd (FOEq t (FOnumeral 5)) (FOcpairF (FOnumeral 5) (FOPlus L p) y))
  (FOOr (FOAnd (FOEq t (FOnumeral 6)) (FOcpairF (FOnumeral 6) (FOPlus L p) y))
        (FOAnd (FONeg (FOEq t (FOnumeral 4)))
          (FOAnd (FONeg (FOEq t (FOnumeral 5)))
            (FOAnd (FONeg (FOEq t (FOnumeral 6))) (FOcpairF t p y)))))).

Definition FOSHROW (L cj dj cj' dj' i i' : FOTerm) : FOFormula :=
  FOForall 445 (FOForall 446 (FOForall 447
    (FOImplF (FObetaF 480 cj dj i (FOVar 447))
      (FOImplF (FOcpairF (FOVar 445) (FOVar 446) (FOVar 447))
        (FOExists 448 (FOAnd (FObetaF 484 cj' dj' i' (FOVar 448))
                             (FOSHIFTC L (FOVar 445) (FOVar 446) (FOVar 448)))))))).

Lemma FOsubst_f_SHIFTMP : forall x s L p y,
  x <> 440 -> x <> 441 -> x <> 442 ->
  FOsubst_f x s (FOSHIFTMP L p y) =
  FOSHIFTMP (FOsubst_t x s L) (FOsubst_t x s p) (FOsubst_t x s y).
Proof. intros. unfold FOSHIFTMP. autorewrite with fosubf. reflexivity. Qed.

Lemma FOsubst_f_SHIFTC : forall x s L t p y,
  x <> 440 -> x <> 441 -> x <> 442 ->
  FOsubst_f x s (FOSHIFTC L t p y) =
  FOSHIFTC (FOsubst_t x s L) (FOsubst_t x s t) (FOsubst_t x s p) (FOsubst_t x s y).
Proof.
  intros. unfold FOSHIFTC. autorewrite with fosubf.
  rewrite FOsubst_f_SHIFTMP by lia. reflexivity.
Qed.

Hint Rewrite FOsubst_f_SHIFTMP FOsubst_f_SHIFTC using nat_fast : fosubf.

Lemma FOsubst_ok_SHIFTMP : forall x s L p y, FOtm_avoid s 440 443 ->
  FOsubst_ok x s (FOSHIFTMP L p y) = true.
Proof. intros. unfold FOSHIFTMP. auto 100 with fook. Qed.

Hint Resolve FOsubst_ok_SHIFTMP : fook.

Lemma FOsubst_ok_SHIFTC : forall x s L t p y, FOtm_avoid s 440 443 ->
  FOsubst_ok x s (FOSHIFTC L t p y) = true.
Proof. intros. unfold FOSHIFTC. auto 100 with fook. Qed.

Ltac ok_fast_leaf V ::=
  lazymatch goal with
  | |- FOsubst_ok _ _ (FOROWAG _ _ _ _ _ _) = true =>
      apply FOsubst_ok_ROWAG; refine (FOtm_avoid_sub _ _ _ _ _ V _ _); lia
  | |- FOsubst_ok _ _ (FOcpairF _ _ _) = true => apply FOsubst_ok_cpairF
  | |- FOsubst_ok _ _ (FOSHIFTC _ _ _ _) = true =>
      apply FOsubst_ok_SHIFTC; refine (FOtm_avoid_sub _ _ _ _ _ V _ _); lia
  | |- FOsubst_ok _ _ (FOSHIFTMP _ _ _) = true =>
      apply FOsubst_ok_SHIFTMP; refine (FOtm_avoid_sub _ _ _ _ _ V _ _); lia
  end.

(** Reading a shifted code off [FOSHROW]. *)

Lemma FOPrH_shrow_use : forall n G L cj dj cj' dj' i i' v tg pl jc,
  FOPrH n G (FOSHROW L cj dj cj' dj' i i') ->
  FOPrH n G (FObetaF v cj dj i jc) -> FOPrH n G (FOcpairF tg pl jc) ->
  v + 4 <= 420 -> FOctx_avoid G v (v + 4) -> FOctx_avoid G 420 500 ->
  FOtms_avoid [L; cj; dj; cj'; dj'; i; i'; tg; pl; jc] 420 500 ->
  FOtms_avoid [cj; dj; i; jc] v (v + 4) ->
  FOPrH n G (FOExists 448 (FOAnd (FObetaF 484 cj' dj' i' (FOVar 448))
                                  (FOSHIFTC L tg pl (FOVar 448)))).
Proof.
  intros n G L cj dj cj' dj' i i' v tg pl jc H Hb Hc Hv HG1 HG2 Hav1 Hav2.
  assert (Vtg : FOtm_avoid tg 420 500) by avoid_tm.
  assert (Vpl : FOtm_avoid pl 420 500) by avoid_tm.
  assert (Vjc : FOtm_avoid jc 420 500) by avoid_tm.
  unfold FOSHROW in H.
  fo_inst_f H tg Vtg Hav1. fo_inst_f H pl Vpl Hav1. fo_inst_f H jc Vjc Hav1.
  refine (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ H _) Hc).
  refine (FOPrH_mp _ _ _ _ _ Hb).
  apply (FOPrH_beta_rebase n G v 480 cj dj i jc ltac:(lia)
           (fun w H1 H3 => HG2 w ltac:(lia) ltac:(lia))); avoid_tm.
Qed.

(** ** Reasoning in a one-formula context.

    A consequence drawn from a single premise in the context holding
    only that premise holds in every context deriving the premise, so
    the freshness conditions of its eigenvariables concern the premise
    alone. *)

Lemma FOPrH_ctxfree : forall n G A B, FOPrH n [A] B -> FOPrH n G A -> FOPrH n G B.
Proof.
  intros n G A B H1 H2.
  apply (FOPrH_mp n G A B); [|exact H2].
  apply (FOPrH_weaken n []); [intros X []|].
  apply FOPrH_intro. exact H1.
Qed.

Lemma FOfree_ctx_single : forall v A, FOfree_in v A = false -> FOfree_ctx v [A].
Proof. intros v A HA H [<-|[]]. exact HA. Qed.

(** ** Bounded existentials introduced at a term. *)

Lemma FOPrH_bex_intro_t : forall n G x t s A,
  x <> 498 -> S x <> 498 ->
  FOtm_avoid s 498 499 -> FOtm_avoid t 498 499 ->
  FOtm_avoid s (S x) (S (S x)) -> FOtm_avoid t x (S (S x)) ->
  FOPrH n G (FOle (FOSucc s) t) ->
  FOsubst_ok x s A = true ->
  FOPrH n G (FOsubst_f x s A) -> FOPrH n G (FOBexC x t A).
Proof.
  intros n G x t s A Hx1 Hx2 Hs1 Ht1 Hs2 Ht2 Hle Hok HA.
  rewrite FOBexC_ltv.
  apply (FOPrH_ex_intro _ _ x s).
  { apply FOsubst_ok_and; [|exact Hok]. unfold FOltv.
    apply FOsubst_ok_ex; [apply Hs2; lia | apply FOsubst_ok_eq]. }
  rewrite FOsubst_f_and. apply FOPrH_and_intro; [|exact HA].
  unfold FOltv. rewrite FOsubst_f_ex_ne by lia.
  rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_var_eq', FOsubst_t_succ.
  rewrite FOsubst_t_var_ne by lia.
  rewrite (FOsubst_t_not_in t x s (Ht2 x ltac:(lia) ltac:(lia))).
  refine (FOPrH_ctxfree n G _ _ _ Hle). unfold FOle.
  refine (FOPrH_ex_elim n _ 498 (FOEq (FOPlus (FOSucc s) (FOVar 498)) t) _
            (FOfree_ctx_single _ _ (FOfree_in_ex_self _ _)) _
            (FOPrH_assum n [FOle (FOSucc s) t] (FOle (FOSucc s) t) (or_introl eq_refl)) _).
  - cbn [FOfree_in FOin_tm]. nat_eqb_simpl.
    rewrite (Hs1 498), (Ht1 498) by lia. reflexivity.
  - apply (FOPrH_ex_intro _ _ (S x) (FOVar 498)); [reflexivity|].
    rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_succ, FOsubst_t_var_eq'.
    rewrite (FOsubst_t_not_in s (S x) _ (Hs2 (S x) ltac:(lia) ltac:(lia))),
            (FOsubst_t_not_in t (S x) _ (Ht2 (S x) ltac:(lia) ltac:(lia))).
    fo_lin [(.S .0, t, .S s .+ #498)].
Qed.

(** A conjunction whose first conjunct is refuted implies anything. *)

Lemma FOPrH_and_absurd : forall n G P X Y,
  FOPrH n G (FONeg P) -> FOPrH n G (FOAnd P X .-> Y).
Proof.
  intros n G P X Y H. apply FOPrH_intro. apply FOPrH_efq.
  apply (FOPrH_mp _ _ P FOFalseF); [apply FOPrH_weak_app; exact H|].
  exact (FOPrH_and_l _ _ _ _ (FOPrH_last n G _)).
Qed.

Lemma FOPrH_tag_and_absurd : forall n G t k m X Y,
  k <> m -> FOPrH n G (FOEq t (FOnumeral k)) ->
  FOPrH n G (FOAnd (FOEq t (FOnumeral m)) X .-> Y).
Proof.
  intros n G t k m X Y Hkm H. apply FOPrH_intro. apply FOPrH_efq.
  apply (FOPrH_tag_absurd _ _ t k m Hkm); [apply FOPrH_weak_app; exact H|].
  exact (FOPrH_and_l _ _ _ _ (FOPrH_last n G _)).
Qed.

(** ** The justification check: elimination at its own variables and
    introduction at a shifted code. *)

Lemma FOPrH_JUSTCK_elim : forall n G B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds cj dj i C,
  FOctx_avoid G B (B + 16) -> 2 <= B ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; cs; ds; cj; dj; i] B (B + 16) ->
  FOfree_in B C = false -> FOfree_in (B + 2) C = false ->
  FOfree_in (B + 12) C = false -> FOfree_in (B + 14) C = false ->
  FOPrH n (G ++ [FOltv B (FOSucc cs); FOltv (B + 2) (FOSucc cj);
                 FObetaF (B + 4) cs ds i (FOVar B); FObetaF (B + 8) cj dj i (FOVar (B + 2));
                 FOltv (B + 12) (FOSucc (FOVar (B + 2)));
                 FOltv (B + 14) (FOSucc (FOVar (B + 2)));
                 FOcpairF (FOVar (B + 12)) (FOVar (B + 14)) (FOVar (B + 2))])
    (FOJDISJ B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i (FOVar B)
       (FOVar (B + 12)) (FOVar (B + 14)) .-> C) ->
  FOPrH n G (FOJUSTCK B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds cj dj i .-> C).
Proof.
  intros n G B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds cj dj i C
    HG HB Hav F0 F2 F12 F14 H.
  rewrite FOJUSTCK_split.
  apply FOPrH_imp_bexl; [apply HG; lia | exact F0 |].
  apply FOPrH_imp_bexl; [free_ctx | exact F2 |].
  apply FOPrH_imp_andl. apply FOPrH_intro.
  apply FOPrH_imp_andl. apply FOPrH_intro.
  unfold FOCHK.
  apply FOPrH_imp_bexl; [free_ctx | exact F12 |].
  apply FOPrH_imp_bexl; [free_ctx | exact F14 |].
  apply FOPrH_imp_andl. apply FOPrH_intro.
  refine (FOPrH_weaken n _ _ _ _ H).
  intros X HX. rewrite <- !app_assoc. exact HX.
Qed.

Lemma FOPrH_JUSTCK_intro : forall n G B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds cj dj i y,
  B + 232 <= 498 ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; cs; ds; cj; dj; i; y]
    B (B + 232) ->
  FOtms_avoid [cj; y] 498 499 ->
  FOPrH n G (FOltv B (FOSucc cs)) ->
  FOPrH n G (FObetaF (B + 4) cs ds i (FOVar B)) ->
  FOPrH n G (FOle (FOSucc y) (FOSucc cj)) ->
  FOPrH n G (FObetaF (B + 8) cj dj i y) ->
  FOPrH n G (FOCHK B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i (FOVar B) y) ->
  FOPrH n G (FOJUSTCK B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds cj dj i).
Proof.
  intros n G B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds cj dj i y
    HB Hav Hav2 H1 H2 H3 H4 H5.
  rewrite FOJUSTCK_split.
  apply FOPrH_bex_same; [exact H1|].
  assert (Vy : FOtm_avoid y (B + 2) (B + 232)) by avoid_tm.
  apply (FOPrH_bex_intro_t n G (B + 2) (FOSucc cj) y); try lia;
    try avoid_tm; [exact H3 | |].
  - apply FOsubst_ok_and; [apply FOsubst_ok_betaF; avoid_tm|].
    apply FOsubst_ok_and; [apply FOsubst_ok_betaF; avoid_tm|].
    apply FOsubst_ok_CHK. avoid_tm.
  - rewrite !FOsubst_f_and, !FOsubst_f_betaF, FOsubst_f_CHK by lia.
    rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne by lia.
    subst_avoid_h Hav.
    apply FOPrH_and_intro; [exact H2|]. apply FOPrH_and_intro; [exact H4 | exact H5].
Qed.

Lemma FOPrH_CHK_intro : forall n G B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds i vd y p,
  B + 232 <= 498 ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; cs; ds; i; vd; y]
    (B + 12) (B + 232) ->
  FOtms_avoid [p] (B + 15) (B + 232) ->
  FOtms_avoid [y; p] 498 499 ->
  FOPrH n G (FOltv (B + 12) (FOSucc y)) ->
  FOPrH n G (FOle (FOSucc p) (FOSucc y)) ->
  FOPrH n G (FOcpairF (FOVar (B + 12)) p y) ->
  FOPrH n G (FOJDISJ B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd
               (FOVar (B + 12)) p) ->
  FOPrH n G (FOCHK B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd y).
Proof.
  intros n G B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd y p
    HB Hav Hp Hav2 H1 H2 H3 H4.
  unfold FOCHK. apply FOPrH_bex_same; [exact H1|].
  apply (FOPrH_bex_intro_t n G (B + 14) (FOSucc y) p); try lia;
    try avoid_tm; [exact H2 | |].
  - apply FOsubst_ok_and; [apply FOsubst_ok_cpairF|].
    apply FOsubst_ok_JDISJ. avoid_tm.
  - rewrite FOsubst_f_and, FOsubst_f_cpairF, FOsubst_f_JDISJ by lia.
    rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne by lia.
    subst_avoid_h Hav.
    apply FOPrH_and_intro; assumption.
Qed.

(** ** Reading and naming a shifted justification code. *)

Lemma FOPrH_shrow_elim : forall n G L cj dj cj' dj' i i' v tg pl jc y C,
  FOPrH n G (FOSHROW L cj dj cj' dj' i i') ->
  FOPrH n G (FObetaF v cj dj i jc) -> FOPrH n G (FOcpairF tg pl jc) ->
  v + 4 <= 420 -> FOctx_avoid G v (v + 4) -> FOctx_avoid G 420 500 ->
  FOtms_avoid [L; cj; dj; cj'; dj'; i; i'; tg; pl; jc] 420 500 ->
  FOtms_avoid [cj; dj; i; jc] v (v + 4) ->
  2 <= y -> y < 420 -> FOfree_ctx y G -> FOfree_in y C = false ->
  FOtms_avoid [L; cj'; dj'; i'; tg; pl] y (S y) ->
  FOPrH n (G ++ [FOAnd (FObetaF 484 cj' dj' i' (FOVar y)) (FOSHIFTC L tg pl (FOVar y))]) C ->
  FOPrH n G C.
Proof.
  intros n G L cj dj cj' dj' i i' v tg pl jc y C HS Hb Hc Hv HG1 HG2 Hav1 Hav2
    Hy1 Hy2 HGy HCy Hav3 H.
  pose proof (FOPrH_shrow_use n G L cj dj cj' dj' i i' v tg pl jc HS Hb Hc Hv HG1 HG2
                Hav1 Hav2) as E.
  assert (Vy : FOtm_avoid (FOVar y) 420 500) by (apply FOtm_avoid_var; lia).
  refine (FOPrH_exe n G 448 y _ C E HGy HCy _ _ _).
  - unfold FOSHIFTC, FOSHIFTMP. free_fm.
  - ok_fast Vy.
  - rewrite FOsubst_f_and, FOsubst_f_betaF, FOsubst_f_SHIFTC by nat_fast.
    rewrite FOsubst_t_var_eq'. subst_avoid_h Hav1. exact H.
Qed.

Lemma FOPrH_shiftmp_elim : forall n G L p y a b q C,
  FOPrH n G (FOSHIFTMP L p y) -> FOPrH n G (FOcpairF a b p) ->
  FOctx_avoid G 420 500 -> FOtms_avoid [L; p; y; a; b] 420 500 ->
  2 <= q -> q < 420 -> FOfree_ctx q G -> FOfree_in q C = false ->
  FOtms_avoid [L; y; a; b] q (S q) ->
  FOPrH n (G ++ [FOAnd (FOcpairF (FOPlus L a) (FOPlus L b) (FOVar q))
                       (FOcpairF (FOnumeral 4) (FOVar q) y)]) C ->
  FOPrH n G C.
Proof.
  intros n G L p y a b q C HS Hc HG Hav Hq1 Hq2 HGq HCq Hav3 H.
  assert (Va : FOtm_avoid a 420 500) by avoid_tm.
  assert (Vb : FOtm_avoid b 420 500) by avoid_tm.
  assert (Vq : FOtm_avoid (FOVar q) 420 500) by (apply FOtm_avoid_var; lia).
  unfold FOSHIFTMP in HS.
  fo_inst_f HS a Va Hav. fo_inst_f HS b Vb Hav.
  pose proof (FOPrH_mp _ _ _ _ HS Hc) as E.
  refine (FOPrH_exe n G 442 q _ C E HGq HCq _ _ _).
  - free_fm.
  - ok_fast Vq.
  - rewrite FOsubst_f_and, !FOsubst_f_cpairF, !FOsubst_t_plus, FOsubst_t_var_eq',
      FOsubst_t_numeral.
    subst_avoid_h Hav. exact H.
Qed.

(** ** The payload disjunction for a code the shift leaves unchanged. *)

Lemma FOtr_JDISJ_other : forall n G B cores T T' cs ds i cs' ds' i' vd tg pl,
  FOTabMono n G T T' ->
  FOPrH n G (FONeg (FOEq tg (FOnumeral 4))) ->
  FOPrH n G (FONeg (FOEq tg (FOnumeral 5))) ->
  FOPrH n G (FONeg (FOEq tg (FOnumeral 6))) ->
  B + 232 <= 400 -> FOctx_avoid G (B + 16) (B + 232) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [vd; pl]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [vd; pl]) (B + 16) (B + 232) ->
  FOPrH n G (FOJDISJ B cores (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) cs ds i vd tg pl .->
             FOJDISJ B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T')
               (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' i' vd tg pl).
Proof.
  intros n G B cores T T' cs ds i cs' ds' i' vd tg pl Hm H4 H5 H6 HB HG HG2 Hav1 Hav2.
  pose proof Hm as (HmA & Hct & Hc1 & Hc2 & Hc3 & Hcr).
  unfold FOJDISJ.
  apply FOPrH_or_mono; [apply FOPrH_and_mono; [apply FOPrH_imp_refl | fo_tr_leaf]|].
  apply FOPrH_or_mono; [apply FOPrH_and_mono; [apply FOPrH_imp_refl | fo_tr_leaf]|].
  apply FOPrH_or_mono; [apply FOPrH_and_mono; [apply FOPrH_imp_refl | fo_tr_leaf]|].
  apply FOPrH_or_mono; [apply FOPrH_and_mono; [apply FOPrH_imp_refl | fo_tr_leaf]|].
  apply FOPrH_or_mono; [apply FOPrH_and_absurd; exact H4|].
  apply FOPrH_or_mono; [apply FOPrH_and_absurd; exact H5|].
  apply FOPrH_or_mono; [apply FOPrH_and_absurd; exact H6|].
  apply FOPrH_or_mono; [apply FOPrH_and_mono; [apply FOPrH_imp_refl | fo_tr_leaf]|].
  apply FOPrH_or_mono; [apply FOPrH_and_mono; [apply FOPrH_imp_refl | fo_tr_leaf]|].
  apply FOPrH_or_mono; apply FOPrH_and_mono; [apply FOPrH_imp_refl | fo_tr_leaf
                                             | apply FOPrH_imp_refl | fo_tr_leaf].
Qed.

(** ** Modus ponens, generalization and Loeb entries split at their
    premise indices.

    Each recognizer binds its premise index (two for modus ponens)
    below the current position; the remainder reads the formula track
    at the index.  The remainders transfer to a track holding the same
    entries [L] positions later, at the index moved by [L]. *)

Definition FOJMPREST (B : nat) (cs ds vd a b : FOTerm) : FOFormula :=
  FOBexC (B+4) (FOSucc cs) (FOBexC (B+6) (FOSucc cs)
    (FOAnd (FObetaF (B+8) cs ds a (FOVar (B+4)))
    (FOAnd (FObetaF (B+12) cs ds b (FOVar (B+6)))
       (FOPATF (B+16) [FOVar (B+6); vd] cpatImpl01 (FOVar (B+4)))))).

Lemma FOJMP_split : forall B cs ds vd pl ipos,
  FOJMP B cs ds vd pl ipos =
  FOBexC B ipos (FOBexC (B+2) ipos
    (FOAnd (FOcpairF (FOVar B) (FOVar (B+2)) pl)
       (FOJMPREST B cs ds vd (FOVar B) (FOVar (B+2))))).
Proof. reflexivity. Qed.

Definition FOJGENREST (B : nat) (cs ds vd a : FOTerm) : FOFormula :=
  FOBexC (B+2) (FOSucc cs)
    (FOAnd (FObetaF (B+4) cs ds a (FOVar (B+2)))
    (FOBexC (B+8) (FOSucc vd)
      (FOPATF (B+10) [FOVar (B+8); FOVar (B+2)] cpatAll01 vd))).

Lemma FOJGEN_split : forall B cs ds vd pl ipos,
  FOJGEN B cs ds vd pl ipos =
  FOBexC B ipos (FOAnd (FOEq (FOVar B) pl) (FOJGENREST B cs ds vd (FOVar B))).
Proof. reflexivity. Qed.

Definition FOJLOEBREST (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (cs ds vd a : FOTerm) : FOFormula :=
  FOBexC (B+2) (FOSucc cs)
    (FOAnd (FObetaF (B+4) cs ds a (FOVar (B+2)))
    (FOBexC (B+8) (FOSucc cr)
    (FOBexC (B+10) (FOSucc cr)
    (FOBexC (B+12) (FOSucc cr)
    (FOBexC (B+14) (FOSucc cr)
      (FOAnd
         (FOlookup (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len
            (FOnumeral 5) (FOVar 0) FOZero FOZero (FOVar (B+8)))
      (FOAnd
         (FOlookup (B+38) ct dt c1 d1 c2 d2 c3 d3 cr dr len
            (FOnumeral 3) FOZero (FOVar (B+8)) (FOVar 0)
            (FOVar (B+10)))
      (FOAnd
         (FOlookup (B+60) ct dt c1 d1 c2 d2 c3 d3 cr dr len
            (FOnumeral 5) vd FOZero FOZero (FOVar (B+12)))
      (FOAnd
         (FOlookup (B+82) ct dt c1 d1 c2 d2 c3 d3 cr dr len
            (FOnumeral 3) (FOnumeral 1) (FOVar (B+12))
            (FOVar (B+10)) (FOVar (B+14)))
         (FOPATF (B+104) [FOVar (B+14); vd] cpatImpl01 (FOVar (B+2))
         )))))))))).

Lemma FOJLOEB_split : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd pl ipos,
  FOJLOEB B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd pl ipos =
  FOBexC B ipos (FOAnd (FOEq (FOVar B) pl)
    (FOJLOEBREST B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd (FOVar B))).
Proof. reflexivity. Qed.

Lemma FOsubst_f_JMPREST : forall x s B cs ds vd a b, x < B + 4 ->
  FOsubst_f x s (FOJMPREST B cs ds vd a b) =
  FOJMPREST B (FOsubst_t x s cs) (FOsubst_t x s ds) (FOsubst_t x s vd)
    (FOsubst_t x s a) (FOsubst_t x s b).
Proof. intros. unfold FOJMPREST. autorewrite with fosubf. reflexivity. Qed.

Lemma FOsubst_f_JGENREST : forall x s B cs ds vd a, x < B + 2 ->
  FOsubst_f x s (FOJGENREST B cs ds vd a) =
  FOJGENREST B (FOsubst_t x s cs) (FOsubst_t x s ds) (FOsubst_t x s vd) (FOsubst_t x s a).
Proof. intros. unfold FOJGENREST. autorewrite with fosubf. reflexivity. Qed.

Lemma FOsubst_f_JLOEBREST : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd a,
  0 < x -> x < B + 2 ->
  FOsubst_f x s (FOJLOEBREST B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd a) =
  FOJLOEBREST B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1)
    (FOsubst_t x s d1) (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3)
    (FOsubst_t x s d3) (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s cs) (FOsubst_t x s ds) (FOsubst_t x s vd) (FOsubst_t x s a).
Proof.
  intros. unfold FOJLOEBREST. autorewrite with fosubst. reflexivity.
Qed.

Lemma FOsubst_ok_JMPREST : forall x s B cs ds vd a b, FOtm_avoid s (B + 4) (B + 24) ->
  FOsubst_ok x s (FOJMPREST B cs ds vd a b) = true.
Proof. intros. unfold FOJMPREST. auto 100 with fook. Qed.

Lemma FOsubst_ok_JGENREST : forall x s B cs ds vd a, FOtm_avoid s (B + 2) (B + 18) ->
  FOsubst_ok x s (FOJGENREST B cs ds vd a) = true.
Proof. intros. unfold FOJGENREST. auto 100 with fook. Qed.

Lemma FOsubst_ok_JLOEBREST : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd a,
  FOtm_avoid s (B + 2) (B + 112) ->
  FOsubst_ok x s (FOJLOEBREST B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd a) = true.
Proof. intros. unfold FOJLOEBREST. auto 100 with fook. Qed.

(** Introduction at given indices. *)

Lemma FOPrH_JMP_intro : forall n G B cs ds vd pl ipos a b,
  B + 24 <= 498 ->
  FOtms_avoid [cs; ds; vd; pl; ipos] B (B + 24) ->
  FOtms_avoid [a] (B + 1) (B + 24) -> FOtms_avoid [b] (B + 3) (B + 24) ->
  FOtms_avoid [ipos; a; b] 498 499 ->
  FOPrH n G (FOle (FOSucc a) ipos) -> FOPrH n G (FOle (FOSucc b) ipos) ->
  FOPrH n G (FOcpairF a b pl) -> FOPrH n G (FOJMPREST B cs ds vd a b) ->
  FOPrH n G (FOJMP B cs ds vd pl ipos).
Proof.
  intros n G B cs ds vd pl ipos a b HB Hav Hava Havb Hav2 Ha Hb Hc HR.
  rewrite FOJMP_split.
  apply (FOPrH_bex_intro_t n G B ipos a); try lia; try avoid_tm; [exact Ha| |].
  { apply FOsubst_ok_bex; [fr_tm | fr_tm|]. apply FOsubst_ok_and; [apply FOsubst_ok_cpairF|].
    apply FOsubst_ok_JMPREST. avoid_tm. }
  rewrite FOsubst_f_bex, FOsubst_f_and, FOsubst_f_cpairF, FOsubst_f_JMPREST by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne by lia. subst_avoid_h Hav.
  apply (FOPrH_bex_intro_t n G (B + 2) ipos b); try lia; try avoid_tm;
    [exact Hb| |].
  { apply FOsubst_ok_and; [apply FOsubst_ok_cpairF|].
    apply FOsubst_ok_JMPREST. avoid_tm. }
  rewrite FOsubst_f_and, FOsubst_f_cpairF, FOsubst_f_JMPREST by lia.
  rewrite FOsubst_t_var_eq'. subst_avoid_h Hav. subst_avoid_h Hava.
  apply FOPrH_and_intro; assumption.
Qed.

Lemma FOPrH_JGEN_intro : forall n G B cs ds vd pl ipos a,
  B + 18 <= 498 ->
  FOtms_avoid [cs; ds; vd; pl; ipos] B (B + 18) ->
  FOtms_avoid [a] (B + 1) (B + 18) ->
  FOtms_avoid [ipos; a] 498 499 ->
  FOPrH n G (FOle (FOSucc a) ipos) -> FOPrH n G (FOEq a pl) ->
  FOPrH n G (FOJGENREST B cs ds vd a) ->
  FOPrH n G (FOJGEN B cs ds vd pl ipos).
Proof.
  intros n G B cs ds vd pl ipos a HB Hav Hava Hav2 Ha He HR.
  rewrite FOJGEN_split.
  apply (FOPrH_bex_intro_t n G B ipos a); try lia; try avoid_tm; [exact Ha| |].
  { apply FOsubst_ok_and; [apply FOsubst_ok_eq|].
    apply FOsubst_ok_JGENREST. avoid_tm. }
  rewrite FOsubst_f_and, FOsubst_f_eq, FOsubst_f_JGENREST by lia.
  rewrite FOsubst_t_var_eq'. subst_avoid_h Hav.
  apply FOPrH_and_intro; assumption.
Qed.

Lemma FOPrH_JLOEB_intro : forall n G B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd pl ipos a,
  B + 112 <= 498 -> 0 < B ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; cs; ds; vd; pl; ipos]
    B (B + 112) ->
  FOtms_avoid [a] (B + 1) (B + 112) ->
  FOtms_avoid [ipos; a] 498 499 ->
  FOPrH n G (FOle (FOSucc a) ipos) -> FOPrH n G (FOEq a pl) ->
  FOPrH n G (FOJLOEBREST B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd a) ->
  FOPrH n G (FOJLOEB B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd pl ipos).
Proof.
  intros n G B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd pl ipos a HB HB0 Hav Hava Hav2
    Ha He HR.
  rewrite FOJLOEB_split.
  apply (FOPrH_bex_intro_t n G B ipos a); try lia; try avoid_tm; [exact Ha| |].
  { apply FOsubst_ok_and; [apply FOsubst_ok_eq|].
    apply FOsubst_ok_JLOEBREST. avoid_tm. }
  rewrite FOsubst_f_and, FOsubst_f_eq, FOsubst_f_JLOEBREST by lia.
  rewrite FOsubst_t_var_eq'. subst_avoid_h Hav.
  apply FOPrH_and_intro; assumption.
Qed.

(** Elimination at the recognizers' own variables. *)

Lemma FOPrH_JMP_elim : forall n G B cs ds vd pl ipos C,
  FOctx_avoid G B (B + 4) -> 2 <= B ->
  FOtms_avoid [cs; ds; vd; pl; ipos] B (B + 4) ->
  FOfree_in B C = false -> FOfree_in (B + 2) C = false ->
  FOPrH n (G ++ [FOltv B ipos; FOltv (B + 2) ipos; FOcpairF (FOVar B) (FOVar (B + 2)) pl])
    (FOJMPREST B cs ds vd (FOVar B) (FOVar (B + 2)) .-> C) ->
  FOPrH n G (FOJMP B cs ds vd pl ipos .-> C).
Proof.
  intros n G B cs ds vd pl ipos C HG HB Hav F0 F2 H.
  rewrite FOJMP_split.
  apply FOPrH_imp_bexl; [apply HG; lia | exact F0 |].
  apply FOPrH_imp_bexl; [free_ctx | exact F2 |].
  apply FOPrH_imp_andl. apply FOPrH_intro.
  refine (FOPrH_weaken n _ _ _ _ H).
  intros X HX. rewrite <- !app_assoc. exact HX.
Qed.

Lemma FOPrH_JGEN_elim : forall n G B cs ds vd pl ipos C,
  FOctx_avoid G B (B + 2) -> FOtms_avoid [ipos] B (B + 2) ->
  FOfree_in B C = false ->
  FOPrH n (G ++ [FOltv B ipos; FOEq (FOVar B) pl])
    (FOJGENREST B cs ds vd (FOVar B) .-> C) ->
  FOPrH n G (FOJGEN B cs ds vd pl ipos .-> C).
Proof.
  intros n G B cs ds vd pl ipos C HG Hav F0 H.
  rewrite FOJGEN_split.
  apply FOPrH_imp_bexl; [apply HG; lia | exact F0 |].
  apply FOPrH_imp_andl. apply FOPrH_intro.
  refine (FOPrH_weaken n _ _ _ _ H).
  intros X HX. rewrite <- !app_assoc. exact HX.
Qed.

Lemma FOPrH_JLOEB_elim : forall n G B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd pl ipos C,
  FOctx_avoid G B (B + 2) -> FOtms_avoid [ipos] B (B + 2) ->
  FOfree_in B C = false ->
  FOPrH n (G ++ [FOltv B ipos; FOEq (FOVar B) pl])
    (FOJLOEBREST B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd (FOVar B) .-> C) ->
  FOPrH n G (FOJLOEB B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd pl ipos .-> C).
Proof.
  intros n G B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd pl ipos C HG Hav F0 H.
  rewrite FOJLOEB_split.
  apply FOPrH_imp_bexl; [apply HG; lia | exact F0 |].
  apply FOPrH_imp_andl. apply FOPrH_intro.
  refine (FOPrH_weaken n _ _ _ _ H).
  intros X HX. rewrite <- !app_assoc. exact HX.
Qed.

(** Transfer of the remainders to the shifted track. *)

Lemma FOtr_JMPREST_sh : forall n G B cs ds cs' ds' vd a b L Lb,
  FOPrH n G (FOAGRS L Lb cs ds cs' ds') ->
  FOPrH n G (FOlt470 a Lb) -> FOPrH n G (FOlt470 b Lb) ->
  FOPrH n G (FOle (FOSucc cs) (FOSucc cs')) ->
  B + 24 <= 400 -> FOctx_avoid G (B + 4) (B + 24) -> FOctx_avoid G 420 500 ->
  FOtms_avoid [cs; ds; cs'; ds'; vd; a; b; L; Lb] 420 500 ->
  FOtms_avoid [cs; ds; cs'; ds'; vd; a; b; L; Lb] (B + 4) (B + 24) ->
  FOPrH n G (FOJMPREST B cs ds vd a b .-> FOJMPREST B cs' ds' vd (FOPlus L a) (FOPlus L b)).
Proof.
  intros n G B cs ds cs' ds' vd a b L Lb HA Ha Hb Hcs HB HG HG2 Hav1 Hav2.
  unfold FOJMPREST.
  apply FOPrH_bex_mono; [apply HG; lia | mono_code' | apply FOPrH_imp_weaken].
  apply FOPrH_bex_mono; [apply HG; lia | mono_code' | apply FOPrH_imp_weaken].
  apply FOPrH_and_mono; [|apply FOPrH_and_mono; [|apply FOPrH_imp_refl]].
  - apply (FOPrH_agrs_beta n G L Lb cs ds cs' ds' a (FOVar (B + 4)) (B + 8) HA Ha);
      [lia | intros ? ? ?; apply HG; lia | intros ? ? ?; apply HG2; lia | avoid_tms | avoid_tms].
  - apply (FOPrH_agrs_beta n G L Lb cs ds cs' ds' b (FOVar (B + 6)) (B + 12) HA Hb);
      [lia | intros ? ? ?; apply HG; lia | intros ? ? ?; apply HG2; lia | avoid_tms | avoid_tms].
Qed.

Lemma FOtr_JGENREST_sh : forall n G B cs ds cs' ds' vd a L Lb,
  FOPrH n G (FOAGRS L Lb cs ds cs' ds') -> FOPrH n G (FOlt470 a Lb) ->
  FOPrH n G (FOle (FOSucc cs) (FOSucc cs')) ->
  B + 18 <= 400 -> FOctx_avoid G (B + 2) (B + 18) -> FOctx_avoid G 420 500 ->
  FOtms_avoid [cs; ds; cs'; ds'; vd; a; L; Lb] 420 500 ->
  FOtms_avoid [cs; ds; cs'; ds'; vd; a; L; Lb] (B + 2) (B + 18) ->
  FOPrH n G (FOJGENREST B cs ds vd a .-> FOJGENREST B cs' ds' vd (FOPlus L a)).
Proof.
  intros n G B cs ds cs' ds' vd a L Lb HA Ha Hcs HB HG HG2 Hav1 Hav2.
  unfold FOJGENREST.
  apply FOPrH_bex_mono; [apply HG; lia | mono_code' | apply FOPrH_imp_weaken].
  apply FOPrH_and_mono; [|apply FOPrH_imp_refl].
  apply (FOPrH_agrs_beta n G L Lb cs ds cs' ds' a (FOVar (B + 2)) (B + 4) HA Ha);
    [lia | intros ? ? ?; apply HG; lia | intros ? ? ?; apply HG2; lia | avoid_tms | avoid_tms].
Qed.

Lemma FOtr_JLOEBREST_sh : forall n G B T T' cs ds cs' ds' vd a L Lb,
  FOTabMono n G T T' ->
  FOPrH n G (FOAGRS L Lb cs ds cs' ds') -> FOPrH n G (FOlt470 a Lb) ->
  FOPrH n G (FOle (FOSucc cs) (FOSucc cs')) ->
  B + 112 <= 400 -> FOctx_avoid G (B + 2) (B + 112) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [cs; ds; cs'; ds'; vd; a; L; Lb])
    420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [cs; ds; cs'; ds'; vd; a; L; Lb])
    (B + 2) (B + 112) ->
  FOPrH n G (FOJLOEBREST B (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) cs ds vd a .->
             FOJLOEBREST B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T')
               (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' vd (FOPlus L a)).
Proof.
  intros n G B T T' cs ds cs' ds' vd a L Lb Hm HA Ha Hcs HB HG HG2 Hav1 Hav2.
  pose proof Hm as (HmA & Hct & Hc1 & Hc2 & Hc3 & Hcr).
  unfold FOJLOEBREST.
  apply FOPrH_bex_mono; [apply HG; lia | mono_code' | apply FOPrH_imp_weaken].
  apply FOPrH_and_mono.
  - apply (FOPrH_agrs_beta n G L Lb cs ds cs' ds' a (FOVar (B + 2)) (B + 4) HA Ha);
      [lia | intros ? ? ?; apply HG; lia | intros ? ? ?; apply HG2; lia | avoid_tms | avoid_tms].
  - fo_tr2.
Qed.

(** ** Freshness at any variable outside the arguments.

    The library formulas bind their own variables; a variable absent
    from every argument is not free in them, whether or not it is one
    of their binders. *)

Ltac free_any_close :=
  repeat match goal with
  | |- context [Nat.eqb ?k ?w] => is_var w; destruct (Nat.eqb k w)
  end; reflexivity.

Lemma FOfree_in_le_any : forall w a b,
  FOin_tm w a = false -> FOin_tm w b = false -> FOfree_in w (FOle a b) = false.
Proof.
  intros w a b Ha Hb. unfold FOle. cbn [FOfree_in FOin_tm].
  rewrite Ha, Hb. free_any_close.
Qed.

Lemma FOfree_in_lt470_any : forall w a b,
  FOin_tm w a = false -> FOin_tm w b = false -> FOfree_in w (FOlt470 a b) = false.
Proof.
  intros w a b Ha Hb. unfold FOlt470. cbn [FOfree_in FOin_tm].
  rewrite Ha, Hb. free_any_close.
Qed.

Lemma FOfree_in_SHIFTMP_any : forall w L p y,
  FOin_tm w L = false -> FOin_tm w p = false -> FOin_tm w y = false ->
  FOfree_in w (FOSHIFTMP L p y) = false.
Proof.
  intros w L p y HL Hp Hy. unfold FOSHIFTMP, FOAnd, FONeg, FOcpairF.
  cbn [FOfree_in FOin_tm FOnumeral]. rewrite HL, Hp, Hy. free_any_close.
Qed.

Lemma FOfree_in_SHIFTC_any : forall w L t p y,
  FOin_tm w L = false -> FOin_tm w t = false -> FOin_tm w p = false ->
  FOin_tm w y = false -> FOfree_in w (FOSHIFTC L t p y) = false.
Proof.
  intros w L t p y HL Ht Hp Hy. unfold FOSHIFTC.
  rewrite !FOfree_in_FOOr, !FOfree_in_FOAnd, !FOfree_in_FONeg,
    FOfree_in_SHIFTMP_any by assumption.
  rewrite !FOfree_in_FOcpairF. cbn [FOfree_in FOin_tm FOnumeral].
  rewrite HL, Ht, Hp, Hy. reflexivity.
Qed.

Lemma FOfree_in_ROWAG_any : forall w c d c' d' j j',
  2 <= w -> FOtms_avoid [c; d; c'; d'; j; j'] w (S w) ->
  FOfree_in w (FOROWAG c d c' d' j j') = false.
Proof.
  intros w c d c' d' j j' Hw Hav.
  destruct (Nat.eq_dec w 471) as [->|Hne].
  - unfold FOROWAG. apply FOfree_in_all_self.
  - apply FOfree_in_ROWAG_not; assumption.
Qed.

Lemma FOfree_in_AGRS_any : forall w L Lb c d c' d',
  2 <= w -> FOtms_avoid [L; Lb; c; d; c'; d'] w (S w) ->
  FOfree_in w (FOAGRS L Lb c d c' d') = false.
Proof.
  intros w L Lb c d c' d' Hw Hav.
  assert (A : forall u, In u [L; Lb; c; d; c'; d'] -> FOin_tm w u = false)
    by (intros u Hu; exact (Hav u Hu w ltac:(lia) ltac:(lia))).
  unfold FOAGRS.
  destruct (Nat.eq_dec w 469) as [->|H1]; [apply FOfree_in_all_self|].
  rewrite FOfree_in_all_ne, FOfree_in_impl by lia.
  apply Bool.orb_false_iff. split.
  - destruct (Nat.eq_dec w 470) as [->|H2]; [apply FOfree_in_ex_self|].
    rewrite FOfree_in_FOExists_neq by lia. cbn [FOfree_in FOin_tm].
    rewrite (A Lb ltac:(in_list)). nat_eqb_simpl. reflexivity.
  - destruct (Nat.eq_dec w 471) as [->|H3]; [apply FOfree_in_all_self|].
    rewrite FOfree_in_all_ne, FOfree_in_impl by lia.
    rewrite !FOfree_in_betaF_not; try reflexivity; try lia;
      first [ apply A; in_list | apply FOin_tm_var_ne; lia
            | rewrite FOin_tm_plus_eq, (A L ltac:(in_list)); apply FOin_tm_var_ne; lia ].
Qed.

Lemma FOfree_in_SHROW_any : forall w L cj dj cj' dj' i i',
  2 <= w -> FOtms_avoid [L; cj; dj; cj'; dj'; i; i'] w (S w) ->
  FOfree_in w (FOSHROW L cj dj cj' dj' i i') = false.
Proof.
  intros w L cj dj cj' dj' i i' Hw Hav.
  assert (A : forall u, In u [L; cj; dj; cj'; dj'; i; i'] -> FOin_tm w u = false)
    by (intros u Hu; exact (Hav u Hu w ltac:(lia) ltac:(lia))).
  unfold FOSHROW.
  destruct (Nat.eq_dec w 445) as [->|H1]; [apply FOfree_in_all_self|].
  rewrite FOfree_in_all_ne by lia.
  destruct (Nat.eq_dec w 446) as [->|H2]; [apply FOfree_in_all_self|].
  rewrite FOfree_in_all_ne by lia.
  destruct (Nat.eq_dec w 447) as [->|H3]; [apply FOfree_in_all_self|].
  rewrite FOfree_in_all_ne by lia.
  rewrite !FOfree_in_impl. apply Bool.orb_false_iff; split.
  { apply FOfree_in_betaF_not; try lia; first [apply A; in_list | apply FOin_tm_var_ne; lia]. }
  apply Bool.orb_false_iff; split.
  { rewrite FOfree_in_FOcpairF. rewrite !FOin_tm_var_ne by lia. reflexivity. }
  destruct (Nat.eq_dec w 448) as [->|H4]; [apply FOfree_in_ex_self|].
  rewrite FOfree_in_FOExists_neq, FOfree_in_FOAnd by lia.
  apply Bool.orb_false_iff; split.
  - apply FOfree_in_betaF_not; try lia; first [apply A; in_list | apply FOin_tm_var_ne; lia].
  - apply FOfree_in_SHIFTC_any; first [apply A; in_list | apply FOin_tm_var_ne; lia].
Qed.

Ltac free_fm ::=
  lazymatch goal with
  | |- FOfree_in _ (FOltv _ _) = false => apply FOfree_in_ltv; [lia | fr_tm]
  | |- FOfree_in _ (FObetaF _ _ _ _ _) = false =>
      apply FOfree_in_betaF_not; [lia | fr_tm | fr_tm | fr_tm | fr_tm]
  | |- FOfree_in _ (FOcpairF _ _ _) = false =>
      rewrite FOfree_in_FOcpairF; apply Bool.orb_false_iff; split;
      [apply Bool.orb_false_iff; split|]; fr_tm
  | |- FOfree_in _ (FOle _ _) = false => apply FOfree_in_le_any; fr_tm
  | |- FOfree_in _ (FOlt470 _ _) = false => apply FOfree_in_lt470_any; fr_tm
  | |- FOfree_in _ (FOSHIFTMP _ _ _) = false => apply FOfree_in_SHIFTMP_any; fr_tm
  | |- FOfree_in _ (FOSHIFTC _ _ _ _) = false => apply FOfree_in_SHIFTC_any; fr_tm
  | |- FOfree_in _ (FOROWAG _ _ _ _ _ _) = false =>
      apply FOfree_in_ROWAG_any; [lia | avoid_tms]
  | |- FOfree_in _ (FOAGRS _ _ _ _ _ _) = false =>
      apply FOfree_in_AGRS_any; [lia | avoid_tms]
  | |- FOfree_in _ (FOSHROW _ _ _ _ _ _ _) = false =>
      apply FOfree_in_SHROW_any; [lia | avoid_tms]
  | |- FOfree_in _ (FOEq _ _) = false =>
      cbn [FOfree_in]; apply Bool.orb_false_iff; split; fr_tm
  | |- FOfree_in _ (FONeg _) = false => rewrite FOfree_in_FONeg; free_fm
  | |- FOfree_in _ (FOAnd _ _) = false =>
      rewrite FOfree_in_FOAnd; apply Bool.orb_false_iff; split; free_fm
  | |- FOfree_in _ (FOOr _ _) = false =>
      rewrite FOfree_in_FOOr; apply Bool.orb_false_iff; split; free_fm
  | |- FOfree_in _ (FOImplF _ _) = false =>
      rewrite FOfree_in_impl; apply Bool.orb_false_iff; split; free_fm
  | |- FOfree_in ?w (FOExists ?y _) = false =>
      first [ constr_eq w y; apply FOfree_in_ex_self
            | rewrite FOfree_in_FOExists_neq by lia; free_fm ]
  | |- FOfree_in ?w (FOForall ?y _) = false =>
      first [ constr_eq w y; apply FOfree_in_all_self
            | rewrite FOfree_in_all_ne by lia; free_fm ]
  | |- FOfree_in _ FOFalseF = false => reflexivity
  end.

(** ** Consequences drawn in the context of their premises. *)

Lemma FOPrH_ctxfree2 : forall n G A B C,
  FOPrH n [A; B] C -> FOPrH n G A -> FOPrH n G B -> FOPrH n G C.
Proof.
  intros n G A B C H HA HB.
  assert (H0 : FOPrH n [] (A .-> B .-> C)).
  { apply FOPrH_intro. apply FOPrH_intro. exact H. }
  apply (FOPrH_mp n G B C); [|exact HB].
  apply (FOPrH_mp n G A (B .-> C)); [|exact HA].
  apply (FOPrH_weaken n []); [intros X [] | exact H0].
Qed.

Lemma FOPrH_empty : forall n G A, FOPrH n [] A -> FOPrH n G A.
Proof. intros n G A H. apply (FOPrH_weaken n []); [intros X [] | exact H]. Qed.

Ltac ctx_list :=
  intros ? ? ?; free_ctx.

Lemma FOPrH_code_cf : forall n G v c c',
  FOPrH n G (FOle (FOSucc c) (FOSucc c')) -> FOPrH n G (FOltv v (FOSucc c)) -> v < 400 ->
  FOtms_avoid [c; c'] (S v) (S (S v)) -> FOtms_avoid [c; c'] 420 500 ->
  FOPrH n G (FOltv v (FOSucc c')).
Proof.
  intros n G v c c' H1 H2 Hv Hav1 Hav2.
  refine (FOPrH_ctxfree2 n G _ _ _ _ H1 H2).
  refine (FOPrH_mp _ _ _ _ _ (FOPrH_assum _ [_; _] _ (or_intror (or_introl eq_refl)))).
  apply FOPrH_code_tr; [apply FOPrH_assum; left; reflexivity | lia | free_ctx | ctx_list
                       | avoid_tm | avoid_tm | avoid_tm | avoid_tm].
Qed.

Lemma FOPrH_row_cf : forall n G c d c' d' j j' x v,
  FOPrH n G (FOROWAG c d c' d' j j') -> FOPrH n G (FObetaF v c d j x) ->
  2 <= v -> v + 4 <= 420 ->
  FOtms_avoid [c; d; c'; d'; j; j'; x] 420 500 ->
  FOtms_avoid [c; d; c'; d'; j; j'; x] v (v + 4) ->
  FOPrH n G (FObetaF v c' d' j' x).
Proof.
  intros n G c d c' d' j j' x v H1 H2 Hv1 Hv2 Hav1 Hav2.
  refine (FOPrH_ctxfree2 n G _ _ _ _ H1 H2).
  refine (FOPrH_mp _ _ _ _ _ (FOPrH_assum _ [_; _] _ (or_intror (or_introl eq_refl)))).
  apply FOPrH_row_beta; [apply FOPrH_assum; left; reflexivity | lia | ctx_list | ctx_list
                        | avoid_tms | avoid_tms].
Qed.

Lemma FOPrH_rebase_cf : forall n G v v' c d i x,
  v + 4 <= v' \/ v' + 4 <= v ->
  FOtms_avoid [c; d; i; x] v (v + 4) -> FOtms_avoid [c; d; i; x] v' (v' + 4) ->
  FOPrH n G (FObetaF v c d i x) -> FOPrH n G (FObetaF v' c d i x).
Proof.
  intros n G v v' c d i x Hvv Hav1 Hav2 H.
  refine (FOPrH_mp _ _ _ _ _ H). apply FOPrH_empty.
  apply FOPrH_beta_rebase; [lia | intros ? ? ? ? [] | avoid_tm | avoid_tm | avoid_tm
                           | avoid_tm | avoid_tm | avoid_tm | avoid_tm | avoid_tm].
Qed.

Lemma FOPrH_beta_le_cf : forall n G v c d i x,
  FOPrH n G (FObetaF v c d i x) -> 2 <= v -> v + 4 <= 498 ->
  FOtms_avoid [c; d; i; x] v (v + 4) -> FOtms_avoid [c; d; i; x] 498 499 ->
  FOPrH n G (FOle x c).
Proof.
  intros n G v c d i x H Hv1 Hv2 Hav1 Hav2.
  refine (FOPrH_ctxfree n G _ _ _ H).
  refine (FOPrH_mp _ _ _ _ _ (FOPrH_assum _ [_] _ (or_introl eq_refl))).
  apply FOPrH_beta_le; [ctx_list | lia | exact Hav1 | exact Hav2].
Qed.

Lemma FOPrH_le_succ_cf : forall n G a b,
  FOtms_avoid [a; b] 498 499 ->
  FOPrH n G (FOle a b) -> FOPrH n G (FOle (FOSucc a) (FOSucc b)).
Proof.
  intros n G a b Hav H.
  refine (FOPrH_ctxfree n G _ _ _ H).
  apply FOPrH_le_succ; [free_ctx | avoid_tm | avoid_tm | apply FOPrH_assum; left; reflexivity].
Qed.

Lemma FOPrH_ltv_of_le_cf : forall n G x t,
  x < 400 -> FOtms_avoid [t] 498 499 -> FOtms_avoid [t] (S x) (S (S x)) ->
  FOPrH n G (FOle (FOSucc (FOVar x)) t) -> FOPrH n G (FOltv x t).
Proof.
  intros n G x t Hx Hav1 Hav2 H.
  refine (FOPrH_ctxfree n G _ _ _ H).
  apply FOPrH_ltv_of_le; [free_ctx | lia | lia | avoid_tm | avoid_tm
                         | apply FOPrH_assum; left; reflexivity].
Qed.

Lemma FOPrH_le_of_ltv_cf : forall n G x t,
  x < 400 -> FOtms_avoid [t] 498 499 -> FOtms_avoid [t] (S x) (S (S x)) ->
  FOPrH n G (FOltv x t) -> FOPrH n G (FOle (FOSucc (FOVar x)) t).
Proof.
  intros n G x t Hx Hav1 Hav2 H.
  refine (FOPrH_ctxfree n G _ _ _ H).
  apply FOPrH_le_of_ltv; [| lia | lia | avoid_tm | avoid_tm
                         | apply FOPrH_assum; left; reflexivity].
  apply FOfree_ctx_single. unfold FOltv. apply FOfree_in_ex_self.
Qed.

Lemma FOPrH_cpair_le_cf : forall n G a b c,
  FOtms_avoid [a; b; c] 420 500 -> FOPrH n G (FOcpairF a b c) ->
  FOPrH n G (FOle a c) /\ FOPrH n G (FOle b c).
Proof.
  intros n G a b c Hav H.
  assert (C : FOctx_avoid [FOcpairF a b c] 420 500) by ctx_list.
  destruct (FOPrH_cpair_le n [FOcpairF a b c] a b c Hav C
              (FOPrH_assum n [FOcpairF a b c] (FOcpairF a b c) (or_introl eq_refl)))
    as [H1 H2].
  split; [exact (FOPrH_ctxfree n G _ _ H1 H) | exact (FOPrH_ctxfree n G _ _ H2 H)].
Qed.

Lemma FOPrH_lt470_cf : forall n G v ipos L,
  FOPrH n G (FOltv v ipos) -> FOPrH n G (FOle ipos L) -> v < 400 ->
  FOtms_avoid [ipos; L] (S v) (S (S v)) -> FOtms_avoid [ipos; L] 420 500 ->
  FOPrH n G (FOlt470 (FOVar v) L).
Proof.
  intros n G v ipos L H1 H2 Hv Hav1 Hav2.
  refine (FOPrH_ctxfree2 n G _ _ _ _ H1 H2).
  apply (FOPrH_lt_from_ltv n [FOltv v ipos; FOle ipos L] v ipos L);
                           [apply FOPrH_assum; left; reflexivity
                           | apply FOPrH_assum; right; left; reflexivity
                           | free_ctx | ctx_list | lia | avoid_tm | avoid_tm | avoid_tm
                           | avoid_tm].
Qed.

(** Strict bounds under a common summand. *)

Lemma FOPrH_le_shift : forall n G L a b,
  FOtms_avoid [L; a; b] 498 499 ->
  FOPrH n G (FOle (FOSucc a) b) -> FOPrH n G (FOle (FOSucc (FOPlus L a)) (FOPlus L b)).
Proof.
  intros n G L a b Hav H.
  refine (FOPrH_ctxfree n G _ _ _ H). unfold FOle.
  refine (FOPrH_ex_elim n _ 498 (FOEq (FOPlus (FOSucc a) (FOVar 498)) b) _
            (FOfree_ctx_single _ _ (FOfree_in_ex_self _ _)) (FOfree_in_ex_self _ _)
            (FOPrH_assum n [FOle (FOSucc a) b] (FOle (FOSucc a) b) (or_introl eq_refl)) _).
  apply FOPrH_ex_same. fo_lin [(.S .0, b, .S a .+ #498)].
Qed.

(** ** Tactics for the shifted check. *)

Ltac wk H :=
  first [ exact H
        | lazymatch goal with |- FOPrH _ (_ ++ _) _ => apply FOPrH_weak_app; wk H end ].

Ltac free_by lem :=
  lazymatch goal with
  | |- FOfree_in ?w ?X = false =>
      let E := fresh "E" in
      destruct (FOfree_in w X) eqn:E; [exfalso | reflexivity];
      apply lem in E;
      repeat match type of E with
             | _ \/ _ => destruct E as [E|E]
             end;
      first [ lia
            | match type of E with FOin_tm _ ?t = true =>
                let F := fresh in
                assert (F : FOin_tm w t = false) by fr_tm;
                rewrite F in E; discriminate E
              end ]
  end.

Lemma FOJMPREST_free : forall w B cs ds vd a b,
  FOfree_in w (FOJMPREST B cs ds vd a b) = true ->
  FOin_tm w cs = true \/ FOin_tm w ds = true \/ FOin_tm w vd = true
  \/ FOin_tm w a = true \/ FOin_tm w b = true \/ w < 2.
Proof. intros w B cs ds vd a b H. unfold FOJMPREST in H. ffree_walk; ffin. Qed.

Lemma FOPrH_CHK_intro_same : forall n G B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds i vd y,
  FOPrH n G (FOltv (B + 12) (FOSucc y)) -> FOPrH n G (FOltv (B + 14) (FOSucc y)) ->
  FOPrH n G (FOcpairF (FOVar (B + 12)) (FOVar (B + 14)) y) ->
  FOPrH n G (FOJDISJ B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd
               (FOVar (B + 12)) (FOVar (B + 14))) ->
  FOPrH n G (FOCHK B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd y).
Proof.
  intros. unfold FOCHK. apply FOPrH_bex_same; [assumption|].
  apply FOPrH_bex_same; [assumption|]. apply FOPrH_and_intro; assumption.
Qed.

(** ** A code the shift leaves unchanged. *)

Lemma FOcase_other : forall n G B cores T T' cs ds cj' dj' cs' ds' i L,
  FOTabMono n G T T' ->
  FOPrH n G (FOltv B (FOSucc cs)) ->
  FOPrH n G (FOle (FOSucc cs) (FOSucc cs')) ->
  FOPrH n G (FObetaF (B + 4) cs ds i (FOVar B)) ->
  FOPrH n G (FOROWAG cs ds cs' ds' i (FOPlus L i)) ->
  FOPrH n G (FObetaF 484 cj' dj' (FOPlus L i) (FOVar (B + 232))) ->
  FOPrH n G (FONeg (FOEq (FOVar (B + 12)) (FOnumeral 4))) ->
  FOPrH n G (FONeg (FOEq (FOVar (B + 12)) (FOnumeral 5))) ->
  FOPrH n G (FONeg (FOEq (FOVar (B + 12)) (FOnumeral 6))) ->
  FOPrH n G (FOcpairF (FOVar (B + 12)) (FOVar (B + 14)) (FOVar (B + 232))) ->
  2 <= B -> B + 240 <= 400 ->
  FOctx_avoid G (B + 16) (B + 232) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [cs; ds; cj'; dj'; cs'; ds'; i; L])
    420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [cs; ds; cj'; dj'; cs'; ds'; i; L])
    B (B + 240) ->
  FOPrH n G (FOJDISJ B cores (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) cs ds i (FOVar B) (FOVar (B + 12))
               (FOVar (B + 14)) .->
             FOJUSTCK B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T')
               (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' cj' dj' (FOPlus L i)).
Proof.
  intros n G B cores T T' cs ds cj' dj' cs' ds' i L Hm HB0 Hcs H4 HR Hy H4n H5n H6n Hcp
    HB HB2 HG HG2 Hav1 Hav2.
  apply (FOPrH_imp_trans _ _ _
           (FOJDISJ B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
              (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' (FOPlus L i) (FOVar B)
              (FOVar (B + 12)) (FOVar (B + 14)))).
  { apply FOtr_JDISJ_other; [exact Hm | exact H4n | exact H5n | exact H6n | lia
                            | exact HG | exact HG2 | avoid_tms | avoid_tms]. }
  apply FOPrH_intro.
  lazymatch goal with
  | |- FOPrH _ ?G1 _ =>
      assert (Hl : FOPrH n G1 (FOle (FOVar (B + 12)) (FOVar (B + 232))) /\
                   FOPrH n G1 (FOle (FOVar (B + 14)) (FOVar (B + 232))))
        by (apply FOPrH_cpair_le_cf; [avoid_tms | wk Hcp])
  end.
  destruct Hl as [Hl1 Hl2].
  apply (FOPrH_JUSTCK_intro n _ B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T')
           (td2 T') (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' cj' dj'
           (FOPlus L i) (FOVar (B + 232))); [lia | avoid_tms | avoid_tms | | | | |].
  - apply (FOPrH_code_cf n _ B cs cs'); [wk Hcs | wk HB0 | lia | avoid_tms | avoid_tms].
  - apply (FOPrH_row_cf n _ cs ds cs' ds' i (FOPlus L i) (FOVar B) (B + 4));
      [wk HR | wk H4 | lia | lia | avoid_tms | avoid_tms].
  - apply FOPrH_le_succ_cf; [avoid_tms|].
    apply (FOPrH_beta_le_cf n _ 484 cj' dj' (FOPlus L i) (FOVar (B + 232)));
      [wk Hy | lia | lia | avoid_tms | avoid_tms].
  - apply (FOPrH_rebase_cf n _ 484 (B + 8)); [lia | avoid_tms | avoid_tms | wk Hy].
  - apply FOPrH_CHK_intro_same; [| | wk Hcp | apply FOPrH_last].
    + apply FOPrH_ltv_of_le_cf; [lia | avoid_tms | avoid_tms|].
      apply FOPrH_le_succ_cf; [avoid_tms | exact Hl1].
    + apply FOPrH_ltv_of_le_cf; [lia | avoid_tms | avoid_tms|].
      apply FOPrH_le_succ_cf; [avoid_tms | exact Hl2].
Qed.

Ltac in_app :=
  lazymatch goal with
  | |- In _ (_ ++ _) =>
      first [ apply in_or_app; right; in_app | apply in_or_app; left; in_app ]
  | |- In _ (_ :: _) => in_list
  end.

Ltac wk_in := apply FOPrH_assum; in_app.

Ltac in_ctx := wk_in.

Ltac free_ctx ::=
  lazymatch goal with
  | |- FOfree_ctx _ (_ ++ _) => apply FOfree_ctx_app_inv; free_ctx
  | |- FOfree_ctx _ (_ :: _) => apply FOfree_ctx_cons; [free_fm | free_ctx]
  | |- FOfree_ctx _ [] => apply FOfree_ctx_nil
  | |- FOfree_ctx ?w _ =>
      first [ assumption
            | match goal with HG : FOctx_avoid _ ?lo ?hi |- _ => apply HG; lia end ]
  end.

(** ** A modus ponens code: its premise indices move up by [L]. *)

Lemma FOcase_mp : forall n G B cores T T' cs ds cj' dj' cs' ds' i L Lb,
  FOPrH n G (FOltv B (FOSucc cs)) ->
  FOPrH n G (FOle (FOSucc cs) (FOSucc cs')) ->
  FOPrH n G (FObetaF (B + 4) cs ds i (FOVar B)) ->
  FOPrH n G (FOROWAG cs ds cs' ds' i (FOPlus L i)) ->
  FOPrH n G (FObetaF 484 cj' dj' (FOPlus L i) (FOVar (B + 232))) ->
  FOPrH n G (FOEq (FOVar (B + 12)) (FOnumeral 4)) ->
  FOPrH n G (FOSHIFTMP L (FOVar (B + 14)) (FOVar (B + 232))) ->
  FOPrH n G (FOAGRS L Lb cs ds cs' ds') -> FOPrH n G (FOle i Lb) ->
  2 <= B -> B + 240 <= 400 ->
  FOctx_avoid G (B + 16) (B + 232) -> FOfree_ctx (B + 234) G -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [cs; ds; cj'; dj'; cs'; ds'; i; L; Lb])
    420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [cs; ds; cj'; dj'; cs'; ds'; i; L; Lb])
    B (B + 240) ->
  FOPrH n G (FOJDISJ B cores (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) cs ds i (FOVar B) (FOVar (B + 12))
               (FOVar (B + 14)) .->
             FOJUSTCK B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T')
               (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' cj' dj' (FOPlus L i)).
Proof.
  intros n G B cores T T' cs ds cj' dj' cs' ds' i L Lb HB0 Hcs H4 HR Hy Htg HSM HA Hle
    HB HB2 HG Hq HG2 Hav1 Hav2.
  assert (FJ : forall w, B <= w -> w < B + 240 ->
            FOfree_in w (FOJUSTCK B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T')
                           (td2 T') (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds'
                           cj' dj' (FOPlus L i)) = false)
    by (intros w Hw1 Hw2; free_by FOJUSTCK_free).
  unfold FOJDISJ.
  apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 4 0); [lia | exact Htg]|].
  apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 4 1); [lia | exact Htg]|].
  apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 4 2); [lia | exact Htg]|].
  apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 4 3); [lia | exact Htg]|].
  apply FOPrH_imp_orl.
  2:{ apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 4 5); [lia | exact Htg]|].
      apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 4 6); [lia | exact Htg]|].
      apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 4 7); [lia | exact Htg]|].
      apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 4 8); [lia | exact Htg]|].
      apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 4 9); [lia | exact Htg]
                           | apply (FOPrH_tag_and_absurd _ _ _ 4 10); [lia | exact Htg]]. }
  apply FOPrH_imp_andl. apply FOPrH_imp_weaken.
  apply FOPrH_JMP_elim; [intros w ? ?; apply HG; lia | lia | avoid_tms
                        | apply FJ; lia | apply FJ; lia |].
  replace (B + 16 + 2) with (B + 18) by lia.
  apply (FOPrH_shiftmp_elim n _ L (FOVar (B + 14)) (FOVar (B + 232)) (FOVar (B + 16))
           (FOVar (B + 18)) (B + 234));
    [wk HSM | in_ctx | ctx_list | avoid_tms | lia | lia | free_ctx | | avoid_tms |].
  { rewrite FOfree_in_impl. apply Bool.orb_false_iff. split.
    - free_by FOJMPREST_free.
    - apply FJ; lia. }
  lazymatch goal with
  | |- FOPrH _ ?G2 (FOImplF ?R _) =>
      assert (TR : FOPrH n G2 (R .-> FOJMPREST (B + 16) cs' ds' (FOVar B)
                                        (FOPlus L (FOVar (B + 16)))
                                        (FOPlus L (FOVar (B + 18)))))
  end.
  { apply (FOtr_JMPREST_sh n _ (B + 16) cs ds cs' ds' (FOVar B) (FOVar (B + 16))
             (FOVar (B + 18)) L Lb);
      [ wk HA
      | apply (FOPrH_lt470_cf n _ (B + 16) i Lb); [wk_in | wk Hle | lia | avoid_tms | avoid_tms]
      | apply (FOPrH_lt470_cf n _ (B + 18) i Lb); [wk_in | wk Hle | lia | avoid_tms | avoid_tms]
      | wk Hcs | lia | ctx_list | ctx_list | avoid_tms | avoid_tms ]. }
  apply FOPrH_intro.
  lazymatch goal with
  | |- FOPrH _ ?G3 _ =>
      assert (Hsm : FOPrH n G3
                (FOAnd (FOcpairF (FOPlus L (FOVar (B + 16))) (FOPlus L (FOVar (B + 18)))
                          (FOVar (B + 234)))
                       (FOcpairF (FOnumeral 4) (FOVar (B + 234)) (FOVar (B + 232)))))
        by wk_in;
      assert (TR3 : FOPrH n G3 (FOJMPREST (B + 16) cs' ds' (FOVar B)
                                  (FOPlus L (FOVar (B + 16))) (FOPlus L (FOVar (B + 18)))))
        by exact (FOPrH_mp _ _ _ _ (FOPrH_weak_app _ _ _ _ TR) (FOPrH_last _ _ _));
      assert (Htg3 : FOPrH n G3 (FOEq (FOVar (B + 12)) (FOnumeral 4))) by wk Htg
  end.
  pose proof (FOPrH_and_l _ _ _ _ Hsm) as Hc1.
  pose proof (FOPrH_and_r _ _ _ _ Hsm) as Hc2.
  pose proof (FOPrH_cpairF_cong _ _ _ _ _ (FOVar (B + 12)) (FOVar (B + 234)) (FOVar (B + 232))
                (FOPrH_eq_sym _ _ _ _ Htg3) (FOPrH_refl _ _ _) (FOPrH_refl _ _ _) Hc2) as Hcq.
  assert (Hl : FOtms_avoid [FOVar (B + 12); FOVar (B + 234); FOVar (B + 232)] 420 500)
    by avoid_tms.
  destruct (FOPrH_cpair_le_cf n _ _ _ _ Hl Hcq) as [Hl1 Hl2].
  apply (FOPrH_JUSTCK_intro n _ B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T')
           (td2 T') (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' cj' dj'
           (FOPlus L i) (FOVar (B + 232))); [lia | avoid_tms | avoid_tms | | | | |].
  - apply (FOPrH_code_cf n _ B cs cs'); [wk Hcs | wk HB0 | lia | avoid_tms | avoid_tms].
  - apply (FOPrH_row_cf n _ cs ds cs' ds' i (FOPlus L i) (FOVar B) (B + 4));
      [wk HR | wk H4 | lia | lia | avoid_tms | avoid_tms].
  - apply FOPrH_le_succ_cf; [avoid_tms|].
    apply (FOPrH_beta_le_cf n _ 484 cj' dj' (FOPlus L i) (FOVar (B + 232)));
      [wk Hy | lia | lia | avoid_tms | avoid_tms].
  - apply (FOPrH_rebase_cf n _ 484 (B + 8)); [lia | avoid_tms | avoid_tms | wk Hy].
  - apply (FOPrH_CHK_intro n _ B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T')
             (td2 T') (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' (FOPlus L i)
             (FOVar B) (FOVar (B + 232)) (FOVar (B + 234)));
      [lia | avoid_tms | avoid_tms | avoid_tms | | | exact Hcq |].
    + apply FOPrH_ltv_of_le_cf; [lia | avoid_tms | avoid_tms|].
      apply FOPrH_le_succ_cf; [avoid_tms | exact Hl1].
    + apply FOPrH_le_succ_cf; [avoid_tms | exact Hl2].
    + unfold FOJDISJ. do 4 apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
      apply FOPrH_and_intro; [exact Htg3|].
      apply (FOPrH_JMP_intro n _ (B + 16) cs' ds' (FOVar B) (FOVar (B + 234)) (FOPlus L i)
               (FOPlus L (FOVar (B + 16))) (FOPlus L (FOVar (B + 18))));
        [lia | avoid_tms | avoid_tms | avoid_tms | avoid_tms | | | exact Hc1 | exact TR3].
      * apply (FOPrH_le_shift n _ L (FOVar (B + 16)) i); [avoid_tms|].
        apply FOPrH_le_of_ltv_cf; [lia | avoid_tms | avoid_tms | wk_in].
      * apply (FOPrH_le_shift n _ L (FOVar (B + 18)) i); [avoid_tms|].
        apply FOPrH_le_of_ltv_cf; [lia | avoid_tms | avoid_tms | wk_in].
Qed.

(** ** Generalization and Loeb codes: the premise index moves up by
    [L]. *)

Lemma FOcase_gen : forall n G B cores T T' cs ds cj' dj' cs' ds' i L Lb,
  FOPrH n G (FOltv B (FOSucc cs)) ->
  FOPrH n G (FOle (FOSucc cs) (FOSucc cs')) ->
  FOPrH n G (FObetaF (B + 4) cs ds i (FOVar B)) ->
  FOPrH n G (FOROWAG cs ds cs' ds' i (FOPlus L i)) ->
  FOPrH n G (FObetaF 484 cj' dj' (FOPlus L i) (FOVar (B + 232))) ->
  FOPrH n G (FOEq (FOVar (B + 12)) (FOnumeral 5)) ->
  FOPrH n G (FOcpairF (FOnumeral 5) (FOPlus L (FOVar (B + 14))) (FOVar (B + 232))) ->
  FOPrH n G (FOAGRS L Lb cs ds cs' ds') -> FOPrH n G (FOle i Lb) ->
  2 <= B -> B + 240 <= 400 ->
  FOctx_avoid G (B + 16) (B + 232) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [cs; ds; cj'; dj'; cs'; ds'; i; L; Lb])
    420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [cs; ds; cj'; dj'; cs'; ds'; i; L; Lb])
    B (B + 240) ->
  FOPrH n G (FOJDISJ B cores (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) cs ds i (FOVar B) (FOVar (B + 12))
               (FOVar (B + 14)) .->
             FOJUSTCK B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T')
               (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' cj' dj' (FOPlus L i)).
Proof.
  intros n G B cores T T' cs ds cj' dj' cs' ds' i L Lb HB0 Hcs H4 HR Hy Htg Hc5 HA Hle
    HB HB2 HG HG2 Hav1 Hav2.
  assert (FJ : forall w, B <= w -> w < B + 240 ->
            FOfree_in w (FOJUSTCK B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T')
                           (td2 T') (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds'
                           cj' dj' (FOPlus L i)) = false)
    by (intros w Hw1 Hw2; free_by FOJUSTCK_free).
  unfold FOJDISJ.
  apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 5 0); [lia | exact Htg]|].
  apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 5 1); [lia | exact Htg]|].
  apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 5 2); [lia | exact Htg]|].
  apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 5 3); [lia | exact Htg]|].
  apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 5 4); [lia | exact Htg]|].
  apply FOPrH_imp_orl.
  2:{ apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 5 6); [lia | exact Htg]|].
      apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 5 7); [lia | exact Htg]|].
      apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 5 8); [lia | exact Htg]|].
      apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 5 9); [lia | exact Htg]
                           | apply (FOPrH_tag_and_absurd _ _ _ 5 10); [lia | exact Htg]]. }
  apply FOPrH_imp_andl. apply FOPrH_imp_weaken.
  apply FOPrH_JGEN_elim; [intros w ? ?; apply HG; lia | avoid_tms | apply FJ; lia |].
  lazymatch goal with
  | |- FOPrH _ ?G2 (FOImplF ?R _) =>
      assert (TR : FOPrH n G2 (R .-> FOJGENREST (B + 16) cs' ds' (FOVar B)
                                        (FOPlus L (FOVar (B + 16)))))
  end.
  { apply (FOtr_JGENREST_sh n _ (B + 16) cs ds cs' ds' (FOVar B) (FOVar (B + 16)) L Lb);
      [ wk HA
      | apply (FOPrH_lt470_cf n _ (B + 16) i Lb); [wk_in | wk Hle | lia | avoid_tms | avoid_tms]
      | wk Hcs | lia | ctx_list | ctx_list | avoid_tms | avoid_tms ]. }
  apply FOPrH_intro.
  lazymatch goal with
  | |- FOPrH _ ?G3 _ =>
      assert (TR3 : FOPrH n G3 (FOJGENREST (B + 16) cs' ds' (FOVar B)
                                  (FOPlus L (FOVar (B + 16)))))
        by exact (FOPrH_mp _ _ _ _ (FOPrH_weak_app _ _ _ _ TR) (FOPrH_last _ _ _));
      assert (Htg3 : FOPrH n G3 (FOEq (FOVar (B + 12)) (FOnumeral 5))) by wk Htg;
      assert (Hc2 : FOPrH n G3 (FOcpairF (FOnumeral 5) (FOPlus L (FOVar (B + 14)))
                                  (FOVar (B + 232)))) by wk Hc5;
      assert (Heq : FOPrH n G3 (FOEq (FOVar (B + 16)) (FOVar (B + 14)))) by wk_in
  end.
  pose proof (FOPrH_cpairF_cong _ _ _ _ _ (FOVar (B + 12)) (FOPlus L (FOVar (B + 14)))
                (FOVar (B + 232)) (FOPrH_eq_sym _ _ _ _ Htg3) (FOPrH_refl _ _ _)
                (FOPrH_refl _ _ _) Hc2) as Hcq.
  assert (Hl : FOtms_avoid [FOVar (B + 12); FOPlus L (FOVar (B + 14)); FOVar (B + 232)]
                 420 500) by avoid_tms.
  destruct (FOPrH_cpair_le_cf n _ _ _ _ Hl Hcq) as [Hl1 Hl2].
  apply (FOPrH_JUSTCK_intro n _ B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T')
           (td2 T') (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' cj' dj'
           (FOPlus L i) (FOVar (B + 232))); [lia | avoid_tms | avoid_tms | | | | |].
  - apply (FOPrH_code_cf n _ B cs cs'); [wk Hcs | wk HB0 | lia | avoid_tms | avoid_tms].
  - apply (FOPrH_row_cf n _ cs ds cs' ds' i (FOPlus L i) (FOVar B) (B + 4));
      [wk HR | wk H4 | lia | lia | avoid_tms | avoid_tms].
  - apply FOPrH_le_succ_cf; [avoid_tms|].
    apply (FOPrH_beta_le_cf n _ 484 cj' dj' (FOPlus L i) (FOVar (B + 232)));
      [wk Hy | lia | lia | avoid_tms | avoid_tms].
  - apply (FOPrH_rebase_cf n _ 484 (B + 8)); [lia | avoid_tms | avoid_tms | wk Hy].
  - apply (FOPrH_CHK_intro n _ B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T')
             (td2 T') (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' (FOPlus L i)
             (FOVar B) (FOVar (B + 232)) (FOPlus L (FOVar (B + 14))));
      [lia | avoid_tms | avoid_tms | avoid_tms | | | exact Hcq |].
    + apply FOPrH_ltv_of_le_cf; [lia | avoid_tms | avoid_tms|].
      apply FOPrH_le_succ_cf; [avoid_tms | exact Hl1].
    + apply FOPrH_le_succ_cf; [avoid_tms | exact Hl2].
    + unfold FOJDISJ. do 5 apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
      apply FOPrH_and_intro; [exact Htg3|].
      apply (FOPrH_JGEN_intro n _ (B + 16) cs' ds' (FOVar B) (FOPlus L (FOVar (B + 14)))
               (FOPlus L i) (FOPlus L (FOVar (B + 16))));
        [lia | avoid_tms | avoid_tms | avoid_tms | | | exact TR3].
      * apply (FOPrH_le_shift n _ L (FOVar (B + 16)) i); [avoid_tms|].
        apply FOPrH_le_of_ltv_cf; [lia | avoid_tms | avoid_tms | wk_in].
      * apply FOPrH_congPlus; [apply FOPrH_refl | exact Heq].
Qed.

Lemma FOcase_loeb : forall n G B cores T T' cs ds cj' dj' cs' ds' i L Lb,
  FOTabMono n G T T' ->
  FOPrH n G (FOltv B (FOSucc cs)) ->
  FOPrH n G (FOle (FOSucc cs) (FOSucc cs')) ->
  FOPrH n G (FObetaF (B + 4) cs ds i (FOVar B)) ->
  FOPrH n G (FOROWAG cs ds cs' ds' i (FOPlus L i)) ->
  FOPrH n G (FObetaF 484 cj' dj' (FOPlus L i) (FOVar (B + 232))) ->
  FOPrH n G (FOEq (FOVar (B + 12)) (FOnumeral 6)) ->
  FOPrH n G (FOcpairF (FOnumeral 6) (FOPlus L (FOVar (B + 14))) (FOVar (B + 232))) ->
  FOPrH n G (FOAGRS L Lb cs ds cs' ds') -> FOPrH n G (FOle i Lb) ->
  2 <= B -> B + 240 <= 400 ->
  FOctx_avoid G (B + 16) (B + 232) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [cs; ds; cj'; dj'; cs'; ds'; i; L; Lb])
    420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [cs; ds; cj'; dj'; cs'; ds'; i; L; Lb])
    B (B + 240) ->
  FOPrH n G (FOJDISJ B cores (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) cs ds i (FOVar B) (FOVar (B + 12))
               (FOVar (B + 14)) .->
             FOJUSTCK B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T')
               (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' cj' dj' (FOPlus L i)).
Proof.
  intros n G B cores T T' cs ds cj' dj' cs' ds' i L Lb Hm HB0 Hcs H4 HR Hy Htg Hc6 HA Hle
    HB HB2 HG HG2 Hav1 Hav2.
  assert (FJ : forall w, B <= w -> w < B + 240 ->
            FOfree_in w (FOJUSTCK B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T')
                           (td2 T') (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds'
                           cj' dj' (FOPlus L i)) = false)
    by (intros w Hw1 Hw2; free_by FOJUSTCK_free).
  unfold FOJDISJ.
  apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 6 0); [lia | exact Htg]|].
  apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 6 1); [lia | exact Htg]|].
  apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 6 2); [lia | exact Htg]|].
  apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 6 3); [lia | exact Htg]|].
  apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 6 4); [lia | exact Htg]|].
  apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 6 5); [lia | exact Htg]|].
  apply FOPrH_imp_orl.
  2:{ apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 6 7); [lia | exact Htg]|].
      apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 6 8); [lia | exact Htg]|].
      apply FOPrH_imp_orl; [apply (FOPrH_tag_and_absurd _ _ _ 6 9); [lia | exact Htg]
                           | apply (FOPrH_tag_and_absurd _ _ _ 6 10); [lia | exact Htg]]. }
  apply FOPrH_imp_andl. apply FOPrH_imp_weaken.
  apply FOPrH_JLOEB_elim; [intros w ? ?; apply HG; lia | avoid_tms | apply FJ; lia |].
  lazymatch goal with
  | |- FOPrH _ ?G2 (FOImplF ?R _) =>
      assert (TR : FOPrH n G2 (R .-> FOJLOEBREST (B + 16) (tct T') (tdt T') (tc1 T')
                                        (td1 T') (tc2 T') (td2 T') (tc3 T') (td3 T')
                                        (tcr T') (tdr T') (tlen T') cs' ds' (FOVar B)
                                        (FOPlus L (FOVar (B + 16)))))
  end.
  { apply (FOtr_JLOEBREST_sh n _ (B + 16) T T' cs ds cs' ds' (FOVar B) (FOVar (B + 16)) L Lb);
      [ apply FOTabMono_weak; exact Hm
      | wk HA
      | apply (FOPrH_lt470_cf n _ (B + 16) i Lb); [wk_in | wk Hle | lia | avoid_tms | avoid_tms]
      | wk Hcs | lia | ctx_list | ctx_list | avoid_tms | avoid_tms ]. }
  apply FOPrH_intro.
  lazymatch goal with
  | |- FOPrH _ ?G3 _ =>
      assert (TR3 : FOPrH n G3 (FOJLOEBREST (B + 16) (tct T') (tdt T') (tc1 T') (td1 T')
                                  (tc2 T') (td2 T') (tc3 T') (td3 T') (tcr T') (tdr T')
                                  (tlen T') cs' ds' (FOVar B) (FOPlus L (FOVar (B + 16)))))
        by exact (FOPrH_mp _ _ _ _ (FOPrH_weak_app _ _ _ _ TR) (FOPrH_last _ _ _));
      assert (Htg3 : FOPrH n G3 (FOEq (FOVar (B + 12)) (FOnumeral 6))) by wk Htg;
      assert (Hc2 : FOPrH n G3 (FOcpairF (FOnumeral 6) (FOPlus L (FOVar (B + 14)))
                                  (FOVar (B + 232)))) by wk Hc6;
      assert (Heq : FOPrH n G3 (FOEq (FOVar (B + 16)) (FOVar (B + 14)))) by wk_in
  end.
  pose proof (FOPrH_cpairF_cong _ _ _ _ _ (FOVar (B + 12)) (FOPlus L (FOVar (B + 14)))
                (FOVar (B + 232)) (FOPrH_eq_sym _ _ _ _ Htg3) (FOPrH_refl _ _ _)
                (FOPrH_refl _ _ _) Hc2) as Hcq.
  assert (Hl : FOtms_avoid [FOVar (B + 12); FOPlus L (FOVar (B + 14)); FOVar (B + 232)]
                 420 500) by avoid_tms.
  destruct (FOPrH_cpair_le_cf n _ _ _ _ Hl Hcq) as [Hl1 Hl2].
  apply (FOPrH_JUSTCK_intro n _ B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T')
           (td2 T') (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' cj' dj'
           (FOPlus L i) (FOVar (B + 232))); [lia | avoid_tms | avoid_tms | | | | |].
  - apply (FOPrH_code_cf n _ B cs cs'); [wk Hcs | wk HB0 | lia | avoid_tms | avoid_tms].
  - apply (FOPrH_row_cf n _ cs ds cs' ds' i (FOPlus L i) (FOVar B) (B + 4));
      [wk HR | wk H4 | lia | lia | avoid_tms | avoid_tms].
  - apply FOPrH_le_succ_cf; [avoid_tms|].
    apply (FOPrH_beta_le_cf n _ 484 cj' dj' (FOPlus L i) (FOVar (B + 232)));
      [wk Hy | lia | lia | avoid_tms | avoid_tms].
  - apply (FOPrH_rebase_cf n _ 484 (B + 8)); [lia | avoid_tms | avoid_tms | wk Hy].
  - apply (FOPrH_CHK_intro n _ B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T')
             (td2 T') (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' (FOPlus L i)
             (FOVar B) (FOVar (B + 232)) (FOPlus L (FOVar (B + 14))));
      [lia | avoid_tms | avoid_tms | avoid_tms | | | exact Hcq |].
    + apply FOPrH_ltv_of_le_cf; [lia | avoid_tms | avoid_tms|].
      apply FOPrH_le_succ_cf; [avoid_tms | exact Hl1].
    + apply FOPrH_le_succ_cf; [avoid_tms | exact Hl2].
    + unfold FOJDISJ. do 6 apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
      apply FOPrH_and_intro; [exact Htg3|].
      apply (FOPrH_JLOEB_intro n _ (B + 16) (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T')
               (td2 T') (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' (FOVar B)
               (FOPlus L (FOVar (B + 14))) (FOPlus L i) (FOPlus L (FOVar (B + 16))));
        [lia | lia | avoid_tms | avoid_tms | avoid_tms | | | exact TR3].
      * apply (FOPrH_le_shift n _ L (FOVar (B + 16)) i); [avoid_tms|].
        apply FOPrH_le_of_ltv_cf; [lia | avoid_tms | avoid_tms | wk_in].
      * apply FOPrH_congPlus; [apply FOPrH_refl | exact Heq].
Qed.

(** ** The justification check at a position of the second derivation.

    Position [i] of the second derivation is position [L + i] of the
    merged one: its formula entry is unchanged, its justification code
    is the shifted code, and its premises are read [L] positions
    later. *)

Lemma FOtr_JUSTCK_sh : forall n G B cores T T' cs ds cj dj cs' ds' cj' dj' i L Lb,
  FOTabMono n G T T' ->
  FOPrH n G (FOROWAG cs ds cs' ds' i (FOPlus L i)) ->
  FOPrH n G (FOSHROW L cj dj cj' dj' i (FOPlus L i)) ->
  FOPrH n G (FOle (FOSucc cs) (FOSucc cs')) ->
  FOPrH n G (FOAGRS L Lb cs ds cs' ds') -> FOPrH n G (FOle i Lb) ->
  2 <= B -> B + 240 <= 400 -> FOctx_avoid G B (B + 240) -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++
                 [cs; ds; cj; dj; cs'; ds'; cj'; dj'; i; L; Lb]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++
                 [cs; ds; cj; dj; cs'; ds'; cj'; dj'; i; L; Lb]) B (B + 240) ->
  FOPrH n G (FOJUSTCK B cores (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) cs ds cj dj i .->
             FOJUSTCK B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T')
               (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds' cj' dj' (FOPlus L i)).
Proof.
  intros n G B cores T T' cs ds cj dj cs' ds' cj' dj' i L Lb Hm HR HSH Hcs HA Hle
    HB HB2 HG HG2 Hav1 Hav2.
  assert (FJ : forall w, B <= w -> w < B + 240 ->
            FOfree_in w (FOJUSTCK B cores (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T')
                           (td2 T') (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') cs' ds'
                           cj' dj' (FOPlus L i)) = false)
    by (intros w Hw1 Hw2; free_by FOJUSTCK_free).
  apply FOPrH_JUSTCK_elim; [intros w ? ?; apply HG; lia | lia | avoid_tms
                           | apply FJ; lia | apply FJ; lia | apply FJ; lia | apply FJ; lia |].
  apply (FOPrH_shrow_elim n _ L cj dj cj' dj' i (FOPlus L i) (B + 8) (FOVar (B + 12))
           (FOVar (B + 14)) (FOVar (B + 2)) (B + 232));
    [ wk HSH | wk_in | wk_in | lia | ctx_list | ctx_list | avoid_tms | avoid_tms | lia | lia
    | free_ctx | | avoid_tms |].
  { rewrite FOfree_in_impl. apply Bool.orb_false_iff. split.
    - free_by FOJDISJ_free.
    - apply FJ; lia. }
  lazymatch goal with
  | |- FOPrH _ ?G2 _ =>
      assert (HSY : FOPrH n G2 (FOAnd (FObetaF 484 cj' dj' (FOPlus L i) (FOVar (B + 232)))
                                  (FOSHIFTC L (FOVar (B + 12)) (FOVar (B + 14))
                                     (FOVar (B + 232))))) by wk_in
  end.
  pose proof (FOPrH_and_l _ _ _ _ HSY) as Hy.
  apply (FOPrH_mp _ _ (FOSHIFTC L (FOVar (B + 12)) (FOVar (B + 14)) (FOVar (B + 232))));
    [| exact (FOPrH_and_r _ _ _ _ HSY)].
  unfold FOSHIFTC at 1.
  apply FOPrH_imp_orl; [|apply FOPrH_imp_orl; [|apply FOPrH_imp_orl]].
  - apply FOPrH_imp_andl. apply FOPrH_intro. apply FOPrH_intro.
    apply (FOcase_mp n _ B cores T T' cs ds cj' dj' cs' ds' i L Lb);
      [wk_in | wk Hcs | wk_in | wk HR | wk Hy | wk_in | wk_in | wk HA | wk Hle | lia | lia
      | ctx_list | free_ctx | ctx_list | avoid_tms | avoid_tms].
  - apply FOPrH_imp_andl. apply FOPrH_intro. apply FOPrH_intro.
    apply (FOcase_gen n _ B cores T T' cs ds cj' dj' cs' ds' i L Lb);
      [wk_in | wk Hcs | wk_in | wk HR | wk Hy | wk_in | wk_in | wk HA | wk Hle | lia | lia
      | ctx_list | ctx_list | avoid_tms | avoid_tms].
  - apply FOPrH_imp_andl. apply FOPrH_intro. apply FOPrH_intro.
    apply (FOcase_loeb n _ B cores T T' cs ds cj' dj' cs' ds' i L Lb);
      [apply FOTabMono_weak; apply FOTabMono_weak; apply FOTabMono_weak;
       apply FOTabMono_weak; exact Hm
      | wk_in | wk Hcs | wk_in | wk HR | wk Hy | wk_in | wk_in | wk HA | wk Hle | lia | lia
      | ctx_list | ctx_list | avoid_tms | avoid_tms].
  - apply FOPrH_imp_andl. apply FOPrH_intro.
    apply FOPrH_imp_andl. apply FOPrH_intro.
    apply FOPrH_imp_andl. apply FOPrH_intro. apply FOPrH_intro.
    apply (FOcase_other n _ B cores T T' cs ds cj' dj' cs' ds' i L);
      [ apply FOTabMono_weak; apply FOTabMono_weak; apply FOTabMono_weak;
        apply FOTabMono_weak; apply FOTabMono_weak; apply FOTabMono_weak; exact Hm
      | wk_in | wk Hcs | wk_in | wk HR | wk Hy | wk_in | wk_in | wk_in | wk_in | lia | lia
      | ctx_list | ctx_list | avoid_tms | avoid_tms].
Qed.
