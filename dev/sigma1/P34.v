From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33.
Open Scope fo_scope.

(** ** Codes of closed formulas and provability of theorems. *)

Lemma FOPrH_patf_closed_code : forall n G A B, 2 <= B ->
  FOPrH n G (FOPATF B [] (cpat_f (fun _ => None) A) (FOnumeral (FOcode_f A))).
Proof.
  intros n G A B HB. apply FOPrH_empty. apply FOPrH_true_closed.
  - apply FOs1_d0. apply FOdelta0_FOPATF; [constructor | rewrite FOmax_var_numeral; lia].
  - intros v. destruct (Nat.lt_ge_cases v B) as [Hv|Hv].
    + apply FOfree_in_PATF_lo; [exact Hv|]. apply FOtms_avoid_cons; [apply FOtm_avoid_numeral|].
      apply FOtms_avoid_nil.
    + apply FOfree_in_PATF_any; [lia|]. apply FOtms_avoid_cons; [apply FOtm_avoid_numeral|].
      apply FOtms_avoid_nil.
  - apply (proj2 (FOsat_FOPATF _ _ B [] _ ltac:(constructor)
                    ltac:(rewrite FOmax_var_numeral; lia))).
    rewrite cpat_f_closed_sem by (intros; reflexivity). rewrite FOeval_numeral. reflexivity.
Qed.

Definition FOu0 (k : nat) : nat := FOcode_f (FOPRMAT (FOPrCores k)).

Lemma FOPrH_pru_thm : forall n G k A, FOProvesTn 0 A ->
  FOPrH n G (FOPRu (FOPrCores k) (FOu0 k) (FOnumeral (FOcode_f A))).
Proof.
  intros n G k A H.
  pose proof (FOHBL3_provable k n A (FOProvesTn_cumulative 0 k A (Nat.le_0_l k) H)) as H3.
  apply FOPrH_thm. unfold FOPRu, FOu0. rewrite FOPRMATx_num, FOsubst_f_num.
  rewrite (FOsubst_num_comm (FOPRMAT (FOPrCores k)) 0 1) by lia.
  exact H3.
Qed.

(** ** Provable instances.

    [PRI V G p env]: in every extension of [G] clean above a base
    [B >= V], every code of [p] over [env] is provable.  [EnvOK]: the
    slot codes carry their numeral rows and every variable of [G] and
    [env] lies in [1000 .. V). *)

Definition Clean (G : list FOFormula) (L : list FOTerm) (lo : nat) : Prop :=
  (forall w, lo <= w -> FOfree_ctx w G) /\
  (forall t, In t L -> forall w, lo <= w -> FOin_tm w t = false).

Definition PRI (n : nat) (cores : list nat) (u0 V : nat) (G : list FOFormula) (p : CPat)
    (env : list FOTerm) : Prop :=
  forall G' B c, (forall X, In X G -> In X G') -> FOctx_avoid G' 0 1000 ->
  FOtms_avoid [c] 0 1000 -> V <= B -> Clean G' [c] B ->
  FOPrH n G' (FOPATF B env p c) -> FOPrH n G' (FOPRu cores u0 c).

Definition EnvOK (n V : nat) (G : list FOFormula) (env : list FOTerm) : Prop :=
  SlotCtx n env G /\ FOtms_avoid env 0 1000 /\ 1000 <= V /\
  (forall t, In t env -> forall w, V <= w -> FOin_tm w t = false).

Lemma SlotCtx_mono : forall n env G G',
  (forall X, In X G -> In X G') -> FOctx_avoid G' 2 1000 -> SlotCtx n env G -> SlotCtx n env G'.
Proof.
  intros n env G G' Hinc HG' [_ Hs]. split; [exact HG'|].
  intros i Hi. destruct (Hs i Hi) as [w Hw]. exists w. exact (FOPrH_weaken n G G' _ Hinc Hw).
Qed.

Lemma Clean_tms : forall G L lo a b, Clean G L lo -> lo <= a -> FOtms_avoid L a b.
Proof. intros G L lo a b [_ H] Ha t Ht w Hw1 Hw2. apply (H t Ht). lia. Qed.

Lemma Clean_ctx : forall G L lo a b, Clean G L lo -> lo <= a -> FOctx_avoid G a b.
Proof. intros G L lo a b [H _] Ha w Hw1 Hw2. apply H. lia. Qed.

Lemma env_above : forall env V a b, (forall t, In t env -> forall w, V <= w -> FOin_tm w t = false) ->
  V <= a -> FOtms_avoid env a b.
Proof. intros env V a b H Ha t Ht w Hw1 Hw2. apply (H t Ht). lia. Qed.
