From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29.
Open Scope fo_scope.

(** ** The provability matrix with the template code fixed.

    [FOPRu cores u0 c]: the matrix at target [c] with the template
    code [u0] substituted for variable [0]; for [u0] the code of the
    level template this is the provability sentence at [c]. *)

Definition FOPRu (cores : list nat) (u0 : nat) (c : FOTerm) : FOFormula :=
  FOsubst_f 0 (FOnumeral u0) (FOPRMATx cores c).

Lemma FOPrH_fix0 : forall n G u0 A,
  FOfree_ctx 0 G -> FOPrH n G A -> FOPrH n G (FOsubst_f 0 (FOnumeral u0) A).
Proof.
  intros n G u0 A HG H.
  apply (FOPrH_inst n G 0 (FOnumeral u0)); [|apply FOsubst_ok_numeral].
  apply FOPrH_all_intro; [exact HG | exact H].
Qed.

Lemma FOPrH_mpu : forall n G cores u0 a b c,
  FOctx_avoid G 0 500 ->
  FOPrH n G (FOPATF 52 [b; c] cpatImpl01 a) -> FOPrH n G (FOGUARDB c) ->
  FOtms_avoid [a; b; c] 1 500 ->
  FOPrH n G (FOPRu cores u0 a) -> FOPrH n G (FOPRu cores u0 b) ->
  FOPrH n G (FOPRu cores u0 c).
Proof.
  intros n G cores u0 a b c HG HP HB Hav Ha Hb.
  pose proof (FOPrH_D2_gen n G cores a b c ltac:(intros w ? ?; apply HG; lia) HP HB Hav) as H.
  pose proof (FOPrH_fix0 n G u0 _ ltac:(apply HG; lia) H) as H'.
  rewrite !FOsubst_f_impl in H'.
  exact (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ H' Ha) Hb).
Qed.

(** ** A strict bound separates. *)

Lemma FOPrH_le_neq : forall n G t u,
  FOPrH n G (FOle (FOSucc t) u) -> FOctx_avoid G 498 499 -> FOtms_avoid [t; u] 498 499 ->
  FOPrH n G (FONeg (FOEq t u)).
Proof.
  intros n G t u H HG Hav. unfold FONeg. apply FOPrH_intro.
  unfold FOle in H.
  refine (FOPrH_ex_elim _ _ 498 _ FOFalseF _ _ (FOPrH_weak_app _ _ _ _ H) _);
    [free_ctx | reflexivity |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (E1 : FOPrH n Gc (FOEq (FOPlus (FOSucc t) (FOVar 498)) u)) by apply FOPrH_last;
    assert (E2 : FOPrH n Gc (FOEq t u)) by wk_in
  end.
  apply (FOPrH_add_succ_absurd n _ t (FOVar 498)).
  apply (FOPrH_eq_trans _ _ _ (FOPlus (FOSucc t) (FOVar 498)) _);
    [apply FOPrH_ring; fo_ring|].
  exact (FOPrH_eq_trans _ _ _ _ _ E1 (FOPrH_eq_sym _ _ _ _ E2)).
Qed.

(** ** Every pattern code carries its guard. *)

Lemma FOPrH_guard_code : forall n G A rho env B e,
  SlotCtx n env G -> (forall z i, rho z = Some i -> i < length env) ->
  FOPrH n G (FOPATF B env (cpat_f rho A) e) ->
  1000 <= B ->
  FOctx_avoid G B (B + 2 * cpat_span (cpat_f rho A)) ->
  FOtms_avoid (e :: env) B (B + 2 * cpat_span (cpat_f rho A)) ->
  FOtms_avoid (e :: env) 2 1000 ->
  FOPrH n G (FOGUARDB e).
Proof.
  intros n G A rho env B e HS Hrho H HB HG Hav Hlo.
  pose proof HS as [HG2 Hslot].
  pose proof (FOPrH_patf_rebase _ n G B (B + cpat_span (cpat_f rho A)) env e H ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(intros w ? ?; apply HG; lia) ltac:(avoid_tms)
                ltac:(avoid_tms) ltac:(avoid_tms)) as H'.
  assert (Hlit : forall G' y, (forall Y, In Y G -> In Y G') ->
            FOPrH n G' (FOle (FOSucc (FOnumeral y)) (FOSucc e)) -> ox_eq None y = false ->
            FOPrH n G' (FONeg (FOEq (FOnumeral y) (FOSucc e)))).
  { intros G' y Hinc Hle _.
    (* the context [G'] may carry any variable: argue in the empty context *)
    refine (FOPrH_mp _ _ _ _ _ Hle). apply FOPrH_empty. apply FOPrH_intro.
    apply FOPrH_le_neq; [apply FOPrH_last | ctx_list | avoid_tms]. }
  assert (HE : RowEnv None (FOSucc e) (FOSucc e) FOZero env env 0).
  { split; [reflexivity|]. split; [exact I|]. split; [exact I|]. avoid_tms. }
  assert (HC : RowCtx n None (FOSucc e) (FOSucc e) env G).
  { split; [exact HG2|]. split; [exact Hslot | exact Hlit]. }
  pose proof (FOPrH_rows_f n None (FOSucc e) (FOSucc e) FOZero env env 0 A G rho B
                (B + cpat_span (cpat_f rho A)) e e HE HC Hrho I H H'
                (FOPrH_le_refl n G (FOSucc e) ltac:(avoid_tm)) HB ltac:(lia)
                ltac:(cbn [rho_sub]; lia)
                ltac:(intros w ? ?; apply HG; lia)
                ltac:(intros w ? ?; apply HG; cbn [rho_sub] in *; lia)
                ltac:(avoid_tms) ltac:(cbn [rho_sub]; avoid_tms) ltac:(avoid_tms)) as R.
  exact (FOPrH_guard_of_row n G e e ltac:(intros w ? ?; apply HG2; lia) ltac:(avoid_tms) R).
Qed.
