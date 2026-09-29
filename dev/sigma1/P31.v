From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30.
Open Scope fo_scope.

(** ** Freshness of the provability matrix with the template fixed. *)

Lemma FOfree_in_PRu : forall cores u0 w c,
  18 <= w -> FOtms_avoid [c] w (S w) -> FOfree_in w (FOPRu cores u0 c) = false.
Proof.
  intros cores u0 w c Hw Hav. unfold FOPRu.
  rewrite FOsubst_f_num, FOfree_in_subst_num.
  destruct (Nat.eqb w 0); [reflexivity|]. apply FOfree_in_PRMATx; [exact Hw | exact Hav].
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
      apply FOfree_in_PATF_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOGUARDB _) = false =>
      apply FOfree_in_GUARDB_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOTEXT _ _ _ _ _ _ _) = false => unfold FOTEXT; free_fm
  | |- FOfree_in _ (FOTBLNEW _ _ _ _ _ _ _) = false => unfold FOTBLNEW; free_fm
  | |- FOfree_in _ (FOINCL _ _) = false =>
      apply FOfree_in_INCL_any; [nat_fast | avoid_tms]
  | |- _ => free_fm_core
  end.

(** ** Slot contexts extended by one numeral code. *)

Lemma SlotCtx_snoc : forall n env G m w,
  SlotCtx n env G -> FOPrH n G (FONUMR w m) -> SlotCtx n (env ++ [m]) G.
Proof.
  intros n env G m w [HG Hs] Hm. split; [exact HG|]. intros i Hi.
  rewrite length_app in Hi. cbn [length] in Hi.
  destruct (Nat.lt_ge_cases i (length env)) as [Hlt|Hge].
  - rewrite app_nth1 by exact Hlt. exact (Hs i Hlt).
  - assert (Ei : i = length env) by lia. subst i.
    rewrite app_nth2 by lia. rewrite Nat.sub_diag. exists w. exact Hm.
Qed.

Lemma rho_sub_hide_self : forall x j rho z,
  rho_sub (Some x) j (rho_hide x rho) z = rho_sub (Some x) j rho z.
Proof.
  intros x j rho z. unfold rho_sub, rho_hide. destruct (Nat.eqb z x); reflexivity.
Qed.

(** ** Guard rows below an arbitrary bound. *)

Lemma FOPrH_guard_rows : forall n G A rho env B e X,
  SlotCtx n env G -> (forall z i, rho z = Some i -> i < length env) ->
  FOPrH n G (FOPATF B env (cpat_f rho A) e) ->
  FOPrH n G (FOle (FOSucc e) X) ->
  1000 <= B ->
  FOctx_avoid G B (B + 2 * cpat_span (cpat_f rho A)) ->
  FOtms_avoid (e :: X :: env) B (B + 2 * cpat_span (cpat_f rho A)) ->
  FOtms_avoid (e :: X :: env) 2 1000 ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X FOZero e e).
Proof.
  intros n G A rho env B e X HS Hrho H Hle HB HG Hav Hlo.
  pose proof HS as [HG2 Hslot].
  pose proof (FOPrH_patf_rebase _ n G B (B + cpat_span (cpat_f rho A)) env e H ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(intros w ? ?; apply HG; lia) ltac:(avoid_tms)
                ltac:(avoid_tms) ltac:(avoid_tms)) as H'.
  assert (Hlit : forall G' y, (forall Y, In Y G -> In Y G') ->
            FOPrH n G' (FOle (FOSucc (FOnumeral y)) X) -> ox_eq None y = false ->
            FOPrH n G' (FONeg (FOEq (FOnumeral y) X))).
  { intros G' y Hinc Hy _.
    refine (FOPrH_mp _ _ _ _ _ Hy). apply FOPrH_empty. apply FOPrH_intro.
    apply FOPrH_le_neq; [apply FOPrH_last | ctx_list | avoid_tms]. }
  assert (HE : RowEnv None X X FOZero env env 0).
  { split; [reflexivity|]. split; [exact I|]. split; [exact I|]. avoid_tms. }
  assert (HC : RowCtx n None X X env G).
  { split; [exact HG2|]. split; [exact Hslot | exact Hlit]. }
  exact (FOPrH_rows_f n None X X FOZero env env 0 A G rho B
           (B + cpat_span (cpat_f rho A)) e e HE HC Hrho I H H' Hle HB ltac:(lia)
           ltac:(cbn [rho_sub]; lia)
           ltac:(intros w ? ?; apply HG; lia)
           ltac:(intros w ? ?; apply HG; cbn [rho_sub] in *; lia)
           ltac:(avoid_tms) ltac:(cbn [rho_sub]; avoid_tms) ltac:(avoid_tms)).
Qed.

(** ** The small rule patterns built from pairing facts. *)

Lemma FOPrH_patf_impl01 : forall n G a b c q,
  FOPrH n G (FOcpairF (FOnumeral 2) q a) -> FOPrH n G (FOcpairF b c q) ->
  FOtms_avoid [a; b; c; q] 44 80 -> FOtms_avoid [a; b; c; q] 420 500 ->
  FOPrH n G (FOPATF 52 [b; c] cpatImpl01 a).
Proof.
  intros n G a b c q Ha Hq Hav Hav2. unfold cpatImpl01, pImpP.
  apply (FOPrH_patf_pair_intro_lo n G 52 [b; c] (CLit 2) (CPair (CVarP 0) (CVarP 1)) a
           (FOnumeral 2) q Ha (FOPrH_patf_lit _ _ _ _ _)).
  - apply (FOPrH_patf_pair_intro_lo n G 56 [b; c] (CVarP 0) (CVarP 1) q b c Hq
             (FOPrH_patf_slot _ _ _ _ 0) (FOPrH_patf_slot _ _ _ _ 1));
      [lia | vm_compute; lia | cbn [cpat_span cpat_pairs]; avoid_tms | avoid_tms].
  - lia.
  - vm_compute; lia.
  - cbn [cpat_span cpat_pairs]; avoid_tms.
  - avoid_tms.
Qed.

Lemma FOPrH_patf_allelim : forall n G x a c d q d0 p,
  FOPrH n G (FOcpairF (FOnumeral 2) q d) -> FOPrH n G (FOcpairF d0 c q) ->
  FOPrH n G (FOcpairF (FOnumeral 3) p d0) -> FOPrH n G (FOcpairF x a p) ->
  FOtms_avoid [x; a; c; d; q; d0; p] 44 80 -> FOtms_avoid [x; a; c; d; q; d0; p] 420 500 ->
  FOPrH n G (FOPATF 44 [x; a; c] cpatAllElim d).
Proof.
  intros n G x a c d q d0 p Hd Hq Hd0 Hp Hav Hav2. unfold cpatAllElim, pImpP, pAllP.
  apply (FOPrH_patf_pair_intro_lo n G 44 [x; a; c] (CLit 2)
           (CPair (CPair (CLit 3) (CPair (CVarP 0) (CVarP 1))) (CVarP 2)) d (FOnumeral 2) q Hd
           (FOPrH_patf_lit _ _ _ _ _));
    [| lia | vm_compute; lia | cbn [cpat_span cpat_pairs]; avoid_tms | avoid_tms].
  apply (FOPrH_patf_pair_intro_lo n G 48 [x; a; c] (CPair (CLit 3) (CPair (CVarP 0) (CVarP 1)))
           (CVarP 2) q d0 c Hq);
    [| exact (FOPrH_patf_slot _ _ _ _ 2) | lia | vm_compute; lia
     | cbn [cpat_span cpat_pairs]; avoid_tms | avoid_tms].
  apply (FOPrH_patf_pair_intro_lo n G 52 [x; a; c] (CLit 3) (CPair (CVarP 0) (CVarP 1)) d0
           (FOnumeral 3) p Hd0 (FOPrH_patf_lit _ _ _ _ _));
    [| lia | vm_compute; lia | cbn [cpat_span cpat_pairs]; avoid_tms | avoid_tms].
  exact (FOPrH_patf_pair_intro_lo n G 56 [x; a; c] (CVarP 0) (CVarP 1) p x a Hp
           (FOPrH_patf_slot _ _ _ _ 0) (FOPrH_patf_slot _ _ _ _ 1) ltac:(lia)
           ltac:(vm_compute; lia) ltac:(cbn [cpat_span cpat_pairs]; avoid_tms)
           ltac:(avoid_tms)).
Qed.
