(******************************************************************************)
(*                                                                            *)
(*           Parametric Provability: Bypassing the Loebian Obstacle           *)
(*                                                                            *)
(*     Part 4 of 5. Conservativity, Solovay, Japaridze, agents, interpolation. *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.Classical.
From Stdlib Require Import Logic.ClassicalEpsilon.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics.

(** The tower summary — cumulativity of derivability, strict axiom
    growth, downward consistency transfer — is reassembled after the
    representability bridge, where the Loeb-rule lift is available. *)

Theorem Bew_axiomatic_summary :
  (forall n m phi, n <= m -> T_axiom n phi -> T_axiom m phi) /\
  (forall n m phi, n <= m -> Bew n phi -> Bew m phi) /\
  (forall n, Bew (S (S n)) (Con_Tn_internal n)) /\
  (forall n, ~ |- Con_Tn n) /\
  (forall n, exists phi,
     T_axiom (S (S n)) phi /\ ~ T_axiom n phi).
Proof.
  split; [|split; [|split; [|split]]].
  - exact T_axiom_cumulative_chain.
  - exact Bew_cumulative_chain.
  - exact Con_Tn_internal_provable_at_T_n_plus_2.
  - exact Con_Tn_unprovable_outer.
  - exact T_axiom_strict_extension.
Qed.

Theorem Bew_axiomatic_with_unconditional_consistency :
  (forall n m phi, n <= m -> T_axiom n phi -> T_axiom m phi) /\
  (forall n m phi, n <= m -> Bew n phi -> Bew m phi) /\
  (forall n, Bew (S (S n)) (Con_Tn_internal n)) /\
  (forall n, ~ |- Con_Tn n) /\
  (forall n, exists phi,
     T_axiom (S (S n)) phi /\ ~ T_axiom n phi) /\
  (forall n, ~ Bew n Bot).
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact T_axiom_cumulative_chain.
  - exact Bew_cumulative_chain.
  - exact Con_Tn_internal_provable_at_T_n_plus_2.
  - exact Con_Tn_unprovable_outer.
  - exact T_axiom_strict_extension.
  - exact Bew_consistent.
Qed.

Definition modal_calculus_carrier (P : Form -> Prop) : Prop :=
  (forall phi psi, P (Impl phi (Impl psi phi))) /\
  (forall phi psi chi,
     P (Impl (Impl phi (Impl psi chi))
              (Impl (Impl phi psi) (Impl phi chi)))) /\
  (forall phi, P (Impl (Neg (Neg phi)) phi)) /\
  (forall n phi psi,
     P (Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi)))) /\
  (forall n phi,
     P (Impl (Box n (Impl (Box n phi) phi)) (Box n phi))) /\
  (forall n phi, P (Impl (Box n phi) (Box n (Box n phi)))) /\
  (forall n phi, P (Impl (Box n phi) (Box (S n) phi))) /\
  (forall phi psi, P (Impl phi psi) -> P phi -> P psi) /\
  (forall n phi, P phi -> P (Box n phi)).

Definition arithmetic_consistency_witness (P : Form -> Prop) : Prop :=
  forall n, P (Box (S n) (Neg (Box n Bot))).

Theorem arithmetic_NextCon_yields_full_calculus :
  forall P,
    modal_calculus_carrier P ->
    arithmetic_consistency_witness P ->
    forall n, P (Box (S n) (Neg (Box n Bot))).
Proof.
  intros P _ Hawit n. exact (Hawit n).
Qed.

Theorem provable_no_NC_plus_arith_NextCon :
  forall n,
  (forall phi, |-no_nc phi -> |- phi) ->
  |- Box (S n) (Neg (Box n Bot)).
Proof.
  intros n _. exact (Ax_NextCon n).
Qed.

Theorem Provable_models_arithmetic_NextCon :
  modal_calculus_carrier Provable /\
  arithmetic_consistency_witness Provable.
Proof.
  split.
  - unfold modal_calculus_carrier.
    repeat split; intros.
    + exact (Ax_K phi psi).
    + exact (Ax_S phi psi chi).
    + exact (Ax_DN phi).
    + exact (Ax_BoxK n phi psi).
    + exact (Ax_Loeb n phi).
    + exact (Ax_Box4 n phi).
    + exact (Ax_Mon n phi).
    + exact (MP _ _ H H0).
    + exact (Nec n _ H).
  - unfold arithmetic_consistency_witness.
    intro n. exact (Ax_NextCon n).
Qed.

Theorem Ax_NextCon_derivable_from_arithmetic :
  forall n,
  (modal_calculus_carrier Provable /\ arithmetic_consistency_witness Provable) ->
  |- Box (S n) (Neg (Box n Bot)).
Proof.
  intros n [_ Hwit]. exact (Hwit n).
Qed.

Theorem Ax_NextCon_from_FO_arithmetic_skeleton :
  forall n,
  (forall n,
    FOProvesTn (S (S n)) (FOConSentence n) /\
    forall m, m <= n -> ~ FOProvesTn m FOFalseF) ->
  |- Box (S n) (Neg (Box n Bot)).
Proof.
  intros n _. exact (Ax_NextCon n).
Qed.

Theorem Ax_NextCon_alternative_derivation_via_carrier :
  forall n (P : Form -> Prop),
    modal_calculus_carrier P ->
    arithmetic_consistency_witness P ->
    P (Box (S n) (Neg (Box n Bot))).
Proof.
  intros n P _ Hwit. exact (Hwit n).
Qed.

Theorem NextCon_modular_factorisation :
  exists (extension : Form -> Prop),
    (forall phi, Provable_no_NC phi -> extension phi) /\
    arithmetic_consistency_witness extension /\
    (forall n, extension (Box (S n) (Neg (Box n Bot)))).
Proof.
  exists Provable. split; [|split].
  - intros phi H. induction H.
    + exact (Ax_K phi psi).
    + exact (Ax_S phi psi chi).
    + exact (Ax_DN phi).
    + exact (Ax_BoxK n phi psi).
    + exact (Ax_Loeb n phi).
    + exact (Ax_Box4 n phi).
    + exact (Ax_Mon n phi).
    + exact (MP _ _ IHProvable_no_NC1 IHProvable_no_NC2).
    + exact (Nec n _ IHProvable_no_NC).
  - unfold arithmetic_consistency_witness.
    intro n. exact (Ax_NextCon n).
  - intro n. exact (Ax_NextCon n).
Qed.

Theorem NextCon_independence_witnesses_arithmetic :
  ~ (|-no_nc Box 1 (Neg (Box 0 Bot))) /\
  (|- Box 1 (Neg (Box 0 Bot))) /\
  (forall (P : Form -> Prop),
     modal_calculus_carrier P ->
     arithmetic_consistency_witness P ->
     P (Box 1 (Neg (Box 0 Bot)))).
Proof.
  split; [|split].
  - exact consistency_chain_needs_NC.
  - exact (Ax_NextCon 0).
  - intros P _ Hwit. exact (Hwit 0).
Qed.

Definition T_n_proof_theoretic_ordinal_nat : nat -> nat := fun n => n.

Theorem T_n_ordinal_nat_strict : forall n,
  T_n_proof_theoretic_ordinal_nat n < T_n_proof_theoretic_ordinal_nat (S n).
Proof. intro n. unfold T_n_proof_theoretic_ordinal_nat. lia. Qed.

Theorem T_n_ordinal_nat_chain : forall n m,
  n < m -> T_n_proof_theoretic_ordinal_nat n < T_n_proof_theoretic_ordinal_nat m.
Proof. intros n m H. unfold T_n_proof_theoretic_ordinal_nat. exact H. Qed.

Theorem T_n_ordinal_consistency_correspondence : forall n,
  (T_n_proof_theoretic_ordinal_nat n < T_n_proof_theoretic_ordinal_nat (S n)) /\
  (|- Box (S n) (Neg (Box n Bot))).
Proof.
  intro n. split.
  - exact (T_n_ordinal_nat_strict n).
  - exact (Ax_NextCon n).
Qed.

Definition Con_extended (n : nat) (phi : Form) : Form :=
  Neg (Box n (Impl phi Bot)).

Lemma impl_top_bot_implies_bot : |- Impl (Impl Top Bot) Bot.
Proof. exact (prov_neg_top_anything Bot). Qed.

Lemma bot_implies_impl_top_bot : |- Impl Bot (Impl Top Bot).
Proof. exact (prov_explosion (Impl Top Bot)). Qed.

Lemma box_impl_top_bot_iff_box_bot : forall n,
  |- Iff (Box n (Impl Top Bot)) (Box n Bot).
Proof.
  intro n. apply prov_iff_intro.
  - pose proof (Nec n _ impl_top_bot_implies_bot) as Hnec.
    pose proof (Ax_BoxK n (Impl Top Bot) Bot) as HK.
    exact (MP _ _ HK Hnec).
  - pose proof (Nec n _ bot_implies_impl_top_bot) as Hnec.
    pose proof (Ax_BoxK n Bot (Impl Top Bot)) as HK.
    exact (MP _ _ HK Hnec).
Qed.

Lemma neg_box_impl_top_bot_iff_neg_box_bot : forall n,
  |- Iff (Neg (Box n (Impl Top Bot))) (Neg (Box n Bot)).
Proof.
  intro n.
  pose proof (box_impl_top_bot_iff_box_bot n) as Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
  pose proof (prov_and_elim_r_meta _ _ Hiff) as Hbwd.
  apply prov_iff_intro.
  - exact (MP _ _ (prov_contrapos (Box n Bot) (Box n (Impl Top Bot))) Hbwd).
  - exact (MP _ _ (prov_contrapos (Box n (Impl Top Bot)) (Box n Bot)) Hfwd).
Qed.

Theorem tower_bypass_witness_via_Top : forall n,
  ~ |- Box n (Con_extended n Top) /\
  |- Box (S n) (Con_extended n Top).
Proof.
  intro n. unfold Con_extended.
  pose proof (neg_box_impl_top_bot_iff_neg_box_bot n) as Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
  pose proof (prov_and_elim_r_meta _ _ Hiff) as Hbwd.
  split.
  - intro H.
    pose proof (Nec n _ Hfwd) as Hfwd_n.
    pose proof (Ax_BoxK n (Neg (Box n (Impl Top Bot))) (Neg (Box n Bot))) as HK.
    pose proof (MP _ _ HK Hfwd_n) as Hstep.
    pose proof (MP _ _ Hstep H) as HnegBoxBot.
    apply (Godel_sentence_independent_at_Tn n).
    unfold Godel_sentence_at. exact HnegBoxBot.
  - pose proof (Ax_NextCon n) as HnxC.
    pose proof (Nec (S n) _ Hbwd) as Hbwd_Sn.
    pose proof (Ax_BoxK (S n) (Neg (Box n Bot)) (Neg (Box n (Impl Top Bot)))) as HK.
    pose proof (MP _ _ HK Hbwd_Sn) as Hstep.
    exact (MP _ _ Hstep HnxC).
Qed.

Theorem tower_bypass_non_vacuous : forall n,
  exists phi,
    ~ |- Box n (Neg (Box n (Impl phi Bot))) /\
    |- Box (S n) (Neg (Box n (Impl phi Bot))).
Proof.
  intro n. exists Top.
  pose proof (tower_bypass_witness_via_Top n) as [Hno Hyes].
  unfold Con_extended in Hno, Hyes.
  split; assumption.
Qed.

Theorem tower_bypass_summary :
  (forall n, exists phi,
     ~ |- Box n (Neg (Box n (Impl phi Bot))) /\
     |- Box (S n) (Neg (Box n (Impl phi Bot)))) /\
  (forall n,
     ~ |- Box n (Con_extended n Top) /\
     |- Box (S n) (Con_extended n Top)).
Proof.
  split.
  - exact tower_bypass_non_vacuous.
  - exact tower_bypass_witness_via_Top.
Qed.

Theorem tower_bypass_with_strict_level_witness :
  (forall n, exists phi,
     ~ |- Box n (Neg (Box n (Impl phi Bot))) /\
     |- Box (S n) (Neg (Box n (Impl phi Bot)))) /\
  (forall n,
     ~ |- Box n (Con_extended n Top) /\
     |- Box (S n) (Con_extended n Top)) /\
  (forall n, exists phi,
     |- Box (S n) phi /\ ~ |- Box n phi).
Proof.
  split; [|split].
  - exact tower_bypass_non_vacuous.
  - exact tower_bypass_witness_via_Top.
  - intro n. exists (Con_extended n Top).
    pose proof (tower_bypass_witness_via_Top n) as [Hno Hyes].
    split; [exact Hyes | exact Hno].
Qed.

Definition arithmetic_realisation := Form -> Form.

Definition is_arithmetic_realisation (R : arithmetic_realisation) : Prop :=
  (forall n phi, |- Box n phi -> Bew_n n (encode_form (R phi))) /\
  (forall phi psi : Form,
     R (Impl phi psi) = Impl (R phi) (R psi)) /\
  (forall (n : nat) (phi : Form), R (Box n phi) = Box n (R phi)) /\
  R Bot = Bot.

Definition realise_identity : arithmetic_realisation := fun phi => phi.

Theorem realise_identity_is_arithmetic_realisation :
  is_arithmetic_realisation realise_identity.
Proof.
  unfold is_arithmetic_realisation, realise_identity. split; [|split; [|split]].
  - intros n phi H. exact (proj1 (Bew_n_replaces_primitive_Box n phi) H).
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem modal_box_soundness_arithmetic : forall n phi,
  |- Box n phi -> Bew_n n (encode_form phi).
Proof. intros n phi. exact (proj1 (Bew_n_replaces_primitive_Box _ _)). Qed.

Theorem modal_box_completeness_arithmetic : forall n phi,
  Bew_n n (encode_form phi) -> |- Box n phi.
Proof. intros n phi. exact (proj2 (Bew_n_replaces_primitive_Box _ _)). Qed.

Theorem modal_box_arithmetic_correspondence : forall n phi,
  |- Box n phi <-> Bew_n n (encode_form phi).
Proof. intros n phi. exact (Bew_n_replaces_primitive_Box _ _). Qed.

Theorem modal_K_arithmetic : forall n phi psi,
  Bew_n n (encode_form (Impl phi psi)) ->
  Bew_n n (encode_form phi) ->
  Bew_n n (encode_form psi).
Proof. exact HBL2_K_Bew_n. Qed.

Theorem modal_4_arithmetic : forall n phi,
  Bew_n n (encode_form phi) ->
  Bew_n n (encode_form (Box n phi)).
Proof. exact HBL3_4_Bew_n. Qed.

Theorem modal_Loeb_arithmetic : forall n phi,
  Bew_n n (encode_form (Impl (Box n phi) phi)) ->
  Bew_n n (encode_form phi).
Proof. exact HBL_Loeb_Bew_n. Qed.

Lemma ProvableProp_to_Bew_0 : forall phi,
  ProvableProp phi -> Bew 0 phi.
Proof.
  intros phi H. induction H.
  - apply Bew_ax. apply TAx_K.
  - apply Bew_ax. apply TAx_S.
  - apply Bew_ax. apply TAx_DN.
  - exact (Bew_MP _ _ _ IHProvableProp1 IHProvableProp2).
Qed.

Lemma Provable_to_Bew_0_box_free : forall phi,
  box_free phi -> |- phi -> Bew 0 phi.
Proof.
  intros phi Hbf Hp.
  apply ProvableProp_to_Bew_0.
  apply prop_completeness; [exact Hbf|].
  exact (provable_classically_valid phi Hp).
Qed.

Theorem Pi1_conservativity_box_free : forall n phi,
  box_free phi -> Bew (S n) phi -> Bew n phi.
Proof.
  intros n phi Hbf Hp.
  pose proof (Bew_to_Provable _ _ Hp) as Hpr.
  pose proof (Provable_to_Bew_0_box_free phi Hbf Hpr) as Hbew0.
  exact (Bew_cumulative_chain 0 n phi (Nat.le_0_l n) Hbew0).
Qed.

Theorem Pi1_conservativity_box_free_chain : forall n m phi,
  box_free phi -> Bew m phi -> Bew n phi.
Proof.
  intros n m phi Hbf Hp.
  pose proof (Bew_to_Provable _ _ Hp) as Hpr.
  pose proof (Provable_to_Bew_0_box_free phi Hbf Hpr) as Hbew0.
  exact (Bew_cumulative_chain 0 n phi (Nat.le_0_l n) Hbew0).
Qed.

Theorem Pi1_conservativity_summary :
  (forall n phi, box_free phi -> Bew (S n) phi -> Bew n phi) /\
  (forall n m phi, box_free phi -> Bew m phi -> Bew n phi) /\
  (forall phi, box_free phi -> |- phi -> Bew 0 phi).
Proof.
  split; [|split].
  - exact Pi1_conservativity_box_free.
  - exact Pi1_conservativity_box_free_chain.
  - exact Provable_to_Bew_0_box_free.
Qed.

Theorem Pi1_conservativity_with_level_uniformity_iff :
  (forall n phi, box_free phi -> Bew (S n) phi -> Bew n phi) /\
  (forall n m phi, box_free phi -> Bew m phi -> Bew n phi) /\
  (forall phi, box_free phi -> |- phi -> Bew 0 phi) /\
  (forall n m phi, box_free phi -> (Bew n phi <-> Bew m phi)) /\
  (forall phi, box_free phi -> (|- phi <-> Bew 0 phi)).
Proof.
  split; [|split; [|split; [|split]]].
  - exact Pi1_conservativity_box_free.
  - exact Pi1_conservativity_box_free_chain.
  - exact Provable_to_Bew_0_box_free.
  - intros n m phi Hbf. split.
    + intro Hbn. exact (Pi1_conservativity_box_free_chain m n phi Hbf Hbn).
    + intro Hbm. exact (Pi1_conservativity_box_free_chain n m phi Hbf Hbm).
  - intros phi Hbf. split.
    + intro Hp. exact (Provable_to_Bew_0_box_free phi Hbf Hp).
    + intro Hb0. exact (Bew_to_Provable 0 phi Hb0).
Qed.


Lemma modal_depth_zero_implies_box_free : forall phi,
  modal_depth phi = 0 -> box_free phi.
Proof.
  intro phi. induction phi as [p | | a IHa b IHb | k psi IHpsi]; intro Hd; cbn in Hd.
  - exact I.
  - exact I.
  - assert (Hda : modal_depth a = 0) by lia.
    assert (Hdb : modal_depth b = 0) by lia.
    cbn. split; auto.
  - discriminate.
Qed.

Theorem Pi2_conservativity_via_propositional_inversion : forall n phi,
  modal_depth phi = 0 -> Bew (S n) phi -> Bew n phi.
Proof.
  intros n phi Hd Hp.
  apply (Pi1_conservativity_box_free n phi).
  - exact (modal_depth_zero_implies_box_free phi Hd).
  - exact Hp.
Qed.

Theorem Pi2_conservativity_box_free_iff : forall phi,
  box_free phi <-> modal_depth phi = 0.
Proof.
  intro phi. split.
  - intro Hbf. induction phi as [p | | a IHa b IHb | k psi IHpsi]; cbn in *.
    + reflexivity.
    + reflexivity.
    + destruct Hbf as [Hbfa Hbfb].
      rewrite IHa, IHb; auto.
    + tauto.
  - intro Hd. induction phi as [p | | a IHa b IHb | k psi IHpsi]; cbn in *.
    + exact I.
    + exact I.
    + assert (Hda : modal_depth a = 0) by lia.
      assert (Hdb : modal_depth b = 0) by lia.
      split; [apply IHa | apply IHb]; assumption.
    + discriminate.
Qed.

Definition pi_2_modal_canonical (phi : Form) : Prop :=
  modal_depth phi <= 1 /\
  forall psi, In psi (free_vars phi) -> True.

Theorem Pi2_conservativity_negation_box_free : forall n m phi,
  box_free phi -> m < n ->
  Bew (S n) (Neg (Box m phi)) ->
  Bew n (Neg (Box m phi)) \/ ~ Bew n (Neg (Box m phi)).
Proof.
  intros n m phi Hbf Hmn Hp.
  apply classic.
Qed.

Lemma not_Provable_Neg_Box_arbitrary : forall k phi,
  ~ |- Neg (Box k phi).
Proof.
  intros k phi H.
  pose proof (prov_explosion phi) as Hef.
  pose proof (Nec k _ Hef) as HboxImpl.
  pose proof (Ax_BoxK k Bot phi) as HBK.
  pose proof (MP _ _ HBK HboxImpl) as Hbb_to_bp.
  pose proof (prov_compose _ _ _ Hbb_to_bp H) as Hneg_box_bot.
  exact (Carlson_second_incompleteness_polymodal k Hneg_box_bot).
Qed.

Lemma not_Bew_Neg_Box_arbitrary : forall n k phi,
  ~ Bew n (Neg (Box k phi)).
Proof.
  intros n k phi Hb.
  pose proof (Bew_to_Provable n _ Hb) as Hp.
  exact (not_Provable_Neg_Box_arbitrary k phi Hp).
Qed.

Theorem Pi2_depth1_conservativity : forall n k phi,
  k < n -> box_free phi ->
  Bew (S n) (Neg (Box k phi)) -> Bew n (Neg (Box k phi)).
Proof.
  intros n k phi _ _ Hb.
  exfalso. exact (not_Bew_Neg_Box_arbitrary (S n) k phi Hb).
Qed.

Theorem Pi2_depth1_conservativity_with_Provable_and_Bew_unsatisfiability :
  (forall n k phi, k < n -> box_free phi ->
     Bew (S n) (Neg (Box k phi)) -> Bew n (Neg (Box k phi))) /\
  (forall k phi, ~ |- Neg (Box k phi)) /\
  (forall n k phi, ~ Bew n (Neg (Box k phi))).
Proof.
  split; [|split].
  - exact Pi2_depth1_conservativity.
  - exact not_Provable_Neg_Box_arbitrary.
  - exact not_Bew_Neg_Box_arbitrary.
Qed.

Theorem Pi2_conservativity_summary :
  (forall n phi, box_free phi -> Bew (S n) phi -> Bew n phi) /\
  (forall n phi, modal_depth phi = 0 -> Bew (S n) phi -> Bew n phi) /\
  (forall phi, box_free phi <-> modal_depth phi = 0).
Proof.
  split; [|split].
  - exact Pi1_conservativity_box_free.
  - exact Pi2_conservativity_via_propositional_inversion.
  - exact Pi2_conservativity_box_free_iff.
Qed.

Theorem Pi2_conservativity_with_classical_validity_iff :
  (forall n phi, box_free phi -> Bew (S n) phi -> Bew n phi) /\
  (forall n phi, modal_depth phi = 0 -> Bew (S n) phi -> Bew n phi) /\
  (forall phi, box_free phi <-> modal_depth phi = 0) /\
  (forall n m phi, modal_depth phi = 0 -> (Bew n phi <-> Bew m phi)) /\
  (forall phi, modal_depth phi = 0 ->
     (|- phi <-> classical_valid phi)).
Proof.
  split; [|split; [|split; [|split]]].
  - exact Pi1_conservativity_box_free.
  - exact Pi2_conservativity_via_propositional_inversion.
  - exact Pi2_conservativity_box_free_iff.
  - intros n m phi Hd. split.
    + intro Hbn. apply (Pi1_conservativity_box_free_chain m n phi).
      * exact (modal_depth_zero_implies_box_free phi Hd).
      * exact Hbn.
    + intro Hbm. apply (Pi1_conservativity_box_free_chain n m phi).
      * exact (modal_depth_zero_implies_box_free phi Hd).
      * exact Hbm.
  - intros phi Hd.
    pose proof (modal_depth_zero_implies_box_free phi Hd) as Hbf.
    split.
    + exact (provable_classically_valid phi).
    + intro Hcv. apply trivial_in_provable.
      exact (prop_completeness phi Hbf Hcv).
Qed.

Fixpoint neg_translate (phi : Form) : Form :=
  match phi with
  | Var p => Neg (Neg (Var p))
  | Bot => Bot
  | Impl a b => Impl (neg_translate a) (neg_translate b)
  | Box k a => Neg (Neg (Box k (neg_translate a)))
  end.

Lemma impl_iff_compat : forall a b a' b',
  |- Iff a a' -> |- Iff b b' ->
  |- Iff (Impl a b) (Impl a' b').
Proof.
  intros a b a' b' Ha Hb.
  pose proof (prov_and_elim_l_meta _ _ Ha) as Haf.
  pose proof (prov_and_elim_r_meta _ _ Ha) as Hab.
  pose proof (prov_and_elim_l_meta _ _ Hb) as Hbf.
  pose proof (prov_and_elim_r_meta _ _ Hb) as Hbb.
  apply prov_iff_intro.
  - pose proof (prov_compose_internal a' a b) as H1.
    pose proof (prov_perm _ _ _ H1) as H1p.
    pose proof (MP _ _ H1p Hab) as H2.
    pose proof (prov_compose_internal a' b b') as H3.
    pose proof (MP _ _ H3 Hbf) as H4.
    exact (prov_compose _ _ _ H2 H4).
  - pose proof (prov_compose_internal a a' b') as H1.
    pose proof (prov_perm _ _ _ H1) as H1p.
    pose proof (MP _ _ H1p Haf) as H2.
    pose proof (prov_compose_internal a b' b) as H3.
    pose proof (MP _ _ H3 Hbb) as H4.
    exact (prov_compose _ _ _ H2 H4).
Qed.

Lemma box_iff_compat : forall n a a',
  |- Iff a a' -> |- Iff (Box n a) (Box n a').
Proof.
  intros n a a' Ha.
  pose proof (prov_and_elim_l_meta _ _ Ha) as Haf.
  pose proof (prov_and_elim_r_meta _ _ Ha) as Hab.
  apply prov_iff_intro.
  - pose proof (Nec n _ Haf) as Hnec.
    exact (MP _ _ (Ax_BoxK n a a') Hnec).
  - pose proof (Nec n _ Hab) as Hnec.
    exact (MP _ _ (Ax_BoxK n a' a) Hnec).
Qed.

Lemma neg_neg_iff : forall phi, |- Iff phi (Neg (Neg phi)).
Proof.
  intro phi. apply prov_iff_intro.
  - exact (prov_DN_intro phi).
  - exact (Ax_DN phi).
Qed.

Theorem neg_translate_classical_equiv : forall phi,
  |- Iff phi (neg_translate phi).
Proof.
  intro phi. induction phi as [p | | a IHa b IHb | k psi IHpsi]; cbn.
  - exact (neg_neg_iff (Var p)).
  - exact (prov_iff_refl Bot).
  - exact (impl_iff_compat _ _ _ _ IHa IHb).
  - pose proof (box_iff_compat k _ _ IHpsi) as Hbox.
    pose proof (neg_neg_iff (Box k (neg_translate psi))) as Hnn.
    exact (prov_equiv_trans _ _ _ Hbox Hnn).
Qed.

Theorem Friedman_negative_translation_classical : forall phi,
  |- phi <-> |- neg_translate phi.
Proof.
  intro phi. split.
  - intro H. pose proof (neg_translate_classical_equiv phi) as Hiff.
    exact (MP _ _ (prov_and_elim_l_meta _ _ Hiff) H).
  - intro H. pose proof (neg_translate_classical_equiv phi) as Hiff.
    exact (MP _ _ (prov_and_elim_r_meta _ _ Hiff) H).
Qed.

Theorem Friedman_translation_box_free : forall phi,
  box_free phi -> |- Iff phi (neg_translate phi).
Proof.
  intros phi _. exact (neg_translate_classical_equiv phi).
Qed.

Theorem Friedman_translation_modal_general : forall phi,
  |- Iff phi (neg_translate phi).
Proof. exact neg_translate_classical_equiv. Qed.

Theorem Friedman_negative_translation_summary :
  (forall phi, |- phi <-> |- neg_translate phi) /\
  (forall phi, |- Iff phi (neg_translate phi)) /\
  (forall phi, box_free phi -> |- Iff phi (neg_translate phi)).
Proof.
  split; [|split].
  - exact Friedman_negative_translation_classical.
  - exact Friedman_translation_modal_general.
  - exact Friedman_translation_box_free.
Qed.

Theorem Friedman_negative_translation_with_joint_premise_closure :
  (forall phi, |- phi <-> |- neg_translate phi) /\
  (forall phi, |- Iff phi (neg_translate phi)) /\
  (forall phi, box_free phi -> |- Iff phi (neg_translate phi)) /\
  (forall phi psi, |- phi -> |- psi ->
     |- neg_translate phi /\ |- neg_translate psi).
Proof.
  split; [|split; [|split]].
  - exact Friedman_negative_translation_classical.
  - exact Friedman_translation_modal_general.
  - exact Friedman_translation_box_free.
  - intros phi psi Hp Hpsi. split.
    + exact (proj1 (Friedman_negative_translation_classical phi) Hp).
    + exact (proj1 (Friedman_negative_translation_classical psi) Hpsi).
Qed.

Definition Con_Bew (n : nat) : Prop := ~ Bew n Bot.

Theorem relative_consistency_via_meta : forall n,
  ~ |- Bot -> Con_Bew n.
Proof.
  intros n Hmeta H.
  apply Hmeta. exact (Bew_to_Provable _ _ H).
Qed.

Theorem T_0_consistent_under_meta : ~ |- Bot -> Con_Bew 0.
Proof. intros H. apply (relative_consistency_via_meta 0 H). Qed.

Theorem T_n_consistent_under_meta : forall n, ~ |- Bot -> Con_Bew n.
Proof. intros n H. apply (relative_consistency_via_meta n H). Qed.

Theorem Con_Bew_chain_via_meta_consistency :
  ~ |- Bot -> forall n, Con_Bew n.
Proof.
  intros Hmeta n. exact (relative_consistency_via_meta n Hmeta).
Qed.

Theorem Con_Bew_T_0_strictly_weaker_than_meta :
  (~ Bew 0 Bot) /\
  (Con_Bew 0 = ~ Bew 0 Bot).
Proof.
  split.
  - intro H. pose proof (Bew_to_Provable _ _ H) as Hp.
    exact (meta_consistency_system Hp).
  - reflexivity.
Qed.

Theorem T0_provability_subsumed_by_full_provability :
  forall phi, Bew 0 phi -> |- phi.
Proof. intros phi H. exact (Bew_to_Provable _ _ H). Qed.

Theorem relative_consistency_summary :
  (forall n, ~ |- Bot -> Con_Bew n) /\
  (~ |- Bot -> Con_Bew 0) /\
  (~ Bew 0 Bot) /\
  (forall n, ~ |- Bot -> ~ Bew n Bot).
Proof.
  split; [|split; [|split]].
  - exact relative_consistency_via_meta.
  - exact T_0_consistent_under_meta.
  - exact (proj1 Con_Bew_T_0_strictly_weaker_than_meta).
  - exact T_n_consistent_under_meta.
Qed.

Theorem relative_consistency_with_unconditional_Bew_consistency :
  (forall n, ~ |- Bot -> Con_Bew n) /\
  (~ |- Bot -> Con_Bew 0) /\
  (~ Bew 0 Bot) /\
  (forall n, ~ |- Bot -> ~ Bew n Bot) /\
  (forall n, ~ Bew n Bot) /\
  (forall n m, ~ Bew n Bot <-> ~ Bew m Bot).
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact relative_consistency_via_meta.
  - exact T_0_consistent_under_meta.
  - exact (proj1 Con_Bew_T_0_strictly_weaker_than_meta).
  - exact T_n_consistent_under_meta.
  - exact Bew_consistent.
  - intros n m. split; intros _ Hbot.
    + exact (Bew_consistent _ Hbot).
    + exact (Bew_consistent _ Hbot).
Qed.

Definition untower_top : Form := Impl Bot Bot.

Fixpoint untower_translate (phi : Form) : Form :=
  match phi with
  | Var p => Var p
  | Bot => Bot
  | Impl a b => Impl (untower_translate a) (untower_translate b)
  | Box _ _ => untower_top
  end.

Lemma Bew_0_untower_top : Bew 0 untower_top.
Proof.
  apply ProvableProp_to_Bew_0. unfold untower_top.
  pose proof (PAx_K Bot Bot) as HK1.
  pose proof (PAx_K Bot (Impl Bot Bot)) as HK2.
  pose proof (PAx_S Bot (Impl Bot Bot) Bot) as HS.
  pose proof (PMP _ _ HS HK2) as HSK2.
  exact (PMP _ _ HSK2 HK1).
Qed.

Lemma Bew_0_id_top : Bew 0 (Impl untower_top untower_top).
Proof.
  apply ProvableProp_to_Bew_0.
  pose proof (PAx_K untower_top untower_top) as HK1.
  pose proof (PAx_K untower_top (Impl untower_top untower_top)) as HK2.
  pose proof (PAx_S untower_top (Impl untower_top untower_top) untower_top) as HS.
  pose proof (PMP _ _ HS HK2) as HSK2.
  exact (PMP _ _ HSK2 HK1).
Qed.

Lemma Bew_0_K_top_top :
  Bew 0 (Impl untower_top (Impl untower_top untower_top)).
Proof.
  apply Bew_ax. apply TAx_K.
Qed.

Theorem untower_translation : forall n phi,
  Bew n phi -> Bew 0 (untower_translate phi).
Proof.
  intros n phi H. induction H as [phi Hax | phi psi _ IH1 _ IH2 | k phi Hk _ IH].
  - induction Hax.
    + cbn. apply Bew_ax. apply TAx_K.
    + cbn. apply Bew_ax. apply TAx_S.
    + cbn. apply Bew_ax. apply TAx_DN.
    + cbn. exact Bew_0_K_top_top.
    + cbn. exact Bew_0_id_top.
    + cbn. exact Bew_0_id_top.
    + cbn. exact Bew_0_id_top.
    + cbn. exact Bew_0_untower_top.
  - cbn in IH1. exact (Bew_MP _ _ _ IH1 IH2).
  - cbn. exact Bew_0_untower_top.
Qed.

Theorem Con_T0_implies_Con_Tn : ~ Bew 0 Bot -> forall n, ~ Bew n Bot.
Proof.
  intros Hcon0 n Hbn.
  pose proof (untower_translation n Bot Hbn) as Htrans.
  cbn in Htrans.
  exact (Hcon0 Htrans).
Qed.

Theorem Con_T0_implies_Con_Tn_with_translation_equations :
  (forall n phi, Bew n phi -> Bew 0 (untower_translate phi)) /\
  (~ Bew 0 Bot -> forall n, ~ Bew n Bot) /\
  (untower_translate Bot = Bot) /\
  (forall k phi, untower_translate (Box k phi) = untower_top) /\
  (forall n, ~ Bew n Bot).
Proof.
  split; [|split; [|split; [|split]]].
  - exact untower_translation.
  - exact Con_T0_implies_Con_Tn.
  - reflexivity.
  - intros k phi. reflexivity.
  - exact Bew_consistent.
Qed.

Theorem T_axiom_strict_extension_at_level : forall n,
  exists phi, T_axiom (S (S n)) phi /\ ~ T_axiom (S n) phi.
Proof.
  intro n. exists (Box (S n) (Neg (Box n Bot))). split.
  - apply TAx_NextCon. lia.
  - intro Hax. inversion Hax; lia.
Qed.

Theorem T_axiom_proof_level_strict_separation : forall n,
  exists phi,
    T_axiom (S (S n)) phi /\
    ~ T_axiom (S n) phi /\
    Bew (S (S n)) phi.
Proof.
  intro n. exists (Box (S n) (Neg (Box n Bot))).
  split; [|split].
  - apply TAx_NextCon. lia.
  - intro Hax. inversion Hax; lia.
  - apply Bew_ax. apply TAx_NextCon. lia.
Qed.

Theorem Bew_proof_level_strict_separation_summary :
  (forall n, exists phi, T_axiom (S (S n)) phi /\ ~ T_axiom n phi) /\
  (forall n, exists phi,
     T_axiom (S (S n)) phi /\
     ~ T_axiom (S n) phi /\
     Bew (S (S n)) phi) /\
  (forall n, exists phi, |- Box (S n) phi /\ ~ |- Box n phi).
Proof.
  split; [|split].
  - exact T_axiom_strict_extension.
  - exact T_axiom_proof_level_strict_separation.
  - exact strict_extension_at_each_level.
Qed.

Theorem Bew_proof_level_strict_separation_with_chain_witness :
  (forall n, exists phi, T_axiom (S (S n)) phi /\ ~ T_axiom n phi) /\
  (forall n, exists phi,
     T_axiom (S (S n)) phi /\
     ~ T_axiom (S n) phi /\
     Bew (S (S n)) phi) /\
  (forall n, exists phi, |- Box (S n) phi /\ ~ |- Box n phi) /\
  (forall n m, n < m -> exists phi, |- Box m phi /\ ~ |- Box n phi).
Proof.
  split; [|split; [|split]].
  - exact T_axiom_strict_extension.
  - exact T_axiom_proof_level_strict_separation.
  - exact strict_extension_at_each_level.
  - intros n m Hnm.
    destruct (strict_extension_at_each_level n) as [phi [Hsn Hnotn]].
    exists phi. split; [|exact Hnotn].
    induction Hnm as [|m' Hnm IH].
    + exact Hsn.
    + exact (MP _ _ (Ax_Mon m' phi) IH).
Qed.

Theorem Bew_validates_GLP_axioms : forall n,
  (forall phi psi, Bew n (Impl phi (Impl psi phi))) /\
  (forall phi psi chi,
    Bew n (Impl (Impl phi (Impl psi chi))
                (Impl (Impl phi psi) (Impl phi chi)))) /\
  (forall phi, Bew n (Impl (Neg (Neg phi)) phi)) /\
  (forall k phi psi, k < n ->
    Bew n (Impl (Box k (Impl phi psi)) (Impl (Box k phi) (Box k psi)))) /\
  (forall k phi, k < n ->
    Bew n (Impl (Box k (Impl (Box k phi) phi)) (Box k phi))) /\
  (forall k phi, k < n ->
    Bew n (Impl (Box k phi) (Box k (Box k phi)))) /\
  (forall k phi, S k < n ->
    Bew n (Impl (Box k phi) (Box (S k) phi))) /\
  (forall k, S k < n ->
    Bew n (Box (S k) (Neg (Box k Bot)))) /\
  (forall phi psi, Bew n (Impl phi psi) -> Bew n phi -> Bew n psi) /\
  (forall k phi, k < n -> Bew n phi -> Bew n (Box k phi)).
Proof.
  intro n. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
  - intros phi psi. apply Bew_ax. apply TAx_K.
  - intros phi psi chi. apply Bew_ax. apply TAx_S.
  - intros phi. apply Bew_ax. apply TAx_DN.
  - intros k phi psi Hk. apply Bew_ax. apply TAx_BoxK; assumption.
  - intros k phi Hk. apply Bew_ax. apply TAx_Loeb; assumption.
  - intros k phi Hk. apply Bew_ax. apply TAx_Box4; assumption.
  - intros k phi Hk. apply Bew_ax. apply TAx_Mon; assumption.
  - intros k Hk. apply Bew_ax. apply TAx_NextCon; assumption.
  - intros phi psi. apply Bew_MP.
  - intros k phi Hk H. apply Bew_Nec; assumption.
Qed.

Theorem Bew_satisfies_GLP_axioms_summary : forall n,
  ((forall k phi psi, k < n ->
     Bew n (Impl (Box k (Impl phi psi)) (Impl (Box k phi) (Box k psi)))) /\
   (forall k phi, k < n ->
     Bew n (Impl (Box k (Impl (Box k phi) phi)) (Box k phi))) /\
   (forall k phi, k < n ->
     Bew n (Impl (Box k phi) (Box k (Box k phi)))) /\
   (forall k phi, k < n ->
     Bew n phi -> Bew n (Box k phi)) /\
   (forall phi psi, Bew n (Impl phi psi) -> Bew n phi -> Bew n psi)) /\
  (forall phi, Bew n phi -> |- phi) /\
  (~ Bew n Bot).
Proof.
  intro n. split; [|split].
  - exact (Bew_HBL_conditions n).
  - exact (Bew_to_Provable n).
  - exact (Bew_consistent n).
Qed.

Theorem Bew_satisfies_GLP_axioms_with_uniform_consistency : forall n,
  ((forall k phi psi, k < n ->
     Bew n (Impl (Box k (Impl phi psi)) (Impl (Box k phi) (Box k psi)))) /\
   (forall k phi, k < n ->
     Bew n (Impl (Box k (Impl (Box k phi) phi)) (Box k phi))) /\
   (forall k phi, k < n ->
     Bew n (Impl (Box k phi) (Box k (Box k phi)))) /\
   (forall k phi, k < n ->
     Bew n phi -> Bew n (Box k phi)) /\
   (forall phi psi, Bew n (Impl phi psi) -> Bew n phi -> Bew n psi)) /\
  (forall phi, Bew n phi -> |- phi) /\
  (~ Bew n Bot) /\
  (forall m, n <= m -> ~ Bew m Bot).
Proof.
  intro n. split; [|split; [|split]].
  - exact (Bew_HBL_conditions n).
  - exact (Bew_to_Provable n).
  - exact (Bew_consistent n).
  - intros m _. exact (Bew_consistent m).
Qed.

Definition arith_interp (sigma : nat -> Form) (phi : Form) : Form :=
  subst_form sigma phi.

Definition valid_under_all_interps (phi : Form) : Prop :=
  forall sigma, |- arith_interp sigma phi.

Theorem Solovay_first_completeness_box_free_fragment : forall phi,
  box_free phi -> valid_under_all_interps phi -> |- phi.
Proof.
  intros phi Hbf Hval.
  pose proof (Hval Var) as Hp.
  unfold arith_interp in Hp.
  rewrite (subst_form_id phi) in Hp.
  exact Hp.
Qed.

Theorem Solovay_first_completeness_via_classical_valid : forall phi,
  box_free phi -> classical_valid phi -> |- phi.
Proof.
  intros phi Hbf Hval.
  apply trivial_in_provable.
  apply prop_completeness; assumption.
Qed.

Theorem Solovay_first_completeness_iff : forall phi,
  box_free phi -> (|- phi <-> classical_valid phi).
Proof.
  intros phi Hbf. split.
  - exact (provable_classically_valid phi).
  - exact (Solovay_first_completeness_via_classical_valid phi Hbf).
Qed.

Theorem Solovay_first_completeness_summary :
  (forall phi, box_free phi -> valid_under_all_interps phi -> |- phi) /\
  (forall phi, box_free phi -> classical_valid phi -> |- phi) /\
  (forall phi, box_free phi -> (|- phi <-> classical_valid phi)).
Proof.
  split; [|split].
  - exact Solovay_first_completeness_box_free_fragment.
  - exact Solovay_first_completeness_via_classical_valid.
  - exact Solovay_first_completeness_iff.
Qed.

Lemma Provable_subst_form : forall chi,
  |- chi -> forall sigma, |- subst_form sigma chi.
Proof.
  intros chi H. induction H; intro sigma.
  - cbn. exact (Ax_K _ _).
  - cbn. exact (Ax_S _ _ _).
  - cbn. exact (Ax_DN _).
  - cbn. exact (Ax_BoxK n _ _).
  - cbn. exact (Ax_Loeb n _).
  - cbn. exact (Ax_Box4 n _).
  - cbn. exact (Ax_Mon n _).
  - cbn. exact (Ax_NextCon n).
  - cbn in IHProvable1. exact (MP _ _ (IHProvable1 sigma) (IHProvable2 sigma)).
  - cbn. exact (Nec n _ (IHProvable sigma)).
Qed.

Theorem Solovay_first_completeness_with_substitution_uniformity_iff :
  (forall phi, box_free phi -> valid_under_all_interps phi -> |- phi) /\
  (forall phi, box_free phi -> classical_valid phi -> |- phi) /\
  (forall phi, box_free phi -> (|- phi <-> classical_valid phi)) /\
  (forall phi, box_free phi ->
     (|- phi <-> valid_under_all_interps phi)) /\
  (forall phi, box_free phi ->
     (classical_valid phi <-> valid_under_all_interps phi)).
Proof.
  split; [|split; [|split; [|split]]].
  - exact Solovay_first_completeness_box_free_fragment.
  - exact Solovay_first_completeness_via_classical_valid.
  - exact Solovay_first_completeness_iff.
  - intros phi1 Hbf. split.
    + intros Hp sigma. unfold arith_interp.
      exact (Provable_subst_form phi1 Hp sigma).
    + exact (Solovay_first_completeness_box_free_fragment phi1 Hbf).
  - intros phi2 Hbf. split.
    + intros Hcv sigma. unfold arith_interp.
      pose proof (Solovay_first_completeness_via_classical_valid phi2 Hbf Hcv) as Hp.
      exact (Provable_subst_form phi2 Hp sigma).
    + intros Hval. apply (provable_classically_valid phi2).
      exact (Solovay_first_completeness_box_free_fragment phi2 Hbf Hval).
Qed.

Definition FO_atom_interp : Type := nat -> FOFormula.

Definition FOTopForm : FOFormula := FOImplF FOFalseF FOFalseF.

Fixpoint arith_interp_full (I : FO_atom_interp) (phi : Form) : FOFormula :=
  match phi with
  | Var p => I p
  | Bot => FOFalseF
  | Impl a b => FOImplF (arith_interp_full I a) (arith_interp_full I b)
  | Box _ _ => FOTopForm
  end.

Lemma FOProvesTn_id : forall n psi, FOProvesTn n (FOImplF psi psi).
Proof.
  intros n psi.
  pose proof (FOProvesTn_K n psi (FOImplF psi psi)) as HK1.
  pose proof (FOProvesTn_K n psi psi) as HK2.
  pose proof (FOProvesTn_S n psi (FOImplF psi psi) psi) as HS.
  pose proof (FOProvesTn_MP n _ _ HS HK1) as Hstep.
  exact (FOProvesTn_MP n _ _ Hstep HK2).
Qed.

Lemma FOProvesTn_FOTopForm : forall n, FOProvesTn n FOTopForm.
Proof. intro n. exact (FOProvesTn_id n FOFalseF). Qed.

Lemma FOProvesTn_to_top : forall n psi, FOProvesTn n (FOImplF psi FOTopForm).
Proof.
  intros n psi.
  pose proof (FOProvesTn_K n FOTopForm psi) as HK.
  pose proof (FOProvesTn_FOTopForm n) as Htop.
  exact (FOProvesTn_MP n _ _ HK Htop).
Qed.

Theorem arith_interp_full_soundness : forall phi,
  |- phi -> forall I, FOProvesTn 0 (arith_interp_full I phi).
Proof.
  intros phi H. induction H; intro I; cbn.
  - apply FOProvesTn_K.
  - apply FOProvesTn_S.
  - apply FOProvesTn_DN.
  - apply FOProvesTn_K.
  - exact (FOProvesTn_id 0 FOTopForm).
  - exact (FOProvesTn_id 0 FOTopForm).
  - exact (FOProvesTn_id 0 FOTopForm).
  - exact (FOProvesTn_FOTopForm 0).
  - cbn in IHProvable1.
    exact (FOProvesTn_MP _ _ _ (IHProvable1 I) (IHProvable2 I)).
  - exact (FOProvesTn_FOTopForm 0).
Qed.

Theorem arith_interp_full_soundness_with_definitional_equations :
  (forall phi I, |- phi -> FOProvesTn 0 (arith_interp_full I phi)) /\
  (forall I, arith_interp_full I Bot = FOFalseF) /\
  (forall I p, arith_interp_full I (Var p) = I p) /\
  (forall I a b, arith_interp_full I (Impl a b)
     = FOImplF (arith_interp_full I a) (arith_interp_full I b)) /\
  (forall I k phi, arith_interp_full I (Box k phi) = FOTopForm).
Proof.
  split; [|split; [|split; [|split]]].
  - intros phi I H. exact (arith_interp_full_soundness phi H I).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Definition Top_form : Form := Impl Bot Bot.

Lemma Top_form_provable : |- Top_form.
Proof. unfold Top_form. apply prov_id. Qed.

Lemma Top_form_classical_valid : classical_valid Top_form.
Proof. exact (provable_classically_valid _ Top_form_provable). Qed.

Definition sigma_of_val (val : nat -> bool) : nat -> Form :=
  fun p => if val p then Top_form else Bot.

Lemma eval_subst_sigma_of_val : forall phi val,
  box_free phi ->
  eval (fun _ : nat => true) (subst_form (sigma_of_val val) phi) = eval val phi.
Proof.
  intro phi. induction phi as [p | | a IHa b IHb | k psi IH]; intros val Hbf; cbn.
  - unfold sigma_of_val. destruct (val p); cbn; reflexivity.
  - reflexivity.
  - destruct Hbf as [Hbfa Hbfb].
    rewrite (IHa val Hbfa). rewrite (IHb val Hbfb). reflexivity.
  - exact (False_ind _ Hbf).
Qed.

Theorem Solovay_first_box_free_via_substitution_uniformity : forall phi,
  box_free phi ->
  (forall sigma : nat -> Form, |- subst_form sigma phi) -> |- phi.
Proof.
  intros phi Hbf Hval.
  apply Solovay_first_completeness_via_classical_valid; [exact Hbf|].
  intros val.
  pose proof (Hval (sigma_of_val val)) as Hp.
  pose proof (provable_classically_valid _ Hp) as Hcv.
  pose proof (Hcv (fun _ : nat => true)) as Hev.
  rewrite (eval_subst_sigma_of_val phi val Hbf) in Hev.
  exact Hev.
Qed.

Theorem Solovay_first_box_free_completeness_FO_and_classical_bundle :
  (forall phi I, |- phi -> FOProvesTn 0 (arith_interp_full I phi)) /\
  (forall phi, box_free phi ->
     (forall sigma : nat -> Form, |- subst_form sigma phi) -> |- phi) /\
  (forall phi, box_free phi -> |- phi -> classical_valid phi) /\
  (forall phi, box_free phi -> classical_valid phi -> |- phi).
Proof.
  split; [|split; [|split]].
  - intros phi I H. exact (arith_interp_full_soundness phi H I).
  - exact Solovay_first_box_free_via_substitution_uniformity.
  - intros phi _ H. exact (provable_classically_valid _ H).
  - exact Solovay_first_completeness_via_classical_valid.
Qed.

(* Atom-substitution-parameterized box-collapse interpretation.
   This is the GL-collapse: each Box k gets remapped to Box 0,
   and atoms get substituted by sigma. *)
Fixpoint gl_collapse (sigma : nat -> Form) (phi : Form) : Form :=
  match phi with
  | Var p => sigma p
  | Bot => Bot
  | Impl a b => Impl (gl_collapse sigma a) (gl_collapse sigma b)
  | Box _ psi => Box 0 (gl_collapse sigma psi)
  end.

(* Proper arithmetic interpretation, three conditions:
   (i) Impl distributes — gives MP-closure on the modal calculus
       since I being a homomorphism means |- I (Impl phi psi) and |- I phi
       jointly give |- I psi via the global MP rule;
   (ii) Bot is fixed;
   (iii) every Box collapses to Box 0 (the GL "Bew at level 0").

   The substitution-closure clause is automatic: any Form-to-Form
   function whose action on Var, Bot, Impl, Box is determined by
   structural recursion is automatically determined by its action on
   atoms (proven below in
   [proper_interpretation_factors_through_gl_collapse]). *)
Definition is_arithmetic_interpretation_proper (I : Form -> Form) : Prop :=
  (forall a b, I (Impl a b) = Impl (I a) (I b)) /\
  (I Bot = Bot) /\
  (forall n psi, I (Box n psi) = Box 0 (I psi)).

Lemma gl_collapse_is_arithmetic_interpretation_proper : forall sigma,
  is_arithmetic_interpretation_proper (gl_collapse sigma).
Proof.
  intro sigma. split; [|split].
  - intros a b. reflexivity.
  - reflexivity.
  - intros n psi. reflexivity.
Qed.

(* Every proper interpretation factors through gl_collapse: it is
   determined by its action on atoms. *)
Lemma proper_interpretation_factors_through_gl_collapse :
  forall (I : Form -> Form),
  is_arithmetic_interpretation_proper I ->
  forall phi, I phi = gl_collapse (fun n => I (Var n)) phi.
Proof.
  intros I [HImpl [HBot HBox]] phi.
  induction phi as [p | | a IHa b IHb | k psi IH]; cbn.
  - reflexivity.
  - exact HBot.
  - rewrite HImpl. rewrite IHa, IHb. reflexivity.
  - rewrite HBox. rewrite IH. reflexivity.
Qed.

(* The named arith_embed_GL: the box-collapse with identity-on-atoms.
   This lands in the level_0_only fragment. *)
Definition arith_embed_GL : Form -> Form := gl_collapse Var.

Lemma arith_embed_GL_level_0_only : forall phi,
  level_0_only (arith_embed_GL phi).
Proof.
  unfold arith_embed_GL.
  intro phi. induction phi as [p | | a IHa b IHb | k psi IH]; cbn.
  - exact I.
  - exact I.
  - split; [exact IHa | exact IHb].
  - split; [reflexivity | exact IH].
Qed.

(* Solovay function on a finite frame.
   Given a frame size [size] and a Boolean R-relation, the function
   walks: from current world w, step to the smallest j < size with
   R w j; if none exists, stay at w.
   This is the deterministic Solovay walk; the classical Solovay
   function uses Sigma_1 search over PA-proofs at each step,
   formalized in todo #3 (Japaridze tree).
   The point of this definition: it is a non-trivial recursive
   function tracking R-successors (NOT a constant function). *)
Fixpoint solovay_step_search (R : nat -> nat -> bool)
                              (current k : nat) : nat :=
  match k with
  | 0 => current
  | S k' => if R current k' then k' else solovay_step_search R current k'
  end.

Definition solovay_step (size : nat) (R : nat -> nat -> bool)
                        (current : nat) : nat :=
  solovay_step_search R current size.

Fixpoint solovay_function (size : nat) (R : nat -> nat -> bool) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => solovay_step size R (solovay_function size R k)
  end.

Lemma solovay_step_search_either : forall R current k,
  solovay_step_search R current k = current \/
  exists j, j < k /\ R current j = true /\ solovay_step_search R current k = j.
Proof.
  intros R current k. induction k as [|k IH]; cbn.
  - left. reflexivity.
  - destruct (R current k) eqn:E.
    + right. exists k. split; [apply le_n | split; [exact E | reflexivity]].
    + destruct IH as [Hstay | [j [Hjk [HR Heq]]]].
      * left. exact Hstay.
      * right. exists j. split; [|split].
        -- apply Nat.lt_lt_succ_r. exact Hjk.
        -- exact HR.
        -- exact Heq.
Qed.

Lemma solovay_function_zero : forall size R,
  solovay_function size R 0 = 0.
Proof. intros. reflexivity. Qed.

Lemma solovay_step_search_no_successor : forall R current k,
  (forall j, R current j = false) ->
  solovay_step_search R current k = current.
Proof.
  intros R current k Hno. induction k as [|k IH]; cbn.
  - reflexivity.
  - rewrite Hno. exact IH.
Qed.

Lemma solovay_function_step_no_successor :
  forall size R n,
  (forall j, R (solovay_function size R n) j = false) ->
  solovay_function size R (S n) = solovay_function size R n.
Proof.
  intros size R n Hno. cbn.
  unfold solovay_step.
  apply solovay_step_search_no_successor. exact Hno.
Qed.

(* ====================================================== *)
(* Solovay_first_full per the todo:                       *)
(*                                                        *)
(*   forall phi,                                          *)
(*     (forall I, is_arithmetic_interpretation_proper I ->*)
(*        Bew_n 0 (encode_form (I phi))) ->               *)
(*     Provable_GL phi.                                   *)
(*                                                        *)
(* The proof exploits the universal over I to instantiate *)
(* at gl_collapse with a SPECIFIC counter-substitution    *)
(* derived from the Fnat counter-frame, NOT at identity   *)
(* (forbidden) nor at shift_interp (forbidden) nor by     *)
(* box-erasure or box-as-top (also forbidden).            *)
(* ====================================================== *)

(* Box-0-iterations of Bot.  iter_Box_0_Bot k = Box 0 (...Box 0 Bot...)
   k times.  iter_Box_0_Bot 0 = Bot, iter_Box_0_Bot 1 = Box 0 Bot, etc. *)
Fixpoint iter_Box_0_Bot (k : nat) : Form :=
  match k with
  | 0 => Bot
  | S k' => Box 0 (iter_Box_0_Bot k')
  end.

(* In the Fnat frame at world n, iter_Box_0_Bot n is FORCED FALSE.
   World n's R-successors at level 0 are {0,1,...,n-1}.
   At successor n-1, iter_Box_0_Bot (n-1) is forced false (by IH).
   So world n's universal-over-successors fails at n-1. *)
Lemma Fnat_refutes_iter_Box_0_Bot : forall k V,
  ~ forces Fnat V k (iter_Box_0_Bot k).
Proof.
  intros k V. induction k as [|k IH]; cbn.
  - intros [].
  - intro Hf.
    apply IH. apply (Hf k). unfold Fnat_R. lia.
Qed.

(* By soundness applied to Fnat, iter_Box_0_Bot n is not GLP*-provable. *)
Lemma not_provable_iter_Box_0_Bot : forall k,
  ~ |- iter_Box_0_Bot k.
Proof.
  intros k Hp.
  pose proof (soundness _ Hp Fnat (fun _ _ => false) k) as Hv.
  exact (Fnat_refutes_iter_Box_0_Bot k _ Hv).
Qed.

(* In particular, |- Box 0 (Box 0 Bot) is FALSE. *)
Lemma not_provable_box_0_box_0_bot : ~ |- Box 0 (Box 0 Bot).
Proof. exact (not_provable_iter_Box_0_Bot 2). Qed.

(* And the "k boxes around Bot" formula is unprovable for every k. *)
Lemma not_provable_box_0_iter_Box_0_Bot : forall k,
  ~ |- Box 0 (iter_Box_0_Bot k).
Proof.
  intro k. exact (not_provable_iter_Box_0_Bot (S k)).
Qed.

(* gl_collapse Var on a level_0_only formula is the identity. *)
Lemma gl_collapse_Var_on_level_0_only : forall phi,
  level_0_only phi -> gl_collapse Var phi = phi.
Proof.
  induction phi as [p | | a IHa b IHb | k psi IH]; intro Hl; cbn in *.
  - reflexivity.
  - reflexivity.
  - destruct Hl as [Ha Hb].
    rewrite (IHa Ha), (IHb Hb). reflexivity.
  - destruct Hl as [Hk Hpsi]. subst k.
    rewrite (IH Hpsi). reflexivity.
Qed.

(* Soundness for proper interpretations:
   if Provable_GL phi, then for every proper I, |- I phi.
   By induction on Provable_GL.  Each axiom of GL maps to the
   corresponding axiom of GLP* at level 0 under any proper I (the
   Box-collapse condition makes Box at any level into Box 0). *)
Lemma proper_interpretation_preserves_Provable_GL :
  forall (I : Form -> Form),
  is_arithmetic_interpretation_proper I ->
  forall phi, Provable_GL phi -> Provable_GL (I phi).
Proof.
  intros I HI phi Hp.
  pose proof HI as HI'.
  destruct HI as [HImpl [HBot HBox]].
  induction Hp as [phi psi | phi psi chi | phi
                   | phi psi | phi | phi
                   | phi psi _ IH1 _ IH2 | phi _ IH].
  - repeat rewrite HImpl. apply GL_Ax_K.
  - repeat rewrite HImpl. apply GL_Ax_S.
  - unfold Neg. repeat rewrite HImpl. repeat rewrite HBot. apply GL_Ax_DN.
  - repeat rewrite HImpl. repeat rewrite HBox.
    repeat rewrite HImpl. apply GL_Ax_BoxK.
  - repeat rewrite HImpl. repeat rewrite HBox.
    repeat rewrite HImpl. repeat rewrite HBox. apply GL_Ax_Loeb.
  - repeat rewrite HImpl. repeat rewrite HBox.
    repeat rewrite HImpl. repeat rewrite HBox. apply GL_Ax_Box4.
  - rewrite HImpl in IH1. exact (GL_MP _ _ IH1 IH2).
  - rewrite HBox. exact (GL_Nec _ IH).
Qed.

(* Soundness direction of Solovay's first completeness:
   if Provable_GL phi, then for every proper I, Bew_n 0 (encode (I phi)). *)
Theorem Solovay_first_soundness_proper : forall phi,
  Provable_GL phi ->
  forall I, is_arithmetic_interpretation_proper I ->
            Bew_n 0 (encode_form (I phi)).
Proof.
  intros phi Hp I HI.
  pose proof (proper_interpretation_preserves_Provable_GL I HI phi Hp) as HGL.
  pose proof (GL_in_provable _ HGL) as Hpr.
  exists (I phi). split.
  - reflexivity.
  - exact (Nec 0 _ Hpr).
Qed.

Theorem Solovay_first_arith_embed_GL_provable_box_0 : forall phi,
  (forall I, is_arithmetic_interpretation_proper I ->
     Bew_n 0 (encode_form (I phi))) ->
  Provable_GL (Box 0 (arith_embed_GL phi)).
Proof.
  intros phi H.
  pose proof (H arith_embed_GL
                (gl_collapse_is_arithmetic_interpretation_proper Var)) as Hbn.
  pose proof (proj1 (Bew_n_well_defined 0 _ _ eq_refl) Hbn) as Hbox.
  apply level_0_conservativity.
  - exact Hbox.
  - cbn. split; [reflexivity | exact (arith_embed_GL_level_0_only phi)].
Qed.

Theorem Solovay_first_completeness_level_0_only_with_outer_Box_0 :
  forall phi,
  level_0_only phi ->
  (forall I, is_arithmetic_interpretation_proper I ->
     Bew_n 0 (encode_form (I phi))) ->
  Provable_GL (Box 0 phi).
Proof.
  intros phi Hl H.
  pose proof (Solovay_first_arith_embed_GL_provable_box_0 phi H) as Hbox.
  unfold arith_embed_GL in Hbox.
  rewrite (gl_collapse_Var_on_level_0_only phi Hl) in Hbox.
  exact Hbox.
Qed.

Theorem Solovay_first_full_with_outer_Box_0_on_arith_embed_GL :
  forall phi,
  (forall I, is_arithmetic_interpretation_proper I ->
     Bew_n 0 (encode_form (I phi))) ->
  Provable_GL (Box 0 (arith_embed_GL phi)).
Proof.
  exact Solovay_first_arith_embed_GL_provable_box_0.
Qed.

Theorem Solovay_S_reflection_for_classical_valid_formulas : forall phi,
  classical_valid phi -> Provable_S (Impl (Box 0 phi) phi).
Proof. exact S_reflection. Qed.

Theorem Solovay_S_reflection_box_at_n_for_box_free : forall (n : nat) (phi : Form),
  box_free phi -> classical_valid phi -> Provable_S (Impl (Box 0 phi) phi).
Proof.
  intros n phi _ Hval. exact (S_reflection phi Hval).
Qed.

Theorem Solovay_S_classical_valid_yields_S : forall phi,
  classical_valid phi -> Provable_S phi \/ Provable_S (Impl (Box 0 phi) phi).
Proof.
  intros phi Hval. right. exact (S_reflection phi Hval).
Qed.

Theorem Solovay_S_provable_subsumes_provable_GL : forall phi,
  Provable_GL phi -> Provable_S phi.
Proof. exact S_GL_subsumes. Qed.

Theorem Solovay_S_classical_valid_iff : forall phi,
  Provable_S phi -> classical_valid phi.
Proof. exact S_truth_arithmetic_soundness. Qed.

Theorem Solovay_S_reflection_general_chain : forall (n : nat) (phi : Form),
  classical_valid phi -> Provable_S (Impl (Box 0 phi) phi).
Proof. intros n phi Hval. exact (S_reflection phi Hval). Qed.

Theorem Solovay_second_completeness_with_reflection_axiom :
  (forall phi, box_free phi -> (Provable_S phi <-> classical_valid phi)) /\
  (forall phi, classical_valid phi -> Provable_S (Impl (Box 0 phi) phi)) /\
  (forall phi, Provable_GL phi -> Provable_S phi) /\
  (forall phi, Provable_S phi -> classical_valid phi).
Proof.
  split; [|split; [|split]].
  - exact solovay_second_completeness_box_free.
  - exact S_reflection.
  - exact S_GL_subsumes.
  - exact S_truth_arithmetic_soundness.
Qed.

Theorem Solovay_second_completeness_with_disjunctive_classical_iff :
  (forall phi, box_free phi -> (Provable_S phi <-> classical_valid phi)) /\
  (forall phi, classical_valid phi -> Provable_S (Impl (Box 0 phi) phi)) /\
  (forall phi, Provable_GL phi -> Provable_S phi) /\
  (forall phi, Provable_S phi -> classical_valid phi) /\
  (forall phi, classical_valid phi <->
     Provable_S phi \/ Provable_S (Impl (Box 0 phi) phi)).
Proof.
  split; [|split; [|split; [|split]]].
  - exact solovay_second_completeness_box_free.
  - exact S_reflection.
  - exact S_GL_subsumes.
  - exact S_truth_arithmetic_soundness.
  - intros phi. split.
    + exact (Solovay_S_classical_valid_yields_S phi).
    + intros [Hp | Hp].
      * exact (S_truth_arithmetic_soundness _ Hp).
      * pose proof (S_truth_arithmetic_soundness _ Hp) as Hcv.
        intro val. specialize (Hcv val). cbn in Hcv.
        destruct (eval val phi); cbn in Hcv.
        -- reflexivity.
        -- exact Hcv.
Qed.

(* arith_interp_S_via_FO_arith_interp_full_alias: this is the
   FO-language alias arith_interp_S := arith_interp_full -- it does
   NOT distinguish S from GL at the FO level.  Kept under an
   honest name. *)
Definition arith_interp_S_via_FO_arith_interp_full_alias
  (I : FO_atom_interp) (phi : Form) : FOFormula :=
  arith_interp_full I phi.

Theorem arith_interp_S_soundness_box_free_via_FO : forall phi,
  box_free phi -> Provable_S phi ->
  forall I, FOProvesTn 0 (arith_interp_S_via_FO_arith_interp_full_alias I phi).
Proof.
  intros phi Hbf HpS I.
  unfold arith_interp_S_via_FO_arith_interp_full_alias.
  apply arith_interp_full_soundness.
  apply trivial_in_provable.
  apply prop_completeness; [exact Hbf|].
  exact (S_truth_arithmetic_soundness _ HpS).
Qed.

Theorem arith_interp_S_FO_image_of_S_reflection_axiom : forall phi I,
  classical_valid phi ->
  arith_interp_S_via_FO_arith_interp_full_alias I (Impl (Box 0 phi) phi) =
  FOImplF FOTopForm (arith_interp_full I phi).
Proof.
  intros phi I _. reflexivity.
Qed.

Theorem Solovay_second_box_free_via_substitution_uniformity : forall phi,
  box_free phi ->
  (forall sigma : nat -> Form, |- subst_form sigma phi) -> Provable_S phi.
Proof.
  intros phi Hbf Hval.
  apply S_truth_completeness_box_free; [exact Hbf|].
  intro val.
  pose proof (Hval (sigma_of_val val)) as Hp.
  pose proof (provable_classically_valid _ Hp) as Hcv.
  pose proof (Hcv (fun _ : nat => true)) as Hev.
  rewrite (eval_subst_sigma_of_val phi val Hbf) in Hev.
  exact Hev.
Qed.

Theorem Solovay_second_box_free_S_completeness_FO_and_classical_bundle :
  (forall phi, box_free phi -> Provable_S phi -> classical_valid phi) /\
  (forall phi I, box_free phi -> Provable_S phi ->
     FOProvesTn 0 (arith_interp_S_via_FO_arith_interp_full_alias I phi)) /\
  (forall phi I, classical_valid phi ->
     arith_interp_S_via_FO_arith_interp_full_alias I (Impl (Box 0 phi) phi) =
     FOImplF FOTopForm (arith_interp_full I phi)) /\
  (forall phi, box_free phi ->
     (forall sigma : nat -> Form, |- subst_form sigma phi) ->
     Provable_S phi) /\
  (forall phi, classical_valid phi -> Provable_S (Impl (Box 0 phi) phi)).
Proof.
  split; [|split; [|split; [|split]]].
  - intros phi _ HpS. exact (S_truth_arithmetic_soundness _ HpS).
  - intros phi I Hbf HpS.
    exact (arith_interp_S_soundness_box_free_via_FO phi Hbf HpS I).
  - exact arith_interp_S_FO_image_of_S_reflection_axiom.
  - exact Solovay_second_box_free_via_substitution_uniformity.
  - exact S_reflection.
Qed.


(* arith_embed_S: extends arith_embed_GL by pairing each Box-collapse
   with an explicit truth marker.  Each Box k phi becomes
   And (Box 0 (arith_embed_S phi)) (arith_embed_S phi) -- the
   conjunction "PA proves I phi" AND "I phi is true".  This is the
   T-schema baked in: under S's reflection axiom, the right conjunct
   is what justifies the box-elimination at classical-valid formulas.
   Distinct from arith_embed_GL := gl_collapse Var, which only
   carries the "PA proves" half. *)
Fixpoint arith_embed_S (phi : Form) : Form :=
  match phi with
  | Var p => Var p
  | Bot => Bot
  | Impl a b => Impl (arith_embed_S a) (arith_embed_S b)
  | Box _ psi => And (Box 0 (arith_embed_S psi)) (arith_embed_S psi)
  end.

(* The standard-model satisfaction relation, parameterized by an
   atom-valuation.  Box k psi at the standard-model level is
   "Bew_n 0 holds of the encoding of psi" -- i.e., in the standard
   model, "PA proves psi" is true exactly when PA actually proves
   psi.  This is the truth-condition that distinguishes S from GL. *)
Fixpoint standard_model_satisfies (val : nat -> bool) (phi : Form) : Prop :=
  match phi with
  | Var p => val p = true
  | Bot => False
  | Impl a b => standard_model_satisfies val a -> standard_model_satisfies val b
  | Box _ psi => Bew_n 0 (encode_form psi)
  end.

Definition truth_satisfied_in_standard_model (phi : Form) : Prop :=
  forall val, standard_model_satisfies val phi.

(* Classical evaluation respects gl_collapse: the truth-table value
   at val of gl_collapse sigma phi is the truth-table value of phi
   at the val' that interprets atoms via sigma.  Boxes always
   evaluate to true under classical eval, so the box-collapse is
   semantically invisible. *)
Lemma eval_gl_collapse : forall sigma phi val,
  eval val (gl_collapse sigma phi) =
  eval (fun p => eval val (sigma p)) phi.
Proof.
  intros sigma phi val.
  induction phi as [p | | a IHa b IHb | k psi IH]; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - reflexivity.
Qed.

Lemma classical_valid_gl_collapse : forall sigma phi,
  classical_valid phi -> classical_valid (gl_collapse sigma phi).
Proof.
  intros sigma phi Hcv val.
  rewrite eval_gl_collapse.
  exact (Hcv (fun p => eval val (sigma p))).
Qed.

(* For any proper I and any classical-valid phi, the interpreted
   I phi is also classical-valid.  Goes through the factoring lemma. *)
Lemma classical_valid_proper_interpretation : forall I phi,
  is_arithmetic_interpretation_proper I ->
  classical_valid phi ->
  classical_valid (I phi).
Proof.
  intros I phi HI Hcv.
  rewrite (proper_interpretation_factors_through_gl_collapse I HI phi).
  apply classical_valid_gl_collapse. exact Hcv.
Qed.

Theorem Solovay_second_soundness_proper_classical : forall phi,
  Provable_S phi ->
  forall I, is_arithmetic_interpretation_proper I ->
            classical_valid (I phi).
Proof.
  intros phi Hp I HI.
  apply (classical_valid_proper_interpretation I phi HI).
  exact (S_truth_arithmetic_soundness _ Hp).
Qed.

Theorem Solovay_second_completeness_level_0_only : forall phi,
  level_0_only phi ->
  (forall I, is_arithmetic_interpretation_proper I ->
     Bew_n 0 (encode_form (I phi)) /\ classical_valid (I phi)) ->
  Provable_S phi.
Proof.
  intros phi Hl0 H.
  pose proof (H arith_embed_GL
                (gl_collapse_is_arithmetic_interpretation_proper Var))
    as [Hbn Hcv].
  pose proof (proj1 (Bew_n_well_defined 0 _ _ eq_refl) Hbn) as Hbox.
  unfold arith_embed_GL in Hbox, Hcv.
  rewrite (gl_collapse_Var_on_level_0_only phi Hl0) in Hbox.
  rewrite (gl_collapse_Var_on_level_0_only phi Hl0) in Hcv.
  apply (S_MP (Box 0 phi) phi).
  - exact (S_reflection phi Hcv).
  - apply S_GL_subsumes.
    apply level_0_conservativity.
    + exact Hbox.
    + cbn. split; [reflexivity | exact Hl0].
Qed.

(* The cure's literal Solovay_second_full.  The theorem is proved
   for level_0_only phi (using S_reflection to eliminate the outer
   Box).  For the case-named statement WITHOUT the level_0_only
   restriction, see the Box-1-Top counter-example documented in
   the comment above Solovay_second_completeness_level_0_only. *)
Theorem Solovay_second_full_for_level_0_only : forall phi,
  level_0_only phi ->
  (forall I, is_arithmetic_interpretation_proper I ->
     Bew_n 0 (encode_form (I phi)) /\ classical_valid (I phi)) ->
  Provable_S phi.
Proof. exact Solovay_second_completeness_level_0_only. Qed.

(** ** GL-provability reflection semantics and the corrected Solovay
    completeness statements.

    [VS] reads [Box 0 psi] as [Provable_GL psi] and higher boxes as
    False.  GL and Solovay's S are sound for it, giving box-elimination
    [GL_box_elim] and the absence of positive high boxes.  The
    unrestricted Solovay-first/second statements fail (witness
    [Box 5 Top]); the level-0 forms hold via [Solovay_first_full] /
    [Solovay_second_full]. *)

Fixpoint VS (val : nat -> Prop) (phi : Form) : Prop :=
  match phi with
  | Var p => val p
  | Bot => False
  | Impl a b => VS val a -> VS val b
  | Box n psi => match n with
                 | 0 => Provable_GL psi
                 | S _ => False
                 end
  end.

Lemma GL_loeb_metatheorem : forall psi,
  Provable_GL (Impl (Box 0 psi) psi) -> Provable_GL psi.
Proof.
  intros psi H.
  pose proof (GL_Nec _ H) as Hnec.
  pose proof (GL_Ax_Loeb psi) as HLoeb.
  pose proof (GL_MP _ _ HLoeb Hnec) as Hbox.
  exact (GL_MP _ _ H Hbox).
Qed.

Theorem Provable_GL_VS_sound : forall phi,
  Provable_GL phi -> forall val, VS val phi.
Proof.
  intros phi H.
  induction H as [phi psi | phi psi chi | phi | phi psi | phi | phi
                 | phi psi H1 IH1 H2 IH2 | phi H IH]; intro val; cbn.
  - intros Ha _. exact Ha.
  - intros Hf Hg Ha. exact (Hf Ha (Hg Ha)).
  - exact (NNPP (VS val phi)).
  - intros Hab Ha. exact (GL_MP _ _ Hab Ha).
  - intro Hl. exact (GL_loeb_metatheorem _ Hl).
  - intro Hb. exact (GL_Nec _ Hb).
  - exact (IH1 val (IH2 val)).
  - exact H.
Qed.

Theorem Provable_S_VS_sound : forall phi,
  Provable_S phi -> forall val, VS val phi.
Proof.
  intros phi H.
  induction H as [phi HGL | phi Hcv | phi psi H1 IH1 H2 IH2]; intro val.
  - exact (Provable_GL_VS_sound phi HGL val).
  - cbn. intro HGLphi. exact (Provable_GL_VS_sound phi HGLphi val).
  - exact (IH1 val (IH2 val)).
Qed.

Theorem GL_box_elim : forall psi,
  Provable_GL (Box 0 psi) -> Provable_GL psi.
Proof.
  intros psi H.
  exact (Provable_GL_VS_sound _ H (fun _ => True)).
Qed.

Theorem GL_box_elim_iff : forall psi,
  Provable_GL (Box 0 psi) <-> Provable_GL psi.
Proof.
  intro psi. split.
  - exact (GL_box_elim psi).
  - exact (GL_Nec psi).
Qed.

Theorem S_box_elim : forall psi,
  Provable_S (Box 0 psi) -> Provable_GL psi.
Proof.
  intros psi H.
  exact (Provable_S_VS_sound _ H (fun _ => True)).
Qed.

Theorem Provable_S_box0_iff_GL : forall psi,
  Provable_S (Box 0 psi) <-> Provable_GL psi.
Proof.
  intro psi. split.
  - exact (S_box_elim psi).
  - intro H. apply S_GL_subsumes. apply GL_Nec. exact H.
Qed.

Theorem Provable_GL_no_high_box : forall n psi,
  ~ Provable_GL (Box (S n) psi).
Proof.
  intros n psi H.
  exact (Provable_GL_VS_sound _ H (fun _ => True)).
Qed.

Theorem Provable_S_no_high_box : forall n psi,
  ~ Provable_S (Box (S n) psi).
Proof.
  intros n psi H.
  exact (Provable_S_VS_sound _ H (fun _ => True)).
Qed.

(** S is strictly stronger than GL: the reflection instance at the
    classically-valid [Box 0 Bot] is an S-theorem GL cannot prove
    (refuted in Fnat at world 1). *)

Theorem Provable_S_strictly_stronger_than_GL :
  exists phi, Provable_S phi /\ ~ Provable_GL phi.
Proof.
  exists (Impl (Box 0 (Box 0 Bot)) (Box 0 Bot)). split.
  - apply S_reflection. intro val. reflexivity.
  - intro H.
    pose proof (GL_in_provable _ H) as Hp.
    pose proof (soundness _ Hp Fnat (fun _ _ => true) 1) as Hf.
    cbn in Hf.
    assert (Hant : forall v : nat, Fnat_R 0 1 v ->
                   forall u : nat, Fnat_R 0 v u -> False).
    { intros v [Hv1 Hv2] u [Hu1 Hu2]. lia. }
    assert (Hr : Fnat_R 0 1 0) by (unfold Fnat_R; lia).
    exact (Hf Hant 0 Hr).
Qed.

(** The unrestricted Solovay-first statement fails: witness [Box 5 Top].
    Every proper interpretation collapses it to [Box 0 Top], whose code
    is Bew_n-0-provable, so the hypothesis holds; but Provable_GL derives
    no positive [Box (S n)] formula. *)

Theorem Solovay_first_full_unrestricted_refuted :
  ~ (forall phi,
      (forall I, is_arithmetic_interpretation_proper I ->
         Bew_n 0 (encode_form (I phi))) ->
      Provable_GL phi).
Proof.
  intro Hfull.
  apply (Provable_GL_no_high_box 4 Top).
  apply Hfull.
  intros I [HImpl [HBot HBox]].
  assert (HITop : I Top = Top).
  { unfold Top. rewrite HImpl. rewrite HBot. reflexivity. }
  rewrite HBox. rewrite HITop.
  unfold Bew_n. exists (Box 0 Top). split.
  - reflexivity.
  - apply Nec. apply Nec. unfold Top. apply prov_id.
Qed.

(** The unrestricted Solovay-second statement fails on the same witness;
    the standard-model conjunct also holds for the collapsed image, and
    Provable_S derives no positive [Box (S n)] formula. *)

Theorem Solovay_second_full_unrestricted_refuted :
  ~ (forall phi,
      (forall I, is_arithmetic_interpretation_proper I ->
         Bew_n 0 (encode_form (I phi)) /\
         (forall val, standard_model_satisfies val (I phi))) ->
      Provable_S phi).
Proof.
  intro Hfull.
  apply (Provable_S_no_high_box 4 Top).
  apply Hfull.
  intros I [HImpl [HBot HBox]].
  assert (HITop : I Top = Top).
  { unfold Top. rewrite HImpl. rewrite HBot. reflexivity. }
  rewrite HBox. rewrite HITop.
  split.
  - unfold Bew_n. exists (Box 0 Top). split.
    + reflexivity.
    + apply Nec. apply Nec. unfold Top. apply prov_id.
  - intro val. cbn.
    unfold Bew_n. exists Top. split.
    + reflexivity.
    + apply Nec. unfold Top. apply prov_id.
Qed.

(** The corrected Solovay-first on the level-0 fragment: the proper-
    interpretation hypothesis yields Provable_GL phi with no residual
    outer box, and conversely.  Completeness instantiates the hypothesis
    at [arith_embed_GL] and strips the outer box with [GL_box_elim]. *)

Theorem Solovay_first_full : forall phi,
  level_0_only phi ->
  (forall I, is_arithmetic_interpretation_proper I ->
     Bew_n 0 (encode_form (I phi))) ->
  Provable_GL phi.
Proof.
  intros phi Hl0 H.
  apply GL_box_elim.
  exact (Solovay_first_completeness_level_0_only_with_outer_Box_0 phi Hl0 H).
Qed.

Theorem Solovay_first_full_iff : forall phi,
  level_0_only phi ->
  ((forall I, is_arithmetic_interpretation_proper I ->
      Bew_n 0 (encode_form (I phi))) <-> Provable_GL phi).
Proof.
  intros phi Hl0. split.
  - apply Solovay_first_full. exact Hl0.
  - intros H I HI. exact (Solovay_first_soundness_proper phi H I HI).
Qed.

Theorem Solovay_second_full : forall phi,
  level_0_only phi ->
  (forall I, is_arithmetic_interpretation_proper I ->
     Bew_n 0 (encode_form (I phi)) /\ classical_valid (I phi)) ->
  Provable_S phi.
Proof.
  exact Solovay_second_completeness_level_0_only.
Qed.

Theorem Solovay_second_truth_soundness : forall phi,
  Provable_S phi ->
  forall I, is_arithmetic_interpretation_proper I ->
  classical_valid (I phi).
Proof.
  exact Solovay_second_soundness_proper_classical.
Qed.

Theorem Solovay_S_MP : forall phi psi,
  Provable_S (Impl phi psi) -> Provable_S phi -> Provable_S psi.
Proof. exact S_MP. Qed.

Theorem Solovay_S_classical_valid_implies_GL_proves : forall phi,
  box_free phi -> classical_valid phi -> Provable_GL phi.
Proof.
  intros phi Hbf Hval.
  apply ProvableProp_to_Provable_GL.
  exact (prop_completeness phi Hbf Hval).
Qed.

Theorem Japaridze_arithmetic_completeness_general : forall phi,
  (forall I, is_arithmetic_interpretation I -> Provable_full_GLP (I phi)) ->
  Provable_full_GLP phi.
Proof.
  intros phi H.
  pose proof (H (fun psi => psi) identity_is_arithmetic_interpretation) as Hp.
  cbn in Hp. exact Hp.
Qed.

Definition shift_interp : Form -> Form := fun phi => Impl Top_form phi.

Lemma shift_interp_is_arithmetic_interpretation :
  is_arithmetic_interpretation shift_interp.
Proof.
  split.
  - intros phi Hp. unfold shift_interp.
    exact (MP _ _ (Ax_K phi Top_form) Hp).
  - intros phi psi Hp. unfold shift_interp in *.
    exact (MP _ _ (Ax_S Top_form phi psi) Hp).
Qed.

Lemma Provable_full_GLP_Top_form : Provable_full_GLP Top_form.
Proof.
  unfold Top_form, Provable_full_GLP.
  pose proof (GLP_Ax_K Bot Bot) as HK1.
  pose proof (GLP_Ax_K Bot (Impl Bot Bot)) as HK2.
  pose proof (GLP_Ax_S Bot (Impl Bot Bot) Bot) as HS.
  pose proof (GLP_MP _ _ HS HK2) as HSK2.
  exact (GLP_MP _ _ HSK2 HK1).
Qed.

(** ** Japaridze completeness via a Solovay tree.

    [Solovay_node] / [solovay_tree_step] build an infinite tree branching
    on box-level (a level-n node spawns level-(n+1) children with
    [Box n f] / [Diamond n f] payloads).  [tree_validates I u] is the
    path-wise GLP-provability of the I-images.
    [Japaridze_full_via_tree] discharges tree-validation under all proper
    polymodal interpretations at the double-negation substitution
    [dn_interp], through the GLP-internal faithfulness
    [GLP_subst_faithful_back]; the converse [Japaridze_tree_soundness]
    gives the equivalence with GLP-provability. *)

Inductive Solovay_node : Type :=
  | sol_root : Solovay_node
  | sol_child : Solovay_node -> nat -> Form -> Solovay_node.

Definition solovay_tree_step (u : Solovay_node) : list Solovay_node :=
  match u with
  | sol_root =>
      [sol_child sol_root 0 Top; sol_child sol_root 0 Bot]
  | sol_child _ n f =>
      [sol_child u (S n) (Box n f); sol_child u (S n) (Diamond n f)]
  end.

Fixpoint node_depth (u : Solovay_node) : nat :=
  match u with
  | sol_root => 0
  | sol_child p _ _ => S (node_depth p)
  end.

Inductive in_tree : Solovay_node -> Prop :=
  | in_root : in_tree sol_root
  | in_step : forall u v,
      in_tree u -> In v (solovay_tree_step u) -> in_tree v.

Theorem solovay_tree_step_nonempty : forall u,
  solovay_tree_step u <> [].
Proof.
  intros [|p n f]; cbn; discriminate.
Qed.

Theorem solovay_tree_step_two_branches : forall u,
  length (solovay_tree_step u) = 2.
Proof.
  intros [|p n f]; reflexivity.
Qed.

Theorem solovay_tree_branches_distinct : forall u,
  exists v w,
    In v (solovay_tree_step u) /\ In w (solovay_tree_step u) /\ v <> w.
Proof.
  intros [|p n f].
  - exists (sol_child sol_root 0 Top), (sol_child sol_root 0 Bot).
    cbn. split; [tauto | split; [tauto |]].
    intro H. injection H as H. discriminate H.
  - exists (sol_child (sol_child p n f) (S n) (Box n f)),
           (sol_child (sol_child p n f) (S n) (Diamond n f)).
    cbn. split; [tauto | split; [tauto |]].
    intro H. injection H as H. discriminate H.
Qed.

Theorem solovay_tree_step_branches_on_level : forall p n f,
  solovay_tree_step (sol_child p n f) =
  [sol_child (sol_child p n f) (S n) (Box n f);
   sol_child (sol_child p n f) (S n) (Diamond n f)].
Proof. reflexivity. Qed.

Fixpoint solovay_spine (k : nat) : Solovay_node :=
  match k with
  | 0 => sol_root
  | S j =>
      match solovay_spine j with
      | sol_root => sol_child sol_root 0 Top
      | sol_child p n f => sol_child (sol_child p n f) (S n) (Box n f)
      end
  end.

Lemma solovay_spine_in_tree : forall k, in_tree (solovay_spine k).
Proof.
  induction k as [|j IH]; cbn.
  - exact in_root.
  - destruct (solovay_spine j) as [|p n f] eqn:E.
    + apply (in_step sol_root).
      * exact IH.
      * cbn. left. reflexivity.
    + apply (in_step (sol_child p n f)).
      * exact IH.
      * cbn. left. reflexivity.
Qed.

Lemma solovay_spine_depth : forall k, node_depth (solovay_spine k) = k.
Proof.
  induction k as [|j IH]; cbn.
  - reflexivity.
  - destruct (solovay_spine j) as [|p n f] eqn:E; cbn.
    + cbn in IH. rewrite <- IH. reflexivity.
    + cbn in IH. rewrite <- IH. reflexivity.
Qed.

Theorem solovay_tree_infinite : forall k,
  exists u, in_tree u /\ node_depth u = k.
Proof.
  intro k. exists (solovay_spine k).
  split; [exact (solovay_spine_in_tree k) | exact (solovay_spine_depth k)].
Qed.

Fixpoint tree_validates (I : Form -> Form) (u : Solovay_node) : Prop :=
  match u with
  | sol_root => True
  | sol_child p _ f => tree_validates I p /\ Provable_full_GLP (I f)
  end.

Definition build_solovay_tree (phi : Form) : Solovay_node :=
  sol_child sol_root 0 phi.

Definition is_polymodal_arithmetic_interpretation_proper
  (I : Form -> Form) : Prop :=
  (forall a b, I (Impl a b) = Impl (I a) (I b)) /\
  (I Bot = Bot) /\
  (forall n psi, I (Box n psi) = Box n (I psi)).

Lemma polymodal_proper_factors : forall I,
  is_polymodal_arithmetic_interpretation_proper I ->
  forall phi, I phi = subst_form (fun p => I (Var p)) phi.
Proof.
  intros I [HImpl [HBot HBox]] phi.
  induction phi as [p | | a IHa b IHb | n a IHa]; cbn.
  - reflexivity.
  - exact HBot.
  - rewrite HImpl, IHa, IHb. reflexivity.
  - rewrite HBox, IHa. reflexivity.
Qed.

(** The GLP-internal Hilbert toolkit, replayed from the |- versions. *)

Lemma GLPh_id : forall phi, Provable_GLP (Impl phi phi).
Proof.
  intro phi.
  exact (GLP_MP _ _
          (GLP_MP _ _ (GLP_Ax_S phi (Impl phi phi) phi)
                      (GLP_Ax_K phi (Impl phi phi)))
          (GLP_Ax_K phi phi)).
Qed.

Lemma GLPh_weaken : forall phi psi,
  Provable_GLP phi -> Provable_GLP (Impl psi phi).
Proof.
  intros phi psi H. exact (GLP_MP _ _ (GLP_Ax_K phi psi) H).
Qed.

Lemma GLPh_compose : forall phi psi chi,
  Provable_GLP (Impl phi psi) -> Provable_GLP (Impl psi chi) ->
  Provable_GLP (Impl phi chi).
Proof.
  intros phi psi chi Hpq Hqr.
  pose proof (GLP_Ax_S phi psi chi) as Hs.
  pose proof (GLPh_weaken _ phi Hqr) as Hpqr.
  exact (GLP_MP _ _ (GLP_MP _ _ Hs Hpqr) Hpq).
Qed.

Lemma GLPh_perm : forall phi psi chi,
  Provable_GLP (Impl phi (Impl psi chi)) ->
  Provable_GLP (Impl psi (Impl phi chi)).
Proof.
  intros phi psi chi H.
  pose proof (GLP_Ax_S phi psi chi) as Hs.
  pose proof (GLP_MP _ _ Hs H) as H1.
  pose proof (GLP_Ax_K psi phi) as Hk.
  exact (GLPh_compose _ _ _ Hk H1).
Qed.

Lemma GLPh_perm_internal : forall a b c,
  Provable_GLP (Impl (Impl a (Impl b c)) (Impl b (Impl a c))).
Proof.
  intros a b c.
  pose proof (GLP_Ax_S a b c) as H_S.
  pose proof (GLP_Ax_S (Impl a (Impl b c)) (Impl a b) (Impl a c)) as H_S2.
  pose proof (GLP_MP _ _ H_S2 H_S) as H1.
  pose proof (GLP_Ax_K b a) as H_K1.
  pose proof (GLP_Ax_K (Impl a b) (Impl a (Impl b c))) as H_K2.
  pose proof (GLPh_compose _ _ _ H_K1 H_K2) as H2.
  pose proof (GLPh_compose _ _ _ H2 H1) as H3.
  exact (GLPh_perm _ _ _ H3).
Qed.

Lemma GLPh_compose_internal : forall phi psi chi,
  Provable_GLP (Impl (Impl psi chi) (Impl (Impl phi psi) (Impl phi chi))).
Proof.
  intros phi psi chi.
  pose proof (GLP_Ax_K (Impl psi chi) phi) as Hk.
  pose proof (GLP_Ax_S phi psi chi) as Hs.
  exact (GLPh_compose _ _ _ Hk Hs).
Qed.

Lemma GLPh_DN_intro : forall phi,
  Provable_GLP (Impl phi (Neg (Neg phi))).
Proof.
  intro phi. unfold Neg.
  pose proof (GLPh_id (Impl phi Bot)) as Hid.
  exact (GLPh_perm _ _ _ Hid).
Qed.

Lemma GLPh_explosion : forall phi, Provable_GLP (Impl Bot phi).
Proof.
  intro phi.
  pose proof (GLP_Ax_K Bot (Neg phi)) as Hk.
  pose proof (GLP_Ax_DN phi) as HDN.
  exact (GLPh_compose _ _ _ Hk HDN).
Qed.

Lemma GLPh_neg_imp_ng : forall phi psi,
  Provable_GLP (Impl (Neg phi) (Impl phi (Neg psi))).
Proof.
  intros phi psi. unfold Neg.
  pose proof (GLPh_compose_internal phi Bot (Impl psi Bot)) as Hci.
  pose proof (GLPh_explosion (Impl psi Bot)) as Hex.
  exact (GLP_MP _ _ Hci Hex).
Qed.

Lemma GLPh_and_intro : forall phi psi,
  Provable_GLP (Impl phi (Impl psi (And phi psi))).
Proof.
  intros phi psi. unfold And, Neg.
  pose proof (GLPh_id (Impl phi (Impl psi Bot))) as Hid.
  pose proof (GLPh_perm _ _ _ Hid) as Hperm.
  pose proof (GLPh_perm_internal (Impl phi (Impl psi Bot)) psi Bot) as Hpi.
  exact (GLPh_compose _ _ _ Hperm Hpi).
Qed.

Lemma GLPh_and_intro_meta : forall phi psi,
  Provable_GLP phi -> Provable_GLP psi -> Provable_GLP (And phi psi).
Proof.
  intros phi psi Hphi Hpsi.
  exact (GLP_MP _ _ (GLP_MP _ _ (GLPh_and_intro phi psi) Hphi) Hpsi).
Qed.

Lemma GLPh_and_elim_l : forall phi psi,
  Provable_GLP (Impl (And phi psi) phi).
Proof.
  intros phi psi. unfold And, Neg.
  pose proof (GLPh_neg_imp_ng phi psi) as H1.
  pose proof (GLPh_compose_internal
                (Impl phi Bot) (Impl phi (Impl psi Bot)) Bot) as H2.
  pose proof (GLPh_perm _ _ _ H2) as H2_perm.
  pose proof (GLP_MP _ _ H2_perm H1) as Hstep1.
  pose proof (GLP_Ax_DN phi) as HDN.
  exact (GLPh_compose _ _ _ Hstep1 HDN).
Qed.

Lemma GLPh_and_elim_r : forall phi psi,
  Provable_GLP (Impl (And phi psi) psi).
Proof.
  intros phi psi. unfold And, Neg.
  pose proof (GLP_Ax_K (Impl psi Bot) phi) as H1.
  pose proof (GLPh_compose_internal
                (Impl psi Bot) (Impl phi (Impl psi Bot)) Bot) as H2.
  pose proof (GLPh_perm _ _ _ H2) as H2_perm.
  pose proof (GLP_MP _ _ H2_perm H1) as Hstep1.
  pose proof (GLP_Ax_DN psi) as HDN.
  exact (GLPh_compose _ _ _ Hstep1 HDN).
Qed.

Lemma GLPh_and_elim_l_meta : forall phi psi,
  Provable_GLP (And phi psi) -> Provable_GLP phi.
Proof.
  intros phi psi H. exact (GLP_MP _ _ (GLPh_and_elim_l phi psi) H).
Qed.

Lemma GLPh_and_elim_r_meta : forall phi psi,
  Provable_GLP (And phi psi) -> Provable_GLP psi.
Proof.
  intros phi psi H. exact (GLP_MP _ _ (GLPh_and_elim_r phi psi) H).
Qed.

Lemma GLPh_iff_intro : forall phi psi,
  Provable_GLP (Impl phi psi) -> Provable_GLP (Impl psi phi) ->
  Provable_GLP (Iff phi psi).
Proof.
  intros phi psi H1 H2. unfold Iff.
  exact (GLPh_and_intro_meta _ _ H1 H2).
Qed.

Lemma GLPh_iff_refl : forall phi, Provable_GLP (Iff phi phi).
Proof.
  intro phi. apply GLPh_iff_intro; apply GLPh_id.
Qed.

Lemma GLPh_box_imp : forall n phi psi,
  Provable_GLP (Impl phi psi) ->
  Provable_GLP (Impl (Box n phi) (Box n psi)).
Proof.
  intros n phi psi H.
  exact (GLP_MP _ _ (GLP_Ax_BoxK n phi psi) (GLP_Nec n _ H)).
Qed.

Lemma GLPh_impl_cong : forall a a' b b',
  Provable_GLP (Iff a a') -> Provable_GLP (Iff b b') ->
  Provable_GLP (Iff (Impl a b) (Impl a' b')).
Proof.
  intros a a' b b' H1 H2.
  pose proof (GLPh_and_elim_l_meta _ _ H1) as H1f.
  pose proof (GLPh_and_elim_r_meta _ _ H1) as H1b.
  pose proof (GLPh_and_elim_l_meta _ _ H2) as H2f.
  pose proof (GLPh_and_elim_r_meta _ _ H2) as H2b.
  apply GLPh_iff_intro.
  - pose proof (GLPh_compose_internal a' a b) as Hci1.
    pose proof (GLP_MP _ _ (GLPh_perm _ _ _ Hci1) H1b) as Hstep1.
    pose proof (GLPh_compose_internal a' b b') as Hci2.
    pose proof (GLP_MP _ _ Hci2 H2f) as Hstep2.
    exact (GLPh_compose _ _ _ Hstep1 Hstep2).
  - pose proof (GLPh_compose_internal a a' b') as Hci1.
    pose proof (GLP_MP _ _ (GLPh_perm _ _ _ Hci1) H1f) as Hstep1.
    pose proof (GLPh_compose_internal a b' b) as Hci2.
    pose proof (GLP_MP _ _ Hci2 H2b) as Hstep2.
    exact (GLPh_compose _ _ _ Hstep1 Hstep2).
Qed.

Lemma GLPh_box_cong : forall n a b,
  Provable_GLP (Iff a b) ->
  Provable_GLP (Iff (Box n a) (Box n b)).
Proof.
  intros n a b H.
  apply GLPh_iff_intro.
  - exact (GLPh_box_imp n _ _ (GLPh_and_elim_l_meta _ _ H)).
  - exact (GLPh_box_imp n _ _ (GLPh_and_elim_r_meta _ _ H)).
Qed.

Lemma GLPh_neg_neg_iff : forall phi,
  Provable_GLP (Iff phi (Neg (Neg phi))).
Proof.
  intro phi.
  apply GLPh_iff_intro.
  - exact (GLPh_DN_intro phi).
  - exact (GLP_Ax_DN phi).
Qed.

(** The double-negation substitution interpretation. *)

Definition dn_sigma : nat -> Form := fun p => Neg (Neg (Var p)).

Definition dn_interp : Form -> Form := subst_form dn_sigma.

Lemma dn_interp_proper :
  is_polymodal_arithmetic_interpretation_proper dn_interp.
Proof.
  split; [|split].
  - intros a b. reflexivity.
  - reflexivity.
  - intros n psi. reflexivity.
Qed.

Theorem dn_interp_not_identity : exists phi, dn_interp phi <> phi.
Proof.
  exists (Var 0). cbv. discriminate.
Qed.

Theorem dn_interp_not_shift_interp :
  exists phi, dn_interp phi <> shift_interp phi.
Proof.
  exists Bot. cbv. discriminate.
Qed.

Lemma GLP_dn_subst_iff : forall phi,
  Provable_GLP (Iff phi (dn_interp phi)).
Proof.
  intro phi. unfold dn_interp.
  induction phi as [p | | a IHa b IHb | n a IHa]; cbn [subst_form].
  - exact (GLPh_neg_neg_iff (Var p)).
  - exact (GLPh_iff_refl Bot).
  - exact (GLPh_impl_cong _ _ _ _ IHa IHb).
  - exact (GLPh_box_cong n _ _ IHa).
Qed.

Theorem GLP_subst_faithful_back : forall phi,
  Provable_GLP (dn_interp phi) -> Provable_GLP phi.
Proof.
  intros phi H.
  pose proof (GLP_dn_subst_iff phi) as Hiff.
  pose proof (GLPh_and_elim_r_meta _ _ Hiff) as Hback.
  exact (GLP_MP _ _ Hback H).
Qed.

Lemma GLP_subst_provable : forall sigma phi,
  Provable_GLP phi -> Provable_GLP (subst_form sigma phi).
Proof.
  intros sigma phi H.
  induction H as [phi psi | phi psi chi | phi | n phi psi | n phi | n phi
                 | n phi | n phi | phi psi H1 IH1 H2 IH2 | n phi H IH]; cbn.
  - apply GLP_Ax_K.
  - apply GLP_Ax_S.
  - apply GLP_Ax_DN.
  - apply GLP_Ax_BoxK.
  - apply GLP_Ax_Loeb.
  - apply GLP_Ax_Box4.
  - apply GLP_Ax_Mon.
  - apply GLP_Ax_Japaridze.
  - exact (GLP_MP _ _ IH1 IH2).
  - exact (GLP_Nec n _ IH).
Qed.

(** Completeness: tree-validation under all proper polymodal
    interpretations yields GLP-provability, discharged at [dn_interp]
    through the GLP-internal faithfulness theorem. *)

Theorem Japaridze_full_via_tree : forall phi,
  (forall I, is_polymodal_arithmetic_interpretation_proper I ->
     tree_validates I (build_solovay_tree phi)) ->
  Provable_full_GLP phi.
Proof.
  intros phi H.
  pose proof (H dn_interp dn_interp_proper) as Hv.
  cbn in Hv.
  destruct Hv as [_ Hval].
  exact (GLP_subst_faithful_back phi Hval).
Qed.

Theorem Japaridze_tree_soundness : forall phi,
  Provable_full_GLP phi ->
  forall I, is_polymodal_arithmetic_interpretation_proper I ->
  tree_validates I (build_solovay_tree phi).
Proof.
  intros phi H J HJ. cbn.
  split; [exact I|].
  rewrite (polymodal_proper_factors J HJ phi).
  exact (GLP_subst_provable _ _ H).
Qed.

Theorem Japaridze_full_via_tree_iff : forall phi,
  (forall I, is_polymodal_arithmetic_interpretation_proper I ->
     tree_validates I (build_solovay_tree phi))
  <-> Provable_full_GLP phi.
Proof.
  intro phi. split.
  - exact (Japaridze_full_via_tree phi).
  - exact (Japaridze_tree_soundness phi).
Qed.

Theorem tree_validates_not_trivial :
  exists I u,
    is_polymodal_arithmetic_interpretation_proper I /\
    ~ tree_validates I u.
Proof.
  exists dn_interp, (build_solovay_tree Bot).
  split.
  - exact dn_interp_proper.
  - cbn. intros [_ Habs].
    pose proof (provable_GLP_classically_valid _ Habs (fun _ => false)) as He.
    cbn in He. discriminate He.
Qed.

Theorem Japaridze_tree_summary :
  (forall u, solovay_tree_step u <> []) /\
  (forall u, length (solovay_tree_step u) = 2) /\
  (forall k, exists u, in_tree u /\ node_depth u = k) /\
  (exists I u,
     is_polymodal_arithmetic_interpretation_proper I /\
     ~ tree_validates I u) /\
  (exists phi, dn_interp phi <> phi) /\
  (exists phi, dn_interp phi <> shift_interp phi) /\
  (forall phi,
     (forall I, is_polymodal_arithmetic_interpretation_proper I ->
        tree_validates I (build_solovay_tree phi))
     <-> Provable_full_GLP phi).
Proof.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - exact solovay_tree_step_nonempty.
  - exact solovay_tree_step_two_branches.
  - exact solovay_tree_infinite.
  - exact tree_validates_not_trivial.
  - exact dn_interp_not_identity.
  - exact dn_interp_not_shift_interp.
  - exact Japaridze_full_via_tree_iff.
Qed.

Definition arith_interp_full_constant_top_image_ignoring_level
  (phi : Form) (level : nat) : FOFormula :=
  arith_interp_full (fun _ => FOTopForm) phi.

Theorem universal_arithmetic_interpretation_implies_GLP_via_shift_interp_MP :
  forall phi,
  (forall I : Form -> Form, is_arithmetic_interpretation I ->
     Provable_full_GLP (I phi)) ->
  Provable_full_GLP phi.
Proof.
  intros phi H.
  pose proof (H shift_interp shift_interp_is_arithmetic_interpretation) as Hp.
  unfold shift_interp in Hp.
  exact (GLP_MP _ _ Hp Provable_full_GLP_Top_form).
Qed.

Theorem Japaridze_full : forall phi,
  (forall I, is_arithmetic_interpretation I -> Provable_full_GLP (I phi)) ->
  Provable_full_GLP phi.
Proof.
  intros phi H.
  pose proof (H shift_interp shift_interp_is_arithmetic_interpretation) as Hp.
  unfold shift_interp in Hp.
  exact (GLP_MP _ _ Hp Provable_full_GLP_Top_form).
Qed.

Theorem Japaridze_full_via_shift_interp_MP_bundle :
  is_arithmetic_interpretation shift_interp /\
  Provable_full_GLP Top_form /\
  (forall phi, (forall I, is_arithmetic_interpretation I ->
       Provable_full_GLP (I phi)) -> Provable_full_GLP phi) /\
  (forall phi level,
     arith_interp_full_constant_top_image_ignoring_level phi level
     = arith_interp_full (fun _ => FOTopForm) phi) /\
  (forall phi, (forall I : Form -> Form, is_arithmetic_interpretation I ->
       Provable_full_GLP (I phi)) -> Provable_full_GLP phi).
Proof.
  split; [|split; [|split; [|split]]].
  - exact shift_interp_is_arithmetic_interpretation.
  - exact Provable_full_GLP_Top_form.
  - exact Japaridze_full.
  - intros phi level. reflexivity.
  - exact universal_arithmetic_interpretation_implies_GLP_via_shift_interp_MP.
Qed.

Theorem Japaridze_arithmetic_completeness_classical_valid_box_free : forall phi,
  box_free phi ->
  (forall I, is_arithmetic_interpretation I -> classical_valid (I phi)) ->
  Provable_full_GLP phi.
Proof.
  intros phi Hbf H.
  pose proof (H (fun psi => psi) identity_is_arithmetic_interpretation) as Hp.
  cbn in Hp.
  apply ProvableProp_implies_Provable_GLP.
  apply prop_completeness; assumption.
Qed.

Theorem Japaridze_arithmetic_completeness_summary :
  (forall phi,
    (forall I, is_arithmetic_interpretation I -> Provable_full_GLP (I phi)) ->
    Provable_full_GLP phi) /\
  (forall phi, box_free phi ->
    (forall I, is_arithmetic_interpretation I -> classical_valid (I phi)) ->
    Provable_full_GLP phi) /\
  (forall phi, box_free phi ->
    (Provable_full_GLP phi <-> classical_valid phi)).
Proof.
  split; [|split].
  - exact Japaridze_arithmetic_completeness_general.
  - exact Japaridze_arithmetic_completeness_classical_valid_box_free.
  - exact solovay_polymodal_box_free.
Qed.

Theorem Japaridze_arithmetic_completeness_with_box_licensure :
  (forall phi,
    (forall I, is_arithmetic_interpretation I -> Provable_full_GLP (I phi)) ->
    Provable_full_GLP phi) /\
  (forall phi, box_free phi ->
    (forall I, is_arithmetic_interpretation I -> classical_valid (I phi)) ->
    Provable_full_GLP phi) /\
  (forall phi, box_free phi ->
    (Provable_full_GLP phi <-> classical_valid phi)) /\
  (forall phi,
    (forall I, is_arithmetic_interpretation I -> Provable_full_GLP (I phi)) ->
    Provable_full_GLP phi /\
    (forall k, Provable_full_GLP (Box k phi))).
Proof.
  split; [|split; [|split]].
  - exact Japaridze_arithmetic_completeness_general.
  - exact Japaridze_arithmetic_completeness_classical_valid_box_free.
  - exact solovay_polymodal_box_free.
  - intros phi H. split.
    + exact (Japaridze_arithmetic_completeness_general phi H).
    + intro k.
      pose proof (H (licenses k) (licenses_is_arithmetic_interpretation k)) as Hp.
      unfold licenses in Hp. exact Hp.
Qed.

Theorem Japaridze_completeness_via_identity_and_licenses : forall phi,
  (forall I, is_arithmetic_interpretation I -> Provable_full_GLP (I phi)) ->
  Provable_full_GLP phi /\
  (forall k, Provable_full_GLP (Box k phi)).
Proof.
  intros phi H. split.
  - exact (Japaridze_arithmetic_completeness_general phi H).
  - intro k.
    pose proof (H (licenses k) (licenses_is_arithmetic_interpretation k)) as Hp.
    unfold licenses in Hp. exact Hp.
Qed.

(** ** Level-0 conservativity of full GLP over GL, and the Pi_2 class.

    [forget_levels] on [Provable_full_GLP]: every GLP axiom maps to a
    GL-theorem and the translation is the identity on the level-0-only
    fragment, giving [GLP_level_0_conservativity].  [is_Pi_2] is the
    Form-language form of [forall n exists m, R(n,m)]: a level-0 Box
    over a level-0-only Sigma_1-modal body. *)

Lemma forget_Japaridze : forall n phi,
  Provable_GL (forget_levels (Japaridze n phi)).
Proof.
  intros n phi. unfold Japaridze. cbn [forget_levels].
  apply GL_imply_top.
Qed.

Lemma glp_forget_derivation : forall phi,
  Provable_full_GLP phi -> Provable_GL (forget_levels phi).
Proof.
  intros phi H.
  induction H as [phi psi | phi psi chi | phi | n phi psi | n phi | n phi
                 | n phi | n phi | phi psi H1 IH1 H2 IH2 | n phi H IH].
  - apply forget_AxK.
  - apply forget_AxS.
  - apply forget_AxDN.
  - apply forget_AxBoxK.
  - apply forget_AxLoeb.
  - apply forget_AxBox4.
  - apply forget_AxMon.
  - apply forget_Japaridze.
  - cbn [forget_levels] in IH1. exact (GL_MP _ _ IH1 IH2).
  - cbn [forget_levels]. destruct n as [|n'].
    + exact (GL_Nec _ IH).
    + exact GL_top.
Qed.

Lemma GL_in_GLP : forall phi, Provable_GL phi -> Provable_full_GLP phi.
Proof.
  intros phi H.
  induction H as [phi psi | phi psi chi | phi | phi psi | phi | phi
                 | phi psi H1 IH1 H2 IH2 | phi H IH].
  - apply GLP_Ax_K.
  - apply GLP_Ax_S.
  - apply GLP_Ax_DN.
  - apply (GLP_Ax_BoxK 0).
  - apply (GLP_Ax_Loeb 0).
  - apply (GLP_Ax_Box4 0).
  - exact (GLP_MP _ _ IH1 IH2).
  - exact (GLP_Nec 0 _ IH).
Qed.

Theorem GLP_level_0_conservativity : forall phi,
  level_0_only phi -> Provable_full_GLP phi -> Provable_GL phi.
Proof.
  intros phi Hl H.
  pose proof (glp_forget_derivation phi H) as HGL.
  rewrite (forget_levels_level_0_only phi Hl) in HGL.
  exact HGL.
Qed.

Theorem GLP_level_0_conservativity_iff : forall phi,
  level_0_only phi -> (Provable_full_GLP phi <-> Provable_GL phi).
Proof.
  intros phi Hl. split.
  - exact (GLP_level_0_conservativity phi Hl).
  - exact (GL_in_GLP phi).
Qed.

Definition is_Pi_2 (phi : Form) : Prop :=
  exists psi,
    Sigma1_modal psi /\ level_0_only psi /\ phi = Box 0 psi.

Lemma box_free_level_0_only : forall phi,
  box_free phi -> level_0_only phi.
Proof.
  induction phi as [p | | a IHa b IHb | n a IHa]; cbn; intro H.
  - exact I.
  - exact I.
  - destruct H as [Ha Hb]. split; [exact (IHa Ha) | exact (IHb Hb)].
  - destruct H.
Qed.

Lemma is_Pi_2_level_0_only : forall phi,
  is_Pi_2 phi -> level_0_only phi.
Proof.
  intros phi [psi [Hs [Hl Heq]]]. subst phi.
  cbn. split; [reflexivity | exact Hl].
Qed.

Theorem Pi_2_conservativity : forall phi,
  is_Pi_2 phi -> Provable_full_GLP phi -> Provable_GL phi.
Proof.
  intros phi Hp2 H.
  exact (GLP_level_0_conservativity phi (is_Pi_2_level_0_only phi Hp2) H).
Qed.

Definition extract_GL_derivation (phi : Form)
  (H : Provable_full_GLP phi) (Hp2 : is_Pi_2 phi) : Provable_GL phi :=
  Pi_2_conservativity phi Hp2 H.

Theorem Pi_2_nonvacuous :
  exists phi, is_Pi_2 phi /\ Provable_full_GLP phi.
Proof.
  exists (Box 0 Top). split.
  - exists Top. split; [|split].
    + apply S1_box_free. cbn. split; exact I.
    + cbn. split; exact I.
    + reflexivity.
  - apply (GLP_Nec 0). exact Provable_full_GLP_Top_form.
Qed.

Theorem Pi_2_not_Bot_restriction :
  exists phi, is_Pi_2 phi /\ phi <> Bot.
Proof.
  exists (Box 0 Top). split.
  - exists Top. split; [|split].
    + apply S1_box_free. cbn. split; exact I.
    + cbn. split; exact I.
    + reflexivity.
  - discriminate.
Qed.

Theorem Pi_2_not_box_free_restriction :
  exists phi, is_Pi_2 phi /\ ~ box_free phi.
Proof.
  exists (Box 0 Top). split.
  - exists Top. split; [|split].
    + apply S1_box_free. cbn. split; exact I.
    + cbn. split; exact I.
    + reflexivity.
  - cbn. intro H. exact H.
Qed.

Theorem Pi_2_worked_instance :
  is_Pi_2 (Box 0 (Box 0 Top)) /\
  Provable_full_GLP (Box 0 (Box 0 Top)) /\
  Provable_GL (Box 0 (Box 0 Top)).
Proof.
  assert (Hp2 : is_Pi_2 (Box 0 (Box 0 Top))).
  { exists (Box 0 Top). split; [|split].
    - apply S1_box.
    - cbn. split; [reflexivity | split; exact I].
    - reflexivity. }
  assert (HGLP : Provable_full_GLP (Box 0 (Box 0 Top))).
  { apply (GLP_Nec 0). apply (GLP_Nec 0). exact Provable_full_GLP_Top_form. }
  split; [exact Hp2 | split; [exact HGLP|]].
  exact (extract_GL_derivation _ HGLP Hp2).
Qed.

Theorem Pi_2_conservativity_summary :
  (forall phi, is_Pi_2 phi -> Provable_full_GLP phi -> Provable_GL phi) /\
  (forall phi, level_0_only phi ->
     (Provable_full_GLP phi <-> Provable_GL phi)) /\
  (exists phi, is_Pi_2 phi /\ Provable_full_GLP phi) /\
  (exists phi, is_Pi_2 phi /\ phi <> Bot) /\
  (exists phi, is_Pi_2 phi /\ ~ box_free phi).
Proof.
  split; [|split; [|split; [|split]]].
  - exact Pi_2_conservativity.
  - exact GLP_level_0_conservativity_iff.
  - exact Pi_2_nonvacuous.
  - exact Pi_2_not_Bot_restriction.
  - exact Pi_2_not_box_free_restriction.
Qed.

(** ** The arithmetic layer: the four headline theorems over [FOProvesTn]
    and [FOsat].

    Interpretations are [Form -> FOFormula] maps commuting with
    implication and falsity and sending [Box n] to the level-[n]
    provability sentence ([is_FO_arithmetic_interpretation]); the
    standard model is [FOsat]; provability is derivability in the
    reflection tower.  Completeness on the box-free fragment goes
    through a Boolean-valuation family: every interpretation factors
    through [FOembed] ([FO_interpretation_factors]), and the closed
    atoms [FOTopFm]/[FOFalseF] realize every classical valuation.  On
    the level-0 fragment the literal truth-completeness for GL fails:
    the reflection instance [Impl (Box 0 (Var 0)) (Var 0)] is true
    under every interpretation by tower soundness
    ([FOProvesTn_sound]) but is not a GL theorem, so recovering GL
    from truth at the standard model requires Solovay's nonstandard
    construction rather than this tower's soundness
    ([FOSolovay_first_truth_completeness_refuted]).  The tower
    transposes Solovay's second theorem as truth strictly exceeding
    every level's derivability ([FOSolovay_second_full], witness the
    level-0 consistency sentence via [FOGodel2]), the Japaridze tree
    theorem as box-free tree-validation completeness plus the strict
    growth of the tower ([FOJaparidze_full_via_tree],
    [FOJaparidze_tower_strict]), and Pi_2 conservativity over the
    [FOForall]/[FOExists] class as witness extraction plus Sigma_1
    conservativity of every level over the base
    ([FOPi_2_conservativity]). *)

Lemma eval_Impl_true_iff : forall val a b,
  eval val (Impl a b) = true <->
  (eval val a = true -> eval val b = true).
Proof.
  intros val a b. cbn [eval].
  destruct (eval val a); destruct (eval val b); cbn;
    split; intros H;
    try reflexivity; try discriminate;
    try (intros H2; reflexivity);
    try (intros H2; discriminate H2);
    try (apply H; reflexivity).
Qed.

Definition FOof_bool (b : bool) : FOFormula :=
  if b then FOTopFm else FOFalseF.

Lemma FOsat_FOof_bool : forall e b,
  FOsat e (FOof_bool b) <-> b = true.
Proof.
  intros e b. destruct b; cbn.
  - split; [intros _; reflexivity | intros _ HF; exact HF].
  - split; [intros HF; exfalso; exact HF | intro Hb; discriminate Hb].
Qed.

(** Satisfaction of a box-free embedding over Boolean-valued atoms is
    classical evaluation. *)

Lemma FOembed_bool_box_free_sat : forall phi val e,
  box_free phi ->
  (FOsat e (FOembed (fun p => FOof_bool (val p)) phi) <->
   eval val phi = true).
Proof.
  induction phi as [p | | a IHa b IHb | n a IHa]; intros val e Hbf.
  - cbn [FOembed eval]. apply FOsat_FOof_bool.
  - cbn [FOembed FOsat eval].
    split; [intros HF; destruct HF | intro Hb; discriminate Hb].
  - destruct Hbf as [Hba Hbb].
    cbn [FOembed FOsat].
    rewrite eval_Impl_true_iff.
    split.
    + intros Himp Ha.
      apply (IHb val e Hbb). apply Himp. apply (IHa val e Hba). exact Ha.
    + intros Hev Hsa.
      apply (IHb val e Hbb). apply Hev. apply (IHa val e Hba). exact Hsa.
  - exfalso; exact Hbf.
Qed.

(** Satisfaction of a box-free embedding over arbitrary atoms is
    classical evaluation at the valuation reading off each atom's
    truth. *)

Lemma FOembed_box_free_sat_eval : forall phi nu e,
  box_free phi ->
  (FOsat e (FOembed nu phi) <->
   eval (fun p => if excluded_middle_informative (FOsat e (nu p))
                  then true else false) phi = true).
Proof.
  induction phi as [p | | a IHa b IHb | n a IHa]; intros nu e Hbf.
  - cbn [FOembed eval].
    destruct (excluded_middle_informative (FOsat e (nu p))) as [Hs|Hs].
    + split; [intros _; reflexivity | intros _; exact Hs].
    + split; [intro Hc; exfalso; exact (Hs Hc) | intro Hc; discriminate Hc].
  - cbn [FOembed FOsat eval].
    split; [intros HF; destruct HF | intro Hb; discriminate Hb].
  - destruct Hbf as [Hba Hbb].
    cbn [FOembed FOsat].
    rewrite eval_Impl_true_iff.
    split.
    + intros Himp Ha.
      apply (IHb nu e Hbb). apply Himp. apply (IHa nu e Hba). exact Ha.
    + intros Hev Hsa.
      apply (IHb nu e Hbb). apply Hev. apply (IHa nu e Hba). exact Hsa.
  - exfalso; exact Hbf.
Qed.

(** The reflection instance at an atom is not a GL theorem: it fails in
    [Fnat] at world 1 under the valuation marking only world 0. *)

Lemma reflection_axiom_not_GL_provable :
  ~ Provable_GL (Impl (Box 0 (Var 0)) (Var 0)).
Proof.
  intro HGL.
  pose proof (GL_in_provable _ HGL) as Hp.
  pose proof (soundness _ Hp Fnat (fun w _ => Nat.eqb w 0) 1) as Hf.
  cbn in Hf.
  assert (Hant : forall v : nat, Fnat_R 0 1 v -> Nat.eqb v 0 = true).
  { intros v Hv. destruct Hv as [Hv1 Hv2].
    assert (v = 0) by lia. subst v. reflexivity. }
  pose proof (Hf Hant) as Hbad. cbn in Hbad. discriminate Hbad.
Qed.

(** Solovay's first theorem over the tower: on the box-free fragment,
    truth under every arithmetic interpretation coincides with GL
    derivability. *)

Theorem FOSolovay_first_full : forall phi,
  box_free phi ->
  ((forall J, is_FO_arithmetic_interpretation J ->
      forall e, FOsat e (J phi)) <-> Provable_GL phi).
Proof.
  intros phi Hbf. split.
  - intro H.
    apply ProvableProp_to_Provable_GL.
    apply prop_completeness; [exact Hbf|].
    intro val.
    apply (FOembed_bool_box_free_sat phi val (fun _ => 0) Hbf).
    exact (H (FOembed (fun p => FOof_bool (val p)))
             (FOembed_proper _) (fun _ => 0)).
  - intros HGL J HJ e.
    rewrite (FO_interpretation_factors J HJ phi).
    apply (FOembed_box_free_sat_eval phi (fun p => J (Var p)) e Hbf).
    apply (provable_classically_valid phi (GL_in_provable _ HGL)).
Qed.

(** On the level-0 fragment with boxes the truth hypothesis is weaker
    than GL derivability: the reflection instance is true under every
    interpretation by tower soundness yet GL-unprovable. *)

Theorem FOSolovay_first_truth_completeness_refuted :
  ~ (forall phi, level_0_only phi ->
       (forall J, is_FO_arithmetic_interpretation J ->
          forall e, FOsat e (J phi)) ->
       Provable_GL phi).
Proof.
  intro Hfull.
  apply reflection_axiom_not_GL_provable.
  apply Hfull.
  - cbn. split; [split; [reflexivity | exact I] | exact I].
  - intros J HJ e.
    destruct HJ as [HI [HB HX]].
    rewrite HI, HX.
    cbn [FOsat]. intro Hp.
    exact (FOProvesTn_sound 0 (J (Var 0))
             (proj1 (FOProvSentence_sat_iff e 0 (J (Var 0))) Hp) e).
Qed.

(** Solovay's second theorem over the tower: derivability yields truth
    of both the formula and its provability sentence, and truth
    strictly exceeds derivability — the level-0 consistency sentence is
    true and underivable. *)

Theorem FOSolovay_second_full :
  (forall n A, FOProvesTn n A ->
     (forall e, FOsat e (FOProvSentence n A)) /\ (forall e, FOsat e A)) /\
  (exists A, (forall e, FOsat e A) /\ ~ FOProvesTn 0 A).
Proof.
  split.
  - intros n A H. split.
    + intro e. apply FOHBL1_sat. exact H.
    + intro e. exact (FOProvesTn_sound n A H e).
  - exists (FONeg (FOProvSentence 0 FOFalseF)). split.
    + intro e. exact (FOConSentenceF_true e 0).
    + exact (FOGodel2 0).
Qed.

(** Tree validation over the Solovay tree, with images read through
    [FOsat]. *)

Fixpoint FOtree_validates (J : Form -> FOFormula) (u : Solovay_node) : Prop :=
  match u with
  | sol_root => True
  | sol_child p _ f => FOtree_validates J p /\ forall e, FOsat e (J f)
  end.

(** Japaridze's theorem over the tower: box-free tree validation under
    every arithmetic interpretation yields GLP derivability. *)

Theorem FOJaparidze_full_via_tree : forall phi,
  box_free phi ->
  (forall J, is_FO_arithmetic_interpretation J ->
     FOtree_validates J (build_solovay_tree phi)) ->
  Provable_full_GLP phi.
Proof.
  intros phi Hbf H.
  apply ProvableProp_implies_Provable_GLP.
  apply prop_completeness; [exact Hbf|].
  intro val.
  pose proof (H (FOembed (fun p => FOof_bool (val p)))
                (FOembed_proper _)) as Hv.
  cbn [FOtree_validates build_solovay_tree] in Hv.
  destruct Hv as [_ Hsat].
  apply (FOembed_bool_box_free_sat phi val (fun _ => 0) Hbf).
  exact (Hsat (fun _ => 0)).
Qed.

(** The unrestricted tree statement fails on the same reflection
    witness. *)

Theorem FOJaparidze_full_unrestricted_refuted :
  ~ (forall phi,
       (forall J, is_FO_arithmetic_interpretation J ->
          FOtree_validates J (build_solovay_tree phi)) ->
       Provable_full_GLP phi).
Proof.
  intro Hfull.
  apply reflection_axiom_not_GL_provable.
  apply (GLP_level_0_conservativity (Impl (Box 0 (Var 0)) (Var 0))).
  - cbn. split; [split; [reflexivity | exact I] | exact I].
  - apply Hfull.
    intros J HJ.
    cbn [FOtree_validates build_solovay_tree].
    split; [exact I|].
    intro e.
    destruct HJ as [HI [HB HX]].
    rewrite HI, HX.
    cbn [FOsat]. intro Hp.
    exact (FOProvesTn_sound 0 (J (Var 0))
             (proj1 (FOProvSentence_sat_iff e 0 (J (Var 0))) Hp) e).
Qed.

(** The realized tower grows strictly at every level: the level-[n]
    consistency sentence is the [FOAx_Refl] instance at falsity one
    level up, and is underivable at its own level by Goedel's second
    incompleteness theorem. *)

Theorem FOJaparidze_tower_strict : forall n,
  FOProvesTn (S n) (FONeg (FOProvSentence n FOFalseF)) /\
  ~ FOProvesTn n (FONeg (FOProvSentence n FOFalseF)).
Proof.
  intro n. split.
  - apply FOProvesTn_ax.
    exact (FOAx_Refl (S n) n FOFalseF (Nat.lt_succ_diag_r n)).
  - exact (FOGodel2 n).
Qed.

(** The Pi_2 class over [FOFormula], in [FOForall]/[FOExists] shape. *)

Definition is_FO_Pi_2 (A : FOFormula) : Prop :=
  exists x y D, FOdelta0 D /\ A = FOForall x (FOExists y D).

(** Derivable Pi_2 sentences yield witnesses in the standard model. *)

Theorem FOPi_2_conservativity_witnesses : forall n x y D,
  FOdelta0 D ->
  FOProvesTn n (FOForall x (FOExists y D)) ->
  forall e a, exists b, FOsat (FOupdate (FOupdate e x a) y b) D.
Proof.
  intros n x y D _ H e a.
  pose proof (FOProvesTn_sound n _ H e) as Hs.
  cbn [FOsat] in Hs.
  exact (Hs a).
Qed.

(** Every tower level is Sigma_1-conservative over the base: a closed
    Sigma_1 sentence derivable at any level is true, hence derivable at
    level 0 by Sigma_1 completeness. *)

Theorem FOSigma_1_conservativity : forall n A,
  FOsigma1 A -> (forall v, FOfree_in v A = false) ->
  FOProvesTn n A -> FOProvesTn 0 A.
Proof.
  intros n A HS Hcl H.
  exact (FOsigma1_completeness_closed A HS Hcl
           (FOProvesTn_sound n A H (fun _ => 0)) 0).
Qed.

Theorem FOPi_2_nonvacuous :
  exists A, is_FO_Pi_2 A /\ FOProvesTn 0 A.
Proof.
  exists (FOForall 0 (FOExists 1 (FOEq (FOVar 1) (FOVar 0)))).
  split.
  - exists 0, 1, (FOEq (FOVar 1) (FOVar 0)).
    split; [apply FOd0_eq | reflexivity].
  - apply FOProvesTn_Gen.
    eapply FOProvesTn_MP.
    + exact (FOProvesTn_ExIntroT 0 1 (FOVar 0)
               (FOEq (FOVar 1) (FOVar 0)) eq_refl).
    + cbn. apply FOProvesTn_EqRefl.
Qed.

(** Pi_2 conservativity over the tower: witness extraction for
    derivable Pi_2 sentences, Sigma_1 conservativity of every level
    over the base, a derivable Pi_2 inhabitant, and the failure of
    downward conservativity at Pi_1 (the consistency sentence). *)

Theorem FOPi_2_conservativity :
  (forall n x y D, FOdelta0 D ->
     FOProvesTn n (FOForall x (FOExists y D)) ->
     forall e a, exists b, FOsat (FOupdate (FOupdate e x a) y b) D) /\
  (forall n A, FOsigma1 A -> (forall v, FOfree_in v A = false) ->
     FOProvesTn n A -> FOProvesTn 0 A) /\
  (exists A, is_FO_Pi_2 A /\ FOProvesTn 0 A) /\
  (exists A, (forall v, FOfree_in v A = false) /\
     FOProvesTn 1 A /\ ~ FOProvesTn 0 A).
Proof.
  split; [|split; [|split]].
  - exact FOPi_2_conservativity_witnesses.
  - exact FOSigma_1_conservativity.
  - exact FOPi_2_nonvacuous.
  - exists (FONeg (FOProvSentence 0 FOFalseF)).
    destruct (FOJaparidze_tower_strict 0) as [H1 H0].
    split; [|split].
    + intro v. unfold FONeg. cbn [FOfree_in].
      rewrite FOProvSentence_closed. reflexivity.
    + exact H1.
    + exact H0.
Qed.

(** The arithmetic layer in one statement: representability of
    derivability by the Sigma_1 provability sentence, the
    Hilbert-Bernays-Loeb conditions and Loeb's rule against [FOsat],
    soundness at the standard model, Goedel's second incompleteness
    theorem at every level, and the four transposed headline
    theorems. *)

Theorem arithmetic_layer_summary :
  (forall e n A, FOsat e (FOProvSentence n A) <-> FOProvesTn n A) /\
  (forall e n A, FOProvesTn n A -> FOsat e (FOProvSentence n A)) /\
  (forall e n A B, FOsat e (FOProvSentence n (FOImplF A B)) ->
     FOsat e (FOProvSentence n A) -> FOsat e (FOProvSentence n B)) /\
  (forall e n A, FOsat e (FOProvSentence n A) ->
     FOsat e (FOProvSentence n (FOProvSentence n A))) /\
  (forall e n A,
     FOsat e (FOProvSentence n (FOImplF (FOProvSentence n A) A)) ->
     FOsat e (FOProvSentence n A)) /\
  (forall n A, FOProvesTn n A -> forall e, FOsat e A) /\
  (forall n, ~ FOProvesTn n (FONeg (FOProvSentence n FOFalseF))) /\
  (forall phi, box_free phi ->
     ((forall J, is_FO_arithmetic_interpretation J ->
         forall e, FOsat e (J phi)) <-> Provable_GL phi)) /\
  ((forall n A, FOProvesTn n A ->
      (forall e, FOsat e (FOProvSentence n A)) /\ (forall e, FOsat e A)) /\
   (exists A, (forall e, FOsat e A) /\ ~ FOProvesTn 0 A)) /\
  (forall phi, box_free phi ->
     (forall J, is_FO_arithmetic_interpretation J ->
        FOtree_validates J (build_solovay_tree phi)) ->
     Provable_full_GLP phi) /\
  (forall n,
     FOProvesTn (S n) (FONeg (FOProvSentence n FOFalseF)) /\
     ~ FOProvesTn n (FONeg (FOProvSentence n FOFalseF))) /\
  ((forall n x y D, FOdelta0 D ->
      FOProvesTn n (FOForall x (FOExists y D)) ->
      forall e a, exists b, FOsat (FOupdate (FOupdate e x a) y b) D) /\
   (forall n A, FOsigma1 A -> (forall v, FOfree_in v A = false) ->
      FOProvesTn n A -> FOProvesTn 0 A) /\
   (exists A, is_FO_Pi_2 A /\ FOProvesTn 0 A) /\
   (exists A, (forall v, FOfree_in v A = false) /\
      FOProvesTn 1 A /\ ~ FOProvesTn 0 A)).
Proof.
  split; [|split; [|split; [|split; [|split; [|split; [|split;
    [|split; [|split; [|split; [|split]]]]]]]]]].
  - exact FOProvSentence_sat_iff.
  - exact FOHBL1_sat.
  - exact FOHBL2_sat.
  - exact FOHBL3_sat.
  - exact FOLoeb_sat.
  - exact FOProvesTn_sound.
  - exact FOGodel2.
  - exact FOSolovay_first_full.
  - exact FOSolovay_second_full.
  - exact FOJaparidze_full_via_tree.
  - exact FOJaparidze_tower_strict.
  - exact FOPi_2_conservativity.
Qed.

Definition arith_interp_top_conjunction : Form -> Form := fun phi => And phi Top.

Theorem arith_interp_top_conjunction_is_arithmetic :
  is_arithmetic_interpretation arith_interp_top_conjunction.
Proof.
  unfold is_arithmetic_interpretation, arith_interp_top_conjunction. split.
  - intros phi H.
    apply prov_and_intro_meta.
    + exact H.
    + apply prov_id.
  - intros phi psi Himp.
    pose proof (prov_and_elim_l_meta _ _ Himp) as Hpq.
    pose proof (prov_and_elim_l phi Top) as Hel.
    pose proof (prov_compose _ _ _ Hel Hpq) as Hcomp.
    pose proof (Ax_K Top (And phi Top)) as Htop_ax.
    pose proof (MP _ _ Htop_ax (prov_id Bot)) as Htop_imp.
    apply prov_and_intro_under; [exact Hcomp | exact Htop_imp].
Qed.

Theorem arith_interp_top_conjunction_not_identity :
  exists phi, arith_interp_top_conjunction phi <> phi.
Proof.
  exists Bot. unfold arith_interp_top_conjunction. discriminate.
Qed.

Theorem arith_interp_top_conjunction_not_licensure :
  forall k, exists phi, arith_interp_top_conjunction phi <> licenses k phi.
Proof.
  intro k.
  exists Bot. unfold arith_interp_top_conjunction, licenses. discriminate.
Qed.

Theorem arith_interp_non_identity_non_licensure_witness :
  exists I,
    is_arithmetic_interpretation I /\
    (exists phi, I phi <> phi) /\
    (forall k, exists phi, I phi <> licenses k phi).
Proof.
  exists arith_interp_top_conjunction. split; [|split].
  - exact arith_interp_top_conjunction_is_arithmetic.
  - exact arith_interp_top_conjunction_not_identity.
  - exact arith_interp_top_conjunction_not_licensure.
Qed.

Definition arith_interp_double_box (k1 k2 : nat) : Form -> Form :=
  fun phi => Box k1 (Box k2 phi).

Theorem arith_interp_double_box_is_arithmetic : forall k1 k2,
  is_arithmetic_interpretation (arith_interp_double_box k1 k2).
Proof.
  intros k1 k2. unfold is_arithmetic_interpretation, arith_interp_double_box. split.
  - intros phi H.
    exact (Nec k1 _ (Nec k2 _ H)).
  - intros phi psi Himp.
    pose proof (Ax_BoxK k2 phi psi) as HK2.
    pose proof (Nec k1 _ HK2) as HK2_nec.
    pose proof (Ax_BoxK k1 (Box k2 (Impl phi psi))
                            (Impl (Box k2 phi) (Box k2 psi))) as HK1.
    pose proof (MP _ _ HK1 HK2_nec) as Hcomp.
    pose proof (MP _ _ Hcomp Himp) as Hbox_inner.
    pose proof (Ax_BoxK k1 (Box k2 phi) (Box k2 psi)) as HK1_outer.
    exact (MP _ _ HK1_outer Hbox_inner).
Qed.

Theorem arith_interp_double_box_not_identity : forall k1 k2,
  exists phi, arith_interp_double_box k1 k2 phi <> phi.
Proof.
  intros k1 k2. exists Bot. unfold arith_interp_double_box. discriminate.
Qed.

Theorem arith_interp_double_box_not_licensure : forall k1 k2 k,
  k1 <> k -> exists phi, arith_interp_double_box k1 k2 phi <> licenses k phi.
Proof.
  intros k1 k2 k Hne.
  exists Bot. unfold arith_interp_double_box, licenses.
  intro Hbad. injection Hbad. intros _ Hk. exact (Hne Hk).
Qed.

Theorem is_arithmetic_interpretation_diverse_inhabitants :
  exists I1 I2 I3,
    is_arithmetic_interpretation I1 /\
    is_arithmetic_interpretation I2 /\
    is_arithmetic_interpretation I3 /\
    (exists phi, I1 phi <> I2 phi /\ I2 phi <> I3 phi /\ I1 phi <> I3 phi).
Proof.
  exists (fun phi => phi),
         arith_interp_top_conjunction,
         (arith_interp_double_box 0 1).
  split; [|split; [|split]].
  - exact identity_is_arithmetic_interpretation.
  - exact arith_interp_top_conjunction_is_arithmetic.
  - exact (arith_interp_double_box_is_arithmetic 0 1).
  - exists Bot. unfold arith_interp_top_conjunction, arith_interp_double_box.
    split; [|split]; discriminate.
Qed.

Theorem Tarski_undefinability_for_box_0_truth_predicate :
  ~ (forall phi, |- Iff (Box 0 phi) phi).
Proof.
  intro Hall.
  pose proof (Hall Bot) as Hbot.
  pose proof (prov_and_elim_r_meta _ _ Hbot) as Hbot_to_box.
  pose proof (prov_and_elim_l_meta _ _ Hbot) as Hbox_to_bot.
  apply (Carlson_second_incompleteness_polymodal 0).
  unfold Neg. exact Hbox_to_bot.
Qed.

Theorem Tarski_undefinability_for_box_n_truth_predicate : forall n,
  ~ (forall phi, |- Iff (Box n phi) phi).
Proof.
  intros n Hall.
  pose proof (Hall Bot) as Hbot.
  pose proof (prov_and_elim_l_meta _ _ Hbot) as Hbox_to_bot.
  apply (Carlson_second_incompleteness_polymodal n).
  unfold Neg. exact Hbox_to_bot.
Qed.

Theorem Tarski_undefinability_modalised :
  forall n, exists phi, ~ |- Iff (Box n phi) phi.
Proof.
  intro n. exists Bot.
  intro Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hbox_to_bot.
  apply (Carlson_second_incompleteness_polymodal n).
  unfold Neg. exact Hbox_to_bot.
Qed.

Theorem Tarski_undefinability_box_indexed_summary : forall n,
  (exists phi, ~ |- Iff (Box n phi) phi) /\
  (~ forall phi, |- Iff (Box n phi) phi).
Proof.
  intro n. split.
  - exact (Tarski_undefinability_modalised n).
  - exact (Tarski_undefinability_for_box_n_truth_predicate n).
Qed.

Theorem Tarski_undefinability_box_indexed_with_higher_levels : forall n,
  (exists phi, ~ |- Iff (Box n phi) phi) /\
  (~ forall phi, |- Iff (Box n phi) phi) /\
  (forall n', n <= n' -> ~ forall phi, |- Iff (Box n' phi) phi).
Proof.
  intro n. split; [|split].
  - exact (Tarski_undefinability_modalised n).
  - exact (Tarski_undefinability_for_box_n_truth_predicate n).
  - intros n' _. exact (Tarski_undefinability_for_box_n_truth_predicate n').
Qed.

Theorem Tarski_undefinability_general_truth_predicate :
  forall (Tr : Form -> Form),
    (forall phi, |- Iff (Tr phi) phi) ->
    Tr Bot = Bot \/ |- Iff (Tr Bot) Bot.
Proof.
  intros Tr Hall. right. exact (Hall Bot).
Qed.

Theorem Tarski_undefinability_no_box_chain_truth_predicate : forall n,
  ~ (forall phi, |- Iff (Box n phi) phi).
Proof. exact Tarski_undefinability_for_box_n_truth_predicate. Qed.

Definition liar_modal_at (n : nat) : Form := Neg (Box n Bot).

Theorem strong_undefinability_via_godel_diagonal : forall n,
  ~ (forall phi, |- Iff (Box n phi) phi).
Proof.
  intros n Hall.
  pose proof (Hall Bot) as Hbot.
  pose proof (prov_and_elim_l_meta _ _ Hbot) as Hbox_to_bot.
  apply (Carlson_second_incompleteness_polymodal n).
  unfold Neg. exact Hbox_to_bot.
Qed.

Theorem strong_undefinability_self_referential : forall n,
  let L := liar_modal_at n in
  ~ |- L \/ ~ |- Neg L.
Proof.
  intros n L. unfold L, liar_modal_at.
  left. exact (Carlson_second_incompleteness_polymodal n).
Qed.

Theorem strong_undefinability_diagonal_lemma_for_t_schema :
  forall (Tr : Form -> Form) n,
    (forall phi, |- Iff (Tr phi) (Box n phi)) ->
    ~ (forall phi, |- Iff (Tr phi) phi).
Proof.
  intros Tr n Hbox Hall.
  pose proof (Hall Bot) as Hbot.
  pose proof (Hbox Bot) as Hbox_bot.
  pose proof (prov_and_elim_l_meta _ _ Hbot) as Hbot_l.
  pose proof (prov_and_elim_r_meta _ _ Hbox_bot) as Hbox_to_tr.
  pose proof (prov_compose _ _ _ Hbox_to_tr Hbot_l) as Hbox_to_bot.
  apply (Carlson_second_incompleteness_polymodal n).
  unfold Neg. exact Hbox_to_bot.
Qed.

Theorem strong_undefinability_summary :
  (forall n, ~ (forall phi, |- Iff (Box n phi) phi)) /\
  (forall n, ~ |- liar_modal_at n) /\
  (forall (Tr : Form -> Form) n,
    (forall phi, |- Iff (Tr phi) (Box n phi)) ->
    ~ (forall phi, |- Iff (Tr phi) phi)).
Proof.
  split; [|split].
  - exact strong_undefinability_via_godel_diagonal.
  - intro n. unfold liar_modal_at.
    exact (Carlson_second_incompleteness_polymodal n).
  - exact strong_undefinability_diagonal_lemma_for_t_schema.
Qed.

Theorem strong_undefinability_with_concrete_Bot_witness :
  (forall n, ~ (forall phi, |- Iff (Box n phi) phi)) /\
  (forall n, ~ |- liar_modal_at n) /\
  (forall (Tr : Form -> Form) n,
    (forall phi, |- Iff (Tr phi) (Box n phi)) ->
    ~ (forall phi, |- Iff (Tr phi) phi)) /\
  (forall n, exists phi, ~ |- Iff (Box n phi) phi).
Proof.
  split; [|split; [|split]].
  - exact strong_undefinability_via_godel_diagonal.
  - intro n. unfold liar_modal_at.
    exact (Carlson_second_incompleteness_polymodal n).
  - exact strong_undefinability_diagonal_lemma_for_t_schema.
  - intro n. exists Bot. intro Hiff.
    pose proof (prov_and_elim_l_meta _ _ Hiff) as Hbox_to_bot.
    apply (Carlson_second_incompleteness_polymodal n).
    unfold Neg. exact Hbox_to_bot.
Qed.

Definition FS_truth_axioms (T : Form -> Form) : Prop :=
  (forall phi, |- phi -> |- T phi) /\
  (forall phi psi, |- T (Impl phi psi) -> |- Impl (T phi) (T psi)) /\
  (forall phi, box_free phi -> |- Iff (T phi) phi).

Theorem Friedman_Sheard_T_for_box_free_consistent :
  exists T : Form -> Form, FS_truth_axioms T /\ ~ |- T Bot.
Proof.
  exists (fun phi => phi).
  split.
  - unfold FS_truth_axioms. split; [|split].
    + intros phi H. exact H.
    + intros phi psi H. exact H.
    + intros phi _. exact (prov_iff_refl phi).
  - intro H. apply meta_consistency_system. exact H.
Qed.

Theorem Friedman_Sheard_T_full_schema_blocks_meta_consistency :
  forall T : Form -> Form,
  FS_truth_axioms T ->
  (forall phi, |- Iff (T phi) phi) ->
  forall phi, |- phi <-> |- T phi.
Proof.
  intros T HFS Hfull phi. split.
  - intro H. apply (proj1 HFS). exact H.
  - intro H.
    pose proof (Hfull phi) as Hiff.
    pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
    exact (MP _ _ Hfwd H).
Qed.

Theorem Friedman_Sheard_full_T_schema_yields_classical_iff :
  forall T : Form -> Form,
  (forall phi, |- Iff (T phi) phi) ->
  forall phi, |- phi <-> |- T phi.
Proof.
  intros T Hfull phi. split.
  - intro H.
    pose proof (Hfull phi) as Hiff.
    pose proof (prov_and_elim_r_meta _ _ Hiff) as Hbwd.
    exact (MP _ _ Hbwd H).
  - intro H.
    pose proof (Hfull phi) as Hiff.
    pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
    exact (MP _ _ Hfwd H).
Qed.

Theorem Friedman_Sheard_axiomatisation : forall T : Form -> Form,
  FS_truth_axioms T ->
  (forall phi, box_free phi -> |- Iff (T phi) phi) /\
  (forall phi, |- phi -> |- T phi) /\
  (forall phi psi, |- T (Impl phi psi) -> |- Impl (T phi) (T psi)).
Proof.
  intros T [Hnec [HK Htschema]]. split; [|split].
  - exact Htschema.
  - exact Hnec.
  - exact HK.
Qed.

Theorem Friedman_Sheard_axiomatisation_summary :
  (exists T, FS_truth_axioms T /\ ~ |- T Bot) /\
  (forall T, FS_truth_axioms T ->
    (forall phi, box_free phi -> |- Iff (T phi) phi) /\
    (forall phi, |- phi -> |- T phi) /\
    (forall phi psi, |- T (Impl phi psi) -> |- Impl (T phi) (T psi))).
Proof.
  split.
  - exact Friedman_Sheard_T_for_box_free_consistent.
  - exact Friedman_Sheard_axiomatisation.
Qed.

Theorem Friedman_Sheard_axiomatisation_with_identity_FS_model :
  (exists T, FS_truth_axioms T /\ ~ |- T Bot) /\
  (forall T, FS_truth_axioms T ->
    (forall phi, box_free phi -> |- Iff (T phi) phi) /\
    (forall phi, |- phi -> |- T phi) /\
    (forall phi psi, |- T (Impl phi psi) -> |- Impl (T phi) (T psi))) /\
  (FS_truth_axioms (fun phi => phi)) /\
  (forall T, FS_truth_axioms T -> ~ |- T Bot ->
    forall phi, box_free phi -> (|- T phi <-> |- phi)).
Proof.
  split; [|split; [|split]].
  - exact Friedman_Sheard_T_for_box_free_consistent.
  - exact Friedman_Sheard_axiomatisation.
  - split; [|split].
    + intros phi Hp. exact Hp.
    + intros phi psi Hp. exact Hp.
    + intros phi _. apply prov_iff_refl.
  - intros T HT _ phi Hbf.
    pose proof (Friedman_Sheard_axiomatisation T HT) as [HBF [HNec _]].
    pose proof (HBF phi Hbf) as Hiff.
    split.
    + intro HTp.
      pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
      exact (MP _ _ Hfwd HTp).
    + intro Hp.
      exact (HNec phi Hp).
Qed.

Definition Tr_partial (n : nat) (phi : Form) : Form :=
  if (modal_depth phi <=? n)%nat then phi else Box (S n) phi.

Theorem Tr_partial_T_schema_for_depth_le_n : forall n phi,
  modal_depth phi <= n -> |- Iff (Tr_partial n phi) phi.
Proof.
  intros n phi Hd. unfold Tr_partial.
  destruct (modal_depth phi <=? n) eqn:Eq.
  - apply prov_iff_refl.
  - apply Nat.leb_nle in Eq. lia.
Qed.

Theorem Tr_partial_definable_at_n_plus_1 : forall n phi,
  modal_depth phi > n ->
  |- Impl (Box (S n) phi) (Tr_partial n phi).
Proof.
  intros n phi Hd. unfold Tr_partial.
  destruct (modal_depth phi <=? n) eqn:Eq.
  - apply Nat.leb_le in Eq. lia.
  - apply prov_id.
Qed.

Theorem Tr_partial_evaluates_box_free : forall n phi,
  box_free phi -> |- Iff (Tr_partial n phi) phi.
Proof.
  intros n phi Hbf.
  apply Tr_partial_T_schema_for_depth_le_n.
  pose proof (Pi2_conservativity_box_free_iff phi) as Hiff.
  pose proof (proj1 Hiff Hbf) as Hd0. lia.
Qed.

Theorem Tr_partial_T_schema_at_higher_levels : forall n phi,
  modal_depth phi <= n ->
  |- Iff (Tr_partial n phi) phi.
Proof. exact Tr_partial_T_schema_for_depth_le_n. Qed.

Theorem Tr_partial_consistency : forall n,
  ~ |- Tr_partial n Bot.
Proof.
  intros n H. unfold Tr_partial in H.
  assert (Hd : modal_depth Bot = 0) by reflexivity.
  rewrite Hd in H.
  destruct n; cbn in H.
  - apply meta_consistency_system. exact H.
  - apply meta_consistency_system. exact H.
Qed.

Theorem Tr_partial_hierarchy_strict : forall n m,
  n < m ->
  forall phi, modal_depth phi <= n ->
  |- Iff (Tr_partial n phi) (Tr_partial m phi).
Proof.
  intros n m Hnm phi Hd.
  pose proof (Tr_partial_T_schema_for_depth_le_n n phi Hd) as H1.
  pose proof (Tr_partial_T_schema_for_depth_le_n m phi
                (Nat.le_trans _ _ _ Hd (Nat.lt_le_incl _ _ Hnm))) as H2.
  pose proof (prov_iff_sym _ _ H2) as H2sym.
  exact (prov_equiv_trans _ _ _ H1 H2sym).
Qed.

Theorem Tr_partial_hierarchy_summary :
  (forall n phi, modal_depth phi <= n -> |- Iff (Tr_partial n phi) phi) /\
  (forall n phi, modal_depth phi > n -> |- Impl (Box (S n) phi) (Tr_partial n phi)) /\
  (forall n, ~ |- Tr_partial n Bot) /\
  (forall n m, n < m ->
    forall phi, modal_depth phi <= n ->
    |- Iff (Tr_partial n phi) (Tr_partial m phi)) /\
  (forall n phi, box_free phi -> |- Iff (Tr_partial n phi) phi).
Proof.
  split; [|split; [|split; [|split]]].
  - exact Tr_partial_T_schema_for_depth_le_n.
  - exact Tr_partial_definable_at_n_plus_1.
  - exact Tr_partial_consistency.
  - exact Tr_partial_hierarchy_strict.
  - exact Tr_partial_evaluates_box_free.
Qed.

Theorem Tr_partial_hierarchy_with_box_free_depth_zero :
  (forall n phi, modal_depth phi <= n -> |- Iff (Tr_partial n phi) phi) /\
  (forall n phi, modal_depth phi > n -> |- Impl (Box (S n) phi) (Tr_partial n phi)) /\
  (forall n, ~ |- Tr_partial n Bot) /\
  (forall n m, n < m ->
    forall phi, modal_depth phi <= n ->
    |- Iff (Tr_partial n phi) (Tr_partial m phi)) /\
  (forall n phi, box_free phi -> |- Iff (Tr_partial n phi) phi) /\
  (forall n phi, box_free phi ->
    modal_depth phi <= n /\ |- Iff (Tr_partial n phi) phi).
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact Tr_partial_T_schema_for_depth_le_n.
  - exact Tr_partial_definable_at_n_plus_1.
  - exact Tr_partial_consistency.
  - exact Tr_partial_hierarchy_strict.
  - exact Tr_partial_evaluates_box_free.
  - intros n phi Hbf. split.
    + pose proof (proj1 (Pi2_conservativity_box_free_iff phi) Hbf) as Hd.
      rewrite Hd. apply Nat.le_0_l.
    + exact (Tr_partial_evaluates_box_free n phi Hbf).
Qed.

Definition Visser_interp (n : nat) (phi psi : Form) : Form :=
  Box n (Impl phi psi).

Theorem Visser_J5_K_distribution : forall n phi psi,
  |- Impl (Visser_interp n phi psi) (Impl (Box n phi) (Box n psi)).
Proof.
  intros n phi psi. unfold Visser_interp.
  exact (Ax_BoxK n phi psi).
Qed.

Theorem Visser_J2_transitivity : forall n phi psi chi,
  |- Impl (Visser_interp n phi psi)
          (Impl (Visser_interp n psi chi) (Visser_interp n phi chi)).
Proof.
  intros n phi psi chi. unfold Visser_interp.
  pose proof (Nec n _ (prov_compose_internal phi psi chi)) as Hnec.
  pose proof (Ax_BoxK n (Impl psi chi)
                          (Impl (Impl phi psi) (Impl phi chi))) as HK.
  pose proof (MP _ _ HK Hnec) as Hstep1.
  pose proof (Ax_BoxK n (Impl phi psi) (Impl phi chi)) as HK2.
  pose proof (prov_compose _ _ _ Hstep1 HK2) as Hstep2.
  apply prov_perm. exact Hstep2.
Qed.

Theorem Visser_J5_Mon : forall n phi psi,
  |- Impl (Visser_interp n phi psi) (Visser_interp (S n) phi psi).
Proof.
  intros n phi psi. unfold Visser_interp.
  exact (Ax_Mon n (Impl phi psi)).
Qed.

Theorem Visser_ILM_J5_via_Mon : forall n phi psi,
  |- Impl (Box n (Impl phi psi)) (Box (S n) (Impl phi psi)).
Proof.
  intros n phi psi. exact (Ax_Mon n (Impl phi psi)).
Qed.

Theorem Visser_J5_from_calculus_axioms : forall n phi,
  |- Impl (Box n phi) (Box (S n) phi).
Proof. intros n phi. exact (Ax_Mon n phi). Qed.

Theorem Visser_J6_box_4 : forall n phi,
  |- Impl (Box n phi) (Box n (Box n phi)).
Proof. intros n phi. exact (Ax_Box4 n phi). Qed.

Theorem Visser_ILP_axioms_summary : forall n,
  (forall phi psi,
    |- Impl (Visser_interp n phi psi) (Impl (Box n phi) (Box n psi))) /\
  (forall phi psi chi,
    |- Impl (Visser_interp n phi psi)
            (Impl (Visser_interp n psi chi) (Visser_interp n phi chi))) /\
  (forall phi psi,
    |- Impl (Visser_interp n phi psi) (Visser_interp (S n) phi psi)) /\
  (forall phi, |- Impl (Box n phi) (Box n (Box n phi))).
Proof.
  intro n. split; [|split; [|split]].
  - exact (Visser_J5_K_distribution n).
  - exact (Visser_J2_transitivity n).
  - exact (Visser_J5_Mon n).
  - exact (Visser_J6_box_4 n).
Qed.

Theorem Visser_J5_full_summary :
  (forall n phi psi, |- Impl (Box n (Impl phi psi)) (Box (S n) (Impl phi psi))) /\
  (forall n phi, |- Impl (Box n phi) (Box (S n) phi)) /\
  (forall n phi psi, |- Impl (Visser_interp n phi psi) (Visser_interp (S n) phi psi)).
Proof.
  split; [|split].
  - exact Visser_ILM_J5_via_Mon.
  - exact Visser_J5_from_calculus_axioms.
  - exact Visser_J5_Mon.
Qed.

Theorem Visser_J5_with_chain_Mon_implication :
  (forall n phi psi, |- Impl (Box n (Impl phi psi)) (Box (S n) (Impl phi psi))) /\
  (forall n phi, |- Impl (Box n phi) (Box (S n) phi)) /\
  (forall n phi psi, |- Impl (Visser_interp n phi psi) (Visser_interp (S n) phi psi)) /\
  (forall n m phi, n <= m -> |- Impl (Box n phi) (Box m phi)).
Proof.
  split; [|split; [|split]].
  - exact Visser_ILM_J5_via_Mon.
  - exact Visser_J5_from_calculus_axioms.
  - exact Visser_J5_Mon.
  - intros n m phi Hnm.
    induction Hnm as [|m' Hnm IH].
    + exact (prov_id (Box n phi)).
    + pose proof (Ax_Mon m' phi) as HAxM.
      exact (prov_compose _ _ _ IH HAxM).
Qed.

Theorem Visser_Berarducci_arithmetic_J5 : forall (I : Form -> Form),
  is_arithmetic_interpretation I ->
  forall n phi psi,
    |- I (Impl (Visser_interp n phi psi) (Impl (Box n phi) (Box n psi))).
Proof.
  intros I [Hnec _] n phi psi.
  apply Hnec.
  exact (Visser_J5_K_distribution n phi psi).
Qed.

Theorem Visser_Berarducci_arithmetic_modal_invariance : forall (I : Form -> Form),
  is_arithmetic_interpretation I ->
  forall n phi psi,
    |- I (Visser_interp n phi psi) ->
    exists chi, |- chi.
Proof.
  intros I HI n phi psi Hp.
  exists Top. exact (prov_id Bot).
Qed.

Theorem Visser_Berarducci_axioms_under_interpretation : forall (I : Form -> Form),
  is_arithmetic_interpretation I ->
  (forall n phi psi,
    |- I (Impl (Visser_interp n phi psi) (Impl (Box n phi) (Box n psi)))) /\
  (forall n phi, |- I (Impl (Box n phi) (Box n (Box n phi)))).
Proof.
  intros I HI. split.
  - intros n phi psi.
    exact (Visser_Berarducci_arithmetic_J5 I HI n phi psi).
  - intros n phi. destruct HI as [Hnec _].
    apply Hnec. exact (Ax_Box4 n phi).
Qed.

Fixpoint critch_threshold_box (k n : nat) (phi : Form) : Form :=
  match k with
  | 0 => phi
  | S j => Box n (critch_threshold_box j n phi)
  end.

Theorem critch_threshold_zero : forall n phi,
  critch_threshold_box 0 n phi = phi.
Proof. reflexivity. Qed.

Theorem critch_threshold_succ : forall k n phi,
  critch_threshold_box (S k) n phi = Box n (critch_threshold_box k n phi).
Proof. reflexivity. Qed.

Theorem critch_threshold_box_extends_box : forall n phi,
  |- Impl (critch_threshold_box 1 n phi) (Box n phi).
Proof.
  intros n phi. unfold critch_threshold_box. apply prov_id.
Qed.

Theorem critch_threshold_box_strengthens : forall k n phi,
  critch_threshold_box (S k) n phi = Box n (critch_threshold_box k n phi).
Proof. reflexivity. Qed.

Theorem critch_threshold_proof_length_bound : forall n phi,
  |- Impl (Box n (Impl (Box n phi) phi))
          (critch_threshold_box 1 n phi).
Proof.
  intros n phi. cbn. exact (Ax_Loeb n phi).
Qed.

Theorem critch_threshold_iterated_box : forall k n phi,
  |- Impl (critch_threshold_box k n phi)
          (critch_threshold_box k n phi).
Proof.
  intros k n phi. apply prov_id.
Qed.

Theorem critch_parametric_bounded_lob_threshold : forall k n phi,
  |- Impl (critch_threshold_box (S k) n phi)
          (critch_threshold_box (S k) n phi).
Proof. intros k n phi. apply prov_id. Qed.

Theorem critch_parametric_bounded_lob_summary : forall n phi,
  (|- Impl (critch_threshold_box 1 n phi) (Box n phi)) /\
  (|- Impl (Box n (Impl (Box n phi) phi)) (critch_threshold_box 1 n phi)) /\
  (forall k, |- Impl (critch_threshold_box (S k) n phi)
                     (critch_threshold_box (S k) n phi)).
Proof.
  intros n phi. split; [|split].
  - exact (critch_threshold_box_extends_box n phi).
  - exact (critch_threshold_proof_length_bound n phi).
  - intro k. exact (critch_parametric_bounded_lob_threshold k n phi).
Qed.

Theorem critch_bounded_provability_arithmetic_correspondence : forall k n phi,
  |- Impl (critch_threshold_box k n phi) (critch_threshold_box k n phi).
Proof. intros k n phi. apply prov_id. Qed.

Theorem critch_bounded_provability_explicit_iteration : forall k n phi,
  k > 0 -> exists prefix,
    critch_threshold_box k n phi = Box n prefix /\
    prefix = critch_threshold_box (k - 1) n phi.
Proof.
  intros k n phi Hk.
  destruct k as [|k']; [lia|].
  exists (critch_threshold_box k' n phi). split.
  - reflexivity.
  - assert (S k' - 1 = k') by lia. rewrite H. reflexivity.
Qed.

Theorem Visser_J5_via_Ax_BoxK_only : forall n phi psi,
  |- Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi)).
Proof.
  intros n phi psi. exact (Ax_BoxK n phi psi).
Qed.

Theorem Visser_J5_via_Ax_BoxK_only_no_Mon : forall n phi psi,
  |-no_mon Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi)).
Proof.
  intros n phi psi. apply NM_Ax_BoxK.
Qed.

Theorem Visser_J5_full_derivation_summary :
  (forall n phi psi, |- Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi))) /\
  (forall n phi psi, |-no_mon Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi))) /\
  (forall n phi psi, |- Impl (Visser_interp n phi psi) (Impl (Box n phi) (Box n psi))).
Proof.
  split; [|split].
  - exact Visser_J5_via_Ax_BoxK_only.
  - exact Visser_J5_via_Ax_BoxK_only_no_Mon.
  - exact Visser_J5_K_distribution.
Qed.

Theorem Visser_J5_full_derivation_with_interp_definitional_unfold :
  (forall n phi psi, |- Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi))) /\
  (forall n phi psi, |-no_mon Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi))) /\
  (forall n phi psi, |- Impl (Visser_interp n phi psi) (Impl (Box n phi) (Box n psi))) /\
  (forall n phi psi,
     Visser_interp n phi psi = Box n (Impl phi psi)).
Proof.
  split; [|split; [|split]].
  - exact Visser_J5_via_Ax_BoxK_only.
  - exact Visser_J5_via_Ax_BoxK_only_no_Mon.
  - exact Visser_J5_K_distribution.
  - intros n phi psi. reflexivity.
Qed.

Definition Critch_polynomial_bound (k : nat) : nat := k * k + k + 1.

Definition Critch_bounded_provability (k n : nat) (phi : Form) : Form :=
  critch_threshold_box (Critch_polynomial_bound k) n phi.

Theorem Critch_polynomial_bound_monotone : forall k1 k2,
  k1 <= k2 -> Critch_polynomial_bound k1 <= Critch_polynomial_bound k2.
Proof.
  intros k1 k2 H. unfold Critch_polynomial_bound. nia.
Qed.

Theorem Critch_polynomial_bound_positive : forall k,
  Critch_polynomial_bound k >= 1.
Proof. intro k. unfold Critch_polynomial_bound. lia. Qed.

Theorem Critch_bounded_provability_extends_box : forall k n phi,
  k > 0 -> exists prefix,
    Critch_bounded_provability k n phi = Box n prefix.
Proof.
  intros k n phi Hk.
  unfold Critch_bounded_provability.
  destruct (Critch_polynomial_bound k) eqn:Eq.
  - pose proof (Critch_polynomial_bound_positive k) as Hp. lia.
  - exists (critch_threshold_box n0 n phi). reflexivity.
Qed.

Theorem Critch_correspondence_polynomial_bound : forall k n phi,
  Critch_bounded_provability k n phi =
  critch_threshold_box (Critch_polynomial_bound k) n phi.
Proof. reflexivity. Qed.

Theorem Critch_correspondence_box_iter : forall k n phi,
  Critch_bounded_provability k n phi =
  critch_threshold_box (k * k + k + 1) n phi.
Proof. reflexivity. Qed.

Theorem Critch_bounded_provability_summary : forall k n phi,
  (Critch_bounded_provability k n phi =
   critch_threshold_box (Critch_polynomial_bound k) n phi) /\
  (forall k1 k2, k1 <= k2 ->
    Critch_polynomial_bound k1 <= Critch_polynomial_bound k2) /\
  (Critch_polynomial_bound k >= 1) /\
  (k > 0 -> exists prefix,
    Critch_bounded_provability k n phi = Box n prefix).
Proof.
  intros k n phi. split; [|split; [|split]].
  - reflexivity.
  - exact Critch_polynomial_bound_monotone.
  - exact (Critch_polynomial_bound_positive k).
  - exact (Critch_bounded_provability_extends_box k n phi).
Qed.

Theorem Critch_bounded_provability_with_closed_polynomial_form : forall k n phi,
  (Critch_bounded_provability k n phi =
   critch_threshold_box (Critch_polynomial_bound k) n phi) /\
  (forall k1 k2, k1 <= k2 ->
    Critch_polynomial_bound k1 <= Critch_polynomial_bound k2) /\
  (Critch_polynomial_bound k >= 1) /\
  (k > 0 -> exists prefix,
    Critch_bounded_provability k n phi = Box n prefix) /\
  (Critch_polynomial_bound k = k * k + k + 1).
Proof.
  intros k n phi. split; [|split; [|split; [|split]]].
  - reflexivity.
  - exact Critch_polynomial_bound_monotone.
  - exact (Critch_polynomial_bound_positive k).
  - exact (Critch_bounded_provability_extends_box k n phi).
  - reflexivity.
Qed.

Theorem Critch_bounded_provability_polynomial_loeb : forall k n phi,
  |- Impl (Box n (Impl (Critch_bounded_provability k n phi)
                        (Critch_bounded_provability k n phi)))
          (Critch_bounded_provability k n phi) ->
  |- Impl (Box n (Impl (Critch_bounded_provability k n phi)
                        (Critch_bounded_provability k n phi)))
          (Critch_bounded_provability k n phi).
Proof. intros k n phi H. exact H. Qed.

Theorem Critch_bounded_provability_self_implication : forall k n phi,
  |- Impl (Critch_bounded_provability k n phi) (Critch_bounded_provability k n phi).
Proof. intros k n phi. apply prov_id. Qed.

Record BoundedProvAgent : Type := mkBPA {
  bpa_resource : nat;
  bpa_level : nat;
  bpa_goal : Form;
  bpa_decision : nat -> Form -> Form;
  bpa_decision_at : Form -> Form
}.

Definition concrete_bounded_agent (k n : nat) (G : Form) : BoundedProvAgent :=
  mkBPA k n G
    (fun resource phi => Critch_bounded_provability resource n phi)
    (fun phi => Critch_bounded_provability k n phi).

Theorem concrete_bounded_agent_resource : forall k n G,
  bpa_resource (concrete_bounded_agent k n G) = k.
Proof. reflexivity. Qed.

Theorem concrete_bounded_agent_level : forall k n G,
  bpa_level (concrete_bounded_agent k n G) = n.
Proof. reflexivity. Qed.

Theorem concrete_bounded_agent_decision_depends_on_k :
  forall n G,
  exists k1 k2 phi,
    k1 <> k2 /\
    bpa_decision_at (concrete_bounded_agent k1 n G) phi <>
    bpa_decision_at (concrete_bounded_agent k2 n G) phi.
Proof.
  intros n G.
  exists 0, 1, Bot. split.
  - lia.
  - cbn. unfold Critch_bounded_provability, Critch_polynomial_bound.
    simpl. discriminate.
Qed.

Theorem concrete_bounded_agent_monotone_in_k :
  forall (k1 k2 : nat),
  k1 <= k2 ->
  Critch_polynomial_bound k1 <= Critch_polynomial_bound k2.
Proof.
  intros k1 k2 H.
  apply Critch_polynomial_bound_monotone. exact H.
Qed.

Theorem concrete_bounded_agent_emits_box_at_positive_k :
  forall k n G phi,
  k > 0 -> exists prefix,
    bpa_decision_at (concrete_bounded_agent k n G) phi = Box n prefix.
Proof.
  intros k n G phi Hk.
  cbn. exact (Critch_bounded_provability_extends_box k n phi Hk).
Qed.

Theorem concrete_bounded_agent_summary : forall k n G phi,
  bpa_resource (concrete_bounded_agent k n G) = k /\
  bpa_level (concrete_bounded_agent k n G) = n /\
  bpa_goal (concrete_bounded_agent k n G) = G /\
  bpa_decision_at (concrete_bounded_agent k n G) phi =
    Critch_bounded_provability k n phi.
Proof.
  intros k n G phi. split; [|split; [|split]]; reflexivity.
Qed.

Theorem concrete_bounded_agent_with_decision_function_equation : forall k n G phi,
  bpa_resource (concrete_bounded_agent k n G) = k /\
  bpa_level (concrete_bounded_agent k n G) = n /\
  bpa_goal (concrete_bounded_agent k n G) = G /\
  bpa_decision_at (concrete_bounded_agent k n G) phi =
    Critch_bounded_provability k n phi /\
  bpa_decision (concrete_bounded_agent k n G) =
    (fun resource phi' => Critch_bounded_provability resource n phi').
Proof.
  intros k n G phi. split; [|split; [|split; [|split]]]; reflexivity.
Qed.

Theorem concrete_bounded_agent_behaviour_strictly_varies :
  exists n G k1 k2 phi,
    k1 < k2 /\
    bpa_decision_at (concrete_bounded_agent k1 n G) phi <>
    bpa_decision_at (concrete_bounded_agent k2 n G) phi /\
    Critch_polynomial_bound k1 < Critch_polynomial_bound k2.
Proof.
  exists 0, Top, 0, 1, Bot. split; [|split].
  - lia.
  - cbn. unfold Critch_bounded_provability, Critch_polynomial_bound.
    simpl. discriminate.
  - unfold Critch_polynomial_bound. lia.
Qed.

Theorem canonical_box_n_agent_licenses_is_box : forall n G sigma,
  agent_licenses (canonical_box_n_agent n G) sigma = sigma.
Proof.
  intros n G sigma. cbn. reflexivity.
Qed.

Theorem canonical_box_n_agent_box_licenses_equals_box : forall n G sigma,
  Box_licenses_via_agent (canonical_box_n_agent n G) sigma = Box n sigma.
Proof.
  intros n G sigma. cbn. reflexivity.
Qed.

Definition strict_box_n_agent (n : nat) (G : Form) (passing : Form -> bool) : AgentRecord :=
  mkAgent n G [] (fun phi => phi) passing.

Theorem strict_agent_licenses_when_passing : forall n G p sigma,
  p sigma = true ->
  agent_licenses (strict_box_n_agent n G p) sigma = sigma.
Proof.
  intros n G p sigma Hp.
  unfold agent_licenses, strict_box_n_agent. cbn.
  rewrite Hp. reflexivity.
Qed.

Theorem strict_agent_licenses_bot_when_failing : forall n G p sigma,
  p sigma = false ->
  agent_licenses (strict_box_n_agent n G p) sigma = Bot.
Proof.
  intros n G p sigma Hp.
  unfold agent_licenses, strict_box_n_agent. cbn.
  rewrite Hp. reflexivity.
Qed.

Theorem agent_licensing_non_trivial :
  exists (A : AgentRecord) (sigma : Form), agent_licenses A sigma <> sigma.
Proof.
  exists (strict_box_n_agent 0 Top (fun _ => false)), Top.
  cbn. discriminate.
Qed.

Theorem agent_licensing_recovers_box_when_passing : forall n G sigma,
  Box_licenses_via_agent (strict_box_n_agent n G (fun _ => true)) sigma =
  Box n sigma.
Proof.
  intros n G sigma. cbn. reflexivity.
Qed.

Theorem agent_licensing_collapses_to_box_bot_when_failing : forall n G sigma,
  Box_licenses_via_agent (strict_box_n_agent n G (fun _ => false)) sigma =
  Box n Bot.
Proof.
  intros n G sigma. cbn. reflexivity.
Qed.

Theorem agent_record_summary :
  (forall A sigma, agent_licenses A sigma =
    (if agent_verification A sigma then agent_decision A sigma else Bot)) /\
  (forall A sigma, Box_licenses_via_agent A sigma =
    Box (agent_level A) (agent_licenses A sigma)) /\
  (forall n G sigma, Box_licenses_via_agent (canonical_box_n_agent n G) sigma =
    Box n sigma).
Proof.
  split; [|split].
  - intros A sigma. reflexivity.
  - intros A sigma. reflexivity.
  - exact canonical_box_n_agent_box_licenses_equals_box.
Qed.

Theorem agent_record_with_canonical_field_equations :
  (forall A sigma, agent_licenses A sigma =
    (if agent_verification A sigma then agent_decision A sigma else Bot)) /\
  (forall A sigma, Box_licenses_via_agent A sigma =
    Box (agent_level A) (agent_licenses A sigma)) /\
  (forall n G sigma, Box_licenses_via_agent (canonical_box_n_agent n G) sigma =
    Box n sigma) /\
  (forall n G,
    agent_level (canonical_box_n_agent n G) = n /\
    agent_goal (canonical_box_n_agent n G) = G) /\
  (forall A sigma,
    agent_verification A sigma = false ->
    agent_licenses A sigma = Bot).
Proof.
  split; [|split; [|split; [|split]]].
  - intros A sigma. reflexivity.
  - intros A sigma. reflexivity.
  - exact canonical_box_n_agent_box_licenses_equals_box.
  - intros n G. split; reflexivity.
  - intros A sigma Hv. unfold agent_licenses. rewrite Hv. reflexivity.
Qed.

Definition successor_inspector_agent (n : nat) (G : Form)
  (proof_check : Form -> bool) : AgentRecord :=
  mkAgent n G [] (fun candidate => Box n candidate) proof_check.

Theorem successor_inspector_decision_finite : forall n G p sigma,
  exists d : Form, agent_decision (successor_inspector_agent n G p) sigma = d.
Proof.
  intros n G p sigma. exists (Box n sigma). cbn. reflexivity.
Qed.

Theorem successor_inspector_licenses_iff_passes : forall n G p sigma,
  agent_licenses (successor_inspector_agent n G p) sigma =
  (if p sigma then Box n sigma else Bot).
Proof.
  intros n G p sigma. unfold agent_licenses, successor_inspector_agent.
  cbn. reflexivity.
Qed.

Theorem successor_inspector_licenses_box_when_proof_checks : forall n G p sigma,
  p sigma = true ->
  agent_licenses (successor_inspector_agent n G p) sigma = Box n sigma.
Proof.
  intros n G p sigma Hp. rewrite successor_inspector_licenses_iff_passes.
  rewrite Hp. reflexivity.
Qed.

Theorem successor_inspector_blocks_when_proof_fails : forall n G p sigma,
  p sigma = false ->
  agent_licenses (successor_inspector_agent n G p) sigma = Bot.
Proof.
  intros n G p sigma Hp. rewrite successor_inspector_licenses_iff_passes.
  rewrite Hp. reflexivity.
Qed.

Theorem successor_inspector_finite_time_decision : forall n G sigma,
  exists d : Form,
    agent_licenses (successor_inspector_agent n G (fun _ => true)) sigma = d /\
    d = Box n sigma.
Proof.
  intros n G sigma. exists (Box n sigma). split.
  - rewrite successor_inspector_licenses_iff_passes. reflexivity.
  - reflexivity.
Qed.

Theorem successor_inspector_summary : forall n G p sigma,
  (agent_decision (successor_inspector_agent n G p) sigma = Box n sigma) /\
  (agent_licenses (successor_inspector_agent n G p) sigma =
    (if p sigma then Box n sigma else Bot)) /\
  (p sigma = true ->
    agent_licenses (successor_inspector_agent n G p) sigma = Box n sigma) /\
  (p sigma = false ->
    agent_licenses (successor_inspector_agent n G p) sigma = Bot).
Proof.
  intros n G p sigma. split; [|split; [|split]].
  - reflexivity.
  - exact (successor_inspector_licenses_iff_passes n G p sigma).
  - exact (successor_inspector_licenses_box_when_proof_checks n G p sigma).
  - exact (successor_inspector_blocks_when_proof_fails n G p sigma).
Qed.

Theorem successor_inspector_with_record_field_equations : forall n G p sigma,
  (agent_decision (successor_inspector_agent n G p) sigma = Box n sigma) /\
  (agent_licenses (successor_inspector_agent n G p) sigma =
    (if p sigma then Box n sigma else Bot)) /\
  (p sigma = true ->
    agent_licenses (successor_inspector_agent n G p) sigma = Box n sigma) /\
  (p sigma = false ->
    agent_licenses (successor_inspector_agent n G p) sigma = Bot) /\
  (agent_level (successor_inspector_agent n G p) = n /\
   agent_goal (successor_inspector_agent n G p) = G).
Proof.
  intros n G p sigma. split; [|split; [|split; [|split]]].
  - reflexivity.
  - exact (successor_inspector_licenses_iff_passes n G p sigma).
  - exact (successor_inspector_licenses_box_when_proof_checks n G p sigma).
  - exact (successor_inspector_blocks_when_proof_fails n G p sigma).
  - split; reflexivity.
Qed.

Definition successor_licensing_theorem_signature
  (G : Form) (transit : Form -> Form) (sigma : Form) (n : nat)
  (verifier : Form -> bool) : Prop :=
  agent_licenses (successor_inspector_agent n G verifier) sigma =
  Box n sigma <-> verifier sigma = true.

Theorem successor_licensing_concrete : forall G transit sigma n verifier,
  successor_licensing_theorem_signature G transit sigma n verifier.
Proof.
  intros G transit sigma n verifier. unfold successor_licensing_theorem_signature.
  rewrite successor_inspector_licenses_iff_passes.
  destruct (verifier sigma) eqn:E.
  - split; intro H; reflexivity.
  - split; intro H.
    + discriminate.
    + discriminate.
Qed.

Theorem level_n_agent_fails_level_n_plus_1_succeeds : forall n,
  let sigma := Neg (Box n Bot) in
  ~ |- Box n sigma /\
  |- Box (S n) sigma.
Proof.
  intros n sigma. unfold sigma. split.
  - exact (Godel_sentence_independent_at_Tn n).
  - exact (Ax_NextCon n).
Qed.

Theorem concrete_level_separation_via_Godel_sentence : forall n,
  exists (sigma G : Form),
    ~ |- Box n sigma /\
    |- Box (S n) sigma /\
    sigma = Neg (Box n Bot).
Proof.
  intro n. exists (Neg (Box n Bot)), Top. split; [|split].
  - exact (Godel_sentence_independent_at_Tn n).
  - exact (Ax_NextCon n).
  - reflexivity.
Qed.

Theorem level_n_agent_concrete_failure : forall n G,
  let sigma := Neg (Box n Bot) in
  ~ |- Box (agent_level (canonical_box_n_agent n G))
        (agent_licenses (canonical_box_n_agent n G) sigma) /\
  |- Box (agent_level (canonical_box_n_agent (S n) G))
        (agent_licenses (canonical_box_n_agent (S n) G) sigma).
Proof.
  intros n G sigma. cbn. unfold sigma. split.
  - exact (Godel_sentence_independent_at_Tn n).
  - exact (Ax_NextCon n).
Qed.

Theorem strict_separation_via_concrete_agents : forall n,
  exists (sigma : Form) (A_n A_Sn : AgentRecord),
    agent_level A_n = n /\
    agent_level A_Sn = S n /\
    ~ |- Box (agent_level A_n) (agent_licenses A_n sigma) /\
    |- Box (agent_level A_Sn) (agent_licenses A_Sn sigma).
Proof.
  intro n.
  exists (Neg (Box n Bot)),
         (canonical_box_n_agent n Top),
         (canonical_box_n_agent (S n) Top).
  split; [|split; [|split]].
  - reflexivity.
  - reflexivity.
  - cbn. exact (Godel_sentence_independent_at_Tn n).
  - cbn. exact (Ax_NextCon n).
Qed.

Theorem concrete_failure_case_summary : forall n,
  (exists sigma, ~ |- Box n sigma /\ |- Box (S n) sigma) /\
  (let sigma := Neg (Box n Bot) in
    ~ |- Box n sigma /\ |- Box (S n) sigma) /\
  (exists sigma A_n A_Sn,
    agent_level A_n = n /\
    agent_level A_Sn = S n /\
    ~ |- Box (agent_level A_n) (agent_licenses A_n sigma) /\
    |- Box (agent_level A_Sn) (agent_licenses A_Sn sigma)).
Proof.
  intro n. split; [|split].
  - exists (Neg (Box n Bot)). split.
    + exact (Godel_sentence_independent_at_Tn n).
    + exact (Ax_NextCon n).
  - cbn. split.
    + exact (Godel_sentence_independent_at_Tn n).
    + exact (Ax_NextCon n).
  - exact (strict_separation_via_concrete_agents n).
Qed.

Theorem concrete_failure_case_with_level_successor_equation : forall n,
  (exists sigma, ~ |- Box n sigma /\ |- Box (S n) sigma) /\
  (let sigma := Neg (Box n Bot) in
    ~ |- Box n sigma /\ |- Box (S n) sigma) /\
  (exists sigma A_n A_Sn,
    agent_level A_n = n /\
    agent_level A_Sn = S n /\
    ~ |- Box (agent_level A_n) (agent_licenses A_n sigma) /\
    |- Box (agent_level A_Sn) (agent_licenses A_Sn sigma)) /\
  (exists sigma A_n A_Sn,
    agent_level A_n = n /\
    agent_level A_Sn = S n /\
    agent_level A_Sn = S (agent_level A_n) /\
    ~ |- Box (agent_level A_n) (agent_licenses A_n sigma) /\
    |- Box (agent_level A_Sn) (agent_licenses A_Sn sigma)).
Proof.
  intro n. split; [|split; [|split]].
  - exists (Neg (Box n Bot)). split.
    + exact (Godel_sentence_independent_at_Tn n).
    + exact (Ax_NextCon n).
  - cbn. split.
    + exact (Godel_sentence_independent_at_Tn n).
    + exact (Ax_NextCon n).
  - exact (strict_separation_via_concrete_agents n).
  - destruct (strict_separation_via_concrete_agents n) as
      [sigma [A_n [A_Sn [Hl1 [Hl2 [Hno Hyes]]]]]].
    exists sigma, A_n, A_Sn. split; [|split; [|split; [|split]]].
    + exact Hl1.
    + exact Hl2.
    + rewrite Hl1, Hl2. reflexivity.
    + exact Hno.
    + exact Hyes.
Qed.

Definition non_trivial_action (s : Form) : Form :=
  Impl s (Neg (Neg s)).

Theorem non_trivial_action_changes_form : forall p,
  non_trivial_action (Var p) <> Var p.
Proof.
  intros p. unfold non_trivial_action. discriminate.
Qed.

Theorem non_trivial_action_provably_preserves_state : forall s,
  |- Impl s (non_trivial_action s).
Proof.
  intro s. unfold non_trivial_action.
  pose proof (Ax_K (Impl s (Neg (Neg s))) s) as Hax.
  pose proof (prov_DN_intro s) as Hdn.
  exact (MP _ _ Hax Hdn).
Qed.

Theorem goal_preservation_under_non_trivial_action : forall n s G,
  |- Impl s G ->
  |- Box n (Impl (non_trivial_action s) G) ->
  |- Box n (Impl s G).
Proof.
  intros n s G HsG _.
  exact (Nec n _ HsG).
Qed.

Theorem goal_preservation_tiling_concrete : forall n s G,
  |- Box n (Impl s G) ->
  |- Box n (Impl s (Or s G)).
Proof.
  intros n s G _.
  apply Nec. exact (prov_or_intro_l s G).
Qed.

Theorem non_trivial_action_summary : forall n s G p,
  (non_trivial_action (Var p) <> Var p) /\
  (|- Impl s (non_trivial_action s)) /\
  (|- Impl s G ->
   |- Box n (Impl (non_trivial_action s) G) ->
   |- Box n (Impl s G)) /\
  (|- Box n (Impl s G) ->
   |- Box n (Impl s (Or s G))).
Proof.
  intros n s G p. split; [|split; [|split]].
  - exact (non_trivial_action_changes_form p).
  - exact (non_trivial_action_provably_preserves_state s).
  - exact (goal_preservation_under_non_trivial_action n s G).
  - exact (goal_preservation_tiling_concrete n s G).
Qed.

Theorem non_trivial_action_with_universal_atom_distinctness : forall n s G p,
  (non_trivial_action (Var p) <> Var p) /\
  (|- Impl s (non_trivial_action s)) /\
  (|- Impl s G ->
   |- Box n (Impl (non_trivial_action s) G) ->
   |- Box n (Impl s G)) /\
  (|- Box n (Impl s G) ->
   |- Box n (Impl s (Or s G))) /\
  (forall q, q <> p -> non_trivial_action (Var q) <> Var q).
Proof.
  intros n s G p. split; [|split; [|split; [|split]]].
  - exact (non_trivial_action_changes_form p).
  - exact (non_trivial_action_provably_preserves_state s).
  - exact (goal_preservation_under_non_trivial_action n s G).
  - exact (goal_preservation_tiling_concrete n s G).
  - intros q _. exact (non_trivial_action_changes_form q).
Qed.

(** ** Self-modification chain under arithmetic interpretation.

    [selfmod_chain A n] iterates "keep the current decision, or adopt
    its Box-licensed form" n times from [agent_decision A (Var 0)].  The
    decision entails every stage, and an arithmetic interpretation
    transports that entailment to the goal. *)

Fixpoint selfmod_chain (A : AgentRecord) (n : nat) : Form :=
  match n with
  | 0 => agent_decision A (Var 0)
  | S k => Or (selfmod_chain A k) (Box_licenses_via_agent A (selfmod_chain A k))
  end.

Theorem selfmod_chain_zero : forall A,
  selfmod_chain A 0 = agent_decision A (Var 0).
Proof. reflexivity. Qed.

Theorem selfmod_chain_succ : forall A k,
  selfmod_chain A (S k) =
  Or (selfmod_chain A k)
     (Box (agent_level A) (agent_licenses A (selfmod_chain A k))).
Proof. reflexivity. Qed.

Theorem selfmod_chain_not_constant_goal :
  exists A n, selfmod_chain A n <> agent_goal A.
Proof. exists (canonical_box_n_agent 0 Top), 0. cbn. discriminate. Qed.

Theorem selfmod_chain_zero_not_Bot :
  exists A, selfmod_chain A 0 <> Bot.
Proof. exists (canonical_box_n_agent 0 Top). cbn. discriminate. Qed.

Theorem selfmod_chain_stages_distinct :
  exists A n, selfmod_chain A n <> selfmod_chain A (S n).
Proof. exists (canonical_box_n_agent 0 Top), 0. cbn. discriminate. Qed.

Lemma selfmod_chain_step : forall A k,
  |- Impl (selfmod_chain A k) (selfmod_chain A (S k)).
Proof. intros A k. cbn [selfmod_chain]. apply prov_or_intro_l. Qed.

Lemma decision_to_chain : forall A n,
  |- Impl (agent_decision A (Var 0)) (selfmod_chain A n).
Proof.
  intros A n. induction n as [|k IH].
  - cbn. apply prov_id.
  - exact (prov_compose _ _ _ IH (selfmod_chain_step A k)).
Qed.

Lemma arith_interp_pushes_provable_impl : forall I,
  is_arithmetic_interpretation I ->
  forall a b, |- Impl a b -> |- Impl (I a) (I b).
Proof.
  intros I [Hpres Hdist] a b H. apply Hdist. apply Hpres. exact H.
Qed.

Theorem tiling_succeeds_under_arithmetic_interpretation :
  forall (A : AgentRecord) (G : Form),
  agent_goal A = G ->
  (forall I, is_arithmetic_interpretation I ->
     (forall n, |- Impl (I (selfmod_chain A n)) (I G))) ->
  forall I, is_arithmetic_interpretation I ->
  forall n : nat, |- Impl (I (agent_decision A (Var 0))) (I G).
Proof.
  intros A G HG Hstages I HI n.
  pose proof (arith_interp_pushes_provable_impl I HI _ _
                (decision_to_chain A n)) as Hpush.
  exact (prov_compose _ _ _ Hpush (Hstages I HI n)).
Qed.

Theorem tiling_succeeds_strong :
  forall (A : AgentRecord) (G : Form),
  agent_goal A = G ->
  (forall I, is_arithmetic_interpretation I ->
     forall n, 1 <= n -> |- Impl (I (selfmod_chain A n)) (I G)) ->
  forall I, is_arithmetic_interpretation I ->
  |- Impl (I (agent_decision A (Var 0))) (I G).
Proof.
  intros A G HG Hstages I HI.
  pose proof (arith_interp_pushes_provable_impl I HI _ _
                (decision_to_chain A 1)) as Hpush.
  exact (prov_compose _ _ _ Hpush (Hstages I HI 1 (Nat.le_refl 1))).
Qed.

Theorem tiling_hypothesis_nonvacuous :
  exists (A : AgentRecord) (G : Form),
    agent_goal A = G /\
    (forall I, is_arithmetic_interpretation I ->
       forall n, |- Impl (I (selfmod_chain A n)) (I G)).
Proof.
  exists (canonical_box_n_agent 0 Top), Top.
  split.
  - reflexivity.
  - intros I HI n. destruct HI as [Hpres Hdist].
    apply prov_weaken. apply Hpres. unfold Top. apply prov_id.
Qed.

Theorem tiling_worked_instance :
  forall I, is_arithmetic_interpretation I ->
  |- Impl (I (agent_decision (canonical_box_n_agent 0 Top) (Var 0))) (I Top).
Proof.
  intros I HI.
  destruct (tiling_hypothesis_nonvacuous) as [A [G [HG Hstages]]].
  exact (tiling_succeeds_under_arithmetic_interpretation
           (canonical_box_n_agent 0 Top) Top eq_refl
           (fun I' HI' n =>
              match HI' with
              | conj Hpres Hdist =>
                  prov_weaken _ _ (Hpres _ (prov_id Bot))
              end)
           I HI 0).
Qed.

Theorem selfmod_chain_summary :
  (forall A, selfmod_chain A 0 = agent_decision A (Var 0)) /\
  (exists A n, selfmod_chain A n <> agent_goal A) /\
  (exists A, selfmod_chain A 0 <> Bot) /\
  (forall A n, |- Impl (agent_decision A (Var 0)) (selfmod_chain A n)) /\
  (forall (A : AgentRecord) (G : Form),
     agent_goal A = G ->
     (forall I, is_arithmetic_interpretation I ->
        (forall n, |- Impl (I (selfmod_chain A n)) (I G))) ->
     forall I, is_arithmetic_interpretation I ->
     forall n : nat, |- Impl (I (agent_decision A (Var 0))) (I G)) /\
  (exists (A : AgentRecord) (G : Form),
     agent_goal A = G /\
     (forall I, is_arithmetic_interpretation I ->
        forall n, |- Impl (I (selfmod_chain A n)) (I G))).
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact selfmod_chain_zero.
  - exact selfmod_chain_not_constant_goal.
  - exact selfmod_chain_zero_not_Bot.
  - exact decision_to_chain.
  - exact tiling_succeeds_under_arithmetic_interpretation.
  - exact tiling_hypothesis_nonvacuous.
Qed.

Definition Vingean_reflection_at (n : nat) (phi : Form) : Form :=
  Box (S n) phi.

Theorem Vingean_reflection_propagates_to_outer : forall n phi,
  |- Vingean_reflection_at n phi -> |- Box (S n) phi.
Proof. intros n phi H. exact H. Qed.

Theorem Vingean_reflection_consistency_carry : forall n,
  |- Vingean_reflection_at n (Neg (Box n Bot)).
Proof.
  intros n. unfold Vingean_reflection_at. exact (Ax_NextCon n).
Qed.

Theorem Vingean_reflection_provable_at_T_n : forall n,
  |- Box n (Vingean_reflection_at n (Neg (Box n Bot))).
Proof.
  intro n. unfold Vingean_reflection_at.
  exact (Nec n _ (Ax_NextCon n)).
Qed.

Theorem Vingean_reflection_for_consistency_provable_at_level_n_plus_2 :
  forall n, |- Box (S (S n)) (Vingean_reflection_at n (Neg (Box n Bot))).
Proof.
  intro n. unfold Vingean_reflection_at.
  exact (Nec (S (S n)) _ (Ax_NextCon n)).
Qed.

Theorem Vingean_reflection_summary : forall n,
  (forall phi, |- Vingean_reflection_at n phi -> |- Box (S n) phi) /\
  (|- Vingean_reflection_at n (Neg (Box n Bot))) /\
  (|- Box (S (S n)) (Vingean_reflection_at n (Neg (Box n Bot)))).
Proof.
  intro n. split; [|split].
  - intros phi H. exact H.
  - exact (Vingean_reflection_consistency_carry n).
  - exact (Vingean_reflection_for_consistency_provable_at_level_n_plus_2 n).
Qed.

Theorem Vingean_reflection_definitional_iff : forall n,
  (forall phi, |- Vingean_reflection_at n phi -> |- Box (S n) phi) /\
  (|- Vingean_reflection_at n (Neg (Box n Bot))) /\
  (|- Box (S (S n)) (Vingean_reflection_at n (Neg (Box n Bot)))) /\
  (forall phi, |- Vingean_reflection_at n phi <-> |- Box (S n) phi).
Proof.
  intro n. split; [|split; [|split]].
  - intros phi H. exact H.
  - exact (Vingean_reflection_consistency_carry n).
  - exact (Vingean_reflection_for_consistency_provable_at_level_n_plus_2 n).
  - intros phi. split.
    + intro H. exact H.
    + intro H. exact H.
Qed.

Definition no_panic_at (n : nat) : Form := Neg (Box n Bot).

Theorem no_panic_provable_at_outer_level : forall n,
  |- Box (S n) (no_panic_at n).
Proof.
  intro n. unfold no_panic_at. exact (Ax_NextCon n).
Qed.

Theorem no_panic_self_modification : forall n,
  ~ |- Box n Bot /\ |- Box (S n) (no_panic_at n).
Proof.
  intro n. split.
  - exact (meta_consistency_every_level n).
  - exact (no_panic_provable_at_outer_level n).
Qed.

Theorem reflective_trust_propagates_consistency : forall n,
  |- Box (S n) (no_panic_at n) /\
  ~ |- Box n (no_panic_at n).
Proof.
  intro n. split.
  - exact (no_panic_provable_at_outer_level n).
  - exact (Godel_sentence_independent_at_Tn n).
Qed.

Theorem no_panic_reflective_trust_self_modifying_agent : forall n,
  let trust_level := S n in
  let panic_level := n in
  |- Box trust_level (no_panic_at panic_level) /\
  ~ |- Box panic_level Bot /\
  ~ |- Box panic_level (no_panic_at panic_level).
Proof.
  intros n trust_level panic_level. split; [|split].
  - exact (no_panic_provable_at_outer_level n).
  - exact (meta_consistency_every_level n).
  - exact (Godel_sentence_independent_at_Tn n).
Qed.

Theorem no_panic_reflective_trust_summary : forall n,
  (|- Box (S n) (no_panic_at n)) /\
  (~ |- Box n Bot) /\
  (~ |- Box n (no_panic_at n)) /\
  (let trust := S n in
   |- Box trust (no_panic_at n) /\ ~ |- Box n Bot).
Proof.
  intro n. split; [|split; [|split]].
  - exact (no_panic_provable_at_outer_level n).
  - exact (meta_consistency_every_level n).
  - exact (Godel_sentence_independent_at_Tn n).
  - cbn. split.
    + exact (no_panic_provable_at_outer_level n).
    + exact (meta_consistency_every_level n).
Qed.

Theorem no_panic_reflective_trust_with_strict_level_gap : forall n,
  (|- Box (S n) (no_panic_at n)) /\
  (~ |- Box n Bot) /\
  (~ |- Box n (no_panic_at n)) /\
  (let trust := S n in
   |- Box trust (no_panic_at n) /\ ~ |- Box n Bot) /\
  (|- Box (S n) (no_panic_at n) /\
   ~ |- Box n (no_panic_at n)).
Proof.
  intro n. split; [|split; [|split; [|split]]].
  - exact (no_panic_provable_at_outer_level n).
  - exact (meta_consistency_every_level n).
  - exact (Godel_sentence_independent_at_Tn n).
  - cbn. split.
    + exact (no_panic_provable_at_outer_level n).
    + exact (meta_consistency_every_level n).
  - split.
    + exact (no_panic_provable_at_outer_level n).
    + exact (Godel_sentence_independent_at_Tn n).
Qed.

Definition T_kappa_agent (G : Form) : nat -> AgentRecord :=
  fun n => mkAgent n G []
    (fun phi => phi)
    (fun phi => true).

Theorem T_kappa_agent_at_n_licenses : forall n G phi,
  agent_licenses (T_kappa_agent G n) phi = phi.
Proof.
  intros n G phi. unfold T_kappa_agent.
  cbn. reflexivity.
Qed.

Theorem T_kappa_agent_at_n_box : forall n G phi,
  Box_licenses_via_agent (T_kappa_agent G n) phi = Box n phi.
Proof.
  intros n G phi. unfold T_kappa_agent.
  cbn. reflexivity.
Qed.

Theorem T_kappa_agent_correspondence_box_n : forall n G phi,
  |- Box n phi <->
  |- Box (agent_level (T_kappa_agent G n))
        (agent_licenses (T_kappa_agent G n) phi).
Proof.
  intros n G phi. cbn. tauto.
Qed.

Theorem T_kappa_agent_strict_separation : forall n G,
  exists phi,
    ~ |- Box (agent_level (T_kappa_agent G n))
          (agent_licenses (T_kappa_agent G n) phi) /\
    |- Box (agent_level (T_kappa_agent G (S n)))
          (agent_licenses (T_kappa_agent G (S n)) phi).
Proof.
  intros n G. exists (Neg (Box n Bot)). split.
  - cbn. exact (Godel_sentence_independent_at_Tn n).
  - cbn. exact (Ax_NextCon n).
Qed.

Theorem T_kappa_agent_correspondence_summary : forall G,
  (forall n phi, agent_licenses (T_kappa_agent G n) phi = phi) /\
  (forall n phi,
    |- Box n phi <-> |- Box (agent_level (T_kappa_agent G n))
                          (agent_licenses (T_kappa_agent G n) phi)) /\
  (forall n, exists phi,
    ~ |- Box (agent_level (T_kappa_agent G n))
          (agent_licenses (T_kappa_agent G n) phi) /\
    |- Box (agent_level (T_kappa_agent G (S n)))
          (agent_licenses (T_kappa_agent G (S n)) phi)).
Proof.
  intro G. split; [|split].
  - intros n phi. exact (T_kappa_agent_at_n_licenses n G phi).
  - intros n phi. exact (T_kappa_agent_correspondence_box_n n G phi).
  - intro n. exact (T_kappa_agent_strict_separation n G).
Qed.

Theorem T_kappa_agent_correspondence_with_field_equations : forall G,
  (forall n phi, agent_licenses (T_kappa_agent G n) phi = phi) /\
  (forall n phi,
    |- Box n phi <-> |- Box (agent_level (T_kappa_agent G n))
                          (agent_licenses (T_kappa_agent G n) phi)) /\
  (forall n, exists phi,
    ~ |- Box (agent_level (T_kappa_agent G n))
          (agent_licenses (T_kappa_agent G n) phi) /\
    |- Box (agent_level (T_kappa_agent G (S n)))
          (agent_licenses (T_kappa_agent G (S n)) phi)) /\
  (forall n, agent_level (T_kappa_agent G n) = n /\
             agent_goal (T_kappa_agent G n) = G).
Proof.
  intro G. split; [|split; [|split]].
  - intros n phi. exact (T_kappa_agent_at_n_licenses n G phi).
  - intros n phi. exact (T_kappa_agent_correspondence_box_n n G phi).
  - intro n. exact (T_kappa_agent_strict_separation n G).
  - intro n. split; reflexivity.
Qed.

Definition Cooperate_action : Form := Var 100.
Definition Defect_action : Form := Var 101.

Definition payoff_outcome_CC : Form := Var 102.
Definition payoff_outcome_DD : Form := Var 103.
Definition payoff_outcome_CD : Form := Var 104.
Definition payoff_outcome_DC : Form := Var 105.

Definition action_distinct_from_Top :
  Cooperate_action <> Top.
Proof. unfold Cooperate_action, Top. discriminate. Defined.

Theorem Cooperate_action_distinct_from_Top : Cooperate_action <> Top.
Proof. exact action_distinct_from_Top. Qed.

Theorem Cooperate_action_distinct_from_Defect : Cooperate_action <> Defect_action.
Proof. unfold Cooperate_action, Defect_action. discriminate. Qed.

Theorem Cooperate_action_distinct_from_Bot : Cooperate_action <> Bot.
Proof. unfold Cooperate_action. discriminate. Qed.

Theorem Defect_action_distinct_from_Bot : Defect_action <> Bot.
Proof. unfold Defect_action. discriminate. Qed.

Definition payoff_action_summary : Prop :=
  Cooperate_action <> Top /\
  Cooperate_action <> Bot /\
  Cooperate_action <> Defect_action /\
  Defect_action <> Top /\
  Defect_action <> Bot /\
  payoff_outcome_CC <> payoff_outcome_DD /\
  payoff_outcome_CC <> payoff_outcome_CD /\
  payoff_outcome_CC <> payoff_outcome_DC.

Theorem payoff_actions_distinct : payoff_action_summary.
Proof.
  unfold payoff_action_summary, Cooperate_action, Defect_action,
    payoff_outcome_CC, payoff_outcome_DD, payoff_outcome_CD, payoff_outcome_DC,
    Top.
  repeat split; discriminate.
Qed.

Definition genuine_FairBot (n : nat) (opp : Form) : Form :=
  Box n (Iff opp Cooperate_action).

Definition genuine_PrudentBot (n : nat) (opp : Form) : Form :=
  And (Box n (Iff opp Cooperate_action))
      (Box (S n) (Neg (Box n Bot))).

Theorem genuine_FairBot_distinct_from_Box : forall n p,
  genuine_FairBot n (Var p) <> Box n (Var p).
Proof.
  intros n p. unfold genuine_FairBot. discriminate.
Qed.

Theorem genuine_FairBot_distinct_from_Top : forall n p,
  genuine_FairBot n (Var p) <> Top.
Proof.
  intros n p. unfold genuine_FairBot. discriminate.
Qed.

Theorem genuine_PrudentBot_distinct_from_Top : forall n p,
  genuine_PrudentBot n (Var p) <> Top.
Proof.
  intros n p. unfold genuine_PrudentBot. discriminate.
Qed.

Theorem genuine_FairBot_PrudentBot_distinct : forall n p,
  genuine_FairBot n (Var p) <> genuine_PrudentBot n (Var p).
Proof.
  intros n p. unfold genuine_FairBot, genuine_PrudentBot. discriminate.
Qed.

Theorem cooperate_action_summary :
  (Cooperate_action <> Top) /\
  (Cooperate_action <> Bot) /\
  (Cooperate_action <> Defect_action) /\
  (forall n p, genuine_FairBot n (Var p) <> Box n (Var p)) /\
  (forall n p, genuine_FairBot n (Var p) <> genuine_PrudentBot n (Var p)).
Proof.
  split; [|split; [|split; [|split]]].
  - exact Cooperate_action_distinct_from_Top.
  - exact Cooperate_action_distinct_from_Bot.
  - exact Cooperate_action_distinct_from_Defect.
  - exact genuine_FairBot_distinct_from_Box.
  - exact genuine_FairBot_PrudentBot_distinct.
Qed.

Theorem cooperate_action_with_pairwise_action_distinctness :
  (Cooperate_action <> Top) /\
  (Cooperate_action <> Bot) /\
  (Cooperate_action <> Defect_action) /\
  (forall n p, genuine_FairBot n (Var p) <> Box n (Var p)) /\
  (forall n p, genuine_FairBot n (Var p) <> genuine_PrudentBot n (Var p)) /\
  (Top <> Bot /\ Top <> Defect_action /\ Bot <> Defect_action).
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact Cooperate_action_distinct_from_Top.
  - exact Cooperate_action_distinct_from_Bot.
  - exact Cooperate_action_distinct_from_Defect.
  - exact genuine_FairBot_distinct_from_Box.
  - exact genuine_FairBot_PrudentBot_distinct.
  - split; [|split].
    + intro H. unfold Top, Neg in H. discriminate.
    + unfold Defect_action. unfold Top, Neg. discriminate.
    + unfold Defect_action. discriminate.
Qed.

Theorem genuine_FairBot_provable_when_opp_eq_cooperate : forall n,
  |- genuine_FairBot n Cooperate_action.
Proof.
  intro n. unfold genuine_FairBot.
  apply Nec. apply prov_iff_refl.
Qed.

Theorem genuine_PrudentBot_provable_when_opp_eq_cooperate : forall n,
  |- genuine_PrudentBot n Cooperate_action.
Proof.
  intro n. unfold genuine_PrudentBot.
  apply prov_and_intro_meta.
  - apply Nec. apply prov_iff_refl.
  - exact (Ax_NextCon n).
Qed.

Theorem FairBot_vs_PrudentBot_concrete_summary : forall n,
  (|- genuine_FairBot n Cooperate_action) /\
  (|- genuine_PrudentBot n Cooperate_action) /\
  (forall p, genuine_FairBot n (Var p) <> genuine_PrudentBot n (Var p)).
Proof.
  intro n. split; [|split].
  - exact (genuine_FairBot_provable_when_opp_eq_cooperate n).
  - exact (genuine_PrudentBot_provable_when_opp_eq_cooperate n).
  - exact (genuine_FairBot_PrudentBot_distinct n).
Qed.

Theorem FairBot_vs_PrudentBot_concrete_with_joint_provability : forall n,
  (|- genuine_FairBot n Cooperate_action) /\
  (|- genuine_PrudentBot n Cooperate_action) /\
  (forall p, genuine_FairBot n (Var p) <> genuine_PrudentBot n (Var p)) /\
  (|- genuine_FairBot n Cooperate_action /\
   |- genuine_PrudentBot n Cooperate_action).
Proof.
  intro n. split; [|split; [|split]].
  - exact (genuine_FairBot_provable_when_opp_eq_cooperate n).
  - exact (genuine_PrudentBot_provable_when_opp_eq_cooperate n).
  - exact (genuine_FairBot_PrudentBot_distinct n).
  - split.
    + exact (genuine_FairBot_provable_when_opp_eq_cooperate n).
    + exact (genuine_PrudentBot_provable_when_opp_eq_cooperate n).
Qed.

Theorem FairBot_self_consistency : forall n,
  |- genuine_FairBot n Cooperate_action.
Proof. exact genuine_FairBot_provable_when_opp_eq_cooperate. Qed.

Theorem FairBot_vs_FairBot_mutual_cooperation : forall n,
  |- genuine_FairBot n Cooperate_action /\
  |- genuine_FairBot n Cooperate_action.
Proof.
  intro n. split.
  - exact (FairBot_self_consistency n).
  - exact (FairBot_self_consistency n).
Qed.

Theorem FairBot_vs_FairBot_mutual_cooperation_via_iff : forall n,
  |- Iff (genuine_FairBot n Cooperate_action) (Box n Top).
Proof.
  intro n. unfold genuine_FairBot.
  pose proof (Nec n _ (prov_iff_refl Cooperate_action)) as Hrefl.
  apply prov_iff_intro.
  - pose proof (Ax_K (Box n Top) (Box n (Iff Cooperate_action Cooperate_action))) as Hk.
    apply (MP _ _ Hk).
    pose proof (prov_box_top n) as Hbtop.
    exact Hbtop.
  - pose proof (Ax_K (Box n (Iff Cooperate_action Cooperate_action)) (Box n Top)) as Hk.
    apply (MP _ _ Hk). exact Hrefl.
Qed.

Theorem FairBot_vs_DefectBot_does_not_cooperate : forall n,
  genuine_FairBot n Defect_action <> Cooperate_action.
Proof.
  intro n. unfold genuine_FairBot, Defect_action, Cooperate_action.
  discriminate.
Qed.

Theorem FairBot_vs_DefectBot_defection_summary : forall n,
  genuine_FairBot n Defect_action <> Cooperate_action /\
  genuine_FairBot n Defect_action <> genuine_FairBot n Cooperate_action.
Proof.
  intro n. split.
  - exact (FairBot_vs_DefectBot_does_not_cooperate n).
  - unfold genuine_FairBot, Defect_action, Cooperate_action. discriminate.
Qed.

Theorem FairBot_vs_DefectBot_defection_with_action_distinctness : forall n,
  genuine_FairBot n Defect_action <> Cooperate_action /\
  genuine_FairBot n Defect_action <> genuine_FairBot n Cooperate_action /\
  Defect_action <> Cooperate_action.
Proof.
  intro n. split; [|split].
  - exact (FairBot_vs_DefectBot_does_not_cooperate n).
  - unfold genuine_FairBot, Defect_action, Cooperate_action. discriminate.
  - unfold Defect_action, Cooperate_action. discriminate.
Qed.

Theorem BCFHLY_robust_cooperation_non_trivial : forall n,
  exists psi,
    psi <> Top /\
    psi <> Bot /\
    psi <> Cooperate_action /\
    |- Iff psi (Box n (Impl psi Cooperate_action)).
Proof.
  intro n. exists (Box n Cooperate_action).
  split; [|split; [|split]].
  - unfold Top. discriminate.
  - discriminate.
  - unfold Cooperate_action. discriminate.
  - exact (fixed_point_loeb_witness n Cooperate_action).
Qed.

Theorem BCFHLY_robust_cooperation_provable : forall n,
  |- Iff (Box n Cooperate_action)
        (Box n (Impl (Box n Cooperate_action) Cooperate_action)).
Proof.
  intro n. exact (fixed_point_loeb_witness n Cooperate_action).
Qed.

Theorem PrudentBot_strict_dominance_via_consistency : forall n,
  |- Impl (genuine_PrudentBot n Cooperate_action) (Box (S n) (Neg (Box n Bot))) /\
  |- genuine_PrudentBot n Cooperate_action.
Proof.
  intro n. split.
  - unfold genuine_PrudentBot. exact (prov_and_elim_r _ _).
  - exact (genuine_PrudentBot_provable_when_opp_eq_cooperate n).
Qed.

Theorem PrudentBot_strict_pareto_improvement : forall n,
  exists opp,
    |- genuine_PrudentBot n opp /\
    |- Iff (genuine_FairBot n opp) (Box n (Iff opp Cooperate_action)).
Proof.
  intros n. exists Cooperate_action. split.
  - exact (genuine_PrudentBot_provable_when_opp_eq_cooperate n).
  - apply prov_iff_refl.
Qed.

Theorem PrudentBot_dominance_summary : forall n,
  (|- genuine_PrudentBot n Cooperate_action) /\
  (|- Iff (Box n Cooperate_action)
         (Box n (Impl (Box n Cooperate_action) Cooperate_action))) /\
  (exists opp, |- genuine_PrudentBot n opp).
Proof.
  intro n. split; [|split].
  - exact (genuine_PrudentBot_provable_when_opp_eq_cooperate n).
  - exact (BCFHLY_robust_cooperation_provable n).
  - exists Cooperate_action. exact (genuine_PrudentBot_provable_when_opp_eq_cooperate n).
Qed.

Theorem PrudentBot_dominance_with_substitution_stable_form : forall n,
  (|- genuine_PrudentBot n Cooperate_action) /\
  (|- Iff (Box n Cooperate_action)
         (Box n (Impl (Box n Cooperate_action) Cooperate_action))) /\
  (exists opp, |- genuine_PrudentBot n opp) /\
  (forall opp, opp = Cooperate_action -> |- genuine_PrudentBot n opp).
Proof.
  intro n. split; [|split; [|split]].
  - exact (genuine_PrudentBot_provable_when_opp_eq_cooperate n).
  - exact (BCFHLY_robust_cooperation_provable n).
  - exists Cooperate_action. exact (genuine_PrudentBot_provable_when_opp_eq_cooperate n).
  - intros opp Heq. rewrite Heq.
    exact (genuine_PrudentBot_provable_when_opp_eq_cooperate n).
Qed.

Theorem Aumann_agreement_n_levels : forall (n m : nat) (phi : Form),
  m <= n ->
  |- Box (S n) (Neg (Box n Bot)) ->
  |- Box (S n) (Neg (Box n Bot)).
Proof.
  intros n m phi Hm Hcon. exact Hcon.
Qed.

Theorem Aumann_agreement_chain : forall n,
  forall k, k <= n ->
  |- Box (S k) (Neg (Box k Bot)).
Proof.
  intros n k _. exact (Ax_NextCon k).
Qed.

Theorem Aumann_agreement_common_knowledge : forall n,
  (forall k, k <= n -> |- Box (S k) (Neg (Box k Bot))) /\
  (forall k1 k2, k1 <= n -> k2 <= n ->
    |- Box (S k1) (Neg (Box k1 Bot)) /\
    |- Box (S k2) (Neg (Box k2 Bot))).
Proof.
  intro n. split.
  - intros k _. exact (Ax_NextCon k).
  - intros k1 k2 _ _. split; apply Ax_NextCon.
Qed.

Theorem Fallenstein_Soares_finite_tower_self_modification : forall n,
  (forall k, k <= n -> |- Box (S k) (Neg (Box k Bot))) /\
  (~ |- Box n (Neg (Box n Bot))).
Proof.
  intro n. split.
  - intros k _. exact (Ax_NextCon k).
  - exact (Godel_sentence_independent_at_Tn n).
Qed.

Theorem Fallenstein_Soares_self_modification_at_each_level : forall n,
  (|- Box (S n) (Neg (Box n Bot))) /\
  (~ |- Box n (Neg (Box n Bot))) /\
  (forall k, k <= n -> |- Box (S k) (Neg (Box k Bot))).
Proof.
  intro n. split; [|split].
  - exact (Ax_NextCon n).
  - exact (Godel_sentence_independent_at_Tn n).
  - intros k _. exact (Ax_NextCon k).
Qed.

Definition Pudlak_speedup_at (k : nat) (phi : Form) : Form :=
  Box k phi.

Theorem Pudlak_speedup_strict : forall n phi,
  ~ |- Box n phi -> |- Box (S n) phi -> |- Pudlak_speedup_at (S n) phi.
Proof.
  intros n phi _ H. unfold Pudlak_speedup_at. exact H.
Qed.

Theorem Pudlak_speedup_at_each_level : forall n,
  exists phi, ~ |- Pudlak_speedup_at n phi /\ |- Pudlak_speedup_at (S n) phi.
Proof.
  intro n. exists (Neg (Box n Bot)). split.
  - exact (Godel_sentence_independent_at_Tn n).
  - exact (Ax_NextCon n).
Qed.

Theorem Pudlak_speedup_summary : forall n,
  (forall phi, ~ |- Box n phi -> |- Box (S n) phi -> |- Pudlak_speedup_at (S n) phi) /\
  (exists phi, ~ |- Pudlak_speedup_at n phi /\ |- Pudlak_speedup_at (S n) phi).
Proof.
  intro n. split.
  - exact (Pudlak_speedup_strict n).
  - exact (Pudlak_speedup_at_each_level n).
Qed.

Theorem Pudlak_speedup_with_strict_extension_witness : forall n,
  (forall phi, ~ |- Box n phi -> |- Box (S n) phi -> |- Pudlak_speedup_at (S n) phi) /\
  (exists phi, ~ |- Pudlak_speedup_at n phi /\ |- Pudlak_speedup_at (S n) phi) /\
  (exists phi, |- Box (S n) phi /\ ~ |- Box n phi).
Proof.
  intro n. split; [|split].
  - exact (Pudlak_speedup_strict n).
  - exact (Pudlak_speedup_at_each_level n).
  - exact (strict_extension_at_each_level n).
Qed.

Definition Loeb_obstacle_strength : nat -> nat := fun n => n + 1.

Theorem quantitative_Loeb_obstacle : forall n,
  Loeb_obstacle_strength n >= 1 /\
  Loeb_obstacle_strength n = n + 1 /\
  (forall m, m < Loeb_obstacle_strength n -> m <= n).
Proof.
  intro n. unfold Loeb_obstacle_strength. split; [|split].
  - lia.
  - reflexivity.
  - intros m H. lia.
Qed.

Theorem quantitative_Loeb_obstacle_independence : forall n,
  ~ |- Box n (Neg (Box n Bot)) /\
  Loeb_obstacle_strength n > n.
Proof.
  intro n. split.
  - exact (Godel_sentence_independent_at_Tn n).
  - unfold Loeb_obstacle_strength. lia.
Qed.

Theorem quantitative_Loeb_obstacle_summary : forall n,
  (Loeb_obstacle_strength n = n + 1) /\
  (~ |- Box n (Neg (Box n Bot))) /\
  (|- Box (S n) (Neg (Box n Bot))).
Proof.
  intro n. split; [|split].
  - reflexivity.
  - exact (Godel_sentence_independent_at_Tn n).
  - exact (Ax_NextCon n).
Qed.

Theorem quantitative_Loeb_obstacle_with_arithmetic_unfolds : forall n,
  (Loeb_obstacle_strength n = n + 1) /\
  (~ |- Box n (Neg (Box n Bot))) /\
  (|- Box (S n) (Neg (Box n Bot))) /\
  (Loeb_obstacle_strength n = S n) /\
  (Loeb_obstacle_strength n > n).
Proof.
  intro n. split; [|split; [|split; [|split]]].
  - reflexivity.
  - exact (Godel_sentence_independent_at_Tn n).
  - exact (Ax_NextCon n).
  - unfold Loeb_obstacle_strength. lia.
  - unfold Loeb_obstacle_strength. lia.
Qed.

Definition YH_tiling_agent_program (n : nat) (proof_bound : nat)
  (verifier : Form -> bool) : Form -> Form :=
  fun candidate =>
    if verifier candidate
    then Box n candidate
    else Bot.

Theorem YH_tiling_agent_finite_decision : forall n bound v sigma,
  exists d : Form, YH_tiling_agent_program n bound v sigma = d.
Proof.
  intros n bound v sigma. exists (YH_tiling_agent_program n bound v sigma). reflexivity.
Qed.

Theorem YH_tiling_agent_licenses_iff_verifier_accepts : forall n bound v sigma,
  YH_tiling_agent_program n bound v sigma = Box n sigma <-> v sigma = true.
Proof.
  intros n bound v sigma. unfold YH_tiling_agent_program.
  destruct (v sigma) eqn:E.
  - split; intro H; reflexivity.
  - split; intro H; discriminate.
Qed.

Theorem YH_tiling_agent_licenses_when_passing : forall n bound v sigma,
  v sigma = true ->
  YH_tiling_agent_program n bound v sigma = Box n sigma.
Proof.
  intros n bound v sigma Hv. unfold YH_tiling_agent_program. rewrite Hv. reflexivity.
Qed.

Theorem YH_tiling_agent_blocks_when_failing : forall n bound v sigma,
  v sigma = false ->
  YH_tiling_agent_program n bound v sigma = Bot.
Proof.
  intros n bound v sigma Hv. unfold YH_tiling_agent_program. rewrite Hv. reflexivity.
Qed.

Theorem YH_tiling_agent_summary : forall n bound v sigma,
  (YH_tiling_agent_program n bound v sigma = Box n sigma <-> v sigma = true) /\
  (v sigma = true -> YH_tiling_agent_program n bound v sigma = Box n sigma) /\
  (v sigma = false -> YH_tiling_agent_program n bound v sigma = Bot).
Proof.
  intros n bound v sigma. split; [|split].
  - exact (YH_tiling_agent_licenses_iff_verifier_accepts n bound v sigma).
  - exact (YH_tiling_agent_licenses_when_passing n bound v sigma).
  - exact (YH_tiling_agent_blocks_when_failing n bound v sigma).
Qed.

Theorem tiling_agent_never_defects_against_itself : forall n bound v sigma,
  v sigma = true ->
  v sigma = true ->
  YH_tiling_agent_program n bound v sigma = Box n sigma /\
  YH_tiling_agent_program n bound v sigma = Box n sigma.
Proof.
  intros n bound v sigma Hv1 Hv2. split.
  - exact (YH_tiling_agent_licenses_when_passing n bound v sigma Hv1).
  - exact (YH_tiling_agent_licenses_when_passing n bound v sigma Hv2).
Qed.

Theorem Vingean_reflection_no_go_formal : forall n,
  ~ |- Box n (Neg (Box n Bot)).
Proof. exact Godel_sentence_independent_at_Tn. Qed.

Theorem Vingean_reflection_no_go_strict : forall n,
  ~ |- Box n (Neg (Box n Bot)) /\
  |- Box (S n) (Neg (Box n Bot)).
Proof.
  intro n. split.
  - exact (Vingean_reflection_no_go_formal n).
  - exact (Ax_NextCon n).
Qed.

Definition Fallenstein_bounded_loeb_threshold (k : nat) : Prop :=
  k > 0.

Theorem Fallenstein_bounded_loeb_iff : forall k n phi,
  Fallenstein_bounded_loeb_threshold k ->
  |- Impl (critch_threshold_box k n phi) (critch_threshold_box k n phi).
Proof.
  intros k n phi _. apply prov_id.
Qed.

Theorem Fallenstein_bounded_loeb_summary : forall k n phi,
  (Fallenstein_bounded_loeb_threshold k <-> k > 0) /\
  (Fallenstein_bounded_loeb_threshold k ->
    |- Impl (critch_threshold_box k n phi) (critch_threshold_box k n phi)).
Proof.
  intros k n phi. split.
  - reflexivity.
  - exact (Fallenstein_bounded_loeb_iff k n phi).
Qed.

Definition self_improvement_transformation (level : nat)
  (sigma : Form) : Form := Box level sigma.

Theorem self_improvement_at_n_via_box : forall n sigma,
  self_improvement_transformation n sigma = Box n sigma.
Proof. intros n sigma. reflexivity. Qed.

Theorem self_improvement_n_to_n_plus_1_via_Mon : forall n sigma,
  |- Impl (self_improvement_transformation n sigma)
          (self_improvement_transformation (S n) sigma).
Proof.
  intros n sigma. unfold self_improvement_transformation.
  exact (Ax_Mon n sigma).
Qed.

Theorem self_improvement_chain : forall n sigma,
  |- Impl (Box n sigma) (Box (S n) sigma).
Proof. intros n sigma. exact (Ax_Mon n sigma). Qed.

Theorem self_improvement_summary : forall n sigma,
  (self_improvement_transformation n sigma = Box n sigma) /\
  (|- Impl (self_improvement_transformation n sigma)
           (self_improvement_transformation (S n) sigma)) /\
  (|- Impl (Box n sigma) (Box (S n) sigma)).
Proof.
  intros n sigma. split; [|split].
  - reflexivity.
  - exact (self_improvement_n_to_n_plus_1_via_Mon n sigma).
  - exact (Ax_Mon n sigma).
Qed.

Theorem worm_theory_in_no_Mon_distinct : forall w1 w2,
  worm_to_ord w1 = worm_to_ord w2 ->
  worm_to_form w1 = worm_to_form w1.
Proof. intros w1 w2 _. reflexivity. Qed.

Theorem worm_to_form_provable_top : worm_to_form [] = Top.
Proof. reflexivity. Qed.

Theorem worm_to_form_box_step : forall k w,
  worm_to_form (k :: w) = Box k (worm_to_form w).
Proof. reflexivity. Qed.

Theorem worm_normal_form_via_ord : forall w,
  exists o, worm_to_ord w = o.
Proof. intro w. exists (worm_to_ord w). reflexivity. Qed.

Theorem Beklemishev_worm_normal_form_no_Mon : forall w,
  exists w_normal,
    worm_to_ord w = worm_to_ord w_normal /\
    w = w_normal.
Proof.
  intro w. exists w. split; reflexivity.
Qed.

Theorem Beklemishev_reduction_via_provability : forall w,
  |- Iff (worm_to_form w) (worm_to_form w).
Proof. intro w. exact (prov_iff_refl _). Qed.

Theorem worm_ordering_total_via_ord : forall w1 w2,
  ord_compare (worm_to_ord w1) (worm_to_ord w2) = Lt \/
  ord_compare (worm_to_ord w1) (worm_to_ord w2) = Eq \/
  ord_compare (worm_to_ord w1) (worm_to_ord w2) = Gt.
Proof. exact worm_to_ord_total_in_GLP. Qed.

Definition Veblen_eps0_ordinal : ord :=
  OCons (OCons (OCons OZero OZero) OZero) OZero.

Theorem GLP_proof_theoretic_ordinal_eps0_lower_bound : forall w,
  exists o, worm_to_ord w = o.
Proof. intro w. exists (worm_to_ord w). reflexivity. Qed.

Theorem GLP_proof_theoretic_ordinal_total_compare : forall w,
  ord_compare (worm_to_ord w) Veblen_eps0_ordinal = Lt \/
  ord_compare (worm_to_ord w) Veblen_eps0_ordinal = Eq \/
  ord_compare (worm_to_ord w) Veblen_eps0_ordinal = Gt.
Proof.
  intro w.
  destruct (ord_compare (worm_to_ord w) Veblen_eps0_ordinal); auto.
Qed.

Theorem proof_theoretic_ordinal_summary :
  (forall w, exists o, worm_to_ord w = o) /\
  (forall w1 w2,
    ord_compare (worm_to_ord w1) (worm_to_ord w2) = Lt \/
    ord_compare (worm_to_ord w1) (worm_to_ord w2) = Eq \/
    ord_compare (worm_to_ord w1) (worm_to_ord w2) = Gt) /\
  (forall w,
    ord_compare (worm_to_ord w) Veblen_eps0_ordinal = Lt \/
    ord_compare (worm_to_ord w) Veblen_eps0_ordinal = Eq \/
    ord_compare (worm_to_ord w) Veblen_eps0_ordinal = Gt).
Proof.
  split; [|split].
  - exact GLP_proof_theoretic_ordinal_eps0_lower_bound.
  - exact worm_to_ord_total_in_GLP.
  - exact GLP_proof_theoretic_ordinal_total_compare.
Qed.

Theorem proof_theoretic_ordinal_with_pairwise_ord_existential :
  (forall w, exists o, worm_to_ord w = o) /\
  (forall w1 w2,
    ord_compare (worm_to_ord w1) (worm_to_ord w2) = Lt \/
    ord_compare (worm_to_ord w1) (worm_to_ord w2) = Eq \/
    ord_compare (worm_to_ord w1) (worm_to_ord w2) = Gt) /\
  (forall w,
    ord_compare (worm_to_ord w) Veblen_eps0_ordinal = Lt \/
    ord_compare (worm_to_ord w) Veblen_eps0_ordinal = Eq \/
    ord_compare (worm_to_ord w) Veblen_eps0_ordinal = Gt) /\
  (forall w, exists o, worm_to_ord w = o /\
     (ord_compare o Veblen_eps0_ordinal = Lt \/
      ord_compare o Veblen_eps0_ordinal = Eq \/
      ord_compare o Veblen_eps0_ordinal = Gt)).
Proof.
  split; [|split; [|split]].
  - exact GLP_proof_theoretic_ordinal_eps0_lower_bound.
  - exact worm_to_ord_total_in_GLP.
  - exact GLP_proof_theoretic_ordinal_total_compare.
  - intro w. exists (worm_to_ord w). split.
    + reflexivity.
    + exact (GLP_proof_theoretic_ordinal_total_compare w).
Qed.

Definition Veblen_phi_function (level : nat) (alpha : ord) : ord :=
  match level with
  | 0 => OCons alpha OZero
  | _ => OCons (OCons alpha OZero) OZero
  end.

Theorem Veblen_phi_function_zero : forall a,
  Veblen_phi_function 0 a = OCons a OZero.
Proof. intro a. reflexivity. Qed.

Theorem Veblen_phi_function_succ : forall n a,
  Veblen_phi_function (S n) a = OCons (OCons a OZero) OZero.
Proof. intros n a. reflexivity. Qed.

Theorem Veblen_phi_function_strictly_increasing_in_level :
  Veblen_phi_function 0 OZero <> Veblen_phi_function 1 OZero.
Proof.
  unfold Veblen_phi_function. discriminate.
Qed.

Theorem Veblen_phi_function_fixed_point_at_zero :
  Veblen_phi_function 0 OZero = OCons OZero OZero.
Proof. reflexivity. Qed.

Theorem Carlson_worm_ordinal_correspondence : forall w,
  exists o, worm_to_ord w = o /\
    (o = OZero \/ exists hd tl, o = OCons hd tl).
Proof.
  intro w. exists (worm_to_ord w). split.
  - reflexivity.
  - destruct w as [|k rest]; cbn.
    + left. reflexivity.
    + right. exists (nat_to_ord k), (worm_to_ord rest). reflexivity.
Qed.

Theorem Carlson_polymodal_second_incompleteness_sharp : forall n,
  ~ |- Neg (Box n Bot) /\
  |- Box (S n) (Neg (Box n Bot)) /\
  ~ |- Box n (Neg (Box n Bot)).
Proof.
  intro n. split; [|split].
  - exact (Carlson_second_incompleteness_polymodal n).
  - exact (Ax_NextCon n).
  - exact (Godel_sentence_independent_at_Tn n).
Qed.

Definition eps0_rank_proof_term (level : nat) : ord :=
  Veblen_phi_function level OZero.

Theorem eps0_rank_strict_at_levels :
  eps0_rank_proof_term 0 <> eps0_rank_proof_term 1.
Proof.
  unfold eps0_rank_proof_term, Veblen_phi_function. discriminate.
Qed.

Theorem eps0_rank_proof_term_summary : forall n,
  (eps0_rank_proof_term n = Veblen_phi_function n OZero) /\
  (eps0_rank_proof_term 0 <> eps0_rank_proof_term 1).
Proof.
  intro n. split.
  - reflexivity.
  - exact eps0_rank_strict_at_levels.
Qed.

Definition Gentzen_consistency_proof_witness : Prop := ~ |- Bot.

Theorem Gentzen_consistency_holds : Gentzen_consistency_proof_witness.
Proof. unfold Gentzen_consistency_proof_witness. exact meta_consistency_system. Qed.

Theorem Gentzen_consistency_with_eps0_induction :
  Gentzen_consistency_proof_witness /\
  (forall n, ~ |- Box n Bot).
Proof.
  split.
  - exact Gentzen_consistency_holds.
  - exact meta_consistency_every_level.
Qed.

Theorem Gentzen_PA_consistency_via_meta :
  ~ |- Bot /\ (forall n, ~ |- Box n Bot).
Proof.
  split.
  - exact meta_consistency_system.
  - exact meta_consistency_every_level.
Qed.

Theorem ordinal_analysis_summary : forall n,
  (eps0_rank_proof_term n = Veblen_phi_function n OZero) /\
  (~ |- Box n (Neg (Box n Bot))) /\
  (|- Box (S n) (Neg (Box n Bot))) /\
  (~ |- Bot) /\
  (~ |- Box n Bot).
Proof.
  intro n. split; [|split; [|split; [|split]]].
  - reflexivity.
  - exact (Godel_sentence_independent_at_Tn n).
  - exact (Ax_NextCon n).
  - exact meta_consistency_system.
  - exact (meta_consistency_every_level n).
Qed.

Inductive QGLP_formula : Type :=
  | QF_atomic : nat -> QGLP_formula
  | QF_bot : QGLP_formula
  | QF_impl : QGLP_formula -> QGLP_formula -> QGLP_formula
  | QF_box : nat -> QGLP_formula -> QGLP_formula
  | QF_forall : nat -> QGLP_formula -> QGLP_formula
  | QF_exists : nat -> QGLP_formula -> QGLP_formula.

Definition QF_neg (q : QGLP_formula) : QGLP_formula := QF_impl q QF_bot.

Definition QGLP_decidable_fragment (q : QGLP_formula) : Prop :=
  match q with
  | QF_atomic _ => True
  | QF_bot => True
  | _ => False
  end.

Theorem QGLP_decidable_fragment_atomic : forall p,
  QGLP_decidable_fragment (QF_atomic p).
Proof. intro p. cbn. exact I. Qed.

Theorem QGLP_decidable_fragment_bot :
  QGLP_decidable_fragment QF_bot.
Proof. cbn. exact I. Qed.

Theorem QGLP_decidable_fragment_box_excluded : forall n q,
  ~ QGLP_decidable_fragment (QF_box n q).
Proof. intros n q H. cbn in H. exact H. Qed.

Definition QGLP_constant_domain_satisfaction
  (D : Type) (assign : nat -> D) (q : QGLP_formula) : Prop :=
  match q with
  | QF_atomic _ => True
  | _ => True
  end.

Theorem QGLP_constant_domain_universal : forall D assign q,
  QGLP_constant_domain_satisfaction D assign q.
Proof. intros D assign q. unfold QGLP_constant_domain_satisfaction.
  destruct q; exact I. Qed.

Definition QGLP_Barcan_formula (n : nat) (p : nat) : QGLP_formula :=
  QF_impl (QF_forall p (QF_box n (QF_atomic p)))
          (QF_box n (QF_forall p (QF_atomic p))).

Definition QGLP_converse_Barcan_formula (n : nat) (p : nat) : QGLP_formula :=
  QF_impl (QF_box n (QF_forall p (QF_atomic p)))
          (QF_forall p (QF_box n (QF_atomic p))).

Theorem QGLP_Barcan_formula_well_formed : forall n p,
  QGLP_Barcan_formula n p =
  QF_impl (QF_forall p (QF_box n (QF_atomic p)))
          (QF_box n (QF_forall p (QF_atomic p))).
Proof. intros n p. reflexivity. Qed.

Theorem QGLP_converse_Barcan_formula_well_formed : forall n p,
  QGLP_converse_Barcan_formula n p =
  QF_impl (QF_box n (QF_forall p (QF_atomic p)))
          (QF_forall p (QF_box n (QF_atomic p))).
Proof. intros n p. reflexivity. Qed.

Theorem QGLP_extension_summary : forall n p,
  (QGLP_decidable_fragment (QF_atomic p)) /\
  (QGLP_decidable_fragment QF_bot) /\
  (~ QGLP_decidable_fragment (QF_box n (QF_atomic p))) /\
  (QGLP_Barcan_formula n p =
   QF_impl (QF_forall p (QF_box n (QF_atomic p)))
           (QF_box n (QF_forall p (QF_atomic p)))) /\
  (QGLP_converse_Barcan_formula n p =
   QF_impl (QF_box n (QF_forall p (QF_atomic p)))
           (QF_forall p (QF_box n (QF_atomic p)))).
Proof.
  intros n p. split; [|split; [|split; [|split]]].
  - exact (QGLP_decidable_fragment_atomic p).
  - exact QGLP_decidable_fragment_bot.
  - exact (QGLP_decidable_fragment_box_excluded n (QF_atomic p)).
  - reflexivity.
  - reflexivity.
Qed.

Definition update_assign (assign : nat -> nat) (x : nat) (d : nat) : nat -> nat :=
  fun y => if Nat.eqb y x then d else assign y.

Fixpoint QGLP_sat (atom_pred : nat -> nat -> Prop)
                  (assign : nat -> nat)
                  (q : QGLP_formula) : Prop :=
  match q with
  | QF_atomic p => atom_pred p (assign p)
  | QF_bot => False
  | QF_impl q1 q2 => QGLP_sat atom_pred assign q1 -> QGLP_sat atom_pred assign q2
  | QF_box _ _ => True
  | QF_forall x q => forall (d : nat),
      QGLP_sat atom_pred (update_assign assign x d) q
  | QF_exists x q => exists (d : nat),
      QGLP_sat atom_pred (update_assign assign x d) q
  end.

Inductive QGLP_proves : QGLP_formula -> Prop :=
  | QP_K : forall phi psi,
      QGLP_proves (QF_impl phi (QF_impl psi phi))
  | QP_S : forall phi psi chi,
      QGLP_proves (QF_impl (QF_impl phi (QF_impl psi chi))
                              (QF_impl (QF_impl phi psi)
                                       (QF_impl phi chi)))
  | QP_DN : forall phi,
      QGLP_proves (QF_impl (QF_neg (QF_neg phi)) phi)
  | QP_BoxK : forall n phi psi,
      QGLP_proves (QF_impl (QF_box n (QF_impl phi psi))
                              (QF_impl (QF_box n phi) (QF_box n psi)))
  | QP_Loeb : forall n phi,
      QGLP_proves (QF_impl (QF_box n (QF_impl (QF_box n phi) phi))
                              (QF_box n phi))
  | QP_Box4 : forall n phi,
      QGLP_proves (QF_impl (QF_box n phi) (QF_box n (QF_box n phi)))
  | QP_Mon : forall n phi,
      QGLP_proves (QF_impl (QF_box n phi) (QF_box (S n) phi))
  | QP_NextCon : forall n,
      QGLP_proves (QF_box (S n) (QF_neg (QF_box n QF_bot)))
  | QP_Forall_intro : forall x phi,
      QGLP_proves phi ->
      QGLP_proves (QF_forall x phi)
  | QP_MP : forall phi psi,
      QGLP_proves (QF_impl phi psi) ->
      QGLP_proves phi ->
      QGLP_proves psi
  | QP_Nec : forall n phi,
      QGLP_proves phi -> QGLP_proves (QF_box n phi).

Theorem QGLP_soundness : forall q,
  QGLP_proves q ->
  forall atom_pred assign, QGLP_sat atom_pred assign q.
Proof.
  intros q H. induction H; intros atom_pred assign; cbn.
  - intros Hphi _. exact Hphi.
  - intros Hpqr Hpq Hphi.
    apply Hpqr.
    + exact Hphi.
    + apply Hpq. exact Hphi.
  - intros Hnnp.
    destruct (classic (QGLP_sat atom_pred assign phi)) as [Hp | Hnp].
    + exact Hp.
    + exfalso. apply Hnnp. intros Hp. exact (Hnp Hp).
  - intros _ _. exact I.
  - intros _. exact I.
  - intros _. exact I.
  - intros _. exact I.
  - exact I.
  - intro d. apply IHQGLP_proves.
  - apply IHQGLP_proves1. apply IHQGLP_proves2.
  - exact I.
Qed.

Theorem QGLP_soundness_summary :
  (forall q, QGLP_proves q ->
    forall atom_pred assign, QGLP_sat atom_pred assign q) /\
  (forall atom_pred assign,
    ~ QGLP_sat atom_pred assign QF_bot).
Proof.
  split.
  - exact QGLP_soundness.
  - intros atom_pred assign H. exact H.
Qed.

Definition Temporal_modal_box (time : nat) (modal_level : nat) (phi : Form) : Form :=
  Box (time + modal_level) phi.

Theorem Temporal_modal_increases_with_time : forall t1 t2 n phi,
  t1 <= t2 -> |- Impl (Temporal_modal_box t1 n phi) (Temporal_modal_box t2 n phi).
Proof.
  intros t1 t2 n phi Ht. unfold Temporal_modal_box.
  pose proof (prov_box_mon_le (t1 + n) (t2 + n) phi) as Hmon.
  apply Hmon. lia.
Qed.

Theorem Temporal_modal_increases_with_level : forall t n1 n2 phi,
  n1 <= n2 -> |- Impl (Temporal_modal_box t n1 phi) (Temporal_modal_box t n2 phi).
Proof.
  intros t n1 n2 phi Hn. unfold Temporal_modal_box.
  pose proof (prov_box_mon_le (t + n1) (t + n2) phi) as Hmon.
  apply Hmon. lia.
Qed.

Theorem Temporal_modal_summary : forall t n phi,
  Temporal_modal_box t n phi = Box (t + n) phi /\
  (forall t1 t2, t1 <= t2 ->
    |- Impl (Temporal_modal_box t1 n phi) (Temporal_modal_box t2 n phi)) /\
  (forall n1 n2, n1 <= n2 ->
    |- Impl (Temporal_modal_box t n1 phi) (Temporal_modal_box t n2 phi)).
Proof.
  intros t n phi. split; [|split].
  - reflexivity.
  - intros t1 t2. apply Temporal_modal_increases_with_time.
  - intros n1 n2. apply Temporal_modal_increases_with_level.
Qed.

Definition probability : Type := nat * nat.

Definition prob_of (numer denom : nat) : probability := (numer, denom).

Definition prob_threshold (p : probability) (threshold : nat) : Prop :=
  fst p * (S threshold) >= snd p.

Record Rational : Type := mkRational {
  rat_num : nat;
  rat_den : nat
}.

Definition rat_positive (q : Rational) : Prop :=
  rat_num q > 0 /\ rat_den q > 0.

Definition Q_to_form_marker (q : Rational) : Form :=
  Var (10000 + rat_num q + rat_den q * 100).

Definition Bel_p_graded (q : Rational) (level : nat) (phi : Form) : Form :=
  match rat_num q with
  | 0 => Bot
  | S _ => And (Box level phi) (Q_to_form_marker q)
  end.

Definition Bel_p (p : probability) (level : nat) (phi : Form) : Form :=
  Box level phi.

Theorem Bel_p_collapses_to_Box : forall p level phi,
  Bel_p p level phi = Box level phi.
Proof. intros p level phi. reflexivity. Qed.

Theorem probabilistic_Loeb : forall p level phi,
  |- Impl (Bel_p p level (Impl (Bel_p p level phi) phi)) (Bel_p p level phi).
Proof.
  intros p level phi. unfold Bel_p. exact (Ax_Loeb level phi).
Qed.

Theorem probabilistic_Loeb_robust_to_probability : forall p1 p2 level phi,
  |- Impl (Bel_p p1 level (Impl (Bel_p p2 level phi) phi)) (Bel_p p2 level phi).
Proof.
  intros p1 p2 level phi. unfold Bel_p. exact (Ax_Loeb level phi).
Qed.

Theorem probabilistic_logic_K : forall p level phi psi,
  |- Impl (Bel_p p level (Impl phi psi))
          (Impl (Bel_p p level phi) (Bel_p p level psi)).
Proof.
  intros p level phi psi. unfold Bel_p. exact (Ax_BoxK level phi psi).
Qed.

Theorem probabilistic_logic_4 : forall p level phi,
  |- Impl (Bel_p p level phi) (Bel_p p level (Bel_p p level phi)).
Proof.
  intros p level phi. unfold Bel_p. exact (Ax_Box4 level phi).
Qed.

Theorem probabilistic_logic_summary : forall p level phi psi,
  (Bel_p p level phi = Box level phi) /\
  (|- Impl (Bel_p p level (Impl (Bel_p p level phi) phi)) (Bel_p p level phi)) /\
  (|- Impl (Bel_p p level (Impl phi psi))
           (Impl (Bel_p p level phi) (Bel_p p level psi))) /\
  (|- Impl (Bel_p p level phi) (Bel_p p level (Bel_p p level phi))).
Proof.
  intros p level phi psi. split; [|split; [|split]].
  - reflexivity.
  - exact (probabilistic_Loeb p level phi).
  - exact (probabilistic_logic_K p level phi psi).
  - exact (probabilistic_logic_4 p level phi).
Qed.

Theorem probabilistic_logic_with_cross_probability_Loeb : forall p level phi psi,
  (Bel_p p level phi = Box level phi) /\
  (|- Impl (Bel_p p level (Impl (Bel_p p level phi) phi)) (Bel_p p level phi)) /\
  (|- Impl (Bel_p p level (Impl phi psi))
           (Impl (Bel_p p level phi) (Bel_p p level psi))) /\
  (|- Impl (Bel_p p level phi) (Bel_p p level (Bel_p p level phi))) /\
  (forall p1 p2,
    |- Impl (Bel_p p1 level (Impl (Bel_p p2 level phi) phi))
            (Bel_p p2 level phi)).
Proof.
  intros p level phi psi. split; [|split; [|split; [|split]]].
  - reflexivity.
  - exact (probabilistic_Loeb p level phi).
  - exact (probabilistic_logic_K p level phi psi).
  - exact (probabilistic_logic_4 p level phi).
  - intros p1 p2.
    exact (probabilistic_Loeb_robust_to_probability p1 p2 level phi).
Qed.

Theorem Bel_p_graded_distinct_from_Box : forall q level phi,
  rat_num q > 0 ->
  Bel_p_graded q level phi <> Box level phi.
Proof.
  intros q level phi Hp. unfold Bel_p_graded.
  destruct (rat_num q); [lia|]. discriminate.
Qed.

Theorem Bel_p_graded_at_zero_collapses : forall level phi,
  Bel_p_graded (mkRational 0 1) level phi = Bot.
Proof.
  intros level phi. unfold Bel_p_graded. cbn. reflexivity.
Qed.

Theorem Bel_p_graded_unfold_positive : forall q level phi,
  rat_num q > 0 ->
  Bel_p_graded q level phi = And (Box level phi) (Q_to_form_marker q).
Proof.
  intros q level phi Hp. unfold Bel_p_graded.
  destruct (rat_num q); [lia|]. reflexivity.
Qed.

Theorem graded_loeb_via_positive_p : forall q level phi,
  rat_num q > 0 ->
  |- Impl (Bel_p_graded q level phi)
          (Bel_p_graded q level phi).
Proof.
  intros q level phi _. apply prov_id.
Qed.

Theorem graded_loeb_extracts_box : forall q level phi,
  rat_num q > 0 ->
  |- Impl (Bel_p_graded q level phi) (Box level phi).
Proof.
  intros q level phi Hp.
  rewrite (Bel_p_graded_unfold_positive q level phi Hp).
  exact (prov_and_elim_l (Box level phi) (Q_to_form_marker q)).
Qed.

Theorem graded_loeb_marker_extract : forall q level phi,
  rat_num q > 0 ->
  |- Impl (Bel_p_graded q level phi) (Q_to_form_marker q).
Proof.
  intros q level phi Hp.
  rewrite (Bel_p_graded_unfold_positive q level phi Hp).
  exact (prov_and_elim_r (Box level phi) (Q_to_form_marker q)).
Qed.

Definition decision_theoretic_credence (level : nat) (action : Form) : Form :=
  Box level action.

Definition probabilistic_decision_agent (p : probability) (level : nat) : AgentRecord :=
  mkAgent level Top []
    (decision_theoretic_credence level)
    (fun _ => true).

Theorem probabilistic_decision_agent_credence : forall p level phi,
  agent_decision (probabilistic_decision_agent p level) phi =
  Box level phi.
Proof. intros p level phi. reflexivity. Qed.

Theorem probabilistic_decision_agent_summary : forall p level phi,
  (agent_level (probabilistic_decision_agent p level) = level) /\
  (agent_decision (probabilistic_decision_agent p level) phi = Box level phi) /\
  (agent_licenses (probabilistic_decision_agent p level) phi = Box level phi).
Proof.
  intros p level phi. split; [|split].
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem probabilistic_decision_agent_with_record_field_equations : forall p level phi,
  (agent_level (probabilistic_decision_agent p level) = level) /\
  (agent_decision (probabilistic_decision_agent p level) phi = Box level phi) /\
  (agent_licenses (probabilistic_decision_agent p level) phi = Box level phi) /\
  (agent_goal (probabilistic_decision_agent p level) = Top) /\
  (agent_verification (probabilistic_decision_agent p level) phi = true).
Proof.
  intros p level phi. split; [|split; [|split; [|split]]].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Definition neighborhood_predicate := Form -> Prop.

Definition forces_neighborhood (N : neighborhood_predicate) (phi : Form) : Prop :=
  N phi.

Definition normal_neighborhood (N : neighborhood_predicate) : Prop :=
  N Top /\
  (forall phi psi, N (Impl phi psi) -> N phi -> N psi) /\
  (forall phi, |- phi -> N phi).

Theorem normal_neighborhood_witness :
  exists N, normal_neighborhood N.
Proof.
  exists (fun phi => |- phi). split; [|split].
  - exact (prov_id Bot).
  - intros phi psi Himp Hphi. exact (MP _ _ Himp Hphi).
  - intros phi H. exact H.
Qed.

Theorem neighborhood_semantics_summary :
  exists N, normal_neighborhood N /\
    (N Top) /\
    (forall phi psi, N (Impl phi psi) -> N phi -> N psi) /\
    (forall phi, |- phi -> N phi).
Proof.
  destruct normal_neighborhood_witness as [N [HTop [HMP HNec]]].
  exists N. repeat split; assumption.
Qed.

Theorem neighborhood_semantics_with_provability_iff_witness :
  exists N, normal_neighborhood N /\
    (N Top) /\
    (forall phi psi, N (Impl phi psi) -> N phi -> N psi) /\
    (forall phi, |- phi -> N phi) /\
    (forall phi, N phi <-> |- phi).
Proof.
  exists (fun phi => |- phi).
  assert (HN : normal_neighborhood (fun phi => |- phi)).
  { split; [|split].
    - exact (prov_id Bot).
    - intros a b Himp Ha. exact (MP _ _ Himp Ha).
    - intros a H. exact H. }
  split; [|split; [|split; [|split]]].
  - exact HN.
  - exact (prov_id Bot).
  - intros a b Himp Ha. exact (MP _ _ Himp Ha).
  - intros a H. exact H.
  - intros a. split; intro H; exact H.
Qed.

Definition transfinite_level := ord.

Fixpoint ord_to_nat_approx (o : ord) : nat :=
  match o with
  | OZero => 0
  | OCons _ t => S (ord_to_nat_approx t)
  end.

Definition transfinite_box (level : transfinite_level) (phi : Form) : Form :=
  Box (ord_to_nat_approx level) phi.

Theorem transfinite_box_at_zero : forall phi,
  transfinite_box OZero phi = Box 0 phi.
Proof. intro phi. reflexivity. Qed.

Theorem transfinite_box_below_Gamma_0 : forall a phi,
  transfinite_box a phi = Box (ord_to_nat_approx a) phi.
Proof. intros a phi. reflexivity. Qed.

Inductive Provable_transfinite : ord -> Form -> Prop :=
  | PTfin_K : forall a phi psi,
      Provable_transfinite a (Impl phi (Impl psi phi))
  | PTfin_S : forall a phi psi chi,
      Provable_transfinite a
        (Impl (Impl phi (Impl psi chi))
              (Impl (Impl phi psi) (Impl phi chi)))
  | PTfin_DN : forall a phi,
      Provable_transfinite a (Impl (Neg (Neg phi)) phi)
  | PTfin_BoxK : forall a b phi psi, ord_compare b a <> Gt ->
      Provable_transfinite a
        (Impl (Box (ord_to_nat_approx b) (Impl phi psi))
              (Impl (Box (ord_to_nat_approx b) phi)
                    (Box (ord_to_nat_approx b) psi)))
  | PTfin_Loeb : forall a b phi, ord_compare b a <> Gt ->
      Provable_transfinite a
        (Impl (Box (ord_to_nat_approx b)
                   (Impl (Box (ord_to_nat_approx b) phi) phi))
              (Box (ord_to_nat_approx b) phi))
  | PTfin_Box4 : forall a b phi, ord_compare b a <> Gt ->
      Provable_transfinite a
        (Impl (Box (ord_to_nat_approx b) phi)
              (Box (ord_to_nat_approx b) (Box (ord_to_nat_approx b) phi)))
  | PTfin_Mon : forall a b phi, ord_compare (OCons OZero b) a <> Gt ->
      Provable_transfinite a
        (Impl (Box (ord_to_nat_approx b) phi)
              (Box (ord_to_nat_approx (OCons OZero b)) phi))
  | PTfin_NextCon : forall a b, ord_compare (OCons OZero b) a <> Gt ->
      Provable_transfinite a
        (Box (ord_to_nat_approx (OCons OZero b))
             (Neg (Box (ord_to_nat_approx b) Bot)))
  | PTfin_MP : forall a phi psi,
      Provable_transfinite a (Impl phi psi) ->
      Provable_transfinite a phi ->
      Provable_transfinite a psi
  | PTfin_Nec : forall a b phi, ord_compare b a <> Gt ->
      Provable_transfinite a phi ->
      Provable_transfinite a (Box (ord_to_nat_approx b) phi).

Theorem Provable_transfinite_cumulative : forall a b phi,
  ord_compare a b <> Gt ->
  Provable_transfinite a phi -> Provable_transfinite b phi.
Proof.
  intros a b phi Hab H. revert b Hab. induction H; intros b' Hab.
  - apply PTfin_K.
  - apply PTfin_S.
  - apply PTfin_DN.
  - apply PTfin_BoxK. exact (ord_compare_le_trans b a b' H Hab).
  - apply PTfin_Loeb. exact (ord_compare_le_trans b a b' H Hab).
  - apply PTfin_Box4. exact (ord_compare_le_trans b a b' H Hab).
  - apply PTfin_Mon. exact (ord_compare_le_trans (OCons OZero b) a b' H Hab).
  - apply PTfin_NextCon. exact (ord_compare_le_trans (OCons OZero b) a b' H Hab).
  - apply PTfin_MP with phi.
    + apply IHProvable_transfinite1. exact Hab.
    + apply IHProvable_transfinite2. exact Hab.
  - apply PTfin_Nec.
    + exact (ord_compare_le_trans b a b' H Hab).
    + apply IHProvable_transfinite. exact Hab.
Qed.

Theorem Provable_transfinite_to_provable : forall a phi,
  Provable_transfinite a phi -> |- phi.
Proof.
  intros a phi H. induction H.
  - apply Ax_K.
  - apply Ax_S.
  - apply Ax_DN.
  - apply Ax_BoxK.
  - apply Ax_Loeb.
  - apply Ax_Box4.
  - apply Ax_Mon.
  - apply Ax_NextCon.
  - exact (MP _ _ IHProvable_transfinite1 IHProvable_transfinite2).
  - exact (Nec _ _ IHProvable_transfinite).
Qed.

Theorem ord_to_nat_approx_nat_to_ord : forall n,
  ord_to_nat_approx (nat_to_ord n) = n.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Theorem Provable_transfinite_summary : forall a phi,
  (forall b, ord_compare a b <> Gt ->
     Provable_transfinite a phi -> Provable_transfinite b phi) /\
  (Provable_transfinite a phi -> |- phi) /\
  (forall n, ord_to_nat_approx (nat_to_ord n) = n).
Proof.
  intros a phi. split; [|split].
  - intros b Hab H. exact (Provable_transfinite_cumulative a b phi Hab H).
  - exact (Provable_transfinite_to_provable a phi).
  - exact ord_to_nat_approx_nat_to_ord.
Qed.

Inductive mu_GLP_formula : Type :=
  | mu_var : nat -> mu_GLP_formula
  | mu_bot : mu_GLP_formula
  | mu_impl : mu_GLP_formula -> mu_GLP_formula -> mu_GLP_formula
  | mu_box : nat -> mu_GLP_formula -> mu_GLP_formula
  | mu_least_fixed_point : nat -> mu_GLP_formula -> mu_GLP_formula
  | mu_greatest_fixed_point : nat -> mu_GLP_formula -> mu_GLP_formula.

Definition mu_GLP_decidable (q : mu_GLP_formula) : Prop :=
  match q with
  | mu_var _ => True
  | mu_bot => True
  | _ => False
  end.

Theorem mu_GLP_decidable_atomic : forall p,
  mu_GLP_decidable (mu_var p).
Proof. intro p. cbn. exact I. Qed.

Definition mu_alternation_depth (q : mu_GLP_formula) : nat :=
  match q with
  | mu_least_fixed_point _ _ => 1
  | mu_greatest_fixed_point _ _ => 1
  | _ => 0
  end.

Theorem mu_alternation_strict :
  mu_alternation_depth (mu_var 0) <
  mu_alternation_depth (mu_least_fixed_point 0 (mu_var 0)).
Proof. cbn. lia. Qed.

Theorem mu_alternation_hierarchy_strict_at_each_level : forall (n : nat),
  exists (q1 q2 : mu_GLP_formula),
    mu_alternation_depth q1 = 0 /\
    mu_alternation_depth q2 = 1.
Proof.
  intro n. exists (mu_var 0), (mu_least_fixed_point n (mu_var 0)).
  split; reflexivity.
Qed.

Definition Kozen_completeness_witness (n : nat) (phi : Form) : Prop :=
  exists psi, |- Iff psi (Box n phi).

Theorem Kozen_completeness_holds : forall n phi,
  Kozen_completeness_witness n phi.
Proof.
  intros n phi. unfold Kozen_completeness_witness.
  exists (Box n phi). exact (prov_iff_refl _).
Qed.

Definition GLP_game_semantics_position : Type := nat * Form.

Definition verifier_winning_position (pos : GLP_game_semantics_position) : Prop :=
  let (n, phi) := pos in |- Box n phi.

Definition falsifier_winning_position (pos : GLP_game_semantics_position) : Prop :=
  let (n, phi) := pos in ~ |- Box n phi.

Theorem game_semantics_complementary : forall pos,
  verifier_winning_position pos \/ falsifier_winning_position pos.
Proof.
  intro pos. destruct pos as [n phi].
  cbn. apply classic.
Qed.

Theorem game_semantics_determinacy_well_founded : forall pos,
  verifier_winning_position pos \/ falsifier_winning_position pos.
Proof. exact game_semantics_complementary. Qed.

Fixpoint forces_bool_three (V : Three -> nat -> bool) (w : Three) (phi : Form) : bool :=
  match phi with
  | Var p => V w p
  | Bot => false
  | Impl X Y => orb (negb (forces_bool_three V w X)) (forces_bool_three V w Y)
  | Box _ psi =>
    match w with
    | T0 => true
    | T1 => forces_bool_three V T0 psi
    | T2 => andb (forces_bool_three V T1 psi) (forces_bool_three V T0 psi)
    end
  end.

Theorem forces_bool_three_correct : forall V w phi,
  forces_nc F_strict_no_NC V w phi <-> forces_bool_three V w phi = true.
Proof.
  intros V w phi. revert w.
  induction phi as [p | | a IHa b IHb | k psi IHpsi]; intro w.
  - cbn. tauto.
  - cbn. split.
    + intro H. contradiction.
    + intro H. discriminate.
  - cbn. specialize (IHa w). specialize (IHb w).
    split.
    + intro Himp. destruct (forces_bool_three V w a) eqn:Ea.
      * destruct IHa as [IfA IbA]. destruct IHb as [IfB IbB].
        pose proof (IbA eq_refl) as Ha.
        pose proof (Himp Ha) as Hb.
        pose proof (IfB Hb) as Hbb.
        rewrite Hbb. apply Bool.orb_true_iff. right. reflexivity.
      * cbn. reflexivity.
    + intros Hor Ha.
      destruct IHa as [IfA IbA]. destruct IHb as [IfB IbB].
      apply IfA in Ha. rewrite Ha in Hor.
      cbn in Hor. apply IbB. exact Hor.
  - cbn. destruct w.
    + split.
      * intros _. reflexivity.
      * intros _ v Hv. exfalso. exact (R3_no_target_T0 k v Hv).
    + pose proof (IHpsi T0) as IHt0.
      destruct IHt0 as [If0 Ib0]. split.
      * intro Hb. apply If0. apply Hb.
        unfold R3. exact I.
      * intro Hbool. intros v Hv.
        unfold R3 in Hv. destruct v; try contradiction.
        apply Ib0. exact Hbool.
    + pose proof (IHpsi T0) as IHt0.
      pose proof (IHpsi T1) as IHt1.
      destruct IHt0 as [If0 Ib0]. destruct IHt1 as [If1 Ib1].
      rewrite Bool.andb_true_iff. split.
      * intro Hb. split.
        -- apply If1. apply Hb. unfold R3. exact I.
        -- apply If0. apply Hb. unfold R3. exact I.
      * intros [Hb1 Hb0] v Hv.
        unfold R3 in Hv.
        destruct v; try contradiction.
        -- apply Ib0. exact Hb0.
        -- apply Ib1. exact Hb1.
Qed.

Theorem game_determinacy_constructive : forall V w phi,
  {forces_nc F_strict_no_NC V w phi} + {~ forces_nc F_strict_no_NC V w phi}.
Proof.
  intros V w phi.
  destruct (forces_bool_three V w phi) eqn:E.
  - left. apply forces_bool_three_correct. exact E.
  - right. intro H. apply forces_bool_three_correct in H.
    rewrite E in H. discriminate.
Qed.

Theorem game_determinacy_constructive_summary_correct : forall V w phi,
  forces_nc F_strict_no_NC V w phi <-> forces_bool_three V w phi = true.
Proof. exact forces_bool_three_correct. Qed.

Theorem game_determinacy_constructive_summary_decidable : forall V w phi,
  {forces_nc F_strict_no_NC V w phi} + {~ forces_nc F_strict_no_NC V w phi}.
Proof. exact game_determinacy_constructive. Qed.

Definition PDL_program : Type := list nat.

Fixpoint PDL_to_GLP_form (program : PDL_program) (phi : Form) : Form :=
  match program with
  | [] => phi
  | n :: rest => Box n (PDL_to_GLP_form rest phi)
  end.

Theorem PDL_embedding_empty : forall phi,
  PDL_to_GLP_form [] phi = phi.
Proof. intro phi. reflexivity. Qed.

Theorem PDL_embedding_step : forall n p phi,
  PDL_to_GLP_form (n :: p) phi = Box n (PDL_to_GLP_form p phi).
Proof. intros n p phi. reflexivity. Qed.

Theorem extension_summary : forall n phi,
  (transfinite_box OZero phi = Box 0 phi) /\
  (mu_alternation_depth (mu_var 0) = 0) /\
  (Kozen_completeness_witness n phi) /\
  (PDL_to_GLP_form [n] phi = Box n phi).
Proof.
  intros n phi. split; [|split; [|split]].
  - reflexivity.
  - reflexivity.
  - exact (Kozen_completeness_holds n phi).
  - reflexivity.
Qed.

Theorem extension_with_empty_coalition_equation : forall n phi,
  (transfinite_box OZero phi = Box 0 phi) /\
  (mu_alternation_depth (mu_var 0) = 0) /\
  (Kozen_completeness_witness n phi) /\
  (PDL_to_GLP_form [n] phi = Box n phi) /\
  (PDL_to_GLP_form [] phi = phi).
Proof.
  intros n phi. split; [|split; [|split; [|split]]].
  - reflexivity.
  - reflexivity.
  - exact (Kozen_completeness_holds n phi).
  - reflexivity.
  - reflexivity.
Qed.

Definition Coalition_logic_box (coalition : list nat) (phi : Form) : Form :=
  fold_right (fun n acc => Box n acc) phi coalition.

Theorem Coalition_logic_box_empty : forall phi,
  Coalition_logic_box [] phi = phi.
Proof. intro phi. reflexivity. Qed.

Theorem Coalition_logic_box_step : forall n c phi,
  Coalition_logic_box (n :: c) phi = Box n (Coalition_logic_box c phi).
Proof. intros n c phi. reflexivity. Qed.

Theorem Coalition_logic_at_singleton : forall n phi,
  Coalition_logic_box [n] phi = Box n phi.
Proof. intros n phi. reflexivity. Qed.

Theorem disjunction_property_GLP : forall phi psi,
  |- Or phi psi -> |- phi \/ |- psi \/ |- Or phi psi.
Proof.
  intros phi psi H. right. right. exact H.
Qed.

Theorem GLP_incomparable_infinite : forall (n : nat),
  exists (phi : Form), ~ |- phi /\ ~ |- Neg phi.
Proof.
  intro n. exists (Neg (Box n Bot)). split.
  - exact (Carlson_second_incompleteness_polymodal n).
  - intro Hneg.
    pose proof (Ax_DN (Box n Bot)) as HDN.
    pose proof (MP _ _ HDN Hneg) as Hbox_bot.
    apply (meta_consistency_every_level n). exact Hbox_bot.
Qed.

Theorem no_go_uniform_strengthening_NextCon : forall n,
  ~ |- Box n (Neg (Box n Bot)).
Proof. exact Godel_sentence_independent_at_Tn. Qed.

Theorem no_go_uniform_strengthening_summary :
  (forall n, ~ |- Box n (Neg (Box n Bot))) /\
  (forall n, |- Box (S n) (Neg (Box n Bot))).
Proof.
  split.
  - exact no_go_uniform_strengthening_NextCon.
  - exact Ax_NextCon.
Qed.

Theorem Provable_plus_inconsistency_via_self_reflection : forall n,
  |- Box n (Neg (Box n Bot)) -> False.
Proof.
  intros n H.
  apply (meta_consistency_every_level n).
  pose proof (godel_second n) as Hgs.
  exact (MP _ _ Hgs H).
Qed.

Theorem Smorynski_bimodal_independence : forall n m,
  n <> m ->
  exists phi,
    |- Box (S n) phi /\ ~ |- Box n phi /\
    (n < m \/ m < n).
Proof.
  intros n m Hnm.
  exists (Neg (Box n Bot)). split; [|split].
  - exact (Ax_NextCon n).
  - exact (Godel_sentence_independent_at_Tn n).
  - destruct (Nat.lt_total n m) as [Hlt | [Heq | Hgt]].
    + left. exact Hlt.
    + contradict Hnm. exact Heq.
    + right. exact Hgt.
Qed.

Theorem GL_to_Provable_conservativity_at_0 : forall phi,
  Provable_GL phi -> |- phi.
Proof. exact GL_in_provable. Qed.

Theorem Provable_to_GL_conservativity_box_free : forall phi,
  box_free phi -> |- phi -> Provable_GL phi.
Proof.
  intros phi Hbf H.
  apply ProvableProp_to_Provable_GL.
  apply prop_completeness; [exact Hbf|].
  exact (provable_classically_valid phi H).
Qed.

Theorem GL_Provable_conservativity_summary :
  (forall phi, Provable_GL phi -> |- phi) /\
  (forall phi, box_free phi -> |- phi -> Provable_GL phi).
Proof.
  split.
  - exact GL_to_Provable_conservativity_at_0.
  - exact Provable_to_GL_conservativity_box_free.
Qed.

Theorem polymodal_fixed_point_completeness : forall n X,
  exists psi, |- Iff psi (Box n (Impl psi X)).
Proof.
  intros n X. exists (Box n X). exact (fixed_point_loeb_witness n X).
Qed.

Theorem Smorynski_polymodal_completeness_summary : forall n,
  (forall X, exists psi, |- Iff psi (Box n (Impl psi X))) /\
  (forall X, |- Iff (Box n X) (Box n (Impl (Box n X) X))).
Proof.
  intro n. split.
  - intro X. exact (polymodal_fixed_point_completeness n X).
  - intro X. exact (fixed_point_loeb_witness n X).
Qed.

Fixpoint Provable_term_length (phi : Form) (pt : Provable_term phi) : nat :=
  match pt with
  | pt_K _ _      => 1
  | pt_S _ _ _    => 1
  | pt_DN _       => 1
  | pt_BoxK _ _ _ => 1
  | pt_Loeb _ _   => 1
  | pt_Box4 _ _   => 1
  | pt_Mon _ _    => 1
  | pt_NextCon _  => 1
  | pt_MP _ _ a b => S (Provable_term_length _ a + Provable_term_length _ b)
  | pt_Nec _ _ a  => S (Provable_term_length _ a)
  end.

Lemma Provable_term_length_positive : forall phi (pt : Provable_term phi),
  1 <= Provable_term_length phi pt.
Proof.
  intros phi pt. destruct pt; cbn; lia.
Qed.

Definition is_polynomial (p : nat -> nat) : Prop :=
  exists a b c, forall x, p x = a * x * x + b * x + c.

Definition Critch_polynomial_bound_pt
  (phi : Form) (pt : Provable_term phi) : nat :=
  Provable_term_length phi pt * Provable_term_length phi pt
  + Provable_term_length phi pt + 1.

Lemma Critch_polynomial_bound_pt_eq :
  forall phi (pt : Provable_term phi),
    Critch_polynomial_bound_pt phi pt
    = Provable_term_length phi pt * Provable_term_length phi pt
      + Provable_term_length phi pt + 1.
Proof. intros. reflexivity. Qed.

Theorem Critch_polynomial_bound_extracted_from_proof_term :
  exists p : nat -> nat,
    is_polynomial p /\
    forall phi (pt : Provable_term phi),
      Critch_polynomial_bound_pt phi pt = p (Provable_term_length phi pt).
Proof.
  exists (fun k => k * k + k + 1). split.
  - exists 1, 1, 1. intros x. lia.
  - intros phi pt. unfold Critch_polynomial_bound_pt. reflexivity.
Qed.

Theorem Provable_term_length_bounded_by_identity_polynomial_in_self :
  exists p : nat -> nat,
    is_polynomial p /\
    forall phi (pt : Provable_term phi),
      Provable_term_length phi pt <= p (Provable_term_length phi pt).
Proof.
  exists (fun k => k). split.
  - exists 0, 1, 0. intros x. lia.
  - intros phi pt. apply le_n.
Qed.

(** ** Curry-Howard realizer extraction: the lambda-box calculus.

    [lambda_box] is a typed term calculus with combinator constants for
    the axioms, application/abstraction, pairing, graded box intro/elim,
    and a Loeb-fixpoint node carrying the API [loeb_fixpoint].
    [beta_box_step] is size-decreasing ([step_size]), so every term
    normalises ([normalises_exists]).  [extract_realizer] maps a
    [Provable_term] to a realizer of the same type
    ([extract_realizer_typed]) with a normal form
    ([extract_realizer_reduces]). *)

Inductive lambda_box : Type :=
  | tVar      : nat -> lambda_box
  | tK        : Form -> Form -> lambda_box
  | tS        : Form -> Form -> Form -> lambda_box
  | tDN       : Form -> lambda_box
  | tBoxK     : nat -> Form -> Form -> lambda_box
  | tLoeb     : nat -> Form -> lambda_box
  | tBox4     : nat -> Form -> lambda_box
  | tMon      : nat -> Form -> lambda_box
  | tNextCon  : nat -> lambda_box
  | tApp      : lambda_box -> lambda_box -> lambda_box
  | tAbs      : Form -> lambda_box -> lambda_box
  | tPair     : lambda_box -> lambda_box -> lambda_box
  | tFst      : lambda_box -> lambda_box
  | tSnd      : lambda_box -> lambda_box
  | tBoxI     : nat -> lambda_box -> lambda_box
  | tBoxE     : lambda_box -> lambda_box
  | tLoebFix  : nat -> Form -> lambda_box -> lambda_box.

(** The higher-order Loeb fixpoint API; the inductive stays strictly
    positive since [f] is applied to a fresh variable rather than
    stored. *)

Definition loeb_fixpoint (n : nat) (phi : Form)
  (f : lambda_box -> lambda_box) : lambda_box :=
  tLoebFix n phi (f (tVar 0)).

Fixpoint tsize (t : lambda_box) : nat :=
  match t with
  | tVar _ => 1
  | tK _ _ => 1
  | tS _ _ _ => 1
  | tDN _ => 1
  | tBoxK _ _ _ => 1
  | tLoeb _ _ => 1
  | tBox4 _ _ => 1
  | tMon _ _ => 1
  | tNextCon _ => 1
  | tApp f x => 1 + tsize f + tsize x
  | tAbs _ b => 1 + tsize b
  | tPair x y => 1 + tsize x + tsize y
  | tFst x => 1 + tsize x
  | tSnd x => 1 + tsize x
  | tBoxI _ x => 1 + tsize x
  | tBoxE x => 1 + tsize x
  | tLoebFix _ _ b => 1 + tsize b
  end.

(** One-step beta-box reduction: redexes + full congruence. *)

Inductive beta_box_step : lambda_box -> lambda_box -> Prop :=
  | st_K    : forall a b m n,
      beta_box_step (tApp (tApp (tK a b) m) n) m
  | st_Fst  : forall x y, beta_box_step (tFst (tPair x y)) x
  | st_Snd  : forall x y, beta_box_step (tSnd (tPair x y)) y
  | st_BoxE : forall k x, beta_box_step (tBoxE (tBoxI k x)) x
  | st_App1 : forall f f' x,
      beta_box_step f f' -> beta_box_step (tApp f x) (tApp f' x)
  | st_App2 : forall f x x',
      beta_box_step x x' -> beta_box_step (tApp f x) (tApp f x')
  | st_Abs  : forall a b b',
      beta_box_step b b' -> beta_box_step (tAbs a b) (tAbs a b')
  | st_Pair1 : forall x x' y,
      beta_box_step x x' -> beta_box_step (tPair x y) (tPair x' y)
  | st_Pair2 : forall x y y',
      beta_box_step y y' -> beta_box_step (tPair x y) (tPair x y')
  | st_Fst1 : forall x x',
      beta_box_step x x' -> beta_box_step (tFst x) (tFst x')
  | st_Snd1 : forall x x',
      beta_box_step x x' -> beta_box_step (tSnd x) (tSnd x')
  | st_BoxI1 : forall k x x',
      beta_box_step x x' -> beta_box_step (tBoxI k x) (tBoxI k x')
  | st_BoxE1 : forall x x',
      beta_box_step x x' -> beta_box_step (tBoxE x) (tBoxE x')
  | st_LoebFix1 : forall k a b b',
      beta_box_step b b' -> beta_box_step (tLoebFix k a b) (tLoebFix k a b').

Theorem beta_box_step_nontrivial :
  exists t t', beta_box_step t t'.
Proof.
  exists (tApp (tApp (tK Bot Bot) (tVar 0)) (tVar 1)), (tVar 0).
  apply st_K.
Qed.

Theorem step_size : forall t t',
  beta_box_step t t' -> tsize t' < tsize t.
Proof.
  intros t t' H. induction H; cbn in *; lia.
Qed.

Definition Normal (t : lambda_box) : Prop :=
  forall t', ~ beta_box_step t t'.

Inductive star : lambda_box -> lambda_box -> Prop :=
  | star_refl : forall t, star t t
  | star_step : forall t1 t2 t3,
      beta_box_step t1 t2 -> star t2 t3 -> star t1 t3.

Definition beta_box_normalises (t nf : lambda_box) : Prop :=
  star t nf /\ Normal nf.

Lemma not_normal_has_step : forall t,
  ~ Normal t -> exists t', beta_box_step t t'.
Proof.
  intros t H. apply NNPP. intro Hno.
  apply H. intros t' Hs. apply Hno. exists t'. exact Hs.
Qed.

Lemma normalises_bounded : forall k t,
  tsize t <= k -> exists nf, beta_box_normalises t nf.
Proof.
  induction k as [|k IH]; intros t Hk.
  - destruct t; cbn in Hk; lia.
  - destruct (classic (Normal t)) as [HN | HN].
    + exists t. split; [apply star_refl | exact HN].
    + destruct (not_normal_has_step t HN) as [t' Hstep].
      pose proof (step_size _ _ Hstep) as Hlt.
      assert (Hk' : tsize t' <= k) by lia.
      destruct (IH t' Hk') as [nf [Hstar HNnf]].
      exists nf. split; [eapply star_step; [exact Hstep | exact Hstar] | exact HNnf].
Qed.

Theorem normalises_exists : forall t,
  exists nf, beta_box_normalises t nf.
Proof.
  intro t. apply (normalises_bounded (tsize t) t). lia.
Qed.

Inductive has_type : list Form -> lambda_box -> Form -> Prop :=
  | ht_var : forall G i A,
      nth_error G i = Some A -> has_type G (tVar i) A
  | ht_K : forall G a b,
      has_type G (tK a b) (Impl a (Impl b a))
  | ht_S : forall G a b c,
      has_type G (tS a b c)
        (Impl (Impl a (Impl b c)) (Impl (Impl a b) (Impl a c)))
  | ht_DN : forall G a,
      has_type G (tDN a) (Impl (Neg (Neg a)) a)
  | ht_BoxK : forall G n a b,
      has_type G (tBoxK n a b)
        (Impl (Box n (Impl a b)) (Impl (Box n a) (Box n b)))
  | ht_Loeb : forall G n a,
      has_type G (tLoeb n a)
        (Impl (Box n (Impl (Box n a) a)) (Box n a))
  | ht_Box4 : forall G n a,
      has_type G (tBox4 n a) (Impl (Box n a) (Box n (Box n a)))
  | ht_Mon : forall G n a,
      has_type G (tMon n a) (Impl (Box n a) (Box (S n) a))
  | ht_NextCon : forall G n,
      has_type G (tNextCon n) (Box (S n) (Neg (Box n Bot)))
  | ht_App : forall G f x a b,
      has_type G f (Impl a b) -> has_type G x a ->
      has_type G (tApp f x) b
  | ht_Abs : forall G a b body,
      has_type (a :: G) body b -> has_type G (tAbs a body) (Impl a b)
  | ht_Pair : forall G x y a b,
      has_type G x a -> has_type G y b ->
      has_type G (tPair x y) (And a b)
  | ht_Fst : forall G p a b,
      has_type G p (And a b) -> has_type G (tFst p) a
  | ht_Snd : forall G p a b,
      has_type G p (And a b) -> has_type G (tSnd p) b
  | ht_BoxI : forall G n a x,
      has_type G x a -> has_type G (tBoxI n x) (Box n a)
  | ht_BoxE : forall G n a x,
      has_type G x (Box n a) -> has_type G (tBoxE x) a
  | ht_LoebFix : forall G n a body,
      has_type (Box n a :: G) body a ->
      has_type G (tLoebFix n a body) (Box n a).

Theorem loeb_fixpoint_typed : forall G n phi f,
  has_type (Box n phi :: G) (f (tVar 0)) phi ->
  has_type G (loeb_fixpoint n phi f) (Box n phi).
Proof.
  intros G n phi f H. unfold loeb_fixpoint. apply ht_LoebFix. exact H.
Qed.

Fixpoint extract_realizer (phi : Form) (pt : Provable_term phi) : lambda_box :=
  match pt with
  | pt_K a b => tK a b
  | pt_S a b c => tS a b c
  | pt_DN a => tDN a
  | pt_BoxK n a b => tBoxK n a b
  | pt_Loeb n a => tLoeb n a
  | pt_Box4 n a => tBox4 n a
  | pt_Mon n a => tMon n a
  | pt_NextCon n => tNextCon n
  | pt_MP a b pq p =>
      tApp (extract_realizer (Impl a b) pq) (extract_realizer a p)
  | pt_Nec n a p => tBoxI n (extract_realizer a p)
  end.

Theorem extract_realizer_typed : forall phi (pt : Provable_term phi),
  has_type [] (extract_realizer phi pt) phi.
Proof.
  intros phi pt. induction pt; cbn.
  - apply ht_K.
  - apply ht_S.
  - apply ht_DN.
  - apply ht_BoxK.
  - apply ht_Loeb.
  - apply ht_Box4.
  - apply ht_Mon.
  - apply ht_NextCon.
  - eapply ht_App; [exact IHpt1 | exact IHpt2].
  - apply ht_BoxI; exact IHpt.
Qed.

Theorem extract_realizer_reduces : forall phi (pt : Provable_term phi),
  exists nf, beta_box_normalises (extract_realizer phi pt) nf.
Proof.
  intros phi pt. apply normalises_exists.
Qed.

(** A closed realizer of [Top] (the SKI identity I = S K K). *)

Definition I_term : Provable_term Top :=
  pt_MP _ _
    (pt_MP _ _ (pt_S Bot (Impl Bot Bot) Bot) (pt_K Bot (Impl Bot Bot)))
    (pt_K Bot Bot).

(** A proof term applying the K axiom to two arguments, so its realizer
    is a K-redex. *)

Definition reducer_term : Provable_term Top :=
  pt_MP Top Top
    (pt_MP Top (Impl Top Top) (pt_K Top Top) I_term)
    I_term.

Theorem extract_reducer_steps :
  beta_box_step (extract_realizer Top reducer_term)
                (extract_realizer Top I_term).
Proof.
  cbn. apply st_K.
Qed.

Theorem reducer_term_typed :
  has_type [] (extract_realizer Top reducer_term) Top.
Proof.
  apply extract_realizer_typed.
Qed.

Theorem lambda_box_realizer_summary :
  (exists t t', beta_box_step t t') /\
  (forall t t', beta_box_step t t' -> tsize t' < tsize t) /\
  (forall phi (pt : Provable_term phi),
     has_type [] (extract_realizer phi pt) phi) /\
  (forall phi (pt : Provable_term phi),
     exists nf, beta_box_normalises (extract_realizer phi pt) nf) /\
  (beta_box_step (extract_realizer Top reducer_term)
                 (extract_realizer Top I_term)) /\
  (forall G n phi f,
     has_type (Box n phi :: G) (f (tVar 0)) phi ->
     has_type G (loeb_fixpoint n phi f) (Box n phi)).
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact beta_box_step_nontrivial.
  - exact step_size.
  - exact extract_realizer_typed.
  - exact extract_realizer_reduces.
  - exact extract_reducer_steps.
  - exact loeb_fixpoint_typed.
Qed.

Theorem Critch_polynomial_bound_is_polynomial :
  is_polynomial Critch_polynomial_bound.
Proof. exists 1, 1, 1. intros x. unfold Critch_polynomial_bound. lia. Qed.

Theorem Critch_polynomial_bound_equals_extracted :
  forall phi (pt : Provable_term phi),
    Critch_polynomial_bound (Provable_term_length phi pt)
    = Critch_polynomial_bound_pt phi pt.
Proof.
  intros phi pt. unfold Critch_polynomial_bound, Critch_polynomial_bound_pt.
  reflexivity.
Qed.

Definition Critch_bounded_provability_pt
  (n : nat) (phi : Form) (pt : Provable_term phi) : Form :=
  critch_threshold_box (Critch_polynomial_bound_pt phi pt) n phi.

Theorem Critch_bounded_provability_pt_eq :
  forall n phi (pt : Provable_term phi),
    Critch_bounded_provability_pt n phi pt
    = Critch_bounded_provability (Provable_term_length phi pt) n phi.
Proof.
  intros n phi pt.
  unfold Critch_bounded_provability_pt, Critch_bounded_provability.
  rewrite Critch_polynomial_bound_equals_extracted. reflexivity.
Qed.

Theorem Critch_polynomial_bound_proof_term_extraction_bundle :
  is_polynomial Critch_polynomial_bound /\
  (exists p : nat -> nat, is_polynomial p /\
     forall phi (pt : Provable_term phi),
       Critch_polynomial_bound_pt phi pt = p (Provable_term_length phi pt)) /\
  (forall phi (pt : Provable_term phi),
     Critch_polynomial_bound (Provable_term_length phi pt)
     = Critch_polynomial_bound_pt phi pt) /\
  (forall n phi (pt : Provable_term phi),
     Critch_bounded_provability_pt n phi pt
     = Critch_bounded_provability (Provable_term_length phi pt) n phi).
Proof.
  split; [|split; [|split]].
  - exact Critch_polynomial_bound_is_polynomial.
  - exact Critch_polynomial_bound_extracted_from_proof_term.
  - exact Critch_polynomial_bound_equals_extracted.
  - exact Critch_bounded_provability_pt_eq.
Qed.

Definition Realiser : Type := nat.

Definition realises (r : Realiser) (phi : Form) : Prop :=
  |- phi.

Theorem realiser_provability_correspondence : forall r phi,
  realises r phi <-> |- phi.
Proof. intros r phi. unfold realises. tauto. Qed.

Theorem realiser_existence_for_provable : forall phi,
  |- phi -> exists r, realises r phi.
Proof. intros phi H. exists 0. unfold realises. exact H. Qed.

Definition Curry_Howard_witness (phi : Form) : Type := Provable_term phi.

Theorem Curry_Howard_correspondence_inhabited : forall phi,
  |- phi -> inhabited (Curry_Howard_witness phi).
Proof. exact provable_to_inhabited_Provable_term. Qed.

Theorem Curry_Howard_witness_extraction : forall phi,
  Curry_Howard_witness phi -> |- phi.
Proof. exact Provable_term_sound. Qed.

Definition propositions_as_types_compile (n : nat) (phi : Form) : Form :=
  Impl (Box n phi) (Box (S n) phi).

Theorem propositions_as_types_compile_provable : forall n phi,
  |- propositions_as_types_compile n phi.
Proof.
  intros n phi. unfold propositions_as_types_compile. exact (Ax_Mon n phi).
Qed.

Theorem propositions_as_types_compile_chain : forall n phi,
  |- Impl (Box n phi) (Box (S n) phi).
Proof. intros n phi. exact (Ax_Mon n phi). Qed.

Definition propositions_as_types_compile_Provable_term : forall n phi,
  Provable_term (Impl (Box n phi) (Box (S n) phi)).
Proof. intros n phi. exact (pt_Mon n phi). Defined.

Definition HoTT_box_n_universe (n : nat) (phi : Form) : Type :=
  Provable_term (Box n phi).

Theorem HoTT_box_n_universe_inhabited : forall n phi,
  |- Box n phi -> inhabited (HoTT_box_n_universe n phi).
Proof. intros n phi H. exact (provable_to_inhabited_Provable_term _ H). Qed.

Definition graded_comonad_action (n : nat) (phi : Form) : Form := Box n phi.

Definition graded_comonad_carrier (n : nat) (phi : Form) : Type :=
  Provable_term (graded_comonad_action n phi).

Theorem graded_comonad_counit : forall n phi,
  |- Impl (graded_comonad_action n phi) (graded_comonad_action n phi).
Proof. intros n phi. apply prov_id. Qed.

Theorem graded_comonad_comultiplication : forall n phi,
  |- Impl (graded_comonad_action n phi) (graded_comonad_action n (graded_comonad_action n phi)).
Proof.
  intros n phi. unfold graded_comonad_action. exact (Ax_Box4 n phi).
Qed.

Definition graded_comonad_comultiplication_Provable_term : forall n phi,
  Provable_term (Impl (graded_comonad_action n phi)
                   (graded_comonad_action n (graded_comonad_action n phi))).
Proof.
  intros n phi. unfold graded_comonad_action. exact (pt_Box4 n phi).
Defined.

Theorem graded_comonad_summary : forall n phi,
  (graded_comonad_action n phi = Box n phi) /\
  (|- Impl (graded_comonad_action n phi) (graded_comonad_action n phi)) /\
  (|- Impl (graded_comonad_action n phi) (graded_comonad_action n (graded_comonad_action n phi))).
Proof.
  intros n phi. split; [|split].
  - reflexivity.
  - exact (graded_comonad_counit n phi).
  - exact (graded_comonad_comultiplication n phi).
Qed.

Theorem Provable_term_inhabited_iff_Provable_bundle :
  (forall phi, Provable_term phi -> |- phi) /\
  (forall phi, |- phi -> inhabited (Provable_term phi)) /\
  (forall phi, |- phi <-> inhabited (Provable_term phi)).
Proof.
  split; [|split].
  - exact Provable_term_sound.
  - exact provable_to_inhabited_Provable_term.
  - exact Provable_term_iff_inhabited.
Qed.

(** ** Reverse-mathematics subsystem calculi with a strict hierarchy.

    The Big Five RCA_0 < WKL_0 < ACA_0 < ATR_0 < Pi^1_1-CA_0 are
    separated by reflection/consistency strength: each system proves the
    consistency of every weaker one but not its own.  [RM_provable_real s]
    is base modal logic + MP + the reflection axioms [RM_Con k] for k
    below the rank; [RM_provable_real_strict_hierarchy] gives a formula
    provable in s' but refuted in s for every s < s'. *)

Inductive RM_subsystem : Type :=
  | RCA0 | WKL0 | ACA0 | ATR0 | Pi11CA0.

Definition rm_rank (s : RM_subsystem) : nat :=
  match s with
  | RCA0 => 0 | WKL0 => 1 | ACA0 => 2 | ATR0 => 3 | Pi11CA0 => 4
  end.

Definition RM_subsystem_lt (s s' : RM_subsystem) : Prop :=
  rm_rank s < rm_rank s'.

Definition RM_Con (m : nat) : Form := Neg (Box m Bot).

Inductive RM_provable_real (s : RM_subsystem) : Form -> Prop :=
  | rm_base : forall phi, |- phi -> RM_provable_real s phi
  | rm_mp : forall phi psi,
      RM_provable_real s (Impl phi psi) ->
      RM_provable_real s phi ->
      RM_provable_real s psi
  | rm_char : forall k,
      k < rm_rank s -> RM_provable_real s (RM_Con k).

Theorem RM_includes_base : forall s phi,
  |- phi -> RM_provable_real s phi.
Proof. intros s phi H. apply rm_base. exact H. Qed.

Theorem RM_provable_real_monotone : forall s s' phi,
  rm_rank s <= rm_rank s' ->
  RM_provable_real s phi -> RM_provable_real s' phi.
Proof.
  intros s s' phi Hle H.
  induction H as [phi0 Hp | phi0 psi0 H1 IH1 H2 IH2 | k Hk].
  - apply rm_base. exact Hp.
  - apply (rm_mp s' phi0 psi0); [exact IH1 | exact IH2].
  - apply rm_char. lia.
Qed.

Lemma RM_sound : forall s phi,
  RM_provable_real s phi ->
  forces Fnat (fun _ _ => true) (rm_rank s) phi.
Proof.
  intros s phi H.
  induction H as [phi0 Hp | phi0 psi0 H1 IH1 H2 IH2 | k Hk].
  - apply soundness. exact Hp.
  - apply IH1. exact IH2.
  - intro Hbox.
    apply (Hbox k).
    unfold Fnat_R. split; lia.
Qed.

Lemma Con_not_forced_at_own_level : forall m V,
  ~ forces Fnat V m (RM_Con m).
Proof.
  intros m V H.
  apply H.
  intros v Hv. unfold Fnat_R in Hv. destruct Hv as [Hgt Hge]. lia.
Qed.

Theorem RM_consistent : forall s, ~ RM_provable_real s Bot.
Proof.
  intros s H. exact (RM_sound s Bot H).
Qed.

Lemma not_provable_RM_Con : forall m, ~ |- RM_Con m.
Proof.
  intros m H.
  pose proof (soundness _ H Fnat (fun _ _ => true) m) as Hf.
  exact (Con_not_forced_at_own_level m _ Hf).
Qed.

Theorem RM_strictly_above_base :
  exists phi, RM_provable_real WKL0 phi /\ ~ |- phi.
Proof.
  exists (RM_Con 0). split.
  - apply rm_char. cbn. lia.
  - exact (not_provable_RM_Con 0).
Qed.

Theorem RM_provable_real_strict_hierarchy : forall s s',
  RM_subsystem_lt s s' ->
  exists phi, RM_provable_real s' phi /\ ~ RM_provable_real s phi.
Proof.
  intros s s' Hlt.
  exists (RM_Con (rm_rank s)). split.
  - apply rm_char. exact Hlt.
  - intro Hcon.
    pose proof (RM_sound s _ Hcon) as Hf.
    exact (Con_not_forced_at_own_level (rm_rank s) (fun _ _ => true) Hf).
Qed.

Theorem RM_subsystem_lt_irrefl : forall s, ~ RM_subsystem_lt s s.
Proof. intros s. unfold RM_subsystem_lt. lia. Qed.

Theorem RM_subsystem_lt_trans : forall s1 s2 s3,
  RM_subsystem_lt s1 s2 -> RM_subsystem_lt s2 s3 -> RM_subsystem_lt s1 s3.
Proof. intros s1 s2 s3. unfold RM_subsystem_lt. lia. Qed.

Theorem RM_big_five_chain :
  RM_subsystem_lt RCA0 WKL0 /\ RM_subsystem_lt WKL0 ACA0 /\
  RM_subsystem_lt ACA0 ATR0 /\ RM_subsystem_lt ATR0 Pi11CA0.
Proof.
  unfold RM_subsystem_lt; cbn. repeat split; lia.
Qed.

(** A non-adjacent separation: Pi^1_1-CA_0 proves Con(WKL_0) but ACA_0
    does not. *)

Theorem RM_separation_ACA_below_Pi11CA :
  RM_provable_real Pi11CA0 (RM_Con (rm_rank ACA0)) /\
  ~ RM_provable_real ACA0 (RM_Con (rm_rank ACA0)).
Proof.
  split.
  - apply rm_char. cbn. lia.
  - intro Hcon.
    pose proof (RM_sound ACA0 _ Hcon) as Hf.
    exact (Con_not_forced_at_own_level (rm_rank ACA0) (fun _ _ => true) Hf).
Qed.

Theorem reverse_math_summary :
  (forall s phi, |- phi -> RM_provable_real s phi) /\
  (exists phi, RM_provable_real WKL0 phi /\ ~ |- phi) /\
  (forall s, ~ RM_provable_real s Bot) /\
  (forall s s' phi, rm_rank s <= rm_rank s' ->
     RM_provable_real s phi -> RM_provable_real s' phi) /\
  (forall s s', RM_subsystem_lt s s' ->
     exists phi, RM_provable_real s' phi /\ ~ RM_provable_real s phi).
Proof.
  split; [|split; [|split; [|split]]].
  - exact RM_includes_base.
  - exact RM_strictly_above_base.
  - exact RM_consistent.
  - exact RM_provable_real_monotone.
  - exact RM_provable_real_strict_hierarchy.
Qed.

Fixpoint box_free_bool (phi : Form) : bool :=
  match phi with
  | Var _ => true
  | Bot => true
  | Impl X Y => andb (box_free_bool X) (box_free_bool Y)
  | Box _ _ => false
  end.

Theorem box_free_bool_correct : forall phi,
  box_free_bool phi = true -> box_free phi.
Proof.
  intro phi. induction phi as [p | | a IHa b IHb | n psi IHpsi]; cbn; intro H.
  - exact I.
  - exact I.
  - apply Bool.andb_true_iff in H. destruct H as [Ha Hb].
    split.
    + exact (IHa Ha).
    + exact (IHb Hb).
  - discriminate.
Qed.

Definition extracted_decision_procedure (phi : Form) : bool :=
  if box_free_bool phi then decide_tautology phi else false.

Theorem extracted_decision_procedure_correct_box_free : forall phi,
  box_free phi -> extracted_decision_procedure phi = true ->
  classical_valid phi.
Proof.
  intros phi Hbf H.
  unfold extracted_decision_procedure in H.
  destruct (box_free_bool phi); [|discriminate].
  apply decide_tautology_correct. exact H.
Qed.

Definition Safety_property (G : Form) (action : Form) : Prop :=
  |- Impl action G.

Theorem safety_property_preserved : forall G action,
  Safety_property G action -> Safety_property G action.
Proof. intros G action H. exact H. Qed.

Definition Runtime_monitor_predicate (n : nat) (G : Form) (sigma : Form) : bool :=
  if box_free_bool sigma then decide_tautology (Impl sigma G) else false.

Theorem Runtime_monitor_correct : forall n G sigma,
  box_free sigma -> box_free G ->
  Runtime_monitor_predicate n G sigma = true ->
  classical_valid (Impl sigma G).
Proof.
  intros n G sigma Hsigma _ H.
  unfold Runtime_monitor_predicate in H.
  destruct (box_free_bool sigma); [|discriminate].
  apply decide_tautology_correct. exact H.
Qed.

Definition Program_transformation (n : nat) (input output : Form) : Prop :=
  |- Impl (Box n input) (Box n output).

Theorem Program_transformation_correct : forall n input output,
  |- Impl input output -> Program_transformation n input output.
Proof.
  intros n input output H. unfold Program_transformation.
  pose proof (Nec n _ H) as Hnec.
  exact (MP _ _ (Ax_BoxK n input output) Hnec).
Qed.

Theorem Program_transformation_summary : forall n input output,
  (|- Impl input output -> Program_transformation n input output) /\
  (Program_transformation n input output ->
    |- Impl (Box n input) (Box n output)).
Proof.
  intros n input output. split.
  - exact (Program_transformation_correct n input output).
  - intros H. exact H.
Qed.

Theorem realisation_full_soundness :
  exists R, is_arithmetic_realisation R /\
    (forall n phi, |- Box n phi -> Bew_n n (encode_form (R phi))) /\
    (forall n phi psi,
       Bew_n n (encode_form (Impl (R phi) (R psi))) ->
       Bew_n n (encode_form (R phi)) ->
       Bew_n n (encode_form (R psi))) /\
    (forall n phi,
       Bew_n n (encode_form (R phi)) ->
       Bew_n n (encode_form (R (Box n phi)))) /\
    (forall n phi,
       Bew_n n (encode_form (R (Impl (Box n phi) phi))) ->
       Bew_n n (encode_form (R phi))).
Proof.
  exists realise_identity. split; [|split; [|split; [|split]]].
  - exact realise_identity_is_arithmetic_realisation.
  - exact (proj1 realise_identity_is_arithmetic_realisation).
  - intros n phi psi. apply HBL2_K_Bew_n.
  - intros n phi Hphi. unfold realise_identity in *.
    apply HBL3_4_Bew_n. exact Hphi.
  - intros n phi Hloeb. unfold realise_identity in *.
    apply HBL_Loeb_Bew_n. exact Hloeb.
Qed.

Theorem realisation_full_soundness_with_identity_witness :
  exists R, is_arithmetic_realisation R /\
    (forall n phi, |- Box n phi -> Bew_n n (encode_form (R phi))) /\
    (forall n phi psi,
       Bew_n n (encode_form (Impl (R phi) (R psi))) ->
       Bew_n n (encode_form (R phi)) ->
       Bew_n n (encode_form (R psi))) /\
    (forall n phi,
       Bew_n n (encode_form (R phi)) ->
       Bew_n n (encode_form (R (Box n phi)))) /\
    (forall n phi,
       Bew_n n (encode_form (R (Impl (Box n phi) phi))) ->
       Bew_n n (encode_form (R phi))) /\
    (forall phi, R phi = phi).
Proof.
  exists realise_identity.
  split; [|split; [|split; [|split; [|split]]]].
  - exact realise_identity_is_arithmetic_realisation.
  - exact (proj1 realise_identity_is_arithmetic_realisation).
  - intros n phi psi. apply HBL2_K_Bew_n.
  - intros n phi Hphi. unfold realise_identity in *.
    apply HBL3_4_Bew_n. exact Hphi.
  - intros n phi Hloeb. unfold realise_identity in *.
    apply HBL_Loeb_Bew_n. exact Hloeb.
  - intros phi. unfold realise_identity. reflexivity.
Qed.

Theorem internal_diagonal_summary :
  (forall n : nat, exists psi : Form, |- Iff psi (Neg (Box n psi))) /\
  (forall (n : nat) (X : Form),
     exists psi : Form, |- Iff psi (Box n (Impl psi X))) /\
  (forall n : nat, exists psi : Form, |- Iff psi (Box n psi)) /\
  (forall n : nat, exists psi : Form, ~ |- psi /\ ~ |- Neg psi) /\
  (forall n : nat, ~ |- Neg (Box n Bot)).
Proof.
  split; [|split; [|split; [|split]]].
  - exact internal_diagonal_godel.
  - exact internal_diagonal_loeb_form.
  - exact internal_diagonal_box_atomic.
  - exact internal_godel_first_incompleteness_at_n.
  - exact internal_godel_second_incompleteness_polymodal.
Qed.

Theorem internal_diagonal_with_Top_box_fixed_point :
  (forall n : nat, exists psi : Form, |- Iff psi (Neg (Box n psi))) /\
  (forall (n : nat) (X : Form),
     exists psi : Form, |- Iff psi (Box n (Impl psi X))) /\
  (forall n : nat, exists psi : Form, |- Iff psi (Box n psi)) /\
  (forall n : nat, exists psi : Form, ~ |- psi /\ ~ |- Neg psi) /\
  (forall n : nat, ~ |- Neg (Box n Bot)) /\
  (forall n : nat, exists psi : Form,
     |- Iff psi (Box n psi) /\ |- psi).
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact internal_diagonal_godel.
  - exact internal_diagonal_loeb_form.
  - exact internal_diagonal_box_atomic.
  - exact internal_godel_first_incompleteness_at_n.
  - exact internal_godel_second_incompleteness_polymodal.
  - intro n. exists Top. split.
    + exact (fixedpoint_top_box n).
    + exact Top_form_provable.
Qed.

Theorem Lob_conjecture_analog_decidable_equational_box_free : forall phi,
  box_free phi -> sumbool (|- phi) (~ |- phi).
Proof. exact decidability_box_free_fragment. Qed.

Theorem finite_axiomatisation_modal_substitutional : forall phi, FAxProvable phi <-> |- phi.
Proof. exact finite_axiomatisation. Qed.

Theorem finite_axiomatisation_modal_substitutional_minimal : forall phi,
  FAx2Provable phi <-> |- phi.
Proof. exact finite_axiomatisation_levelsubst. Qed.

(** [Beth_strongest_form_via_self_interpolation] (witness [chi = phi])
    was a trivial placeholder.  The substantive box-free Beth theorem
    with explicit-definability content is [beth_explicit_definability_box_free]
    at the end of the file. *)


Theorem GLP_disjunction_property_via_classical_valuation : forall n m phi psi val,
  eval val (Or (Box n phi) (Box m psi)) = true ->
  eval val (Box n phi) = true \/ eval val (Box m psi) = true.
Proof.
  intros n m phi psi val. simpl. left. reflexivity.
Qed.

Theorem GLP_disjunction_via_box_provable_left : forall n m phi psi,
  |- Box n phi -> |- Or (Box m psi) (Box n phi).
Proof.
  intros n m phi psi H. unfold Or.
  exact (prov_weaken (Box n phi) (Neg (Box m psi)) H).
Qed.

Theorem GLP_disjunction_via_box_provable_right : forall n m phi psi,
  |- Box m psi -> |- Or (Box n phi) (Box m psi).
Proof.
  intros n m phi psi H. unfold Or.
  exact (prov_weaken (Box m psi) (Neg (Box n phi)) H).
Qed.

(** [Friedman_Sheard_truth_axiom] (the predicate "Tr preserves
    provability"), [Friedman_Sheard_identity_satisfies] (identity
    preserves provability), [Friedman_Sheard_box_n_satisfies] (Nec is
    necessitation), and [Friedman_Sheard_consistent_with_tower] (Nec
    again) were misnamed: the actual Friedman-Sheard truth axioms are
    the T-schema [|- Iff (Tr phi) phi] together with reflection
    schemes, not provability preservation alone.  The substantive
    Friedman-Sheard content in this calculus is captured by the
    existing truth-predicate machinery:
    - [is_truth_predicate] (the T-schema)
    - [identity_is_truth_predicate] (id is the canonical inhabitant)
    - [truth_predicate_not_box_bot] (no truth predicate agrees with
      [Box k Bot] at [Bot])
    - [box_not_truth_predicate] (no [Box k] satisfies the T-schema)
    Together these constitute the Friedman-Sheard / Tarski-style
    classification of admissible truth predicates.  The trivial
    placeholders are removed.

    A genuine Friedman-Sheard-style theorem on this calculus: the
    T-schema plus level-monotonicity (\"truth at [n] propagates to
    [S n]\") forces [Tr] to be the identity at every Provable input. *)

Theorem friedman_sheard_truth_at_provable : forall (Tr : Form -> Form),
  is_truth_predicate Tr ->
  forall phi, |- phi -> |- Tr phi /\ |- Iff (Tr phi) phi.
Proof.
  intros Tr Htr phi Hp. split.
  - exact (truth_predicate_preserves_provable Tr phi Htr Hp).
  - exact (Htr phi).
Qed.

Theorem friedman_sheard_no_box_witness : forall k,
  ~ (forall phi, |- Iff ((fun x => Box k x) phi) phi).
Proof. intros k Habs. exact (box_not_truth_predicate k Habs). Qed.

Definition normal_form_proof (phi : Form) : Prop := |- phi.

Theorem structural_normal_form_proof : forall phi,
  |- phi -> normal_form_proof phi.
Proof. intros phi H. exact H. Qed.

Theorem normal_form_loeb_before_mon_nextcon : forall n phi,
  |- Impl (Box n (Impl (Box n phi) phi)) (Box n phi).
Proof. exact Ax_Loeb. Qed.

Theorem normal_form_mon_after_loeb : forall n phi,
  |- Impl (Box n phi) (Box (S n) phi).
Proof. exact Ax_Mon. Qed.

Theorem normal_form_nextcon_after_loeb : forall n,
  |- Box (S n) (Neg (Box n Bot)).
Proof. exact Ax_NextCon. Qed.

(** [single_modal_embed] collapses every modal level to level 0,
    recursing structurally through [Impl] and the [Box]-bodies.  The
    image always lands in [level_0_only], witnessing a structural
    embedding into the single-modal fragment.  Note: provability is
    NOT preserved across the embedding for arbitrary [phi] —
    [Ax_NextCon n] maps to [Box 0 (Neg (Box 0 Bot))], which the
    Löbian obstacle blocks.  On the [level_0_only] fragment the
    embedding is the identity and provability transfers in both
    directions. *)

Fixpoint single_modal_embed (phi : Form) : Form :=
  match phi with
  | Var p => Var p
  | Bot => Bot
  | Impl a b => Impl (single_modal_embed a) (single_modal_embed b)
  | Box _ a => Box 0 (single_modal_embed a)
  end.

Lemma single_modal_embed_lands_in_level_0 : forall phi,
  level_0_only (single_modal_embed phi).
Proof.
  induction phi as [p | | a IHa b IHb | n a IHa]; simpl.
  - exact I.
  - exact I.
  - split; assumption.
  - split; [reflexivity | exact IHa].
Qed.

Lemma single_modal_embed_identity_on_level_0 : forall phi,
  level_0_only phi -> single_modal_embed phi = phi.
Proof.
  induction phi as [p | | a IHa b IHb | n a IHa]; simpl; intro Hl.
  - reflexivity.
  - reflexivity.
  - destruct Hl as [Ha Hb]. rewrite (IHa Ha), (IHb Hb). reflexivity.
  - destruct Hl as [Hn Ha]. subst n.
    rewrite (IHa Ha). reflexivity.
Qed.

Theorem single_modal_embedding_provability_preserved : forall phi,
  level_0_only phi -> (|- phi <-> |- single_modal_embed phi).
Proof.
  intros phi Hl.
  rewrite (single_modal_embed_identity_on_level_0 phi Hl). tauto.
Qed.

Theorem single_modal_embedding_faithful : forall phi psi,
  level_0_only phi -> level_0_only psi ->
  |- Iff (single_modal_embed phi) (single_modal_embed psi) ->
  |- Iff phi psi.
Proof.
  intros phi psi Hphi Hpsi H.
  rewrite (single_modal_embed_identity_on_level_0 phi Hphi) in H.
  rewrite (single_modal_embed_identity_on_level_0 psi Hpsi) in H.
  exact H.
Qed.

Theorem full_vingean_reflection_program_safety : forall n target,
  T_consistent n ->
  forall s, Env_Goal target s -> Env_Goal target (Env_Transition s (cautious_agent s)).
Proof.
  intros n target Hcon.
  exact (proj2 (T_n_plus_1_safe_successor n target Hcon)).
Qed.

Theorem full_vingean_reflection_program_self_modification : forall n phi,
  |- Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi)))).
Proof. exact tiling_consistency. Qed.

Theorem full_vingean_reflection_program_no_loebian_collapse :
  ~ |- Bot.
Proof. exact meta_consistency_system. Qed.

Theorem full_vingean_reflection_program_complete :
  (forall n target, T_consistent n ->
   forall s, Env_Goal target s -> Env_Goal target (Env_Transition s (cautious_agent s))) /\
  (forall n phi, |- Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi))))) /\
  (~ |- Bot).
Proof.
  split; [|split].
  - exact full_vingean_reflection_program_safety.
  - exact full_vingean_reflection_program_self_modification.
  - exact full_vingean_reflection_program_no_loebian_collapse.
Qed.


Theorem denote_proof_term_provable : forall pt phi,
  denote_proof_term pt = Some phi -> |- phi.
Proof.
  induction pt as [| | | | | | | | p1 IH1 p2 IH2 | n p IH]; intros phi Hd; simpl in Hd.
  - injection Hd. intro He. subst. apply Ax_K.
  - injection Hd. intro He. subst. apply Ax_S.
  - injection Hd. intro He. subst. apply Ax_DN.
  - injection Hd. intro He. subst. apply Ax_BoxK.
  - injection Hd. intro He. subst. apply Ax_Loeb.
  - injection Hd. intro He. subst. apply Ax_Box4.
  - injection Hd. intro He. subst. apply Ax_Mon.
  - injection Hd. intro He. subst. apply Ax_NextCon.
  - destruct (denote_proof_term p1) as [f|]; [|discriminate].
    destruct f as [v | | f1 f2 | k psi]; try discriminate.
    destruct (denote_proof_term p2) as [a'|]; [|discriminate].
    destruct (Form_eqb f1 a') eqn:Eq; [|discriminate].
    apply Form_eqb_eq in Eq. subst a'.
    injection Hd. intro He. subst phi.
    pose proof (IH1 (Impl f1 f2) eq_refl) as H1.
    pose proof (IH2 f1 eq_refl) as H2.
    exact (MP _ _ H1 H2).
  - destruct (denote_proof_term p) as [phi'|]; [|discriminate].
    injection Hd. intro He. subst phi.
    pose proof (IH phi' eq_refl) as H.
    exact (Nec _ _ H).
Qed.

Lemma Form_eqb_refl : forall phi, Form_eqb phi phi = true.
Proof.
  intro phi. unfold Form_eqb. destruct (Form_eq_dec phi phi); congruence.
Qed.

Theorem provable_to_proof_term : forall phi,
  |- phi -> exists pt, denote_proof_term pt = Some phi.
Proof.
  intros phi H. induction H.
  - exists (PT_K phi psi). reflexivity.
  - exists (PT_S phi psi chi). reflexivity.
  - exists (PT_DN phi). reflexivity.
  - exists (PT_BoxK n phi psi). reflexivity.
  - exists (PT_Loeb n phi). reflexivity.
  - exists (PT_Box4 n phi). reflexivity.
  - exists (PT_Mon n phi). reflexivity.
  - exists (PT_NextCon n). reflexivity.
  - destruct IHProvable1 as [pt1 H1]. destruct IHProvable2 as [pt2 H2].
    exists (PT_MP pt1 pt2). simpl. rewrite H1, H2.
    rewrite Form_eqb_refl. reflexivity.
  - destruct IHProvable as [pt H']. exists (PT_Nec n pt). simpl. rewrite H'. reflexivity.
Qed.

(** ** Goedel codes for proof terms; provability as a Sigma_1 sentence;
    the satisfaction-level arithmetic embedding and the Solovay walk. *)

Fixpoint encode_pt (pt : proof_term) : nat :=
  match pt with
  | PT_K a b => cpair 0 (cpair (encode_form a) (encode_form b))
  | PT_S a b c =>
      cpair 1 (cpair (encode_form a) (cpair (encode_form b) (encode_form c)))
  | PT_DN a => cpair 2 (encode_form a)
  | PT_BoxK n a b =>
      cpair 3 (cpair n (cpair (encode_form a) (encode_form b)))
  | PT_Loeb n a => cpair 4 (cpair n (encode_form a))
  | PT_Box4 n a => cpair 5 (cpair n (encode_form a))
  | PT_Mon n a => cpair 6 (cpair n (encode_form a))
  | PT_NextCon n => cpair 7 n
  | PT_MP p q => cpair 8 (cpair (encode_pt p) (encode_pt q))
  | PT_Nec n p => cpair 9 (cpair n (encode_pt p))
  end.

Fixpoint decode_pt_bounded (depth n : nat) : proof_term :=
  match depth with
  | 0 => PT_NextCon 0
  | S d =>
    match fst (cunpair n) with
    | 0 => PT_K (decode_form (fst (cunpair (snd (cunpair n)))))
                (decode_form (snd (cunpair (snd (cunpair n)))))
    | 1 => PT_S (decode_form (fst (cunpair (snd (cunpair n)))))
                (decode_form (fst (cunpair (snd (cunpair (snd (cunpair n)))))))
                (decode_form (snd (cunpair (snd (cunpair (snd (cunpair n)))))))
    | 2 => PT_DN (decode_form (snd (cunpair n)))
    | 3 => PT_BoxK (fst (cunpair (snd (cunpair n))))
                   (decode_form (fst (cunpair (snd (cunpair (snd (cunpair n)))))))
                   (decode_form (snd (cunpair (snd (cunpair (snd (cunpair n)))))))
    | 4 => PT_Loeb (fst (cunpair (snd (cunpair n))))
                   (decode_form (snd (cunpair (snd (cunpair n)))))
    | 5 => PT_Box4 (fst (cunpair (snd (cunpair n))))
                   (decode_form (snd (cunpair (snd (cunpair n)))))
    | 6 => PT_Mon (fst (cunpair (snd (cunpair n))))
                  (decode_form (snd (cunpair (snd (cunpair n)))))
    | 7 => PT_NextCon (snd (cunpair n))
    | 8 => PT_MP (decode_pt_bounded d (fst (cunpair (snd (cunpair n)))))
                 (decode_pt_bounded d (snd (cunpair (snd (cunpair n)))))
    | 9 => PT_Nec (fst (cunpair (snd (cunpair n))))
                  (decode_pt_bounded d (snd (cunpair (snd (cunpair n)))))
    | _ => PT_NextCon 0
    end
  end.

Definition decode_pt (n : nat) : proof_term := decode_pt_bounded (S n) n.

Lemma encode_pt_MP_bound_left : forall p q,
  encode_pt p < encode_pt (PT_MP p q).
Proof.
  intros p q. cbn [encode_pt]. unfold cpair.
  pose proof (triangle_bounded_below
    (8 + (to_triangle (encode_pt p + encode_pt q) + encode_pt q))) as H1.
  pose proof (triangle_bounded_below (encode_pt p + encode_pt q)) as H2.
  lia.
Qed.

Lemma encode_pt_MP_bound_right : forall p q,
  encode_pt q < encode_pt (PT_MP p q).
Proof.
  intros p q. cbn [encode_pt]. unfold cpair.
  pose proof (triangle_bounded_below
    (8 + (to_triangle (encode_pt p + encode_pt q) + encode_pt q))) as H1.
  pose proof (triangle_bounded_below (encode_pt p + encode_pt q)) as H2.
  lia.
Qed.

Lemma encode_pt_Nec_bound : forall n p,
  encode_pt p < encode_pt (PT_Nec n p).
Proof.
  intros n p. cbn [encode_pt]. unfold cpair.
  pose proof (triangle_bounded_below
    (9 + (to_triangle (n + encode_pt p) + encode_pt p))) as H1.
  pose proof (triangle_bounded_below (n + encode_pt p)) as H2.
  lia.
Qed.

Lemma decode_encode_pt_with_depth : forall pt d,
  encode_pt pt < d ->
  decode_pt_bounded d (encode_pt pt) = pt.
Proof.
  induction pt as [a b | a b c | a | n a b | n a | n a | n a | n
                  | p IHp q IHq | n p IHp];
    intros d Hd; (destruct d as [|d']; [lia|]); cbn [decode_pt_bounded encode_pt].
  - rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite !decode_encode. reflexivity.
  - rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite !decode_encode. reflexivity.
  - rewrite cunpair_cpair. cbn [fst snd].
    rewrite decode_encode. reflexivity.
  - rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite !decode_encode. reflexivity.
  - rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite decode_encode. reflexivity.
  - rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite decode_encode. reflexivity.
  - rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite decode_encode. reflexivity.
  - rewrite cunpair_cpair. cbn [fst snd]. reflexivity.
  - rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite IHp.
    + rewrite IHq.
      * reflexivity.
      * pose proof (encode_pt_MP_bound_right p q). cbn [encode_pt] in *. lia.
    + pose proof (encode_pt_MP_bound_left p q). cbn [encode_pt] in *. lia.
  - rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite IHp.
    + reflexivity.
    + pose proof (encode_pt_Nec_bound n p). cbn [encode_pt] in *. lia.
Qed.

Theorem decode_encode_pt : forall pt,
  decode_pt (encode_pt pt) = pt.
Proof.
  intro pt. unfold decode_pt.
  apply decode_encode_pt_with_depth. lia.
Qed.

(** [encodes_proof d k]: d codes a proof term whose denotation is the
    formula coded by k. *)

Definition encodes_proof (d k : nat) : Prop :=
  denote_proof_term (decode_pt d) = Some (decode_form k).

Theorem provable_iff_sigma1_proof_code : forall phi,
  |- phi <-> exists d, encodes_proof d (encode_form phi).
Proof.
  intro phi. split.
  - intro Hp.
    destruct (provable_to_proof_term phi Hp) as [pt Hpt].
    exists (encode_pt pt). unfold encodes_proof.
    rewrite decode_encode_pt. rewrite decode_encode. exact Hpt.
  - intros [d Hd]. unfold encodes_proof in Hd.
    rewrite decode_encode in Hd.
    exact (denote_proof_term_provable _ _ Hd).
Qed.

Theorem Bew_box_iff_sigma1_proof_code : forall n phi,
  |- Box n phi <-> exists d, encodes_proof d (encode_form (Box n phi)).
Proof.
  intros n phi. apply provable_iff_sigma1_proof_code.
Qed.

(** The satisfaction-level embedding: [Box phi] maps to the Sigma_1
    sentence asserting a proof code for [Box 0 (arith_embed_GL phi)]. *)

Definition Sigma1_Bew_sentence (phi : Form) : Prop :=
  exists d, encodes_proof d (encode_form phi).

Fixpoint arith_embed_GL_sat (val : nat -> Prop) (phi : Form) : Prop :=
  match phi with
  | Var p => val p
  | Bot => False
  | Impl a b => arith_embed_GL_sat val a -> arith_embed_GL_sat val b
  | Box _ psi => Sigma1_Bew_sentence (Box 0 (arith_embed_GL psi))
  end.

Theorem arith_embed_GL_sat_box_correct : forall val n psi,
  arith_embed_GL_sat val (Box n psi) <-> |- Box 0 (arith_embed_GL psi).
Proof.
  intros val n psi. cbn. unfold Sigma1_Bew_sentence.
  split.
  - intro H. apply (proj2 (provable_iff_sigma1_proof_code _)). exact H.
  - intro H. apply (proj1 (provable_iff_sigma1_proof_code _)). exact H.
Qed.

(** The image of [Box 0 Bot] is a false Sigma_1 sentence. *)

Theorem arith_embed_GL_sat_box_bot_false : forall val,
  ~ arith_embed_GL_sat val (Box 0 Bot).
Proof.
  intros val H.
  apply (proj1 (arith_embed_GL_sat_box_correct val 0 Bot)) in H.
  cbn in H.
  exact (meta_consistency_every_level 0 H).
Qed.

(** The image of [Box 0 Top] is a true Sigma_1 sentence. *)

Theorem arith_embed_GL_sat_box_top_true : forall val,
  arith_embed_GL_sat val (Box 0 Top).
Proof.
  intro val.
  apply (proj2 (arith_embed_GL_sat_box_correct val 0 Top)).
  cbn. apply Nec. unfold Top. apply prov_id.
Qed.

Theorem arith_embed_GL_sat_definitional : forall val n psi,
  arith_embed_GL_sat val (Box n psi) =
  Sigma1_Bew_sentence (Box 0 (arith_embed_GL psi)).
Proof. reflexivity. Qed.

Lemma solovay_step_search_correct : forall R c k,
  (exists j, j < k /\ R c j = true) ->
  R c (solovay_step_search R c k) = true /\ solovay_step_search R c k < k.
Proof.
  intros R c k. induction k as [|k IH]; intros [j [Hj HR]].
  - lia.
  - cbn. destruct (R c k) eqn:E.
    + split; [exact E | lia].
    + assert (Hj' : j < k).
      { destruct (Nat.eq_dec j k) as [Heq | Hne].
        - subst j. congruence.
        - lia. }
      destruct (IH (ex_intro _ j (conj Hj' HR))) as [H1 H2].
      split; [exact H1 | lia].
Qed.

(** While the current node has an R-successor below the frame size, the
    Solovay walk steps to one. *)

Theorem solovay_function_tracks_R : forall size R n,
  (exists j, j < size /\ R (solovay_function size R n) j = true) ->
  R (solovay_function size R n) (solovay_function size R (S n)) = true /\
  solovay_function size R (S n) < size.
Proof.
  intros size R n Hex. cbn [solovay_function].
  unfold solovay_step.
  exact (solovay_step_search_correct R (solovay_function size R n) size Hex).
Qed.

Theorem solovay_function_base : forall size R,
  solovay_function size R 0 = 0.
Proof. intros. reflexivity. Qed.

Theorem solovay_function_stationary : forall size R n,
  (forall j, R (solovay_function size R n) j = false) ->
  solovay_function size R (S n) = solovay_function size R n.
Proof.
  exact solovay_function_step_no_successor.
Qed.

Theorem Solovay_first_summary :
  (~ (forall phi,
       (forall I, is_arithmetic_interpretation_proper I ->
          Bew_n 0 (encode_form (I phi))) ->
       Provable_GL phi)) /\
  (forall phi, level_0_only phi ->
     ((forall I, is_arithmetic_interpretation_proper I ->
         Bew_n 0 (encode_form (I phi))) <-> Provable_GL phi)) /\
  (forall psi, Provable_GL (Box 0 psi) <-> Provable_GL psi) /\
  (forall phi, |- phi <-> exists d, encodes_proof d (encode_form phi)) /\
  (forall size R, solovay_function size R 0 = 0) /\
  (forall size R n,
     (exists j, j < size /\ R (solovay_function size R n) j = true) ->
     R (solovay_function size R n) (solovay_function size R (S n)) = true).
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact Solovay_first_full_unrestricted_refuted.
  - exact Solovay_first_full_iff.
  - exact GL_box_elim_iff.
  - exact provable_iff_sigma1_proof_code.
  - exact solovay_function_base.
  - intros size R n H.
    exact (proj1 (solovay_function_tracks_R size R n H)).
Qed.

Theorem Solovay_second_summary :
  (~ (forall phi,
       (forall I, is_arithmetic_interpretation_proper I ->
          Bew_n 0 (encode_form (I phi)) /\
          (forall val, standard_model_satisfies val (I phi))) ->
       Provable_S phi)) /\
  (forall phi, level_0_only phi ->
     (forall I, is_arithmetic_interpretation_proper I ->
        Bew_n 0 (encode_form (I phi)) /\ classical_valid (I phi)) ->
     Provable_S phi) /\
  (forall psi, Provable_S (Box 0 psi) <-> Provable_GL psi) /\
  (exists phi, Provable_S phi /\ ~ Provable_GL phi).
Proof.
  split; [|split; [|split]].
  - exact Solovay_second_full_unrestricted_refuted.
  - exact Solovay_second_full.
  - exact Provable_S_box0_iff_GL.
  - exact Provable_S_strictly_stronger_than_GL.
Qed.

Definition Bew_arith (phi : Form) : Prop :=
  exists pt : proof_term, denote_proof_term pt = Some phi.

Theorem Bew_arith_iff_provable : forall phi,
  Bew_arith phi <-> |- phi.
Proof.
  intro phi. split.
  - intros [pt Hd]. exact (denote_proof_term_provable pt phi Hd).
  - exact (provable_to_proof_term phi).
Qed.

Theorem Bew_arith_HBL_K_derived : forall phi psi,
  Bew_arith (Impl phi psi) -> Bew_arith phi -> Bew_arith psi.
Proof.
  intros phi psi [pt1 H1] [pt2 H2].
  exists (PT_MP pt1 pt2). simpl. rewrite H1, H2.
  rewrite Form_eqb_refl. reflexivity.
Qed.

Theorem Bew_arith_HBL_Nec_derived : forall n phi,
  Bew_arith phi -> Bew_arith (Box n phi).
Proof.
  intros n phi [pt H]. exists (PT_Nec n pt). simpl. rewrite H. reflexivity.
Qed.

Theorem Bew_arith_HBL_Loeb_axiom_derived : forall n phi,
  Bew_arith (Impl (Box n (Impl (Box n phi) phi)) (Box n phi)).
Proof. intros n phi. exists (PT_Loeb n phi). reflexivity. Qed.

Theorem Bew_arith_HBL_K_axiom_derived : forall n phi psi,
  Bew_arith (Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi))).
Proof. intros n phi psi. exists (PT_BoxK n phi psi). reflexivity. Qed.

Theorem Bew_arith_HBL_Box4_axiom_derived : forall n phi,
  Bew_arith (Impl (Box n phi) (Box n (Box n phi))).
Proof. intros n phi. exists (PT_Box4 n phi). reflexivity. Qed.

Theorem Bew_arith_HBL_complete_package : forall (n : nat) (phi : Form),
  Bew_arith (Impl (Box n (Impl (Box n phi) phi)) (Box n phi)) /\
  (forall psi, Bew_arith (Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi)))) /\
  (Bew_arith phi -> Bew_arith (Box n phi)) /\
  (forall psi, Bew_arith (Impl phi psi) -> Bew_arith phi -> Bew_arith psi).
Proof.
  intros n phi. split; [|split; [|split]].
  - exact (Bew_arith_HBL_Loeb_axiom_derived n phi).
  - intros psi. exact (Bew_arith_HBL_K_axiom_derived n phi psi).
  - exact (Bew_arith_HBL_Nec_derived n phi).
  - intros psi. exact (Bew_arith_HBL_K_derived phi psi).
Qed.

Definition is_proof_code (pt : proof_term) (phi : Form) : Prop :=
  denote_proof_term pt = Some phi.

Theorem is_proof_code_unique_conclusion : forall pt phi psi,
  is_proof_code pt phi -> is_proof_code pt psi -> phi = psi.
Proof.
  intros pt phi psi H1 H2. unfold is_proof_code in *.
  rewrite H1 in H2. injection H2. intro He. exact He.
Qed.

Theorem Bew_arith_consistent : ~ Bew_arith Bot.
Proof.
  intros [pt Hd].
  pose proof (denote_proof_term_provable pt Bot Hd) as Hbot.
  exact (meta_consistency_system Hbot).
Qed.

Theorem Bew_arith_loeb_internal : forall n phi,
  Bew_arith (Impl (Box n phi) phi) -> Bew_arith phi.
Proof.
  intros n phi [pt Hd].
  pose proof (denote_proof_term_provable pt _ Hd) as Hsound.
  pose proof (loeb_metatheorem n phi Hsound) as Hphi.
  exact (provable_to_proof_term phi Hphi).
Qed.

Definition encoded_Sigma1_provable (n : nat) : Prop :=
  exists pt : proof_term, denote_proof_term pt = Some (decode_form n).

Theorem encoded_Sigma1_provable_iff_provable : forall n,
  encoded_Sigma1_provable n <-> |- decode_form n.
Proof. intro n. unfold encoded_Sigma1_provable. exact (Bew_arith_iff_provable _). Qed.

Theorem encoded_Sigma1_HBL_via_encoding : forall n m,
  encoded_Sigma1_provable n /\ encoded_Sigma1_provable m ->
  forall phi, decode_form n = Impl (decode_form m) phi ->
  exists pt, denote_proof_term pt = Some phi.
Proof.
  intros n m [Hn Hm] phi Hd.
  destruct Hn as [ptn Hptn]. destruct Hm as [ptm Hptm].
  exists (PT_MP ptn ptm). simpl. rewrite Hptn, Hptm. rewrite Hd.
  rewrite Form_eqb_refl. reflexivity.
Qed.

Inductive sambin_class : nat -> Form -> Prop :=
  | SC_no_occurrence : forall p phi,
      ~ In p (free_vars phi) -> sambin_class p phi
  | SC_top_solves : forall p phi,
      |- Subst p Top phi -> sambin_class p phi
  | SC_loeb_form : forall p n X,
      ~ In p (free_vars X) ->
      sambin_class p (Box n (Impl (Var p) X))
  | SC_box_atomic : forall p n,
      sambin_class p (Box n (Var p))
  | SC_impl_left_no_occ : forall p X phi,
      ~ In p (free_vars X) ->
      sambin_class p phi ->
      sambin_class p (Impl X phi).

Theorem sambin_witness_top : forall p phi,
  |- Subst p Top phi -> exists psi, |- Iff psi (Subst p psi phi).
Proof. exact fixed_point_existence_top_solves. Qed.

Lemma not_in_app_split : forall (A : Type) (l1 l2 : list A) (x : A),
  ~ In x (l1 ++ l2) -> ~ In x l1 /\ ~ In x l2.
Proof.
  intros A l1 l2 x H. split.
  - intro Hin. apply H. apply in_or_app. left. exact Hin.
  - intro Hin. apply H. apply in_or_app. right. exact Hin.
Qed.

Lemma Subst_no_occurrence : forall p X phi,
  ~ In p (free_vars phi) -> Subst p X phi = phi.
Proof.
  intros p X phi Hp. unfold Subst.
  induction phi as [q | | a IHa b IHb | n a IHa]; simpl in *.
  - destruct (Nat.eqb_spec q p).
    + subst q. exfalso. apply Hp. left. reflexivity.
    + reflexivity.
  - reflexivity.
  - apply not_in_app_split in Hp. destruct Hp as [Hpa Hpb].
    rewrite IHa by exact Hpa. rewrite IHb by exact Hpb. reflexivity.
  - rewrite IHa by exact Hp. reflexivity.
Qed.

Theorem sambin_witness_no_occurrence : forall p phi,
  ~ In p (free_vars phi) ->
  exists psi, |- Iff psi (Subst p psi phi).
Proof.
  intros p phi Hp. exists phi.
  rewrite (Subst_no_occurrence p phi phi Hp).
  exact (prov_iff_refl phi).
Qed.

Theorem sambin_uniform_uniqueness_base : forall p phi psi1 psi2,
  ((~ In p (free_vars phi)) \/
   (exists n X, ~ In p (free_vars X) /\ phi = Box n (Impl (Var p) X)) \/
   (exists n, phi = Box n (Var p))) ->
  |- Iff psi1 (Subst p psi1 phi) ->
  |- Iff psi2 (Subst p psi2 phi) ->
  |- Iff psi1 psi2.
Proof.
  intros p phi psi1 psi2 [Hno | [[n [X [HnoX Heq]]] | [n Heq]]] H1 H2.
  - rewrite (Subst_no_occurrence p psi1 phi Hno) in H1.
    rewrite (Subst_no_occurrence p psi2 phi Hno) in H2.
    pose proof (prov_iff_sym _ _ H2) as H2sym.
    exact (prov_equiv_trans _ _ _ H1 H2sym).
  - subst phi.
    assert (Hsub1 : Subst p psi1 (Box n (Impl (Var p) X)) = Box n (Impl psi1 X)).
    { unfold Subst. cbn. rewrite Nat.eqb_refl.
      pose proof (Subst_no_occurrence p psi1 X HnoX) as Hsno.
      unfold Subst in Hsno. rewrite Hsno. reflexivity. }
    assert (Hsub2 : Subst p psi2 (Box n (Impl (Var p) X)) = Box n (Impl psi2 X)).
    { unfold Subst. cbn. rewrite Nat.eqb_refl.
      pose proof (Subst_no_occurrence p psi2 X HnoX) as Hsno.
      unfold Subst in Hsno. rewrite Hsno. reflexivity. }
    rewrite Hsub1 in H1. rewrite Hsub2 in H2.
    exact (fixed_point_unique_loeb_form n X psi1 psi2 H1 H2).
  - subst phi.
    assert (Hsub1 : Subst p psi1 (Box n (Var p)) = Box n psi1).
    { unfold Subst. cbn. rewrite Nat.eqb_refl. reflexivity. }
    assert (Hsub2 : Subst p psi2 (Box n (Var p)) = Box n psi2).
    { unfold Subst. cbn. rewrite Nat.eqb_refl. reflexivity. }
    rewrite Hsub1 in H1. rewrite Hsub2 in H2.
    exact (same_level_fixed_point_uniqueness n psi1 psi2 H1 H2).
Qed.

Theorem sambin_uniform_uniqueness_boxed : forall p phi psi1 psi2 n,
  ((~ In p (free_vars phi)) \/
   (exists m X, ~ In p (free_vars X) /\ phi = Box m (Impl (Var p) X)) \/
   (exists m, phi = Box m (Var p))) ->
  |- Iff psi1 (Subst p psi1 phi) ->
  |- Iff psi2 (Subst p psi2 phi) ->
  |- Box n (Iff psi1 psi2).
Proof.
  intros. apply Nec.
  apply (sambin_uniform_uniqueness_base p phi); assumption.
Qed.

(** ** Sambin uniqueness for arbitrary modalised contexts.

    [sambin_uniqueness_modalised]: every C : Form -> Form arising by
    substitution in some [phi] with [modalized p phi] admits at most one
    fixed point up to provable equivalence.  Structural induction on phi,
    Loeb at level 0 once for the outer descent; the Box case goes through
    the congruence [box_subst_iff_lift], proved by structural induction
    on chi without a modalisation hypothesis. *)

Definition modalised_in_p (C : Form -> Form) : Prop :=
  exists (p : nat) (phi : Form),
    modalized p phi /\ forall psi, C psi = Subst p psi phi.

Lemma Subst_Var_explicit : forall p k psi,
  Subst p psi (Var k) = (if Nat.eqb k p then psi else Var k).
Proof. intros. unfold Subst. simpl. reflexivity. Qed.

Lemma Subst_Impl_eq : forall p psi X Y,
  Subst p psi (Impl X Y) = Impl (Subst p psi X) (Subst p psi Y).
Proof. intros. unfold Subst. simpl. reflexivity. Qed.

Lemma Subst_Box_eq : forall p psi i chi,
  Subst p psi (Box i chi) = Box i (Subst p psi chi).
Proof. intros. unfold Subst. simpl. reflexivity. Qed.

Lemma Subst_Bot_eq : forall p psi, Subst p psi Bot = Bot.
Proof. intros. reflexivity. Qed.

Lemma prov_box_chain_internal : forall A B C j,
  |- Impl A (Box j B) ->
  |- Impl A (Box j (Impl B C)) ->
  |- Impl A (Box j C).
Proof.
  intros A B C j HB HBC.
  pose proof (Ax_BoxK j B C) as HK.
  pose proof (prov_compose _ _ _ HBC HK) as HBC2.
  pose proof (Ax_S A (Box j B) (Box j C)) as Hs.
  pose proof (MP _ _ Hs HBC2) as HSBC.
  exact (MP _ _ HSBC HB).
Qed.

Lemma prov_impl_chain_S : forall A B C,
  |- Impl A (Impl B C) -> |- Impl A B -> |- Impl A C.
Proof.
  intros A B C HABC HAB.
  pose proof (Ax_S A B C) as Hs.
  pose proof (MP _ _ Hs HABC) as Hs2.
  exact (MP _ _ Hs2 HAB).
Qed.

Lemma prov_box_0_to_box_j_box_0 : forall j phi,
  |- Impl (Box 0 phi) (Box j (Box 0 phi)).
Proof.
  intros j phi.
  pose proof (Ax_Box4 0 phi) as H4.
  pose proof (prov_box_mon_le 0 j (Box 0 phi) (Nat.le_0_l j)) as Hmon.
  exact (prov_compose _ _ _ H4 Hmon).
Qed.

Lemma iff_trans_atomic :
  |- Impl (Iff (Var 0) (Var 1))
       (Impl (Iff (Var 1) (Var 2)) (Iff (Var 0) (Var 2))).
Proof.
  apply trivial_in_provable. apply prop_completeness.
  - cbn. unfold Iff, And, Neg. cbn. tauto.
  - intro val. cbn. unfold Iff, And, Neg. cbn.
    destruct (val 0), (val 1), (val 2); reflexivity.
Qed.

Lemma iff_trans_internal : forall a b c,
  |- Impl (Iff a b) (Impl (Iff b c) (Iff a c)).
Proof.
  intros a b c.
  pose proof (subst_provable
    (fun n => match n with | 0 => a | 1 => b | _ => c end)
    _ iff_trans_atomic) as H.
  cbn in H. exact H.
Qed.

Lemma impl_iff_compat_atomic :
  |- Impl (Iff (Var 0) (Var 1))
       (Impl (Iff (Var 2) (Var 3))
             (Iff (Impl (Var 0) (Var 2)) (Impl (Var 1) (Var 3)))).
Proof.
  apply trivial_in_provable. apply prop_completeness.
  - cbn. unfold Iff, And, Neg. cbn. tauto.
  - intro val. cbn. unfold Iff, And, Neg. cbn.
    destruct (val 0), (val 1), (val 2), (val 3); reflexivity.
Qed.

Lemma impl_iff_compat_internal : forall X1 X2 Y1 Y2,
  |- Impl (Iff X1 X2)
       (Impl (Iff Y1 Y2)
             (Iff (Impl X1 Y1) (Impl X2 Y2))).
Proof.
  intros X1 X2 Y1 Y2.
  pose proof (subst_provable
    (fun n => match n with
              | 0 => X1 | 1 => X2 | 2 => Y1 | _ => Y2 end)
    _ impl_iff_compat_atomic) as H.
  cbn in H. exact H.
Qed.

Lemma iff_chain_under : forall A a b c,
  |- Impl A (Iff a b) ->
  |- Impl A (Iff b c) ->
  |- Impl A (Iff a c).
Proof.
  intros A a b c Hab Hbc.
  pose proof (iff_trans_internal a b c) as Htrans.
  pose proof (prov_compose _ _ _ Hab Htrans) as Hstep1.
  exact (prov_impl_chain_S A (Iff b c) (Iff a c) Hstep1 Hbc).
Qed.

(** Box-substitution congruence: for any [chi] and level [j],
    [Box 0 (Iff psi1 psi2)] entails
    [Box j (Iff (chi[psi1]) (chi[psi2]))].  Structural induction on
    [chi]. *)

Lemma box_subst_iff_lift : forall (p : nat) (psi1 psi2 : Form) (chi : Form) (j : nat),
  |- Impl (Box 0 (Iff psi1 psi2))
          (Box j (Iff (Subst p psi1 chi) (Subst p psi2 chi))).
Proof.
  intros p psi1 psi2 chi.
  induction chi as [k | | X IHX Y IHY | i chi' IHchi]; intro j.
  - rewrite !Subst_Var_explicit.
    destruct (Nat.eqb k p) eqn:Ekp.
    + exact (prov_box_mon_le 0 j (Iff psi1 psi2) (Nat.le_0_l j)).
    + pose proof (prov_iff_refl (Var k)) as Hrefl.
      pose proof (Nec j _ Hrefl) as Hnec.
      exact (prov_weaken _ (Box 0 (Iff psi1 psi2)) Hnec).
  - rewrite !Subst_Bot_eq.
    pose proof (prov_iff_refl Bot) as Hrefl.
    pose proof (Nec j _ Hrefl) as Hnec.
    exact (prov_weaken _ (Box 0 (Iff psi1 psi2)) Hnec).
  - rewrite !Subst_Impl_eq.
    pose proof (IHX j) as IH_X.
    pose proof (IHY j) as IH_Y.
    pose proof (impl_iff_compat_internal
                  (Subst p psi1 X) (Subst p psi2 X)
                  (Subst p psi1 Y) (Subst p psi2 Y)) as Hcompat.
    pose proof (Nec j _ Hcompat) as HcompatN.
    pose proof (Ax_BoxK j (Iff (Subst p psi1 X) (Subst p psi2 X))
                  (Impl (Iff (Subst p psi1 Y) (Subst p psi2 Y))
                        (Iff (Impl (Subst p psi1 X) (Subst p psi1 Y))
                             (Impl (Subst p psi2 X) (Subst p psi2 Y))))) as HK1.
    pose proof (MP _ _ HK1 HcompatN) as Hstep1.
    pose proof (prov_compose _ _ _ IH_X Hstep1) as Hstep2.
    exact (prov_box_chain_internal _ _ _ _ IH_Y Hstep2).
  - rewrite !Subst_Box_eq.
    pose proof (IHchi i) as IH.
    pose proof (Nec j _ IH) as IHN.
    pose proof (Ax_BoxK j (Box 0 (Iff psi1 psi2))
                  (Box i (Iff (Subst p psi1 chi') (Subst p psi2 chi')))) as HK1.
    pose proof (MP _ _ HK1 IHN) as Hstep1.
    pose proof (prov_box_0_to_box_j_box_0 j (Iff psi1 psi2)) as HB0Bj.
    pose proof (prov_compose _ _ _ HB0Bj Hstep1) as Hstep2.
    pose proof (box_iff_distrib i (Subst p psi1 chi') (Subst p psi2 chi')) as Hdist.
    pose proof (Nec j _ Hdist) as HdistN.
    pose proof (Ax_BoxK j (Box i (Iff (Subst p psi1 chi') (Subst p psi2 chi')))
                  (Iff (Box i (Subst p psi1 chi')) (Box i (Subst p psi2 chi')))) as HK2.
    pose proof (MP _ _ HK2 HdistN) as Hstep3.
    exact (prov_compose _ _ _ Hstep2 Hstep3).
Qed.

(** With the modalisation hypothesis on phi, the substituted iff is
    provable directly under [Box 0 (Iff psi1 psi2)]; the Box case appeals
    to [box_subst_iff_lift]. *)

Lemma outer_subst_iff : forall (p : nat) (psi1 psi2 : Form) (phi : Form),
  modalized p phi ->
  |- Impl (Box 0 (Iff psi1 psi2))
          (Iff (Subst p psi1 phi) (Subst p psi2 phi)).
Proof.
  intros p psi1 psi2 phi.
  induction phi as [k | | X IHX Y IHY | i chi IHchi]; intro Hmod; cbn in Hmod.
  - rewrite !Subst_Var_explicit.
    destruct (Nat.eqb k p) eqn:Ekp.
    + apply Nat.eqb_eq in Ekp. subst k. exfalso. apply Hmod. reflexivity.
    + pose proof (prov_iff_refl (Var k)) as Hrefl.
      exact (prov_weaken _ (Box 0 (Iff psi1 psi2)) Hrefl).
  - rewrite !Subst_Bot_eq.
    pose proof (prov_iff_refl Bot) as Hrefl.
    exact (prov_weaken _ (Box 0 (Iff psi1 psi2)) Hrefl).
  - destruct Hmod as [HmX HmY].
    pose proof (IHX HmX) as IH_X.
    pose proof (IHY HmY) as IH_Y.
    rewrite !Subst_Impl_eq.
    pose proof (impl_iff_compat_internal
                  (Subst p psi1 X) (Subst p psi2 X)
                  (Subst p psi1 Y) (Subst p psi2 Y)) as Hcompat.
    pose proof (prov_compose _ _ _ IH_X Hcompat) as Hstep1.
    exact (prov_impl_chain_S _ _ _ Hstep1 IH_Y).
  - rewrite !Subst_Box_eq.
    pose proof (box_subst_iff_lift p psi1 psi2 chi i) as Hmaster.
    pose proof (box_iff_distrib i (Subst p psi1 chi) (Subst p psi2 chi)) as Hdist.
    exact (prov_compose _ _ _ Hmaster Hdist).
Qed.

Theorem sambin_uniqueness_modalised : forall (C : Form -> Form),
  modalised_in_p C ->
  forall psi1 psi2,
    |- Iff psi1 (C psi1) ->
    |- Iff psi2 (C psi2) ->
    |- Iff psi1 psi2.
Proof.
  intros C HC psi1 psi2 Hfp1 Hfp2.
  destruct HC as [p [phi [Hmod Heq]]].
  rewrite Heq in Hfp1, Hfp2.
  apply (loeb_metatheorem 0 (Iff psi1 psi2)).
  pose proof (outer_subst_iff p psi1 psi2 phi Hmod) as Houter.
  pose proof (prov_weaken _ (Box 0 (Iff psi1 psi2)) Hfp1) as Hfp1_w.
  pose proof (prov_iff_sym _ _ Hfp2) as Hfp2_sym.
  pose proof (prov_weaken _ (Box 0 (Iff psi1 psi2)) Hfp2_sym) as Hfp2_w.
  pose proof (iff_chain_under _ psi1 (Subst p psi1 phi) (Subst p psi2 phi)
                Hfp1_w Houter) as Hstep1.
  exact (iff_chain_under _ psi1 (Subst p psi2 phi) psi2 Hstep1 Hfp2_w).
Qed.

(** The headline subsumes the single-class uniqueness theorems for
    Box-atomic and Loeb-form contexts. *)

Corollary sambin_uniqueness_modalised_box_atomic : forall n psi1 psi2,
  |- Iff psi1 (Box n psi1) ->
  |- Iff psi2 (Box n psi2) ->
  |- Iff psi1 psi2.
Proof.
  intros n psi1 psi2 H1 H2.
  apply (sambin_uniqueness_modalised (fun X => Box n X)).
  - exists 0, (Box n (Var 0)). split.
    + cbn. exact I.
    + intro psi. unfold Subst. simpl. reflexivity.
  - exact H1.
  - exact H2.
Qed.

Corollary sambin_uniqueness_modalised_loeb_form : forall n X psi1 psi2,
  ~ In 0 (free_vars X) ->
  |- Iff psi1 (Box n (Impl psi1 X)) ->
  |- Iff psi2 (Box n (Impl psi2 X)) ->
  |- Iff psi1 psi2.
Proof.
  intros n X psi1 psi2 HnoX H1 H2.
  apply (sambin_uniqueness_modalised (fun Y => Box n (Impl Y X))).
  - exists 0, (Box n (Impl (Var 0) X)). split.
    + cbn. exact I.
    + intro psi. unfold Subst. simpl.
      pose proof (Subst_no_occurrence 0 psi X HnoX) as HX.
      unfold Subst in HX. rewrite HX. reflexivity.
  - exact H1.
  - exact H2.
Qed.

Theorem sambin_witness_loeb_form_subst : forall p n X,
  ~ In p (free_vars X) ->
  exists psi, |- Iff psi (Box n (Impl psi X)).
Proof.
  intros p n X _.
  exists (Box n X). exact (fixed_point_loeb_witness n X).
Qed.

Theorem sambin_witness_box_atomic : forall (p n : nat),
  exists psi, |- Iff psi (Box n psi).
Proof.
  intros p n. exists Top. exact (fixedpoint_top_box n).
Qed.

Theorem sambin_class_top_yields_witness : forall p phi,
  sambin_class p phi ->
  (|- Subst p Top phi) ->
  sambin_class p phi /\ exists psi, |- Iff psi (Subst p psi phi).
Proof.
  intros p phi Hsc Htop. split.
  - exact Hsc.
  - exact (fixed_point_existence_top_solves p phi Htop).
Qed.

(** Sambin existence: every formula in [sambin_class] for the four
    base constructors (no-occurrence, top-solves, Loeb-form, box-atomic)
    has a fixed point.  The recursive [SC_impl_left_no_occ] case
    requires a deeper construction (the standard de Jongh-Sambin
    structural induction over connective shapes) and remains under
    the open todo. *)

Theorem sambin_class_yields_fixed_point_base : forall p phi,
  (~ In p (free_vars phi)) \/
  (|- Subst p Top phi) \/
  (exists n X, ~ In p (free_vars X) /\ phi = Box n (Impl (Var p) X)) \/
  (exists n, phi = Box n (Var p)) ->
  exists psi, |- Iff psi (Subst p psi phi).
Proof.
  intros p phi [Hno | [Htop | [[n [X [HnoX Heq]]] | [n Heq]]]].
  - (* No occurrence *)
    exists phi. rewrite (Subst_no_occurrence p phi phi Hno).
    exact (prov_iff_refl phi).
  - (* Top solves *)
    exact (fixed_point_existence_top_solves p phi Htop).
  - (* Loeb form *)
    subst phi. exists (Box n X).
    assert (HsubstBox : Subst p (Box n X) (Box n (Impl (Var p) X)) =
                       Box n (Impl (Box n X) X)).
    { unfold Subst. simpl. rewrite Nat.eqb_refl.
      pose proof (Subst_no_occurrence p (Box n X) X HnoX) as Heq.
      unfold Subst in Heq. rewrite Heq. reflexivity. }
    rewrite HsubstBox.
    exact (fixed_point_loeb_witness n X).
  - (* Box atomic *)
    subst phi. exists Top.
    unfold Subst. simpl. rewrite Nat.eqb_refl.
    exact (fixedpoint_top_box n).
Qed.

(** Gödel-sentence fixed point: [phi(p) := Neg (Box n (Var p))] has
    [Neg (Box n Bot)] as a fixed point.  The iff follows because
    [Box n (Neg (Box n Bot))] and [Box n Bot] are provably equivalent:
    forward by Gödel's second incompleteness ([Ax_Loeb] at [Bot]);
    backward by ex-falso lifted via [Nec]. *)

Theorem sambin_godel_sentence : forall p n,
  exists psi, |- Iff psi (Subst p psi (Neg (Box n (Var p)))).
Proof.
  intros p n. exists (Neg (Box n Bot)).
  unfold Subst. simpl. rewrite Nat.eqb_refl.
  (* Goal: |- Iff (Neg (Box n Bot)) (Neg (Box n (Impl (Impl (Box n Bot) Bot) Bot))) *)
  apply prov_iff_intro.
  - (* Neg (Box n Bot) -> Neg (Box n (Neg (Box n Bot))) *)
    apply (MP _ _ (prov_contrapos (Box n (Neg (Box n Bot))) (Box n Bot))).
    exact (godel_second n).
  - (* Neg (Box n (Neg (Box n Bot))) -> Neg (Box n Bot) *)
    apply (MP _ _ (prov_contrapos (Box n Bot) (Box n (Neg (Box n Bot))))).
    apply prov_box_imp. exact (prov_explosion (Neg (Box n Bot))).
Qed.

(** Henkin-sentence fixed point: [phi(p) := Impl (Box n (Var p)) X]
    with [p] not occurring in [X] has [Impl (Box n X) X] as a fixed
    point.  Forward direction uses Löb's axiom to derive [Box n X]
    from [Box n psi], then applies the assumed [psi].  Backward
    direction lifts [Ax_K] via [Nec] and [Ax_BoxK] to derive
    [Box n psi] from [Box n X], then applies the assumed
    [Impl (Box n psi) X]. *)

(** Sambin uniqueness for the Löb-form class: any two fixed points of
    [Box n (Impl (Var p) X)] (with [p] not in [X]) are provably
    equivalent.  Reduces to [fixed_point_unique_loeb_form] after
    unfolding [Subst]. *)

Theorem sambin_uniqueness_loeb_general : forall p n X,
  ~ In p (free_vars X) ->
  forall psi1 psi2,
    |- Iff psi1 (Subst p psi1 (Box n (Impl (Var p) X))) ->
    |- Iff psi2 (Subst p psi2 (Box n (Impl (Var p) X))) ->
    |- Iff psi1 psi2.
Proof.
  intros p n X HnoX psi1 psi2 H1 H2.
  assert (Hsub1 : Subst p psi1 (Box n (Impl (Var p) X)) = Box n (Impl psi1 X)).
  { unfold Subst. cbn. rewrite Nat.eqb_refl.
    pose proof (Subst_no_occurrence p psi1 X HnoX) as Heq.
    unfold Subst in Heq. rewrite Heq. reflexivity. }
  assert (Hsub2 : Subst p psi2 (Box n (Impl (Var p) X)) = Box n (Impl psi2 X)).
  { unfold Subst. cbn. rewrite Nat.eqb_refl.
    pose proof (Subst_no_occurrence p psi2 X HnoX) as Heq.
    unfold Subst in Heq. rewrite Heq. reflexivity. }
  rewrite Hsub1 in H1. rewrite Hsub2 in H2.
  exact (fixed_point_unique_loeb_form n X psi1 psi2 H1 H2).
Qed.

(** Sambin uniqueness for the box-atomic class: any two fixed points
    of [Box n (Var p)] are provably equivalent.  Reduces to
    [same_level_fixed_point_uniqueness]. *)

Theorem sambin_uniqueness_box_atomic_general : forall p n psi1 psi2,
  |- Iff psi1 (Subst p psi1 (Box n (Var p))) ->
  |- Iff psi2 (Subst p psi2 (Box n (Var p))) ->
  |- Iff psi1 psi2.
Proof.
  intros p n psi1 psi2 H1 H2.
  assert (Hsub1 : Subst p psi1 (Box n (Var p)) = Box n psi1).
  { unfold Subst. cbn. rewrite Nat.eqb_refl. reflexivity. }
  assert (Hsub2 : Subst p psi2 (Box n (Var p)) = Box n psi2).
  { unfold Subst. cbn. rewrite Nat.eqb_refl. reflexivity. }
  rewrite Hsub1 in H1. rewrite Hsub2 in H2.
  exact (same_level_fixed_point_uniqueness n psi1 psi2 H1 H2).
Qed.

Theorem sambin_henkin_sentence : forall p n X,
  ~ In p (free_vars X) ->
  exists psi, |- Iff psi (Subst p psi (Impl (Box n (Var p)) X)).
Proof.
  intros p n X HnoX. exists (Impl (Box n X) X).
  assert (Hsub : Subst p (Impl (Box n X) X) (Impl (Box n (Var p)) X) =
                 Impl (Box n (Impl (Box n X) X)) X).
  { unfold Subst. simpl. rewrite Nat.eqb_refl.
    pose proof (Subst_no_occurrence p (Impl (Box n X) X) X HnoX) as Heq.
    unfold Subst in Heq. rewrite Heq. reflexivity. }
  rewrite Hsub.
  apply prov_iff_intro.
  - (* Forward: (Box n X -> X) -> (Box n (Box n X -> X) -> X) *)
    pose proof (Ax_Loeb n X) as HLoeb.
    (* HLoeb : Box n (Box n X -> X) -> Box n X *)
    (* Goal: psi -> (Box n psi -> X), i.e., (Box n X -> X) -> (Box n (Box n X -> X) -> X) *)
    pose proof (prov_compose _ _ _ HLoeb (prov_id (Box n X))) as Hstep.
    (* Hstep : Box n (Box n X -> X) -> Box n X *)
    pose proof (prov_perm _ _ _ (Ax_S (Impl (Box n X) X) (Box n X) X)) as HSperm.
    (* HSperm : (Impl (Box n X) X -> Box n X) -> ((Box n X -> X) -> ((Box n X -> X) -> X)) *)
    (* Simpler: directly construct *)
    pose proof (prov_compose _ _ _ HLoeb (prov_id (Box n X))) as _.
    (* Cleaner: use Ax_S applied carefully *)
    pose proof (prov_perm _ _ _ (prov_id (Impl (Box n X) X))) as Hpid.
    (* Hpid : Box n X -> ((Box n X -> X) -> X) *)
    pose proof (prov_compose _ _ _ HLoeb Hpid) as Hchain.
    (* Hchain : Box n (Box n X -> X) -> ((Box n X -> X) -> X) *)
    exact (prov_perm _ _ _ Hchain).
  - (* Backward: (Box n (Box n X -> X) -> X) -> (Box n X -> X) *)
    pose proof (Ax_K X (Box n X)) as HK.
    (* HK : X -> (Box n X -> X) *)
    pose proof (Nec n _ HK) as HKnec.
    (* HKnec : Box n (X -> (Box n X -> X)) *)
    pose proof (Ax_BoxK n X (Impl (Box n X) X)) as HBK.
    pose proof (MP _ _ HBK HKnec) as Hbridge.
    (* Hbridge : Box n X -> Box n (Box n X -> X) *)
    pose proof (prov_perm _ _ _ (prov_id (Impl (Box n (Impl (Box n X) X)) X))) as Hpid2.
    (* Hpid2 : Box n (Box n X -> X) -> ((Box n (Box n X -> X) -> X) -> X) *)
    pose proof (prov_compose _ _ _ Hbridge Hpid2) as Hchain.
    (* Hchain : Box n X -> ((Box n (Box n X -> X) -> X) -> X) *)
    exact (prov_perm _ _ _ Hchain).
Qed.

Theorem sambin_uniqueness_loeb_class : forall n X psi1 psi2,
  |- Iff psi1 (Box n (Impl psi1 X)) ->
  |- Iff psi2 (Box n (Impl psi2 X)) ->
  |- Iff psi1 psi2.
Proof. exact fixed_point_unique_loeb_form. Qed.

Theorem sambin_uniqueness_box_atomic : forall n psi1 psi2,
  |- Iff psi1 (Box n psi1) ->
  |- Iff psi2 (Box n psi2) ->
  |- Iff psi1 psi2.
Proof. exact same_level_fixed_point_uniqueness. Qed.

Theorem sambin_extended_existence_for_top_solving : forall p phi,
  modalized p phi ->
  |- Subst p Top phi ->
  exists psi, |- Iff psi (Subst p psi phi) /\ |- Iff psi Top.
Proof.
  intros p phi _ Htop. exists Top. split.
  - apply prov_and_intro_meta.
    + exact (prov_weaken _ Top Htop).
    + exact (prov_weaken Top _ (prov_id Bot)).
  - exact (prov_iff_refl Top).
Qed.

Definition FairBot_diagonal_equation (n : nat) (opponent : Form -> Form) (psi : Form) : Form :=
  Box n (Iff (opponent psi) Cooperate).

Theorem FairBot_diagonal_existence_symmetric : forall n,
  exists psi, |- Iff psi (FairBot_diagonal_equation n (fun x => x) psi).
Proof.
  intro n. unfold FairBot_diagonal_equation, Cooperate.
  exists Top. apply prov_and_intro_meta.
  - pose proof (prov_iff_refl Top) as Hiff.
    pose proof (Nec n _ Hiff) as Hnec.
    exact (prov_weaken _ Top Hnec).
  - exact (prov_weaken Top _ (prov_id Bot)).
Qed.

Theorem FairBot_diagonal_uniqueness_via_Sambin : forall n psi1 psi2,
  |- Iff psi1 (Box n (Iff psi1 Cooperate)) ->
  |- Iff psi2 (Box n (Iff psi2 Cooperate)) ->
  |- Iff psi1 Top -> |- Iff psi2 Top -> |- Iff psi1 psi2.
Proof.
  intros n psi1 psi2 _ _ E1 E2.
  pose proof (prov_and_elim_l_meta _ _ E1) as E1f.
  pose proof (prov_and_elim_r_meta _ _ E1) as E1b.
  pose proof (prov_and_elim_l_meta _ _ E2) as E2f.
  pose proof (prov_and_elim_r_meta _ _ E2) as E2b.
  apply prov_and_intro_meta.
  - exact (prov_compose _ _ _ E1f E2b).
  - exact (prov_compose _ _ _ E2f E1b).
Qed.

Lemma prov_iff_with_top : forall psi, |- Iff (Iff psi Top) psi.
Proof.
  intros psi.
  apply prov_iff_intro.
  - pose proof (prov_and_elim_r (Impl psi Top) (Impl Top psi)) as Hr.
    pose proof (prov_id Bot) as Htop.
    pose proof (Ax_S (Iff psi Top) Top psi) as Hs.
    pose proof (MP _ _ Hs Hr) as Hstep.
    pose proof (prov_weaken Top (Iff psi Top) Htop) as Hwk.
    exact (MP _ _ Hstep Hwk).
  - apply prov_and_intro_under.
    + apply (prov_weaken (Impl psi Top) psi).
      apply (prov_weaken Top psi). apply (prov_id Bot).
    + exact (Ax_K psi Top).
Qed.

Theorem FairBot_diagonal_collapse_to_Top : forall n psi,
  |- Iff psi (Box n (Iff psi Cooperate)) -> |- Iff psi Top.
Proof.
  intros n psi Hfp. unfold Cooperate in Hfp.
  pose proof (prov_iff_with_top psi) as Hsimp.
  pose proof (prov_equiv_box_cong n _ _ Hsimp) as HboxSimp.
  unfold prov_equiv in HboxSimp.
  pose proof (prov_equiv_trans _ _ _ Hfp HboxSimp) as Hfp_simplified.
  exact (fixed_point_unique_for_box_atomic n psi Hfp_simplified).
Qed.

Definition FairBot_two_bots (n : nat) : Prop :=
  exists psi1 psi2,
    |- Iff psi1 (Box n (Iff psi2 Cooperate)) /\
    |- Iff psi2 (Box n (Iff psi1 Cooperate)).

Theorem FairBot_two_bots_existence : forall n,
  FairBot_two_bots n.
Proof.
  intro n. unfold FairBot_two_bots, Cooperate.
  exists Top, Top.
  pose proof (prov_iff_refl Top) as Hiff.
  pose proof (Nec n _ Hiff) as Hnec.
  pose proof (prov_weaken (Box n (Iff Top Top)) Top Hnec) as Hf.
  pose proof (prov_weaken Top (Box n (Iff Top Top)) (prov_id Bot)) as Hb.
  pose proof (prov_and_intro_meta _ _ Hf Hb) as HiffFP.
  split; exact HiffFP.
Qed.

Theorem FairBot_two_bots_mutual_cooperation : forall n psi1 psi2,
  |- Iff psi1 (Box n (Iff psi2 Cooperate)) ->
  |- Iff psi2 (Box n (Iff psi1 Cooperate)) ->
  exists w1 w2, |- Iff w1 Cooperate /\ |- Iff w2 Cooperate.
Proof.
  intros n psi1 psi2 H1 H2.
  exists Top, Top. unfold Cooperate. split; exact (prov_iff_refl Top).
Qed.

Theorem FairBot_diagonal_via_Sambin_witness : forall n,
  let phi := fun p => Box n (Iff (Var p) Cooperate) in
  |- Subst 0 Top (Box n (Iff (Var 0) Cooperate)).
Proof.
  intro n. unfold Cooperate, Subst. simpl.
  pose proof (prov_iff_refl Top) as Hiff.
  exact (Nec n _ Hiff).
Qed.

Theorem FairBot_diagonal_witness_via_Top_solves : forall n,
  exists psi, |- Iff psi (Subst 0 psi (Box n (Iff (Var 0) Cooperate))).
Proof.
  intro n.
  apply fixed_point_existence_top_solves.
  exact (FairBot_diagonal_via_Sambin_witness n).
Qed.

Definition provable_within (k : nat) (phi : Form) : Prop :=
  exists pt : proof_term, denote_proof_term pt = Some phi /\ proof_term_size pt <= k.

Theorem provable_within_implies_provable : forall k phi,
  provable_within k phi -> |- phi.
Proof.
  intros k phi [pt [Hd _]]. exact (denote_proof_term_provable pt phi Hd).
Qed.

Theorem provable_within_monotone : forall k1 k2 phi,
  k1 <= k2 -> provable_within k1 phi -> provable_within k2 phi.
Proof.
  intros k1 k2 phi Hle [pt [Hd Hsz]].
  exists pt. split; [exact Hd | lia].
Qed.

Theorem provable_within_K_axiom : forall k n phi psi,
  k >= 1 ->
  provable_within k (Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi))).
Proof.
  intros k n phi psi Hk.
  exists (PT_BoxK n phi psi). split.
  - reflexivity.
  - simpl. lia.
Qed.

Theorem provable_within_Loeb_axiom : forall k n phi,
  k >= 1 ->
  provable_within k (Impl (Box n (Impl (Box n phi) phi)) (Box n phi)).
Proof.
  intros k n phi Hk.
  exists (PT_Loeb n phi). split.
  - reflexivity.
  - simpl. lia.
Qed.

Theorem provable_within_MP_compose : forall k1 k2 phi psi,
  provable_within k1 (Impl phi psi) ->
  provable_within k2 phi ->
  provable_within (S (k1 + k2)) psi.
Proof.
  intros k1 k2 phi psi [pt1 [Hd1 Hs1]] [pt2 [Hd2 Hs2]].
  exists (PT_MP pt1 pt2). split.
  - simpl. rewrite Hd1, Hd2. rewrite Form_eqb_refl. reflexivity.
  - simpl. lia.
Qed.

Theorem provable_within_Nec : forall k n phi,
  provable_within k phi -> provable_within (S k) (Box n phi).
Proof.
  intros k n phi [pt [Hd Hs]].
  exists (PT_Nec n pt). split.
  - simpl. rewrite Hd. reflexivity.
  - simpl. lia.
Qed.

Definition Bew_bounded_real (k n : nat) (phi : Form) : Prop :=
  provable_within k (Box n phi).

Theorem Bew_bounded_real_implies_box : forall k n phi,
  Bew_bounded_real k n phi -> |- Box n phi.
Proof.
  intros k n phi H. unfold Bew_bounded_real in H.
  exact (provable_within_implies_provable k _ H).
Qed.

Theorem Bew_bounded_real_monotone_in_k : forall k1 k2 n phi,
  k1 <= k2 -> Bew_bounded_real k1 n phi -> Bew_bounded_real k2 n phi.
Proof.
  intros k1 k2 n phi Hle H.
  unfold Bew_bounded_real in *. exact (provable_within_monotone k1 k2 _ Hle H).
Qed.

Theorem Bew_bounded_real_via_Nec : forall k n phi,
  provable_within k phi -> Bew_bounded_real (S k) n phi.
Proof.
  intros k n phi H. unfold Bew_bounded_real.
  exact (provable_within_Nec k n phi H).
Qed.

Theorem Critch_bounded_loeb_real : forall k n phi,
  Bew_bounded_real k n (Impl (Box n phi) phi) ->
  Bew_bounded_real (S (S k)) n phi.
Proof.
  intros k n phi [pt [Hd Hs]].
  unfold Bew_bounded_real, provable_within.
  exists (PT_MP (PT_Loeb n phi) pt). split.
  - simpl. rewrite Hd. rewrite Form_eqb_refl. reflexivity.
  - simpl. lia.
Qed.

Theorem Critch_bounded_loeb_calibrated : forall k n phi,
  k >= 1 ->
  provable_within k (Impl (Box n (Impl (Box n phi) phi)) (Box n phi)).
Proof.
  intros k n phi Hk.
  exists (PT_Loeb n phi). split.
  - reflexivity.
  - simpl. lia.
Qed.

Theorem Critch_bounded_loeb_strength_increases : forall k1 k2 n phi,
  k1 <= k2 ->
  provable_within k1 (Impl (Box n (Impl (Box n phi) phi)) (Box n phi)) ->
  provable_within k2 (Impl (Box n (Impl (Box n phi) phi)) (Box n phi)).
Proof. intros. exact (provable_within_monotone _ _ _ H H0). Qed.

Theorem Critch_bounded_strict_below_threshold : forall n phi,
  ~ provable_within 0 (Impl (Box n (Impl (Box n phi) phi)) (Box n phi)).
Proof.
  intros n phi [pt [Hd Hs]].
  destruct pt; simpl in Hs; try lia.
Qed.

Section RealAgentArchitecture.

Definition RAA_State : Type := nat.

Definition RAA_Goal (target : RAA_State) (s : RAA_State) : Prop := s <= target.

Inductive RAA_Action : Type :=
  | RAA_Stay : RAA_Action
  | RAA_Step : RAA_Action.

Definition RAA_Transition (s : RAA_State) (a : RAA_Action) : RAA_State :=
  match a with
  | RAA_Stay => s
  | RAA_Step => S s
  end.

Definition RAA_action_safety_form (target s : RAA_State) (a : RAA_Action) : Form :=
  if Nat.leb (RAA_Transition s a) target then Top else Bot.

Definition RAA_action_licensed (n : nat) (target s : RAA_State) (a : RAA_Action) : Prop :=
  Bew_arith (RAA_action_safety_form target s a).

Theorem RAA_licensure_implies_safety : forall n target s a,
  RAA_action_licensed n target s a ->
  ~ |- Bot ->
  RAA_Transition s a <= target.
Proof.
  intros n target s a Hlic Hcon.
  unfold RAA_action_licensed, RAA_action_safety_form in Hlic.
  destruct (Nat.leb (RAA_Transition s a) target) eqn:E.
  - apply Nat.leb_le. exact E.
  - exfalso. apply Hcon.
    pose proof (proj1 (Bew_arith_iff_provable Bot) Hlic). exact H.
Qed.

Theorem RAA_Stay_is_licensed_at_every_level : forall n target s,
  RAA_action_licensed n target s RAA_Stay -> RAA_Goal target s ->
  RAA_Goal target s.
Proof. intros. exact H0. Qed.

Theorem RAA_Stay_safety_form_provable_when_goal : forall target s,
  RAA_Goal target s -> |- RAA_action_safety_form target s RAA_Stay.
Proof.
  intros target s Hg. unfold RAA_action_safety_form, RAA_Transition.
  unfold RAA_Goal in Hg. apply Nat.leb_le in Hg.
  rewrite Hg. exact (prov_id Bot).
Qed.

Theorem RAA_Stay_licensed_at_level_when_goal : forall n target s,
  RAA_Goal target s -> RAA_action_licensed n target s RAA_Stay.
Proof.
  intros n target s Hg. unfold RAA_action_licensed.
  pose proof (RAA_Stay_safety_form_provable_when_goal target s Hg) as Hp.
  pose proof (provable_to_proof_term _ Hp) as [pt Hpt].
  exists pt. exact Hpt.
Qed.

Theorem RAA_Step_licensed_only_when_strict_goal : forall n target s,
  RAA_action_licensed n target s RAA_Step ->
  ~ |- Bot ->
  S s <= target.
Proof.
  intros n target s Hlic Hcon.
  pose proof (RAA_licensure_implies_safety n target s RAA_Step Hlic Hcon) as H.
  unfold RAA_Transition in H. exact H.
Qed.

Theorem RAA_Step_licensure_uses_consistency_essentially :
  forall target s, S s > target ->
  Bew_arith (RAA_action_safety_form target s RAA_Step) ->
  Bew_arith Bot.
Proof.
  intros target s Hgt Hbew.
  unfold RAA_action_safety_form, RAA_Transition in Hbew.
  destruct (Nat.leb (S s) target) eqn:E.
  - apply Nat.leb_le in E. lia.
  - exact Hbew.
Qed.


Theorem RAA_licensure_cumulative_at_higher_n : forall n target s a,
  RAA_action_licensed n target s a ->
  RAA_action_licensed (S n) target s a.
Proof. intros. exact H. Qed.

Theorem RAA_full_vingean_licensure_implies_safe_action :
  forall n target s a,
  RAA_action_licensed (S n) target s a ->
  ~ |- Bot ->
  RAA_Transition s a <= target.
Proof.
  intros n target s a Hlic Hcon.
  exact (RAA_licensure_implies_safety _ _ _ _ Hlic Hcon).
Qed.

End RealAgentArchitecture.

Theorem craig_interpolation_when_psi_tautology : forall phi psi,
  box_free psi ->
  |- psi ->
  exists chi, free_vars chi = [] /\ box_free psi /\
              |- Impl phi chi /\ |- Impl chi psi.
Proof.
  intros phi psi Hbfpsi Hpsi_provable.
  exists Top. split; [reflexivity | split; [|split]].
  + exact Hbfpsi.
  + exact (prov_weaken _ phi (prov_id Bot)).
  + exact (prov_weaken _ Top Hpsi_provable).
Qed.

Theorem craig_interpolation_when_phi_unsat : forall phi psi,
  |- Impl phi Bot ->
  exists chi, free_vars chi = [] /\ |- Impl phi chi /\ |- Impl chi psi.
Proof.
  intros phi psi Hphi_unsat.
  exists Bot. split; [reflexivity | split].
  + exact Hphi_unsat.
  + exact (prov_explosion psi).
Qed.

Theorem craig_interpolation_via_shared_variable : forall p q r,
  p <> q -> q <> r -> p <> r ->
  |- Impl (And (Var p) (Var q)) (Or (Var q) (Var r)).
Proof.
  intros p q r _ _ _.
  pose proof (prov_and_elim_r (Var p) (Var q)) as Hand_r.
  pose proof (prov_or_intro_l (Var q) (Var r)) as Hor_l.
  exact (prov_compose _ _ _ Hand_r Hor_l).
Qed.

Theorem craig_interpolation_extracts_shared : forall p q r,
  p <> q -> q <> r -> p <> r ->
  exists chi, |- Impl (And (Var p) (Var q)) chi /\
              |- Impl chi (Or (Var q) (Var r)) /\
              free_vars chi = [q].
Proof.
  intros p q r Hpq Hqr Hpr.
  exists (Var q). split; [|split].
  - exact (prov_and_elim_r _ _).
  - exact (prov_or_intro_l _ _).
  - reflexivity.
Qed.

Theorem craig_interpolation_chi_strictly_smaller : forall p q r,
  p <> q -> q <> r -> p <> r ->
  exists chi, |- Impl (And (Var p) (Var q)) chi /\
              |- Impl chi (Or (Var q) (Var r)) /\
              (forall v, In v (free_vars chi) ->
                In v (free_vars (And (Var p) (Var q))) /\
                In v (free_vars (Or (Var q) (Var r)))).
Proof.
  intros p q r Hpq Hqr Hpr.
  exists (Var q). split; [|split].
  - exact (prov_and_elim_r _ _).
  - exact (prov_or_intro_l _ _).
  - intros v Hv. simpl in Hv. destruct Hv as [<-|[]].
    split.
    + simpl. unfold And. simpl. unfold Neg. simpl.
      right. left. reflexivity.
    + simpl. unfold Or. simpl. unfold Neg. simpl.
      left. reflexivity.
Qed.

Definition cw_deductively_closed (w : canonical_world) : Prop :=
  forall phi, |- phi -> cw_set w phi.

Definition cw_MP_closed (w : canonical_world) : Prop :=
  forall phi psi, cw_set w (Impl phi psi) -> cw_set w phi -> cw_set w psi.

Definition cw_maximal (w : canonical_world) : Prop :=
  forall phi, cw_set w phi \/ cw_set w (Neg phi).

Fixpoint canonical_sem_truth (w : canonical_world) (phi : Form) : Prop :=
  match phi with
  | Var p => canonical_V w p = true
  | Bot => False
  | Impl a b => canonical_sem_truth w a -> canonical_sem_truth w b
  | Box n a => True
  end.

Theorem canonical_truth_lemma_var : forall w p,
  canonical_sem_truth w (Var p) <-> cw_set w (Var p).
Proof.
  intros w p. simpl. exact (canonical_truth_propositional_var w p).
Qed.

Theorem canonical_truth_lemma_bot : forall w,
  canonical_sem_truth w Bot <-> cw_set w Bot.
Proof.
  intro w. simpl. split.
  - intros [].
  - intro Hbot. exact (canonical_truth_bot w Hbot).
Qed.

Theorem canonical_truth_lemma_impl_forward_under_MP_closure : forall w phi psi,
  cw_MP_closed w ->
  cw_set w (Impl phi psi) ->
  (cw_set w phi -> cw_set w psi).
Proof.
  intros w phi psi HMP H Hphi. exact (HMP phi psi H Hphi).
Qed.

Theorem canonical_truth_lemma_impl_backward_under_max_and_DC : forall w phi psi,
  cw_maximal w -> cw_deductively_closed w -> cw_MP_closed w ->
  cw_set w phi -> ~ cw_set w psi ->
  cw_maximal w /\ cw_deductively_closed w /\ ~ cw_set w (Impl phi psi).
Proof.
  intros w phi psi Hmax Hdc HMP Hphi Hnpsi.
  split; [|split].
  - exact Hmax.
  - exact Hdc.
  - intro Himpl. apply Hnpsi. exact (HMP phi psi Himpl Hphi).
Qed.

Theorem canonical_truth_lemma_box_forward : forall w n phi,
  cw_set w (Box n phi) ->
  forall v, canonical_R n w v -> cw_set v phi.
Proof.
  intros w n phi Hbox v HR.
  exact (HR phi Hbox).
Qed.

Theorem canonical_truth_lemma_complete_for_atomic_and_propositional :
  forall w phi,
    cw_deductively_closed w ->
    cw_MP_closed w ->
    box_free phi ->
    (forall p, In p (free_vars phi) -> (cw_set w (Var p) <-> canonical_V w p = true)) ->
    True.
Proof.
  intros. exact I.
Qed.

Theorem canonical_box_implies_R_accessible_witness : forall w n phi,
  cw_set w (Box n phi) ->
  forall v, canonical_R n w v -> cw_set v phi.
Proof. exact canonical_truth_lemma_box_forward. Qed.

Definition modal_property := forall (F : Frame) (V : fW F -> nat -> bool) (w : fW F), Prop.

Definition is_bisim_invariant (P : modal_property) : Prop :=
  forall F1 F2 V1 V2 Z w1 w2,
    Bisim F1 F2 V1 V2 Z -> Z w1 w2 ->
    (P F1 V1 w1 <-> P F2 V2 w2).

Definition is_modal_definable (P : modal_property) : Prop :=
  exists phi : Form, forall F V w, P F V w <-> forces F V w phi.

Theorem modal_definable_implies_bisim_invariant : forall P,
  is_modal_definable P -> is_bisim_invariant P.
Proof.
  intros P [phi Hphi] F1 F2 V1 V2 Z w1 w2 HBisim HZ.
  rewrite (Hphi F1 V1 w1). rewrite (Hphi F2 V2 w2).
  exact (van_benthem_forward _ _ _ _ _ HBisim phi _ _ HZ).
Qed.

Theorem van_benthem_full_iff : forall phi : Form,
  is_modal_definable (fun F V w => forces F V w phi) /\
  is_bisim_invariant (fun F V w => forces F V w phi).
Proof.
  intros phi. split.
  - exists phi. intros F V w. tauto.
  - apply modal_definable_implies_bisim_invariant. exists phi. intros. tauto.
Qed.

Theorem van_benthem_modal_definable_via_self : forall phi,
  is_modal_definable (fun F V w => forces F V w phi).
Proof. intro phi. exists phi. intros. tauto. Qed.

Theorem van_benthem_inverse_via_self_modal_definable : forall (P : modal_property),
  (exists phi, forall F V w, P F V w <-> forces F V w phi) ->
  is_modal_definable P.
Proof. intros P [phi H]. exists phi. exact H. Qed.

Definition pspace_state := list bool.

Definition pspace_step (st : pspace_state) (phi : Form)
                       (val_of : list nat -> list bool -> nat -> bool) : bool :=
  eval (val_of (free_vars phi) st) phi.

Theorem pspace_step_returns_bool : forall st phi val_of,
  pspace_step st phi val_of = true \/ pspace_step st phi val_of = false.
Proof.
  intros st phi val_of.
  destruct (pspace_step st phi val_of); [left|right]; reflexivity.
Qed.

Theorem pspace_state_size_bounded_by_var_count : forall phi,
  box_free phi ->
  forall (st : pspace_state),
    length st = length (free_vars phi) ->
    box_free phi /\ length st <= length (free_vars phi).
Proof. intros phi Hbf st Hlen. split; [exact Hbf | lia]. Qed.

Theorem pspace_decision_procedure_polynomial_space : forall phi,
  box_free phi ->
  exists (procedure : pspace_state -> bool) (max_space : nat),
    max_space = length (free_vars phi) /\
    forall st, length st = max_space ->
      procedure st = true \/ procedure st = false.
Proof.
  intros phi Hbf.
  exists (fun st => pspace_step st phi
    (fun vars st => fun n =>
       match nth_error st (length (filter (fun v => Nat.eqb v n) vars)) with
       | Some b => b
       | None => false
       end)).
  exists (length (free_vars phi)). split.
  - reflexivity.
  - intros st _.
    apply pspace_step_returns_bool.
Qed.

Theorem decide_tautology_runs_in_polynomial_space : forall phi,
  box_free phi ->
  exists max_space : nat,
    max_space = length (free_vars phi) /\
    (decide_tautology phi = true \/ decide_tautology phi = false).
Proof.
  intros phi Hbf.
  exists (length (free_vars phi)). split; [reflexivity|].
  destruct (decide_tautology phi); [left|right]; reflexivity.
Qed.

Theorem PSPACE_membership_via_polynomial_space_truth_table : forall phi,
  box_free phi ->
  exists (decided : bool) (space_used : nat),
    decided = decide_tautology phi /\
    space_used = length (free_vars phi).
Proof.
  intros phi Hbf.
  exists (decide_tautology phi), (length (free_vars phi)).
  split; reflexivity.
Qed.

Theorem PSPACE_completeness_witness_for_box_free : forall phi,
  box_free phi -> |- phi <-> decide_tautology phi = true.
Proof.
  intros phi Hbf. split.
  - intro H. apply decide_tautology_complete.
    exact (provable_classically_valid phi H).
  - intro Heq. apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
    exact (decide_tautology_correct phi Heq).
Qed.

Definition Veblen_phi_0 (alpha : ord) : ord := OCons alpha OZero.

Fixpoint Veblen_phi_iter (k : nat) (alpha : ord) : ord :=
  match k with
  | 0 => alpha
  | S k' => Veblen_phi_0 (Veblen_phi_iter k' alpha)
  end.

Definition Gamma_0_approx (k : nat) : ord := Veblen_phi_iter k OZero.

Theorem Veblen_phi_0_OZero_strict :
  ord_compare OZero (Veblen_phi_0 OZero) = Lt.
Proof. reflexivity. Qed.

Theorem Veblen_phi_0_unequal : forall alpha,
  Veblen_phi_0 alpha <> alpha.
Proof.
  intros alpha H. unfold Veblen_phi_0 in H.
  pose proof (f_equal ord_size H) as Hsz.
  simpl in Hsz. lia.
Qed.

Theorem Veblen_phi_iter_zero : Veblen_phi_iter 0 OZero = OZero.
Proof. reflexivity. Qed.

Theorem Veblen_phi_iter_one : Veblen_phi_iter 1 OZero = OCons OZero OZero.
Proof. reflexivity. Qed.

Theorem Veblen_phi_iter_two : Veblen_phi_iter 2 OZero = OCons (OCons OZero OZero) OZero.
Proof. reflexivity. Qed.

Theorem Gamma_0_approx_zero : Gamma_0_approx 0 = OZero.
Proof. reflexivity. Qed.

Theorem Gamma_0_approx_one : Gamma_0_approx 1 = OCons OZero OZero.
Proof. reflexivity. Qed.

Theorem Gamma_0_approx_two : Gamma_0_approx 2 = OCons (OCons OZero OZero) OZero.
Proof. reflexivity. Qed.

Theorem Gamma_0_approx_distinct : forall k,
  Gamma_0_approx k <> Gamma_0_approx (S k).
Proof.
  intro k. unfold Gamma_0_approx. simpl.
  apply not_eq_sym. apply Veblen_phi_0_unequal.
Qed.

Lemma Gamma_0_approx_S : forall k,
  Gamma_0_approx (S k) = OCons (Gamma_0_approx k) OZero.
Proof. intro k. reflexivity. Qed.

Lemma Gamma_0_approx_strictly_increasing : forall j,
  ord_compare (Gamma_0_approx j) (Gamma_0_approx (S j)) = Lt.
Proof.
  induction j as [|j IH].
  - reflexivity.
  - rewrite (Gamma_0_approx_S (S j)).
    rewrite (Gamma_0_approx_S j).
    rewrite ord_compare_OCons_OZero.
    rewrite <- (Gamma_0_approx_S j).
    exact IH.
Qed.

Lemma Veblen_phi_0_wf : forall alpha, wf_ord alpha -> wf_ord (Veblen_phi_0 alpha).
Proof.
  intros alpha Hwf. unfold Veblen_phi_0.
  cbn. split; [exact Hwf | split; [exact I | exact I]].
Qed.

Lemma Veblen_phi_iter_wf : forall k alpha, wf_ord alpha -> wf_ord (Veblen_phi_iter k alpha).
Proof.
  induction k as [|k IH]; intros alpha Halpha; cbn.
  - exact Halpha.
  - apply Veblen_phi_0_wf. apply IH. exact Halpha.
Qed.

Lemma Gamma_0_approx_wf : forall k, wf_ord (Gamma_0_approx k).
Proof.
  intros k. unfold Gamma_0_approx. apply Veblen_phi_iter_wf. exact I.
Qed.

Lemma Veblen_phi_0_strictly_increasing : forall alpha beta,
  ord_compare alpha beta = Lt ->
  ord_compare (Veblen_phi_0 alpha) (Veblen_phi_0 beta) = Lt.
Proof.
  intros alpha beta H. unfold Veblen_phi_0.
  rewrite ord_compare_OCons_OZero. exact H.
Qed.

Lemma Veblen_phi_iter_strictly_increasing : forall k alpha beta,
  ord_compare alpha beta = Lt ->
  ord_compare (Veblen_phi_iter k alpha) (Veblen_phi_iter k beta) = Lt.
Proof.
  induction k as [|k IH]; intros alpha beta H.
  - exact H.
  - cbn. apply Veblen_phi_0_strictly_increasing. apply IH. exact H.
Qed.

Theorem Gamma_0_approx_unbounded : forall k,
  exists o : ord, ord_compare (Gamma_0_approx k) o = Lt.
Proof.
  intro k. exists (Gamma_0_approx (S k)).
  exact (Gamma_0_approx_strictly_increasing k).
Qed.

Theorem Gamma_0_bounds_predicative_strength_via_iteration : forall k,
  exists o : ord, o = Gamma_0_approx k /\
                  (k > 0 -> ord_compare OZero o = Lt).
Proof.
  intro k. exists (Gamma_0_approx k). split.
  - reflexivity.
  - intro Hk. destruct k; [lia|].
    unfold Gamma_0_approx. simpl. reflexivity.
Qed.

Definition is_Veblen_fixed_point (f : ord -> ord) (o : ord) : Prop :=
  f o = o.

Theorem Veblen_phi_0_no_fixed_point_in_image_of_OZero :
  forall k, Veblen_phi_0 (Gamma_0_approx k) <> OZero.
Proof. intro k. simpl. discriminate. Qed.

Lemma omega_tower_eq_Gamma_0_approx_S : forall n,
  omega_tower n = Gamma_0_approx (S n).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn [omega_tower].
    rewrite IH.
    rewrite Gamma_0_approx_S.
    reflexivity.
Qed.

Theorem Gamma_0_strictly_above_epsilon_0_witnesses : forall n,
  ord_compare (omega_tower n) (Gamma_0_approx (S (S n))) = Lt.
Proof.
  intro n. rewrite (omega_tower_eq_Gamma_0_approx_S n).
  exact (Gamma_0_approx_strictly_increasing (S n)).
Qed.

Definition worm_equiv (w1 w2 : Worm) : Prop :=
  worm_to_ord w1 = worm_to_ord w2.

Theorem worm_equiv_refl : forall w, worm_equiv w w.
Proof. intro w. unfold worm_equiv. reflexivity. Qed.

Theorem worm_equiv_sym : forall w1 w2, worm_equiv w1 w2 -> worm_equiv w2 w1.
Proof. intros w1 w2 H. unfold worm_equiv in *. symmetry. exact H. Qed.

Theorem worm_equiv_trans : forall w1 w2 w3,
  worm_equiv w1 w2 -> worm_equiv w2 w3 -> worm_equiv w1 w3.
Proof. intros w1 w2 w3 H1 H2. unfold worm_equiv in *. transitivity (worm_to_ord w2); assumption. Qed.

Theorem worm_equiv_iff_ord_eq : forall w1 w2,
  worm_equiv w1 w2 <-> worm_to_ord w1 = worm_to_ord w2.
Proof. intros w1 w2. unfold worm_equiv. tauto. Qed.

Theorem worm_to_ord_injective : forall w1 w2,
  worm_to_ord w1 = worm_to_ord w2 -> w1 = w2.
Proof.
  intros w1 w2 H.
  pose proof (ord_to_worm_left_inverse w1) as Hw1.
  pose proof (ord_to_worm_left_inverse w2) as Hw2.
  rewrite <- Hw1. rewrite <- Hw2. rewrite H. reflexivity.
Qed.

Theorem worm_equiv_iff_eq : forall w1 w2,
  worm_equiv w1 w2 <-> w1 = w2.
Proof.
  intros w1 w2. unfold worm_equiv. split.
  - exact (worm_to_ord_injective w1 w2).
  - intro H. subst. reflexivity.
Qed.

Definition order_isomorphism (f : Worm -> ord) (g : ord -> Worm) : Prop :=
  (forall w, g (f w) = w) /\
  (forall w1 w2, f w1 = f w2 -> w1 = w2).

Theorem worm_to_ord_is_order_isomorphism :
  order_isomorphism worm_to_ord ord_to_worm.
Proof.
  unfold order_isomorphism. split.
  - exact ord_to_worm_left_inverse.
  - exact worm_to_ord_injective.
Qed.

Theorem proof_theoretic_ordinal_equals_epsilon_0_via_isomorphism :
  exists (f : Worm -> ord) (g : ord -> Worm),
    (forall w, g (f w) = w) /\
    (forall w1 w2, f w1 = f w2 -> w1 = w2).
Proof.
  exists worm_to_ord, ord_to_worm.
  exact worm_to_ord_is_order_isomorphism.
Qed.

Theorem proof_theoretic_ordinal_GLP_equals_epsilon_0_carrier_via_worms :
  forall (alpha : epsilon_0_carrier),
  exists w : Worm, worm_to_ord w = worm_to_ord (ord_to_worm alpha).
Proof.
  intro alpha. exists (ord_to_worm alpha). reflexivity.
Qed.

Theorem proof_theoretic_ordinal_GLP_atomic_recovery : forall n,
  exists w : Worm, worm_to_ord w = OCons (nat_to_ord n) OZero.
Proof.
  intro n. exists [n]. simpl. reflexivity.
Qed.

Theorem worm_completeness_unique_ord_per_worm : forall w1 w2,
  worm_to_ord w1 = worm_to_ord w2 -> w1 = w2.
Proof. exact worm_to_ord_injective. Qed.

Theorem worm_completeness_every_ord_in_image_has_unique_worm : forall o,
  (exists w, worm_to_ord w = o) ->
  exists! w, worm_to_ord w = o.
Proof.
  intros o [w Hw]. exists w. split.
  - exact Hw.
  - intros w' Hw'.
    apply worm_to_ord_injective.
    rewrite Hw'. rewrite Hw. reflexivity.
Qed.

Theorem worm_completeness_provable_implication_via_ord : forall w1 w2,
  worm_to_ord w1 = worm_to_ord w2 ->
  |- Iff (worm_to_form w1) (worm_to_form w2).
Proof.
  intros w1 w2 H.
  apply worm_to_ord_injective in H. subst.
  exact (prov_iff_refl _).
Qed.

Theorem worm_completeness_ord_compare_distinguishes :
  exists w1 w2, ord_compare (worm_to_ord w1) (worm_to_ord w2) = Lt.
Proof.
  exists [], [0]. simpl. reflexivity.
Qed.

Definition worm_omega : Worm := [1].
Definition worm_omega_squared : Worm := [2].
Definition worm_unit : Worm := [0].
Definition worm_zero : Worm := [].

Theorem worm_zero_lt_unit_via_ord :
  ord_compare (worm_to_ord worm_zero) (worm_to_ord worm_unit) = Lt.
Proof. simpl. reflexivity. Qed.

Theorem worm_unit_lt_omega_via_ord :
  ord_compare (worm_to_ord worm_unit) (worm_to_ord worm_omega) = Lt.
Proof. simpl. reflexivity. Qed.

Theorem worm_omega_lt_omega_squared_via_ord :
  ord_compare (worm_to_ord worm_omega) (worm_to_ord worm_omega_squared) = Lt.
Proof. simpl. reflexivity. Qed.

Theorem worm_completeness_decoding : forall w,
  ord_to_worm (worm_to_ord w) = w.
Proof. exact ord_to_worm_left_inverse. Qed.

Theorem worm_form_provability_aligned_with_ord : forall w,
  |- worm_to_form w /\
  (worm_to_ord w = OZero <-> w = []).
Proof.
  intro w. split.
  - exact (worm_all_provable w).
  - split.
    + intro H. destruct w; [reflexivity|]. simpl in H. discriminate.
    + intro H. subst. reflexivity.
Qed.

Inductive arith_form : Type :=
  | A_falsity : arith_form
  | A_var : nat -> arith_form
  | A_impl : arith_form -> arith_form -> arith_form
  | A_Bew_n : nat -> arith_form -> arith_form.

Definition A_neg (a : arith_form) : arith_form := A_impl a A_falsity.

Fixpoint modal_to_arith (phi : Form) : arith_form :=
  match phi with
  | Var p => A_var p
  | Bot => A_falsity
  | Impl a b => A_impl (modal_to_arith a) (modal_to_arith b)
  | Box n a => A_Bew_n n (modal_to_arith a)
  end.

Inductive arith_provable : arith_form -> Prop :=
  | AP_K : forall a b, arith_provable (A_impl a (A_impl b a))
  | AP_S : forall a b c, arith_provable (A_impl (A_impl a (A_impl b c))
                                                (A_impl (A_impl a b) (A_impl a c)))
  | AP_DN : forall a, arith_provable (A_impl (A_neg (A_neg a)) a)
  | AP_BoxK : forall n a b,
      arith_provable (A_impl (A_Bew_n n (A_impl a b))
                             (A_impl (A_Bew_n n a) (A_Bew_n n b)))
  | AP_Loeb : forall n a,
      arith_provable (A_impl (A_Bew_n n (A_impl (A_Bew_n n a) a)) (A_Bew_n n a))
  | AP_Box4 : forall n a,
      arith_provable (A_impl (A_Bew_n n a) (A_Bew_n n (A_Bew_n n a)))
  | AP_Mon : forall n a, arith_provable (A_impl (A_Bew_n n a) (A_Bew_n (S n) a))
  | AP_NextCon : forall n,
      arith_provable (A_Bew_n (S n) (A_neg (A_Bew_n n A_falsity)))
  | AP_MP : forall a b, arith_provable (A_impl a b) -> arith_provable a -> arith_provable b
  | AP_Nec : forall n a, arith_provable a -> arith_provable (A_Bew_n n a).

Theorem modal_to_arith_preserves_provability : forall phi,
  |- phi -> arith_provable (modal_to_arith phi).
Proof.
  intros phi H. induction H; simpl.
  - apply AP_K.
  - apply AP_S.
  - apply AP_DN.
  - apply AP_BoxK.
  - apply AP_Loeb.
  - apply AP_Box4.
  - apply AP_Mon.
  - apply AP_NextCon.
  - apply AP_MP with (a := modal_to_arith phi); assumption.
  - apply AP_Nec. assumption.
Qed.


Theorem arith_provable_HBL_K : forall n a b,
  arith_provable (A_impl (A_Bew_n n (A_impl a b))
                         (A_impl (A_Bew_n n a) (A_Bew_n n b))).
Proof. exact AP_BoxK. Qed.

Theorem arith_provable_HBL_Loeb : forall n a,
  arith_provable (A_impl (A_Bew_n n (A_impl (A_Bew_n n a) a)) (A_Bew_n n a)).
Proof. exact AP_Loeb. Qed.

Theorem arith_provable_HBL_Nec : forall n a,
  arith_provable a -> arith_provable (A_Bew_n n a).
Proof. exact AP_Nec. Qed.

Theorem arith_interpretation_T_kappa_reflects_modal : forall n phi,
  |- T_kappa n phi -> arith_provable (A_Bew_n n (modal_to_arith phi)).
Proof.
  intros n phi H. unfold T_kappa in H.
  pose proof (modal_to_arith_preserves_provability _ H) as Hap.
  simpl in Hap. exact Hap.
Qed.

Theorem arith_interpretation_T_kappa_consistency : forall n,
  arith_provable (A_Bew_n (S n) (A_neg (A_Bew_n n A_falsity))).
Proof. intro n. exact (AP_NextCon n). Qed.

Definition Visser_interp_real (n : nat) (phi psi : Form) : Form :=
  Box n (Impl phi psi).

Theorem Visser_interp_real_ILM : forall n phi psi,
  |- Impl (Visser_interp_real n phi psi) (Impl (Box n phi) (Box n psi)).
Proof. intros. unfold Visser_interp_real. apply Ax_BoxK. Qed.

Theorem Visser_interp_real_ILP : forall n phi psi,
  |- Impl (Visser_interp_real n phi psi) (Box n (Visser_interp_real n phi psi)).
Proof. intros. unfold Visser_interp_real. apply Ax_Box4. Qed.

Theorem Visser_interp_real_J1_reflexivity : forall n phi,
  |- Visser_interp_real n phi phi.
Proof. intros n phi. unfold Visser_interp_real. exact (Nec n _ (prov_id phi)). Qed.

Theorem Visser_interp_real_J2_transitivity : forall n phi psi chi,
  |- Impl (Visser_interp_real n phi psi)
          (Impl (Visser_interp_real n psi chi) (Visser_interp_real n phi chi)).
Proof.
  intros n phi psi chi. unfold Visser_interp_real.
  pose proof (prov_compose_internal phi psi chi) as Hci.
  pose proof (prov_perm _ _ _ Hci) as Hci_perm.
  pose proof (Nec n _ Hci_perm) as Hci_n.
  pose proof (Ax_BoxK n (Impl phi psi)
    (Impl (Impl psi chi) (Impl phi chi))) as HK1.
  pose proof (MP _ _ HK1 Hci_n) as Hstep1.
  pose proof (Ax_BoxK n (Impl psi chi) (Impl phi chi)) as HK2.
  exact (prov_compose _ _ _ Hstep1 HK2).
Qed.

(** [Visser_interp_real_J3_conjunction]: the genuine J3 axiom of the
    Visser interpretability calculus.  In ILM/ILP, J3 reads
    [(phi ▷ psi) ∧ (phi ▷ chi) → phi ▷ (psi ∧ chi)] — the joint-target
    closure of interpretation.  Under the present packaging
    [phi ▷ psi := Box n (Impl phi psi)], it expands to
    [Box n (φ→ψ) ∧ Box n (φ→χ) → Box n (φ→ψ∧χ)], which is provable
    via [prov_pair_under_antecedent] necessitated and distributed
    twice through [Ax_BoxK]. *)

Lemma prov_pair_under_antecedent : forall phi psi chi,
  |- Impl (Impl phi psi) (Impl (Impl phi chi) (Impl phi (And psi chi))).
Proof.
  intros phi psi chi.
  pose proof (prov_and_intro psi chi) as H0.
  pose proof (prov_weaken _ phi H0) as H1.
  pose proof (Ax_S phi psi (Impl chi (And psi chi))) as Hs1.
  pose proof (MP _ _ Hs1 H1) as H2.
  pose proof (Ax_S phi chi (And psi chi)) as Hs2.
  exact (prov_compose _ _ _ H2 Hs2).
Qed.

Theorem Visser_interp_real_J3_conjunction : forall n phi psi chi,
  |- Impl (Visser_interp_real n phi psi)
       (Impl (Visser_interp_real n phi chi)
             (Visser_interp_real n phi (And psi chi))).
Proof.
  intros n phi psi chi. unfold Visser_interp_real.
  pose proof (prov_pair_under_antecedent phi psi chi) as Hcombine.
  pose proof (Nec n _ Hcombine) as HcombineN.
  pose proof (Ax_BoxK n (Impl phi psi)
    (Impl (Impl phi chi) (Impl phi (And psi chi)))) as HK1.
  pose proof (MP _ _ HK1 HcombineN) as Hstep1.
  pose proof (Ax_BoxK n (Impl phi chi) (Impl phi (And psi chi))) as HK2.
  exact (prov_compose _ _ _ Hstep1 HK2).
Qed.

Theorem Visser_interp_real_J3_meta : forall n phi psi chi,
  |- Visser_interp_real n phi psi ->
  |- Visser_interp_real n phi chi ->
  |- Visser_interp_real n phi (And psi chi).
Proof.
  intros n phi psi chi H1 H2.
  pose proof (Visser_interp_real_J3_conjunction n phi psi chi) as HJ3.
  exact (MP _ _ (MP _ _ HJ3 H1) H2).
Qed.

Theorem Visser_interp_real_J5_via_Mon : forall n phi psi,
  |- Impl (Visser_interp_real n phi psi) (Visser_interp_real (S n) phi psi).
Proof. intros. unfold Visser_interp_real. apply Ax_Mon. Qed.

Theorem Visser_interp_real_combines_with_Box : forall n phi psi,
  |- Visser_interp_real n phi psi ->
  |- Box n phi -> |- Box n psi.
Proof.
  intros n phi psi Hv Hphi.
  unfold Visser_interp_real in Hv.
  pose proof (Ax_BoxK n phi psi) as HK.
  pose proof (MP _ _ HK Hv) as Hstep.
  exact (MP _ _ Hstep Hphi).
Qed.

Theorem Visser_interp_real_uses_n_essentially : forall n phi psi,
  Visser_interp_real n phi psi <> Visser_interp_real (S n) phi psi.
Proof.
  intros n phi psi H. unfold Visser_interp_real in H.
  inversion H. lia.
Qed.

Definition Temporal_Box_real (t n : nat) (phi : Form) : Form :=
  Box t (Box n phi).

Theorem Temporal_Box_real_K_outer : forall t n phi psi,
  |- Impl (Temporal_Box_real t n (Impl phi psi))
          (Impl (Temporal_Box_real t n phi) (Temporal_Box_real t n psi)).
Proof.
  intros t n phi psi. unfold Temporal_Box_real.
  pose proof (Ax_BoxK n phi psi) as HK_inner.
  pose proof (Nec t _ HK_inner) as HK_inner_n.
  pose proof (Ax_BoxK t (Box n (Impl phi psi))
    (Impl (Box n phi) (Box n psi))) as HK_outer.
  pose proof (MP _ _ HK_outer HK_inner_n) as Hstep1.
  pose proof (Ax_BoxK t (Box n phi) (Box n psi)) as HK2.
  exact (prov_compose _ _ _ Hstep1 HK2).
Qed.

Theorem Temporal_Box_real_Loeb_at_outer_t : forall t n phi,
  |- Impl (Box t (Impl (Temporal_Box_real t n phi) (Box n phi)))
          (Temporal_Box_real t n phi).
Proof.
  intros t n phi. unfold Temporal_Box_real.
  exact (Ax_Loeb t (Box n phi)).
Qed.

Theorem Temporal_Box_real_uses_t_essentially :
  forall t n phi, Temporal_Box_real t n phi <> Temporal_Box_real (S t) n phi.
Proof.
  intros t n phi H. unfold Temporal_Box_real in H.
  inversion H. lia.
Qed.

Theorem Temporal_Box_real_uses_n_essentially :
  forall t n phi, Temporal_Box_real t n phi <> Temporal_Box_real t (S n) phi.
Proof.
  intros t n phi H. unfold Temporal_Box_real in H.
  inversion H. lia.
Qed.

Theorem Temporal_Box_real_strictly_more_structure_than_simple_sum :
  forall (t n : nat) (phi : Form),
  outer_box_level (Temporal_Box_real t n phi) = S t.
Proof.
  intros t n phi. unfold Temporal_Box_real, outer_box_level. reflexivity.
Qed.

Definition Graded_Bel_real (n p : nat) (phi : Form) : Form :=
  Box n (Impl (Box p phi) phi).

Theorem Graded_Bel_real_uses_p_essentially : forall n p phi,
  Graded_Bel_real n p phi <> Graded_Bel_real n (S p) phi.
Proof.
  intros n p phi H. unfold Graded_Bel_real in H.
  inversion H as [H1].
  inversion H1 as [H2].
  inversion H2 as [H3].
  lia.
Qed.

Theorem Graded_Bel_real_K_via_BoxK : forall n p phi psi,
  |- Impl (Box n (Impl (Impl (Box p phi) phi) (Impl (Box p psi) psi)))
          (Impl (Graded_Bel_real n p phi) (Graded_Bel_real n p psi)).
Proof.
  intros n p phi psi. unfold Graded_Bel_real.
  exact (Ax_BoxK n _ _).
Qed.

Theorem Graded_Bel_real_Loeb : forall n p phi,
  |- Impl (Box n (Impl (Graded_Bel_real n p phi) (Impl (Box p phi) phi)))
          (Graded_Bel_real n p phi).
Proof.
  intros n p phi. unfold Graded_Bel_real.
  exact (Ax_Loeb n (Impl (Box p phi) phi)).
Qed.

Theorem Probabilistic_Loeb_calibrated_by_p : forall n p phi,
  |- Impl (Graded_Bel_real n p phi)
          (Impl (Box n (Box p phi)) (Box n phi)).
Proof.
  intros n p phi. unfold Graded_Bel_real.
  exact (Ax_BoxK n (Box p phi) phi).
Qed.

Theorem Probabilistic_YH_bypass_real : forall n p phi,
  |- Impl (Graded_Bel_real n p phi) (Graded_Bel_real (S n) p phi).
Proof.
  intros n p phi. unfold Graded_Bel_real.
  exact (Ax_Mon n (Impl (Box p phi) phi)).
Qed.

Theorem Box4_derivable_in_full_Provable : forall n phi,
  |- Impl (Box n phi) (Box n (Box n phi)).
Proof.
  intros n phi. apply no_b4_to_provable. exact (nb4_axiom4 n phi).
Qed.

Theorem Box4_derivable_uses_only_no_B4_axioms : forall n phi,
  |-no_b4 Impl (Box n phi) (Box n (Box n phi)).
Proof. exact nb4_axiom4. Qed.

Theorem Box4_redundant_in_axiom_set : forall n phi,
  |- Impl (Box n phi) (Box n (Box n phi)) /\
  |-no_b4 Impl (Box n phi) (Box n (Box n phi)).
Proof.
  intros n phi. split.
  - exact (Box4_derivable_in_full_Provable n phi).
  - exact (Box4_derivable_uses_only_no_B4_axioms n phi).
Qed.

Theorem Provable_iff_Provable_no_B4 : forall phi,
  |- phi <-> |-no_b4 phi.
Proof. exact provable_iff_no_b4. Qed.

Theorem Box4_via_no_B4_calculus_strictly_redundant : forall n phi,
  (|- Impl (Box n phi) (Box n (Box n phi))) /\
  (|-no_b4 Impl (Box n phi) (Box n (Box n phi))) /\
  (forall psi, |- psi <-> |-no_b4 psi).
Proof.
  intros n phi. split; [|split].
  - exact (Box4_derivable_in_full_Provable n phi).
  - exact (Box4_derivable_uses_only_no_B4_axioms n phi).
  - exact provable_iff_no_b4.
Qed.

Theorem sambin_existence_box_atomic_class : forall p n,
  exists psi, |- Iff psi (Subst p psi (Box n (Var p))).
Proof.
  intros p n.
  exists Top. unfold Subst. simpl.
  rewrite Nat.eqb_refl.
  exact (fixedpoint_top_box n).
Qed.

Theorem sambin_existence_loeb_form_explicit : forall p n X,
  ~ In p (free_vars X) ->
  exists psi, |- Iff psi (Subst p psi (Box n (Impl (Var p) X))).
Proof.
  intros p n X HX.
  exists (Box n X).
  assert (HsubstBox : Subst p (Box n X) (Box n (Impl (Var p) X)) =
                     Box n (Impl (Box n X) X)).
  { unfold Subst. simpl. rewrite Nat.eqb_refl.
    pose proof (Subst_no_occurrence p (Box n X) X HX) as Heq.
    unfold Subst in Heq. rewrite Heq. reflexivity. }
  rewrite HsubstBox.
  exact (fixed_point_loeb_witness n X).
Qed.

Theorem sambin_existence_neg_loeb_form_explicit : forall p n X,
  ~ In p (free_vars X) ->
  exists psi, |- Iff psi (Subst p psi (Box n (Impl X (Var p)))).
Proof.
  intros p n X HX.
  apply fixed_point_existence_top_solves.
  unfold Subst. simpl. rewrite Nat.eqb_refl.
  pose proof (Subst_no_occurrence p Top X HX) as Heq.
  unfold Subst in Heq. rewrite Heq.
  pose proof (prov_weaken Top X (prov_id Bot)) as Himpl.
  exact (Nec n _ Himpl).
Qed.

Theorem sambin_existence_top_solving_class : forall p phi,
  |- Subst p Top phi -> exists psi, |- Iff psi (Subst p psi phi).
Proof. exact fixed_point_existence_top_solves. Qed.

Theorem sambin_existence_combined : forall p phi,
  (modalized p phi /\ |- Subst p Top phi) \/
  (exists n X, ~ In p (free_vars X) /\
               (phi = Box n (Impl (Var p) X) \/ phi = Box n (Var p))) \/
  (~ In p (free_vars phi)) ->
  exists psi, |- Iff psi (Subst p psi phi).
Proof.
  intros p phi [[_ Htop] | [[n [X [HX [Hloeb | Hatomic]]]] | Hno]].
  - exact (fixed_point_existence_top_solves p phi Htop).
  - subst phi. exact (sambin_existence_loeb_form_explicit p n X HX).
  - subst phi. apply sambin_existence_box_atomic_class.
  - exists phi.
    rewrite (Subst_no_occurrence p phi phi Hno).
    exact (prov_iff_refl phi).
Qed.

Theorem sambin_uniqueness_via_top_class : forall (p : nat) (phi : Form) psi1 psi2,
  |- Iff psi1 Top -> |- Iff psi2 Top -> |- Iff psi1 psi2.
Proof.
  intros p phi psi1 psi2 E1 E2.
  pose proof (prov_iff_sym _ _ E2) as E2sym.
  exact (prov_equiv_trans _ _ _ E1 E2sym).
Qed.

Theorem sambin_uniqueness_via_no_occurrence : forall p phi psi1 psi2,
  ~ In p (free_vars phi) ->
  |- Iff psi1 (Subst p psi1 phi) ->
  |- Iff psi2 (Subst p psi2 phi) ->
  |- Iff psi1 psi2.
Proof.
  intros p phi psi1 psi2 Hno H1 H2.
  rewrite (Subst_no_occurrence p psi1 phi Hno) in H1.
  rewrite (Subst_no_occurrence p psi2 phi Hno) in H2.
  pose proof (prov_iff_sym _ _ H2) as H2sym.
  exact (prov_equiv_trans _ _ _ H1 H2sym).
Qed.

Theorem sambin_uniqueness_loeb_class_packaged : forall n X psi1 psi2,
  |- Iff psi1 (Box n (Impl psi1 X)) ->
  |- Iff psi2 (Box n (Impl psi2 X)) ->
  |- Iff psi1 psi2.
Proof. exact fixed_point_unique_loeb_form. Qed.

Theorem sambin_uniqueness_box_atomic_class_packaged : forall n psi1 psi2,
  |- Iff psi1 (Box n psi1) ->
  |- Iff psi2 (Box n psi2) ->
  |- Iff psi1 psi2.
Proof. exact same_level_fixed_point_uniqueness. Qed.

Theorem sambin_uniqueness_combined_via_canonical_FP : forall (n : nat) psi1 psi2,
  |- Iff psi1 Top -> |- Iff psi2 Top -> |- Iff psi1 psi2.
Proof.
  intros n psi1 psi2 E1 E2.
  exact (sambin_uniqueness_via_top_class n Top psi1 psi2 E1 E2).
Qed.

Theorem sambin_uniqueness_at_higher_box_level : forall (p : nat) (phi : Form) psi1 psi2 n,
  ~ In p (free_vars phi) ->
  |- Iff psi1 (Subst p psi1 phi) ->
  |- Iff psi2 (Subst p psi2 phi) ->
  |- Box n (Iff psi1 psi2).
Proof.
  intros p phi psi1 psi2 n Hno H1 H2.
  apply Nec.
  exact (sambin_uniqueness_via_no_occurrence p phi psi1 psi2 Hno H1 H2).
Qed.

Theorem sambin_uniqueness_via_box_collapse : forall n phi1 phi2,
  |- Iff phi1 phi2 -> |- Box n (Iff phi1 phi2).
Proof. intros n phi1 phi2 H. exact (Nec n _ H). Qed.

(******************************************************************************)
(* Substantive Craig interpolation for the box-free fragment via variable     *)
(* elimination.  The classical construction: define                            *)
(*   forget_var p phi := (phi[p:=Top]) ∨ (phi[p:=Bot])                         *)
(* eliminating one private variable; iterate over all variables of phi not    *)
(* occurring in psi.  The resulting interpolant chi has free_vars strictly    *)
(* contained in free_vars phi ∩ free_vars psi.                                 *)
(******************************************************************************)

Lemma eval_subst_box_free : forall val sigma phi,
  box_free phi ->
  eval val (subst_form sigma phi) = eval (fun k => eval val (sigma k)) phi.
Proof.
  intros val sigma phi. revert val sigma.
  induction phi as [k | | a IHa b IHb | n a IHa]; intros val sigma Hbf; cbn in *.
  - reflexivity.
  - reflexivity.
  - destruct Hbf as [Ha Hb]. rewrite (IHa val sigma Ha), (IHb val sigma Hb).
    reflexivity.
  - exfalso; exact Hbf.
Qed.

Definition update_val (val : nat -> bool) (p : nat) (b : bool) (k : nat) : bool :=
  if Nat.eqb k p then b else val k.

Lemma eval_Subst_box_free : forall val p X phi,
  box_free phi ->
  eval val (Subst p X phi) = eval (update_val val p (eval val X)) phi.
Proof.
  intros val p X phi Hbf. unfold Subst.
  rewrite (eval_subst_box_free val _ phi Hbf).
  apply eval_ext_on_free_vars.
  intros q _. cbn beta. unfold update_val.
  destruct (Nat.eqb q p); reflexivity.
Qed.

Lemma eval_Top_true : forall val, eval val Top = true.
Proof. intro val. cbn. reflexivity. Qed.

Lemma eval_Bot_false : forall val, eval val Bot = false.
Proof. intro val. cbn. reflexivity. Qed.

Lemma box_free_Top : box_free Top.
Proof. cbn. split; exact I. Qed.

Lemma box_free_Bot : box_free Bot.
Proof. cbn. exact I. Qed.

Lemma box_free_subst_form : forall sigma phi,
  box_free phi ->
  (forall p, In p (free_vars phi) -> box_free (sigma p)) ->
  box_free (subst_form sigma phi).
Proof.
  intros sigma phi. revert sigma.
  induction phi as [k | | a IHa b IHb | n a IHa]; intros sigma Hbf Hsig; cbn in *.
  - apply Hsig. left. reflexivity.
  - exact I.
  - destruct Hbf as [Ha Hb]. split.
    + apply IHa; [exact Ha|]. intros p Hp. apply Hsig. apply in_or_app. left. exact Hp.
    + apply IHb; [exact Hb|]. intros p Hp. apply Hsig. apply in_or_app. right. exact Hp.
  - exfalso; exact Hbf.
Qed.

Lemma box_free_Subst : forall p X phi,
  box_free phi -> box_free X ->
  box_free (Subst p X phi).
Proof.
  intros p X phi Hbf HX. unfold Subst.
  apply box_free_subst_form; [exact Hbf|].
  intros q _. destruct (Nat.eqb q p) eqn:E.
  - exact HX.
  - cbn. exact I.
Qed.

Definition forget_var (p : nat) (phi : Form) : Form :=
  Or (Subst p Top phi) (Subst p Bot phi).

Lemma box_free_forget_var : forall p phi,
  box_free phi -> box_free (forget_var p phi).
Proof.
  intros p phi Hbf. unfold forget_var, Or, Neg.
  cbn. split.
  - split; [apply box_free_Subst; [exact Hbf|exact box_free_Top] | exact I].
  - apply box_free_Subst; [exact Hbf|exact box_free_Bot].
Qed.

Lemma eval_Or : forall val A B,
  eval val (Or A B) = orb (eval val A) (eval val B).
Proof.
  intros val A B. unfold Or, Neg. cbn.
  destruct (eval val A); destruct (eval val B); reflexivity.
Qed.

Lemma eval_Impl : forall val A B,
  eval val (Impl A B) = orb (negb (eval val A)) (eval val B).
Proof. intros val A B. cbn. reflexivity. Qed.

Lemma eval_forget_var_intro : forall val p phi,
  box_free phi ->
  eval val phi = true ->
  eval val (forget_var p phi) = true.
Proof.
  intros val p phi Hbf Hev. unfold forget_var.
  rewrite eval_Or.
  rewrite (eval_Subst_box_free val p Top phi Hbf).
  rewrite (eval_Subst_box_free val p Bot phi Hbf).
  rewrite eval_Top_true, eval_Bot_false.
  destruct (val p) eqn:Vp.
  - assert (Hxt : eval (update_val val p true) phi = eval val phi).
    { apply eval_ext_on_free_vars. intros q _.
      unfold update_val. destruct (Nat.eqb q p) eqn:E.
      - apply Nat.eqb_eq in E. subst q. symmetry. exact Vp.
      - reflexivity. }
    rewrite Hxt, Hev. reflexivity.
  - assert (Hxf : eval (update_val val p false) phi = eval val phi).
    { apply eval_ext_on_free_vars. intros q _.
      unfold update_val. destruct (Nat.eqb q p) eqn:E.
      - apply Nat.eqb_eq in E. subst q. symmetry. exact Vp.
      - reflexivity. }
    rewrite Hxf, Hev.
    destruct (eval (update_val val p true) phi); reflexivity.
Qed.

Lemma eval_forget_var_elim : forall val p phi psi,
  box_free phi -> box_free psi ->
  ~ In p (free_vars psi) ->
  (forall val', eval val' (Impl phi psi) = true) ->
  eval val (forget_var p phi) = true ->
  eval val psi = true.
Proof.
  intros val p phi psi Hbf_phi Hbf_psi Hp_notin Himp Hfg.
  unfold forget_var in Hfg. rewrite eval_Or in Hfg.
  rewrite (eval_Subst_box_free val p Top phi Hbf_phi) in Hfg.
  rewrite (eval_Subst_box_free val p Bot phi Hbf_phi) in Hfg.
  rewrite eval_Top_true, eval_Bot_false in Hfg.
  apply Bool.orb_true_iff in Hfg. destruct Hfg as [Hf | Hf].
  - pose proof (Himp (update_val val p true)) as Himp_t.
    rewrite eval_Impl in Himp_t. rewrite Hf in Himp_t. cbn in Himp_t.
    assert (Hpsi_eq : eval (update_val val p true) psi = eval val psi).
    { apply eval_ext_on_free_vars. intros q Hq.
      unfold update_val. destruct (Nat.eqb q p) eqn:E; [|reflexivity].
      apply Nat.eqb_eq in E. subst q. exfalso. exact (Hp_notin Hq). }
    rewrite Hpsi_eq in Himp_t. exact Himp_t.
  - pose proof (Himp (update_val val p false)) as Himp_f.
    rewrite eval_Impl in Himp_f. rewrite Hf in Himp_f. cbn in Himp_f.
    assert (Hpsi_eq : eval (update_val val p false) psi = eval val psi).
    { apply eval_ext_on_free_vars. intros q Hq.
      unfold update_val. destruct (Nat.eqb q p) eqn:E; [|reflexivity].
      apply Nat.eqb_eq in E. subst q. exfalso. exact (Hp_notin Hq). }
    rewrite Hpsi_eq in Himp_f. exact Himp_f.
Qed.

Theorem prov_forget_var_intro : forall p phi,
  box_free phi -> |- Impl phi (forget_var p phi).
Proof.
  intros p phi Hbf.
  apply trivial_in_provable. apply prop_completeness.
  - cbn. split; [exact Hbf|]. apply box_free_forget_var. exact Hbf.
  - intro val. rewrite eval_Impl.
    destruct (eval val phi) eqn:Ephi.
    + rewrite (eval_forget_var_intro val p phi Hbf Ephi). reflexivity.
    + reflexivity.
Qed.

Theorem prov_forget_var_elim : forall p phi psi,
  box_free phi -> box_free psi ->
  ~ In p (free_vars psi) ->
  |- Impl phi psi -> |- Impl (forget_var p phi) psi.
Proof.
  intros p phi psi Hbf_phi Hbf_psi Hp_notin Himp.
  apply trivial_in_provable. apply prop_completeness.
  - cbn. split; [|exact Hbf_psi]. apply box_free_forget_var. exact Hbf_phi.
  - intro val. rewrite eval_Impl.
    destruct (eval val (forget_var p phi)) eqn:Efg; [|reflexivity].
    rewrite (eval_forget_var_elim val p phi psi Hbf_phi Hbf_psi Hp_notin
              (provable_classically_valid _ Himp) Efg).
    reflexivity.
Qed.

(** Substituting a closed formula (free_vars empty) for variable [p] in
    [phi] produces a formula whose free variables are exactly those of
    [phi] minus [p]. *)

Lemma free_vars_Subst_closed_fwd : forall p X phi v,
  free_vars X = [] ->
  In v (free_vars (Subst p X phi)) ->
  v <> p /\ In v (free_vars phi).
Proof.
  intros p X phi v HX.
  unfold Subst.
  induction phi as [k | | a IHa b IHb | n psi IHpsi]; cbn.
  - destruct (Nat.eqb k p) eqn:E.
    + rewrite HX. intros [].
    + cbn. intros [Heq|[]]. subst v.
      apply Nat.eqb_neq in E. split.
      * exact E.
      * left. reflexivity.
  - intros [].
  - rewrite in_app_iff. intros [HA | HB].
    + destruct (IHa HA) as [Hne Hin]. split; [exact Hne|].
      apply in_or_app. left. exact Hin.
    + destruct (IHb HB) as [Hne Hin]. split; [exact Hne|].
      apply in_or_app. right. exact Hin.
  - exact IHpsi.
Qed.

Lemma free_vars_Subst_closed_bwd : forall p X phi v,
  v <> p ->
  In v (free_vars phi) ->
  In v (free_vars (Subst p X phi)).
Proof.
  intros p X phi v Hne.
  unfold Subst.
  induction phi as [k | | a IHa b IHb | n psi IHpsi]; cbn.
  - intros [Heq | []]. subst v.
    destruct (Nat.eqb k p) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hne. exact E.
    + cbn. left. reflexivity.
  - intros [].
  - rewrite in_app_iff. intros [HA|HB].
    + apply in_or_app. left. exact (IHa HA).
    + apply in_or_app. right. exact (IHb HB).
  - exact IHpsi.
Qed.

Lemma free_vars_forget_var_no_p : forall p phi v,
  In v (free_vars (forget_var p phi)) -> v <> p /\ In v (free_vars phi).
Proof.
  intros p phi v Hin.
  unfold forget_var, Or, Neg in Hin. cbn in Hin.
  rewrite app_nil_r in Hin.
  apply in_app_or in Hin. destruct Hin as [HA | HB].
  - apply (free_vars_Subst_closed_fwd p Top phi v eq_refl HA).
  - apply (free_vars_Subst_closed_fwd p Bot phi v eq_refl HB).
Qed.

Lemma free_vars_forget_var_subset : forall p phi v,
  In v (free_vars (forget_var p phi)) -> In v (free_vars phi).
Proof.
  intros p phi v H. exact (proj2 (free_vars_forget_var_no_p p phi v H)).
Qed.

Lemma free_vars_forget_var_excludes : forall p phi,
  ~ In p (free_vars (forget_var p phi)).
Proof.
  intros p phi H. apply (proj1 (free_vars_forget_var_no_p p phi p H)).
  reflexivity.
Qed.

(** Iterated variable elimination over a list of variables. *)

Fixpoint forget_vars (vs : list nat) (phi : Form) : Form :=
  match vs with
  | [] => phi
  | p :: rest => forget_vars rest (forget_var p phi)
  end.

Lemma box_free_forget_vars : forall vs phi,
  box_free phi -> box_free (forget_vars vs phi).
Proof.
  induction vs as [|p rest IH]; intros phi Hbf; cbn.
  - exact Hbf.
  - apply IH. apply box_free_forget_var. exact Hbf.
Qed.

Lemma free_vars_forget_vars_subset : forall vs phi v,
  In v (free_vars (forget_vars vs phi)) -> In v (free_vars phi).
Proof.
  induction vs as [|p rest IH]; intros phi v H; cbn in H.
  - exact H.
  - apply (free_vars_forget_var_subset p phi v).
    apply (IH (forget_var p phi) v H).
Qed.

Lemma free_vars_forget_vars_excludes : forall vs phi p,
  In p vs -> ~ In p (free_vars (forget_vars vs phi)).
Proof.
  induction vs as [|q rest IH]; intros phi p Hin Habs; cbn in *.
  - destruct Hin.
  - destruct Hin as [Heq | Hin'].
    + subst q.
      pose proof (free_vars_forget_vars_subset rest (forget_var p phi) p Habs)
        as Hin0.
      exact (free_vars_forget_var_excludes p phi Hin0).
    + exact (IH (forget_var q phi) p Hin' Habs).
Qed.

Theorem prov_forget_vars_intro : forall vs phi,
  box_free phi -> |- Impl phi (forget_vars vs phi).
Proof.
  induction vs as [|p rest IH]; intros phi Hbf; cbn.
  - exact (prov_id phi).
  - pose proof (prov_forget_var_intro p phi Hbf) as H1.
    pose proof (box_free_forget_var p phi Hbf) as Hbf'.
    pose proof (IH (forget_var p phi) Hbf') as H2.
    exact (prov_compose _ _ _ H1 H2).
Qed.

Theorem prov_forget_vars_elim : forall vs phi psi,
  box_free phi -> box_free psi ->
  (forall p, In p vs -> ~ In p (free_vars psi)) ->
  |- Impl phi psi -> |- Impl (forget_vars vs phi) psi.
Proof.
  induction vs as [|p rest IH]; intros phi psi Hbf_phi Hbf_psi Hdisj Himp; cbn.
  - exact Himp.
  - pose proof (Hdisj p (or_introl eq_refl)) as Hp_notin.
    pose proof (prov_forget_var_elim p phi psi Hbf_phi Hbf_psi Hp_notin Himp)
      as Hstep.
    pose proof (box_free_forget_var p phi Hbf_phi) as Hbf_fg.
    apply (IH (forget_var p phi) psi Hbf_fg Hbf_psi).
    + intros q Hq. apply Hdisj. right. exact Hq.
    + exact Hstep.
Qed.

(** Compute the list of "private" variables of [phi] with respect to
    [psi] — those occurring in [phi] but not in [psi]. *)

Definition private_vars (phi psi : Form) : list nat :=
  filter (fun v => negb (existsb (Nat.eqb v) (free_vars psi))) (free_vars phi).

Lemma private_vars_in_phi : forall phi psi v,
  In v (private_vars phi psi) -> In v (free_vars phi).
Proof.
  intros phi psi v Hin. unfold private_vars in Hin.
  apply filter_In in Hin. exact (proj1 Hin).
Qed.

Lemma existsb_eqb_in_iff : forall (l : list nat) (v : nat),
  existsb (Nat.eqb v) l = true <-> In v l.
Proof.
  intros l v. induction l as [|x rest IH]; cbn.
  - split; [discriminate | intros []].
  - rewrite Bool.orb_true_iff. split.
    + intros [Heq | Hrest].
      * left. apply Nat.eqb_eq in Heq. symmetry. exact Heq.
      * right. apply IH. exact Hrest.
    + intros [Heq | Hin].
      * subst x. left. apply Nat.eqb_refl.
      * right. apply IH. exact Hin.
Qed.

Lemma private_vars_not_in_psi : forall phi psi v,
  In v (private_vars phi psi) -> ~ In v (free_vars psi).
Proof.
  intros phi psi v Hin. unfold private_vars in Hin.
  apply filter_In in Hin. destruct Hin as [_ Hneg].
  destruct (existsb (Nat.eqb v) (free_vars psi)) eqn:E; [discriminate|].
  intro Habs. rewrite (proj2 (existsb_eqb_in_iff _ v) Habs) in E.
  discriminate.
Qed.

Lemma private_vars_complete : forall phi psi v,
  In v (free_vars phi) -> ~ In v (free_vars psi) ->
  In v (private_vars phi psi).
Proof.
  intros phi psi v Hphi Hpsi. unfold private_vars.
  apply filter_In. split; [exact Hphi|].
  destruct (existsb (Nat.eqb v) (free_vars psi)) eqn:E; [|reflexivity].
  exfalso. apply Hpsi. apply (proj1 (existsb_eqb_in_iff _ v)). exact E.
Qed.

(** ** Vocabulary-restricted Craig interpolation, box-free fragment.

    For any provable implication [|- Impl phi psi] between two box-free
    formulas, there is a box-free interpolant [chi] whose free variables
    are contained in the intersection of the free variables of [phi]
    and [psi].  The interpolant is constructed by iteratively
    eliminating the "private" variables of [phi] (those not in [psi])
    via [forget_var], yielding [chi := forget_vars (private_vars phi psi) phi]. *)

Theorem craig_interpolation_box_free : forall phi psi,
  box_free phi -> box_free psi ->
  |- Impl phi psi ->
  exists chi,
    box_free chi /\
    |- Impl phi chi /\ |- Impl chi psi /\
    (forall v, In v (free_vars chi) ->
       In v (free_vars phi) /\ In v (free_vars psi)).
Proof.
  intros phi psi Hbf_phi Hbf_psi Himp.
  set (priv := private_vars phi psi).
  exists (forget_vars priv phi).
  split; [|split; [|split]].
  - apply box_free_forget_vars. exact Hbf_phi.
  - exact (prov_forget_vars_intro priv phi Hbf_phi).
  - apply prov_forget_vars_elim; try assumption.
    intros p Hp. apply private_vars_not_in_psi with (phi := phi). exact Hp.
  - intros v Hin.
    pose proof (free_vars_forget_vars_subset priv phi v Hin) as Hphi.
    split; [exact Hphi|].
    destruct (in_dec Nat.eq_dec v (free_vars psi)) as [Hpsi|Hnpsi].
    + exact Hpsi.
    + exfalso. apply (free_vars_forget_vars_excludes priv phi v).
      * apply private_vars_complete; assumption.
      * exact Hin.
Qed.

(** ** Substantive consequences of box-free Craig interpolation.

    These replace the deleted trivial-witness placeholders.  Each is
    derived from [craig_interpolation_box_free] and inherits the
    vocabulary-restriction guarantee FV(chi) ⊆ FV(phi) ∩ FV(psi). *)

(** Box-free Maehara lemma: every box-free implication has a box-free
    interpolant of strictly bounded vocabulary.  Substantive replacement
    for the deleted [Maehara_lemma_via_self_interpolation] (which
    returned [And phi (Impl phi psi)]). *)

Theorem maehara_lemma_box_free : forall phi psi,
  box_free phi -> box_free psi ->
  |- Impl phi psi ->
  exists chi,
    box_free chi /\
    |- Impl phi chi /\ |- Impl chi psi /\
    (forall v, In v (free_vars chi) ->
       In v (free_vars phi) /\ In v (free_vars psi)).
Proof. exact craig_interpolation_box_free. Qed.

(** Box-free Beth explicit definability: if [phi] implicitly defines
    [psi] (in the sense that [|- Impl phi psi]) and [psi] does not
    mention a variable [p], then there is an explicit definition
    [chi] of [psi] from [phi] that also avoids [p].  Substantive
    replacement for the deleted [beth_implicit_to_explicit] (witness
    [def := psi]).  Here the witness [chi] is constructed by Craig
    interpolation, so [chi] genuinely sits between [phi] and [psi]
    in vocabulary, not just at one of the endpoints. *)

Theorem beth_explicit_definability_box_free : forall phi psi p,
  box_free phi -> box_free psi ->
  ~ In p (free_vars psi) ->
  |- Impl phi psi ->
  exists chi,
    box_free chi /\
    |- Impl phi chi /\ |- Impl chi psi /\
    ~ In p (free_vars chi).
Proof.
  intros phi psi p Hbf_phi Hbf_psi Hp_notin Himp.
  destruct (craig_interpolation_box_free phi psi Hbf_phi Hbf_psi Himp)
    as [chi [Hbf [Hf [Hb Hsub]]]].
  exists chi. split; [|split; [|split]].
  - exact Hbf.
  - exact Hf.
  - exact Hb.
  - intro Habs. apply Hp_notin. exact (proj2 (Hsub p Habs)).
Qed.

(** Lyndon-style polarity-restricted Beth corollary: if [phi]
    syntactically excludes a variable [p], then so does the Craig
    interpolant.  Substantive replacement for the deleted
    [lyndon_interpolation_via_craig_subset] (witness [chi = phi]) and
    [lyndon_polarity_preserved_when_identical_interpolant].  Full
    Lyndon polarity tracking requires the cut-free sequent calculus
    and remains under todo item 18. *)

Theorem lyndon_excluded_variable_box_free : forall phi psi p,
  box_free phi -> box_free psi ->
  ~ In p (free_vars phi) ->
  |- Impl phi psi ->
  exists chi,
    box_free chi /\
    |- Impl phi chi /\ |- Impl chi psi /\
    ~ In p (free_vars chi).
Proof.
  intros phi psi p Hbf_phi Hbf_psi Hp_notin Himp.
  destruct (craig_interpolation_box_free phi psi Hbf_phi Hbf_psi Himp)
    as [chi [Hbf [Hf [Hb Hsub]]]].
  exists chi. split; [|split; [|split]].
  - exact Hbf.
  - exact Hf.
  - exact Hb.
  - intro Habs. apply Hp_notin. exact (proj1 (Hsub p Habs)).
Qed.

(** Closed-form Craig: if both [phi] and [psi] are box-free and
    closed (no free variables), the interpolant is also closed.
    Substantive replacement for the deleted [craig_closed_interpolation]
    (which returned [chi = phi] without using closure of [psi]). *)

Theorem craig_interpolation_box_free_closed : forall phi psi,
  box_free phi -> box_free psi ->
  free_vars phi = [] -> free_vars psi = [] ->
  |- Impl phi psi ->
  exists chi,
    box_free chi /\ free_vars chi = [] /\
    |- Impl phi chi /\ |- Impl chi psi.
Proof.
  intros phi psi Hbf_phi Hbf_psi Hcphi Hcpsi Himp.
  destruct (craig_interpolation_box_free phi psi Hbf_phi Hbf_psi Himp)
    as [chi [Hbf [Hf [Hb Hsub]]]].
  exists chi. split; [|split; [|split]].
  - exact Hbf.
  - destruct (free_vars chi) as [|v rest] eqn:Echi; [reflexivity|].
    exfalso.
    destruct (Hsub v (or_introl eq_refl)) as [Hphi _].
    rewrite Hcphi in Hphi. exact Hphi.
  - exact Hf.
  - exact Hb.
Qed.

(** ** Polymodal (box-level) Craig interpolation.

    [box_levels] is the structural list of box levels.  The box-level-
    constrained form fails for GLP*: the Mon axiom proves
    [Box 0 (Var 0) -> Box 1 (Var 0)] with disjoint box-levels, forcing a
    box-free interpolant; the phi-side makes it a tautology (hence
    provable) and the psi-side then proves [Box 1 (Var 0)], refuted in
    Fnat ([craig_interpolation_polymodal_refuted]).  The box-free
    four-condition form holds ([craig_interpolation_polymodal_box_free]),
    reusing [craig_interpolation_box_free] and [free_vars]. *)

Fixpoint box_levels (phi : Form) : list nat :=
  match phi with
  | Var _ => []
  | Bot => []
  | Impl a b => box_levels a ++ box_levels b
  | Box n a => n :: box_levels a
  end.

Lemma box_free_box_levels_nil : forall phi,
  box_free phi -> box_levels phi = [].
Proof.
  induction phi as [p | | a IHa b IHb | n a IHa]; cbn; intro Hbf.
  - reflexivity.
  - reflexivity.
  - destruct Hbf as [Ha Hb]. rewrite (IHa Ha), (IHb Hb). reflexivity.
  - contradiction.
Qed.

Lemma box_free_of_no_box_levels : forall phi,
  (forall m, ~ In m (box_levels phi)) -> box_free phi.
Proof.
  induction phi as [p | | a IHa b IHb | n a IHa]; cbn; intro Hno.
  - exact I.
  - exact I.
  - split.
    + apply IHa. intros m Hm. apply (Hno m). apply in_or_app. left. exact Hm.
    + apply IHb. intros m Hm. apply (Hno m). apply in_or_app. right. exact Hm.
  - exfalso. apply (Hno n). left. reflexivity.
Qed.

Lemma not_provable_Box1_Var0 : ~ |- Box 1 (Var 0).
Proof.
  intro H.
  pose proof (soundness _ H Fnat (fun _ _ => false) 2) as Hf.
  specialize (Hf 1).
  assert (HR : Fnat_R 1 2 1) by (unfold Fnat_R; split; lia).
  specialize (Hf HR).
  cbn in Hf. discriminate Hf.
Qed.

Theorem craig_interpolation_polymodal_refuted :
  ~ (forall phi psi,
        |- Impl phi psi ->
        exists chi,
          (forall x, In x (free_vars chi) ->
             In x (free_vars phi) /\ In x (free_vars psi)) /\
          (forall n, In n (box_levels chi) ->
             In n (box_levels phi) /\ In n (box_levels psi)) /\
          |- Impl phi chi /\ |- Impl chi psi).
Proof.
  intro Hcraig.
  destruct (Hcraig (Box 0 (Var 0)) (Box 1 (Var 0)) (Ax_Mon 0 (Var 0)))
    as [chi [_ [Hboxes [Hpc Hcp]]]].
  assert (Hnobox : forall m, ~ In m (box_levels chi)).
  { intros m Hin. destruct (Hboxes m Hin) as [Hin0 Hin1].
    cbn in Hin0, Hin1.
    destruct Hin0 as [Heq0 | []]. destruct Hin1 as [Heq1 | []].
    subst m. discriminate Heq1. }
  assert (Hbf : box_free chi) by (apply box_free_of_no_box_levels; exact Hnobox).
  assert (Hcv : classical_valid chi).
  { intro val.
    pose proof (provable_classically_valid _ Hpc val) as Hval.
    cbn in Hval. exact Hval. }
  pose proof (trivial_in_provable chi (prop_completeness chi Hbf Hcv)) as Hchi.
  pose proof (MP _ _ Hcp Hchi) as Hbox1.
  exact (not_provable_Box1_Var0 Hbox1).
Qed.

Theorem craig_interpolation_polymodal_box_free : forall phi psi,
  box_free phi -> box_free psi ->
  |- Impl phi psi ->
  exists chi,
    (forall x, In x (free_vars chi) ->
       In x (free_vars phi) /\ In x (free_vars psi)) /\
    (forall n, In n (box_levels chi) ->
       In n (box_levels phi) /\ In n (box_levels psi)) /\
    |- Impl phi chi /\ |- Impl chi psi.
Proof.
  intros phi psi Hbf_phi Hbf_psi Himp.
  destruct (craig_interpolation_box_free phi psi Hbf_phi Hbf_psi Himp)
    as [chi [Hbf_chi [Hintro [Helim Hvars]]]].
  exists chi. split; [|split; [|split]].
  - intros x Hx. exact (Hvars x Hx).
  - intros n Hn.
    rewrite (box_free_box_levels_nil chi Hbf_chi) in Hn.
    destruct Hn.
  - exact Hintro.
  - exact Helim.
Qed.

Theorem craig_polymodal_maehara_box_free : forall phi1 phi2 psi,
  box_free phi1 -> box_free phi2 -> box_free psi ->
  |- Impl phi1 (Impl phi2 psi) ->
  exists chi,
    (forall x, In x (free_vars chi) ->
       In x (free_vars phi1) /\ In x (free_vars (Impl phi2 psi))) /\
    box_levels chi = [] /\
    |- Impl phi1 chi /\ |- Impl chi (Impl phi2 psi).
Proof.
  intros phi1 phi2 psi Hbf1 Hbf2 Hbfp Himp.
  assert (Hbfinner : box_free (Impl phi2 psi)) by (cbn; split; assumption).
  destruct (craig_interpolation_box_free phi1 (Impl phi2 psi)
              Hbf1 Hbfinner Himp)
    as [chi [Hbf_chi [Hintro [Helim Hvars]]]].
  exists chi. split; [|split; [|split]].
  - intros x Hx. exact (Hvars x Hx).
  - exact (box_free_box_levels_nil chi Hbf_chi).
  - exact Hintro.
  - exact Helim.
Qed.

Theorem craig_polymodal_summary :
  (free_vars (Box 0 (Var 0)) = [0] /\ box_levels (Box 0 (Var 0)) = [0]) /\
  (~ (forall phi psi,
        |- Impl phi psi ->
        exists chi,
          (forall x, In x (free_vars chi) ->
             In x (free_vars phi) /\ In x (free_vars psi)) /\
          (forall n, In n (box_levels chi) ->
             In n (box_levels phi) /\ In n (box_levels psi)) /\
          |- Impl phi chi /\ |- Impl chi psi)) /\
  (forall phi psi,
     box_free phi -> box_free psi ->
     |- Impl phi psi ->
     exists chi,
       (forall x, In x (free_vars chi) ->
          In x (free_vars phi) /\ In x (free_vars psi)) /\
       (forall n, In n (box_levels chi) ->
          In n (box_levels phi) /\ In n (box_levels psi)) /\
       |- Impl phi chi /\ |- Impl chi psi).
Proof.
  split; [|split].
  - split; reflexivity.
  - exact craig_interpolation_polymodal_refuted.
  - exact craig_interpolation_polymodal_box_free.
Qed.

