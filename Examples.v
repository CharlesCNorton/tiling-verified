From Tiling Require Import Tiling.

Example example_1_godel_second_at_level_zero :
  ~ |- Box 0 (Neg (Box 0 Bot)).
Proof. exact (Godel_sentence_independent_at_Tn 0). Qed.

Example example_1_consistency_provable_at_level_one :
  |- Box 1 (Neg (Box 0 Bot)).
Proof. exact (Ax_NextCon 0). Qed.

Example example_2_loeb_at_level_two :
  forall phi, |- Impl (Box 2 (Impl (Box 2 phi) phi)) (Box 2 phi).
Proof. intros phi. exact (Ax_Loeb 2 phi). Qed.

Example example_3_fairbot_provable :
  forall n, |- genuine_FairBot n Cooperate_action.
Proof. exact genuine_FairBot_provable_when_opp_eq_cooperate. Qed.

Example example_3_prudentbot_provable :
  forall n, |- genuine_PrudentBot n Cooperate_action.
Proof. exact genuine_PrudentBot_provable_when_opp_eq_cooperate. Qed.

Example example_4_strict_separation : forall n,
  exists phi,
    |- Box (S n) phi /\
    ~ |- Box n phi.
Proof. exact strict_extension_at_each_level. Qed.

Example example_5_meta_consistency : ~ |- Bot.
Proof. exact meta_consistency_system. Qed.

Example example_6_box_atomic_fixedpoint : forall n,
  |- Iff Top (Box n Top).
Proof. exact fixedpoint_top_box. Qed.

Example example_7_kalmar_completeness : forall phi,
  box_free phi -> classical_valid phi -> |- phi.
Proof. exact Solovay_first_completeness_via_classical_valid. Qed.
