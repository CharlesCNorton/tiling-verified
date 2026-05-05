# tiling-verified todo

1. Replace `Japaridze_arithmetic_completeness_general` with a
    Solovay-tree construction. Define `Solovay_tree : Form -> nat ->
    FOFormula` returning the Solovay-tree node at each level, prove
    the modal-image theorem
    `Solovay_tree_validates_iff_GLP : forall phi, (forall I,
    is_arithmetic_interpretation I -> FOProvesTn 0 (I phi))
    <-> Provable_full_GLP phi`, and use it to discharge
    `Japaridze_full` without instantiating at the identity
    interpretation.
2. Replace the `From Tiling Require Export Tiling.` content of
    `Calculus.v`, `Hilbert.v`, `Kripke.v`, `FixedPoints.v`, `Bew.v`,
    `ProofTerms.v`, `Worms.v`, and `Agents.v` with a physical
    partition of `Tiling.v`'s body. Move calculus inductives plus
    axioms to `Calculus.v`; propositional metatheory to `Hilbert.v`;
    `Frame`, `forces`, `eval`, soundness to `Kripke.v`; Sambin
    existence and uniqueness to `FixedPoints.v`; `Bew_n` plus HBL to
    `Bew.v`; proof-term reduction to `ProofTerms.v`; Worm theory to
    `Worms.v`; `AgentRecord` plus FairBot/PrudentBot to `Agents.v`.
    Update `_CoqProject` with the dependency order. `Tiling.v`
    becomes a meta-file containing only `From Tiling Require Export
    Calculus Hilbert Kripke FixedPoints Bew ProofTerms Worms Agents.`
3. Replace each `*_summary` theorem that is a conjunction of
    already-named theorems (`Pi1_conservativity_summary`,
    `Pi2_conservativity_summary`, `Bew_axiomatic_summary`,
    `realisation_full_soundness`, `Bew_satisfies_GLP_axioms_summary`,
    `Solovay_first_completeness_summary`,
    `Solovay_second_completeness_with_reflection_axiom`,
    `Japaridze_arithmetic_completeness_summary`,
    `cooperate_action_summary`,
    `FairBot_vs_PrudentBot_concrete_summary`,
    `FairBot_vs_DefectBot_defection_summary`,
    `PrudentBot_dominance_summary`,
    `quantitative_Loeb_obstacle_summary`, `Visser_J5_full_summary`,
    `Visser_J5_full_derivation_summary`,
    `extension_summary`, `non_trivial_action_summary`,
    `Vingean_reflection_summary`,
    `no_panic_reflective_trust_summary`,
    `T_kappa_agent_correspondence_summary`,
    `successor_inspector_summary`, `concrete_failure_case_summary`,
    `Pudlak_speedup_summary`, `agent_record_summary`,
    `concrete_bounded_agent_summary`,
    `Critch_bounded_provability_summary`,
    `proof_theoretic_ordinal_summary`,
    `probabilistic_logic_summary`,
    `probabilistic_decision_agent_summary`,
    `neighborhood_semantics_summary`, `T_n_ordinal_summary`,
    `tower_bypass_summary`, `Bew_n_HBL_summary`,
    `Bew_PA_HBL_summary`,
    `Bew_proof_level_strict_separation_summary`,
    `relative_consistency_summary`, `T_axiom_cumulativity_strict`,
    `T_n_extension_proves_internal_Con`, `Tr_partial_hierarchy_summary`,
    `Friedman_Sheard_axiomatisation_summary`,
    `Friedman_negative_translation_summary`,
    `Tarski_undefinability_box_indexed_summary`,
    `strong_undefinability_summary`,
    `internal_diagonal_summary`,
    `Godel_sentence_summary`,
    `categorical_semantics_summary`) with a non-trivially-additive
    packaging that establishes a property not derivable from the
    conjunction of its parts (e.g., a quotient, an isomorphism, or
    a uniformity statement). For each summary, prove a strengthened
    form `<name>_strengthened` that adds at least one non-redundant
    conjunct relating the bundled theorems.
