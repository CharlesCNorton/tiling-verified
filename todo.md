# tiling-verified todo

1. Strengthen `Pi2_conservativity_via_propositional_inversion` to cover
    depth-1 formulas. Construct a `Provable_no_NC`-style frame
    validating `Neg (Box k phi)` at level `S n` and refuting it at
    level `n` for every `k < n` with `phi` box-free, and use it to
    prove `Pi2_depth1_conservativity : forall n k phi, k < n ->
    box_free phi -> Bew (S n) (Neg (Box k phi)) -> Bew n (Neg (Box k
    phi))`.
2. Replace `relative_consistency_via_meta` with
    `Con_T0_implies_Con_Tn : ~ Bew 0 Bot -> forall n, ~ Bew n Bot`.
    Define `untower_translation : forall n phi, Bew n phi ->
    Bew 0 (translate phi)` by induction on Bew-derivations,
    replacing each `TAx_NextCon` application with a `Bew 0`
    derivation under the hypothesis `~ Bew 0 Bot`. Prove the lemma at
    `phi = Bot` to obtain `Con_T0_implies_Con_Tn`.
3. Replace `Solovay_first_completeness_box_free_fragment` with the
    full Solovay theorem for arbitrary `phi`. Define
    `arith_interp : Form -> FOFormula` that maps `Box k phi` to a
    `FOProvesTn k` claim under Gödel encoding, prove
    `arith_interp_soundness : forall phi, |- phi -> forall I,
    FOProvesTn 0 (I (arith_interp phi))`, and prove
    `Solovay_first_full : forall phi, (forall I, FOProvesTn 0
    (I (arith_interp phi))) -> |- phi` without collapsing the
    universal premise to identity.
4. Replace `Solovay_second_completeness_with_reflection_axiom` with
    the full Solovay-S theorem for arbitrary `phi`. Construct
    `arith_interp_S : Form -> FOFormula` with the T-schema for true
    sentences, and prove `Solovay_second_full : forall phi, (forall
    I, FOProvesTn 0 (I (arith_interp_S phi))) -> Provable_S phi`.
5. Replace `Japaridze_arithmetic_completeness_general` with a
    Solovay-tree construction. Define `Solovay_tree : Form -> nat ->
    FOFormula` returning the Solovay-tree node at each level, prove
    the modal-image theorem
    `Solovay_tree_validates_iff_GLP : forall phi, (forall I,
    is_arithmetic_interpretation I -> FOProvesTn 0 (I phi))
    <-> Provable_full_GLP phi`, and use it to discharge
    `Japaridze_full` without instantiating at the identity
    interpretation.
6. Replace the hardcoded `Critch_polynomial_bound k := k * k + k + 1`
    with the bound extracted from proof-term length. Define
    `proof_term_length : proof_term -> nat`, prove
    `proof_term_length_polynomial : exists p : nat -> nat,
    polynomial p /\ forall phi (pt : proof_term phi),
    proof_term_length pt <= p (rank phi)`, and replace the constant
    with the extracted polynomial inside `Critch_bounded_provability`.
7. Replace the syntactic-only `QGLP_formula` definitions with a
    Tarski semantics. Define
    `QGLP_sat : forall (D : Type), (nat -> D) ->
    QGLP_formula -> Prop` recursively over `QGLP_formula`, define
    `QGLP_provable : QGLP_formula -> Prop` with the standard
    quantifier rules, and prove
    `QGLP_soundness : forall q, QGLP_provable q ->
    forall D assign, QGLP_sat D assign q`.
8. Replace `Bel_p p level := Box level` with a genuine graded
    modality. Use `Coq.QArith.QArith_base.Q` as the rational carrier,
    define `Bel_p (p : Q) (level : nat) (phi : Form) : Form` as a
    syntactically distinct predicate (a record carrying `p` and
    `Box level phi`), and prove `graded_loeb : forall p, (0 < p)%Q ->
    forall level phi, |- Impl (Bel_p p level (Impl (Bel_p p level
    phi) phi)) (Bel_p p level phi)` whose proof references `p`
    non-trivially.
9. Replace `transfinite_box level phi := Box (ord_to_nat_approx
    level) phi` with a genuinely transfinite calculus. Define
    `Inductive Provable_transfinite : ord -> Form -> Prop` indexed by
    `ord`, prove cumulativity `forall a b phi, ord_lt a b ->
    Provable_transfinite a phi -> Provable_transfinite b phi` by
    `wf_vord` induction, and prove
    `transfinite_collapse_at_nat : forall n phi, Provable_transfinite
    (nat_to_ord n) phi <-> |- Box n phi`.
10. Replace `Reverse_math_strength` and
    `primitive_recursive_arithmetic_strength` with an explicit
    RM-hierarchy. Define `Inductive RM_subsystem : Type := RCA_0 |
    WKL_0 | ACA_0 | ATR_0 | Pi11_CA_0`, define `RM_provable :
    RM_subsystem -> Form -> Prop`, and for each major theorem in
    the development prove `<theorem>_RM_strength : RM_provable
    <minimal_subsystem> <theorem>`. At minimum: `meta_consistency_system`
    in RCA_0, `Bew_PA_HBL_summary` in WKL_0,
    `polymodal_sambin_existence` in ACA_0,
    `proof_theoretic_ordinal_summary` in ATR_0.
11. Replace the `From Tiling Require Export Tiling.` content of
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
12. Replace each `*_summary` theorem that is a conjunction of
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
