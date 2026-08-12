# tiling-verified todo

1. Unify `Provable` and `Provable_GLP` into a single calculus in which
   the Japaridze scheme is derivable, and carry every downstream theorem
   through the unification.

2. Replace the surrogate predicates `Bew_PA`, `Bew_n`, and `Bew_arith`
   with definitions grounded in the `FOProvSentence`/`FOsat` layer, so
   "arithmetic" and "Σ₁" describe actual arithmetic objects.

3. Derive the Hilbert-Bernays-Löb conditions as theorems of `FOProvesTn`
   about its own `FOProvSentence`, eliminating `FOAx_D2`, `FOAx_D3`, and
   `FOAx_DMon` as axioms; prove `third_HBL_derived_summary`.

4. Prove internal Σ₁-completeness against `FOsat` and provable
   Σ₁-completeness (`provable_sigma1_completeness : forall sigma,
   is_sigma1 sigma -> Prov_T (Impl sigma (prov_sentence sigma))`) derived
   inside `T`, proved against satisfaction rather than imported or
   discharged by a calculus rule, and reduce the primitive
   `FOProvesTn_Loeb` rule and internal necessitation to derived theorems.

5. Restate and prove the Solovay completeness theorems with
   interpretations into the first-order arithmetic layer, replacing the
   `Form -> Form` level-collapse notion of "arithmetic interpretation."

6. Establish the reflection/consistency-strength bridge
   `Prov_{T_{n+1}} <-> Prov_{T_n + RFN(T_n)}` so the tower matches
   Beklemishev's characterization, derived rather than posited and
   carrying the RFN/Con content; prove `reflection_strength_summary`.

7. Reprove every downstream consumer (Π₂ conservativity, the Japaridze
   tree, the tiling chain, the agent modules) against
   `FOProvesTn`/`FOsat`, witnessed by per-module `Print Assumptions`;
   prove `arithmetic_layer_coherence_summary`.

8. Add a sequent presentation with cut elimination, prove equivalence
   with the Hilbert system in both directions, and derive the subformula
   property where it holds; prove `sequent_cut_elim_summary`.

9. Develop neighborhood or scattered-topological (Ignatiev-style)
   semantics `forces_topo` with frame conditions, and prove
   `soundness_topo` and full completeness
   (`topo_completeness : topo_valid phi -> |- phi`) for the whole
   language beyond the box-free fragment, with validity over the frame
   class rather than a single fixed frame; prove
   `topo_completeness_summary`.

10. Construct the total decision procedure
    `glp_decide_total : forall phi, sumbool (|- phi) (~ |- phi)` with a
    computable Ignatiev-model bound or a terminating cut-free search and
    a full correctness proof `glp_decide_total_correct`, without
    `excluded_middle_informative` and without restriction to the
    box-tower-over-box-free fragment.

11. Formalize and prove Vardanyan's theorem that the quantified
    provability logic of PA is Π⁰₂-complete, stated over `FOProvesTn`
    and `FOFormula`; prove `quantified_boundary_summary`.

12. Construct the two-argument Veblen function
    `veblen : ord -> ord -> ord` with its standard fixed-point clauses,
    define Γ₀ as the least strongly critical ordinal, prove it the
    supremum of the iterated Veblen tower, derive its well-foundedness
    from the construction, and re-establish
    `GLP_proof_height_below_Gamma_0` against it; prove
    `veblen_Gamma_0_summary`.

13. Replace `Veblen_eps0_ordinal` and the two-case `Veblen_phi_function`
    with objects satisfying the defining equations of the ordinals they
    are named after.

14. State and prove a strict bound (`ord_compare ... = Lt`) in
    `proof_theoretic_ordinal_summary`, replacing trichotomy disjunctions
    that hold for any comparison value.

15. Prove the proof-height rank invariant across all derivations of a
    given theorem, or introduce a Type-level `ProvableT` with
    `proof_height : forall phi, ProvableT phi -> vord` and
    `ProvableT_iff : ProvableT phi <-> inhabited (Provable_term phi)`,
    so the ordinal assignment genuinely ranks `|-` itself rather than
    individual `Provable_term` witnesses; prove
    `proof_height_on_derivations_summary`.

16. Prove the worm/closed-fragment order type is exactly ε₀
    (`worm_order_type_eps0`) and connect the proof-height bound to it
    tightly (`proof_height_tight`); prove
    `ordinal_analysis_tight_summary`.

17. Replace `ec_hom_eq := fun _ _ => True` in the Stone equivalence with
    a genuine equivalence on derivations modulo conversion and cut, and
    reprove `Stone_eta_natural`, `Stone_epsilon_natural`,
    `Stone_triangle_F`, and `Stone_triangle_G` against it; prove
    `stone_proof_relevant_summary`.

18. Quotient the Magari-freeness category's hom-sets so `LT_GLP_free`
    uniqueness is a contractibility statement inside the category,
    without functional extensionality or proof irrelevance; prove
    `magari_strict_free_summary`.

19. Equip the inert `LambdaBox` combinators (`tS`, `tBoxK`, `tLoeb`,
    `tBox4`, `tMon`, `tNextCon`, `tLoebFix`) with contraction rules,
    including S duplication and a guarded `tLoebFix` unfolding, prove
    strong normalization by reducibility candidates against the full
    reduction relation, and reprove `extract_realizer_reduces`; prove
    `lambda_box_SN_summary`.

20. Define `Vingean_reflection_at` as a genuine reflection principle
    whose statement quantifies over the successor level's proofs rather
    than aliasing `Box (S n)`, and reprove the reflection summary
    against it.

21. Formalize and prove Critch's parametric bounded Löb theorem itself,
    with proof-length accounting and the polynomial-overhead argument.

22. Prove single-level reflective trust
    (`single_level_self_trust : exists T, Prov_T (Con T) ->
    Prov_T (trusts T T)`) against the arithmetic layer, or the
    machine-checked obstruction `single_level_trust_blocked` derived
    from Löb, with the Critch parametric bounded variant as the
    strongest true form; prove `reflective_trust_resolution_summary`.

23. Reformulate `goal_preservation_tiling` so `default_action` and the
    successor condition carry content, making the statement falsifiable
    rather than tautological.

24. Prove the Löbian handshake proper: derive mutual cooperation for the
    diagonal fixed points of FairBot vs. FairBot via Löb and Sambin
    uniqueness, quantifying over all solutions.

25. Extend the bot-vs-bot results beyond `opp = Cooperate_action` to the
    standard opponent matrix, and repair
    `FairBot_two_bots_mutual_cooperation` so its conclusion uses its
    hypotheses; prove `program_equilibrium_summary`.

26. Build the single finite bounded-budget agent and prove
    `bounded_agent_tiling : forall budget,
    goal_preserved (rewrite_step agent budget)` across its rewrite
    steps, replacing tower-indexed trust; prove `bounded_agent_summary`.

27. Wire the extracted lambda-box realizers to `AgentRecord` decisions
    and prove `extracted_fairbot_correct :
    run (extract fairbot_proof) opp = fairbot_action opp`; prove
    `agent_extraction_summary`.

28. Remove padding conjuncts such as `solovay_function size R 0 = 0`
    from summary bundles, keeping only conjuncts with independent
    mathematical content.

29. Carve the decidable and syntactic results (box-free decidability,
    the Hilbert toolkit, proof-term reductions, `glp_dec_b`) into
    modules importing neither `Classical` nor `ClassicalEpsilon`,
    verified by `Print Assumptions`, confining the classical axioms to
    the Lindenbaum/completeness parts; prove
    `constructive_core_summary`.

30. Attach every completeness, conservativity, and duality headline to
    the exact named logic it holds for (GL, GLP, the proven subsystem,
    or GLS), with a machine-checked `logic_identification_summary`.

31. Prove, at full strength, the genuine theorems whose names invoke
    Solovay, Feferman-Schütte, Tarski, Friedman, Critch, and Vingean
    reflection, so every named result's body matches its claim.
