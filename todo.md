# tiling-verified todo

1. Prove provable Σ₁-completeness: for every Σ₁ formula `sigma` with
   free variables `x1 … xm`, `T_0` derives `sigma` implies the level-`k`
   provability formula applied to the code of `sigma` with the numerals
   of `x1 … xm` substituted, through a formalized numeral-substitution
   function, and for Σ₁ sentences `FOProvesTn 0 (FOImplF sigma
   (FOProvSentence k sigma))`.  Derive the formalized third condition
   `FOProvesTn 0 (FOImplF (FOProvSentence k A) (FOProvSentence k
   (FOProvSentence k A)))`; prove `provable_sigma1_completeness`.

2. Formalize the diagonal lemma for `FOFormula` and derive Löb's
   theorem at every level together with its internal form
   `FOProvesTn 0 (FOImplF (FOProvSentence k (FOImplF (FOProvSentence k
   A) A)) (FOProvSentence k A))` and formalized monotonicity
   `FOProvesTn 0 (FOImplF (FOProvSentence k A) (FOProvSentence k' A))`
   for `k <= k'`.  Then remove the primitive `FOProvesTn_Loeb` rule and
   the `FOAx_D2`, `FOAx_D3` and `FOAx_DMon` axioms with their checker
   justifications, so that `T_0` is PA and `T_(n+1)` is `T_n` plus local
   reflection for `T_n`, and re-establish representability, soundness,
   cumulativity and `FOGodel2` for the reduced tower; prove
   `third_HBL_derived_summary`.

3. Replace the surrogate predicates `Bew_PA`, `Bew_n` and `Bew_arith` by
   `FOProvSentence` applied to `FOembed` images, or delete them, and
   carry every theorem that mentions them onto the arithmetic layer, so
   that "arithmetic" and "Σ₁" in their statements describe arithmetic
   objects.

4. Prove arithmetic soundness of GLP* for the tower:
   `forall phi, |- phi -> forall nu, FOProvesTn 0 (FOembed nu phi)`,
   the modal axioms going through `FOHBL2_internal` and items 1–2 and
   necessitation through provable Σ₁-completeness; prove
   `arithmetic_soundness_summary`.

5. Compare the strength of the levels: with the provability predicate
   of finite extensions of a level formalized, prove that `T_(n+1)`
   derives `Con(T_n + Con(T_n))` and that `T_n + Con(T_n)` does not, so
   each level strictly exceeds the consistency extension of the level
   below; prove `reflection_strength_summary`.

6. Prove the de Jongh–Sambin fixed-point theorem for `Provable_GL`:
   every formula modalised in `p` has an explicit fixed point `psi`,
   free of `p`, with `Provable_GL (Iff psi (Subst p psi phi))`.  For
   GLP*, prove the same theorem for single formulas and for
   simultaneous systems across levels, or exhibit a formula modalised
   in `p` with no fixed point.  `sambin_uniqueness_modalised` supplies
   uniqueness; prove `de_jongh_sambin_summary`.

7. Prove completeness for the whole language.  For GL and GLP*: Kripke
   completeness with the finite model property, GLP* over the
   conditions of `Frame`.  For the tower's candidate logic, GLP* plus
   `Box (S n) (Impl (Box n phi) phi)`: prove that every Kripke frame
   validating it has empty `R (S n)`, and prove it complete for a
   neighbourhood or scattered-topological semantics.  For GLP
   (`Provable_GLP`): completeness for Ignatiev's universal model and
   for GLP-spaces.  Prove `modal_completeness_summary`.

8. Give sequent calculi for GL and GLP* with cut elimination, prove
   each equivalent to its Hilbert system in both directions, and derive
   the subformula property where it holds; prove
   `sequent_cut_elim_summary`.

9. Construct the total decision procedure
   `glp_decide_total : forall phi, sumbool (|- phi) (~ |- phi)` from
   the finite model property or a terminating cut-free proof search,
   with a full correctness proof `glp_decide_total_correct`, without
   `excluded_middle_informative` and without restriction to a
   fragment.

10. State the freeness of `LT_GLP` among GLP* algebras as a universal
    property whose homomorphisms are compared by pointwise setoid
    equality, so that existence and uniqueness of the induced
    homomorphism hold without functional extensionality or proof
    irrelevance; prove `magari_strict_free_summary`.

11. Prove Jónsson–Tarski duality for GLP* algebras: the category of
    GLP* algebras with homomorphisms is dually equivalent to the
    category of descriptive general frames validating GLP* with their
    morphisms, the canonical frame being the dual of `LT_GLP`; and
    Esakia's representation of Magari algebras as derivative operators
    of scattered spaces.  Replace the posetal `Stone_*` and `Esakia_*`
    statements; prove `modal_duality_summary`.

12. Prove Solovay's theorems for level 0 of the tower, with
    interpretations into `FOFormula` in place of the `Form -> Form`
    notion of arithmetic interpretation: for level-0 formulas,
    `Provable_GL phi <-> forall nu, FOProvesTn 0 (FOembed nu phi)`, and
    `Provable_GLS phi <-> forall nu e, FOsat e (FOembed nu phi)`, with
    `Provable_GLS` defined as GL plus every instance of
    `Impl (Box 0 phi) phi` under modus ponens alone; prove
    `solovay_summary`.

13. Determine the polymodal logic of the tower under `FOembed`.  Prove
    that it contains GLP* (item 4) and the local reflection schema
    `Box (S n) (Impl (Box n phi) phi)`, which GLP* does not derive; that
    it does not contain the Japaridze scheme, some instance failing in
    the standard model because every level is a sound r.e. extension of
    Q; axiomatize it as `Provable_tower` and prove
    `forall phi, (forall nu, FOProvesTn 0 (FOembed nu phi)) ->
    Provable_tower phi`; prove `tower_logic_summary`.

14. Define the consistency progression, `T^c_0 = T_0` and
    `T^c_(n+1) = T^c_n + Con(T^c_n)`, with its provability sentences;
    determine its polymodal logic, which contains GLP* and
    `Iff (Box (S n) phi) (Box n (Impl (Diamond n Top) phi))`, and prove
    the arithmetical completeness theorem of Beklemishev, "Provability
    logics for natural Turing progressions of arithmetical theories"
    (Studia Logica 50, 1991), for it; prove
    `consistency_progression_summary`.

15. Define n-provability in the arithmetic layer, provability in `T_0`
    extended by all true Π_n sentences through partial truth
    definitions for Π_n formulas, and prove Japaridze's theorem that
    GLP (`Provable_GLP`) is sound and complete for it, moving the
    Japaridze-tree results onto this interpretation; prove
    `japaridze_completeness_summary`.

16. Reprove every downstream consumer (Π₂ conservativity, the tiling
    chain, the agent modules) against the arithmetic interpretation
    that matches its calculus: the tower for GLP* and the tower's
    logic, the consistency progression for its logic, n-provability
    for GLP.  Each module's `Print Assumptions` lists only the two
    classical axioms; prove `arithmetic_layer_coherence_summary`.

17. Attach every completeness, conservativity and duality theorem to
    the calculus it concerns (GL, GLS, GLP*, GLP, the tower's logic,
    the consistency progression's logic) and prove the containments and
    separations among these calculi, including the conservativity of
    GLP* over GL on level-0 formulas and the incomparability of GLP*
    and GLP; prove `logic_identification_summary`.

18. Formalize and prove Vardanyan's theorem that the quantified
    provability logic of `T_0` is Π⁰₂-complete, with the quantified
    modal language interpreted into `FOFormula`; prove
    `quantified_boundary_summary`.

19. Build an ordinal notation system for the ordinals below Γ₀ in
    Veblen normal form (the CNF type `ord` covers only the ordinals
    below ε₀), with the two-argument Veblen function and its
    fixed-point clauses, Γ₀ as the least strongly critical ordinal and
    the supremum of the iterated Veblen tower, and well-foundedness
    derived from the construction; prove `veblen_Gamma_0_summary`.

20. Replace `Veblen_eps0_ordinal` and the two-case
    `Veblen_phi_function` with ε₀ = φ(1, 0) and φ(n, α) from the
    notation system of item 19.

21. For the closed fragment of GLP, prove that the worm ordering is a
    well-order of type exactly ε₀, with `worm_to_ord` an order
    isomorphism onto the ordinals below ε₀, so that
    `proof_theoretic_ordinal_summary` states the strict bound
    `worm_to_ord w < ε₀` in place of trichotomy disjunctions; prove
    Beklemishev's worm principle true and unprovable in `T_0`; prove
    `ordinal_analysis_tight_summary`.

22. Define the least proof height of a theorem over all of its
    `Provable_term` derivations, prove that it is attained, and use it
    wherever a statement is meant to rank `|-` rather than a single
    derivation; prove `proof_height_on_derivations_summary`.

23. Equip the inert `LambdaBox` combinators (`tS`, `tBoxK`, `tLoeb`,
    `tBox4`, `tMon`, `tNextCon`, `tLoebFix`) with contraction rules,
    including S duplication and a guarded `tLoebFix` unfolding, prove
    strong normalization by reducibility candidates against the full
    reduction relation, and reprove `extract_realizer_reduces`; prove
    `lambda_box_SN_summary`.

24. Define `Vingean_reflection_at` as local reflection of level `n`
    inside level `n + 1`, `Box (S n) (Impl (Box n phi) phi)` in the
    modal language and `FOAx_Refl` with its uniform variant in the
    tower, prove it for the tower and its logic, prove that GLP* does
    not derive it, and reprove the reflection summary against it.

25. Formalize and prove Critch's parametric bounded Löb theorem over
    length-bounded provability sentences in the arithmetic layer, with
    the bounded diagonal lemma, proof-length accounting and the
    polynomial-overhead argument; prove `Critch_bounded_Loeb_summary`.

26. Prove the self-trust obstruction at every level: `T_n` derives
    `FOImplF (FOProvSentence n A) A` only when it derives `A`, so no
    level derives its own local reflection schema.  State the Löbian
    obstacle for tiling agents in these terms and derive from item 25
    the bounded self-trust that does hold; prove
    `reflective_trust_resolution_summary`.

27. Formalize the Yudkowsky–Herreshoff tiling agent: actions, a goal
    predicate, an agent at level `n + 1` that takes an action only when
    it proves the action null or goal-achieving, and the construction
    of a successor as an action.  Replace `default_action := Top` and
    prove `goal_preservation_tiling` as the theorem that a successor
    licensed at level `n` preserves the goal, together with its failure
    when the successor's level is not below its parent's.

28. Formalize Fallenstein and Soares's parametric polymorphism
    ("Problems of self-reference in self-improving space-time embedded
    intelligence", AGI 2014): a theory `T_κ` with a parameter κ whose
    axioms state that, when κ > 0, every theorem of `T_κ` with κ read as
    κ − 1 is true; its consistency for every numeral value of κ; and
    the tiling theorem for agents that license successors through
    `T_(κ−1)` while κ > 0.  Replace the `Box`-valued `T_kappa`; prove
    `parametric_polymorphism_summary`.

29. Prove the Löbian handshake: for every `psi1` and `psi2` with
    `|- Iff psi1 (Box n (Iff psi2 Cooperate))` and
    `|- Iff psi2 (Box n (Iff psi1 Cooperate))`, both are provable, by
    Löb and `sambin_uniqueness_modalised`; and its arithmetic form for
    FairBots built in `T_0` by the diagonal lemma of item 2.

30. Extend the bot-versus-bot results beyond `opp = Cooperate_action`
    to the opponent matrix of Barasz et al., "Robust Cooperation in the
    Prisoner's Dilemma: Program Equilibrium via Provability Logic"
    (2014): DefectBot, CooperateBot, FairBot, PrudentBot and TrollBot,
    with outcomes computed from the fixed points of item 6 and the
    decision procedure of item 9.  Make the conclusion of
    `FairBot_two_bots_mutual_cooperation` use its hypotheses; prove
    `program_equilibrium_summary`.

31. Build the single finite bounded-budget agent and prove
    `bounded_agent_tiling : forall budget,
    goal_preserved (rewrite_step agent budget)` across its rewrite steps
    from item 25, in place of tower-indexed trust; prove
    `bounded_agent_summary`.

32. Wire the extracted lambda-box realizers to `AgentRecord` decisions
    and prove `extracted_fairbot_correct :
    run (extract fairbot_proof) opp = fairbot_action opp` for the
    bounded FairBot; prove `agent_extraction_summary`.

33. Remove or rename the statements whose content is definitional,
    tautological or a restatement of their hypotheses, among them
    `licenses_universal_property_categorical`,
    `polymodal_sambin_existence`, `cut_admissible_in_full_calculus` and
    `arith_interp_full_soundness`, whose interpretation sends every box
    to ⊤; drop padding conjuncts such as `solovay_function size R 0 = 0`
    from summary bundles; and bring the README's headline list and
    `list.md` into line.

34. Make every theorem named after a result state that result: the
    Solovay, Japaridze, Feferman–Schütte, Tarski, Friedman, Carlson,
    Critch, Vingean, Esakia and Stone statements either prove the named
    theorem, in the item that tracks it, or are renamed to what they
    prove.  Tarski's undefinability of truth for `FOsat`, from the
    diagonal lemma of item 2, is the named result no other item
    tracks.

35. Carve the decidable and syntactic results (box-free decidability,
    the Hilbert toolkit, proof-term reductions, `glp_dec_b`) into
    modules importing neither `Classical` nor `ClassicalEpsilon`,
    verified by `Print Assumptions`, confining the classical axioms to
    the Lindenbaum and completeness parts; prove
    `constructive_core_summary`.

36. Make the build fail on any assumption beyond `classic` and
    `constructive_indefinite_description`: run `rocqchk -o` in CI and
    check its axiom list, and check `Print Assumptions` for every
    summary theorem.
