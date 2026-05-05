# tiling-verified todo

Ordered so each item's prerequisites appear earlier.  Each item must
compile cleanly before the next is begun.

1. Construct, for each `n`, a Gödel sentence `Gₙ` with
    `|- Iff Gₙ (Neg (Bew_n ⌜Gₙ⌝))`; prove `Gₙ` is independent of
    `Tₙ` but provable in `Tₙ₊₁`.
2. Construct in Coq an explicit recursive enumeration of axioms
    for each `Tₙ` as actual arithmetic theories extending Robinson
    Q (or PA), with the level-(n+1) theory containing the Σ₁
    sentence `Con(Tₙ)`; prove cumulativity as a theorem about
    provability rather than a definitional inclusion.
3. Construct a first-order theory `T_n` with explicit axioms (not
    just modal axiom-schemas via `T_axiom`); prove the
    cumulativity, consistency, and tiling results at the genuine
    first-order level.
4. Eliminate `Ax_NextCon` from the axiom list and instead derive
    `Box (S n) (¬ Box n ⊥)` from properties of an underlying
    arithmetic theory.
5. Establish a non-trivial consistency-strength ordering between
    `Tₙ` and `Tₙ₊₁` by proving an ordinal analysis result.
6. Prove the tower bypass non-vacuous by exhibiting a specific
    `φ` such that `Tₙ` does not prove `Con(Tₙ → φ)` but `Tₙ₊₁`
    does.
7. Prove a soundness theorem connecting modal `Box n φ` to the
    arithmetised `Bew_n ⌜φ*⌝` for a realisation map `φ ↦ φ*`.
8. Prove Π₁ conservativity of `T_(n+1)` over `T_n` for arithmetic
    Π₁ sentences.
9. Prove Π₂ conservativity across the tower.
10. Prove Friedman's negative translation result connecting
    classical to constructive provability beyond the box-free
    case.
11. Prove the relative-consistency direction `Con(T_0) → Con(T_n)`
    from a strictly weaker hypothesis than meta-consistency of the
    full system.
12. Prove the strict separation between `Bew n` and `Bew (S n)` at
    the proof level (not just at the axiom-set level).
13. Prove that the structural `Bew` predicate satisfies provability
    logic (i.e. `Bew n` interpreted into `Box n` validates exactly
    GLP* at the relevant level).
14. Prove Solovay's first completeness theorem in full: every
    modal formula valid under all arithmetic interpretations into
    PA is provable in GL.
15. Prove Solovay's second completeness theorem for the
    truth-extension `Provable_S` beyond the box-free fragment.
16. Prove arithmetic completeness of `Provable_GLP` (Japaridze's
    theorem) for arbitrary formulas, not just box-free ones.
17. Construct a genuinely non-identity, non-licensure inhabitant of
    `is_arithmetic_interpretation` to show the predicate has
    non-trivial structure beyond `identity` and `licenses k`.
18. Prove Tarski undefinability in its sharpest form: no formula
    `Tr(x)` in the language of GLP* with one free variable
    satisfies `|- Iff (Tr ⌜φ⌝) φ` for all `φ`.
19. Prove a strong undefinability theorem by Gödel diagonalisation
    on a self-referential sentence, in any consistent extension of
    the calculus with a unary `Tr` satisfying the T-schema.
20. Prove the Friedman-Sheard truth-axiomatisation theorem.
21. Construct a hierarchy of partial truth predicates `Trₙ` where
    each `Trₙ` correctly evaluates formulas of modal depth `≤ n`,
    with `Trₙ` definable at level `n+1`, paralleling Tarski's
    hierarchy.
22. Prove the Visser interpretability logic ILM/ILP axioms beyond
    just the K-distribution and Box4 forms.
23. Prove the Visser-Berarducci theorem on interpretability logic:
    ILM is the interpretability logic of any reasonable arithmetic
    theory containing IΣ₁.
24. Prove the Visser ILM J5 axiom from the calculus axioms rather
    than via `Ax_Mon`.
25. Prove the Critch parametric bounded-Löb theorem for a genuinely
    bounded provability predicate (with proof-length bound encoded
    inside the modal formula), not just iterated `Box`.
26. Prove the Critch correspondence between modal
    `critch_bounded_box` and a genuine bounded-arithmetic
    provability predicate with explicit polynomial bounds.
27. Implement Critch's bounded provability with an explicit
    resource bound `k` counting proof steps; prove a parametric
    Löb theorem with a threshold `k₀`.
28. Construct a concrete agent using bounded provability whose
    behaviour depends measurably on `k`.
29. Replace the cosmetic alias `licenses n φ := Box n φ` with a
    substantive predicate over a separately defined `Agent`
    record carrying a decision procedure, a goal predicate, an
    action space, and a verification routine.
30. Formalise a concrete agent that takes as input a candidate
    successor and outputs a decision in finite time based on
    inspection of a level-`n` proof.
31. Prove a non-trivial successor-licensing theorem: given an
    explicit goal predicate `G`, an explicit transition function,
    and an explicit candidate successor `σ`, derive that the
    level-`n` agent licenses `σ` iff a verifiable condition on
    `σ` holds, where the condition is computable.
32. Demonstrate a concrete failure case where a level-`n` agent
    cannot license a successor that a level-(n+1) agent can,
    using actual programs and goals rather than uninterpreted
    formulas.
33. Prove the goal-preservation tiling theorem for an agent that
    takes non-trivial actions changing the state.
34. Prove vingean reflection in a setting where the agent's
    decision genuinely depends on `T_(n+1)` licensure.
35. Prove the no-panic reflective-trust theorem at the level of
    self-modifying agents.
36. Prove the `T_kappa` agent-correspondence theorem with a
    non-trivial agent architecture.
37. Replace the constant `Cooperate := ⊤` with a genuine action
    representing cooperation in a payoff-bearing game.
38. Define `FairBot n psi := psi := Box n (Iff (opp psi) Cooperate)`
    as a real Sambin fixed point where `opp` reads from the open
    variable.
39. Define `PrudentBot n psi` as a real Sambin fixed point with
    the consistency conjunct `Box (S n) (Neg (Box n Bot))`.
40. Prove FairBot vs FairBot mutual cooperation with the genuine
    fixed-point semantics and source-code reflection.
41. Prove FairBot vs DefectBot defection.
42. Prove FairBot vs CooperateBot mutual cooperation and FairBot
    vs DefectBot mutual defection as theorems where the bots
    access opponents' source code via a reflection principle.
43. Prove the BCFHLY robust-cooperation theorem for non-trivial
    fixed points (not just the collapse to `Top`).
44. Prove that PrudentBot strictly dominates FairBot in modal-PD
    against DefectBot, exhibiting concrete formula witnesses.
45. Establish PrudentBot's strict Pareto improvement over FairBot
    by exhibiting an opponent against which PrudentBot defects
    correctly but a naïve FairBot would cooperate.
46. Prove Aumann's agreement theorem in modal form: agents at
    different levels with common knowledge of consistency provably
    agree (the existing `Aumann_agreement_modal_real` covers the
    two-level case; extend to common-knowledge across many
47. Prove the Fallenstein-Soares 2014 finite-tower
    self-modification theorem at the arithmetic level.
48. Prove the Pudlák speedup result for the parametric tower at
    every level.
49. Prove a quantitative version of the Löbian obstacle: bound the
    proof length of the inconsistency derivation by a function of
    the reflection-schema's proof complexity.
50. Formalise the original Yudkowsky-Herreshoff tiling agent as a
    concrete program: a Turing machine that, given a candidate
    successor, performs a bounded proof search at level `n`,
    decides licensing based on a specific verification predicate,
51. Prove the tiling-agent never-defects-against-itself theorem:
    when two such agents face each other in a coordination game,
    both license the cooperative strategy via a common-knowledge
    fixed point.
52. Establish the Vingean reflection no-go result formally.
53. Prove the Fallenstein parametric bounded Löb result: bounded
    Löb with parameter `k` holds iff the agent's verifier has
    access to proofs of length at least `k`.
54. Connect the tower to a concrete model of self-improvement:
    prove that an agent at level `n` licensing a successor at
    level `n+1` corresponds to a specific code transformation
    preserving a goal predicate.
55. Re-derive the worm theory inside a calculus where Mon is
    absent (genuine GLP), so worms have non-trivial provability
    content and the worm-ordinal correspondence captures real
    proof-theoretic strength rather than collapsing.
56. Prove Beklemishev's worm normal form theorem for
    `Provable_GLP` (where worms are not all provable), not just
    the trivial collapse in `Provable`.
57. Prove the Beklemishev reduction theorem: every theorem of GLP
    is provably equivalent (in GLP) to a Boolean combination of
    worms.
58. Prove the worm-ordering total: for any two worms `w₁`, `w₂`,
    decide which provably implies the other in GLP, with the
    ordering matching Cantor-normal-form comparison on
    `worm_to_ord`.
59. Prove that the proof-theoretic ordinal of GLP (without Mon)
    equals ε₀ via Beklemishev's worm normalisation.
60. Prove the proof-theoretic ordinal of `Provable_GLP` is exactly
    ε₀ via a complete ordinal-assignment to proof terms with
    strict decrease under reduction.
61. Compute the proof-theoretic ordinal of GLP* as presented and
    prove a sharp upper and lower bound.
62. Replace the syntactic `Veblen_phi_iter` and `Gamma_0_approx`
    shells with the genuine Veblen hierarchy as ordinal functions;
    prove their fixed-point properties.
63. Prove Carlson's theorem on the ordinal-analysis correspondence
    between worms and ordinals below ε₀.
64. Prove Carlson's theorem (second incompleteness for polymodal
    provability) in its sharp form.
65. Prove the explicit ε₀-rank-respecting normalisation theorem
    for proof terms with strict ordinal decrease.
66. Prove Gentzen's consistency proof for PA via ε₀-induction
    inside Coq.
67. Define a genuine first-order extension `QGLP` with quantifiers,
    variable assignments, and a Tarskian semantics; prove which
    fragments are decidable, which are recursively enumerable,
    and which are Π¹₁-complete.
68. Prove constant-domain QGLP* soundness and completeness with
    respect to a Kripke-style first-order semantics for quantified
    modal formulas.
69. Prove the Barcan and converse-Barcan formulas hold or fail in
    the quantified extension, with semantic witnesses.
70. Prove a genuine temporal-extension result where time and modal
    level interact non-trivially.
71. Prove a probabilistic-Löb theorem with a real probability
    parameter (not just `nat`) showing graded reflection survives
    at strictly positive ε.
72. Define a probabilistic logic of provability with graded
    modalities `Bel_p` where `p` is a probability; prove sound
    and complete with respect to a measure-theoretic semantics.
73. Connect the probabilistic version to actual decision-theoretic
    agents using credences.
74. Construct a proper neighborhood-semantics framework; prove
    soundness/completeness for a non-normal modal logic separating
    it from GLP*.
75. Formalise a transfinite-level extension where modalities are
    indexed by ordinals below Γ₀.
76. Extend the calculus with a μ-operator for least fixed points;
    prove the resulting μGLP is decidable.
77. Prove the modal μ-calculus alternation hierarchy is strict at
    every level.
78. Establish the Kozen completeness theorem for μGLP and connect
    μ-fixed points to the parametric tower's fixed-point
    licensing decisions.
79. Define a game semantics for GLP* where verifier and falsifier
    play over the Kripke frame.
80. Establish determinacy for the resulting games on well-founded
    frames; connect winning strategies to proof terms.
81. Connect the FairBot/PrudentBot constructions to actual
    game-theoretic equilibria via the game semantics.
82. Prove the modal logic of programs (PDL) embeds into GLP* via
    a translation mapping program iteration to fixed points.
83. Connect Coalition Logic and ATL to the licensing tower.
84. Prove the disjunction property for `Provable_GLP`.
85. Prove that `Provable_GLP_incomparable_with_provable` extends
    to infinitely many incomparable formulas.
86. Prove a no-go theorem for any uniform strengthening of
    `Ax_NextCon` to `Box n (Neg (Box n Bot))` across all levels.
87. Prove that the `Provable_plus` extension scheme yields
    inconsistency for any reflection-schema extension at any
    level uniformly.
88. Prove the Smoryński bimodal independence theorem at distinct
    levels for non-trivial formulas.
89. Prove the full conservativity of `Provable_GL` over `Provable`
    at level 0 in both directions.
90. Establish the conservativity of GLP* over GL at level 0 in
    both directions and over Japaridze's GLP at all levels.
91. Prove a conservativity ordering: GLP* is conservative over GL
    for level-0 sentences, conservative over a specific theory of
    arithmetic for Π₁ sentences.
92. Prove the polymodal-fixed-point system completeness à la
    Smoryński.
93. Define a realisability interpretation of GLP* where realisers
    are verified programs.
94. Prove a Curry-Howard correspondence for the modal fragment.
95. Establish a propositions-as-types interpretation where
    licensing translates to the existence of a verified compiler
    from level-`n` programs to level-(n+1) programs.
96. Embed GLP* into homotopy type theory.
97. Connect `Box n` to a graded comonad in the categorical
    semantics.
98. Determine the reverse-mathematical strength of each major
    theorem in the development.
99. Prove that `meta_consistency_system` requires no more than
    primitive recursive arithmetic.
100. Extract a verified OCaml or Haskell decision procedure from
    the Coq development; benchmark against existing modal-logic
    provers.
101. Use the formalisation to verify a real safety property of a
    real machine-learning system.
102. Connect the verification to a runtime monitor that rejects
    unsafe operations based on level-`n` proof obligations.
103. Prove a non-trivial program transformation correct using the
    modal apparatus.
104. Split `Tiling.v` into themed modules — `Calculus`, `Hilbert`,
    `Kripke`, `FixedPoints`, `Bew`, `ProofTerms`, `Worms`,
    `Agents`.  (A 15-module split is already drafted on
    `multi-module-split` and can be merged.)
105. Add `Examples.v` with three worked examples.
106. Add `README.md` listing the headline theorems, the dependency
    story, and build instructions.
107. Provide tutorial sections explaining the proof strategies.
108. Cross-reference each theorem to its source in Boolos's *The
    Logic of Provability*, Smoryński's *Self-Reference and Modal
    Logic*, Beklemishev's papers, and the YH13 tech report.
