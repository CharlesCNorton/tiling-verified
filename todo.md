# tiling-verified todo

Ordered so each item's prerequisites appear earlier.  Each item must
compile cleanly before the next is begun.

1. Demonstrate a concrete failure case where a level-`n` agent
    cannot license a successor that a level-(n+1) agent can,
    using actual programs and goals rather than uninterpreted
    formulas.
2. Prove the goal-preservation tiling theorem for an agent that
    takes non-trivial actions changing the state.
3. Prove vingean reflection in a setting where the agent's
    decision genuinely depends on `T_(n+1)` licensure.
4. Prove the no-panic reflective-trust theorem at the level of
    self-modifying agents.
5. Prove the `T_kappa` agent-correspondence theorem with a
    non-trivial agent architecture.
6. Replace the constant `Cooperate := ⊤` with a genuine action
    representing cooperation in a payoff-bearing game.
7. Define `FairBot n psi := psi := Box n (Iff (opp psi) Cooperate)`
    as a real Sambin fixed point where `opp` reads from the open
    variable.
8. Define `PrudentBot n psi` as a real Sambin fixed point with
    the consistency conjunct `Box (S n) (Neg (Box n Bot))`.
9. Prove FairBot vs FairBot mutual cooperation with the genuine
    fixed-point semantics and source-code reflection.
10. Prove FairBot vs DefectBot defection.
11. Prove FairBot vs CooperateBot mutual cooperation and FairBot
    vs DefectBot mutual defection as theorems where the bots
    access opponents' source code via a reflection principle.
12. Prove the BCFHLY robust-cooperation theorem for non-trivial
    fixed points (not just the collapse to `Top`).
13. Prove that PrudentBot strictly dominates FairBot in modal-PD
    against DefectBot, exhibiting concrete formula witnesses.
14. Establish PrudentBot's strict Pareto improvement over FairBot
    by exhibiting an opponent against which PrudentBot defects
    correctly but a naïve FairBot would cooperate.
15. Prove Aumann's agreement theorem in modal form: agents at
    different levels with common knowledge of consistency provably
    agree (the existing `Aumann_agreement_modal_real` covers the
    two-level case; extend to common-knowledge across many
16. Prove the Fallenstein-Soares 2014 finite-tower
    self-modification theorem at the arithmetic level.
17. Prove the Pudlák speedup result for the parametric tower at
    every level.
18. Prove a quantitative version of the Löbian obstacle: bound the
    proof length of the inconsistency derivation by a function of
    the reflection-schema's proof complexity.
19. Formalise the original Yudkowsky-Herreshoff tiling agent as a
    concrete program: a Turing machine that, given a candidate
    successor, performs a bounded proof search at level `n`,
    decides licensing based on a specific verification predicate,
20. Prove the tiling-agent never-defects-against-itself theorem:
    when two such agents face each other in a coordination game,
    both license the cooperative strategy via a common-knowledge
    fixed point.
21. Establish the Vingean reflection no-go result formally.
22. Prove the Fallenstein parametric bounded Löb result: bounded
    Löb with parameter `k` holds iff the agent's verifier has
    access to proofs of length at least `k`.
23. Connect the tower to a concrete model of self-improvement:
    prove that an agent at level `n` licensing a successor at
    level `n+1` corresponds to a specific code transformation
    preserving a goal predicate.
24. Re-derive the worm theory inside a calculus where Mon is
    absent (genuine GLP), so worms have non-trivial provability
    content and the worm-ordinal correspondence captures real
    proof-theoretic strength rather than collapsing.
25. Prove Beklemishev's worm normal form theorem for
    `Provable_GLP` (where worms are not all provable), not just
    the trivial collapse in `Provable`.
26. Prove the Beklemishev reduction theorem: every theorem of GLP
    is provably equivalent (in GLP) to a Boolean combination of
    worms.
27. Prove the worm-ordering total: for any two worms `w₁`, `w₂`,
    decide which provably implies the other in GLP, with the
    ordering matching Cantor-normal-form comparison on
    `worm_to_ord`.
28. Prove that the proof-theoretic ordinal of GLP (without Mon)
    equals ε₀ via Beklemishev's worm normalisation.
29. Prove the proof-theoretic ordinal of `Provable_GLP` is exactly
    ε₀ via a complete ordinal-assignment to proof terms with
    strict decrease under reduction.
30. Compute the proof-theoretic ordinal of GLP* as presented and
    prove a sharp upper and lower bound.
31. Replace the syntactic `Veblen_phi_iter` and `Gamma_0_approx`
    shells with the genuine Veblen hierarchy as ordinal functions;
    prove their fixed-point properties.
32. Prove Carlson's theorem on the ordinal-analysis correspondence
    between worms and ordinals below ε₀.
33. Prove Carlson's theorem (second incompleteness for polymodal
    provability) in its sharp form.
34. Prove the explicit ε₀-rank-respecting normalisation theorem
    for proof terms with strict ordinal decrease.
35. Prove Gentzen's consistency proof for PA via ε₀-induction
    inside Coq.
36. Define a genuine first-order extension `QGLP` with quantifiers,
    variable assignments, and a Tarskian semantics; prove which
    fragments are decidable, which are recursively enumerable,
    and which are Π¹₁-complete.
37. Prove constant-domain QGLP* soundness and completeness with
    respect to a Kripke-style first-order semantics for quantified
    modal formulas.
38. Prove the Barcan and converse-Barcan formulas hold or fail in
    the quantified extension, with semantic witnesses.
39. Prove a genuine temporal-extension result where time and modal
    level interact non-trivially.
40. Prove a probabilistic-Löb theorem with a real probability
    parameter (not just `nat`) showing graded reflection survives
    at strictly positive ε.
41. Define a probabilistic logic of provability with graded
    modalities `Bel_p` where `p` is a probability; prove sound
    and complete with respect to a measure-theoretic semantics.
42. Connect the probabilistic version to actual decision-theoretic
    agents using credences.
43. Construct a proper neighborhood-semantics framework; prove
    soundness/completeness for a non-normal modal logic separating
    it from GLP*.
44. Formalise a transfinite-level extension where modalities are
    indexed by ordinals below Γ₀.
45. Extend the calculus with a μ-operator for least fixed points;
    prove the resulting μGLP is decidable.
46. Prove the modal μ-calculus alternation hierarchy is strict at
    every level.
47. Establish the Kozen completeness theorem for μGLP and connect
    μ-fixed points to the parametric tower's fixed-point
    licensing decisions.
48. Define a game semantics for GLP* where verifier and falsifier
    play over the Kripke frame.
49. Establish determinacy for the resulting games on well-founded
    frames; connect winning strategies to proof terms.
50. Connect the FairBot/PrudentBot constructions to actual
    game-theoretic equilibria via the game semantics.
51. Prove the modal logic of programs (PDL) embeds into GLP* via
    a translation mapping program iteration to fixed points.
52. Connect Coalition Logic and ATL to the licensing tower.
53. Prove the disjunction property for `Provable_GLP`.
54. Prove that `Provable_GLP_incomparable_with_provable` extends
    to infinitely many incomparable formulas.
55. Prove a no-go theorem for any uniform strengthening of
    `Ax_NextCon` to `Box n (Neg (Box n Bot))` across all levels.
56. Prove that the `Provable_plus` extension scheme yields
    inconsistency for any reflection-schema extension at any
    level uniformly.
57. Prove the Smoryński bimodal independence theorem at distinct
    levels for non-trivial formulas.
58. Prove the full conservativity of `Provable_GL` over `Provable`
    at level 0 in both directions.
59. Establish the conservativity of GLP* over GL at level 0 in
    both directions and over Japaridze's GLP at all levels.
60. Prove a conservativity ordering: GLP* is conservative over GL
    for level-0 sentences, conservative over a specific theory of
    arithmetic for Π₁ sentences.
61. Prove the polymodal-fixed-point system completeness à la
    Smoryński.
62. Define a realisability interpretation of GLP* where realisers
    are verified programs.
63. Prove a Curry-Howard correspondence for the modal fragment.
64. Establish a propositions-as-types interpretation where
    licensing translates to the existence of a verified compiler
    from level-`n` programs to level-(n+1) programs.
65. Embed GLP* into homotopy type theory.
66. Connect `Box n` to a graded comonad in the categorical
    semantics.
67. Determine the reverse-mathematical strength of each major
    theorem in the development.
68. Prove that `meta_consistency_system` requires no more than
    primitive recursive arithmetic.
69. Extract a verified OCaml or Haskell decision procedure from
    the Coq development; benchmark against existing modal-logic
    provers.
70. Use the formalisation to verify a real safety property of a
    real machine-learning system.
71. Connect the verification to a runtime monitor that rejects
    unsafe operations based on level-`n` proof obligations.
72. Prove a non-trivial program transformation correct using the
    modal apparatus.
73. Split `Tiling.v` into themed modules — `Calculus`, `Hilbert`,
    `Kripke`, `FixedPoints`, `Bew`, `ProofTerms`, `Worms`,
    `Agents`.  (A 15-module split is already drafted on
    `multi-module-split` and can be merged.)
74. Add `Examples.v` with three worked examples.
75. Add `README.md` listing the headline theorems, the dependency
    story, and build instructions.
76. Provide tutorial sections explaining the proof strategies.
77. Cross-reference each theorem to its source in Boolos's *The
    Logic of Provability*, Smoryński's *Self-Reference and Modal
    Logic*, Beklemishev's papers, and the YH13 tech report.
