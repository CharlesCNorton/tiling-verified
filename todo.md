# tiling-verified todo

Ordered so each item's prerequisites appear earlier.  Each item must
compile cleanly before the next is begun.

1. Prove vingean reflection in a setting where the agent's
    decision genuinely depends on `T_(n+1)` licensure.
2. Prove the no-panic reflective-trust theorem at the level of
    self-modifying agents.
3. Prove the `T_kappa` agent-correspondence theorem with a
    non-trivial agent architecture.
4. Replace the constant `Cooperate := ⊤` with a genuine action
    representing cooperation in a payoff-bearing game.
5. Define `FairBot n psi := psi := Box n (Iff (opp psi) Cooperate)`
    as a real Sambin fixed point where `opp` reads from the open
    variable.
6. Define `PrudentBot n psi` as a real Sambin fixed point with
    the consistency conjunct `Box (S n) (Neg (Box n Bot))`.
7. Prove FairBot vs FairBot mutual cooperation with the genuine
    fixed-point semantics and source-code reflection.
8. Prove FairBot vs DefectBot defection.
9. Prove FairBot vs CooperateBot mutual cooperation and FairBot
    vs DefectBot mutual defection as theorems where the bots
    access opponents' source code via a reflection principle.
10. Prove the BCFHLY robust-cooperation theorem for non-trivial
    fixed points (not just the collapse to `Top`).
11. Prove that PrudentBot strictly dominates FairBot in modal-PD
    against DefectBot, exhibiting concrete formula witnesses.
12. Establish PrudentBot's strict Pareto improvement over FairBot
    by exhibiting an opponent against which PrudentBot defects
    correctly but a naïve FairBot would cooperate.
13. Prove Aumann's agreement theorem in modal form: agents at
    different levels with common knowledge of consistency provably
    agree (the existing `Aumann_agreement_modal_real` covers the
    two-level case; extend to common-knowledge across many
14. Prove the Fallenstein-Soares 2014 finite-tower
    self-modification theorem at the arithmetic level.
15. Prove the Pudlák speedup result for the parametric tower at
    every level.
16. Prove a quantitative version of the Löbian obstacle: bound the
    proof length of the inconsistency derivation by a function of
    the reflection-schema's proof complexity.
17. Formalise the original Yudkowsky-Herreshoff tiling agent as a
    concrete program: a Turing machine that, given a candidate
    successor, performs a bounded proof search at level `n`,
    decides licensing based on a specific verification predicate,
18. Prove the tiling-agent never-defects-against-itself theorem:
    when two such agents face each other in a coordination game,
    both license the cooperative strategy via a common-knowledge
    fixed point.
19. Establish the Vingean reflection no-go result formally.
20. Prove the Fallenstein parametric bounded Löb result: bounded
    Löb with parameter `k` holds iff the agent's verifier has
    access to proofs of length at least `k`.
21. Connect the tower to a concrete model of self-improvement:
    prove that an agent at level `n` licensing a successor at
    level `n+1` corresponds to a specific code transformation
    preserving a goal predicate.
22. Re-derive the worm theory inside a calculus where Mon is
    absent (genuine GLP), so worms have non-trivial provability
    content and the worm-ordinal correspondence captures real
    proof-theoretic strength rather than collapsing.
23. Prove Beklemishev's worm normal form theorem for
    `Provable_GLP` (where worms are not all provable), not just
    the trivial collapse in `Provable`.
24. Prove the Beklemishev reduction theorem: every theorem of GLP
    is provably equivalent (in GLP) to a Boolean combination of
    worms.
25. Prove the worm-ordering total: for any two worms `w₁`, `w₂`,
    decide which provably implies the other in GLP, with the
    ordering matching Cantor-normal-form comparison on
    `worm_to_ord`.
26. Prove that the proof-theoretic ordinal of GLP (without Mon)
    equals ε₀ via Beklemishev's worm normalisation.
27. Prove the proof-theoretic ordinal of `Provable_GLP` is exactly
    ε₀ via a complete ordinal-assignment to proof terms with
    strict decrease under reduction.
28. Compute the proof-theoretic ordinal of GLP* as presented and
    prove a sharp upper and lower bound.
29. Replace the syntactic `Veblen_phi_iter` and `Gamma_0_approx`
    shells with the genuine Veblen hierarchy as ordinal functions;
    prove their fixed-point properties.
30. Prove Carlson's theorem on the ordinal-analysis correspondence
    between worms and ordinals below ε₀.
31. Prove Carlson's theorem (second incompleteness for polymodal
    provability) in its sharp form.
32. Prove the explicit ε₀-rank-respecting normalisation theorem
    for proof terms with strict ordinal decrease.
33. Prove Gentzen's consistency proof for PA via ε₀-induction
    inside Coq.
34. Define a genuine first-order extension `QGLP` with quantifiers,
    variable assignments, and a Tarskian semantics; prove which
    fragments are decidable, which are recursively enumerable,
    and which are Π¹₁-complete.
35. Prove constant-domain QGLP* soundness and completeness with
    respect to a Kripke-style first-order semantics for quantified
    modal formulas.
36. Prove the Barcan and converse-Barcan formulas hold or fail in
    the quantified extension, with semantic witnesses.
37. Prove a genuine temporal-extension result where time and modal
    level interact non-trivially.
38. Prove a probabilistic-Löb theorem with a real probability
    parameter (not just `nat`) showing graded reflection survives
    at strictly positive ε.
39. Define a probabilistic logic of provability with graded
    modalities `Bel_p` where `p` is a probability; prove sound
    and complete with respect to a measure-theoretic semantics.
40. Connect the probabilistic version to actual decision-theoretic
    agents using credences.
41. Construct a proper neighborhood-semantics framework; prove
    soundness/completeness for a non-normal modal logic separating
    it from GLP*.
42. Formalise a transfinite-level extension where modalities are
    indexed by ordinals below Γ₀.
43. Extend the calculus with a μ-operator for least fixed points;
    prove the resulting μGLP is decidable.
44. Prove the modal μ-calculus alternation hierarchy is strict at
    every level.
45. Establish the Kozen completeness theorem for μGLP and connect
    μ-fixed points to the parametric tower's fixed-point
    licensing decisions.
46. Define a game semantics for GLP* where verifier and falsifier
    play over the Kripke frame.
47. Establish determinacy for the resulting games on well-founded
    frames; connect winning strategies to proof terms.
48. Connect the FairBot/PrudentBot constructions to actual
    game-theoretic equilibria via the game semantics.
49. Prove the modal logic of programs (PDL) embeds into GLP* via
    a translation mapping program iteration to fixed points.
50. Connect Coalition Logic and ATL to the licensing tower.
51. Prove the disjunction property for `Provable_GLP`.
52. Prove that `Provable_GLP_incomparable_with_provable` extends
    to infinitely many incomparable formulas.
53. Prove a no-go theorem for any uniform strengthening of
    `Ax_NextCon` to `Box n (Neg (Box n Bot))` across all levels.
54. Prove that the `Provable_plus` extension scheme yields
    inconsistency for any reflection-schema extension at any
    level uniformly.
55. Prove the Smoryński bimodal independence theorem at distinct
    levels for non-trivial formulas.
56. Prove the full conservativity of `Provable_GL` over `Provable`
    at level 0 in both directions.
57. Establish the conservativity of GLP* over GL at level 0 in
    both directions and over Japaridze's GLP at all levels.
58. Prove a conservativity ordering: GLP* is conservative over GL
    for level-0 sentences, conservative over a specific theory of
    arithmetic for Π₁ sentences.
59. Prove the polymodal-fixed-point system completeness à la
    Smoryński.
60. Define a realisability interpretation of GLP* where realisers
    are verified programs.
61. Prove a Curry-Howard correspondence for the modal fragment.
62. Establish a propositions-as-types interpretation where
    licensing translates to the existence of a verified compiler
    from level-`n` programs to level-(n+1) programs.
63. Embed GLP* into homotopy type theory.
64. Connect `Box n` to a graded comonad in the categorical
    semantics.
65. Determine the reverse-mathematical strength of each major
    theorem in the development.
66. Prove that `meta_consistency_system` requires no more than
    primitive recursive arithmetic.
67. Extract a verified OCaml or Haskell decision procedure from
    the Coq development; benchmark against existing modal-logic
    provers.
68. Use the formalisation to verify a real safety property of a
    real machine-learning system.
69. Connect the verification to a runtime monitor that rejects
    unsafe operations based on level-`n` proof obligations.
70. Prove a non-trivial program transformation correct using the
    modal apparatus.
71. Split `Tiling.v` into themed modules — `Calculus`, `Hilbert`,
    `Kripke`, `FixedPoints`, `Bew`, `ProofTerms`, `Worms`,
    `Agents`.  (A 15-module split is already drafted on
    `multi-module-split` and can be merged.)
72. Add `Examples.v` with three worked examples.
73. Add `README.md` listing the headline theorems, the dependency
    story, and build instructions.
74. Provide tutorial sections explaining the proof strategies.
75. Cross-reference each theorem to its source in Boolos's *The
    Logic of Provability*, Smoryński's *Self-Reference and Modal
    Logic*, Beklemishev's papers, and the YH13 tech report.
