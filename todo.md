# tiling-verified todo

Ordered so each item's prerequisites appear earlier.  Each item must
compile cleanly before the next is begun.

1. Re-derive the worm theory inside a calculus where Mon is
    absent (genuine GLP), so worms have non-trivial provability
    content and the worm-ordinal correspondence captures real
    proof-theoretic strength rather than collapsing.
2. Prove Beklemishev's worm normal form theorem for
    `Provable_GLP` (where worms are not all provable), not just
    the trivial collapse in `Provable`.
3. Prove the Beklemishev reduction theorem: every theorem of GLP
    is provably equivalent (in GLP) to a Boolean combination of
    worms.
4. Prove the worm-ordering total: for any two worms `w₁`, `w₂`,
    decide which provably implies the other in GLP, with the
    ordering matching Cantor-normal-form comparison on
    `worm_to_ord`.
5. Prove that the proof-theoretic ordinal of GLP (without Mon)
    equals ε₀ via Beklemishev's worm normalisation.
6. Prove the proof-theoretic ordinal of `Provable_GLP` is exactly
    ε₀ via a complete ordinal-assignment to proof terms with
    strict decrease under reduction.
7. Compute the proof-theoretic ordinal of GLP* as presented and
    prove a sharp upper and lower bound.
8. Replace the syntactic `Veblen_phi_iter` and `Gamma_0_approx`
    shells with the genuine Veblen hierarchy as ordinal functions;
    prove their fixed-point properties.
9. Prove Carlson's theorem on the ordinal-analysis correspondence
    between worms and ordinals below ε₀.
10. Prove Carlson's theorem (second incompleteness for polymodal
    provability) in its sharp form.
11. Prove the explicit ε₀-rank-respecting normalisation theorem
    for proof terms with strict ordinal decrease.
12. Prove Gentzen's consistency proof for PA via ε₀-induction
    inside Coq.
13. Define a genuine first-order extension `QGLP` with quantifiers,
    variable assignments, and a Tarskian semantics; prove which
    fragments are decidable, which are recursively enumerable,
    and which are Π¹₁-complete.
14. Prove constant-domain QGLP* soundness and completeness with
    respect to a Kripke-style first-order semantics for quantified
    modal formulas.
15. Prove the Barcan and converse-Barcan formulas hold or fail in
    the quantified extension, with semantic witnesses.
16. Prove a genuine temporal-extension result where time and modal
    level interact non-trivially.
17. Prove a probabilistic-Löb theorem with a real probability
    parameter (not just `nat`) showing graded reflection survives
    at strictly positive ε.
18. Define a probabilistic logic of provability with graded
    modalities `Bel_p` where `p` is a probability; prove sound
    and complete with respect to a measure-theoretic semantics.
19. Connect the probabilistic version to actual decision-theoretic
    agents using credences.
20. Construct a proper neighborhood-semantics framework; prove
    soundness/completeness for a non-normal modal logic separating
    it from GLP*.
21. Formalise a transfinite-level extension where modalities are
    indexed by ordinals below Γ₀.
22. Extend the calculus with a μ-operator for least fixed points;
    prove the resulting μGLP is decidable.
23. Prove the modal μ-calculus alternation hierarchy is strict at
    every level.
24. Establish the Kozen completeness theorem for μGLP and connect
    μ-fixed points to the parametric tower's fixed-point
    licensing decisions.
25. Define a game semantics for GLP* where verifier and falsifier
    play over the Kripke frame.
26. Establish determinacy for the resulting games on well-founded
    frames; connect winning strategies to proof terms.
27. Connect the FairBot/PrudentBot constructions to actual
    game-theoretic equilibria via the game semantics.
28. Prove the modal logic of programs (PDL) embeds into GLP* via
    a translation mapping program iteration to fixed points.
29. Connect Coalition Logic and ATL to the licensing tower.
30. Prove the disjunction property for `Provable_GLP`.
31. Prove that `Provable_GLP_incomparable_with_provable` extends
    to infinitely many incomparable formulas.
32. Prove a no-go theorem for any uniform strengthening of
    `Ax_NextCon` to `Box n (Neg (Box n Bot))` across all levels.
33. Prove that the `Provable_plus` extension scheme yields
    inconsistency for any reflection-schema extension at any
    level uniformly.
34. Prove the Smoryński bimodal independence theorem at distinct
    levels for non-trivial formulas.
35. Prove the full conservativity of `Provable_GL` over `Provable`
    at level 0 in both directions.
36. Establish the conservativity of GLP* over GL at level 0 in
    both directions and over Japaridze's GLP at all levels.
37. Prove a conservativity ordering: GLP* is conservative over GL
    for level-0 sentences, conservative over a specific theory of
    arithmetic for Π₁ sentences.
38. Prove the polymodal-fixed-point system completeness à la
    Smoryński.
39. Define a realisability interpretation of GLP* where realisers
    are verified programs.
40. Prove a Curry-Howard correspondence for the modal fragment.
41. Establish a propositions-as-types interpretation where
    licensing translates to the existence of a verified compiler
    from level-`n` programs to level-(n+1) programs.
42. Embed GLP* into homotopy type theory.
43. Connect `Box n` to a graded comonad in the categorical
    semantics.
44. Determine the reverse-mathematical strength of each major
    theorem in the development.
45. Prove that `meta_consistency_system` requires no more than
    primitive recursive arithmetic.
46. Extract a verified OCaml or Haskell decision procedure from
    the Coq development; benchmark against existing modal-logic
    provers.
47. Use the formalisation to verify a real safety property of a
    real machine-learning system.
48. Connect the verification to a runtime monitor that rejects
    unsafe operations based on level-`n` proof obligations.
49. Prove a non-trivial program transformation correct using the
    modal apparatus.
50. Split `Tiling.v` into themed modules — `Calculus`, `Hilbert`,
    `Kripke`, `FixedPoints`, `Bew`, `ProofTerms`, `Worms`,
    `Agents`.  (A 15-module split is already drafted on
    `multi-module-split` and can be merged.)
51. Add `Examples.v` with three worked examples.
52. Add `README.md` listing the headline theorems, the dependency
    story, and build instructions.
53. Provide tutorial sections explaining the proof strategies.
54. Cross-reference each theorem to its source in Boolos's *The
    Logic of Provability*, Smoryński's *Self-Reference and Modal
    Logic*, Beklemishev's papers, and the YH13 tech report.
