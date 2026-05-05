# tiling-verified todo

Ordered so each item's prerequisites appear earlier.  Each item must
compile cleanly before the next is begun.

1. Define a genuine first-order extension `QGLP` with quantifiers,
    variable assignments, and a Tarskian semantics; prove which
    fragments are decidable, which are recursively enumerable,
    and which are Π¹₁-complete.
2. Prove constant-domain QGLP* soundness and completeness with
    respect to a Kripke-style first-order semantics for quantified
    modal formulas.
3. Prove the Barcan and converse-Barcan formulas hold or fail in
    the quantified extension, with semantic witnesses.
4. Prove a genuine temporal-extension result where time and modal
    level interact non-trivially.
5. Prove a probabilistic-Löb theorem with a real probability
    parameter (not just `nat`) showing graded reflection survives
    at strictly positive ε.
6. Define a probabilistic logic of provability with graded
    modalities `Bel_p` where `p` is a probability; prove sound
    and complete with respect to a measure-theoretic semantics.
7. Connect the probabilistic version to actual decision-theoretic
    agents using credences.
8. Construct a proper neighborhood-semantics framework; prove
    soundness/completeness for a non-normal modal logic separating
    it from GLP*.
9. Formalise a transfinite-level extension where modalities are
    indexed by ordinals below Γ₀.
10. Extend the calculus with a μ-operator for least fixed points;
    prove the resulting μGLP is decidable.
11. Prove the modal μ-calculus alternation hierarchy is strict at
    every level.
12. Establish the Kozen completeness theorem for μGLP and connect
    μ-fixed points to the parametric tower's fixed-point
    licensing decisions.
13. Define a game semantics for GLP* where verifier and falsifier
    play over the Kripke frame.
14. Establish determinacy for the resulting games on well-founded
    frames; connect winning strategies to proof terms.
15. Connect the FairBot/PrudentBot constructions to actual
    game-theoretic equilibria via the game semantics.
16. Prove the modal logic of programs (PDL) embeds into GLP* via
    a translation mapping program iteration to fixed points.
17. Connect Coalition Logic and ATL to the licensing tower.
18. Prove the disjunction property for `Provable_GLP`.
19. Prove that `Provable_GLP_incomparable_with_provable` extends
    to infinitely many incomparable formulas.
20. Prove a no-go theorem for any uniform strengthening of
    `Ax_NextCon` to `Box n (Neg (Box n Bot))` across all levels.
21. Prove that the `Provable_plus` extension scheme yields
    inconsistency for any reflection-schema extension at any
    level uniformly.
22. Prove the Smoryński bimodal independence theorem at distinct
    levels for non-trivial formulas.
23. Prove the full conservativity of `Provable_GL` over `Provable`
    at level 0 in both directions.
24. Establish the conservativity of GLP* over GL at level 0 in
    both directions and over Japaridze's GLP at all levels.
25. Prove a conservativity ordering: GLP* is conservative over GL
    for level-0 sentences, conservative over a specific theory of
    arithmetic for Π₁ sentences.
26. Prove the polymodal-fixed-point system completeness à la
    Smoryński.
27. Define a realisability interpretation of GLP* where realisers
    are verified programs.
28. Prove a Curry-Howard correspondence for the modal fragment.
29. Establish a propositions-as-types interpretation where
    licensing translates to the existence of a verified compiler
    from level-`n` programs to level-(n+1) programs.
30. Embed GLP* into homotopy type theory.
31. Connect `Box n` to a graded comonad in the categorical
    semantics.
32. Determine the reverse-mathematical strength of each major
    theorem in the development.
33. Prove that `meta_consistency_system` requires no more than
    primitive recursive arithmetic.
34. Extract a verified OCaml or Haskell decision procedure from
    the Coq development; benchmark against existing modal-logic
    provers.
35. Use the formalisation to verify a real safety property of a
    real machine-learning system.
36. Connect the verification to a runtime monitor that rejects
    unsafe operations based on level-`n` proof obligations.
37. Prove a non-trivial program transformation correct using the
    modal apparatus.
38. Split `Tiling.v` into themed modules — `Calculus`, `Hilbert`,
    `Kripke`, `FixedPoints`, `Bew`, `ProofTerms`, `Worms`,
    `Agents`.  (A 15-module split is already drafted on
    `multi-module-split` and can be merged.)
39. Add `Examples.v` with three worked examples.
40. Add `README.md` listing the headline theorems, the dependency
    story, and build instructions.
41. Provide tutorial sections explaining the proof strategies.
42. Cross-reference each theorem to its source in Boolos's *The
    Logic of Provability*, Smoryński's *Self-Reference and Modal
    Logic*, Beklemishev's papers, and the YH13 tech report.
