# tiling-verified todo

Ordered so each item's prerequisites appear earlier.  Each item must
compile cleanly before the next is begun.

1. Formalise a transfinite-level extension where modalities are
    indexed by ordinals below Γ₀.
2. Extend the calculus with a μ-operator for least fixed points;
    prove the resulting μGLP is decidable.
3. Prove the modal μ-calculus alternation hierarchy is strict at
    every level.
4. Establish the Kozen completeness theorem for μGLP and connect
    μ-fixed points to the parametric tower's fixed-point
    licensing decisions.
5. Define a game semantics for GLP* where verifier and falsifier
    play over the Kripke frame.
6. Establish determinacy for the resulting games on well-founded
    frames; connect winning strategies to proof terms.
7. Connect the FairBot/PrudentBot constructions to actual
    game-theoretic equilibria via the game semantics.
8. Prove the modal logic of programs (PDL) embeds into GLP* via
    a translation mapping program iteration to fixed points.
9. Connect Coalition Logic and ATL to the licensing tower.
10. Prove the disjunction property for `Provable_GLP`.
11. Prove that `Provable_GLP_incomparable_with_provable` extends
    to infinitely many incomparable formulas.
12. Prove a no-go theorem for any uniform strengthening of
    `Ax_NextCon` to `Box n (Neg (Box n Bot))` across all levels.
13. Prove that the `Provable_plus` extension scheme yields
    inconsistency for any reflection-schema extension at any
    level uniformly.
14. Prove the Smoryński bimodal independence theorem at distinct
    levels for non-trivial formulas.
15. Prove the full conservativity of `Provable_GL` over `Provable`
    at level 0 in both directions.
16. Establish the conservativity of GLP* over GL at level 0 in
    both directions and over Japaridze's GLP at all levels.
17. Prove a conservativity ordering: GLP* is conservative over GL
    for level-0 sentences, conservative over a specific theory of
    arithmetic for Π₁ sentences.
18. Prove the polymodal-fixed-point system completeness à la
    Smoryński.
19. Define a realisability interpretation of GLP* where realisers
    are verified programs.
20. Prove a Curry-Howard correspondence for the modal fragment.
21. Establish a propositions-as-types interpretation where
    licensing translates to the existence of a verified compiler
    from level-`n` programs to level-(n+1) programs.
22. Embed GLP* into homotopy type theory.
23. Connect `Box n` to a graded comonad in the categorical
    semantics.
24. Determine the reverse-mathematical strength of each major
    theorem in the development.
25. Prove that `meta_consistency_system` requires no more than
    primitive recursive arithmetic.
26. Extract a verified OCaml or Haskell decision procedure from
    the Coq development; benchmark against existing modal-logic
    provers.
27. Use the formalisation to verify a real safety property of a
    real machine-learning system.
28. Connect the verification to a runtime monitor that rejects
    unsafe operations based on level-`n` proof obligations.
29. Prove a non-trivial program transformation correct using the
    modal apparatus.
30. Split `Tiling.v` into themed modules — `Calculus`, `Hilbert`,
    `Kripke`, `FixedPoints`, `Bew`, `ProofTerms`, `Worms`,
    `Agents`.  (A 15-module split is already drafted on
    `multi-module-split` and can be merged.)
31. Add `Examples.v` with three worked examples.
32. Add `README.md` listing the headline theorems, the dependency
    story, and build instructions.
33. Provide tutorial sections explaining the proof strategies.
34. Cross-reference each theorem to its source in Boolos's *The
    Logic of Provability*, Smoryński's *Self-Reference and Modal
    Logic*, Beklemishev's papers, and the YH13 tech report.
