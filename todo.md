# tiling-verified todo

Ordered so each item's prerequisites appear earlier.  Each item must
compile cleanly before the next is begun.

1. Connect Coalition Logic and ATL to the licensing tower.
2. Prove the disjunction property for `Provable_GLP`.
3. Prove that `Provable_GLP_incomparable_with_provable` extends
    to infinitely many incomparable formulas.
4. Prove a no-go theorem for any uniform strengthening of
    `Ax_NextCon` to `Box n (Neg (Box n Bot))` across all levels.
5. Prove that the `Provable_plus` extension scheme yields
    inconsistency for any reflection-schema extension at any
    level uniformly.
6. Prove the Smoryński bimodal independence theorem at distinct
    levels for non-trivial formulas.
7. Prove the full conservativity of `Provable_GL` over `Provable`
    at level 0 in both directions.
8. Establish the conservativity of GLP* over GL at level 0 in
    both directions and over Japaridze's GLP at all levels.
9. Prove a conservativity ordering: GLP* is conservative over GL
    for level-0 sentences, conservative over a specific theory of
    arithmetic for Π₁ sentences.
10. Prove the polymodal-fixed-point system completeness à la
    Smoryński.
11. Define a realisability interpretation of GLP* where realisers
    are verified programs.
12. Prove a Curry-Howard correspondence for the modal fragment.
13. Establish a propositions-as-types interpretation where
    licensing translates to the existence of a verified compiler
    from level-`n` programs to level-(n+1) programs.
14. Embed GLP* into homotopy type theory.
15. Connect `Box n` to a graded comonad in the categorical
    semantics.
16. Determine the reverse-mathematical strength of each major
    theorem in the development.
17. Prove that `meta_consistency_system` requires no more than
    primitive recursive arithmetic.
18. Extract a verified OCaml or Haskell decision procedure from
    the Coq development; benchmark against existing modal-logic
    provers.
19. Use the formalisation to verify a real safety property of a
    real machine-learning system.
20. Connect the verification to a runtime monitor that rejects
    unsafe operations based on level-`n` proof obligations.
21. Prove a non-trivial program transformation correct using the
    modal apparatus.
22. Split `Tiling.v` into themed modules — `Calculus`, `Hilbert`,
    `Kripke`, `FixedPoints`, `Bew`, `ProofTerms`, `Worms`,
    `Agents`.  (A 15-module split is already drafted on
    `multi-module-split` and can be merged.)
23. Add `Examples.v` with three worked examples.
24. Add `README.md` listing the headline theorems, the dependency
    story, and build instructions.
25. Provide tutorial sections explaining the proof strategies.
26. Cross-reference each theorem to its source in Boolos's *The
    Logic of Provability*, Smoryński's *Self-Reference and Modal
    Logic*, Beklemishev's papers, and the YH13 tech report.
