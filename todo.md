# tiling-verified todo

Ordered so each item's prerequisites appear earlier.  Each item must
compile cleanly before the next is begun.

1. Define a realisability interpretation of GLP* where realisers
    are verified programs.
2. Prove a Curry-Howard correspondence for the modal fragment.
3. Establish a propositions-as-types interpretation where
    licensing translates to the existence of a verified compiler
    from level-`n` programs to level-(n+1) programs.
4. Embed GLP* into homotopy type theory.
5. Connect `Box n` to a graded comonad in the categorical
    semantics.
6. Determine the reverse-mathematical strength of each major
    theorem in the development.
7. Prove that `meta_consistency_system` requires no more than
    primitive recursive arithmetic.
8. Extract a verified OCaml or Haskell decision procedure from
    the Coq development; benchmark against existing modal-logic
    provers.
9. Use the formalisation to verify a real safety property of a
    real machine-learning system.
10. Connect the verification to a runtime monitor that rejects
    unsafe operations based on level-`n` proof obligations.
11. Prove a non-trivial program transformation correct using the
    modal apparatus.
12. Split `Tiling.v` into themed modules — `Calculus`, `Hilbert`,
    `Kripke`, `FixedPoints`, `Bew`, `ProofTerms`, `Worms`,
    `Agents`.  (A 15-module split is already drafted on
    `multi-module-split` and can be merged.)
13. Add `Examples.v` with three worked examples.
14. Add `README.md` listing the headline theorems, the dependency
    story, and build instructions.
15. Provide tutorial sections explaining the proof strategies.
16. Cross-reference each theorem to its source in Boolos's *The
    Logic of Provability*, Smoryński's *Self-Reference and Modal
    Logic*, Beklemishev's papers, and the YH13 tech report.
