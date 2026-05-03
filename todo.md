# tiling-verified todo

Ordered so each item's prerequisites appear earlier.  Each item must
compile cleanly before the next is begun.

## Foundational infrastructure (remaining)

1. Prove `well_founded ord_lt` and restate ordinal-embedding theorems on `{ o : ord | wf_ord o }`.  (`ord_lt_trans`, `ord_lt_total`, `wf_ord`, `wf_ord_dec` already done.)
2. Prove `decide_tautology_pspace` soundness: returning `true` implies `classical_valid`, via showing iteration of `bool_list_succ` from `repeat false n` visits every length-n bool list exactly once.

## Proof-term reduction (remaining)

3. Add S-axiom and DN-axiom contraction rules to `pt_reduces` with a measure that strictly decreases (multiset ordinal on subterm-size pairs).  (K and BoxK_Nec already added.)
4. Prove local confluence of `pt_reduces` (any two redexes from the same term reduce to a common form), then lift to full confluence via Newman's lemma.
5. Prove strong normalisation of the extended reduction via a multiset-ordinal measure on proof-term structure (rather than the basic size measure, which doesn't accommodate S-contraction).

## Sambin theorems (remaining)

6. Prove the SC_impl_left_no_occ case of Sambin existence (recursive case where phi = Impl X phi' with p not in X and phi' itself in sambin_class), completing `sambin_class_yields_fixed_point_base` to a uniform existence theorem over the full `sambin_class` inductive.
7. Prove fixed-point existence for `phi(p) := And X (Box n (Var p))` and other compound modalized contexts.
8. Prove full de Jongh-Sambin uniqueness over arbitrary modalized formulas (combining `sambin_uniqueness_loeb_general`, `sambin_uniqueness_box_atomic_general`, `sambin_uniqueness_via_no_occurrence`, `sambin_uniqueness_via_top_class` into a uniform statement keyed on `sambin_class`).

## Canonical model + Kripke completeness

9. Prove `canonical_R` satisfies transitivity from `Ax_Box4`.
10. Prove `canonical_R` satisfies monotonicity from `Ax_Mon`.
11. Prove `canonical_R` satisfies NextCon-successor from `Ax_NextCon`.
12. Prove `canonical_R` satisfies converse-well-foundedness from `Ax_Loeb`.
13. Extend the canonical-model truth lemma to the full modal language (`Box n psi` case) by structural induction on `phi`.
14. Prove Kripke completeness of GLP*: every non-theorem is refuted by some GLP*-frame.
15. Prove the finite frame property: every non-theorem is refuted by a finite GLP*-frame.
16. Prove decidability of the full polymodal calculus via filtration.
17. Prove PSPACE-completeness of GLP* satisfiability/provability.
18. Prove independence of `Ax_K` using non-Kripke (e.g. neighborhood) semantics.
19. Prove Kripke completeness for `Provable_no_NC`, `Provable_no_Mon`, `Provable_no_Loeb`, `Provable_no_B4` separately with their distinguishing frame classes.
20. Prove that each axiom-removal calculus is strictly weaker than `Provable` for infinitely many distinct theorems.

## Sequent calculus + interpolation

21. Build a sequent presentation of GLP*.
22. Prove cut admissibility structurally for the sequent calculus.
23. Prove full Craig interpolation: for every `|- Impl phi psi`, exhibit an interpolant `chi` whose free variables and Box-levels are contained in the intersection of those of `phi` and `psi`.
24. Prove Lyndon interpolation: the interpolant additionally preserves polarity of variable occurrences.
25. Prove uniform interpolation: for every `phi` and variable `p`, exhibit `phi_p` not containing `p` such that for every `psi` not containing `p`, `|- Impl phi psi <-> |- Impl phi_p psi`.
26. Prove Beth definability in its full form: every implicitly definable predicate is explicitly definable.

## Bisimulation + frame characterisation

27. Prove the unconditional reverse direction of van Benthem: every bisimulation-invariant first-order property over ω-saturated models is modally definable.
28. Strengthen `is_modal_definable` to require the witnessing formula to land in a syntactically restricted fragment matching the property's intended class; restate the bisim-invariance theorems on the strengthened predicate.
29. Prove the full Goldblatt-Thomason theorem characterizing modally-definable frame classes.
30. Prove Sahlqvist correspondence in its general form (not just for K, Löb).
31. Prove the polymodal Fine-Schurz incompleteness result identifying GLP*-formulas not derivable in any Kripke-complete sub-logic.

## Arithmetic Bew + Solovay

32. Construct a genuine arithmetic Σ₁ provability predicate `Bew_PA` over a Gödel-encoded fragment of arithmetic (formulas as numerals, proofs as numerals); prove the Hilbert-Bernays-Löb conditions for it.
33. Prove arithmetic completeness of GL (Solovay's first theorem) at every level, not just the box-free fragment.
34. Prove Solovay's second completeness theorem for the truth-extension `Provable_S` beyond the box-free fragment.
35. Prove arithmetic completeness of `Provable_GLP` (Japaridze's theorem) for arbitrary formulas, not just box-free ones.
36. Construct a genuinely non-identity, non-licensure inhabitant of `is_arithmetic_interpretation` to show the predicate has non-trivial structure beyond `identity` and `licenses k`.
37. Prove the Friedman-Sheard truth-axiomatization theorem.
38. Prove Tarski undefinability in its sharpest form: no formula `Tr(x)` in the language of GLP* with one free variable satisfies `|- Iff (Tr(phi-code)) phi` for all `phi`.

## First-order tower

39. Construct a first-order theory `T_n` with explicit axioms (not just modal axiom-schemas via `T_axiom`); prove the cumulativity, consistency, and tiling results at the genuine first-order level.
40. Prove Π₁ conservativity of `T_(n+1)` over `T_n` for arithmetic Π₁ sentences.
41. Prove Π₂ conservativity across the tower.
42. Prove Friedman's negative translation result connecting classical to constructive provability beyond the box-free case.
43. Prove the relative-consistency direction `Con(T_0) → Con(T_n)` from a strictly weaker hypothesis than meta-consistency of the full system.
44. Prove `T_no_self_consistency` directly from `Bew`'s HBL conditions rather than routing through the full Provable calculus.
45. Prove the strict separation between `Bew n` and `Bew (S n)` at the proof level (not just at the axiom-set level).
46. Prove that the structural `Bew` predicate satisfies provability logic (i.e., `Bew n` interpreted into `Box n` validates exactly GLP* at the relevant level).

## Critch + Fallenstein-Soares

47. Prove the Critch parametric bounded-Löb theorem for a genuinely bounded provability predicate (with proof-length bound encoded inside the modal formula), not just iterated Box.
48. Prove the Critch correspondence between modal `critch_bounded_box` and a genuine bounded-arithmetic provability predicate with explicit polynomial bounds.
49. Prove the Fallenstein-Soares 2014 finite-tower self-modification theorem at the arithmetic level: a `T_n`-using agent provably-safely transitions to a `T_(n+1)`-using agent.
50. Prove the Pudlák speedup result for the parametric tower at every level (super-polynomial in proof length when ascending the hierarchy).
51. Prove a quantitative version of the Löbian obstacle: bound the proof length of the inconsistency derivation by a function of the reflection-schema's proof complexity.

## Agents + cooperation

52. Define `FairBot n psi := psi := Box n (Iff (opp psi) Cooperate)` as a real Sambin fixed point where `opp` reads from the open variable; prove existence via `fixed_point_existence_top_solves` applied to the modalized self-referential formula.
53. Define `PrudentBot n psi` as a real Sambin fixed point with the consistency conjunct `Box (S n) (Neg (Box n Bot))`.
54. Prove FairBot vs FairBot mutual cooperation with the genuine fixed-point semantics.
55. Prove FairBot vs DefectBot defection.
56. Prove the BCFHLY robust-cooperation theorem for non-trivial fixed points (not just the collapse to `Top`).
57. Prove that PrudentBot strictly dominates FairBot in modal-PD against DefectBot, exhibiting concrete formula witnesses.
58. Prove the goal-preservation tiling theorem for an agent that takes non-trivial actions changing the state.
59. Prove vingean reflection in a setting where the agent's decision genuinely depends on `T_(n+1)` licensure (not vacuously satisfied by `cautious_agent`).
60. Prove the no-panic reflective-trust theorem at the level of self-modifying agents, not just modal consistency.
61. Prove the `T_kappa` agent-correspondence theorem with a non-trivial agent architecture.
62. Prove Aumann's agreement theorem in modal form: agents at different levels with common knowledge of consistency provably agree.

## Worms + ordinal analysis

63. Prove Beklemishev's worm normal form theorem for `Provable_GLP` (where worms are not all provable), not just the trivial collapse in `Provable`.
64. Prove the proof-theoretic ordinal of `Provable_GLP` is exactly ε₀ via a complete ordinal-assignment to proof terms with strict decrease under reduction.
65. Replace the syntactic `Veblen_phi_iter` and `Gamma_0_approx` shells with the genuine Veblen hierarchy as ordinal functions; prove their fixed-point properties.
66. Prove Carlson's theorem on the ordinal-analysis correspondence between worms and ordinals below ε₀.
67. Prove Carlson's theorem (second incompleteness for polymodal provability) in its sharp form.
68. Prove the explicit ε₀-rank-respecting normalization theorem for proof terms with strict ordinal decrease (currently `proof_term_ordinal` is defined but no decrease theorem under reduction is proved).

## Algebraic + categorical

69. Prove Magari algebra completeness: the Lindenbaum-Tarski algebra is the free Magari algebra on the propositional variables.
70. Prove Jónsson-Tarski duality between the Lindenbaum-Tarski algebra and the canonical frame.
71. Prove a genuine categorical-semantics theorem: define a category of GLP*-frames with bisimulation-respecting morphisms; prove `Provable` corresponds to global sections of a sheaf or similar structure.
72. Strengthen `licenses_axiomatic_uniqueness` to derive its bounds from a categorical universal property — uniqueness as the unique-up-to-provable-equivalence functor preserving `|-` and admitting `Ax_BoxK`, `Ax_Loeb`, `Ax_Mon`.
73. Prove `licenses_axiomatic_uniqueness` extends to non-extensional candidate operators via a categorical universal property.

## Quantified + temporal + probabilistic + neighborhood

74. Prove constant-domain QGLP* soundness and completeness with respect to a Kripke-style first-order semantics for quantified modal formulas.
75. Prove the Barcan and converse-Barcan formulas hold or fail in the quantified extension, with semantic witnesses.
76. Prove a genuine temporal-extension result where time and modal level interact non-trivially (e.g., temporal succession changes the proof-theoretic ordinal).
77. Prove a probabilistic-Löb theorem with a real probability parameter (not just nat) showing graded reflection survives at strictly positive ε.
78. Construct a proper neighborhood-semantics framework; prove soundness/completeness for a non-normal modal logic separating it from GLP*.

## Decision procedures + lower bounds

79. Prove decidability of admissible rules (Rybakov's theorem) for at least the box-free fragment, with a real decision procedure rather than a vacuous skeleton.
80. Prove a decidability result for the bimodal `Box n + Box m` fragment with `n ≠ m` distinct from the full polymodal case.
81. Prove the existence of a finite refuting frame for every specific non-theorem (not just `Box n Bot`).
82. Replace `lindenbaum_extend` (which uses `excluded_middle_informative`) with a constructive Lindenbaum construction over a decidable theory.
83. Prove a proper Kalmár-style completeness for the `Sigma1_modal` closure (not just box-free).

## Reflection Calculus + closed fragments

84. Prove the full Reflection Calculus completeness theorem for strictly positive formulas.
85. Prove decidability of the closed (variable-free) fragment with explicit complexity bounds via filtration.
86. Prove the Abashidze-Japaridze characterization of the closed fragment of `Provable_GLP`.
87. Prove the omega-completeness of `Fnat`: every formula true at every world of `Fnat` is provable.
88. Prove the Henkin-style truth lemma over the canonical model for the modal fragment, not just propositional cases.

## Visser interpretability

89. Prove the Visser interpretability logic ILM/ILP axioms beyond just the K-distribution and Box4 forms.
90. Prove the Visser ILM J5 axiom from the calculus axioms rather than via `Ax_Mon`.

## Disjunction + polymodal extensions

91. Prove the disjunction property for `Provable_GLP`: if `|- Or (Box n phi) (Box m psi)` then `|- Box n phi` or `|- Box m psi`.
92. Prove that `Provable_GLP_incomparable_with_provable` extends to infinitely many incomparable formulas, witnessing genuine logical separation.
93. Prove a no-go theorem for any uniform strengthening of `Ax_NextCon` to `Box n (Neg (Box n Bot))` across all levels.
94. Prove that the `Provable_plus` extension scheme yields inconsistency for any reflection-schema extension at any level uniformly.
95. Prove the reverse direction of `licensing_consistency_concrete_converse` quantifying over all formulas at level n simultaneously.
96. Prove the Smoryński bimodal independence theorem at distinct levels for non-trivial formulas.

## Conservativity + translation

97. Prove the full conservativity of `Provable_GL` over `Provable` at level 0 in both directions (currently only one direction is fully proved without using the trivial `forget_levels` collapse).
98. Prove the polymodal-fixed-point system completeness à la Smoryński.

## Final hygiene (do these last, when content is stable)

99. Split `Tiling.v` into themed modules — `Calculus`, `Hilbert`, `Kripke`, `FixedPoints`, `Bew`, `ProofTerms`, `Worms`, `Agents` — keeping the dependency DAG acyclic.  Update `_CoqProject` and `Makefile`.
100. Add `Examples.v` with three worked examples: consistency-of-PA from consistency-of-Q in the modal abstraction; Gödel's second incompleteness specialised to a concrete formula; an agent-tower with a non-cautious agent that uses `Bew (S n)` licensure.
101. Add `README.md` listing the headline theorems, dependency story, and build instructions.
