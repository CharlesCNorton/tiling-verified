# tiling-verified todo

Ordered so that each item's prerequisites appear earlier.

1. Replace Ax_Box4 as a primitive axiom with a derived theorem in Provable itself (not just in Provable_no_B4), using nb4_axiom4's argument inlined.
2. Prove the de Jongh-Sambin fixed-point theorem in full generality: for every phi(p) with modalized p phi, exhibit psi with |- Iff psi (Subst p psi phi).
3. Prove the uniqueness half of de Jongh-Sambin: any two fixed points of the same modalized formula are provably equivalent.
4. Construct a genuine arithmetic Σ₁ provability predicate Bew_PA over a Gödel-encoded fragment of arithmetic (formulas as numerals, proofs as numerals) and prove the Hilbert-Bernays-Löb conditions for it, replacing the structural Bew_arith.
5. Prove the arithmetic completeness of GL (Solovay's first theorem) at every level, not just the box-free fragment.
6. Prove Solovay's second completeness theorem for the truth-extension Provable_S beyond the box-free fragment.
7. Prove arithmetic completeness of Provable_GLP (Japaridze's theorem) for arbitrary formulas, not just box-free ones.
8. Prove the unconditional reverse direction of van Benthem's theorem: every bisimulation-invariant first-order property over ω-saturated models is modally definable.
9. Prove the full Goldblatt-Thomason theorem characterizing modally-definable frame classes.
10. Prove cut-elimination for a sequent presentation of GLP* (build the sequent calculus first, then prove cut admissibility structurally).
11. Prove full Craig interpolation for GLP*: for every |- Impl phi psi, exhibit an interpolant chi whose free variables and Box-levels are contained in the intersection of those of phi and psi.
12. Prove Lyndon interpolation: the interpolant additionally preserves polarity of variable occurrences.
13. Prove uniform interpolation: for every phi and variable p, exhibit phi_p not containing p such that for every psi not containing p, |- Impl phi psi <-> |- Impl phi_p psi.
14. Prove Beth definability in its full form: every implicitly definable predicate is explicitly definable.
15. Prove the canonical-model truth lemma for the full modal language, not just for variables and Bot.
16. Prove Kripke completeness of GLP* with respect to its frame class (every non-theorem is refuted by some GLP*-frame).
17. Prove the finite frame property: every non-theorem is refuted by a finite GLP*-frame.
18. Prove decidability of the full polymodal calculus via filtration.
19. Prove PSPACE-completeness of GLP* satisfiability/provability.
20. Prove independence of Ax_K using non-Kripke (e.g. neighborhood) semantics.
21. Construct a first-order theory T_n with explicit axioms (not just modal axiom-schemas via T_axiom) and prove the cumulativity, consistency, and tiling results at the genuine first-order level.
22. Prove the Critch parametric bounded-Löb theorem for a genuinely bounded provability predicate (with proof-length bound encoded inside the modal formula), not just iterated Box.
23. Prove the Fallenstein-Soares 2014 finite-tower self-modification theorem at the arithmetic level: a T_n-using agent provably-safely transitions to a T_(n+1)-using agent.
24. Prove Π₁ conservativity of T_(n+1) over T_n for arithmetic Π₁ sentences.
25. Prove Π₂ conservativity of the appropriate kind across the tower.
26. Prove Friedman's negative translation result connecting classical to constructive provability beyond the box-free case.
27. Prove the disjunction property for Provable_GLP: if |- Or (Box n phi) (Box m psi) then |- Box n phi or |- Box m psi.
28. Prove Carlson's theorem (second incompleteness for polymodal provability) in its sharp form.
29. Prove Pudlák's super-polynomial speedup theorem at the proof-length level (with explicit bounds).
30. Prove that the proof-theoretic ordinal of Provable_GLP is exactly ε₀ via a complete ordinal-assignment to proof terms with strict decrease under reduction.
31. Replace the syntactic Veblen_phi_iter and Gamma_0_approx shells with the genuine Veblen hierarchy as ordinal functions and prove their fixed-point properties.
32. Prove Beklemishev's worm normal form theorem for Provable_GLP (where worms are not all provable), not just the trivial collapse in Provable.
33. Prove the Visser interpretability logic ILM/ILP axioms beyond just the K-distribution and Box4 forms.
34. Prove Magari algebra completeness: the Lindenbaum-Tarski algebra is the free Magari algebra on the propositional variables.
35. Prove Jónsson-Tarski duality between the Lindenbaum-Tarski algebra and the canonical frame.
36. Prove Sahlqvist correspondence in its general form (not just for the specific axioms K, Löb).
37. Prove decidability of admissible rules (Rybakov's theorem) for at least the box-free fragment, with a real decision procedure rather than a vacuous skeleton.
38. Prove the full Reflection Calculus completeness theorem for strictly positive formulas.
39. Prove Carlson's theorem on the ordinal analysis correspondence between worms and ordinals below ε₀.
40. Construct a proper neighborhood-semantics framework and prove soundness/completeness for a non-normal modal logic separating it from GLP*.
41. Prove a genuine categorical-semantics theorem: define a category of GLP*-frames with bisimulation-respecting morphisms and prove Provable corresponds to global sections of a sheaf or similar structure.
42. Prove constant-domain QGLP* soundness and completeness with respect to a Kripke-style first-order semantics for quantified modal formulas.
43. Prove the Barcan and converse-Barcan formulas hold or fail in the quantified extension, with semantic witnesses.
44. Prove a genuine temporal-extension result where time and modal level interact non-trivially (e.g., temporal succession changes the proof-theoretic ordinal).
45. Prove a probabilistic-Löb theorem with a real probability parameter (not just nat) showing graded reflection survives at strictly positive ε.
46. Prove Aumann's agreement theorem in modal form: agents at different levels with common knowledge of consistency provably agree.
47. Prove the BCFHLY robust-cooperation theorem for non-trivial fixed points (not just the collapse to Top), with FairBot/PrudentBot defined with genuine self-reference rather than constants.
48. Prove that PrudentBot strictly dominates FairBot in modal-PD against DefectBot, exhibiting concrete formula witnesses.
49. Prove Tarski undefinability in its sharpest form: no formula Tr(x) in the language of GLP* with one free variable satisfies |- Iff (Tr(phi-code)) phi for all phi.
50. Construct a genuinely non-identity, non-licensure inhabitant of is_arithmetic_interpretation to show the predicate has non-trivial structure.
51. Prove the Friedman-Sheard truth-axiomatization theorem.
52. Prove the Smoryński bimodal independence theorem at distinct levels for non-trivial formulas.
53. Prove the full conservativity of Provable_GL over Provable at level 0 in both directions (currently only one direction is fully proved without using the trivial forget_levels collapse).
54. Prove the Goldblatt translation faithfulness for a non-trivial translation (the current Goldblatt_translation is the identity).
55. Prove Maehara's lemma constructively: extract a constructive interpolant from a cut-free proof.
56. Prove the omega-completeness of Fnat: every formula true at every world of Fnat is provable.
57. Prove the Henkin-style truth lemma over the canonical model for the modal fragment, not just propositional cases.
58. Prove decidability of the closed (variable-free) fragment with explicit complexity bounds via filtration.
59. Prove the Abashidze-Japaridze characterization of the closed fragment of Provable_GLP.
60. Prove the explicit ε₀-rank-respecting normalization theorem for proof terms with strict ordinal decrease (currently proof_term_ordinal is defined but no decrease theorem under reduction is proved).
61. Replace the size-based pt_reduces_decreases_size with a genuine reduction relation that actually performs proof-term simplification (β-reduction analog for Hilbert-style proofs).
62. Prove confluence of the proof-term reduction relation.
63. Prove strong normalization of proof-term reduction in its full form (not just well-foundedness of the size order).
64. Prove the Visser ILM J5 axiom from the calculus axioms rather than via Ax_Mon.
65. Prove a non-trivial Lyndon interpolation theorem with polarity preservation actually checked.
66. Prove the existence of a finite refuting frame for every specific non-theorem (not just Box n Bot).
67. Replace lindenbaum_extend (which uses excluded_middle_informative) with a constructive Lindenbaum construction over a decidable theory.
68. Prove that the formula enumeration enum_form is a bijection between nat and Form (currently encoding/decoding correctness is not proved).
69. Prove decode_form (encode_form phi) = phi for the Gödel numbering.
70. Prove cunpair (cpair a b) = (a, b) for the Cantor pairing (currently not proved).
71. Prove find_root_correct in its full form establishing it returns the genuine root of the triangle inequality.
72. Prove the relative-consistency direction Con(T_0) → Con(T_n) from a strictly weaker hypothesis than meta-consistency of the full system.
73. Prove T_no_self_consistency directly from Bew's HBL conditions rather than routing through the full Provable calculus.
74. Prove the strict separation between Bew n and Bew (S n) at the proof level (not just at the axiom-set level).
75. Prove that the structural Bew predicate satisfies provability logic (i.e., Bew n interpreted into Box n validates exactly GLP* at the relevant level).
76. Prove the T_kappa agent-correspondence theorem with a non-trivial agent architecture (not the cautious-agent stub that always succeeds).
77. Prove the goal-preservation tiling theorem for an agent that actually takes non-trivial actions changing the state.
78. Prove vingean reflection in a setting where the agent's decision genuinely depends on T_(n+1) licensure (not vacuously satisfied by cautious_agent).
79. Prove the no-panic reflective-trust theorem at the level of self-modifying agents, not just modal consistency.
80. Replace the truth-table-based eval_provable_true consistency proof with a cut-elimination-based syntactic proof.
81. Prove Kripke completeness for Provable_no_NC, Provable_no_Mon, Provable_no_Loeb, Provable_no_B4 separately with their distinguishing frame classes.
82. Prove that each axiom-removal calculus is strictly weaker than Provable for infinitely many distinct theorems (not just one).
83. Prove a quantitative version of the Löbian obstacle: bound the proof length of the inconsistency derivation by a function of the reflection-schema's proof complexity.
84. Prove the polymodal Fine-Schurz incompleteness result identifying GLP*-formulas not derivable in any Kripke-complete sub-logic.
85. Prove a decidability result for the bimodal Box n + Box m fragment with n ≠ m distinct from the full polymodal case.
86. Prove that licenses_axiomatic_uniqueness extends to non-extensional candidate operators via a categorical universal property.
87. Prove the Critch correspondence between modal critch_bounded_box and a genuine bounded-arithmetic provability predicate with explicit polynomial bounds.
88. Prove the Pudlák speedup result for the parametric tower at every level (super-polynomial in proof length when ascending the hierarchy).
89. Prove fixed-point existence for phi(p) := Neg (Box n (Var p)) (the Gödel-sentence case) — this is the simplest non-Top-solving case currently not handled.
90. Prove fixed-point existence for phi(p) := Impl (Box n (Var p)) X for arbitrary X not containing p — this is the Henkin-sentence case.
91. Prove fixed-point existence for phi(p) := And X (Box n (Var p)) and other compound modalized contexts.
92. Prove the substitution composition lemma's converse direction.
93. Prove that modalized is preserved under all calculus operations.
94. Prove a proper Kalmar-style completeness for the Sigma1_modal closure (not just box_free).
95. Prove Solovay completeness of Provable_S extending Provable_GL with the truth axiom on the full modal fragment.
96. Prove the polymodal-fixed-point system completeness à la Smoryński.
97. Prove that Provable_GLP_incomparable_with_provable extends to infinitely many incomparable formulas, witnessing genuine logical separation.
98. Prove a no-go theorem for any uniform strengthening of Ax_NextCon to Box n (Neg (Box n Bot)) across all levels (this is tiling_strongest but for arbitrary psi schemata).
99. Prove that the Provable_plus extension scheme yields inconsistency for any reflection-schema extension at any level uniformly.
100. Prove the reverse direction of licensing_consistency_concrete_converse quantifying over all formulas at level n simultaneously.
