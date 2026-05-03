# tiling-verified todo

Ordered so that each item's prerequisites appear earlier.

1. Prove K independence from {Löb, Mon, NextCon, Box4} by exhibiting a non-Kripke (neighborhood-style) model validating the other axioms and refuting K, completing the mutual-independence package beyond Kripke semantics.
2. Prove the van Benthem characterisation: the bisimulation-invariant fragment of first-order logic over Frame structures is exactly the polymodal language.
3. Prove a topological-completeness theorem via scattered spaces (Beklemishev-Esakia style).
4. Define polytopological semantics for GLP* in the Beklemishev-Gabelaia style and prove soundness.
5. Prove a Lindenbaum lemma: every consistent set of formulas extends to a maximal consistent set.
6. Construct the canonical model for Provable and prove the truth-lemma.
7. Prove a Henkin-style construction extending consistent sets to satisfiable models.
8. Prove a Kripke-model completeness theorem for the polymodal fragment used: Valid phi -> |- phi.
9. Resolve the Kripke-completeness question for GLP*: complete item 8 for the full calculus, or refute it by exhibiting a Kripke-valid non-theorem.
10. Prove a Kripke-completeness or topological-completeness theorem for GLP*-with-monotonicity-and-NextCon.
11. Prove full Kripke completeness for the no-NextCon calculus Provable_no_NC against the wider class of no-NC frames.
12. Prove the file's tower is conservative over single-level GL at level 0.
13. Prove the finite frame property: every non-theorem of Provable is refuted by some finite Frame.
14. Extract from Kripke soundness a model-search procedure that, given a non-theorem, produces a refuting Frame.
15. Prove decidability of |- phi for the single-level modal fragment using filtration.
16. Define the closed (variable-free) fragment and prove its decidability and normal form.
17. Prove decidability of the full polymodal calculus GLP*; extract to OCaml.
18. For each k, define Provable_k restricting Box to levels ≤ k; prove its decidability.
19. Prove a model-theoretic forcing theorem: closure under disjoint unions and generated submodels.
20. Prove a cut-elimination theorem for a sequent presentation of GLP*.
21. Prove the cut-elimination theorem yields a syntactic proof of ~(|- Bot).
22. Prove a normalization theorem for Provable.
23. Prove that every theorem of Provable has a derivation of bounded modal depth.
24. Prove the Beklemishev worm normal form algorithm.
25. Prove worm-translation: define worms as Form objects with linear ordering by provable implication.
26. Prove Craig interpolation for GLP*.
27. Prove Beth definability for GLP* by deriving it from Craig interpolation.
28. Prove a fixed-point theorem within GLP*: for every modalised phi(p), exhibit psi with |- Iff psi (phi(psi)).
29. Prove the resulting fixed points are unique up to provable equivalence.
30. Prove the polymodal de Jongh-Sambin fixed-point theorem.
31. Prove fixed-point functoriality.
32. Prove a fixed-point uniqueness theorem for solutions at the same level.
33. Prove the full strictly-stronger claim for the Japaridze axiom.
34. Prove conservativity into full GLP.
35. Define the reflection algebra of Provable and prove it forms a GLP-algebra.
36. Define a categorical semantics: the category of Frames with bisimulation morphisms.
37. Prove that the consistency chain forms a cofibered diagram of theories indexed by ω.
38. Prove that the agent licensure layer factors through a free construction.
39. Prove a recursion theorem for the agent licensure layer.
40. Define the Σ_α / Δ_α decomposition from YH 2013 §5.2 and prove tiling preserves it.
41. Prove a naturalistic-trust theorem (YH 2013's fourth desideratum).
42. Define an updateless decision-theoretic agent and prove tiling preserves the action criterion.
43. Encode FairBot and PrudentBot as Form-level objects; prove robust-cooperation theorem.
44. Construct the procrastination paradox as a Form, prove derivability under naive axioms, and prove T_κ blocks it.
45. Define Box_n^k for proofs of length ≤ k, prove bounded Löb, prove reduction to Ax_Loeb in the limit.
46. Prove the connection to Critch's parametric bounded Löb (JSL 2019).
47. Prove the precise Critch correspondence at proof level.
48. Prove the Hilbert-Bernays-Löb derivability conditions for a concrete encoded Bew_n.
49. Prove that the file's results are robust under adding a truth predicate Tr_n + Tarski biconditionals.
50. Prove a self-application theorem.
51. Prove Ax_NextCon arithmetically: construct concrete T_n, T_(n+1) such that T_(n+1) derives Con(T_n).
52. Prove Ax_Mon arithmetically.
53. Construct T_κ as a first-order theory in the YH 2013 §3 sense.
54. Define the parametric tower with κ as a Form-level parameter.
55. Prove soundness of T_κ at each standard κ ∈ N.
56. Prove the tiling theorem proper: A_α using T_κ derives safety of A_(α-1) using T_(κ-1).
57. Define ZF_τ-style set-theoretic licensure (YH 2013 §6).
58. Prove an arithmetic soundness bridge I : Form -> Arith.
59. Prove the bridge faithful at level 0.
60. Prove arithmetical soundness of the polymodal calculus.
61. Prove a Σ_1-soundness theorem.
62. Prove a Π_1-conservativity theorem matching Fallenstein 2013.
63. Prove the Π_2-conservativity of every level over its predecessor.
64. Prove a Friedman-translation analog.
65. Prove a Solovay-style arithmetic completeness theorem for the level-0 fragment.
66. Prove Solovay completeness for the full polymodal calculus.
67. Prove the polymodal extension is arithmetically complete relative to the Beklemishev hierarchy.
68. Prove a reflection-schema classification theorem.
69. Prove a reflection-principle hierarchy theorem.
70. Prove a strict per-level hierarchy theorem.
71. Prove that the proof-theoretic ordinal of GLP* equals the value predicted by Beklemishev's worm-ordinal analysis.
72. Prove the connection to Beklemishev's iterated-reflection hierarchy.
73. Prove a temporal-extension procrastination bypass theorem: extend GLP* with "do action a at time t".
74. Prove a Visser-style interpretability logic embedding.
75. Prove a bimodal Σ_1-vs-general provability extension (Smoryński-style).
76. Construct a quantified polymodal logic QGLP* and prove its core metatheorems and completeness.
77. Prove a deduction theorem with necessitation under modal-closure side conditions.
78. Prove a transfinite Löb metatheorem for ordinals α < ε_0.
79. Prove a transfinite consistency chain.
80. Prove the file's results extend to transfinite levels: define Box_α and prove tiling_consistency lifts.
81. Construct uniform Box_α machinery.
82. Prove the transfinite extension recovers the full Beklemishev GLP system.
83. Define a graded modality [Bel ≥ p]_n; prove unbounded reflection schema collapses; ε-tolerant variant survives.
84. Construct a probabilistic agent licensure extension and prove a probabilistic YH bypass.
85. Prove a complexity bound: membership in Provable is decidable in PSPACE.
86. Prove PSPACE-hardness of the variable-free fragment.
87. Define a proof-term calculus and prove every closed proof term normalises.
88. Prove the proof-term normal forms are unique up to a specified equational theory.
89. Prove an extracted certified verifier: extract from Provable an OCaml proof-checker.
90. Prove verifier completeness: every Provable closed formula is accepted by the extracted checker.
