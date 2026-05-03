# tiling-verified todo

Ordered so that each item's prerequisites appear earlier.

1. Prove a Diamond-elimination theorem: every Diamond-involving theorem of GLP* admits a Box-only proof under the standard definitional translation, eliminating Diamond as a derived rather than primitive modality.
2. Prove substitution: define Subst p psi phi and prove |- phi -> |- Subst p psi phi, so that schematic theorems are theorems of the calculus rather than artifacts of Coq's parametric polymorphism.
3. Prove the replacement congruence: |- Iff phi psi implies |- Iff (Subst p phi chi) (Subst p psi chi), generalizing licenses_subst beyond the licensure layer.
4. Prove the iff form of Löb: |- Iff (Box n phi) (Box n (Impl (Box n phi) phi)).
5. Prove a finite-axiomatisation theorem: GLP* is equivalent to a finite, non-schematic axiom system together with substitution and modus ponens, isolating finitely many axiom carriers whose substitution closure recovers exactly Provable.
6. Construct the Lindenbaum-Tarski algebra of GLP* and prove it is non-degenerate, giving an algebraic completeness counterpart to meta_consistency_system that is provably independent of the trivial-truth-assignment argument.
7. Define a notion of "trivial" theorem (a theorem whose derivation uses no modal axioms) and prove the trivial fragment coincides with classical propositional logic.
8. Prove a uniform-witness theorem for tiling_consistency: extract from the proof a uniform Coq term f such that f n phi : |- Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi)))), making explicit that the schema is delivered by a single derivation.
9. Prove a level-indexed Gödel-Rosser theorem: for every n there is a formula phi with ~(|- Box n phi) and ~(|- Box n (Neg phi)), establishing that level-n provability is genuinely incomplete in the Gödel sense at every level.
10. Prove a frame-condition independence theorem: each of the four Frame conditions (transitivity, converse-well-foundedness, monotone inclusion fR (S n) ⊆ fR n, NextCon successor existence) is independent of the others, by exhibiting four counter-frames each violating one condition while satisfying the rest.
11. Prove independence of Ax_Mon by exhibiting a frame validating the other axioms and refuting a monotonicity-essential theorem, paralleling consistency_chain_needs_NC.
12. Prove independence of Ax_Box4: either exhibit a frame validating K, Löb, Mon, NextCon and refuting Box4, or, once axiom 4 is derived from K+Löb, show that dropping Box4 yields the same theorems.
13. Prove mutual independence of {K, Löb, Mon, NextCon, Box4} by exhibiting, for each axiom, a frame validating the other four and refuting it.
14. Collect mon_converse_fails, reflection_at_same_level_unprovable_uniformly, strict_extension_at_each_level, and analogous results into a single failure_catalog theorem with refuting frames.
15. Prove bisimulation invariance for forces and a van Benthem characterisation: GLP* captures exactly the bisimulation-invariant fragment of first-order logic over Frame structures.
16. Define n-bisimulation on Frames and prove forces is bisimulation-invariant.
17. Prove an encoding theorem: every finite Frame is the underlying frame of some explicit recursive construction, supporting model-checking-style certified refutations.
18. Prove the finite frame property: every non-theorem is refuted by a finite Frame.
19. Extract from the Kripke soundness proof a model-search procedure that, given a non-theorem, produces a refuting Frame.
20. Prove decidability of |- phi for the propositional-only fragment (no Box), giving a decision procedure extracted to OCaml.
21. Implement a reflective tactic that closes propositional-fragment goals automatically by appeal to the propositional decision procedure.
22. Prove decidability of |- phi for the single-level modal fragment using filtration on Kripke models.
23. Define the closed (variable-free) fragment and prove its decidability and normal form, paralleling Beklemishev-Joosten-Vervoort for GLP.
24. Prove decidability of the full polymodal calculus GLP*: extend Beklemishev's decision procedure for GLP to handle the cross-level monotonicity and NextCon axioms; extract to OCaml.
25. For each k, define Provable_k restricting Box to levels ≤ k, prove its decidability via the full decision procedure, and prove every Box i ≤ k theorem of Provable is a theorem of Provable_k.
26. Prove a compactness theorem for Provable: if every finite subset of an axiom extension is consistent, so is the extension.
27. Prove a Lindenbaum lemma: every consistent set of formulas extends to a maximal consistent set, as infrastructure for the canonical-model construction.
28. Construct the canonical model for Provable and prove the truth-lemma, completing the standard route to Kripke completeness.
29. Prove a Henkin-style construction: from a consistent extension of Provable, build a Frame in which it is satisfiable, refining the canonical-model construction to handle modal hypotheses.
30. Prove the file's tower is conservative over single-level GL at level 0: every Box 0-only formula |- phi here is provable in standard Gödel-Löb logic.
31. Prove a Kripke-model completeness theorem for the polymodal fragment used: Valid phi -> |- phi, restricted to the axioms actually in Provable.
32. Resolve the Kripke-completeness question for GLP*: complete the previous Kripke-completeness item, or refute it by exhibiting a Kripke-valid non-theorem.
33. Prove a Kripke-completeness or topological-completeness theorem for the specific axiomatization (GLP-with-monotonicity-and-NextCon), since this combination is not literally GLP and its semantic characterization is not immediate from existing results.
34. Prove a topological-completeness theorem via scattered spaces (Beklemishev-Esakia style): every theorem of GLP* is valid on a scattered topology, and validity on every such topology entails provability.
35. Define polytopological semantics for GLP* in the Beklemishev-Gabelaia style and prove soundness, anticipating Kripke-incompleteness inherited from GLP.
36. Prove full Kripke completeness for the no-NextCon calculus Provable_no_NC against the wider class of no-NC frames, extending the existing single counter-model to a full completeness theorem.
37. Prove a model-theoretic forcing theorem for Provable: the class of frames validating a theory is closed under disjoint unions and generated submodels.
38. Formalize the full Japaridze axiom Impl (Diamond n phi) (Box (S n) (Diamond n phi)) and prove it strictly stronger than Ax_NextCon: unprovable in Provable, but consistent with it.
39. Prove conservativity into full GLP: define Provable_GLP with the Japaridze axiom replacing NextCon, and prove |- phi -> Provable_GLP phi.
40. Prove a separation theorem distinguishing Provable from Provable_no_NC at every level n ≥ 1: exhibit a formula provable at level n in Provable but not in Provable_no_NC.
41. Prove the analog of separation for Provable_no_Mon and any future Provable_no_Box4.
42. Prove a cut-elimination theorem for a sequent presentation of GLP* equivalent to Provable, following the Goré-Ramanayake style.
43. Prove the cut-elimination theorem of (42) yields a syntactic proof of ~ (|- Bot), removing the dependence on Kripke semantics for global consistency.
44. Prove a normalization theorem for Provable: every derivation reduces to a canonical form, enabling decidability arguments for fragments.
45. Prove that every theorem of Provable has a derivation of bounded modal depth depending only on the Box-levels appearing in the conclusion, anticipating cut-elimination.
46. Prove the Beklemishev worm normal form algorithm: every GLP*-formula is provably equivalent to a unique worm under Beklemishev normalisation, with a Coq decision procedure for the equivalence.
47. Prove worm-translation: define worms (sequences of Box indices applied to ⊤) as Form objects and prove the linear ordering of worms by provable implication.
48. Prove Craig interpolation for GLP*: for every theorem |- (Impl phi psi), exhibit chi over only the propositional variables and Box-levels appearing in both phi and psi, with |- (Impl phi chi) and |- (Impl chi psi).
49. Prove Beth definability for GLP* by deriving it from Craig interpolation: every implicit definition of a propositional variable in the calculus is explicit.
50. Prove a fixed-point theorem within GLP*: for every phi(p) with p occurring only inside Box, exhibit psi with |- Iff psi (phi(psi)), the polymodal analogue of the GL fixed-point theorem.
51. Prove the resulting fixed points are unique up to provable equivalence at the level the box is taken.
52. Prove a fixed-point theorem for the polymodal calculus, in the de Jongh-Sambin style, so that self-referential modal sentences have provable explicit fixed points.
53. Prove fixed-point functoriality: the polymodal fixed points are functorial over substitution and unique not merely up to provable equivalence but up to definable transformations between fixed-point indices.
54. Prove a fixed-point uniqueness theorem distinct from the same-level uniqueness: any two solutions of phi(p) at the same level are provably equivalent at every higher level.
55. Prove |- Impl (Box n phi) (Box n (Box n phi)) (axiom 4) as a derived theorem from K + Löb, following Boolos Theorem 11 via the polymodal fixed-point theorem of (52), demoting Ax_Box4 from a primitive axiom to a derived theorem.
56. Prove that tiling_consistency is the strongest such property: any formula psi(n, phi) provable at Box (S n) and stronger than Impl (Box n phi) (Neg (Box n (Neg phi))) collapses the system.
57. Prove a no-go theorem locating the file's calculus precisely: there is no extension of Provable by a single uniform schema that proves same-level reflection without becoming inconsistent, a strengthening of reflection_schema_unprovable.
58. Prove a "minimal viable bypass" theorem: removing any axiom from {K, Löb, Mon, NextCon} either trivializes the calculus or fails to prove tiling_consistency, identifying the four-axiom set as minimal for the YH bypass.
59. Prove robustness of yh_bypass_summary under axiomatization perturbations: dropping any single non-essential axiom preserves the bypass.
60. Define the reflection algebra of Provable as a quotient of Form by provable equivalence and prove it forms a GLP-algebra.
61. Define a categorical semantics: the category of Frames with bisimulation morphisms, and prove Provable is sound and complete with respect to its terminal object.
62. Prove that the licensure layer is functorial: cross-level licensure composition (Theorem licenses_compose_cross) is the morphism action of a functor from a level-indexed category to Form.
63. Prove that the consistency chain forms a cofibered diagram of theories indexed by ω, and that the file's tower is its limit object.
64. Prove that the agent licensure layer factors through a free construction: define a syntactic category of agents with morphisms = licensing-preserving maps, and prove licenses : nat → Form → Form is the free such functor.
65. Prove a recursion theorem for the agent licensure layer: licensing decisions defined by structural recursion on Form preserve licensing-consistency.
66. Define a notion of agent extensional equivalence (two agents licensing the same Forms at every level) and prove tiling_consistency is invariant under it.
67. Define and prove a distinction between de re and de dicto licensure: |- Box n (∃ phi. Box m phi) versus ∃ phi. |- Box n (Box m phi), and prove which YH-style results require which.
68. Extend Provable with sensor-licensure rules and prove tiling_consistency, consistency_chain, and joint_licensing_consistency_list survive the extension.
69. Formalize a goal G and default ∅, and prove the goal-preservation tiling theorem |- Box n (Impl (constructs_successor n) (Or empty G)) lifts up the chain.
70. Formalize the Vingean principle as a structural property of derivations: tiling_consistency derivations mention Box n phi only under a universal quantifier over phi, never instantiated.
71. Prove a no-panic reflective trust theorem: from Box n's internalization of Gödel's second, the agent does not derive |- Box n Bot.
72. Define the Σ_α / Δ_α decomposition from YH 2013 §5.2 as a structural property of agent encodings and prove tiling preserves the decomposition.
73. Prove a naturalistic-trust theorem: for an environmental subsystem provably isomorphic to an internal subroutine, Box n licenses the same conclusions from either, formalizing YH 2013's fourth desideratum.
74. Define an updateless decision-theoretic agent on top of the licensure layer, with action criterion ¯b ⇒ Box n (Impl ¯b G), and prove tiling preserves the criterion.
75. Encode FairBot and PrudentBot as Form-level objects via the polymodal fixed-point theorem and prove the robust-cooperation theorem of Barász et al. 2014.
76. Construct the procrastination paradox as a Form, prove its derivability under naive axioms, and prove T_κ blocks the construction.
77. Define Box_n^k for proofs of length ≤ k, prove bounded Löb in the calculus, and prove it reduces to Ax_Loeb in the limit, deriving the Critch connection rather than asserting it.
78. Prove the connection to Critch's parametric bounded Löb (JSL 2019): bounded-proof-length variants of Ax_Loeb are derivable in the system under appropriate complexity assumptions, unifying the proof-length-parametric and tower-index-parametric forms of "parametric Löb".
79. Prove the precise Critch correspondence at proof level: the bounded-proof-length parameter k in Critch's parametric Löb is exactly the level n in GLP* under a specific term-level mapping, with the bypass arguments in both formalisms identified up to translation.
80. Prove the Hilbert-Bernays-Löb derivability conditions hold for a concrete encoded provability predicate Bew_n over a representation of formulas, so that Ax_Loeb becomes a derived theorem rather than a primitive axiom.
81. Prove that the file's results are robust under adding a truth predicate Tr_n at each level n and the Tarski biconditionals Tr_n ⌜phi⌝ ↔ phi for level-n formulas, mirroring the YH 2013 §6 truth-predicate construction.
82. Prove a self-application theorem clarifying when the calculus may reason about its own metatheory: define a Form-level encoding of Provable and prove |- Box (S n) (Impl (Provable_encoded phi) (Box n phi)) under Hilbert-Bernays-Löb conditions.
83. Prove Ax_NextCon arithmetically: construct concrete theories T_n and T_(n+1) such that T_(n+1) derives the formalized statement of Con(T_n), rather than asserting it as a primitive.
84. Prove Ax_Mon (cross-level monotonicity) as a theorem about the concrete tower: show that every theorem of T_n is a theorem of T_(n+1) from the construction of the theories.
85. Construct T_κ as a first-order theory in the sense of YH 2013 §3 (PA augmented with the schematic axiom (κ > 0) -> ∀x. Box_{T_κ} ⌜φ(x)⌝ -> φ(x)[κ\κ-1]) and prove that each schema instance is well-formed.
86. Define the parametric tower with κ as a Form-level parameter rather than a meta-level nat and prove tiling_consistency in this internalized form, anticipating the first-order construction.
87. Prove soundness of T_κ at each standard κ ∈ N, which is the central positive result of YH 2013.
88. Prove the tiling theorem proper: that an agent A_α using T_κ derives the safety of constructing a successor agent A_(α-1) using T_(κ-1), for arbitrary standard κ.
89. Define ZF_τ-style set-theoretic licensure (YH 2013 §6) at level n+2 over level n+1's set-theoretic reasoning, and prove the central trust lemma A_(n+2) |- A_(n+1) → ∀φ. (τ |=_τ ⌜A_n  pφq⌝ → τ |=_τ ⌜φ⌝).
90. Prove an arithmetic soundness bridge: define an interpretation I : Form -> Arith such that |- phi implies PA |- I(phi) under the natural reading of Box n as iterated consistency extensions of PA.
91. Prove the bridge in (90) is faithful at level 0: |- Box 0 phi iff PA |- Bew_PA(I(phi)).
92. Prove arithmetical soundness of the polymodal calculus: every theorem |- phi translates, under the standard arithmetical interpretation, to a theorem of the appropriate concrete theory in the tower.
93. Prove a Σ_1-soundness theorem: every Σ_1-content theorem of GLP* under the canonical interpretation lifts to a true Σ_1 sentence about PA, providing the Σ-soundness bridge feeding Solovay-style completeness.
94. Prove a Π_1-conservativity theorem matching Fallenstein 2013: every Π_1-formula provable at level n is provable at level n+1, formalizing the soundness used in the consistency-waterfall construction.
95. Prove the Π_2-conservativity of every level over its predecessor in the arithmetical interpretation.
96. Prove a Friedman-translation analog: a syntactic transformation [·]_φ such that classical |- ψ implies intuitionistic |- [ψ]_φ for all φ, recovering the constructive content of the calculus.
97. Prove a Solovay-style arithmetic completeness theorem for the level-0 fragment: every arithmetically valid formula is |--derivable at level 0.
98. Prove arithmetical completeness in the Solovay sense: the modal theorems of the polymodal calculus are exactly the formulas valid under all arithmetical interpretations into the tower.
99. Prove the polymodal extension is arithmetically complete relative to the Beklemishev hierarchy: |- phi iff phi holds under the iterated-reflection interpretation in PA + RFN.
100. Prove a reflection-schema classification theorem: classify which reflection schemata (local, uniform, partial, Σ_n-restricted) GLP* and its strengthenings admit, and locate GLP* precisely within this classification.
101. Prove a reflection-principle hierarchy theorem: define RFN_n as the level-n local reflection schema, prove RFN_n is strictly weaker than RFN_(n+1), and embed the resulting hierarchy into Provable.
102. Prove a strict per-level hierarchy theorem: each level-n theory strictly dominates level-(n−1) in proof power, with the gap exactly a reflection principle.
103. Prove that the proof-theoretic ordinal of GLP* (under appropriate arithmetisation) equals the value predicted by Beklemishev's worm-ordinal analysis (typically ε_0 for the standard polymodal hierarchy), confirming the ordinal-theoretic place of the calculus.
104. Prove the connection to Beklemishev's iterated-reflection hierarchy: that the tower's consistency-chain structure embeds into, or is interpretable by, the standard iterated local reflection ordering, locating this axiomatization within the existing polymodal landscape.
105. Prove the procrastination paradox in this formalization and prove that T_κ avoids it: that a T_κ-using agent cannot derive a paradoxical postponement of an action it is required to take.
106. Prove a temporal-extension procrastination bypass theorem: extend GLP* with a "do action a at time t" predicate and prove the bypass step happens precisely at the cross-level reflection.
107. Prove a Visser-style interpretability logic embedding: there is a precise translation from a polymodal extension of Visser's IL into GLP* under which the tiling structure rereads as a tower of interpretations.
108. Prove a bimodal Σ_1-vs-general provability extension (Smoryński-style): adding a second modality at each level capturing Σ_1-provability yields a calculus that interprets GLP* and validates a strengthened tiling.
109. Construct a quantified polymodal logic QGLP* by adding first-order quantifiers, and prove its core metatheorems (Loeb, tiling, monotonicity at every level) together with completeness against quantified Kripke models.
110. Prove a deduction theorem with necessitation under modal-closure side conditions: extend Provable_with_hyp to admit Nec on hypothesis-free derivations and prove the corresponding deduction theorem.
111. Prove a transfinite Löb metatheorem: for ordinals α < ε_0, |- Impl (Box α phi) phi implies |- phi, generalizing loeb_metatheorem.
112. Prove a transfinite consistency chain: for α < β < ε_0, |- Box β (Neg (Box α Bot)), generalizing consistency_chain.
113. Prove the file's results extend to transfinite levels: define Box alpha for ordinals alpha < epsilon_0 and prove tiling_consistency lifts.
114. Construct uniform Box_α machinery: a generic ordinal-indexed construction giving Box_α for α < ε_0 (or up to the Bachmann-Howard ordinal), with corresponding T_α tower and arithmetic interpretation.
115. Prove the transfinite extension of (113) recovers the full Beklemishev GLP system, with explicit translation between this file's Box n tower and the GLP-worm hierarchy.
116. Define a graded modality [Bel ≥ p]_n, prove its unbounded reflection schema collapses, and prove an ε-tolerant variant survives, connecting to Christiano et al. 2013.
117. Construct a probabilistic agent licensure extension (phi holds with probability ≥ p at level n) and prove a probabilistic YH bypass theorem under appropriate frame conditions, giving a quantitative version of tiling_consistency.
118. Prove a complexity bound on the decision procedure: membership in Provable is decidable in PSPACE, paralleling Shapirovsky's bound for GLP.
119. Prove PSPACE-hardness of the variable-free fragment, paralleling Pakhomov for GLP.
120. Define a proof-term calculus (terms inhabiting Provable propositions under Curry-Howard) and prove every closed proof term normalizes.
121. Prove that the proof-term normal forms are unique up to a specified equational theory on proof terms.
122. Prove an extracted certified verifier: extract from Provable an OCaml proof-checker, prove its soundness inside Coq, and prove it accepts exactly the closed terms of Provable.
123. Prove verifier completeness: every Provable closed formula is accepted by the extracted checker (the converse soundness direction of (122)), giving a fully verified bidirectional decision procedure for the proof predicate.
