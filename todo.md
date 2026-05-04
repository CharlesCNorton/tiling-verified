# tiling-verified todo

Ordered so each item's prerequisites appear earlier.  Each item must
compile cleanly before the next is begun.

1. Define `Maehara_interpolant_real` by structural recursion on a
    cut-free derivation; prove the standard Maehara case-split at
    every rule with the invariant FV(χ) ⊆ FV(Γ₁) ∩ ({phi} ∪ FV(Γ₂))
    and analogous bound on box-levels.
2. Prove genuine Craig interpolation: for every `|- Impl phi psi`,
    exhibit `chi` whose free variables and Box-levels are strictly
    contained in the intersection of those of `phi` and `psi`,
    via cut-free proof induction.
3. Prove Lyndon interpolation: the interpolant additionally
    preserves polarity of variable occurrences.
4. Prove uniform interpolation: for every `phi` and variable `p`,
    exhibit `phi_p` not containing `p` such that for every `psi`
    not containing `p`, `|- Impl phi psi <-> |- Impl phi_p psi`.
5. Prove Beth definability in its full form: every implicitly
    definable predicate is explicitly definable.
6. Define `canonical_world_max := { Γ | Consistent Γ /\ maximal /\
    deductively_closed }`; lift `canonical_R` to it; prove the
    modal truth lemma over the maximal-consistent canonical model.
7. Prove `canonical_R` satisfies converse-well-foundedness from
    `Ax_Loeb`.
8. Construct the explicit `canonical_R` NextCon-successor by
    showing `{ phi | v (Box n phi) }` is consistent (using
    `canonical_R_NextCon_witness`) and extending to a canonical
    world via Lindenbaum.
9. Extend the canonical-model truth lemma to the full modal
    language (`Box n psi` case) by structural induction on `phi`,
    including the non-trivial backward direction requiring a
    witnessing world for the negation.
10. Prove the existence-lemma for the canonical model: every
    consistent formula is true at some canonical world; chain to
    strong completeness rather than weak completeness.
11. Prove Kripke completeness of GLP*: every non-theorem is refuted
    by some GLP*-frame.
12. Prove Kripke completeness for `Provable_no_NC`,
    `Provable_no_Mon`, `Provable_no_Loeb`, `Provable_no_B4`
    separately, with their distinguishing frame classes.
13. Prove modal compactness: a set of formulas has a model iff
    every finite subset does.
14. Prove ω-completeness for `Fnat`: every formula valid at every
    world of `Fnat` is provable; characterise the formulas valid
    in `Fnat` as a sublogic of GLP*.
15. Construct the universal frame for GLP* and prove it is the
    canonical Kripke model up to bisimulation.
16. Implement filtration through a finite subformula-closed set Σ;
    prove the resulting finite model preserves truth values for
    formulas in Σ.
17. Prove the finite frame property: every non-theorem of GLP* is
    refuted on some finite frame.
18. Prove finite-model property with effective bounds: every
    non-theorem is refuted on a frame of size at most exponential
    in the formula's modal depth.
19. Prove a selection theorem: from a Kripke model extract a
    generated submodel containing a designated point bisimilar to
    the original at that point.
20. Prove the existence of a finite refuting frame for every
    specific non-theorem (not just `Box n Bot`).
21. Implement a true PSPACE decision procedure for the full
    polymodal language via filtration; prove a Coq-verified PSPACE
    complexity bound.
22. Prove decidability of the full polymodal calculus via
    filtration.
23. Prove PSPACE-completeness of GLP* satisfiability/provability,
    by reducing QBF to provability in GLP*.
24. Prove the box-free fragment coNP-complete via a verified
    reduction from UNSAT.
25. Replace `decidability_admissibility_box_free` (whose conclusion
    is `sumbool (... -> True) True`) with
    `decidability_admissibility_box_free_canonical`:
    a real `sumbool` of `(forall sigma, |- subst_form sigma phi)`
    against its negation, witnessed by `decide_tautology phi`.
26. Prove decidability of admissible rules (Rybakov's theorem) for
    at least the box-free fragment, with a real decision procedure
    rather than a vacuous skeleton.
27. Prove a decidability result for the bimodal `Box n + Box m`
    fragment with `n ≠ m` distinct from the full polymodal case.
28. Provide a verified extracted decision procedure operating on
    actual inputs and producing certificates, rather than a
    Coq-internal `sumbool` mediated by classical excluded-middle.
29. Implement and verify a tableau procedure for GLP* that produces
    either a closed tableau (proof) or an open branch
    (countermodel).
30. Verify a SAT/QBF-based reduction of box-free GLP* validity and
    extract a procedure calling an external solver, with the
    soundness of the reduction proven in Coq.
31. Prove decidability of the closed (variable-free) fragment with
    explicit complexity bounds via filtration.
32. Establish decidability of the variable-free fragment with
    bounded modal depth and exhibit the complexity class precisely.
33. Prove the Abashidze-Japaridze characterisation of the closed
    fragment of `Provable_GLP`.
34. Prove a proper Kalmár-style completeness for the `Sigma1_modal`
    closure (not just box-free).
35. Prove the full Reflection Calculus completeness theorem for
    strictly positive formulas.
36. Prove independence of `Ax_K` using non-Kripke (e.g.
    neighborhood) semantics, via a calculus-soundness theorem
    against the neighborhood semantics that omits Ax_K.
37. Prove `Ax_DN` is independent of K, S, BoxK, Loeb, Box4, Mon,
    NextCon by exhibiting an intuitionistic-modal frame validating
    the others but refuting DN.
38. Establish a complete independence matrix: for each pair of
    axioms, exhibit a model validating one but not the other.
39. Prove minimality of the axiom set: removing any axiom strictly
    weakens the calculus, with each minimality result witnessed by
    a specific theorem that fails.
40. Prove that each axiom-removal calculus is strictly weaker than
    `Provable` for infinitely many distinct theorems.
41. Prove undecidability of any extension of GLP* with binary
    modalities corresponding to interpretation, by reduction from
    the halting problem or a known undecidable modal logic.
42. Strengthen `is_modal_definable` to require the witnessing
    formula to land in a syntactically restricted fragment matching
    the property's intended class; restate the bisim-invariance
    theorems on the strengthened predicate.
43. Prove the unconditional reverse direction of van Benthem: every
    bisimulation-invariant first-order property over ω-saturated
    models is modally definable.
44. Prove the full Goldblatt-Thomason theorem characterising
    modally-definable frame classes.
45. Prove Sahlqvist correspondence in its general form (not just
    for K, Löb).
46. Prove the polymodal Fine-Schurz incompleteness result
    identifying GLP*-formulas not derivable in any Kripke-complete
    sub-logic.
47. Construct the Lindenbaum-Tarski algebra explicitly as a
    quotient type with proven decidable equality on equivalence
    classes (where decidability holds); prove it is the free
    Magari algebra on countably many generators.
48. Prove Magari (diagonalisable algebra) completeness: every GL
    theorem holds in every Magari algebra and conversely; the
    Lindenbaum-Tarski algebra is the free Magari algebra on the
    propositional variables.
49. Prove Jónsson-Tarski / Stone duality between the
    Lindenbaum-Tarski algebra and the canonical frame, in the
    style of Stone duality for Boolean algebras lifted to modal
    algebras.
50. Establish that the variety generated by Magari algebras is
    locally finite for the box-free fragment and prove a
    McKinsey-Tarski-style algebraic completeness result.
51. Prove a genuine categorical-semantics theorem: define a
    category of GLP*-frames with bisimulation-respecting morphisms;
    prove `Provable` corresponds to global sections of a sheaf or
    similar structure.
52. Establish a categorical equivalence between provability-style
    modal logics and a class of preordered algebras, in the manner
    of Esakia duality for intuitionistic logic.
53. Replace `categorical_fixed_point_for_licenses` and
    `categorical_fixed_point_for_T_kappa` (currently
    `prov_iff_refl`) with `licenses_universal_property_categorical`:
    `forall F, (preserves provability) -> (K-distrib) ->
              (monotonicity) -> (Loeb closure) ->
    forall n phi, |- Iff (F n phi) (Box n phi)`.
54. Strengthen `licenses_axiomatic_uniqueness` to non-extensional
    candidate operators via a categorical universal property.
55. Construct a genuine arithmetic Σ₁ provability predicate
    `Bew_PA` over a Gödel-encoded fragment of arithmetic (formulas
    as numerals, proofs as numerals); prove the
    Hilbert-Bernays-Löb conditions for it.
56. Replace the primitive `Box n` view with a Σ₁ predicate
    `Bew_n : nat -> Prop` defined over a Gödel-numbered syntax of
    formulas and proofs; prove the HBL conditions as theorems
    about this predicate rather than postulates.
57. Prove an internal Gödel diagonalisation lemma: for every
    `φ(p)` with one free variable, construct `ψ` with
    `|- Iff ψ (φ ⌜ψ⌝)`; use it to derive Gödel's first and second
    incompleteness theorems internally.
58. Construct, for each `n`, a Gödel sentence `Gₙ` with
    `|- Iff Gₙ (Neg (Bew_n ⌜Gₙ⌝))`; prove `Gₙ` is independent of
    `Tₙ` but provable in `Tₙ₊₁`.
59. Construct in Coq an explicit recursive enumeration of axioms
    for each `Tₙ` as actual arithmetic theories extending Robinson
    Q (or PA), with the level-(n+1) theory containing the Σ₁
    sentence `Con(Tₙ)`; prove cumulativity as a theorem about
    provability rather than a definitional inclusion.
60. Construct a first-order theory `T_n` with explicit axioms (not
    just modal axiom-schemas via `T_axiom`); prove the
    cumulativity, consistency, and tiling results at the genuine
    first-order level.
61. Eliminate `Ax_NextCon` from the axiom list and instead derive
    `Box (S n) (¬ Box n ⊥)` from properties of an underlying
    arithmetic theory.
62. Establish a non-trivial consistency-strength ordering between
    `Tₙ` and `Tₙ₊₁` by proving an ordinal analysis result.
63. Prove the tower bypass non-vacuous by exhibiting a specific
    `φ` such that `Tₙ` does not prove `Con(Tₙ → φ)` but `Tₙ₊₁`
    does.
64. Prove a soundness theorem connecting modal `Box n φ` to the
    arithmetised `Bew_n ⌜φ*⌝` for a realisation map `φ ↦ φ*`.
65. Prove Π₁ conservativity of `T_(n+1)` over `T_n` for arithmetic
    Π₁ sentences.
66. Prove Π₂ conservativity across the tower.
67. Prove Friedman's negative translation result connecting
    classical to constructive provability beyond the box-free
    case.
68. Prove the relative-consistency direction `Con(T_0) → Con(T_n)`
    from a strictly weaker hypothesis than meta-consistency of the
    full system.
69. Prove the strict separation between `Bew n` and `Bew (S n)` at
    the proof level (not just at the axiom-set level).
70. Prove that the structural `Bew` predicate satisfies provability
    logic (i.e. `Bew n` interpreted into `Box n` validates exactly
    GLP* at the relevant level).
71. Prove Solovay's first completeness theorem in full: every
    modal formula valid under all arithmetic interpretations into
    PA is provable in GL.
72. Prove Solovay's second completeness theorem for the
    truth-extension `Provable_S` beyond the box-free fragment.
73. Prove arithmetic completeness of `Provable_GLP` (Japaridze's
    theorem) for arbitrary formulas, not just box-free ones.
74. Construct a genuinely non-identity, non-licensure inhabitant of
    `is_arithmetic_interpretation` to show the predicate has
    non-trivial structure beyond `identity` and `licenses k`.
75. Prove Tarski undefinability in its sharpest form: no formula
    `Tr(x)` in the language of GLP* with one free variable
    satisfies `|- Iff (Tr ⌜φ⌝) φ` for all `φ`.
76. Prove a strong undefinability theorem by Gödel diagonalisation
    on a self-referential sentence, in any consistent extension of
    the calculus with a unary `Tr` satisfying the T-schema.
77. Prove the Friedman-Sheard truth-axiomatisation theorem.
78. Construct a hierarchy of partial truth predicates `Trₙ` where
    each `Trₙ` correctly evaluates formulas of modal depth `≤ n`,
    with `Trₙ` definable at level `n+1`, paralleling Tarski's
    hierarchy.
79. Prove the Visser interpretability logic ILM/ILP axioms beyond
    just the K-distribution and Box4 forms.
80. Prove the Visser-Berarducci theorem on interpretability logic:
    ILM is the interpretability logic of any reasonable arithmetic
    theory containing IΣ₁.
81. Prove the Visser ILM J5 axiom from the calculus axioms rather
    than via `Ax_Mon`.
82. Prove the Critch parametric bounded-Löb theorem for a genuinely
    bounded provability predicate (with proof-length bound encoded
    inside the modal formula), not just iterated `Box`.
83. Prove the Critch correspondence between modal
    `critch_bounded_box` and a genuine bounded-arithmetic
    provability predicate with explicit polynomial bounds.
84. Implement Critch's bounded provability with an explicit
    resource bound `k` counting proof steps; prove a parametric
    Löb theorem with a threshold `k₀`.
85. Construct a concrete agent using bounded provability whose
    behaviour depends measurably on `k`.
86. Replace the cosmetic alias `licenses n φ := Box n φ` with a
    substantive predicate over a separately defined `Agent`
    record carrying a decision procedure, a goal predicate, an
    action space, and a verification routine.
87. Formalise a concrete agent that takes as input a candidate
    successor and outputs a decision in finite time based on
    inspection of a level-`n` proof.
88. Prove a non-trivial successor-licensing theorem: given an
    explicit goal predicate `G`, an explicit transition function,
    and an explicit candidate successor `σ`, derive that the
    level-`n` agent licenses `σ` iff a verifiable condition on
    `σ` holds, where the condition is computable.
89. Demonstrate a concrete failure case where a level-`n` agent
    cannot license a successor that a level-(n+1) agent can,
    using actual programs and goals rather than uninterpreted
    formulas.
90. Prove the goal-preservation tiling theorem for an agent that
    takes non-trivial actions changing the state.
91. Prove vingean reflection in a setting where the agent's
    decision genuinely depends on `T_(n+1)` licensure.
92. Prove the no-panic reflective-trust theorem at the level of
    self-modifying agents.
93. Prove the `T_kappa` agent-correspondence theorem with a
    non-trivial agent architecture.
94. Replace the constant `Cooperate := ⊤` with a genuine action
    representing cooperation in a payoff-bearing game.
95. Define `FairBot n psi := psi := Box n (Iff (opp psi) Cooperate)`
    as a real Sambin fixed point where `opp` reads from the open
    variable.
96. Define `PrudentBot n psi` as a real Sambin fixed point with
    the consistency conjunct `Box (S n) (Neg (Box n Bot))`.
97. Prove FairBot vs FairBot mutual cooperation with the genuine
    fixed-point semantics and source-code reflection.
98. Prove FairBot vs DefectBot defection.
99. Prove FairBot vs CooperateBot mutual cooperation and FairBot
    vs DefectBot mutual defection as theorems where the bots
    access opponents' source code via a reflection principle.
100. Prove the BCFHLY robust-cooperation theorem for non-trivial
    fixed points (not just the collapse to `Top`).
101. Prove that PrudentBot strictly dominates FairBot in modal-PD
    against DefectBot, exhibiting concrete formula witnesses.
102. Establish PrudentBot's strict Pareto improvement over FairBot
    by exhibiting an opponent against which PrudentBot defects
    correctly but a naïve FairBot would cooperate.
103. Prove Aumann's agreement theorem in modal form: agents at
    different levels with common knowledge of consistency provably
    agree (the existing `Aumann_agreement_modal_real` covers the
    two-level case; extend to common-knowledge across many
    levels).
104. Prove the Fallenstein-Soares 2014 finite-tower
    self-modification theorem at the arithmetic level.
105. Prove the Pudlák speedup result for the parametric tower at
    every level.
106. Prove a quantitative version of the Löbian obstacle: bound the
    proof length of the inconsistency derivation by a function of
    the reflection-schema's proof complexity.
107. Formalise the original Yudkowsky-Herreshoff tiling agent as a
    concrete program: a Turing machine that, given a candidate
    successor, performs a bounded proof search at level `n`,
    decides licensing based on a specific verification predicate,
    and outputs a decision.
108. Prove the tiling-agent never-defects-against-itself theorem:
    when two such agents face each other in a coordination game,
    both license the cooperative strategy via a common-knowledge
    fixed point.
109. Establish the Vingean reflection no-go result formally.
110. Prove the Fallenstein parametric bounded Löb result: bounded
    Löb with parameter `k` holds iff the agent's verifier has
    access to proofs of length at least `k`.
111. Connect the tower to a concrete model of self-improvement:
    prove that an agent at level `n` licensing a successor at
    level `n+1` corresponds to a specific code transformation
    preserving a goal predicate.
112. Re-derive the worm theory inside a calculus where Mon is
    absent (genuine GLP), so worms have non-trivial provability
    content and the worm-ordinal correspondence captures real
    proof-theoretic strength rather than collapsing.
113. Prove Beklemishev's worm normal form theorem for
    `Provable_GLP` (where worms are not all provable), not just
    the trivial collapse in `Provable`.
114. Prove the Beklemishev reduction theorem: every theorem of GLP
    is provably equivalent (in GLP) to a Boolean combination of
    worms.
115. Prove the worm-ordering total: for any two worms `w₁`, `w₂`,
    decide which provably implies the other in GLP, with the
    ordering matching Cantor-normal-form comparison on
    `worm_to_ord`.
116. Prove that the proof-theoretic ordinal of GLP (without Mon)
    equals ε₀ via Beklemishev's worm normalisation.
117. Prove the proof-theoretic ordinal of `Provable_GLP` is exactly
    ε₀ via a complete ordinal-assignment to proof terms with
    strict decrease under reduction.
118. Compute the proof-theoretic ordinal of GLP* as presented and
    prove a sharp upper and lower bound.
119. Replace the syntactic `Veblen_phi_iter` and `Gamma_0_approx`
    shells with the genuine Veblen hierarchy as ordinal functions;
    prove their fixed-point properties.
120. Prove Carlson's theorem on the ordinal-analysis correspondence
    between worms and ordinals below ε₀.
121. Prove Carlson's theorem (second incompleteness for polymodal
    provability) in its sharp form.
122. Prove the explicit ε₀-rank-respecting normalisation theorem
    for proof terms with strict ordinal decrease.
123. Prove Gentzen's consistency proof for PA via ε₀-induction
    inside Coq.
124. Define a genuine first-order extension `QGLP` with quantifiers,
    variable assignments, and a Tarskian semantics; prove which
    fragments are decidable, which are recursively enumerable,
    and which are Π¹₁-complete.
125. Prove constant-domain QGLP* soundness and completeness with
    respect to a Kripke-style first-order semantics for quantified
    modal formulas.
126. Prove the Barcan and converse-Barcan formulas hold or fail in
    the quantified extension, with semantic witnesses.
127. Prove a genuine temporal-extension result where time and modal
    level interact non-trivially.
128. Prove a probabilistic-Löb theorem with a real probability
    parameter (not just `nat`) showing graded reflection survives
    at strictly positive ε.
129. Define a probabilistic logic of provability with graded
    modalities `Bel_p` where `p` is a probability; prove sound
    and complete with respect to a measure-theoretic semantics.
130. Connect the probabilistic version to actual decision-theoretic
    agents using credences.
131. Construct a proper neighborhood-semantics framework; prove
    soundness/completeness for a non-normal modal logic separating
    it from GLP*.
132. Formalise a transfinite-level extension where modalities are
    indexed by ordinals below Γ₀.
133. Extend the calculus with a μ-operator for least fixed points;
    prove the resulting μGLP is decidable.
134. Prove the modal μ-calculus alternation hierarchy is strict at
    every level.
135. Establish the Kozen completeness theorem for μGLP and connect
    μ-fixed points to the parametric tower's fixed-point
    licensing decisions.
136. Define a game semantics for GLP* where verifier and falsifier
    play over the Kripke frame.
137. Establish determinacy for the resulting games on well-founded
    frames; connect winning strategies to proof terms.
138. Connect the FairBot/PrudentBot constructions to actual
    game-theoretic equilibria via the game semantics.
139. Prove the modal logic of programs (PDL) embeds into GLP* via
    a translation mapping program iteration to fixed points.
140. Connect Coalition Logic and ATL to the licensing tower.
141. Prove the disjunction property for `Provable_GLP`.
142. Prove that `Provable_GLP_incomparable_with_provable` extends
    to infinitely many incomparable formulas.
143. Prove a no-go theorem for any uniform strengthening of
    `Ax_NextCon` to `Box n (Neg (Box n Bot))` across all levels.
144. Prove that the `Provable_plus` extension scheme yields
    inconsistency for any reflection-schema extension at any
    level uniformly.
145. Prove the Smoryński bimodal independence theorem at distinct
    levels for non-trivial formulas.
146. Prove the full conservativity of `Provable_GL` over `Provable`
    at level 0 in both directions.
147. Establish the conservativity of GLP* over GL at level 0 in
    both directions and over Japaridze's GLP at all levels.
148. Prove a conservativity ordering: GLP* is conservative over GL
    for level-0 sentences, conservative over a specific theory of
    arithmetic for Π₁ sentences.
149. Prove the polymodal-fixed-point system completeness à la
    Smoryński.
150. Define a realisability interpretation of GLP* where realisers
    are verified programs.
151. Prove a Curry-Howard correspondence for the modal fragment.
152. Establish a propositions-as-types interpretation where
    licensing translates to the existence of a verified compiler
    from level-`n` programs to level-(n+1) programs.
153. Embed GLP* into homotopy type theory.
154. Connect `Box n` to a graded comonad in the categorical
    semantics.
155. Determine the reverse-mathematical strength of each major
    theorem in the development.
156. Prove that `meta_consistency_system` requires no more than
    primitive recursive arithmetic.
157. Extract a verified OCaml or Haskell decision procedure from
    the Coq development; benchmark against existing modal-logic
    provers.
158. Use the formalisation to verify a real safety property of a
    real machine-learning system.
159. Connect the verification to a runtime monitor that rejects
    unsafe operations based on level-`n` proof obligations.
160. Prove a non-trivial program transformation correct using the
    modal apparatus.
161. Split `Tiling.v` into themed modules — `Calculus`, `Hilbert`,
    `Kripke`, `FixedPoints`, `Bew`, `ProofTerms`, `Worms`,
    `Agents`.  (A 15-module split is already drafted on
    `multi-module-split` and can be merged.)
162. Add `Examples.v` with three worked examples.
163. Add `README.md` listing the headline theorems, the dependency
    story, and build instructions.
164. Provide tutorial sections explaining the proof strategies.
165. Cross-reference each theorem to its source in Boolos's *The
    Logic of Provability*, Smoryński's *Self-Reference and Modal
    Logic*, Beklemishev's papers, and the YH13 tech report.
