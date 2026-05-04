# tiling-verified todo

Ordered so each item's prerequisites appear earlier.  Each item must
compile cleanly before the next is begun.

1. Establish that `proof_term_ordinal` has order type ε₀ in Cantor
   normal form and strictly decreases under reduction, giving a
   sharp proof-theoretic ordinal bound.
2. Prove the SC_impl_left_no_occ case of Sambin existence
   (recursive case where `phi = Impl X phi'` with `p` not in `X`
   and `phi'` itself in `sambin_class`), completing
   `sambin_class_yields_fixed_point_base` to a uniform existence
   theorem over the full `sambin_class` inductive.
3. Prove fixed-point existence for `phi(p) := And X (Box n (Var p))`
   and other compound modalised contexts.
4. Prove the full Sambin-de Jongh fixed-point theorem: for every
   `phi(p)` in which `p` occurs only modalised, exhibit a closed
   `psi` with `|- Iff psi (Subst p psi phi)`, by structural
   induction on `phi`.
5. Extend `sambin_uniform_uniqueness_base` to cover the
    `SC_impl_left_no_occ` recursive case and the `SC_top_solves`
    case (currently only no-occurrence, Loeb-form, and box-atomic
    are handled).
6. Prove the full de Jongh-Sambin uniqueness over arbitrary
    modalised formulas (combining `sambin_uniqueness_loeb_general`,
    `sambin_uniqueness_box_atomic_general`,
    `sambin_uniqueness_via_no_occurrence`,
    `sambin_uniqueness_via_top_class`).
7. Implement an explicit fixed-point computation algorithm: given
    a modalised `phi(p)`, return a syntactic `psi` in normal form
    plus a derivation of the equivalence; prove the algorithm
    correct.
8. Build a sequent presentation `SC_GLP : list Form -> list Form ->
    Prop` with structural rules, propositional rules, and per-level
    modal rules with the Löb side-condition.
9. Prove cut admissibility structurally for the sequent calculus
    (Avron-Negri-von Plato discharge mechanism for the Löb case).
10. Prove cut-free derivations exist for every theorem and have
    bounded modal depth as a function of the conclusion, giving a
    constructive bound on proof complexity.
11. Define `Maehara_interpolant_real` by structural recursion on a
    cut-free derivation; prove the standard Maehara case-split at
    every rule with the invariant FV(χ) ⊆ FV(Γ₁) ∩ ({phi} ∪ FV(Γ₂))
    and analogous bound on box-levels.
12. Prove genuine Craig interpolation: for every `|- Impl phi psi`,
    exhibit `chi` whose free variables and Box-levels are strictly
    contained in the intersection of those of `phi` and `psi`,
    via cut-free proof induction.
13. Prove Lyndon interpolation: the interpolant additionally
    preserves polarity of variable occurrences.
14. Prove uniform interpolation: for every `phi` and variable `p`,
    exhibit `phi_p` not containing `p` such that for every `psi`
    not containing `p`, `|- Impl phi psi <-> |- Impl phi_p psi`.
15. Prove Beth definability in its full form: every implicitly
    definable predicate is explicitly definable.
16. Define `canonical_world_max := { Γ | Consistent Γ /\ maximal /\
    deductively_closed }`; lift `canonical_R` to it; prove the
    modal truth lemma over the maximal-consistent canonical model.
17. Prove `canonical_R` satisfies converse-well-foundedness from
    `Ax_Loeb`.
18. Construct the explicit `canonical_R` NextCon-successor by
    showing `{ phi | v (Box n phi) }` is consistent (using
    `canonical_R_NextCon_witness`) and extending to a canonical
    world via Lindenbaum.
19. Extend the canonical-model truth lemma to the full modal
    language (`Box n psi` case) by structural induction on `phi`,
    including the non-trivial backward direction requiring a
    witnessing world for the negation.
20. Prove the existence-lemma for the canonical model: every
    consistent formula is true at some canonical world; chain to
    strong completeness rather than weak completeness.
21. Prove Kripke completeness of GLP*: every non-theorem is refuted
    by some GLP*-frame.
22. Prove Kripke completeness for `Provable_no_NC`,
    `Provable_no_Mon`, `Provable_no_Loeb`, `Provable_no_B4`
    separately, with their distinguishing frame classes.
23. Prove modal compactness: a set of formulas has a model iff
    every finite subset does.
24. Prove ω-completeness for `Fnat`: every formula valid at every
    world of `Fnat` is provable; characterise the formulas valid
    in `Fnat` as a sublogic of GLP*.
25. Construct the universal frame for GLP* and prove it is the
    canonical Kripke model up to bisimulation.
26. Implement filtration through a finite subformula-closed set Σ;
    prove the resulting finite model preserves truth values for
    formulas in Σ.
27. Prove the finite frame property: every non-theorem of GLP* is
    refuted on some finite frame.
28. Prove finite-model property with effective bounds: every
    non-theorem is refuted on a frame of size at most exponential
    in the formula's modal depth.
29. Prove a selection theorem: from a Kripke model extract a
    generated submodel containing a designated point bisimilar to
    the original at that point.
30. Implement a true PSPACE decision procedure for the full
    polymodal language via filtration; prove a Coq-verified PSPACE
    complexity bound.
31. Prove decidability of the full polymodal calculus via filtration
    plus 32.
32. Prove PSPACE-completeness of GLP* satisfiability/provability,
    by reducing QBF to provability in GLP*.
33. Prove the box-free fragment coNP-complete via a verified
    reduction from UNSAT.
34. Provide a verified extracted decision procedure operating on
    actual inputs and producing certificates, rather than a
    Coq-internal `sumbool` mediated by classical excluded-middle.
35. Implement and verify a tableau procedure for GLP* that produces
    either a closed tableau (proof) or an open branch
    (countermodel).
36. Verify a SAT/QBF-based reduction of box-free GLP* validity and
    extract a procedure calling an external solver, with the
    soundness of the reduction proven in Coq.
37. Replace `decidability_admissibility_box_free` (whose conclusion
    is `sumbool (... -> True) True`) with
    `decidability_admissibility_box_free_canonical`:
    a real `sumbool` of `(forall sigma, |- subst_form sigma phi)`
    against its negation, witnessed by `decide_tautology phi`.
38. Prove decidability of admissible rules (Rybakov's theorem) for
    at least the box-free fragment, with a real decision procedure
    rather than a vacuous skeleton.
39. Prove a decidability result for the bimodal `Box n + Box m`
    fragment with `n ≠ m` distinct from the full polymodal case.
40. Prove the existence of a finite refuting frame for every
    specific non-theorem (not just `Box n Bot`).
41. Prove a proper Kalmár-style completeness for the `Sigma1_modal`
    closure (not just box-free).
42. Prove the full Reflection Calculus completeness theorem for
    strictly positive formulas.
43. Prove decidability of the closed (variable-free) fragment with
    explicit complexity bounds via filtration.
44. Establish decidability of the variable-free fragment with
    bounded modal depth and exhibit the complexity class precisely.
45. Prove the Abashidze-Japaridze characterisation of the closed
    fragment of `Provable_GLP`.
46. Prove independence of `Ax_K` using non-Kripke (e.g. neighborhood)
    semantics, via a calculus-soundness theorem against the
    neighborhood semantics that omits Ax_K.
47. Prove `Ax_DN` is independent of K, S, BoxK, Loeb, Box4, Mon,
    NextCon by exhibiting an intuitionistic-modal frame validating
    the others but refuting DN.
48. Establish a complete independence matrix: for each pair of
    axioms, exhibit a model validating one but not the other.
49. Prove minimality of the axiom set: removing any axiom strictly
    weakens the calculus, with each minimality result witnessed by
    a specific theorem that fails.
50. Prove that each axiom-removal calculus is strictly weaker than
    `Provable` for infinitely many distinct theorems.
51. Prove undecidability of any extension of GLP* with binary
    modalities corresponding to interpretation, by reduction from
    the halting problem or a known undecidable modal logic.
52. Strengthen `is_modal_definable` to require the witnessing
    formula to land in a syntactically restricted fragment matching
    the property's intended class; restate the bisim-invariance
    theorems on the strengthened predicate.
53. Prove the unconditional reverse direction of van Benthem: every
    bisimulation-invariant first-order property over ω-saturated
    models is modally definable.
54. Prove the full Goldblatt-Thomason theorem characterising
    modally-definable frame classes.
55. Prove Sahlqvist correspondence in its general form (not just
    for K, Löb).
56. Prove the polymodal Fine-Schurz incompleteness result
    identifying GLP*-formulas not derivable in any Kripke-complete
    sub-logic.
57. Construct the Lindenbaum-Tarski algebra explicitly as a
    quotient type with proven decidable equality on equivalence
    classes (where decidability holds); prove it is the free
    Magari algebra on countably many generators.
58. Prove Magari (diagonalisable algebra) completeness: every GL
    theorem holds in every Magari algebra and conversely; the
    Lindenbaum-Tarski algebra is the free Magari algebra on the
    propositional variables.
59. Prove Jónsson-Tarski / Stone duality between the
    Lindenbaum-Tarski algebra and the canonical frame, in the
    style of Stone duality for Boolean algebras lifted to modal
    algebras.
60. Establish that the variety generated by Magari algebras is
    locally finite for the box-free fragment and prove a
    McKinsey-Tarski-style algebraic completeness result.
61. Prove a genuine categorical-semantics theorem: define a
    category of GLP*-frames with bisimulation-respecting morphisms;
    prove `Provable` corresponds to global sections of a sheaf or
    similar structure.
62. Establish a categorical equivalence between provability-style
    modal logics and a class of preordered algebras, in the manner
    of Esakia duality for intuitionistic logic.
63. Replace `categorical_fixed_point_for_licenses` and
    `categorical_fixed_point_for_T_kappa` (currently
    `prov_iff_refl`) with `licenses_universal_property_categorical`:
    `forall F, (preserves provability) -> (K-distrib) ->
              (monotonicity) -> (Loeb closure) ->
    forall n phi, |- Iff (F n phi) (Box n phi)`.
64. Strengthen `licenses_axiomatic_uniqueness` to non-extensional
    candidate operators via a categorical universal property.
65. Wrapper-content audit: for every `Theorem foo : ... Proof.
    exact bar. Qed.` style one-line restatement currently in
    `Tiling.v`, replace with a strengthened version that adds
    quantitative, categorical, or proof-length content.
66. Construct a genuine arithmetic Σ₁ provability predicate
    `Bew_PA` over a Gödel-encoded fragment of arithmetic (formulas
    as numerals, proofs as numerals); prove the
    Hilbert-Bernays-Löb conditions for it.
67. Replace the primitive `Box n` view with a Σ₁ predicate
    `Bew_n : nat -> Prop` defined over a Gödel-numbered syntax of
    formulas and proofs; prove the HBL conditions as theorems
    about this predicate rather than postulates.
68. Prove an internal Gödel diagonalisation lemma: for every
    `φ(p)` with one free variable, construct `ψ` with
    `|- Iff ψ (φ ⌜ψ⌝)`; use it to derive Gödel's first and second
    incompleteness theorems internally.
69. Construct, for each `n`, a Gödel sentence `Gₙ` with
    `|- Iff Gₙ (Neg (Bew_n ⌜Gₙ⌝))`; prove `Gₙ` is independent of
    `Tₙ` but provable in `Tₙ₊₁`.
70. Construct in Coq an explicit recursive enumeration of axioms
    for each `Tₙ` as actual arithmetic theories extending Robinson
    Q (or PA), with the level-(n+1) theory containing the Σ₁
    sentence `Con(Tₙ)`; prove cumulativity as a theorem about
    provability rather than a definitional inclusion.
71. Construct a first-order theory `T_n` with explicit axioms (not
    just modal axiom-schemas via `T_axiom`); prove the
    cumulativity, consistency, and tiling results at the genuine
    first-order level.
72. Eliminate `Ax_NextCon` from the axiom list and instead derive
    `Box (S n) (¬ Box n ⊥)` from properties of an underlying
    arithmetic theory.
73. Establish a non-trivial consistency-strength ordering between
    `Tₙ` and `Tₙ₊₁` by proving an ordinal analysis result.
74. Prove the tower bypass non-vacuous by exhibiting a specific
    `φ` such that `Tₙ` does not prove `Con(Tₙ → φ)` but `Tₙ₊₁`
    does.
75. Prove a soundness theorem connecting modal `Box n φ` to the
    arithmetised `Bew_n ⌜φ*⌝` for a realisation map `φ ↦ φ*`.
76. Prove Π₁ conservativity of `T_(n+1)` over `T_n` for arithmetic
    Π₁ sentences.
77. Prove Π₂ conservativity across the tower.
78. Prove Friedman's negative translation result connecting
    classical to constructive provability beyond the box-free
    case.
79. Prove the relative-consistency direction `Con(T_0) → Con(T_n)`
    from a strictly weaker hypothesis than meta-consistency of the
    full system.
80. Prove `T_no_self_consistency` directly from `Bew`'s HBL
    conditions rather than routing through the full Provable
    calculus.
81. Prove the strict separation between `Bew n` and `Bew (S n)` at
    the proof level (not just at the axiom-set level).
82. Prove that the structural `Bew` predicate satisfies provability
    logic (i.e. `Bew n` interpreted into `Box n` validates exactly
    GLP* at the relevant level).
83. Prove Solovay's first completeness theorem in full: every
    modal formula valid under all arithmetic interpretations into
    PA is provable in GL.
84. Prove Solovay's second completeness theorem for the
    truth-extension `Provable_S` beyond the box-free fragment.
85. Prove arithmetic completeness of `Provable_GLP` (Japaridze's
    theorem) for arbitrary formulas, not just box-free ones.
86. Construct a genuinely non-identity, non-licensure inhabitant of
    `is_arithmetic_interpretation` to show the predicate has
    non-trivial structure beyond `identity` and `licenses k`.
87. Prove the Friedman-Sheard truth-axiomatisation theorem.
88. Construct a hierarchy of partial truth predicates `Trₙ` where
    each `Trₙ` correctly evaluates formulas of modal depth `≤ n`,
    with `Trₙ` definable at level `n+1`, paralleling Tarski's
    hierarchy.
89. Prove Tarski undefinability in its sharpest form: no formula
    `Tr(x)` in the language of GLP* with one free variable
    satisfies `|- Iff (Tr ⌜φ⌝) φ` for all `φ`.
90. Prove a strong undefinability theorem by Gödel diagonalisation
    on a self-referential sentence, in any consistent extension of
    the calculus with a unary `Tr` satisfying the T-schema.
91. Prove the Visser interpretability logic ILM/ILP axioms beyond
    just the K-distribution and Box4 forms.
92. Prove the Visser-Berarducci theorem on interpretability logic:
    ILM is the interpretability logic of any reasonable arithmetic
    theory containing IΣ₁.
93. Prove the Visser ILM J5 axiom from the calculus axioms rather
    than via `Ax_Mon`.
94. Prove the Critch parametric bounded-Löb theorem for a genuinely
    bounded provability predicate (with proof-length bound encoded
    inside the modal formula), not just iterated `Box`.
95. Prove the Critch correspondence between modal
     `critch_bounded_box` and a genuine bounded-arithmetic
     provability predicate with explicit polynomial bounds.
96. Implement Critch's bounded provability with an explicit
     resource bound `k` counting proof steps; prove a parametric
     Löb theorem with a threshold `k₀`.
97. Construct a concrete agent using bounded provability whose
     behaviour depends measurably on `k`.
98. Replace the cosmetic alias `licenses n φ := Box n φ` with a
     substantive predicate over a separately defined `Agent`
     record carrying a decision procedure, a goal predicate, an
     action space, and a verification routine.
99. Formalise a concrete agent that takes as input a candidate
     successor and outputs a decision in finite time based on
     inspection of a level-`n` proof.
100. Prove a non-trivial successor-licensing theorem: given an
     explicit goal predicate `G`, an explicit transition function,
     and an explicit candidate successor `σ`, derive that the
     level-`n` agent licenses `σ` iff a verifiable condition on
     `σ` holds, where the condition is computable.
101. Demonstrate a concrete failure case where a level-`n` agent
     cannot license a successor that a level-(n+1) agent can,
     using actual programs and goals rather than uninterpreted
     formulas.
102. Prove the goal-preservation tiling theorem for an agent that
     takes non-trivial actions changing the state.
103. Prove vingean reflection in a setting where the agent's
     decision genuinely depends on `T_(n+1)` licensure.
104. Prove the no-panic reflective-trust theorem at the level of
     self-modifying agents.
105. Prove the `T_kappa` agent-correspondence theorem with a
     non-trivial agent architecture.
106. Prove Aumann's agreement theorem in modal form: agents at
     different levels with common knowledge of consistency provably
     agree (the existing `Aumann_agreement_modal_real` covers the
     two-level case; extend to common-knowledge across many
     levels).
107. Define `FairBot n psi := psi := Box n (Iff (opp psi) Cooperate)`
     as a real Sambin fixed point where `opp` reads from the open
     variable.
108. Define `PrudentBot n psi` as a real Sambin fixed point with
     the consistency conjunct `Box (S n) (Neg (Box n Bot))`.
109. Replace the constant `Cooperate := ⊤` with a genuine action
     representing cooperation in a payoff-bearing game.
110. Prove FairBot vs FairBot mutual cooperation with the genuine
     fixed-point semantics and source-code reflection.
111. Prove FairBot vs DefectBot defection.
112. Prove FairBot vs CooperateBot mutual cooperation and FairBot
     vs DefectBot mutual defection as theorems where the bots
     access opponents' source code via a reflection principle.
113. Prove the BCFHLY robust-cooperation theorem for non-trivial
     fixed points (not just the collapse to `Top`).
114. Prove that PrudentBot strictly dominates FairBot in modal-PD
     against DefectBot, exhibiting concrete formula witnesses.
115. Establish PrudentBot's strict Pareto improvement over FairBot
     by exhibiting an opponent against which PrudentBot defects
     correctly but a naïve FairBot would cooperate.
116. Prove the Fallenstein-Soares 2014 finite-tower
     self-modification theorem at the arithmetic level.
117. Prove the Pudlák speedup result for the parametric tower at
     every level.
118. Prove a quantitative version of the Löbian obstacle: bound the
     proof length of the inconsistency derivation by a function of
     the reflection-schema's proof complexity.
119. Formalise the original Yudkowsky-Herreshoff tiling agent as a
     concrete program: a Turing machine that, given a candidate
     successor, performs a bounded proof search at level `n`,
     decides licensing based on a specific verification predicate,
     and outputs a decision.
120. Prove the tiling-agent never-defects-against-itself theorem:
     when two such agents face each other in a coordination game,
     both license the cooperative strategy via a common-knowledge
     fixed point.
121. Establish the Vingean reflection no-go result formally.
122. Prove the Fallenstein parametric bounded Löb result: bounded
     Löb with parameter `k` holds iff the agent's verifier has
     access to proofs of length at least `k`.
123. Connect the tower to a concrete model of self-improvement:
     prove that an agent at level `n` licensing a successor at
     level `n+1` corresponds to a specific code transformation
     preserving a goal predicate.
124. Re-derive the worm theory inside a calculus where Mon is
     absent (genuine GLP), so worms have non-trivial provability
     content and the worm-ordinal correspondence captures real
     proof-theoretic strength rather than collapsing.
125. Prove Beklemishev's worm normal form theorem for
     `Provable_GLP` (where worms are not all provable), not just
     the trivial collapse in `Provable`.
126. Prove the Beklemishev reduction theorem: every theorem of GLP
     is provably equivalent (in GLP) to a Boolean combination of
     worms.
127. Prove the worm-ordering total: for any two worms `w₁`, `w₂`,
     decide which provably implies the other in GLP, with the
     ordering matching Cantor-normal-form comparison on
     `worm_to_ord`.
128. Prove that the proof-theoretic ordinal of GLP (without Mon)
     equals ε₀ via Beklemishev's worm normalisation.
129. Prove the proof-theoretic ordinal of `Provable_GLP` is exactly
     ε₀ via a complete ordinal-assignment to proof terms with
     strict decrease under reduction.
130. Compute the proof-theoretic ordinal of GLP* as presented and
     prove a sharp upper and lower bound.
131. Replace the syntactic `Veblen_phi_iter` and `Gamma_0_approx`
     shells with the genuine Veblen hierarchy as ordinal functions;
     prove their fixed-point properties.
132. Prove Carlson's theorem on the ordinal-analysis correspondence
     between worms and ordinals below ε₀.
133. Prove Carlson's theorem (second incompleteness for polymodal
     provability) in its sharp form.
134. Prove the explicit ε₀-rank-respecting normalisation theorem
     for proof terms with strict ordinal decrease.
135. Prove Gentzen's consistency proof for PA via ε₀-induction
     inside Coq.
136. Define a genuine first-order extension `QGLP` with quantifiers,
     variable assignments, and a Tarskian semantics; prove which
     fragments are decidable, which are recursively enumerable,
     and which are Π¹₁-complete.
137. Prove constant-domain QGLP* soundness and completeness with
     respect to a Kripke-style first-order semantics for quantified
     modal formulas.
138. Prove the Barcan and converse-Barcan formulas hold or fail in
     the quantified extension, with semantic witnesses.
139. Prove a genuine temporal-extension result where time and modal
     level interact non-trivially.
140. Prove a probabilistic-Löb theorem with a real probability
     parameter (not just `nat`) showing graded reflection survives
     at strictly positive ε.
141. Define a probabilistic logic of provability with graded
     modalities `Bel_p` where `p` is a probability; prove sound
     and complete with respect to a measure-theoretic semantics.
142. Connect the probabilistic version to actual decision-theoretic
     agents using credences.
143. Construct a proper neighborhood-semantics framework; prove
     soundness/completeness for a non-normal modal logic separating
     it from GLP*.
144. Formalise a transfinite-level extension where modalities are
     indexed by ordinals below Γ₀.
145. Extend the calculus with a μ-operator for least fixed points;
     prove the resulting μGLP is decidable.
146. Prove the modal μ-calculus alternation hierarchy is strict at
     every level.
147. Establish the Kozen completeness theorem for μGLP and connect
     μ-fixed points to the parametric tower's fixed-point
     licensing decisions.
148. Define a game semantics for GLP* where verifier and falsifier
     play over the Kripke frame.
149. Establish determinacy for the resulting games on well-founded
     frames; connect winning strategies to proof terms.
150. Connect the FairBot/PrudentBot constructions to actual
     game-theoretic equilibria via the game semantics.
151. Prove the modal logic of programs (PDL) embeds into GLP* via
     a translation mapping program iteration to fixed points.
152. Connect Coalition Logic and ATL to the licensing tower.
153. Prove the disjunction property for `Provable_GLP`.
154. Prove that `Provable_GLP_incomparable_with_provable` extends
     to infinitely many incomparable formulas.
155. Prove a no-go theorem for any uniform strengthening of
     `Ax_NextCon` to `Box n (Neg (Box n Bot))` across all levels.
156. Prove that the `Provable_plus` extension scheme yields
     inconsistency for any reflection-schema extension at any
     level uniformly.
157. Prove the reverse direction of
     `licensing_consistency_concrete_converse` quantifying over all
     formulas at level `n` simultaneously.
158. Prove the Smoryński bimodal independence theorem at distinct
     levels for non-trivial formulas.
159. Prove the full conservativity of `Provable_GL` over `Provable`
     at level 0 in both directions.
160. Establish the conservativity of GLP* over GL at level 0 in
     both directions and over Japaridze's GLP at all levels.
161. Prove a conservativity ordering: GLP* is conservative over GL
     for level-0 sentences, conservative over a specific theory of
     arithmetic for Π₁ sentences.
162. Prove the polymodal-fixed-point system completeness à la
     Smoryński.
163. Define a realisability interpretation of GLP* where realisers
     are verified programs.
164. Prove a Curry-Howard correspondence for the modal fragment.
165. Establish a propositions-as-types interpretation where
     licensing translates to the existence of a verified compiler
     from level-`n` programs to level-(n+1) programs.
166. Embed GLP* into homotopy type theory.
167. Connect `Box n` to a graded comonad in the categorical
     semantics.
168. Determine the reverse-mathematical strength of each major
     theorem in the development.
169. Prove that `meta_consistency_system` requires no more than
     primitive recursive arithmetic.
170. Extract a verified OCaml or Haskell decision procedure from
     the Coq development; benchmark against existing modal-logic
     provers.
171. Use the formalisation to verify a real safety property of a
     real machine-learning system.
172. Connect the verification to a runtime monitor that rejects
     unsafe operations based on level-`n` proof obligations.
173. Prove a non-trivial program transformation correct using the
     modal apparatus.
174. Split `Tiling.v` into themed modules — `Calculus`, `Hilbert`,
     `Kripke`, `FixedPoints`, `Bew`, `ProofTerms`, `Worms`,
     `Agents`.
175. Add `Examples.v` with three worked examples.
176. Add `README.md` listing the headline theorems, the dependency
     story, and build instructions.
177. Provide tutorial sections explaining the proof strategies.
178. Cross-reference each theorem to its source in Boolos's *The
     Logic of Provability*, Smoryński's *Self-Reference and Modal
     Logic*, Beklemishev's papers, and the YH13 tech report.
