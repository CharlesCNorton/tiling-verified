# tiling-verified todo

Ordered so each item's prerequisites appear earlier.  Each item must
compile cleanly before the next is begun.

1. Prove `well_founded ord_lt` (restricted to `{ o : ord | wf_ord o }`)
   by direct nested structural recursion: outer fix on the head
   exponent's syntactic structure with an inner fix on the tail.
   `ord_lt_trans`, `ord_lt_total`, `wf_ord`, `wf_ord_dec` already
   done; this item closes the genuine well-order content for CNF
   ordinals up to ε₀.
2. Define a canonical Cantor-normal-form datatype `cnf_ord` as a
   sigma `{ o : ord | wf_ord o }` with smart constructors that
   guarantee CNF; lift `ord_lt`, `ord_compare`, the `nat_to_ord` /
   `worm_to_ord` embeddings to `cnf_ord`; prove the ordering is a
   well-order up to ε₀ (using item 1).
3. Implement Buchholz's notation system or a Veblen-hierarchy
   notation in Coq; prove the notation system well-ordered; connect
   it to the proof-theoretic ordinals of GLP*-style calculi.
4. Replace the binder-free `Form` substitution with an α-aware
   substitution operation over a binder-aware syntax, anticipating
   the QGLP extension; prove its substitution lemmas.
5. Prove the Kripke substitution lemma:
   `forces F V w (subst_form sigma phi) <-> forces F V' w phi`
   where `V' = V ∘ sigma`.
6. Define a canonical normal form on `Form` (negation normal form,
   plus a Beklemishev-style worm normal form for the modal part);
   give a Coq function computing it and a proof of provable
   equivalence to the input.
7. Prove decidability of α-equivalence once binders are added, and
   decidability of provable equivalence on decidable fragments.

8. Audit which results require classical logic (LEM) and which
   require choice (ClassicalEpsilon); isolate the constructive core,
   restoring computational content to the bulk of the development.
9. Prove all syntactic results — Hilbert derivability, normalisation,
   decidability of the box-free fragment, finite axiomatisation —
   in pure intuitionistic Coq, with classical axioms isolated to a
   clearly marked "semantic completeness" section.
10. Prove the box-free fragment is constructively decidable without
    classical reasoning, via a direct recursion on formula structure
    with a verified output.
11. Construct a constructive truth-table decision procedure that
    produces a verifying certificate or refuting valuation,
    replacing `excluded_middle_informative` in `lindenbaum_extend`.
12. Replace `lindenbaum_extend` with a constructive Lindenbaum
    construction over a decidable theory — or prove the classical
    version is conservative over a constructive Henkin construction
    restricted to recursively enumerable theories.

13. Rename current `pspace_check_iter_sound` to
    `pspace_check_iter_pointwise_sound` (its actual content: the
    starting state's `eval` is `true`).
14. Prove the bool-list traversal-coverage lemma:
    iterating `bool_list_succ` from `repeat false n` for `2^n` steps
    visits every length-`n` bool list exactly once.
15. Prove `pspace_check_iter_full_sound`:
    after the full iteration, every length-`length vars` bool list
    has been checked.
16. Prove `decide_tautology_pspace_sound`:
    `decide_tautology_pspace phi = true -> classical_valid phi`,
    via 14 + 15 + `all_bool_lists_complete`.

17. Add S-axiom and DN-axiom contraction rules to `pt_reduces` with
    a measure that strictly decreases (multiset ordinal on
    subterm-size pairs).  K and BoxK_Nec already added.
18. Define a complete set of reduction rules covering all
    axiom-axiom interactions, such that the normal forms correspond
    to a recognisable cut-free or canonical proof shape; prove every
    `Provable` formula has a unique normal-form derivation.
19. Prove local confluence of `pt_reduces` (any two redexes from the
    same term reduce to a common form), then lift to full Church-
    Rosser confluence via Newman's lemma, replacing the present
    "both reducts shrink" placeholder.
20. Prove strong normalisation of the extended reduction via a
    multiset-ordinal measure on proof-term structure (rather than
    the basic size measure, which doesn't accommodate S-contraction).
21. Establish that `proof_term_ordinal` has order type ε₀ in Cantor
    normal form and strictly decreases under reduction, giving a
    sharp proof-theoretic ordinal bound.

22. Prove the SC_impl_left_no_occ case of Sambin existence
    (recursive case where `phi = Impl X phi'` with `p` not in `X`
    and `phi'` itself in `sambin_class`), completing
    `sambin_class_yields_fixed_point_base` to a uniform existence
    theorem over the full `sambin_class` inductive.
23. Prove fixed-point existence for `phi(p) := And X (Box n (Var p))`
    and other compound modalised contexts.
24. Prove the full Sambin-de Jongh fixed-point theorem: for every
    `phi(p)` in which `p` occurs only modalised, exhibit a closed
    `psi` with `|- Iff psi (Subst p psi phi)`, by structural
    induction on `phi`.
25. Replace `fixed_point_uniqueness_assumed` (currently a tautology
    given `|- Iff ψ₁ ψ₂`) with `sambin_uniform_uniqueness`:
    structural induction on `sambin_class p phi` deriving
    `|- Iff psi1 psi2` from the two fixed-point equations alone.
    Cases reduce to existing `sambin_uniqueness_via_no_occurrence`,
    `sambin_uniqueness_via_top_class`, `fixed_point_unique_loeb_form`,
    `fixed_point_unique_for_box_atomic`; the recursive
    `SC_impl_left_no_occ` case shares its construction with item 22.
26. Replace `same_level_fixed_point_uniqueness_assumed` with
    `sambin_uniform_uniqueness_boxed`: `Nec n` lift of 25.
27. Prove the full de Jongh-Sambin uniqueness over arbitrary
    modalised formulas (combining `sambin_uniqueness_loeb_general`,
    `sambin_uniqueness_box_atomic_general`,
    `sambin_uniqueness_via_no_occurrence`,
    `sambin_uniqueness_via_top_class`).
28. Implement an explicit fixed-point computation algorithm: given
    a modalised `phi(p)`, return a syntactic `psi` in normal form
    plus a derivation of the equivalence; prove the algorithm
    correct.

29. Build a sequent presentation `SC_GLP : list Form -> list Form ->
    Prop` with structural rules, propositional rules, and per-level
    modal rules with the Löb side-condition.
30. Prove cut admissibility structurally for the sequent calculus
    (Avron-Negri-von Plato discharge mechanism for the Löb case).
31. Prove cut-free derivations exist for every theorem and have
    bounded modal depth as a function of the conclusion, giving a
    constructive bound on proof complexity.

32. Define `Maehara_interpolant_real` by structural recursion on a
    cut-free derivation; prove the standard Maehara case-split at
    every rule with the invariant FV(χ) ⊆ FV(Γ₁) ∩ ({phi} ∪ FV(Γ₂))
    and analogous bound on box-levels.
33. Rename current `Maehara_constructive_interp_*` lemmas to
    `self_interpolation_via_conjunction_*` to clarify they are not
    Maehara.
34. Prove genuine Craig interpolation: for every `|- Impl phi psi`,
    exhibit `chi` whose free variables and Box-levels are strictly
    contained in the intersection of those of `phi` and `psi`,
    via cut-free proof induction.  Current "interpolation" theorems
    return `phi` or `psi` themselves and defeat the
    vocabulary-restriction content.
35. Prove Lyndon interpolation: the interpolant additionally
    preserves polarity of variable occurrences.
36. Prove uniform interpolation: for every `phi` and variable `p`,
    exhibit `phi_p` not containing `p` such that for every `psi`
    not containing `p`, `|- Impl phi psi <-> |- Impl phi_p psi`.
37. Prove Beth definability in its full form: every implicitly
    definable predicate is explicitly definable.

38. Prove `Lindenbaum_limit_maximal`:
    `forall Gamma, Consistent Gamma -> forall phi,
    Lindenbaum_limit Gamma phi \/ Lindenbaum_limit Gamma (Neg phi)`.
    Construction: `n := encode_form phi`; by `decode_encode`,
    `Form_seq n = phi`; the (S n)-th iteration of `lindenbaum_extend`
    decides `phi` by `lindenbaum_extend_decides`.
39. Prove `Lindenbaum_limit_deductively_closed`:
    `Provable_set (Lindenbaum_limit Gamma) phi ->
    Lindenbaum_limit Gamma phi`.
    Construction: bound the iteration by max `encode_form` over the
    finite hypothesis list; the alternative branch would contradict
    `lindenbaum_iterate_consistent`.
40. Define `canonical_world_max := { Γ | Consistent Γ /\ maximal /\
    deductively_closed }`; lift `canonical_R` to it; prove the
    modal truth lemma over the maximal-consistent canonical model.
41. Prove `canonical_R` satisfies transitivity from `Ax_Box4`.
42. Prove `canonical_R` satisfies monotonicity from `Ax_Mon`.
43. Prove `canonical_R` satisfies NextCon-successor from
    `Ax_NextCon`.
44. Prove `canonical_R` satisfies converse-well-foundedness from
    `Ax_Loeb`.
45. Extend the canonical-model truth lemma to the full modal
    language (`Box n psi` case) by structural induction on `phi`,
    including the non-trivial backward direction requiring a
    witnessing world for the negation.
46. Prove the existence-lemma for the canonical model: every
    consistent formula is true at some canonical world; chain to
    strong completeness rather than weak completeness.

47. Prove Kripke completeness of GLP*: every non-theorem is refuted
    by some GLP*-frame.
48. Prove Kripke completeness for `Provable_no_NC`,
    `Provable_no_Mon`, `Provable_no_Loeb`, `Provable_no_B4`
    separately, with their distinguishing frame classes.
49. Prove modal compactness: a set of formulas has a model iff
    every finite subset does.
50. Prove ω-completeness for `Fnat`: every formula valid at every
    world of `Fnat` is provable; characterise the formulas valid
    in `Fnat` as a sublogic of GLP*.
51. Construct the universal frame for GLP* and prove it is the
    canonical Kripke model up to bisimulation.

52. Implement filtration through a finite subformula-closed set Σ;
    prove the resulting finite model preserves truth values for
    formulas in Σ.
53. Prove the finite frame property: every non-theorem of GLP* is
    refuted on some finite frame.
54. Prove finite-model property with effective bounds: every
    non-theorem is refuted on a frame of size at most exponential
    in the formula's modal depth.
55. Prove a selection theorem: from a Kripke model extract a
    generated submodel containing a designated point bisimilar to
    the original at that point.

56. Implement a true PSPACE decision procedure for the full
    polymodal language via filtration; prove a Coq-verified PSPACE
    complexity bound, replacing the present `pspace_check_iter`
    which only handles propositional truth-table evaluation.
57. Prove decidability of the full polymodal calculus via filtration
    plus 53.
58. Prove PSPACE-completeness of GLP* satisfiability/provability,
    by reducing QBF to provability in GLP*.
59. Prove the box-free fragment coNP-complete via a verified
    reduction from UNSAT.
60. Provide a verified extracted decision procedure operating on
    actual inputs and producing certificates, rather than a
    Coq-internal `sumbool` mediated by classical excluded-middle.
61. Implement and verify a tableau procedure for GLP* that produces
    either a closed tableau (proof) or an open branch
    (countermodel).
62. Verify a SAT/QBF-based reduction of box-free GLP* validity and
    extract a procedure calling an external solver, with the
    soundness of the reduction proven in Coq.
63. Replace `decidability_admissibility_box_free` (whose conclusion
    is `sumbool (... -> True) True`) with
    `decidability_admissibility_box_free_canonical`:
    a real `sumbool` of `(forall sigma, |- subst_form sigma phi)`
    against its negation, witnessed by `decide_tautology phi`.
64. Prove decidability of admissible rules (Rybakov's theorem) for
    at least the box-free fragment, with a real decision procedure
    rather than a vacuous skeleton.
65. Prove a decidability result for the bimodal `Box n + Box m`
    fragment with `n ≠ m` distinct from the full polymodal case.
66. Prove the existence of a finite refuting frame for every
    specific non-theorem (not just `Box n Bot`).
67. Prove a proper Kalmár-style completeness for the `Sigma1_modal`
    closure (not just box-free).

68. Prove the full Reflection Calculus completeness theorem for
    strictly positive formulas.
69. Prove decidability of the closed (variable-free) fragment with
    explicit complexity bounds via filtration.
70. Establish decidability of the variable-free fragment with
    bounded modal depth and exhibit the complexity class precisely
    (likely PSPACE in the depth bound).
71. Prove the Abashidze-Japaridze characterisation of the closed
    fragment of `Provable_GLP`.

72. Prove independence of `Ax_K` using non-Kripke (e.g. neighborhood)
    semantics, via a calculus-soundness theorem against the
    neighborhood semantics that omits Ax_K.
73. Prove `Ax_DN` is independent of K, S, BoxK, Loeb, Box4, Mon,
    NextCon by exhibiting an intuitionistic-modal frame validating
    the others but refuting DN.
74. Establish a complete independence matrix: for each pair of
    axioms, exhibit a model validating one but not the other.
75. Prove minimality of the axiom set: removing any axiom strictly
    weakens the calculus, with each minimality result witnessed by
    a specific theorem that fails.
76. Prove that each axiom-removal calculus is strictly weaker than
    `Provable` for infinitely many distinct theorems.
77. Prove undecidability of any extension of GLP* with binary
    modalities corresponding to interpretation, by reduction from
    the halting problem or a known undecidable modal logic.

78. Strengthen `is_modal_definable` to require the witnessing
    formula to land in a syntactically restricted fragment matching
    the property's intended class; restate the bisim-invariance
    theorems on the strengthened predicate.
79. Prove the unconditional reverse direction of van Benthem: every
    bisimulation-invariant first-order property over ω-saturated
    models is modally definable.
80. Prove the full Goldblatt-Thomason theorem characterising
    modally-definable frame classes.
81. Prove Sahlqvist correspondence in its general form (not just
    for K, Löb).
82. Prove the polymodal Fine-Schurz incompleteness result
    identifying GLP*-formulas not derivable in any Kripke-complete
    sub-logic.

83. Construct the Lindenbaum-Tarski algebra explicitly as a
    quotient type with proven decidable equality on equivalence
    classes (where decidability holds); prove it is the free
    Magari algebra on countably many generators.
84. Prove Magari (diagonalisable algebra) completeness: every GL
    theorem holds in every Magari algebra and conversely; the
    Lindenbaum-Tarski algebra is the free Magari algebra on the
    propositional variables.
85. Prove Jónsson-Tarski / Stone duality between the
    Lindenbaum-Tarski algebra and the canonical frame, in the
    style of Stone duality for Boolean algebras lifted to modal
    algebras.
86. Establish that the variety generated by Magari algebras is
    locally finite for the box-free fragment and prove a
    McKinsey-Tarski-style algebraic completeness result.
87. Prove a genuine categorical-semantics theorem: define a
    category of GLP*-frames with bisimulation-respecting morphisms;
    prove `Provable` corresponds to global sections of a sheaf or
    similar structure.
88. Establish a categorical equivalence between provability-style
    modal logics and a class of preordered algebras, in the manner
    of Esakia duality for intuitionistic logic.
89. Replace `categorical_fixed_point_for_licenses` and
    `categorical_fixed_point_for_T_kappa` (currently
    `prov_iff_refl`) with `licenses_universal_property_categorical`:
    `forall F, (preserves provability) -> (K-distrib) ->
              (monotonicity) -> (Loeb closure) ->
    forall n phi, |- Iff (F n phi) (Box n phi)`.
    Subsumes both old aliases as instances at `F := licenses` and
    `F := T_kappa`.  Subsumes and strengthens
    `licenses_axiomatic_uniqueness`.
90. Strengthen `licenses_axiomatic_uniqueness` to non-extensional
    candidate operators via a categorical universal property —
    uniqueness as the unique-up-to-provable-equivalence functor
    preserving `|-` and admitting `Ax_BoxK`, `Ax_Loeb`, `Ax_Mon`.

91. Replace `FairBot_diagonal_collapse_to_Top` with
    `FairBot_diagonal_collapses_to_Top_uniform`:
    `forall n psi, |- Iff psi (Box n (Iff psi Cooperate)) ->
                   |- Iff psi Top`.
    Construction: `|- Iff (Iff psi Top) psi` by `prop_completeness`;
    lift to `|- Iff (Box n (Iff psi Cooperate)) (Box n psi)` via
    `prov_equiv_box_cong`; chain through the hypothesis to
    `|- Iff psi (Box n psi)`; close with
    `fixed_point_unique_for_box_atomic`.
92. Replace `no_go_strict_tiling_inconsistency_collapse` with
    `no_go_uniform_strict_tiling_collapse`:
    `(forall psi, |- Box (S n) (Impl (Box n Top) (Box n (Neg psi))))
    -> |- Bot`.
    Construction: `prov_box_top` + `Nec (S n)` →
    `|- Box (S n) (Box n Top)`; instantiate at `psi := Top`; apply
    `Ax_BoxK (S n)`; lift via `Box n Top -> Box n Bot` (BoxK +
    `prov_box_top`) to `|- Box (S n) (Box n Bot)`; combine with
    `Ax_NextCon n` and `prov_box_n_contradiction (S n)` to derive
    `|- Box (S n) Bot`; conclude via
    `meta_consistency_every_level (S n)`.
93. Replace `no_go_strengthening_collapses` with
    `no_go_uniform_negative_strengthening`:
    `(forall psi, |- Impl (Box n Bot) (Neg (Box n psi))) -> |- Bot`.
    Construction: instantiate at `psi := Top`; combined with
    `prov_box_top` derive `|- Neg (Box n Bot)`; lift via `Nec n`;
    apply `godel_second n` to get `|- Box n Bot`; chain to
    `|- Bot`.
94. Two-step replacement of `QGLP_full_undecidability_witness` plus
    the broken `QGLP_provable` (currently `True` on `Q_forall` /
    `Q_exists`):
    (a) define `QGLP_kripke_valid` over constant-domain Kripke
        frames with first-order quantifiers;
    (b) prove
        `forall decide, (forall q, decide q = true <->
        QGLP_kripke_valid q) -> False`,
    by reduction from undecidability of finite-validity for monadic
    FO with one binary relation; transfer Trakhtenbrot.

95. Replace `agent_modal_T_kappa_correspondence` with
    `agent_T_kappa_lattice_iso`:
    a lattice-isomorphism statement between `Provable_agent n` and
    `T_kappa n` that includes the lattice-preservation clause
    `forall phi psi, |- Iff phi psi <-> |- Iff (Phi phi) (Phi psi)`
    requiring `prov_equiv_impl_cong` + `prov_equiv_box_cong` over
    the agent-licensure quotient.
96. Replace `Aumann_agreement_modal` (currently `prov_iff_refl` +
    `prov_box_mon_le`) with the genuine modal Aumann theorem:
    agents at different levels with common knowledge of consistency
    provably agree on the consistency of any propositional sentence.

97. For every `Theorem foo : ... Proof. exact bar. Qed.` style
    one-line restatement currently in `Tiling.v`, replace with a
    strengthened version that adds quantitative, categorical, or
    proof-length content.  Specific instances:

    (a) `Pudlak_super_polynomial_speedup_witness` →
        `Pudlak_super_polynomial_speedup_real`:
        exhibit `phi` plus a level-(S n) proof term whose size is
        bounded, alongside the absence of any level-n proof term
        (vacuously infinite gap dominates polynomial bound).
        Instantiate `phi := Neg (Box n Bot)`; impossibility uses
        `meta_consistency_every_level n` + `godel_second n`.

    (b) `connection_to_beklemishev_hierarchy` →
        `Beklemishev_hierarchy_aligned`: define a Beklemishev-style
        enumeration `Bek : nat -> Form` and prove
        `|- Box (S n) (Bek n) /\ ~ |- Box n (Bek n) /\
        |- Iff (Bek n) (Neg (Box n Bot))`.

    (c) Apply the same audit to
        `proof_theoretic_ordinal_strict_layering`,
        `reflection_principle_hierarchy`,
        `transfinite_consistency_chain_repr`,
        `HoTT_GLP_correspondence_via_modal_box4`,
        `omega_completeness_indexed_by_naturals`,
        `sahlqvist_correspondence_for_K`,
        `sahlqvist_correspondence_for_Loeb`,
        `Magari_diag_*`, `transfinite_Box_*`,
        `Friedman_Sheard_*`, `single_modal_embedding_*`,
        `Visser_interp_*`, `Temporal_Box_*`, `Graded_Bel_*`.
        Each replacement must add a quantitative bound, a
        categorical universal property, a derivation-length
        witness, or a frame-class characterisation that the bare
        alias does not provide.

98. Construct a genuine arithmetic Σ₁ provability predicate
    `Bew_PA` over a Gödel-encoded fragment of arithmetic (formulas
    as numerals, proofs as numerals); prove the Hilbert-Bernays-Löb
    conditions for it.
99. Replace the primitive `Box n` view with a Σ₁ predicate
    `Bew_n : nat -> Prop` defined over a Gödel-numbered syntax of
    formulas and proofs, such that `Bew_n ⌜φ⌝` holds iff there
    exists a code `p` with `Proof_n(p, ⌜φ⌝)`; prove the HBL
    conditions as theorems about this predicate rather than
    postulates.
100. Prove an internal Gödel diagonalisation lemma: for every `φ(p)`
     with one free variable, construct `ψ` with
     `|- Iff ψ (φ ⌜ψ⌝)` where `⌜ψ⌝` is the actual Gödel number;
     use it to derive Gödel's first and second incompleteness
     theorems internally.
101. Construct, for each `n`, a Gödel sentence `Gₙ` with
     `|- Iff Gₙ (Neg (Bew_n ⌜Gₙ⌝))`; prove `Gₙ` is independent of
     `Tₙ` but provable in `Tₙ₊₁` — the genuine arithmetic content
     the modal calculus is supposed to abstract.

102. Construct in Coq an explicit recursive enumeration of axioms
     for each `Tₙ` as actual arithmetic theories extending Robinson
     Q (or PA), with the level-(n+1) theory containing the Σ₁
     sentence `Con(Tₙ)`; prove cumulativity as a theorem about
     provability rather than a definitional inclusion.
103. Construct a first-order theory `T_n` with explicit axioms (not
     just modal axiom-schemas via `T_axiom`); prove the
     cumulativity, consistency, and tiling results at the genuine
     first-order level.
104. Eliminate `Ax_NextCon` from the axiom list and instead derive
     `Box (S n) (¬ Box n ⊥)` from properties of an underlying
     arithmetic theory, demonstrating the bypass arises from
     genuine proof-theoretic strength rather than a postulate that
     bakes in the conclusion.
105. Establish a non-trivial consistency-strength ordering between
     `Tₙ` and `Tₙ₊₁` by proving an ordinal analysis result —
     proof-theoretic ordinal of `Tₙ` strictly less than that of
     `Tₙ₊₁` in a recognised ordinal notation system — so that
     ascending the tower corresponds to a measurable increase in
     strength.
106. Prove the tower bypass non-vacuous by exhibiting a specific
     `φ` such that `Tₙ` does not prove `Con(Tₙ → φ)` but `Tₙ₊₁`
     does, where the gap is essential to a successor-agent
     licensing decision.
107. Prove a soundness theorem connecting modal `Box n φ` to the
     arithmetised `Bew_n ⌜φ*⌝` for a realisation map `φ ↦ φ*`,
     exhibiting the modal calculus as the propositional reasoning
     principles inherited from the arithmetic tower rather than as
     an independent object.
108. Prove Π₁ conservativity of `T_(n+1)` over `T_n` for arithmetic
     Π₁ sentences.
109. Prove Π₂ conservativity across the tower.
110. Prove Friedman's negative translation result connecting
     classical to constructive provability beyond the box-free
     case.
111. Prove the relative-consistency direction `Con(T_0) → Con(T_n)`
     from a strictly weaker hypothesis than meta-consistency of the
     full system.
112. Prove `T_no_self_consistency` directly from `Bew`'s HBL
     conditions rather than routing through the full Provable
     calculus.
113. Prove the strict separation between `Bew n` and `Bew (S n)` at
     the proof level (not just at the axiom-set level).
114. Prove that the structural `Bew` predicate satisfies provability
     logic (i.e. `Bew n` interpreted into `Box n` validates exactly
     GLP* at the relevant level).

115. Prove Solovay's first completeness theorem in full: every
     modal formula valid under all arithmetic interpretations into
     PA is provable in GL, via the encoding of finite Kripke models
     as PA-definable functions.
116. Prove Solovay's second completeness theorem for the
     truth-extension `Provable_S` beyond the box-free fragment,
     via the encoding into the standard model.
117. Prove arithmetic completeness of `Provable_GLP` (Japaridze's
     theorem) for arbitrary formulas, not just box-free ones,
     reading `◇_n` as "provable using `n` applications of the
     ω-rule" or an equivalent reflection schema.
118. Construct a genuinely non-identity, non-licensure inhabitant of
     `is_arithmetic_interpretation` to show the predicate has
     non-trivial structure beyond `identity` and `licenses k`.
119. Prove the Friedman-Sheard truth-axiomatisation theorem.
120. Construct a hierarchy of partial truth predicates `Trₙ` where
     each `Trₙ` correctly evaluates formulas of modal depth `≤ n`,
     with `Trₙ` definable at level `n+1`, paralleling Tarski's
     hierarchy and matching the licensing tower.
121. Prove Tarski undefinability in its sharpest form: no formula
     `Tr(x)` in the language of GLP* with one free variable
     satisfies `|- Iff (Tr ⌜φ⌝) φ` for all `φ`.
122. Prove a strong undefinability theorem by Gödel diagonalisation
     on a self-referential sentence, in any consistent extension of
     the calculus with a unary `Tr` satisfying the T-schema.

123. Prove the Visser interpretability logic ILM/ILP axioms beyond
     just the K-distribution and Box4 forms.
124. Prove the Visser-Berarducci theorem on interpretability logic:
     ILM is the interpretability logic of any reasonable arithmetic
     theory containing IΣ₁, with the modal axioms corresponding to
     actual interpretation-preservation principles.
125. Prove the Visser ILM J5 axiom from the calculus axioms rather
     than via `Ax_Mon`.

126. Prove the Critch parametric bounded-Löb theorem for a genuinely
     bounded provability predicate (with proof-length bound encoded
     inside the modal formula), not just iterated `Box`.
127. Prove the Critch correspondence between modal
     `critch_bounded_box` and a genuine bounded-arithmetic
     provability predicate with explicit polynomial bounds.
128. Implement Critch's bounded provability with an explicit
     resource bound `k` counting proof steps; prove a parametric
     Löb theorem with a threshold `k₀` such that `Bew^k` proves Löb
     iff `k ≥ k₀`, with `k₀` explicitly computable from the
     formula being verified.
129. Construct a concrete agent using bounded provability whose
     behaviour depends measurably on `k` (e.g. cooperates against
     `k`-bounded FairBot for `k` above a threshold and defects
     below), showing the bound is not a notational artifact.

130. Replace the cosmetic alias `licenses n φ := Box n φ` with a
     substantive predicate over a separately defined `Agent`
     record carrying a decision procedure, a goal predicate, an
     action space, and a verification routine.  Prove tiling
     theorems about the interaction of these components rather
     than about renamed boxes.
131. Formalise a concrete agent that takes as input a candidate
     successor (encoded as a program or proof-search procedure)
     and outputs a decision in finite time based on inspection of a
     level-`n` proof, with safety theorems quantifying over actual
     decisions rather than over modal formulas standing in.
132. Prove a non-trivial successor-licensing theorem: given an
     explicit goal predicate `G`, an explicit transition function,
     and an explicit candidate successor `σ`, derive that the
     level-`n` agent licenses `σ` iff a verifiable condition on
     `σ` holds, where the condition is computable and the licensing
     decision is not the trivial "license everything provable".
133. Demonstrate a concrete failure case where a level-`n` agent
     cannot license a successor that a level-(n+1) agent can,
     using actual programs and goals rather than uninterpreted
     formulas, so that the tower's stratification has observable
     behavioural content.
134. Prove the goal-preservation tiling theorem for an agent that
     takes non-trivial actions changing the state.
135. Prove vingean reflection in a setting where the agent's
     decision genuinely depends on `T_(n+1)` licensure (not
     vacuously satisfied by `cautious_agent`).
136. Prove the no-panic reflective-trust theorem at the level of
     self-modifying agents, not just modal consistency.
137. Prove the `T_kappa` agent-correspondence theorem with a
     non-trivial agent architecture.
138. Prove Aumann's agreement theorem in modal form: agents at
     different levels with common knowledge of consistency provably
     agree.

139. Define `FairBot n psi := psi := Box n (Iff (opp psi) Cooperate)`
     as a real Sambin fixed point where `opp` reads from the open
     variable; prove existence via
     `fixed_point_existence_top_solves` applied to the modalised
     self-referential formula.
140. Define `PrudentBot n psi` as a real Sambin fixed point with
     the consistency conjunct
     `Box (S n) (Neg (Box n Bot))`.
141. Replace the constant `Cooperate := ⊤` with a genuine action
     representing cooperation in a payoff-bearing game; prove two
     FairBots reach the cooperative payoff via a fixed-point
     construction whose witness is non-trivially derived from the
     opponents' code.
142. Prove FairBot vs FairBot mutual cooperation with the genuine
     fixed-point semantics and source-code reflection.
143. Prove FairBot vs DefectBot defection.
144. Prove FairBot vs CooperateBot mutual cooperation and FairBot
     vs DefectBot mutual defection as theorems where the bots
     access opponents' source code via a reflection principle, with
     the proof structurally distinguishing the two cases rather
     than collapsing both to ⊤.
145. Prove the BCFHLY robust-cooperation theorem for non-trivial
     fixed points (not just the collapse to `Top`).
146. Prove that PrudentBot strictly dominates FairBot in modal-PD
     against DefectBot, exhibiting concrete formula witnesses.
147. Establish PrudentBot's strict Pareto improvement over FairBot
     by exhibiting an opponent against which PrudentBot defects
     correctly but a naïve FairBot would cooperate, with both bots
     formalised as concrete proof-search procedures.

148. Prove the Fallenstein-Soares 2014 finite-tower
     self-modification theorem at the arithmetic level: a
     `T_n`-using agent provably-safely transitions to a
     `T_(n+1)`-using agent.
149. Prove the Pudlák speedup result for the parametric tower at
     every level (super-polynomial in proof length when ascending
     the hierarchy).
150. Prove a quantitative version of the Löbian obstacle: bound the
     proof length of the inconsistency derivation by a function of
     the reflection-schema's proof complexity.
151. Formalise the original Yudkowsky-Herreshoff tiling agent as a
     concrete program: a Turing machine that, given a candidate
     successor, performs a bounded proof search at level `n`,
     decides licensing based on a specific verification predicate,
     and outputs a decision.
152. Prove the tiling-agent never-defects-against-itself theorem:
     when two such agents face each other in a coordination game,
     both license the cooperative strategy via a common-knowledge
     fixed point.
153. Establish the Vingean reflection no-go result formally: an
     agent with full access to its own source code and proof system
     cannot license self-modification without invoking a strictly
     stronger meta-theory, replacing the present licensing-bypass
     with the proof-theoretic obstacle it is meant to circumvent.
154. Prove the Fallenstein parametric bounded Löb result: bounded
     Löb with parameter `k` holds iff the agent's verifier has
     access to proofs of length at least `k`, with the threshold
     explicitly computable from the formula being verified.
155. Connect the tower to a concrete model of self-improvement:
     prove that an agent at level `n` licensing a successor at
     level `n+1` corresponds to a specific code transformation
     preserving a goal predicate, with the transformation explicit
     and the preservation verified.

156. Re-derive the worm theory inside a calculus where Mon is
     absent (genuine GLP), so worms have non-trivial provability
     content and the worm-ordinal correspondence captures real
     proof-theoretic strength rather than collapsing.
157. Prove Beklemishev's worm normal form theorem for
     `Provable_GLP` (where worms are not all provable), not just
     the trivial collapse in `Provable`.
158. Prove the Beklemishev reduction theorem: every theorem of GLP
     is provably equivalent (in GLP) to a Boolean combination of
     worms, with the equivalence computable.
159. Prove the worm-ordering total: for any two worms `w₁`, `w₂`,
     decide which provably implies the other in GLP, with the
     ordering matching Cantor-normal-form comparison on
     `worm_to_ord`.  Replaces the vacuous "ordering total" theorem
     in the Mon-stipulated calculus.
160. Prove that the proof-theoretic ordinal of GLP (without Mon)
     equals ε₀ via Beklemishev's worm normalisation, with
     `worm_to_ord` providing the order isomorphism between
     worm-equivalence-classes and ordinals below ε₀.
161. Prove the proof-theoretic ordinal of `Provable_GLP` is exactly
     ε₀ via a complete ordinal-assignment to proof terms with
     strict decrease under reduction.
162. Compute the proof-theoretic ordinal of GLP* as presented and
     prove a sharp upper and lower bound, distinguishing it from GL
     (ω^ω), GLP (ε₀), and the Mon-stipulated calculus (which
     collapses because all worms are theorems).
163. Replace the syntactic `Veblen_phi_iter` and `Gamma_0_approx`
     shells with the genuine Veblen hierarchy as ordinal functions;
     prove their fixed-point properties.
164. Prove Carlson's theorem on the ordinal-analysis correspondence
     between worms and ordinals below ε₀.
165. Prove Carlson's theorem (second incompleteness for polymodal
     provability) in its sharp form.
166. Prove the explicit ε₀-rank-respecting normalisation theorem
     for proof terms with strict ordinal decrease (currently
     `proof_term_ordinal` is defined but no decrease theorem under
     reduction is proved).
167. Prove Gentzen's consistency proof for PA via ε₀-induction
     inside Coq; verify that the analogous argument bounds the
     strength of the GLP*-arithmetic hierarchy.

168. Define a genuine first-order extension `QGLP` with quantifiers,
     variable assignments, and a Tarskian semantics; prove which
     fragments are decidable, which are recursively enumerable,
     and which are Π¹₁-complete, replacing the present one-line
     stub.
169. Prove constant-domain QGLP* soundness and completeness with
     respect to a Kripke-style first-order semantics for quantified
     modal formulas.
170. Prove the Barcan and converse-Barcan formulas hold or fail in
     the quantified extension, with semantic witnesses.
171. Prove a genuine temporal-extension result where time and modal
     level interact non-trivially (e.g. temporal succession changes
     the proof-theoretic ordinal).
172. Prove a probabilistic-Löb theorem with a real probability
     parameter (not just `nat`) showing graded reflection survives
     at strictly positive ε.
173. Define a probabilistic logic of provability with graded
     modalities `Bel_p` where `p` is a probability; prove sound
     and complete with respect to a measure-theoretic semantics.
174. Connect the probabilistic version to actual decision-theoretic
     agents using credences, with the modal calculus becoming a
     logic of degrees of belief rather than provability.
175. Construct a proper neighborhood-semantics framework; prove
     soundness/completeness for a non-normal modal logic separating
     it from GLP*.
176. Formalise a transfinite-level extension where modalities are
     indexed by ordinals below Γ₀ (in Veblen normal form); prove
     the resulting calculus consistent; recover the polymodal
     calculus as the ω-restriction.

177. Extend the calculus with a μ-operator for least fixed points;
     prove the resulting μGLP is decidable; recover Sambin fixed
     points as μ-definitions.
178. Prove the modal μ-calculus alternation hierarchy is strict at
     every level, with concrete formulas at each alternation depth
     not expressible at lower depths.
179. Establish the Kozen completeness theorem for μGLP and connect
     μ-fixed points to the parametric tower's fixed-point
     licensing decisions.
180. Define a game semantics for GLP* where verifier and falsifier
     play over the Kripke frame; prove a formula is true at a
     world iff the verifier has a winning strategy starting there.
181. Establish determinacy for the resulting games on well-founded
     frames; connect winning strategies to proof terms.
182. Connect the FairBot/PrudentBot constructions to actual
     game-theoretic equilibria via the game semantics, replacing
     the modal-formula stand-ins with strategy profiles.
183. Prove the modal logic of programs (PDL) embeds into GLP* via
     a translation mapping program iteration to fixed points; use
     it to formalise agent decision procedures as programs.
184. Connect Coalition Logic and ATL to the licensing tower, where
     coalitions correspond to multi-level licensing groups and the
     modalities express what coalitions can ensure.

185. Prove the disjunction property for `Provable_GLP`: if
     `|- Or (Box n phi) (Box m psi)` then `|- Box n phi` or
     `|- Box m psi`.
186. Prove that `Provable_GLP_incomparable_with_provable` extends
     to infinitely many incomparable formulas, witnessing genuine
     logical separation.
187. Prove a no-go theorem for any uniform strengthening of
     `Ax_NextCon` to `Box n (Neg (Box n Bot))` across all levels.
188. Prove that the `Provable_plus` extension scheme yields
     inconsistency for any reflection-schema extension at any
     level uniformly.
189. Prove the reverse direction of
     `licensing_consistency_concrete_converse` quantifying over all
     formulas at level `n` simultaneously.
190. Prove the Smoryński bimodal independence theorem at distinct
     levels for non-trivial formulas.

191. Prove the full conservativity of `Provable_GL` over `Provable`
     at level 0 in both directions (currently only one direction
     is fully proved without using the trivial `forget_levels`
     collapse).
192. Establish the conservativity of GLP* over GL at level 0 in
     both directions and over Japaridze's GLP at all levels, with
     explicit syntactic translations and proofs that each is
     faithful.
193. Prove a conservativity ordering: GLP* is conservative over GL
     for level-0 sentences, conservative over a specific theory of
     arithmetic for Π₁ sentences, and exactly captures something
     specific for Σ₁ sentences.
194. Prove the polymodal-fixed-point system completeness à la
     Smoryński.

195. Define a realisability interpretation of GLP* where realisers
     are verified programs; prove every theorem has a realiser,
     with the realiser extracted by Coq's extraction.
196. Prove a Curry-Howard correspondence for the modal fragment:
     proof terms correspond to programs with staged computation,
     where `Box n` corresponds to a level-`n` computation phase.
197. Establish a propositions-as-types interpretation where
     licensing translates to the existence of a verified compiler
     from level-`n` programs to level-(n+1) programs.
198. Embed GLP* into homotopy type theory; prove the modal axioms
     correspond to specific type-theoretic constructions,
     recovering "polymodal provability" as a type-level phenomenon.
199. Connect `Box n` to a graded comonad in the categorical
     semantics, with the levels corresponding to computational
     stages in a staged-computation interpretation; prove the
     graded comonad laws as theorems.

200. Determine the reverse-mathematical strength of each major
     theorem in the development: which require ACA₀, which RCA₀,
     which WKL₀.
201. Prove that `meta_consistency_system` requires no more than
     primitive recursive arithmetic, isolating the foundational
     floor of the construction.

202. Extract a verified OCaml or Haskell decision procedure from
     the Coq development; benchmark against existing modal-logic
     provers (LWB, MOLLE, etc.).
203. Use the formalisation to verify a real safety property of a
     real machine-learning system, demonstrating practical traction
     beyond toy examples.
204. Connect the verification to a runtime monitor that rejects
     unsafe operations based on level-`n` proof obligations, with
     the monitor extracted from Coq and benchmarked.
205. Prove a non-trivial program transformation correct using the
     modal apparatus, where the transformation is one a real
     compiler might perform and the correctness one a real verifier
     would care about.

206. Split `Tiling.v` into themed modules — `Calculus`, `Hilbert`,
     `Kripke`, `FixedPoints`, `Bew`, `ProofTerms`, `Worms`,
     `Agents` — keeping the dependency DAG acyclic.  Update
     `_CoqProject` and `Makefile`.
207. Add `Examples.v` with three worked examples: consistency-of-PA
     from consistency-of-Q in the modal abstraction; Gödel's second
     incompleteness specialised to a concrete formula; an
     agent-tower with a non-cautious agent that uses `Bew (S n)`
     licensure.
208. Add `README.md` listing the headline theorems, the dependency
     story, and build instructions.
209. Provide tutorial sections explaining the proof strategies,
     with worked examples connecting each major theorem to its
     informal counterpart in the literature, making the development
     accessible to non-modal-logicians.
210. Cross-reference each theorem to its source in Boolos's *The
     Logic of Provability*, Smoryński's *Self-Reference and Modal
     Logic*, Beklemishev's papers, and the YH13 tech report, with
     citations precise enough to verify correspondence.
