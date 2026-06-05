# tiling-verified todo

Open research programs for the GLP* formalization, ordered by logical
completion: each item's prerequisites appear earlier. Every entry names a
specific construction or computational artifact and lists the forbidden
trivializations (which deliberately rule out the present schematic
implementations, so an item is not closed by re-aliasing what exists).

Completed work is not tracked here. It is documented in each definition's
section comment, the `*_summary` bundle theorem near it, the README, and the
git history.

---

1. **First-order arithmetic layer.** The marquee "arithmetic completeness"
   results are transposed into the modal `Form` language: `arith_embed_GL`
   / `arith_embed_S` are substitutions, `is_Pi_2` is a modal class,
   standard-model satisfaction is `classical_valid`, completeness is
   instantiated at fixed substitutions. Build the arithmetic layer: an
   inductive `ArithForm` (terms over `0`, `S`, `+`, `*`; relations `=`,
   `<`; connectives and `forall`/`exists`), an N-satisfaction relation
   `sat : (nat -> nat) -> ArithForm -> Prop`, a Goedel numbering, and a
   Sigma_1 provability predicate `Prov_T` for an inductively presented
   theory `T` (EA or PA) satisfying the three Hilbert-Bernays-Loeb
   conditions against `sat`. Redefine the embeddings so `Box n` maps to
   the Sigma_1 provability sentence of `T_n`, and reprove `Solovay_first_full`,
   `Solovay_second_full`, `Japaridze_full_via_tree`, `Pi_2_conservativity`
   as statements about `Prov_T` and `sat`. Prove `arithmetic_layer_summary`.
   Forbidden: `standard_model_satisfies := classical_valid`;
   `arith_embed_* := subst_form`; instantiating any interpretation at
   `identity`/`shift_interp`; using `Bew_n` as the provability predicate
   without an N-satisfaction soundness proof; `is_Pi_2` a `Form` class
   rather than the `forall/exists` shape of `ArithForm`.

2. **Provable Sigma_1-completeness as a derived HBL condition.** Prove
   `provable_sigma1_completeness : forall sigma, is_sigma1 sigma ->
   Prov_T (Impl sigma (prov_sentence sigma))` derived inside `T`, with
   internal necessitation reduced to it. Prove `third_HBL_derived_summary`.
   Forbidden: a calculus rule (`Nec`, `TAx_Box4`) standing in for the
   condition; the condition imported rather than proved against `sat`.
   (Depends on item 1.)

3. **Reflection / consistency-strength bridge.** Prove
   `reflection_tower_correspondence : Prov_{T_{n+1}} <-> Prov_{T_n + RFN(T_n)}`
   (Beklemishev's Con/uniform-reflection tower). Prove
   `reflection_strength_summary`. Forbidden: a `Box n` correspondence
   stated without the RFN/Con content; the bridge posited as an axiom.
   (Depends on items 1, 2.)

4. **Single-level reflective trust.** Prove `single_level_self_trust :
   exists T, Prov_T (Con T) -> Prov_T (trusts T T)` against the item-1
   layer, or the machine-checked obstruction `single_level_trust_blocked`
   showing no consistent `T` trusts itself, with the Critch
   parametric/bounded variant as the strongest true form. Prove
   `reflective_trust_resolution_summary`. Forbidden: trust quantified over
   the tower; the obstruction asserted rather than derived from Loeb.
   (Depends on items 1, 2.)

5. **Faithfulness to canonical Japaridze GLP.** `NextCon` is only the
   `phi := Top` instance `Box (S n) (Diamond n Top)` of GLP's general
   negative-introspection scheme. Either prove the general scheme
   `forall n phi, |- Impl (Diamond n phi) (Box (S n) (Diamond n phi))`
   from the present axioms (establishing this calculus IS GLP), or exhibit
   a sound model in which it fails (establishing a proper subsystem) and
   document the divergence. Prove either
   `glp_faithfulness_general_introspection` or
   `glp_proper_subsystem_witness`. Forbidden: leaving the question open;
   proving only the `phi := Top` instance.

6. **Sequent presentation and cut-elimination.** Give a sequent calculus
   for GLP, prove equivalence to the Hilbert system, prove cut-elimination,
   derive the subformula property where it holds. Prove
   `sequent_cut_elim_summary`. Forbidden: cut admissibility asserted;
   equivalence stated in one direction only.

7. **Topological completeness for full GLP\*.** Only the box-free fragment
   has a completeness theorem; GLP* is relationally Kripke-incomplete and
   the neighborhood layer is a lone existence witness. Define
   neighborhood/scattered-topological (Ignatiev-style) semantics
   `forces_topo` with frame conditions, prove `soundness_topo` and the
   converse `topo_completeness : topo_valid phi -> |- phi` for ALL `phi`.
   Prove `topo_completeness_summary`. Forbidden: restricting to `box_free`;
   `topo_valid` via a single fixed frame; an existence statement standing
   in for completeness; routing through `prop_completeness`.
   (Sequent calculus from item 6 may assist.)

8. **Full decidability of GLP\*.** `glp_dec_b` only decides the
   box-tower-over-box-free fragment; provability is non-compositional, so a
   total decider needs a real finite/topological model property. Construct
   `glp_decide_total : forall phi, sumbool (|- phi) (~ |- phi)` total on
   every formula, with a computable model bound (Ignatiev model) or a
   terminating cut-free search, and prove `glp_decide_total_correct`.
   Forbidden: `excluded_middle_informative (|- phi)`; restricting to
   `is_iter_box_of_box_free`; falling back to `decide_tautology` on the
   box-free part only; deferring to a hypothetical normaliser.
   (Depends on item 7.)

9. **Constructed Feferman-Schuette Gamma_0.** `V_gamma0` is a declared
   nullary atom above the `V_phi` tower with well-foundedness asserted by
   fiat, and the height bound is non-tight. Define the two-argument Veblen
   function `veblen : ord -> ord -> ord` with the standard clauses, and
   `Gamma_0` as the least `a` with `veblen a OZero = a` (first strongly
   critical ordinal), proved the supremum of the iterated `veblen`-tower.
   Re-establish `GLP_proof_height_below_Gamma_0` against it and prove
   `veblen_Gamma_0_summary`. Forbidden: a nullary atom above the carrier by
   fiat; `Gamma_0 := veps0` or `V_phi 0 OZero`; asserting well-foundedness
   of the top point without deriving it from the Veblen construction.

10. **Ordinal proof-height directly on derivations.** Large elimination
    from `Prop` blocks `forall phi, |- phi -> vord`, so the rank lives on
    the Type-level `Provable_term`. Introduce a `Provable`-in-Type relation
    `ProvableT` with `proof_height : forall phi, ProvableT phi -> vord` and
    `ProvableT_iff : ProvableT phi <-> inhabited (Provable_term phi)`, or
    prove the `Provable_term` rank invariant across derivations of a given
    theorem. Prove `proof_height_on_derivations_summary`. Forbidden:
    keeping the rank only on `Provable_term` while stating it ranks `|-`;
    a constant rank; `proof_height _ _ := OZero`.

11. **Tight ordinal characterization.** Prove the worm/closed-fragment
    order type is exactly epsilon_0 (`worm_order_type_eps0`) and connect
    the proof-height bound to it (`proof_height_tight`). Prove
    `ordinal_analysis_tight_summary`. Forbidden: a non-tight bound
    relabeled as the order type; `V_gamma0` standing in for the epsilon_0
    result. (Depends on items 9, 10.)

12. **Stone equivalence with proof-relevant hom-setoids.** The current
    `StoneEquivalence` sets `ec_hom_eq := fun _ _ => True`, so naturality
    and the triangle identities hold only because all parallel morphisms
    are identified (preorder collapse). Replace the hom-equality with a
    genuine equivalence on morphisms (derivations modulo conversion/cut)
    and reprove `Stone_eta_natural`, `Stone_epsilon_natural`,
    `Stone_triangle_F`, `Stone_triangle_G` up to it. Prove
    `stone_proof_relevant_summary`. Forbidden: `ec_hom_eq := fun _ _ => True`;
    `hom_eq f g := |- Top`; any hom-equality identifying all parallel
    morphisms.

13. **Strict (non-setoid) Magari freeness.** `MagariFree` proves
    uniqueness only pointwise because intensional equality of morphism
    records is funext-strength. Build a setoid-enriched category whose
    hom-equality is pointwise by definition, and state `LT_GLP_free` as a
    genuinely unique morphism (a contractible space of homomorphisms
    extending the valuation). Prove `magari_strict_free_summary`.
    Forbidden: pointwise uniqueness stated outside a category whose homs
    are quotiented; appeal to `proof_irrelevance`/`functional_extensionality`.

14. **Lambda-box strong normalisation with live combinators.** The
    `LambdaBox` calculus keeps `tS`, `tBoxK`, `tLoeb`, `tBox4`, `tMon`,
    `tNextCon`, `tLoebFix` inert to keep the size measure decreasing, so
    realizers using them are stuck-normal. Give each its contraction rule
    (S duplication; a guarded `tLoebFix` unfolding) and prove strong
    normalisation by reducibility candidates (Tait-Girard), then reprove
    `extract_realizer_reduces` against the full reduction. Prove
    `lambda_box_SN_summary`. Forbidden: inert combinators with no reduction
    rule; `tLoebFix` as a value; a reduction relation containing only the
    K/pair/box-beta redexes; a size measure excluding the duplicating rules.

15. **Realizer extraction wired to agent decisions.** Extract executable
    decision procedures for FairBot/PrudentBot from their fixed-point
    proofs; prove `extracted_fairbot_correct : run (extract fairbot_proof)
    opp = fairbot_action opp`. Prove `agent_extraction_summary`. Forbidden:
    realizers left disconnected from `AgentRecord`; the extracted program's
    agreement asserted rather than proved. (Depends on item 14.)

16. **Finite agent, not a tower.** Define one finite agent with a bounded
    proof budget; prove `bounded_agent_tiling : forall budget,
    goal_preserved (rewrite_step agent budget)`. Prove
    `bounded_agent_summary`. Forbidden: indexing the successor at level
    `n+1`; unbounded proof search; goal preservation quantifying over the
    tower rather than over rewrite steps of one agent.

17. **Open-source / adversarial agent semantics.** Give the general
    modal-fixed-point treatment of opponents reading each other's source
    (the bot-vs-bot provability matrix); prove cooperation/defection
    outcomes across the standard opponent classes. Prove
    `program_equilibrium_summary`. Forbidden: results restricted to
    `opp = Cooperate_action`; outcomes proved only for the cooperate
    instance.

18. **Genuine QGLP quantifier semantics.** `QGLP_provable` sets
    `Q_forall _ _ := True` and `Q_exists _ _ := True`, making every
    quantified formula trivially provable. Give `QGLP_form` constant-domain
    Kripke semantics and an inductive derivability relation with real
    quantifier rules, prove `QGLP_soundness`, and (target) completeness.
    Prove `qglp_genuine_summary`. Forbidden:
    `QGLP_provable (Q_forall _ _) := True`;
    `QGLP_provable (Q_exists _ _) := True`; any clause whose truth is
    independent of the quantified body.

19. **Quantified provability logic of PA.** Formalize and prove
    Vardanyan's theorem that the quantified provability logic of PA is
    Pi^0_2-complete, stated over `Prov_T` and `ArithForm` from item 1.
    Prove `quantified_boundary_summary`. Forbidden: the result stated
    without the Pi^0_2-completeness content; QGLP Kripke completeness (item
    18) presented as the arithmetic completeness of the quantified logic.
    (Depends on items 1, 18.)

20. **Constructive core.** The development is wholly classical (`classic`,
    `constructive_indefinite_description`). Carve the syntactic/decidable
    results — box-free decidability, the Hilbert toolkit, proof-term
    reductions, `glp_dec_b` — into modules importing neither `Classical`
    nor `ClassicalEpsilon`, verified by `Print Assumptions`, and confine
    the classical axioms to the Lindenbaum/completeness parts. Prove (or
    `Print Assumptions`-witness) `constructive_core_summary`. Forbidden:
    importing `Classical`/`ClassicalEpsilon` into the constructive modules;
    `NNPP`/`classic`/`excluded_middle_informative` in any result claimed
    constructive.

21. **Cross-module coherence of the arithmetic layer.** Reprove every
    downstream consumer (Pi_2 conservativity, JaparidzeTree, TilingChain,
    the agent modules) against the item-1 `Prov_T`/`sat` definitions. Prove
    `arithmetic_layer_coherence_summary`. Forbidden: a consumer left on the
    surrogate `Bew_n`/`classical_valid`/`arith_embed_*`; coherence claimed
    without per-module `Print Assumptions`. (Depends on items 1, 2.)

22. **Per-theorem logic identification.** For every completeness, duality,
    and conservativity headline, fix the exact logic it concerns and prove
    it against that named system. Prove `logic_identification_summary`
    pairing each result with the system (GL, GLP, the proven subsystem, or
    GLS) it holds for. Forbidden: GLP attached to a theorem about a proper
    subsystem; identification recorded in prose only; a headline naming a
    stronger logic than the cited theorem proves. (Depends on item 5.)
