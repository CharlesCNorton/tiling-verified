# tiling-verified todo

Open research programs for the GLP* formalization. Each entry names a specific
construction or computational artifact, with the forbidden trivializations
listed, so that completion is unambiguous. The forbidden lists deliberately
rule out the present schematic implementations, so an item is not closed by
re-aliasing what already exists.

Completed work is not tracked here. It is documented in each module's header
comment, the `*_summary` bundle theorem at the end of each module, the
"Resolved research-program modules" section of `README.md`, and the git
history.

---

1. **Genuine first-order arithmetic layer.** The marquee "arithmetic
   completeness" results are currently transposed into the modal `Form`
   language: `arith_embed_GL`/`arith_embed_S` are substitutions,
   `is_Pi_2` is a modal formula class, "standard-model satisfaction" is
   `classical_valid`, and completeness is instantiated at fixed
   substitutions. Build a real arithmetic layer: an inductive
   `ArithForm` (terms over `0`, `S`, `+`, `*`; relations `=`, `<`;
   connectives and `forall`/`exists`), an N-satisfaction relation
   `sat : (nat -> nat) -> ArithForm -> Prop`, a Goedel numbering, and a
   Sigma_1 provability predicate `Prov_T` for an actual inductively
   presented theory `T` (EA or PA) proved to satisfy the three
   Hilbert-Bernays-Loeb conditions *against `sat`*. Then redefine the
   embeddings so `Box n` maps to the genuine Sigma_1 provability
   sentence of `T_n`, and reprove `Solovay_first_full`,
   `Solovay_second_full`, `Japaridze_full_via_tree`, and
   `Pi_2_conservativity` as statements about `Prov_T` and `sat`. Prove
   `arithmetic_layer_summary`. Forbidden:
   `standard_model_satisfies := classical_valid`;
   `arith_embed_* := subst_form`; instantiating any interpretation at
   `identity`/`shift_interp`; using `Bew_n` as the provability predicate
   without an N-satisfaction soundness proof; making `is_Pi_2` a `Form`
   class rather than the `forall/exists` shape of `ArithForm`.

2. **Topological completeness for full GLP\*.** Only the box-free
   fragment has a completeness theorem (`prop_completeness`,
   `kripke_completeness_box_free`); GLP* is relationally Kripke-
   incomplete and the file's neighborhood layer is a lone existence
   witness (`normal_neighborhood_witness`). Define genuine
   neighborhood/scattered-topological (Ignatiev-style) semantics
   `forces_topo` with frame conditions, prove `soundness_topo` and the
   converse `topo_completeness : topo_valid phi -> |- phi` for ALL
   `phi`. Prove `topo_completeness_summary`. Forbidden: restricting to
   `box_free`; `topo_valid` defined via a single fixed frame (e.g.
   `Fnat`); a `normal_neighborhood` existence statement standing in for
   completeness; routing through `prop_completeness`.

3. **Full decidability of GLP\*.** `GLPDecide` only decides the
   box-tower-over-box-free fragment; provability was shown
   non-compositional, so a total decider needs a real finite/topological
   model property. Construct
   `glp_decide_total : forall phi, sumbool (|- phi) (~ |- phi)` total on
   every formula, with a computable model bound (Ignatiev model) or a
   terminating cut-free search, and prove
   `glp_decide_total_correct : forall phi, (exists p, glp_decide_total phi = left p) <-> |- phi`.
   Forbidden: `glp_decide_total phi := excluded_middle_informative (|- phi)`;
   restricting to `is_iter_box_of_box_free`; falling back to
   `decide_tautology` on the box-free part only; deferring to a
   hypothetical normaliser.

4. **Constructed Feferman-Schuette Gamma_0.** `V_gamma0` is a declared
   nullary atom placed above the `V_phi` tower with well-foundedness
   asserted by fiat, and the height bound is proved non-tight. Define
   the two-argument Veblen function `veblen : ord -> ord -> ord` with
   the standard clauses (`veblen 0 = omega-power`, continuity, and
   fixed-point enumeration at successor/limit first arguments), and
   define `Gamma_0` as the least `a` with `veblen a OZero = a` (the first
   strongly critical ordinal), proved to be the supremum of the iterated
   `veblen`-tower. Re-establish `GLP_proof_height_below_Gamma_0` against
   this constructed `Gamma_0` and prove `veblen_Gamma_0_summary`.
   Forbidden: a nullary atom above the carrier by fiat;
   `Gamma_0 := veps0` or `V_phi 0 OZero` (the epsilon_0 alias);
   asserting `Acc`/well-foundedness of the top point without deriving it
   from the Veblen construction.

5. **Ordinal proof-height directly on derivations.** Large elimination
   from `Prop` blocks `forall phi, |- phi -> vord`, so the rank lives on
   the Type-level `Provable_term`. Either introduce a `Provable`-in-Type
   relation `ProvableT` with `proof_height : forall phi, ProvableT phi -> vord`
   and `ProvableT_iff : ProvableT phi <-> inhabited (Provable_term phi)`,
   or prove the `Provable_term` rank is invariant across all derivations
   of a given theorem. Prove `proof_height_on_derivations_summary`.
   Forbidden: keeping the rank only on `Provable_term` while stating it
   ranks `|-`; a constant rank; `proof_height _ _ := OZero`.

6. **Stone equivalence with proof-relevant hom-setoids.** The current
   `StoneEquivalence` sets `ec_hom_eq := fun _ _ => True`, so naturality
   and the triangle identities hold only because all parallel morphisms
   are identified (a preorder collapse). Replace the hom-equality with a
   genuine equivalence on morphisms (derivations modulo a conversion/cut
   relation, or the canonical 2-cell structure) and reprove
   `Stone_eta_natural`, `Stone_epsilon_natural`, `Stone_triangle_F`,
   `Stone_triangle_G` up to that relation. Prove
   `stone_proof_relevant_summary`. Forbidden:
   `ec_hom_eq := fun _ _ => True`; `hom_eq f g := |- Top`; any
   hom-equality identifying all parallel morphisms.

7. **Lambda-box strong normalisation with live combinators.** The
   `LambdaBox` calculus keeps `tS`, `tBoxK`, `tLoeb`, `tBox4`, `tMon`,
   `tNextCon`, and `tLoebFix` inert (no contraction rule) to keep the
   size measure decreasing, so realizers using them are stuck-normal
   rather than computed. Give each its genuine contraction rule (S
   duplication; a guarded `tLoebFix` unfolding) and prove strong
   normalisation of the typed calculus by reducibility candidates
   (Tait-Girard), then reprove `extract_realizer_reduces` against the
   full reduction. Prove `lambda_box_SN_summary`. Forbidden: inert
   combinators with no reduction rule; `tLoebFix` as a value; a reduction
   relation containing only the K / pair / box-beta redexes; a size
   measure that excludes the duplicating rules.

8. **Strict (non-setoid) Magari freeness.** `MagariFree` proves
   uniqueness only pointwise because intensional equality of morphism
   records is funext-strength. Build a setoid-enriched category of
   polymodal Magari algebras whose hom-equality is pointwise by
   definition, and state `LT_GLP_free` as a genuinely unique morphism in
   that category (a contractible space of homomorphisms extending the
   valuation). Prove `magari_strict_free_summary`. Forbidden: pointwise
   uniqueness stated outside a category whose homs are quotiented; appeal
   to `proof_irrelevance` or `functional_extensionality` to bridge
   morphism equality.

9. **Genuine QGLP quantifier semantics.** `QGLP_provable` currently sets
   `Q_forall _ _ := True` and `Q_exists _ _ := True`, making every
   quantified formula trivially provable. Give `QGLP_form` constant-
   domain Kripke semantics and an inductive derivability relation with
   real quantifier rules, prove `QGLP_soundness` against it, and
   (target) completeness. Prove `qglp_genuine_summary`. Forbidden:
   `QGLP_provable (Q_forall _ _) := True`;
   `QGLP_provable (Q_exists _ _) := True`; any clause whose truth is
   independent of the quantified body.

10. **Faithfulness to canonical Japaridze GLP.** `NextCon` is only the
    `phi := Top` instance `Box (S n) (Diamond n Top)` of GLP's general
    negative-introspection scheme. Either prove the general scheme
    `forall n phi, |- Impl (Diamond n phi) (Box (S n) (Diamond n phi))`
    from the present axioms (establishing this calculus IS GLP), or
    exhibit a sound model in which it fails (establishing a proper
    subsystem) and document the divergence. Prove either
    `glp_faithfulness_general_introspection` or
    `glp_proper_subsystem_witness`. Forbidden: leaving the question
    open; proving only the `phi := Top` instance (which is `NextCon`).

11. **Constructive core.** The development is wholly classical
    (`classic`, `constructive_indefinite_description`). Carve out the
    syntactic/decidable results — box-free decidability, the Hilbert
    toolkit, proof-term reductions, `glp_dec_b` — into modules that
    import neither `Classical` nor `ClassicalEpsilon`, verified by
    `Print Assumptions` showing no classical axiom, and confine the
    classical axioms to the Lindenbaum/completeness modules. Prove (or
    `Print Assumptions`-witness) `constructive_core_summary`. Forbidden:
    importing `Classical`/`ClassicalEpsilon` into the constructive
    modules; using `NNPP`/`classic`/`excluded_middle_informative` in any
    result claimed constructive.
