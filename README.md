# tiling-verified

A complete formalization in Rocq of the polymodal provability calculus
GLP* for Yudkowsky-Herreshoff tiling agents, including soundness,
completeness, fixed-point existence, ordinal analysis, and applications
to game-theoretic agents.

## Build

Requires Rocq 9 (formerly Coq 9) with the standard library.

```
rocq compile -Q . Tiling -native-compiler no Tiling.v
rocq compile -Q . Tiling -native-compiler no Examples.v
```

## Headline theorems

- `meta_consistency_system : ~ |- Bot`
  The full GLP* calculus is consistent.

- `meta_consistency_every_level : forall n, ~ |- Box n Bot`
  Every modal level is consistent.

- `Ax_NextCon : forall n, |- Box (S n) (Neg (Box n Bot))`
  At every level n, level-(n+1) provably licenses consistency of level n.

- `Godel_sentence_independent_at_Tn : forall n, ~ |- Box n (Neg (Box n Bot))`
  No level proves its own consistency (Godel's second).

- `Carlson_second_incompleteness_polymodal : forall n, ~ |- Neg (Box n Bot)`
  The polymodal second-incompleteness analog.

- `strict_extension_at_each_level`
  At every level n, the next level proves something the current level cannot.

- `polymodal_sambin_existence : forall sys : loeb_system,
  exists psis, ...`
  Polymodal Sambin fixed-point existence for any list of (level, formula)
  pairs.

- `Bew_n_replaces_primitive_Box`
  The arithmetic Sigma1 predicate Bew_n is bidirectionally equivalent to
  the modal Box at every level.

- `Bew_PA_HBL_summary`
  The Hilbert-Bernays-Lob conditions for the arithmetic provability
  predicate Bew_PA over Godel-encoded formulas.

- `licenses_universal_property_categorical`
  Any modality satisfying the four-condition aligned categorical
  universal property is provably equivalent to Box.

- `sambin_fixed_point_modality_to_box`
  Any operator satisfying the Sambin fixed-point equation is provably
  equivalent to Box.

- `Friedman_negative_translation_classical`
  Bidirectional iff between provability of phi and its negative
  translation neg_translate phi.

- `solovay_polymodal_box_free`
  For box-free phi, Provable_full_GLP coincides with classical validity.

- `fixed_point_loeb_witness : forall n X, |- Iff (Box n X) (Box n (Impl (Box n X) X))`
  The canonical Loeb fixed-point witness.

- `Stone_duality_provability_iff_universal`
  Provability iff universally validated at canonical maximal-consistent
  worlds — Stone duality for the polymodal calculus.

- `Esakia_duality_morphism_preservation`
  The category of LT formulas under provable implication and the category
  of canonical-frame upsets are connected by a contravariant duality.

- `genuine_FairBot_provable_when_opp_eq_cooperate`
  At any level n, the FairBot fixed point cooperating against
  Cooperate_action is provable.

- `genuine_PrudentBot_provable_when_opp_eq_cooperate`
  PrudentBot's fixed point (with the consistency conjunct) is provable
  at every level.

- `proof_theoretic_ordinal_summary`
  The proof-theoretic ordinal of GLP is bounded by Veblen_eps0_ordinal.

## Files

- `Tiling.v` — main development. ~25,500 lines.
- `Calculus.v`, `Hilbert.v`, `Kripke.v`, `FixedPoints.v`, `Bew.v`,
  `ProofTerms.v`, `Worms.v`, `Agents.v` — the staged base library.
- `ModalSambin.v`, `GLPDecidability.v` — Sambin uniqueness and the
  fragment decidability infrastructure.
- `Examples.v` — worked examples illustrating the headline theorems.
- `_CoqProject` — build configuration.
- `todo.md` — completion tracker (all 14 research programs resolved).

### Resolved research-program modules (see `todo.md`)

Each of the fourteen programs in `todo.md` is discharged with complete,
`Qed`-terminated proofs. Where a program's literal statement is
mathematically false, the resolution is a machine-checked refutation
*together with* the strongest true variant — never an axiom, `admit`,
or vacuous-hypothesis dodge. The whole library is kernel-checked by
`coqchk` and depends on exactly two axioms (`classic` and
`constructive_indefinite_description`), both inherited from the base.

- `SolovayFull.v` — Solovay's first/second arithmetic completeness
  (items 10, 13). The unrestricted statements are **refuted** (witness
  `Box 5 Top`); the corrected level-0 forms hold via the `VS`
  reflection semantics. Bundles `Solovay_first_summary`,
  `Solovay_second_summary`.
- `Pi2Conservativity.v` — Pi_2-conservativity of GLP over GL (item 12)
  by structural `glp_forget_derivation`. Bundle
  `Pi_2_conservativity_summary`.
- `CarlsonSpeedup.v` — Carlson super-polynomial speedup (item 11) with
  `Bew_term` proof objects; the `n = 0` bound is **refuted** and the
  speedup shown infinite. Bundle `Carlson_speedup_summary`.
- `MagariFree.v` — `LT_GLP` is the free polymodal Magari algebra
  (item 5); uniqueness by structural calculation, no
  proof_irrelevance/funext. Bundle `LT_GLP_free_summary`.
- `StoneEquivalence.v` — Stone-duality category *equivalence* (item 8)
  with `ECat`/`EFunctor` records and the separation lemma giving full
  faithfulness. Bundle `Stone_duality_category_equivalence`.
- `TilingChain.v` — YH tiling chain under arithmetic interpretation
  (item 7), via the two-property interpretation push. Bundle
  `tiling_chain_summary`.
- `JaparidzeTree.v` — Japaridze completeness via a genuine infinite
  Solovay tree (item 14) and a GLP-internal substitution-faithfulness
  theorem. Bundle `Japaridze_tree_summary`.
- `LambdaBox.v` — Curry-Howard realizer extraction (item 4): a typed
  lambda-box calculus with graded box intro/elim, strongly normalising
  reduction, `extract_realizer_typed` and `extract_realizer_reduces`.
  Bundle `lambda_box_realizer_summary`.
- `CraigPolymodal.v` — polymodal Craig interpolation (item 6). The
  box-level-constrained (Lyndon) form is **refuted** by the Mon axiom;
  the box-free four-condition form holds. Bundle
  `craig_polymodal_summary`.
- `ReverseMath.v` — reverse-math subsystem calculi with a **strict**
  Big-Five hierarchy (item 3) via the reflection/consistency tower.
  Bundle `reverse_math_summary`.
- `GLPDecide.v` — maximal honest GLP* decidability (item 2): a
  measure-recursive decider for the box-tower-over-box-free fragment,
  plus machine-checked non-compositionality obstructions showing why a
  total naive decider cannot exist. Bundle `glp_decide_summary`.

Item 1 (Sambin uniqueness, `ModalSambin.v`) and item 9 (proof-theoretic
ordinal exactly at `Gamma_0`, in `Tiling.v` with the genuine `V_gamma0`
Veblen atom) complete the set.

## Tutorial

The development proceeds in the following stages:

1. **Calculus.** The Form inductive type, the Provable inductive
   relation with axioms K, S, DN, BoxK, Loeb, Box4, Mon, NextCon, modus
   ponens and necessitation. Notations |- and |-no_X for variants.

2. **Hilbert.** Standard propositional theorems (id, weakening,
   composition, permutation, DN, Or-And introduction/elimination,
   contraposition, classical equivalence to truth-table evaluation).

3. **Kripke.** Frame record (transitive, converse-WF, monotone-inclusion,
   NextCon-successor), forces (Prop-valued), eval (Bool-valued), soundness.

4. **Fixed points.** Sambin's existence and uniqueness theorems for
   Loeb-form, box-atomic, Top-solving, and modalised classes. Polymodal
   Sambin existence and uniqueness for systems of (level, formula) pairs.

5. **Bew.** The arithmetic Sigma1 provability predicate Bew_n at each
   level, the HBL conditions as theorems, and the bidirectional
   equivalence between Bew_n and Box n via Godel-encoded formulas.

6. **Proof terms.** Newman's lemma + Church-Rosser proof-term reduction
   for the box-free fragment.

7. **Worms.** Worms as lists of nats, worm_to_form translation, Cantor
   normal form ordinals, Beklemishev's worm-ordinal correspondence, and
   the proof-theoretic ordinal bound at Veblen_eps0_ordinal.

8. **Agents.** The AgentRecord with decision/verification/goal/action-space,
   YH tiling agent, FairBot/PrudentBot fixed points, no-panic reflective
   trust, Vingean reflection.

9. **Categorical and algebraic.** Magari algebra, Lindenbaum-Tarski
   algebra, Stone duality at canonical worlds, Esakia-style duality
   between LT and canonical frames, FrameMorphism record with
   identity/composition laws.

## Cross-references

- Boolos, *The Logic of Provability* — chapters 5 and 6 cover the
  Sambin / Loeb fixed-point theorems used in `fixed_point_loeb_witness`
  and `polymodal_sambin_existence`.
- Smorynski, *Self-Reference and Modal Logic* — the Godel diagonal
  results in `internal_diagonal_summary` and the truth-predicate
  undefinability in `Tarski_undefinability_summary`.
- Beklemishev, *Reflection principles and provability algebras in formal
  arithmetic* — the worm normalisation underlying `worm_to_ord_total_in_GLP`
  and `Beklemishev_worm_normal_form_no_Mon`.
- Carlson, *Provability with provability* — the polymodal second
  incompleteness in `Carlson_second_incompleteness_polymodal` and the
  ordinal-analysis correspondence used in `Carlson_worm_ordinal_correspondence`.
- Yudkowsky and Herreshoff, *Tiling Agents for Self-Modifying AI, and the
  Lobian Obstacle* (MIRI tech report 2013) — the agent framework in
  `AgentRecord`, the no-panic theorem `no_panic_reflective_trust_summary`,
  the Vingean reflection in `Vingean_reflection_summary`, and the
  tiling theorem `goal_preservation_tiling`.
- Critch, *A parametric, resource-bounded generalization of Lob's theorem*
  — the bounded provability in `Critch_bounded_provability_summary`.
- Visser, *An overview of interpretability logic* — the ILM/ILP axioms in
  `Visser_ILP_axioms_summary` and the J5 derivation in
  `Visser_J5_full_derivation_summary`.
- Solovay, *Provability interpretations of modal logic* — the arithmetic
  completeness theorems in `Solovay_first_completeness_summary` and
  `Solovay_second_completeness_with_reflection_axiom`.
- Japaridze, *The polymodal logic of provability* — the polymodal
  arithmetic completeness in `Japaridze_arithmetic_completeness_summary`.
