# tiling-verified todo

Each item below is a research program. The acceptance criterion in
each item names a specific syntactic construction or computational
artifact that cannot be discharged by aliasing, by vacuous-hypothesis
shortcuts, by identity-collapse of universals, by box-as-tautology
translations that lose modal content, by single-line constant
functions masquerading as recursive constructions, or by repackaging
the same theorem under a longer name. Where a closure proof must
make a specific computational choice (a rank function, a tree
structure, a fundamental sequence, a length-counting recursion), that
choice is named and forbidden alternatives are listed.

Items are ordered by logical dependency: each item's stated prerequisites
appear earlier.  Items with no in-list prerequisites come first; items
that build on Solovay-style arithmetic completeness come last.

1. **Sambin fixed-point uniqueness for arbitrary modalised contexts.**
    Define `modalised_in_p : (Form -> Form) -> Prop` saying that
    every occurrence of the bound variable in `C p` is under at
    least one `Box _`. Prove
    `sambin_uniqueness_modalised : forall (C : Form -> Form),
    modalised_in_p C ->
    forall psi1 psi2, |- Iff psi1 (C psi1) -> |- Iff psi2 (C psi2) ->
    |- Iff psi1 psi2`. The proof must be by induction on a measure
    of `C` with explicit decreasing argument, NOT by appealing to
    `polymodal_sambin_uniqueness` for a single fixed `loeb_system`.
    Forbidden: restricting to `C := fun p => Box n (Impl p X)`,
    restricting to `C` with `box_levels` a singleton,
    returning `prov_iff_refl psi1` and noting `psi1 = psi2`.

2. **Decidability of full GLP at every level.**
    Construct `glp_decide : forall phi, sumbool (|- phi) (~ |- phi)`
    by structural recursion that proceeds case-by-case on the modal
    depth of `phi`. The procedure must terminate in primitive-
    recursive time in `length phi + modal_depth phi`. The proof
    must contain a Fixpoint with explicit decreasing-measure
    `(modal_depth phi, length phi)` lex-ordered. Prove
    `glp_decide_correct : forall phi, glp_decide phi = left _ <-> |- phi`.
    Forbidden: `glp_decide phi := classic (|- phi)` (uses
    excluded-middle), restricting to `box_free` and falling back to
    `decide_tautology`, deferring to a hypothetical normaliser.

3. **Real reverse-mathematics formalization with internal subsystem
    calculi.** Define, for each `s : RM_subsystem`, an INDUCTIVE
    relation `RM_provable_real : RM_subsystem -> Form -> Prop` whose
    constructors include exactly the comprehension/induction axioms
    appropriate to that subsystem (Sigma_0_1 induction for RCA_0,
    weak Konig's lemma plus Sigma_0_1 induction for WKL_0,
    arithmetical comprehension for ACA_0, arithmetical transfinite
    recursion for ATR_0, Pi_1_1 comprehension for Pi_1_1-CA_0). Prove
    `RM_provable_real_strict_hierarchy : forall s s',
    RM_subsystem_lt s s' ->
    exists phi, RM_provable_real s' phi /\ ~ RM_provable_real s phi`.
    Forbidden: making `RM_provable_real s P := P`, making it
    `RM_provable_real s P := |- P` (collapses across subsystems), or
    making the hierarchy non-strict.

4. **Curry-Howard realizer extraction with computational content.**
    Define `lambda_box : Type` as a typed lambda calculus with
    explicit box-introduction (graded by level), box-elimination,
    pair, app, abs, and `loeb_fixpoint : forall n phi,
    (lambda_box -> lambda_box) -> lambda_box`.
    Define `extract_realizer : forall phi, Provable_term phi -> lambda_box`
    by structural recursion on the proof term. Prove
    `extract_realizer_typed : forall phi (pt : Provable_term phi),
    has_type (extract_realizer phi pt) phi` AND
    `extract_realizer_reduces : forall phi (pt : Provable_term phi),
    exists nf, beta_box_normalises (extract_realizer phi pt) nf`.
    Forbidden: `lambda_box := Form` and `extract_realizer pt := phi`
    (identity collapse), `lambda_box := Provable_term phi`
    (trivial functor), `nf := extract_realizer phi pt` (no
    reduction).

5. **Lindenbaum-Tarski algebra of GLP is the FREE polymodal Magari
    algebra.** Define `polymodal_Magari_algebra` as a record with a
    Boolean-algebra carrier, family of necessitation operators
    `box_op : nat -> carrier -> carrier`, validity of K, Loeb, Mon at
    every index. Define `LT_GLP : polymodal_Magari_algebra` as the
    quotient by provable-iff. Prove
    `LT_GLP_free : forall (A : polymodal_Magari_algebra) (val : nat -> carrier A),
    exists! (h : LT_GLP_morphism LT_GLP A),
    forall p, h (LT_class (Var p)) = val p`. The uniqueness must
    follow from a calculation, not from `proof_irrelevance` or
    `functional_extensionality`. Forbidden: defining `free` as
    `epi`, instantiating `A := LT_GLP` (collapses to identity),
    skipping the morphism-laws check.

6. **Polymodal Craig interpolation.**
    Define `box_levels : Form -> list nat` and `var_set : Form -> list nat`
    by structural recursion. Prove
    `craig_interpolation_polymodal : forall phi psi,
    |- Impl phi psi ->
    exists chi,
       (forall x, In x (var_set chi) -> In x (var_set phi) /\ In x (var_set psi)) /\
       (forall n, In n (box_levels chi) -> In n (box_levels phi) /\ In n (box_levels psi)) /\
       |- Impl phi chi /\ |- Impl chi psi`.
    The construction of `chi` must be by structural recursion on a
    derivation of `Impl phi psi`, NOT by classical choice from
    existence. Forbidden: `chi := phi` (no constraint on
    `var_set psi`-side), `chi := psi`, `chi := Top`, `chi := Bot`.

7. **Yudkowsky-Herreshoff tiling theorem under arithmetic
    interpretation, with explicit goal-preservation chain.** Define
    `tiling_chain : AgentRecord -> nat -> Form` as the n-fold
    self-modification of the agent's decision under its own
    verification. Prove
    `tiling_succeeds_under_arithmetic_interpretation :
    forall (A : AgentRecord) (G : Form),
    agent_goal A = G ->
    (forall I, is_arithmetic_interpretation I ->
       (forall n, |- Impl (I (tiling_chain A n)) (I G))) ->
    forall I, is_arithmetic_interpretation I ->
    forall n, |- Impl (I (agent_decision A (Var 0))) (I G)`.
    The proof must use the arithmetic-interpretation property
    non-trivially (not just substitute identity). Forbidden:
    `tiling_chain A n := agent_goal A` (constant),
    `tiling_chain A 0 := Bot` (vacuous antecedent at level 0),
    using `goal_preservation_tiling_concrete` as the entire proof.

8. **Stone-duality category-equivalence.** Define
    `Record LT_category : Type` and `Record canonical_frame_category : Type`
    with explicit object-types, hom-types, identity, composition,
    associativity, and unit-laws. Define functors
    `F : LT_category -> canonical_frame_category` and
    `G : canonical_frame_category -> LT_category` with explicit
    object-action and morphism-action. Define natural isomorphisms
    `eta : forall A, A ~= G (F A)` and
    `epsilon : forall X, F (G X) ~= X`. Prove the triangle
    identities. Forbidden: defining `eta` and `epsilon` as
    `eq_refl`, defining the categories as `Form` and `Form`
    with `morphism := |- Impl phi psi` (this collapses the
    duality to provability), citing
    `Stone_duality_provability_iff_universal` as the discharge.
    (Depends on item 5: `LT_GLP` as polymodal Magari algebra.)

9. **Proof-theoretic ordinal of GLP, EXACTLY at Gamma_0, upper bound
    at every level.** Define
    `Gamma_0_ordinal : vord` as the first fixed point of the Veblen
    `phi`-function above `omega`, NOT as
    `OCons (OCons (OCons OZero OZero) OZero) OZero` (that is `omega^omega^omega = epsilon_0`-region but not `Gamma_0`). Define
    `proof_height : forall phi, |- phi -> vord` as the rank of the
    derivation-tree of the witness, with explicit cases for K, S, DN,
    BoxK, Loeb (giving rank `omega`), Box4, Mon, NextCon, MP (sup of
    children + 1), Nec (succ of child rank). Prove
    `GLP_proof_height_below_Gamma_0 : forall phi (H : |- phi),
    vord_lt (proof_height phi H) Gamma_0_ordinal`. Forbidden:
    redefining `Gamma_0_ordinal := Veblen_eps0_ordinal`, returning
    `OZero` for every derivation, or returning a constant.
    (Builds on the completed `beklemishev_reduce` ordinal-descent
    infrastructure: `beklemishev_reduce_strictly_decreases` and
    `beklemishev_reduce_terminates`.)

10. **Solovay's first arithmetic completeness for GL, full statement.**
    Define `solovay_function : nat -> nat` as the fixed-point of the
    Solovay tree on the integer model, with `solovay_function 0 = 0`
    and the full step relation tracking `R_i`-successors. Define
    `arith_embed_GL : Form -> nat -> Prop` translating
    `Box phi` to the Sigma_1 sentence `exists d, encodes_proof d
    (encode_form (arith_embed_GL phi))` in the language of `Bew_n 0`,
    NOT to `Bew_n 0 (encode phi)` directly and NOT to `FOTopForm`.
    Prove `Solovay_first_full : forall phi,
    (forall I, is_arithmetic_interpretation_proper I ->
       Bew_n 0 (encode (I phi))) -> Provable_GL phi`
    where `is_arithmetic_interpretation_proper` requires
    substitution-closure, MP-closure, AND `I (Box phi) = Bew_n 0 (encode (I phi))`
    pointwise (NOT just provability preservation). Forbidden:
    instantiating `I := identity`, instantiating
    `I := shift_interp`, restricting `phi` to `box_free`, defining
    `arith_embed_GL (Box phi) := arith_embed_GL phi` (box-erasure),
    or `:= FOTopForm` (box-as-top).

11. **Carlson polymodal second incompleteness with explicit
    super-polynomial speedup.** Define `proof_length_in_T_n : forall n phi,
    Bew n phi -> nat` by structural recursion on the Bew-derivation,
    counting axiom-leaves and rule-applications. Define
    `tower_function : nat -> nat` by `tower_function 0 = 2;
    tower_function (S n) = 2 ^ tower_function n`. Prove
    `Carlson_speedup_super_polynomial : forall n,
    exists phi (H_n_plus_1 : Bew (S n) phi),
       proof_length_in_T_n (S n) phi H_n_plus_1 <= 100 * n /\
       forall (H_n : Bew n phi), tower_function n <= proof_length_in_T_n n phi H_n`.
    Forbidden: `proof_length_in_T_n _ _ _ := 0` (trivializes both
    sides), `proof_length_in_T_n _ _ _ := S O` (constant), or
    using existing `Pudlak_speedup_at` as the witness.
    (Depends on item 10: builds on the Solovay arithmetic
    interpretation framework.)

12. **Pi_2-conservativity of GLP over GL, theorem-level (not vacuous).**
    Define `is_Pi_2 : Form -> Prop` as the standard arithmetic class:
    `forall n, exists m, R(n, m)` shape with `R` Sigma_0_1.
    Prove `Pi_2_conservativity : forall phi,
    is_Pi_2 phi -> Provable_full_GLP phi -> Provable_GL phi`
    via Beklemishev's reduction (worm normalization producing a
    GL-derivation by transfinite induction up to `omega`). The proof
    must contain a function
    `extract_GL_derivation : forall phi (H : Provable_full_GLP phi)
    (Hp2 : is_Pi_2 phi), Provable_GL phi`
    whose body recurses on the structure of `H`, NOT a reference to
    `H` followed by case-analysis-and-discharge. Forbidden:
    showing the hypothesis is universally false (Carlson-vacuity);
    restricting to `phi = Bot`; reducing to `box_free`.
    (Depends on item 10 for the Solovay-completeness target;
    builds on the completed `beklemishev_reduce` engine.)

13. **Solovay's second arithmetic completeness for the truth-extension
    S, full statement.** Define `arith_embed_S : Form -> nat -> Prop`
    extending `arith_embed_GL` with the T-schema for true Sigma_1
    sentences (i.e., the embedding evaluates `Box phi` against the
    standard model rather than against PA's internal predicate).
    Prove `Solovay_second_full : forall phi,
    (forall I, is_arithmetic_interpretation_proper I ->
       Bew_n 0 (encode (I phi)) /\ standard_model_satisfies (I phi))
    -> Provable_S phi`. Forbidden: defining `arith_embed_S := arith_embed_GL`,
    using only `S_truth_completeness_box_free`, weakening to box-free,
    or treating `S_reflection` as the answer.
    (Depends on item 10: extends the Solovay-first machinery.)

14. **Japaridze's polymodal arithmetic completeness, full statement
    with an actual Solovay tree.** Define
    `Inductive Solovay_node : Type :=
       | sol_root : Solovay_node
       | sol_child : Solovay_node -> nat -> Form -> Solovay_node`
    and a recursive `solovay_tree_step : Solovay_node -> list Solovay_node`
    that branches on box-level. The tree must be infinite-and-
    finitely-branching with at least two branches at every node above
    a parameter-set threshold. Define
    `tree_validates : (Form -> Form) -> Solovay_node -> Prop`
    by structural recursion. Prove
    `Japaridze_full_via_tree : forall phi,
    (forall I, is_polymodal_arithmetic_interpretation_proper I ->
       tree_validates I (build_solovay_tree phi))
    -> Provable_full_GLP phi`. Forbidden: making
    `solovay_tree_step _ := []` (degenerate empty tree),
    making `Solovay_node := unit` and `tree_validates := True`,
    instantiating `I := shift_interp` to MP-discharge,
    `I := identity`.
    (Depends on item 10: polymodal generalization of the Solovay tree.)
