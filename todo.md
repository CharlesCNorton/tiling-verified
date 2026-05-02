# tiling-verified todo

Ordered so that each item's prerequisites appear earlier.

1. Prove |- Impl (Box n phi) (Box n (Box n phi)) (axiom 4) as a derived theorem from K + Löb, following Boolos Theorem 11, rather than leaving it as a comment.
2. Prove the converse direction of contraposition: |- Impl (Impl (Neg psi) (Neg phi)) (Impl phi psi), completing the contrapositive equivalence.
3. Prove the And-introduction metatheorem in conjunction-elimination form: |- phi -> |- psi -> |- And phi psi, and its converse pair.
4. Prove the Or-elimination rule: |- Impl (Or phi psi) (Impl (Impl phi chi) (Impl (Impl psi chi) chi)).
5. Prove the And/Or/Iff de Morgan dualities as theorems: |- Iff (Neg (And phi psi)) (Or (Neg phi) (Neg psi)) and the three companions.
6. Prove the deduction theorem for this Hilbert system: if Provable_with_hyp Gamma phi psi then |- Impl phi psi, formalizing Provable_with_hyp as an inductive extension of Provable.
7. Prove the converse of prov_box_and_intro: |- Impl (Box n (And phi psi)) (And (Box n phi) (Box n psi)), giving the full K-distribution-over-And biconditional.
8. Prove K-distribution over Or: |- Impl (Or (Box n phi) (Box n psi)) (Box n (Or phi psi)).
9. Prove the Box-Diamond duality theorems: |- Iff (Diamond n phi) (Neg (Box n (Neg phi))) (definitional) and |- Iff (Box n phi) (Neg (Diamond n (Neg phi))).
10. Prove the agent-licensure layer respects substitution: if |- Iff phi psi then |- Iff (licenses n phi) (licenses n psi), internalizing the congruence that justifies the abstraction.
11. Prove transitivity of nested licensing: |- Box (S (S n)) (licenses (S n) (licenses n phi)) -> |- Box (S (S n)) (licenses n phi) under appropriate reflection conditions.
12. Prove the converse of licensing_consistency_concrete: if |- Box (S n) (Neg (Box n (Neg phi))) and the level is meta-consistent, then |- Box n phi is licensable, characterizing the bypass conditions exactly.
13. Prove a finitary version of joint_licensing_consistency_chain for arbitrary finite conjunctions: |- Box n (phi_1) -> ... -> |- Box n (phi_k) -> |- Box (S n) (Neg (Box n (Neg (And-list [phi_1; ...; phi_k])))).
14. Prove an internal version of the YH bypass: |- Box (S n) (yh_bypass_summary_internal n), where the summary itself is a Form that the higher level proves.
15. Prove the bypass is uniform: there exists a single derivation schema parameterized by n such that tiling_consistency instances are obtained by substitution, formalized as a derivation-tree generator.
16. Prove a normalization theorem for Provable: every derivation reduces to a canonical form, enabling decidability arguments for fragments.
17. Prove decidability of |- phi for the propositional-only fragment (no Box), giving a decision procedure extracted to OCaml.
18. Prove decidability of |- phi for the single-level modal fragment using filtration on Kripke models.
19. Prove decidability of the full polymodal calculus by giving a terminating proof-search procedure with cut-elimination, following the Goré-Ramanayake style for GLS.
20. Construct a Kripke-model soundness theorem: define frames for GLP* and prove |- phi -> Valid phi, where Valid quantifies over admissible frames.
21. Prove a Kripke-model completeness theorem for the polymodal fragment used: Valid phi -> |- phi, restricted to the axioms actually in Provable.
22. Prove the converse of monotonicity fails: exhibit a model in which Box (S n) phi holds but Box n phi does not, formalizing a Kripke semantics for GLP*.
23. Prove meta-consistency of Box 0 directly: ~ (|- Box 0 Bot), using the Kripke completeness theorem of (21) and a finite countermodel.
24. Prove the meta-consistency assumption ~(|- Box n Bot) for at least one concrete n — by Kripke semantics for GL, by cut-elimination for the polymodal sequent calculus, or by a model-theoretic argument — so that meta_consistency_no_contradiction becomes unconditional for that n.
25. Prove meta-consistency of every level: forall n, ~ (|- Box n Bot), by induction on n using (21) and the cut-elimination structure of the tower.
26. Prove the file's tower is conservative over single-level GL at level 0: every Box 0-only formula |- phi here is provable in standard Gödel-Löb logic.
27. Prove Ax_NextCon is independent of the lower-level axioms: removing it makes consistency_chain underivable, formalized as a relative-consistency argument.
28. Prove a Kripke-completeness or topological-completeness theorem for your specific axiomatization (GLP-with-monotonicity-and-NextCon), since this combination is not literally GLP and its semantic characterization is not immediate from existing results.
29. Prove strict extension at every level: exhibit phi_n such that |- Box (S n) phi_n but ~ (|- Box n phi_n), witnessing genuine ascent.
30. Prove the explicit reflection schema fails at every level: ~ (forall phi, |- Impl (Box n phi) phi), strengthening loebian_obstacle from "implies Bot" to "is itself unprovable as a schema."
31. Prove the parametric reflection schema succeeds across levels: forall n phi, |- Impl (Box n phi) (Box (S n) phi) is exactly the legitimate replacement, and characterize formally why this avoids Löb.
32. Prove that tiling_consistency is the strongest such property: any formula psi(n, phi) provable at Box (S n) and stronger than Impl (Box n phi) (Neg (Box n (Neg phi))) collapses the system.
33. Prove that licenses n phi := Box n phi satisfies the agent-theoretic properties claimed for it: licensing decisions compose correctly across agents, nested licensure has the expected modal structure, and the licensure layer is conservative over the underlying modal calculus.
34. Prove a cut-elimination theorem for a sequent presentation of GLP* equivalent to Provable, following the Goré-Ramanayake style.
35. Prove the cut-elimination theorem of (34) yields a syntactic proof of ~ (|- Bot), removing the dependence on Kripke semantics for global consistency.
36. Prove a fixed-point theorem within GLP*: for every phi(p) with p occurring only inside Box, exhibit psi with |- Iff psi (phi(psi)), the polymodal analogue of the GL fixed-point theorem.
37. Prove the resulting fixed points are unique up to provable equivalence at the level the box is taken.
38. Prove a fixed-point theorem for the polymodal calculus, in the de Jongh-Sambin style, so that self-referential modal sentences have provable explicit fixed points.
39. Prove the Hilbert-Bernays-Löb derivability conditions hold for a concrete encoded provability predicate Bew_n over a representation of formulas, so that Ax_Loeb becomes a derived theorem rather than a primitive axiom.
40. Prove Ax_NextCon arithmetically: construct concrete theories T_n and T_(n+1) such that T_(n+1) derives the formalized statement of Con(T_n), rather than asserting it as a primitive.
41. Prove Ax_Mon (cross-level monotonicity) as a theorem about the concrete tower: show that every theorem of T_n is a theorem of T_(n+1) from the construction of the theories.
42. Construct T_κ as a first-order theory in the sense of YH 2013 §3 — PA augmented with the schematic axiom (κ > 0) -> ∀x. Box_{T_κ} ⌜φ(x)⌝ -> φ(x)[κ\κ-1] — and prove that each schema instance is well-formed.
43. Prove soundness of T_κ at each standard κ ∈ N, which is the central positive result of YH 2013.
44. Prove the tiling theorem proper: that an agent A_α using T_κ derives the safety of constructing a successor agent A_(α-1) using T_(κ-1), for arbitrary standard κ.
45. Prove an arithmetic soundness bridge: define an interpretation I : Form -> Arith such that |- phi implies PA |- I(phi) under the natural reading of Box n as iterated consistency extensions of PA.
46. Prove the bridge in (45) is faithful at level 0: |- Box 0 phi iff PA |- Bew_PA(I(phi)).
47. Prove arithmetical soundness of the polymodal calculus: every theorem |- phi translates, under the standard arithmetical interpretation, to a theorem of the appropriate concrete theory in the tower.
48. Prove a Solovay-style arithmetic completeness theorem for the level-0 fragment: every arithmetically valid formula is |--derivable at level 0.
49. Prove arithmetical completeness in the Solovay sense: the modal theorems of the polymodal calculus are exactly the formulas valid under all arithmetical interpretations into the tower.
50. Prove the polymodal extension is arithmetically complete relative to the Beklemishev hierarchy: |- phi iff phi holds under the iterated-reflection interpretation in PA + RFN.
51. Prove the FS2014 finite tower result: for any fixed n, there is a sequence T_0, T_1, ..., T_n where each T_(k+1) proves the soundness of T_k over the appropriate sentence class.
52. Prove the FS2014 infinite consistency-chain result: there is an infinite sequence of theories {T_n}_{n ∈ N} in which every T_n proves Con(T_(n+1)), and an agent using T_n proves it is safe to self-modify into an agent using T_(n+1).
53. Prove the connection to Critch's parametric bounded Löb (JSL 2019): that bounded-proof-length variants of Ax_Loeb are derivable in the system under appropriate complexity assumptions, unifying the proof-length-parametric and tower-index-parametric forms of "parametric Löb."
54. Prove the connection to Beklemishev's iterated-reflection hierarchy: that the tower's consistency-chain structure embeds into, or is interpretable by, the standard iterated local reflection ordering, locating this axiomatization within the existing polymodal landscape.
55. Prove the procrastination paradox in this formalization and prove that T_κ avoids it: that a T_κ-using agent cannot derive a paradoxical postponement of an action it is required to take.
56. Prove a robustness theorem: that the YH bypass continues to hold under small perturbations of the axiomatization (e.g., weaker monotonicity, NextCon restricted to a sentence class), establishing that the bypass is not an artifact of the specific axioms chosen.
57. Prove the file's results extend to transfinite levels: define Box alpha for ordinals alpha < epsilon_0 and prove tiling_consistency lifts.
58. Prove the transfinite extension of (57) recovers the full Beklemishev GLP system, with explicit translation between this file's Box n tower and the GLP-worm hierarchy.
59. Prove an extracted certified verifier: extract from Provable an OCaml proof-checker, prove its soundness inside Coq, and prove it accepts exactly the closed terms of Provable.
