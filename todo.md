# tiling-verified todo

Ordered so that each item's prerequisites appear earlier.

1. Prove |- Impl (Box n phi) (Box n (Box n phi)) (axiom 4) as a derived theorem from K + Löb, following Boolos Theorem 11, rather than leaving it as a comment.
2. Prove a normalization theorem for Provable: every derivation reduces to a canonical form, enabling decidability arguments for fragments.
3. Prove decidability of |- phi for the propositional-only fragment (no Box), giving a decision procedure extracted to OCaml.
4. Prove decidability of |- phi for the single-level modal fragment using filtration on Kripke models.
5. Prove a Kripke-model completeness theorem for the polymodal fragment used: Valid phi -> |- phi, restricted to the axioms actually in Provable.
6. Prove the file's tower is conservative over single-level GL at level 0: every Box 0-only formula |- phi here is provable in standard Gödel-Löb logic.
7. Prove a Kripke-completeness or topological-completeness theorem for the specific axiomatization (GLP-with-monotonicity-and-NextCon), since this combination is not literally GLP and its semantic characterization is not immediate from existing results.
8. Prove that tiling_consistency is the strongest such property: any formula psi(n, phi) provable at Box (S n) and stronger than Impl (Box n phi) (Neg (Box n (Neg phi))) collapses the system.
9. Prove a cut-elimination theorem for a sequent presentation of GLP* equivalent to Provable, following the Goré-Ramanayake style.
10. Prove the cut-elimination theorem of (9) yields a syntactic proof of ~ (|- Bot), removing the dependence on Kripke semantics for global consistency.
11. Prove a fixed-point theorem within GLP*: for every phi(p) with p occurring only inside Box, exhibit psi with |- Iff psi (phi(psi)), the polymodal analogue of the GL fixed-point theorem.
12. Prove the resulting fixed points are unique up to provable equivalence at the level the box is taken.
13. Prove a fixed-point theorem for the polymodal calculus, in the de Jongh-Sambin style, so that self-referential modal sentences have provable explicit fixed points.
14. Prove the Hilbert-Bernays-Löb derivability conditions hold for a concrete encoded provability predicate Bew_n over a representation of formulas, so that Ax_Loeb becomes a derived theorem rather than a primitive axiom.
15. Prove Ax_NextCon arithmetically: construct concrete theories T_n and T_(n+1) such that T_(n+1) derives the formalized statement of Con(T_n), rather than asserting it as a primitive.
16. Prove Ax_Mon (cross-level monotonicity) as a theorem about the concrete tower: show that every theorem of T_n is a theorem of T_(n+1) from the construction of the theories.
17. Construct T_κ as a first-order theory in the sense of YH 2013 §3 — PA augmented with the schematic axiom (κ > 0) -> ∀x. Box_{T_κ} ⌜φ(x)⌝ -> φ(x)[κ\κ-1] — and prove that each schema instance is well-formed.
18. Prove soundness of T_κ at each standard κ ∈ N, which is the central positive result of YH 2013.
19. Prove the tiling theorem proper: that an agent A_α using T_κ derives the safety of constructing a successor agent A_(α-1) using T_(κ-1), for arbitrary standard κ.
20. Prove an arithmetic soundness bridge: define an interpretation I : Form -> Arith such that |- phi implies PA |- I(phi) under the natural reading of Box n as iterated consistency extensions of PA.
21. Prove the bridge in (20) is faithful at level 0: |- Box 0 phi iff PA |- Bew_PA(I(phi)).
22. Prove arithmetical soundness of the polymodal calculus: every theorem |- phi translates, under the standard arithmetical interpretation, to a theorem of the appropriate concrete theory in the tower.
23. Prove a Solovay-style arithmetic completeness theorem for the level-0 fragment: every arithmetically valid formula is |--derivable at level 0.
24. Prove arithmetical completeness in the Solovay sense: the modal theorems of the polymodal calculus are exactly the formulas valid under all arithmetical interpretations into the tower.
25. Prove the polymodal extension is arithmetically complete relative to the Beklemishev hierarchy: |- phi iff phi holds under the iterated-reflection interpretation in PA + RFN.
26. Prove the connection to Critch's parametric bounded Löb (JSL 2019): that bounded-proof-length variants of Ax_Loeb are derivable in the system under appropriate complexity assumptions, unifying the proof-length-parametric and tower-index-parametric forms of "parametric Löb."
27. Prove the connection to Beklemishev's iterated-reflection hierarchy: that the tower's consistency-chain structure embeds into, or is interpretable by, the standard iterated local reflection ordering, locating this axiomatization within the existing polymodal landscape.
28. Prove the procrastination paradox in this formalization and prove that T_κ avoids it: that a T_κ-using agent cannot derive a paradoxical postponement of an action it is required to take.
29. Prove the file's results extend to transfinite levels: define Box alpha for ordinals alpha < epsilon_0 and prove tiling_consistency lifts.
30. Prove the transfinite extension of (29) recovers the full Beklemishev GLP system, with explicit translation between this file's Box n tower and the GLP-worm hierarchy.
31. Prove an extracted certified verifier: extract from Provable an OCaml proof-checker, prove its soundness inside Coq, and prove it accepts exactly the closed terms of Provable.
