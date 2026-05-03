# tiling-verified todo

Ordered so that each item's prerequisites appear earlier.

1. Prove the van Benthem characterisation: every bisimulation-invariant first-order formula over Frame structures is equivalent to a polymodal formula.
2. Prove a topological-completeness theorem via scattered spaces (Beklemishev-Esakia style).
3. Define polytopological semantics for GLP* in the Beklemishev-Gabelaia style and prove soundness.
4. Prove the Lindenbaum lemma proper: every consistent set of formulas extends to a maximal consistent set.
5. Construct the canonical model for Provable and prove the truth-lemma.
6. Prove a Henkin-style construction extending consistent sets to satisfiable models.
7. Prove a Kripke-model completeness theorem for the polymodal fragment used: Valid phi -> |- phi.
8. Resolve the Kripke-completeness question for GLP*: complete the canonical model construction or refute by exhibiting a Kripke-valid non-theorem.
9. Prove a Kripke-completeness or topological-completeness theorem for GLP*-with-monotonicity-and-NextCon.
10. Prove full Kripke completeness for the no-NextCon calculus Provable_no_NC against the wider class of no-NC frames.
11. Prove the file's tower is conservative over single-level GL at level 0: every level-0-only Provable theorem is in Provable_GL.
12. Prove the finite frame property: every non-theorem of Provable is refuted by some finite Frame.
13. Extract from Kripke soundness a model-search procedure that, given a non-theorem, produces a refuting Frame.
14. Prove decidability of |- phi for the single-level modal fragment using filtration on Kripke models.
15. Prove decidability of the closed (variable-free) fragment and its normal form.
16. Prove decidability of the full polymodal calculus GLP*; extract to OCaml.
17. Prove a cut-elimination theorem for a sequent presentation of GLP*.
18. Prove the cut-elimination theorem yields a syntactic proof of ~(|- Bot).
19. Prove a normalization theorem for Provable.
20. Prove that every theorem of Provable has a derivation of bounded modal depth depending only on the Box-levels appearing in the conclusion.
21. Prove the Beklemishev worm normal form algorithm.
22. Prove worm-translation: define worms with linear ordering by provable implication.
23. Prove Craig interpolation for GLP*.
24. Prove Beth definability for GLP* by deriving it from Craig interpolation.
25. Prove a fixed-point theorem within GLP*: for every modalised phi(p), exhibit psi with |- Iff psi (Subst p psi phi).
26. Prove the fixed points are unique up to provable equivalence.
27. Prove the polymodal de Jongh-Sambin fixed-point theorem.
28. Prove a fixed-point uniqueness theorem distinct from same-level uniqueness.
29. Define a categorical semantics: the category of Frames with bisimulation morphisms, and prove Provable is sound and complete with respect to its terminal object.
30. Prove that the consistency chain forms a cofibered diagram of theories indexed by ω.
31. Prove that the agent licensure layer factors through a free construction: a syntactic category of agents with morphisms = licensing-preserving maps, and licenses : nat -> Form -> Form is the free such functor.
32. Encode FairBot and PrudentBot as Form-level objects via the polymodal fixed-point theorem and prove the robust-cooperation theorem.
33. Construct the procrastination paradox as a Form, prove derivability under naive axioms, and prove T_κ blocks it.
34. Prove the connection to Critch's parametric bounded Löb (JSL 2019).
35. Prove the precise Critch correspondence at proof level.
36. Prove the Hilbert-Bernays-Löb derivability conditions for a concrete encoded Bew_n.
37. Prove a self-application theorem: Form-level encoding of Provable + |- Box (S n) (Impl (Provable_encoded phi) (Box n phi)) under HBL.
38. Prove Ax_NextCon arithmetically: construct concrete T_n, T_(n+1) such that T_(n+1) derives Con(T_n).
39. Prove Ax_Mon arithmetically.
40. Construct T_κ as a first-order theory in the YH 2013 §3 sense.
41. Define the parametric tower with κ as a Form-level parameter.
42. Prove soundness of T_κ at each standard κ ∈ N.
43. Prove the tiling theorem proper: A_α using T_κ derives safety of A_(α-1) using T_(κ-1).
44. Define ZF_τ-style set-theoretic licensure (YH 2013 §6).
45. Prove an arithmetic soundness bridge I : Form -> Arith such that |- phi implies PA |- I(phi).
46. Prove the bridge faithful at level 0.
47. Prove arithmetical soundness of the polymodal calculus.
48. Prove a Π_1-conservativity theorem matching Fallenstein 2013.
49. Prove the Π_2-conservativity of every level over its predecessor.
50. Prove a Friedman-translation analog.
51. Prove a Solovay-style arithmetic completeness theorem for the level-0 fragment.
52. Prove Solovay completeness for the full polymodal calculus.
53. Prove the polymodal extension is arithmetically complete relative to the Beklemishev hierarchy.
54. Prove a reflection-schema classification theorem.
55. Prove a reflection-principle hierarchy theorem.
56. Prove the connection to Beklemishev's iterated-reflection hierarchy.
57. Prove that the proof-theoretic ordinal of GLP* equals the Beklemishev value (ε_0 for standard polymodal hierarchy).
58. Prove a temporal-extension procrastination bypass theorem: extend GLP* with "do action a at time t".
59. Prove a Visser-style interpretability logic embedding.
60. Prove a bimodal Σ_1-vs-general provability extension (Smoryński-style).
61. Construct a quantified polymodal logic QGLP* and prove its core metatheorems and completeness.
62. Prove the file's results extend to transfinite levels: define Box_α for ordinals α < ε_0 and prove tiling_consistency lifts.
63. Construct uniform Box_α machinery for α < ε_0.
64. Prove the transfinite extension recovers the full Beklemishev GLP system.
65. Define a graded modality [Bel ≥ p]_n; prove unbounded reflection schema collapses; ε-tolerant variant survives.
66. Construct a probabilistic agent licensure extension and prove a probabilistic YH bypass.
67. Prove a complexity bound: membership in Provable is decidable in PSPACE.
68. Prove PSPACE-hardness of the variable-free fragment.
69. Define a proof-term calculus and prove every closed proof term normalises.
70. Prove the proof-term normal forms are unique up to a specified equational theory.
