(******************************************************************************)
(*                                                                            *)
(*           Parametric Provability: Bypassing the Löbian Obstacle            *)
(*                                                                            *)
(*     Formalizing parametric Löbian obstacle bypass. Yudkowsky-Herreshoff    *)
(*     tiling agents over a chain of proof systems.                           *)
(*                                                                            *)
(*     "Wir müssen wissen, wir werden wissen."                                *)
(*     - David Hilbert, 1930                                                  *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: May 2, 2026                                                      *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(** Entry point.  The development is nine parts, each depending only on
    those before it:

      Calculus           modal language, Provable and its variants, Kripke
                         and neighbourhood semantics, Sambin fixed points,
                         the Bew/T_n tower, CNF ordinals, worms, proof terms
      ArithSyntax        first-order syntax, Robinson Q, Goedel coding, the
                         FOProvesTn reflection tower, Delta_0/Sigma_1 classes
      ArithSemantics     FOsat, the arithmetized proof checker, the HBL
                         conditions, Loeb, Goedel II, FOembed
      ArithInternal      object-level arithmetic: instantiation of open
                         equations, the object-level ring, derivations under
                         hypotheses, the Chinese remainder theorem, beta
                         sequence extension and concatenation, Cantor pairing
      ArithTransfer      substitution and capture conditions through the
                         checker's formula builders, and the transfer of
                         every checker clause to larger tables and shifted
                         positions
      ArithMerge         merging two checked derivations: shifted tracks,
                         merged tables, and the new final entry
      ArithDerivability  the checker body and matrix inside the tower, and
                         the second derivability condition FOHBL2_internal
      Completeness       conservativity, Friedman, Solovay, Japaridze,
                         Visser, Critch, agents, reverse math, lambda-box,
                         Craig
      Decidability       decision procedures, Magari algebras, Veblen and
                         Gamma_0, proof-term rewriting, Stone/Esakia duality

    Requiring [Tiling.Tiling] loads and imports all nine. *)

From Tiling Require Export Calculus.
From Tiling Require Export ArithSyntax.
From Tiling Require Export ArithSemantics.
From Tiling Require Export ArithInternal.
From Tiling Require Export ArithTransfer.
From Tiling Require Export ArithMerge.
From Tiling Require Export ArithDerivability.
From Tiling Require Export Completeness.
From Tiling Require Export Decidability.
