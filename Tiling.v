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

(** Entry point.  The development is five parts, each depending only on
    those before it:

      Calculus        modal language, Provable and its variants, Kripke and
                      neighbourhood semantics, Sambin fixed points, the
                      Bew/T_n tower, CNF ordinals, worms, proof terms
      ArithSyntax     first-order syntax, Robinson Q, Goedel coding, the
                      FOProvesTn reflection tower, Delta_0/Sigma_1 classes
      ArithSemantics  FOsat, the arithmetized proof checker, the HBL
                      conditions, Loeb, Goedel II, FOembed
      Completeness    conservativity, Friedman, Solovay, Japaridze, Visser,
                      Critch, agents, reverse math, lambda-box, Craig
      Decidability    decision procedures, Magari algebras, Veblen and
                      Gamma_0, proof-term rewriting, Stone/Esakia duality

    Requiring [Tiling.Tiling] loads and imports all five. *)

From Tiling Require Export Calculus.
From Tiling Require Export ArithSyntax.
From Tiling Require Export ArithSemantics.
From Tiling Require Export Completeness.
From Tiling Require Export Decidability.
