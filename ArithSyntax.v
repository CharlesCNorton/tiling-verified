(******************************************************************************)
(*                                                                            *)
(*           Parametric Provability: Bypassing the Loebian Obstacle           *)
(*                                                                            *)
(*     Part 2 of 5. First-order syntax, Goedel coding, the FOProvesTn tower.  *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.Classical.
From Stdlib Require Import Logic.ClassicalEpsilon.
Import ListNotations.

From Tiling Require Import Calculus.

Inductive FOTerm : Type :=
  | FOVar : nat -> FOTerm
  | FOZero : FOTerm
  | FOSucc : FOTerm -> FOTerm
  | FOPlus : FOTerm -> FOTerm -> FOTerm
  | FOMult : FOTerm -> FOTerm -> FOTerm.

Inductive FOFormula : Type :=
  | FOEq : FOTerm -> FOTerm -> FOFormula
  | FOFalseF : FOFormula
  | FOImplF : FOFormula -> FOFormula -> FOFormula
  | FOForall : nat -> FOFormula -> FOFormula
  | FOExists : nat -> FOFormula -> FOFormula.

Definition FOTrue : FOFormula := FOImplF FOFalseF FOFalseF.
Definition FONeg (phi : FOFormula) : FOFormula := FOImplF phi FOFalseF.

Fixpoint FOnumeral (n : nat) : FOTerm :=
  match n with
  | 0 => FOZero
  | S k => FOSucc (FOnumeral k)
  end.

Fixpoint FOmax_var_tm (t : FOTerm) : nat :=
  match t with
  | FOVar n => n
  | FOZero => 0
  | FOSucc a => FOmax_var_tm a
  | FOPlus a b => Nat.max (FOmax_var_tm a) (FOmax_var_tm b)
  | FOMult a b => Nat.max (FOmax_var_tm a) (FOmax_var_tm b)
  end.

(** The Robinson Q axioms, schematic in arbitrary terms.  The
    zero-or-succ witness variable is chosen above every variable of the
    instantiating term. *)

Inductive FORobinsonQ : FOFormula -> Prop :=
  | RQ_S_inj : forall a b,
      FORobinsonQ (FOImplF (FOEq (FOSucc a) (FOSucc b)) (FOEq a b))
  | RQ_S_nonzero : forall a,
      FORobinsonQ (FONeg (FOEq (FOSucc a) FOZero))
  | RQ_zero_or_succ : forall x,
      FORobinsonQ (FOImplF (FONeg (FOEq (FOVar x) FOZero))
                            (FOExists (S x)
                               (FOEq (FOVar x) (FOSucc (FOVar (S x))))))
  | RQ_plus_zero : forall a,
      FORobinsonQ (FOEq (FOPlus a FOZero) a)
  | RQ_plus_succ : forall a b,
      FORobinsonQ (FOEq (FOPlus a (FOSucc b)) (FOSucc (FOPlus a b)))
  | RQ_mult_zero : forall a,
      FORobinsonQ (FOEq (FOMult a FOZero) FOZero)
  | RQ_mult_succ : forall a b,
      FORobinsonQ (FOEq (FOMult a (FOSucc b)) (FOPlus (FOMult a b) a)).

(** ** The pure-syntax coding and table-formula layer.

    Everything here is a plain definition over [FOTerm]/[FOFormula]
    and [nat] — Goedel codes, the connective sugar, the bounded
    quantifier builders, the beta-access formula, and the master
    computation-table matrices.  They sit before the tower so the
    consistency axioms and the Loeb rule can mention the provability
    sentence.  Their satisfaction and Delta_0 lemmas stay with the
    toolkit below. *)

Fixpoint FOcode_tm (t : FOTerm) : nat :=
  match t with
  | FOVar x => cpair 0 x
  | FOZero => cpair 1 0
  | FOSucc a => cpair 2 (FOcode_tm a)
  | FOPlus a b => cpair 3 (cpair (FOcode_tm a) (FOcode_tm b))
  | FOMult a b => cpair 4 (cpair (FOcode_tm a) (FOcode_tm b))
  end.

Fixpoint FOcode_f (A : FOFormula) : nat :=
  match A with
  | FOEq a b => cpair 0 (cpair (FOcode_tm a) (FOcode_tm b))
  | FOFalseF => cpair 1 0
  | FOImplF B C => cpair 2 (cpair (FOcode_f B) (FOcode_f C))
  | FOForall x B => cpair 3 (cpair x (FOcode_f B))
  | FOExists x B => cpair 4 (cpair x (FOcode_f B))
  end.

Definition FOAnd (A B : FOFormula) : FOFormula :=
  FONeg (FOImplF A (FONeg B)).
Definition FOOr (A B : FOFormula) : FOFormula :=
  FOImplF (FONeg A) B.

Definition FOcpairF (a b c : FOTerm) : FOFormula :=
  FOEq (FOPlus c c)
       (FOPlus (FOMult (FOPlus a b) (FOSucc (FOPlus a b)))
               (FOPlus b b)).

Definition FOBexC (v : nat) (t : FOTerm) (A : FOFormula) : FOFormula :=
  FOExists v
    (FOAnd
       (FOExists (S v)
          (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) t))
       A).

Definition FOBallC (v : nat) (t : FOTerm) (A : FOFormula) : FOFormula :=
  FOForall v
    (FOImplF
       (FOExists (S v)
          (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) t))
       A).

Definition FObetaF (v : nat) (c d i x : FOTerm) : FOFormula :=
  FOBexC v (FOSucc c)
    (FOAnd
       (FOEq c (FOPlus
                  (FOMult (FOVar v) (FOSucc (FOMult d (FOSucc i))))
                  x))
       (FOBexC (S (S v)) (FOSucc (FOMult d (FOSucc i)))
          (FOEq (FOPlus x (FOSucc (FOVar (S (S v)))))
                (FOSucc (FOMult d (FOSucc i)))))).

Definition tbl_below (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm) : Prop :=
  FOmax_var_tm ct < B /\ FOmax_var_tm dt < B /\
  FOmax_var_tm c1 < B /\ FOmax_var_tm d1 < B /\
  FOmax_var_tm c2 < B /\ FOmax_var_tm d2 < B /\
  FOmax_var_tm c3 < B /\ FOmax_var_tm d3 < B /\
  FOmax_var_tm cr < B /\ FOmax_var_tm dr < B /\
  FOmax_var_tm len < B.

Definition FOlookup (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (tg a1 a2 a3 r : FOTerm) : FOFormula :=
  FOBexC B len
    (FOAnd (FObetaF (B+2) ct dt (FOVar B) tg)
    (FOAnd (FObetaF (B+6) c1 d1 (FOVar B) a1)
    (FOAnd (FObetaF (B+10) c2 d2 (FOVar B) a2)
    (FOAnd (FObetaF (B+14) c3 d3 (FOVar B) a3)
           (FObetaF (B+18) cr dr (FOVar B) r))))).

Definition FOSTEP0 (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (w tc r : FOTerm) : FOFormula :=
  FOOr
    (FOBexC B (FOSucc tc)
       (FOAnd (FOcpairF FOZero (FOVar B) tc)
          (FOOr (FOAnd (FOEq (FOVar B) w) (FOEq r (FOnumeral 1)))
                (FOAnd (FONeg (FOEq (FOVar B) w)) (FOEq r FOZero)))))
  (FOOr
    (FOAnd (FOcpairF (FOnumeral 1) FOZero tc) (FOEq r FOZero))
  (FOOr
    (FOBexC B (FOSucc tc)
       (FOAnd (FOcpairF (FOnumeral 2) (FOVar B) tc)
          (FOlookup (B+2) ct dt c1 d1 c2 d2 c3 d3 cr dr len
             (FOnumeral 0) w (FOVar B) FOZero r)))
  (FOOr
    (FOBexC B (FOSucc tc)
       (FOAnd (FOcpairF (FOnumeral 3) (FOVar B) tc)
          (FOBexC (B+2) (FOSucc (FOVar B))
             (FOBexC (B+4) (FOSucc (FOVar B))
                (FOAnd
                   (FOcpairF (FOVar (B+2)) (FOVar (B+4)) (FOVar B))
                   (FOOr
                      (FOAnd
                         (FOlookup (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr
                            len (FOnumeral 0) w (FOVar (B+2)) FOZero
                            (FOnumeral 1))
                         (FOEq r (FOnumeral 1)))
                      (FOAnd
                         (FOlookup (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr
                            len (FOnumeral 0) w (FOVar (B+2)) FOZero
                            FOZero)
                         (FOlookup (B+28) ct dt c1 d1 c2 d2 c3 d3 cr dr
                            len (FOnumeral 0) w (FOVar (B+4)) FOZero r))))))))
    (FOBexC B (FOSucc tc)
       (FOAnd (FOcpairF (FOnumeral 4) (FOVar B) tc)
          (FOBexC (B+2) (FOSucc (FOVar B))
             (FOBexC (B+4) (FOSucc (FOVar B))
                (FOAnd
                   (FOcpairF (FOVar (B+2)) (FOVar (B+4)) (FOVar B))
                   (FOOr
                      (FOAnd
                         (FOlookup (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr
                            len (FOnumeral 0) w (FOVar (B+2)) FOZero
                            (FOnumeral 1))
                         (FOEq r (FOnumeral 1)))
                      (FOAnd
                         (FOlookup (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr
                            len (FOnumeral 0) w (FOVar (B+2)) FOZero
                            FOZero)
                         (FOlookup (B+28) ct dt c1 d1 c2 d2 c3 d3 cr dr
                            len (FOnumeral 0) w (FOVar (B+4)) FOZero r))))))))))).

Definition FOSTEP_bin (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (w pc r : FOTerm) (k tg : nat) : FOFormula :=
  FOBexC B (FOSucc pc)
    (FOAnd (FOcpairF (FOnumeral k) (FOVar B) pc)
       (FOBexC (B+2) (FOSucc (FOVar B))
          (FOBexC (B+4) (FOSucc (FOVar B))
             (FOAnd
                (FOcpairF (FOVar (B+2)) (FOVar (B+4)) (FOVar B))
                (FOOr
                   (FOAnd
                      (FOlookup (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr
                         len (FOnumeral tg) w (FOVar (B+2)) FOZero
                         (FOnumeral 1))
                      (FOEq r (FOnumeral 1)))
                   (FOAnd
                      (FOlookup (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr
                         len (FOnumeral tg) w (FOVar (B+2)) FOZero
                         FOZero)
                      (FOlookup (B+28) ct dt c1 d1 c2 d2 c3 d3 cr dr
                         len (FOnumeral tg) w (FOVar (B+4)) FOZero
                         r))))))).

Definition FOSTEP_quant0 (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (w pc r : FOTerm) (k tg : nat) : FOFormula :=
  FOBexC B (FOSucc pc)
    (FOAnd (FOcpairF (FOnumeral k) (FOVar B) pc)
       (FOBexC (B+2) (FOSucc (FOVar B))
          (FOBexC (B+4) (FOSucc (FOVar B))
             (FOAnd
                (FOcpairF (FOVar (B+2)) (FOVar (B+4)) (FOVar B))
                (FOOr
                   (FOAnd (FOEq (FOVar (B+2)) w) (FOEq r FOZero))
                   (FOAnd (FONeg (FOEq (FOVar (B+2)) w))
                      (FOlookup (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr
                         len (FOnumeral tg) w (FOVar (B+4)) FOZero
                         r))))))).

Definition FOSTEP1 (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (w pc r : FOTerm) : FOFormula :=
  FOOr
    (FOSTEP_bin B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r 0 0)
  (FOOr
    (FOAnd (FOcpairF (FOnumeral 1) FOZero pc) (FOEq r FOZero))
  (FOOr
    (FOSTEP_bin B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r 2 1)
  (FOOr
    (FOSTEP_quant0 B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r 3 1)
    (FOSTEP_quant0 B ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc r 4 1)))).

Definition FOSTEP5 (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (a1 r : FOTerm) : FOFormula :=
  FOOr
    (FOAnd (FOEq a1 FOZero) (FOcpairF (FOnumeral 1) FOZero r))
    (FOBexC B a1
       (FOAnd (FOEq a1 (FOSucc (FOVar B)))
          (FOBexC (B+2) r
             (FOAnd
                (FOlookup (B+4) ct dt c1 d1 c2 d2 c3 d3 cr dr len
                   (FOnumeral 5) (FOVar B) FOZero FOZero
                   (FOVar (B+2)))
                (FOcpairF (FOnumeral 2) (FOVar (B+2)) r))))).

Definition FOSTEP_substbin (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (x sc tc r : FOTerm) (ktag lktag rtag : nat) : FOFormula :=
  FOBexC B (FOSucc tc)
    (FOAnd (FOcpairF (FOnumeral ktag) (FOVar B) tc)
       (FOBexC (B+2) (FOSucc (FOVar B))
          (FOBexC (B+4) (FOSucc (FOVar B))
             (FOAnd
                (FOcpairF (FOVar (B+2)) (FOVar (B+4)) (FOVar B))
                (FOBexC (B+6) (FOSucc r)
                   (FOBexC (B+8) (FOSucc r)
                      (FOAnd
                         (FOlookup (B+10) ct dt c1 d1 c2 d2 c3 d3 cr dr
                            len (FOnumeral lktag) x sc (FOVar (B+2))
                            (FOVar (B+6)))
                      (FOAnd
                         (FOlookup (B+32) ct dt c1 d1 c2 d2 c3 d3 cr dr
                            len (FOnumeral lktag) x sc (FOVar (B+4))
                            (FOVar (B+8)))
                         (FOBexC (B+54) (FOSucc r)
                            (FOAnd
                               (FOcpairF (FOVar (B+6)) (FOVar (B+8))
                                  (FOVar (B+54)))
                               (FOcpairF (FOnumeral rtag)
                                  (FOVar (B+54)) r))))))))))).

Definition FOSTEP2 (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (x sc tc r : FOTerm) : FOFormula :=
  FOOr
    (FOBexC B (FOSucc tc)
       (FOAnd (FOcpairF FOZero (FOVar B) tc)
          (FOOr (FOAnd (FOEq (FOVar B) x) (FOEq r sc))
                (FOAnd (FONeg (FOEq (FOVar B) x)) (FOEq r tc)))))
  (FOOr
    (FOAnd (FOcpairF (FOnumeral 1) FOZero tc) (FOEq r tc))
  (FOOr
    (FOBexC B (FOSucc tc)
       (FOAnd (FOcpairF (FOnumeral 2) (FOVar B) tc)
          (FOBexC (B+2) r
             (FOAnd
                (FOlookup (B+4) ct dt c1 d1 c2 d2 c3 d3 cr dr len
                   (FOnumeral 2) x sc (FOVar B) (FOVar (B+2)))
                (FOcpairF (FOnumeral 2) (FOVar (B+2)) r)))))
  (FOOr
    (FOSTEP_substbin B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc tc r
       3 2 3)
    (FOSTEP_substbin B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc tc r
       4 2 4)))).

Definition FOSTEP_substquant (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (x sc pc r : FOTerm) (ktag : nat) : FOFormula :=
  FOBexC B (FOSucc pc)
    (FOAnd (FOcpairF (FOnumeral ktag) (FOVar B) pc)
       (FOBexC (B+2) (FOSucc (FOVar B))
          (FOBexC (B+4) (FOSucc (FOVar B))
             (FOAnd
                (FOcpairF (FOVar (B+2)) (FOVar (B+4)) (FOVar B))
                (FOOr
                   (FOAnd (FOEq (FOVar (B+2)) x) (FOEq r pc))
                   (FOAnd (FONeg (FOEq (FOVar (B+2)) x))
                      (FOBexC (B+6) r
                         (FOAnd
                            (FOlookup (B+8) ct dt c1 d1 c2 d2 c3 d3 cr
                               dr len (FOnumeral 3) x sc (FOVar (B+4))
                               (FOVar (B+6)))
                            (FOBexC (B+30) (FOSucc r)
                               (FOAnd
                                  (FOcpairF (FOVar (B+2))
                                     (FOVar (B+6)) (FOVar (B+30)))
                                  (FOcpairF (FOnumeral ktag)
                                     (FOVar (B+30)) r))))))))))).

Definition FOSTEP3 (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (x sc pc r : FOTerm) : FOFormula :=
  FOOr
    (FOSTEP_substbin B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r
       0 2 0)
  (FOOr
    (FOAnd (FOcpairF (FOnumeral 1) FOZero pc) (FOEq r pc))
  (FOOr
    (FOSTEP_substbin B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r
       2 3 2)
  (FOOr
    (FOSTEP_substquant B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r 3)
    (FOSTEP_substquant B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r
       4)))).

Definition FOSTEP_subokbin (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (x sc pc r : FOTerm) : FOFormula :=
  FOBexC B (FOSucc pc)
    (FOAnd (FOcpairF (FOnumeral 2) (FOVar B) pc)
       (FOBexC (B+2) (FOSucc (FOVar B))
          (FOBexC (B+4) (FOSucc (FOVar B))
             (FOAnd
                (FOcpairF (FOVar (B+2)) (FOVar (B+4)) (FOVar B))
                (FOOr
                   (FOAnd
                      (FOlookup (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr
                         len (FOnumeral 4) x sc (FOVar (B+2)) FOZero)
                      (FOEq r FOZero))
                   (FOAnd
                      (FOlookup (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr
                         len (FOnumeral 4) x sc (FOVar (B+2))
                         (FOnumeral 1))
                      (FOlookup (B+28) ct dt c1 d1 c2 d2 c3 d3 cr dr
                         len (FOnumeral 4) x sc (FOVar (B+4)) r))))))).

Definition FOSTEP_subokquant (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (x sc pc r : FOTerm) (k : nat) : FOFormula :=
  FOBexC B (FOSucc pc)
    (FOAnd (FOcpairF (FOnumeral k) (FOVar B) pc)
       (FOBexC (B+2) (FOSucc (FOVar B))
          (FOBexC (B+4) (FOSucc (FOVar B))
             (FOAnd
                (FOcpairF (FOVar (B+2)) (FOVar (B+4)) (FOVar B))
                (FOOr
                   (FOAnd (FOEq (FOVar (B+2)) x) (FOEq r (FOnumeral 1)))
                   (FOAnd (FONeg (FOEq (FOVar (B+2)) x))
                      (FOOr
                         (FOAnd
                            (FOlookup (B+6) ct dt c1 d1 c2 d2 c3 d3 cr
                               dr len (FOnumeral 1) x (FOVar (B+4))
                               FOZero FOZero)
                            (FOEq r (FOnumeral 1)))
                         (FOAnd
                            (FOlookup (B+6) ct dt c1 d1 c2 d2 c3 d3 cr
                               dr len (FOnumeral 1) x (FOVar (B+4))
                               FOZero (FOnumeral 1))
                            (FOOr
                               (FOAnd
                                  (FOlookup (B+28) ct dt c1 d1 c2 d2 c3
                                     d3 cr dr len (FOnumeral 0)
                                     (FOVar (B+2)) sc FOZero
                                     (FOnumeral 1))
                                  (FOEq r FOZero))
                               (FOAnd
                                  (FOlookup (B+28) ct dt c1 d1 c2 d2 c3
                                     d3 cr dr len (FOnumeral 0)
                                     (FOVar (B+2)) sc FOZero FOZero)
                                  (FOlookup (B+50) ct dt c1 d1 c2 d2 c3
                                     d3 cr dr len (FOnumeral 4) x sc
                                     (FOVar (B+4)) r))))))))))).

Definition FOSTEP4 (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (x sc pc r : FOTerm) : FOFormula :=
  FOOr
    (FOBexC B (FOSucc pc)
       (FOAnd (FOcpairF FOZero (FOVar B) pc)
          (FOEq r (FOnumeral 1))))
  (FOOr
    (FOAnd (FOcpairF (FOnumeral 1) FOZero pc) (FOEq r (FOnumeral 1)))
  (FOOr
    (FOSTEP_subokbin B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r)
  (FOOr
    (FOSTEP_subokquant B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r 3)
    (FOSTEP_subokquant B ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc r
       4)))).

Definition FOSTEPDISPATCH (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (j : FOTerm) : FOFormula :=
  FOBexC B (FOSucc ct)
  (FOBexC (B+2) (FOSucc c1)
  (FOBexC (B+4) (FOSucc c2)
  (FOBexC (B+6) (FOSucc c3)
  (FOBexC (B+8) (FOSucc cr)
    (FOAnd (FObetaF (B+10) ct dt j (FOVar B))
    (FOAnd (FObetaF (B+14) c1 d1 j (FOVar (B+2)))
    (FOAnd (FObetaF (B+18) c2 d2 j (FOVar (B+4)))
    (FOAnd (FObetaF (B+22) c3 d3 j (FOVar (B+6)))
    (FOAnd (FObetaF (B+26) cr dr j (FOVar (B+8)))
      (FOOr
         (FOAnd (FOEq (FOVar B) FOZero)
            (FOSTEP0 (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len
               (FOVar (B+2)) (FOVar (B+4)) (FOVar (B+8))))
      (FOOr
         (FOAnd (FOEq (FOVar B) (FOnumeral 1))
            (FOSTEP1 (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len
               (FOVar (B+2)) (FOVar (B+4)) (FOVar (B+8))))
      (FOOr
         (FOAnd (FOEq (FOVar B) (FOnumeral 2))
            (FOSTEP2 (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len
               (FOVar (B+2)) (FOVar (B+4)) (FOVar (B+6))
               (FOVar (B+8))))
      (FOOr
         (FOAnd (FOEq (FOVar B) (FOnumeral 3))
            (FOSTEP3 (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len
               (FOVar (B+2)) (FOVar (B+4)) (FOVar (B+6))
               (FOVar (B+8))))
      (FOOr
         (FOAnd (FOEq (FOVar B) (FOnumeral 4))
            (FOSTEP4 (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len
               (FOVar (B+2)) (FOVar (B+4)) (FOVar (B+6))
               (FOVar (B+8))))
         (FOAnd (FOEq (FOVar B) (FOnumeral 5))
            (FOSTEP5 (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len
               (FOVar (B+2)) (FOVar (B+8)))))))))))))))))).

Definition FOTBLVALID (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm) : FOFormula :=
  FOBallC B len
    (FOSTEPDISPATCH (B+2) ct dt c1 d1 c2 d2 c3 d3 cr dr len
       (FOVar B)).

Fixpoint FOsubst_tm (x k : nat) (t : FOTerm) : FOTerm :=
  match t with
  | FOVar y => if Nat.eqb y x then FOnumeral k else FOVar y
  | FOZero => FOZero
  | FOSucc a => FOSucc (FOsubst_tm x k a)
  | FOPlus a b => FOPlus (FOsubst_tm x k a) (FOsubst_tm x k b)
  | FOMult a b => FOMult (FOsubst_tm x k a) (FOsubst_tm x k b)
  end.

Fixpoint FOsubst_num (x k : nat) (A : FOFormula) : FOFormula :=
  match A with
  | FOEq a b => FOEq (FOsubst_tm x k a) (FOsubst_tm x k b)
  | FOFalseF => FOFalseF
  | FOImplF A B => FOImplF (FOsubst_num x k A) (FOsubst_num x k B)
  | FOForall y A =>
      if Nat.eqb y x then FOForall y A else FOForall y (FOsubst_num x k A)
  | FOExists y A =>
      if Nat.eqb y x then FOExists y A else FOExists y (FOsubst_num x k A)
  end.

(** ** Code patterns.

    A [CPat] is a cpair tree with literal leaves, slot leaves indexing
    an environment of terms, and a successor node.  [FOPATF] renders a
    pattern as a Delta_0 formula matching a code term against the tree,
    one bounded witness pair per internal node.  [cpat_sem] is its
    numeric semantics.  Every code-shape recognizer below — Robinson
    axioms, logical axioms, rule shapes — is one pattern instance. *)

Inductive CPat : Type :=
  | CLit : nat -> CPat
  | CVarP : nat -> CPat
  | CSuccP : CPat -> CPat
  | CPair : CPat -> CPat -> CPat.

Fixpoint cpat_sem (sigma : nat -> nat) (p : CPat) : nat :=
  match p with
  | CLit k => k
  | CVarP s => sigma s
  | CSuccP q => S (cpat_sem sigma q)
  | CPair a b => cpair (cpat_sem sigma a) (cpat_sem sigma b)
  end.

Fixpoint cpat_pairs (p : CPat) : nat :=
  match p with
  | CLit _ => 0
  | CVarP _ => 0
  | CSuccP q => 1 + cpat_pairs q
  | CPair a b => 1 + cpat_pairs a + cpat_pairs b
  end.

Fixpoint cpat_occurs (s : nat) (p : CPat) : bool :=
  match p with
  | CLit _ => false
  | CVarP s' => Nat.eqb s' s
  | CSuccP q => cpat_occurs s q
  | CPair a b => cpat_occurs s a || cpat_occurs s b
  end.

Fixpoint FOPATF (B : nat) (env : list FOTerm) (p : CPat)
    (d : FOTerm) : FOFormula :=
  match p with
  | CLit k => FOEq d (FOnumeral k)
  | CVarP s => FOEq d (nth s env FOZero)
  | CSuccP q =>
      FOBexC B d
        (FOAnd (FOEq d (FOSucc (FOVar B)))
               (FOPATF (B+2) env q (FOVar B)))
  | CPair a b =>
      FOBexC B (FOSucc d)
        (FOBexC (B+2) (FOSucc d)
           (FOAnd (FOcpairF (FOVar B) (FOVar (B+2)) d)
           (FOAnd (FOPATF (B+4) env a (FOVar B))
                  (FOPATF (B+4+4*cpat_pairs a) env b (FOVar (B+2))))))
  end.

(** Pattern shorthands mirroring [FOcode_f] and [FOcode_tm]. *)

Definition pEqP (a b : CPat) : CPat := CPair (CLit 0) (CPair a b).
Definition pFlsP : CPat := CPair (CLit 1) (CLit 0).
Definition pImpP (a b : CPat) : CPat := CPair (CLit 2) (CPair a b).
Definition pAllP (x a : CPat) : CPat := CPair (CLit 3) (CPair x a).
Definition pExP (x a : CPat) : CPat := CPair (CLit 4) (CPair x a).
Definition tVarP (x : CPat) : CPat := CPair (CLit 0) x.
Definition tZeroP : CPat := CPair (CLit 1) (CLit 0).
Definition tSuccP (a : CPat) : CPat := CPair (CLit 2) a.
Definition tPlusP (a b : CPat) : CPat := CPair (CLit 3) (CPair a b).
Definition tMultP (a b : CPat) : CPat := CPair (CLit 4) (CPair a b).

(** The seven Robinson axiom-scheme patterns. *)

Definition cpatQ1 : CPat :=
  pImpP (pEqP (tSuccP (CVarP 0)) (tSuccP (CVarP 1)))
        (pEqP (CVarP 0) (CVarP 1)).
Definition cpatQ2 : CPat :=
  pImpP (pEqP (tSuccP (CVarP 0)) tZeroP) pFlsP.
Definition cpatQ3 : CPat :=
  pImpP (pImpP (pEqP (tVarP (CVarP 0)) tZeroP) pFlsP)
        (pExP (CSuccP (CVarP 0))
              (pEqP (tVarP (CVarP 0))
                    (tSuccP (tVarP (CSuccP (CVarP 0)))))).
Definition cpatQ4 : CPat :=
  pEqP (tPlusP (CVarP 0) tZeroP) (CVarP 0).
Definition cpatQ5 : CPat :=
  pEqP (tPlusP (CVarP 0) (tSuccP (CVarP 1)))
       (tSuccP (tPlusP (CVarP 0) (CVarP 1))).
Definition cpatQ6 : CPat :=
  pEqP (tMultP (CVarP 0) tZeroP) tZeroP.
Definition cpatQ7 : CPat :=
  pEqP (tMultP (CVarP 0) (tSuccP (CVarP 1)))
       (tPlusP (tMultP (CVarP 0) (CVarP 1)) (CVarP 0)).

(** The twelve logical axiom-scheme patterns. *)

Definition cpatLK : CPat :=
  pImpP (CVarP 0) (pImpP (CVarP 1) (CVarP 0)).
Definition cpatLS : CPat :=
  pImpP (pImpP (CVarP 0) (pImpP (CVarP 1) (CVarP 2)))
        (pImpP (pImpP (CVarP 0) (CVarP 1)) (pImpP (CVarP 0) (CVarP 2))).
Definition cpatLDN : CPat :=
  pImpP (pImpP (pImpP (CVarP 0) pFlsP) pFlsP) (CVarP 0).
Definition cpatLEqRefl : CPat := pEqP (CVarP 0) (CVarP 0).
Definition cpatLEqSym : CPat :=
  pImpP (pEqP (CVarP 0) (CVarP 1)) (pEqP (CVarP 1) (CVarP 0)).
Definition cpatLEqTrans : CPat :=
  pImpP (pEqP (CVarP 0) (CVarP 1))
        (pImpP (pEqP (CVarP 1) (CVarP 2)) (pEqP (CVarP 0) (CVarP 2))).
Definition cpatLCongS : CPat :=
  pImpP (pEqP (CVarP 0) (CVarP 1))
        (pEqP (tSuccP (CVarP 0)) (tSuccP (CVarP 1))).
Definition cpatLCongPlus : CPat :=
  pImpP (pEqP (CVarP 0) (CVarP 1))
        (pImpP (pEqP (CVarP 2) (CVarP 3))
               (pEqP (tPlusP (CVarP 0) (CVarP 2))
                     (tPlusP (CVarP 1) (CVarP 3)))).
Definition cpatLCongMult : CPat :=
  pImpP (pEqP (CVarP 0) (CVarP 1))
        (pImpP (pEqP (CVarP 2) (CVarP 3))
               (pEqP (tMultP (CVarP 0) (CVarP 2))
                     (tMultP (CVarP 1) (CVarP 3)))).
Definition cpatLExElim : CPat :=
  pImpP (pAllP (CVarP 0) (pImpP (CVarP 1) (CVarP 2)))
        (pImpP (pExP (CVarP 0) (CVarP 1)) (CVarP 2)).
Definition cpatLAllK : CPat :=
  pImpP (pAllP (CVarP 0) (pImpP (CVarP 1) (CVarP 2)))
        (pImpP (pAllP (CVarP 0) (CVarP 1)) (pAllP (CVarP 0) (CVarP 2))).
Definition cpatLAllExport : CPat :=
  pImpP (pAllP (CVarP 0) (pImpP (CVarP 1) (CVarP 2)))
        (pImpP (CVarP 1) (pAllP (CVarP 0) (CVarP 2))).

(** Rule-shape patterns used by the justification checker. *)

Definition cpatImpl01 : CPat := pImpP (CVarP 0) (CVarP 1).
Definition cpatImpl012 : CPat :=
  pImpP (CVarP 0) (pImpP (CVarP 1) (CVarP 2)).
Definition cpatAll01 : CPat := pAllP (CVarP 0) (CVarP 1).
Definition cpatAllElim : CPat :=
  pImpP (pAllP (CVarP 0) (CVarP 1)) (CVarP 2).
Definition cpatExIntro : CPat :=
  pImpP (CVarP 2) (pExP (CVarP 0) (CVarP 1)).

(** The induction-axiom shape over slots [0=x], [1=A], [2=A[x:=0]],
    [3=A[x:=S x]]: the curried base/step/conclusion form. *)
Definition cpatInd : CPat :=
  pImpP (CVarP 2)
        (pImpP (pAllP (CVarP 0) (pImpP (CVarP 1) (CVarP 3)))
               (pAllP (CVarP 0) (CVarP 1))).

(** Code-level recognizers.  [FOAXQc] holds of [d] exactly when [d]
    codes an instance of one of the seven Robinson schemes; the slot
    witnesses are the component codes, each bounded by the code. *)

Definition FOAXQ1c (B : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOBexC (B+2) (FOSucc d)
       (FOPATF (B+4) [FOVar B; FOVar (B+2)] cpatQ1 d)).
Definition FOAXQ2c (B : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOPATF (B+2) [FOVar B] cpatQ2 d).
Definition FOAXQ3c (B : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOPATF (B+2) [FOVar B] cpatQ3 d).
Definition FOAXQ4c (B : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOPATF (B+2) [FOVar B] cpatQ4 d).
Definition FOAXQ5c (B : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOBexC (B+2) (FOSucc d)
       (FOPATF (B+4) [FOVar B; FOVar (B+2)] cpatQ5 d)).
Definition FOAXQ6c (B : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOPATF (B+2) [FOVar B] cpatQ6 d).
Definition FOAXQ7c (B : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOBexC (B+2) (FOSucc d)
       (FOPATF (B+4) [FOVar B; FOVar (B+2)] cpatQ7 d)).

Definition FOAXQc (B : nat) (d : FOTerm) : FOFormula :=
  FOOr (FOAXQ1c B d)
  (FOOr (FOAXQ2c B d)
  (FOOr (FOAXQ3c B d)
  (FOOr (FOAXQ4c B d)
  (FOOr (FOAXQ5c B d)
  (FOOr (FOAXQ6c B d)
        (FOAXQ7c B d)))))).

(** Logical-axiom recognizers.  Two of them carry the freshness side
    condition as a tag-1 master-table lookup. *)

Definition FOLOG1c (B : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOBexC (B+2) (FOSucc d)
       (FOPATF (B+4) [FOVar B; FOVar (B+2)] cpatLK d)).
Definition FOLOG2c (B : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOBexC (B+2) (FOSucc d)
       (FOBexC (B+4) (FOSucc d)
          (FOPATF (B+6) [FOVar B; FOVar (B+2); FOVar (B+4)] cpatLS d))).
Definition FOLOG3c (B : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOPATF (B+2) [FOVar B] cpatLDN d).
Definition FOLOG4c (B : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOPATF (B+2) [FOVar B] cpatLEqRefl d).
Definition FOLOG5c (B : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOBexC (B+2) (FOSucc d)
       (FOPATF (B+4) [FOVar B; FOVar (B+2)] cpatLEqSym d)).
Definition FOLOG6c (B : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOBexC (B+2) (FOSucc d)
       (FOBexC (B+4) (FOSucc d)
          (FOPATF (B+6) [FOVar B; FOVar (B+2); FOVar (B+4)]
             cpatLEqTrans d))).
Definition FOLOG7c (B : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOBexC (B+2) (FOSucc d)
       (FOPATF (B+4) [FOVar B; FOVar (B+2)] cpatLCongS d)).
Definition FOLOG8c (B : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOBexC (B+2) (FOSucc d)
       (FOBexC (B+4) (FOSucc d)
          (FOBexC (B+6) (FOSucc d)
             (FOPATF (B+8)
                [FOVar B; FOVar (B+2); FOVar (B+4); FOVar (B+6)]
                cpatLCongPlus d)))).
Definition FOLOG9c (B : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOBexC (B+2) (FOSucc d)
       (FOBexC (B+4) (FOSucc d)
          (FOBexC (B+6) (FOSucc d)
             (FOPATF (B+8)
                [FOVar B; FOVar (B+2); FOVar (B+4); FOVar (B+6)]
                cpatLCongMult d)))).
Definition FOLOG10c (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOBexC (B+2) (FOSucc d)
       (FOBexC (B+4) (FOSucc d)
          (FOAnd
             (FOPATF (B+6) [FOVar B; FOVar (B+2); FOVar (B+4)]
                cpatLExElim d)
             (FOlookup (B+60) ct dt c1 d1 c2 d2 c3 d3 cr dr len
                (FOnumeral 1) (FOVar B) (FOVar (B+4)) FOZero FOZero)))).
Definition FOLOG11c (B : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOBexC (B+2) (FOSucc d)
       (FOBexC (B+4) (FOSucc d)
          (FOPATF (B+6) [FOVar B; FOVar (B+2); FOVar (B+4)]
             cpatLAllK d))).
Definition FOLOG12c (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOBexC (B+2) (FOSucc d)
       (FOBexC (B+4) (FOSucc d)
          (FOAnd
             (FOPATF (B+6) [FOVar B; FOVar (B+2); FOVar (B+4)]
                cpatLAllExport d)
             (FOlookup (B+60) ct dt c1 d1 c2 d2 c3 d3 cr dr len
                (FOnumeral 1) (FOVar B) (FOVar (B+2)) FOZero FOZero)))).

Definition FOLOGc (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (d : FOTerm) : FOFormula :=
  FOOr (FOLOG1c B d)
  (FOOr (FOLOG2c B d)
  (FOOr (FOLOG3c B d)
  (FOOr (FOLOG4c B d)
  (FOOr (FOLOG5c B d)
  (FOOr (FOLOG6c B d)
  (FOOr (FOLOG7c B d)
  (FOOr (FOLOG8c B d)
  (FOOr (FOLOG9c B d)
  (FOOr (FOLOG10c B ct dt c1 d1 c2 d2 c3 d3 cr dr len d)
  (FOOr (FOLOG11c B d)
        (FOLOG12c B ct dt c1 d1 c2 d2 c3 d3 cr dr len d))))))))))).

(** Reflection-instance recognizer for one lower template core code
    [c]: [d] codes [Impl (core c applied to numeral a) A] where [a] is
    the code of [A].  The application is computed through the table:
    tag 5 turns [a] into its numeral code, tag 3 substitutes it at
    variable 1 inside [c]. *)

Definition FOAXREFLc (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (c : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc d)
    (FOBexC (B+2) (FOSucc cr)
       (FOBexC (B+4) (FOSucc cr)
          (FOAnd
             (FOlookup (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr len
                (FOnumeral 5) (FOVar B) FOZero FOZero (FOVar (B+2)))
          (FOAnd
             (FOlookup (B+28) ct dt c1 d1 c2 d2 c3 d3 cr dr len
                (FOnumeral 3) (FOnumeral 1) (FOVar (B+2))
                (FOnumeral c) (FOVar (B+4)))
             (FOPATF (B+50) [FOVar (B+4); FOVar B] cpatImpl01 d))))).

Fixpoint FOREFLSc (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (cores : list nat) (d : FOTerm) : FOFormula :=
  match cores with
  | [] => FOFalseF
  | c :: rest =>
      FOOr (FOAXREFLc B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d)
           (FOREFLSc B ct dt c1 d1 c2 d2 c3 d3 cr dr len rest d)
  end.

Definition FOTHAXc (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (cores : list nat) (d : FOTerm) : FOFormula :=
  FOOr (FOAXQc B d)
       (FOREFLSc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d).

(** The justification checker at one derivation position [i].  The
    formula code at [i] and the justification code at [i] come off the
    two derivation tracks; the justification splits as
    [cpair jtag payload] and dispatches on [jtag]:
    0 theory axiom, 1 logical axiom, 2 forall-elimination,
    3 exists-introduction, 4 modus ponens, 5 generalization,
    6 the Loeb rule against the self template [u] (variable 0). *)

Definition FOJSUBST (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (pat : CPat) (vd pl : FOTerm) : FOFormula :=
  FOBexC B (FOSucc pl)
  (FOBexC (B+2) (FOSucc pl)
    (FOAnd (FOcpairF (FOVar B) (FOVar (B+2)) pl)
    (FOBexC (B+4) (FOSucc vd)
    (FOBexC (B+6) (FOSucc vd)
      (FOAnd
         (FOPATF (B+8) [FOVar B; FOVar (B+4); FOVar (B+6)] pat vd)
      (FOAnd
         (FOlookup (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len
            (FOnumeral 4) (FOVar B) (FOVar (B+2)) (FOVar (B+4))
            (FOnumeral 1))
         (FOlookup (B+52) ct dt c1 d1 c2 d2 c3 d3 cr dr len
            (FOnumeral 3) (FOVar B) (FOVar (B+2)) (FOVar (B+4))
            (FOVar (B+6))))))))).

(** The induction-axiom recognizer.  [pl = cpair x PA] supplies the
    induction variable [x] and the body code [PA].  Two table lookups
    each check a substitution into [PA]: the base at the closed term
    [FOZero] (term code [cpair 1 0]) giving [C0], and the step at
    [FOSucc (FOVar x)] (term code [cpair 2 (cpair 0 x)], built by two
    pairings [vx], [tcs]) giving [SS].  Nine pairings then assemble the
    code of

      FOInduction x A
        = (A[x:=0]) -> (forall x, A -> A[x:=S x]) -> forall x, A

    bottom-up into [vd].  The step term code is not a subterm of [vd],
    so [vx] and [tcs] carry the square over-bounds [(x+1)^2] and
    [(vx+3)^2] in place of the [FOSucc vd] bound used by the
    subformula nodes. *)

Definition FOJIND (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (vd pl : FOTerm) : FOFormula :=
  FOBexC B (FOSucc pl)
  (FOBexC (B+2) (FOSucc pl)
    (FOAnd (FOcpairF (FOVar B) (FOVar (B+2)) pl)
  (FOBexC (B+4) (FOSucc vd)
  (FOBexC (B+6) (FOSucc vd)
  (FOBexC (B+8) (FOSucc (FOMult (FOSucc (FOVar B)) (FOSucc (FOVar B))))
  (FOBexC (B+10) (FOSucc (FOMult (FOSucc (FOSucc (FOSucc (FOVar (B+8)))))
                                 (FOSucc (FOSucc (FOSucc (FOVar (B+8)))))))
    (FOAnd (FOcpairF FOZero (FOVar B) (FOVar (B+8)))
    (FOAnd (FOcpairF (FOnumeral 2) (FOVar (B+8)) (FOVar (B+10)))
    (FOAnd (FOPATF (B+12)
              [FOVar B; FOVar (B+2); FOVar (B+4); FOVar (B+6)] cpatInd vd)
    (FOAnd (FOlookup (B+52) ct dt c1 d1 c2 d2 c3 d3 cr dr len
              (FOnumeral 4) (FOVar B) (FOnumeral (cpair 1 0))
              (FOVar (B+2)) (FOnumeral 1))
    (FOAnd (FOlookup (B+74) ct dt c1 d1 c2 d2 c3 d3 cr dr len
              (FOnumeral 3) (FOVar B) (FOnumeral (cpair 1 0))
              (FOVar (B+2)) (FOVar (B+4)))
    (FOAnd (FOlookup (B+96) ct dt c1 d1 c2 d2 c3 d3 cr dr len
              (FOnumeral 4) (FOVar B) (FOVar (B+10))
              (FOVar (B+2)) (FOnumeral 1))
           (FOlookup (B+118) ct dt c1 d1 c2 d2 c3 d3 cr dr len
              (FOnumeral 3) (FOVar B) (FOVar (B+10))
              (FOVar (B+2)) (FOVar (B+6)))
    )))))))))))).

Definition FOJMP (B : nat) (cs ds : FOTerm)
    (vd pl ipos : FOTerm) : FOFormula :=
  FOBexC B ipos
  (FOBexC (B+2) ipos
    (FOAnd (FOcpairF (FOVar B) (FOVar (B+2)) pl)
    (FOBexC (B+4) (FOSucc cs)
    (FOBexC (B+6) (FOSucc cs)
      (FOAnd (FObetaF (B+8) cs ds (FOVar B) (FOVar (B+4)))
      (FOAnd (FObetaF (B+12) cs ds (FOVar (B+2)) (FOVar (B+6)))
         (FOPATF (B+16) [FOVar (B+6); vd] cpatImpl01
            (FOVar (B+4))))))))).

Definition FOJGEN (B : nat) (cs ds : FOTerm)
    (vd pl ipos : FOTerm) : FOFormula :=
  FOBexC B ipos
  (FOAnd (FOEq (FOVar B) pl)
  (FOBexC (B+2) (FOSucc cs)
    (FOAnd (FObetaF (B+4) cs ds (FOVar B) (FOVar (B+2)))
    (FOBexC (B+8) (FOSucc vd)
      (FOPATF (B+10) [FOVar (B+8); FOVar (B+2)] cpatAll01 vd))))).

Definition FOJLOEB (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (cs ds : FOTerm) (vd pl ipos : FOTerm) : FOFormula :=
  FOBexC B ipos
  (FOAnd (FOEq (FOVar B) pl)
  (FOBexC (B+2) (FOSucc cs)
    (FOAnd (FObetaF (B+4) cs ds (FOVar B) (FOVar (B+2)))
    (FOBexC (B+8) (FOSucc cr)
    (FOBexC (B+10) (FOSucc cr)
    (FOBexC (B+12) (FOSucc cr)
    (FOBexC (B+14) (FOSucc cr)
      (FOAnd
         (FOlookup (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len
            (FOnumeral 5) (FOVar 0) FOZero FOZero (FOVar (B+8)))
      (FOAnd
         (FOlookup (B+38) ct dt c1 d1 c2 d2 c3 d3 cr dr len
            (FOnumeral 3) FOZero (FOVar (B+8)) (FOVar 0)
            (FOVar (B+10)))
      (FOAnd
         (FOlookup (B+60) ct dt c1 d1 c2 d2 c3 d3 cr dr len
            (FOnumeral 5) vd FOZero FOZero (FOVar (B+12)))
      (FOAnd
         (FOlookup (B+82) ct dt c1 d1 c2 d2 c3 d3 cr dr len
            (FOnumeral 3) (FOnumeral 1) (FOVar (B+12))
            (FOVar (B+10)) (FOVar (B+14)))
         (FOPATF (B+104) [FOVar (B+14); vd] cpatImpl01
            (FOVar (B+2)))))))))))))).

(** Applied provability code: [p] codes the level template [c]
    applied to the numeral of [z] — a tag-5 row turns [z] into its
    numeral code, a tag-3 row substitutes it at variable 1 inside
    [c].  This is the reflection recognizer's row pair factored out;
    the formalized derivability axioms each consult it. *)

Definition FOPROVAT (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (c : nat) (z p : FOTerm) : FOFormula :=
  FOBexC B (FOSucc cr)
    (FOAnd
       (FOlookup (B+2) ct dt c1 d1 c2 d2 c3 d3 cr dr len
          (FOnumeral 5) z FOZero FOZero (FOVar B))
       (FOlookup (B+24) ct dt c1 d1 c2 d2 c3 d3 cr dr len
          (FOnumeral 3) (FOnumeral 1) (FOVar B) (FOnumeral c) p)).

(** Code recognizers for the formalized derivability axioms at one
    core [c]: distribution of provability over implication, provable
    upward persistence, and level monotonicity.  Component codes are
    bounded by the argument track, applied provability codes by the
    result track.  [FOGENF] is the genuineness guard: a substitution
    row at the shadow variable [S z] forces [z] to be a formula
    code. *)

Definition FOGENF (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (z : FOTerm) : FOFormula :=
  FOBexC B (FOSucc cr)
    (FOlookup (B+2) ct dt c1 d1 c2 d2 c3 d3 cr dr len
       (FOnumeral 3) (FOSucc z) FOZero z (FOVar B)).

Definition FOD2c (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (c : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc c1)
  (FOBexC (B+2) (FOSucc c1)
  (FOBexC (B+4) (FOSucc c1)
  (FOBexC (B+6) (FOSucc c1)
  (FOBexC (B+8) (FOSucc cr)
  (FOBexC (B+10) (FOSucc cr)
  (FOBexC (B+12) (FOSucc cr)
    (FOAnd (FOcpairF (FOVar B) (FOVar (B+2)) (FOVar (B+4)))
    (FOAnd (FOcpairF (FOnumeral 2) (FOVar (B+4)) (FOVar (B+6)))
    (FOAnd (FOGENF (B+14) ct dt c1 d1 c2 d2 c3 d3 cr dr len
              (FOVar B))
    (FOAnd (FOGENF (B+38) ct dt c1 d1 c2 d2 c3 d3 cr dr len
              (FOVar (B+2)))
    (FOAnd (FOPROVAT (B+62) ct dt c1 d1 c2 d2 c3 d3 cr dr len
              c (FOVar (B+6)) (FOVar (B+8)))
    (FOAnd (FOPROVAT (B+108) ct dt c1 d1 c2 d2 c3 d3 cr dr len
              c (FOVar B) (FOVar (B+10)))
    (FOAnd (FOPROVAT (B+154) ct dt c1 d1 c2 d2 c3 d3 cr dr len
              c (FOVar (B+2)) (FOVar (B+12)))
           (FOPATF (B+200)
              [FOVar (B+8); FOVar (B+10); FOVar (B+12)]
              cpatImpl012 d)))))))))))))).

Definition FOD3c (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (c : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc c1)
  (FOBexC (B+2) (FOSucc cr)
  (FOBexC (B+4) (FOSucc cr)
    (FOAnd (FOGENF (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr len
              (FOVar B))
    (FOAnd (FOPROVAT (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len
              c (FOVar B) (FOVar (B+2)))
    (FOAnd (FOPROVAT (B+76) ct dt c1 d1 c2 d2 c3 d3 cr dr len
              c (FOVar (B+2)) (FOVar (B+4)))
           (FOPATF (B+122) [FOVar (B+2); FOVar (B+4)]
              cpatImpl01 d)))))).

Definition FODMONc (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (c c' : nat) (d : FOTerm) : FOFormula :=
  FOBexC B (FOSucc c1)
  (FOBexC (B+2) (FOSucc cr)
  (FOBexC (B+4) (FOSucc cr)
    (FOAnd (FOGENF (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr len
              (FOVar B))
    (FOAnd (FOPROVAT (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len
              c (FOVar B) (FOVar (B+2)))
    (FOAnd (FOPROVAT (B+76) ct dt c1 d1 c2 d2 c3 d3 cr dr len
              c' (FOVar B) (FOVar (B+4)))
           (FOPATF (B+122) [FOVar (B+2); FOVar (B+4)]
              cpatImpl01 d)))))).

Fixpoint FOD2Sc (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (cores : list nat) (d : FOTerm) : FOFormula :=
  match cores with
  | [] => FOFalseF
  | c :: rest =>
      FOOr (FOD2c B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d)
           (FOD2Sc B ct dt c1 d1 c2 d2 c3 d3 cr dr len rest d)
  end.

Fixpoint FOD3Sc (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (cores : list nat) (d : FOTerm) : FOFormula :=
  match cores with
  | [] => FOFalseF
  | c :: rest =>
      FOOr (FOD3c B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d)
           (FOD3Sc B ct dt c1 d1 c2 d2 c3 d3 cr dr len rest d)
  end.

Fixpoint FODMONS1 (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (c : nat) (cs : list nat) (d : FOTerm) : FOFormula :=
  match cs with
  | [] => FOFalseF
  | c' :: rest =>
      FOOr (FODMONc B ct dt c1 d1 c2 d2 c3 d3 cr dr len c c' d)
           (FODMONS1 B ct dt c1 d1 c2 d2 c3 d3 cr dr len c rest d)
  end.

Fixpoint FODMONSc (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (cores : list nat) (d : FOTerm) : FOFormula :=
  match cores with
  | [] => FOFalseF
  | c :: rest =>
      FOOr (FODMONS1 B ct dt c1 d1 c2 d2 c3 d3 cr dr len
              c (c :: rest) d)
           (FODMONSc B ct dt c1 d1 c2 d2 c3 d3 cr dr len rest d)
  end.

Definition FOJUSTCK (B : nat) (cores : list nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (cs ds cj dj : FOTerm) (i : FOTerm) : FOFormula :=
  FOBexC B (FOSucc cs)
  (FOBexC (B+2) (FOSucc cj)
    (FOAnd (FObetaF (B+4) cs ds i (FOVar B))
    (FOAnd (FObetaF (B+8) cj dj i (FOVar (B+2)))
    (FOBexC (B+12) (FOSucc (FOVar (B+2)))
    (FOBexC (B+14) (FOSucc (FOVar (B+2)))
      (FOAnd (FOcpairF (FOVar (B+12)) (FOVar (B+14)) (FOVar (B+2)))
        (FOOr
           (FOAnd (FOEq (FOVar (B+12)) FOZero)
              (FOTHAXc (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len
                 cores (FOVar B)))
        (FOOr
           (FOAnd (FOEq (FOVar (B+12)) (FOnumeral 1))
              (FOLOGc (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len
                 (FOVar B)))
        (FOOr
           (FOAnd (FOEq (FOVar (B+12)) (FOnumeral 2))
              (FOJSUBST (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len
                 cpatAllElim (FOVar B) (FOVar (B+14))))
        (FOOr
           (FOAnd (FOEq (FOVar (B+12)) (FOnumeral 3))
              (FOJSUBST (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len
                 cpatExIntro (FOVar B) (FOVar (B+14))))
        (FOOr
           (FOAnd (FOEq (FOVar (B+12)) (FOnumeral 4))
              (FOJMP (B+16) cs ds (FOVar B) (FOVar (B+14)) i))
        (FOOr
           (FOAnd (FOEq (FOVar (B+12)) (FOnumeral 5))
              (FOJGEN (B+16) cs ds (FOVar B) (FOVar (B+14)) i))
        (FOOr
           (FOAnd (FOEq (FOVar (B+12)) (FOnumeral 6))
              (FOJLOEB (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len
                 cs ds (FOVar B) (FOVar (B+14)) i))
        (FOOr
           (FOAnd (FOEq (FOVar (B+12)) (FOnumeral 7))
              (FOD2Sc (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len
                 cores (FOVar B)))
        (FOOr
           (FOAnd (FOEq (FOVar (B+12)) (FOnumeral 8))
              (FOD3Sc (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len
                 cores (FOVar B)))
        (FOOr
           (FOAnd (FOEq (FOVar (B+12)) (FOnumeral 9))
              (FODMONSc (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len
                 cores (FOVar B)))
           (FOAnd (FOEq (FOVar (B+12)) (FOnumeral 10))
              (FOJIND (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len
                 (FOVar B) (FOVar (B+14)))))))))))))))))))).

(** Entry-code guard at one derivation position [i]: some table row
    substitutes at variable [S vd] inside the entry code [vd] off the
    formula track.  Every payload inside [vd] is at most [vd], so the
    substitution variable shadows no binder and the row's existence
    forces [vd] to be a genuine formula code. *)

Definition FOGUARDC (B : nat)
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (cs ds : FOTerm) (i : FOTerm) : FOFormula :=
  FOBexC B (FOSucc cs)
    (FOAnd (FObetaF (B+2) cs ds i (FOVar B))
       (FOBexC (B+6) (FOSucc cr)
          (FOlookup (B+8) ct dt c1 d1 c2 d2 c3 d3 cr dr len
             (FOnumeral 3) (FOSucc (FOVar B)) FOZero (FOVar B)
             (FOVar (B+6))))).

(** The Delta_0 derivation checker: a valid master table, a final
    track entry equal to the target code [f] (variable 1), a
    justified entry at every position, and the entry-code guard at
    every position.  Free variables: 0 the template
    code [u], 1 the target [f]; variables 2 through 17 are the table
    codes, the two derivation tracks, and the length, bound by the
    Sigma_1 prefix in [FOPRMAT]. *)

Definition FOPRDER (cores : list nat) : FOFormula :=
  FOAnd
    (FOTBLVALID 18 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
       (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12))
  (FOAnd
    (FOBexC 18 (FOVar 17)
       (FOAnd (FOEq (FOVar 17) (FOSucc (FOVar 18)))
              (FObetaF 20 (FOVar 13) (FOVar 14) (FOVar 18) (FOVar 1))))
  (FOAnd
    (FOBallC 18 (FOVar 17)
       (FOJUSTCK 20 cores
          (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6) (FOVar 7)
          (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
          (FOVar 13) (FOVar 14) (FOVar 15) (FOVar 16) (FOVar 18)))
    (FOBallC 18 (FOVar 17)
       (FOGUARDC 20
          (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6) (FOVar 7)
          (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
          (FOVar 13) (FOVar 14) (FOVar 18))))).

Definition FOPRMAT (cores : list nat) : FOFormula :=
  FOExists 2 (FOExists 3 (FOExists 4 (FOExists 5 (FOExists 6
  (FOExists 7 (FOExists 8 (FOExists 9 (FOExists 10 (FOExists 11
  (FOExists 12 (FOExists 13 (FOExists 14 (FOExists 15 (FOExists 16
  (FOExists 17 (FOPRDER cores)))))))))))))))).

(** The level tower of provability templates.  [FOPrCores n] lists,
    for each [k < n], the code of the level-[k] template with its own
    code already substituted for variable 0 — the self-applied core
    whose remaining free variable 1 receives a target formula code.
    The level-[n] provability sentence substitutes the level-[n]
    template code at variable 0 and the target code at variable 1. *)

Fixpoint FOPrCores (n : nat) : list nat :=
  match n with
  | 0 => []
  | S k =>
      FOPrCores k ++
      [FOcode_f (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores k)))
                   (FOPRMAT (FOPrCores k)))]
  end.

Definition FOProvSentence (n : nat) (A : FOFormula) : FOFormula :=
  FOsubst_num 1 (FOcode_f A)
    (FOsubst_num 0 (FOcode_f (FOPRMAT (FOPrCores n)))
       (FOPRMAT (FOPrCores n))).

Definition FOTopFm : FOFormula := FOImplF FOFalseF FOFalseF.

(** The consistency sentence of level [n]: the level-[n] provability
    sentence does not prove the negation of the propositional truth.
    The tower axioms are local reflection: for every [k] below the
    level and every formula [A], if [T_k] proves [A] then [A].  The
    consistency sentence is the reflection instance at [FONeg FOTopFm]
    composed with the derivability of [FOTopFm]. *)

Definition FOConSentence (n : nat) : FOFormula :=
  FONeg (FOProvSentence n (FONeg FOTopFm)).

(** Term-level substitution with its capture test.  [FOin_tm v t]:
    [v] occurs in [t].  [FOfree_in v A]: [v] occurs free in [A].
    [FOsubst_f x s A] replaces free [x] by [s], stopping under a binder
    of [x].  [FOsubst_ok x s A]: [s] is free for [x] in [A], so the
    substitution is capture-free. *)

Fixpoint FOin_tm (v : nat) (t : FOTerm) : bool :=
  match t with
  | FOVar y => Nat.eqb y v
  | FOZero => false
  | FOSucc a => FOin_tm v a
  | FOPlus a b => FOin_tm v a || FOin_tm v b
  | FOMult a b => FOin_tm v a || FOin_tm v b
  end.

Fixpoint FOfree_in (v : nat) (A : FOFormula) : bool :=
  match A with
  | FOEq a b => FOin_tm v a || FOin_tm v b
  | FOFalseF => false
  | FOImplF B C => FOfree_in v B || FOfree_in v C
  | FOForall y B => if Nat.eqb y v then false else FOfree_in v B
  | FOExists y B => if Nat.eqb y v then false else FOfree_in v B
  end.

Fixpoint FOsubst_t (x : nat) (s : FOTerm) (t : FOTerm) : FOTerm :=
  match t with
  | FOVar y => if Nat.eqb y x then s else FOVar y
  | FOZero => FOZero
  | FOSucc a => FOSucc (FOsubst_t x s a)
  | FOPlus a b => FOPlus (FOsubst_t x s a) (FOsubst_t x s b)
  | FOMult a b => FOMult (FOsubst_t x s a) (FOsubst_t x s b)
  end.

Fixpoint FOsubst_f (x : nat) (s : FOTerm) (A : FOFormula) : FOFormula :=
  match A with
  | FOEq a b => FOEq (FOsubst_t x s a) (FOsubst_t x s b)
  | FOFalseF => FOFalseF
  | FOImplF B C => FOImplF (FOsubst_f x s B) (FOsubst_f x s C)
  | FOForall y B =>
      if Nat.eqb y x then FOForall y B else FOForall y (FOsubst_f x s B)
  | FOExists y B =>
      if Nat.eqb y x then FOExists y B else FOExists y (FOsubst_f x s B)
  end.

Fixpoint FOsubst_ok (x : nat) (s : FOTerm) (A : FOFormula) : bool :=
  match A with
  | FOEq _ _ => true
  | FOFalseF => true
  | FOImplF B C => FOsubst_ok x s B && FOsubst_ok x s C
  | FOForall y B =>
      if Nat.eqb y x then true
      else if FOfree_in x B
           then negb (FOin_tm y s) && FOsubst_ok x s B
           else true
  | FOExists y B =>
      if Nat.eqb y x then true
      else if FOfree_in x B
           then negb (FOin_tm y s) && FOsubst_ok x s B
           else true
  end.

(** ** The first-order induction schema (PA base).

    [FOInduction x A] is the curried base/step/conclusion form

      A[x:=0] -> (forall x, A -> A[x:=S x]) -> forall x, A,

    placed here, after the substitution toolkit and before [FOAxiomTn],
    so the tower's induction axiom can refer to it.  Its standard-model
    soundness [FOInduction_sat] is proved later, once [FOsat] and the
    substitution lemma are available. *)

Definition FOInduction (x : nat) (A : FOFormula) : FOFormula :=
  FOImplF (FOsubst_f x FOZero A)
    (FOImplF (FOForall x (FOImplF A (FOsubst_f x (FOSucc (FOVar x)) A)))
       (FOForall x A)).

Lemma FOsubst_ok_succ_var_self : forall A x,
  FOsubst_ok x (FOSucc (FOVar x)) A = true.
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB]; intros x; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite IHB, IHC. reflexivity.
  - destruct (Nat.eqb_spec y x) as [E|E]; [reflexivity|].
    destruct (FOfree_in x B); [|reflexivity].
    cbn. destruct (Nat.eqb_spec x y) as [E2|E2].
    + exfalso. apply E. symmetry. exact E2.
    + cbn. exact (IHB x).
  - destruct (Nat.eqb_spec y x) as [E|E]; [reflexivity|].
    destruct (FOfree_in x B); [|reflexivity].
    cbn. destruct (Nat.eqb_spec x y) as [E2|E2].
    + exfalso. apply E. symmetry. exact E2.
    + cbn. exact (IHB x).
Qed.

Inductive FOAxiomTn : nat -> FOFormula -> Prop :=
  | FOAx_RQ : forall n phi, FORobinsonQ phi -> FOAxiomTn n phi
  | FOAx_Refl : forall n k A, k < n ->
      FOAxiomTn n (FOImplF (FOProvSentence k A) A)
  | FOAx_D2 : forall n k A B, k < n ->
      FOAxiomTn n
        (FOImplF (FOProvSentence k (FOImplF A B))
           (FOImplF (FOProvSentence k A) (FOProvSentence k B)))
  | FOAx_D3 : forall n k A, k < n ->
      FOAxiomTn n
        (FOImplF (FOProvSentence k A)
           (FOProvSentence k (FOProvSentence k A)))
  | FOAx_DMon : forall n k k' A, k <= k' -> k' < n ->
      FOAxiomTn n
        (FOImplF (FOProvSentence k A) (FOProvSentence k' A))
  | FOAx_Ind : forall n x A, FOAxiomTn n (FOInduction x A).

(** ** Boolean equality and Goedel codes for the first-order syntax. *)

Fixpoint FOterm_eqb (a b : FOTerm) : bool :=
  match a, b with
  | FOVar x, FOVar y => Nat.eqb x y
  | FOZero, FOZero => true
  | FOSucc a', FOSucc b' => FOterm_eqb a' b'
  | FOPlus a1 a2, FOPlus b1 b2 => FOterm_eqb a1 b1 && FOterm_eqb a2 b2
  | FOMult a1 a2, FOMult b1 b2 => FOterm_eqb a1 b1 && FOterm_eqb a2 b2
  | _, _ => false
  end.

Lemma FOterm_eqb_eq : forall a b, FOterm_eqb a b = true <-> a = b.
Proof.
  induction a as [x | | a IH | a1 IH1 a2 IH2 | a1 IH1 a2 IH2];
    destruct b as [y | | b' | b1 b2 | b1 b2]; cbn;
    try (split; intro HH; discriminate HH).
  - rewrite Nat.eqb_eq. split.
    + intro e. rewrite e. reflexivity.
    + intro e. injection e. intro e'. exact e'.
  - split; intro; reflexivity.
  - rewrite IH. split.
    + intro e. rewrite e. reflexivity.
    + intro e. injection e. intro e'. exact e'.
  - rewrite Bool.andb_true_iff, IH1, IH2. split.
    + intros [e1 e2]. rewrite e1, e2. reflexivity.
    + intro e. injection e. intros e2 e1. split; assumption.
  - rewrite Bool.andb_true_iff, IH1, IH2. split.
    + intros [e1 e2]. rewrite e1, e2. reflexivity.
    + intro e. injection e. intros e2 e1. split; assumption.
Qed.

Fixpoint FOform_eqb (A B : FOFormula) : bool :=
  match A, B with
  | FOEq a1 a2, FOEq b1 b2 => FOterm_eqb a1 b1 && FOterm_eqb a2 b2
  | FOFalseF, FOFalseF => true
  | FOImplF A1 A2, FOImplF B1 B2 => FOform_eqb A1 B1 && FOform_eqb A2 B2
  | FOForall x A', FOForall y B' => Nat.eqb x y && FOform_eqb A' B'
  | FOExists x A', FOExists y B' => Nat.eqb x y && FOform_eqb A' B'
  | _, _ => false
  end.

Lemma FOform_eqb_eq : forall A B, FOform_eqb A B = true <-> A = B.
Proof.
  induction A as [a1 a2 | | A1 IH1 A2 IH2 | x A' IH | x A' IH];
    destruct B as [b1 b2 | | B1 B2 | y B' | y B']; cbn;
    try (split; intro HH; discriminate HH).
  - rewrite Bool.andb_true_iff, !FOterm_eqb_eq. split.
    + intros [e1 e2]. rewrite e1, e2. reflexivity.
    + intro e. injection e. intros e2 e1. split; assumption.
  - split; intro; reflexivity.
  - rewrite Bool.andb_true_iff, IH1, IH2. split.
    + intros [e1 e2]. rewrite e1, e2. reflexivity.
    + intro e. injection e. intros e2 e1. split; assumption.
  - rewrite Bool.andb_true_iff, Nat.eqb_eq, IH. split.
    + intros [e1 e2]. rewrite e1, e2. reflexivity.
    + intro e. injection e. intros e2 e1. split; assumption.
  - rewrite Bool.andb_true_iff, Nat.eqb_eq, IH. split.
    + intros [e1 e2]. rewrite e1, e2. reflexivity.
    + intro e. injection e. intros e2 e1. split; assumption.
Qed.

Fixpoint FOdecode_tm_b (depth n : nat) : FOTerm :=
  match depth with
  | 0 => FOZero
  | S d =>
    match fst (cunpair n) with
    | 0 => FOVar (snd (cunpair n))
    | 1 => FOZero
    | 2 => FOSucc (FOdecode_tm_b d (snd (cunpair n)))
    | 3 => FOPlus (FOdecode_tm_b d (fst (cunpair (snd (cunpair n)))))
                  (FOdecode_tm_b d (snd (cunpair (snd (cunpair n)))))
    | 4 => FOMult (FOdecode_tm_b d (fst (cunpair (snd (cunpair n)))))
                  (FOdecode_tm_b d (snd (cunpair (snd (cunpair n)))))
    | _ => FOZero
    end
  end.

Definition FOdecode_tm (n : nat) : FOTerm := FOdecode_tm_b (S n) n.

Lemma FOcode_tm_succ_lt : forall a, FOcode_tm a < FOcode_tm (FOSucc a).
Proof.
  intro a. cbn [FOcode_tm].
  pose proof (cpair_bound 2 (FOcode_tm a)). lia.
Qed.

Lemma FOcode_tm_plus_lt_l : forall a b,
  FOcode_tm a < FOcode_tm (FOPlus a b).
Proof.
  intros a b. cbn [FOcode_tm].
  pose proof (cpair_bound 3 (cpair (FOcode_tm a) (FOcode_tm b))).
  pose proof (cpair_bound (FOcode_tm a) (FOcode_tm b)). lia.
Qed.

Lemma FOcode_tm_plus_lt_r : forall a b,
  FOcode_tm b < FOcode_tm (FOPlus a b).
Proof.
  intros a b. cbn [FOcode_tm].
  pose proof (cpair_bound 3 (cpair (FOcode_tm a) (FOcode_tm b))).
  pose proof (cpair_bound (FOcode_tm a) (FOcode_tm b)). lia.
Qed.

Lemma FOcode_tm_mult_lt_l : forall a b,
  FOcode_tm a < FOcode_tm (FOMult a b).
Proof.
  intros a b. cbn [FOcode_tm].
  pose proof (cpair_bound 4 (cpair (FOcode_tm a) (FOcode_tm b))).
  pose proof (cpair_bound (FOcode_tm a) (FOcode_tm b)). lia.
Qed.

Lemma FOcode_tm_mult_lt_r : forall a b,
  FOcode_tm b < FOcode_tm (FOMult a b).
Proof.
  intros a b. cbn [FOcode_tm].
  pose proof (cpair_bound 4 (cpair (FOcode_tm a) (FOcode_tm b))).
  pose proof (cpair_bound (FOcode_tm a) (FOcode_tm b)). lia.
Qed.

Lemma FOdecode_tm_b_code : forall t d,
  FOcode_tm t < d -> FOdecode_tm_b d (FOcode_tm t) = t.
Proof.
  induction t as [x | | a IH | a IHa b IHb | a IHa b IHb];
    intros d Hd; destruct d as [|d]; try lia; cbn [FOdecode_tm_b].
  - cbn [FOcode_tm]. rewrite cunpair_cpair. reflexivity.
  - cbn [FOcode_tm]. rewrite cunpair_cpair. reflexivity.
  - pose proof (FOcode_tm_succ_lt a) as Hlt.
    cbn [FOcode_tm] in Hlt, Hd.
    cbn [FOcode_tm]. rewrite cunpair_cpair. cbn [fst snd].
    rewrite IH; [reflexivity | lia].
  - pose proof (FOcode_tm_plus_lt_l a b) as Hla.
    pose proof (FOcode_tm_plus_lt_r a b) as Hlb.
    cbn [FOcode_tm] in Hla, Hlb, Hd.
    cbn [FOcode_tm]. rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite IHa; [rewrite IHb; [reflexivity|]|]; lia.
  - pose proof (FOcode_tm_mult_lt_l a b) as Hla.
    pose proof (FOcode_tm_mult_lt_r a b) as Hlb.
    cbn [FOcode_tm] in Hla, Hlb, Hd.
    cbn [FOcode_tm]. rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite IHa; [rewrite IHb; [reflexivity|]|]; lia.
Qed.

Lemma FOdecode_code_tm : forall t, FOdecode_tm (FOcode_tm t) = t.
Proof.
  intro t. unfold FOdecode_tm. apply FOdecode_tm_b_code. lia.
Qed.

Lemma FOcode_tm_inj : forall a b, FOcode_tm a = FOcode_tm b -> a = b.
Proof.
  intros a b H.
  rewrite <- (FOdecode_code_tm a), <- (FOdecode_code_tm b), H.
  reflexivity.
Qed.

Fixpoint FOdecode_f_b (depth n : nat) : FOFormula :=
  match depth with
  | 0 => FOFalseF
  | S d =>
    match fst (cunpair n) with
    | 0 => FOEq (FOdecode_tm (fst (cunpair (snd (cunpair n)))))
                (FOdecode_tm (snd (cunpair (snd (cunpair n)))))
    | 1 => FOFalseF
    | 2 => FOImplF (FOdecode_f_b d (fst (cunpair (snd (cunpair n)))))
                   (FOdecode_f_b d (snd (cunpair (snd (cunpair n)))))
    | 3 => FOForall (fst (cunpair (snd (cunpair n))))
                    (FOdecode_f_b d (snd (cunpair (snd (cunpair n)))))
    | 4 => FOExists (fst (cunpair (snd (cunpair n))))
                    (FOdecode_f_b d (snd (cunpair (snd (cunpair n)))))
    | _ => FOFalseF
    end
  end.

Definition FOdecode_f (n : nat) : FOFormula := FOdecode_f_b (S n) n.

Lemma FOcode_f_impl_lt_l : forall B C,
  FOcode_f B < FOcode_f (FOImplF B C).
Proof.
  intros B C. cbn [FOcode_f].
  pose proof (cpair_bound 2 (cpair (FOcode_f B) (FOcode_f C))).
  pose proof (cpair_bound (FOcode_f B) (FOcode_f C)). lia.
Qed.

Lemma FOcode_f_impl_lt_r : forall B C,
  FOcode_f C < FOcode_f (FOImplF B C).
Proof.
  intros B C. cbn [FOcode_f].
  pose proof (cpair_bound 2 (cpair (FOcode_f B) (FOcode_f C))).
  pose proof (cpair_bound (FOcode_f B) (FOcode_f C)). lia.
Qed.

Lemma FOcode_f_forall_lt : forall x B,
  FOcode_f B < FOcode_f (FOForall x B).
Proof.
  intros x B. cbn [FOcode_f].
  pose proof (cpair_bound 3 (cpair x (FOcode_f B))).
  pose proof (cpair_bound x (FOcode_f B)). lia.
Qed.

Lemma FOcode_f_exists_lt : forall x B,
  FOcode_f B < FOcode_f (FOExists x B).
Proof.
  intros x B. cbn [FOcode_f].
  pose proof (cpair_bound 4 (cpair x (FOcode_f B))).
  pose proof (cpair_bound x (FOcode_f B)). lia.
Qed.

Lemma FOdecode_f_b_code : forall A d,
  FOcode_f A < d -> FOdecode_f_b d (FOcode_f A) = A.
Proof.
  induction A as [a b | | B IHB C IHC | x B IHB | x B IHB];
    intros d Hd; destruct d as [|d]; try lia; cbn [FOdecode_f_b].
  - cbn [FOcode_f]. rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite !FOdecode_code_tm. reflexivity.
  - cbn [FOcode_f]. rewrite cunpair_cpair. reflexivity.
  - pose proof (FOcode_f_impl_lt_l B C) as HlB.
    pose proof (FOcode_f_impl_lt_r B C) as HlC.
    cbn [FOcode_f] in HlB, HlC, Hd.
    cbn [FOcode_f]. rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite IHB; [rewrite IHC; [reflexivity|]|]; lia.
  - pose proof (FOcode_f_forall_lt x B) as HlB.
    cbn [FOcode_f] in HlB, Hd.
    cbn [FOcode_f]. rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite IHB; [reflexivity | lia].
  - pose proof (FOcode_f_exists_lt x B) as HlB.
    cbn [FOcode_f] in HlB, Hd.
    cbn [FOcode_f]. rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite IHB; [reflexivity | lia].
Qed.

Lemma FOdecode_code_f : forall A, FOdecode_f (FOcode_f A) = A.
Proof.
  intro A. unfold FOdecode_f. apply FOdecode_f_b_code. lia.
Qed.

Lemma FOcode_f_inj : forall A B, FOcode_f A = FOcode_f B -> A = B.
Proof.
  intros A B H.
  rewrite <- (FOdecode_code_f A), <- (FOdecode_code_f B), H.
  reflexivity.
Qed.

(** ** The Goedel beta function, complete for finite sequences by the
    Chinese remainder construction with factorial moduli. *)

Definition beta (c d i : nat) : nat := c mod (d * S i + 1).

Lemma fact_ge : forall n, n <= fact n.
Proof.
  induction n as [|n IH].
  - cbn. lia.
  - cbn [fact]. pose proof (lt_O_fact n). nia.
Qed.

Lemma fact_divide : forall k n, 1 <= k -> k <= n -> Nat.divide k (fact n).
Proof.
  intros k n Hk. induction n as [|n IH]; intro Hkn.
  - lia.
  - destruct (Nat.eq_dec k (S n)) as [->|Hne].
    + cbn [fact]. apply Nat.divide_factor_l.
    + cbn [fact]. apply Nat.divide_mul_r. apply IH. lia.
Qed.

Fixpoint mprod (m : nat -> nat) (k : nat) : nat :=
  match k with
  | 0 => 1
  | S k' => mprod m k' * m k'
  end.

Lemma mprod_divide : forall m k i, i < k -> Nat.divide (m i) (mprod m k).
Proof.
  intros m k. induction k as [|k IH]; intros i Hik.
  - lia.
  - cbn. destruct (Nat.eq_dec i k) as [->|Hne].
    + apply Nat.divide_factor_r.
    + apply Nat.divide_mul_l. apply IH. lia.
Qed.

Lemma coprime_mul_l_pre : forall a b p,
  Nat.gcd a p = 1 -> Nat.gcd b p = 1 -> Nat.gcd (a * b) p = 1.
Proof.
  intros a b p Ha Hb.
  apply Nat.divide_1_r.
  rewrite <- Hb.
  apply Nat.gcd_greatest.
  - apply (Nat.gauss _ a).
    + exact (Nat.gcd_divide_l (a * b) p).
    + apply Nat.divide_1_r.
      rewrite <- Ha.
      apply Nat.gcd_greatest.
      * apply Nat.gcd_divide_r.
      * eapply Nat.divide_trans.
        -- apply Nat.gcd_divide_l.
        -- apply Nat.gcd_divide_r.
  - apply Nat.gcd_divide_r.
Qed.

Lemma coprime_mprod : forall m k p,
  (forall i, i < k -> Nat.gcd (m i) p = 1) ->
  Nat.gcd (mprod m k) p = 1.
Proof.
  intros m k p H. induction k as [|k IH].
  - cbn. reflexivity.
  - cbn. apply coprime_mul_l_pre.
    + apply IH. intros i Hi. apply H. lia.
    + apply H. lia.
Qed.

Lemma crt_step : forall P m, 0 < m -> Nat.gcd P m = 1 ->
  forall x0 a, exists t, (x0 + P * t) mod m = a mod m.
Proof.
  intros P m Hm Hg x0 a.
  destruct (Nat.eq_dec m 1) as [->|Hm1].
  { exists 0. rewrite !Nat.mod_1_r. reflexivity. }
  assert (HB : exists u v, u * P = 1 + v * m).
  { destruct (Nat.gcd_bezout P m) as [HBz|HBz]; rewrite Hg in HBz;
      destruct HBz as [u [v Huv]].
    - exists u, v. exact Huv.
    - destruct m as [|w]; [lia|].
      assert (Hw1 : 1 <= w) by lia.
      assert (Hu1 : 1 <= u) by nia.
      exists (v * w), (u * w - 1).
      assert (EvP : v * P = u * S w - 1) by lia.
      assert (E1 : v * w * P = w * (v * P)) by nia.
      rewrite E1, EvP.
      assert (Huw : 1 <= u * w) by nia.
      nia. }
  destruct HB as [u [v HuP]].
  set (s := a + (m - x0 mod m)).
  exists (u * s).
  assert (E1 : x0 + P * (u * s) = x0 + s + v * s * m) by nia.
  rewrite E1.
  rewrite Nat.Div0.mod_add.
  pose proof (Nat.div_mod_eq x0 m) as Hdm.
  pose proof (Nat.mod_upper_bound x0 m ltac:(lia)) as Hub.
  assert (E2 : x0 + s = a + (S (x0 / m)) * m) by (unfold s; nia).
  rewrite E2.
  rewrite Nat.Div0.mod_add.
  reflexivity.
Qed.

Lemma crt_chain : forall (a m : nat -> nat) (len : nat),
  (forall i j, i < j -> j < len -> Nat.gcd (m i) (m j) = 1) ->
  (forall i, i < len -> 0 < m i) ->
  exists c, forall i, i < len -> c mod m i = a i mod m i.
Proof.
  intros a m len. induction len as [|len IH]; intros Hcop Hpos.
  - exists 0. intros i Hi. lia.
  - assert (Hcop' : forall i j, i < j -> j < len -> Nat.gcd (m i) (m j) = 1)
      by (intros; apply Hcop; lia).
    assert (Hpos' : forall i, i < len -> 0 < m i)
      by (intros; apply Hpos; lia).
    destruct (IH Hcop' Hpos') as [c0 Hc0].
    assert (HgP : Nat.gcd (mprod m len) (m len) = 1).
    { apply coprime_mprod. intros i Hi. apply Hcop; lia. }
    destruct (crt_step (mprod m len) (m len)
                (Hpos len (Nat.lt_succ_diag_r len)) HgP c0 (a len))
      as [t Ht].
    exists (c0 + mprod m len * t).
    intros i Hi.
    destruct (Nat.eq_dec i len) as [->|Hne].
    + exact Ht.
    + assert (Hil : i < len) by lia.
      destruct (mprod_divide m len i Hil) as [q Hq].
      rewrite Hq.
      replace (c0 + q * m i * t) with (c0 + (q * t) * m i) by nia.
      rewrite Nat.Div0.mod_add.
      exact (Hc0 i Hil).
Qed.

Lemma fold_max_base : forall l b, b <= fold_right Nat.max b l.
Proof.
  induction l as [|x l IH]; intro b; cbn.
  - lia.
  - pose proof (IH b). lia.
Qed.

Lemma fold_max_in : forall l b x, In x l -> x <= fold_right Nat.max b l.
Proof.
  induction l as [|y l IH]; intros b x Hin; cbn.
  - destruct Hin.
  - destruct Hin as [->|Hin]; [lia|]. pose proof (IH b x Hin). lia.
Qed.

Theorem beta_complete : forall l : list nat,
  exists c d, forall i, i < length l -> beta c d i = nth i l 0.
Proof.
  intro l.
  set (N := fold_right Nat.max (length l) l).
  assert (HNlen : length l <= N) by apply fold_max_base.
  assert (HNin : forall i, i < length l -> nth i l 0 <= N).
  { intros i Hi. apply fold_max_in. apply nth_In. exact Hi. }
  set (d := fact N).
  assert (HdN : N <= d) by apply fact_ge.
  assert (Hdpos : 0 < d) by apply lt_O_fact.
  destruct (crt_chain (fun i => nth i l 0) (fun i => d * S i + 1)
              (length l)) as [c Hc].
  - intros i j Hij Hj.
    set (g := Nat.gcd (d * S i + 1) (d * S j + 1)).
    assert (Hgi : Nat.divide g (d * S i + 1)) by apply Nat.gcd_divide_l.
    assert (Hgj : Nat.divide g (d * S j + 1)) by apply Nat.gcd_divide_r.
    assert (Hgd : Nat.divide g (d * (j - i))).
    { replace (d * (j - i)) with ((d * S j + 1) - (d * S i + 1)) by nia.
      apply Nat.divide_sub_r; assumption. }
    assert (Hgd1 : Nat.gcd g d = 1).
    { apply Nat.divide_1_r.
      replace 1 with ((d * S i + 1) - d * S i) by lia.
      apply Nat.divide_sub_r.
      - eapply Nat.divide_trans; [apply Nat.gcd_divide_l | exact Hgi].
      - apply Nat.divide_mul_l. apply Nat.gcd_divide_r. }
    assert (Hgji : Nat.divide g (j - i)).
    { apply (Nat.gauss g d (j - i)); [exact Hgd | exact Hgd1]. }
    assert (Hjid : Nat.divide (j - i) d).
    { unfold d. apply fact_divide; lia. }
    apply Nat.divide_1_r.
    replace 1 with ((d * S i + 1) - d * S i) by lia.
    apply Nat.divide_sub_r.
    + exact Hgi.
    + apply Nat.divide_mul_l.
      eapply Nat.divide_trans; [exact Hgji | exact Hjid].
  - intros i Hi. lia.
  - exists c, d. intros i Hi.
    unfold beta. rewrite (Hc i Hi).
    apply Nat.mod_small.
    pose proof (HNin i Hi). lia.
Qed.

(** The defining Diophantine characterization of [beta]: this is the
    shape the arithmetized access formula mirrors. *)

Lemma beta_spec : forall c d i x,
  beta c d i = x
  <-> (exists q, c = q * (d * S i + 1) + x /\ x < d * S i + 1).
Proof.
  intros c d i x. unfold beta. split.
  - intro H. exists (c / (d * S i + 1)). split.
    + pose proof (Nat.div_mod_eq c (d * S i + 1)). nia.
    + rewrite <- H. apply Nat.mod_upper_bound. lia.
  - intros [q [Hc Hx]]. subst c.
    rewrite Nat.add_comm, Nat.Div0.mod_add.
    apply Nat.mod_small. exact Hx.
Qed.

(** ** Shape recognizers for the rules of the T_n calculus.

    Each premise-free rule conclusion is recognized by a boolean test
    on the formula; quantifier instantiation carries its variable and
    term as certificates.  Derivations are then checkable sequences of
    (formula, justification) entries, parametric in the theory-axiom
    test and the provability-sentence former. *)

Fixpoint FOnum_of_tm (t : FOTerm) : option nat :=
  match t with
  | FOZero => Some 0
  | FOSucc a =>
      match FOnum_of_tm a with
      | Some k => Some (S k)
      | None => None
      end
  | _ => None
  end.

Lemma FOnum_of_tm_numeral : forall k, FOnum_of_tm (FOnumeral k) = Some k.
Proof.
  induction k as [|k IH]; cbn; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma FOnum_of_tm_correct : forall t k,
  FOnum_of_tm t = Some k -> t = FOnumeral k.
Proof.
  induction t as [x | | a IH | |]; intros k H; cbn in H;
    try discriminate.
  - injection H. intro e. rewrite <- e. reflexivity.
  - destruct (FOnum_of_tm a) as [m|] eqn:E; [|discriminate].
    injection H. intro e. rewrite <- e. cbn.
    rewrite (IH m eq_refl). reflexivity.
Qed.

Definition FOis_RQ (A : FOFormula) : bool :=
  match A with
  | FOImplF (FOEq (FOSucc a) (FOSucc b)) (FOEq a' b') =>
      FOterm_eqb a a' && FOterm_eqb b b'
  | FOImplF (FOEq (FOSucc a) FOZero) FOFalseF => true
  | FOImplF (FOImplF (FOEq (FOVar x) FOZero) FOFalseF)
            (FOExists w (FOEq (FOVar x') (FOSucc (FOVar w')))) =>
      Nat.eqb x x' && Nat.eqb w (S x) && Nat.eqb w' (S x)
  | FOEq (FOPlus a FOZero) a' => FOterm_eqb a a'
  | FOEq (FOPlus a (FOSucc b)) (FOSucc (FOPlus a' b')) =>
      FOterm_eqb a a' && FOterm_eqb b b'
  | FOEq (FOMult a FOZero) FOZero => true
  | FOEq (FOMult a (FOSucc b)) (FOPlus (FOMult a' b') a'') =>
      FOterm_eqb a a' && FOterm_eqb b b' && FOterm_eqb a a''
  | _ => false
  end.

Definition FOis_K (A : FOFormula) : bool :=
  match A with
  | FOImplF P (FOImplF _ P') => FOform_eqb P P'
  | _ => false
  end.

Definition FOis_S (A : FOFormula) : bool :=
  match A with
  | FOImplF (FOImplF P (FOImplF Q R))
            (FOImplF (FOImplF P' Q') (FOImplF P'' R')) =>
      FOform_eqb P P' && FOform_eqb P P'' && FOform_eqb Q Q'
        && FOform_eqb R R'
  | _ => false
  end.

Definition FOis_DN (A : FOFormula) : bool :=
  match A with
  | FOImplF (FOImplF (FOImplF P FOFalseF) FOFalseF) P' => FOform_eqb P P'
  | _ => false
  end.

Definition FOis_EqRefl (A : FOFormula) : bool :=
  match A with
  | FOEq a a' => FOterm_eqb a a'
  | _ => false
  end.

Definition FOis_EqSym (A : FOFormula) : bool :=
  match A with
  | FOImplF (FOEq a b) (FOEq b' a') => FOterm_eqb a a' && FOterm_eqb b b'
  | _ => false
  end.

Definition FOis_EqTrans (A : FOFormula) : bool :=
  match A with
  | FOImplF (FOEq a b) (FOImplF (FOEq b' c) (FOEq a' c')) =>
      FOterm_eqb a a' && FOterm_eqb b b' && FOterm_eqb c c'
  | _ => false
  end.

Definition FOis_CongS (A : FOFormula) : bool :=
  match A with
  | FOImplF (FOEq a b) (FOEq (FOSucc a') (FOSucc b')) =>
      FOterm_eqb a a' && FOterm_eqb b b'
  | _ => false
  end.

Definition FOis_CongPlus (A : FOFormula) : bool :=
  match A with
  | FOImplF (FOEq a b)
            (FOImplF (FOEq c d) (FOEq (FOPlus a' c') (FOPlus b' d'))) =>
      FOterm_eqb a a' && FOterm_eqb b b' && FOterm_eqb c c'
        && FOterm_eqb d d'
  | _ => false
  end.

Definition FOis_CongMult (A : FOFormula) : bool :=
  match A with
  | FOImplF (FOEq a b)
            (FOImplF (FOEq c d) (FOEq (FOMult a' c') (FOMult b' d'))) =>
      FOterm_eqb a a' && FOterm_eqb b b' && FOterm_eqb c c'
        && FOterm_eqb d d'
  | _ => false
  end.

Definition FOis_ExElim (A : FOFormula) : bool :=
  match A with
  | FOImplF (FOForall x (FOImplF P Q)) (FOImplF (FOExists x' P') Q') =>
      Nat.eqb x x' && FOform_eqb P P' && FOform_eqb Q Q'
        && negb (FOfree_in x Q)
  | _ => false
  end.

Definition FOis_AllK (A : FOFormula) : bool :=
  match A with
  | FOImplF (FOForall y (FOImplF P Q))
            (FOImplF (FOForall y' P') (FOForall y'' Q')) =>
      Nat.eqb y y' && Nat.eqb y y'' && FOform_eqb P P' && FOform_eqb Q Q'
  | _ => false
  end.

Definition FOis_AllExport (A : FOFormula) : bool :=
  match A with
  | FOImplF (FOForall y (FOImplF H R))
            (FOImplF H' (FOForall y' R')) =>
      Nat.eqb y y' && FOform_eqb H H' && FOform_eqb R R'
        && negb (FOfree_in y H)
  | _ => false
  end.

Definition FOis_AllElim (x : nat) (t : FOTerm) (A : FOFormula) : bool :=
  match A with
  | FOImplF (FOForall x' P) Q =>
      Nat.eqb x x' && FOsubst_ok x t P && FOform_eqb Q (FOsubst_f x t P)
  | _ => false
  end.

Definition FOis_ExIntro (x : nat) (t : FOTerm) (A : FOFormula) : bool :=
  match A with
  | FOImplF Q (FOExists x' P) =>
      Nat.eqb x x' && FOsubst_ok x t P && FOform_eqb Q (FOsubst_f x t P)
  | _ => false
  end.

Definition FOis_logical_axiom (A : FOFormula) : bool :=
  FOis_K A || FOis_S A || FOis_DN A || FOis_EqRefl A || FOis_EqSym A
  || FOis_EqTrans A || FOis_CongS A || FOis_CongPlus A || FOis_CongMult A
  || FOis_ExElim A || FOis_AllK A || FOis_AllExport A.

Inductive FOjust : Type :=
  | J_thax : FOjust
  | J_log : FOjust
  | J_AllElim : nat -> FOTerm -> FOjust
  | J_ExIntro : nat -> FOTerm -> FOjust
  | J_MP : nat -> nat -> FOjust
  | J_Gen : nat -> FOjust
  | J_Loeb : nat -> FOjust
  | J_d2 : nat -> FOFormula -> FOFormula -> FOjust
  | J_d3 : nat -> FOFormula -> FOjust
  | J_dmon : nat -> nat -> FOFormula -> FOjust
  | J_ind : nat -> FOFormula -> FOjust.

Definition FOentry_check (axb : FOFormula -> bool)
    (PrF : FOFormula -> FOFormula) (maxk : nat)
    (prev : list FOFormula) (A : FOFormula) (j : FOjust) : bool :=
  match j with
  | J_thax => axb A
  | J_log => FOis_logical_axiom A
  | J_AllElim x t => FOis_AllElim x t A
  | J_ExIntro x t => FOis_ExIntro x t A
  | J_MP i j' =>
      match nth_error prev i, nth_error prev j' with
      | Some AB, Some B => FOform_eqb AB (FOImplF B A)
      | _, _ => false
      end
  | J_Gen i =>
      match A with
      | FOForall _ B =>
          match nth_error prev i with
          | Some B' => FOform_eqb B B'
          | None => false
          end
      | _ => false
      end
  | J_Loeb i =>
      match nth_error prev i with
      | Some P => FOform_eqb P (FOImplF (PrF A) A)
      | None => false
      end
  | J_d2 k X Y =>
      (k <? maxk) &&
      FOform_eqb A (FOImplF (FOProvSentence k (FOImplF X Y))
                      (FOImplF (FOProvSentence k X)
                         (FOProvSentence k Y)))
  | J_d3 k X =>
      (k <? maxk) &&
      FOform_eqb A (FOImplF (FOProvSentence k X)
                      (FOProvSentence k (FOProvSentence k X)))
  | J_dmon k k' X =>
      (k <=? k') && (k' <? maxk) &&
      FOform_eqb A (FOImplF (FOProvSentence k X)
                      (FOProvSentence k' X))
  | J_ind x X => FOform_eqb A (FOInduction x X)
  end.

Fixpoint FOseq_check (axb : FOFormula -> bool)
    (PrF : FOFormula -> FOFormula) (maxk : nat)
    (done : list FOFormula)
    (rest : list (FOFormula * FOjust)) : bool :=
  match rest with
  | [] => true
  | (A, j) :: rest' =>
      FOentry_check axb PrF maxk done A j
        && FOseq_check axb PrF maxk (done ++ [A]) rest'
  end.

Inductive FOProvesTn (n : nat) : FOFormula -> Prop :=
  | FOProvesTn_ax : forall phi, FOAxiomTn n phi -> FOProvesTn n phi
  | FOProvesTn_K : forall phi psi, FOProvesTn n (FOImplF phi (FOImplF psi phi))
  | FOProvesTn_S : forall phi psi chi,
      FOProvesTn n (FOImplF (FOImplF phi (FOImplF psi chi))
                            (FOImplF (FOImplF phi psi) (FOImplF phi chi)))
  | FOProvesTn_DN : forall phi,
      FOProvesTn n (FOImplF (FONeg (FONeg phi)) phi)
  | FOProvesTn_MP : forall phi psi,
      FOProvesTn n (FOImplF phi psi) -> FOProvesTn n phi -> FOProvesTn n psi
  | FOProvesTn_Gen : forall x phi,
      FOProvesTn n phi -> FOProvesTn n (FOForall x phi)
  | FOProvesTn_EqRefl : forall t, FOProvesTn n (FOEq t t)
  | FOProvesTn_EqSym : forall a b,
      FOProvesTn n (FOImplF (FOEq a b) (FOEq b a))
  | FOProvesTn_EqTrans : forall a b c,
      FOProvesTn n (FOImplF (FOEq a b) (FOImplF (FOEq b c) (FOEq a c)))
  | FOProvesTn_CongS : forall a b,
      FOProvesTn n (FOImplF (FOEq a b) (FOEq (FOSucc a) (FOSucc b)))
  | FOProvesTn_CongPlus : forall a b c d,
      FOProvesTn n (FOImplF (FOEq a b)
                      (FOImplF (FOEq c d) (FOEq (FOPlus a c) (FOPlus b d))))
  | FOProvesTn_CongMult : forall a b c d,
      FOProvesTn n (FOImplF (FOEq a b)
                      (FOImplF (FOEq c d) (FOEq (FOMult a c) (FOMult b d))))
  | FOProvesTn_AllElimT : forall x t phi,
      FOsubst_ok x t phi = true ->
      FOProvesTn n (FOImplF (FOForall x phi) (FOsubst_f x t phi))
  | FOProvesTn_ExIntroT : forall x t phi,
      FOsubst_ok x t phi = true ->
      FOProvesTn n (FOImplF (FOsubst_f x t phi) (FOExists x phi))
  | FOProvesTn_ExElim : forall x phi psi,
      FOfree_in x psi = false ->
      FOProvesTn n (FOImplF (FOForall x (FOImplF phi psi))
                            (FOImplF (FOExists x phi) psi))
  | FOProvesTn_AllK : forall y P Q,
      FOProvesTn n (FOImplF (FOForall y (FOImplF P Q))
                            (FOImplF (FOForall y P) (FOForall y Q)))
  | FOProvesTn_AllExport : forall y H R,
      FOfree_in y H = false ->
      FOProvesTn n (FOImplF (FOForall y (FOImplF H R))
                            (FOImplF H (FOForall y R)))
  | FOProvesTn_Loeb : forall phi,
      FOProvesTn n (FOImplF (FOProvSentence n phi) phi) ->
      FOProvesTn n phi.

Theorem FOAxiomTn_cumulative : forall n phi,
  FOAxiomTn n phi -> FOAxiomTn (S n) phi.
Proof.
  intros n phi H. inversion H.
  - apply FOAx_RQ. exact H0.
  - apply FOAx_Refl. lia.
  - apply FOAx_D2. lia.
  - apply FOAx_D3. lia.
  - apply FOAx_DMon; lia.
  - apply FOAx_Ind.
Qed.

Theorem FOAxiomTn_cumulative_chain : forall n m phi,
  n <= m -> FOAxiomTn n phi -> FOAxiomTn m phi.
Proof.
  intros n m phi Hnm Hax.
  induction Hnm as [|m' Hnm IH].
  - exact Hax.
  - exact (FOAxiomTn_cumulative m' phi IH).
Qed.

(** Cumulativity of [FOProvesTn] is proved after the representability
    bridge: lifting a Loeb-rule step from level [n] to level [S n]
    goes through the truth of the level-[n] provability sentence and
    Sigma_1 completeness against the level-[S n] reflection axiom. *)

(** Numerals are variable-free, so numeral substitution is always
    capture-free; the numeral rules are instances of the term rules. *)

Lemma FOin_tm_numeral : forall y k, FOin_tm y (FOnumeral k) = false.
Proof.
  intros y k. induction k as [|k IH]; cbn; [reflexivity | exact IH].
Qed.

Lemma FOsubst_ok_numeral : forall A x k,
  FOsubst_ok x (FOnumeral k) A = true.
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB];
    intros x k; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite IHB, IHC. reflexivity.
  - destruct (Nat.eqb y x); [reflexivity|].
    destruct (FOfree_in x B); [|reflexivity].
    rewrite FOin_tm_numeral, IHB. reflexivity.
  - destruct (Nat.eqb y x); [reflexivity|].
    destruct (FOfree_in x B); [|reflexivity].
    rewrite FOin_tm_numeral, IHB. reflexivity.
Qed.

Lemma FOsubst_t_num : forall t x k,
  FOsubst_t x (FOnumeral k) t = FOsubst_tm x k t.
Proof.
  induction t; intros x k; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma FOsubst_f_num : forall A x k,
  FOsubst_f x (FOnumeral k) A = FOsubst_num x k A.
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB];
    intros x k; cbn.
  - rewrite !FOsubst_t_num. reflexivity.
  - reflexivity.
  - rewrite IHB, IHC. reflexivity.
  - destruct (Nat.eqb y x); [reflexivity | rewrite IHB; reflexivity].
  - destruct (Nat.eqb y x); [reflexivity | rewrite IHB; reflexivity].
Qed.

Lemma FOsubst_t_id : forall t x, FOsubst_t x (FOVar x) t = t.
Proof.
  induction t; intros x; cbn.
  - destruct (Nat.eqb_spec n x) as [E|E]; [subst n; reflexivity | reflexivity].
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma FOsubst_f_id : forall A x, FOsubst_f x (FOVar x) A = A.
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB]; intros x; cbn.
  - rewrite !FOsubst_t_id. reflexivity.
  - reflexivity.
  - rewrite IHB, IHC. reflexivity.
  - destruct (Nat.eqb y x); [reflexivity | rewrite IHB; reflexivity].
  - destruct (Nat.eqb y x); [reflexivity | rewrite IHB; reflexivity].
Qed.

Lemma FOsubst_ok_var_self : forall A x, FOsubst_ok x (FOVar x) A = true.
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB]; intros x; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite IHB, IHC. reflexivity.
  - destruct (Nat.eqb_spec y x) as [E|E]; [reflexivity|].
    destruct (FOfree_in x B); [|reflexivity].
    cbn. destruct (Nat.eqb_spec x y) as [E2|E2].
    + exfalso. apply E. symmetry. exact E2.
    + cbn. exact (IHB x).
  - destruct (Nat.eqb_spec y x) as [E|E]; [reflexivity|].
    destruct (FOfree_in x B); [|reflexivity].
    cbn. destruct (Nat.eqb_spec x y) as [E2|E2].
    + exfalso. apply E. symmetry. exact E2.
    + cbn. exact (IHB x).
Qed.

Lemma FOProvesTn_AllElimNum : forall n x k phi,
  FOProvesTn n (FOImplF (FOForall x phi) (FOsubst_num x k phi)).
Proof.
  intros n x k phi.
  rewrite <- (FOsubst_f_num phi x k).
  exact (FOProvesTn_AllElimT n x (FOnumeral k) phi
           (FOsubst_ok_numeral phi x k)).
Qed.

Lemma FOProvesTn_ExIntroNum : forall n x k phi,
  FOProvesTn n (FOImplF (FOsubst_num x k phi) (FOExists x phi)).
Proof.
  intros n x k phi.
  rewrite <- (FOsubst_f_num phi x k).
  exact (FOProvesTn_ExIntroT n x (FOnumeral k) phi
           (FOsubst_ok_numeral phi x k)).
Qed.

Lemma FOProvesTn_AllNegToNegEx : forall n x phi,
  FOProvesTn n (FOImplF (FOForall x (FONeg phi)) (FONeg (FOExists x phi))).
Proof.
  intros n x phi.
  exact (FOProvesTn_ExElim n x phi FOFalseF eq_refl).
Qed.

(** ** The shape recognizers are sound and complete for their rules. *)

Lemma FOterm_eqb_refl : forall a, FOterm_eqb a a = true.
Proof. intro a. apply FOterm_eqb_eq. reflexivity. Qed.

Lemma FOform_eqb_refl : forall A, FOform_eqb A A = true.
Proof. intro A. apply FOform_eqb_eq. reflexivity. Qed.

Lemma FOis_RQ_complete : forall A, FORobinsonQ A -> FOis_RQ A = true.
Proof.
  intros A H. destruct H as [a b | a | x | a | a b | a | a b]; cbn.
  - rewrite !FOterm_eqb_refl. reflexivity.
  - reflexivity.
  - rewrite !Nat.eqb_refl. reflexivity.
  - rewrite FOterm_eqb_refl. reflexivity.
  - rewrite !FOterm_eqb_refl. reflexivity.
  - reflexivity.
  - rewrite !FOterm_eqb_refl. reflexivity.
Qed.

Lemma FOis_RQ_sound : forall A, FOis_RQ A = true -> FORobinsonQ A.
Proof.
  intros A H.
  destruct A as [t1 t2 | | L R | x B | x B]; try discriminate.
  - destruct t1 as [x | | a | a u | a u]; try discriminate.
    + destruct u as [y | | b | u1 u2 | u1 u2]; try discriminate.
      * cbn in H. apply FOterm_eqb_eq in H. subst t2.
        apply RQ_plus_zero.
      * destruct t2 as [y | | s | s1 s2 | s1 s2]; try discriminate.
        destruct s as [y | | | a' b' | s1 s2]; try discriminate.
        cbn in H.
        apply Bool.andb_true_iff in H. destruct H as [H1 H2].
        apply FOterm_eqb_eq in H1, H2. subst a' b'.
        apply RQ_plus_succ.
    + destruct u as [y | | b | u1 u2 | u1 u2]; try discriminate.
      * destruct t2 as [y | | s | s1 s2 | s1 s2]; try discriminate.
        apply RQ_mult_zero.
      * destruct t2 as [y | | s | m a'' | s1 s2]; try discriminate.
        destruct m as [y | | s | s1 s2 | a' b']; try discriminate.
        cbn in H.
        apply Bool.andb_true_iff in H. destruct H as [H H3].
        apply Bool.andb_true_iff in H. destruct H as [H1 H2].
        apply FOterm_eqb_eq in H1, H2, H3. subst a' b' a''.
        apply RQ_mult_succ.
  - destruct L as [l1 l2 | | L1 L2 | y B | y B]; try discriminate.
    + destruct l1 as [y | | a | u1 u2 | u1 u2]; try discriminate.
      destruct l2 as [y | | b | u1 u2 | u1 u2]; try discriminate.
      * destruct R as [a' b' | | R1 R2 | y B | y B]; try discriminate.
        exact (RQ_S_nonzero a).
      * destruct R as [a' b' | | R1 R2 | y B | y B]; try discriminate.
        cbn in H.
        apply Bool.andb_true_iff in H. destruct H as [H1 H2].
        apply FOterm_eqb_eq in H1, H2. subst a' b'.
        apply RQ_S_inj.
    + destruct L1 as [a z | | M1 M2 | y B | y B]; try discriminate.
      destruct a as [x | | s | u1 u2 | u1 u2]; try discriminate.
      destruct z as [y | | s | u1 u2 | u1 u2]; try discriminate.
      destruct L2 as [u1 u2 | | M1 M2 | y B | y B]; try discriminate.
      destruct R as [u1 u2 | | R1 R2 | y B | w RB]; try discriminate.
      destruct RB as [a' su | | R1 R2 | y B | y B]; try discriminate.
      destruct a' as [x' | | s | u1 u2 | u1 u2]; try discriminate.
      destruct su as [y | | sv | u1 u2 | u1 u2]; try discriminate.
      destruct sv as [w' | | s | u1 u2 | u1 u2]; try discriminate.
      cbn in H.
      apply Bool.andb_true_iff in H. destruct H as [H Hw'].
      apply Bool.andb_true_iff in H. destruct H as [Hx Hw].
      apply Nat.eqb_eq in Hx, Hw, Hw'.
      subst x' w w'.
      exact (RQ_zero_or_succ x).
Qed.

Lemma FOis_K_sound : forall n A, FOis_K A = true -> FOProvesTn n A.
Proof.
  intros n A H.
  destruct A as [a b | | P R | x B | x B]; try discriminate.
  destruct R as [a b | | Q P' | x B | x B]; try discriminate.
  cbn in H. apply FOform_eqb_eq in H. subst P'.
  apply FOProvesTn_K.
Qed.

Lemma FOis_K_complete : forall P Q,
  FOis_K (FOImplF P (FOImplF Q P)) = true.
Proof. intros P Q. cbn. apply FOform_eqb_refl. Qed.

Lemma FOis_S_sound : forall n A, FOis_S A = true -> FOProvesTn n A.
Proof.
  intros n A H.
  destruct A as [a b | | L R | x B | x B]; try discriminate.
  destruct L as [a b | | P QR | x B | x B]; try discriminate.
  destruct QR as [a b | | Q R0 | x B | x B]; try discriminate.
  destruct R as [a b | | PQ PR | x B | x B]; try discriminate.
  destruct PQ as [a b | | P' Q' | x B | x B]; try discriminate.
  destruct PR as [a b | | P'' R' | x B | x B]; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H H4].
  apply Bool.andb_true_iff in H. destruct H as [H H3].
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply FOform_eqb_eq in H1, H2, H3, H4.
  subst. apply FOProvesTn_S.
Qed.

Lemma FOis_S_complete : forall P Q R,
  FOis_S (FOImplF (FOImplF P (FOImplF Q R))
                  (FOImplF (FOImplF P Q) (FOImplF P R))) = true.
Proof. intros. cbn. rewrite !FOform_eqb_refl. reflexivity. Qed.

Lemma FOis_DN_sound : forall n A, FOis_DN A = true -> FOProvesTn n A.
Proof.
  intros n A H.
  destruct A as [a b | | L P' | x B | x B]; try discriminate.
  destruct L as [a b | | M F1 | x B | x B]; try discriminate.
  destruct M as [a b | | P F2 | x B | x B]; try discriminate.
  destruct F2 as [a b | | M1 M2 | x B | x B]; try discriminate.
  destruct F1 as [a b | | M1 M2 | x B | x B]; try discriminate.
  cbn in H. apply FOform_eqb_eq in H. subst P'.
  apply FOProvesTn_DN.
Qed.

Lemma FOis_DN_complete : forall P,
  FOis_DN (FOImplF (FONeg (FONeg P)) P) = true.
Proof. intro P. cbn. apply FOform_eqb_refl. Qed.

Lemma FOis_EqRefl_sound : forall n A,
  FOis_EqRefl A = true -> FOProvesTn n A.
Proof.
  intros n A H.
  destruct A as [a a' | | B C | x B | x B]; try discriminate.
  cbn in H. apply FOterm_eqb_eq in H. subst a'.
  apply FOProvesTn_EqRefl.
Qed.

Lemma FOis_EqRefl_complete : forall t, FOis_EqRefl (FOEq t t) = true.
Proof. intro t. cbn. apply FOterm_eqb_refl. Qed.

Lemma FOis_EqSym_sound : forall n A,
  FOis_EqSym A = true -> FOProvesTn n A.
Proof.
  intros n A H.
  destruct A as [a b | | L R | x B | x B]; try discriminate.
  destruct L as [a b | | B C | x B | x B]; try discriminate.
  destruct R as [b' a' | | B C | x B | x B]; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply FOterm_eqb_eq in H1, H2. subst a' b'.
  apply FOProvesTn_EqSym.
Qed.

Lemma FOis_EqSym_complete : forall a b,
  FOis_EqSym (FOImplF (FOEq a b) (FOEq b a)) = true.
Proof. intros a b. cbn. rewrite !FOterm_eqb_refl. reflexivity. Qed.

Lemma FOis_EqTrans_sound : forall n A,
  FOis_EqTrans A = true -> FOProvesTn n A.
Proof.
  intros n A H.
  destruct A as [a b | | L R | x B | x B]; try discriminate.
  destruct L as [a b | | B C | x B | x B]; try discriminate.
  destruct R as [u1 u2 | | M N | y1 D1 | y2 D2]; try discriminate.
  destruct M as [b' c | | B2 C2 | y3 D3 | y4 D4]; try discriminate.
  destruct N as [a' c' | | B3 C3 | y5 D5 | y6 D6]; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H H3].
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply FOterm_eqb_eq in H1, H2, H3. subst a' b' c'.
  apply FOProvesTn_EqTrans.
Qed.

Lemma FOis_EqTrans_complete : forall a b c,
  FOis_EqTrans (FOImplF (FOEq a b) (FOImplF (FOEq b c) (FOEq a c)))
  = true.
Proof. intros. cbn. rewrite !FOterm_eqb_refl. reflexivity. Qed.

Lemma FOis_CongS_sound : forall n A,
  FOis_CongS A = true -> FOProvesTn n A.
Proof.
  intros n A H.
  destruct A as [a b | | L R | x B | x B]; try discriminate.
  destruct L as [a b | | B C | x B | x B]; try discriminate.
  destruct R as [sa sb | | B2 C2 | y1 D1 | y2 D2]; try discriminate.
  destruct sa as [z1 | | a' | u1 u2 | u3 u4]; try discriminate.
  destruct sb as [z2 | | b' | u5 u6 | u7 u8]; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply FOterm_eqb_eq in H1, H2. subst a' b'.
  apply FOProvesTn_CongS.
Qed.

Lemma FOis_CongS_complete : forall a b,
  FOis_CongS (FOImplF (FOEq a b) (FOEq (FOSucc a) (FOSucc b))) = true.
Proof. intros. cbn. rewrite !FOterm_eqb_refl. reflexivity. Qed.

Lemma FOis_CongPlus_sound : forall n A,
  FOis_CongPlus A = true -> FOProvesTn n A.
Proof.
  intros n A H.
  destruct A as [a b | | L R | x B | x B]; try discriminate.
  destruct L as [a b | | B C | x B | x B]; try discriminate.
  destruct R as [u1 u2 | | M N | y1 D1 | y2 D2]; try discriminate.
  destruct M as [c d | | B2 C2 | y3 D3 | y4 D4]; try discriminate.
  destruct N as [pa pb | | B3 C3 | y5 D5 | y6 D6]; try discriminate.
  destruct pa as [z1 | | s1 | a' c' | u3 u4]; try discriminate.
  destruct pb as [z2 | | s2 | b' d' | u5 u6]; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H H4].
  apply Bool.andb_true_iff in H. destruct H as [H H3].
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply FOterm_eqb_eq in H1, H2, H3, H4. subst a' b' c' d'.
  apply FOProvesTn_CongPlus.
Qed.

Lemma FOis_CongPlus_complete : forall a b c d,
  FOis_CongPlus (FOImplF (FOEq a b)
    (FOImplF (FOEq c d) (FOEq (FOPlus a c) (FOPlus b d)))) = true.
Proof. intros. cbn. rewrite !FOterm_eqb_refl. reflexivity. Qed.

Lemma FOis_CongMult_sound : forall n A,
  FOis_CongMult A = true -> FOProvesTn n A.
Proof.
  intros n A H.
  destruct A as [a b | | L R | x B | x B]; try discriminate.
  destruct L as [a b | | B C | x B | x B]; try discriminate.
  destruct R as [u1 u2 | | M N | y1 D1 | y2 D2]; try discriminate.
  destruct M as [c d | | B2 C2 | y3 D3 | y4 D4]; try discriminate.
  destruct N as [pa pb | | B3 C3 | y5 D5 | y6 D6]; try discriminate.
  destruct pa as [z1 | | s1 | u3 u4 | a' c']; try discriminate.
  destruct pb as [z2 | | s2 | u5 u6 | b' d']; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H H4].
  apply Bool.andb_true_iff in H. destruct H as [H H3].
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply FOterm_eqb_eq in H1, H2, H3, H4. subst a' b' c' d'.
  apply FOProvesTn_CongMult.
Qed.

Lemma FOis_CongMult_complete : forall a b c d,
  FOis_CongMult (FOImplF (FOEq a b)
    (FOImplF (FOEq c d) (FOEq (FOMult a c) (FOMult b d)))) = true.
Proof. intros. cbn. rewrite !FOterm_eqb_refl. reflexivity. Qed.

Lemma FOis_ExElim_sound : forall n A,
  FOis_ExElim A = true -> FOProvesTn n A.
Proof.
  intros n A H.
  destruct A as [a b | | L R | x B | x B]; try discriminate.
  destruct L as [a b | | B C | x B | x B]; try discriminate.
  destruct B as [a b | | P Q | y C | y C]; try discriminate.
  destruct R as [a b | | EX Q' | y C | y C]; try discriminate.
  destruct EX as [a b | | B C | y C | x' P']; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H Hf].
  apply Bool.andb_true_iff in H. destruct H as [H HQ].
  apply Bool.andb_true_iff in H. destruct H as [Hx HP].
  apply Nat.eqb_eq in Hx. apply FOform_eqb_eq in HP, HQ.
  apply Bool.negb_true_iff in Hf.
  subst. apply FOProvesTn_ExElim. exact Hf.
Qed.

Lemma FOis_ExElim_complete : forall x P Q,
  FOfree_in x Q = false ->
  FOis_ExElim (FOImplF (FOForall x (FOImplF P Q))
                       (FOImplF (FOExists x P) Q)) = true.
Proof.
  intros x P Q Hf. cbn.
  rewrite Nat.eqb_refl, !FOform_eqb_refl, Hf. reflexivity.
Qed.

Lemma FOis_AllK_sound : forall n A,
  FOis_AllK A = true -> FOProvesTn n A.
Proof.
  intros n A H.
  destruct A as [a b | | L R | x B | x B]; try discriminate.
  destruct L as [a b | | B C | y B | x B]; try discriminate.
  destruct B as [a b | | P Q | z C | z C]; try discriminate.
  destruct R as [a b | | FP FQ | z C | z C]; try discriminate.
  destruct FP as [a b | | B C | y' P' | z C]; try discriminate.
  destruct FQ as [a b | | B C | y'' Q' | z C]; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H H4].
  apply Bool.andb_true_iff in H. destruct H as [H H3].
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply Nat.eqb_eq in H1, H2. apply FOform_eqb_eq in H3, H4.
  subst. apply FOProvesTn_AllK.
Qed.

Lemma FOis_AllK_complete : forall y P Q,
  FOis_AllK (FOImplF (FOForall y (FOImplF P Q))
                     (FOImplF (FOForall y P) (FOForall y Q))) = true.
Proof.
  intros. cbn. rewrite !Nat.eqb_refl, !FOform_eqb_refl. reflexivity.
Qed.

Lemma FOis_AllExport_sound : forall n A,
  FOis_AllExport A = true -> FOProvesTn n A.
Proof.
  intros n A H.
  destruct A as [a b | | L R | x B | x B]; try discriminate.
  destruct L as [a b | | B C | y B | x B]; try discriminate.
  destruct B as [a b | | Hh Rr | z C | z C]; try discriminate.
  destruct R as [a b | | H' FR | z C | z C]; try discriminate.
  destruct FR as [a b | | B C | y' R' | z C]; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H Hf].
  apply Bool.andb_true_iff in H. destruct H as [H H3].
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply Nat.eqb_eq in H1. apply FOform_eqb_eq in H2, H3.
  apply Bool.negb_true_iff in Hf.
  subst. apply FOProvesTn_AllExport. exact Hf.
Qed.

Lemma FOis_AllExport_complete : forall y Hh R,
  FOfree_in y Hh = false ->
  FOis_AllExport (FOImplF (FOForall y (FOImplF Hh R))
                          (FOImplF Hh (FOForall y R))) = true.
Proof.
  intros y Hh R Hf. cbn.
  rewrite Nat.eqb_refl, !FOform_eqb_refl, Hf. reflexivity.
Qed.

Lemma FOis_AllElim_sound : forall n x t A,
  FOis_AllElim x t A = true -> FOProvesTn n A.
Proof.
  intros n x t A H.
  destruct A as [a b | | L Q | y B | y B]; try discriminate.
  destruct L as [a b | | B C | x' P | y B]; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H HQ].
  apply Bool.andb_true_iff in H. destruct H as [Hx Hok].
  apply Nat.eqb_eq in Hx. apply FOform_eqb_eq in HQ.
  subst x' Q.
  apply FOProvesTn_AllElimT. exact Hok.
Qed.

Lemma FOis_AllElim_complete : forall x t P,
  FOsubst_ok x t P = true ->
  FOis_AllElim x t (FOImplF (FOForall x P) (FOsubst_f x t P)) = true.
Proof.
  intros x t P Hok. cbn.
  rewrite Nat.eqb_refl, Hok, FOform_eqb_refl. reflexivity.
Qed.

Lemma FOis_ExIntro_sound : forall n x t A,
  FOis_ExIntro x t A = true -> FOProvesTn n A.
Proof.
  intros n x t A H.
  destruct A as [a b | | Q R | y B | y B]; try discriminate.
  destruct R as [a b | | B C | y B | x' P]; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H HQ].
  apply Bool.andb_true_iff in H. destruct H as [Hx Hok].
  apply Nat.eqb_eq in Hx. apply FOform_eqb_eq in HQ.
  subst x' Q.
  apply FOProvesTn_ExIntroT. exact Hok.
Qed.

Lemma FOis_ExIntro_complete : forall x t P,
  FOsubst_ok x t P = true ->
  FOis_ExIntro x t (FOImplF (FOsubst_f x t P) (FOExists x P)) = true.
Proof.
  intros x t P Hok. cbn.
  rewrite Nat.eqb_refl, Hok, FOform_eqb_refl. reflexivity.
Qed.

Lemma FOis_logical_axiom_sound : forall n A,
  FOis_logical_axiom A = true -> FOProvesTn n A.
Proof.
  intros n A H. unfold FOis_logical_axiom in H.
  repeat (apply Bool.orb_true_iff in H; destruct H as [H|H]).
  - exact (FOis_K_sound n A H).
  - exact (FOis_S_sound n A H).
  - exact (FOis_DN_sound n A H).
  - exact (FOis_EqRefl_sound n A H).
  - exact (FOis_EqSym_sound n A H).
  - exact (FOis_EqTrans_sound n A H).
  - exact (FOis_CongS_sound n A H).
  - exact (FOis_CongPlus_sound n A H).
  - exact (FOis_CongMult_sound n A H).
  - exact (FOis_ExElim_sound n A H).
  - exact (FOis_AllK_sound n A H).
  - exact (FOis_AllExport_sound n A H).
Qed.

Lemma FOis_logical_axiom_of : forall A,
  (FOis_K A = true) \/ (FOis_S A = true) \/ (FOis_DN A = true)
  \/ (FOis_EqRefl A = true) \/ (FOis_EqSym A = true)
  \/ (FOis_EqTrans A = true) \/ (FOis_CongS A = true)
  \/ (FOis_CongPlus A = true) \/ (FOis_CongMult A = true)
  \/ (FOis_ExElim A = true) \/ (FOis_AllK A = true)
  \/ (FOis_AllExport A = true) ->
  FOis_logical_axiom A = true.
Proof.
  intros A H. unfold FOis_logical_axiom.
  repeat destruct H as [H|H]; rewrite H;
    repeat (rewrite Bool.orb_true_l || rewrite Bool.orb_true_r);
    reflexivity.
Qed.

(** ** Shape extraction for the logical-axiom recognizers.

    Each recognizer's acceptance pins the formula to its axiom
    template; the encode direction reads the template back out. *)

Lemma FOis_K_shape : forall A, FOis_K A = true ->
  exists P Q, A = FOImplF P (FOImplF Q P).
Proof.
  intros A H.
  destruct A as [a b | | P R | x B | x B]; try discriminate.
  destruct R as [a b | | Q P' | x B | x B]; try discriminate.
  cbn in H. apply FOform_eqb_eq in H. subst P'.
  exists P, Q. reflexivity.
Qed.

Lemma FOis_S_shape : forall A, FOis_S A = true ->
  exists P Q R, A = FOImplF (FOImplF P (FOImplF Q R))
                      (FOImplF (FOImplF P Q) (FOImplF P R)).
Proof.
  intros A H.
  destruct A as [a b | | L R | x B | x B]; try discriminate.
  destruct L as [a b | | P QR | x B | x B]; try discriminate.
  destruct QR as [a b | | Q R0 | x B | x B]; try discriminate.
  destruct R as [a b | | PQ PR | x B | x B]; try discriminate.
  destruct PQ as [a b | | P' Q' | x B | x B]; try discriminate.
  destruct PR as [a b | | P'' R' | x B | x B]; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H H4].
  apply Bool.andb_true_iff in H. destruct H as [H H3].
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply FOform_eqb_eq in H1, H2, H3, H4.
  subst. do 3 eexists. reflexivity.
Qed.

Lemma FOis_DN_shape : forall A, FOis_DN A = true ->
  exists P, A = FOImplF (FOImplF (FOImplF P FOFalseF) FOFalseF) P.
Proof.
  intros A H.
  destruct A as [a b | | L P' | x B | x B]; try discriminate.
  destruct L as [a b | | M F1 | x B | x B]; try discriminate.
  destruct M as [a b | | P F2 | x B | x B]; try discriminate.
  destruct F2 as [a b | | M1 M2 | x B | x B]; try discriminate.
  destruct F1 as [a b | | M1 M2 | x B | x B]; try discriminate.
  cbn in H. apply FOform_eqb_eq in H. subst P'.
  exists P. reflexivity.
Qed.

Lemma FOis_EqRefl_shape : forall A, FOis_EqRefl A = true ->
  exists t, A = FOEq t t.
Proof.
  intros A H.
  destruct A as [a a' | | B C | x B | x B]; try discriminate.
  cbn in H. apply FOterm_eqb_eq in H. subst a'.
  exists a. reflexivity.
Qed.

Lemma FOis_EqSym_shape : forall A, FOis_EqSym A = true ->
  exists a b, A = FOImplF (FOEq a b) (FOEq b a).
Proof.
  intros A H.
  destruct A as [a b | | L R | x B | x B]; try discriminate.
  destruct L as [a b | | B C | x B | x B]; try discriminate.
  destruct R as [b' a' | | B C | x B | x B]; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply FOterm_eqb_eq in H1, H2. subst a' b'.
  exists a, b. reflexivity.
Qed.

Lemma FOis_EqTrans_shape : forall A, FOis_EqTrans A = true ->
  exists a b c,
    A = FOImplF (FOEq a b) (FOImplF (FOEq b c) (FOEq a c)).
Proof.
  intros A H.
  destruct A as [a b | | L R | x B | x B]; try discriminate.
  destruct L as [a b | | B C | x B | x B]; try discriminate.
  destruct R as [u1 u2 | | M N | y1 D1 | y2 D2]; try discriminate.
  destruct M as [b' c | | B2 C2 | y3 D3 | y4 D4]; try discriminate.
  destruct N as [a' c' | | B3 C3 | y5 D5 | y6 D6]; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H H3].
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply FOterm_eqb_eq in H1, H2, H3. subst a' b' c'.
  exists a, b, c. reflexivity.
Qed.

Lemma FOis_CongS_shape : forall A, FOis_CongS A = true ->
  exists a b,
    A = FOImplF (FOEq a b) (FOEq (FOSucc a) (FOSucc b)).
Proof.
  intros A H.
  destruct A as [a b | | L R | x B | x B]; try discriminate.
  destruct L as [a b | | B C | x B | x B]; try discriminate.
  destruct R as [sa sb | | B2 C2 | y1 D1 | y2 D2]; try discriminate.
  destruct sa as [z1 | | a' | u1 u2 | u3 u4]; try discriminate.
  destruct sb as [z2 | | b' | u5 u6 | u7 u8]; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply FOterm_eqb_eq in H1, H2. subst a' b'.
  exists a, b. reflexivity.
Qed.

Lemma FOis_CongPlus_shape : forall A, FOis_CongPlus A = true ->
  exists a b c d,
    A = FOImplF (FOEq a b)
          (FOImplF (FOEq c d) (FOEq (FOPlus a c) (FOPlus b d))).
Proof.
  intros A H.
  destruct A as [a b | | L R | x B | x B]; try discriminate.
  destruct L as [a b | | B C | x B | x B]; try discriminate.
  destruct R as [u1 u2 | | M N | y1 D1 | y2 D2]; try discriminate.
  destruct M as [c d | | B2 C2 | y3 D3 | y4 D4]; try discriminate.
  destruct N as [pa pb | | B3 C3 | y5 D5 | y6 D6]; try discriminate.
  destruct pa as [z1 | | s1 | a' c' | u3 u4]; try discriminate.
  destruct pb as [z2 | | s2 | b' d' | u5 u6]; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H H4].
  apply Bool.andb_true_iff in H. destruct H as [H H3].
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply FOterm_eqb_eq in H1, H2, H3, H4. subst a' b' c' d'.
  exists a, b, c, d. reflexivity.
Qed.

Lemma FOis_CongMult_shape : forall A, FOis_CongMult A = true ->
  exists a b c d,
    A = FOImplF (FOEq a b)
          (FOImplF (FOEq c d) (FOEq (FOMult a c) (FOMult b d))).
Proof.
  intros A H.
  destruct A as [a b | | L R | x B | x B]; try discriminate.
  destruct L as [a b | | B C | x B | x B]; try discriminate.
  destruct R as [u1 u2 | | M N | y1 D1 | y2 D2]; try discriminate.
  destruct M as [c d | | B2 C2 | y3 D3 | y4 D4]; try discriminate.
  destruct N as [pa pb | | B3 C3 | y5 D5 | y6 D6]; try discriminate.
  destruct pa as [z1 | | s1 | u3 u4 | a' c']; try discriminate.
  destruct pb as [z2 | | s2 | u5 u6 | b' d']; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H H4].
  apply Bool.andb_true_iff in H. destruct H as [H H3].
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply FOterm_eqb_eq in H1, H2, H3, H4. subst a' b' c' d'.
  exists a, b, c, d. reflexivity.
Qed.

Lemma FOis_ExElim_shape : forall A, FOis_ExElim A = true ->
  exists x P Q,
    A = FOImplF (FOForall x (FOImplF P Q))
          (FOImplF (FOExists x P) Q)
    /\ FOfree_in x Q = false.
Proof.
  intros A H.
  destruct A as [a b | | L R | x B | x B]; try discriminate.
  destruct L as [a b | | B C | x B | x B]; try discriminate.
  destruct B as [a b | | P Q | y C | y C]; try discriminate.
  destruct R as [a b | | EX Q' | y C | y C]; try discriminate.
  destruct EX as [a b | | B C | y C | x' P']; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H Hf].
  apply Bool.andb_true_iff in H. destruct H as [H HQ].
  apply Bool.andb_true_iff in H. destruct H as [Hx HP].
  apply Nat.eqb_eq in Hx. apply FOform_eqb_eq in HP, HQ.
  apply Bool.negb_true_iff in Hf.
  subst. do 3 eexists. split; [reflexivity|exact Hf].
Qed.

Lemma FOis_AllK_shape : forall A, FOis_AllK A = true ->
  exists y P Q,
    A = FOImplF (FOForall y (FOImplF P Q))
          (FOImplF (FOForall y P) (FOForall y Q)).
Proof.
  intros A H.
  destruct A as [a b | | L R | x B | x B]; try discriminate.
  destruct L as [a b | | B C | y B | x B]; try discriminate.
  destruct B as [a b | | P Q | z C | z C]; try discriminate.
  destruct R as [a b | | FP FQ | z C | z C]; try discriminate.
  destruct FP as [a b | | B C | y' P' | z C]; try discriminate.
  destruct FQ as [a b | | B C | y'' Q' | z C]; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H H4].
  apply Bool.andb_true_iff in H. destruct H as [H H3].
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply Nat.eqb_eq in H1, H2. apply FOform_eqb_eq in H3, H4.
  subst. do 3 eexists. reflexivity.
Qed.

Lemma FOis_AllExport_shape : forall A, FOis_AllExport A = true ->
  exists y Hh R,
    A = FOImplF (FOForall y (FOImplF Hh R))
          (FOImplF Hh (FOForall y R))
    /\ FOfree_in y Hh = false.
Proof.
  intros A H.
  destruct A as [a b | | L R | x B | x B]; try discriminate.
  destruct L as [a b | | B C | y B | x B]; try discriminate.
  destruct B as [a b | | Hh Rr | z C | z C]; try discriminate.
  destruct R as [a b | | H' FR | z C | z C]; try discriminate.
  destruct FR as [a b | | B C | y' R' | z C]; try discriminate.
  cbn in H.
  apply Bool.andb_true_iff in H. destruct H as [H Hf].
  apply Bool.andb_true_iff in H. destruct H as [H H3].
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply Nat.eqb_eq in H1. apply FOform_eqb_eq in H2, H3.
  apply Bool.negb_true_iff in Hf.
  subst. do 3 eexists. split; [reflexivity|exact Hf].
Qed.

(** ** The level axiom recognizer and sequence-checker soundness.

    [FOaxb n] decides membership in [FOAxiomTn n]: a Robinson scheme
    instance or a reflection instance at some level below [n].  An
    [FOseq_check]-accepted sequence then consists of [FOProvesTn]
    theorems, by one pass with the per-shape soundness kit. *)

Definition FOreflb (n : nat) (A : FOFormula) : bool :=
  match A with
  | FOImplF P C =>
      existsb (fun k => FOform_eqb P (FOProvSentence k C)) (seq 0 n)
  | _ => false
  end.

Definition FOaxb (n : nat) (A : FOFormula) : bool :=
  FOis_RQ A || FOreflb n A.

Lemma FOaxb_sound : forall n A,
  FOaxb n A = true -> FOAxiomTn n A.
Proof.
  intros n A H. unfold FOaxb in H.
  apply Bool.orb_prop in H. destruct H as [H|H].
  - apply FOAx_RQ. exact (FOis_RQ_sound A H).
  - unfold FOreflb in H.
    destruct A as [a b | | P C | y A' | y A']; try discriminate.
    apply existsb_exists in H.
    destruct H as [k [Hin Heq]].
    apply in_seq in Hin.
    apply FOform_eqb_eq in Heq.
    subst P.
    apply FOAx_Refl. lia.
Qed.

Lemma FOaxb_complete_RQ : forall n A,
  FORobinsonQ A -> FOaxb n A = true.
Proof.
  intros n A HQ. unfold FOaxb.
  rewrite (FOis_RQ_complete A HQ). reflexivity.
Qed.

Lemma FOaxb_complete_Refl : forall n k A,
  k < n ->
  FOaxb n (FOImplF (FOProvSentence k A) A) = true.
Proof.
  intros n k A Hk. unfold FOaxb.
  apply Bool.orb_true_iff. right.
  unfold FOreflb.
  apply existsb_exists.
  exists k. split.
  - apply in_seq. lia.
  - apply FOform_eqb_refl.
Qed.

Lemma FOentry_check_sound : forall n prev A j,
  FOentry_check (FOaxb n) (FOProvSentence n) n prev A j = true ->
  (forall B, In B prev -> FOProvesTn n B) ->
  FOProvesTn n A.
Proof.
  intros n prev A j Hck Hprev.
  destruct j as [| | x t | x t | i j' | i | i | k X Y | k X | k k' X | x X];
    cbn [FOentry_check] in Hck.
  - apply FOProvesTn_ax. exact (FOaxb_sound n A Hck).
  - exact (FOis_logical_axiom_sound n A Hck).
  - exact (FOis_AllElim_sound n x t A Hck).
  - exact (FOis_ExIntro_sound n x t A Hck).
  - destruct (nth_error prev i) as [AB|] eqn:E1; [|discriminate].
    destruct (nth_error prev j') as [B|] eqn:E2; [|discriminate].
    apply FOform_eqb_eq in Hck. subst AB.
    apply (FOProvesTn_MP n B A).
    + apply Hprev. exact (nth_error_In prev i E1).
    + apply Hprev. exact (nth_error_In prev j' E2).
  - destruct A as [a b | | P C | y A' | y A']; try discriminate.
    destruct (nth_error prev i) as [B|] eqn:E1; [|discriminate].
    apply FOform_eqb_eq in Hck. subst B.
    apply FOProvesTn_Gen.
    apply Hprev. exact (nth_error_In prev i E1).
  - destruct (nth_error prev i) as [P|] eqn:E1; [|discriminate].
    apply FOform_eqb_eq in Hck. subst P.
    apply FOProvesTn_Loeb.
    apply Hprev. exact (nth_error_In prev i E1).
  - apply Bool.andb_true_iff in Hck. destruct Hck as [Hk Heq].
    apply Nat.ltb_lt in Hk.
    apply FOform_eqb_eq in Heq. subst A.
    apply FOProvesTn_ax. apply FOAx_D2. exact Hk.
  - apply Bool.andb_true_iff in Hck. destruct Hck as [Hk Heq].
    apply Nat.ltb_lt in Hk.
    apply FOform_eqb_eq in Heq. subst A.
    apply FOProvesTn_ax. apply FOAx_D3. exact Hk.
  - apply Bool.andb_true_iff in Hck. destruct Hck as [Hk Heq].
    apply Bool.andb_true_iff in Hk. destruct Hk as [Hkk Hk'].
    apply Nat.leb_le in Hkk. apply Nat.ltb_lt in Hk'.
    apply FOform_eqb_eq in Heq. subst A.
    apply FOProvesTn_ax. apply FOAx_DMon; assumption.
  - apply FOform_eqb_eq in Hck. subst A.
    apply FOProvesTn_ax. apply FOAx_Ind.
Qed.

Lemma FOseq_check_sound : forall n items done,
  FOseq_check (FOaxb n) (FOProvSentence n) n done items = true ->
  (forall B, In B done -> FOProvesTn n B) ->
  forall B, In B (map fst items) -> FOProvesTn n B.
Proof.
  intros n items.
  induction items as [|[A j] rest IH]; intros done Hck Hdone B HB.
  - destruct HB.
  - cbn [FOseq_check] in Hck.
    apply Bool.andb_true_iff in Hck.
    destruct Hck as [Hentry Hrest].
    assert (HA : FOProvesTn n A)
      by (exact (FOentry_check_sound n done A j Hentry Hdone)).
    destruct HB as [HB | HB].
    + subst B. exact HA.
    + apply (IH (done ++ [A]) Hrest); [|exact HB].
      intros C HC.
      apply in_app_or in HC.
      destruct HC as [HC | HC].
      * exact (Hdone C HC).
      * destruct HC as [HC|[]]. subst C. exact HA.
Qed.

Lemma FOProvesTn_of_seq : forall n items A,
  FOseq_check (FOaxb n) (FOProvSentence n) n [] items = true ->
  In A (map fst items) ->
  FOProvesTn n A.
Proof.
  intros n items A Hck HIn.
  apply (FOseq_check_sound n items [] Hck); [|exact HIn].
  intros B HB. destruct HB.
Qed.

(** ** Sequence-checker completeness.

    Every [FOProvesTn] derivation linearizes into an accepted
    [FOseq_check] sequence ending in its conclusion.  Justification
    indices are absolute positions in the checked prefix, so
    concatenating two sequences shifts the second sequence's indices
    by the length of the first. *)

Definition FOjshift (k : nat) (j : FOjust) : FOjust :=
  match j with
  | J_MP i j' => J_MP (k + i) (k + j')
  | J_Gen i => J_Gen (k + i)
  | J_Loeb i => J_Loeb (k + i)
  | _ => j
  end.

Fixpoint FOshift_items (k : nat)
    (items : list (FOFormula * FOjust)) : list (FOFormula * FOjust) :=
  match items with
  | [] => []
  | (A, j) :: rest => (A, FOjshift k j) :: FOshift_items k rest
  end.

Lemma FOshift_items_fst : forall k items,
  map fst (FOshift_items k items) = map fst items.
Proof.
  intros k items.
  induction items as [|[A j] rest IH]; cbn; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma nth_error_app_shift : forall (front prev : list FOFormula) i,
  nth_error (front ++ prev) (length front + i) = nth_error prev i.
Proof.
  intros front prev i.
  rewrite nth_error_app2 by lia.
  f_equal. lia.
Qed.

Lemma nth_error_last : forall (pre : list FOFormula) A,
  nth_error (pre ++ [A]) (length pre) = Some A.
Proof.
  intros pre A.
  rewrite nth_error_app2 by lia.
  rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma FOentry_check_shift : forall axb PrF maxk front prev A j,
  FOentry_check axb PrF maxk prev A j = true ->
  FOentry_check axb PrF maxk (front ++ prev) A
    (FOjshift (length front) j) = true.
Proof.
  intros axb PrF maxk front prev A j H.
  destruct j as [| | x t | x t | i j' | i | i | k X Y | k X | k k' X | x X];
    cbn [FOjshift FOentry_check] in H |- *.
  - exact H.
  - exact H.
  - exact H.
  - exact H.
  - destruct (nth_error prev i) as [AB|] eqn:E1; [|discriminate].
    destruct (nth_error prev j') as [B|] eqn:E2; [|discriminate].
    rewrite nth_error_app_shift, E1.
    rewrite nth_error_app_shift, E2.
    exact H.
  - destruct A as [a b | | P C | y A' | y A']; try discriminate.
    destruct (nth_error prev i) as [B'|] eqn:E1; [|discriminate].
    rewrite nth_error_app_shift, E1.
    exact H.
  - destruct (nth_error prev i) as [P|] eqn:E1; [|discriminate].
    rewrite nth_error_app_shift, E1.
    exact H.
  - exact H.
  - exact H.
  - exact H.
  - exact H.
Qed.

Lemma FOseq_check_app : forall axb PrF maxk items1 items2 done,
  FOseq_check axb PrF maxk done (items1 ++ items2)
  = (FOseq_check axb PrF maxk done items1
     && FOseq_check axb PrF maxk (done ++ map fst items1)
          items2)%bool.
Proof.
  intros axb PrF maxk items1.
  induction items1 as [|[A j] rest IH]; intros items2 done.
  - cbn [FOseq_check app map]. rewrite app_nil_r. reflexivity.
  - cbn [FOseq_check app map fst].
    rewrite IH.
    rewrite Bool.andb_assoc.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma FOseq_check_shift : forall axb PrF maxk items front done,
  FOseq_check axb PrF maxk done items = true ->
  FOseq_check axb PrF maxk (front ++ done)
    (FOshift_items (length front) items) = true.
Proof.
  intros axb PrF maxk items.
  induction items as [|[A j] rest IH]; intros front done Hck.
  - reflexivity.
  - cbn [FOseq_check FOshift_items] in Hck |- *.
    apply Bool.andb_true_iff in Hck. destruct Hck as [H1 H2].
    apply Bool.andb_true_iff. split.
    + exact (FOentry_check_shift axb PrF maxk front done A j H1).
    + rewrite <- app_assoc.
      exact (IH front (done ++ [A]) H2).
Qed.

Lemma FOseq_check_single_log : forall axb PrF maxk done A,
  FOis_logical_axiom A = true ->
  FOseq_check axb PrF maxk done [(A, J_log)] = true.
Proof.
  intros axb PrF maxk done A H.
  cbn [FOseq_check FOentry_check]. rewrite H. reflexivity.
Qed.

Lemma FOseq_check_single_MP : forall axb PrF maxk done i1 i2 phi psi,
  nth_error done i1 = Some (FOImplF phi psi) ->
  nth_error done i2 = Some phi ->
  FOseq_check axb PrF maxk done [(psi, J_MP i1 i2)] = true.
Proof.
  intros axb PrF maxk done i1 i2 phi psi H1 H2.
  cbn [FOseq_check FOentry_check].
  rewrite H1, H2.
  change ((FOform_eqb (FOImplF phi psi) (FOImplF phi psi)
           && true)%bool = true).
  rewrite FOform_eqb_refl. reflexivity.
Qed.

Lemma FOseq_check_single_Gen : forall axb PrF maxk done i x phi,
  nth_error done i = Some phi ->
  FOseq_check axb PrF maxk done [(FOForall x phi, J_Gen i)] = true.
Proof.
  intros axb PrF maxk done i x phi H.
  cbn [FOseq_check FOentry_check].
  rewrite H.
  change ((FOform_eqb phi phi && true)%bool = true).
  rewrite FOform_eqb_refl. reflexivity.
Qed.

Lemma FOseq_check_single_Loeb : forall axb PrF maxk done i phi,
  nth_error done i = Some (FOImplF (PrF phi) phi) ->
  FOseq_check axb PrF maxk done [(phi, J_Loeb i)] = true.
Proof.
  intros axb PrF maxk done i phi H.
  cbn [FOseq_check FOentry_check].
  rewrite H.
  change ((FOform_eqb (FOImplF (PrF phi) phi) (FOImplF (PrF phi) phi)
           && true)%bool = true).
  rewrite FOform_eqb_refl. reflexivity.
Qed.

Theorem FOProvesTn_to_seq : forall n A,
  FOProvesTn n A ->
  exists items pre,
    FOseq_check (FOaxb n) (FOProvSentence n) n [] items = true
    /\ map fst items = pre ++ [A].
Proof.
  intros n A H.
  induction H as
    [ phi Hax
    | phi psi
    | phi psi chi
    | phi
    | phi psi Hp1 IH1 Hp2 IH2
    | x phi Hp IH
    | t
    | a b
    | a b c
    | a b
    | a b c d
    | a b c d
    | x t phi Hok
    | x t phi Hok
    | x phi psi Hfree
    | y P Q
    | y Hh R Hfree
    | phi Hp IH ].
  - inversion Hax; subst.
    + eexists [(_, J_thax)], [].
      split; [|reflexivity].
      cbn [FOseq_check FOentry_check].
      rewrite FOaxb_complete_RQ by assumption. reflexivity.
    + eexists [(_, J_thax)], [].
      split; [|reflexivity].
      cbn [FOseq_check FOentry_check].
      rewrite FOaxb_complete_Refl by assumption. reflexivity.
    + eexists [(_, J_d2 _ _ _)], [].
      split; [|reflexivity].
      cbn [FOseq_check FOentry_check].
      rewrite FOform_eqb_refl,
        (proj2 (Nat.ltb_lt _ _)) by eassumption.
      reflexivity.
    + eexists [(_, J_d3 _ _)], [].
      split; [|reflexivity].
      cbn [FOseq_check FOentry_check].
      rewrite FOform_eqb_refl,
        (proj2 (Nat.ltb_lt _ _)) by eassumption.
      reflexivity.
    + eexists [(_, J_dmon _ _ _)], [].
      split; [|reflexivity].
      cbn [FOseq_check FOentry_check].
      rewrite FOform_eqb_refl,
        (proj2 (Nat.leb_le _ _)),
        (proj2 (Nat.ltb_lt _ _)) by eassumption.
      reflexivity.
    + eexists [(_, J_ind _ _)], [].
      split; [|reflexivity].
      cbn [FOseq_check FOentry_check].
      rewrite FOform_eqb_refl. reflexivity.
  - exists [(FOImplF phi (FOImplF psi phi), J_log)], [].
    split; [|reflexivity].
    apply FOseq_check_single_log.
    unfold FOis_logical_axiom.
    rewrite (FOis_K_complete phi psi).
    rewrite ?Bool.orb_true_r. reflexivity.
  - exists [(FOImplF (FOImplF phi (FOImplF psi chi))
              (FOImplF (FOImplF phi psi) (FOImplF phi chi)), J_log)], [].
    split; [|reflexivity].
    apply FOseq_check_single_log.
    unfold FOis_logical_axiom.
    rewrite (FOis_S_complete phi psi chi).
    rewrite ?Bool.orb_true_r. reflexivity.
  - exists [(FOImplF (FONeg (FONeg phi)) phi, J_log)], [].
    split; [|reflexivity].
    apply FOseq_check_single_log.
    unfold FOis_logical_axiom.
    rewrite (FOis_DN_complete phi).
    rewrite ?Bool.orb_true_r. reflexivity.
  - destruct IH1 as [items1 [pre1 [Hc1 Hm1]]].
    destruct IH2 as [items2 [pre2 [Hc2 Hm2]]].
    exists (items1
            ++ FOshift_items (length (map fst items1)) items2
            ++ [(psi, J_MP (length pre1)
                           (length (map fst items1) + length pre2))]).
    exists (map fst items1 ++ map fst items2).
    assert (N1 : nth_error (map fst items1 ++ map fst items2)
                   (length pre1) = Some (FOImplF phi psi)).
    { rewrite Hm1, <- app_assoc.
      rewrite nth_error_app2 by lia.
      rewrite Nat.sub_diag. reflexivity. }
    assert (N2 : nth_error (map fst items1 ++ map fst items2)
                   (length (map fst items1) + length pre2) = Some phi).
    { rewrite nth_error_app_shift, Hm2.
      exact (nth_error_last pre2 phi). }
    split.
    + rewrite FOseq_check_app.
      apply Bool.andb_true_iff. split; [exact Hc1|].
      rewrite FOseq_check_app.
      apply Bool.andb_true_iff. split.
      * assert (Hsh := FOseq_check_shift (FOaxb n) (FOProvSentence n)
                         n items2 (map fst items1) [] Hc2).
        rewrite app_nil_r in Hsh. exact Hsh.
      * rewrite FOshift_items_fst.
        apply (FOseq_check_single_MP (FOaxb n) (FOProvSentence n)
                 n _ _ _ phi psi); [exact N1 | exact N2].
    + rewrite !map_app, FOshift_items_fst.
      cbn [map fst].
      rewrite app_assoc. reflexivity.
  - destruct IH as [items1 [pre1 [Hc1 Hm1]]].
    exists (items1 ++ [(FOForall x phi, J_Gen (length pre1))]).
    exists (map fst items1).
    assert (N1 : nth_error (map fst items1) (length pre1) = Some phi).
    { rewrite Hm1. exact (nth_error_last pre1 phi). }
    split.
    + rewrite FOseq_check_app.
      apply Bool.andb_true_iff. split; [exact Hc1|].
      apply (FOseq_check_single_Gen (FOaxb n) (FOProvSentence n)
               n _ (length pre1) x phi).
      exact N1.
    + rewrite map_app. cbn [map fst]. reflexivity.
  - exists [(FOEq t t, J_log)], [].
    split; [|reflexivity].
    apply FOseq_check_single_log.
    unfold FOis_logical_axiom.
    rewrite (FOis_EqRefl_complete t).
    rewrite ?Bool.orb_true_r. reflexivity.
  - exists [(FOImplF (FOEq a b) (FOEq b a), J_log)], [].
    split; [|reflexivity].
    apply FOseq_check_single_log.
    unfold FOis_logical_axiom.
    rewrite (FOis_EqSym_complete a b).
    rewrite ?Bool.orb_true_r. reflexivity.
  - exists [(FOImplF (FOEq a b) (FOImplF (FOEq b c) (FOEq a c)),
             J_log)], [].
    split; [|reflexivity].
    apply FOseq_check_single_log.
    unfold FOis_logical_axiom.
    rewrite (FOis_EqTrans_complete a b c).
    rewrite ?Bool.orb_true_r. reflexivity.
  - exists [(FOImplF (FOEq a b) (FOEq (FOSucc a) (FOSucc b)),
             J_log)], [].
    split; [|reflexivity].
    apply FOseq_check_single_log.
    unfold FOis_logical_axiom.
    rewrite (FOis_CongS_complete a b).
    rewrite ?Bool.orb_true_r. reflexivity.
  - exists [(FOImplF (FOEq a b)
              (FOImplF (FOEq c d) (FOEq (FOPlus a c) (FOPlus b d))),
             J_log)], [].
    split; [|reflexivity].
    apply FOseq_check_single_log.
    unfold FOis_logical_axiom.
    rewrite (FOis_CongPlus_complete a b c d).
    rewrite ?Bool.orb_true_r. reflexivity.
  - exists [(FOImplF (FOEq a b)
              (FOImplF (FOEq c d) (FOEq (FOMult a c) (FOMult b d))),
             J_log)], [].
    split; [|reflexivity].
    apply FOseq_check_single_log.
    unfold FOis_logical_axiom.
    rewrite (FOis_CongMult_complete a b c d).
    rewrite ?Bool.orb_true_r. reflexivity.
  - exists [(FOImplF (FOForall x phi) (FOsubst_f x t phi),
             J_AllElim x t)], [].
    split; [|reflexivity].
    cbn [FOseq_check FOentry_check].
    rewrite (FOis_AllElim_complete x t phi Hok). reflexivity.
  - exists [(FOImplF (FOsubst_f x t phi) (FOExists x phi),
             J_ExIntro x t)], [].
    split; [|reflexivity].
    cbn [FOseq_check FOentry_check].
    rewrite (FOis_ExIntro_complete x t phi Hok). reflexivity.
  - exists [(FOImplF (FOForall x (FOImplF phi psi))
              (FOImplF (FOExists x phi) psi), J_log)], [].
    split; [|reflexivity].
    apply FOseq_check_single_log.
    unfold FOis_logical_axiom.
    rewrite (FOis_ExElim_complete x phi psi Hfree).
    rewrite ?Bool.orb_true_r. reflexivity.
  - exists [(FOImplF (FOForall y (FOImplF P Q))
              (FOImplF (FOForall y P) (FOForall y Q)), J_log)], [].
    split; [|reflexivity].
    apply FOseq_check_single_log.
    unfold FOis_logical_axiom.
    rewrite (FOis_AllK_complete y P Q).
    rewrite ?Bool.orb_true_r. reflexivity.
  - exists [(FOImplF (FOForall y (FOImplF Hh R))
              (FOImplF Hh (FOForall y R)), J_log)], [].
    split; [|reflexivity].
    apply FOseq_check_single_log.
    unfold FOis_logical_axiom.
    rewrite (FOis_AllExport_complete y Hh R Hfree).
    rewrite ?Bool.orb_true_r. reflexivity.
  - destruct IH as [items1 [pre1 [Hc1 Hm1]]].
    exists (items1 ++ [(phi, J_Loeb (length pre1))]).
    exists (map fst items1).
    assert (N1 : nth_error (map fst items1) (length pre1)
                 = Some (FOImplF (FOProvSentence n phi) phi)).
    { rewrite Hm1.
      exact (nth_error_last pre1
               (FOImplF (FOProvSentence n phi) phi)). }
    split.
    + rewrite FOseq_check_app.
      apply Bool.andb_true_iff. split; [exact Hc1|].
      apply (FOseq_check_single_Loeb (FOaxb n) (FOProvSentence n)
               n _ (length pre1) phi).
      exact N1.
    + rewrite map_app. cbn [map fst]. reflexivity.
Qed.

Theorem FOProvesTn_iff_seq : forall n A,
  FOProvesTn n A
  <-> exists items,
        FOseq_check (FOaxb n) (FOProvSentence n) n [] items = true
        /\ In A (map fst items).
Proof.
  intros n A. split.
  - intros H.
    destruct (FOProvesTn_to_seq n A H) as [items [pre [Hck Hm]]].
    exists items. split; [exact Hck|].
    rewrite Hm. apply in_or_app. right. left. reflexivity.
  - intros [items [Hck HIn]].
    exact (FOProvesTn_of_seq n items A Hck HIn).
Qed.

(** ** Propositional tautologies transfer into the T_n tower.

    [FOofForm m phi] reads a modal skeleton as an FO formula through an
    atom assignment [m].  [ProvableProp] derivations push through the
    reading, so [prop_decide_correct] turns every boolean-checked
    tautology skeleton into an [FOProvesTn] theorem at any level. *)

Definition FOIff (A B : FOFormula) : FOFormula :=
  FOAnd (FOImplF A B) (FOImplF B A).

Definition FOm1 (A : FOFormula) : nat -> FOFormula := fun _ => A.
Definition FOm2 (A B : FOFormula) : nat -> FOFormula :=
  fun i => match i with 0 => A | _ => B end.
Definition FOm3 (A B C : FOFormula) : nat -> FOFormula :=
  fun i => match i with 0 => A | 1 => B | _ => C end.
Definition FOm4 (A B C D : FOFormula) : nat -> FOFormula :=
  fun i => match i with 0 => A | 1 => B | 2 => C | _ => D end.

Fixpoint FOofForm (m : nat -> FOFormula) (phi : Form) : FOFormula :=
  match phi with
  | Var i => m i
  | Bot => FOFalseF
  | Impl a b => FOImplF (FOofForm m a) (FOofForm m b)
  | Box _ _ => FOTrue
  end.

Lemma FOPr_of_ProvableProp : forall n (m : nat -> FOFormula) phi,
  ProvableProp phi -> FOProvesTn n (FOofForm m phi).
Proof.
  intros n m phi H. induction H; cbn.
  - apply FOProvesTn_K.
  - apply FOProvesTn_S.
  - apply FOProvesTn_DN.
  - exact (FOProvesTn_MP n _ _ IHProvableProp1 IHProvableProp2).
Qed.

Lemma FOPr_taut : forall n (m : nat -> FOFormula) phi,
  box_free phi -> decide_tautology phi = true ->
  FOProvesTn n (FOofForm m phi).
Proof.
  intros n m phi Hbf Hdec.
  exact (FOPr_of_ProvableProp n m phi (prop_decide_correct phi Hbf Hdec)).
Qed.

Lemma FOPr_efq : forall n A, FOProvesTn n (FOImplF FOFalseF A).
Proof.
  intros n A.
  apply (FOPr_taut n (FOm1 A) (Impl Bot (Var 0))); [cbn; tauto | reflexivity].
Qed.

Lemma FOPr_dni : forall n A, FOProvesTn n (FOImplF A (FONeg (FONeg A))).
Proof.
  intros n A.
  apply (FOPr_taut n (FOm1 A) (Impl (Var 0) (Neg (Neg (Var 0)))));
    [cbn; tauto | reflexivity].
Qed.

Lemma FOPr_contrapose : forall n A B,
  FOProvesTn n (FOImplF (FOImplF A B) (FOImplF (FONeg B) (FONeg A))).
Proof.
  intros n A B.
  apply (FOPr_taut n (FOm2 A B)
    (Impl (Impl (Var 0) (Var 1)) (Impl (Neg (Var 1)) (Neg (Var 0)))));
    [cbn; tauto | reflexivity].
Qed.

Lemma FOPr_syl : forall n A B C,
  FOProvesTn n (FOImplF (FOImplF A B)
                  (FOImplF (FOImplF B C) (FOImplF A C))).
Proof.
  intros n A B C.
  apply (FOPr_taut n (FOm3 A B C)
    (Impl (Impl (Var 0) (Var 1))
          (Impl (Impl (Var 1) (Var 2)) (Impl (Var 0) (Var 2)))));
    [cbn; tauto | reflexivity].
Qed.

Lemma FOPr_imp_swap : forall n A B C,
  FOProvesTn n (FOImplF (FOImplF A (FOImplF B C))
                        (FOImplF B (FOImplF A C))).
Proof.
  intros n A B C.
  apply (FOPr_taut n (FOm3 A B C)
    (Impl (Impl (Var 0) (Impl (Var 1) (Var 2)))
          (Impl (Var 1) (Impl (Var 0) (Var 2)))));
    [cbn; tauto | reflexivity].
Qed.

Lemma FOPr_horizontal : forall n B' B C C',
  FOProvesTn n (FOImplF (FOImplF B' B)
                  (FOImplF (FOImplF C C')
                     (FOImplF (FOImplF B C) (FOImplF B' C')))).
Proof.
  intros n B' B C C'.
  apply (FOPr_taut n (FOm4 B' B C C')
    (Impl (Impl (Var 0) (Var 1))
          (Impl (Impl (Var 2) (Var 3))
                (Impl (Impl (Var 1) (Var 2)) (Impl (Var 0) (Var 3))))));
    [cbn; tauto | reflexivity].
Qed.

Lemma FOPr_and_intro : forall n A B,
  FOProvesTn n A -> FOProvesTn n B -> FOProvesTn n (FOAnd A B).
Proof.
  intros n A B HA HB.
  assert (Ht : FOProvesTn n (FOImplF A (FOImplF B (FOAnd A B)))).
  { apply (FOPr_taut n (FOm2 A B)
      (Impl (Var 0) (Impl (Var 1) (And (Var 0) (Var 1)))));
      [cbn; tauto | reflexivity]. }
  exact (FOProvesTn_MP n _ _ (FOProvesTn_MP n _ _ Ht HA) HB).
Qed.

Lemma FOPr_and_elim_l : forall n A B,
  FOProvesTn n (FOImplF (FOAnd A B) A).
Proof.
  intros n A B.
  apply (FOPr_taut n (FOm2 A B)
    (Impl (And (Var 0) (Var 1)) (Var 0)));
    [cbn; tauto | reflexivity].
Qed.

Lemma FOPr_and_elim_r : forall n A B,
  FOProvesTn n (FOImplF (FOAnd A B) B).
Proof.
  intros n A B.
  apply (FOPr_taut n (FOm2 A B)
    (Impl (And (Var 0) (Var 1)) (Var 1)));
    [cbn; tauto | reflexivity].
Qed.

Lemma FOPr_or_intro_l : forall n A B,
  FOProvesTn n (FOImplF A (FOOr A B)).
Proof.
  intros n A B.
  apply (FOPr_taut n (FOm2 A B)
    (Impl (Var 0) (Or (Var 0) (Var 1))));
    [cbn; tauto | reflexivity].
Qed.

Lemma FOPr_or_intro_r : forall n A B,
  FOProvesTn n (FOImplF B (FOOr A B)).
Proof.
  intros n A B.
  apply (FOPr_taut n (FOm2 A B)
    (Impl (Var 1) (Or (Var 0) (Var 1))));
    [cbn; tauto | reflexivity].
Qed.

Lemma FOPr_or_elim : forall n A B C,
  FOProvesTn n (FOImplF (FOImplF A C)
                  (FOImplF (FOImplF B C) (FOImplF (FOOr A B) C))).
Proof.
  intros n A B C.
  apply (FOPr_taut n (FOm3 A B C)
    (Impl (Impl (Var 0) (Var 2))
          (Impl (Impl (Var 1) (Var 2)) (Impl (Or (Var 0) (Var 1)) (Var 2)))));
    [cbn; tauto | reflexivity].
Qed.

(** Case analysis under a fixed antecedent: from [H -> A \/ B],
    [A -> C], [B -> C], conclude [H -> C]. *)

Lemma FOPr_case : forall n A B C,
  FOProvesTn n (FOOr A B) ->
  FOProvesTn n (FOImplF A C) -> FOProvesTn n (FOImplF B C) ->
  FOProvesTn n C.
Proof.
  intros n A B C Hor HA HB.
  exact (FOProvesTn_MP n _ _
          (FOProvesTn_MP n _ _ (FOProvesTn_MP n _ _ (FOPr_or_elim n A B C) HA)
             HB) Hor).
Qed.

Lemma FOPr_idf : forall n A, FOProvesTn n (FOImplF A A).
Proof.
  intros n A.
  apply (FOPr_taut n (FOm1 A) (Impl (Var 0) (Var 0)));
    [cbn; tauto | reflexivity].
Qed.

Lemma FOPr_under_mp : forall n H A B,
  FOProvesTn n (FOImplF H (FOImplF A B)) ->
  FOProvesTn n (FOImplF H A) ->
  FOProvesTn n (FOImplF H B).
Proof.
  intros n H0 A B H1 H2.
  exact (FOProvesTn_MP n _ _
           (FOProvesTn_MP n _ _ (FOProvesTn_S n H0 A B) H1) H2).
Qed.

Theorem FO_T_n_proves_Con_prev : forall n,
  FOProvesTn (S n) (FOConSentence n).
Proof.
  intro n.
  unfold FOConSentence, FONeg.
  apply (FOPr_under_mp (S n) (FOProvSentence n (FONeg FOTopFm))
           FOTopFm FOFalseF).
  - exact (FOProvesTn_ax (S n) _
             (FOAx_Refl (S n) n (FONeg FOTopFm) (Nat.lt_succ_diag_r n))).
  - apply (FOProvesTn_MP (S n) FOTopFm).
    + exact (FOProvesTn_K (S n) FOTopFm _).
    + exact (FOPr_idf (S n) FOFalseF).
Qed.

Lemma FOnumeral_not_FOPlus : forall n x y,
  FOnumeral n <> FOPlus x y.
Proof.
  intros [|k]; intros x y H; cbn in H; discriminate.
Qed.

Lemma FOnumeral_not_FOMult : forall n x y,
  FOnumeral n <> FOMult x y.
Proof.
  intros [|k]; intros x y H; cbn in H; discriminate.
Qed.

Lemma FOnumeral_form_not_RobinsonQ : forall n,
  ~ FORobinsonQ (FOEq (FOnumeral n) (FOnumeral n)).
Proof.
  intros n H.
  remember (FOEq (FOnumeral n) (FOnumeral n)) as F.
  destruct H; try discriminate.
  - injection HeqF as Heq1 _.
    symmetry in Heq1. revert Heq1. apply FOnumeral_not_FOPlus.
  - injection HeqF as Heq1 _.
    symmetry in Heq1. revert Heq1. apply FOnumeral_not_FOPlus.
  - injection HeqF as Heq1 _.
    symmetry in Heq1. revert Heq1. apply FOnumeral_not_FOMult.
  - injection HeqF as Heq1 _.
    symmetry in Heq1. revert Heq1. apply FOnumeral_not_FOMult.
Qed.

Lemma FOnumeral_inj : forall k n,
  FOnumeral k = FOnumeral n -> k = n.
Proof.
  induction k as [|k IH]; intros [|n'] Heq; cbn in Heq; try discriminate; try reflexivity.
  injection Heq. intro Heq'. f_equal. exact (IH n' Heq').
Qed.

(** ** N-satisfaction for the first-order layer, and soundness of the
    T_n tower.

    [FOeval] and [FOsat] interpret [FOTerm]/[FOFormula] in the standard
    model.  [FOProvesTn_sound] is soundness of [FOProvesTn] against
    [FOsat]; [FOProvesTn_consistent] its consistency.  [FOsubst_num] is
    numeral instantiation with its semantics. *)

Definition FOenv := nat -> nat.

Definition FOupdate (e : FOenv) (x v : nat) : FOenv :=
  fun y => if Nat.eqb y x then v else e y.

Fixpoint FOeval (e : FOenv) (t : FOTerm) : nat :=
  match t with
  | FOVar n => e n
  | FOZero => 0
  | FOSucc a => S (FOeval e a)
  | FOPlus a b => FOeval e a + FOeval e b
  | FOMult a b => FOeval e a * FOeval e b
  end.

Fixpoint FOsat (e : FOenv) (A : FOFormula) : Prop :=
  match A with
  | FOEq a b => FOeval e a = FOeval e b
  | FOFalseF => False
  | FOImplF A B => FOsat e A -> FOsat e B
  | FOForall x A => forall v, FOsat (FOupdate e x v) A
  | FOExists x A => exists v, FOsat (FOupdate e x v) A
  end.

Lemma FOeval_numeral : forall e k, FOeval e (FOnumeral k) = k.
Proof.
  intros e k. induction k as [|k IH]; cbn;
    [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma FOeval_ext : forall t e1 e2,
  (forall n, e1 n = e2 n) -> FOeval e1 t = FOeval e2 t.
Proof.
  induction t; intros e1 e2 H; cbn.
  - apply H.
  - reflexivity.
  - rewrite (IHt e1 e2 H); reflexivity.
  - rewrite (IHt1 e1 e2 H), (IHt2 e1 e2 H); reflexivity.
  - rewrite (IHt1 e1 e2 H), (IHt2 e1 e2 H); reflexivity.
Qed.

Lemma FOupdate_comm : forall e x y u w n,
  x <> y ->
  FOupdate (FOupdate e x u) y w n = FOupdate (FOupdate e y w) x u n.
Proof.
  intros e x y u w n Hxy. unfold FOupdate.
  destruct (Nat.eqb n y) eqn:Ey; destruct (Nat.eqb n x) eqn:Ex; try reflexivity.
  apply Nat.eqb_eq in Ey, Ex. subst. contradiction.
Qed.

Lemma FOupdate_shadow : forall e x u w n,
  FOupdate (FOupdate e x u) x w n = FOupdate e x w n.
Proof.
  intros e x u w n. unfold FOupdate. destruct (Nat.eqb n x); reflexivity.
Qed.

Lemma FOsat_ext : forall A e1 e2,
  (forall n, e1 n = e2 n) -> (FOsat e1 A <-> FOsat e2 A).
Proof.
  induction A as [a b | | A IHA B IHB | x A IHA | x A IHA];
    intros e1 e2 H; cbn.
  - rewrite (FOeval_ext a e1 e2 H), (FOeval_ext b e1 e2 H). reflexivity.
  - reflexivity.
  - rewrite (IHA e1 e2 H), (IHB e1 e2 H). reflexivity.
  - split; intros Hf v; specialize (Hf v).
    + rewrite <- (IHA (FOupdate e1 x v) (FOupdate e2 x v)); [exact Hf|].
      intro n. unfold FOupdate. destruct (Nat.eqb n x); [reflexivity | apply H].
    + rewrite (IHA (FOupdate e1 x v) (FOupdate e2 x v)); [exact Hf|].
      intro n. unfold FOupdate. destruct (Nat.eqb n x); [reflexivity | apply H].
  - split; intros [v Hv]; exists v.
    + rewrite <- (IHA (FOupdate e1 x v) (FOupdate e2 x v)); [exact Hv|].
      intro n. unfold FOupdate. destruct (Nat.eqb n x); [reflexivity | apply H].
    + rewrite (IHA (FOupdate e1 x v) (FOupdate e2 x v)); [exact Hv|].
      intro n. unfold FOupdate. destruct (Nat.eqb n x); [reflexivity | apply H].
Qed.

Lemma FOeval_subst_tm : forall t x k e,
  FOeval e (FOsubst_tm x k t) = FOeval (FOupdate e x k) t.
Proof.
  induction t; intros x k e; cbn.
  - destruct (Nat.eqb n x) eqn:E.
    + rewrite FOeval_numeral. unfold FOupdate. rewrite E. reflexivity.
    + cbn. unfold FOupdate. rewrite E. reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma FOsat_subst_num : forall A x k e,
  FOsat e (FOsubst_num x k A) <-> FOsat (FOupdate e x k) A.
Proof.
  induction A as [a b | | A IHA B IHB | y A IHA | y A IHA];
    intros x k e; cbn.
  - rewrite (FOeval_subst_tm a), (FOeval_subst_tm b). reflexivity.
  - reflexivity.
  - rewrite IHA, IHB. reflexivity.
  - destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst y. cbn.
      split; intros Hf v; specialize (Hf v).
      * rewrite (FOsat_ext A (FOupdate (FOupdate e x k) x v) (FOupdate e x v)
                  (FOupdate_shadow e x k v)). exact Hf.
      * rewrite <- (FOsat_ext A (FOupdate (FOupdate e x k) x v) (FOupdate e x v)
                  (FOupdate_shadow e x k v)). exact Hf.
    + apply Nat.eqb_neq in E. cbn.
      split; intros Hf v; specialize (Hf v).
      * rewrite (IHA x k (FOupdate e y v)) in Hf.
        rewrite (FOsat_ext A (FOupdate (FOupdate e x k) y v)
                  (FOupdate (FOupdate e y v) x k)
                  (fun n => FOupdate_comm e x y k v n (fun H => E (eq_sym H)))).
        exact Hf.
      * rewrite (IHA x k (FOupdate e y v)).
        rewrite (FOsat_ext A (FOupdate (FOupdate e y v) x k)
                  (FOupdate (FOupdate e x k) y v)
                  (fun n => FOupdate_comm e y x v k n E)). exact Hf.
  - destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst y. cbn.
      split; intros [v Hv]; exists v.
      * rewrite (FOsat_ext A (FOupdate (FOupdate e x k) x v) (FOupdate e x v)
                  (FOupdate_shadow e x k v)). exact Hv.
      * rewrite <- (FOsat_ext A (FOupdate (FOupdate e x k) x v) (FOupdate e x v)
                  (FOupdate_shadow e x k v)). exact Hv.
    + apply Nat.eqb_neq in E. cbn.
      split; intros [v Hv]; exists v.
      * rewrite (IHA x k (FOupdate e y v)) in Hv.
        rewrite (FOsat_ext A (FOupdate (FOupdate e x k) y v)
                  (FOupdate (FOupdate e y v) x k)
                  (fun n => FOupdate_comm e x y k v n (fun H => E (eq_sym H)))).
        exact Hv.
      * rewrite (IHA x k (FOupdate e y v)).
        rewrite (FOsat_ext A (FOupdate (FOupdate e y v) x k)
                  (FOupdate (FOupdate e x k) y v)
                  (fun n => FOupdate_comm e y x v k n E)). exact Hv.
Qed.

(** Semantics of term-level substitution. *)

Lemma FOeval_subst_t : forall t x s e,
  FOeval e (FOsubst_t x s t) = FOeval (FOupdate e x (FOeval e s)) t.
Proof.
  induction t; intros x s e; cbn.
  - destruct (Nat.eqb n x) eqn:E.
    + unfold FOupdate. rewrite E. reflexivity.
    + cbn. unfold FOupdate. rewrite E. reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma FOeval_agree_in : forall t e1 e2,
  (forall v, FOin_tm v t = true -> e1 v = e2 v) ->
  FOeval e1 t = FOeval e2 t.
Proof.
  induction t; intros e1 e2 H; cbn.
  - apply H. cbn. apply Nat.eqb_refl.
  - reflexivity.
  - rewrite (IHt e1 e2 H). reflexivity.
  - rewrite (IHt1 e1 e2
      (fun v Hv => H v (proj2 (Bool.orb_true_iff _ _) (or_introl Hv)))).
    rewrite (IHt2 e1 e2
      (fun v Hv => H v (proj2 (Bool.orb_true_iff _ _) (or_intror Hv)))).
    reflexivity.
  - rewrite (IHt1 e1 e2
      (fun v Hv => H v (proj2 (Bool.orb_true_iff _ _) (or_introl Hv)))).
    rewrite (IHt2 e1 e2
      (fun v Hv => H v (proj2 (Bool.orb_true_iff _ _) (or_intror Hv)))).
    reflexivity.
Qed.

Lemma FOeval_update_not_in : forall t e x w,
  FOin_tm x t = false ->
  FOeval (FOupdate e x w) t = FOeval e t.
Proof.
  intros t e x w Hni. apply FOeval_agree_in.
  intros v Hv. unfold FOupdate.
  destruct (Nat.eqb_spec v x) as [E|E].
  - subst v. rewrite Hv in Hni. discriminate.
  - reflexivity.
Qed.

Lemma FOsat_agree_free : forall A e1 e2,
  (forall v, FOfree_in v A = true -> e1 v = e2 v) ->
  (FOsat e1 A <-> FOsat e2 A).
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB];
    intros e1 e2 H; cbn.
  - rewrite (FOeval_agree_in a e1 e2
      (fun v Hv => H v (proj2 (Bool.orb_true_iff _ _) (or_introl Hv)))).
    rewrite (FOeval_agree_in b e1 e2
      (fun v Hv => H v (proj2 (Bool.orb_true_iff _ _) (or_intror Hv)))).
    reflexivity.
  - reflexivity.
  - rewrite (IHB e1 e2
      (fun v Hv => H v (proj2 (Bool.orb_true_iff _ _) (or_introl Hv)))).
    rewrite (IHC e1 e2
      (fun v Hv => H v (proj2 (Bool.orb_true_iff _ _) (or_intror Hv)))).
    reflexivity.
  - assert (Hpt : forall v0, forall v, FOfree_in v B = true ->
      FOupdate e1 y v0 v = FOupdate e2 y v0 v).
    { intros v0 v Hv. unfold FOupdate.
      destruct (Nat.eqb_spec v y) as [E|E]; [reflexivity|].
      apply H. cbn.
      destruct (Nat.eqb_spec y v) as [E2|E2].
      - exfalso. apply E. symmetry. exact E2.
      - exact Hv. }
    split; intros Hf v0; specialize (Hf v0).
    + rewrite <- (IHB _ _ (Hpt v0)). exact Hf.
    + rewrite (IHB _ _ (Hpt v0)). exact Hf.
  - assert (Hpt : forall v0, forall v, FOfree_in v B = true ->
      FOupdate e1 y v0 v = FOupdate e2 y v0 v).
    { intros v0 v Hv. unfold FOupdate.
      destruct (Nat.eqb_spec v y) as [E|E]; [reflexivity|].
      apply H. cbn.
      destruct (Nat.eqb_spec y v) as [E2|E2].
      - exfalso. apply E. symmetry. exact E2.
      - exact Hv. }
    split; intros [v0 Hv0]; exists v0.
    + rewrite <- (IHB _ _ (Hpt v0)). exact Hv0.
    + rewrite (IHB _ _ (Hpt v0)). exact Hv0.
Qed.

Lemma FOsat_update_not_free : forall A e x w,
  FOfree_in x A = false ->
  (FOsat (FOupdate e x w) A <-> FOsat e A).
Proof.
  intros A e x w Hnf. apply FOsat_agree_free.
  intros v Hv. unfold FOupdate.
  destruct (Nat.eqb_spec v x) as [E|E].
  - subst v. rewrite Hv in Hnf. discriminate.
  - reflexivity.
Qed.

Lemma FOsubst_t_not_in : forall t x s,
  FOin_tm x t = false -> FOsubst_t x s t = t.
Proof.
  induction t; intros x s Hni; cbn in *.
  - destruct (Nat.eqb_spec n x) as [E|E].
    + discriminate Hni.
    + reflexivity.
  - reflexivity.
  - rewrite (IHt x s Hni). reflexivity.
  - apply Bool.orb_false_iff in Hni. destruct Hni as [H1 H2].
    rewrite (IHt1 x s H1), (IHt2 x s H2). reflexivity.
  - apply Bool.orb_false_iff in Hni. destruct Hni as [H1 H2].
    rewrite (IHt1 x s H1), (IHt2 x s H2). reflexivity.
Qed.

Lemma FOsubst_f_not_free : forall A x s,
  FOfree_in x A = false -> FOsubst_f x s A = A.
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB];
    intros x s Hnf; cbn in *.
  - apply Bool.orb_false_iff in Hnf. destruct Hnf as [H1 H2].
    rewrite (FOsubst_t_not_in a x s H1), (FOsubst_t_not_in b x s H2).
    reflexivity.
  - reflexivity.
  - apply Bool.orb_false_iff in Hnf. destruct Hnf as [H1 H2].
    rewrite (IHB x s H1), (IHC x s H2). reflexivity.
  - destruct (Nat.eqb_spec y x) as [E|E].
    + reflexivity.
    + rewrite (IHB x s Hnf). reflexivity.
  - destruct (Nat.eqb_spec y x) as [E|E].
    + reflexivity.
    + rewrite (IHB x s Hnf). reflexivity.
Qed.

(** The substitution lemma: a capture-free substitution evaluates the
    substituted term in the outer environment. *)

Lemma FOsat_subst_f : forall A x s e,
  FOsubst_ok x s A = true ->
  (FOsat e (FOsubst_f x s A) <-> FOsat (FOupdate e x (FOeval e s)) A).
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB];
    intros x s e Hok; cbn.
  - rewrite (FOeval_subst_t a), (FOeval_subst_t b). reflexivity.
  - reflexivity.
  - cbn in Hok. apply Bool.andb_true_iff in Hok. destruct Hok as [H1 H2].
    rewrite (IHB x s e H1), (IHC x s e H2). reflexivity.
  - cbn in Hok. destruct (Nat.eqb_spec y x) as [E|E].
    + subst y. cbn.
      split; intros Hf v0; specialize (Hf v0).
      * rewrite (FOsat_ext B (FOupdate (FOupdate e x (FOeval e s)) x v0)
                  (FOupdate e x v0)
                  (FOupdate_shadow e x (FOeval e s) v0)).
        exact Hf.
      * rewrite (FOsat_ext B (FOupdate (FOupdate e x (FOeval e s)) x v0)
                  (FOupdate e x v0)
                  (FOupdate_shadow e x (FOeval e s) v0)) in Hf.
        exact Hf.
    + destruct (FOfree_in x B) eqn:EF.
      * apply Bool.andb_true_iff in Hok. destruct Hok as [Hns Hok].
        apply Bool.negb_true_iff in Hns.
        cbn. split; intros Hf v0; specialize (Hf v0).
        -- rewrite (IHB x s (FOupdate e y v0) Hok) in Hf.
           rewrite (FOeval_update_not_in s e y v0 Hns) in Hf.
           rewrite (FOsat_ext B _ _
             (fun nn => FOupdate_comm e y x v0 (FOeval e s) nn E)) in Hf.
           exact Hf.
        -- rewrite (IHB x s (FOupdate e y v0) Hok).
           rewrite (FOeval_update_not_in s e y v0 Hns).
           rewrite (FOsat_ext B _ _
             (fun nn => FOupdate_comm e y x v0 (FOeval e s) nn E)).
           exact Hf.
      * rewrite (FOsubst_f_not_free B x s EF).
        assert (Hpt : forall v0, forall v, FOfree_in v B = true ->
          FOupdate e y v0 v = FOupdate (FOupdate e x (FOeval e s)) y v0 v).
        { intros v0 v Hv. unfold FOupdate.
          destruct (Nat.eqb v y) eqn:Evy; [reflexivity|].
          destruct (Nat.eqb_spec v x) as [Ex|Ex]; [|reflexivity].
          subst v. rewrite Hv in EF. discriminate. }
        cbn. split; intros Hf v0; specialize (Hf v0).
        -- rewrite <- (FOsat_agree_free B _ _ (Hpt v0)). exact Hf.
        -- rewrite (FOsat_agree_free B _ _ (Hpt v0)). exact Hf.
  - cbn in Hok. destruct (Nat.eqb_spec y x) as [E|E].
    + subst y. cbn.
      split; intros [v0 Hv0]; exists v0.
      * rewrite (FOsat_ext B (FOupdate (FOupdate e x (FOeval e s)) x v0)
                  (FOupdate e x v0)
                  (FOupdate_shadow e x (FOeval e s) v0)).
        exact Hv0.
      * rewrite (FOsat_ext B (FOupdate (FOupdate e x (FOeval e s)) x v0)
                  (FOupdate e x v0)
                  (FOupdate_shadow e x (FOeval e s) v0)) in Hv0.
        exact Hv0.
    + destruct (FOfree_in x B) eqn:EF.
      * apply Bool.andb_true_iff in Hok. destruct Hok as [Hns Hok].
        apply Bool.negb_true_iff in Hns.
        cbn. split; intros [v0 Hv0]; exists v0.
        -- rewrite (IHB x s (FOupdate e y v0) Hok) in Hv0.
           rewrite (FOeval_update_not_in s e y v0 Hns) in Hv0.
           rewrite (FOsat_ext B _ _
             (fun nn => FOupdate_comm e y x v0 (FOeval e s) nn E)) in Hv0.
           exact Hv0.
        -- rewrite (IHB x s (FOupdate e y v0) Hok).
           rewrite (FOeval_update_not_in s e y v0 Hns).
           rewrite (FOsat_ext B _ _
             (fun nn => FOupdate_comm e y x v0 (FOeval e s) nn E)).
           exact Hv0.
      * rewrite (FOsubst_f_not_free B x s EF).
        assert (Hpt : forall v0, forall v, FOfree_in v B = true ->
          FOupdate e y v0 v = FOupdate (FOupdate e x (FOeval e s)) y v0 v).
        { intros v0 v Hv. unfold FOupdate.
          destruct (Nat.eqb v y) eqn:Evy; [reflexivity|].
          destruct (Nat.eqb_spec v x) as [Ex|Ex]; [|reflexivity].
          subst v. rewrite Hv in EF. discriminate. }
        cbn. split; intros [v0 Hv0]; exists v0.
        -- rewrite <- (FOsat_agree_free B _ _ (Hpt v0)). exact Hv0.
        -- rewrite (FOsat_agree_free B _ _ (Hpt v0)). exact Hv0.
Qed.

(** ** Standard-model soundness of the induction schema.

    [FOInduction] (defined with the substitution toolkit above) is true
    in the standard model by natural-number induction on the bound; this
    is the soundness obligation discharged when the schema is admitted as
    a tower axiom. *)

Lemma FOInduction_sat : forall e x A, FOsat e (FOInduction x A).
Proof.
  intros e x A. unfold FOInduction. cbn [FOsat].
  intros Hbase Hstep v.
  induction v as [|v IHv].
  - apply (proj1 (FOsat_subst_f A x FOZero e
                   (FOsubst_ok_numeral A x 0))) in Hbase.
    cbn [FOeval] in Hbase. exact Hbase.
  - specialize (Hstep v). cbn [FOsat] in Hstep.
    pose proof (Hstep IHv) as Hsucc.
    apply (proj1 (FOsat_subst_f A x (FOSucc (FOVar x)) (FOupdate e x v)
                   (FOsubst_ok_succ_var_self A x))) in Hsucc.
    assert (Hev : FOeval (FOupdate e x v) (FOSucc (FOVar x)) = S v).
    { cbn. unfold FOupdate. rewrite Nat.eqb_refl. reflexivity. }
    rewrite Hev in Hsucc.
    exact (proj1 (FOsat_ext A _ _ (FOupdate_shadow e x v (S v))) Hsucc).
Qed.

(** The order relation, defined Diophantine-style with a variable above
    both terms. *)

Lemma FOeval_update_above : forall t e z v,
  FOmax_var_tm t < z ->
  FOeval (FOupdate e z v) t = FOeval e t.
Proof.
  induction t; intros e z v Hz; cbn in *.
  - unfold FOupdate.
    destruct (Nat.eqb_spec n z) as [E|E]; [lia | reflexivity].
  - reflexivity.
  - rewrite (IHt e z v Hz). reflexivity.
  - rewrite (IHt1 e z v), (IHt2 e z v); [reflexivity | lia | lia].
  - rewrite (IHt1 e z v), (IHt2 e z v); [reflexivity | lia | lia].
Qed.

Definition FOLtF (a b : FOTerm) : FOFormula :=
  FOExists (S (Nat.max (FOmax_var_tm a) (FOmax_var_tm b)))
    (FOEq (FOPlus a (FOSucc
             (FOVar (S (Nat.max (FOmax_var_tm a) (FOmax_var_tm b))))))
          b).

Lemma FOsat_FOLtF : forall e a b,
  FOsat e (FOLtF a b) <-> FOeval e a < FOeval e b.
Proof.
  intros e a b. unfold FOLtF. cbn.
  split.
  - intros [v Hv].
    rewrite (FOeval_update_above a) in Hv; [|lia].
    rewrite (FOeval_update_above b) in Hv; [|lia].
    try unfold FOupdate in Hv. rewrite Nat.eqb_refl in Hv. cbn in Hv.
    lia.
  - intro Hlt.
    exists (FOeval e b - FOeval e a - 1).
    rewrite (FOeval_update_above a); [|lia].
    rewrite (FOeval_update_above b); [|lia].
    try unfold FOupdate. rewrite Nat.eqb_refl. cbn.
    lia.
Qed.

(** Soundness of [FOProvesTn] against [FOsat] is proved after the
    representability bridge: the reflection axioms and the Loeb rule
    refer to the provability sentence, whose truth at each level needs
    the bridge at the levels below. *)

Lemma FOsat_FOAnd : forall e A B,
  FOsat e (FOAnd A B) <-> (FOsat e A /\ FOsat e B).
Proof.
  intros e A B. cbn. split.
  - intro H.
    destruct (classic (FOsat e A)); destruct (classic (FOsat e B)); tauto.
  - intros [Ha Hb] Hi. exact (Hi Ha Hb).
Qed.

Lemma FOsat_FOOr : forall e A B,
  FOsat e (FOOr A B) <-> (FOsat e A \/ FOsat e B).
Proof.
  intros e A B. cbn. split.
  - intro H. destruct (classic (FOsat e A)) as [a|a].
    + left. exact a.
    + right. exact (H a).
  - intros [a|b].
    + intro na. exfalso. exact (na a).
    + intro. exact b.
Qed.

Lemma FOsat_FOIff : forall e A B,
  FOsat e (FOIff A B) <-> (FOsat e A <-> FOsat e B).
Proof.
  intros e A B. unfold FOIff. rewrite FOsat_FOAnd. cbn. tauto.
Qed.

(** ** Provable numeral arithmetic in the T_n tower. *)

Lemma FOPr_weaken : forall n A B,
  FOProvesTn n A -> FOProvesTn n (FOImplF B A).
Proof.
  intros n A B H. exact (FOProvesTn_MP n _ _ (FOProvesTn_K n A B) H).
Qed.

Lemma FOPr_compose : forall n A B C,
  FOProvesTn n (FOImplF A B) -> FOProvesTn n (FOImplF B C) ->
  FOProvesTn n (FOImplF A C).
Proof.
  intros n A B C HAB HBC.
  pose proof (FOProvesTn_S n A B C) as HS.
  pose proof (FOPr_weaken n _ A HBC) as HW.
  exact (FOProvesTn_MP n _ _ (FOProvesTn_MP n _ _ HS HW) HAB).
Qed.

Lemma FOPr_mp2 : forall n A B C,
  FOProvesTn n (FOImplF A (FOImplF B C)) ->
  FOProvesTn n A -> FOProvesTn n B -> FOProvesTn n C.
Proof.
  intros n A B C H HA HB.
  exact (FOProvesTn_MP n _ _ (FOProvesTn_MP n _ _ H HA) HB).
Qed.

Lemma FOPr_swap_mp : forall n A B C,
  FOProvesTn n (FOImplF A (FOImplF B C)) -> FOProvesTn n B ->
  FOProvesTn n (FOImplF A C).
Proof.
  intros n A B C H HB.
  pose proof (FOProvesTn_S n A B C) as HS.
  pose proof (FOProvesTn_MP n _ _ HS H) as H1.
  exact (FOProvesTn_MP n _ _ H1 (FOPr_weaken n B A HB)).
Qed.

(** Numeral substitution into any theorem. *)

Lemma FOPr_inst1 : forall n x k A,
  FOProvesTn n A -> FOProvesTn n (FOsubst_num x k A).
Proof.
  intros n x k A H.
  exact (FOProvesTn_MP n _ _ (FOProvesTn_AllElimNum n x k A)
           (FOProvesTn_Gen n x A H)).
Qed.

Lemma FOsubst_tm_numeral : forall x k m,
  FOsubst_tm x k (FOnumeral m) = FOnumeral m.
Proof.
  intros x k m. induction m as [|m IH]; cbn;
    [reflexivity | rewrite IH; reflexivity].
Qed.

(** Robinson Q instances; the term-schematic axioms apply directly. *)

Lemma FOPr_q_succ_inj : forall n a b,
  FOProvesTn n (FOImplF (FOEq (FOSucc a) (FOSucc b)) (FOEq a b)).
Proof.
  intros n a b. exact (FOProvesTn_ax n _ (FOAx_RQ n _ (RQ_S_inj a b))).
Qed.

Lemma FOPr_q_succ_nonzero : forall n a,
  FOProvesTn n (FONeg (FOEq (FOSucc a) FOZero)).
Proof.
  intros n a. exact (FOProvesTn_ax n _ (FOAx_RQ n _ (RQ_S_nonzero a))).
Qed.

Lemma FOPr_q_plus_zero : forall n a,
  FOProvesTn n (FOEq (FOPlus a FOZero) a).
Proof.
  intros n a. exact (FOProvesTn_ax n _ (FOAx_RQ n _ (RQ_plus_zero a))).
Qed.

Lemma FOPr_q_plus_succ : forall n a b,
  FOProvesTn n (FOEq (FOPlus a (FOSucc b)) (FOSucc (FOPlus a b))).
Proof.
  intros n a b. exact (FOProvesTn_ax n _ (FOAx_RQ n _ (RQ_plus_succ a b))).
Qed.

Lemma FOPr_q_mult_zero : forall n a,
  FOProvesTn n (FOEq (FOMult a FOZero) FOZero).
Proof.
  intros n a. exact (FOProvesTn_ax n _ (FOAx_RQ n _ (RQ_mult_zero a))).
Qed.

Lemma FOPr_q_mult_succ : forall n a b,
  FOProvesTn n (FOEq (FOMult a (FOSucc b)) (FOPlus (FOMult a b) a)).
Proof.
  intros n a b. exact (FOProvesTn_ax n _ (FOAx_RQ n _ (RQ_mult_succ a b))).
Qed.

Lemma FOPr_succ_nonzero : forall n k,
  FOProvesTn n (FONeg (FOEq (FOSucc (FOnumeral k)) FOZero)).
Proof.
  intros n k. exact (FOPr_q_succ_nonzero n (FOnumeral k)).
Qed.

Lemma FOPr_succ_inj : forall n a b,
  FOProvesTn n (FOImplF (FOEq (FOSucc (FOnumeral a)) (FOSucc (FOnumeral b)))
                        (FOEq (FOnumeral a) (FOnumeral b))).
Proof.
  intros n a b. exact (FOPr_q_succ_inj n (FOnumeral a) (FOnumeral b)).
Qed.

Lemma FOPr_plus_zero : forall n a,
  FOProvesTn n (FOEq (FOPlus (FOnumeral a) FOZero) (FOnumeral a)).
Proof.
  intros n a. exact (FOPr_q_plus_zero n (FOnumeral a)).
Qed.

Lemma FOPr_plus_succ : forall n a b,
  FOProvesTn n (FOEq (FOPlus (FOnumeral a) (FOSucc (FOnumeral b)))
                     (FOSucc (FOPlus (FOnumeral a) (FOnumeral b)))).
Proof.
  intros n a b. exact (FOPr_q_plus_succ n (FOnumeral a) (FOnumeral b)).
Qed.

Lemma FOPr_mult_zero : forall n a,
  FOProvesTn n (FOEq (FOMult (FOnumeral a) FOZero) FOZero).
Proof.
  intros n a. exact (FOPr_q_mult_zero n (FOnumeral a)).
Qed.

Lemma FOPr_mult_succ : forall n a b,
  FOProvesTn n (FOEq (FOMult (FOnumeral a) (FOSucc (FOnumeral b)))
                     (FOPlus (FOMult (FOnumeral a) (FOnumeral b)) (FOnumeral a))).
Proof.
  intros n a b. exact (FOPr_q_mult_succ n (FOnumeral a) (FOnumeral b)).
Qed.

(** Numeral addition and multiplication are provable. *)

Lemma FOPr_add_numerals : forall n a b,
  FOProvesTn n (FOEq (FOPlus (FOnumeral a) (FOnumeral b)) (FOnumeral (a + b))).
Proof.
  intros n a b. induction b as [|b IH].
  - rewrite Nat.add_0_r. exact (FOPr_plus_zero n a).
  - cbn [FOnumeral]. rewrite Nat.add_succ_r. cbn [FOnumeral].
    pose proof (FOPr_plus_succ n a b) as Hps.
    pose proof (FOProvesTn_MP n _ _ (FOProvesTn_CongS n _ _) IH) as Hcong.
    exact (FOPr_mp2 n _ _ _ (FOProvesTn_EqTrans n _ _ _) Hps Hcong).
Qed.

Lemma FOPr_mul_numerals : forall n a b,
  FOProvesTn n (FOEq (FOMult (FOnumeral a) (FOnumeral b)) (FOnumeral (a * b))).
Proof.
  intros n a b. induction b as [|b IH].
  - rewrite Nat.mul_0_r. exact (FOPr_mult_zero n a).
  - cbn [FOnumeral]. rewrite Nat.mul_succ_r.
    pose proof (FOPr_mult_succ n a b) as Hms.
    pose proof (FOPr_mp2 n _ _ _ (FOProvesTn_CongPlus n _ _ _ _) IH
                  (FOProvesTn_EqRefl n (FOnumeral a))) as Hcong.
    pose proof (FOPr_add_numerals n (a * b) a) as Hadd.
    pose proof (FOPr_mp2 n _ _ _ (FOProvesTn_EqTrans n _ _ _) Hcong Hadd)
      as Htrans1.
    exact (FOPr_mp2 n _ _ _ (FOProvesTn_EqTrans n _ _ _) Hms Htrans1).
Qed.

(** Distinct numerals are provably distinct. *)

Lemma FOPr_num_neq : forall n a b,
  a <> b ->
  FOProvesTn n (FONeg (FOEq (FOnumeral a) (FOnumeral b))).
Proof.
  intros n a. induction a as [|a IH]; intros b Hne; destruct b as [|b].
  - exfalso. apply Hne. reflexivity.
  - cbn [FOnumeral].
    pose proof (FOPr_succ_nonzero n b) as Hnz.
    pose proof (FOProvesTn_EqSym n FOZero (FOSucc (FOnumeral b))) as Hsym.
    exact (FOPr_compose n _ _ _ Hsym Hnz).
  - cbn [FOnumeral]. exact (FOPr_succ_nonzero n a).
  - cbn [FOnumeral].
    assert (Hne' : a <> b) by (intro; apply Hne; f_equal; assumption).
    pose proof (FOPr_succ_inj n a b) as Hinj.
    pose proof (IH b Hne') as Hihb.
    exact (FOPr_compose n _ _ _ Hinj Hihb).
Qed.

(** Closed terms provably evaluate to their numerals. *)

Fixpoint FOclosed_tm (t : FOTerm) : Prop :=
  match t with
  | FOVar _ => False
  | FOZero => True
  | FOSucc a => FOclosed_tm a
  | FOPlus a b => FOclosed_tm a /\ FOclosed_tm b
  | FOMult a b => FOclosed_tm a /\ FOclosed_tm b
  end.

Lemma FOPr_closed_term_eval : forall n t, FOclosed_tm t ->
  FOProvesTn n (FOEq t (FOnumeral (FOeval (fun _ => 0) t))).
Proof.
  intros n t. induction t as [v | | a IHa | a IHa b IHb | a IHa b IHb];
    cbn; intro Hc.
  - contradiction.
  - exact (FOProvesTn_EqRefl n FOZero).
  - pose proof (IHa Hc) as IH.
    exact (FOProvesTn_MP n _ _ (FOProvesTn_CongS n _ _) IH).
  - destruct Hc as [H1 H2].
    pose proof (FOPr_mp2 n _ _ _ (FOProvesTn_CongPlus n _ _ _ _)
                  (IHa H1) (IHb H2)) as Hcong.
    pose proof (FOPr_add_numerals n (FOeval (fun _ => 0) a)
                  (FOeval (fun _ => 0) b)) as Hadd.
    exact (FOPr_mp2 n _ _ _ (FOProvesTn_EqTrans n _ _ _) Hcong Hadd).
  - destruct Hc as [H1 H2].
    pose proof (FOPr_mp2 n _ _ _ (FOProvesTn_CongMult n _ _ _ _)
                  (IHa H1) (IHb H2)) as Hcong.
    pose proof (FOPr_mul_numerals n (FOeval (fun _ => 0) a)
                  (FOeval (fun _ => 0) b)) as Hmul.
    exact (FOPr_mp2 n _ _ _ (FOProvesTn_EqTrans n _ _ _) Hcong Hmul).
Qed.

(** Closed equations are provably decided by their truth value. *)

Lemma FOPr_closed_eq_true : forall n a b,
  FOclosed_tm a -> FOclosed_tm b ->
  FOeval (fun _ => 0) a = FOeval (fun _ => 0) b ->
  FOProvesTn n (FOEq a b).
Proof.
  intros n a b Hca Hcb Heq.
  pose proof (FOPr_closed_term_eval n a Hca) as Ta.
  pose proof (FOPr_closed_term_eval n b Hcb) as Tb.
  rewrite Heq in Ta.
  pose proof (FOProvesTn_MP n _ _ (FOProvesTn_EqSym n _ _) Tb) as Tb'.
  exact (FOPr_mp2 n _ _ _ (FOProvesTn_EqTrans n _ _ _) Ta Tb').
Qed.

Lemma FOPr_closed_eq_false : forall n a b,
  FOclosed_tm a -> FOclosed_tm b ->
  FOeval (fun _ => 0) a <> FOeval (fun _ => 0) b ->
  FOProvesTn n (FONeg (FOEq a b)).
Proof.
  intros n a b Hca Hcb Hne.
  pose proof (FOPr_closed_term_eval n a Hca) as Ta.
  pose proof (FOPr_closed_term_eval n b Hcb) as Tb.
  pose proof (FOProvesTn_MP n _ _ (FOProvesTn_EqSym n _ _) Ta) as Ta'.
  pose proof (FOProvesTn_MP n _ _
    (FOProvesTn_EqTrans n (FOnumeral (FOeval (fun _ => 0) a)) a b) Ta') as S1.
  pose proof (FOPr_swap_mp n _ _ _
    (FOProvesTn_EqTrans n (FOnumeral (FOeval (fun _ => 0) a)) b
       (FOnumeral (FOeval (fun _ => 0) b))) Tb) as S2.
  pose proof (FOPr_compose n _ _ _ S1 S2) as S3.
  pose proof (FOPr_num_neq n _ _ Hne) as Hnn.
  exact (FOPr_compose n _ _ _ S3 Hnn).
Qed.

(** ** Leibniz substitution of provable equals. *)

Lemma FOPr_tm_leibniz : forall n x s t a,
  FOProvesTn n (FOImplF (FOEq s t)
                        (FOEq (FOsubst_t x s a) (FOsubst_t x t a))).
Proof.
  intros n x s t a.
  induction a as [y | | a IH | a IHa b IHb | a IHa b IHb]; cbn.
  - destruct (Nat.eqb y x).
    + exact (FOPr_idf n (FOEq s t)).
    + exact (FOPr_weaken n _ _ (FOProvesTn_EqRefl n (FOVar y))).
  - exact (FOPr_weaken n _ _ (FOProvesTn_EqRefl n FOZero)).
  - exact (FOPr_compose n _ _ _ IH (FOProvesTn_CongS n _ _)).
  - exact (FOPr_under_mp n _ _ _
            (FOPr_compose n _ _ _ IHa (FOProvesTn_CongPlus n _ _ _ _)) IHb).
  - exact (FOPr_under_mp n _ _ _
            (FOPr_compose n _ _ _ IHa (FOProvesTn_CongMult n _ _ _ _)) IHb).
Qed.

Lemma FOPr_f_leibniz : forall A n x s t,
  FOsubst_ok x s A = true -> FOsubst_ok x t A = true ->
  FOProvesTn n (FOImplF (FOEq s t)
                  (FOImplF (FOsubst_f x s A) (FOsubst_f x t A))).
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB];
    intros n x s t Hoks Hokt; cbn.
  - pose proof (FOPr_tm_leibniz n x s t a) as La.
    pose proof (FOPr_tm_leibniz n x s t b) as Lb.
    pose proof (FOPr_compose n _ _ _ La
                  (FOProvesTn_EqSym n (FOsubst_t x s a) (FOsubst_t x t a)))
      as U1.
    pose proof (FOPr_compose n _ _ _ U1
                  (FOProvesTn_EqTrans n (FOsubst_t x t a) (FOsubst_t x s a)
                     (FOsubst_t x s b))) as U2.
    pose proof (FOProvesTn_MP n _ _
                  (FOPr_imp_swap n _ _ _)
                  (FOProvesTn_EqTrans n (FOsubst_t x t a) (FOsubst_t x s b)
                     (FOsubst_t x t b))) as SW.
    pose proof (FOPr_compose n _ _ _ Lb SW) as U3.
    pose proof (FOPr_compose n _ _ _ U2
                  (FOPr_syl n (FOEq (FOsubst_t x s a) (FOsubst_t x s b))
                     (FOEq (FOsubst_t x t a) (FOsubst_t x s b))
                     (FOEq (FOsubst_t x t a) (FOsubst_t x t b)))) as U4.
    exact (FOPr_under_mp n _ _ _ U4 U3).
  - exact (FOPr_weaken n _ _ (FOPr_idf n FOFalseF)).
  - cbn in Hoks, Hokt.
    apply Bool.andb_true_iff in Hoks. destruct Hoks as [HsB HsC].
    apply Bool.andb_true_iff in Hokt. destruct Hokt as [HtB HtC].
    pose proof (FOPr_compose n _ _ _ (FOProvesTn_EqSym n s t)
                  (IHB n x t s HtB HsB)) as VB.
    pose proof (IHC n x s t HsC HtC) as VC.
    pose proof (FOPr_compose n _ _ _ VB
                  (FOPr_horizontal n (FOsubst_f x t B) (FOsubst_f x s B)
                     (FOsubst_f x s C) (FOsubst_f x t C))) as W1.
    exact (FOPr_under_mp n _ _ _ W1 VC).
  - cbn in Hoks, Hokt.
    destruct (Nat.eqb y x) eqn:E.
    + exact (FOPr_weaken n _ _ (FOPr_idf n (FOForall y B))).
    + destruct (FOfree_in x B) eqn:EF.
      * apply Bool.andb_true_iff in Hoks. destruct Hoks as [Hys HokBs].
        apply Bool.andb_true_iff in Hokt. destruct Hokt as [Hyt HokBt].
        apply Bool.negb_true_iff in Hys. apply Bool.negb_true_iff in Hyt.
        pose proof (FOProvesTn_Gen n y _ (IHB n x s t HokBs HokBt)) as G.
        assert (Hfree : FOfree_in y (FOEq s t) = false).
        { cbn. rewrite Hys, Hyt. reflexivity. }
        pose proof (FOProvesTn_MP n _ _
                      (FOProvesTn_AllExport n y (FOEq s t)
                         (FOImplF (FOsubst_f x s B) (FOsubst_f x t B)) Hfree)
                      G) as E1.
        exact (FOPr_compose n _ _ _ E1
                 (FOProvesTn_AllK n y (FOsubst_f x s B) (FOsubst_f x t B))).
      * rewrite (FOsubst_f_not_free B x s EF), (FOsubst_f_not_free B x t EF).
        exact (FOPr_weaken n _ _ (FOPr_idf n (FOForall y B))).
  - cbn in Hoks, Hokt.
    destruct (Nat.eqb y x) eqn:E.
    + exact (FOPr_weaken n _ _ (FOPr_idf n (FOExists y B))).
    + destruct (FOfree_in x B) eqn:EF.
      * apply Bool.andb_true_iff in Hoks. destruct Hoks as [Hys HokBs].
        apply Bool.andb_true_iff in Hokt. destruct Hokt as [Hyt HokBt].
        apply Bool.negb_true_iff in Hys. apply Bool.negb_true_iff in Hyt.
        pose proof (IHB n x s t HokBs HokBt) as IH1.
        pose proof (FOProvesTn_ExIntroT n y (FOVar y) (FOsubst_f x t B)
                      (FOsubst_ok_var_self (FOsubst_f x t B) y)) as EX0.
        rewrite (FOsubst_f_id (FOsubst_f x t B) y) in EX0.
        pose proof (FOPr_compose n _ _ _ IH1
                      (FOPr_syl n (FOsubst_f x s B) (FOsubst_f x t B)
                         (FOExists y (FOsubst_f x t B)))) as U1.
        pose proof (FOPr_under_mp n _ _ _ U1
                      (FOPr_weaken n _ _ EX0)) as P.
        pose proof (FOProvesTn_Gen n y _ P) as G.
        assert (Hfree : FOfree_in y (FOEq s t) = false).
        { cbn. rewrite Hys, Hyt. reflexivity. }
        pose proof (FOProvesTn_MP n _ _
                      (FOProvesTn_AllExport n y (FOEq s t)
                         (FOImplF (FOsubst_f x s B)
                            (FOExists y (FOsubst_f x t B))) Hfree) G) as E1.
        assert (Hfree2 : FOfree_in y (FOExists y (FOsubst_f x t B)) = false).
        { cbn. rewrite Nat.eqb_refl. reflexivity. }
        exact (FOPr_compose n _ _ _ E1
                 (FOProvesTn_ExElim n y (FOsubst_f x s B)
                    (FOExists y (FOsubst_f x t B)) Hfree2)).
      * rewrite (FOsubst_f_not_free B x s EF), (FOsubst_f_not_free B x t EF).
        exact (FOPr_weaken n _ _ (FOPr_idf n (FOExists y B))).
Qed.

(** ** Internal facts about the order relation at numerals.

    [FOLtF (FOVar v) t] has witness variable [S v] whenever [t] is
    closed, so the bounded quantifier [FOBall v t A] keeps one
    canonical binder throughout. *)

Lemma FOclosed_numeral : forall m, FOclosed_tm (FOnumeral m).
Proof. induction m as [|m IH]; cbn; [exact I | exact IH]. Qed.

Lemma FOmax_var_numeral : forall k, FOmax_var_tm (FOnumeral k) = 0.
Proof. induction k as [|k IH]; cbn; [reflexivity | exact IH]. Qed.

Lemma FOmax_var_closed : forall t, FOclosed_tm t -> FOmax_var_tm t = 0.
Proof.
  induction t; cbn; intro Hc.
  - contradiction.
  - reflexivity.
  - exact (IHt Hc).
  - destruct Hc as [H1 H2]. rewrite (IHt1 H1), (IHt2 H2). reflexivity.
  - destruct Hc as [H1 H2]. rewrite (IHt1 H1), (IHt2 H2). reflexivity.
Qed.

Lemma FOLtF_var_num : forall v k,
  FOLtF (FOVar v) (FOnumeral k)
  = FOExists (S v)
      (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) (FOnumeral k)).
Proof.
  intros v k. unfold FOLtF. cbn [FOmax_var_tm].
  rewrite FOmax_var_numeral, Nat.max_0_r. reflexivity.
Qed.

Lemma FOLtF_var_closed : forall v t,
  FOclosed_tm t ->
  FOLtF (FOVar v) t
  = FOExists (S v) (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) t).
Proof.
  intros v t Hc. unfold FOLtF. cbn [FOmax_var_tm].
  rewrite (FOmax_var_closed t Hc), Nat.max_0_r. reflexivity.
Qed.

Lemma FOLtF_num_num : forall i k,
  FOLtF (FOnumeral i) (FOnumeral k)
  = FOExists 1
      (FOEq (FOPlus (FOnumeral i) (FOSucc (FOVar 1))) (FOnumeral k)).
Proof.
  intros i k. unfold FOLtF. rewrite !FOmax_var_numeral. reflexivity.
Qed.

Lemma FOPr_absorb2 : forall n X M Y H,
  FOProvesTn n (FOImplF (FOImplF X (FOImplF M Y))
                  (FOImplF (FOImplF H M)
                     (FOImplF X (FOImplF H Y)))).
Proof.
  intros n X M Y H.
  apply (FOPr_taut n (FOm4 X M Y H)
    (Impl (Impl (Var 0) (Impl (Var 1) (Var 2)))
          (Impl (Impl (Var 3) (Var 1))
                (Impl (Var 0) (Impl (Var 3) (Var 2))))));
    [cbn; tauto | reflexivity].
Qed.

Lemma FOPr_compose2 : forall n X H Y Z,
  FOProvesTn n (FOImplF (FOImplF X (FOImplF H Y))
                  (FOImplF (FOImplF Y Z)
                     (FOImplF X (FOImplF H Z)))).
Proof.
  intros n X H Y Z.
  apply (FOPr_taut n (FOm4 X H Y Z)
    (Impl (Impl (Var 0) (Impl (Var 1) (Var 2)))
          (Impl (Impl (Var 2) (Var 3))
                (Impl (Var 0) (Impl (Var 1) (Var 3))))));
    [cbn; tauto | reflexivity].
Qed.

Lemma FOPr_not_lt_zero : forall n u,
  FOProvesTn n (FONeg (FOLtF u FOZero)).
Proof.
  intros n u. unfold FOLtF.
  apply (FOProvesTn_MP n _ _ (FOProvesTn_AllNegToNegEx n _ _)).
  apply FOProvesTn_Gen.
  pose proof (FOPr_q_plus_succ n u
                (FOVar (S (Nat.max (FOmax_var_tm u) (FOmax_var_tm FOZero)))))
    as Hps.
  pose proof (FOProvesTn_MP n _ _
                (FOProvesTn_EqSym n
                   (FOPlus u (FOSucc (FOVar (S (Nat.max (FOmax_var_tm u)
                                                 (FOmax_var_tm FOZero))))))
                   (FOSucc (FOPlus u (FOVar (S (Nat.max (FOmax_var_tm u)
                                                 (FOmax_var_tm FOZero)))))))
                Hps) as Hps'.
  pose proof (FOProvesTn_MP n _ _
                (FOProvesTn_EqTrans n
                   (FOSucc (FOPlus u (FOVar (S (Nat.max (FOmax_var_tm u)
                                                 (FOmax_var_tm FOZero))))))
                   (FOPlus u (FOSucc (FOVar (S (Nat.max (FOmax_var_tm u)
                                                 (FOmax_var_tm FOZero))))))
                   FOZero) Hps') as Himp.
  exact (FOPr_compose n _ _ _ Himp
           (FOPr_q_succ_nonzero n
              (FOPlus u (FOVar (S (Nat.max (FOmax_var_tm u)
                                     (FOmax_var_tm FOZero))))))).
Qed.

Lemma FOPr_ex_mono : forall n w phi psi,
  FOProvesTn n (FOForall w (FOImplF phi psi)) ->
  FOProvesTn n (FOImplF (FOExists w phi) (FOExists w psi)).
Proof.
  intros n w phi psi Hall.
  pose proof (FOProvesTn_ExIntroT n w (FOVar w) psi
                (FOsubst_ok_var_self psi w)) as EX0.
  rewrite (FOsubst_f_id psi w) in EX0.
  pose proof (FOProvesTn_MP n _ _
                (FOPr_imp_swap n (FOImplF phi psi)
                   (FOImplF psi (FOExists w psi))
                   (FOImplF phi (FOExists w psi)))
                (FOPr_syl n phi psi (FOExists w psi))) as SW.
  pose proof (FOProvesTn_MP n _ _ SW EX0) as PW.
  pose proof (FOProvesTn_Gen n w _ PW) as G.
  pose proof (FOProvesTn_MP n _ _
                (FOProvesTn_AllK n w (FOImplF phi psi)
                   (FOImplF phi (FOExists w psi))) G) as DK.
  pose proof (FOProvesTn_MP n _ _ DK Hall) as G2.
  assert (Hside : FOfree_in w (FOExists w psi) = false).
  { cbn. rewrite Nat.eqb_refl. reflexivity. }
  exact (FOProvesTn_MP n _ _
           (FOProvesTn_ExElim n w phi (FOExists w psi) Hside) G2).
Qed.

Lemma FOPr_lt_bound_to_num : forall n v t,
  FOclosed_tm t ->
  FOProvesTn n (FOImplF (FOLtF (FOVar v) t)
                  (FOLtF (FOVar v) (FOnumeral (FOeval (fun _ => 0) t)))).
Proof.
  intros n v t Hc.
  rewrite (FOLtF_var_closed v t Hc), FOLtF_var_num.
  apply FOPr_ex_mono.
  apply FOProvesTn_Gen.
  pose proof (FOPr_closed_term_eval n t Hc) as Ht.
  exact (FOPr_swap_mp n _ _ _
          (FOProvesTn_EqTrans n
             (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) t
             (FOnumeral (FOeval (fun _ => 0) t))) Ht).
Qed.

Lemma FOPr_lt_num : forall n i k, i < k ->
  FOProvesTn n (FOLtF (FOnumeral i) (FOnumeral k)).
Proof.
  intros n i k Hik. rewrite FOLtF_num_num.
  apply (FOProvesTn_MP n _ _
          (FOProvesTn_ExIntroNum n 1 (k - i - 1)
             (FOEq (FOPlus (FOnumeral i) (FOSucc (FOVar 1)))
                   (FOnumeral k)))).
  cbn [FOsubst_num FOsubst_tm].
  rewrite !FOsubst_tm_numeral.
  apply FOPr_closed_eq_true.
  - cbn. split; [apply FOclosed_numeral | apply FOclosed_numeral].
  - apply FOclosed_numeral.
  - change (FOeval (fun _ => 0) (FOnumeral i)
              + S (FOeval (fun _ => 0) (FOnumeral (k - i - 1)))
            = FOeval (fun _ => 0) (FOnumeral k)).
    rewrite !FOeval_numeral. lia.
Qed.

Lemma FOPr_lt_subst_inst : forall n v i k, i < k ->
  FOProvesTn n (FOsubst_num v i (FOLtF (FOVar v) (FOnumeral k))).
Proof.
  intros n v i k Hik. rewrite FOLtF_var_num.
  assert (ESvv : Nat.eqb (S v) v = false) by (apply Nat.eqb_neq; lia).
  assert (Hs : FOsubst_num v i
      (FOExists (S v)
         (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) (FOnumeral k)))
    = FOExists (S v)
        (FOEq (FOPlus (FOnumeral i) (FOSucc (FOVar (S v)))) (FOnumeral k))).
  { cbn -[Nat.eqb]. rewrite ESvv, Nat.eqb_refl, FOsubst_tm_numeral.
    reflexivity. }
  rewrite Hs.
  apply (FOProvesTn_MP n _ _
          (FOProvesTn_ExIntroNum n (S v) (k - i - 1)
             (FOEq (FOPlus (FOnumeral i) (FOSucc (FOVar (S v))))
                   (FOnumeral k)))).
  assert (Hs2 : FOsubst_num (S v) (k - i - 1)
      (FOEq (FOPlus (FOnumeral i) (FOSucc (FOVar (S v)))) (FOnumeral k))
    = FOEq (FOPlus (FOnumeral i) (FOSucc (FOnumeral (k - i - 1))))
        (FOnumeral k)).
  { cbn -[Nat.eqb]. rewrite Nat.eqb_refl, !FOsubst_tm_numeral.
    reflexivity. }
  rewrite Hs2.
  apply FOPr_closed_eq_true.
  - cbn. split; [apply FOclosed_numeral | apply FOclosed_numeral].
  - apply FOclosed_numeral.
  - change (FOeval (fun _ => 0) (FOnumeral i)
              + S (FOeval (fun _ => 0) (FOnumeral (k - i - 1)))
            = FOeval (fun _ => 0) (FOnumeral k)).
    rewrite !FOeval_numeral. lia.
Qed.

Lemma FOsubst_t_numeral : forall x s m,
  FOsubst_t x s (FOnumeral m) = FOnumeral m.
Proof.
  intros x s m. induction m as [|m IH]; cbn;
    [reflexivity | rewrite IH; reflexivity].
Qed.

(** The case split below a successor numeral bound: anything below
    [S k] is below [k] or equal to [k], provably. *)

Lemma FOPr_lt_succ_cases : forall n v k,
  FOProvesTn n (FOImplF (FOLtF (FOVar v) (FOnumeral (S k)))
                  (FOOr (FOLtF (FOVar v) (FOnumeral k))
                        (FOEq (FOVar v) (FOnumeral k)))).
Proof.
  intros n v k.
  rewrite !FOLtF_var_num.
  assert (E1 : Nat.eqb v (S v) = false) by (apply Nat.eqb_neq; lia).
  assert (E2 : Nat.eqb v (S (S v)) = false) by (apply Nat.eqb_neq; lia).
  assert (E3 : Nat.eqb (S v) (S (S v)) = false) by (apply Nat.eqb_neq; lia).
  assert (Hside1 : FOfree_in (S v)
      (FOOr (FOExists (S v)
               (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) (FOnumeral k)))
            (FOEq (FOVar v) (FOnumeral k))) = false).
  { cbn -[Nat.eqb]. rewrite Nat.eqb_refl, E1, !FOin_tm_numeral. reflexivity. }
  apply (FOProvesTn_MP n _ _
          (FOProvesTn_ExElim n (S v)
             (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) (FOnumeral (S k)))
             (FOOr (FOExists (S v)
                      (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                            (FOnumeral k)))
                   (FOEq (FOVar v) (FOnumeral k))) Hside1)).
  apply FOProvesTn_Gen.
  pose proof (FOPr_q_plus_succ n (FOVar v) (FOVar (S v))) as P1.
  pose proof (FOProvesTn_MP n _ _
                (FOProvesTn_EqSym n
                   (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                   (FOSucc (FOPlus (FOVar v) (FOVar (S v))))) P1) as P1'.
  pose proof (FOProvesTn_MP n _ _
                (FOProvesTn_EqTrans n
                   (FOSucc (FOPlus (FOVar v) (FOVar (S v))))
                   (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                   (FOnumeral (S k))) P1') as U1.
  pose proof (FOPr_compose n _ _ _ U1
                (FOPr_q_succ_inj n (FOPlus (FOVar v) (FOVar (S v)))
                   (FOnumeral k))) as U2.
  pose proof (FOProvesTn_MP n _ _
                (FOProvesTn_CongPlus n (FOVar v) (FOVar v) (FOVar (S v))
                   FOZero)
                (FOProvesTn_EqRefl n (FOVar v))) as Z1.
  pose proof (FOPr_swap_mp n _ _ _
                (FOProvesTn_EqTrans n
                   (FOPlus (FOVar v) (FOVar (S v)))
                   (FOPlus (FOVar v) FOZero) (FOVar v))
                (FOPr_q_plus_zero n (FOVar v))) as Z2.
  pose proof (FOPr_compose n _ _ _ Z1 Z2) as Z3.
  pose proof (FOPr_compose n _ _ _ Z3
                (FOProvesTn_EqSym n (FOPlus (FOVar v) (FOVar (S v)))
                   (FOVar v))) as Z4.
  pose proof (FOPr_compose n _ _ _ Z4
                (FOProvesTn_EqTrans n (FOVar v)
                   (FOPlus (FOVar v) (FOVar (S v))) (FOnumeral k))) as Z5.
  pose proof (FOPr_mp2 n _ _ _
                (FOPr_absorb2 n (FOEq (FOVar (S v)) FOZero)
                   (FOEq (FOPlus (FOVar v) (FOVar (S v))) (FOnumeral k))
                   (FOEq (FOVar v) (FOnumeral k))
                   (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                         (FOnumeral (S k))))
                Z5 U2) as Z6.
  pose proof (FOPr_mp2 n _ _ _
                (FOPr_compose2 n (FOEq (FOVar (S v)) FOZero)
                   (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                         (FOnumeral (S k)))
                   (FOEq (FOVar v) (FOnumeral k))
                   (FOOr (FOExists (S v)
                            (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                                  (FOnumeral k)))
                         (FOEq (FOVar v) (FOnumeral k))))
                Z6
                (FOPr_or_intro_r n
                   (FOExists (S v)
                      (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                            (FOnumeral k)))
                   (FOEq (FOVar v) (FOnumeral k)))) as BZ.
  assert (Hsub : FOsubst_f (S v) (FOVar (S (S v)))
      (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) (FOnumeral k))
    = FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S (S v))))) (FOnumeral k)).
  { cbn -[Nat.eqb]. rewrite E1, Nat.eqb_refl, FOsubst_t_numeral.
    reflexivity. }
  pose proof (FOProvesTn_ExIntroT n (S v) (FOVar (S (S v)))
                (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                      (FOnumeral k)) eq_refl) as EXI.
  rewrite Hsub in EXI.
  pose proof (FOPr_compose n _ _ _ EXI
                (FOPr_or_intro_l n
                   (FOExists (S v)
                      (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                            (FOnumeral k)))
                   (FOEq (FOVar v) (FOnumeral k)))) as LF.
  pose proof (FOProvesTn_MP n _ _
                (FOProvesTn_CongPlus n (FOVar v) (FOVar v) (FOVar (S v))
                   (FOSucc (FOVar (S (S v)))))
                (FOProvesTn_EqRefl n (FOVar v))) as S1.
  pose proof (FOPr_swap_mp n _ _ _
                (FOProvesTn_EqTrans n
                   (FOPlus (FOVar v) (FOVar (S v)))
                   (FOPlus (FOVar v) (FOSucc (FOVar (S (S v)))))
                   (FOSucc (FOPlus (FOVar v) (FOVar (S (S v))))))
                (FOPr_q_plus_succ n (FOVar v) (FOVar (S (S v))))) as S2.
  pose proof (FOPr_compose n _ _ _ S1 S2) as S3.
  pose proof (FOPr_compose n _ _ _ S3
                (FOProvesTn_EqSym n (FOPlus (FOVar v) (FOVar (S v)))
                   (FOSucc (FOPlus (FOVar v) (FOVar (S (S v))))))) as S4.
  pose proof (FOPr_compose n _ _ _ S4
                (FOProvesTn_EqTrans n
                   (FOSucc (FOPlus (FOVar v) (FOVar (S (S v)))))
                   (FOPlus (FOVar v) (FOVar (S v)))
                   (FOnumeral k))) as S5.
  pose proof (FOPr_mp2 n _ _ _
                (FOPr_absorb2 n
                   (FOEq (FOVar (S v)) (FOSucc (FOVar (S (S v)))))
                   (FOEq (FOPlus (FOVar v) (FOVar (S v))) (FOnumeral k))
                   (FOEq (FOSucc (FOPlus (FOVar v) (FOVar (S (S v)))))
                         (FOnumeral k))
                   (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                         (FOnumeral (S k))))
                S5 U2) as S6.
  pose proof (FOProvesTn_MP n _ _
                (FOProvesTn_EqTrans n
                   (FOPlus (FOVar v) (FOSucc (FOVar (S (S v)))))
                   (FOSucc (FOPlus (FOVar v) (FOVar (S (S v)))))
                   (FOnumeral k))
                (FOPr_q_plus_succ n (FOVar v) (FOVar (S (S v))))) as CONV.
  pose proof (FOPr_mp2 n _ _ _
                (FOPr_compose2 n
                   (FOEq (FOVar (S v)) (FOSucc (FOVar (S (S v)))))
                   (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                         (FOnumeral (S k)))
                   (FOEq (FOSucc (FOPlus (FOVar v) (FOVar (S (S v)))))
                         (FOnumeral k))
                   (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S (S v)))))
                         (FOnumeral k)))
                S6 CONV) as S7.
  pose proof (FOPr_mp2 n _ _ _
                (FOPr_compose2 n
                   (FOEq (FOVar (S v)) (FOSucc (FOVar (S (S v)))))
                   (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                         (FOnumeral (S k)))
                   (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S (S v)))))
                         (FOnumeral k))
                   (FOOr (FOExists (S v)
                            (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                                  (FOnumeral k)))
                         (FOEq (FOVar v) (FOnumeral k))))
                S7 LF) as CORE2.
  pose proof (FOProvesTn_Gen n (S (S v)) _ CORE2) as G2.
  assert (Hside2 : FOfree_in (S (S v))
      (FOImplF (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                     (FOnumeral (S k)))
               (FOOr (FOExists (S v)
                        (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                              (FOnumeral k)))
                     (FOEq (FOVar v) (FOnumeral k)))) = false).
  { cbn -[Nat.eqb]. rewrite E2, E3, !FOin_tm_numeral. reflexivity. }
  pose proof (FOProvesTn_MP n _ _
                (FOProvesTn_ExElim n (S (S v))
                   (FOEq (FOVar (S v)) (FOSucc (FOVar (S (S v)))))
                   (FOImplF (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                                  (FOnumeral (S k)))
                            (FOOr (FOExists (S v)
                                     (FOEq (FOPlus (FOVar v)
                                              (FOSucc (FOVar (S v))))
                                           (FOnumeral k)))
                                  (FOEq (FOVar v) (FOnumeral k)))) Hside2)
                G2) as BS.
  pose proof (FOProvesTn_ax n _
                (FOAx_RQ n _ (RQ_zero_or_succ (S v)))) as ORAX.
  exact (FOPr_case n (FOEq (FOVar (S v)) FOZero)
           (FOExists (S (S v))
              (FOEq (FOVar (S v)) (FOSucc (FOVar (S (S v))))))
           (FOImplF (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                          (FOnumeral (S k)))
                    (FOOr (FOExists (S v)
                             (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                                   (FOnumeral k)))
                          (FOEq (FOVar v) (FOnumeral k))))
           ORAX BZ BS).
Qed.

(** The bounded universal quantifier, with introduction from its
    finitely many numeral instances and refutation from one failing
    instance. *)

Definition FOBall (v : nat) (t : FOTerm) (A : FOFormula) : FOFormula :=
  FOForall v (FOImplF (FOLtF (FOVar v) t) A).

Lemma FOPr_ball_intro_num : forall n v k A,
  (forall i, i < k -> FOProvesTn n (FOsubst_num v i A)) ->
  FOProvesTn n (FOBall v (FOnumeral k) A).
Proof.
  intros n v k A. induction k as [|k IH]; intros Hinst.
  - unfold FOBall. apply FOProvesTn_Gen.
    exact (FOPr_compose n _ _ _ (FOPr_not_lt_zero n (FOVar v))
             (FOPr_efq n A)).
  - unfold FOBall. apply FOProvesTn_Gen.
    pose proof (IH (fun i Hi => Hinst i (Nat.lt_lt_succ_r i k Hi))) as IHb.
    pose proof (FOProvesTn_AllElimT n v (FOVar v)
                  (FOImplF (FOLtF (FOVar v) (FOnumeral k)) A)
                  (FOsubst_ok_var_self
                     (FOImplF (FOLtF (FOVar v) (FOnumeral k)) A) v)) as AE.
    rewrite (FOsubst_f_id (FOImplF (FOLtF (FOVar v) (FOnumeral k)) A) v)
      in AE.
    pose proof (FOProvesTn_MP n _ _ AE IHb) as Blt.
    pose proof (Hinst k (Nat.lt_succ_diag_r k)) as Hk.
    pose proof (FOPr_f_leibniz A n v (FOnumeral k) (FOVar v)
                  (FOsubst_ok_numeral A v k) (FOsubst_ok_var_self A v)) as LB.
    rewrite (FOsubst_f_id A v) in LB.
    rewrite (FOsubst_f_num A v k) in LB.
    pose proof (FOPr_compose n _ _ _
                  (FOProvesTn_EqSym n (FOVar v) (FOnumeral k)) LB) as LB'.
    pose proof (FOPr_swap_mp n _ _ _ LB' Hk) as Beq.
    pose proof (FOPr_lt_succ_cases n v k) as CS.
    pose proof (FOPr_or_elim n (FOLtF (FOVar v) (FOnumeral k))
                  (FOEq (FOVar v) (FOnumeral k)) A) as OE.
    exact (FOPr_compose n _ _ _ CS
            (FOProvesTn_MP n _ _ (FOProvesTn_MP n _ _ OE Blt) Beq)).
Qed.

Lemma FOPr_ball_refute_num : forall n v k A i,
  i < k ->
  FOProvesTn n (FONeg (FOsubst_num v i A)) ->
  FOProvesTn n (FONeg (FOBall v (FOnumeral k) A)).
Proof.
  intros n v k A i Hik Hneg.
  pose proof (FOProvesTn_AllElimNum n v i
                (FOImplF (FOLtF (FOVar v) (FOnumeral k)) A)) as AE.
  cbn [FOsubst_num] in AE.
  pose proof (FOPr_lt_subst_inst n v i k Hik) as Hlt.
  pose proof (FOPr_swap_mp n _ _ _ AE Hlt) as T2.
  exact (FOPr_compose n _ _ _ T2 Hneg).
Qed.

(** Substituted canonical bounds: the equation, the provable instance,
    and the conversion of a closed bound to its numeral. *)

Lemma FOclosed_in_false : forall t w,
  FOclosed_tm t -> FOin_tm w t = false.
Proof.
  induction t; cbn; intros w Hc.
  - contradiction.
  - reflexivity.
  - exact (IHt w Hc).
  - rewrite (IHt1 w (proj1 Hc)), (IHt2 w (proj2 Hc)). reflexivity.
  - rewrite (IHt1 w (proj1 Hc)), (IHt2 w (proj2 Hc)). reflexivity.
Qed.

Lemma FOin_all_false_closed : forall t,
  (forall w, FOin_tm w t = false) -> FOclosed_tm t.
Proof.
  induction t; cbn; intro H.
  - specialize (H n). rewrite Nat.eqb_refl in H. discriminate.
  - exact I.
  - apply IHt. intro w. exact (H w).
  - split.
    + apply IHt1. intro w.
      exact (proj1 (proj1 (Bool.orb_false_iff _ _) (H w))).
    + apply IHt2. intro w.
      exact (proj2 (proj1 (Bool.orb_false_iff _ _) (H w))).
  - split.
    + apply IHt1. intro w.
      exact (proj1 (proj1 (Bool.orb_false_iff _ _) (H w))).
    + apply IHt2. intro w.
      exact (proj2 (proj1 (Bool.orb_false_iff _ _) (H w))).
Qed.

Lemma FOsubst_tm_closed : forall t x k,
  FOclosed_tm t -> FOsubst_tm x k t = t.
Proof.
  intros t x k Hc. rewrite <- (FOsubst_t_num t x k).
  apply FOsubst_t_not_in. apply FOclosed_in_false. exact Hc.
Qed.

Lemma FOsubst_num_clt : forall v w0 t,
  FOclosed_tm t ->
  FOsubst_num v w0
    (FOExists (S v) (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) t))
  = FOExists (S v)
      (FOEq (FOPlus (FOnumeral w0) (FOSucc (FOVar (S v)))) t).
Proof.
  intros v w0 t Hct.
  assert (ESvv : Nat.eqb (S v) v = false) by (apply Nat.eqb_neq; lia).
  cbn -[Nat.eqb].
  rewrite ESvv, Nat.eqb_refl, (FOsubst_tm_closed t v w0 Hct).
  reflexivity.
Qed.

Lemma FOPr_clt_inst : forall n v w0 t,
  FOclosed_tm t -> w0 < FOeval (fun _ => 0) t ->
  FOProvesTn n
    (FOExists (S v)
       (FOEq (FOPlus (FOnumeral w0) (FOSucc (FOVar (S v)))) t)).
Proof.
  intros n v w0 t Hct Hwk.
  apply (FOProvesTn_MP n _ _
          (FOProvesTn_ExIntroNum n (S v)
             (FOeval (fun _ => 0) t - w0 - 1)
             (FOEq (FOPlus (FOnumeral w0) (FOSucc (FOVar (S v)))) t))).
  assert (Hse : FOsubst_num (S v) (FOeval (fun _ => 0) t - w0 - 1)
      (FOEq (FOPlus (FOnumeral w0) (FOSucc (FOVar (S v)))) t)
    = FOEq (FOPlus (FOnumeral w0)
             (FOSucc (FOnumeral (FOeval (fun _ => 0) t - w0 - 1)))) t).
  { cbn -[Nat.eqb]. rewrite Nat.eqb_refl, FOsubst_tm_numeral,
      (FOsubst_tm_closed t (S v) _ Hct). reflexivity. }
  rewrite Hse.
  apply FOPr_closed_eq_true.
  - cbn. split; [apply FOclosed_numeral | apply FOclosed_numeral].
  - exact Hct.
  - change (FOeval (fun _ => 0) (FOnumeral w0)
              + S (FOeval (fun _ => 0)
                     (FOnumeral (FOeval (fun _ => 0) t - w0 - 1)))
            = FOeval (fun _ => 0) t).
    rewrite !FOeval_numeral. lia.
Qed.

Lemma FOPr_clt_conv : forall n v t,
  FOclosed_tm t ->
  FOProvesTn n
    (FOImplF
       (FOExists (S v)
          (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) t))
       (FOExists (S v)
          (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                (FOnumeral (FOeval (fun _ => 0) t))))).
Proof.
  intros n v t Hct.
  apply FOPr_ex_mono.
  apply FOProvesTn_Gen.
  pose proof (FOPr_closed_term_eval n t Hct) as Ht.
  exact (FOPr_swap_mp n _ _ _
          (FOProvesTn_EqTrans n
             (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) t
             (FOnumeral (FOeval (fun _ => 0) t))) Ht).
Qed.

(** ** The Sigma_1 class and its completeness over the T_n tower.

    [FOdelta0] is built from equations, falsity, implication, and the
    canonical bounded universal quantifier with binder [v] and witness
    variable [S v], neither occurring in the bound.  [FOsigma1] closes
    it under existential quantification.  Every closed true Sigma_1
    sentence is provable in every theory of the tower, and every closed
    false Delta_0 sentence is refutable. *)

Fixpoint FOfsize (A : FOFormula) : nat :=
  match A with
  | FOEq _ _ => 1
  | FOFalseF => 1
  | FOImplF B C => S (FOfsize B + FOfsize C)
  | FOForall _ B => S (FOfsize B)
  | FOExists _ B => S (FOfsize B)
  end.

Lemma FOfsize_subst_num : forall A x k,
  FOfsize (FOsubst_num x k A) = FOfsize A.
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB];
    intros x k; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite IHB, IHC. reflexivity.
  - destruct (Nat.eqb y x); cbn; [reflexivity | rewrite IHB; reflexivity].
  - destruct (Nat.eqb y x); cbn; [reflexivity | rewrite IHB; reflexivity].
Qed.

Lemma FOin_tm_subst_num : forall t x k w,
  FOin_tm w (FOsubst_tm x k t)
  = if Nat.eqb w x then false else FOin_tm w t.
Proof.
  induction t as [y | | a IH | a IHa b IHb | a IHa b IHb];
    intros x k w; cbn.
  - destruct (Nat.eqb_spec y x) as [->|Eyx].
    + rewrite FOin_tm_numeral.
      destruct (Nat.eqb_spec w x) as [->|Ewx].
      * reflexivity.
      * destruct (Nat.eqb_spec x w) as [e|e];
          [exfalso; apply Ewx; symmetry; exact e | reflexivity].
    + cbn. destruct (Nat.eqb_spec w x) as [->|Ewx]; [|reflexivity].
      destruct (Nat.eqb_spec y x) as [e|e];
        [exfalso; exact (Eyx e) | reflexivity].
  - destruct (Nat.eqb w x); reflexivity.
  - exact (IH x k w).
  - rewrite IHa, IHb. destruct (Nat.eqb w x); cbn; reflexivity.
  - rewrite IHa, IHb. destruct (Nat.eqb w x); cbn; reflexivity.
Qed.

Lemma FOfree_in_subst_num : forall A x k w,
  FOfree_in w (FOsubst_num x k A)
  = if Nat.eqb w x then false else FOfree_in w A.
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB];
    intros x k w; cbn.
  - rewrite !FOin_tm_subst_num.
    destruct (Nat.eqb w x); cbn; reflexivity.
  - destruct (Nat.eqb w x); reflexivity.
  - rewrite IHB, IHC. destruct (Nat.eqb w x); cbn; reflexivity.
  - destruct (Nat.eqb_spec y x) as [->|Eyx]; cbn.
    + destruct (Nat.eqb_spec x w) as [->|Exw].
      * rewrite Nat.eqb_refl. reflexivity.
      * destruct (Nat.eqb_spec w x) as [e|e];
          [exfalso; apply Exw; symmetry; exact e | reflexivity].
    + rewrite IHB.
      destruct (Nat.eqb_spec y w) as [->|Eyw].
      * destruct (Nat.eqb_spec w x) as [e|e];
          [exfalso; exact (Eyx e) | reflexivity].
      * reflexivity.
  - destruct (Nat.eqb_spec y x) as [->|Eyx]; cbn.
    + destruct (Nat.eqb_spec x w) as [->|Exw].
      * rewrite Nat.eqb_refl. reflexivity.
      * destruct (Nat.eqb_spec w x) as [e|e];
          [exfalso; apply Exw; symmetry; exact e | reflexivity].
    + rewrite IHB.
      destruct (Nat.eqb_spec y w) as [->|Eyw].
      * destruct (Nat.eqb_spec w x) as [e|e];
          [exfalso; exact (Eyx e) | reflexivity].
      * reflexivity.
Qed.

Inductive FOdelta0 : FOFormula -> Prop :=
  | FOd0_eq : forall a b, FOdelta0 (FOEq a b)
  | FOd0_false : FOdelta0 FOFalseF
  | FOd0_impl : forall B C,
      FOdelta0 B -> FOdelta0 C -> FOdelta0 (FOImplF B C)
  | FOd0_ball : forall v t A,
      FOin_tm v t = false -> FOin_tm (S v) t = false ->
      FOdelta0 A ->
      FOdelta0 (FOForall v
        (FOImplF
           (FOExists (S v)
              (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) t))
           A))
  | FOd0_bex : forall v t A,
      FOin_tm v t = false -> FOin_tm (S v) t = false ->
      FOdelta0 A ->
      FOdelta0 (FOExists v
        (FOAnd
           (FOExists (S v)
              (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) t))
           A)).

Inductive FOsigma1 : FOFormula -> Prop :=
  | FOs1_d0 : forall A, FOdelta0 A -> FOsigma1 A
  | FOs1_ex : forall x A, FOsigma1 A -> FOsigma1 (FOExists x A).

Lemma FOdelta0_subst_num : forall A x k,
  FOdelta0 A -> FOdelta0 (FOsubst_num x k A).
Proof.
  intros A x k HD.
  induction HD as [a b | | B C HB IHB HC IHC | v t A' Hvt HSvt HA' IHA'
                   | v t A' Hvt HSvt HA' IHA'].
  - cbn. apply FOd0_eq.
  - cbn. apply FOd0_false.
  - cbn. apply FOd0_impl; assumption.
  - cbn -[Nat.eqb]. destruct (Nat.eqb v x) eqn:Evx.
    + apply FOd0_ball; assumption.
    + destruct (Nat.eqb (S v) x) eqn:ESvx.
      * apply FOd0_ball; assumption.
      * apply FOd0_ball.
        -- rewrite FOin_tm_subst_num.
           destruct (Nat.eqb v x); [reflexivity | exact Hvt].
        -- rewrite FOin_tm_subst_num.
           destruct (Nat.eqb (S v) x); [reflexivity | exact HSvt].
        -- exact IHA'.
  - cbn -[Nat.eqb]. destruct (Nat.eqb v x) eqn:Evx.
    + apply FOd0_bex; assumption.
    + destruct (Nat.eqb (S v) x) eqn:ESvx.
      * apply FOd0_bex; assumption.
      * apply FOd0_bex.
        -- rewrite FOin_tm_subst_num.
           destruct (Nat.eqb v x); [reflexivity | exact Hvt].
        -- rewrite FOin_tm_subst_num.
           destruct (Nat.eqb (S v) x); [reflexivity | exact HSvt].
        -- exact IHA'.
Qed.

Lemma FOsigma1_subst_num : forall A x k,
  FOsigma1 A -> FOsigma1 (FOsubst_num x k A).
Proof.
  intros A x k HS. induction HS as [A' HD | y A' HS IH].
  - apply FOs1_d0. apply FOdelta0_subst_num. exact HD.
  - cbn -[Nat.eqb]. destruct (Nat.eqb y x).
    + apply FOs1_ex. exact HS.
    + apply FOs1_ex. exact IH.
Qed.

Lemma FOdelta0_decided : forall s A,
  FOfsize A <= s -> FOdelta0 A ->
  (forall v, FOfree_in v A = false) ->
  forall n,
  (FOsat (fun _ => 0) A -> FOProvesTn n A) /\
  (~ FOsat (fun _ => 0) A -> FOProvesTn n (FONeg A)).
Proof.
  induction s as [|s IHs]; intros A Hsz HD Hcl n.
  - destruct A; cbn in Hsz; lia.
  - destruct HD as [a b | | B C HB HC | v t A' Hvt HSvt HA'
                    | v t A' Hvt HSvt HA'].
    + assert (Hca : FOclosed_tm a).
      { apply FOin_all_false_closed. intro w.
        specialize (Hcl w). cbn in Hcl.
        exact (proj1 (proj1 (Bool.orb_false_iff _ _) Hcl)). }
      assert (Hcb : FOclosed_tm b).
      { apply FOin_all_false_closed. intro w.
        specialize (Hcl w). cbn in Hcl.
        exact (proj2 (proj1 (Bool.orb_false_iff _ _) Hcl)). }
      split.
      * intro Hsat. cbn in Hsat.
        exact (FOPr_closed_eq_true n a b Hca Hcb Hsat).
      * intro Hns. apply (FOPr_closed_eq_false n a b Hca Hcb).
        intro Heq. apply Hns. cbn. exact Heq.
    + split.
      * intro Hsat. cbn in Hsat. contradiction.
      * intro. exact (FOPr_idf n FOFalseF).
    + cbn in Hsz.
      assert (HclB : forall w, FOfree_in w B = false).
      { intro w. specialize (Hcl w). cbn in Hcl.
        exact (proj1 (proj1 (Bool.orb_false_iff _ _) Hcl)). }
      assert (HclC : forall w, FOfree_in w C = false).
      { intro w. specialize (Hcl w). cbn in Hcl.
        exact (proj2 (proj1 (Bool.orb_false_iff _ _) Hcl)). }
      assert (HszB : FOfsize B <= s) by lia.
      assert (HszC : FOfsize C <= s) by lia.
      pose proof (IHs B HszB HB HclB n) as [IHBt IHBf].
      pose proof (IHs C HszC HC HclC n) as [IHCt IHCf].
      split.
      * intro Hsat.
        destruct (classic (FOsat (fun _ => 0) C)) as [HC1|HC0].
        -- exact (FOPr_weaken n C B (IHCt HC1)).
        -- assert (HB0 : ~ FOsat (fun _ => 0) B).
           { intro HB1. apply HC0. cbn in Hsat. exact (Hsat HB1). }
           exact (FOPr_compose n B FOFalseF C (IHBf HB0) (FOPr_efq n C)).
      * intro Hns.
        assert (HB1 : FOsat (fun _ => 0) B).
        { destruct (classic (FOsat (fun _ => 0) B)) as [|HB0]; [assumption|].
          exfalso. apply Hns. cbn. intro HBx. exfalso. exact (HB0 HBx). }
        assert (HC0 : ~ FOsat (fun _ => 0) C).
        { intro HC1. apply Hns. cbn. intro. exact HC1. }
        assert (HT : FOProvesTn n (FOImplF B (FOImplF (FONeg C)
                       (FONeg (FOImplF B C))))).
        { apply (FOPr_taut n (FOm2 B C)
            (Impl (Var 0) (Impl (Neg (Var 1)) (Neg (Impl (Var 0) (Var 1))))));
            [cbn; tauto | reflexivity]. }
        exact (FOPr_mp2 n _ _ _ HT (IHBt HB1) (IHCf HC0)).
    + cbn in Hsz.
      assert (EvSv : Nat.eqb v (S v) = false) by (apply Nat.eqb_neq; lia).
      assert (HtA : forall w, w <> v -> w <> S v ->
          FOin_tm w t = false /\ FOfree_in w A' = false).
      { intros w Ewv EwSv.
        specialize (Hcl w). cbn -[Nat.eqb] in Hcl.
        assert (Evw : Nat.eqb v w = false)
          by (apply Nat.eqb_neq; intro e; apply Ewv; symmetry; exact e).
        assert (ESvw : Nat.eqb (S v) w = false)
          by (apply Nat.eqb_neq; intro e; apply EwSv; symmetry; exact e).
        rewrite Evw, ESvw in Hcl. cbn in Hcl.
        exact (proj1 (Bool.orb_false_iff _ _) Hcl). }
      assert (Hct : FOclosed_tm t).
      { apply FOin_all_false_closed. intro w.
        destruct (Nat.eqb_spec w v) as [->|Ewv]; [exact Hvt|].
        destruct (Nat.eqb_spec w (S v)) as [->|EwSv]; [exact HSvt|].
        exact (proj1 (HtA w Ewv EwSv)). }
      assert (HclA : forall w, w <> v -> FOfree_in w A' = false).
      { intros w Ewv.
        destruct (Nat.eqb_spec w (S v)) as [->|EwSv].
        - specialize (Hcl (S v)). cbn -[Nat.eqb] in Hcl.
          rewrite EvSv, !Nat.eqb_refl in Hcl. cbn in Hcl.
          exact Hcl.
        - exact (proj2 (HtA w Ewv EwSv)). }
      assert (HclI : forall i w,
          FOfree_in w (FOsubst_num v i A') = false).
      { intros i w. rewrite FOfree_in_subst_num.
        destruct (Nat.eqb_spec w v) as [->|Ew]; [reflexivity|].
        exact (HclA w Ew). }
      assert (HszI : forall i, FOfsize (FOsubst_num v i A') <= s).
      { intro i. rewrite FOfsize_subst_num. lia. }
      split.
      * intro Hsat.
        assert (Hinst : forall i, i < FOeval (fun _ => 0) t ->
            FOProvesTn n (FOsubst_num v i A')).
        { intros i Hik.
          assert (HsatI : FOsat (fun _ => 0) (FOsubst_num v i A')).
          { apply (proj2 (FOsat_subst_num A' v i (fun _ => 0))).
            cbn -[Nat.eqb FOupdate] in Hsat.
            specialize (Hsat i). apply Hsat.
            cbn -[Nat.eqb FOupdate].
            exists (FOeval (fun _ => 0) t - i - 1).
            rewrite (FOeval_update_not_in t _ (S v)
                       (FOeval (fun _ => 0) t - i - 1)
                       (FOclosed_in_false t (S v) Hct)).
            rewrite (FOeval_update_not_in t _ v i
                       (FOclosed_in_false t v Hct)).
            unfold FOupdate.
            rewrite EvSv, !Nat.eqb_refl.
            cbn. lia. }
          exact (proj1 (IHs (FOsubst_num v i A') (HszI i)
                          (FOdelta0_subst_num A' v i HA') (HclI i) n)
                   HsatI). }
        pose proof (FOPr_clt_conv n v t Hct) as CONV.
        pose proof (FOPr_ball_intro_num n v (FOeval (fun _ => 0) t) A'
                      Hinst) as BI.
        unfold FOBall in BI.
        rewrite FOLtF_var_num in BI.
        pose proof (FOProvesTn_AllElimT n v (FOVar v)
                      (FOImplF
                         (FOExists (S v)
                            (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                                  (FOnumeral (FOeval (fun _ => 0) t))))
                         A')
                      (FOsubst_ok_var_self _ v)) as AE.
        rewrite (FOsubst_f_id _ v) in AE.
        pose proof (FOProvesTn_MP n _ _ AE BI) as OPEN.
        apply FOProvesTn_Gen.
        exact (FOPr_compose n _ _ _ CONV OPEN).
      * intro Hnsat.
        assert (Hex : exists w0,
            FOsat (FOupdate (fun _ => 0) v w0)
              (FOExists (S v)
                 (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) t))
            /\ ~ FOsat (FOupdate (fun _ => 0) v w0) A').
        { apply NNPP. intro Hno. apply Hnsat. cbn. intros w0 HsatLT.
          destruct (classic (FOsat (FOupdate (fun _ => 0) v w0) A'))
            as [|Hna]; [assumption|].
          exfalso. apply Hno. exists w0. split; [exact HsatLT | exact Hna]. }
        destruct Hex as [w0 [HsatLT HnsatA]].
        assert (Hwk : w0 < FOeval (fun _ => 0) t).
        { cbn -[Nat.eqb FOupdate] in HsatLT. destruct HsatLT as [z Hz].
          rewrite (FOeval_update_not_in t _ (S v) z
                     (FOclosed_in_false t (S v) Hct)) in Hz.
          rewrite (FOeval_update_not_in t _ v w0
                     (FOclosed_in_false t v Hct)) in Hz.
          unfold FOupdate in Hz.
          rewrite EvSv, !Nat.eqb_refl in Hz.
          cbn in Hz. lia. }
        assert (HnsI : ~ FOsat (fun _ => 0) (FOsubst_num v w0 A')).
        { intro Hx. apply HnsatA.
          exact (proj1 (FOsat_subst_num A' v w0 (fun _ => 0)) Hx). }
        pose proof (proj2 (IHs (FOsubst_num v w0 A') (HszI w0)
                             (FOdelta0_subst_num A' v w0 HA')
                             (HclI w0) n) HnsI) as HnegI.
        pose proof (FOProvesTn_AllElimNum n v w0
                      (FOImplF
                         (FOExists (S v)
                            (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                                  t))
                         A')) as AE.
        pose proof (FOPr_clt_inst n v w0 t Hct Hwk) as HLT.
        rewrite <- (FOsubst_num_clt v w0 t Hct) in HLT.
        pose proof (FOPr_swap_mp n _ _ _ AE HLT) as T2.
        exact (FOPr_compose n _ _ _ T2 HnegI).
    + cbn in Hsz.
      assert (EvSv : Nat.eqb v (S v) = false) by (apply Nat.eqb_neq; lia).
      assert (HtA : forall w, w <> v -> w <> S v ->
          FOin_tm w t = false /\ FOfree_in w A' = false).
      { intros w Ewv EwSv.
        specialize (Hcl w). cbn -[Nat.eqb] in Hcl.
        assert (Evw : Nat.eqb v w = false)
          by (apply Nat.eqb_neq; intro e; apply Ewv; symmetry; exact e).
        assert (ESvw : Nat.eqb (S v) w = false)
          by (apply Nat.eqb_neq; intro e; apply EwSv; symmetry; exact e).
        rewrite Evw, ESvw in Hcl. cbn in Hcl.
        rewrite !Bool.orb_false_r in Hcl.
        exact (proj1 (Bool.orb_false_iff _ _) Hcl). }
      assert (Hct : FOclosed_tm t).
      { apply FOin_all_false_closed. intro w.
        destruct (Nat.eqb_spec w v) as [->|Ewv]; [exact Hvt|].
        destruct (Nat.eqb_spec w (S v)) as [->|EwSv]; [exact HSvt|].
        exact (proj1 (HtA w Ewv EwSv)). }
      assert (HclA : forall w, w <> v -> FOfree_in w A' = false).
      { intros w Ewv.
        destruct (Nat.eqb_spec w (S v)) as [->|EwSv].
        - specialize (Hcl (S v)). cbn -[Nat.eqb] in Hcl.
          rewrite EvSv, !Nat.eqb_refl in Hcl. cbn in Hcl.
          rewrite !Bool.orb_false_r in Hcl.
          exact Hcl.
        - exact (proj2 (HtA w Ewv EwSv)). }
      assert (HclI : forall i w,
          FOfree_in w (FOsubst_num v i A') = false).
      { intros i w. rewrite FOfree_in_subst_num.
        destruct (Nat.eqb_spec w v) as [->|Ew]; [reflexivity|].
        exact (HclA w Ew). }
      assert (HszI : forall i, FOfsize (FOsubst_num v i A') <= s).
      { intro i. rewrite FOfsize_subst_num. lia. }
      split.
      * intro Hsat.
        destruct Hsat as [w0 Hw0].
        pose proof (proj1 (FOsat_FOAnd (FOupdate (fun _ => 0) v w0) _ _)
                      Hw0) as [HLTs HAs].
        assert (Hwk : w0 < FOeval (fun _ => 0) t).
        { cbn -[Nat.eqb FOupdate] in HLTs. destruct HLTs as [z Hz].
          rewrite (FOeval_update_not_in t _ (S v) z
                     (FOclosed_in_false t (S v) Hct)) in Hz.
          rewrite (FOeval_update_not_in t _ v w0
                     (FOclosed_in_false t v Hct)) in Hz.
          unfold FOupdate in Hz.
          rewrite EvSv, !Nat.eqb_refl in Hz.
          cbn in Hz. lia. }
        assert (HsatI : FOsat (fun _ => 0) (FOsubst_num v w0 A')).
        { apply (proj2 (FOsat_subst_num A' v w0 (fun _ => 0))). exact HAs. }
        pose proof (proj1 (IHs (FOsubst_num v w0 A') (HszI w0)
                             (FOdelta0_subst_num A' v w0 HA')
                             (HclI w0) n) HsatI) as HAp.
        pose proof (FOPr_clt_inst n v w0 t Hct Hwk) as HLTp.
        rewrite <- (FOsubst_num_clt v w0 t Hct) in HLTp.
        apply (FOProvesTn_MP n _ _
                (FOProvesTn_ExIntroNum n v w0
                   (FOAnd
                      (FOExists (S v)
                         (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                               t))
                      A'))).
        exact (FOPr_and_intro n _ _ HLTp HAp).
      * intro Hnsat.
        assert (Hinst : forall i, i < FOeval (fun _ => 0) t ->
            FOProvesTn n (FOsubst_num v i (FONeg A'))).
        { intros i Hik.
          assert (HnsI : ~ FOsat (fun _ => 0) (FOsubst_num v i A')).
          { intro Hx. apply Hnsat.
            exists i.
            apply (proj2 (FOsat_FOAnd _ _ _)). split.
            - cbn -[Nat.eqb FOupdate].
              exists (FOeval (fun _ => 0) t - i - 1).
              rewrite (FOeval_update_not_in t _ (S v) _
                         (FOclosed_in_false t (S v) Hct)).
              rewrite (FOeval_update_not_in t _ v i
                         (FOclosed_in_false t v Hct)).
              unfold FOupdate. rewrite EvSv, !Nat.eqb_refl. cbn. lia.
            - exact (proj1 (FOsat_subst_num A' v i (fun _ => 0)) Hx). }
          exact (proj2 (IHs (FOsubst_num v i A') (HszI i)
                          (FOdelta0_subst_num A' v i HA')
                          (HclI i) n) HnsI). }
        pose proof (FOPr_ball_intro_num n v (FOeval (fun _ => 0) t)
                      (FONeg A') Hinst) as BI.
        unfold FOBall in BI. rewrite FOLtF_var_num in BI.
        pose proof (FOProvesTn_AllElimT n v (FOVar v)
                      (FOImplF
                         (FOExists (S v)
                            (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
                                  (FOnumeral (FOeval (fun _ => 0) t))))
                         (FONeg A'))
                      (FOsubst_ok_var_self _ v)) as AE.
        rewrite (FOsubst_f_id _ v) in AE.
        pose proof (FOProvesTn_MP n _ _ AE BI) as OPEN.
        pose proof (FOPr_compose n _ _ _ (FOPr_clt_conv n v t Hct) OPEN)
          as OPEN2.
        assert (HT : FOProvesTn n
            (FOImplF
               (FOImplF
                  (FOExists (S v)
                     (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) t))
                  (FONeg A'))
               (FONeg (FOAnd
                  (FOExists (S v)
                     (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) t))
                  A')))).
        { apply (FOPr_taut n
            (FOm2 (FOExists (S v)
                     (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) t))
                  A')
            (Impl (Impl (Var 0) (Neg (Var 1)))
                  (Neg (And (Var 0) (Var 1)))));
            [cbn; tauto | reflexivity]. }
        pose proof (FOProvesTn_MP n _ _ HT OPEN2) as NEG1.
        pose proof (FOProvesTn_Gen n v _ NEG1) as GN.
        exact (FOProvesTn_MP n _ _ (FOProvesTn_AllNegToNegEx n v _) GN).
Qed.

Theorem FOsigma1_completeness : forall s A,
  FOfsize A <= s ->
  FOsigma1 A -> (forall v, FOfree_in v A = false) ->
  FOsat (fun _ => 0) A -> forall n, FOProvesTn n A.
Proof.
  induction s as [|s IHs]; intros A Hsz HS Hcl Hsat n.
  - destruct A; cbn in Hsz; lia.
  - destruct HS as [A HD | x A HS'].
    + exact (proj1 (FOdelta0_decided (S s) A Hsz HD Hcl n) Hsat).
    + cbn in Hsat. destruct Hsat as [w Hw].
      apply (FOProvesTn_MP n _ _ (FOProvesTn_ExIntroNum n x w A)).
      apply (IHs (FOsubst_num x w A)).
      * rewrite FOfsize_subst_num. cbn in Hsz. lia.
      * apply FOsigma1_subst_num. exact HS'.
      * intro v0. rewrite FOfree_in_subst_num.
        destruct (Nat.eqb_spec v0 x) as [->|Ev]; [reflexivity|].
        specialize (Hcl v0). cbn -[Nat.eqb] in Hcl.
        assert (Exv : Nat.eqb x v0 = false)
          by (apply Nat.eqb_neq; intro e; apply Ev; symmetry; exact e).
        rewrite Exv in Hcl. exact Hcl.
      * exact (proj2 (FOsat_subst_num A x w (fun _ => 0)) Hw).
Qed.

Theorem FOsigma1_completeness_closed : forall A,
  FOsigma1 A -> (forall v, FOfree_in v A = false) ->
  FOsat (fun _ => 0) A -> forall n, FOProvesTn n A.
Proof.
  intros A HS Hcl Hsat n.
  exact (FOsigma1_completeness (FOfsize A) A (Nat.le_refl _) HS Hcl Hsat n).
Qed.

(** ** Builders for arithmetized Delta_0 formulas.

    The arithmetization is assembled from equation atoms over +, *, S
    terms, conjunction and disjunction, and the canonical bounded
    quantifiers.  Variables are allocated in consecutive pairs (v, S v)
    with every argument term's variables strictly below the binder, so
    each builder's side conditions discharge by a max-var bound. *)

Lemma FOin_tm_above : forall t v,
  FOmax_var_tm t < v -> FOin_tm v t = false.
Proof.
  induction t; intros v Hv; cbn in *.
  - apply Nat.eqb_neq. lia.
  - reflexivity.
  - apply IHt. exact Hv.
  - rewrite IHt1, IHt2; [reflexivity | lia | lia].
  - rewrite IHt1, IHt2; [reflexivity | lia | lia].
Qed.

Lemma FOdelta0_and : forall A B,
  FOdelta0 A -> FOdelta0 B -> FOdelta0 (FOAnd A B).
Proof.
  intros A B HA HB. unfold FOAnd, FONeg.
  apply FOd0_impl; [apply FOd0_impl|apply FOd0_false].
  - exact HA.
  - apply FOd0_impl; [exact HB | apply FOd0_false].
Qed.

Lemma FOdelta0_or : forall A B,
  FOdelta0 A -> FOdelta0 B -> FOdelta0 (FOOr A B).
Proof.
  intros A B HA HB. unfold FOOr, FONeg.
  apply FOd0_impl.
  - apply FOd0_impl; [exact HA | apply FOd0_false].
  - exact HB.
Qed.

Lemma FOdelta0_neg : forall A, FOdelta0 A -> FOdelta0 (FONeg A).
Proof.
  intros A HA. unfold FONeg.
  apply FOd0_impl; [exact HA | apply FOd0_false].
Qed.

Lemma FOfree_in_FOAnd : forall w A B,
  FOfree_in w (FOAnd A B) = (FOfree_in w A || FOfree_in w B)%bool.
Proof.
  intros w A B. cbn. rewrite !Bool.orb_false_r. reflexivity.
Qed.

Lemma FOfree_in_FOOr : forall w A B,
  FOfree_in w (FOOr A B) = (FOfree_in w A || FOfree_in w B)%bool.
Proof.
  intros w A B. cbn. rewrite !Bool.orb_false_r. reflexivity.
Qed.

Lemma FOfree_in_FONeg : forall w A,
  FOfree_in w (FONeg A) = FOfree_in w A.
Proof.
  intros w A. cbn. rewrite !Bool.orb_false_r. reflexivity.
Qed.

(** The Cantor-pair equation as a term-level atom:
    [2c = (a+b)(a+b+1) + 2b]. *)

Lemma triangle_double : forall s, 2 * to_triangle s = s * S s.
Proof.
  induction s as [|s IH]; cbn [to_triangle]; nia.
Qed.

Lemma FOsat_FOcpairF : forall e a b c,
  FOsat e (FOcpairF a b c)
  <-> cpair (FOeval e a) (FOeval e b) = FOeval e c.
Proof.
  intros e a b c. unfold FOcpairF. cbn.
  pose proof (triangle_double (FOeval e a + FOeval e b)) as Ht.
  unfold cpair. split; intro H; nia.
Qed.

Lemma FOdelta0_FOcpairF : forall a b c, FOdelta0 (FOcpairF a b c).
Proof. intros. apply FOd0_eq. Qed.

Lemma FOfree_in_FOcpairF : forall w a b c,
  FOfree_in w (FOcpairF a b c)
  = (FOin_tm w a || FOin_tm w b || FOin_tm w c)%bool.
Proof.
  intros w a b c. cbn.
  destruct (FOin_tm w a); destruct (FOin_tm w b);
    destruct (FOin_tm w c); reflexivity.
Qed.

(** The canonical bounded quantifiers as builders with their
    satisfaction laws. *)

Lemma FOdelta0_FOBexC : forall v t A,
  FOin_tm v t = false -> FOin_tm (S v) t = false -> FOdelta0 A ->
  FOdelta0 (FOBexC v t A).
Proof. intros. apply FOd0_bex; assumption. Qed.

Lemma FOdelta0_FOBallC : forall v t A,
  FOin_tm v t = false -> FOin_tm (S v) t = false -> FOdelta0 A ->
  FOdelta0 (FOBallC v t A).
Proof. intros. apply FOd0_ball; assumption. Qed.

Lemma FOsat_lt_witness : forall e v t w,
  FOin_tm v t = false -> FOin_tm (S v) t = false ->
  (FOsat (FOupdate e v w)
     (FOExists (S v)
        (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) t))
   <-> w < FOeval e t).
Proof.
  intros e v t w Hvt HSvt.
  assert (EvSv : Nat.eqb v (S v) = false) by (apply Nat.eqb_neq; lia).
  split.
  - intros [z Hz].
    cbn -[Nat.eqb FOupdate] in Hz.
    rewrite (FOeval_update_not_in t _ (S v) z HSvt) in Hz.
    rewrite (FOeval_update_not_in t _ v w Hvt) in Hz.
    unfold FOupdate in Hz.
    rewrite EvSv, !Nat.eqb_refl in Hz.
    cbn in Hz. lia.
  - intro Hw. cbn -[Nat.eqb FOupdate].
    exists (FOeval e t - w - 1).
    rewrite (FOeval_update_not_in t _ (S v) _ HSvt).
    rewrite (FOeval_update_not_in t _ v w Hvt).
    unfold FOupdate. rewrite EvSv, !Nat.eqb_refl. cbn. lia.
Qed.

Lemma FOsat_FOBexC : forall e v t A,
  FOin_tm v t = false -> FOin_tm (S v) t = false ->
  (FOsat e (FOBexC v t A)
   <-> exists w, w < FOeval e t /\ FOsat (FOupdate e v w) A).
Proof.
  intros e v t A Hvt HSvt. unfold FOBexC.
  split.
  - intros [w Hw].
    pose proof (proj1 (FOsat_FOAnd _ _ _) Hw) as [HL HA].
    exists w. split.
    + exact (proj1 (FOsat_lt_witness e v t w Hvt HSvt) HL).
    + exact HA.
  - intros [w [Hwlt HA]].
    exists w.
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    + exact (proj2 (FOsat_lt_witness e v t w Hvt HSvt) Hwlt).
    + exact HA.
Qed.

Lemma FOsat_FOBallC : forall e v t A,
  FOin_tm v t = false -> FOin_tm (S v) t = false ->
  (FOsat e (FOBallC v t A)
   <-> forall w, w < FOeval e t -> FOsat (FOupdate e v w) A).
Proof.
  intros e v t A Hvt HSvt. unfold FOBallC.
  split.
  - intros Hf w Hw.
    exact (Hf w (proj2 (FOsat_lt_witness e v t w Hvt HSvt) Hw)).
  - intros Hf w HL.
    exact (Hf w (proj1 (FOsat_lt_witness e v t w Hvt HSvt) HL)).
Qed.

Lemma FOfree_in_FOBexC : forall w v t A,
  w <> v -> w <> S v ->
  FOfree_in w (FOBexC v t A) = (FOin_tm w t || FOfree_in w A)%bool.
Proof.
  intros w v t A Hwv HwSv. unfold FOBexC.
  assert (Evw : Nat.eqb v w = false)
    by (apply Nat.eqb_neq; intro e; apply Hwv; symmetry; exact e).
  assert (ESvw : Nat.eqb (S v) w = false)
    by (apply Nat.eqb_neq; intro e; apply HwSv; symmetry; exact e).
  cbn -[Nat.eqb]. rewrite Evw, ESvw. cbn.
  rewrite !Bool.orb_false_r. reflexivity.
Qed.

Lemma FOfree_in_FOBexC_self : forall v t A,
  FOfree_in v (FOBexC v t A) = false.
Proof.
  intros v t A. unfold FOBexC. cbn -[Nat.eqb].
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma FOfree_in_FOBexC_succ : forall v t A,
  FOfree_in (S v) (FOBexC v t A) = FOfree_in (S v) A.
Proof.
  intros v t A. unfold FOBexC.
  assert (EvSv : Nat.eqb v (S v) = false) by (apply Nat.eqb_neq; lia).
  cbn -[Nat.eqb]. rewrite EvSv, !Nat.eqb_refl. cbn.
  rewrite !Bool.orb_false_r. reflexivity.
Qed.

Lemma FOfree_in_FOBallC : forall w v t A,
  w <> v -> w <> S v ->
  FOfree_in w (FOBallC v t A) = (FOin_tm w t || FOfree_in w A)%bool.
Proof.
  intros w v t A Hwv HwSv. unfold FOBallC.
  assert (Evw : Nat.eqb v w = false)
    by (apply Nat.eqb_neq; intro e; apply Hwv; symmetry; exact e).
  assert (ESvw : Nat.eqb (S v) w = false)
    by (apply Nat.eqb_neq; intro e; apply HwSv; symmetry; exact e).
  cbn -[Nat.eqb]. rewrite Evw, ESvw. cbn. reflexivity.
Qed.

Lemma FOfree_in_FOBallC_self : forall v t A,
  FOfree_in v (FOBallC v t A) = false.
Proof.
  intros v t A. unfold FOBallC. cbn -[Nat.eqb].
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma FOfree_in_FOBallC_succ : forall v t A,
  FOfree_in (S v) (FOBallC v t A) = FOfree_in (S v) A.
Proof.
  intros v t A. unfold FOBallC.
  assert (EvSv : Nat.eqb v (S v) = false) by (apply Nat.eqb_neq; lia).
  cbn -[Nat.eqb]. rewrite EvSv, !Nat.eqb_refl. cbn. reflexivity.
Qed.

(** Beta access as a Delta_0 formula: [x = beta c d i], using the
    block (v, S v, S (S v), S (S (S v))). *)

Lemma FOdelta0_FObetaF : forall v c d i x,
  FOmax_var_tm c < v -> FOmax_var_tm d < v ->
  FOmax_var_tm i < v -> FOmax_var_tm x < v ->
  FOdelta0 (FObetaF v c d i x).
Proof.
  intros v c d i x Hc Hd Hi Hx. unfold FObetaF.
  apply FOdelta0_FOBexC.
  - apply FOin_tm_above. cbn. lia.
  - apply FOin_tm_above. cbn. lia.
  - apply FOdelta0_and; [apply FOd0_eq|].
    apply FOdelta0_FOBexC.
    + apply FOin_tm_above. cbn. lia.
    + apply FOin_tm_above. cbn. lia.
    + apply FOd0_eq.
Qed.

(** ** The generic pattern lemmas.

    [FOPATF] is Delta_0 and its satisfaction is exactly the [cpat_sem]
    equation, proved once by induction on the pattern; every shape
    recognizer instantiates these. *)

Lemma cpat_sem_ext : forall p sg1 sg2,
  (forall s, sg1 s = sg2 s) ->
  cpat_sem sg1 p = cpat_sem sg2 p.
Proof.
  intros p sg1 sg2 H.
  induction p as [k | s | q IH | a IHa b IHb]; cbn.
  - reflexivity.
  - apply H.
  - rewrite IH. reflexivity.
  - rewrite IHa, IHb. reflexivity.
Qed.

Lemma cpat_occurs_le : forall p sigma s,
  cpat_occurs s p = true -> sigma s <= cpat_sem sigma p.
Proof.
  intros p sigma s.
  induction p as [k | s' | q IH | a IHa b IHb]; cbn; intro H.
  - discriminate.
  - apply Nat.eqb_eq in H. subst s'. lia.
  - specialize (IH H). lia.
  - apply Bool.orb_prop in H.
    pose proof (cpair_bound (cpat_sem sigma a) (cpat_sem sigma b)).
    destruct H as [H | H].
    + pose proof (IHa H). lia.
    + pose proof (IHb H). lia.
Qed.

Lemma FOmax_var_nth_lt : forall env B C s,
  Forall (fun t => FOmax_var_tm t < B) env -> B <= C -> 0 < C ->
  FOmax_var_tm (nth s env FOZero) < C.
Proof.
  intros env B C s Hf HBC HC. revert s.
  induction Hf as [|t l Ht Hl IH]; intro s.
  - destruct s; cbn; exact HC.
  - destruct s; cbn; [lia | exact (IH s)].
Qed.

Lemma FOdelta0_FOPATF : forall p B env d,
  Forall (fun t => FOmax_var_tm t < B) env ->
  FOmax_var_tm d < B ->
  FOdelta0 (FOPATF B env p d).
Proof.
  intros p.
  induction p as [k | s | q IH | a IHa b IHb];
    intros B env d Henv Hd; cbn [FOPATF].
  - apply FOd0_eq.
  - apply FOd0_eq.
  - apply FOdelta0_FOBexC.
    + apply FOin_tm_above. exact Hd.
    + apply FOin_tm_above. lia.
    + apply FOdelta0_and; [apply FOd0_eq|].
      apply IH.
      * eapply Forall_impl; [|exact Henv]. intros t Ht. cbv beta in *. lia.
      * cbn. lia.
  - apply FOdelta0_FOBexC.
    + apply FOin_tm_above. cbn. exact Hd.
    + apply FOin_tm_above. cbn. lia.
    + apply FOdelta0_FOBexC.
      * apply FOin_tm_above. cbn. lia.
      * apply FOin_tm_above. cbn. lia.
      * apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
        apply FOdelta0_and.
        -- apply IHa.
           ++ eapply Forall_impl; [|exact Henv]. intros t Ht. cbv beta in *. lia.
           ++ cbn. lia.
        -- apply IHb.
           ++ eapply Forall_impl; [|exact Henv]. intros t Ht. cbv beta in *. lia.
           ++ cbn. lia.
Qed.

Lemma FOsat_FOPATF : forall p e B env d,
  Forall (fun t => FOmax_var_tm t < B) env ->
  FOmax_var_tm d < B ->
  (FOsat e (FOPATF B env p d) <->
   cpat_sem (fun s => FOeval e (nth s env FOZero)) p = FOeval e d).
Proof.
  intros p.
  induction p as [k | s | q IH | a IHa b IHb];
    intros e B env d Henv Hd; cbn [FOPATF cpat_sem].
  - cbn [FOsat]. rewrite FOeval_numeral.
    split; intro H; symmetry; exact H.
  - cbn [FOsat]. split; intro H; symmetry; exact H.
  - assert (HinB : FOin_tm B d = false) by (apply FOin_tm_above; exact Hd).
    assert (HinSB : FOin_tm (S B) d = false)
      by (apply FOin_tm_above; lia).
    assert (HenvB2 : Forall (fun t => FOmax_var_tm t < B+2) env)
      by (eapply Forall_impl; [|exact Henv]; intros t Ht; cbv beta in *; lia).
    assert (HmaxB2 : FOmax_var_tm (FOVar B) < B+2) by (cbn; lia).
    rewrite (FOsat_FOBexC e B d _ HinB HinSB).
    split.
    + intros [w [Hw Hbody]].
      apply (proj1 (FOsat_FOAnd _ _ _)) in Hbody.
      destruct Hbody as [Heq Hq].
      cbn [FOsat FOeval] in Heq.
      rewrite (FOeval_update_above d e B w Hd) in Heq.
      unfold FOupdate in Heq. rewrite Nat.eqb_refl in Heq.
      apply (proj1 (IH (FOupdate e B w) (B+2) env (FOVar B)
                      HenvB2 HmaxB2)) in Hq.
      assert (Hsg : forall s,
          FOeval (FOupdate e B w) (nth s env FOZero)
          = FOeval e (nth s env FOZero)).
      { intro s. apply FOeval_update_above.
        eapply FOmax_var_nth_lt; [exact Henv | lia | lia]. }
      rewrite (cpat_sem_ext q _ _ Hsg) in Hq.
      cbn [FOeval] in Hq.
      unfold FOupdate in Hq. rewrite Nat.eqb_refl in Hq.
      lia.
    + intro Hsem.
      exists (cpat_sem (fun s => FOeval e (nth s env FOZero)) q).
      split; [lia|].
      apply (proj2 (FOsat_FOAnd _ _ _)). split.
      * cbn [FOsat FOeval].
        rewrite (FOeval_update_above d e B _ Hd).
        unfold FOupdate. rewrite Nat.eqb_refl. lia.
      * apply (proj2 (IH (FOupdate e B _) (B+2) env (FOVar B)
                        HenvB2 HmaxB2)).
        assert (Hsg : forall s,
            FOeval (FOupdate e B
                      (cpat_sem (fun s' => FOeval e (nth s' env FOZero))
                         q)) (nth s env FOZero)
            = FOeval e (nth s env FOZero)).
        { intro s. apply FOeval_update_above.
          eapply FOmax_var_nth_lt; [exact Henv | lia | lia]. }
        rewrite (cpat_sem_ext q _ _ Hsg).
        cbn [FOeval]. unfold FOupdate. rewrite Nat.eqb_refl.
        reflexivity.
  - assert (HinB : FOin_tm B (FOSucc d) = false)
      by (apply FOin_tm_above; cbn; exact Hd).
    assert (HinSB : FOin_tm (S B) (FOSucc d) = false)
      by (apply FOin_tm_above; cbn; lia).
    assert (HinB2 : FOin_tm (B+2) (FOSucc d) = false)
      by (apply FOin_tm_above; cbn; lia).
    assert (HinSB2 : FOin_tm (S (B+2)) (FOSucc d) = false)
      by (apply FOin_tm_above; cbn; lia).
    assert (EB2 : Nat.eqb B (B+2) = false)
      by (apply Nat.eqb_neq; lia).
    assert (HenvB4 : Forall (fun t => FOmax_var_tm t < B+4) env)
      by (eapply Forall_impl; [|exact Henv]; intros t Ht; cbv beta in *; lia).
    assert (HenvBP : Forall
        (fun t => FOmax_var_tm t < B+4+4*cpat_pairs a) env)
      by (eapply Forall_impl; [|exact Henv]; intros t Ht; cbv beta in *; lia).
    assert (HmaxA : FOmax_var_tm (FOVar B) < B+4) by (cbn; lia).
    assert (HmaxB : FOmax_var_tm (FOVar (B+2)) < B+4+4*cpat_pairs a)
      by (cbn; lia).
    rewrite (FOsat_FOBexC e B (FOSucc d) _ HinB HinSB).
    split.
    + intros [va [Hva Hbody]].
      rewrite (FOsat_FOBexC _ (B+2) (FOSucc d) _ HinB2 HinSB2) in Hbody.
      destruct Hbody as [vb [Hvb Hbody]].
      apply (proj1 (FOsat_FOAnd _ _ _)) in Hbody.
      destruct Hbody as [Hcp Hbody].
      apply (proj1 (FOsat_FOAnd _ _ _)) in Hbody.
      destruct Hbody as [Hpa Hpb].
      set (e2 := FOupdate (FOupdate e B va) (B+2) vb) in *.
      assert (EvB : FOeval e2 (FOVar B) = va).
      { cbn. unfold e2, FOupdate. rewrite EB2, Nat.eqb_refl.
        reflexivity. }
      assert (EvB2 : FOeval e2 (FOVar (B+2)) = vb).
      { cbn. unfold e2, FOupdate. rewrite Nat.eqb_refl. reflexivity. }
      assert (Ed : FOeval e2 d = FOeval e d).
      { unfold e2.
        rewrite (FOeval_update_above d _ (B+2) vb ltac:(lia)).
        exact (FOeval_update_above d e B va Hd). }
      apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp.
      rewrite EvB, EvB2, Ed in Hcp.
      assert (Hsg : forall s,
          FOeval e2 (nth s env FOZero) = FOeval e (nth s env FOZero)).
      { intro s. unfold e2.
        rewrite (FOeval_update_above _ _ (B+2) vb
                   ltac:(eapply FOmax_var_nth_lt; [exact Henv | lia | lia])).
        apply FOeval_update_above.
        eapply FOmax_var_nth_lt; [exact Henv | lia | lia]. }
      apply (proj1 (IHa e2 (B+4) env (FOVar B) HenvB4 HmaxA)) in Hpa.
      rewrite (cpat_sem_ext a _ _ Hsg), EvB in Hpa.
      apply (proj1 (IHb e2 (B+4+4*cpat_pairs a) env (FOVar (B+2))
                      HenvBP HmaxB)) in Hpb.
      rewrite (cpat_sem_ext b _ _ Hsg), EvB2 in Hpb.
      rewrite Hpa, Hpb. exact Hcp.
    + intro Hsem.
      set (sg := fun s => FOeval e (nth s env FOZero)) in *.
      pose proof (cpair_bound (cpat_sem sg a) (cpat_sem sg b)) as Hcb.
      cbn [FOeval].
      exists (cpat_sem sg a). split; [lia|].
      rewrite (FOsat_FOBexC _ (B+2) (FOSucc d) _ HinB2 HinSB2).
      exists (cpat_sem sg b).
      assert (EvSucc : forall e',
          FOeval e' (FOSucc d) = S (FOeval e' d)) by reflexivity.
      split; [|apply (proj2 (FOsat_FOAnd _ _ _)); split].
      * cbn [FOeval].
        rewrite (FOeval_update_above d e B _ Hd). lia.
      * set (e2 := FOupdate (FOupdate e B (cpat_sem sg a)) (B+2)
                     (cpat_sem sg b)).
        apply (proj2 (FOsat_FOcpairF e2 _ _ _)).
        assert (EvB : FOeval e2 (FOVar B) = cpat_sem sg a).
        { cbn. unfold e2, FOupdate. rewrite EB2, Nat.eqb_refl.
          reflexivity. }
        assert (EvB2 : FOeval e2 (FOVar (B+2)) = cpat_sem sg b).
        { cbn. unfold e2, FOupdate. rewrite Nat.eqb_refl. reflexivity. }
        assert (Ed : FOeval e2 d = FOeval e d).
        { unfold e2.
          rewrite (FOeval_update_above d _ (B+2) _ ltac:(lia)).
          exact (FOeval_update_above d e B _ Hd). }
        rewrite EvB, EvB2, Ed. exact Hsem.
      * apply (proj2 (FOsat_FOAnd _ _ _)).
        set (e2 := FOupdate (FOupdate e B (cpat_sem sg a)) (B+2)
                     (cpat_sem sg b)).
        assert (Hsg : forall s,
            FOeval e2 (nth s env FOZero) = FOeval e (nth s env FOZero)).
        { intro s. unfold e2.
          rewrite (FOeval_update_above _ _ (B+2) _
                     ltac:(eapply FOmax_var_nth_lt; [exact Henv | lia | lia])).
          apply FOeval_update_above.
          eapply FOmax_var_nth_lt; [exact Henv | lia | lia]. }
        assert (EvB : FOeval e2 (FOVar B) = cpat_sem sg a).
        { cbn. unfold e2, FOupdate. rewrite EB2, Nat.eqb_refl.
          reflexivity. }
        assert (EvB2 : FOeval e2 (FOVar (B+2)) = cpat_sem sg b).
        { cbn. unfold e2, FOupdate. rewrite Nat.eqb_refl. reflexivity. }
        split.
        -- apply (proj2 (IHa e2 (B+4) env (FOVar B) HenvB4 HmaxA)).
           rewrite (cpat_sem_ext a _ _ Hsg), EvB. reflexivity.
        -- apply (proj2 (IHb e2 (B+4+4*cpat_pairs a) env (FOVar (B+2))
                           HenvBP HmaxB)).
           rewrite (cpat_sem_ext b _ _ Hsg), EvB2. reflexivity.
Qed.

(** Slot wrappers: each recognizer binds its slot witnesses by the
    code and matches a fixed pattern; the satisfaction laws expose the
    slot values, each bounded by the code value. *)

Lemma FOsat_pat1 : forall e B p d,
  FOmax_var_tm d < B ->
  (FOsat e (FOBexC B (FOSucc d) (FOPATF (B+2) [FOVar B] p d)) <->
   exists v0, v0 <= FOeval e d /\
     cpat_sem (fun s => match s with 0 => v0 | _ => 0 end) p
     = FOeval e d).
Proof.
  intros e B p d Hd.
  assert (HinB : FOin_tm B (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; exact Hd).
  assert (HinSB : FOin_tm (S B) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (Henv : Forall (fun t => FOmax_var_tm t < B+2) [FOVar B])
    by (constructor; [cbn; lia | constructor]).
  assert (Hd2 : FOmax_var_tm d < B+2) by lia.
  rewrite (FOsat_FOBexC e B (FOSucc d) _ HinB HinSB).
  split.
  - intros [w [Hw Hp]].
    cbn [FOeval] in Hw.
    apply (proj1 (FOsat_FOPATF p _ (B+2) [FOVar B] d Henv Hd2)) in Hp.
    rewrite (FOeval_update_above d e B w Hd) in Hp.
    exists w. split; [lia|].
    rewrite <- Hp.
    apply cpat_sem_ext. intro s.
    destruct s as [|s]; cbn.
    + unfold FOupdate. rewrite Nat.eqb_refl. reflexivity.
    + destruct s; reflexivity.
  - intros [v0 [Hb Hsem]].
    exists v0. split.
    + cbn [FOeval]. lia.
    + apply (proj2 (FOsat_FOPATF p _ (B+2) [FOVar B] d Henv Hd2)).
      rewrite (FOeval_update_above d e B v0 Hd).
      rewrite <- Hsem.
      apply cpat_sem_ext. intro s.
      destruct s as [|s]; cbn.
      * unfold FOupdate. rewrite Nat.eqb_refl. reflexivity.
      * destruct s; reflexivity.
Qed.

Lemma FOsat_pat2 : forall e B p d,
  FOmax_var_tm d < B ->
  (FOsat e (FOBexC B (FOSucc d)
              (FOBexC (B+2) (FOSucc d)
                 (FOPATF (B+4) [FOVar B; FOVar (B+2)] p d))) <->
   exists v0 v1, v0 <= FOeval e d /\ v1 <= FOeval e d /\
     cpat_sem (fun s => match s with 0 => v0 | 1 => v1 | _ => 0 end) p
     = FOeval e d).
Proof.
  intros e B p d Hd.
  assert (HinB : FOin_tm B (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; exact Hd).
  assert (HinSB : FOin_tm (S B) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB2 : FOin_tm (B+2) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB2 : FOin_tm (S (B+2)) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (EB2 : Nat.eqb B (B+2) = false) by (apply Nat.eqb_neq; lia).
  assert (Henv : Forall (fun t => FOmax_var_tm t < B+4)
                   [FOVar B; FOVar (B+2)])
    by (constructor; [cbn; lia |
        constructor; [cbn; lia | constructor]]).
  assert (Hd4 : FOmax_var_tm d < B+4) by lia.
  rewrite (FOsat_FOBexC e B (FOSucc d) _ HinB HinSB).
  split.
  - intros [w0 [Hw0 Hb1]].
    cbn [FOeval] in Hw0.
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc d) _ HinB2 HinSB2) in Hb1.
    destruct Hb1 as [w1 [Hw1 Hp]].
    cbn [FOeval] in Hw1.
    rewrite (FOeval_update_above d e B w0 Hd) in Hw1.
    set (e2 := FOupdate (FOupdate e B w0) (B+2) w1) in *.
    apply (proj1 (FOsat_FOPATF p _ (B+4) _ d Henv Hd4)) in Hp.
    assert (Ed : FOeval e2 d = FOeval e d).
    { unfold e2.
      rewrite (FOeval_update_above d _ (B+2) w1 ltac:(lia)).
      exact (FOeval_update_above d e B w0 Hd). }
    rewrite Ed in Hp.
    exists w0, w1. split; [lia|]. split; [lia|].
    rewrite <- Hp.
    apply cpat_sem_ext. intro s.
    destruct s as [|[|s]]; cbn.
    + unfold e2, FOupdate. rewrite EB2, Nat.eqb_refl. reflexivity.
    + unfold e2, FOupdate. rewrite Nat.eqb_refl. reflexivity.
    + destruct s; reflexivity.
  - intros [v0 [v1 [Hb0 [Hb1 Hsem]]]].
    exists v0. split; [cbn [FOeval]; lia|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc d) _ HinB2 HinSB2).
    exists v1. split.
    + cbn [FOeval].
      rewrite (FOeval_update_above d e B v0 Hd). lia.
    + set (e2 := FOupdate (FOupdate e B v0) (B+2) v1).
      apply (proj2 (FOsat_FOPATF p e2 (B+4) _ d Henv Hd4)).
      assert (Ed : FOeval e2 d = FOeval e d).
      { unfold e2.
        rewrite (FOeval_update_above d _ (B+2) v1 ltac:(lia)).
        exact (FOeval_update_above d e B v0 Hd). }
      rewrite Ed, <- Hsem.
      apply cpat_sem_ext. intro s.
      destruct s as [|[|s]]; cbn.
      * unfold e2, FOupdate. rewrite EB2, Nat.eqb_refl. reflexivity.
      * unfold e2, FOupdate. rewrite Nat.eqb_refl. reflexivity.
      * destruct s; reflexivity.
Qed.

Lemma FOsat_pat3 : forall e B p d,
  FOmax_var_tm d < B ->
  (FOsat e (FOBexC B (FOSucc d)
              (FOBexC (B+2) (FOSucc d)
                 (FOBexC (B+4) (FOSucc d)
                    (FOPATF (B+6) [FOVar B; FOVar (B+2); FOVar (B+4)]
                       p d)))) <->
   exists v0 v1 v2,
     v0 <= FOeval e d /\ v1 <= FOeval e d /\ v2 <= FOeval e d /\
     cpat_sem (fun s => match s with
                        | 0 => v0 | 1 => v1 | 2 => v2 | _ => 0 end) p
     = FOeval e d).
Proof.
  intros e B p d Hd.
  assert (HinB : FOin_tm B (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; exact Hd).
  assert (HinSB : FOin_tm (S B) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB2 : FOin_tm (B+2) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB2 : FOin_tm (S (B+2)) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB4 : FOin_tm (B+4) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB4 : FOin_tm (S (B+4)) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (EB2 : Nat.eqb B (B+2) = false) by (apply Nat.eqb_neq; lia).
  assert (EB4 : Nat.eqb B (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (E24 : Nat.eqb (B+2) (B+4) = false)
    by (apply Nat.eqb_neq; lia).
  assert (Henv : Forall (fun t => FOmax_var_tm t < B+6)
                   [FOVar B; FOVar (B+2); FOVar (B+4)])
    by (constructor; [cbn; lia |
        constructor; [cbn; lia |
        constructor; [cbn; lia | constructor]]]).
  assert (Hd6 : FOmax_var_tm d < B+6) by lia.
  rewrite (FOsat_FOBexC e B (FOSucc d) _ HinB HinSB).
  split.
  - intros [w0 [Hw0 Hb1]].
    cbn [FOeval] in Hw0.
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc d) _ HinB2 HinSB2) in Hb1.
    destruct Hb1 as [w1 [Hw1 Hb2]].
    cbn [FOeval] in Hw1.
    rewrite (FOeval_update_above d e B w0 Hd) in Hw1.
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc d) _ HinB4 HinSB4) in Hb2.
    destruct Hb2 as [w2 [Hw2 Hp]].
    cbn [FOeval] in Hw2.
    rewrite (FOeval_update_above d _ (B+2) w1 ltac:(lia)) in Hw2.
    rewrite (FOeval_update_above d e B w0 Hd) in Hw2.
    set (e3 := FOupdate (FOupdate (FOupdate e B w0) (B+2) w1)
                 (B+4) w2) in *.
    apply (proj1 (FOsat_FOPATF p _ (B+6) _ d Henv Hd6)) in Hp.
    assert (Ed : FOeval e3 d = FOeval e d).
    { unfold e3.
      rewrite (FOeval_update_above d _ (B+4) w2 ltac:(lia)).
      rewrite (FOeval_update_above d _ (B+2) w1 ltac:(lia)).
      exact (FOeval_update_above d e B w0 Hd). }
    rewrite Ed in Hp.
    exists w0, w1, w2.
    split; [lia|]. split; [lia|]. split; [lia|].
    rewrite <- Hp.
    apply cpat_sem_ext. intro s.
    destruct s as [|[|[|s]]]; cbn.
    + unfold e3, FOupdate. rewrite EB4, EB2, Nat.eqb_refl. reflexivity.
    + unfold e3, FOupdate. rewrite E24, Nat.eqb_refl. reflexivity.
    + unfold e3, FOupdate. rewrite Nat.eqb_refl. reflexivity.
    + destruct s; reflexivity.
  - intros [v0 [v1 [v2 [Hb0 [Hb1 [Hb2 Hsem]]]]]].
    exists v0. split; [cbn [FOeval]; lia|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc d) _ HinB2 HinSB2).
    exists v1. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above d e B v0 Hd). lia. }
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc d) _ HinB4 HinSB4).
    exists v2. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above d _ (B+2) v1 ltac:(lia)).
      rewrite (FOeval_update_above d e B v0 Hd). lia. }
    set (e3 := FOupdate (FOupdate (FOupdate e B v0) (B+2) v1)
                 (B+4) v2).
    apply (proj2 (FOsat_FOPATF p e3 (B+6) _ d Henv Hd6)).
    assert (Ed : FOeval e3 d = FOeval e d).
    { unfold e3.
      rewrite (FOeval_update_above d _ (B+4) v2 ltac:(lia)).
      rewrite (FOeval_update_above d _ (B+2) v1 ltac:(lia)).
      exact (FOeval_update_above d e B v0 Hd). }
    rewrite Ed, <- Hsem.
    apply cpat_sem_ext. intro s.
    destruct s as [|[|[|s]]]; cbn.
    + unfold e3, FOupdate. rewrite EB4, EB2, Nat.eqb_refl. reflexivity.
    + unfold e3, FOupdate. rewrite E24, Nat.eqb_refl. reflexivity.
    + unfold e3, FOupdate. rewrite Nat.eqb_refl. reflexivity.
    + destruct s; reflexivity.
Qed.

Lemma FOsat_pat4 : forall e B p d,
  FOmax_var_tm d < B ->
  (FOsat e (FOBexC B (FOSucc d)
              (FOBexC (B+2) (FOSucc d)
                 (FOBexC (B+4) (FOSucc d)
                    (FOBexC (B+6) (FOSucc d)
                       (FOPATF (B+8)
                          [FOVar B; FOVar (B+2); FOVar (B+4);
                           FOVar (B+6)] p d))))) <->
   exists v0 v1 v2 v3,
     v0 <= FOeval e d /\ v1 <= FOeval e d /\
     v2 <= FOeval e d /\ v3 <= FOeval e d /\
     cpat_sem (fun s => match s with
                        | 0 => v0 | 1 => v1 | 2 => v2 | 3 => v3
                        | _ => 0 end) p
     = FOeval e d).
Proof.
  intros e B p d Hd.
  assert (HinB : FOin_tm B (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; exact Hd).
  assert (HinSB : FOin_tm (S B) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB2 : FOin_tm (B+2) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB2 : FOin_tm (S (B+2)) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB4 : FOin_tm (B+4) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB4 : FOin_tm (S (B+4)) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB6 : FOin_tm (B+6) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB6 : FOin_tm (S (B+6)) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (EB2 : Nat.eqb B (B+2) = false) by (apply Nat.eqb_neq; lia).
  assert (EB4 : Nat.eqb B (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (EB6 : Nat.eqb B (B+6) = false) by (apply Nat.eqb_neq; lia).
  assert (E24 : Nat.eqb (B+2) (B+4) = false)
    by (apply Nat.eqb_neq; lia).
  assert (E26 : Nat.eqb (B+2) (B+6) = false)
    by (apply Nat.eqb_neq; lia).
  assert (E46 : Nat.eqb (B+4) (B+6) = false)
    by (apply Nat.eqb_neq; lia).
  assert (Henv : Forall (fun t => FOmax_var_tm t < B+8)
                   [FOVar B; FOVar (B+2); FOVar (B+4); FOVar (B+6)])
    by (constructor; [cbn; lia |
        constructor; [cbn; lia |
        constructor; [cbn; lia |
        constructor; [cbn; lia | constructor]]]]).
  assert (Hd8 : FOmax_var_tm d < B+8) by lia.
  rewrite (FOsat_FOBexC e B (FOSucc d) _ HinB HinSB).
  split.
  - intros [w0 [Hw0 Hb1]].
    cbn [FOeval] in Hw0.
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc d) _ HinB2 HinSB2) in Hb1.
    destruct Hb1 as [w1 [Hw1 Hb2]].
    cbn [FOeval] in Hw1.
    rewrite (FOeval_update_above d e B w0 Hd) in Hw1.
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc d) _ HinB4 HinSB4) in Hb2.
    destruct Hb2 as [w2 [Hw2 Hb3]].
    cbn [FOeval] in Hw2.
    rewrite (FOeval_update_above d _ (B+2) w1 ltac:(lia)) in Hw2.
    rewrite (FOeval_update_above d e B w0 Hd) in Hw2.
    rewrite (FOsat_FOBexC _ (B+6) (FOSucc d) _ HinB6 HinSB6) in Hb3.
    destruct Hb3 as [w3 [Hw3 Hp]].
    cbn [FOeval] in Hw3.
    rewrite (FOeval_update_above d _ (B+4) w2 ltac:(lia)) in Hw3.
    rewrite (FOeval_update_above d _ (B+2) w1 ltac:(lia)) in Hw3.
    rewrite (FOeval_update_above d e B w0 Hd) in Hw3.
    set (e4 := FOupdate (FOupdate (FOupdate (FOupdate e B w0)
                 (B+2) w1) (B+4) w2) (B+6) w3) in *.
    apply (proj1 (FOsat_FOPATF p _ (B+8) _ d Henv Hd8)) in Hp.
    assert (Ed : FOeval e4 d = FOeval e d).
    { unfold e4.
      rewrite (FOeval_update_above d _ (B+6) w3 ltac:(lia)).
      rewrite (FOeval_update_above d _ (B+4) w2 ltac:(lia)).
      rewrite (FOeval_update_above d _ (B+2) w1 ltac:(lia)).
      exact (FOeval_update_above d e B w0 Hd). }
    rewrite Ed in Hp.
    exists w0, w1, w2, w3.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    rewrite <- Hp.
    apply cpat_sem_ext. intro s.
    destruct s as [|[|[|[|s]]]]; cbn.
    + unfold e4, FOupdate.
      rewrite EB6, EB4, EB2, Nat.eqb_refl. reflexivity.
    + unfold e4, FOupdate.
      rewrite E26, E24, Nat.eqb_refl. reflexivity.
    + unfold e4, FOupdate. rewrite E46, Nat.eqb_refl. reflexivity.
    + unfold e4, FOupdate. rewrite Nat.eqb_refl. reflexivity.
    + destruct s; reflexivity.
  - intros [v0 [v1 [v2 [v3 [Hb0 [Hb1 [Hb2 [Hb3 Hsem]]]]]]]].
    exists v0. split; [cbn [FOeval]; lia|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc d) _ HinB2 HinSB2).
    exists v1. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above d e B v0 Hd). lia. }
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc d) _ HinB4 HinSB4).
    exists v2. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above d _ (B+2) v1 ltac:(lia)).
      rewrite (FOeval_update_above d e B v0 Hd). lia. }
    rewrite (FOsat_FOBexC _ (B+6) (FOSucc d) _ HinB6 HinSB6).
    exists v3. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above d _ (B+4) v2 ltac:(lia)).
      rewrite (FOeval_update_above d _ (B+2) v1 ltac:(lia)).
      rewrite (FOeval_update_above d e B v0 Hd). lia. }
    set (e4 := FOupdate (FOupdate (FOupdate (FOupdate e B v0)
                 (B+2) v1) (B+4) v2) (B+6) v3).
    apply (proj2 (FOsat_FOPATF p e4 (B+8) _ d Henv Hd8)).
    assert (Ed : FOeval e4 d = FOeval e d).
    { unfold e4.
      rewrite (FOeval_update_above d _ (B+6) v3 ltac:(lia)).
      rewrite (FOeval_update_above d _ (B+4) v2 ltac:(lia)).
      rewrite (FOeval_update_above d _ (B+2) v1 ltac:(lia)).
      exact (FOeval_update_above d e B v0 Hd). }
    rewrite Ed, <- Hsem.
    apply cpat_sem_ext. intro s.
    destruct s as [|[|[|[|s]]]]; cbn.
    + unfold e4, FOupdate.
      rewrite EB6, EB4, EB2, Nat.eqb_refl. reflexivity.
    + unfold e4, FOupdate.
      rewrite E26, E24, Nat.eqb_refl. reflexivity.
    + unfold e4, FOupdate. rewrite E46, Nat.eqb_refl. reflexivity.
    + unfold e4, FOupdate. rewrite Nat.eqb_refl. reflexivity.
    + destruct s; reflexivity.
Qed.

(** The semantic mirror of the Robinson-axiom recognizer: the code is
    one of the seven scheme shapes over component codes. *)

Definition axq_sem (d : nat) : Prop :=
  (exists a b, d = cpair 2 (cpair
     (cpair 0 (cpair (cpair 2 a) (cpair 2 b)))
     (cpair 0 (cpair a b))))
  \/ (exists a, d = cpair 2 (cpair
     (cpair 0 (cpair (cpair 2 a) (cpair 1 0)))
     (cpair 1 0)))
  \/ (exists x, d = cpair 2 (cpair
     (cpair 2 (cpair (cpair 0 (cpair (cpair 0 x) (cpair 1 0)))
                     (cpair 1 0)))
     (cpair 4 (cpair (S x)
        (cpair 0 (cpair (cpair 0 x) (cpair 2 (cpair 0 (S x)))))))))
  \/ (exists a, d = cpair 0 (cpair (cpair 3 (cpair a (cpair 1 0))) a))
  \/ (exists a b, d = cpair 0 (cpair
     (cpair 3 (cpair a (cpair 2 b)))
     (cpair 2 (cpair 3 (cpair a b)))))
  \/ (exists a, d = cpair 0 (cpair (cpair 4 (cpair a (cpair 1 0)))
                                   (cpair 1 0)))
  \/ (exists a b, d = cpair 0 (cpair
     (cpair 4 (cpair a (cpair 2 b)))
     (cpair 3 (cpair (cpair 4 (cpair a b)) a)))).

Lemma FOsat_FOAXQ1c : forall e B d,
  FOmax_var_tm d < B ->
  (FOsat e (FOAXQ1c B d) <->
   exists a b, FOeval e d = cpair 2 (cpair
     (cpair 0 (cpair (cpair 2 a) (cpair 2 b)))
     (cpair 0 (cpair a b)))).
Proof.
  intros e B d Hd. unfold FOAXQ1c.
  rewrite (FOsat_pat2 e B cpatQ1 d Hd).
  split.
  - intros [v0 [v1 [_ [_ Hs]]]].
    cbn [cpat_sem cpatQ1 pImpP pEqP tSuccP] in Hs.
    exists v0, v1. symmetry. exact Hs.
  - intros [a [b Heq]].
    pose proof (cpat_occurs_le cpatQ1
      (fun s => match s with 0 => a | 1 => b | _ => 0 end) 0
      eq_refl) as Ha.
    pose proof (cpat_occurs_le cpatQ1
      (fun s => match s with 0 => a | 1 => b | _ => 0 end) 1
      eq_refl) as Hb.
    cbn [cpat_sem cpatQ1 pImpP pEqP tSuccP] in Ha, Hb.
    exists a, b.
    split; [rewrite Heq; exact Ha|].
    split; [rewrite Heq; exact Hb|].
    cbn [cpat_sem cpatQ1 pImpP pEqP tSuccP].
    symmetry. exact Heq.
Qed.

Lemma FOsat_FOAXQ2c : forall e B d,
  FOmax_var_tm d < B ->
  (FOsat e (FOAXQ2c B d) <->
   exists a, FOeval e d = cpair 2 (cpair
     (cpair 0 (cpair (cpair 2 a) (cpair 1 0)))
     (cpair 1 0))).
Proof.
  intros e B d Hd. unfold FOAXQ2c.
  rewrite (FOsat_pat1 e B cpatQ2 d Hd).
  split.
  - intros [v0 [_ Hs]].
    cbn [cpat_sem cpatQ2 pImpP pEqP tSuccP tZeroP pFlsP] in Hs.
    exists v0. symmetry. exact Hs.
  - intros [a Heq].
    pose proof (cpat_occurs_le cpatQ2
      (fun s => match s with 0 => a | _ => 0 end) 0 eq_refl) as Ha.
    cbn [cpat_sem cpatQ2 pImpP pEqP tSuccP tZeroP pFlsP] in Ha.
    exists a.
    split; [rewrite Heq; exact Ha|].
    cbn [cpat_sem cpatQ2 pImpP pEqP tSuccP tZeroP pFlsP].
    symmetry. exact Heq.
Qed.

Lemma FOsat_FOAXQ3c : forall e B d,
  FOmax_var_tm d < B ->
  (FOsat e (FOAXQ3c B d) <->
   exists x, FOeval e d = cpair 2 (cpair
     (cpair 2 (cpair (cpair 0 (cpair (cpair 0 x) (cpair 1 0)))
                     (cpair 1 0)))
     (cpair 4 (cpair (S x)
        (cpair 0 (cpair (cpair 0 x) (cpair 2 (cpair 0 (S x))))))))).
Proof.
  intros e B d Hd. unfold FOAXQ3c.
  rewrite (FOsat_pat1 e B cpatQ3 d Hd).
  split.
  - intros [v0 [_ Hs]].
    cbn [cpat_sem cpatQ3 pImpP pEqP pExP tVarP tSuccP tZeroP
         pFlsP] in Hs.
    exists v0. symmetry. exact Hs.
  - intros [x Heq].
    pose proof (cpat_occurs_le cpatQ3
      (fun s => match s with 0 => x | _ => 0 end) 0 eq_refl) as Hx.
    cbn [cpat_sem cpatQ3 pImpP pEqP pExP tVarP tSuccP tZeroP
         pFlsP] in Hx.
    exists x.
    split; [rewrite Heq; lia|].
    cbn [cpat_sem cpatQ3 pImpP pEqP pExP tVarP tSuccP tZeroP pFlsP].
    symmetry. exact Heq.
Qed.

Lemma FOsat_FOAXQ4c : forall e B d,
  FOmax_var_tm d < B ->
  (FOsat e (FOAXQ4c B d) <->
   exists a, FOeval e d
     = cpair 0 (cpair (cpair 3 (cpair a (cpair 1 0))) a)).
Proof.
  intros e B d Hd. unfold FOAXQ4c.
  rewrite (FOsat_pat1 e B cpatQ4 d Hd).
  split.
  - intros [v0 [_ Hs]].
    cbn [cpat_sem cpatQ4 pEqP tPlusP tZeroP] in Hs.
    exists v0. symmetry. exact Hs.
  - intros [a Heq].
    pose proof (cpat_occurs_le cpatQ4
      (fun s => match s with 0 => a | _ => 0 end) 0 eq_refl) as Ha.
    cbn [cpat_sem cpatQ4 pEqP tPlusP tZeroP] in Ha.
    exists a.
    split; [rewrite Heq; exact Ha|].
    cbn [cpat_sem cpatQ4 pEqP tPlusP tZeroP].
    symmetry. exact Heq.
Qed.

Lemma FOsat_FOAXQ5c : forall e B d,
  FOmax_var_tm d < B ->
  (FOsat e (FOAXQ5c B d) <->
   exists a b, FOeval e d = cpair 0 (cpair
     (cpair 3 (cpair a (cpair 2 b)))
     (cpair 2 (cpair 3 (cpair a b))))).
Proof.
  intros e B d Hd. unfold FOAXQ5c.
  rewrite (FOsat_pat2 e B cpatQ5 d Hd).
  split.
  - intros [v0 [v1 [_ [_ Hs]]]].
    cbn [cpat_sem cpatQ5 pEqP tPlusP tSuccP] in Hs.
    exists v0, v1. symmetry. exact Hs.
  - intros [a [b Heq]].
    pose proof (cpat_occurs_le cpatQ5
      (fun s => match s with 0 => a | 1 => b | _ => 0 end) 0
      eq_refl) as Ha.
    pose proof (cpat_occurs_le cpatQ5
      (fun s => match s with 0 => a | 1 => b | _ => 0 end) 1
      eq_refl) as Hb.
    cbn [cpat_sem cpatQ5 pEqP tPlusP tSuccP] in Ha, Hb.
    exists a, b.
    split; [rewrite Heq; exact Ha|].
    split; [rewrite Heq; exact Hb|].
    cbn [cpat_sem cpatQ5 pEqP tPlusP tSuccP].
    symmetry. exact Heq.
Qed.

Lemma FOsat_FOAXQ6c : forall e B d,
  FOmax_var_tm d < B ->
  (FOsat e (FOAXQ6c B d) <->
   exists a, FOeval e d
     = cpair 0 (cpair (cpair 4 (cpair a (cpair 1 0))) (cpair 1 0))).
Proof.
  intros e B d Hd. unfold FOAXQ6c.
  rewrite (FOsat_pat1 e B cpatQ6 d Hd).
  split.
  - intros [v0 [_ Hs]].
    cbn [cpat_sem cpatQ6 pEqP tMultP tZeroP] in Hs.
    exists v0. symmetry. exact Hs.
  - intros [a Heq].
    pose proof (cpat_occurs_le cpatQ6
      (fun s => match s with 0 => a | _ => 0 end) 0 eq_refl) as Ha.
    cbn [cpat_sem cpatQ6 pEqP tMultP tZeroP] in Ha.
    exists a.
    split; [rewrite Heq; exact Ha|].
    cbn [cpat_sem cpatQ6 pEqP tMultP tZeroP].
    symmetry. exact Heq.
Qed.

Lemma FOsat_FOAXQ7c : forall e B d,
  FOmax_var_tm d < B ->
  (FOsat e (FOAXQ7c B d) <->
   exists a b, FOeval e d = cpair 0 (cpair
     (cpair 4 (cpair a (cpair 2 b)))
     (cpair 3 (cpair (cpair 4 (cpair a b)) a)))).
Proof.
  intros e B d Hd. unfold FOAXQ7c.
  rewrite (FOsat_pat2 e B cpatQ7 d Hd).
  split.
  - intros [v0 [v1 [_ [_ Hs]]]].
    cbn [cpat_sem cpatQ7 pEqP tMultP tPlusP tSuccP] in Hs.
    exists v0, v1. symmetry. exact Hs.
  - intros [a [b Heq]].
    pose proof (cpat_occurs_le cpatQ7
      (fun s => match s with 0 => a | 1 => b | _ => 0 end) 0
      eq_refl) as Ha.
    pose proof (cpat_occurs_le cpatQ7
      (fun s => match s with 0 => a | 1 => b | _ => 0 end) 1
      eq_refl) as Hb.
    cbn [cpat_sem cpatQ7 pEqP tMultP tPlusP tSuccP] in Ha, Hb.
    exists a, b.
    split; [rewrite Heq; exact Ha|].
    split; [rewrite Heq; exact Hb|].
    cbn [cpat_sem cpatQ7 pEqP tMultP tPlusP tSuccP].
    symmetry. exact Heq.
Qed.

Lemma FOsat_FOAXQc : forall e B d,
  FOmax_var_tm d < B ->
  (FOsat e (FOAXQc B d) <-> axq_sem (FOeval e d)).
Proof.
  intros e B d Hd. unfold FOAXQc, axq_sem.
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOAXQ1c e B d Hd).
  rewrite (FOsat_FOAXQ2c e B d Hd).
  rewrite (FOsat_FOAXQ3c e B d Hd).
  rewrite (FOsat_FOAXQ4c e B d Hd).
  rewrite (FOsat_FOAXQ5c e B d Hd).
  rewrite (FOsat_FOAXQ6c e B d Hd).
  rewrite (FOsat_FOAXQ7c e B d Hd).
  reflexivity.
Qed.

Lemma FOdelta0_pat1 : forall B p d,
  FOmax_var_tm d < B ->
  FOdelta0 (FOBexC B (FOSucc d) (FOPATF (B+2) [FOVar B] p d)).
Proof.
  intros B p d Hd.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; exact Hd
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOPATF.
  - constructor; [cbn; lia | constructor].
  - lia.
Qed.

Lemma FOdelta0_pat2 : forall B p d,
  FOmax_var_tm d < B ->
  FOdelta0 (FOBexC B (FOSucc d)
              (FOBexC (B+2) (FOSucc d)
                 (FOPATF (B+4) [FOVar B; FOVar (B+2)] p d))).
Proof.
  intros B p d Hd.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; exact Hd
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOPATF.
  - constructor; [cbn; lia | constructor; [cbn; lia | constructor]].
  - lia.
Qed.

Lemma FOdelta0_pat3 : forall B p d,
  FOmax_var_tm d < B ->
  FOdelta0 (FOBexC B (FOSucc d)
              (FOBexC (B+2) (FOSucc d)
                 (FOBexC (B+4) (FOSucc d)
                    (FOPATF (B+6) [FOVar B; FOVar (B+2); FOVar (B+4)]
                       p d)))).
Proof.
  intros B p d Hd.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; exact Hd
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOPATF.
  - constructor; [cbn; lia |
      constructor; [cbn; lia |
      constructor; [cbn; lia | constructor]]].
  - lia.
Qed.

Lemma FOdelta0_pat4 : forall B p d,
  FOmax_var_tm d < B ->
  FOdelta0 (FOBexC B (FOSucc d)
              (FOBexC (B+2) (FOSucc d)
                 (FOBexC (B+4) (FOSucc d)
                    (FOBexC (B+6) (FOSucc d)
                       (FOPATF (B+8)
                          [FOVar B; FOVar (B+2); FOVar (B+4);
                           FOVar (B+6)] p d))))).
Proof.
  intros B p d Hd.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; exact Hd
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOPATF.
  - constructor; [cbn; lia |
      constructor; [cbn; lia |
      constructor; [cbn; lia |
      constructor; [cbn; lia | constructor]]]].
  - lia.
Qed.

Lemma FOdelta0_FOAXQc : forall B d,
  FOmax_var_tm d < B ->
  FOdelta0 (FOAXQc B d).
Proof.
  intros B d Hd. unfold FOAXQc.
  unfold FOAXQ1c, FOAXQ2c, FOAXQ3c, FOAXQ4c, FOAXQ5c, FOAXQ6c,
    FOAXQ7c.
  apply FOdelta0_or; [apply FOdelta0_pat2; exact Hd|].
  apply FOdelta0_or; [apply FOdelta0_pat1; exact Hd|].
  apply FOdelta0_or; [apply FOdelta0_pat1; exact Hd|].
  apply FOdelta0_or; [apply FOdelta0_pat1; exact Hd|].
  apply FOdelta0_or; [apply FOdelta0_pat2; exact Hd|].
  apply FOdelta0_or; [apply FOdelta0_pat1; exact Hd|].
  apply FOdelta0_pat2; exact Hd.
Qed.

(** The semantic mirror of the logical-axiom recognizer.  The lookup
    relation [L] carries the freshness side conditions of the
    exists-elimination and forall-export shapes through the master
    table's tag-1 rows. *)

Definition logax_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (d : nat) : Prop :=
  (exists P Q, d = cpair 2 (cpair P (cpair 2 (cpair Q P))))
  \/ (exists P Q R, d = cpair 2 (cpair
       (cpair 2 (cpair P (cpair 2 (cpair Q R))))
       (cpair 2 (cpair (cpair 2 (cpair P Q))
                       (cpair 2 (cpair P R))))))
  \/ (exists P, d = cpair 2 (cpair
       (cpair 2 (cpair (cpair 2 (cpair P (cpair 1 0))) (cpair 1 0)))
       P))
  \/ (exists a, d = cpair 0 (cpair a a))
  \/ (exists a b, d = cpair 2 (cpair (cpair 0 (cpair a b))
                                     (cpair 0 (cpair b a))))
  \/ (exists a b c, d = cpair 2 (cpair
       (cpair 0 (cpair a b))
       (cpair 2 (cpair (cpair 0 (cpair b c)) (cpair 0 (cpair a c))))))
  \/ (exists a b, d = cpair 2 (cpair
       (cpair 0 (cpair a b))
       (cpair 0 (cpair (cpair 2 a) (cpair 2 b)))))
  \/ (exists a b c dd, d = cpair 2 (cpair
       (cpair 0 (cpair a b))
       (cpair 2 (cpair (cpair 0 (cpair c dd))
          (cpair 0 (cpair (cpair 3 (cpair a c))
                          (cpair 3 (cpair b dd))))))))
  \/ (exists a b c dd, d = cpair 2 (cpair
       (cpair 0 (cpair a b))
       (cpair 2 (cpair (cpair 0 (cpair c dd))
          (cpair 0 (cpair (cpair 4 (cpair a c))
                          (cpair 4 (cpair b dd))))))))
  \/ (exists x P Q, d = cpair 2 (cpair
       (cpair 3 (cpair x (cpair 2 (cpair P Q))))
       (cpair 2 (cpair (cpair 4 (cpair x P)) Q))) /\ L 1 x Q 0 0)
  \/ (exists x P Q, d = cpair 2 (cpair
       (cpair 3 (cpair x (cpair 2 (cpair P Q))))
       (cpair 2 (cpair (cpair 3 (cpair x P)) (cpair 3 (cpair x Q))))))
  \/ (exists x P Q, d = cpair 2 (cpair
       (cpair 3 (cpair x (cpair 2 (cpair P Q))))
       (cpair 2 (cpair P (cpair 3 (cpair x Q))))) /\ L 1 x P 0 0).

Lemma FOsat_FOLOG1c : forall e B d,
  FOmax_var_tm d < B ->
  (FOsat e (FOLOG1c B d) <->
   exists P Q, FOeval e d = cpair 2 (cpair P (cpair 2 (cpair Q P)))).
Proof.
  intros e B d Hd. unfold FOLOG1c.
  rewrite (FOsat_pat2 e B cpatLK d Hd).
  split.
  - intros [v0 [v1 [_ [_ Hs]]]].
    cbn [cpat_sem cpatLK pImpP] in Hs.
    exists v0, v1. symmetry. exact Hs.
  - intros [P [Q Heq]].
    pose proof (cpat_occurs_le cpatLK
      (fun s => match s with 0 => P | 1 => Q | _ => 0 end) 0
      eq_refl) as HP.
    pose proof (cpat_occurs_le cpatLK
      (fun s => match s with 0 => P | 1 => Q | _ => 0 end) 1
      eq_refl) as HQ.
    cbn [cpat_sem cpatLK pImpP] in HP, HQ.
    exists P, Q.
    split; [rewrite Heq; exact HP|].
    split; [rewrite Heq; exact HQ|].
    cbn [cpat_sem cpatLK pImpP].
    symmetry. exact Heq.
Qed.

Lemma FOsat_FOLOG2c : forall e B d,
  FOmax_var_tm d < B ->
  (FOsat e (FOLOG2c B d) <->
   exists P Q R, FOeval e d = cpair 2 (cpair
     (cpair 2 (cpair P (cpair 2 (cpair Q R))))
     (cpair 2 (cpair (cpair 2 (cpair P Q)) (cpair 2 (cpair P R)))))).
Proof.
  intros e B d Hd. unfold FOLOG2c.
  rewrite (FOsat_pat3 e B cpatLS d Hd).
  split.
  - intros [v0 [v1 [v2 [_ [_ [_ Hs]]]]]].
    cbn [cpat_sem cpatLS pImpP] in Hs.
    exists v0, v1, v2. symmetry. exact Hs.
  - intros [P [Q [R Heq]]].
    pose proof (cpat_occurs_le cpatLS
      (fun s => match s with 0 => P | 1 => Q | 2 => R | _ => 0 end) 0
      eq_refl) as HP.
    pose proof (cpat_occurs_le cpatLS
      (fun s => match s with 0 => P | 1 => Q | 2 => R | _ => 0 end) 1
      eq_refl) as HQ.
    pose proof (cpat_occurs_le cpatLS
      (fun s => match s with 0 => P | 1 => Q | 2 => R | _ => 0 end) 2
      eq_refl) as HR.
    cbn [cpat_sem cpatLS pImpP] in HP, HQ, HR.
    exists P, Q, R.
    split; [rewrite Heq; exact HP|].
    split; [rewrite Heq; exact HQ|].
    split; [rewrite Heq; exact HR|].
    cbn [cpat_sem cpatLS pImpP].
    symmetry. exact Heq.
Qed.

Lemma FOsat_FOLOG3c : forall e B d,
  FOmax_var_tm d < B ->
  (FOsat e (FOLOG3c B d) <->
   exists P, FOeval e d = cpair 2 (cpair
     (cpair 2 (cpair (cpair 2 (cpair P (cpair 1 0))) (cpair 1 0)))
     P)).
Proof.
  intros e B d Hd. unfold FOLOG3c.
  rewrite (FOsat_pat1 e B cpatLDN d Hd).
  split.
  - intros [v0 [_ Hs]].
    cbn [cpat_sem cpatLDN pImpP pFlsP] in Hs.
    exists v0. symmetry. exact Hs.
  - intros [P Heq].
    pose proof (cpat_occurs_le cpatLDN
      (fun s => match s with 0 => P | _ => 0 end) 0 eq_refl) as HP.
    cbn [cpat_sem cpatLDN pImpP pFlsP] in HP.
    exists P.
    split; [rewrite Heq; exact HP|].
    cbn [cpat_sem cpatLDN pImpP pFlsP].
    symmetry. exact Heq.
Qed.

Lemma FOsat_FOLOG4c : forall e B d,
  FOmax_var_tm d < B ->
  (FOsat e (FOLOG4c B d) <->
   exists a, FOeval e d = cpair 0 (cpair a a)).
Proof.
  intros e B d Hd. unfold FOLOG4c.
  rewrite (FOsat_pat1 e B cpatLEqRefl d Hd).
  split.
  - intros [v0 [_ Hs]].
    cbn [cpat_sem cpatLEqRefl pEqP] in Hs.
    exists v0. symmetry. exact Hs.
  - intros [a Heq].
    pose proof (cpat_occurs_le cpatLEqRefl
      (fun s => match s with 0 => a | _ => 0 end) 0 eq_refl) as Ha.
    cbn [cpat_sem cpatLEqRefl pEqP] in Ha.
    exists a.
    split; [rewrite Heq; exact Ha|].
    cbn [cpat_sem cpatLEqRefl pEqP].
    symmetry. exact Heq.
Qed.

Lemma FOsat_FOLOG5c : forall e B d,
  FOmax_var_tm d < B ->
  (FOsat e (FOLOG5c B d) <->
   exists a b, FOeval e d = cpair 2 (cpair (cpair 0 (cpair a b))
                                           (cpair 0 (cpair b a)))).
Proof.
  intros e B d Hd. unfold FOLOG5c.
  rewrite (FOsat_pat2 e B cpatLEqSym d Hd).
  split.
  - intros [v0 [v1 [_ [_ Hs]]]].
    cbn [cpat_sem cpatLEqSym pImpP pEqP] in Hs.
    exists v0, v1. symmetry. exact Hs.
  - intros [a [b Heq]].
    pose proof (cpat_occurs_le cpatLEqSym
      (fun s => match s with 0 => a | 1 => b | _ => 0 end) 0
      eq_refl) as Ha.
    pose proof (cpat_occurs_le cpatLEqSym
      (fun s => match s with 0 => a | 1 => b | _ => 0 end) 1
      eq_refl) as Hb.
    cbn [cpat_sem cpatLEqSym pImpP pEqP] in Ha, Hb.
    exists a, b.
    split; [rewrite Heq; exact Ha|].
    split; [rewrite Heq; exact Hb|].
    cbn [cpat_sem cpatLEqSym pImpP pEqP].
    symmetry. exact Heq.
Qed.

Lemma FOsat_FOLOG6c : forall e B d,
  FOmax_var_tm d < B ->
  (FOsat e (FOLOG6c B d) <->
   exists a b c, FOeval e d = cpair 2 (cpair
     (cpair 0 (cpair a b))
     (cpair 2 (cpair (cpair 0 (cpair b c)) (cpair 0 (cpair a c)))))).
Proof.
  intros e B d Hd. unfold FOLOG6c.
  rewrite (FOsat_pat3 e B cpatLEqTrans d Hd).
  split.
  - intros [v0 [v1 [v2 [_ [_ [_ Hs]]]]]].
    cbn [cpat_sem cpatLEqTrans pImpP pEqP] in Hs.
    exists v0, v1, v2. symmetry. exact Hs.
  - intros [a [b [c Heq]]].
    pose proof (cpat_occurs_le cpatLEqTrans
      (fun s => match s with 0 => a | 1 => b | 2 => c | _ => 0 end) 0
      eq_refl) as Ha.
    pose proof (cpat_occurs_le cpatLEqTrans
      (fun s => match s with 0 => a | 1 => b | 2 => c | _ => 0 end) 1
      eq_refl) as Hb.
    pose proof (cpat_occurs_le cpatLEqTrans
      (fun s => match s with 0 => a | 1 => b | 2 => c | _ => 0 end) 2
      eq_refl) as Hc.
    cbn [cpat_sem cpatLEqTrans pImpP pEqP] in Ha, Hb, Hc.
    exists a, b, c.
    split; [rewrite Heq; exact Ha|].
    split; [rewrite Heq; exact Hb|].
    split; [rewrite Heq; exact Hc|].
    cbn [cpat_sem cpatLEqTrans pImpP pEqP].
    symmetry. exact Heq.
Qed.

Lemma FOsat_FOLOG7c : forall e B d,
  FOmax_var_tm d < B ->
  (FOsat e (FOLOG7c B d) <->
   exists a b, FOeval e d = cpair 2 (cpair
     (cpair 0 (cpair a b))
     (cpair 0 (cpair (cpair 2 a) (cpair 2 b))))).
Proof.
  intros e B d Hd. unfold FOLOG7c.
  rewrite (FOsat_pat2 e B cpatLCongS d Hd).
  split.
  - intros [v0 [v1 [_ [_ Hs]]]].
    cbn [cpat_sem cpatLCongS pImpP pEqP tSuccP] in Hs.
    exists v0, v1. symmetry. exact Hs.
  - intros [a [b Heq]].
    pose proof (cpat_occurs_le cpatLCongS
      (fun s => match s with 0 => a | 1 => b | _ => 0 end) 0
      eq_refl) as Ha.
    pose proof (cpat_occurs_le cpatLCongS
      (fun s => match s with 0 => a | 1 => b | _ => 0 end) 1
      eq_refl) as Hb.
    cbn [cpat_sem cpatLCongS pImpP pEqP tSuccP] in Ha, Hb.
    exists a, b.
    split; [rewrite Heq; exact Ha|].
    split; [rewrite Heq; exact Hb|].
    cbn [cpat_sem cpatLCongS pImpP pEqP tSuccP].
    symmetry. exact Heq.
Qed.

Lemma FOsat_FOLOG8c : forall e B d,
  FOmax_var_tm d < B ->
  (FOsat e (FOLOG8c B d) <->
   exists a b c dd, FOeval e d = cpair 2 (cpair
     (cpair 0 (cpair a b))
     (cpair 2 (cpair (cpair 0 (cpair c dd))
        (cpair 0 (cpair (cpair 3 (cpair a c))
                        (cpair 3 (cpair b dd)))))))).
Proof.
  intros e B d Hd. unfold FOLOG8c.
  rewrite (FOsat_pat4 e B cpatLCongPlus d Hd).
  split.
  - intros [v0 [v1 [v2 [v3 [_ [_ [_ [_ Hs]]]]]]]].
    cbn [cpat_sem cpatLCongPlus pImpP pEqP tPlusP] in Hs.
    exists v0, v1, v2, v3. symmetry. exact Hs.
  - intros [a [b [c [dd Heq]]]].
    pose proof (cpat_occurs_le cpatLCongPlus
      (fun s => match s with
                | 0 => a | 1 => b | 2 => c | 3 => dd | _ => 0 end) 0
      eq_refl) as Ha.
    pose proof (cpat_occurs_le cpatLCongPlus
      (fun s => match s with
                | 0 => a | 1 => b | 2 => c | 3 => dd | _ => 0 end) 1
      eq_refl) as Hb.
    pose proof (cpat_occurs_le cpatLCongPlus
      (fun s => match s with
                | 0 => a | 1 => b | 2 => c | 3 => dd | _ => 0 end) 2
      eq_refl) as Hc.
    pose proof (cpat_occurs_le cpatLCongPlus
      (fun s => match s with
                | 0 => a | 1 => b | 2 => c | 3 => dd | _ => 0 end) 3
      eq_refl) as Hdd.
    cbn [cpat_sem cpatLCongPlus pImpP pEqP tPlusP] in Ha, Hb, Hc, Hdd.
    exists a, b, c, dd.
    split; [rewrite Heq; exact Ha|].
    split; [rewrite Heq; exact Hb|].
    split; [rewrite Heq; exact Hc|].
    split; [rewrite Heq; exact Hdd|].
    cbn [cpat_sem cpatLCongPlus pImpP pEqP tPlusP].
    symmetry. exact Heq.
Qed.

Lemma FOsat_FOLOG9c : forall e B d,
  FOmax_var_tm d < B ->
  (FOsat e (FOLOG9c B d) <->
   exists a b c dd, FOeval e d = cpair 2 (cpair
     (cpair 0 (cpair a b))
     (cpair 2 (cpair (cpair 0 (cpair c dd))
        (cpair 0 (cpair (cpair 4 (cpair a c))
                        (cpair 4 (cpair b dd)))))))).
Proof.
  intros e B d Hd. unfold FOLOG9c.
  rewrite (FOsat_pat4 e B cpatLCongMult d Hd).
  split.
  - intros [v0 [v1 [v2 [v3 [_ [_ [_ [_ Hs]]]]]]]].
    cbn [cpat_sem cpatLCongMult pImpP pEqP tMultP] in Hs.
    exists v0, v1, v2, v3. symmetry. exact Hs.
  - intros [a [b [c [dd Heq]]]].
    pose proof (cpat_occurs_le cpatLCongMult
      (fun s => match s with
                | 0 => a | 1 => b | 2 => c | 3 => dd | _ => 0 end) 0
      eq_refl) as Ha.
    pose proof (cpat_occurs_le cpatLCongMult
      (fun s => match s with
                | 0 => a | 1 => b | 2 => c | 3 => dd | _ => 0 end) 1
      eq_refl) as Hb.
    pose proof (cpat_occurs_le cpatLCongMult
      (fun s => match s with
                | 0 => a | 1 => b | 2 => c | 3 => dd | _ => 0 end) 2
      eq_refl) as Hc.
    pose proof (cpat_occurs_le cpatLCongMult
      (fun s => match s with
                | 0 => a | 1 => b | 2 => c | 3 => dd | _ => 0 end) 3
      eq_refl) as Hdd.
    cbn [cpat_sem cpatLCongMult pImpP pEqP tMultP] in Ha, Hb, Hc, Hdd.
    exists a, b, c, dd.
    split; [rewrite Heq; exact Ha|].
    split; [rewrite Heq; exact Hb|].
    split; [rewrite Heq; exact Hc|].
    split; [rewrite Heq; exact Hdd|].
    cbn [cpat_sem cpatLCongMult pImpP pEqP tMultP].
    symmetry. exact Heq.
Qed.

Lemma FOsat_FOLOG11c : forall e B d,
  FOmax_var_tm d < B ->
  (FOsat e (FOLOG11c B d) <->
   exists x P Q, FOeval e d = cpair 2 (cpair
     (cpair 3 (cpair x (cpair 2 (cpair P Q))))
     (cpair 2 (cpair (cpair 3 (cpair x P))
                     (cpair 3 (cpair x Q)))))).
Proof.
  intros e B d Hd. unfold FOLOG11c.
  rewrite (FOsat_pat3 e B cpatLAllK d Hd).
  split.
  - intros [v0 [v1 [v2 [_ [_ [_ Hs]]]]]].
    cbn [cpat_sem cpatLAllK pImpP pAllP] in Hs.
    exists v0, v1, v2. symmetry. exact Hs.
  - intros [x [P [Q Heq]]].
    pose proof (cpat_occurs_le cpatLAllK
      (fun s => match s with 0 => x | 1 => P | 2 => Q | _ => 0 end) 0
      eq_refl) as Hx.
    pose proof (cpat_occurs_le cpatLAllK
      (fun s => match s with 0 => x | 1 => P | 2 => Q | _ => 0 end) 1
      eq_refl) as HP.
    pose proof (cpat_occurs_le cpatLAllK
      (fun s => match s with 0 => x | 1 => P | 2 => Q | _ => 0 end) 2
      eq_refl) as HQ.
    cbn [cpat_sem cpatLAllK pImpP pAllP] in Hx, HP, HQ.
    exists x, P, Q.
    split; [rewrite Heq; exact Hx|].
    split; [rewrite Heq; exact HP|].
    split; [rewrite Heq; exact HQ|].
    cbn [cpat_sem cpatLAllK pImpP pAllP].
    symmetry. exact Heq.
Qed.

Lemma FOsat_FObetaF : forall e v c d i x,
  FOmax_var_tm c < v -> FOmax_var_tm d < v ->
  FOmax_var_tm i < v -> FOmax_var_tm x < v ->
  (FOsat e (FObetaF v c d i x)
   <-> beta (FOeval e c) (FOeval e d) (FOeval e i) = FOeval e x).
Proof.
  intros e v c d i x Hc Hd Hi Hx.
  assert (HinSc_v : FOin_tm v (FOSucc c) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSc_Sv : FOin_tm (S v) (FOSucc c) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinM_2 : FOin_tm (S (S v))
      (FOSucc (FOMult d (FOSucc i))) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinM_3 : FOin_tm (S (S (S v)))
      (FOSucc (FOMult d (FOSucc i))) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (Hin_c_v : FOin_tm v c = false) by (apply FOin_tm_above; lia).
  assert (Hin_d_v : FOin_tm v d = false) by (apply FOin_tm_above; lia).
  assert (Hin_i_v : FOin_tm v i = false) by (apply FOin_tm_above; lia).
  assert (Hin_x_v : FOin_tm v x = false) by (apply FOin_tm_above; lia).
  assert (Hin_d_2 : FOin_tm (S (S v)) d = false)
    by (apply FOin_tm_above; lia).
  assert (Hin_i_2 : FOin_tm (S (S v)) i = false)
    by (apply FOin_tm_above; lia).
  assert (Hin_x_2 : FOin_tm (S (S v)) x = false)
    by (apply FOin_tm_above; lia).
  unfold FObetaF.
  split.
  - intro H.
    apply (proj1 (FOsat_FOBexC e v (FOSucc c) _ HinSc_v HinSc_Sv)) in H.
    destruct H as [q [Hqlt Hq]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hq.
    destruct Hq as [H1 H2].
    apply (proj1 (FOsat_FOBexC _ (S (S v))
                    (FOSucc (FOMult d (FOSucc i))) _ HinM_2 HinM_3)) in H2.
    destruct H2 as [z [Hzlt Hz]].
    cbn -[Nat.eqb FOupdate] in H1.
    rewrite (FOeval_update_not_in c _ v q Hin_c_v) in H1.
    rewrite (FOeval_update_not_in d _ v q Hin_d_v) in H1.
    rewrite (FOeval_update_not_in i _ v q Hin_i_v) in H1.
    rewrite (FOeval_update_not_in x _ v q Hin_x_v) in H1.
    unfold FOupdate in H1. rewrite Nat.eqb_refl in H1. cbn in H1.
    cbn -[Nat.eqb FOupdate] in Hz.
    rewrite (FOeval_update_not_in x _ (S (S v)) z Hin_x_2) in Hz.
    rewrite (FOeval_update_not_in d _ (S (S v)) z Hin_d_2) in Hz.
    rewrite (FOeval_update_not_in i _ (S (S v)) z Hin_i_2) in Hz.
    rewrite (FOeval_update_not_in x _ v q Hin_x_v) in Hz.
    rewrite (FOeval_update_not_in d _ v q Hin_d_v) in Hz.
    rewrite (FOeval_update_not_in i _ v q Hin_i_v) in Hz.
    unfold FOupdate in Hz. rewrite Nat.eqb_refl in Hz. cbn in Hz.
    apply beta_spec.
    exists q. split; lia.
  - intro H. apply beta_spec in H. destruct H as [q [Hceq Hxlt]].
    apply (proj2 (FOsat_FOBexC e v (FOSucc c) _ HinSc_v HinSc_Sv)).
    exists q. split.
    + cbn. nia.
    + apply (proj2 (FOsat_FOAnd _ _ _)). split.
      * cbn -[Nat.eqb FOupdate].
        rewrite (FOeval_update_not_in c _ v q Hin_c_v).
        rewrite (FOeval_update_not_in d _ v q Hin_d_v).
        rewrite (FOeval_update_not_in i _ v q Hin_i_v).
        rewrite (FOeval_update_not_in x _ v q Hin_x_v).
        unfold FOupdate. rewrite Nat.eqb_refl. cbn. lia.
      * apply (proj2 (FOsat_FOBexC _ (S (S v))
                        (FOSucc (FOMult d (FOSucc i))) _ HinM_2 HinM_3)).
        assert (HMq : FOeval (FOupdate e v q)
                        (FOSucc (FOMult d (FOSucc i)))
                      = FOeval e d * S (FOeval e i) + 1).
        { cbn -[Nat.eqb FOupdate].
          rewrite (FOeval_update_not_in d _ v q Hin_d_v),
                  (FOeval_update_not_in i _ v q Hin_i_v). lia. }
        rewrite HMq.
        exists (FOeval e d * S (FOeval e i) - FOeval e x).
        split.
        -- lia.
        -- cbn -[Nat.eqb FOupdate].
           rewrite (FOeval_update_not_in x _ (S (S v)) _ Hin_x_2).
           rewrite (FOeval_update_not_in d _ (S (S v)) _ Hin_d_2).
           rewrite (FOeval_update_not_in i _ (S (S v)) _ Hin_i_2).
           rewrite (FOeval_update_not_in x _ v q Hin_x_v).
           rewrite (FOeval_update_not_in d _ v q Hin_d_v).
           rewrite (FOeval_update_not_in i _ v q Hin_i_v).
           unfold FOupdate. rewrite Nat.eqb_refl. cbn. lia.
Qed.

Lemma FOfree_in_FObetaF_low : forall w v c d i x,
  w < v ->
  FOfree_in w (FObetaF v c d i x)
  = (FOin_tm w c || FOin_tm w d || FOin_tm w i || FOin_tm w x)%bool.
Proof.
  intros w v c d i x Hwv. unfold FObetaF.
  rewrite (FOfree_in_FOBexC w v _ _ ltac:(lia) ltac:(lia)).
  rewrite FOfree_in_FOAnd.
  rewrite (FOfree_in_FOBexC w (S (S v)) _ _ ltac:(lia) ltac:(lia)).
  assert (Evw : Nat.eqb v w = false) by (apply Nat.eqb_neq; lia).
  assert (ESSvw : Nat.eqb (S (S v)) w = false) by (apply Nat.eqb_neq; lia).
  cbn -[Nat.eqb]. rewrite Evw, ESSvw.
  destruct (FOin_tm w c); destruct (FOin_tm w d);
    destruct (FOin_tm w i); destruct (FOin_tm w x); reflexivity.
Qed.

(** ** Free variables of the arithmetization builders.

    Every free variable of a builder application comes from one of
    its argument terms or is one of the two designated low variables;
    the block binders are internal.  The walker descends the
    skeleton, converting block-variable leaks into equations that the
    binder inequalities refute. *)

Lemma FOfree_in_FOExists_neq : forall w y B,
  y <> w -> FOfree_in w (FOExists y B) = FOfree_in w B.
Proof.
  intros w y B Hne. cbn -[Nat.eqb].
  rewrite (proj2 (Nat.eqb_neq y w) Hne). reflexivity.
Qed.

Lemma FOfree_in_FOBexC_args : forall w v t A,
  FOfree_in w (FOBexC v t A) = true ->
  w <> v /\ (FOin_tm w t = true \/ FOfree_in w A = true).
Proof.
  intros w v t A H.
  destruct (Nat.eqb_spec w v) as [->|Hne].
  - rewrite FOfree_in_FOBexC_self in H. discriminate.
  - split; [exact Hne|].
    destruct (Nat.eqb_spec w (S v)) as [->|Hne2].
    + rewrite FOfree_in_FOBexC_succ in H. right. exact H.
    + rewrite (FOfree_in_FOBexC w v t A Hne Hne2) in H.
      apply Bool.orb_true_iff in H. exact H.
Qed.

Lemma FOfree_in_FOBallC_args : forall w v t A,
  FOfree_in w (FOBallC v t A) = true ->
  w <> v /\ (FOin_tm w t = true \/ FOfree_in w A = true).
Proof.
  intros w v t A H.
  destruct (Nat.eqb_spec w v) as [->|Hne].
  - rewrite FOfree_in_FOBallC_self in H. discriminate.
  - split; [exact Hne|].
    destruct (Nat.eqb_spec w (S v)) as [->|Hne2].
    + rewrite FOfree_in_FOBallC_succ in H. right. exact H.
    + rewrite (FOfree_in_FOBallC w v t A Hne Hne2) in H.
      apply Bool.orb_true_iff in H. exact H.
Qed.

Ltac ffree_leaf :=
  match goal with
  | H : FOfree_in _ (FOAnd _ _) = true |- _ =>
      rewrite FOfree_in_FOAnd in H;
      apply Bool.orb_true_iff in H; destruct H as [H|H]
  | H : FOfree_in _ (FOOr _ _) = true |- _ =>
      rewrite FOfree_in_FOOr in H;
      apply Bool.orb_true_iff in H; destruct H as [H|H]
  | H : FOfree_in _ (FONeg _) = true |- _ =>
      rewrite FOfree_in_FONeg in H
  | H : FOfree_in _ (FOcpairF _ _ _) = true |- _ =>
      rewrite FOfree_in_FOcpairF in H;
      apply Bool.orb_true_iff in H; destruct H as [H|H];
      [apply Bool.orb_true_iff in H; destruct H as [H|H]|]
  | H : FOfree_in _ (FOBexC _ _ _) = true |- _ =>
      apply FOfree_in_FOBexC_args in H;
      let Hne := fresh "Hne" in destruct H as [Hne [H|H]]
  | H : FOfree_in _ (FOBallC _ _ _) = true |- _ =>
      apply FOfree_in_FOBallC_args in H;
      let Hne := fresh "Hne" in destruct H as [Hne [H|H]]
  | H : FOfree_in _ (FOEq _ _) = true |- _ =>
      cbn [FOfree_in] in H;
      apply Bool.orb_true_iff in H; destruct H as [H|H]
  | H : FOfree_in _ (FOImplF _ _) = true |- _ =>
      cbn [FOfree_in] in H;
      apply Bool.orb_true_iff in H; destruct H as [H|H]
  | H : FOfree_in _ FOFalseF = true |- _ => discriminate H
  | H : FOin_tm _ (FOSucc _) = true |- _ => cbn [FOin_tm] in H
  | H : FOin_tm _ (FOPlus _ _) = true |- _ =>
      cbn [FOin_tm] in H;
      apply Bool.orb_true_iff in H; destruct H as [H|H]
  | H : FOin_tm _ (FOMult _ _) = true |- _ =>
      cbn [FOin_tm] in H;
      apply Bool.orb_true_iff in H; destruct H as [H|H]
  | H : FOin_tm _ (FOnumeral _) = true |- _ =>
      rewrite FOin_tm_numeral in H; discriminate H
  | H : FOin_tm _ FOZero = true |- _ =>
      cbn [FOin_tm] in H; discriminate H
  | H : FOin_tm _ (FOVar _) = true |- _ => cbn [FOin_tm] in H
  | H : existsb _ (_ :: _) = true |- _ => cbn [existsb] in H
  | H : existsb _ nil = true |- _ => discriminate H
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
  | H : (_ || _)%bool = true |- _ =>
      apply Bool.orb_true_iff in H; destruct H as [H|H]
  | H : false = true |- _ => discriminate H
  end.

Ltac ffin :=
  solve [ subst; repeat first
        [ assumption | lia
        | (left; solve [assumption | lia])
        | right ] ].

Lemma FObetaF_free : forall w v c d i x,
  FOfree_in w (FObetaF v c d i x) = true ->
  FOin_tm w c = true \/ FOin_tm w d = true \/ FOin_tm w i = true
  \/ FOin_tm w x = true \/ w < 2.
Proof.
  intros w v c d i x H. unfold FObetaF in H.
  repeat ffree_leaf; ffin.
Qed.

Lemma FOPATF_free : forall p w B env d,
  FOfree_in w (FOPATF B env p d) = true ->
  existsb (FOin_tm w) env = true \/ FOin_tm w d = true \/ w < 2.
Proof.
  induction p as [k|s|q IH|a IHa b IHb]; intros w B env d H;
    cbn [FOPATF] in H.
  - repeat ffree_leaf; ffin.
  - cbn [FOfree_in] in H. apply Bool.orb_true_iff in H.
    destruct H as [H|H].
    + right; left; exact H.
    + destruct (Nat.lt_ge_cases s (length env)) as [Hs|Hs].
      * left. apply existsb_exists.
        exists (nth s env FOZero).
        split; [apply nth_In; exact Hs|exact H].
      * rewrite nth_overflow in H by exact Hs.
        cbn [FOin_tm] in H. discriminate H.
  - apply FOfree_in_FOBexC_args in H. destruct H as [Hne [H|H]].
    + right; left; exact H.
    + rewrite FOfree_in_FOAnd in H. apply Bool.orb_true_iff in H.
      destruct H as [H|H].
      * repeat ffree_leaf; ffin.
      * apply IH in H. destruct H as [H|[H|H]].
        -- left; exact H.
        -- cbn [FOin_tm] in H. apply Nat.eqb_eq in H. lia.
        -- right; right; exact H.
  - apply FOfree_in_FOBexC_args in H. destruct H as [Hne [H|H]].
    + cbn [FOin_tm] in H. right; left; exact H.
    + apply FOfree_in_FOBexC_args in H. destruct H as [Hne2 [H|H]].
      * cbn [FOin_tm] in H. right; left; exact H.
      * rewrite FOfree_in_FOAnd in H. apply Bool.orb_true_iff in H.
        destruct H as [H|H].
        { rewrite FOfree_in_FOcpairF in H.
          apply Bool.orb_true_iff in H. destruct H as [H|H];
            [apply Bool.orb_true_iff in H; destruct H as [H|H]|].
          - cbn [FOin_tm] in H. apply Nat.eqb_eq in H. lia.
          - cbn [FOin_tm] in H. apply Nat.eqb_eq in H. lia.
          - right; left; exact H. }
        rewrite FOfree_in_FOAnd in H. apply Bool.orb_true_iff in H.
        destruct H as [H|H].
        { apply IHa in H. destruct H as [H|[H|H]].
          - left; exact H.
          - cbn [FOin_tm] in H. apply Nat.eqb_eq in H. lia.
          - right; right; exact H. }
        { apply IHb in H. destruct H as [H|[H|H]].
          - left; exact H.
          - cbn [FOin_tm] in H. apply Nat.eqb_eq in H. lia.
          - right; right; exact H. }
Qed.

Ltac arm_betaF :=
  match goal with
  | H : FOfree_in _ (FObetaF _ _ _ _ _) = true |- _ =>
      apply FObetaF_free in H;
      destruct H as [H|[H|[H|[H|H]]]]
  end.

Ltac arm_patf :=
  match goal with
  | H : FOfree_in _ (FOPATF _ _ _ _) = true |- _ =>
      apply FOPATF_free in H; destruct H as [H|[H|H]]
  end.

Lemma FOlookup_free : forall w B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    tg a1 a2 a3 r,
  FOfree_in w
    (FOlookup B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r)
  = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true \/ FOin_tm w tg = true
  \/ FOin_tm w a1 = true \/ FOin_tm w a2 = true \/ FOin_tm w a3 = true
  \/ FOin_tm w r = true \/ w < 2.
Proof.
  intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r H.
  unfold FOlookup in H.
  repeat first [arm_betaF | ffree_leaf]; ffin.
Qed.

Ltac arm_lookup :=
  match goal with
  | H : FOfree_in _
          (FOlookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = true |- _ =>
      apply FOlookup_free in H;
      destruct H as
        [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]
  end.

Ltac ffree_walk :=
  repeat first [arm_lookup | arm_betaF | arm_patf | ffree_leaf].

Lemma FOPROVAT_free : forall w B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    c z p,
  FOfree_in w
    (FOPROVAT B ct dt c1 d1 c2 d2 c3 d3 cr dr len c z p) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true
  \/ FOin_tm w z = true \/ FOin_tm w p = true \/ w < 2.
Proof.
  intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len c z p H.
  unfold FOPROVAT in H.
  ffree_walk; ffin.
Qed.

Ltac arm_provat :=
  match goal with
  | H : FOfree_in _
          (FOPROVAT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = true |- _ =>
      apply FOPROVAT_free in H;
      destruct H as
        [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]
  end.

Lemma FOGENF_free : forall w B ct dt c1 d1 c2 d2 c3 d3 cr dr len z,
  FOfree_in w
    (FOGENF B ct dt c1 d1 c2 d2 c3 d3 cr dr len z) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true
  \/ FOin_tm w z = true \/ w < 2.
Proof.
  intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len z H.
  unfold FOGENF in H.
  repeat first [arm_lookup | ffree_leaf]; ffin.
Qed.

Ltac arm_genf :=
  match goal with
  | H : FOfree_in _
          (FOGENF _ _ _ _ _ _ _ _ _ _ _ _ _) = true |- _ =>
      apply FOGENF_free in H;
      destruct H as
        [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]
  end.

Lemma FOD2c_free : forall w B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d,
  FOfree_in w (FOD2c B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true
  \/ FOin_tm w d = true \/ w < 2.
Proof.
  intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d H.
  unfold FOD2c in H.
  repeat first [arm_genf | arm_provat | arm_patf | ffree_leaf]; ffin.
Qed.

Lemma FOD3c_free : forall w B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d,
  FOfree_in w (FOD3c B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true
  \/ FOin_tm w d = true \/ w < 2.
Proof.
  intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d H.
  unfold FOD3c in H.
  repeat first [arm_genf | arm_provat | arm_patf | ffree_leaf]; ffin.
Qed.

Lemma FODMONc_free : forall w B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    c c' d,
  FOfree_in w
    (FODMONc B ct dt c1 d1 c2 d2 c3 d3 cr dr len c c' d) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true
  \/ FOin_tm w d = true \/ w < 2.
Proof.
  intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len c c' d H.
  unfold FODMONc in H.
  repeat first [arm_genf | arm_provat | arm_patf | ffree_leaf]; ffin.
Qed.

Lemma FOD2Sc_free : forall cores w B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len d,
  FOfree_in w
    (FOD2Sc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true
  \/ FOin_tm w d = true \/ w < 2.
Proof.
  induction cores as [|c rest IH];
    intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len d H;
    cbn [FOD2Sc] in H.
  - discriminate H.
  - rewrite FOfree_in_FOOr in H.
    apply Bool.orb_true_iff in H. destruct H as [H|H].
    + exact (FOD2c_free _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
    + exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

Lemma FOD3Sc_free : forall cores w B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len d,
  FOfree_in w
    (FOD3Sc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true
  \/ FOin_tm w d = true \/ w < 2.
Proof.
  induction cores as [|c rest IH];
    intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len d H;
    cbn [FOD3Sc] in H.
  - discriminate H.
  - rewrite FOfree_in_FOOr in H.
    apply Bool.orb_true_iff in H. destruct H as [H|H].
    + exact (FOD3c_free _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
    + exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

Lemma FODMONS1_free : forall cs w B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len c d,
  FOfree_in w
    (FODMONS1 B ct dt c1 d1 c2 d2 c3 d3 cr dr len c cs d) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true
  \/ FOin_tm w d = true \/ w < 2.
Proof.
  induction cs as [|c' rest IH];
    intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d H;
    cbn [FODMONS1] in H.
  - discriminate H.
  - rewrite FOfree_in_FOOr in H.
    apply Bool.orb_true_iff in H. destruct H as [H|H].
    + exact (FODMONc_free _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
    + exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

Lemma FODMONSc_free : forall cores w B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len d,
  FOfree_in w
    (FODMONSc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true
  \/ FOin_tm w d = true \/ w < 2.
Proof.
  induction cores as [|c rest IH];
    intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len d H;
    cbn [FODMONSc] in H.
  - discriminate H.
  - rewrite FOfree_in_FOOr in H.
    apply Bool.orb_true_iff in H. destruct H as [H|H].
    + exact (FODMONS1_free _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
    + exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

Ltac arm_dsc :=
  match goal with
  | H : FOfree_in _
          (FOD2Sc _ _ _ _ _ _ _ _ _ _ _ _ _ _) = true |- _ =>
      apply FOD2Sc_free in H;
      destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]
  | H : FOfree_in _
          (FOD3Sc _ _ _ _ _ _ _ _ _ _ _ _ _ _) = true |- _ =>
      apply FOD3Sc_free in H;
      destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]
  | H : FOfree_in _
          (FODMONSc _ _ _ _ _ _ _ _ _ _ _ _ _ _) = true |- _ =>
      apply FODMONSc_free in H;
      destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]
  end.

Lemma FOAXQc_free : forall w B d,
  FOfree_in w (FOAXQc B d) = true ->
  FOin_tm w d = true \/ w < 2.
Proof.
  intros w B d H.
  unfold FOAXQc, FOAXQ1c, FOAXQ2c, FOAXQ3c, FOAXQ4c, FOAXQ5c,
    FOAXQ6c, FOAXQ7c in H.
  ffree_walk; ffin.
Qed.

Lemma FOLOGc_free : forall w B ct dt c1 d1 c2 d2 c3 d3 cr dr len d,
  FOfree_in w (FOLOGc B ct dt c1 d1 c2 d2 c3 d3 cr dr len d) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true
  \/ FOin_tm w d = true \/ w < 2.
Proof.
  intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len d H.
  unfold FOLOGc, FOLOG1c, FOLOG2c, FOLOG3c, FOLOG4c, FOLOG5c,
    FOLOG6c, FOLOG7c, FOLOG8c, FOLOG9c, FOLOG10c, FOLOG11c,
    FOLOG12c in H.
  ffree_walk; ffin.
Qed.

Lemma FOAXREFLc_free : forall w B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    c d,
  FOfree_in w
    (FOAXREFLc B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true
  \/ FOin_tm w d = true \/ w < 2.
Proof.
  intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d H.
  unfold FOAXREFLc in H.
  ffree_walk; ffin.
Qed.

Lemma FOREFLSc_free : forall cores w B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len d,
  FOfree_in w
    (FOREFLSc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true
  \/ FOin_tm w d = true \/ w < 2.
Proof.
  induction cores as [|c rest IH];
    intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len d H;
    cbn [FOREFLSc] in H.
  - discriminate H.
  - rewrite FOfree_in_FOOr in H.
    apply Bool.orb_true_iff in H. destruct H as [H|H].
    + exact (FOAXREFLc_free _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
    + exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

Lemma FOTHAXc_free : forall cores w B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len d,
  FOfree_in w
    (FOTHAXc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true
  \/ FOin_tm w d = true \/ w < 2.
Proof.
  intros cores w B ct dt c1 d1 c2 d2 c3 d3 cr dr len d H.
  unfold FOTHAXc in H.
  rewrite FOfree_in_FOOr in H.
  apply Bool.orb_true_iff in H. destruct H as [H|H].
  - destruct (FOAXQc_free _ _ _ H) as [H'|H'].
    + do 11 right; left; exact H'.
    + do 12 right; exact H'.
  - exact (FOREFLSc_free _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

Lemma FOJSUBST_free : forall w B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    pat vd pl,
  FOfree_in w
    (FOJSUBST B ct dt c1 d1 c2 d2 c3 d3 cr dr len pat vd pl) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true
  \/ FOin_tm w vd = true \/ FOin_tm w pl = true \/ w < 2.
Proof.
  intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len pat vd pl H.
  unfold FOJSUBST in H.
  ffree_walk; ffin.
Qed.

Lemma FOJIND_free : forall w B ct dt c1 d1 c2 d2 c3 d3 cr dr len vd pl,
  FOfree_in w
    (FOJIND B ct dt c1 d1 c2 d2 c3 d3 cr dr len vd pl) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true
  \/ FOin_tm w vd = true \/ FOin_tm w pl = true \/ w < 2.
Proof.
  intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len vd pl H.
  unfold FOJIND in H.
  ffree_walk; ffin.
Qed.

Lemma FOJMP_free : forall w B cs ds vd pl ipos,
  FOfree_in w (FOJMP B cs ds vd pl ipos) = true ->
  FOin_tm w cs = true \/ FOin_tm w ds = true \/ FOin_tm w vd = true
  \/ FOin_tm w pl = true \/ FOin_tm w ipos = true \/ w < 2.
Proof.
  intros w B cs ds vd pl ipos H.
  unfold FOJMP in H.
  ffree_walk; ffin.
Qed.

Lemma FOJGEN_free : forall w B cs ds vd pl ipos,
  FOfree_in w (FOJGEN B cs ds vd pl ipos) = true ->
  FOin_tm w cs = true \/ FOin_tm w ds = true \/ FOin_tm w vd = true
  \/ FOin_tm w pl = true \/ FOin_tm w ipos = true \/ w < 2.
Proof.
  intros w B cs ds vd pl ipos H.
  unfold FOJGEN in H.
  ffree_walk; ffin.
Qed.

Lemma FOJLOEB_free : forall w B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds vd pl ipos,
  FOfree_in w
    (FOJLOEB B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd pl ipos)
  = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true \/ FOin_tm w cs = true
  \/ FOin_tm w ds = true \/ FOin_tm w vd = true \/ FOin_tm w pl = true
  \/ FOin_tm w ipos = true \/ w < 2.
Proof.
  intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd pl ipos H.
  unfold FOJLOEB in H.
  ffree_walk; ffin.
Qed.

Ltac arm_recog :=
  match goal with
  | H : FOfree_in _
          (FOTHAXc _ _ _ _ _ _ _ _ _ _ _ _ _ _) = true |- _ =>
      apply FOTHAXc_free in H;
      destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]
  | H : FOfree_in _
          (FOLOGc _ _ _ _ _ _ _ _ _ _ _ _ _) = true |- _ =>
      apply FOLOGc_free in H;
      destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]
  | H : FOfree_in _
          (FOJSUBST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = true |- _ =>
      apply FOJSUBST_free in H;
      destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]
  | H : FOfree_in _
          (FOJIND _ _ _ _ _ _ _ _ _ _ _ _ _ _) = true |- _ =>
      apply FOJIND_free in H;
      destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]
  | H : FOfree_in _ (FOJMP _ _ _ _ _ _) = true |- _ =>
      apply FOJMP_free in H;
      destruct H as [H|[H|[H|[H|[H|H]]]]]
  | H : FOfree_in _ (FOJGEN _ _ _ _ _ _) = true |- _ =>
      apply FOJGEN_free in H;
      destruct H as [H|[H|[H|[H|[H|H]]]]]
  | H : FOfree_in _
          (FOJLOEB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = true |- _ =>
      apply FOJLOEB_free in H;
      destruct H as
        [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]
  end.

Lemma FOJUSTCK_free : forall cores w B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len cs ds cj dj i,
  FOfree_in w
    (FOJUSTCK B cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds cj dj i)
  = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true \/ FOin_tm w cs = true
  \/ FOin_tm w ds = true \/ FOin_tm w cj = true \/ FOin_tm w dj = true
  \/ FOin_tm w i = true \/ w < 2.
Proof.
  intros cores w B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds cj dj i H.
  unfold FOJUSTCK in H.
  repeat first [arm_recog | arm_dsc | arm_lookup | arm_betaF
               | arm_patf | ffree_leaf]; ffin.
Qed.

Lemma FOGUARDC_free : forall w B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds i,
  FOfree_in w
    (FOGUARDC B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true \/ FOin_tm w cs = true
  \/ FOin_tm w ds = true \/ FOin_tm w i = true \/ w < 2.
Proof.
  intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i H.
  unfold FOGUARDC in H.
  ffree_walk; ffin.
Qed.

Lemma FOTBLVALID_free : forall w B ct dt c1 d1 c2 d2 c3 d3 cr dr len,
  FOfree_in w
    (FOTBLVALID B ct dt c1 d1 c2 d2 c3 d3 cr dr len) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true \/ w < 2.
Proof.
  intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len H.
  unfold FOTBLVALID, FOSTEPDISPATCH, FOSTEP0, FOSTEP1, FOSTEP2,
    FOSTEP3, FOSTEP4, FOSTEP5, FOSTEP_bin, FOSTEP_quant0,
    FOSTEP_substbin, FOSTEP_substquant, FOSTEP_subokbin,
    FOSTEP_subokquant in H.
  ffree_walk; ffin.
Qed.

Ltac arm_prder :=
  match goal with
  | H : FOfree_in _
          (FOTBLVALID _ _ _ _ _ _ _ _ _ _ _ _) = true |- _ =>
      apply FOTBLVALID_free in H;
      destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]
  | H : FOfree_in _
          (FOJUSTCK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = true |- _ =>
      apply FOJUSTCK_free in H;
      destruct H as
        [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]
  | H : FOfree_in _
          (FOGUARDC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = true |- _ =>
      apply FOGUARDC_free in H;
      destruct H as
        [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]
  end.

Lemma FOPRDER_free : forall cores w,
  FOfree_in w (FOPRDER cores) = true -> w < 18.
Proof.
  intros cores w H. unfold FOPRDER in H.
  repeat first [arm_prder | arm_betaF | ffree_leaf]; ffin.
Qed.

Lemma FOPRMAT_free : forall cores w,
  2 <= w -> FOfree_in w (FOPRMAT cores) = false.
Proof.
  intros cores w Hw.
  destruct (FOfree_in w (FOPRMAT cores)) eqn:E; [exfalso|reflexivity].
  unfold FOPRMAT in E.
  repeat match goal with
  | Hx : FOfree_in ?w0 (FOExists ?y _) = true |- _ =>
      let E2 := fresh "E2" in
      destruct (Nat.eqb y w0) eqn:E2;
        [cbn -[Nat.eqb] in Hx; rewrite E2 in Hx; discriminate Hx
        |apply Nat.eqb_neq in E2;
         rewrite (FOfree_in_FOExists_neq _ _ _ E2) in Hx]
  end.
  apply FOPRDER_free in E. lia.
Qed.

Lemma FOProvSentence_closed : forall n A v,
  FOfree_in v (FOProvSentence n A) = false.
Proof.
  intros n A v. unfold FOProvSentence.
  rewrite FOfree_in_subst_num.
  destruct (Nat.eqb_spec v 1) as [->|Hv1]; [reflexivity|].
  rewrite FOfree_in_subst_num.
  destruct (Nat.eqb_spec v 0) as [->|Hv0]; [reflexivity|].
  apply FOPRMAT_free. lia.
Qed.

(** ** The master computation table.

    The recursive code-level functions behind the derivation checker
    (occurrence, free-occurrence, term and formula substitution, the
    capture test, and numeral coding) are represented by one
    course-of-values table.  A table is five beta-coded tracks
    (tag, arg1, arg2, arg3, result) of a common length; an entry is
    justified when its result relates to lookups of its structurally
    smaller sub-calls by the defining case of its tag.  Soundness of a
    valid table is by strong induction on the code argument;
    completeness builds the trace of the actual recursion and codes it
    with [beta_complete].

    [FOlookup B ... tg a1 a2 a3 r] says some position of the table
    carries the given five fields.  The block of variables
    [B, ..., B+21] is bound here; every argument term must keep its
    variables below [B]. *)

Lemma FOdelta0_FOlookup : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    tg a1 a2 a3 r,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm tg < B -> FOmax_var_tm a1 < B ->
  FOmax_var_tm a2 < B -> FOmax_var_tm a3 < B ->
  FOmax_var_tm r < B ->
  FOdelta0 (FOlookup B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r Htb H1 H2 H3
    H4 H5.
  destruct Htb as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  apply FOdelta0_FOBexC.
  - apply FOin_tm_above. lia.
  - apply FOin_tm_above. lia.
  - apply FOdelta0_and;
      [|apply FOdelta0_and;
        [|apply FOdelta0_and;
          [|apply FOdelta0_and]]];
      apply FOdelta0_FObetaF; cbn; lia.
Qed.

Lemma FOsat_FOlookup : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    tg a1 a2 a3 r,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm tg < B -> FOmax_var_tm a1 < B ->
  FOmax_var_tm a2 < B -> FOmax_var_tm a3 < B ->
  FOmax_var_tm r < B ->
  (FOsat e (FOlookup B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r)
   <-> exists j, j < FOeval e len /\
       beta (FOeval e ct) (FOeval e dt) j = FOeval e tg /\
       beta (FOeval e c1) (FOeval e d1) j = FOeval e a1 /\
       beta (FOeval e c2) (FOeval e d2) j = FOeval e a2 /\
       beta (FOeval e c3) (FOeval e d3) j = FOeval e a3 /\
       beta (FOeval e cr) (FOeval e dr) j = FOeval e r).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r Htb H1 H2
    H3 H4 H5.
  destruct Htb as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  unfold FOlookup.
  rewrite (FOsat_FOBexC e B len _
             (FOin_tm_above len B Hlen)
             (FOin_tm_above len (S B) ltac:(lia))).
  split.
  - intros [j [Hj Hbody]].
    set (e' := FOupdate e B j) in *.
    exists j. split; [exact Hj|].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hbody.
    destruct Hbody as [Hb1 Hbody].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hbody.
    destruct Hbody as [Hb2 Hbody].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hbody.
    destruct Hbody as [Hb3 Hbody].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hbody.
    destruct Hbody as [Hb4 Hb5].
    apply (proj1 (FOsat_FObetaF e' (B+2) ct dt (FOVar B) tg
                    ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia)))
      in Hb1.
    apply (proj1 (FOsat_FObetaF e' (B+6) c1 d1 (FOVar B) a1
                    ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia)))
      in Hb2.
    apply (proj1 (FOsat_FObetaF e' (B+10) c2 d2 (FOVar B) a2
                    ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia)))
      in Hb3.
    apply (proj1 (FOsat_FObetaF e' (B+14) c3 d3 (FOVar B) a3
                    ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia)))
      in Hb4.
    apply (proj1 (FOsat_FObetaF e' (B+18) cr dr (FOVar B) r
                    ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia)))
      in Hb5.
    unfold e' in Hb1, Hb2, Hb3, Hb4, Hb5.
    rewrite (FOeval_update_not_in ct _ B j
               (FOin_tm_above ct B Hct)) in Hb1.
    rewrite (FOeval_update_not_in dt _ B j
               (FOin_tm_above dt B Hdt)) in Hb1.
    rewrite (FOeval_update_not_in tg _ B j
               (FOin_tm_above tg B H1)) in Hb1.
    rewrite (FOeval_update_not_in c1 _ B j
               (FOin_tm_above c1 B Hc1)) in Hb2.
    rewrite (FOeval_update_not_in d1 _ B j
               (FOin_tm_above d1 B Hd1)) in Hb2.
    rewrite (FOeval_update_not_in a1 _ B j
               (FOin_tm_above a1 B H2)) in Hb2.
    rewrite (FOeval_update_not_in c2 _ B j
               (FOin_tm_above c2 B Hc2)) in Hb3.
    rewrite (FOeval_update_not_in d2 _ B j
               (FOin_tm_above d2 B Hd2)) in Hb3.
    rewrite (FOeval_update_not_in a2 _ B j
               (FOin_tm_above a2 B H3)) in Hb3.
    rewrite (FOeval_update_not_in c3 _ B j
               (FOin_tm_above c3 B Hc3)) in Hb4.
    rewrite (FOeval_update_not_in d3 _ B j
               (FOin_tm_above d3 B Hd3)) in Hb4.
    rewrite (FOeval_update_not_in a3 _ B j
               (FOin_tm_above a3 B H4)) in Hb4.
    rewrite (FOeval_update_not_in cr _ B j
               (FOin_tm_above cr B Hcr)) in Hb5.
    rewrite (FOeval_update_not_in dr _ B j
               (FOin_tm_above dr B Hdr)) in Hb5.
    rewrite (FOeval_update_not_in r _ B j
               (FOin_tm_above r B H5)) in Hb5.
    assert (EvB : FOeval (FOupdate e B j) (FOVar B) = j).
    { cbn. unfold FOupdate. rewrite Nat.eqb_refl. reflexivity. }
    rewrite EvB in Hb1, Hb2, Hb3, Hb4, Hb5.
    repeat split; assumption.
  - intros [j [Hj [Hb1 [Hb2 [Hb3 [Hb4 Hb5]]]]]].
    exists j. split; [exact Hj|].
    assert (EvB : FOeval (FOupdate e B j) (FOVar B) = j).
    { cbn. unfold FOupdate. rewrite Nat.eqb_refl. reflexivity. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FObetaF (FOupdate e B j) (B+2) ct dt
                      (FOVar B) tg
                      ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia))).
      rewrite EvB.
      rewrite (FOeval_update_not_in ct _ B j
                 (FOin_tm_above ct B Hct)).
      rewrite (FOeval_update_not_in dt _ B j
                 (FOin_tm_above dt B Hdt)).
      rewrite (FOeval_update_not_in tg _ B j
                 (FOin_tm_above tg B H1)).
      exact Hb1. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FObetaF (FOupdate e B j) (B+6) c1 d1
                      (FOVar B) a1
                      ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia))).
      rewrite EvB.
      rewrite (FOeval_update_not_in c1 _ B j
                 (FOin_tm_above c1 B Hc1)).
      rewrite (FOeval_update_not_in d1 _ B j
                 (FOin_tm_above d1 B Hd1)).
      rewrite (FOeval_update_not_in a1 _ B j
                 (FOin_tm_above a1 B H2)).
      exact Hb2. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FObetaF (FOupdate e B j) (B+10) c2 d2
                      (FOVar B) a2
                      ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia))).
      rewrite EvB.
      rewrite (FOeval_update_not_in c2 _ B j
                 (FOin_tm_above c2 B Hc2)).
      rewrite (FOeval_update_not_in d2 _ B j
                 (FOin_tm_above d2 B Hd2)).
      rewrite (FOeval_update_not_in a2 _ B j
                 (FOin_tm_above a2 B H3)).
      exact Hb3. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FObetaF (FOupdate e B j) (B+14) c3 d3
                      (FOVar B) a3
                      ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia))).
      rewrite EvB.
      rewrite (FOeval_update_not_in c3 _ B j
                 (FOin_tm_above c3 B Hc3)).
      rewrite (FOeval_update_not_in d3 _ B j
                 (FOin_tm_above d3 B Hd3)).
      rewrite (FOeval_update_not_in a3 _ B j
                 (FOin_tm_above a3 B H4)).
      exact Hb4. }
    apply (proj2 (FOsat_FObetaF (FOupdate e B j) (B+18) cr dr
                    (FOVar B) r
                    ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia))).
    rewrite EvB.
    rewrite (FOeval_update_not_in cr _ B j
               (FOin_tm_above cr B Hcr)).
    rewrite (FOeval_update_not_in dr _ B j
               (FOin_tm_above dr B Hdr)).
    rewrite (FOeval_update_not_in r _ B j
               (FOin_tm_above r B H5)).
    exact Hb5.
Qed.

Lemma FOeval_upd_above : forall t e x u,
  FOmax_var_tm t < x -> FOeval (FOupdate e x u) t = FOeval e t.
Proof.
  intros t e x u H.
  apply FOeval_update_not_in. apply FOin_tm_above. exact H.
Qed.

(** The master function the table represents, total on codes through
    the decoders, and the per-tag step semantics over an abstract
    lookup relation. *)

Lemma FOsat_FOLOG10c : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  (FOsat e (FOLOG10c B ct dt c1 d1 c2 d2 c3 d3 cr dr len d) <->
   exists x P Q,
     FOeval e d = cpair 2 (cpair
       (cpair 3 (cpair x (cpair 2 (cpair P Q))))
       (cpair 2 (cpair (cpair 4 (cpair x P)) Q))) /\
     (exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = 1 /\
        beta (FOeval e c1) (FOeval e d1) j = x /\
        beta (FOeval e c2) (FOeval e d2) j = Q /\
        beta (FOeval e c3) (FOeval e d3) j = 0 /\
        beta (FOeval e cr) (FOeval e dr) j = 0)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len d Htb Hd.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb60 : tbl_below (B+60) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (HinB : FOin_tm B (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; exact Hd).
  assert (HinSB : FOin_tm (S B) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB2 : FOin_tm (B+2) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB2 : FOin_tm (S (B+2)) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB4 : FOin_tm (B+4) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB4 : FOin_tm (S (B+4)) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (EB2 : Nat.eqb B (B+2) = false) by (apply Nat.eqb_neq; lia).
  assert (EB4 : Nat.eqb B (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (E24 : Nat.eqb (B+2) (B+4) = false)
    by (apply Nat.eqb_neq; lia).
  assert (Henv : Forall (fun t => FOmax_var_tm t < B+6)
                   [FOVar B; FOVar (B+2); FOVar (B+4)])
    by (constructor; [cbn; lia |
        constructor; [cbn; lia |
        constructor; [cbn; lia | constructor]]]).
  assert (Hd6 : FOmax_var_tm d < B+6) by lia.
  assert (H1m : FOmax_var_tm (FOnumeral 1) < B+60)
    by (rewrite FOmax_var_numeral; lia).
  assert (H2m : FOmax_var_tm (FOVar B) < B+60) by (cbn; lia).
  assert (H3m : FOmax_var_tm (FOVar (B+4)) < B+60) by (cbn; lia).
  assert (H4m : FOmax_var_tm FOZero < B+60) by (cbn; lia).
  unfold FOLOG10c.
  rewrite (FOsat_FOBexC e B (FOSucc d) _ HinB HinSB).
  split.
  - intros [v0 [Hv0 Hb1]].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc d) _ HinB2 HinSB2) in Hb1.
    destruct Hb1 as [v1 [Hv1 Hb2]].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc d) _ HinB4 HinSB4) in Hb2.
    destruct Hb2 as [v2 [Hv2 Hb3]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb3.
    destruct Hb3 as [Hpat Hlk].
    set (e3 := FOupdate (FOupdate (FOupdate e B v0) (B+2) v1)
                 (B+4) v2) in *.
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e3 t = FOeval e t).
    { intros t Ht. unfold e3.
      rewrite (FOeval_update_above t _ (B+4) v2 ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) v1 ltac:(lia)).
      exact (FOeval_update_above t e B v0 Ht). }
    assert (Hsg : forall s,
        FOeval e3 (nth s [FOVar B; FOVar (B+2); FOVar (B+4)] FOZero)
        = (fun s => match s with
                    | 0 => v0 | 1 => v1 | 2 => v2 | _ => 0 end) s).
    { intro s. destruct s as [|[|[|s]]]; cbn.
      - unfold e3, FOupdate. rewrite EB4, EB2, Nat.eqb_refl.
        reflexivity.
      - unfold e3, FOupdate. rewrite E24, Nat.eqb_refl. reflexivity.
      - unfold e3, FOupdate. rewrite Nat.eqb_refl. reflexivity.
      - destruct s; reflexivity. }
    apply (proj1 (FOsat_FOPATF cpatLExElim _ (B+6) _ d Henv Hd6))
      in Hpat.
    rewrite (cpat_sem_ext _ _ _ Hsg) in Hpat.
    rewrite (Hstab d Hd) in Hpat.
    cbn [cpat_sem cpatLExElim pImpP pAllP pExP] in Hpat.
    apply (proj1 (FOsat_FOlookup e3 (B+60) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 1) (FOVar B) (FOVar (B+4))
                    FOZero FOZero Htb60 H1m H2m H3m H4m H4m)) in Hlk.
    destruct Hlk as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
    rewrite (Hstab len Hlen) in Hj.
    rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral in Hf1.
    cbn [FOeval] in Hf2, Hf3, Hf4, Hf5.
    rewrite (Hstab c1 Hc1), (Hstab d1 Hd1') in Hf2.
    rewrite (Hstab c2 Hc2), (Hstab d2 Hd2') in Hf3.
    rewrite (Hstab c3 Hc3), (Hstab d3 Hd3') in Hf4.
    rewrite (Hstab cr Hcr), (Hstab dr Hdr) in Hf5.
    assert (Ee3B : e3 B = v0).
    { unfold e3, FOupdate. rewrite EB4, EB2, Nat.eqb_refl.
      reflexivity. }
    assert (Ee3B4 : e3 (B+4) = v2).
    { unfold e3, FOupdate. rewrite Nat.eqb_refl. reflexivity. }
    rewrite Ee3B in Hf2. rewrite Ee3B4 in Hf3.
    exists v0, v1, v2.
    split; [symmetry; exact Hpat|].
    exists j.
    split; [exact Hj|].
    split; [exact Hf1|].
    split; [exact Hf2|].
    split; [exact Hf3|].
    split; [exact Hf4|].
    exact Hf5.
  - intros [x [P [Q [Heq Hlk]]]].
    pose proof (cpat_occurs_le cpatLExElim
      (fun s => match s with 0 => x | 1 => P | 2 => Q | _ => 0 end) 0
      eq_refl) as Hx.
    pose proof (cpat_occurs_le cpatLExElim
      (fun s => match s with 0 => x | 1 => P | 2 => Q | _ => 0 end) 1
      eq_refl) as HP.
    pose proof (cpat_occurs_le cpatLExElim
      (fun s => match s with 0 => x | 1 => P | 2 => Q | _ => 0 end) 2
      eq_refl) as HQ.
    cbn [cpat_sem cpatLExElim pImpP pAllP pExP] in Hx, HP, HQ.
    cbn [FOeval].
    exists x. split; [lia|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc d) _ HinB2 HinSB2).
    exists P. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above d e B x Hd). lia. }
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc d) _ HinB4 HinSB4).
    exists Q. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above d _ (B+2) P ltac:(lia)).
      rewrite (FOeval_update_above d e B x Hd). lia. }
    apply (proj2 (FOsat_FOAnd _ _ _)).
    set (e3 := FOupdate (FOupdate (FOupdate e B x) (B+2) P)
                 (B+4) Q).
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e3 t = FOeval e t).
    { intros t Ht. unfold e3.
      rewrite (FOeval_update_above t _ (B+4) Q ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) P ltac:(lia)).
      exact (FOeval_update_above t e B x Ht). }
    assert (Hsg : forall s,
        FOeval e3 (nth s [FOVar B; FOVar (B+2); FOVar (B+4)] FOZero)
        = (fun s => match s with
                    | 0 => x | 1 => P | 2 => Q | _ => 0 end) s).
    { intro s. destruct s as [|[|[|s]]]; cbn.
      - unfold e3, FOupdate. rewrite EB4, EB2, Nat.eqb_refl.
        reflexivity.
      - unfold e3, FOupdate. rewrite E24, Nat.eqb_refl. reflexivity.
      - unfold e3, FOupdate. rewrite Nat.eqb_refl. reflexivity.
      - destruct s; reflexivity. }
    split.
    + apply (proj2 (FOsat_FOPATF cpatLExElim e3 (B+6) _ d Henv Hd6)).
      rewrite (cpat_sem_ext _ _ _ Hsg).
      rewrite (Hstab d Hd).
      cbn [cpat_sem cpatLExElim pImpP pAllP pExP].
      symmetry. exact Heq.
    + apply (proj2 (FOsat_FOlookup e3 (B+60) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOnumeral 1) (FOVar B) (FOVar (B+4))
                      FOZero FOZero Htb60 H1m H2m H3m H4m H4m)).
      destruct Hlk as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
      assert (Ee3B : e3 B = x).
      { unfold e3, FOupdate. rewrite EB4, EB2, Nat.eqb_refl.
        reflexivity. }
      assert (Ee3B4 : e3 (B+4) = Q).
      { unfold e3, FOupdate. rewrite Nat.eqb_refl. reflexivity. }
      exists j.
      split; [rewrite (Hstab len Hlen); exact Hj|].
      split.
      { rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral.
        exact Hf1. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), Ee3B. exact Hf2. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), Ee3B4. exact Hf3. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'). exact Hf4. }
      cbn [FOeval].
      rewrite (Hstab cr Hcr), (Hstab dr Hdr). exact Hf5.
Qed.

Lemma FOsat_FOLOG12c : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  (FOsat e (FOLOG12c B ct dt c1 d1 c2 d2 c3 d3 cr dr len d) <->
   exists x P Q,
     FOeval e d = cpair 2 (cpair
       (cpair 3 (cpair x (cpair 2 (cpair P Q))))
       (cpair 2 (cpair P (cpair 3 (cpair x Q))))) /\
     (exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = 1 /\
        beta (FOeval e c1) (FOeval e d1) j = x /\
        beta (FOeval e c2) (FOeval e d2) j = P /\
        beta (FOeval e c3) (FOeval e d3) j = 0 /\
        beta (FOeval e cr) (FOeval e dr) j = 0)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len d Htb Hd.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb60 : tbl_below (B+60) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (HinB : FOin_tm B (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; exact Hd).
  assert (HinSB : FOin_tm (S B) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB2 : FOin_tm (B+2) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB2 : FOin_tm (S (B+2)) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB4 : FOin_tm (B+4) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB4 : FOin_tm (S (B+4)) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (EB2 : Nat.eqb B (B+2) = false) by (apply Nat.eqb_neq; lia).
  assert (EB4 : Nat.eqb B (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (E24 : Nat.eqb (B+2) (B+4) = false)
    by (apply Nat.eqb_neq; lia).
  assert (Henv : Forall (fun t => FOmax_var_tm t < B+6)
                   [FOVar B; FOVar (B+2); FOVar (B+4)])
    by (constructor; [cbn; lia |
        constructor; [cbn; lia |
        constructor; [cbn; lia | constructor]]]).
  assert (Hd6 : FOmax_var_tm d < B+6) by lia.
  assert (H1m : FOmax_var_tm (FOnumeral 1) < B+60)
    by (rewrite FOmax_var_numeral; lia).
  assert (H2m : FOmax_var_tm (FOVar B) < B+60) by (cbn; lia).
  assert (H3m : FOmax_var_tm (FOVar (B+2)) < B+60) by (cbn; lia).
  assert (H4m : FOmax_var_tm FOZero < B+60) by (cbn; lia).
  unfold FOLOG12c.
  rewrite (FOsat_FOBexC e B (FOSucc d) _ HinB HinSB).
  split.
  - intros [v0 [Hv0 Hb1]].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc d) _ HinB2 HinSB2) in Hb1.
    destruct Hb1 as [v1 [Hv1 Hb2]].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc d) _ HinB4 HinSB4) in Hb2.
    destruct Hb2 as [v2 [Hv2 Hb3]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb3.
    destruct Hb3 as [Hpat Hlk].
    set (e3 := FOupdate (FOupdate (FOupdate e B v0) (B+2) v1)
                 (B+4) v2) in *.
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e3 t = FOeval e t).
    { intros t Ht. unfold e3.
      rewrite (FOeval_update_above t _ (B+4) v2 ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) v1 ltac:(lia)).
      exact (FOeval_update_above t e B v0 Ht). }
    assert (Hsg : forall s,
        FOeval e3 (nth s [FOVar B; FOVar (B+2); FOVar (B+4)] FOZero)
        = (fun s => match s with
                    | 0 => v0 | 1 => v1 | 2 => v2 | _ => 0 end) s).
    { intro s. destruct s as [|[|[|s]]]; cbn.
      - unfold e3, FOupdate. rewrite EB4, EB2, Nat.eqb_refl.
        reflexivity.
      - unfold e3, FOupdate. rewrite E24, Nat.eqb_refl. reflexivity.
      - unfold e3, FOupdate. rewrite Nat.eqb_refl. reflexivity.
      - destruct s; reflexivity. }
    apply (proj1 (FOsat_FOPATF cpatLAllExport _ (B+6) _ d Henv Hd6))
      in Hpat.
    rewrite (cpat_sem_ext _ _ _ Hsg) in Hpat.
    rewrite (Hstab d Hd) in Hpat.
    cbn [cpat_sem cpatLAllExport pImpP pAllP] in Hpat.
    apply (proj1 (FOsat_FOlookup e3 (B+60) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 1) (FOVar B) (FOVar (B+2))
                    FOZero FOZero Htb60 H1m H2m H3m H4m H4m)) in Hlk.
    destruct Hlk as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
    rewrite (Hstab len Hlen) in Hj.
    rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral in Hf1.
    cbn [FOeval] in Hf2, Hf3, Hf4, Hf5.
    rewrite (Hstab c1 Hc1), (Hstab d1 Hd1') in Hf2.
    rewrite (Hstab c2 Hc2), (Hstab d2 Hd2') in Hf3.
    rewrite (Hstab c3 Hc3), (Hstab d3 Hd3') in Hf4.
    rewrite (Hstab cr Hcr), (Hstab dr Hdr) in Hf5.
    assert (Ee3B : e3 B = v0).
    { unfold e3, FOupdate. rewrite EB4, EB2, Nat.eqb_refl.
      reflexivity. }
    assert (Ee3B2 : e3 (B+2) = v1).
    { unfold e3, FOupdate. rewrite E24, Nat.eqb_refl. reflexivity. }
    rewrite Ee3B in Hf2. rewrite Ee3B2 in Hf3.
    exists v0, v1, v2.
    split; [symmetry; exact Hpat|].
    exists j.
    split; [exact Hj|].
    split; [exact Hf1|].
    split; [exact Hf2|].
    split; [exact Hf3|].
    split; [exact Hf4|].
    exact Hf5.
  - intros [x [P [Q [Heq Hlk]]]].
    pose proof (cpat_occurs_le cpatLAllExport
      (fun s => match s with 0 => x | 1 => P | 2 => Q | _ => 0 end) 0
      eq_refl) as Hx.
    pose proof (cpat_occurs_le cpatLAllExport
      (fun s => match s with 0 => x | 1 => P | 2 => Q | _ => 0 end) 1
      eq_refl) as HP.
    pose proof (cpat_occurs_le cpatLAllExport
      (fun s => match s with 0 => x | 1 => P | 2 => Q | _ => 0 end) 2
      eq_refl) as HQ.
    cbn [cpat_sem cpatLAllExport pImpP pAllP] in Hx, HP, HQ.
    cbn [FOeval].
    exists x. split; [lia|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc d) _ HinB2 HinSB2).
    exists P. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above d e B x Hd). lia. }
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc d) _ HinB4 HinSB4).
    exists Q. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above d _ (B+2) P ltac:(lia)).
      rewrite (FOeval_update_above d e B x Hd). lia. }
    apply (proj2 (FOsat_FOAnd _ _ _)).
    set (e3 := FOupdate (FOupdate (FOupdate e B x) (B+2) P)
                 (B+4) Q).
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e3 t = FOeval e t).
    { intros t Ht. unfold e3.
      rewrite (FOeval_update_above t _ (B+4) Q ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) P ltac:(lia)).
      exact (FOeval_update_above t e B x Ht). }
    assert (Hsg : forall s,
        FOeval e3 (nth s [FOVar B; FOVar (B+2); FOVar (B+4)] FOZero)
        = (fun s => match s with
                    | 0 => x | 1 => P | 2 => Q | _ => 0 end) s).
    { intro s. destruct s as [|[|[|s]]]; cbn.
      - unfold e3, FOupdate. rewrite EB4, EB2, Nat.eqb_refl.
        reflexivity.
      - unfold e3, FOupdate. rewrite E24, Nat.eqb_refl. reflexivity.
      - unfold e3, FOupdate. rewrite Nat.eqb_refl. reflexivity.
      - destruct s; reflexivity. }
    split.
    + apply (proj2 (FOsat_FOPATF cpatLAllExport e3 (B+6) _ d Henv
                      Hd6)).
      rewrite (cpat_sem_ext _ _ _ Hsg).
      rewrite (Hstab d Hd).
      cbn [cpat_sem cpatLAllExport pImpP pAllP].
      symmetry. exact Heq.
    + apply (proj2 (FOsat_FOlookup e3 (B+60) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOnumeral 1) (FOVar B) (FOVar (B+2))
                      FOZero FOZero Htb60 H1m H2m H3m H4m H4m)).
      destruct Hlk as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
      assert (Ee3B : e3 B = x).
      { unfold e3, FOupdate. rewrite EB4, EB2, Nat.eqb_refl.
        reflexivity. }
      assert (Ee3B2 : e3 (B+2) = P).
      { unfold e3, FOupdate. rewrite E24, Nat.eqb_refl. reflexivity. }
      exists j.
      split; [rewrite (Hstab len Hlen); exact Hj|].
      split.
      { rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral.
        exact Hf1. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), Ee3B. exact Hf2. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), Ee3B2. exact Hf3. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'). exact Hf4. }
      cbn [FOeval].
      rewrite (Hstab cr Hcr), (Hstab dr Hdr). exact Hf5.
Qed.

Lemma FOsat_FOLOGc : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  (FOsat e (FOLOGc B ct dt c1 d1 c2 d2 c3 d3 cr dr len d) <->
   logax_sem
     (fun tg a1 a2 a3 r => exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = tg /\
        beta (FOeval e c1) (FOeval e d1) j = a1 /\
        beta (FOeval e c2) (FOeval e d2) j = a2 /\
        beta (FOeval e c3) (FOeval e d3) j = a3 /\
        beta (FOeval e cr) (FOeval e dr) j = r)
     (FOeval e d)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len d Htb Hd.
  unfold FOLOGc, logax_sem.
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOLOG1c e B d Hd).
  rewrite (FOsat_FOLOG2c e B d Hd).
  rewrite (FOsat_FOLOG3c e B d Hd).
  rewrite (FOsat_FOLOG4c e B d Hd).
  rewrite (FOsat_FOLOG5c e B d Hd).
  rewrite (FOsat_FOLOG6c e B d Hd).
  rewrite (FOsat_FOLOG7c e B d Hd).
  rewrite (FOsat_FOLOG8c e B d Hd).
  rewrite (FOsat_FOLOG9c e B d Hd).
  rewrite (FOsat_FOLOG10c e B ct dt c1 d1 c2 d2 c3 d3 cr dr len d
             Htb Hd).
  rewrite (FOsat_FOLOG11c e B d Hd).
  rewrite (FOsat_FOLOG12c e B ct dt c1 d1 c2 d2 c3 d3 cr dr len d
             Htb Hd).
  reflexivity.
Qed.

Lemma FOdelta0_FOLOG10c : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  FOdelta0 (FOLOG10c B ct dt c1 d1 c2 d2 c3 d3 cr dr len d).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len d Htb Hd.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb60 : tbl_below (B+60) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  unfold FOLOG10c.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; exact Hd
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_and.
  - apply FOdelta0_FOPATF.
    + constructor; [cbn; lia |
        constructor; [cbn; lia |
        constructor; [cbn; lia | constructor]]].
    + lia.
  - apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia.
Qed.

Lemma FOdelta0_FOLOG12c : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  FOdelta0 (FOLOG12c B ct dt c1 d1 c2 d2 c3 d3 cr dr len d).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len d Htb Hd.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb60 : tbl_below (B+60) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  unfold FOLOG12c.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; exact Hd
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_and.
  - apply FOdelta0_FOPATF.
    + constructor; [cbn; lia |
        constructor; [cbn; lia |
        constructor; [cbn; lia | constructor]]].
    + lia.
  - apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia.
Qed.

Lemma FOdelta0_FOLOGc : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  FOdelta0 (FOLOGc B ct dt c1 d1 c2 d2 c3 d3 cr dr len d).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len d Htb Hd.
  unfold FOLOGc.
  unfold FOLOG1c, FOLOG2c, FOLOG3c, FOLOG4c, FOLOG5c, FOLOG6c,
    FOLOG7c, FOLOG8c, FOLOG9c, FOLOG11c.
  apply FOdelta0_or; [apply FOdelta0_pat2; exact Hd|].
  apply FOdelta0_or; [apply FOdelta0_pat3; exact Hd|].
  apply FOdelta0_or; [apply FOdelta0_pat1; exact Hd|].
  apply FOdelta0_or; [apply FOdelta0_pat1; exact Hd|].
  apply FOdelta0_or; [apply FOdelta0_pat2; exact Hd|].
  apply FOdelta0_or; [apply FOdelta0_pat3; exact Hd|].
  apply FOdelta0_or; [apply FOdelta0_pat2; exact Hd|].
  apply FOdelta0_or; [apply FOdelta0_pat4; exact Hd|].
  apply FOdelta0_or; [apply FOdelta0_pat4; exact Hd|].
  apply FOdelta0_or;
    [apply FOdelta0_FOLOG10c; assumption|].
  apply FOdelta0_or; [apply FOdelta0_pat3; exact Hd|].
  apply FOdelta0_FOLOG12c; assumption.
Qed.

(** The semantic mirrors of the reflection-instance recognizer and the
    assembled theory-axiom recognizer.  A reflection instance at a
    lower core code [c] is an implication whose antecedent is the core
    applied through the table — tag 5 turns the conclusion code into
    its numeral code, tag 3 substitutes it at variable 1 in [c]. *)

Definition provat_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (c z p : nat) : Prop :=
  exists nz, L 5 z 0 0 nz /\ L 3 1 nz c p.

Definition genuine_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (z : nat) : Prop :=
  exists rg, L 3 (S z) 0 z rg.

Definition d2one_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (c d : nat) : Prop :=
  exists x y pixy px py,
    genuine_sem L x /\ genuine_sem L y /\
    provat_sem L c (cpair 2 (cpair x y)) pixy /\
    provat_sem L c x px /\
    provat_sem L c y py /\
    d = cpair 2 (cpair pixy (cpair 2 (cpair px py))).

Definition d3one_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (c d : nat) : Prop :=
  exists a pa ppa,
    genuine_sem L a /\
    provat_sem L c a pa /\ provat_sem L c pa ppa /\
    d = cpair 2 (cpair pa ppa).

Definition dmonone_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (c c' d : nat) : Prop :=
  exists a p p',
    genuine_sem L a /\
    provat_sem L c a p /\ provat_sem L c' a p' /\
    d = cpair 2 (cpair p p').

Fixpoint d2s_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (cores : list nat) (d : nat) : Prop :=
  match cores with
  | [] => False
  | c :: rest => d2one_sem L c d \/ d2s_sem L rest d
  end.

Fixpoint d3s_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (cores : list nat) (d : nat) : Prop :=
  match cores with
  | [] => False
  | c :: rest => d3one_sem L c d \/ d3s_sem L rest d
  end.

Fixpoint dmons1_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (c : nat) (cs : list nat) (d : nat) : Prop :=
  match cs with
  | [] => False
  | c' :: rest => dmonone_sem L c c' d \/ dmons1_sem L c rest d
  end.

Fixpoint dmons_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (cores : list nat) (d : nat) : Prop :=
  match cores with
  | [] => False
  | c :: rest => dmons1_sem L c (c :: rest) d \/ dmons_sem L rest d
  end.

Definition refl_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (c d : nat) : Prop :=
  exists a na p, L 5 a 0 0 na /\ L 3 1 na c p /\
    d = cpair 2 (cpair p a).

Fixpoint refls_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (cores : list nat) (d : nat) : Prop :=
  match cores with
  | [] => False
  | c :: rest => refl_sem L c d \/ refls_sem L rest d
  end.

Definition thax_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (cores : list nat) (d : nat) : Prop :=
  axq_sem d \/ refls_sem L cores d.

Lemma FOsat_FOAXREFLc : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    c d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  (FOsat e (FOAXREFLc B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d) <->
   refl_sem
     (fun tg a1 a2 a3 r => exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = tg /\
        beta (FOeval e c1) (FOeval e d1) j = a1 /\
        beta (FOeval e c2) (FOeval e d2) j = a2 /\
        beta (FOeval e c3) (FOeval e d3) j = a3 /\
        beta (FOeval e cr) (FOeval e dr) j = r)
     c (FOeval e d)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d Htb Hd.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb6 : tbl_below (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb28 : tbl_below (B+28) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (HinB : FOin_tm B (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; exact Hd).
  assert (HinSB : FOin_tm (S B) (FOSucc d) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB2 : FOin_tm (B+2) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB2 : FOin_tm (S (B+2)) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB4 : FOin_tm (B+4) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB4 : FOin_tm (S (B+4)) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (EB2 : Nat.eqb B (B+2) = false) by (apply Nat.eqb_neq; lia).
  assert (EB4 : Nat.eqb B (B+4) = false) by (apply Nat.eqb_neq; lia).
  assert (E24 : Nat.eqb (B+2) (B+4) = false)
    by (apply Nat.eqb_neq; lia).
  assert (Henv : Forall (fun t => FOmax_var_tm t < B+50)
                   [FOVar (B+4); FOVar B])
    by (constructor; [cbn; lia |
        constructor; [cbn; lia | constructor]]).
  assert (Hd50 : FOmax_var_tm d < B+50) by lia.
  assert (H5m : FOmax_var_tm (FOnumeral 5) < B+6)
    by (rewrite FOmax_var_numeral; lia).
  assert (HvBm : FOmax_var_tm (FOVar B) < B+6) by (cbn; lia).
  assert (HvB2m : FOmax_var_tm (FOVar (B+2)) < B+6) by (cbn; lia).
  assert (H0m : FOmax_var_tm FOZero < B+6) by (cbn; lia).
  assert (H3m : FOmax_var_tm (FOnumeral 3) < B+28)
    by (rewrite FOmax_var_numeral; lia).
  assert (H1m : FOmax_var_tm (FOnumeral 1) < B+28)
    by (rewrite FOmax_var_numeral; lia).
  assert (HvB2m' : FOmax_var_tm (FOVar (B+2)) < B+28) by (cbn; lia).
  assert (Hcm : FOmax_var_tm (FOnumeral c) < B+28)
    by (rewrite FOmax_var_numeral; lia).
  assert (HvB4m : FOmax_var_tm (FOVar (B+4)) < B+28) by (cbn; lia).
  unfold FOAXREFLc, refl_sem.
  rewrite (FOsat_FOBexC e B (FOSucc d) _ HinB HinSB).
  split.
  - intros [v0 [Hv0 Hb1]].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc cr) _ HinB2 HinSB2) in Hb1.
    destruct Hb1 as [v1 [Hv1 Hb2]].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc cr) _ HinB4 HinSB4) in Hb2.
    destruct Hb2 as [v2 [Hv2 Hb3]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb3.
    destruct Hb3 as [Hlk1 Hb4].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb4.
    destruct Hb4 as [Hlk2 Hpat].
    set (e3 := FOupdate (FOupdate (FOupdate e B v0) (B+2) v1)
                 (B+4) v2) in *.
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e3 t = FOeval e t).
    { intros t Ht. unfold e3.
      rewrite (FOeval_update_above t _ (B+4) v2 ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) v1 ltac:(lia)).
      exact (FOeval_update_above t e B v0 Ht). }
    assert (Ee3B : e3 B = v0).
    { unfold e3, FOupdate. rewrite EB4, EB2, Nat.eqb_refl.
      reflexivity. }
    assert (Ee3B2 : e3 (B+2) = v1).
    { unfold e3, FOupdate. rewrite E24, Nat.eqb_refl. reflexivity. }
    assert (Ee3B4 : e3 (B+4) = v2).
    { unfold e3, FOupdate. rewrite Nat.eqb_refl. reflexivity. }
    apply (proj1 (FOsat_FOlookup e3 (B+6) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 5) (FOVar B) FOZero FOZero
                    (FOVar (B+2)) Htb6 H5m HvBm H0m H0m HvB2m))
      in Hlk1.
    apply (proj1 (FOsat_FOlookup e3 (B+28) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 3) (FOnumeral 1)
                    (FOVar (B+2)) (FOnumeral c) (FOVar (B+4))
                    Htb28 H3m H1m HvB2m' Hcm HvB4m)) in Hlk2.
    apply (proj1 (FOsat_FOPATF cpatImpl01 _ (B+50) _ d Henv Hd50))
      in Hpat.
    assert (Hsg : forall s,
        FOeval e3 (nth s [FOVar (B+4); FOVar B] FOZero)
        = (fun s => match s with
                    | 0 => v2 | 1 => v0 | _ => 0 end) s).
    { intro s. destruct s as [|[|s]]; cbn.
      - unfold e3, FOupdate. rewrite Nat.eqb_refl. reflexivity.
      - unfold e3, FOupdate. rewrite EB4, EB2, Nat.eqb_refl.
        reflexivity.
      - destruct s; reflexivity. }
    rewrite (cpat_sem_ext _ _ _ Hsg) in Hpat.
    rewrite (Hstab d Hd) in Hpat.
    cbn [cpat_sem cpatImpl01 pImpP] in Hpat.
    destruct Hlk1 as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
    rewrite (Hstab len Hlen) in Hj.
    rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral in Hf1.
    cbn [FOeval] in Hf2, Hf3, Hf4, Hf5.
    rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), Ee3B in Hf2.
    rewrite (Hstab c2 Hc2), (Hstab d2 Hd2') in Hf3.
    rewrite (Hstab c3 Hc3), (Hstab d3 Hd3') in Hf4.
    rewrite (Hstab cr Hcr), (Hstab dr Hdr), Ee3B2 in Hf5.
    destruct Hlk2 as [j2 [Hj2 [Hg1 [Hg2 [Hg3 [Hg4 Hg5]]]]]].
    rewrite (Hstab len Hlen) in Hj2.
    rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral in Hg1.
    cbn [FOeval] in Hg2, Hg3, Hg4, Hg5.
    rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), FOeval_numeral in Hg2.
    rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), Ee3B2 in Hg3.
    rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), FOeval_numeral in Hg4.
    rewrite (Hstab cr Hcr), (Hstab dr Hdr), Ee3B4 in Hg5.
    exists v0, v1, v2.
    split.
    { exists j. repeat split; assumption. }
    split.
    { exists j2. repeat split; assumption. }
    symmetry. exact Hpat.
  - intros [a [na [p [Hr1 [Hr2 Hshape]]]]].
    pose proof (cpair_bound p a) as Hcb1.
    pose proof (cpair_bound 2 (cpair p a)) as Hcb2.
    assert (Hna : na <= FOeval e cr).
    { destruct Hr1 as [j [_ [_ [_ [_ [_ F5]]]]]].
      unfold beta in F5.
      pose proof (Nat.Div0.mod_le (FOeval e cr)
                    (FOeval e dr * S j + 1)).
      lia. }
    assert (Hp : p <= FOeval e cr).
    { destruct Hr2 as [j [_ [_ [_ [_ [_ F5]]]]]].
      unfold beta in F5.
      pose proof (Nat.Div0.mod_le (FOeval e cr)
                    (FOeval e dr * S j + 1)).
      lia. }
    cbn [FOeval].
    exists a. split; [lia|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc cr) _ HinB2 HinSB2).
    exists na. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above cr e B a Hcr). lia. }
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc cr) _ HinB4 HinSB4).
    exists p. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above cr _ (B+2) na ltac:(lia)).
      rewrite (FOeval_update_above cr e B a Hcr). lia. }
    set (e3 := FOupdate (FOupdate (FOupdate e B a) (B+2) na)
                 (B+4) p).
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e3 t = FOeval e t).
    { intros t Ht. unfold e3.
      rewrite (FOeval_update_above t _ (B+4) p ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) na ltac:(lia)).
      exact (FOeval_update_above t e B a Ht). }
    assert (Ee3B : e3 B = a).
    { unfold e3, FOupdate. rewrite EB4, EB2, Nat.eqb_refl.
      reflexivity. }
    assert (Ee3B2 : e3 (B+2) = na).
    { unfold e3, FOupdate. rewrite E24, Nat.eqb_refl. reflexivity. }
    assert (Ee3B4 : e3 (B+4) = p).
    { unfold e3, FOupdate. rewrite Nat.eqb_refl. reflexivity. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOlookup e3 (B+6) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOnumeral 5) (FOVar B) FOZero FOZero
                      (FOVar (B+2)) Htb6 H5m HvBm H0m H0m HvB2m)).
      destruct Hr1 as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
      exists j.
      split; [rewrite (Hstab len Hlen); exact Hj|].
      split.
      { rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral.
        exact Hf1. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), Ee3B. exact Hf2. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'). exact Hf3. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'). exact Hf4. }
      cbn [FOeval].
      rewrite (Hstab cr Hcr), (Hstab dr Hdr), Ee3B2. exact Hf5. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOlookup e3 (B+28) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOnumeral 3) (FOnumeral 1)
                      (FOVar (B+2)) (FOnumeral c) (FOVar (B+4))
                      Htb28 H3m H1m HvB2m' Hcm HvB4m)).
      destruct Hr2 as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
      exists j.
      split; [rewrite (Hstab len Hlen); exact Hj|].
      split.
      { rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral.
        exact Hf1. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), FOeval_numeral.
        exact Hf2. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), Ee3B2. exact Hf3. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), FOeval_numeral.
        exact Hf4. }
      cbn [FOeval].
      rewrite (Hstab cr Hcr), (Hstab dr Hdr), Ee3B4. exact Hf5. }
    apply (proj2 (FOsat_FOPATF cpatImpl01 e3 (B+50) _ d Henv Hd50)).
    assert (Hsg : forall s,
        FOeval e3 (nth s [FOVar (B+4); FOVar B] FOZero)
        = (fun s => match s with
                    | 0 => p | 1 => a | _ => 0 end) s).
    { intro s. destruct s as [|[|s]]; cbn.
      - unfold e3, FOupdate. rewrite Nat.eqb_refl. reflexivity.
      - unfold e3, FOupdate. rewrite EB4, EB2, Nat.eqb_refl.
        reflexivity.
      - destruct s; reflexivity. }
    rewrite (cpat_sem_ext _ _ _ Hsg).
    rewrite (Hstab d Hd).
    cbn [cpat_sem cpatImpl01 pImpP].
    symmetry. exact Hshape.
Qed.

Lemma FOsat_FOPROVAT : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    c z p,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm z < B -> FOmax_var_tm p < B ->
  (FOsat e (FOPROVAT B ct dt c1 d1 c2 d2 c3 d3 cr dr len c z p) <->
   provat_sem
     (fun tg a1 a2 a3 r => exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = tg /\
        beta (FOeval e c1) (FOeval e d1) j = a1 /\
        beta (FOeval e c2) (FOeval e d2) j = a2 /\
        beta (FOeval e c3) (FOeval e d3) j = a3 /\
        beta (FOeval e cr) (FOeval e dr) j = r)
     c (FOeval e z) (FOeval e p)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len c z p Htb Hz Hp.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb2 : tbl_below (B+2) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb24 : tbl_below (B+24) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (HinB : FOin_tm B (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB : FOin_tm (S B) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (H5m : FOmax_var_tm (FOnumeral 5) < B+2)
    by (rewrite FOmax_var_numeral; lia).
  assert (Hzm : FOmax_var_tm z < B+2) by lia.
  assert (H0m : FOmax_var_tm FOZero < B+2) by (cbn; lia).
  assert (HvBm : FOmax_var_tm (FOVar B) < B+2) by (cbn; lia).
  assert (H3m : FOmax_var_tm (FOnumeral 3) < B+24)
    by (rewrite FOmax_var_numeral; lia).
  assert (H1m : FOmax_var_tm (FOnumeral 1) < B+24)
    by (rewrite FOmax_var_numeral; lia).
  assert (HvBm' : FOmax_var_tm (FOVar B) < B+24) by (cbn; lia).
  assert (Hcm : FOmax_var_tm (FOnumeral c) < B+24)
    by (rewrite FOmax_var_numeral; lia).
  assert (Hpm : FOmax_var_tm p < B+24) by lia.
  unfold FOPROVAT, provat_sem.
  rewrite (FOsat_FOBexC e B (FOSucc cr) _ HinB HinSB).
  split.
  - intros [v0 [Hv0 Hb]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb.
    destruct Hb as [Hlk1 Hlk2].
    set (e1 := FOupdate e B v0) in *.
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e1 t = FOeval e t).
    { intros t Ht. exact (FOeval_update_above t e B v0 Ht). }
    assert (Ee1B : e1 B = v0).
    { unfold e1, FOupdate. rewrite Nat.eqb_refl. reflexivity. }
    apply (proj1 (FOsat_FOlookup e1 (B+2) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 5) z FOZero FOZero
                    (FOVar B) Htb2 H5m Hzm H0m H0m HvBm)) in Hlk1.
    apply (proj1 (FOsat_FOlookup e1 (B+24) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 3) (FOnumeral 1)
                    (FOVar B) (FOnumeral c) p
                    Htb24 H3m H1m HvBm' Hcm Hpm)) in Hlk2.
    destruct Hlk1 as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
    rewrite (Hstab len Hlen) in Hj.
    rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral in Hf1.
    cbn [FOeval] in Hf2, Hf3, Hf4, Hf5.
    rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab z Hz) in Hf2.
    rewrite (Hstab c2 Hc2), (Hstab d2 Hd2') in Hf3.
    rewrite (Hstab c3 Hc3), (Hstab d3 Hd3') in Hf4.
    rewrite (Hstab cr Hcr), (Hstab dr Hdr), Ee1B in Hf5.
    destruct Hlk2 as [j2 [Hj2 [Hg1 [Hg2 [Hg3 [Hg4 Hg5]]]]]].
    rewrite (Hstab len Hlen) in Hj2.
    rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral in Hg1.
    cbn [FOeval] in Hg2, Hg3, Hg4, Hg5.
    rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), FOeval_numeral in Hg2.
    rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), Ee1B in Hg3.
    rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), FOeval_numeral in Hg4.
    rewrite (Hstab cr Hcr), (Hstab dr Hdr), (Hstab p Hp) in Hg5.
    exists v0.
    split.
    { exists j. repeat split; assumption. }
    { exists j2. repeat split; assumption. }
  - intros [nz [Hr1 Hr2]].
    assert (Hnz : nz <= FOeval e cr).
    { destruct Hr1 as [j [_ [_ [_ [_ [_ F5]]]]]].
      unfold beta in F5.
      pose proof (Nat.Div0.mod_le (FOeval e cr)
                    (FOeval e dr * S j + 1)).
      lia. }
    exists nz. split.
    { cbn [FOeval]. lia. }
    set (e1 := FOupdate e B nz).
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e1 t = FOeval e t).
    { intros t Ht. exact (FOeval_update_above t e B nz Ht). }
    assert (Ee1B : e1 B = nz).
    { unfold e1, FOupdate. rewrite Nat.eqb_refl. reflexivity. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOlookup e1 (B+2) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOnumeral 5) z FOZero FOZero
                      (FOVar B) Htb2 H5m Hzm H0m H0m HvBm)).
      destruct Hr1 as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
      exists j.
      split; [rewrite (Hstab len Hlen); exact Hj|].
      split.
      { rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral.
        exact Hf1. }
      split.
      { rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab z Hz).
        exact Hf2. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'). exact Hf3. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'). exact Hf4. }
      cbn [FOeval].
      rewrite (Hstab cr Hcr), (Hstab dr Hdr), Ee1B. exact Hf5. }
    { apply (proj2 (FOsat_FOlookup e1 (B+24) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOnumeral 3) (FOnumeral 1)
                      (FOVar B) (FOnumeral c) p
                      Htb24 H3m H1m HvBm' Hcm Hpm)).
      destruct Hr2 as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
      exists j.
      split; [rewrite (Hstab len Hlen); exact Hj|].
      split.
      { rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral.
        exact Hf1. }
      split.
      { rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), FOeval_numeral.
        exact Hf2. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), Ee1B. exact Hf3. }
      split.
      { rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), FOeval_numeral.
        exact Hf4. }
      rewrite (Hstab cr Hcr), (Hstab dr Hdr), (Hstab p Hp).
      exact Hf5. }
Qed.

Lemma FOdelta0_FOPROVAT : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    c z p,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm z < B -> FOmax_var_tm p < B ->
  FOdelta0 (FOPROVAT B ct dt c1 d1 c2 d2 c3 d3 cr dr len c z p).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len c z p Htb Hz Hp.
  pose proof Htb as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  unfold FOPROVAT.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_and.
  - apply FOdelta0_FOlookup;
      [unfold tbl_below; repeat split; lia
      |rewrite FOmax_var_numeral; lia
      |lia | cbn; lia | cbn; lia | cbn; lia].
  - apply FOdelta0_FOlookup;
      [unfold tbl_below; repeat split; lia
      |rewrite FOmax_var_numeral; lia
      |rewrite FOmax_var_numeral; lia
      |cbn; lia
      |rewrite FOmax_var_numeral; lia
      |lia].
Qed.

Lemma FOsat_FOGENF : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len z,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm z < B ->
  (FOsat e (FOGENF B ct dt c1 d1 c2 d2 c3 d3 cr dr len z) <->
   genuine_sem
     (fun tg a1 a2 a3 r => exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = tg /\
        beta (FOeval e c1) (FOeval e d1) j = a1 /\
        beta (FOeval e c2) (FOeval e d2) j = a2 /\
        beta (FOeval e c3) (FOeval e d3) j = a3 /\
        beta (FOeval e cr) (FOeval e dr) j = r)
     (FOeval e z)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len z Htb Hz.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb2 : tbl_below (B+2) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (HinB : FOin_tm B (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB : FOin_tm (S B) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (H3m : FOmax_var_tm (FOnumeral 3) < B+2)
    by (rewrite FOmax_var_numeral; lia).
  assert (HSzm : FOmax_var_tm (FOSucc z) < B+2) by (cbn; lia).
  assert (H0m : FOmax_var_tm FOZero < B+2) by (cbn; lia).
  assert (Hzm : FOmax_var_tm z < B+2) by lia.
  assert (HvBm : FOmax_var_tm (FOVar B) < B+2) by (cbn; lia).
  unfold FOGENF, genuine_sem.
  rewrite (FOsat_FOBexC e B (FOSucc cr) _ HinB HinSB).
  split.
  - intros [rg [Hrg Hlk]].
    set (e1 := FOupdate e B rg) in *.
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e1 t = FOeval e t).
    { intros t Ht. exact (FOeval_update_above t e B rg Ht). }
    assert (Ee1B : e1 B = rg).
    { unfold e1, FOupdate. rewrite Nat.eqb_refl. reflexivity. }
    apply (proj1 (FOsat_FOlookup e1 (B+2) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 3) (FOSucc z) FOZero z
                    (FOVar B) Htb2 H3m HSzm H0m Hzm HvBm)) in Hlk.
    destruct Hlk as [j [Hj [F1 [F2 [F3 [F4 F5]]]]]].
    rewrite (Hstab len Hlen) in Hj.
    rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral in F1.
    cbn [FOeval] in F2, F3, F4, F5.
    rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab z Hz) in F2.
    rewrite (Hstab c2 Hc2), (Hstab d2 Hd2') in F3.
    rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), (Hstab z Hz) in F4.
    rewrite (Hstab cr Hcr), (Hstab dr Hdr), Ee1B in F5.
    exists rg, j.
    repeat split; assumption.
  - intros [rg Hrow].
    assert (Hrgb : rg <= FOeval e cr).
    { destruct Hrow as [j [_ [_ [_ [_ [_ F5]]]]]].
      unfold beta in F5.
      pose proof (Nat.Div0.mod_le (FOeval e cr)
                    (FOeval e dr * S j + 1)).
      lia. }
    exists rg. split.
    { cbn [FOeval]. lia. }
    set (e1 := FOupdate e B rg).
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e1 t = FOeval e t).
    { intros t Ht. exact (FOeval_update_above t e B rg Ht). }
    assert (Ee1B : e1 B = rg).
    { unfold e1, FOupdate. rewrite Nat.eqb_refl. reflexivity. }
    apply (proj2 (FOsat_FOlookup e1 (B+2) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 3) (FOSucc z) FOZero z
                    (FOVar B) Htb2 H3m HSzm H0m Hzm HvBm)).
    destruct Hrow as [j [Hj [F1 [F2 [F3 [F4 F5]]]]]].
    exists j.
    split; [rewrite (Hstab len Hlen); exact Hj|].
    split.
    { rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral.
      exact F1. }
    split.
    { cbn [FOeval].
      rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab z Hz).
      exact F2. }
    split.
    { cbn [FOeval].
      rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'). exact F3. }
    split.
    { rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), (Hstab z Hz).
      exact F4. }
    cbn [FOeval].
    rewrite (Hstab cr Hcr), (Hstab dr Hdr), Ee1B. exact F5.
Qed.

Lemma FOdelta0_FOGENF : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len z,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm z < B ->
  FOdelta0 (FOGENF B ct dt c1 d1 c2 d2 c3 d3 cr dr len z).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len z Htb Hz.
  pose proof Htb as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  unfold FOGENF.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia |].
  apply FOdelta0_FOlookup;
    [unfold tbl_below; repeat split; lia
    |rewrite FOmax_var_numeral; lia
    |cbn; lia
    |cbn; lia
    |lia
    |cbn; lia].
Qed.

Lemma FOdelta0_FOD2c : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    c d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  FOdelta0 (FOD2c B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d Htb Hd.
  pose proof Htb as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  unfold FOD2c.
  repeat (apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia |]).
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_and.
  { apply FOdelta0_FOGENF;
      [unfold tbl_below; repeat split; lia | cbn; lia]. }
  apply FOdelta0_and.
  { apply FOdelta0_FOGENF;
      [unfold tbl_below; repeat split; lia | cbn; lia]. }
  apply FOdelta0_and.
  { apply FOdelta0_FOPROVAT;
      [unfold tbl_below; repeat split; lia | cbn; lia | cbn; lia]. }
  apply FOdelta0_and.
  { apply FOdelta0_FOPROVAT;
      [unfold tbl_below; repeat split; lia | cbn; lia | cbn; lia]. }
  apply FOdelta0_and.
  { apply FOdelta0_FOPROVAT;
      [unfold tbl_below; repeat split; lia | cbn; lia | cbn; lia]. }
  apply FOdelta0_FOPATF.
  - constructor; [cbn; lia |
      constructor; [cbn; lia |
      constructor; [cbn; lia | constructor]]].
  - lia.
Qed.

Lemma FOdelta0_FOD3c : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    c d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  FOdelta0 (FOD3c B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d Htb Hd.
  pose proof Htb as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  unfold FOD3c.
  repeat (apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia |]).
  apply FOdelta0_and.
  { apply FOdelta0_FOGENF;
      [unfold tbl_below; repeat split; lia | cbn; lia]. }
  apply FOdelta0_and.
  { apply FOdelta0_FOPROVAT;
      [unfold tbl_below; repeat split; lia | cbn; lia | cbn; lia]. }
  apply FOdelta0_and.
  { apply FOdelta0_FOPROVAT;
      [unfold tbl_below; repeat split; lia | cbn; lia | cbn; lia]. }
  apply FOdelta0_FOPATF.
  - constructor; [cbn; lia |
      constructor; [cbn; lia | constructor]].
  - lia.
Qed.

Lemma FOdelta0_FODMONc : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    c c' d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  FOdelta0 (FODMONc B ct dt c1 d1 c2 d2 c3 d3 cr dr len c c' d).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len c c' d Htb Hd.
  pose proof Htb as [Hct [Hdt [Hc1 [Hd1 [Hc2 [Hd2 [Hc3 [Hd3
    [Hcr [Hdr Hlen]]]]]]]]]].
  unfold FODMONc.
  repeat (apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia |]).
  apply FOdelta0_and.
  { apply FOdelta0_FOGENF;
      [unfold tbl_below; repeat split; lia | cbn; lia]. }
  apply FOdelta0_and.
  { apply FOdelta0_FOPROVAT;
      [unfold tbl_below; repeat split; lia | cbn; lia | cbn; lia]. }
  apply FOdelta0_and.
  { apply FOdelta0_FOPROVAT;
      [unfold tbl_below; repeat split; lia | cbn; lia | cbn; lia]. }
  apply FOdelta0_FOPATF.
  - constructor; [cbn; lia |
      constructor; [cbn; lia | constructor]].
  - lia.
Qed.

Lemma FOsat_FOREFLSc : forall cores e B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  (FOsat e (FOREFLSc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) <->
   refls_sem
     (fun tg a1 a2 a3 r => exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = tg /\
        beta (FOeval e c1) (FOeval e d1) j = a1 /\
        beta (FOeval e c2) (FOeval e d2) j = a2 /\
        beta (FOeval e c3) (FOeval e d3) j = a3 /\
        beta (FOeval e cr) (FOeval e dr) j = r)
     cores (FOeval e d)).
Proof.
  intros cores.
  induction cores as [|c rest IH];
    intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len d Htb Hd;
    cbn [FOREFLSc refls_sem].
  - cbn [FOsat]. tauto.
  - rewrite (FOsat_FOOr e _ _).
    rewrite (FOsat_FOAXREFLc e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
               c d Htb Hd).
    rewrite (IH e B ct dt c1 d1 c2 d2 c3 d3 cr dr len d Htb Hd).
    reflexivity.
Qed.

Lemma FOsat_FOTHAXc : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cores d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  (FOsat e (FOTHAXc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) <->
   thax_sem
     (fun tg a1 a2 a3 r => exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = tg /\
        beta (FOeval e c1) (FOeval e d1) j = a1 /\
        beta (FOeval e c2) (FOeval e d2) j = a2 /\
        beta (FOeval e c3) (FOeval e d3) j = a3 /\
        beta (FOeval e cr) (FOeval e dr) j = r)
     cores (FOeval e d)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d Htb Hd.
  unfold FOTHAXc, thax_sem.
  rewrite (FOsat_FOOr e _ _).
  rewrite (FOsat_FOAXQc e B d Hd).
  rewrite (FOsat_FOREFLSc cores e B ct dt c1 d1 c2 d2 c3 d3 cr dr
             len d Htb Hd).
  reflexivity.
Qed.

Lemma FOdelta0_FOAXREFLc : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    c d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  FOdelta0 (FOAXREFLc B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d Htb Hd.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb6 : tbl_below (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb28 : tbl_below (B+28) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  unfold FOAXREFLc.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; exact Hd
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_and.
  { apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia. }
  apply FOdelta0_and.
  { apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia. }
  apply FOdelta0_FOPATF.
  - constructor; [cbn; lia |
      constructor; [cbn; lia | constructor]].
  - lia.
Qed.

Lemma FOdelta0_FOREFLSc : forall cores B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  FOdelta0 (FOREFLSc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d).
Proof.
  intros cores.
  induction cores as [|c rest IH];
    intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len d Htb Hd;
    cbn [FOREFLSc].
  - exact FOd0_false.
  - apply FOdelta0_or.
    + apply FOdelta0_FOAXREFLc; assumption.
    + apply IH; assumption.
Qed.

Lemma FOdelta0_FOD2Sc : forall cores B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  FOdelta0 (FOD2Sc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d).
Proof.
  induction cores as [|c rest IH];
    intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len d Htb Hd;
    cbn [FOD2Sc].
  - exact FOd0_false.
  - apply FOdelta0_or.
    + apply FOdelta0_FOD2c; assumption.
    + apply IH; assumption.
Qed.

Lemma FOdelta0_FOD3Sc : forall cores B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  FOdelta0 (FOD3Sc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d).
Proof.
  induction cores as [|c rest IH];
    intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len d Htb Hd;
    cbn [FOD3Sc].
  - exact FOd0_false.
  - apply FOdelta0_or.
    + apply FOdelta0_FOD3c; assumption.
    + apply IH; assumption.
Qed.

Lemma FOdelta0_FODMONS1 : forall cs B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len c d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  FOdelta0 (FODMONS1 B ct dt c1 d1 c2 d2 c3 d3 cr dr len c cs d).
Proof.
  induction cs as [|c' rest IH];
    intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d Htb Hd;
    cbn [FODMONS1].
  - exact FOd0_false.
  - apply FOdelta0_or.
    + apply FOdelta0_FODMONc; assumption.
    + apply IH; assumption.
Qed.

Lemma FOdelta0_FODMONSc : forall cores B ct dt c1 d1 c2 d2 c3 d3 cr
    dr len d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  FOdelta0 (FODMONSc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d).
Proof.
  induction cores as [|c rest IH];
    intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len d Htb Hd;
    cbn [FODMONSc].
  - exact FOd0_false.
  - apply FOdelta0_or.
    + apply FOdelta0_FODMONS1; assumption.
    + apply IH; assumption.
Qed.

Lemma FOdelta0_FOTHAXc : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cores d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  FOdelta0 (FOTHAXc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d Htb Hd.
  unfold FOTHAXc.
  apply FOdelta0_or.
  - apply FOdelta0_FOAXQc. exact Hd.
  - apply FOdelta0_FOREFLSc; assumption.
Qed.

(** Extensionality of the recognizer semantics in the lookup
    relation. *)

Lemma logax_sem_ext : forall L L' d,
  (forall a b c0 d0 r, L a b c0 d0 r <-> L' a b c0 d0 r) ->
  (logax_sem L d <-> logax_sem L' d).
Proof.
  intros L L' d HL. unfold logax_sem.
  split; intro H;
    destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]].
  - left. exact H.
  - right; left. exact H.
  - right; right; left. exact H.
  - do 3 right; left. exact H.
  - do 4 right; left. exact H.
  - do 5 right; left. exact H.
  - do 6 right; left. exact H.
  - do 7 right; left. exact H.
  - do 8 right; left. exact H.
  - do 9 right; left.
    destruct H as [x [P [Q [Hs Hr]]]].
    exists x, P, Q. split; [exact Hs | apply HL; exact Hr].
  - do 10 right; left. exact H.
  - do 11 right.
    destruct H as [x [P [Q [Hs Hr]]]].
    exists x, P, Q. split; [exact Hs | apply HL; exact Hr].
  - left. exact H.
  - right; left. exact H.
  - right; right; left. exact H.
  - do 3 right; left. exact H.
  - do 4 right; left. exact H.
  - do 5 right; left. exact H.
  - do 6 right; left. exact H.
  - do 7 right; left. exact H.
  - do 8 right; left. exact H.
  - do 9 right; left.
    destruct H as [x [P [Q [Hs Hr]]]].
    exists x, P, Q. split; [exact Hs | apply HL; exact Hr].
  - do 10 right; left. exact H.
  - do 11 right.
    destruct H as [x [P [Q [Hs Hr]]]].
    exists x, P, Q. split; [exact Hs | apply HL; exact Hr].
Qed.

Lemma refl_sem_ext : forall L L' c d,
  (forall a b c0 d0 r, L a b c0 d0 r <-> L' a b c0 d0 r) ->
  (refl_sem L c d <-> refl_sem L' c d).
Proof.
  intros L L' c d HL. unfold refl_sem.
  split; intros [a [na [p [H1 [H2 H3]]]]];
    exists a, na, p;
    (split; [apply HL; exact H1 |
     split; [apply HL; exact H2 | exact H3]]).
Qed.

Lemma refls_sem_ext : forall cores L L' d,
  (forall a b c0 d0 r, L a b c0 d0 r <-> L' a b c0 d0 r) ->
  (refls_sem L cores d <-> refls_sem L' cores d).
Proof.
  intros cores.
  induction cores as [|c rest IH]; intros L L' d HL; cbn [refls_sem].
  - tauto.
  - rewrite (refl_sem_ext L L' c d HL).
    rewrite (IH L L' d HL).
    reflexivity.
Qed.

Lemma thax_sem_ext : forall L L' cores d,
  (forall a b c0 d0 r, L a b c0 d0 r <-> L' a b c0 d0 r) ->
  (thax_sem L cores d <-> thax_sem L' cores d).
Proof.
  intros L L' cores d HL. unfold thax_sem.
  rewrite (refls_sem_ext cores L L' d HL).
  reflexivity.
Qed.

(** The semantic mirror of the justification checker at one position.
    [u] is the value of the free template variable 0. *)

Definition justck_sem (L : nat -> nat -> nat -> nat -> nat -> Prop)
    (cores : list nat) (u vcs vds vcj vdj i : nat) : Prop :=
  exists vd vj tg pl,
    beta vcs vds i = vd /\ beta vcj vdj i = vj /\
    cpair tg pl = vj /\
    ( (tg = 0 /\ thax_sem L cores vd)
    \/ (tg = 1 /\ logax_sem L vd)
    \/ (tg = 2 /\ exists x tc P Q, cpair x tc = pl /\
          vd = cpair 2 (cpair (cpair 3 (cpair x P)) Q) /\
          L 4 x tc P 1 /\ L 3 x tc P Q)
    \/ (tg = 3 /\ exists x tc P Q, cpair x tc = pl /\
          vd = cpair 2 (cpair Q (cpair 4 (cpair x P))) /\
          L 4 x tc P 1 /\ L 3 x tc P Q)
    \/ (tg = 4 /\ exists i' j' bi bj, cpair i' j' = pl /\
          i' < i /\ j' < i /\
          beta vcs vds i' = bi /\ beta vcs vds j' = bj /\
          bi = cpair 2 (cpair bj vd))
    \/ (tg = 5 /\ pl < i /\ exists bj x,
          beta vcs vds pl = bj /\ vd = cpair 3 (cpair x bj))
    \/ (tg = 6 /\ pl < i /\ exists bj nu core na p,
          beta vcs vds pl = bj /\
          L 5 u 0 0 nu /\ L 3 0 nu u core /\
          L 5 vd 0 0 na /\ L 3 1 na core p /\
          bj = cpair 2 (cpair p vd))
    \/ (tg = 7 /\ d2s_sem L cores vd)
    \/ (tg = 8 /\ d3s_sem L cores vd)
    \/ (tg = 9 /\ dmons_sem L cores vd)
    \/ (tg = 10 /\ exists x PA C0 SS,
          pl = cpair x PA /\
          vd = cpair 2 (cpair C0 (cpair 2 (cpair
                 (cpair 3 (cpair x (cpair 2 (cpair PA SS))))
                 (cpair 3 (cpair x PA))))) /\
          L 4 x (cpair 1 0) PA 1 /\ L 3 x (cpair 1 0) PA C0 /\
          L 4 x (cpair 2 (cpair 0 x)) PA 1 /\
          L 3 x (cpair 2 (cpair 0 x)) PA SS)).

Lemma provat_sem_ext : forall c z p L L',
  (forall a b c0 d0 r, L a b c0 d0 r <-> L' a b c0 d0 r) ->
  (provat_sem L c z p <-> provat_sem L' c z p).
Proof.
  intros c z p L L' HL.
  split; intros [nz [H1 H2]]; exists nz;
    split; apply HL; assumption.
Qed.

Lemma genuine_sem_ext : forall z L L',
  (forall a b c0 d0 r, L a b c0 d0 r <-> L' a b c0 d0 r) ->
  (genuine_sem L z <-> genuine_sem L' z).
Proof.
  intros z L L' HL.
  split; intros [rg Hr]; exists rg; apply HL; assumption.
Qed.

Lemma d2one_sem_ext : forall c L L' d,
  (forall a b c0 d0 r, L a b c0 d0 r <-> L' a b c0 d0 r) ->
  (d2one_sem L c d <-> d2one_sem L' c d).
Proof.
  intros c L L' d HL. unfold d2one_sem.
  split; intros [x [y [pixy [px [py [G1 [G2 [R1 [R2 [R3
      Hsh]]]]]]]]]];
    exists x, y, pixy, px, py;
    (split; [apply (genuine_sem_ext _ L L' HL); exact G1|]);
    (split; [apply (genuine_sem_ext _ L L' HL); exact G2|]);
    (split; [apply (provat_sem_ext _ _ _ L L' HL); exact R1|]);
    (split; [apply (provat_sem_ext _ _ _ L L' HL); exact R2|]);
    (split; [apply (provat_sem_ext _ _ _ L L' HL); exact R3|]);
    exact Hsh.
Qed.

Lemma d3one_sem_ext : forall c L L' d,
  (forall a b c0 d0 r, L a b c0 d0 r <-> L' a b c0 d0 r) ->
  (d3one_sem L c d <-> d3one_sem L' c d).
Proof.
  intros c L L' d HL. unfold d3one_sem.
  split; intros [a [pa [ppa [G1 [R1 [R2 Hsh]]]]]];
    exists a, pa, ppa;
    (split; [apply (genuine_sem_ext _ L L' HL); exact G1|]);
    (split; [apply (provat_sem_ext _ _ _ L L' HL); exact R1|]);
    (split; [apply (provat_sem_ext _ _ _ L L' HL); exact R2|]);
    exact Hsh.
Qed.

Lemma dmonone_sem_ext : forall c c' L L' d,
  (forall a b c0 d0 r, L a b c0 d0 r <-> L' a b c0 d0 r) ->
  (dmonone_sem L c c' d <-> dmonone_sem L' c c' d).
Proof.
  intros c c' L L' d HL. unfold dmonone_sem.
  split; intros [a [p [p' [G1 [R1 [R2 Hsh]]]]]];
    exists a, p, p';
    (split; [apply (genuine_sem_ext _ L L' HL); exact G1|]);
    (split; [apply (provat_sem_ext _ _ _ L L' HL); exact R1|]);
    (split; [apply (provat_sem_ext _ _ _ L L' HL); exact R2|]);
    exact Hsh.
Qed.

Lemma d2s_sem_ext : forall cores L L' d,
  (forall a b c0 d0 r, L a b c0 d0 r <-> L' a b c0 d0 r) ->
  (d2s_sem L cores d <-> d2s_sem L' cores d).
Proof.
  induction cores as [|c rest IH]; intros L L' d HL;
    cbn [d2s_sem].
  - reflexivity.
  - rewrite (d2one_sem_ext c L L' d HL).
    rewrite (IH L L' d HL). reflexivity.
Qed.

Lemma d3s_sem_ext : forall cores L L' d,
  (forall a b c0 d0 r, L a b c0 d0 r <-> L' a b c0 d0 r) ->
  (d3s_sem L cores d <-> d3s_sem L' cores d).
Proof.
  induction cores as [|c rest IH]; intros L L' d HL;
    cbn [d3s_sem].
  - reflexivity.
  - rewrite (d3one_sem_ext c L L' d HL).
    rewrite (IH L L' d HL). reflexivity.
Qed.

Lemma dmons1_sem_ext : forall cs c L L' d,
  (forall a b c0 d0 r, L a b c0 d0 r <-> L' a b c0 d0 r) ->
  (dmons1_sem L c cs d <-> dmons1_sem L' c cs d).
Proof.
  induction cs as [|c' rest IH]; intros c L L' d HL;
    cbn [dmons1_sem].
  - reflexivity.
  - rewrite (dmonone_sem_ext c c' L L' d HL).
    rewrite (IH c L L' d HL). reflexivity.
Qed.

Lemma dmons_sem_ext : forall cores L L' d,
  (forall a b c0 d0 r, L a b c0 d0 r <-> L' a b c0 d0 r) ->
  (dmons_sem L cores d <-> dmons_sem L' cores d).
Proof.
  induction cores as [|c rest IH]; intros L L' d HL;
    cbn [dmons_sem].
  - reflexivity.
  - rewrite (dmons1_sem_ext (c :: rest) c L L' d HL).
    rewrite (IH L L' d HL). reflexivity.
Qed.

Lemma justck_sem_ext : forall L L' cores u vcs vds vcj vdj i,
  (forall a b c0 d0 r, L a b c0 d0 r <-> L' a b c0 d0 r) ->
  (justck_sem L cores u vcs vds vcj vdj i <->
   justck_sem L' cores u vcs vds vcj vdj i).
Proof.
  intros L L' cores u vcs vds vcj vdj i HL. unfold justck_sem.
  split; intros [vd [vj [tg [pl [H1 [H2 [H3 H4]]]]]]];
    exists vd, vj, tg, pl;
    (split; [exact H1|]); (split; [exact H2|]); (split; [exact H3|]);
    (destruct H4 as [H4|[H4|[H4|[H4|[H4|[H4|[H4|[H4|[H4|[H4|H4]]]]]]]]]]).
  - left. destruct H4 as [Ht H4]. split; [exact Ht|].
    apply (thax_sem_ext L L' cores vd HL). exact H4.
  - right; left. destruct H4 as [Ht H4]. split; [exact Ht|].
    apply (logax_sem_ext L L' vd HL). exact H4.
  - do 2 right; left.
    destruct H4 as [Ht [x [tc [P [Q [Hp [Hs [Ha Hb]]]]]]]].
    split; [exact Ht|]. exists x, tc, P, Q.
    split; [exact Hp|]. split; [exact Hs|].
    split; [apply HL; exact Ha | apply HL; exact Hb].
  - do 3 right; left.
    destruct H4 as [Ht [x [tc [P [Q [Hp [Hs [Ha Hb]]]]]]]].
    split; [exact Ht|]. exists x, tc, P, Q.
    split; [exact Hp|]. split; [exact Hs|].
    split; [apply HL; exact Ha | apply HL; exact Hb].
  - do 4 right; left. exact H4.
  - do 5 right; left. exact H4.
  - do 6 right; left.
    destruct H4 as [Ht [Hpl [bj [nu [core [na [p
      [Hb [Hn [Hc [Hna [Hp Hsh]]]]]]]]]]]].
    split; [exact Ht|]. split; [exact Hpl|].
    exists bj, nu, core, na, p.
    split; [exact Hb|].
    split; [apply HL; exact Hn|].
    split; [apply HL; exact Hc|].
    split; [apply HL; exact Hna|].
    split; [apply HL; exact Hp|].
    exact Hsh.
  - do 7 right; left. destruct H4 as [Ht H4]. split; [exact Ht|].
    apply (d2s_sem_ext cores L L' vd HL). exact H4.
  - do 8 right; left. destruct H4 as [Ht H4]. split; [exact Ht|].
    apply (d3s_sem_ext cores L L' vd HL). exact H4.
  - do 9 right; left. destruct H4 as [Ht H4]. split; [exact Ht|].
    apply (dmons_sem_ext cores L L' vd HL). exact H4.
  - do 10 right.
    destruct H4 as [Ht [x [PA [C0 [SS [Hp [Hv [Ha [Hb [Hc Hd]]]]]]]]]].
    split; [exact Ht|]. exists x, PA, C0, SS.
    split; [exact Hp|]. split; [exact Hv|].
    split; [apply HL; exact Ha|]. split; [apply HL; exact Hb|].
    split; [apply HL; exact Hc | apply HL; exact Hd].
  - left. destruct H4 as [Ht H4]. split; [exact Ht|].
    apply (thax_sem_ext L L' cores vd HL). exact H4.
  - right; left. destruct H4 as [Ht H4]. split; [exact Ht|].
    apply (logax_sem_ext L L' vd HL). exact H4.
  - do 2 right; left.
    destruct H4 as [Ht [x [tc [P [Q [Hp [Hs [Ha Hb]]]]]]]].
    split; [exact Ht|]. exists x, tc, P, Q.
    split; [exact Hp|]. split; [exact Hs|].
    split; [apply HL; exact Ha | apply HL; exact Hb].
  - do 3 right; left.
    destruct H4 as [Ht [x [tc [P [Q [Hp [Hs [Ha Hb]]]]]]]].
    split; [exact Ht|]. exists x, tc, P, Q.
    split; [exact Hp|]. split; [exact Hs|].
    split; [apply HL; exact Ha | apply HL; exact Hb].
  - do 4 right; left. exact H4.
  - do 5 right; left. exact H4.
  - do 6 right; left.
    destruct H4 as [Ht [Hpl [bj [nu [core [na [p
      [Hb [Hn [Hc [Hna [Hp Hsh]]]]]]]]]]]].
    split; [exact Ht|]. split; [exact Hpl|].
    exists bj, nu, core, na, p.
    split; [exact Hb|].
    split; [apply HL; exact Hn|].
    split; [apply HL; exact Hc|].
    split; [apply HL; exact Hna|].
    split; [apply HL; exact Hp|].
    exact Hsh.
  - do 7 right; left. destruct H4 as [Ht H4]. split; [exact Ht|].
    apply (d2s_sem_ext cores L L' vd HL). exact H4.
  - do 8 right; left. destruct H4 as [Ht H4]. split; [exact Ht|].
    apply (d3s_sem_ext cores L L' vd HL). exact H4.
  - do 9 right; left. destruct H4 as [Ht H4]. split; [exact Ht|].
    apply (dmons_sem_ext cores L L' vd HL). exact H4.
  - do 10 right.
    destruct H4 as [Ht [x [PA [C0 [SS [Hp [Hv [Ha [Hb [Hc Hd]]]]]]]]]].
    split; [exact Ht|]. exists x, PA, C0, SS.
    split; [exact Hp|]. split; [exact Hv|].
    split; [apply HL; exact Ha|]. split; [apply HL; exact Hb|].
    split; [apply HL; exact Hc | apply HL; exact Hd].
Qed.

Lemma FOdelta0_FOJSUBST : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    pat vd pl,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm vd < B -> FOmax_var_tm pl < B ->
  FOdelta0 (FOJSUBST B ct dt c1 d1 c2 d2 c3 d3 cr dr len pat vd pl).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len pat vd pl Htb Hvd Hpl.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb30 : tbl_below (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb52 : tbl_below (B+52) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  unfold FOJSUBST.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_and.
  { apply FOdelta0_FOPATF.
    - constructor; [cbn; lia |
        constructor; [cbn; lia |
        constructor; [cbn; lia | constructor]]].
    - lia. }
  apply FOdelta0_and.
  { apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia. }
  apply FOdelta0_FOlookup; try assumption;
    rewrite ?FOmax_var_numeral; cbn; lia.
Qed.

Lemma FOdelta0_FOJIND : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len vd pl,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm vd < B -> FOmax_var_tm pl < B ->
  FOdelta0 (FOJIND B ct dt c1 d1 c2 d2 c3 d3 cr dr len vd pl).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len vd pl Htb Hvd Hpl.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb52 : tbl_below (B+52) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb74 : tbl_below (B+74) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb96 : tbl_below (B+96) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb118 : tbl_below (B+118) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  unfold FOJIND.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia|apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia|apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  repeat (apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia|apply FOin_tm_above; cbn; lia|]).
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_and.
  { apply FOdelta0_FOPATF.
    - constructor; [cbn; lia | constructor; [cbn; lia |
        constructor; [cbn; lia | constructor; [cbn; lia | constructor]]]].
    - lia. }
  apply FOdelta0_and;
    [apply FOdelta0_FOlookup; try assumption;
       rewrite ?FOmax_var_numeral; cbn; lia|].
  apply FOdelta0_and;
    [apply FOdelta0_FOlookup; try assumption;
       rewrite ?FOmax_var_numeral; cbn; lia|].
  apply FOdelta0_and;
    [apply FOdelta0_FOlookup; try assumption;
       rewrite ?FOmax_var_numeral; cbn; lia|].
  apply FOdelta0_FOlookup; try assumption;
    rewrite ?FOmax_var_numeral; cbn; lia.
Qed.

Lemma FOdelta0_FOJMP : forall B cs ds vd pl ipos,
  FOmax_var_tm cs < B -> FOmax_var_tm ds < B ->
  FOmax_var_tm vd < B -> FOmax_var_tm pl < B ->
  FOmax_var_tm ipos < B ->
  FOdelta0 (FOJMP B cs ds vd pl ipos).
Proof.
  intros B cs ds vd pl ipos Hcs Hds Hvd Hpl Hi.
  unfold FOJMP.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_and; [apply FOdelta0_FOcpairF|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_and.
  { apply FOdelta0_FObetaF; cbn; lia. }
  apply FOdelta0_and.
  { apply FOdelta0_FObetaF; cbn; lia. }
  apply FOdelta0_FOPATF.
  - constructor; [cbn; lia |
      constructor; [lia | constructor]].
  - cbn. lia.
Qed.

Lemma FOdelta0_FOJGEN : forall B cs ds vd pl ipos,
  FOmax_var_tm cs < B -> FOmax_var_tm ds < B ->
  FOmax_var_tm vd < B -> FOmax_var_tm pl < B ->
  FOmax_var_tm ipos < B ->
  FOdelta0 (FOJGEN B cs ds vd pl ipos).
Proof.
  intros B cs ds vd pl ipos Hcs Hds Hvd Hpl Hi.
  unfold FOJGEN.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_and; [apply FOd0_eq|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_and.
  { apply FOdelta0_FObetaF; cbn; lia. }
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOPATF.
  - constructor; [cbn; lia |
      constructor; [cbn; lia | constructor]].
  - lia.
Qed.

Lemma FOdelta0_FOJLOEB : forall B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    cs ds vd pl ipos,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm cs < B -> FOmax_var_tm ds < B ->
  FOmax_var_tm vd < B -> FOmax_var_tm pl < B ->
  FOmax_var_tm ipos < B ->
  FOdelta0 (FOJLOEB B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds
              vd pl ipos).
Proof.
  intros B ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds vd pl ipos
    Htb Hcs Hds Hvd Hpl Hi.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb16 : tbl_below (B+16) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb38 : tbl_below (B+38) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb60 : tbl_below (B+60) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb82 : tbl_below (B+82) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  unfold FOJLOEB.
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_and; [apply FOd0_eq|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_and.
  { apply FOdelta0_FObetaF; cbn; lia. }
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_FOBexC;
    [apply FOin_tm_above; cbn; lia
    |apply FOin_tm_above; cbn; lia|].
  apply FOdelta0_and.
  { apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia. }
  apply FOdelta0_and.
  { apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia. }
  apply FOdelta0_and.
  { apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia. }
  apply FOdelta0_and.
  { apply FOdelta0_FOlookup; try assumption;
      rewrite ?FOmax_var_numeral; cbn; lia. }
  apply FOdelta0_FOPATF.
  - constructor; [cbn; lia |
      constructor; [lia | constructor]].
  - cbn. lia.
Qed.

Lemma FOupdate_eq : forall e x v, FOupdate e x v x = v.
Proof.
  intros e x v. unfold FOupdate. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma FOupdate_neq : forall e x v y, y <> x -> FOupdate e x v y = e y.
Proof.
  intros e x v y Hyx. unfold FOupdate.
  destruct (Nat.eqb_spec y x) as [E|E]; [contradiction | reflexivity].
Qed.

Lemma provat_arg_le : forall e
    (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm) c z p,
  provat_sem
    (fun tg a1 a2 a3 r => exists j, j < FOeval e len /\
       beta (FOeval e ct) (FOeval e dt) j = tg /\
       beta (FOeval e c1) (FOeval e d1) j = a1 /\
       beta (FOeval e c2) (FOeval e d2) j = a2 /\
       beta (FOeval e c3) (FOeval e d3) j = a3 /\
       beta (FOeval e cr) (FOeval e dr) j = r)
    c z p ->
  z <= FOeval e c1 /\ p <= FOeval e cr.
Proof.
  intros e ct dt c1 d1 c2 d2 c3 d3 cr dr len c z p [nz [R1 R2]].
  split.
  - destruct R1 as [j [_ [_ [F2 _]]]].
    unfold beta in F2.
    pose proof (Nat.Div0.mod_le (FOeval e c1)
                  (FOeval e d1 * S j + 1)).
    lia.
  - destruct R2 as [j [_ [_ [_ [_ [_ F5]]]]]].
    unfold beta in F5.
    pose proof (Nat.Div0.mod_le (FOeval e cr)
                  (FOeval e dr * S j + 1)).
    lia.
Qed.

Lemma FOsat_FOD3c : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  (FOsat e (FOD3c B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d) <->
   d3one_sem
     (fun tg a1 a2 a3 r => exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = tg /\
        beta (FOeval e c1) (FOeval e d1) j = a1 /\
        beta (FOeval e c2) (FOeval e d2) j = a2 /\
        beta (FOeval e c3) (FOeval e d3) j = a3 /\
        beta (FOeval e cr) (FOeval e dr) j = r)
     c (FOeval e d)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d Htb Hd.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb6 : tbl_below (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb30 : tbl_below (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb76 : tbl_below (B+76) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (HinB : FOin_tm B (FOSucc c1) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB : FOin_tm (S B) (FOSucc c1) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB2 : FOin_tm (B+2) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB2 : FOin_tm (S (B+2)) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB4 : FOin_tm (B+4) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB4 : FOin_tm (S (B+4)) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (Hg6 : FOmax_var_tm (FOVar B) < B+6) by (cbn; lia).
  assert (Hz30 : FOmax_var_tm (FOVar B) < B+30) by (cbn; lia).
  assert (Hp30 : FOmax_var_tm (FOVar (B+2)) < B+30) by (cbn; lia).
  assert (Hz76 : FOmax_var_tm (FOVar (B+2)) < B+76) by (cbn; lia).
  assert (Hp76 : FOmax_var_tm (FOVar (B+4)) < B+76) by (cbn; lia).
  assert (Henv : Forall (fun t => FOmax_var_tm t < B+122)
                   [FOVar (B+2); FOVar (B+4)])
    by (constructor; [cbn; lia |
        constructor; [cbn; lia | constructor]]).
  assert (Hd122 : FOmax_var_tm d < B+122) by lia.
  unfold FOD3c, d3one_sem.
  rewrite (FOsat_FOBexC e B (FOSucc c1) _ HinB HinSB).
  split.
  - intros [a [Ha Hb]].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc cr) _ HinB2 HinSB2) in Hb.
    destruct Hb as [pa [Hpa Hb2]].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc cr) _ HinB4 HinSB4) in Hb2.
    destruct Hb2 as [ppa [Hppa Hb3]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb3.
    destruct Hb3 as [HG Hb4].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb4.
    destruct Hb4 as [Hpv1 Hb5].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb5.
    destruct Hb5 as [Hpv2 Hpat].
    set (e3 := FOupdate (FOupdate (FOupdate e B a) (B+2) pa)
                 (B+4) ppa) in *.
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e3 t = FOeval e t).
    { intros t Ht. unfold e3.
      rewrite (FOeval_update_above t _ (B+4) ppa ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) pa ltac:(lia)).
      exact (FOeval_update_above t e B a Ht). }
    assert (Ee3B : e3 B = a).
    { unfold e3.
      rewrite (FOupdate_neq _ (B+4) ppa B) by lia.
      rewrite (FOupdate_neq _ (B+2) pa B) by lia.
      apply FOupdate_eq. }
    assert (Ee3B2 : e3 (B+2) = pa).
    { unfold e3.
      rewrite (FOupdate_neq _ (B+4) ppa (B+2)) by lia.
      apply FOupdate_eq. }
    assert (Ee3B4 : e3 (B+4) = ppa).
    { unfold e3. apply FOupdate_eq. }
    apply (proj1 (FOsat_FOGENF e3 (B+6) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOVar B) Htb6 Hg6)) in HG.
    apply (proj1 (FOsat_FOPROVAT e3 (B+30) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len c (FOVar B) (FOVar (B+2))
                    Htb30 Hz30 Hp30)) in Hpv1.
    apply (proj1 (FOsat_FOPROVAT e3 (B+76) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len c (FOVar (B+2)) (FOVar (B+4))
                    Htb76 Hz76 Hp76)) in Hpv2.
    cbn [FOeval] in HG, Hpv1, Hpv2.
    rewrite Ee3B in HG.
    rewrite Ee3B, Ee3B2 in Hpv1.
    rewrite Ee3B2, Ee3B4 in Hpv2.
    rewrite (Hstab len Hlen), (Hstab ct Hct), (Hstab dt Hdt),
      (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab c2 Hc2),
      (Hstab d2 Hd2'), (Hstab c3 Hc3), (Hstab d3 Hd3'),
      (Hstab cr Hcr), (Hstab dr Hdr) in HG, Hpv1, Hpv2.
    apply (proj1 (FOsat_FOPATF cpatImpl01 e3 (B+122) _ d Henv
                    Hd122)) in Hpat.
    assert (Hsg : forall s,
        FOeval e3 (nth s [FOVar (B+2); FOVar (B+4)] FOZero)
        = (fun s => match s with
                    | 0 => pa | 1 => ppa | _ => 0 end) s).
    { intro s. destruct s as [|[|s]]; cbn.
      - exact Ee3B2.
      - exact Ee3B4.
      - destruct s; reflexivity. }
    rewrite (cpat_sem_ext _ _ _ Hsg) in Hpat.
    rewrite (Hstab d Hd) in Hpat.
    cbn [cpat_sem cpatImpl01 pImpP] in Hpat.
    exists a, pa, ppa.
    split; [exact HG|].
    split; [exact Hpv1|]. split; [exact Hpv2|].
    symmetry. exact Hpat.
  - intros [a [pa [ppa [HG [R1 [R2 Hshape]]]]]].
    destruct (provat_arg_le e ct dt c1 d1 c2 d2 c3 d3 cr dr len
                c a pa R1) as [HaB HpaB].
    destruct (provat_arg_le e ct dt c1 d1 c2 d2 c3 d3 cr dr len
                c pa ppa R2) as [_ HppaB].
    cbn [FOeval].
    exists a. split; [lia|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc cr) _ HinB2 HinSB2).
    exists pa. split.
    { cbn [FOeval]. rewrite (FOeval_update_above cr e B a Hcr).
      lia. }
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc cr) _ HinB4 HinSB4).
    exists ppa. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above cr _ (B+2) pa ltac:(lia)).
      rewrite (FOeval_update_above cr e B a Hcr). lia. }
    set (e3 := FOupdate (FOupdate (FOupdate e B a) (B+2) pa)
                 (B+4) ppa).
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e3 t = FOeval e t).
    { intros t Ht. unfold e3.
      rewrite (FOeval_update_above t _ (B+4) ppa ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) pa ltac:(lia)).
      exact (FOeval_update_above t e B a Ht). }
    assert (Ee3B : e3 B = a).
    { unfold e3.
      rewrite (FOupdate_neq _ (B+4) ppa B) by lia.
      rewrite (FOupdate_neq _ (B+2) pa B) by lia.
      apply FOupdate_eq. }
    assert (Ee3B2 : e3 (B+2) = pa).
    { unfold e3.
      rewrite (FOupdate_neq _ (B+4) ppa (B+2)) by lia.
      apply FOupdate_eq. }
    assert (Ee3B4 : e3 (B+4) = ppa).
    { unfold e3. apply FOupdate_eq. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOGENF e3 (B+6) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOVar B) Htb6 Hg6)).
      cbn [FOeval]. rewrite Ee3B.
      rewrite (Hstab len Hlen), (Hstab ct Hct), (Hstab dt Hdt),
        (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab c2 Hc2),
        (Hstab d2 Hd2'), (Hstab c3 Hc3), (Hstab d3 Hd3'),
        (Hstab cr Hcr), (Hstab dr Hdr).
      exact HG. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOPROVAT e3 (B+30) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len c (FOVar B) (FOVar (B+2))
                      Htb30 Hz30 Hp30)).
      cbn [FOeval]. rewrite Ee3B, Ee3B2.
      rewrite (Hstab len Hlen), (Hstab ct Hct), (Hstab dt Hdt),
        (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab c2 Hc2),
        (Hstab d2 Hd2'), (Hstab c3 Hc3), (Hstab d3 Hd3'),
        (Hstab cr Hcr), (Hstab dr Hdr).
      exact R1. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOPROVAT e3 (B+76) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len c (FOVar (B+2)) (FOVar (B+4))
                      Htb76 Hz76 Hp76)).
      cbn [FOeval]. rewrite Ee3B2, Ee3B4.
      rewrite (Hstab len Hlen), (Hstab ct Hct), (Hstab dt Hdt),
        (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab c2 Hc2),
        (Hstab d2 Hd2'), (Hstab c3 Hc3), (Hstab d3 Hd3'),
        (Hstab cr Hcr), (Hstab dr Hdr).
      exact R2. }
    apply (proj2 (FOsat_FOPATF cpatImpl01 e3 (B+122) _ d Henv
                    Hd122)).
    assert (Hsg : forall s,
        FOeval e3 (nth s [FOVar (B+2); FOVar (B+4)] FOZero)
        = (fun s => match s with
                    | 0 => pa | 1 => ppa | _ => 0 end) s).
    { intro s. destruct s as [|[|s]]; cbn.
      - exact Ee3B2.
      - exact Ee3B4.
      - destruct s; reflexivity. }
    rewrite (cpat_sem_ext _ _ _ Hsg).
    rewrite (Hstab d Hd).
    cbn [cpat_sem cpatImpl01 pImpP].
    symmetry. exact Hshape.
Qed.

Lemma FOsat_FOD2c : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  (FOsat e (FOD2c B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d) <->
   d2one_sem
     (fun tg a1 a2 a3 r => exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = tg /\
        beta (FOeval e c1) (FOeval e d1) j = a1 /\
        beta (FOeval e c2) (FOeval e d2) j = a2 /\
        beta (FOeval e c3) (FOeval e d3) j = a3 /\
        beta (FOeval e cr) (FOeval e dr) j = r)
     c (FOeval e d)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d Htb Hd.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb14 : tbl_below (B+14) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb38 : tbl_below (B+38) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb62 : tbl_below (B+62) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb108 : tbl_below (B+108) ct dt c1 d1 c2 d2 c3 d3 cr dr
                     len)
    by (unfold tbl_below; lia).
  assert (Htb154 : tbl_below (B+154) ct dt c1 d1 c2 d2 c3 d3 cr dr
                     len)
    by (unfold tbl_below; lia).
  assert (Hin0 : forall k, B <= k ->
      FOin_tm k (FOSucc c1) = false /\
      FOin_tm k (FOSucc cr) = false).
  { intros k Hk. split; apply FOin_tm_above; cbn; lia. }
  assert (Hg14 : FOmax_var_tm (FOVar B) < B+14) by (cbn; lia).
  assert (Hg38 : FOmax_var_tm (FOVar (B+2)) < B+38) by (cbn; lia).
  assert (Hz62 : FOmax_var_tm (FOVar (B+6)) < B+62) by (cbn; lia).
  assert (Hp62 : FOmax_var_tm (FOVar (B+8)) < B+62) by (cbn; lia).
  assert (Hz108 : FOmax_var_tm (FOVar B) < B+108) by (cbn; lia).
  assert (Hp108 : FOmax_var_tm (FOVar (B+10)) < B+108) by (cbn; lia).
  assert (Hz154 : FOmax_var_tm (FOVar (B+2)) < B+154) by (cbn; lia).
  assert (Hp154 : FOmax_var_tm (FOVar (B+12)) < B+154) by (cbn; lia).
  assert (Henv : Forall (fun t => FOmax_var_tm t < B+200)
                   [FOVar (B+8); FOVar (B+10); FOVar (B+12)])
    by (constructor; [cbn; lia |
        constructor; [cbn; lia |
        constructor; [cbn; lia | constructor]]]).
  assert (Hd200 : FOmax_var_tm d < B+200) by lia.
  unfold FOD2c, d2one_sem.
  rewrite (FOsat_FOBexC e B (FOSucc c1) _
             (proj1 (Hin0 B ltac:(lia)))
             (proj1 (Hin0 (S B) ltac:(lia)))).
  split.
  - intros [x [Hx Hb]].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc c1) _
               (proj1 (Hin0 (B+2) ltac:(lia)))
               (proj1 (Hin0 (S (B+2)) ltac:(lia)))) in Hb.
    destruct Hb as [y [Hy Hb]].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc c1) _
               (proj1 (Hin0 (B+4) ltac:(lia)))
               (proj1 (Hin0 (S (B+4)) ltac:(lia)))) in Hb.
    destruct Hb as [w1 [Hw1 Hb]].
    rewrite (FOsat_FOBexC _ (B+6) (FOSucc c1) _
               (proj1 (Hin0 (B+6) ltac:(lia)))
               (proj1 (Hin0 (S (B+6)) ltac:(lia)))) in Hb.
    destruct Hb as [ixy [Hixy Hb]].
    rewrite (FOsat_FOBexC _ (B+8) (FOSucc cr) _
               (proj2 (Hin0 (B+8) ltac:(lia)))
               (proj2 (Hin0 (S (B+8)) ltac:(lia)))) in Hb.
    destruct Hb as [pixy [Hpixy Hb]].
    rewrite (FOsat_FOBexC _ (B+10) (FOSucc cr) _
               (proj2 (Hin0 (B+10) ltac:(lia)))
               (proj2 (Hin0 (S (B+10)) ltac:(lia)))) in Hb.
    destruct Hb as [px [Hpx Hb]].
    rewrite (FOsat_FOBexC _ (B+12) (FOSucc cr) _
               (proj2 (Hin0 (B+12) ltac:(lia)))
               (proj2 (Hin0 (S (B+12)) ltac:(lia)))) in Hb.
    destruct Hb as [py [Hpy Hb]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb.
    destruct Hb as [Hcp1 Hb].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb.
    destruct Hb as [Hcp2 Hb].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb.
    destruct Hb as [HG1 Hb].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb.
    destruct Hb as [HG2 Hb].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb.
    destruct Hb as [Hpv1 Hb].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb.
    destruct Hb as [Hpv2 Hb].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb.
    destruct Hb as [Hpv3 Hpat].
    set (e7 := FOupdate (FOupdate (FOupdate (FOupdate (FOupdate
      (FOupdate (FOupdate e B x) (B+2) y) (B+4) w1) (B+6) ixy)
      (B+8) pixy) (B+10) px) (B+12) py) in *.
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e7 t = FOeval e t).
    { intros t Ht. unfold e7.
      rewrite (FOeval_update_above t _ (B+12) py ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+10) px ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+8) pixy ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+6) ixy ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+4) w1 ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) y ltac:(lia)).
      exact (FOeval_update_above t e B x Ht). }
    assert (Ee7B : e7 B = x).
    { unfold e7.
      rewrite (FOupdate_neq _ (B+12) py B) by lia.
      rewrite (FOupdate_neq _ (B+10) px B) by lia.
      rewrite (FOupdate_neq _ (B+8) pixy B) by lia.
      rewrite (FOupdate_neq _ (B+6) ixy B) by lia.
      rewrite (FOupdate_neq _ (B+4) w1 B) by lia.
      rewrite (FOupdate_neq _ (B+2) y B) by lia.
      apply FOupdate_eq. }
    assert (Ee7B2 : e7 (B+2) = y).
    { unfold e7.
      rewrite (FOupdate_neq _ (B+12) py (B+2)) by lia.
      rewrite (FOupdate_neq _ (B+10) px (B+2)) by lia.
      rewrite (FOupdate_neq _ (B+8) pixy (B+2)) by lia.
      rewrite (FOupdate_neq _ (B+6) ixy (B+2)) by lia.
      rewrite (FOupdate_neq _ (B+4) w1 (B+2)) by lia.
      apply FOupdate_eq. }
    assert (Ee7B4 : e7 (B+4) = w1).
    { unfold e7.
      rewrite (FOupdate_neq _ (B+12) py (B+4)) by lia.
      rewrite (FOupdate_neq _ (B+10) px (B+4)) by lia.
      rewrite (FOupdate_neq _ (B+8) pixy (B+4)) by lia.
      rewrite (FOupdate_neq _ (B+6) ixy (B+4)) by lia.
      apply FOupdate_eq. }
    assert (Ee7B6 : e7 (B+6) = ixy).
    { unfold e7.
      rewrite (FOupdate_neq _ (B+12) py (B+6)) by lia.
      rewrite (FOupdate_neq _ (B+10) px (B+6)) by lia.
      rewrite (FOupdate_neq _ (B+8) pixy (B+6)) by lia.
      apply FOupdate_eq. }
    assert (Ee7B8 : e7 (B+8) = pixy).
    { unfold e7.
      rewrite (FOupdate_neq _ (B+12) py (B+8)) by lia.
      rewrite (FOupdate_neq _ (B+10) px (B+8)) by lia.
      apply FOupdate_eq. }
    assert (Ee7B10 : e7 (B+10) = px).
    { unfold e7.
      rewrite (FOupdate_neq _ (B+12) py (B+10)) by lia.
      apply FOupdate_eq. }
    assert (Ee7B12 : e7 (B+12) = py).
    { unfold e7. apply FOupdate_eq. }
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp1.
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp2.
    cbn [FOeval] in Hcp1, Hcp2.
    rewrite Ee7B, Ee7B2, Ee7B4 in Hcp1.
    rewrite FOeval_numeral, Ee7B4, Ee7B6 in Hcp2.
    apply (proj1 (FOsat_FOGENF e7 (B+14) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOVar B) Htb14 Hg14)) in HG1.
    apply (proj1 (FOsat_FOGENF e7 (B+38) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOVar (B+2)) Htb38 Hg38)) in HG2.
    apply (proj1 (FOsat_FOPROVAT e7 (B+62) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len c (FOVar (B+6)) (FOVar (B+8))
                    Htb62 Hz62 Hp62)) in Hpv1.
    apply (proj1 (FOsat_FOPROVAT e7 (B+108) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len c (FOVar B) (FOVar (B+10))
                    Htb108 Hz108 Hp108)) in Hpv2.
    apply (proj1 (FOsat_FOPROVAT e7 (B+154) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len c (FOVar (B+2)) (FOVar (B+12))
                    Htb154 Hz154 Hp154)) in Hpv3.
    cbn [FOeval] in HG1, HG2, Hpv1, Hpv2, Hpv3.
    rewrite Ee7B in HG1.
    rewrite Ee7B2 in HG2.
    rewrite Ee7B6, Ee7B8 in Hpv1.
    rewrite Ee7B, Ee7B10 in Hpv2.
    rewrite Ee7B2, Ee7B12 in Hpv3.
    rewrite (Hstab len Hlen), (Hstab ct Hct), (Hstab dt Hdt),
      (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab c2 Hc2),
      (Hstab d2 Hd2'), (Hstab c3 Hc3), (Hstab d3 Hd3'),
      (Hstab cr Hcr), (Hstab dr Hdr) in HG1, HG2, Hpv1, Hpv2, Hpv3.
    apply (proj1 (FOsat_FOPATF cpatImpl012 e7 (B+200) _ d Henv
                    Hd200)) in Hpat.
    assert (Hsg : forall s,
        FOeval e7 (nth s [FOVar (B+8); FOVar (B+10); FOVar (B+12)]
                     FOZero)
        = (fun s => match s with
                    | 0 => pixy | 1 => px | 2 => py | _ => 0 end) s).
    { intro s. destruct s as [|[|[|s]]]; cbn.
      - exact Ee7B8.
      - exact Ee7B10.
      - exact Ee7B12.
      - destruct s; reflexivity. }
    rewrite (cpat_sem_ext _ _ _ Hsg) in Hpat.
    rewrite (Hstab d Hd) in Hpat.
    cbn [cpat_sem cpatImpl012 pImpP] in Hpat.
    exists x, y, pixy, px, py.
    rewrite <- Hcp2, <- Hcp1 in Hpv1.
    split; [exact HG1|]. split; [exact HG2|].
    split; [exact Hpv1|]. split; [exact Hpv2|].
    split; [exact Hpv3|].
    symmetry. exact Hpat.
  - intros [x [y [pixy [px [py [HG1 [HG2 [R1 [R2 [R3
      Hshape]]]]]]]]]].
    destruct (provat_arg_le e ct dt c1 d1 c2 d2 c3 d3 cr dr len
                c (cpair 2 (cpair x y)) pixy R1) as [HixyB HpixyB].
    destruct (provat_arg_le e ct dt c1 d1 c2 d2 c3 d3 cr dr len
                c x px R2) as [HxB HpxB].
    destruct (provat_arg_le e ct dt c1 d1 c2 d2 c3 d3 cr dr len
                c y py R3) as [HyB HpyB].
    pose proof (cpair_bound x y) as Hcbxy.
    pose proof (cpair_bound 2 (cpair x y)) as Hcb2.
    cbn [FOeval].
    exists x. split; [lia|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc c1) _
               (proj1 (Hin0 (B+2) ltac:(lia)))
               (proj1 (Hin0 (S (B+2)) ltac:(lia)))).
    exists y. split.
    { cbn [FOeval]. rewrite (FOeval_update_above c1 e B x Hc1).
      lia. }
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc c1) _
               (proj1 (Hin0 (B+4) ltac:(lia)))
               (proj1 (Hin0 (S (B+4)) ltac:(lia)))).
    exists (cpair x y). split.
    { cbn [FOeval].
      rewrite (FOeval_update_above c1 _ (B+2) y ltac:(lia)).
      rewrite (FOeval_update_above c1 e B x Hc1). lia. }
    rewrite (FOsat_FOBexC _ (B+6) (FOSucc c1) _
               (proj1 (Hin0 (B+6) ltac:(lia)))
               (proj1 (Hin0 (S (B+6)) ltac:(lia)))).
    exists (cpair 2 (cpair x y)). split.
    { cbn [FOeval].
      rewrite (FOeval_update_above c1 _ (B+4) (cpair x y)
                 ltac:(lia)).
      rewrite (FOeval_update_above c1 _ (B+2) y ltac:(lia)).
      rewrite (FOeval_update_above c1 e B x Hc1). lia. }
    rewrite (FOsat_FOBexC _ (B+8) (FOSucc cr) _
               (proj2 (Hin0 (B+8) ltac:(lia)))
               (proj2 (Hin0 (S (B+8)) ltac:(lia)))).
    exists pixy. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above cr _ (B+6)
                 (cpair 2 (cpair x y)) ltac:(lia)).
      rewrite (FOeval_update_above cr _ (B+4) (cpair x y)
                 ltac:(lia)).
      rewrite (FOeval_update_above cr _ (B+2) y ltac:(lia)).
      rewrite (FOeval_update_above cr e B x Hcr). lia. }
    rewrite (FOsat_FOBexC _ (B+10) (FOSucc cr) _
               (proj2 (Hin0 (B+10) ltac:(lia)))
               (proj2 (Hin0 (S (B+10)) ltac:(lia)))).
    exists px. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above cr _ (B+8) pixy ltac:(lia)).
      rewrite (FOeval_update_above cr _ (B+6)
                 (cpair 2 (cpair x y)) ltac:(lia)).
      rewrite (FOeval_update_above cr _ (B+4) (cpair x y)
                 ltac:(lia)).
      rewrite (FOeval_update_above cr _ (B+2) y ltac:(lia)).
      rewrite (FOeval_update_above cr e B x Hcr). lia. }
    rewrite (FOsat_FOBexC _ (B+12) (FOSucc cr) _
               (proj2 (Hin0 (B+12) ltac:(lia)))
               (proj2 (Hin0 (S (B+12)) ltac:(lia)))).
    exists py. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above cr _ (B+10) px ltac:(lia)).
      rewrite (FOeval_update_above cr _ (B+8) pixy ltac:(lia)).
      rewrite (FOeval_update_above cr _ (B+6)
                 (cpair 2 (cpair x y)) ltac:(lia)).
      rewrite (FOeval_update_above cr _ (B+4) (cpair x y)
                 ltac:(lia)).
      rewrite (FOeval_update_above cr _ (B+2) y ltac:(lia)).
      rewrite (FOeval_update_above cr e B x Hcr). lia. }
    set (e7 := FOupdate (FOupdate (FOupdate (FOupdate (FOupdate
      (FOupdate (FOupdate e B x) (B+2) y) (B+4) (cpair x y))
      (B+6) (cpair 2 (cpair x y))) (B+8) pixy) (B+10) px)
      (B+12) py).
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e7 t = FOeval e t).
    { intros t Ht. unfold e7.
      rewrite (FOeval_update_above t _ (B+12) py ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+10) px ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+8) pixy ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+6)
                 (cpair 2 (cpair x y)) ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+4) (cpair x y)
                 ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) y ltac:(lia)).
      exact (FOeval_update_above t e B x Ht). }
    assert (Ee7B : e7 B = x).
    { unfold e7.
      rewrite (FOupdate_neq _ (B+12) py B) by lia.
      rewrite (FOupdate_neq _ (B+10) px B) by lia.
      rewrite (FOupdate_neq _ (B+8) pixy B) by lia.
      rewrite (FOupdate_neq _ (B+6) (cpair 2 (cpair x y)) B)
        by lia.
      rewrite (FOupdate_neq _ (B+4) (cpair x y) B) by lia.
      rewrite (FOupdate_neq _ (B+2) y B) by lia.
      apply FOupdate_eq. }
    assert (Ee7B2 : e7 (B+2) = y).
    { unfold e7.
      rewrite (FOupdate_neq _ (B+12) py (B+2)) by lia.
      rewrite (FOupdate_neq _ (B+10) px (B+2)) by lia.
      rewrite (FOupdate_neq _ (B+8) pixy (B+2)) by lia.
      rewrite (FOupdate_neq _ (B+6) (cpair 2 (cpair x y)) (B+2))
        by lia.
      rewrite (FOupdate_neq _ (B+4) (cpair x y) (B+2)) by lia.
      apply FOupdate_eq. }
    assert (Ee7B4 : e7 (B+4) = cpair x y).
    { unfold e7.
      rewrite (FOupdate_neq _ (B+12) py (B+4)) by lia.
      rewrite (FOupdate_neq _ (B+10) px (B+4)) by lia.
      rewrite (FOupdate_neq _ (B+8) pixy (B+4)) by lia.
      rewrite (FOupdate_neq _ (B+6) (cpair 2 (cpair x y)) (B+4))
        by lia.
      apply FOupdate_eq. }
    assert (Ee7B6 : e7 (B+6) = cpair 2 (cpair x y)).
    { unfold e7.
      rewrite (FOupdate_neq _ (B+12) py (B+6)) by lia.
      rewrite (FOupdate_neq _ (B+10) px (B+6)) by lia.
      rewrite (FOupdate_neq _ (B+8) pixy (B+6)) by lia.
      apply FOupdate_eq. }
    assert (Ee7B8 : e7 (B+8) = pixy).
    { unfold e7.
      rewrite (FOupdate_neq _ (B+12) py (B+8)) by lia.
      rewrite (FOupdate_neq _ (B+10) px (B+8)) by lia.
      apply FOupdate_eq. }
    assert (Ee7B10 : e7 (B+10) = px).
    { unfold e7.
      rewrite (FOupdate_neq _ (B+12) py (B+10)) by lia.
      apply FOupdate_eq. }
    assert (Ee7B12 : e7 (B+12) = py).
    { unfold e7. apply FOupdate_eq. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      cbn [FOeval]. rewrite Ee7B, Ee7B2, Ee7B4. reflexivity. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF _ _ _ _)).
      cbn [FOeval].
      rewrite FOeval_numeral, Ee7B4, Ee7B6. reflexivity. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOGENF e7 (B+14) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOVar B) Htb14 Hg14)).
      cbn [FOeval]. rewrite Ee7B.
      rewrite (Hstab len Hlen), (Hstab ct Hct), (Hstab dt Hdt),
        (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab c2 Hc2),
        (Hstab d2 Hd2'), (Hstab c3 Hc3), (Hstab d3 Hd3'),
        (Hstab cr Hcr), (Hstab dr Hdr).
      exact HG1. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOGENF e7 (B+38) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOVar (B+2)) Htb38 Hg38)).
      cbn [FOeval]. rewrite Ee7B2.
      rewrite (Hstab len Hlen), (Hstab ct Hct), (Hstab dt Hdt),
        (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab c2 Hc2),
        (Hstab d2 Hd2'), (Hstab c3 Hc3), (Hstab d3 Hd3'),
        (Hstab cr Hcr), (Hstab dr Hdr).
      exact HG2. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOPROVAT e7 (B+62) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len c (FOVar (B+6)) (FOVar (B+8))
                      Htb62 Hz62 Hp62)).
      cbn [FOeval]. rewrite Ee7B6, Ee7B8.
      rewrite (Hstab len Hlen), (Hstab ct Hct), (Hstab dt Hdt),
        (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab c2 Hc2),
        (Hstab d2 Hd2'), (Hstab c3 Hc3), (Hstab d3 Hd3'),
        (Hstab cr Hcr), (Hstab dr Hdr).
      exact R1. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOPROVAT e7 (B+108) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len c (FOVar B) (FOVar (B+10))
                      Htb108 Hz108 Hp108)).
      cbn [FOeval]. rewrite Ee7B, Ee7B10.
      rewrite (Hstab len Hlen), (Hstab ct Hct), (Hstab dt Hdt),
        (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab c2 Hc2),
        (Hstab d2 Hd2'), (Hstab c3 Hc3), (Hstab d3 Hd3'),
        (Hstab cr Hcr), (Hstab dr Hdr).
      exact R2. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOPROVAT e7 (B+154) ct dt c1 d1 c2 d2 c3
                      d3 cr dr len c (FOVar (B+2)) (FOVar (B+12))
                      Htb154 Hz154 Hp154)).
      cbn [FOeval]. rewrite Ee7B2, Ee7B12.
      rewrite (Hstab len Hlen), (Hstab ct Hct), (Hstab dt Hdt),
        (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab c2 Hc2),
        (Hstab d2 Hd2'), (Hstab c3 Hc3), (Hstab d3 Hd3'),
        (Hstab cr Hcr), (Hstab dr Hdr).
      exact R3. }
    apply (proj2 (FOsat_FOPATF cpatImpl012 e7 (B+200) _ d Henv
                    Hd200)).
    assert (Hsg : forall s,
        FOeval e7 (nth s [FOVar (B+8); FOVar (B+10); FOVar (B+12)]
                     FOZero)
        = (fun s => match s with
                    | 0 => pixy | 1 => px | 2 => py | _ => 0 end) s).
    { intro s. destruct s as [|[|[|s]]]; cbn.
      - exact Ee7B8.
      - exact Ee7B10.
      - exact Ee7B12.
      - destruct s; reflexivity. }
    rewrite (cpat_sem_ext _ _ _ Hsg).
    rewrite (Hstab d Hd).
    cbn [cpat_sem cpatImpl012 pImpP].
    symmetry. exact Hshape.
Qed.

Lemma FOsat_FODMONc : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    c c' d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  (FOsat e (FODMONc B ct dt c1 d1 c2 d2 c3 d3 cr dr len c c' d) <->
   dmonone_sem
     (fun tg a1 a2 a3 r => exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = tg /\
        beta (FOeval e c1) (FOeval e d1) j = a1 /\
        beta (FOeval e c2) (FOeval e d2) j = a2 /\
        beta (FOeval e c3) (FOeval e d3) j = a3 /\
        beta (FOeval e cr) (FOeval e dr) j = r)
     c c' (FOeval e d)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len c c' d Htb Hd.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb6 : tbl_below (B+6) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb30 : tbl_below (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb76 : tbl_below (B+76) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (HinB : FOin_tm B (FOSucc c1) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB : FOin_tm (S B) (FOSucc c1) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB2 : FOin_tm (B+2) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB2 : FOin_tm (S (B+2)) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB4 : FOin_tm (B+4) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB4 : FOin_tm (S (B+4)) (FOSucc cr) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (Hg6 : FOmax_var_tm (FOVar B) < B+6) by (cbn; lia).
  assert (Hz30 : FOmax_var_tm (FOVar B) < B+30) by (cbn; lia).
  assert (Hp30 : FOmax_var_tm (FOVar (B+2)) < B+30) by (cbn; lia).
  assert (Hz76 : FOmax_var_tm (FOVar B) < B+76) by (cbn; lia).
  assert (Hp76 : FOmax_var_tm (FOVar (B+4)) < B+76) by (cbn; lia).
  assert (Henv : Forall (fun t => FOmax_var_tm t < B+122)
                   [FOVar (B+2); FOVar (B+4)])
    by (constructor; [cbn; lia |
        constructor; [cbn; lia | constructor]]).
  assert (Hd122 : FOmax_var_tm d < B+122) by lia.
  unfold FODMONc, dmonone_sem.
  rewrite (FOsat_FOBexC e B (FOSucc c1) _ HinB HinSB).
  split.
  - intros [a [Ha Hb]].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc cr) _ HinB2 HinSB2) in Hb.
    destruct Hb as [p [Hp Hb2]].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc cr) _ HinB4 HinSB4) in Hb2.
    destruct Hb2 as [p' [Hp' Hb3]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb3.
    destruct Hb3 as [HG Hb4].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb4.
    destruct Hb4 as [Hpv1 Hb5].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb5.
    destruct Hb5 as [Hpv2 Hpat].
    set (e3 := FOupdate (FOupdate (FOupdate e B a) (B+2) p)
                 (B+4) p') in *.
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e3 t = FOeval e t).
    { intros t Ht. unfold e3.
      rewrite (FOeval_update_above t _ (B+4) p' ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) p ltac:(lia)).
      exact (FOeval_update_above t e B a Ht). }
    assert (Ee3B : e3 B = a).
    { unfold e3.
      rewrite (FOupdate_neq _ (B+4) p' B) by lia.
      rewrite (FOupdate_neq _ (B+2) p B) by lia.
      apply FOupdate_eq. }
    assert (Ee3B2 : e3 (B+2) = p).
    { unfold e3.
      rewrite (FOupdate_neq _ (B+4) p' (B+2)) by lia.
      apply FOupdate_eq. }
    assert (Ee3B4 : e3 (B+4) = p').
    { unfold e3. apply FOupdate_eq. }
    apply (proj1 (FOsat_FOGENF e3 (B+6) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOVar B) Htb6 Hg6)) in HG.
    apply (proj1 (FOsat_FOPROVAT e3 (B+30) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len c (FOVar B) (FOVar (B+2))
                    Htb30 Hz30 Hp30)) in Hpv1.
    apply (proj1 (FOsat_FOPROVAT e3 (B+76) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len c' (FOVar B) (FOVar (B+4))
                    Htb76 Hz76 Hp76)) in Hpv2.
    cbn [FOeval] in HG, Hpv1, Hpv2.
    rewrite Ee3B in HG.
    rewrite Ee3B, Ee3B2 in Hpv1.
    rewrite Ee3B, Ee3B4 in Hpv2.
    rewrite (Hstab len Hlen), (Hstab ct Hct), (Hstab dt Hdt),
      (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab c2 Hc2),
      (Hstab d2 Hd2'), (Hstab c3 Hc3), (Hstab d3 Hd3'),
      (Hstab cr Hcr), (Hstab dr Hdr) in HG, Hpv1, Hpv2.
    apply (proj1 (FOsat_FOPATF cpatImpl01 e3 (B+122) _ d Henv
                    Hd122)) in Hpat.
    assert (Hsg : forall s,
        FOeval e3 (nth s [FOVar (B+2); FOVar (B+4)] FOZero)
        = (fun s => match s with
                    | 0 => p | 1 => p' | _ => 0 end) s).
    { intro s. destruct s as [|[|s]]; cbn.
      - exact Ee3B2.
      - exact Ee3B4.
      - destruct s; reflexivity. }
    rewrite (cpat_sem_ext _ _ _ Hsg) in Hpat.
    rewrite (Hstab d Hd) in Hpat.
    cbn [cpat_sem cpatImpl01 pImpP] in Hpat.
    exists a, p, p'.
    split; [exact HG|].
    split; [exact Hpv1|]. split; [exact Hpv2|].
    symmetry. exact Hpat.
  - intros [a [p [p' [HG [R1 [R2 Hshape]]]]]].
    destruct (provat_arg_le e ct dt c1 d1 c2 d2 c3 d3 cr dr len
                c a p R1) as [HaB HpB].
    destruct (provat_arg_le e ct dt c1 d1 c2 d2 c3 d3 cr dr len
                c' a p' R2) as [_ Hp'B].
    cbn [FOeval].
    exists a. split; [lia|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc cr) _ HinB2 HinSB2).
    exists p. split.
    { cbn [FOeval]. rewrite (FOeval_update_above cr e B a Hcr).
      lia. }
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc cr) _ HinB4 HinSB4).
    exists p'. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above cr _ (B+2) p ltac:(lia)).
      rewrite (FOeval_update_above cr e B a Hcr). lia. }
    set (e3 := FOupdate (FOupdate (FOupdate e B a) (B+2) p)
                 (B+4) p').
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e3 t = FOeval e t).
    { intros t Ht. unfold e3.
      rewrite (FOeval_update_above t _ (B+4) p' ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) p ltac:(lia)).
      exact (FOeval_update_above t e B a Ht). }
    assert (Ee3B : e3 B = a).
    { unfold e3.
      rewrite (FOupdate_neq _ (B+4) p' B) by lia.
      rewrite (FOupdate_neq _ (B+2) p B) by lia.
      apply FOupdate_eq. }
    assert (Ee3B2 : e3 (B+2) = p).
    { unfold e3.
      rewrite (FOupdate_neq _ (B+4) p' (B+2)) by lia.
      apply FOupdate_eq. }
    assert (Ee3B4 : e3 (B+4) = p').
    { unfold e3. apply FOupdate_eq. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOGENF e3 (B+6) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOVar B) Htb6 Hg6)).
      cbn [FOeval]. rewrite Ee3B.
      rewrite (Hstab len Hlen), (Hstab ct Hct), (Hstab dt Hdt),
        (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab c2 Hc2),
        (Hstab d2 Hd2'), (Hstab c3 Hc3), (Hstab d3 Hd3'),
        (Hstab cr Hcr), (Hstab dr Hdr).
      exact HG. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOPROVAT e3 (B+30) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len c (FOVar B) (FOVar (B+2))
                      Htb30 Hz30 Hp30)).
      cbn [FOeval]. rewrite Ee3B, Ee3B2.
      rewrite (Hstab len Hlen), (Hstab ct Hct), (Hstab dt Hdt),
        (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab c2 Hc2),
        (Hstab d2 Hd2'), (Hstab c3 Hc3), (Hstab d3 Hd3'),
        (Hstab cr Hcr), (Hstab dr Hdr).
      exact R1. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOPROVAT e3 (B+76) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len c' (FOVar B) (FOVar (B+4))
                      Htb76 Hz76 Hp76)).
      cbn [FOeval]. rewrite Ee3B, Ee3B4.
      rewrite (Hstab len Hlen), (Hstab ct Hct), (Hstab dt Hdt),
        (Hstab c1 Hc1), (Hstab d1 Hd1'), (Hstab c2 Hc2),
        (Hstab d2 Hd2'), (Hstab c3 Hc3), (Hstab d3 Hd3'),
        (Hstab cr Hcr), (Hstab dr Hdr).
      exact R2. }
    apply (proj2 (FOsat_FOPATF cpatImpl01 e3 (B+122) _ d Henv
                    Hd122)).
    assert (Hsg : forall s,
        FOeval e3 (nth s [FOVar (B+2); FOVar (B+4)] FOZero)
        = (fun s => match s with
                    | 0 => p | 1 => p' | _ => 0 end) s).
    { intro s. destruct s as [|[|s]]; cbn.
      - exact Ee3B2.
      - exact Ee3B4.
      - destruct s; reflexivity. }
    rewrite (cpat_sem_ext _ _ _ Hsg).
    rewrite (Hstab d Hd).
    cbn [cpat_sem cpatImpl01 pImpP].
    symmetry. exact Hshape.
Qed.

Lemma FOsat_FOD2Sc : forall cores e B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  (FOsat e (FOD2Sc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) <->
   d2s_sem
     (fun tg a1 a2 a3 r => exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = tg /\
        beta (FOeval e c1) (FOeval e d1) j = a1 /\
        beta (FOeval e c2) (FOeval e d2) j = a2 /\
        beta (FOeval e c3) (FOeval e d3) j = a3 /\
        beta (FOeval e cr) (FOeval e dr) j = r)
     cores (FOeval e d)).
Proof.
  induction cores as [|c rest IH];
    intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len d Htb Hd;
    cbn [FOD2Sc d2s_sem].
  - cbn. tauto.
  - rewrite FOsat_FOOr.
    rewrite (FOsat_FOD2c e B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d
               Htb Hd).
    rewrite (IH e B ct dt c1 d1 c2 d2 c3 d3 cr dr len d Htb Hd).
    reflexivity.
Qed.

Lemma FOsat_FOD3Sc : forall cores e B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  (FOsat e (FOD3Sc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) <->
   d3s_sem
     (fun tg a1 a2 a3 r => exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = tg /\
        beta (FOeval e c1) (FOeval e d1) j = a1 /\
        beta (FOeval e c2) (FOeval e d2) j = a2 /\
        beta (FOeval e c3) (FOeval e d3) j = a3 /\
        beta (FOeval e cr) (FOeval e dr) j = r)
     cores (FOeval e d)).
Proof.
  induction cores as [|c rest IH];
    intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len d Htb Hd;
    cbn [FOD3Sc d3s_sem].
  - cbn. tauto.
  - rewrite FOsat_FOOr.
    rewrite (FOsat_FOD3c e B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d
               Htb Hd).
    rewrite (IH e B ct dt c1 d1 c2 d2 c3 d3 cr dr len d Htb Hd).
    reflexivity.
Qed.

Lemma FOsat_FODMONS1 : forall cs e B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len c d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  (FOsat e (FODMONS1 B ct dt c1 d1 c2 d2 c3 d3 cr dr len c cs d) <->
   dmons1_sem
     (fun tg a1 a2 a3 r => exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = tg /\
        beta (FOeval e c1) (FOeval e d1) j = a1 /\
        beta (FOeval e c2) (FOeval e d2) j = a2 /\
        beta (FOeval e c3) (FOeval e d3) j = a3 /\
        beta (FOeval e cr) (FOeval e dr) j = r)
     c cs (FOeval e d)).
Proof.
  induction cs as [|c' rest IH];
    intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d Htb Hd;
    cbn [FODMONS1 dmons1_sem].
  - cbn. tauto.
  - rewrite FOsat_FOOr.
    rewrite (FOsat_FODMONc e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
               c c' d Htb Hd).
    rewrite (IH e B ct dt c1 d1 c2 d2 c3 d3 cr dr len c d Htb Hd).
    reflexivity.
Qed.

Lemma FOsat_FODMONSc : forall cores e B ct dt c1 d1 c2 d2 c3 d3 cr dr
    len d,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm d < B ->
  (FOsat e (FODMONSc B ct dt c1 d1 c2 d2 c3 d3 cr dr len cores d) <->
   dmons_sem
     (fun tg a1 a2 a3 r => exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = tg /\
        beta (FOeval e c1) (FOeval e d1) j = a1 /\
        beta (FOeval e c2) (FOeval e d2) j = a2 /\
        beta (FOeval e c3) (FOeval e d3) j = a3 /\
        beta (FOeval e cr) (FOeval e dr) j = r)
     cores (FOeval e d)).
Proof.
  induction cores as [|c rest IH];
    intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len d Htb Hd;
    cbn [FODMONSc dmons_sem].
  - cbn. tauto.
  - rewrite FOsat_FOOr.
    rewrite (FOsat_FODMONS1 (c :: rest) e B ct dt c1 d1 c2 d2 c3 d3
               cr dr len c d Htb Hd).
    rewrite (IH e B ct dt c1 d1 c2 d2 c3 d3 cr dr len d Htb Hd).
    reflexivity.
Qed.

Lemma FOsat_FOJSUBST : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len
    pat vd pl,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm vd < B -> FOmax_var_tm pl < B ->
  cpat_occurs 1 pat = true -> cpat_occurs 2 pat = true ->
  (FOsat e (FOJSUBST B ct dt c1 d1 c2 d2 c3 d3 cr dr len pat vd pl)
   <->
   exists x tc P Q,
     cpair x tc = FOeval e pl /\
     cpat_sem (fun s => match s with
                        | 0 => x | 1 => P | 2 => Q | _ => 0 end) pat
       = FOeval e vd /\
     (exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = 4 /\
        beta (FOeval e c1) (FOeval e d1) j = x /\
        beta (FOeval e c2) (FOeval e d2) j = tc /\
        beta (FOeval e c3) (FOeval e d3) j = P /\
        beta (FOeval e cr) (FOeval e dr) j = 1) /\
     (exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = 3 /\
        beta (FOeval e c1) (FOeval e d1) j = x /\
        beta (FOeval e c2) (FOeval e d2) j = tc /\
        beta (FOeval e c3) (FOeval e d3) j = P /\
        beta (FOeval e cr) (FOeval e dr) j = Q)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len pat vd pl Htb Hvd Hpl
    Hoc1 Hoc2.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb30 : tbl_below (B+30) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb52 : tbl_below (B+52) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (HinB : FOin_tm B (FOSucc pl) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB : FOin_tm (S B) (FOSucc pl) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB2 : FOin_tm (B+2) (FOSucc pl) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB2 : FOin_tm (S (B+2)) (FOSucc pl) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB4 : FOin_tm (B+4) (FOSucc vd) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB4 : FOin_tm (S (B+4)) (FOSucc vd) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB6 : FOin_tm (B+6) (FOSucc vd) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB6 : FOin_tm (S (B+6)) (FOSucc vd) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (Henv : Forall (fun t => FOmax_var_tm t < B+8)
                   [FOVar B; FOVar (B+4); FOVar (B+6)])
    by (constructor; [cbn; lia |
        constructor; [cbn; lia |
        constructor; [cbn; lia | constructor]]]).
  assert (Hvd8 : FOmax_var_tm vd < B+8) by lia.
  assert (H4m : FOmax_var_tm (FOnumeral 4) < B+30)
    by (rewrite FOmax_var_numeral; lia).
  assert (H3m : FOmax_var_tm (FOnumeral 3) < B+52)
    by (rewrite FOmax_var_numeral; lia).
  assert (H1m : FOmax_var_tm (FOnumeral 1) < B+30)
    by (rewrite FOmax_var_numeral; lia).
  assert (HvB30 : FOmax_var_tm (FOVar B) < B+30) by (cbn; lia).
  assert (HvB230 : FOmax_var_tm (FOVar (B+2)) < B+30) by (cbn; lia).
  assert (HvB430 : FOmax_var_tm (FOVar (B+4)) < B+30) by (cbn; lia).
  assert (HvB52 : FOmax_var_tm (FOVar B) < B+52) by (cbn; lia).
  assert (HvB252 : FOmax_var_tm (FOVar (B+2)) < B+52) by (cbn; lia).
  assert (HvB452 : FOmax_var_tm (FOVar (B+4)) < B+52) by (cbn; lia).
  assert (HvB652 : FOmax_var_tm (FOVar (B+6)) < B+52) by (cbn; lia).
  unfold FOJSUBST.
  rewrite (FOsat_FOBexC e B (FOSucc pl) _ HinB HinSB).
  split.
  - intros [x [Hx Hb1]].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc pl) _ HinB2 HinSB2) in Hb1.
    destruct Hb1 as [tc [Htc Hb2]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb2.
    destruct Hb2 as [Hcp Hb3].
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc vd) _ HinB4 HinSB4) in Hb3.
    destruct Hb3 as [P [HP Hb4]].
    rewrite (FOsat_FOBexC _ (B+6) (FOSucc vd) _ HinB6 HinSB6) in Hb4.
    destruct Hb4 as [Q [HQ Hb5]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb5.
    destruct Hb5 as [Hpat Hb6].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb6.
    destruct Hb6 as [Hlk1 Hlk2].
    set (e2 := FOupdate (FOupdate e B x) (B+2) tc) in *.
    set (e4 := FOupdate (FOupdate e2 (B+4) P) (B+6) Q) in *.
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e4 t = FOeval e t).
    { intros t Ht. unfold e4, e2.
      rewrite (FOeval_update_above t _ (B+6) Q ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+4) P ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) tc ltac:(lia)).
      exact (FOeval_update_above t e B x Ht). }
    assert (EvB : e4 B = x).
    { unfold e4, e2.
      rewrite (FOupdate_neq _ (B+6) Q B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+4) P B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+2) tc B ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB2 : e4 (B+2) = tc).
    { unfold e4, e2.
      rewrite (FOupdate_neq _ (B+6) Q (B+2) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+4) P (B+2) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB4 : e4 (B+4) = P).
    { unfold e4.
      rewrite (FOupdate_neq _ (B+6) Q (B+4) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB6 : e4 (B+6) = Q).
    { unfold e4. apply FOupdate_eq. }
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp.
    cbn [FOeval] in Hcp.
    unfold e2 in Hcp.
    rewrite (FOupdate_eq _ _ _) in Hcp.
    rewrite (FOupdate_neq _ (B+2) tc B ltac:(lia)) in Hcp.
    rewrite (FOupdate_eq _ _ _) in Hcp.
    rewrite (FOeval_update_above pl _ (B+2) tc ltac:(lia)) in Hcp.
    rewrite (FOeval_update_above pl e B x Hpl) in Hcp.
    apply (proj1 (FOsat_FOPATF pat _ (B+8) _ vd Henv Hvd8)) in Hpat.
    assert (Hsg : forall s,
        FOeval e4 (nth s [FOVar B; FOVar (B+4); FOVar (B+6)] FOZero)
        = (fun s => match s with
                    | 0 => x | 1 => P | 2 => Q | _ => 0 end) s).
    { intro s. destruct s as [|[|[|s]]]; cbn [nth FOeval].
      - exact EvB.
      - exact EvB4.
      - exact EvB6.
      - destruct s; reflexivity. }
    rewrite (cpat_sem_ext _ _ _ Hsg) in Hpat.
    rewrite (Hstab vd Hvd) in Hpat.
    apply (proj1 (FOsat_FOlookup e4 (B+30) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 4) (FOVar B) (FOVar (B+2))
                    (FOVar (B+4)) (FOnumeral 1)
                    Htb30 H4m HvB30 HvB230 HvB430 H1m)) in Hlk1.
    destruct Hlk1 as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
    rewrite (Hstab len Hlen) in Hj.
    rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral in Hf1.
    cbn [FOeval] in Hf2, Hf3, Hf4.
    rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), EvB in Hf2.
    rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), EvB2 in Hf3.
    rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), EvB4 in Hf4.
    rewrite (Hstab cr Hcr), (Hstab dr Hdr), FOeval_numeral in Hf5.
    apply (proj1 (FOsat_FOlookup e4 (B+52) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 3) (FOVar B) (FOVar (B+2))
                    (FOVar (B+4)) (FOVar (B+6))
                    Htb52 H3m HvB52 HvB252 HvB452 HvB652)) in Hlk2.
    destruct Hlk2 as [j2 [Hj2 [Hg1 [Hg2 [Hg3 [Hg4 Hg5]]]]]].
    rewrite (Hstab len Hlen) in Hj2.
    rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral in Hg1.
    cbn [FOeval] in Hg2, Hg3, Hg4, Hg5.
    rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), EvB in Hg2.
    rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), EvB2 in Hg3.
    rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), EvB4 in Hg4.
    rewrite (Hstab cr Hcr), (Hstab dr Hdr), EvB6 in Hg5.
    exists x, tc, P, Q.
    split; [exact Hcp|].
    split; [exact Hpat|].
    split.
    { exists j. repeat split; assumption. }
    exists j2. repeat split; assumption.
  - intros [x [tc [P [Q [Hcp [Hpat [Hlk1 Hlk2]]]]]]].
    pose proof (cpair_bound x tc) as Hxb.
    pose proof (cpat_occurs_le pat
      (fun s => match s with
                | 0 => x | 1 => P | 2 => Q | _ => 0 end) 1 Hoc1)
      as HPb.
    pose proof (cpat_occurs_le pat
      (fun s => match s with
                | 0 => x | 1 => P | 2 => Q | _ => 0 end) 2 Hoc2)
      as HQb.
    cbn [FOeval].
    exists x. split; [lia|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc pl) _ HinB2 HinSB2).
    exists tc. split.
    { cbn [FOeval].
      rewrite (FOeval_update_above pl e B x Hpl). lia. }
    set (e2 := FOupdate (FOupdate e B x) (B+2) tc).
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF e2 _ _ _)).
      cbn [FOeval].
      unfold e2.
      rewrite (FOupdate_eq _ _ _).
      rewrite (FOupdate_neq _ (B+2) tc B ltac:(lia)).
      rewrite (FOupdate_eq _ _ _).
      rewrite (FOeval_update_above pl _ (B+2) tc ltac:(lia)).
      rewrite (FOeval_update_above pl e B x Hpl).
      exact Hcp. }
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc vd) _ HinB4 HinSB4).
    exists P. split.
    { cbn [FOeval].
      unfold e2.
      rewrite (FOeval_update_above vd _ (B+2) tc ltac:(lia)).
      rewrite (FOeval_update_above vd e B x Hvd). lia. }
    rewrite (FOsat_FOBexC _ (B+6) (FOSucc vd) _ HinB6 HinSB6).
    exists Q. split.
    { cbn [FOeval].
      unfold e2.
      rewrite (FOeval_update_above vd _ (B+4) P ltac:(lia)).
      rewrite (FOeval_update_above vd _ (B+2) tc ltac:(lia)).
      rewrite (FOeval_update_above vd e B x Hvd). lia. }
    set (e4 := FOupdate (FOupdate e2 (B+4) P) (B+6) Q).
    assert (Hstab : forall t, FOmax_var_tm t < B ->
        FOeval e4 t = FOeval e t).
    { intros t Ht. unfold e4, e2.
      rewrite (FOeval_update_above t _ (B+6) Q ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+4) P ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) tc ltac:(lia)).
      exact (FOeval_update_above t e B x Ht). }
    assert (EvB : e4 B = x).
    { unfold e4, e2.
      rewrite (FOupdate_neq _ (B+6) Q B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+4) P B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+2) tc B ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB2 : e4 (B+2) = tc).
    { unfold e4, e2.
      rewrite (FOupdate_neq _ (B+6) Q (B+2) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+4) P (B+2) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB4 : e4 (B+4) = P).
    { unfold e4.
      rewrite (FOupdate_neq _ (B+6) Q (B+4) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB6 : e4 (B+6) = Q).
    { unfold e4. apply FOupdate_eq. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOPATF pat e4 (B+8) _ vd Henv Hvd8)).
      assert (Hsg : forall s,
          FOeval e4 (nth s [FOVar B; FOVar (B+4); FOVar (B+6)] FOZero)
          = (fun s => match s with
                      | 0 => x | 1 => P | 2 => Q | _ => 0 end) s).
      { intro s. destruct s as [|[|[|s]]]; cbn [nth FOeval].
        - exact EvB.
        - exact EvB4.
        - exact EvB6.
        - destruct s; reflexivity. }
      rewrite (cpat_sem_ext _ _ _ Hsg).
      rewrite (Hstab vd Hvd).
      exact Hpat. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOlookup e4 (B+30) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOnumeral 4) (FOVar B) (FOVar (B+2))
                      (FOVar (B+4)) (FOnumeral 1)
                      Htb30 H4m HvB30 HvB230 HvB430 H1m)).
      destruct Hlk1 as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
      exists j.
      split; [rewrite (Hstab len Hlen); exact Hj|].
      split.
      { rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral.
        exact Hf1. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), EvB. exact Hf2. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), EvB2. exact Hf3. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), EvB4. exact Hf4. }
      rewrite (Hstab cr Hcr), (Hstab dr Hdr), FOeval_numeral.
      exact Hf5. }
    apply (proj2 (FOsat_FOlookup e4 (B+52) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 3) (FOVar B) (FOVar (B+2))
                    (FOVar (B+4)) (FOVar (B+6))
                    Htb52 H3m HvB52 HvB252 HvB452 HvB652)).
    destruct Hlk2 as [j [Hj [Hf1 [Hf2 [Hf3 [Hf4 Hf5]]]]]].
    exists j.
    split; [rewrite (Hstab len Hlen); exact Hj|].
    split.
    { rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral.
      exact Hf1. }
    split.
    { cbn [FOeval].
      rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), EvB. exact Hf2. }
    split.
    { cbn [FOeval].
      rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), EvB2. exact Hf3. }
    split.
    { cbn [FOeval].
      rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), EvB4. exact Hf4. }
    cbn [FOeval].
    rewrite (Hstab cr Hcr), (Hstab dr Hdr), EvB6. exact Hf5.
Qed.

Lemma cpair_le_sq : forall a b, cpair a b <= (a + b + 1) * (a + b + 1).
Proof.
  intros a b. unfold cpair.
  pose proof (triangle_double (a + b)) as Ht. nia.
Qed.

Lemma FOsat_FOJIND : forall e B ct dt c1 d1 c2 d2 c3 d3 cr dr len vd pl,
  tbl_below B ct dt c1 d1 c2 d2 c3 d3 cr dr len ->
  FOmax_var_tm vd < B -> FOmax_var_tm pl < B ->
  (FOsat e (FOJIND B ct dt c1 d1 c2 d2 c3 d3 cr dr len vd pl)
   <->
   exists x PA C0 SS,
     cpair x PA = FOeval e pl /\
     cpat_sem (fun s => match s with
                        | 0 => x | 1 => PA | 2 => C0 | 3 => SS | _ => 0 end)
       cpatInd = FOeval e vd /\
     (exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = 4 /\
        beta (FOeval e c1) (FOeval e d1) j = x /\
        beta (FOeval e c2) (FOeval e d2) j = cpair 1 0 /\
        beta (FOeval e c3) (FOeval e d3) j = PA /\
        beta (FOeval e cr) (FOeval e dr) j = 1) /\
     (exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = 3 /\
        beta (FOeval e c1) (FOeval e d1) j = x /\
        beta (FOeval e c2) (FOeval e d2) j = cpair 1 0 /\
        beta (FOeval e c3) (FOeval e d3) j = PA /\
        beta (FOeval e cr) (FOeval e dr) j = C0) /\
     (exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = 4 /\
        beta (FOeval e c1) (FOeval e d1) j = x /\
        beta (FOeval e c2) (FOeval e d2) j = cpair 2 (cpair 0 x) /\
        beta (FOeval e c3) (FOeval e d3) j = PA /\
        beta (FOeval e cr) (FOeval e dr) j = 1) /\
     (exists j, j < FOeval e len /\
        beta (FOeval e ct) (FOeval e dt) j = 3 /\
        beta (FOeval e c1) (FOeval e d1) j = x /\
        beta (FOeval e c2) (FOeval e d2) j = cpair 2 (cpair 0 x) /\
        beta (FOeval e c3) (FOeval e d3) j = PA /\
        beta (FOeval e cr) (FOeval e dr) j = SS)).
Proof.
  intros e B ct dt c1 d1 c2 d2 c3 d3 cr dr len vd pl Htb Hvd Hpl.
  pose proof Htb as Htb'.
  destruct Htb' as [Hct [Hdt [Hc1 [Hd1' [Hc2 [Hd2' [Hc3 [Hd3'
    [Hcr [Hdr Hlen]]]]]]]]]].
  assert (Htb52 : tbl_below (B+52) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb74 : tbl_below (B+74) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb96 : tbl_below (B+96) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (Htb118 : tbl_below (B+118) ct dt c1 d1 c2 d2 c3 d3 cr dr len)
    by (unfold tbl_below; lia).
  assert (HinB : FOin_tm B (FOSucc pl) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB : FOin_tm (S B) (FOSucc pl) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB2 : FOin_tm (B+2) (FOSucc pl) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB2 : FOin_tm (S (B+2)) (FOSucc pl) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB4 : FOin_tm (B+4) (FOSucc vd) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB4 : FOin_tm (S (B+4)) (FOSucc vd) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB6 : FOin_tm (B+6) (FOSucc vd) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB6 : FOin_tm (S (B+6)) (FOSucc vd) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB8 : FOin_tm (B+8)
            (FOSucc (FOMult (FOSucc (FOVar B)) (FOSucc (FOVar B)))) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB8 : FOin_tm (S (B+8))
            (FOSucc (FOMult (FOSucc (FOVar B)) (FOSucc (FOVar B)))) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinB10 : FOin_tm (B+10)
            (FOSucc (FOMult (FOSucc (FOSucc (FOSucc (FOVar (B+8)))))
                            (FOSucc (FOSucc (FOSucc (FOVar (B+8))))))) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (HinSB10 : FOin_tm (S (B+10))
            (FOSucc (FOMult (FOSucc (FOSucc (FOSucc (FOVar (B+8)))))
                            (FOSucc (FOSucc (FOSucc (FOVar (B+8))))))) = false)
    by (apply FOin_tm_above; cbn; lia).
  assert (Henv : Forall (fun t => FOmax_var_tm t < B+12)
                   [FOVar B; FOVar (B+2); FOVar (B+4); FOVar (B+6)])
    by (repeat constructor; cbn; lia).
  assert (Hvd12 : FOmax_var_tm vd < B+12) by lia.
  assert (Hn4_52 : FOmax_var_tm (FOnumeral 4) < B+52)
    by (rewrite FOmax_var_numeral; lia).
  assert (Hn3_74 : FOmax_var_tm (FOnumeral 3) < B+74)
    by (rewrite FOmax_var_numeral; lia).
  assert (Hn4_96 : FOmax_var_tm (FOnumeral 4) < B+96)
    by (rewrite FOmax_var_numeral; lia).
  assert (Hn3_118 : FOmax_var_tm (FOnumeral 3) < B+118)
    by (rewrite FOmax_var_numeral; lia).
  assert (Hn1_52 : FOmax_var_tm (FOnumeral 1) < B+52)
    by (rewrite FOmax_var_numeral; lia).
  assert (Hn1_96 : FOmax_var_tm (FOnumeral 1) < B+96)
    by (rewrite FOmax_var_numeral; lia).
  assert (Hcz_52 : FOmax_var_tm (FOnumeral (cpair 1 0)) < B+52)
    by (rewrite FOmax_var_numeral; lia).
  assert (Hcz_74 : FOmax_var_tm (FOnumeral (cpair 1 0)) < B+74)
    by (rewrite FOmax_var_numeral; lia).
  assert (HtcsB96 : FOmax_var_tm (FOVar (B+10)) < B+96) by (cbn; lia).
  assert (HtcsB118 : FOmax_var_tm (FOVar (B+10)) < B+118) by (cbn; lia).
  assert (HxB52 : FOmax_var_tm (FOVar B) < B+52) by (cbn; lia).
  assert (HxB74 : FOmax_var_tm (FOVar B) < B+74) by (cbn; lia).
  assert (HxB96 : FOmax_var_tm (FOVar B) < B+96) by (cbn; lia).
  assert (HxB118 : FOmax_var_tm (FOVar B) < B+118) by (cbn; lia).
  assert (HpaB52 : FOmax_var_tm (FOVar (B+2)) < B+52) by (cbn; lia).
  assert (HpaB74 : FOmax_var_tm (FOVar (B+2)) < B+74) by (cbn; lia).
  assert (HpaB96 : FOmax_var_tm (FOVar (B+2)) < B+96) by (cbn; lia).
  assert (HpaB118 : FOmax_var_tm (FOVar (B+2)) < B+118) by (cbn; lia).
  assert (Hc0B74 : FOmax_var_tm (FOVar (B+4)) < B+74) by (cbn; lia).
  assert (HssB118 : FOmax_var_tm (FOVar (B+6)) < B+118) by (cbn; lia).
  unfold FOJIND.
  rewrite (FOsat_FOBexC e B (FOSucc pl) _ HinB HinSB).
  split.
  - intros [x [Hx Hb1]].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc pl) _ HinB2 HinSB2) in Hb1.
    destruct Hb1 as [PA [HPA Hb2]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb2. destruct Hb2 as [Hcp Hb3].
    set (e2 := FOupdate (FOupdate e B x) (B+2) PA) in *.
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcp.
    cbn [FOeval] in Hcp. unfold e2 in Hcp.
    rewrite (FOupdate_eq _ _ _) in Hcp.
    rewrite (FOupdate_neq _ (B+2) PA B ltac:(lia)) in Hcp.
    rewrite (FOupdate_eq _ _ _) in Hcp.
    rewrite (FOeval_update_above pl _ (B+2) PA ltac:(lia)) in Hcp.
    rewrite (FOeval_update_above pl e B x Hpl) in Hcp.
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc vd) _ HinB4 HinSB4) in Hb3.
    destruct Hb3 as [C0 [HC0 Hb4]].
    rewrite (FOsat_FOBexC _ (B+6) (FOSucc vd) _ HinB6 HinSB6) in Hb4.
    destruct Hb4 as [SS [HSS Hb5]].
    rewrite (FOsat_FOBexC _ (B+8) _ _ HinB8 HinSB8) in Hb5.
    destruct Hb5 as [vx [Hvx Hb6]].
    rewrite (FOsat_FOBexC _ (B+10) _ _ HinB10 HinSB10) in Hb6.
    destruct Hb6 as [tcs [Htcs Hb7]].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb7. destruct Hb7 as [Hcpvx Hb8].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb8. destruct Hb8 as [Hcptcs Hb9].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb9. destruct Hb9 as [Hpat Hb10].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb10. destruct Hb10 as [Hlk1 Hb11].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb11. destruct Hb11 as [Hlk2 Hb12].
    apply (proj1 (FOsat_FOAnd _ _ _)) in Hb12. destruct Hb12 as [Hlk3 Hlk4].
    set (e6 := FOupdate (FOupdate (FOupdate (FOupdate e2 (B+4) C0)
                 (B+6) SS) (B+8) vx) (B+10) tcs) in *.
    assert (Hstab : forall t, FOmax_var_tm t < B -> FOeval e6 t = FOeval e t).
    { intros t Ht. unfold e6, e2.
      rewrite (FOeval_update_above t _ (B+10) tcs ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+8) vx ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+6) SS ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+4) C0 ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) PA ltac:(lia)).
      exact (FOeval_update_above t e B x Ht). }
    assert (EvB : e6 B = x).
    { unfold e6, e2.
      rewrite (FOupdate_neq _ (B+10) tcs B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+8) vx B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+6) SS B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+4) C0 B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+2) PA B ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB2 : e6 (B+2) = PA).
    { unfold e6, e2.
      rewrite (FOupdate_neq _ (B+10) tcs (B+2) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+8) vx (B+2) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+6) SS (B+2) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+4) C0 (B+2) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB4 : e6 (B+4) = C0).
    { unfold e6, e2.
      rewrite (FOupdate_neq _ (B+10) tcs (B+4) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+8) vx (B+4) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+6) SS (B+4) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB6 : e6 (B+6) = SS).
    { unfold e6, e2.
      rewrite (FOupdate_neq _ (B+10) tcs (B+6) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+8) vx (B+6) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB8 : e6 (B+8) = vx).
    { unfold e6.
      rewrite (FOupdate_neq _ (B+10) tcs (B+8) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB10 : e6 (B+10) = tcs).
    { unfold e6. apply FOupdate_eq. }
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcpvx.
    cbn [FOeval] in Hcpvx. rewrite EvB, EvB8 in Hcpvx.
    apply (proj1 (FOsat_FOcpairF _ _ _ _)) in Hcptcs.
    cbn [FOeval] in Hcptcs. rewrite EvB8, EvB10, FOeval_numeral in Hcptcs.
    rewrite <- Hcpvx in Hcptcs.
    apply (proj1 (FOsat_FOPATF cpatInd e6 (B+12)
                    [FOVar B; FOVar (B+2); FOVar (B+4); FOVar (B+6)]
                    vd Henv Hvd12)) in Hpat.
    assert (Hsg : forall s,
        FOeval e6 (nth s [FOVar B; FOVar (B+2); FOVar (B+4); FOVar (B+6)] FOZero)
        = (fun s => match s with
                    | 0 => x | 1 => PA | 2 => C0 | 3 => SS | _ => 0 end) s).
    { intro s. destruct s as [|[|[|[|s]]]]; cbn [nth FOeval].
      - exact EvB.
      - exact EvB2.
      - exact EvB4.
      - exact EvB6.
      - destruct s; reflexivity. }
    rewrite (cpat_sem_ext _ _ _ Hsg) in Hpat.
    rewrite (Hstab vd Hvd) in Hpat.
    apply (proj1 (FOsat_FOlookup e6 (B+52) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 4) (FOVar B)
                    (FOnumeral (cpair 1 0)) (FOVar (B+2)) (FOnumeral 1)
                    Htb52 Hn4_52 HxB52 Hcz_52 HpaB52 Hn1_52)) in Hlk1.
    destruct Hlk1 as [j1 [Hj1 [Ha1 [Ha2 [Ha3 [Ha4 Ha5]]]]]].
    rewrite (Hstab len Hlen) in Hj1.
    rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral in Ha1.
    cbn [FOeval] in Ha2, Ha4.
    rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), EvB in Ha2.
    rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), FOeval_numeral in Ha3.
    rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), EvB2 in Ha4.
    rewrite (Hstab cr Hcr), (Hstab dr Hdr), FOeval_numeral in Ha5.
    apply (proj1 (FOsat_FOlookup e6 (B+74) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 3) (FOVar B)
                    (FOnumeral (cpair 1 0)) (FOVar (B+2)) (FOVar (B+4))
                    Htb74 Hn3_74 HxB74 Hcz_74 HpaB74 Hc0B74)) in Hlk2.
    destruct Hlk2 as [j2 [Hj2 [Hb1' [Hb2' [Hb3' [Hb4' Hb5']]]]]].
    rewrite (Hstab len Hlen) in Hj2.
    rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral in Hb1'.
    cbn [FOeval] in Hb2', Hb4', Hb5'.
    rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), EvB in Hb2'.
    rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), FOeval_numeral in Hb3'.
    rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), EvB2 in Hb4'.
    rewrite (Hstab cr Hcr), (Hstab dr Hdr), EvB4 in Hb5'.
    apply (proj1 (FOsat_FOlookup e6 (B+96) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 4) (FOVar B)
                    (FOVar (B+10)) (FOVar (B+2)) (FOnumeral 1)
                    Htb96 Hn4_96 HxB96 HtcsB96 HpaB96 Hn1_96)) in Hlk3.
    destruct Hlk3 as [j3 [Hj3 [Hc1'' [Hc2'' [Hc3'' [Hc4'' Hc5'']]]]]].
    rewrite (Hstab len Hlen) in Hj3.
    rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral in Hc1''.
    cbn [FOeval] in Hc2'', Hc3'', Hc4''.
    rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), EvB in Hc2''.
    rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), EvB10, <- Hcptcs in Hc3''.
    rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), EvB2 in Hc4''.
    rewrite (Hstab cr Hcr), (Hstab dr Hdr), FOeval_numeral in Hc5''.
    apply (proj1 (FOsat_FOlookup e6 (B+118) ct dt c1 d1 c2 d2 c3 d3
                    cr dr len (FOnumeral 3) (FOVar B)
                    (FOVar (B+10)) (FOVar (B+2)) (FOVar (B+6))
                    Htb118 Hn3_118 HxB118 HtcsB118 HpaB118 HssB118)) in Hlk4.
    destruct Hlk4 as [j4 [Hj4 [Hd1'' [Hd2'' [Hd3'' [Hd4'' Hd5'']]]]]].
    rewrite (Hstab len Hlen) in Hj4.
    rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral in Hd1''.
    cbn [FOeval] in Hd2'', Hd3'', Hd4'', Hd5''.
    rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), EvB in Hd2''.
    rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), EvB10, <- Hcptcs in Hd3''.
    rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), EvB2 in Hd4''.
    rewrite (Hstab cr Hcr), (Hstab dr Hdr), EvB6 in Hd5''.
    exists x, PA, C0, SS.
    split; [exact Hcp|].
    split; [exact Hpat|].
    split. { exists j1. repeat split; assumption. }
    split. { exists j2. repeat split; assumption. }
    split. { exists j3. repeat split; assumption. }
    exists j4. repeat split; assumption.
  - intros [x [PA [C0 [SS [Hcp [Hpat [Hlk1 [Hlk2 [Hlk3 Hlk4]]]]]]]]].
    pose proof (cpair_bound x PA) as Hxpa.
    assert (HC0le : C0 <= FOeval e vd).
    { rewrite <- Hpat. cbn [cpat_sem cpatInd pImpP pAllP].
      pose proof (cpair_bound 2 (cpair C0 (cpair 2 (cpair
        (cpair 3 (cpair x (cpair 2 (cpair PA SS)))) (cpair 3 (cpair x PA)))))) as Hb1.
      pose proof (cpair_bound C0 (cpair 2 (cpair
        (cpair 3 (cpair x (cpair 2 (cpair PA SS)))) (cpair 3 (cpair x PA))))) as Hb2.
      lia. }
    assert (HSSle : SS <= FOeval e vd).
    { rewrite <- Hpat. cbn [cpat_sem cpatInd pImpP pAllP].
      pose proof (cpair_bound 2 (cpair C0 (cpair 2 (cpair
        (cpair 3 (cpair x (cpair 2 (cpair PA SS)))) (cpair 3 (cpair x PA)))))) as Hb1.
      pose proof (cpair_bound C0 (cpair 2 (cpair
        (cpair 3 (cpair x (cpair 2 (cpair PA SS)))) (cpair 3 (cpair x PA))))) as Hb2.
      pose proof (cpair_bound 2 (cpair
        (cpair 3 (cpair x (cpair 2 (cpair PA SS)))) (cpair 3 (cpair x PA)))) as Hb3.
      pose proof (cpair_bound
        (cpair 3 (cpair x (cpair 2 (cpair PA SS)))) (cpair 3 (cpair x PA))) as Hb4.
      pose proof (cpair_bound 3 (cpair x (cpair 2 (cpair PA SS)))) as Hb5.
      pose proof (cpair_bound x (cpair 2 (cpair PA SS))) as Hb6.
      pose proof (cpair_bound 2 (cpair PA SS)) as Hb7.
      pose proof (cpair_bound PA SS) as Hb8.
      lia. }
    cbn [FOeval].
    exists x. split; [rewrite <- Hcp; lia|].
    rewrite (FOsat_FOBexC _ (B+2) (FOSucc pl) _ HinB2 HinSB2).
    exists PA. split.
    { cbn [FOeval]. rewrite (FOeval_update_above pl e B x Hpl).
      rewrite <- Hcp. lia. }
    set (e2 := FOupdate (FOupdate e B x) (B+2) PA).
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF e2 _ _ _)). cbn [FOeval]. unfold e2.
      rewrite (FOupdate_eq _ _ _).
      rewrite (FOupdate_neq _ (B+2) PA B ltac:(lia)).
      rewrite (FOupdate_eq _ _ _).
      rewrite (FOeval_update_above pl _ (B+2) PA ltac:(lia)).
      rewrite (FOeval_update_above pl e B x Hpl). exact Hcp. }
    rewrite (FOsat_FOBexC _ (B+4) (FOSucc vd) _ HinB4 HinSB4).
    exists C0. split.
    { cbn [FOeval]. unfold e2.
      rewrite (FOeval_update_above vd _ (B+2) PA ltac:(lia)).
      rewrite (FOeval_update_above vd e B x Hvd). lia. }
    rewrite (FOsat_FOBexC _ (B+6) (FOSucc vd) _ HinB6 HinSB6).
    exists SS. split.
    { cbn [FOeval]. unfold e2.
      rewrite (FOeval_update_above vd _ (B+4) C0 ltac:(lia)).
      rewrite (FOeval_update_above vd _ (B+2) PA ltac:(lia)).
      rewrite (FOeval_update_above vd e B x Hvd). lia. }
    rewrite (FOsat_FOBexC _ (B+8) _ _ HinB8 HinSB8).
    exists (cpair 0 x). split.
    { cbn [FOeval]. unfold e2.
      rewrite (FOupdate_neq _ (B+6) SS B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+4) C0 B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+2) PA B ltac:(lia)).
      rewrite (FOupdate_eq _ _ _).
      pose proof (cpair_le_sq 0 x) as Hsq. lia. }
    rewrite (FOsat_FOBexC _ (B+10) _ _ HinB10 HinSB10).
    exists (cpair 2 (cpair 0 x)). split.
    { cbn [FOeval].
      rewrite (FOupdate_eq _ _ _).
      pose proof (cpair_le_sq 2 (cpair 0 x)) as Hsq. lia. }
    set (e6 := FOupdate (FOupdate (FOupdate (FOupdate e2 (B+4) C0)
                 (B+6) SS) (B+8) (cpair 0 x)) (B+10) (cpair 2 (cpair 0 x))).
    assert (Hstab : forall t, FOmax_var_tm t < B -> FOeval e6 t = FOeval e t).
    { intros t Ht. unfold e6, e2.
      rewrite (FOeval_update_above t _ (B+10) (cpair 2 (cpair 0 x)) ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+8) (cpair 0 x) ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+6) SS ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+4) C0 ltac:(lia)).
      rewrite (FOeval_update_above t _ (B+2) PA ltac:(lia)).
      exact (FOeval_update_above t e B x Ht). }
    assert (EvB : e6 B = x).
    { unfold e6, e2.
      rewrite (FOupdate_neq _ (B+10) _ B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+8) _ B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+6) SS B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+4) C0 B ltac:(lia)).
      rewrite (FOupdate_neq _ (B+2) PA B ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB2 : e6 (B+2) = PA).
    { unfold e6, e2.
      rewrite (FOupdate_neq _ (B+10) _ (B+2) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+8) _ (B+2) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+6) SS (B+2) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+4) C0 (B+2) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB4 : e6 (B+4) = C0).
    { unfold e6, e2.
      rewrite (FOupdate_neq _ (B+10) _ (B+4) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+8) _ (B+4) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+6) SS (B+4) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB6 : e6 (B+6) = SS).
    { unfold e6, e2.
      rewrite (FOupdate_neq _ (B+10) _ (B+6) ltac:(lia)).
      rewrite (FOupdate_neq _ (B+8) _ (B+6) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB8 : e6 (B+8) = cpair 0 x).
    { unfold e6.
      rewrite (FOupdate_neq _ (B+10) _ (B+8) ltac:(lia)).
      apply FOupdate_eq. }
    assert (EvB10 : e6 (B+10) = cpair 2 (cpair 0 x)).
    { unfold e6. apply FOupdate_eq. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF e6 _ _ _)). cbn [FOeval].
      rewrite EvB, EvB8. reflexivity. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOcpairF e6 _ _ _)). cbn [FOeval].
      rewrite EvB8, EvB10, FOeval_numeral. reflexivity. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOPATF cpatInd e6 (B+12)
                      [FOVar B; FOVar (B+2); FOVar (B+4); FOVar (B+6)]
                      vd Henv Hvd12)).
      assert (Hsg : forall s,
          FOeval e6
            (nth s [FOVar B; FOVar (B+2); FOVar (B+4); FOVar (B+6)] FOZero)
          = (fun s => match s with
                      | 0 => x | 1 => PA | 2 => C0 | 3 => SS | _ => 0 end) s).
      { intro s. destruct s as [|[|[|[|s]]]]; cbn [nth FOeval].
        - exact EvB.
        - exact EvB2.
        - exact EvB4.
        - exact EvB6.
        - destruct s; reflexivity. }
      rewrite (cpat_sem_ext _ _ _ Hsg).
      rewrite (Hstab vd Hvd). exact Hpat. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOlookup e6 (B+52) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOnumeral 4) (FOVar B)
                      (FOnumeral (cpair 1 0)) (FOVar (B+2)) (FOnumeral 1)
                      Htb52 Hn4_52 HxB52 Hcz_52 HpaB52 Hn1_52)).
      destruct Hlk1 as [j [Hj [Ha1 [Ha2 [Ha3 [Ha4 Ha5]]]]]].
      exists j.
      split; [rewrite (Hstab len Hlen); exact Hj|].
      split.
      { rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral. exact Ha1. }
      split.
      { cbn [FOeval]. rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), EvB. exact Ha2. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), FOeval_numeral. exact Ha3. }
      split.
      { cbn [FOeval]. rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), EvB2. exact Ha4. }
      rewrite (Hstab cr Hcr), (Hstab dr Hdr), FOeval_numeral. exact Ha5. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOlookup e6 (B+74) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOnumeral 3) (FOVar B)
                      (FOnumeral (cpair 1 0)) (FOVar (B+2)) (FOVar (B+4))
                      Htb74 Hn3_74 HxB74 Hcz_74 HpaB74 Hc0B74)).
      destruct Hlk2 as [j [Hj [Ha1 [Ha2 [Ha3 [Ha4 Ha5]]]]]].
      exists j.
      split; [rewrite (Hstab len Hlen); exact Hj|].
      split.
      { rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral. exact Ha1. }
      split.
      { cbn [FOeval]. rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), EvB. exact Ha2. }
      split.
      { cbn [FOeval].
        rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), FOeval_numeral. exact Ha3. }
      split.
      { cbn [FOeval]. rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), EvB2. exact Ha4. }
      cbn [FOeval]. rewrite (Hstab cr Hcr), (Hstab dr Hdr), EvB4. exact Ha5. }
    apply (proj2 (FOsat_FOAnd _ _ _)). split.
    { apply (proj2 (FOsat_FOlookup e6 (B+96) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOnumeral 4) (FOVar B)
                      (FOVar (B+10)) (FOVar (B+2)) (FOnumeral 1)
                      Htb96 Hn4_96 HxB96 HtcsB96 HpaB96 Hn1_96)).
      destruct Hlk3 as [j [Hj [Ha1 [Ha2 [Ha3 [Ha4 Ha5]]]]]].
      exists j.
      split; [rewrite (Hstab len Hlen); exact Hj|].
      split.
      { rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral. exact Ha1. }
      split.
      { cbn [FOeval]. rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), EvB. exact Ha2. }
      split.
      { cbn [FOeval]. rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), EvB10. exact Ha3. }
      split.
      { cbn [FOeval]. rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), EvB2. exact Ha4. }
      rewrite (Hstab cr Hcr), (Hstab dr Hdr), FOeval_numeral. exact Ha5. }
    { apply (proj2 (FOsat_FOlookup e6 (B+118) ct dt c1 d1 c2 d2 c3 d3
                      cr dr len (FOnumeral 3) (FOVar B)
                      (FOVar (B+10)) (FOVar (B+2)) (FOVar (B+6))
                      Htb118 Hn3_118 HxB118 HtcsB118 HpaB118 HssB118)).
      destruct Hlk4 as [j [Hj [Ha1 [Ha2 [Ha3 [Ha4 Ha5]]]]]].
      exists j.
      split; [rewrite (Hstab len Hlen); exact Hj|].
      split.
      { rewrite (Hstab ct Hct), (Hstab dt Hdt), FOeval_numeral. exact Ha1. }
      split.
      { cbn [FOeval]. rewrite (Hstab c1 Hc1), (Hstab d1 Hd1'), EvB. exact Ha2. }
      split.
      { cbn [FOeval]. rewrite (Hstab c2 Hc2), (Hstab d2 Hd2'), EvB10. exact Ha3. }
      split.
      { cbn [FOeval]. rewrite (Hstab c3 Hc3), (Hstab d3 Hd3'), EvB2. exact Ha4. }
      cbn [FOeval]. rewrite (Hstab cr Hcr), (Hstab dr Hdr), EvB6. exact Ha5. }
Qed.

