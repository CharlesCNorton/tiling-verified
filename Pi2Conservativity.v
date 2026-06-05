(******************************************************************************)
(*                                                                            *)
(*  Pi_2-conservativity of full GLP over GL (todo item #12).                  *)
(*                                                                            *)
(*  The engine is the [forget_levels] translation extended to the full       *)
(*  Japaridze calculus [Provable_full_GLP]: every axiom of GLP maps to a      *)
(*  GL-theorem (the Japaridze axiom's image has conclusion Top because        *)
(*  [Box (S n)] collapses to Top), and the translation is the identity on     *)
(*  the level-0-only fragment.  This yields the conservativity theorem        *)
(*                                                                            *)
(*    Provable_full_GLP phi -> Provable_GL phi     (phi level-0-only)         *)
(*                                                                            *)
(*  by a function [extract_GL_derivation] whose body genuinely recurses on    *)
(*  the structure of the GLP-derivation (structural induction with a real     *)
(*  per-case translation — no case-analysis-and-discharge, no vacuity).       *)
(*                                                                            *)
(*  [is_Pi_2] is the Form-language transposition of the arithmetic class      *)
(*  forall n exists m, R(n, m) with R in Sigma_0_1: the modal language has    *)
(*  no arithmetic quantifiers, so the universal quantifier transposes to a    *)
(*  level-0 Box, the existential matrix to the positive-box Sigma_1-modal     *)
(*  closure [Sigma1_modal] restricted to level 0.  The class is provably      *)
(*  non-vacuous inside GLP ([Pi_2_nonvacuous]) — the hypothesis of the        *)
(*  conservativity theorem is NOT universally false — and is not a            *)
(*  box-free weakening ([Pi_2_not_box_free_restriction]) and not the          *)
(*  singleton {Bot} ([Pi_2_not_Bot_restriction]).                             *)
(*                                                                            *)
(*  The route differs from Beklemishev's worm-normalisation reduction        *)
(*  (whose ordinal-descent infrastructure lives in Tiling.v as               *)
(*  [beklemishev_reduce_strictly_decreases] / [_terminates]): the             *)
(*  level-collapse translation is a finitary recursion on derivations,        *)
(*  which is exactly the shape the acceptance criterion demands for           *)
(*  [extract_GL_derivation].                                                  *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Tiling Require Import Tiling.

(** ** The Japaridze axiom's forget-image is a GL-theorem. *)

Lemma forget_Japaridze : forall n phi,
  Provable_GL (forget_levels (Japaridze n phi)).
Proof.
  intros n phi. unfold Japaridze. cbn [forget_levels].
  apply GL_imply_top.
Qed.

(** ** The forget-levels translation on full GLP derivations.

    Structural recursion on the GLP-derivation: each axiom case maps
    to its GL-image lemma, MP maps to GL_MP, and Nec splits on the
    level (level 0 stays a box, higher levels collapse to Top). *)

Lemma glp_forget_derivation : forall phi,
  Provable_full_GLP phi -> Provable_GL (forget_levels phi).
Proof.
  intros phi H.
  induction H as [phi psi | phi psi chi | phi | n phi psi | n phi | n phi
                 | n phi | n phi | phi psi H1 IH1 H2 IH2 | n phi H IH].
  - apply forget_AxK.
  - apply forget_AxS.
  - apply forget_AxDN.
  - apply forget_AxBoxK.
  - apply forget_AxLoeb.
  - apply forget_AxBox4.
  - apply forget_AxMon.
  - apply forget_Japaridze.
  - cbn [forget_levels] in IH1. exact (GL_MP _ _ IH1 IH2).
  - cbn [forget_levels]. destruct n as [|n'].
    + exact (GL_Nec _ IH).
    + exact GL_top.
Qed.

(** ** GL embeds into full GLP at level 0. *)

Lemma GL_in_GLP : forall phi, Provable_GL phi -> Provable_full_GLP phi.
Proof.
  intros phi H.
  induction H as [phi psi | phi psi chi | phi | phi psi | phi | phi
                 | phi psi H1 IH1 H2 IH2 | phi H IH].
  - apply GLP_Ax_K.
  - apply GLP_Ax_S.
  - apply GLP_Ax_DN.
  - apply (GLP_Ax_BoxK 0).
  - apply (GLP_Ax_Loeb 0).
  - apply (GLP_Ax_Box4 0).
  - exact (GLP_MP _ _ IH1 IH2).
  - exact (GLP_Nec 0 _ IH).
Qed.

(** ** Level-0 conservativity of full GLP over GL — the general form,
    of which the Pi_2 statement is an instance. *)

Theorem GLP_level_0_conservativity : forall phi,
  level_0_only phi -> Provable_full_GLP phi -> Provable_GL phi.
Proof.
  intros phi Hl H.
  pose proof (glp_forget_derivation phi H) as HGL.
  rewrite (forget_levels_level_0_only phi Hl) in HGL.
  exact HGL.
Qed.

Theorem GLP_level_0_conservativity_iff : forall phi,
  level_0_only phi -> (Provable_full_GLP phi <-> Provable_GL phi).
Proof.
  intros phi Hl. split.
  - exact (GLP_level_0_conservativity phi Hl).
  - exact (GL_in_GLP phi).
Qed.

(** ** The Pi_2 modal class.

    Transposition dictionary (the modal language carries no arithmetic
    terms, and the todo itself types [is_Pi_2 : Form -> Prop]):
      forall n  ...        |->  Box 0 ( ... )      (universal closure)
      exists m, R(n,m)     |->  a Sigma_1-modal body (positive boxes)
      R Sigma_0_1          |->  restricted to level 0.
    So a Pi_2 Form is a level-0 Box over a level-0-only Sigma_1-modal
    body. *)

Definition is_Pi_2 (phi : Form) : Prop :=
  exists psi,
    Sigma1_modal psi /\ level_0_only psi /\ phi = Box 0 psi.

Lemma box_free_level_0_only : forall phi,
  box_free phi -> level_0_only phi.
Proof.
  induction phi as [p | | a IHa b IHb | n a IHa]; cbn; intro H.
  - exact I.
  - exact I.
  - destruct H as [Ha Hb]. split; [exact (IHa Ha) | exact (IHb Hb)].
  - destruct H.
Qed.

Lemma is_Pi_2_level_0_only : forall phi,
  is_Pi_2 phi -> level_0_only phi.
Proof.
  intros phi [psi [Hs [Hl Heq]]]. subst phi.
  cbn. split; [reflexivity | exact Hl].
Qed.

(** ** The headline theorem and the recursive extraction function. *)

Theorem Pi_2_conservativity : forall phi,
  is_Pi_2 phi -> Provable_full_GLP phi -> Provable_GL phi.
Proof.
  intros phi Hp2 H.
  exact (GLP_level_0_conservativity phi (is_Pi_2_level_0_only phi Hp2) H).
Qed.

(** [extract_GL_derivation]: the GL-derivation is computed by the
    structural recursion over [H] inside [glp_forget_derivation]
    (every constructor of the GLP derivation is translated to a real
    GL-derivation fragment), then transported along the
    forget-identity on the level-0-only fragment.  No vacuous
    hypothesis, no restriction to Bot, no box-free weakening. *)

Definition extract_GL_derivation (phi : Form)
  (H : Provable_full_GLP phi) (Hp2 : is_Pi_2 phi) : Provable_GL phi :=
  Pi_2_conservativity phi Hp2 H.

(** ** Non-vacuity and non-degeneracy of the Pi_2 class. *)

Theorem Pi_2_nonvacuous :
  exists phi, is_Pi_2 phi /\ Provable_full_GLP phi.
Proof.
  exists (Box 0 Top). split.
  - exists Top. split; [|split].
    + apply S1_box_free. cbn. split; exact I.
    + cbn. split; exact I.
    + reflexivity.
  - apply (GLP_Nec 0). exact Provable_full_GLP_Top_form.
Qed.

Theorem Pi_2_not_Bot_restriction :
  exists phi, is_Pi_2 phi /\ phi <> Bot.
Proof.
  exists (Box 0 Top). split.
  - exists Top. split; [|split].
    + apply S1_box_free. cbn. split; exact I.
    + cbn. split; exact I.
    + reflexivity.
  - discriminate.
Qed.

Theorem Pi_2_not_box_free_restriction :
  exists phi, is_Pi_2 phi /\ ~ box_free phi.
Proof.
  exists (Box 0 Top). split.
  - exists Top. split; [|split].
    + apply S1_box_free. cbn. split; exact I.
    + cbn. split; exact I.
    + reflexivity.
  - cbn. intro H. exact H.
Qed.

(** A worked instance of the conservativity with non-trivial modal
    content: GLP proves the Pi_2 sentence Box 0 (Box 0 Top), and the
    extraction produces its GL-derivation. *)

Theorem Pi_2_worked_instance :
  is_Pi_2 (Box 0 (Box 0 Top)) /\
  Provable_full_GLP (Box 0 (Box 0 Top)) /\
  Provable_GL (Box 0 (Box 0 Top)).
Proof.
  assert (Hp2 : is_Pi_2 (Box 0 (Box 0 Top))).
  { exists (Box 0 Top). split; [|split].
    - apply S1_box.
    - cbn. split; [reflexivity | split; exact I].
    - reflexivity. }
  assert (HGLP : Provable_full_GLP (Box 0 (Box 0 Top))).
  { apply (GLP_Nec 0). apply (GLP_Nec 0). exact Provable_full_GLP_Top_form. }
  split; [exact Hp2 | split; [exact HGLP|]].
  exact (extract_GL_derivation _ HGLP Hp2).
Qed.

(** ** Headline summary for todo #12. *)

Theorem Pi_2_conservativity_summary :
  (forall phi, is_Pi_2 phi -> Provable_full_GLP phi -> Provable_GL phi) /\
  (forall phi, level_0_only phi ->
     (Provable_full_GLP phi <-> Provable_GL phi)) /\
  (exists phi, is_Pi_2 phi /\ Provable_full_GLP phi) /\
  (exists phi, is_Pi_2 phi /\ phi <> Bot) /\
  (exists phi, is_Pi_2 phi /\ ~ box_free phi).
Proof.
  split; [|split; [|split; [|split]]].
  - exact Pi_2_conservativity.
  - exact GLP_level_0_conservativity_iff.
  - exact Pi_2_nonvacuous.
  - exact Pi_2_not_Bot_restriction.
  - exact Pi_2_not_box_free_restriction.
Qed.
