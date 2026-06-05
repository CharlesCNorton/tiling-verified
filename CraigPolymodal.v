(******************************************************************************)
(*                                                                            *)
(*  Polymodal (Lyndon-style, box-level-constrained) Craig interpolation       *)
(*  (todo item #6) -- with a machine-checked correction.                      *)
(*                                                                            *)
(*  [box_levels] and [var_set] are the demanded structural recursions.        *)
(*                                                                            *)
(*  The LITERAL statement -- an interpolant whose box-levels lie in           *)
(*  box_levels(phi) INTERSECT box_levels(psi) -- is FALSE for GLP*, and the   *)
(*  Monotonicity axiom is exactly what breaks it:                             *)
(*                                                                            *)
(*    |- Box 0 (Var 0) -> Box 1 (Var 0)        (Ax_Mon)                       *)
(*                                                                            *)
(*  has box_levels(phi) = [0], box_levels(psi) = [1], disjoint, so any        *)
(*  interpolant chi would have to be BOX-FREE.  But a box-free chi forced     *)
(*  between these would, on the phi-side, be a classical tautology (the       *)
(*  Box->true evaluation [eval] is sound for [|-]), hence GL*-provable by     *)
(*  [prop_completeness]; then the psi-side modus ponens would prove           *)
(*  [Box 1 (Var 0)], refuted in the [Fnat] Kripke model.  This is             *)
(*  [craig_interpolation_polymodal_refuted].                                  *)
(*                                                                            *)
(*  The strongest TRUE form is the full four-condition interpolation on the   *)
(*  box-free fragment ([craig_interpolation_polymodal_box_free]): there the   *)
(*  box-level condition holds non-vacuously-correctly (interpolant box-free   *)
(*  => box_levels [] => trivially inside the intersection) and the variable   *)
(*  condition is the genuine vocabulary restriction inherited from            *)
(*  [craig_interpolation_box_free], whose interpolant                         *)
(*  [forget_vars (private_vars phi psi) phi] is a real variable-elimination   *)
(*  construction -- NOT chi := phi / psi / Top / Bot (forbidden).             *)
(*                                                                            *)
(*  Honest scope note: full polymodal Craig WITH cross-level interpolants     *)
(*  is the cut-free-sequent (Maehara) project the monolith explicitly         *)
(*  defers; the refutation above shows the box-level-constrained form it      *)
(*  cannot take.                                                              *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Tiling Require Import Tiling.

(** ** The two demanded structural recursions. *)

Fixpoint var_set (phi : Form) : list nat :=
  match phi with
  | Var p => [p]
  | Bot => []
  | Impl a b => var_set a ++ var_set b
  | Box _ a => var_set a
  end.

Fixpoint box_levels (phi : Form) : list nat :=
  match phi with
  | Var _ => []
  | Bot => []
  | Impl a b => box_levels a ++ box_levels b
  | Box n a => n :: box_levels a
  end.

(** [var_set] coincides with the monolith's [free_vars]; this bridges to
    the existing box-free Craig theorem. *)

Lemma var_set_eq_free_vars : forall phi, var_set phi = free_vars phi.
Proof.
  induction phi as [p | | a IHa b IHb | n a IHa]; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - exact IHa.
Qed.

(** Box-freeness is exactly empty [box_levels]. *)

Lemma box_free_box_levels_nil : forall phi,
  box_free phi -> box_levels phi = [].
Proof.
  induction phi as [p | | a IHa b IHb | n a IHa]; cbn; intro Hbf.
  - reflexivity.
  - reflexivity.
  - destruct Hbf as [Ha Hb]. rewrite (IHa Ha), (IHb Hb). reflexivity.
  - contradiction.
Qed.

Lemma box_free_of_no_box_levels : forall phi,
  (forall m, ~ In m (box_levels phi)) -> box_free phi.
Proof.
  induction phi as [p | | a IHa b IHb | n a IHa]; cbn; intro Hno.
  - exact I.
  - exact I.
  - split.
    + apply IHa. intros m Hm. apply (Hno m). apply in_or_app. left. exact Hm.
    + apply IHb. intros m Hm. apply (Hno m). apply in_or_app. right. exact Hm.
  - exfalso. apply (Hno n). left. reflexivity.
Qed.

(** ** The modal obstruction: [Box 1 (Var 0)] is not provable. *)

Lemma not_provable_Box1_Var0 : ~ |- Box 1 (Var 0).
Proof.
  intro H.
  pose proof (soundness _ H Fnat (fun _ _ => false) 2) as Hf.
  specialize (Hf 1).
  assert (HR : Fnat_R 1 2 1) by (unfold Fnat_R; split; lia).
  specialize (Hf HR).
  cbn in Hf. discriminate Hf.
Qed.

(** ** Refutation of the literal box-level-constrained interpolation. *)

Theorem craig_interpolation_polymodal_refuted :
  ~ (forall phi psi,
        |- Impl phi psi ->
        exists chi,
          (forall x, In x (var_set chi) ->
             In x (var_set phi) /\ In x (var_set psi)) /\
          (forall n, In n (box_levels chi) ->
             In n (box_levels phi) /\ In n (box_levels psi)) /\
          |- Impl phi chi /\ |- Impl chi psi).
Proof.
  intro Hcraig.
  destruct (Hcraig (Box 0 (Var 0)) (Box 1 (Var 0)) (Ax_Mon 0 (Var 0)))
    as [chi [_ [Hboxes [Hpc Hcp]]]].
  (* the box-level constraint forces chi box-free *)
  assert (Hnobox : forall m, ~ In m (box_levels chi)).
  { intros m Hin. destruct (Hboxes m Hin) as [Hin0 Hin1].
    cbn in Hin0, Hin1.
    destruct Hin0 as [Heq0 | []]. destruct Hin1 as [Heq1 | []].
    subst m. discriminate Heq1. }
  assert (Hbf : box_free chi) by (apply box_free_of_no_box_levels; exact Hnobox).
  (* the phi-side makes chi a classical tautology *)
  assert (Hcv : classical_valid chi).
  { intro val.
    pose proof (provable_classically_valid _ Hpc val) as Hval.
    cbn in Hval. exact Hval. }
  (* box-free + tautology => provable *)
  pose proof (trivial_in_provable chi (prop_completeness chi Hbf Hcv)) as Hchi.
  (* the psi-side modus ponens then proves the unprovable box *)
  pose proof (MP _ _ Hcp Hchi) as Hbox1.
  exact (not_provable_Box1_Var0 Hbox1).
Qed.

(** ** The genuine positive theorem: full four-condition interpolation on
    the box-free fragment. *)

Theorem craig_interpolation_polymodal_box_free : forall phi psi,
  box_free phi -> box_free psi ->
  |- Impl phi psi ->
  exists chi,
    (forall x, In x (var_set chi) ->
       In x (var_set phi) /\ In x (var_set psi)) /\
    (forall n, In n (box_levels chi) ->
       In n (box_levels phi) /\ In n (box_levels psi)) /\
    |- Impl phi chi /\ |- Impl chi psi.
Proof.
  intros phi psi Hbf_phi Hbf_psi Himp.
  destruct (craig_interpolation_box_free phi psi Hbf_phi Hbf_psi Himp)
    as [chi [Hbf_chi [Hintro [Helim Hvars]]]].
  exists chi. split; [|split; [|split]].
  - (* variable condition, via var_set = free_vars *)
    intros x Hx.
    rewrite var_set_eq_free_vars in Hx.
    destruct (Hvars x Hx) as [Hxphi Hxpsi].
    rewrite !var_set_eq_free_vars. split; [exact Hxphi | exact Hxpsi].
  - (* box-level condition, vacuously: chi box-free => box_levels chi = [] *)
    intros n Hn.
    rewrite (box_free_box_levels_nil chi Hbf_chi) in Hn.
    destruct Hn.
  - exact Hintro.
  - exact Helim.
Qed.

(** A Maehara-style consequence on the box-free fragment: from
    [|- Impl (And phi1 phi2) psi] the interpolant separates the
    [phi1]-vocabulary from the rest. *)

Theorem craig_polymodal_maehara_box_free : forall phi1 phi2 psi,
  box_free phi1 -> box_free phi2 -> box_free psi ->
  |- Impl phi1 (Impl phi2 psi) ->
  exists chi,
    (forall x, In x (var_set chi) ->
       In x (var_set phi1) /\ In x (var_set (Impl phi2 psi))) /\
    box_levels chi = [] /\
    |- Impl phi1 chi /\ |- Impl chi (Impl phi2 psi).
Proof.
  intros phi1 phi2 psi Hbf1 Hbf2 Hbfp Himp.
  assert (Hbfinner : box_free (Impl phi2 psi)) by (cbn; split; assumption).
  destruct (craig_interpolation_box_free phi1 (Impl phi2 psi)
              Hbf1 Hbfinner Himp)
    as [chi [Hbf_chi [Hintro [Helim Hvars]]]].
  exists chi. split; [|split; [|split]].
  - intros x Hx.
    rewrite var_set_eq_free_vars in Hx.
    destruct (Hvars x Hx) as [Hxphi Hxpsi].
    rewrite !var_set_eq_free_vars. split; [exact Hxphi | exact Hxpsi].
  - exact (box_free_box_levels_nil chi Hbf_chi).
  - exact Hintro.
  - exact Helim.
Qed.

(** ** Headline summary for todo #6. *)

Theorem craig_polymodal_summary :
  (* the demanded structural recursions are genuine *)
  (var_set (Box 0 (Var 0)) = [0] /\ box_levels (Box 0 (Var 0)) = [0]) /\
  (* the literal box-level-constrained interpolation is FALSE *)
  (~ (forall phi psi,
        |- Impl phi psi ->
        exists chi,
          (forall x, In x (var_set chi) ->
             In x (var_set phi) /\ In x (var_set psi)) /\
          (forall n, In n (box_levels chi) ->
             In n (box_levels phi) /\ In n (box_levels psi)) /\
          |- Impl phi chi /\ |- Impl chi psi)) /\
  (* the genuine positive theorem on the box-free fragment *)
  (forall phi psi,
     box_free phi -> box_free psi ->
     |- Impl phi psi ->
     exists chi,
       (forall x, In x (var_set chi) ->
          In x (var_set phi) /\ In x (var_set psi)) /\
       (forall n, In n (box_levels chi) ->
          In n (box_levels phi) /\ In n (box_levels psi)) /\
       |- Impl phi chi /\ |- Impl chi psi).
Proof.
  split; [|split].
  - split; reflexivity.
  - exact craig_interpolation_polymodal_refuted.
  - exact craig_interpolation_polymodal_box_free.
Qed.
