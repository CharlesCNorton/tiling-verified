From Stdlib Require Import Lists.List.
Import ListNotations.
From Tiling Require Export Calculus.
From Tiling Require Export Hilbert.

Definition Worm := list nat.

Fixpoint worm_to_form (w : Worm) : Form :=
  match w with
  | [] => Top
  | k :: rest => Box k (worm_to_form rest)
  end.

Theorem worm_top_provable : |- worm_to_form [].
Proof. simpl. apply prov_id. Qed.

Theorem worm_box_provable : forall k w,
  |- worm_to_form w -> |- worm_to_form (k :: w).
Proof.
  intros k w H. simpl. apply Nec. exact H.
Qed.
