From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Logic.Classical.
From Tiling Require Export Calculus.
From Tiling Require Export Hilbert.

Record Frame : Type := mkFrame {
  fW : Type;
  fR : nat -> fW -> fW -> Prop;
  fR_trans : forall n w v u, fR n w v -> fR n v u -> fR n w u;
  fR_wf : forall n, well_founded (fun u v => fR n v u);
  fR_mon : forall n w v, fR (S n) w v -> fR n w v;
  fR_nextcon : forall n w v, fR (S n) w v -> exists u, fR n v u
}.

Fixpoint forces (F : Frame) (V : fW F -> nat -> bool)
                (w : fW F) (phi : Form) : Prop :=
  match phi with
  | Var p => V w p = true
  | Bot => False
  | Impl X Y => forces F V w X -> forces F V w Y
  | Box n psi => forall v, fR F n w v -> forces F V v psi
  end.

Definition Valid (phi : Form) : Prop :=
  forall F V w, forces F V w phi.

Theorem soundness : forall phi, |- phi -> Valid phi.
Proof.
  intros phi H. induction H.
  - unfold Valid. intros F V w. simpl. intros Hphi _. exact Hphi.
  - unfold Valid. intros F V w. simpl. intros Hf Hg Hphi.
    apply Hf; [exact Hphi | apply Hg; exact Hphi].
  - unfold Valid. intros F V w. simpl. intro Hnnp.
    apply NNPP. exact Hnnp.
  - unfold Valid. intros F V w. simpl. intros Himp Hphi v Hwv.
    apply (Himp v Hwv). apply (Hphi v Hwv).
  - unfold Valid. intros F V w. simpl. intros Hbox v Hwv.
    pose proof (fR_wf F n) as Hwf.
    set (P := fun u => fR F n w u -> forces F V u phi).
    cut (P v); [intro Hpv; exact (Hpv Hwv) |].
    apply (well_founded_ind Hwf P).
    intros u IH. unfold P. intro Hwu.
    apply (Hbox u Hwu).
    intros u' Huu'.
    apply (IH u' Huu' (fR_trans F n w u u' Hwu Huu')).
  - unfold Valid. intros F V w. simpl. intros Hphi v Hwv u Hvu.
    apply Hphi. apply (fR_trans F n w v u Hwv Hvu).
  - unfold Valid. intros F V w. simpl. intros Hphi v Hwv.
    apply Hphi. apply (fR_mon F n w v Hwv).
  - unfold Valid. intros F V w. simpl. intros v Hwv Hbox.
    destruct (fR_nextcon F n w v Hwv) as [u Hvu].
    exact (Hbox u Hvu).
  - unfold Valid. intros F V w.
    apply (IHProvable1 F V w). apply (IHProvable2 F V w).
  - unfold Valid. intros F V w. simpl.
    intros v _. apply (IHProvable F V v).
Qed.
