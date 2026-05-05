From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
From Tiling Require Export Calculus.

Inductive T_axiom (n : nat) : Form -> Prop :=
  | TAx_K : forall phi psi,
      T_axiom n (Impl phi (Impl psi phi))
  | TAx_S : forall phi psi chi,
      T_axiom n (Impl (Impl phi (Impl psi chi))
                      (Impl (Impl phi psi) (Impl phi chi)))
  | TAx_DN : forall phi,
      T_axiom n (Impl (Neg (Neg phi)) phi)
  | TAx_BoxK : forall k phi psi, k < n ->
      T_axiom n (Impl (Box k (Impl phi psi)) (Impl (Box k phi) (Box k psi)))
  | TAx_Loeb : forall k phi, k < n ->
      T_axiom n (Impl (Box k (Impl (Box k phi) phi)) (Box k phi))
  | TAx_Box4 : forall k phi, k < n ->
      T_axiom n (Impl (Box k phi) (Box k (Box k phi)))
  | TAx_Mon : forall k phi, S k < n ->
      T_axiom n (Impl (Box k phi) (Box (S k) phi))
  | TAx_NextCon : forall k, S k < n ->
      T_axiom n (Box (S k) (Neg (Box k Bot))).

Inductive Bew (n : nat) : Form -> Prop :=
  | Bew_ax  : forall phi, T_axiom n phi -> Bew n phi
  | Bew_MP  : forall phi psi, Bew n (Impl phi psi) -> Bew n phi -> Bew n psi
  | Bew_Nec : forall k phi, k < n -> Bew n phi -> Bew n (Box k phi).

Theorem Bew_HBL_K : forall n k phi psi, k < n ->
  Bew n (Impl (Box k (Impl phi psi)) (Impl (Box k phi) (Box k psi))).
Proof. intros n k phi psi Hk. apply Bew_ax. apply TAx_BoxK; assumption. Qed.

Theorem Bew_HBL_Loeb : forall n k phi, k < n ->
  Bew n (Impl (Box k (Impl (Box k phi) phi)) (Box k phi)).
Proof. intros n k phi Hk. apply Bew_ax. apply TAx_Loeb; assumption. Qed.

Theorem Bew_HBL_Box4 : forall n k phi, k < n ->
  Bew n (Impl (Box k phi) (Box k (Box k phi))).
Proof. intros n k phi Hk. apply Bew_ax. apply TAx_Box4; assumption. Qed.

Theorem Bew_HBL_Nec : forall n k phi, k < n ->
  Bew n phi -> Bew n (Box k phi).
Proof. intros n k phi Hk H. exact (Bew_Nec n k phi Hk H). Qed.

Theorem Bew_HBL_MP : forall n phi psi,
  Bew n (Impl phi psi) -> Bew n phi -> Bew n psi.
Proof. exact Bew_MP. Qed.

Theorem T_axiom_cumulative : forall n phi,
  T_axiom n phi -> T_axiom (S n) phi.
Proof.
  intros n phi H. induction H.
  - apply TAx_K.
  - apply TAx_S.
  - apply TAx_DN.
  - apply TAx_BoxK; lia.
  - apply TAx_Loeb; lia.
  - apply TAx_Box4; lia.
  - apply TAx_Mon; lia.
  - apply TAx_NextCon; lia.
Qed.

Theorem Bew_cumulative : forall n phi,
  Bew n phi -> Bew (S n) phi.
Proof.
  intros n phi H. induction H as [phi Hax | phi psi _ IH1 _ IH2 | k phi Hk _ IH].
  - apply Bew_ax. exact (T_axiom_cumulative n phi Hax).
  - exact (Bew_MP _ _ _ IH1 IH2).
  - apply Bew_Nec; [lia|exact IH].
Qed.

Theorem Bew_to_Provable : forall n phi, Bew n phi -> |- phi.
Proof.
  intros n phi H. induction H as [phi Hax | phi psi _ IH1 _ IH2 | k phi Hk _ IH].
  - induction Hax.
    + apply Ax_K.
    + apply Ax_S.
    + apply Ax_DN.
    + apply Ax_BoxK.
    + apply Ax_Loeb.
    + apply Ax_Box4.
    + apply Ax_Mon.
    + apply Ax_NextCon.
  - exact (MP _ _ IH1 IH2).
  - exact (Nec _ _ IH).
Qed.
