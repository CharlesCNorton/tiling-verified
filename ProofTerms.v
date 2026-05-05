From Tiling Require Export Calculus.

Inductive Provable_term : Form -> Type :=
  | pt_K       : forall phi psi,
      Provable_term (Impl phi (Impl psi phi))
  | pt_S       : forall phi psi chi,
      Provable_term (Impl (Impl phi (Impl psi chi))
                       (Impl (Impl phi psi) (Impl phi chi)))
  | pt_DN      : forall phi,
      Provable_term (Impl (Neg (Neg phi)) phi)
  | pt_BoxK    : forall n phi psi,
      Provable_term (Impl (Box n (Impl phi psi))
                       (Impl (Box n phi) (Box n psi)))
  | pt_Loeb    : forall n phi,
      Provable_term (Impl (Box n (Impl (Box n phi) phi)) (Box n phi))
  | pt_Box4    : forall n phi,
      Provable_term (Impl (Box n phi) (Box n (Box n phi)))
  | pt_Mon     : forall n phi,
      Provable_term (Impl (Box n phi) (Box (S n) phi))
  | pt_NextCon : forall n,
      Provable_term (Box (S n) (Neg (Box n Bot)))
  | pt_MP      : forall phi psi,
      Provable_term (Impl phi psi) -> Provable_term phi -> Provable_term psi
  | pt_Nec     : forall n phi,
      Provable_term phi -> Provable_term (Box n phi).

Theorem Provable_term_sound : forall phi, Provable_term phi -> |- phi.
Proof.
  intros phi pt. induction pt.
  - exact (Ax_K phi psi).
  - exact (Ax_S phi psi chi).
  - exact (Ax_DN phi).
  - exact (Ax_BoxK n phi psi).
  - exact (Ax_Loeb n phi).
  - exact (Ax_Box4 n phi).
  - exact (Ax_Mon n phi).
  - exact (Ax_NextCon n).
  - exact (MP _ _ IHpt1 IHpt2).
  - exact (Nec n _ IHpt).
Qed.

Theorem provable_to_inhabited_Provable_term : forall phi,
  |- phi -> inhabited (Provable_term phi).
Proof.
  intros phi H. induction H.
  - exact (inhabits (pt_K phi psi)).
  - exact (inhabits (pt_S phi psi chi)).
  - exact (inhabits (pt_DN phi)).
  - exact (inhabits (pt_BoxK n phi psi)).
  - exact (inhabits (pt_Loeb n phi)).
  - exact (inhabits (pt_Box4 n phi)).
  - exact (inhabits (pt_Mon n phi)).
  - exact (inhabits (pt_NextCon n)).
  - destruct IHProvable1 as [pt1]. destruct IHProvable2 as [pt2].
    exact (inhabits (pt_MP _ _ pt1 pt2)).
  - destruct IHProvable as [pt]. exact (inhabits (pt_Nec n _ pt)).
Qed.

Theorem Provable_term_iff_inhabited : forall phi,
  |- phi <-> inhabited (Provable_term phi).
Proof.
  intros phi. split.
  - exact (provable_to_inhabited_Provable_term phi).
  - intros [pt]. exact (Provable_term_sound phi pt).
Qed.
