From Tiling Require Export Calculus.
From Tiling Require Export Hilbert.

Lemma fp_and_intro_meta : forall phi psi, |- phi -> |- psi -> |- And phi psi.
Proof.
  intros phi psi Hphi Hpsi.
  unfold And, Neg.
  pose proof (prov_id (Impl phi (Impl psi Bot))) as Hid.
  pose proof (Ax_S (Impl phi (Impl psi Bot)) phi (Impl psi Bot)) as HS1.
  pose proof (MP _ _ HS1 Hid) as Hstep1.
  pose proof (prov_weaken _ (Impl phi (Impl psi Bot)) Hphi) as Hphi_w.
  pose proof (MP _ _ Hstep1 Hphi_w) as Hstep2.
  pose proof (Ax_S (Impl phi (Impl psi Bot)) psi Bot) as HS2.
  pose proof (MP _ _ HS2 Hstep2) as Hstep3.
  pose proof (prov_weaken _ (Impl phi (Impl psi Bot)) Hpsi) as Hpsi_w.
  exact (MP _ _ Hstep3 Hpsi_w).
Qed.

Theorem fixed_point_loeb_witness : forall n X,
  |- Iff (Box n X) (Box n (Impl (Box n X) X)).
Proof.
  intros n X.
  apply fp_and_intro_meta.
  - pose proof (Ax_K X (Box n X)) as Hk1.
    pose proof (Nec n _ Hk1) as Hnec1.
    pose proof (Ax_BoxK n X (Impl (Box n X) X)) as HBK1.
    exact (MP _ _ HBK1 Hnec1).
  - exact (Ax_Loeb n X).
Qed.

Theorem fixed_point_existence_loeb_form : forall n X,
  exists psi, |- Iff psi (Box n (Impl psi X)).
Proof.
  intros n X. exists (Box n X). exact (fixed_point_loeb_witness n X).
Qed.
