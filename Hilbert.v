From Tiling Require Export Calculus.

Lemma prov_id : forall phi, |- Impl phi phi.
Proof.
  intro phi.
  pose proof (Ax_S phi (Impl phi phi) phi) as Hs.
  pose proof (Ax_K phi (Impl phi phi)) as Hk1.
  pose proof (Ax_K phi phi) as Hk2.
  exact (MP _ _ (MP _ _ Hs Hk1) Hk2).
Qed.

Lemma prov_weaken : forall phi psi, |- phi -> |- Impl psi phi.
Proof.
  intros phi psi Hphi.
  exact (MP _ _ (Ax_K phi psi) Hphi).
Qed.

Lemma prov_compose : forall phi psi chi,
  |- Impl phi psi -> |- Impl psi chi -> |- Impl phi chi.
Proof.
  intros phi psi chi Hpq Hqr.
  pose proof (Ax_S phi psi chi) as Hs.
  pose proof (prov_weaken _ phi Hqr) as Hpqr.
  exact (MP _ _ (MP _ _ Hs Hpqr) Hpq).
Qed.

Lemma prov_perm : forall phi psi chi,
  |- Impl phi (Impl psi chi) -> |- Impl psi (Impl phi chi).
Proof.
  intros phi psi chi H.
  pose proof (Ax_S phi psi chi) as Hs.
  pose proof (MP _ _ Hs H) as H1.
  pose proof (Ax_K psi phi) as Hk.
  pose proof (prov_compose _ _ _ Hk H1) as H2.
  exact H2.
Qed.

Lemma prov_mp2 : forall phi psi chi,
  |- Impl phi (Impl psi chi) -> |- phi -> |- psi -> |- chi.
Proof.
  intros phi psi chi H Hphi Hpsi.
  exact (MP _ _ (MP _ _ H Hphi) Hpsi).
Qed.

Lemma prov_DN_intro : forall phi, |- Impl phi (Neg (Neg phi)).
Proof.
  intro phi.
  unfold Neg.
  pose proof (prov_id (Impl phi Bot)) as Hid.
  exact (prov_perm _ _ _ Hid).
Qed.

Lemma prov_explosion : forall phi, |- Impl Bot phi.
Proof.
  intro phi.
  pose proof (prov_id Bot) as HBB.
  pose proof (Ax_K Bot (Neg phi)) as Hk.
  pose proof (Ax_DN phi) as HDN.
  exact (prov_compose _ _ _ Hk HDN).
Qed.

Lemma prov_compose_internal : forall phi psi chi,
  |- Impl (Impl psi chi) (Impl (Impl phi psi) (Impl phi chi)).
Proof.
  intros phi psi chi.
  pose proof (Ax_K (Impl psi chi) phi) as Hk.
  pose proof (Ax_S phi psi chi) as Hs.
  exact (prov_compose _ _ _ Hk Hs).
Qed.

Lemma prov_perm_internal : forall a b c,
  |- Impl (Impl a (Impl b c)) (Impl b (Impl a c)).
Proof.
  intros a b c.
  pose proof (Ax_S a b c) as H_S.
  pose proof (Ax_S (Impl a (Impl b c)) (Impl a b) (Impl a c)) as H_S2.
  pose proof (MP _ _ H_S2 H_S) as H1.
  pose proof (Ax_K b a) as H_K1.
  pose proof (Ax_K (Impl a b) (Impl a (Impl b c))) as H_K2.
  pose proof (prov_compose _ _ _ H_K1 H_K2) as H2.
  pose proof (prov_compose _ _ _ H2 H1) as H3.
  exact (prov_perm _ _ _ H3).
Qed.
