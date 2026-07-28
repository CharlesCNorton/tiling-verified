(** Scratch development for the Icard-style neighborhood model of full
    GLP* (with the Japaridze scheme).  Once green, this splices into
    Tiling.v.  Carrier: Cantor normal form with multiplicities. *)

From Stdlib Require Import Arith.Arith Arith.Wf_nat Lists.List micromega.Lia.
From Stdlib Require Import Logic.Classical.
Import ListNotations.

(** ** CNF ordinals with multiplicity: [MC e t] denotes [omega^e + t],
    well-formed when exponents are weakly descending. *)

Inductive mord : Type :=
  | MZ : mord
  | MC : mord -> mord -> mord.

Fixpoint mcmp (a b : mord) : comparison :=
  match a, b with
  | MZ, MZ => Eq
  | MZ, _ => Lt
  | _, MZ => Gt
  | MC e1 t1, MC e2 t2 =>
      match mcmp e1 e2 with
      | Eq => mcmp t1 t2
      | c => c
      end
  end.

Definition mlt (a b : mord) : Prop := mcmp a b = Lt.
Definition mle (a b : mord) : Prop := mcmp a b <> Gt.

Lemma mcmp_refl : forall a, mcmp a a = Eq.
Proof.
  induction a as [|e IHe t IHt]; simpl; [reflexivity|].
  rewrite IHe. exact IHt.
Qed.

Lemma mcmp_eq_iff : forall a b, mcmp a b = Eq <-> a = b.
Proof.
  induction a as [|e1 IHe t1 IHt]; intros [|e2 t2]; cbn;
    try (split; congruence).
  destruct (mcmp e1 e2) eqn:He.
  - apply IHe in He. subst e2.
    split.
    + intro Ht. apply IHt in Ht. now subst t2.
    + intro H. injection H as Ht. subst t2. apply IHt. reflexivity.
  - split; intro H; [discriminate|].
    injection H as He' Ht'. subst. rewrite mcmp_refl in He. discriminate.
  - split; intro H; [discriminate|].
    injection H as He' Ht'. subst. rewrite mcmp_refl in He. discriminate.
Qed.

Lemma mcmp_antisym : forall a b, mcmp a b = CompOpp (mcmp b a).
Proof.
  induction a as [|e1 IHe t1 IHt]; intros [|e2 t2]; simpl; try reflexivity.
  rewrite IHe, IHt.
  destruct (mcmp e2 e1); reflexivity.
Qed.

Lemma mlt_irrefl : forall a, ~ mlt a a.
Proof. intros a H. unfold mlt in H. rewrite mcmp_refl in H. discriminate. Qed.

Lemma mlt_trans : forall a b c, mlt a b -> mlt b c -> mlt a c.
Proof.
  unfold mlt.
  induction a as [|e1 IHe t1 IHt]; intros b c Hab Hbc.
  - destruct b as [|e2 t2]; [discriminate|].
    destruct c as [|e3 t3]; [cbn in Hbc; discriminate|].
    reflexivity.
  - destruct b as [|e2 t2]; [discriminate|].
    destruct c as [|e3 t3]; [cbn in Hbc; discriminate|].
    cbn in *.
    destruct (mcmp e1 e2) eqn:H12; try discriminate.
    + apply mcmp_eq_iff in H12. subst e2.
      destruct (mcmp e1 e3) eqn:H13.
      * exact (IHt _ _ Hab Hbc).
      * reflexivity.
      * exact Hbc.
    + destruct (mcmp e2 e3) eqn:H23; try discriminate.
      * apply mcmp_eq_iff in H23. subst e3. now rewrite H12.
      * now rewrite (IHe _ _ H12 H23).
Qed.

Lemma mlt_total : forall a b, mlt a b \/ a = b \/ mlt b a.
Proof.
  intros a b. unfold mlt.
  destruct (mcmp a b) eqn:H.
  - right. left. now apply mcmp_eq_iff.
  - now left.
  - right. right. rewrite mcmp_antisym, H. reflexivity.
Qed.

Lemma mle_iff : forall a b, mle a b <-> (mlt a b \/ a = b).
Proof.
  intros a b. unfold mle, mlt.
  destruct (mcmp a b) eqn:H; split; intro K.
  - right. now apply mcmp_eq_iff.
  - discriminate.
  - now left.
  - discriminate.
  - now destruct K.
  - destruct K as [K|K]; [discriminate|].
    subst. rewrite mcmp_refl in H. discriminate.
Qed.

Lemma mlt_le_trans : forall a b c, mlt a b -> mle b c -> mlt a c.
Proof.
  intros a b c H1 H2.
  apply mle_iff in H2 as [H2| ->]; [exact (mlt_trans _ _ _ H1 H2) | exact H1].
Qed.

Lemma mle_lt_trans : forall a b c, mle a b -> mlt b c -> mlt a c.
Proof.
  intros a b c H1 H2.
  apply mle_iff in H1 as [H1| ->]; [exact (mlt_trans _ _ _ H1 H2) | exact H2].
Qed.

Lemma mle_trans : forall a b c, mle a b -> mle b c -> mle a c.
Proof.
  intros a b c H1 H2. apply mle_iff in H1 as [H1| ->]; [|exact H2].
  apply mle_iff in H2 as [H2| ->]; apply mle_iff.
  - left. exact (mlt_trans _ _ _ H1 H2).
  - now left.
Qed.

Lemma mle_refl : forall a, mle a a.
Proof. intro a. apply mle_iff. now right. Qed.

Lemma mlt_le : forall a b, mlt a b -> mle a b.
Proof. intros a b H. apply mle_iff. now left. Qed.

Lemma mZ_le : forall a, mle MZ a.
Proof. intros [|e t]; unfold mle; cbn; congruence. Qed.

Lemma mlt_MZ : forall a, a <> MZ -> mlt MZ a.
Proof. intros [|e t] H; [congruence|]. unfold mlt. reflexivity. Qed.

Lemma not_mlt_MZ : forall a, ~ mlt a MZ.
Proof. intros [|e t] H; unfold mlt in H; cbn in H; discriminate. Qed.

Lemma mlt_MC_inv : forall e1 t1 e2 t2,
  mlt (MC e1 t1) (MC e2 t2) ->
  mlt e1 e2 \/ (e1 = e2 /\ mlt t1 t2).
Proof.
  intros e1 t1 e2 t2 H. unfold mlt in *. cbn in H.
  destruct (mcmp e1 e2) eqn:He.
  - right. split; [now apply mcmp_eq_iff | exact H].
  - now left.
  - discriminate.
Qed.

Lemma mlt_MC_head : forall e1 t1 e2 t2,
  mlt e1 e2 -> mlt (MC e1 t1) (MC e2 t2).
Proof.
  intros e1 t1 e2 t2 H. unfold mlt in *. cbn. now rewrite H.
Qed.

Lemma mlt_MC_tail : forall e t1 t2,
  mlt t1 t2 -> mlt (MC e t1) (MC e t2).
Proof.
  intros e t1 t2 H. unfold mlt in *. cbn. now rewrite mcmp_refl.
Qed.

(** Head exponent (0 for MZ). *)

Definition mhead (a : mord) : mord :=
  match a with MZ => MZ | MC e _ => e end.

(** Well-formed CNF: weakly descending exponents. *)

Fixpoint mwf (a : mord) : Prop :=
  match a with
  | MZ => True
  | MC e t => mwf e /\ mwf t /\ mle (mhead t) e
  end.

(** ** Well-foundedness of [mlt] on well-formed ordinals. *)

Definition mR (x y : mord) : Prop := mwf x /\ mlt x y.

Lemma mR_acc_MZ : Acc mR MZ.
Proof.
  constructor. intros y [_ Hy]. destruct (not_mlt_MZ _ Hy).
Qed.

(** Accessibility of every wf ordinal whose head is bounded by an
    accessible exponent, by an inner induction on the spine. *)

Lemma mR_acc_bounded : forall e, Acc mR e ->
  forall a, mwf a -> mle (mhead a) e -> Acc mR a.
Proof.
  intros e Hacc.
  induction Hacc as [e Hacce IHe].
  fix REC 1.  (* structural recursion over the spine of a *)
  intros a.
  destruct a as [|ea ta].
  - intros _ _. exact mR_acc_MZ.
  - intros [Hwfe [Hwft Hdesc]] Hbound.
    cbn in Hbound.
    (* First: Acc of the tail, by the spine recursion. *)
    assert (Hta : Acc mR ta).
    { apply REC.
      - exact Hwft.
      - eapply mle_trans; [exact Hdesc | exact Hbound]. }
    (* Now: Acc (MC ea ta) by induction on Acc of the tail. *)
    clear REC Hwft.
    revert Hdesc.
    induction Hta as [ta Hta IHta]. intro Hdesc.
    constructor. intros y [Hwfy Hy].
    destruct y as [|ey ty]; [exact mR_acc_MZ|].
    destruct Hwfy as [Hwfey [Hwfty Hdescy]].
    destruct (mlt_MC_inv _ _ _ _ Hy) as [Hlt | [Heq Hlt]].
    + (* head drop: use the outer induction at ey *)
      exact (IHe ey
               (conj Hwfey (mlt_le_trans _ _ _ Hlt Hbound))
               (MC ey ty)
               (conj Hwfey (conj Hwfty Hdescy))
               (mle_refl ey)).
    + (* same head, tail drop: inner induction *)
      subst ey.
      apply IHta.
      * exact (conj Hwfty Hlt).
      * exact Hdescy.
Qed.

Theorem mR_wf : well_founded mR.
Proof.
  intro a.
  constructor. intros y [Hwfy Hy]. clear a Hy.
  induction y as [|e IHe t IHt].
  - exact mR_acc_MZ.
  - destruct Hwfy as [Hwfe [Hwft Hdesc]].
    apply (mR_acc_bounded e (IHe Hwfe)).
    + cbn. split; [exact Hwfe | split; [exact Hwft | exact Hdesc]].
    + cbn. apply mle_refl.
Qed.

(** ** End-logarithm and iterates. *)

Fixpoint mell (a : mord) : mord :=
  match a with
  | MZ => MZ
  | MC e MZ => e
  | MC _ t => mell t
  end.

Lemma mell_MC_cons : forall e e' t', mell (MC e (MC e' t')) = mell (MC e' t').
Proof. reflexivity. Qed.

Fixpoint mellk (k : nat) (a : mord) : mord :=
  match k with
  | 0 => a
  | S k' => mellk k' (mell a)
  end.

Lemma mellk_S : forall k a, mellk (S k) a = mellk k (mell a).
Proof. reflexivity. Qed.

Lemma mellk_MZ : forall k, mellk k MZ = MZ.
Proof. induction k; [reflexivity | exact IHk]. Qed.

Lemma mell_wf : forall a, mwf a -> mwf (mell a).
Proof.
  induction a as [|e IHe t IHt]; cbn; [trivial|].
  intros [He [Ht _]].
  destruct t as [|e' t'].
  - exact He.
  - exact (IHt Ht).
Qed.

Lemma mellk_wf : forall k a, mwf a -> mwf (mellk k a).
Proof.
  induction k as [|k IH]; cbn; intros a Ha; [exact Ha|].
  apply IH. exact (mell_wf a Ha).
Qed.

Lemma mell_le_head : forall a, mwf a -> mle (mell a) (mhead a).
Proof.
  induction a as [|e IHe t IHt]; cbn.
  - intros _. apply mle_refl.
  - intros [He [Ht Hd]].
    destruct t as [|e' t'].
    + apply mle_refl.
    + eapply mle_trans; [exact (IHt Ht) | exact Hd].
Qed.

(** [mell a = MZ] iff [a] is zero or a successor; nonzero last exponent
    characterises limits.  We only need the structural side used by the
    model: nothing here yet. *)

(** ** Multiplicity decrement: drop one copy of the last CNF term.
    [mdec (MC e MZ) = MZ], [mdec (MC e t) = MC e (mdec t)]. *)

Fixpoint mdec (a : mord) : mord :=
  match a with
  | MZ => MZ
  | MC _ MZ => MZ
  | MC e t => MC e (mdec t)
  end.

Lemma mdec_lt : forall a, a <> MZ -> mlt (mdec a) a.
Proof.
  induction a as [|e IHe t IHt]; [congruence|].
  intros _.
  destruct t as [|e' t'].
  - cbn. unfold mlt. reflexivity.
  - change (mdec (MC e (MC e' t'))) with (MC e (mdec (MC e' t'))).
    apply mlt_MC_tail. apply IHt. congruence.
Qed.

Lemma mdec_wf : forall a, mwf a -> mwf (mdec a).
Proof.
  induction a as [|e IHe t IHt]; cbn; [trivial|].
  intros [He [Ht Hd]].
  destruct t as [|e' t'].
  - exact I.
  - change (mwf (MC e (mdec (MC e' t')))).
    cbn. split; [exact He|].
    split; [apply IHt; exact Ht|].
    destruct t' as [|e'' t''].
    + cbn. apply mZ_le.
    + cbn. cbn in Hd. exact Hd.
Qed.

(** ** Auxiliary constructions for the density lemmas. *)

(** Comparison respects heads. *)

Lemma mlt_head_le : forall a b, mlt a b -> mle (mhead a) (mhead b).
Proof.
  intros [|ea ta] [|eb tb] H; cbn.
  - apply mle_refl.
  - apply mZ_le.
  - destruct (not_mlt_MZ _ H).
  - unfold mlt in H. cbn in H.
    destruct (mcmp ea eb) eqn:He.
    + apply mcmp_eq_iff in He. subst. apply mle_refl.
    + unfold mle. rewrite He. congruence.
    + discriminate.
Qed.

(** ** Spine length and repeated terms. *)

Fixpoint mlen (a : mord) : nat :=
  match a with MZ => 0 | MC _ t => S (mlen t) end.

Fixpoint mrep (mu : mord) (k : nat) : mord :=
  match k with 0 => MZ | S k' => MC mu (mrep mu k') end.

Lemma mrep_wf : forall mu k, mwf mu -> mwf (mrep mu k).
Proof.
  intros mu k Hmu. induction k as [|k IH]; cbn; [exact I|].
  split; [exact Hmu|]. split; [exact IH|].
  destruct k; cbn; [apply mZ_le | apply mle_refl].
Qed.

Lemma mrep_head_le : forall mu k, mle (mhead (mrep mu k)) mu.
Proof.
  intros mu [|k]; cbn; [apply mZ_le | apply mle_refl].
Qed.

Lemma mell_mrep : forall mu k, mell (mrep mu (S k)) = mu.
Proof.
  intros mu k. induction k as [|k IH]; cbn; [reflexivity|].
  exact IH.
Qed.

(** Any wf ordinal with head at most [mu] is dominated by enough
    [omega^mu] copies. *)

Lemma mrep_dominates : forall t mu,
  mwf t -> mle (mhead t) mu -> mlt t (mrep mu (S (mlen t))).
Proof.
  induction t as [|e IHe t' IHt]; intros mu Hwf Hle.
  - cbn. apply mlt_MZ. congruence.
  - cbn in Hle. destruct Hwf as [He [Ht' Hd]].
    cbn [mlen mrep].
    apply mle_iff in Hle as [Hlt | ->].
    + apply mlt_MC_head. exact Hlt.
    + apply mlt_MC_tail. apply IHt; [exact Ht'|].
      exact Hd.
Qed.

(** ** The bump construction: the least-style witness above [g] with
    prescribed last exponent [mu]: keep the terms of [g] with exponent
    strictly above [mu], then pad with copies of [omega^mu]. *)

Fixpoint bump (g mu : mord) : mord :=
  match g with
  | MZ => MC mu MZ
  | MC e t =>
      match mcmp mu e with
      | Lt => MC e (bump t mu)
      | _ => mrep mu (S (mlen (MC e t)))
      end
  end.

Lemma bump_nonzero : forall g mu, bump g mu <> MZ.
Proof.
  intros [|e t] mu; cbn; [congruence|].
  destruct (mcmp mu e); cbn; congruence.
Qed.

Lemma bump_wf : forall g mu, mwf g -> mwf mu -> mwf (bump g mu).
Proof.
  induction g as [|e IHe t IH]; intros mu Hg Hmu.
  - cbn. repeat split; [exact Hmu | apply mZ_le].
  - destruct Hg as [He [Ht Hd]].
    cbn [bump].
    destruct (mcmp mu e) eqn:Hcmp.
    + apply mrep_wf. exact Hmu.
    + cbn [mwf]. split; [exact He|]. split.
      * apply IH; assumption.
      * destruct t as [|e' t'].
        -- cbn. apply mlt_le. exact Hcmp.
        -- cbn [bump]. destruct (mcmp mu e') eqn:H1.
           ++ cbn [mlen mrep mhead]. apply mlt_le. exact Hcmp.
           ++ cbn [mhead]. cbn in Hd. exact Hd.
           ++ cbn [mlen mrep mhead]. apply mlt_le. exact Hcmp.
    + apply mrep_wf. exact Hmu.
Qed.

Lemma bump_gt : forall g mu, mwf g -> mlt g (bump g mu).
Proof.
  induction g as [|e IHe t IH]; intros mu Hg; cbn.
  - apply mlt_MZ. congruence.
  - destruct Hg as [He [Ht Hd]].
    destruct (mcmp mu e) eqn:Hcmp.
    + apply mcmp_eq_iff in Hcmp. subst mu.
      cbn [mlen mrep].
      apply mlt_MC_tail.
      apply mrep_dominates; [exact Ht | exact Hd].
    + apply mlt_MC_tail. apply IH; assumption.
    + cbn [mlen mrep].
      apply mlt_MC_head. unfold mlt.
      rewrite mcmp_antisym, Hcmp. reflexivity.
Qed.

Lemma bump_mell : forall g mu, mell (bump g mu) = mu.
Proof.
  induction g as [|e IHe t IH]; intros mu.
  - reflexivity.
  - cbn [bump]. destruct (mcmp mu e) eqn:Hcmp.
    + apply mell_mrep.
    + pose proof (bump_nonzero t mu) as Hnz.
      destruct (bump t mu) as [|eb tb] eqn:Hb; [congruence|].
      rewrite (mell_MC_cons e eb tb).
      rewrite <- Hb. apply IH.
    + apply mell_mrep.
Qed.

(** All exponents of [bump g mu] are at least [mu]; combined with a
    strict bound on [g] below [V] whose exponents all exceed [mu],
    the bump stays below [V]. *)

Lemma bump_lt : forall g V mu,
  mwf g -> mwf V ->
  mlt g V -> mlt mu (mell V) ->
  mlt (bump g mu) V.
Proof.
  induction g as [|e IHe t IH]; intros V mu Hg HV Hlt Hmu.
  - (* bump = omega^mu; mu < mell V <= mhead V *)
    destruct V as [|ev tv]; [destruct (not_mlt_MZ _ Hlt)|].
    cbn. apply mlt_MC_head.
    eapply mlt_le_trans; [exact Hmu|].
    apply mell_le_head. exact HV.
  - destruct V as [|ev tv]; [destruct (not_mlt_MZ _ Hlt)|].
    destruct Hg as [He [Ht Hd]].
    destruct HV as [Hev [Htv Hdv]].
    cbn [bump].
    destruct (mcmp mu e) eqn:Hcmp.
    + (* mu = e: bump = mrep; head mu < mell V <= head V = ev *)
      apply mcmp_eq_iff in Hcmp. subst mu.
      cbn [mlen mrep]. apply mlt_MC_head.
      eapply mlt_le_trans; [exact Hmu|].
      apply (mell_le_head (MC ev tv)).
      cbn. split; [exact Hev | split; [exact Htv | exact Hdv]].
    + (* mu < e: keep the head term *)
      destruct (mlt_MC_inv _ _ _ _ Hlt) as [Hh | [Heq Htl]].
      * apply mlt_MC_head. exact Hh.
      * subst ev. apply mlt_MC_tail.
        apply IH; try assumption.
        (* mu < mell (MC e tv): tv = MZ impossible since t < tv *)
        destruct tv as [|ev' tv'].
        -- destruct (not_mlt_MZ _ Htl).
        -- rewrite (mell_MC_cons e ev' tv') in Hmu. exact Hmu.
    + (* mu > e: bump = mrep with head mu *)
      cbn [mlen mrep]. apply mlt_MC_head.
      eapply mlt_le_trans; [exact Hmu|].
      apply (mell_le_head (MC ev tv)).
      cbn. split; [exact Hev | split; [exact Htv | exact Hdv]].
Qed.

(** ** The master density lemma. *)

Lemma master_density : forall V g mu,
  mwf V -> mwf g -> mwf mu ->
  mlt g V -> mlt mu (mell V) ->
  exists B, mwf B /\ mlt g B /\ mlt B V /\ mell B = mu.
Proof.
  intros V g mu HV Hg Hmu Hlt Hmell.
  exists (bump g mu).
  repeat split.
  - apply bump_wf; assumption.
  - apply bump_gt; assumption.
  - apply bump_lt; assumption.
  - apply bump_mell.
Qed.

(** ** Iterated-logarithm bookkeeping. *)

Lemma mellk_add : forall j k y, mellk (j + k) y = mellk k (mellk j y).
Proof.
  induction j as [|j IH]; intros k y; cbn; [reflexivity|].
  apply IH.
Qed.

Lemma mellk_zero_up : forall j k y, j <= k ->
  mellk j y = MZ -> mellk k y = MZ.
Proof.
  intros j k y Hle Hz.
  replace k with (j + (k - j)) by lia.
  rewrite mellk_add, Hz. apply mellk_MZ.
Qed.

Lemma mellk_nonzero_down : forall j k y, j <= k ->
  mellk k y <> MZ -> mellk j y <> MZ.
Proof.
  intros j k y Hle Hnz Hz. apply Hnz.
  exact (mellk_zero_up j k y Hle Hz).
Qed.

(** ** The chain construction: a point strictly below [y] whose first
    [n] iterated logarithms sit strictly between prescribed bounds and
    the logarithms of [y]. *)

Lemma chain : forall n y (g : nat -> mord),
  mwf y -> mellk (S n) y <> MZ ->
  (forall k, k <= n -> mwf (g k) /\ mlt (g k) (mellk k y)) ->
  exists z, mwf z /\
    (forall k, k <= n ->
       mlt (g k) (mellk k z) /\ mlt (mellk k z) (mellk k y)).
Proof.
  induction n as [|m IH]; intros y g Hwf Hnz Hg.
  - destruct (Hg 0 (Nat.le_refl 0)) as [Hg0 Hlt0].
    cbn in Hlt0.
    destruct (master_density y (g 0) MZ Hwf Hg0 I Hlt0
                (mlt_MZ _ Hnz)) as [B [HB1 [HB2 [HB3 _]]]].
    exists B. split; [exact HB1|].
    intros k Hk. assert (k = 0) by lia. subst k.
    cbn. exact (conj HB2 HB3).
  - (* First build the deep witness inside mell y. *)
    destruct (IH (mell y) (fun k => g (S k)) (mell_wf y Hwf) Hnz
                (fun k Hk => Hg (S k) (le_n_S _ _ Hk)))
      as [w [Hww Hwprops]].
    (* Then place it as the last exponent below y. *)
    destruct (Hg 0 (Nat.le_0_l _)) as [Hg0 Hlt0].
    cbn in Hlt0.
    assert (Hwlt : mlt w (mell y)).
    { exact (proj2 (Hwprops 0 (Nat.le_0_l _))). }
    destruct (master_density y (g 0) w Hwf Hg0 Hww Hlt0 Hwlt)
      as [B [HB1 [HB2 [HB3 HB4]]]].
    exists B. split; [exact HB1|].
    intros k Hk. destruct k as [|j].
    + cbn. exact (conj HB2 HB3).
    + cbn [mellk]. rewrite HB4.
      exact (Hwprops j (le_S_n _ _ Hk)).
Qed.

(** ** Pointwise maxima of constraint lists. *)

Definition mmax (a b : mord) : mord :=
  match mcmp a b with Lt => b | _ => a end.

Lemma mmax_le_l : forall a b, mle a (mmax a b).
Proof.
  intros a b. unfold mmax.
  destruct (mcmp a b) eqn:H.
  - apply mle_refl.
  - apply mlt_le. exact H.
  - apply mle_refl.
Qed.

Lemma mmax_le_r : forall a b, mle b (mmax a b).
Proof.
  intros a b. unfold mmax.
  destruct (mcmp a b) eqn:H.
  - apply mcmp_eq_iff in H. subst. apply mle_refl.
  - apply mle_refl.
  - apply mlt_le. unfold mlt. rewrite mcmp_antisym, H. reflexivity.
Qed.

Lemma mmax_lub : forall a b c, mlt a c -> mlt b c -> mlt (mmax a b) c.
Proof.
  intros a b c H1 H2. unfold mmax.
  destruct (mcmp a b); assumption.
Qed.

Lemma mmax_wf : forall a b, mwf a -> mwf b -> mwf (mmax a b).
Proof.
  intros a b Ha Hb. unfold mmax. destruct (mcmp a b); assumption.
Qed.

Definition gs_bound (gs : list (nat * mord)) (k : nat) : mord :=
  fold_right (fun p acc =>
    if Nat.eqb (fst p) k then mmax (snd p) acc else acc) MZ gs.

Lemma gs_bound_ge : forall gs k gamma,
  In (k, gamma) gs -> mle gamma (gs_bound gs k).
Proof.
  induction gs as [|[k' g'] gs IH]; intros k gamma Hin; [destruct Hin|].
  cbn in Hin. destruct Hin as [Heq | Hin].
  - injection Heq as -> ->. cbn. rewrite Nat.eqb_refl.
    apply mmax_le_l.
  - cbn. destruct (Nat.eqb k' k) eqn:He.
    + eapply mle_trans; [exact (IH _ _ Hin) | apply mmax_le_r].
    + exact (IH _ _ Hin).
Qed.

Lemma gs_bound_wf : forall gs k,
  (forall p, In p gs -> mwf (snd p)) -> mwf (gs_bound gs k).
Proof.
  induction gs as [|[k' g'] gs IH]; intros k Hwf; cbn; [exact I|].
  destruct (Nat.eqb k' k) eqn:He.
  - apply mmax_wf.
    + exact (Hwf _ (or_introl eq_refl)).
    + apply IH. intros p Hp. exact (Hwf _ (or_intror Hp)).
  - apply IH. intros p Hp. exact (Hwf _ (or_intror Hp)).
Qed.

Lemma gs_bound_lt : forall gs k bound,
  (forall gamma, In (k, gamma) gs -> mlt gamma bound) ->
  bound <> MZ ->
  mlt (gs_bound gs k) bound.
Proof.
  induction gs as [|[k' g'] gs IH]; intros k bound Hin Hnz; cbn.
  - apply mlt_MZ. exact Hnz.
  - destruct (Nat.eqb k' k) eqn:He.
    + apply Nat.eqb_eq in He. subst k'.
      apply mmax_lub.
      * exact (Hin _ (or_introl eq_refl)).
      * apply IH; [|exact Hnz].
        intros gamma Hg. exact (Hin _ (or_intror Hg)).
    + apply IH; [|exact Hnz].
      intros gamma Hg. exact (Hin _ (or_intror Hg)).
Qed.

(** ** Neighborhood membership and legitimacy. *)

Definition icmember (n : nat) (x : mord) (gs : list (nat * mord))
           (y : mord) : Prop :=
  mwf y /\ mlt y x /\
  (forall k, k <= n -> mle (mellk k y) (mellk k x)) /\
  (forall p, In p gs -> mlt (snd p) (mellk (fst p) y)).

Definition iclegit (n : nat) (x : mord) (gs : list (nat * mord)) : Prop :=
  forall p, In p gs ->
    fst p <= n /\ mwf (snd p) /\ mlt (snd p) (mellk (fst p) x).

(** Existence of members below any point with a nonzero [S n]-th
    logarithm, against arbitrary legitimate constraints. *)

Lemma member_exists : forall n x gs,
  mwf x -> mellk (S n) x <> MZ -> iclegit n x gs ->
  exists z, icmember n x gs z.
Proof.
  intros n x gs Hwf Hnz Hleg.
  set (g := fun k => gs_bound gs k).
  assert (Hgprop : forall k, k <= n -> mwf (g k) /\ mlt (g k) (mellk k x)).
  { intros k Hk. split.
    - apply gs_bound_wf. intros p Hp. exact (proj1 (proj2 (Hleg p Hp))).
    - apply gs_bound_lt.
      + intros gamma Hg.
        exact (proj2 (proj2 (Hleg _ Hg))).
      + apply (mellk_nonzero_down k (S n) x); [lia | exact Hnz]. }
  destruct (chain n x g Hwf Hnz Hgprop) as [z [Hz1 Hz2]].
  exists z.
  repeat split.
  - exact Hz1.
  - exact (proj2 (Hz2 0 (Nat.le_0_l _))).
  - intros k Hk. apply mlt_le. exact (proj2 (Hz2 k Hk)).
  - intros [k gamma] Hin.
    cbn.
    pose proof (Hleg _ Hin) as [Hk [Hwfg Hltg]].
    cbn in Hk, Hwfg, Hltg.
    eapply mle_lt_trans.
    + exact (gs_bound_ge gs k gamma Hin).
    + exact (proj1 (Hz2 k Hk)).
Qed.

(** ** Exact pinning: the interval [(mdec V, V]] collapses to [V] when
    either [V] ends in a successor or the last exponent is matched. *)

Lemma pin_exact : forall V X,
  mwf V -> mwf X -> V <> MZ ->
  mlt (mdec V) X -> mle X V ->
  (mell V = MZ \/ mell X = mell V) ->
  X = V.
Proof.
  induction V as [|e IHe t IHt]; intros X HV HX Hnz Hlo Hhi Hside;
    [congruence|].
  destruct HV as [He [Ht Hd]].
  destruct t as [|e' t'].
  - (* V = omega^e *)
    destruct X as [|ex tx]; [destruct (not_mlt_MZ _ Hlo) | ].
    apply mle_iff in Hhi as [Hlt | Heq]; [|exact Heq].
    destruct (mlt_MC_inv _ _ _ _ Hlt) as [Hh | [Heq' Htl]].
    + (* head drop: contradict the side condition *)
      exfalso.
      destruct Hside as [Hz | Hm].
      * cbn in Hz. subst e. destruct (not_mlt_MZ _ Hh).
      * destruct HX as [Hex [Htx Hdx]].
        pose proof (mell_le_head (MC ex tx)
                      (conj Hex (conj Htx Hdx))) as Hle.
        cbn [mhead] in Hle. rewrite Hm in Hle.
        cbn [mell] in Hle.
        exact (mlt_irrefl e (mle_lt_trans _ _ _ Hle Hh)).
    + subst ex. destruct (not_mlt_MZ _ Htl).
  - (* V = MC e (MC e' t') *)
    change (mdec (MC e (MC e' t'))) with (MC e (mdec (MC e' t'))) in Hlo.
    destruct X as [|ex tx]; [destruct (not_mlt_MZ _ Hlo)|].
    destruct HX as [Hex [Htx Hdx]].
    destruct (mlt_MC_inv _ _ _ _ Hlo) as [Hh | [Heq Htl]].
    + (* e < ex: contradicts X <= V *)
      exfalso.
      apply mle_iff in Hhi as [Hlt | Heq].
      * destruct (mlt_MC_inv _ _ _ _ Hlt) as [Hh' | [Heq' _]].
        -- exact (mlt_irrefl e (mlt_trans _ _ _ Hh Hh')).
        -- subst ex. exact (mlt_irrefl e Hh).
      * injection Heq as He' Ht'. subst ex.
        exact (mlt_irrefl e Hh).
    + subst ex.
      assert (Htxle : mle tx (MC e' t')).
      { apply mle_iff in Hhi as [Hlt | Heq].
        - destruct (mlt_MC_inv _ _ _ _ Hlt) as [Hh' | [_ Htl']].
          + exfalso. exact (mlt_irrefl e Hh').
          + apply mlt_le. exact Htl'.
        - injection Heq as Ht'. subst tx. apply mle_refl. }
      assert (Htxnz : tx <> MZ).
      { intro Hz. subst tx. destruct (not_mlt_MZ _ Htl). }
      assert (Hside' : mell (MC e' t') = MZ \/ mell tx = mell (MC e' t')).
      { destruct Hside as [Hz | Hm].
        - left. rewrite (mell_MC_cons e e' t') in Hz. exact Hz.
        - right.
          rewrite (mell_MC_cons e e' t') in Hm.
          rewrite <- Hm.
          destruct tx as [|fx ux]; [congruence|].
          rewrite (mell_MC_cons e fx ux). reflexivity. }
      pose proof (IHt tx Ht Htx ltac:(congruence) Htl Htxle Hside') as Heqt.
      subst tx. reflexivity.
Qed.

Lemma mord_eq_dec : forall a b : mord, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Lemma mellk_S_alt : forall k y, mellk (S k) y = mell (mellk k y).
Proof.
  intros k y.
  rewrite <- Nat.add_1_r, mellk_add. reflexivity.
Qed.

(** ** The pin depth: the deepest level at or below [n] with a nonzero
    iterated logarithm. *)

Fixpoint pin_depth (n : nat) (x : mord) : nat :=
  match n with
  | 0 => 0
  | S m => if mord_eq_dec (mell x) MZ then 0 else S (pin_depth m (mell x))
  end.

Lemma pin_depth_spec : forall n x,
  x <> MZ -> mellk (S n) x = MZ ->
  pin_depth n x <= n /\
  mellk (pin_depth n x) x <> MZ /\
  mellk (S (pin_depth n x)) x = MZ.
Proof.
  induction n as [|m IH]; intros x Hnz Hz.
  - cbn. auto.
  - cbn [pin_depth].
    destruct (mord_eq_dec (mell x) MZ) as [He | He].
    + split; [lia|]. split; [exact Hnz|].
      cbn. exact He.
    + destruct (IH (mell x) He Hz) as [H1 [H2 H3]].
      split; [lia|]. split.
      * exact H2.
      * exact H3.
Qed.

(** ** The pinning constraint list and member absence. *)

Definition pins (d : nat) (x : mord) : list (nat * mord) :=
  map (fun k => (k, mdec (mellk k x))) (seq 0 (S d)).

Lemma pins_in : forall d x p,
  In p (pins d x) <-> exists k, k <= d /\ p = (k, mdec (mellk k x)).
Proof.
  intros d x p. unfold pins. rewrite in_map_iff.
  split.
  - intros [k [Heq Hin]]. apply in_seq in Hin.
    exists k. split; [lia | now subst].
  - intros [k [Hk ->]]. exists k. split; [reflexivity|].
    apply in_seq. lia.
Qed.

Lemma member_absent : forall n x,
  mwf x -> mellk (S n) x = MZ ->
  exists gs, iclegit n x gs /\ forall z, ~ icmember n x gs z.
Proof.
  intros n x Hwf Hz.
  destruct (mord_eq_dec x MZ) as [-> | Hnz].
  - exists []. split.
    + intros p Hp. destruct Hp.
    + intros z [Hzw [Hlt _]]. exact (not_mlt_MZ _ Hlt).
  - destruct (pin_depth_spec n x Hnz Hz) as [Hd1 [Hd2 Hd3]].
    set (d := pin_depth n x) in *.
    exists (pins d x).
    assert (Hnzk : forall k, k <= d -> mellk k x <> MZ).
    { intros k Hk. apply (mellk_nonzero_down k d x Hk Hd2). }
    split.
    + intros p Hp. apply pins_in in Hp.
      destruct Hp as [k [Hk ->]]. cbn.
      split; [lia|]. split.
      * apply mdec_wf. apply mellk_wf. exact Hwf.
      * apply mdec_lt. apply Hnzk. exact Hk.
    + intros z [Hzw [Hlt [Hup Hgs]]].
      (* downward exactness from level d to level 0 *)
      assert (Hexact : forall j, j <= d -> mellk (d - j) z = mellk (d - j) x).
      { induction j as [|j IHj]; intro Hj.
        - rewrite Nat.sub_0_r.
          apply (pin_exact (mellk d x) (mellk d z)).
          + apply mellk_wf. exact Hwf.
          + apply mellk_wf. exact Hzw.
          + exact Hd2.
          + refine (Hgs (d, mdec (mellk d x)) _).
            apply pins_in. exists d. split; [lia | reflexivity].
          + apply Hup. lia.
          + left. rewrite <- mellk_S_alt. exact Hd3.
        - set (k := d - S j).
          assert (HSk : S k = d - j) by lia.
          apply (pin_exact (mellk k x) (mellk k z)).
          + apply mellk_wf. exact Hwf.
          + apply mellk_wf. exact Hzw.
          + apply Hnzk. lia.
          + refine (Hgs (k, mdec (mellk k x)) _).
            apply pins_in. exists k. split; [lia | reflexivity].
          + apply Hup. lia.
          + right.
            rewrite <- !mellk_S_alt, HSk.
            apply IHj. lia. }
      pose proof (Hexact d (Nat.le_refl d)) as Hz0.
      rewrite Nat.sub_diag in Hz0. cbn in Hz0.
      subst z. exact (mlt_irrefl x Hlt).
Qed.

(** ** The tail cap: inside the open interval [(mdec V, V)], last
    exponents drop strictly. *)

Lemma cap_lemma : forall V X,
  mwf V -> mwf X -> V <> MZ ->
  mlt (mdec V) X -> mlt X V ->
  mlt (mell X) (mell V).
Proof.
  induction V as [|e IHe t IHt]; intros X HV HX Hnz Hlo Hhi; [congruence|].
  destruct HV as [He [Ht Hd]].
  destruct t as [|e' t'].
  - (* V = omega^e; X in (MZ, omega^e) *)
    destruct X as [|ex tx]; [destruct (not_mlt_MZ _ Hlo)|].
    destruct (mlt_MC_inv _ _ _ _ Hhi) as [Hh | [Heq Htl]].
    + (* head ex < e; mell X <= head X = ex < e = mell V *)
      destruct HX as [Hex [Htx Hdx]].
      pose proof (mell_le_head (MC ex tx) (conj Hex (conj Htx Hdx))) as Hle.
      cbn [mhead] in Hle. cbn [mell].
      eapply mle_lt_trans; [exact Hle | exact Hh].
    + subst ex. destruct (not_mlt_MZ _ Htl).
  - (* V = MC e (MC e' t') *)
    change (mdec (MC e (MC e' t'))) with (MC e (mdec (MC e' t'))) in Hlo.
    destruct X as [|ex tx]; [destruct (not_mlt_MZ _ Hlo)|].
    destruct (mlt_MC_inv _ _ _ _ Hlo) as [Hh | [Heq Htl]].
    + (* e < ex contradicts X < V *)
      exfalso.
      destruct (mlt_MC_inv _ _ _ _ Hhi) as [Hh' | [Heq' _]].
      * exact (mlt_irrefl e (mlt_trans _ _ _ Hh Hh')).
      * subst ex. exact (mlt_irrefl e Hh).
    + subst ex.
      destruct (mlt_MC_inv _ _ _ _ Hhi) as [Hh' | [_ Htl']].
      * exfalso. exact (mlt_irrefl e Hh').
      * destruct HX as [Hex [Htx Hdx]].
        assert (Htxnz : tx <> MZ).
        { intro Hz. subst tx. destruct (not_mlt_MZ _ Htl). }
        rewrite (mell_MC_cons e e' t').
        destruct tx as [|fx ux]; [congruence|].
        rewrite (mell_MC_cons e fx ux).
        exact (IHt (MC fx ux) Ht Htx ltac:(congruence) Htl Htl').
Qed.

(** ** The chain with a prescribed deep exponent. *)

Lemma chain_mu : forall n y (g : nat -> mord) mu,
  mwf y -> mwf mu ->
  mlt mu (mellk (S n) y) ->
  (forall k, k <= n -> mwf (g k) /\ mlt (g k) (mellk k y)) ->
  exists z, mwf z /\
    mellk (S n) z = mu /\
    (forall k, k <= n ->
       mlt (g k) (mellk k z) /\ mlt (mellk k z) (mellk k y)).
Proof.
  induction n as [|m IH]; intros y g mu Hwf Hmu Hlt Hg.
  - destruct (Hg 0 (Nat.le_refl 0)) as [Hg0 Hlt0].
    cbn in Hlt0.
    destruct (master_density y (g 0) mu Hwf Hg0 Hmu Hlt0 Hlt)
      as [B [HB1 [HB2 [HB3 HB4]]]].
    exists B. split; [exact HB1|]. split.
    + cbn. exact HB4.
    + intros k Hk. assert (k = 0) by lia. subst k.
      cbn. exact (conj HB2 HB3).
  - destruct (IH (mell y) (fun k => g (S k)) mu (mell_wf y Hwf) Hmu Hlt
                (fun k Hk => Hg (S k) (le_n_S _ _ Hk)))
      as [w [Hww [Hwmu Hwprops]]].
    destruct (Hg 0 (Nat.le_0_l _)) as [Hg0 Hlt0].
    cbn in Hlt0.
    assert (Hwlt : mlt w (mell y)).
    { exact (proj2 (Hwprops 0 (Nat.le_0_l _))). }
    destruct (master_density y (g 0) w Hwf Hg0 Hww Hlt0 Hwlt)
      as [B [HB1 [HB2 [HB3 HB4]]]].
    exists B. split; [exact HB1|]. split.
    + cbn [mellk]. rewrite HB4. exact Hwmu.
    + intros k Hk. destruct k as [|j].
      * cbn. exact (conj HB2 HB3).
      * cbn [mellk]. rewrite HB4.
        exact (Hwprops j (le_S_n _ _ Hk)).
Qed.

(** ** The polymodal language and the extended calculus (scratch
    copies; the spliced version reuses Tiling.v's own definitions). *)

Inductive Form : Type :=
  | Var  : nat -> Form
  | Bot  : Form
  | Impl : Form -> Form -> Form
  | Box  : nat -> Form -> Form.

Definition Neg (phi : Form) : Form := Impl phi Bot.
Definition Top : Form := Impl Bot Bot.
Definition Diamond (n : nat) (phi : Form) : Form := Neg (Box n (Neg phi)).

Inductive Provable : Form -> Prop :=
  | Ax_K   : forall phi psi,
      Provable (Impl phi (Impl psi phi))
  | Ax_S   : forall phi psi chi,
      Provable (Impl (Impl phi (Impl psi chi))
                     (Impl (Impl phi psi) (Impl phi chi)))
  | Ax_DN  : forall phi,
      Provable (Impl (Neg (Neg phi)) phi)
  | Ax_BoxK : forall n phi psi,
      Provable (Impl (Box n (Impl phi psi))
                     (Impl (Box n phi) (Box n psi)))
  | Ax_Loeb : forall n phi,
      Provable (Impl (Box n (Impl (Box n phi) phi)) (Box n phi))
  | Ax_Box4 : forall n phi,
      Provable (Impl (Box n phi) (Box n (Box n phi)))
  | Ax_Mon  : forall n phi,
      Provable (Impl (Box n phi) (Box (S n) phi))
  | Ax_NextCon : forall n,
      Provable (Box (S n) (Neg (Box n Bot)))
  | Ax_J : forall n phi,
      Provable (Impl (Diamond n phi) (Box (S n) (Diamond n phi)))
  | MP : forall phi psi,
      Provable (Impl phi psi) -> Provable phi -> Provable psi
  | Nec : forall n phi,
      Provable phi -> Provable (Box n phi).

(** ** Forcing over the Icard-style neighborhoods. *)

Fixpoint icforces (x : mord) (phi : Form) : Prop :=
  match phi with
  | Var _ => True
  | Bot => False
  | Impl a b => icforces x a -> icforces x b
  | Box n psi =>
      exists gs, iclegit n x gs /\
        forall y, icmember n x gs y -> icforces y psi
  end.

(** Structural facts about membership. *)

Lemma iclegit_app : forall n x gs1 gs2,
  iclegit n x gs1 -> iclegit n x gs2 -> iclegit n x (gs1 ++ gs2).
Proof.
  intros n x gs1 gs2 H1 H2 p Hp.
  apply in_app_or in Hp. destruct Hp as [Hp | Hp]; [exact (H1 _ Hp) | exact (H2 _ Hp)].
Qed.

Lemma icmember_app_l : forall n x gs1 gs2 y,
  icmember n x (gs1 ++ gs2) y -> icmember n x gs1 y.
Proof.
  intros n x gs1 gs2 y [Hw [Hlt [Hup Hgs]]].
  repeat split; try assumption.
  intros p Hp. apply Hgs. apply in_or_app. now left.
Qed.

Lemma icmember_app_r : forall n x gs1 gs2 y,
  icmember n x (gs1 ++ gs2) y -> icmember n x gs2 y.
Proof.
  intros n x gs1 gs2 y [Hw [Hlt [Hup Hgs]]].
  repeat split; try assumption.
  intros p Hp. apply Hgs. apply in_or_app. now right.
Qed.

Lemma iclegit_member : forall n x gs y,
  icmember n x gs y -> iclegit n x gs -> iclegit n y gs.
Proof.
  intros n x gs y [Hw [Hlt [Hup Hgs]]] Hleg p Hp.
  destruct (Hleg p Hp) as [Hk [Hwp _]].
  repeat split; try assumption.
  exact (Hgs p Hp).
Qed.

Lemma icmember_trans : forall n x gs y z,
  icmember n x gs y -> icmember n y gs z -> icmember n x gs z.
Proof.
  intros n x gs y z [Hw1 [Hlt1 [Hup1 Hgs1]]] [Hw2 [Hlt2 [Hup2 Hgs2]]].
  repeat split; try assumption.
  - exact (mlt_trans _ _ _ Hlt2 Hlt1).
  - intros k Hk. eapply mle_trans; [exact (Hup2 k Hk) | exact (Hup1 k Hk)].
Qed.

Lemma icmember_mon : forall n x gs y,
  icmember (S n) x gs y -> icmember n x gs y.
Proof.
  intros n x gs y [Hw [Hlt [Hup Hgs]]].
  repeat split; try assumption.
  intros k Hk. apply Hup. lia.
Qed.

Lemma iclegit_mon : forall n x gs,
  iclegit n x gs -> iclegit (S n) x gs.
Proof.
  intros n x gs H p Hp.
  destruct (H p Hp) as [Hk [Hw Hl]].
  repeat split; try assumption. lia.
Qed.

(** ** Validity of the axioms on the model: the easy cases. *)

Lemma ic_boxk : forall n phi psi x,
  icforces x (Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi))).
Proof.
  intros n phi psi x. cbn.
  intros [gs1 [Hl1 Hm1]] [gs2 [Hl2 Hm2]].
  exists (gs1 ++ gs2).
  split; [exact (iclegit_app _ _ _ _ Hl1 Hl2)|].
  intros y Hy.
  exact (Hm1 y (icmember_app_l _ _ _ _ _ Hy)
             (Hm2 y (icmember_app_r _ _ _ _ _ Hy))).
Qed.

Lemma ic_loeb : forall n phi x,
  icforces x (Impl (Box n (Impl (Box n phi) phi)) (Box n phi)).
Proof.
  intros n phi x. cbn.
  intros [gs [Hleg Hmem]].
  exists gs. split; [exact Hleg|].
  intros y Hy.
  revert Hy.
  induction y as [y IH] using (well_founded_induction mR_wf).
  intro Hy.
  apply (Hmem y Hy).
  exists gs.
  split; [exact (iclegit_member _ _ _ _ Hy Hleg)|].
  intros z Hz.
  apply IH.
  - split; [exact (proj1 Hz) | exact (proj1 (proj2 Hz))].
  - exact (icmember_trans _ _ _ _ _ Hy Hz).
Qed.

Lemma ic_box4 : forall n phi x,
  icforces x (Impl (Box n phi) (Box n (Box n phi))).
Proof.
  intros n phi x. cbn.
  intros [gs [Hleg Hmem]].
  exists gs. split; [exact Hleg|].
  intros y Hy.
  exists gs.
  split; [exact (iclegit_member _ _ _ _ Hy Hleg)|].
  intros z Hz.
  exact (Hmem z (icmember_trans _ _ _ _ _ Hy Hz)).
Qed.

Lemma ic_mon : forall n phi x,
  icforces x (Impl (Box n phi) (Box (S n) phi)).
Proof.
  intros n phi x. cbn.
  intros [gs [Hleg Hmem]].
  exists gs.
  split; [exact (iclegit_mon _ _ _ Hleg)|].
  intros y Hy.
  exact (Hmem y (icmember_mon _ _ _ _ Hy)).
Qed.

(** ** Cells: finite constraint sets on iterated logarithms. *)

Definition constraint : Type := (nat * bool * mord)%type.

Definition csat (y : mord) (c : constraint) : Prop :=
  let '(k, b, gamma) := c in
  if b then mlt gamma (mellk k y) else mle (mellk k y) gamma.

Definition cell : Type := list constraint.

Definition cellsem (y : mord) (c : cell) : Prop :=
  forall p, In p c -> csat y p.

Definition cunion : Type := list cell.

Definition usem (y : mord) (U : cunion) : Prop :=
  exists c, In c U /\ cellsem y c.

Definition cwf (c : cell) : Prop :=
  forall p, In p c -> mwf (snd p).

Definition uwf (U : cunion) : Prop :=
  forall c, In c U -> cwf c.

Lemma csat_dec : forall y p, csat y p \/ ~ csat y p.
Proof.
  intros y [[k b] gamma]. cbn.
  destruct b; unfold mlt, mle;
    destruct (mcmp gamma (mellk k y)) eqn:H1;
    destruct (mcmp (mellk k y) gamma) eqn:H2;
    intuition congruence.
Qed.

Lemma cellsem_dec_neg : forall y c,
  ~ cellsem y c -> exists p, In p c /\ ~ csat y p.
Proof.
  induction c as [|p c IH]; intro Hn.
  - exfalso. apply Hn. intros q Hq. destruct Hq.
  - destruct (csat_dec y p) as [Hp | Hp].
    + destruct IH as [q [Hq1 Hq2]].
      * intro Hc. apply Hn. intros q Hq.
        destruct Hq as [<- | Hq]; [exact Hp | exact (Hc q Hq)].
      * exists q. split; [now right | exact Hq2].
    + exists p. split; [now left | exact Hp].
Qed.

(** Negation of a single constraint. *)

Definition cneg (p : constraint) : constraint :=
  let '(k, b, gamma) := p in (k, negb b, gamma).

Lemma not_mlt_iff : forall a b, ~ mlt a b <-> mle b a.
Proof.
  intros a b. unfold mlt, mle.
  rewrite (mcmp_antisym b a).
  destruct (mcmp a b); cbn; intuition congruence.
Qed.

Lemma csat_cneg : forall y p, csat y (cneg p) <-> ~ csat y p.
Proof.
  intros y [[k b] gamma]. destruct b; cbn.
  - split.
    + intros H1 H2. apply (not_mlt_iff gamma (mellk k y)); assumption.
    + intro H. apply not_mlt_iff in H. exact H.
  - split.
    + intros H1 H2.
      apply (not_mlt_iff gamma (mellk k y)) in H2. exact (H2 H1).
    + intro H.
      destruct (mlt_total gamma (mellk k y)) as [Hl | [He | Hg]].
      * exact Hl.
      * exfalso. apply H. subst. apply mle_refl.
      * exfalso. apply H. apply mlt_le. exact Hg.
Qed.

Lemma cneg_wf : forall p, mwf (snd p) -> mwf (snd (cneg p)).
Proof. intros [[k b] gamma] H. exact H. Qed.

(** Complement of a union of cells (DNF complementation). *)

Fixpoint compl (U : cunion) : cunion :=
  match U with
  | [] => [[]]
  | c :: U' => flat_map (fun p => map (cons (cneg p)) (compl U')) c
  end.

Lemma compl_correct : forall U y,
  usem y (compl U) <-> ~ usem y U.
Proof.
  induction U as [|c U IH]; intro y; cbn [compl].
  - split.
    + intros _ [c [Hc _]]. destruct Hc.
    + intros _. exists []. split; [now left|].
      intros p Hp. destruct Hp.
  - split.
    + intros [d [Hd Hsem]] Hu.
      apply in_flat_map in Hd.
      destruct Hd as [p [Hp Hd]].
      apply in_map_iff in Hd.
      destruct Hd as [d' [<- Hd']].
      destruct Hu as [c0 [Hc0 Hsem0]].
      destruct Hc0 as [<- | Hc0].
      * pose proof (Hsem (cneg p) (or_introl eq_refl)) as Hnp.
        apply csat_cneg in Hnp.
        exact (Hnp (Hsem0 p Hp)).
      * apply (proj1 (IH y)).
        -- exists d'. split; [exact Hd'|].
           intros q Hq. apply Hsem. now right.
        -- exists c0. split; assumption.
    + intro Hn.
      assert (Hnc : ~ cellsem y c).
      { intro Hc. apply Hn. exists c. split; [now left | exact Hc]. }
      assert (HnU : ~ usem y U).
      { intros [c0 [Hc0 Hs0]]. apply Hn. exists c0. split; [now right | exact Hs0]. }
      apply cellsem_dec_neg in Hnc.
      destruct Hnc as [p [Hp Hnp]].
      apply (proj2 (IH y)) in HnU.
      destruct HnU as [d [Hd Hsd]].
      exists (cneg p :: d).
      split.
      * apply in_flat_map. exists p. split; [exact Hp|].
        apply in_map_iff. exists d. split; [reflexivity | exact Hd].
      * intros q Hq. destruct Hq as [<- | Hq].
        -- apply csat_cneg. exact Hnp.
        -- exact (Hsd q Hq).
Qed.

Lemma compl_wf : forall U, uwf U -> uwf (compl U).
Proof.
  induction U as [|c U IH]; intros HU d Hd.
  - cbn in Hd. destruct Hd as [<- | []].
    intros p Hp. destruct Hp.
  - cbn in Hd. apply in_flat_map in Hd.
    destruct Hd as [p [Hp Hd]].
    apply in_map_iff in Hd.
    destruct Hd as [d' [<- Hd']].
    intros q Hq. destruct Hq as [<- | Hq].
    + apply cneg_wf.
      exact (HU c (or_introl eq_refl) p Hp).
    + refine (IH _ d' Hd' q Hq).
      intros c0 Hc0. exact (HU c0 (or_intror Hc0)).
Qed.

(** Union of unions is append; both semantics lemmas are immediate. *)

Lemma usem_app : forall y U1 U2,
  usem y (U1 ++ U2) <-> usem y U1 \/ usem y U2.
Proof.
  intros y U1 U2. split.
  - intros [c [Hc Hs]]. apply in_app_or in Hc.
    destruct Hc as [Hc | Hc]; [left | right]; now exists c.
  - intros [[c [Hc Hs]] | [c [Hc Hs]]]; exists c;
      (split; [apply in_or_app; auto | exact Hs]).
Qed.

Lemma uwf_app : forall U1 U2, uwf U1 -> uwf U2 -> uwf (U1 ++ U2).
Proof.
  intros U1 U2 H1 H2 c Hc.
  apply in_app_or in Hc. destruct Hc as [Hc | Hc]; [exact (H1 _ Hc) | exact (H2 _ Hc)].
Qed.

(** ** The least ordinal above a bound with a prescribed last exponent. *)

Fixpoint mup (c mu : mord) : mord :=
  match c with
  | MZ => MC mu MZ
  | MC e t =>
      match mcmp mu e with
      | Gt => MC mu MZ
      | _ => MC e (mup t mu)
      end
  end.

Lemma mup_nonzero : forall c mu, mup c mu <> MZ.
Proof.
  intros [|e t] mu; cbn; [congruence|].
  destruct (mcmp mu e); congruence.
Qed.

Lemma mup_wf : forall c mu, mwf c -> mwf mu -> mwf (mup c mu).
Proof.
  induction c as [|e IHe t IHt]; intros mu Hc Hmu.
  - cbn. repeat split; [exact Hmu | apply mZ_le].
  - destruct Hc as [He [Ht Hd]].
    cbn [mup]. destruct (mcmp mu e) eqn:Hcmp.
    + (* mu = e *)
      apply mcmp_eq_iff in Hcmp. subst mu.
      cbn [mwf]. split; [exact He|]. split; [apply IHt; assumption|].
      destruct t as [|e' t'].
      * cbn. apply mle_refl.
      * cbn [mup]. destruct (mcmp e e') eqn:H1; cbn [mhead].
        -- apply mcmp_eq_iff in H1. subst e'. apply mle_refl.
        -- cbn in Hd. exact Hd.
        -- apply mle_refl.
    + (* mu < e *)
      cbn [mwf]. split; [exact He|]. split; [apply IHt; assumption|].
      destruct t as [|e' t'].
      * cbn. apply mlt_le. exact Hcmp.
      * cbn [mup]. destruct (mcmp mu e') eqn:H1; cbn [mhead].
        -- cbn in Hd. exact Hd.
        -- cbn in Hd. exact Hd.
        -- apply mlt_le. exact Hcmp.
    + cbn. repeat split; [exact Hmu | apply mZ_le].
Qed.

Lemma mup_gt : forall c mu, mwf c -> mlt c (mup c mu).
Proof.
  induction c as [|e IHe t IHt]; intros mu Hc.
  - cbn. apply mlt_MZ. congruence.
  - destruct Hc as [He [Ht Hd]].
    cbn [mup]. destruct (mcmp mu e) eqn:Hcmp.
    + apply mlt_MC_tail. apply IHt. exact Ht.
    + apply mlt_MC_tail. apply IHt. exact Ht.
    + apply mlt_MC_head. unfold mlt.
      rewrite mcmp_antisym, Hcmp. reflexivity.
Qed.

Lemma mup_mell : forall c mu, mell (mup c mu) = mu.
Proof.
  induction c as [|e IHe t IHt]; intros mu.
  - reflexivity.
  - cbn [mup]. destruct (mcmp mu e) eqn:Hcmp.
    + pose proof (mup_nonzero t mu) as Hnz.
      destruct (mup t mu) as [|eu tu] eqn:Hu; [congruence|].
      rewrite (mell_MC_cons e eu tu). rewrite <- Hu. apply IHt.
    + pose proof (mup_nonzero t mu) as Hnz.
      destruct (mup t mu) as [|eu tu] eqn:Hu; [congruence|].
      rewrite (mell_MC_cons e eu tu). rewrite <- Hu. apply IHt.
    + reflexivity.
Qed.

(** The single-term lower bound through the last exponent. *)

Lemma mell_pow_le : forall X, mwf X -> X <> MZ -> mle (MC (mell X) MZ) X.
Proof.
  induction X as [|e IHe t IHt]; intros HX Hnz; [congruence|].
  destruct HX as [He [Ht Hd]].
  destruct t as [|e' t'].
  - cbn. apply mle_refl.
  - rewrite (mell_MC_cons e e' t').
    assert (Hle : mle (mell (MC e' t')) e).
    { eapply mle_trans.
      - exact (mell_le_head (MC e' t') Ht).
      - cbn [mhead] in Hd |- *. exact Hd. }
    apply mle_iff in Hle as [Hlt | Heq].
    + apply mlt_le. apply mlt_MC_head. exact Hlt.
    + rewrite Heq. unfold mle. cbn. rewrite mcmp_refl.
      congruence.
Qed.

Lemma mle_pow_mono : forall a b, mle a b -> mle (MC a MZ) (MC b MZ).
Proof.
  intros a b H. unfold mle in *. cbn.
  destruct (mcmp a b) eqn:Hc; cbn; congruence.
Qed.

(** Monotone leastness of [mup]. *)

Lemma mup_least : forall c X mu,
  mwf c -> mwf X ->
  mlt c X -> mle mu (mell X) ->
  mle (mup c mu) X.
Proof.
  induction c as [|e IHe t IHt]; intros X mu Hc HX Hlt Hmell.
  - (* mup = omega^mu <= omega^(mell X) <= X *)
    cbn [mup].
    assert (Hnz : X <> MZ).
    { intro Hz. subst X. destruct (not_mlt_MZ _ Hlt). }
    eapply mle_trans; [apply mle_pow_mono; exact Hmell|].
    apply mell_pow_le; assumption.
  - destruct Hc as [He [Ht Hd]].
    assert (Hnz : X <> MZ).
    { intro Hz. subst X. destruct (not_mlt_MZ _ Hlt). }
    cbn [mup]. destruct (mcmp mu e) eqn:Hcmp.
    + (* mu = e; keep head *)
      apply mcmp_eq_iff in Hcmp. subst mu.
      destruct X as [|ex tx]; [congruence|].
      destruct (mlt_MC_inv _ _ _ _ Hlt) as [Hh | [Heq Htl]].
      * apply mlt_le. apply mlt_MC_head. exact Hh.
      * subst ex.
        assert (Htxnz : tx <> MZ).
        { intro Hz. subst tx. destruct (not_mlt_MZ _ Htl). }
        destruct HX as [Hex [Htx Hdx]].
        assert (Hmtx : mle e (mell tx)).
        { destruct tx as [|fx ux]; [congruence|].
          rewrite (mell_MC_cons e fx ux) in Hmell. exact Hmell. }
        assert (Hle : mle (mup t e) tx).
        { apply IHt; assumption. }
        unfold mle. cbn. rewrite mcmp_refl.
        exact Hle.
    + (* mu < e; keep head *)
      destruct X as [|ex tx]; [congruence|].
      destruct (mlt_MC_inv _ _ _ _ Hlt) as [Hh | [Heq Htl]].
      * apply mlt_le. apply mlt_MC_head. exact Hh.
      * subst ex.
        assert (Htxnz : tx <> MZ).
        { intro Hz. subst tx. destruct (not_mlt_MZ _ Htl). }
        destruct HX as [Hex [Htx Hdx]].
        assert (Hmtx : mle mu (mell tx)).
        { destruct tx as [|fx ux]; [congruence|].
          rewrite (mell_MC_cons e fx ux) in Hmell. exact Hmell. }
        assert (Hle : mle (mup t mu) tx).
        { apply IHt; assumption. }
        unfold mle. cbn. rewrite mcmp_refl.
        exact Hle.
    + (* mu > e: mup = omega^mu; X > c with mell X >= mu > e >= head-of-c *)
      assert (Hnz2 : X <> MZ) by exact Hnz.
      eapply mle_trans; [apply mle_pow_mono; exact Hmell|].
      apply mell_pow_le; assumption.
Qed.

Lemma ic_nextcon : forall n x,
  mwf x ->
  icforces x (Box (S n) (Neg (Box n Bot))).
Proof.
  intros n x Hwf. cbn.
  destruct (mord_eq_dec (mellk (S (S n)) x) MZ) as [Hz | Hnz].
  - (* vacuous neighborhood *)
    destruct (member_absent (S n) x Hwf Hz) as [gs [Hleg Hnone]].
    exists gs. split; [exact Hleg|].
    intros y Hy. destruct (Hnone y Hy).
  - (* constrain level (S n) strictly above zero *)
    exists [(S n, MZ)].
    split.
    { intros p Hp. destruct Hp as [<- | []].
      cbn. split; [lia|]. split; [exact I|].
      apply mlt_MZ.
      apply (mellk_nonzero_down (S n) (S (S n)) x); [lia | exact Hnz]. }
    intros y [Hyw [Hylt [Hyup Hygs]]] [gs' [Hleg' Hmem']].
    pose proof (Hygs (S n, MZ) (or_introl eq_refl)) as HySn.
    cbn [fst snd] in HySn.
    assert (HySnz : mellk (S n) y <> MZ).
    { intro Hz. rewrite Hz in HySn. exact (not_mlt_MZ _ HySn). }
    destruct (member_exists n y gs' Hyw HySnz Hleg') as [z Hz].
    exact (Hmem' z Hz).
Qed.

(** ** Reachability of a set from a point. *)

Definition icreach (n : nat) (x : mord) (A : mord -> Prop) : Prop :=
  forall gs, iclegit n x gs -> exists y, icmember n x gs y /\ A y.

(** ** The strict cascade under full pins. *)

Lemma pins_cap : forall n x y,
  mwf x -> mellk (S n) x <> MZ ->
  icmember n x (pins n x) y ->
  forall k, k <= n -> mlt (mellk (S k) y) (mellk (S k) x).
Proof.
  intros n x y Hwf Hnz [Hyw [Hylt [Hyup Hygs]]].
  assert (Hvk : forall k, k <= S n -> mellk k x <> MZ).
  { intros k Hk. apply (mellk_nonzero_down k (S n) x); [lia | exact Hnz]. }
  assert (Hpin : forall k, k <= n -> mlt (mdec (mellk k x)) (mellk k y)).
  { intros k Hk.
    refine (Hygs (k, mdec (mellk k x)) _).
    apply pins_in. exists k. split; [lia | reflexivity]. }
  induction k as [|k IHk]; intro Hk.
  - (* level 1 from the level-0 pin *)
    rewrite !mellk_S_alt. cbn [mellk].
    apply cap_lemma; try assumption.
    + exact (Hvk 0 (Nat.le_0_l _)).
    + exact (Hpin 0 (Nat.le_0_l _)).
  - (* level S (S k) from the level-(S k) pin and strictness at S k *)
    rewrite (mellk_S_alt (S k) y), (mellk_S_alt (S k) x).
    apply cap_lemma.
    + apply mellk_wf. exact Hwf.
    + apply mellk_wf. exact Hyw.
    + apply Hvk. lia.
    + exact (Hpin (S k) Hk).
    + exact (IHk ltac:(lia)).
Qed.

(** ** Deep bounds of a cell relative to a threshold level. *)

Definition dlow (c : cell) (s j : nat) : mord :=
  fold_right (fun p acc =>
    let '(k, b, g) := p in
    if andb b (Nat.eqb k (s + j)) then mmax g acc else acc) MZ c.

Lemma dlow_wf : forall c s j, cwf c -> mwf (dlow c s j).
Proof.
  induction c as [|[[k b] g] c IH]; intros s j Hc; cbn; [exact I|].
  destruct (andb b (Nat.eqb k (s + j))) eqn:Hb.
  - apply mmax_wf.
    + exact (Hc _ (or_introl eq_refl)).
    + apply IH. intros p Hp. exact (Hc _ (or_intror Hp)).
  - apply IH. intros p Hp. exact (Hc _ (or_intror Hp)).
Qed.

Lemma dlow_ge : forall c s j g,
  In (s + j, true, g) c -> mle g (dlow c s j).
Proof.
  induction c as [|[[k b] g'] c IH]; intros s j g Hin; [destruct Hin|].
  destruct Hin as [Heq | Hin].
  - injection Heq as -> -> ->. cbn.
    rewrite Nat.eqb_refl. cbn.
    apply mmax_le_l.
  - cbn. destruct (andb b (Nat.eqb k (s + j))) eqn:Hb.
    + eapply mle_trans; [exact (IH _ _ _ Hin) | apply mmax_le_r].
    + exact (IH _ _ _ Hin).
Qed.

(** If every deep lower bound at shifted level [j] is strictly below
    [W], and [W] is nonzero, then [dlow] is strictly below [W]. *)

Lemma dlow_lt : forall c s j W,
  (forall g, In (s + j, true, g) c -> mlt g W) ->
  W <> MZ ->
  mlt (dlow c s j) W.
Proof.
  induction c as [|[[k b] g'] c IH]; intros s j W Hin Hnz; cbn.
  - apply mlt_MZ. exact Hnz.
  - destruct b; cbn.
    + destruct (Nat.eqb k (s + j)) eqn:He; cbn.
      * apply Nat.eqb_eq in He. subst k.
        apply mmax_lub.
        -- exact (Hin _ (or_introl eq_refl)).
        -- apply IH; [|exact Hnz].
           intros g Hg. exact (Hin _ (or_intror Hg)).
      * apply IH; [|exact Hnz].
        intros g Hg. exact (Hin _ (or_intror Hg)).
    + apply IH; [|exact Hnz].
      intros g Hg. exact (Hin _ (or_intror Hg)).
Qed.

(** Deepest shifted level carrying a deep lower constraint; upper
    constraints force no growth of the witness. *)

Definition ddepth (c : cell) (s : nat) : nat :=
  fold_right (fun p acc =>
    let '(k, b, g) := p in
    if andb b (Nat.leb s k) then Nat.max (k - s) acc else acc) 0 c.

Lemma ddepth_ge : forall c s k g,
  In (k, true, g) c -> s <= k -> k - s <= ddepth c s.
Proof.
  induction c as [|[[k' b'] g'] c IH]; intros s k g Hin Hs; [destruct Hin|].
  destruct Hin as [Heq | Hin].
  - injection Heq as -> -> ->. cbn.
    apply Nat.leb_le in Hs. rewrite Hs. cbn.
    apply Nat.le_max_l.
  - cbn. destruct (andb b' (Nat.leb s k')) eqn:Hk'.
    + eapply Nat.le_trans; [exact (IH _ _ _ Hin Hs) | apply Nat.le_max_r].
    + exact (IH _ _ _ Hin Hs).
Qed.

Definition has_dlow (c : cell) (s : nat) : bool :=
  existsb (fun p => let '(k, b, g) := p in andb b (Nat.leb s k)) c.

Lemma has_dlow_iff : forall c s,
  has_dlow c s = true <-> exists k g, In (k, true, g) c /\ s <= k.
Proof.
  intros c s. unfold has_dlow. rewrite existsb_exists.
  split.
  - intros [[[k b] g] [Hin Hb]].
    apply andb_prop in Hb. destruct Hb as [Hb Hk].
    subst b. apply Nat.leb_le in Hk.
    exists k, g. split; assumption.
  - intros [k [g [Hin Hk]]].
    exists (k, true, g). split; [exact Hin|].
    cbn. apply Nat.leb_le. exact Hk.
Qed.

(** ** The least deep witness. *)

Fixpoint bmu (r : nat) (LB : nat -> mord) : mord :=
  match r with
  | 0 => mup (LB 0) MZ
  | S r' => mup (LB 0) (bmu r' (fun j => LB (S j)))
  end.

Lemma bmu_wf : forall r LB, (forall j, mwf (LB j)) -> mwf (bmu r LB).
Proof.
  induction r as [|r IH]; intros LB HLB; cbn.
  - apply mup_wf; [exact (HLB 0) | exact I].
  - apply mup_wf; [exact (HLB 0)|].
    apply IH. intro j. exact (HLB (S j)).
Qed.

Lemma bmu_mell : forall r LB,
  mell (bmu r LB) = match r with 0 => MZ | S r' => bmu r' (fun j => LB (S j)) end.
Proof.
  intros [|r] LB; cbn; apply mup_mell.
Qed.

Lemma bmu_gt : forall r LB j, j <= r -> (forall i, mwf (LB i)) ->
  mlt (LB j) (mellk j (bmu r LB)).
Proof.
  induction r as [|r IH]; intros LB j Hj HLB.
  - assert (j = 0) by lia. subst j. cbn.
    apply mup_gt. exact (HLB 0).
  - destruct j as [|j].
    + cbn. apply mup_gt. exact (HLB 0).
    + rewrite mellk_S.
      cbn [bmu]. rewrite mup_mell.
      exact (IH (fun i => LB (S i)) j ltac:(lia) (fun i => HLB (S i))).
Qed.

Lemma bmu_mellk_high : forall r LB j, r < j -> mellk j (bmu r LB) = MZ.
Proof.
  induction r as [|r IH]; intros LB j Hj.
  - destruct j as [|j]; [lia|].
    rewrite mellk_S. cbn. rewrite mup_mell. apply mellk_MZ.
  - destruct j as [|j]; [lia|].
    rewrite mellk_S. cbn [bmu]. rewrite mup_mell.
    apply IH. lia.
Qed.

Lemma bmu_least : forall r LB T,
  mwf T -> (forall j, mwf (LB j)) ->
  (forall j, j <= r -> mlt (LB j) (mellk j T)) ->
  mle (bmu r LB) T.
Proof.
  induction r as [|r IH]; intros LB T HT HLB Hsat; cbn.
  - apply mup_least; [exact (HLB 0) | exact HT | exact (Hsat 0 (Nat.le_0_l _)) | apply mZ_le].
  - apply mup_least; [exact (HLB 0) | exact HT | exact (Hsat 0 (Nat.le_0_l _))|].
    (* mle (bmu r (shift LB)) (mell T) via IH at mell T *)
    assert (Hmt : mle (bmu r (fun j => LB (S j))) (mell T)).
    { apply IH.
      - apply mell_wf. exact HT.
      - intro j. exact (HLB (S j)).
      - intros j Hj.
        rewrite <- mellk_S.
        exact (Hsat (S j) (le_n_S _ _ Hj)). }
    exact Hmt.
Qed.

Lemma bmu_least_levels : forall r LB T,
  mwf T -> (forall j, mwf (LB j)) ->
  (forall j, j <= r -> mlt (LB j) (mellk j T)) ->
  forall j, j <= r -> mle (mellk j (bmu r LB)) (mellk j T).
Proof.
  induction r as [|r IH]; intros LB T HT HLB Hsat j Hj.
  - assert (j = 0) by lia. subst j. cbn [mellk].
    apply bmu_least; assumption.
  - destruct j as [|j].
    + cbn [mellk]. apply bmu_least; assumption.
    + rewrite mellk_S. cbn [bmu]. rewrite mup_mell.
      rewrite (mellk_S j T).
      apply IH.
      * apply mell_wf. exact HT.
      * intro i. exact (HLB (S i)).
      * intros i Hi. rewrite <- mellk_S.
        exact (Hsat (S i) (le_n_S _ _ Hi)).
      * lia.
Qed.

(** ** The deep witness of a cell. *)

Definition Tcell (c : cell) (s : nat) : mord :=
  if has_dlow c s then bmu (ddepth c s) (dlow c s) else MZ.

Lemma Tcell_wf : forall c s, cwf c -> mwf (Tcell c s).
Proof.
  intros c s Hc. unfold Tcell.
  destruct (has_dlow c s); [|exact I].
  apply bmu_wf. intro j. apply dlow_wf. exact Hc.
Qed.

(** The deepest lower level is attained (or there are none). *)

Lemma ddepth_cons : forall k' b' g' c s,
  ddepth ((k', b', g') :: c) s =
  if andb b' (Nat.leb s k')
  then Nat.max (k' - s) (ddepth c s) else ddepth c s.
Proof. reflexivity. Qed.

Lemma ddepth_attained0 : forall c s,
  ddepth c s = 0 \/
  exists k g, In (k, true, g) c /\ s <= k /\ k - s = ddepth c s.
Proof.
  induction c as [|[[k' b'] g'] c IH]; intro s; [now left|].
  rewrite ddepth_cons.
  destruct (andb b' (Nat.leb s k')) eqn:Hb.
  - apply andb_prop in Hb. destruct Hb as [Hb Hk].
    subst b'. apply Nat.leb_le in Hk.
    destruct (Nat.max_spec (k' - s) (ddepth c s)) as
      [[Hlt Hmax] | [Hge Hmax]]; rewrite Hmax.
    + (* tail wins *)
      destruct (IH s) as [Hz | [k [g [Hin [Hks Hkd]]]]]; [lia|].
      right. exists k, g.
      split; [now right | split; [exact Hks | exact Hkd]].
    + right. exists k', g'.
      split; [now left | split; [exact Hk | reflexivity]].
  - destruct (IH s) as [Hz | [k [g [Hin [Hks Hkd]]]]].
    + now left.
    + right. exists k, g.
      split; [now right | split; [exact Hks | exact Hkd]].
Qed.

(** The deepest lower level is attained when any deep lower exists. *)

Lemma ddepth_attained : forall c s,
  has_dlow c s = true ->
  exists k g, In (k, true, g) c /\ s <= k /\ k - s = ddepth c s.
Proof.
  intros c s Hhd.
  destruct (ddepth_attained0 c s) as [Hz | Hatt]; [|exact Hatt].
  apply has_dlow_iff in Hhd.
  destruct Hhd as [k0 [g0 [Hin0 Hk0]]].
  pose proof (ddepth_ge c s k0 g0 Hin0 Hk0) as Hd0.
  exists k0, g0.
  split; [exact Hin0 | split; [exact Hk0 | lia]].
Qed.

(** ** The per-cell reachability characterisation. *)

Theorem reach_cell_char : forall n x c,
  mwf x -> cwf c ->
  (icreach n x (fun y => cellsem y c)
   <-> ((forall k b g, In (k, b, g) c -> k <= n -> csat x (k, b, g))
        /\ (forall k g, In (k, false, g) c -> S n <= k ->
              mle (mellk (k - S n) (Tcell c (S n))) g)
        /\ mlt (Tcell c (S n)) (mellk (S n) x))).
Proof.
  intros n x c Hwf Hcwf.
  split.
  - (* necessity *)
    intro Hreach.
    destruct (mord_eq_dec (mellk (S n) x) MZ) as [Hz | Hnz].
    { exfalso.
      destruct (member_absent n x Hwf Hz) as [gs [Hleg Hnone]].
      destruct (Hreach gs Hleg) as [y [Hy _]].
      exact (Hnone y Hy). }
    (* shallow uppers via singleton adversaries *)
    assert (Hshup : forall k g, In (k, false, g) c -> k <= n ->
              mle (mellk k x) g).
    { intros k g Hin Hk.
      destruct (mlt_total (mellk k x) g) as [Hlt | [Heq | Hgt]].
      - apply mlt_le. exact Hlt.
      - subst g. apply mle_refl.
      - exfalso.
        assert (Hleg1 : iclegit n x [(k, g)]).
        { intros p Hp. destruct Hp as [<- | []].
          cbn. split; [exact Hk|].
          split; [exact (Hcwf _ Hin) | exact Hgt]. }
        destruct (Hreach _ Hleg1) as [y [[Hyw [Hylt [Hyup Hygs]]] Hcy]].
        pose proof (Hygs (k, g) (or_introl eq_refl)) as Hlow.
        cbn [fst snd] in Hlow.
        pose proof (Hcy _ Hin) as Hup. cbn in Hup.
        exact (mlt_irrefl g (mlt_le_trans _ _ _ Hlow Hup)). }
    (* the pinned member *)
    assert (Hpins_leg : iclegit n x (pins n x)).
    { intros p Hp. apply pins_in in Hp.
      destruct Hp as [k [Hk ->]]. cbn.
      split; [lia|]. split.
      - apply mdec_wf. apply mellk_wf. exact Hwf.
      - apply mdec_lt.
        apply (mellk_nonzero_down k (S n) x); [lia | exact Hnz]. }
    destruct (Hreach (pins n x) Hpins_leg) as [y [Hy Hcy]].
    pose proof Hy as [Hyw [Hylt [Hyup Hygs]]].
    assert (Hstrict : forall k, k <= n ->
              mlt (mellk (S k) y) (mellk (S k) x)).
    { intros k Hk. exact (pins_cap n x y Hwf Hnz Hy k Hk). }
    (* shallow lowers from the pinned member *)
    assert (Hshallow : forall k b g, In (k, b, g) c -> k <= n ->
              csat x (k, b, g)).
    { intros k b g Hin Hk. destruct b; cbn.
      - pose proof (Hcy _ Hin) as Hsat. cbn in Hsat.
        destruct k as [|k'].
        + cbn in Hsat |- *. exact (mlt_trans _ _ _ Hsat Hylt).
        + eapply mlt_trans; [exact Hsat|].
          apply Hstrict. lia.
      - exact (Hshup k g Hin Hk). }
    destruct (has_dlow c (S n)) eqn:Hhd.
    + (* there are deep lower constraints *)
      destruct (ddepth_attained c (S n) Hhd)
        as [kst [gst [Hinst [Hksst Hkdst]]]].
      pose proof (Hcy _ Hinst) as Hsatst. cbn in Hsatst.
      assert (Halive : forall j, j <= ddepth c (S n) ->
                mellk (S n + j) y <> MZ).
      { intros j Hj.
        apply (mellk_nonzero_down (S n + j) kst y); [lia|].
        intro Hzz. rewrite Hzz in Hsatst.
        exact (not_mlt_MZ _ Hsatst). }
      assert (HT'sat : forall j, j <= ddepth c (S n) ->
                mlt (dlow c (S n) j) (mellk j (mellk (S n) y))).
      { intros j Hj. rewrite <- mellk_add.
        apply dlow_lt; [|exact (Halive j Hj)].
        intros g Hg. exact (Hcy _ Hg). }
      assert (HTle : mle (Tcell c (S n)) (mellk (S n) y)).
      { unfold Tcell. rewrite Hhd.
        apply bmu_least.
        - apply mellk_wf. exact Hyw.
        - intro j. apply dlow_wf. exact Hcwf.
        - exact HT'sat. }
      assert (HTlt : mlt (Tcell c (S n)) (mellk (S n) x)).
      { eapply mle_lt_trans; [exact HTle|].
        apply Hstrict. lia. }
      refine (conj Hshallow (conj _ HTlt)).
      intros k g Hin Hk.
      destruct (Nat.le_gt_cases (k - S n) (ddepth c (S n))) as [Hkd | Hkd].
      * (* within the witness depth: compare through the member's tail *)
        unfold Tcell. rewrite Hhd.
        eapply mle_trans.
        -- apply (bmu_least_levels (ddepth c (S n)) (dlow c (S n))
                    (mellk (S n) y)).
           ++ apply mellk_wf. exact Hyw.
           ++ intro j. apply dlow_wf. exact Hcwf.
           ++ exact HT'sat.
           ++ exact Hkd.
        -- rewrite <- mellk_add.
           replace (S n + (k - S n)) with k by lia.
           pose proof (Hcy _ Hin) as Hup. cbn in Hup.
           exact Hup.
      * (* beyond the witness depth: the witness is dead there *)
        unfold Tcell. rewrite Hhd.
        rewrite (bmu_mellk_high (ddepth c (S n)) (dlow c (S n)) _ Hkd).
        apply mZ_le.
    + (* no deep lower constraints: the witness is zero *)
      refine (conj Hshallow (conj _ _)).
      * intros k g Hin Hk.
        unfold Tcell. rewrite Hhd.
        rewrite mellk_MZ. apply mZ_le.
      * unfold Tcell. rewrite Hhd.
        apply mlt_MZ. exact Hnz.
  - (* sufficiency *)
    intros (Hsh & Hdup & HT) gs Hleg.
    assert (Hnz : mellk (S n) x <> MZ).
    { intro Hz. rewrite Hz in HT. exact (not_mlt_MZ _ HT). }
    set (G := fun k => mmax (gs_bound gs k) (dlow c 0 k)).
    assert (HG : forall k, k <= n -> mwf (G k) /\ mlt (G k) (mellk k x)).
    { intros k Hk. split.
      - apply mmax_wf.
        + apply gs_bound_wf.
          intros p Hp. exact (proj1 (proj2 (Hleg p Hp))).
        + apply dlow_wf. exact Hcwf.
      - apply mmax_lub.
        + apply gs_bound_lt.
          * intros gamma Hg. exact (proj2 (proj2 (Hleg _ Hg))).
          * apply (mellk_nonzero_down k (S n) x); [lia | exact Hnz].
        + apply dlow_lt.
          * intros g Hg.
            exact (Hsh k true g Hg Hk).
          * apply (mellk_nonzero_down k (S n) x); [lia | exact Hnz]. }
    destruct (chain_mu n x G (Tcell c (S n)) Hwf
                (Tcell_wf c (S n) Hcwf) HT HG)
      as [z [Hzw [Hzs Hzk]]].
    exists z.
    assert (Hmem : icmember n x gs z).
    { repeat split.
      - exact Hzw.
      - exact (proj2 (Hzk 0 (Nat.le_0_l _))).
      - intros k Hk. apply mlt_le. exact (proj2 (Hzk k Hk)).
      - intros [k gamma] Hin. cbn.
        pose proof (Hleg _ Hin) as [Hk [Hwfg _]].
        cbn in Hk.
        eapply mle_lt_trans.
        + eapply mle_trans.
          * exact (gs_bound_ge gs k gamma Hin).
          * apply mmax_le_l.
        + exact (proj1 (Hzk k Hk)). }
    split; [exact Hmem|].
    intros [[k b] g] Hin.
    destruct (Nat.le_gt_cases k n) as [Hk | Hk].
    + (* shallow constraint *)
      destruct b; cbn.
      * eapply mle_lt_trans.
        -- eapply mle_trans.
           ++ exact (dlow_ge c 0 k g Hin).
           ++ apply mmax_le_r.
        -- exact (proj1 (Hzk k Hk)).
      * apply mlt_le.
        eapply mlt_le_trans.
        -- exact (proj2 (Hzk k Hk)).
        -- exact (Hsh k false g Hin Hk).
    + (* deep constraint *)
      assert (Hks : S n <= k) by lia.
      destruct b; cbn.
      * (* deep lower *)
        assert (Hhd : has_dlow c (S n) = true).
        { apply has_dlow_iff. exists k, g. split; assumption. }
        replace k with (S n + (k - S n)) by lia.
        rewrite mellk_add, Hzs.
        unfold Tcell. rewrite Hhd.
        eapply mle_lt_trans.
        -- refine (dlow_ge c (S n) (k - S n) g _).
           replace (S n + (k - S n)) with k by lia.
           exact Hin.
        -- apply bmu_gt.
           ++ exact (ddepth_ge c (S n) k g Hin Hks).
           ++ intro i. apply dlow_wf. exact Hcwf.
      * (* deep upper *)
        replace k with (S n + (k - S n)) by lia.
        rewrite mellk_add, Hzs.
        refine (Hdup k g Hin Hks).
Qed.

(** ** The computed reach cell. *)

Definition mleb (a b : mord) : bool :=
  match mcmp a b with Gt => false | _ => true end.

Lemma mleb_iff : forall a b, mleb a b = true <-> mle a b.
Proof.
  intros a b. unfold mleb, mle.
  destruct (mcmp a b); intuition congruence.
Qed.

Definition dup_okb (n : nat) (c : cell) : bool :=
  forallb (fun p =>
    let '(k, b, g) := p in
    if andb (negb b) (Nat.leb (S n) k)
    then mleb (mellk (k - S n) (Tcell c (S n))) g
    else true) c.

Lemma dup_okb_iff : forall n c,
  dup_okb n c = true <->
  (forall k g, In (k, false, g) c -> S n <= k ->
     mle (mellk (k - S n) (Tcell c (S n))) g).
Proof.
  intros n c. unfold dup_okb. rewrite forallb_forall.
  split.
  - intros H k g Hin Hk.
    pose proof (H _ Hin) as Hp.
    apply Nat.leb_le in Hk.
    cbn [negb andb] in Hp.
    rewrite Hk in Hp.
    apply mleb_iff. exact Hp.
  - intros H [[k b] g] Hin.
    destruct b.
    + reflexivity.
    + cbn [negb andb].
      destruct (Nat.leb (S n) k) eqn:Hk.
      * apply Nat.leb_le in Hk.
        apply mleb_iff. exact (H k g Hin Hk).
      * reflexivity.
Qed.

Definition shallow_part (n : nat) (c : cell) : cell :=
  filter (fun p => Nat.leb (fst (fst p)) n) c.

Definition reachcell (n : nat) (c : cell) : cunion :=
  if dup_okb n c
  then [ shallow_part n c ++ [(S n, true, Tcell c (S n))] ]
  else [].

Lemma reachcell_wf : forall n c, cwf c -> uwf (reachcell n c).
Proof.
  intros n c Hc d Hd. unfold reachcell in Hd.
  destruct (dup_okb n c); [|destruct Hd].
  destruct Hd as [<- | []].
  intros p Hp. apply in_app_or in Hp.
  destruct Hp as [Hp | Hp].
  - apply filter_In in Hp. exact (Hc _ (proj1 Hp)).
  - destruct Hp as [<- | []]. cbn.
    apply Tcell_wf. exact Hc.
Qed.

Lemma reachcell_correct : forall n x c,
  mwf x -> cwf c ->
  (usem x (reachcell n c) <-> icreach n x (fun y => cellsem y c)).
Proof.
  intros n x c Hwf Hcwf.
  rewrite (reach_cell_char n x c Hwf Hcwf).
  unfold reachcell.
  destruct (dup_okb n c) eqn:Hok.
  - pose proof (proj1 (dup_okb_iff n c) Hok) as Hokp.
    split.
    + intros [d [Hd Hsem]].
      destruct Hd as [<- | []].
      split; [|split].
      * intros k b g Hin Hk.
        apply (Hsem (k, b, g)).
        apply in_or_app. left.
        apply filter_In. split; [exact Hin|].
        cbn. apply Nat.leb_le. exact Hk.
      * exact Hokp.
      * pose proof (Hsem (S n, true, Tcell c (S n))) as Ht.
        cbn in Ht. apply Ht.
        apply in_or_app. right. now left.
    + intros (Hsh & _ & HT).
      exists (shallow_part n c ++ [(S n, true, Tcell c (S n))]).
      split; [now left|].
      intros [[k b] g] Hp.
      apply in_app_or in Hp.
      destruct Hp as [Hp | Hp].
      * apply filter_In in Hp.
        destruct Hp as [Hin Hk]. cbn in Hk.
        apply Nat.leb_le in Hk.
        exact (Hsh k b g Hin Hk).
      * destruct Hp as [Heq | []].
        injection Heq as <- <- <-. cbn.
        exact HT.
  - split.
    + intros [d [[] _]].
    + intros (_ & Hdup & _).
      exfalso.
      assert (Hok2 : dup_okb n c = true)
        by exact (proj2 (dup_okb_iff n c) Hdup).
      congruence.
Qed.

(** ** Reachability of a union: directedness. *)

Lemma icreach_ext : forall n x (A B : mord -> Prop),
  (forall y, mwf y -> (A y <-> B y)) ->
  icreach n x A -> icreach n x B.
Proof.
  intros n x A B HAB HA gs Hleg.
  destruct (HA gs Hleg) as [y [Hy HAy]].
  exists y. split; [exact Hy|].
  apply (HAB y (proj1 Hy)). exact HAy.
Qed.

Lemma icreach_union : forall n x U,
  icreach n x (fun y => usem y U) ->
  exists c, In c U /\ icreach n x (fun y => cellsem y c).
Proof.
  intros n x U. induction U as [|c U IH]; intro H.
  - destruct (H [] (fun p Hp => match Hp with end))
      as [y [_ [d [[] _]]]].
  - destruct (classic (icreach n x (fun y => cellsem y c))) as [Hc | Hc].
    + exists c. split; [now left | exact Hc].
    + apply not_all_ex_not in Hc.
      destruct Hc as [gsc Hc].
      apply imply_to_and in Hc.
      destruct Hc as [Hlegc Hnoc].
      assert (HU : icreach n x (fun y => usem y U)).
      { intros gs Hleg.
        destruct (H (gs ++ gsc) (iclegit_app _ _ _ _ Hleg Hlegc))
          as [y [Hy [d [Hd Hsd]]]].
        destruct Hd as [<- | Hd].
        - exfalso. apply Hnoc.
          exists y.
          split; [exact (icmember_app_r _ _ _ _ _ Hy) | exact Hsd].
        - exists y.
          split; [exact (icmember_app_l _ _ _ _ _ Hy)|].
          exists d. split; assumption. }
      destruct (IH HU) as [d [Hd Hrd]].
      exists d. split; [now right | exact Hrd].
Qed.

Definition reachU (n : nat) (U : cunion) : cunion :=
  flat_map (reachcell n) U.

Lemma reachU_wf : forall n U, uwf U -> uwf (reachU n U).
Proof.
  intros n U HU d Hd.
  unfold reachU in Hd. apply in_flat_map in Hd.
  destruct Hd as [c [Hc Hd]].
  exact (reachcell_wf n c (HU c Hc) d Hd).
Qed.

Lemma reachU_correct : forall n x U,
  mwf x -> uwf U ->
  (usem x (reachU n U) <-> icreach n x (fun y => usem y U)).
Proof.
  intros n x U Hwf HU.
  split.
  - intros [d [Hd Hsd]].
    unfold reachU in Hd. apply in_flat_map in Hd.
    destruct Hd as [c [Hc Hd]].
    assert (Hr : icreach n x (fun y => cellsem y c)).
    { apply (reachcell_correct n x c Hwf (HU c Hc)).
      exists d. split; assumption. }
    intros gs Hleg.
    destruct (Hr gs Hleg) as [y [Hy Hcy]].
    exists y. split; [exact Hy|].
    exists c. split; assumption.
  - intro H.
    destruct (icreach_union n x U H) as [c [Hc Hrc]].
    apply (reachcell_correct n x c Hwf (HU c Hc)) in Hrc.
    destruct Hrc as [d [Hd Hsd]].
    exists d. split; [|exact Hsd].
    unfold reachU. apply in_flat_map.
    exists c. split; assumption.
Qed.

(** ** Extensions of formulas as cell unions. *)

Fixpoint cells_of (phi : Form) : cunion :=
  match phi with
  | Var _ => [[]]
  | Bot => []
  | Impl a b => compl (cells_of a) ++ cells_of b
  | Box m psi => compl (reachU m (compl (cells_of psi)))
  end.

Lemma cells_of_wf : forall phi, uwf (cells_of phi).
Proof.
  induction phi as [p | | a IHa b IHb | m psi IH]; cbn [cells_of].
  - intros c Hc. destruct Hc as [<- | []].
    intros p' Hp'. destruct Hp'.
  - intros c Hc. destruct Hc.
  - apply uwf_app; [apply compl_wf; exact IHa | exact IHb].
  - apply compl_wf. apply reachU_wf. apply compl_wf. exact IH.
Qed.

Lemma box_reach : forall m psi x,
  mwf x ->
  (icforces x (Box m psi)
   <-> ~ icreach m x (fun y => ~ icforces y psi)).
Proof.
  intros m psi x Hwf.
  split.
  - intros [gs [Hleg Hmem]] Hr.
    destruct (Hr gs Hleg) as [y [Hy Hny]].
    exact (Hny (Hmem y Hy)).
  - intro Hnr.
    apply not_all_ex_not in Hnr.
    destruct Hnr as [gs Hgs].
    apply imply_to_and in Hgs.
    destruct Hgs as [Hleg Hno].
    exists gs. split; [exact Hleg|].
    intros y Hy.
    apply NNPP. intro Hny.
    apply Hno. exists y. split; assumption.
Qed.

Theorem cells_of_correct : forall phi x,
  mwf x -> (icforces x phi <-> usem x (cells_of phi)).
Proof.
  induction phi as [p | | a IHa b IHb | m psi IH]; intros x Hwf.
  - cbn. split.
    + intros _. exists []. split; [now left|].
      intros p' Hp'. destruct Hp'.
    + intros _. exact I.
  - cbn. split.
    + intros [].
    + intros [c [[] _]].
  - cbn [cells_of icforces].
    rewrite usem_app.
    rewrite (compl_correct (cells_of a) x).
    split.
    + intro Hab.
      destruct (classic (icforces x a)) as [Ha | Ha].
      * right. apply (IHb x Hwf). exact (Hab Ha).
      * left. intro Hu. apply Ha. apply (IHa x Hwf). exact Hu.
    + intros [Hna | Hb] Ha.
      * exfalso. apply Hna. apply (IHa x Hwf). exact Ha.
      * apply (IHb x Hwf). exact Hb.
  - cbn [cells_of].
    rewrite (box_reach m psi x Hwf).
    rewrite (compl_correct (reachU m (compl (cells_of psi))) x).
    assert (Hu : uwf (compl (cells_of psi))).
    { apply compl_wf. apply cells_of_wf. }
    rewrite (reachU_correct m x (compl (cells_of psi)) Hwf Hu).
    split.
    + intros Hn Hr. apply Hn.
      refine (icreach_ext m x _ _ _ Hr).
      intros y Hyw.
      rewrite (compl_correct (cells_of psi) y).
      split.
      * intros Hc Hf. apply Hc. apply (IH y Hyw). exact Hf.
      * intros Hnf Hc. apply Hnf. apply (IH y Hyw). exact Hc.
    + intros Hn Hr. apply Hn.
      refine (icreach_ext m x _ _ _ Hr).
      intros y Hyw.
      rewrite (compl_correct (cells_of psi) y).
      split.
      * intros Hnf Hc. apply Hnf. apply (IH y Hyw). exact Hc.
      * intros Hc Hf. apply Hc. apply (IH y Hyw). exact Hf.
Qed.

(** ** Validity of the Japaridze scheme. *)

Definition lowers_of (c : cell) : list (nat * mord) :=
  map (fun p => (fst (fst p), snd p))
      (filter (fun p => snd (fst p)) c).

Lemma lowers_of_in : forall c k g,
  In (k, g) (lowers_of c) <-> In (k, true, g) c.
Proof.
  intros c k g. unfold lowers_of.
  rewrite in_map_iff.
  split.
  - intros [[[k' b'] g'] [Heq Hin]].
    cbn in Heq. injection Heq as -> ->.
    apply filter_In in Hin.
    destruct Hin as [Hin Hb]. cbn in Hb. subst b'.
    exact Hin.
  - intro Hin.
    exists (k, true, g). split; [reflexivity|].
    apply filter_In. split; [exact Hin | reflexivity].
Qed.

Lemma diamond_reach : forall n phi x,
  mwf x ->
  (icforces x (Diamond n phi)
   <-> icreach n x (fun y => icforces y phi)).
Proof.
  intros n phi x Hwf.
  unfold Diamond, Neg.
  cbn [icforces].
  split.
  - intro Hd.
    intros gs Hleg.
    apply NNPP. intro Hno.
    apply Hd.
    exists gs. split; [exact Hleg|].
    intros y Hy Hfy.
    apply Hno. exists y.
    split; [exact Hy | exact Hfy].
  - intros Hr [gs [Hleg Hmem]].
    destruct (Hr gs Hleg) as [y [Hy Hfy]].
    exact (Hmem y Hy Hfy).
Qed.

Lemma ic_j : forall n phi x,
  mwf x ->
  icforces x (Impl (Diamond n phi) (Box (S n) (Diamond n phi))).
Proof.
  intros n phi x Hwf.
  cbn [icforces]. intro Hd.
  apply (diamond_reach n phi x Hwf) in Hd.
  (* translate to the computed cell union *)
  assert (Hru : usem x (reachU n (cells_of phi))).
  { apply (reachU_correct n x (cells_of phi) Hwf (cells_of_wf phi)).
    refine (icreach_ext n x _ _ _ Hd).
    intros y Hyw. exact (cells_of_correct phi y Hyw). }
  destruct Hru as [d [Hd' Hsd]].
  unfold reachU in Hd'. apply in_flat_map in Hd'.
  destruct Hd' as [c [Hc Hrc]].
  assert (Hcwf' : cwf d).
  { exact (reachcell_wf n c (cells_of_wf phi c Hc) d Hrc). }
  (* the witness: the lower constraints of the satisfied reach cell *)
  exists (lowers_of d).
  split.
  { intros [k g] Hp.
    apply lowers_of_in in Hp.
    cbn. split; [|split].
    - (* level bound: all constraints of a reach cell are at levels <= S n *)
      unfold reachcell in Hrc.
      destruct (dup_okb n c); [|destruct Hrc].
      destruct Hrc as [<- | []].
      apply in_app_or in Hp.
      destruct Hp as [Hp | Hp].
      + apply filter_In in Hp.
        destruct Hp as [_ Hk]. cbn in Hk.
        apply Nat.leb_le in Hk. lia.
      + destruct Hp as [Heq | []].
        injection Heq as Hk1 Hg1. lia.
    - exact (Hcwf' _ Hp).
    - pose proof (Hsd _ Hp) as Hs. cbn in Hs. exact Hs. }
  intros y Hy.
  pose proof Hy as [Hyw [Hylt [Hyup Hygs]]].
  apply (diamond_reach n phi y Hyw).
  assert (Hsdy : cellsem y d).
  { intros [[k b] g] Hp.
    destruct b.
    - (* lower: from the neighborhood constraints *)
      pose proof (Hygs (k, g)) as Hl.
      cbn [fst snd] in Hl.
      apply Hl. apply lowers_of_in. exact Hp.
    - (* upper: only at shallow levels; transfer through x *)
      unfold reachcell in Hrc.
      destruct (dup_okb n c); [|destruct Hrc].
      destruct Hrc as [<- | []].
      pose proof (Hsd _ Hp) as Hsx. cbn in Hsx.
      apply in_app_or in Hp.
      destruct Hp as [Hp | Hp].
      + apply filter_In in Hp.
        destruct Hp as [_ Hk]. cbn in Hk.
        apply Nat.leb_le in Hk.
        cbn.
        eapply mle_trans; [apply Hyup; lia | exact Hsx].
      + destruct Hp as [Heq | []]. discriminate Heq. }
  assert (Hry : usem y (reachU n (cells_of phi))).
  { exists d. split; [|exact Hsdy].
    unfold reachU. apply in_flat_map.
    exists c. split; assumption. }
  apply (reachU_correct n y (cells_of phi) Hyw (cells_of_wf phi)) in Hry.
  refine (icreach_ext n y _ _ _ Hry).
  intros z Hzw.
  split.
  - intro Hu. apply (cells_of_correct phi z Hzw). exact Hu.
  - intro Hf. apply (cells_of_correct phi z Hzw). exact Hf.
Qed.

(** ** Soundness of the extended calculus over the model. *)

Theorem icsound : forall phi, Provable phi ->
  forall x, mwf x -> icforces x phi.
Proof.
  intros phi H.
  induction H; intros x Hwf.
  - cbn. intros Ha _. exact Ha.
  - cbn. intros H1 H2 Ha. exact (H1 Ha (H2 Ha)).
  - cbn. intro Hnn. apply NNPP. exact Hnn.
  - apply ic_boxk.
  - apply ic_loeb.
  - apply ic_box4.
  - apply ic_mon.
  - apply ic_nextcon. exact Hwf.
  - apply ic_j. exact Hwf.
  - exact (IHProvable1 x Hwf (IHProvable2 x Hwf)).
  - cbn. exists [].
    split.
    + intros p Hp. destruct Hp.
    + intros y Hy. exact (IHProvable y (proj1 Hy)).
Qed.

(** ** Tower points and per-level consistency. *)

Fixpoint mtower (k : nat) : mord :=
  match k with
  | 0 => MC MZ MZ
  | S k' => MC (mtower k') MZ
  end.

Lemma mtower_wf : forall k, mwf (mtower k).
Proof.
  induction k as [|k IH]; cbn.
  - repeat split. apply mZ_le.
  - repeat split; [exact IH | apply mZ_le].
Qed.

Lemma mtower_nz : forall k, mtower k <> MZ.
Proof. intros [|k]; cbn; congruence. Qed.

Lemma mellk_mtower : forall j m, j <= m ->
  mellk j (mtower m) = mtower (m - j).
Proof.
  induction j as [|j IH]; intros m Hj.
  - cbn. f_equal. lia.
  - destruct m as [|m]; [lia|].
    rewrite mellk_S. cbn [mtower mell].
    rewrite (IH m ltac:(lia)).
    reflexivity.
Qed.

Theorem icmodel_box_consistency : forall n, ~ Provable (Box n Bot).
Proof.
  intros n H.
  pose proof (icsound _ H (mtower (S (S n))) (mtower_wf _)) as Hf.
  cbn in Hf.
  destruct Hf as [gs [Hleg Hmem]].
  assert (Hnz : mellk (S n) (mtower (S (S n))) <> MZ).
  { rewrite (mellk_mtower (S n) (S (S n)) ltac:(lia)).
    apply mtower_nz. }
  destruct (member_exists n (mtower (S (S n))) gs
              (mtower_wf _) Hnz Hleg) as [z Hz].
  exact (Hmem z Hz).
Qed.

Theorem icmodel_consistency : ~ Provable Bot.
Proof.
  intro H.
  exact (icsound _ H MZ I).
Qed.

