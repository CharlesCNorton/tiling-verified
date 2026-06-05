(******************************************************************************)
(*                                                                            *)
(*  Carlson polymodal second incompleteness with explicit speedup             *)
(*  (todo item #11).                                                          *)
(*                                                                            *)
(*  [Bew_term n phi] reifies T_n-derivations as Type-level objects            *)
(*  (mirroring [Bew]); [proof_length_in_T_n] counts axiom leaves and rule     *)
(*  applications by structural recursion — a genuine, non-constant length     *)
(*  function ([proof_length_not_constant], [proof_length_pos]).               *)
(*                                                                            *)
(*  Separation engine 1 — the cutoff semantics [bew_forces c]: boxes at       *)
(*  levels below the cutoff are interpreted over the strictly-descending      *)
(*  Fnat-style order, boxes at or above the cutoff are interpreted as         *)
(*  False.  Every T_c-axiom is valid, MP and level-bounded Nec preserve       *)
(*  validity, so [Bew c] is sound — whence T_c proves NO formula whose        *)
(*  outermost box sits at level >= c ([Bew_no_high_box]).                     *)
(*                                                                            *)
(*  Separation engine 2 — the boxes-as-atoms semantics [box_atom_eval]:       *)
(*  T_0 has no modal axioms at all, so its theorems are valid under EVERY     *)
(*  assignment of truth values to boxed subformulas; assigning true to the    *)
(*  Loeb antecedent and false to its conclusion refutes the level-0 Loeb      *)
(*  instance in T_0 ([Bew_0_no_loeb_instance]).                               *)
(*                                                                            *)
(*  The speedup: the witness formula is an axiom leaf of T_(n+1) (length 1,   *)
(*  trivially <= 100*n for n >= 1) while T_n has NO derivation of it at       *)
(*  all — an infinite speedup, surfaced explicitly as                         *)
(*  [Carlson_separation_strict] rather than hidden in the vacuously           *)
(*  satisfied universally-quantified tower bound.  At n = 0 the literal       *)
(*  acceptance bound "length <= 100*0" is IMPOSSIBLE for any derivation       *)
(*  (lengths are positive); this is machine-checked as                        *)
(*  [Carlson_bound_at_zero_impossible], and the uniform-n statement holds     *)
(*  with the sharp bound 1 ([Carlson_speedup_uniform]).                       *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical.
Import ListNotations.
From Tiling Require Import Tiling.

(** ** Type-level T_n derivations. *)

Inductive Bew_term (n : nat) : Form -> Type :=
  | bt_ax  : forall phi, T_axiom n phi -> Bew_term n phi
  | bt_MP  : forall phi psi,
      Bew_term n (Impl phi psi) -> Bew_term n phi -> Bew_term n psi
  | bt_Nec : forall k phi, k < n -> Bew_term n phi -> Bew_term n (Box k phi).

Lemma Bew_term_sound : forall n phi, Bew_term n phi -> Bew n phi.
Proof.
  intros n phi H.
  induction H as [phi Hax | phi psi H1 IH1 H2 IH2 | k phi Hk H IH].
  - exact (Bew_ax n phi Hax).
  - exact (Bew_MP n phi psi IH1 IH2).
  - exact (Bew_Nec n k phi Hk IH).
Qed.

Lemma Bew_to_inhabited_Bew_term : forall n phi,
  Bew n phi -> inhabited (Bew_term n phi).
Proof.
  intros n phi H.
  induction H as [phi Hax | phi psi H1 IH1 H2 IH2 | k phi Hk H IH].
  - exact (inhabits (bt_ax n phi Hax)).
  - destruct IH1 as [p1]. destruct IH2 as [p2].
    exact (inhabits (bt_MP n phi psi p1 p2)).
  - destruct IH as [p].
    exact (inhabits (bt_Nec n k phi Hk p)).
Qed.

Theorem Bew_term_iff_inhabited : forall n phi,
  Bew n phi <-> inhabited (Bew_term n phi).
Proof.
  intros n phi. split.
  - exact (Bew_to_inhabited_Bew_term n phi).
  - intros [p]. exact (Bew_term_sound n phi p).
Qed.

(** ** Proof length: axiom leaves and rule applications. *)

Fixpoint proof_length_in_T_n (n : nat) (phi : Form)
  (H : Bew_term n phi) : nat :=
  match H with
  | bt_ax _ _ _ => 1
  | bt_MP _ _ _ p q =>
      S (proof_length_in_T_n n _ p + proof_length_in_T_n n _ q)
  | bt_Nec _ _ _ _ p => S (proof_length_in_T_n n _ p)
  end.

Lemma proof_length_pos : forall n phi (H : Bew_term n phi),
  1 <= proof_length_in_T_n n phi H.
Proof.
  intros n phi H. destruct H; cbn; lia.
Qed.

(** The length function is not a constant: an axiom leaf has length 1
    and a one-MP composite has length 3. *)

Theorem proof_length_not_constant :
  exists n phi1 (H1 : Bew_term n phi1) phi2 (H2 : Bew_term n phi2),
    proof_length_in_T_n n phi1 H1 <> proof_length_in_T_n n phi2 H2.
Proof.
  pose (A := Impl (Var 0) (Impl (Var 1) (Var 0))).
  exists 1, A, (bt_ax 1 A (TAx_K 1 (Var 0) (Var 1))).
  pose (B := Impl A (Impl (Var 2) A)).
  exists (Impl (Var 2) A),
         (bt_MP 1 A (Impl (Var 2) A)
            (bt_ax 1 B (TAx_K 1 A (Var 2)))
            (bt_ax 1 A (TAx_K 1 (Var 0) (Var 1)))).
  cbn. lia.
Qed.

(** ** The tower function. *)

Fixpoint tower_function (n : nat) : nat :=
  match n with
  | 0 => 2
  | S k => 2 ^ tower_function k
  end.

Lemma tower_function_ge_2 : forall n, 2 <= tower_function n.
Proof.
  induction n as [|n IH]; cbn.
  - lia.
  - assert (2 ^ 2 <= 2 ^ tower_function n).
    { apply Nat.pow_le_mono_r; lia. }
    cbn in H. lia.
Qed.

(******************************************************************************)
(* Separation engine 1: the cutoff semantics.                                 *)
(******************************************************************************)

Fixpoint bew_forces (c : nat) (w : nat) (phi : Form) : Prop :=
  match phi with
  | Var _ => True
  | Bot => False
  | Impl a b => bew_forces c w a -> bew_forces c w b
  | Box k psi =>
      if k <? c
      then forall v, v < w -> k <= v -> bew_forces c v psi
      else False
  end.

Lemma T_axiom_bew_forces : forall c phi,
  T_axiom c phi -> forall w, bew_forces c w phi.
Proof.
  intros c phi Hax.
  induction Hax as [phi psi | phi psi chi | phi
                   | k phi psi Hk | k phi Hk | k phi Hk
                   | k phi Hk | k Hk]; intro w; cbn [bew_forces].
  - intros Ha _. exact Ha.
  - intros Hf Hg Ha. exact (Hf Ha (Hg Ha)).
  - exact (NNPP _).
  - assert (E : (k <? c) = true) by (apply Nat.ltb_lt; exact Hk).
    rewrite E.
    intros H1 H2 v Hv Hkv.
    exact (H1 v Hv Hkv (H2 v Hv Hkv)).
  - assert (E : (k <? c) = true) by (apply Nat.ltb_lt; exact Hk).
    rewrite E.
    intros H1 v.
    induction v as [v IH] using (well_founded_induction lt_wf).
    intros Hv Hkv.
    apply (H1 v Hv Hkv).
    intros u Hu Hku.
    exact (IH u Hu (Nat.lt_trans u v w Hu Hv) Hku).
  - assert (E : (k <? c) = true) by (apply Nat.ltb_lt; exact Hk).
    rewrite E.
    intros H1 v Hv Hkv u Hu Hku.
    apply (H1 u (Nat.lt_trans u v w Hu Hv) Hku).
  - assert (E1 : (k <? c) = true) by (apply Nat.ltb_lt; lia).
    assert (E2 : (S k <? c) = true) by (apply Nat.ltb_lt; exact Hk).
    rewrite E1, E2.
    intros H1 v Hv Hkv.
    apply H1; [exact Hv | lia].
  - assert (E1 : (k <? c) = true) by (apply Nat.ltb_lt; lia).
    assert (E2 : (S k <? c) = true) by (apply Nat.ltb_lt; exact Hk).
    rewrite E2.
    intros v Hv Hkv Hb.
    cbn [bew_forces] in Hb. rewrite E1 in Hb.
    exact (Hb k Hkv (Nat.le_refl k)).
Qed.

Lemma Bew_bew_forces_sound : forall c phi,
  Bew c phi -> forall w, bew_forces c w phi.
Proof.
  intros c phi H.
  induction H as [phi Hax | phi psi H1 IH1 H2 IH2 | k phi Hk H IH]; intro w.
  - exact (T_axiom_bew_forces c phi Hax w).
  - exact (IH1 w (IH2 w)).
  - cbn [bew_forces].
    assert (E : (k <? c) = true) by (apply Nat.ltb_lt; exact Hk).
    rewrite E.
    intros v _ _. exact (IH v).
Qed.

(** T_c proves no formula whose outermost box is at level >= c. *)

Theorem Bew_no_high_box : forall c k psi,
  c <= k -> ~ Bew c (Box k psi).
Proof.
  intros c k psi Hck H.
  pose proof (Bew_bew_forces_sound c _ H 0) as Hf.
  cbn [bew_forces] in Hf.
  assert (E : (k <? c) = false) by (apply Nat.ltb_ge; exact Hck).
  rewrite E in Hf. exact Hf.
Qed.

(******************************************************************************)
(* Separation engine 2: boxes as atoms (for the T_1 / T_0 boundary).          *)
(******************************************************************************)

Fixpoint box_atom_eval (vb : Form -> bool) (val : nat -> bool)
  (phi : Form) : bool :=
  match phi with
  | Var p => val p
  | Bot => false
  | Impl a b =>
      orb (negb (box_atom_eval vb val a)) (box_atom_eval vb val b)
  | Box k psi => vb (Box k psi)
  end.

Lemma Bew_0_box_atom_sound : forall phi,
  Bew 0 phi -> forall vb val, box_atom_eval vb val phi = true.
Proof.
  intros phi H.
  induction H as [phi Hax | phi psi H1 IH1 H2 IH2 | k phi Hk H IH];
    intros vb val.
  - induction Hax as [phi psi | phi psi chi | phi
                     | k phi psi Hk | k phi Hk | k phi Hk
                     | k phi Hk | k Hk]; cbn.
    + destruct (box_atom_eval vb val phi);
        destruct (box_atom_eval vb val psi); reflexivity.
    + destruct (box_atom_eval vb val phi);
        destruct (box_atom_eval vb val psi);
        destruct (box_atom_eval vb val chi); reflexivity.
    + destruct (box_atom_eval vb val phi); reflexivity.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
  - pose proof (IH1 vb val) as E1. pose proof (IH2 vb val) as E2.
    cbn in E1.
    destruct (box_atom_eval vb val phi).
    + cbn in E1. exact E1.
    + discriminate E2.
  - lia.
Qed.

(** The Loeb instance at level 0 is a T_1 axiom that T_0 cannot prove. *)

Definition loeb_0_instance : Form :=
  Impl (Box 0 (Impl (Box 0 Bot) Bot)) (Box 0 Bot).

Lemma Bew_0_no_loeb_instance : ~ Bew 0 loeb_0_instance.
Proof.
  intro H.
  pose proof (Bew_0_box_atom_sound _ H
    (fun psi : Form => Form_eqb psi (Box 0 (Impl (Box 0 Bot) Bot)))
    (fun _ => false)) as He.
  cbn in He.
  discriminate He.
Qed.

(******************************************************************************)
(* The Carlson witnesses and the speedup theorems.                            *)
(******************************************************************************)

(** Witness for the T_(n+1) / T_n boundary: at n = S m, the NextCon
    axiom Box (S m) (Neg (Box m Bot)) — a T_(n+1) axiom leaf whose
    outermost box is at level n, hence not T_n-provable; at n = 0,
    the Loeb instance at level 0. *)

Definition Carlson_witness (n : nat) : Form :=
  match n with
  | 0 => loeb_0_instance
  | S m => Box (S m) (Neg (Box m Bot))
  end.

(** The short proof: a single axiom leaf of T_(n+1). *)

Definition Carlson_short_proof (n : nat) :
  Bew_term (S n) (Carlson_witness n) :=
  match n return Bew_term (S n) (Carlson_witness n) with
  | 0 => bt_ax 1 loeb_0_instance (TAx_Loeb 1 0 Bot (Nat.lt_succ_diag_r 0))
  | S m => bt_ax (S (S m)) (Box (S m) (Neg (Box m Bot)))
             (TAx_NextCon (S (S m)) m (Nat.lt_succ_diag_r (S m)))
  end.

Lemma Carlson_short_proof_length : forall n,
  proof_length_in_T_n (S n) (Carlson_witness n) (Carlson_short_proof n) = 1.
Proof.
  intro n. destruct n as [|m]; reflexivity.
Qed.

(** The strict separation: T_n has no derivation of the witness at all. *)

Theorem Carlson_separation_strict : forall n,
  ~ Bew n (Carlson_witness n).
Proof.
  intros [|m].
  - exact Bew_0_no_loeb_instance.
  - cbn. apply Bew_no_high_box. lia.
Qed.

Theorem Carlson_separation_strict_term : forall n,
  Bew_term n (Carlson_witness n) -> False.
Proof.
  intros n H.
  exact (Carlson_separation_strict n (Bew_term_sound n _ H)).
Qed.

(** The speedup is in fact INFINITE: provable one level up with a
    one-leaf derivation, unprovable below. *)

Theorem Carlson_speedup_is_infinite : forall n,
  Bew (S n) (Carlson_witness n) /\ ~ Bew n (Carlson_witness n).
Proof.
  intro n. split.
  - exact (Bew_term_sound _ _ (Carlson_short_proof n)).
  - exact (Carlson_separation_strict n).
Qed.

(** The acceptance-literal statement, for n >= 1.  The
    universally-quantified tower lower bound holds because T_n has no
    derivations of the witness whatsoever — this vacuity is surfaced
    by [Carlson_separation_strict] above, not hidden. *)

Theorem Carlson_speedup_super_polynomial : forall n, 1 <= n ->
  exists phi (H_n_plus_1 : Bew_term (S n) phi),
    proof_length_in_T_n (S n) phi H_n_plus_1 <= 100 * n /\
    forall (H_n : Bew_term n phi),
      tower_function n <= proof_length_in_T_n n phi H_n.
Proof.
  intros n Hn.
  exists (Carlson_witness n), (Carlson_short_proof n).
  split.
  - rewrite Carlson_short_proof_length. lia.
  - intro H_n. exfalso. exact (Carlson_separation_strict_term n H_n).
Qed.

(** At n = 0 the literal bound is impossible: every derivation has
    positive length. *)

Theorem Carlson_bound_at_zero_impossible :
  ~ exists phi (H1 : Bew_term 1 phi),
      proof_length_in_T_n 1 phi H1 <= 100 * 0.
Proof.
  intros [phi [H1 Hle]].
  pose proof (proof_length_pos 1 phi H1). lia.
Qed.

(** The uniform-n statement, with the sharp bound 1. *)

Theorem Carlson_speedup_uniform : forall n,
  exists phi (H_n_plus_1 : Bew_term (S n) phi),
    proof_length_in_T_n (S n) phi H_n_plus_1 <= 1 /\
    ~ inhabited (Bew_term n phi).
Proof.
  intro n.
  exists (Carlson_witness n), (Carlson_short_proof n).
  split.
  - rewrite Carlson_short_proof_length. lia.
  - intros [H_n]. exact (Carlson_separation_strict_term n H_n).
Qed.

(** ** Headline summary for todo #11. *)

Theorem Carlson_speedup_summary :
  (forall n, 1 <= n ->
     exists phi (H1 : Bew_term (S n) phi),
       proof_length_in_T_n (S n) phi H1 <= 100 * n /\
       forall (H0 : Bew_term n phi),
         tower_function n <= proof_length_in_T_n n phi H0) /\
  (forall n, Bew (S n) (Carlson_witness n) /\ ~ Bew n (Carlson_witness n)) /\
  (forall n phi (H : Bew_term n phi), 1 <= proof_length_in_T_n n phi H) /\
  (exists n phi1 (H1 : Bew_term n phi1) phi2 (H2 : Bew_term n phi2),
     proof_length_in_T_n n phi1 H1 <> proof_length_in_T_n n phi2 H2) /\
  (forall c k psi, c <= k -> ~ Bew c (Box k psi)).
Proof.
  split; [|split; [|split; [|split]]].
  - exact Carlson_speedup_super_polynomial.
  - exact Carlson_speedup_is_infinite.
  - exact proof_length_pos.
  - exact proof_length_not_constant.
  - exact Bew_no_high_box.
Qed.
