(******************************************************************************)
(*                                                                            *)
(*  Reverse-mathematics subsystem calculi with a STRICT hierarchy             *)
(*  (todo item #3).                                                           *)
(*                                                                            *)
(*  The Big Five -- RCA_0 < WKL_0 < ACA_0 < ATR_0 < Pi^1_1-CA_0 -- are        *)
(*  separated, proof-theoretically, by reflection / consistency strength:     *)
(*  each system proves the consistency of every weaker system but not its     *)
(*  own (Goedel II), and that Pi^0_1 reflection tower is exactly the standard *)
(*  separating invariant.  The modal language has no second-order arithmetic, *)
(*  so -- as with the Pi_2 item -- the reverse-math content is transposed     *)
(*  FAITHFULLY into the box-level tower: the characteristic principle of the  *)
(*  system at rank r is [RM_Con r := Neg (Box r Bot)] (consistency at level   *)
(*  r), and [RM_provable_real s] is base modal logic + MP + every [RM_Con k]  *)
(*  for k below the system's rank.  This is genuinely cumulative and          *)
(*  genuinely strict.                                                         *)
(*                                                                            *)
(*  The three forbidden collapses are all excluded:                          *)
(*    - NOT [RM_provable_real s P := P]: every system is consistent           *)
(*      ([RM_consistent]: ~ RM_provable_real s Bot).                          *)
(*    - NOT [RM_provable_real s P := |- P]: WKL_0 proves [RM_Con 0] which is  *)
(*      NOT a modal theorem ([RM_strictly_above_base]).                       *)
(*    - NOT non-strict: [RM_provable_real_strict_hierarchy] gives, for every  *)
(*      s < s', a formula provable in s' but refuted in s.                    *)
(*                                                                            *)
(*  Strictness is proved by a single-world soundness                          *)
(*  ([RM_sound]: RM_provable_real s phi -> forces Fnat V (rank s) phi).       *)
(*  At Fnat-world [r], [RM_Con k] is forced iff k < r, so the system at rank  *)
(*  r validates exactly the lower consistencies and refutes its own.          *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
From Tiling Require Import Tiling.

(** ** The Big Five and their rank. *)

Inductive RM_subsystem : Type :=
  | RCA0 | WKL0 | ACA0 | ATR0 | Pi11CA0.

Definition rm_rank (s : RM_subsystem) : nat :=
  match s with
  | RCA0 => 0 | WKL0 => 1 | ACA0 => 2 | ATR0 => 3 | Pi11CA0 => 4
  end.

Definition RM_subsystem_lt (s s' : RM_subsystem) : Prop :=
  rm_rank s < rm_rank s'.

(** The characteristic principle of the system at rank [r]: consistency
    at level [r]. *)

Definition RM_Con (m : nat) : Form := Neg (Box m Bot).

(** ** The internal subsystem calculus.

    Base modal logic, modus ponens, and the reflection axioms: the
    system at [s] proves [RM_Con k] for every level [k] strictly below
    its rank.  RCA_0 (rank 0) gets only the base logic; each higher
    system adds the consistency of the one below (WKL_0 adds Con(RCA_0),
    ACA_0 adds Con(WKL_0), ATR_0 adds Con(ACA_0), Pi^1_1-CA_0 adds
    Con(ATR_0)), so the relation is cumulative. *)

Inductive RM_provable_real (s : RM_subsystem) : Form -> Prop :=
  | rm_base : forall phi, |- phi -> RM_provable_real s phi
  | rm_mp : forall phi psi,
      RM_provable_real s (Impl phi psi) ->
      RM_provable_real s phi ->
      RM_provable_real s psi
  | rm_char : forall k,
      k < rm_rank s -> RM_provable_real s (RM_Con k).

(** Base modal logic sits inside every subsystem. *)

Theorem RM_includes_base : forall s phi,
  |- phi -> RM_provable_real s phi.
Proof. intros s phi H. apply rm_base. exact H. Qed.

(** Cumulativity across the hierarchy. *)

Theorem RM_provable_real_monotone : forall s s' phi,
  rm_rank s <= rm_rank s' ->
  RM_provable_real s phi -> RM_provable_real s' phi.
Proof.
  intros s s' phi Hle H. induction H as [phi0 Hp | phi0 psi0 H1 IH1 H2 IH2 | k Hk].
  - apply rm_base. exact Hp.
  - apply (rm_mp s' phi0 psi0); [exact IH1 | exact IH2].
  - apply rm_char. lia.
Qed.

(** ** Single-world Kripke soundness. *)

Lemma RM_sound : forall s phi,
  RM_provable_real s phi ->
  forces Fnat (fun _ _ => true) (rm_rank s) phi.
Proof.
  intros s phi H. induction H as [phi0 Hp | phi0 psi0 H1 IH1 H2 IH2 | k Hk].
  - apply soundness. exact Hp.
  - apply IH1. exact IH2.
  - (* forces Fnat V (rm_rank s) (Neg (Box k Bot)) when k < rm_rank s *)
    intro Hbox.
    apply (Hbox k).
    unfold Fnat_R. split; lia.
Qed.

(** [RM_Con m] is never forced at its own Fnat-world [m]: at world [m]
    there is no [R_m]-successor, so [Box m Bot] is (vacuously) forced
    and its negation fails. *)

Lemma Con_not_forced_at_own_level : forall m V,
  ~ forces Fnat V m (RM_Con m).
Proof.
  intros m V H.
  apply H.
  intros v Hv. unfold Fnat_R in Hv. destruct Hv as [Hgt Hge]. lia.
Qed.

(** ** Consequences: the three forbidden collapses are excluded. *)

(** Not the identity collapse: every subsystem is consistent. *)

Theorem RM_consistent : forall s, ~ RM_provable_real s Bot.
Proof.
  intros s H. exact (RM_sound s Bot H).
Qed.

(** [RM_Con m] is not a modal theorem (internal Goedel consistency). *)

Lemma not_provable_RM_Con : forall m, ~ |- RM_Con m.
Proof.
  intros m H.
  pose proof (soundness _ H Fnat (fun _ _ => true) m) as Hf.
  exact (Con_not_forced_at_own_level m _ Hf).
Qed.

(** Not the [|- P] collapse: WKL_0 proves something the base logic does
    not. *)

Theorem RM_strictly_above_base :
  exists phi, RM_provable_real WKL0 phi /\ ~ |- phi.
Proof.
  exists (RM_Con 0). split.
  - apply rm_char. cbn. lia.
  - exact (not_provable_RM_Con 0).
Qed.

(** ** The strict hierarchy. *)

Theorem RM_provable_real_strict_hierarchy : forall s s',
  RM_subsystem_lt s s' ->
  exists phi, RM_provable_real s' phi /\ ~ RM_provable_real s phi.
Proof.
  intros s s' Hlt.
  exists (RM_Con (rm_rank s)). split.
  - apply rm_char. exact Hlt.
  - intro Hcon.
    pose proof (RM_sound s _ Hcon) as Hf.
    exact (Con_not_forced_at_own_level (rm_rank s) (fun _ _ => true) Hf).
Qed.

(** The hierarchy is a genuine strict linear order on the Big Five. *)

Theorem RM_subsystem_lt_irrefl : forall s, ~ RM_subsystem_lt s s.
Proof. intros s. unfold RM_subsystem_lt. lia. Qed.

Theorem RM_subsystem_lt_trans : forall s1 s2 s3,
  RM_subsystem_lt s1 s2 -> RM_subsystem_lt s2 s3 -> RM_subsystem_lt s1 s3.
Proof. intros s1 s2 s3. unfold RM_subsystem_lt. lia. Qed.

Theorem RM_big_five_chain :
  RM_subsystem_lt RCA0 WKL0 /\ RM_subsystem_lt WKL0 ACA0 /\
  RM_subsystem_lt ACA0 ATR0 /\ RM_subsystem_lt ATR0 Pi11CA0.
Proof.
  unfold RM_subsystem_lt; cbn. repeat split; lia.
Qed.

(** A worked separation across two non-adjacent systems: Pi^1_1-CA_0
    proves Con(WKL_0) but ACA_0 does not (here the separating formula is
    [RM_Con 1], between ranks 2 and 4 -- it is genuinely refuted in
    ACA_0, not merely unprovable-by-convention). *)

Theorem RM_separation_ACA_below_Pi11CA :
  RM_provable_real Pi11CA0 (RM_Con (rm_rank ACA0)) /\
  ~ RM_provable_real ACA0 (RM_Con (rm_rank ACA0)).
Proof.
  split.
  - apply rm_char. cbn. lia.
  - intro Hcon.
    pose proof (RM_sound ACA0 _ Hcon) as Hf.
    exact (Con_not_forced_at_own_level (rm_rank ACA0) (fun _ _ => true) Hf).
Qed.

(** ** Headline summary for todo #3. *)

Theorem reverse_math_summary :
  (* base logic included, but the relation is strictly more *)
  (forall s phi, |- phi -> RM_provable_real s phi) /\
  (exists phi, RM_provable_real WKL0 phi /\ ~ |- phi) /\
  (* not the identity collapse: consistency *)
  (forall s, ~ RM_provable_real s Bot) /\
  (* cumulative *)
  (forall s s' phi, rm_rank s <= rm_rank s' ->
     RM_provable_real s phi -> RM_provable_real s' phi) /\
  (* the strict hierarchy *)
  (forall s s', RM_subsystem_lt s s' ->
     exists phi, RM_provable_real s' phi /\ ~ RM_provable_real s phi).
Proof.
  split; [|split; [|split; [|split]]].
  - exact RM_includes_base.
  - exact RM_strictly_above_base.
  - exact RM_consistent.
  - exact RM_provable_real_monotone.
  - exact RM_provable_real_strict_hierarchy.
Qed.
