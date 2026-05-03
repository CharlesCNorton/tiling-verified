(******************************************************************************)
(*                                                                            *)
(*           Parametric Provability: Bypassing the Löbian Obstacle            *)
(*                                                                            *)
(*     Formalizing parametric Löbian obstacle bypass. Yudkowsky-Herreshoff    *)
(*     tiling agents over a chain of proof systems.                           *)
(*                                                                            *)
(*     "Wir müssen wissen, wir werden wissen."                                *)
(*     - David Hilbert, 1930                                                  *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: May 2, 2026                                                      *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.Classical.
Import ListNotations.

(** Polymodal propositional formulas indexed by a natural-number "level".
    [Box n phi] reads: "phi is provable in the theory at level n."
    The propositional skeleton (Var, Bot, Impl) is classical; modal
    axioms are imposed in [Provable] below. *)

Inductive Form : Type :=
  | Var  : nat -> Form
  | Bot  : Form
  | Impl : Form -> Form -> Form
  | Box  : nat -> Form -> Form.

(** ** Derived connectives.
    We define negation, top, diamond (dual modality), conjunction,
    disjunction, and biconditional in terms of [Impl] and [Bot] in the
    standard classical way. *)

Definition Neg (phi : Form) : Form := Impl phi Bot.
Definition Top : Form := Impl Bot Bot.
Definition Diamond (n : nat) (phi : Form) : Form := Neg (Box n (Neg phi)).
Definition And (phi psi : Form) : Form := Neg (Impl phi (Neg psi)).
Definition Or (phi psi : Form) : Form := Impl (Neg phi) psi.
Definition Iff (phi psi : Form) : Form := And (Impl phi psi) (Impl psi phi).

(** ** Decidable equality on formulas.

    Infrastructure needed for any decision procedure on the calculus.
    Standard structural induction with [decide equality] on the
    [Form] inductive (with [Nat.eq_dec] for the [Var] and [Box]
    payloads). *)

Lemma Form_eq_dec : forall (f g : Form), {f = g} + {f <> g}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

(** GLP* is the Hilbert-style polymodal proof system used throughout.
    Its axioms are:

    - Classical propositional axioms (K, S, double-negation elimination).
    - For each level n: K and Loeb for [Box n].
    - Monotonicity across levels: [Box n phi -> Box (S n) phi].
    - NextCon: [Box (S n) (Neg (Box n Bot))], i.e., level (S n) proves
      that level n is consistent.

    Inference rules are modus ponens and necessitation at every level.
    Propositional consequence and modal-K give the standard "K-valid"
    derivable consequence; the Loeb axiom gives Goedel-Loeb provability
    behaviour at every level; monotonicity and NextCon give the tower
    structure required by Yudkowsky-Herreshoff 2013.

    Axiom 4 ([Box n phi -> Box n (Box n phi)]) is included primitively
    below as [Ax_Box4].  Boolos, "The Logic of Provability", 1993,
    Theorem 11, derives it from K + Loeb, but his proof routes through
    the de Jongh-Sambin fixed-point theorem and is non-elementary.
    Once a polymodal fixed-point theorem is added (todo item 36), the
    primitive axiom can be promoted to a derived theorem. *)

Inductive Provable : Form -> Prop :=
  (* Classical propositional axioms. *)
  | Ax_K   : forall phi psi,
      Provable (Impl phi (Impl psi phi))
  | Ax_S   : forall phi psi chi,
      Provable (Impl (Impl phi (Impl psi chi))
                     (Impl (Impl phi psi) (Impl phi chi)))
  | Ax_DN  : forall phi,
      Provable (Impl (Neg (Neg phi)) phi)
  (* Modal K and Loeb at every level. *)
  | Ax_BoxK : forall n phi psi,
      Provable (Impl (Box n (Impl phi psi))
                     (Impl (Box n phi) (Box n psi)))
  | Ax_Loeb : forall n phi,
      Provable (Impl (Box n (Impl (Box n phi) phi)) (Box n phi))
  | Ax_Box4 : forall n phi,
      Provable (Impl (Box n phi) (Box n (Box n phi)))
  (* Polymodal axioms. *)
  | Ax_Mon  : forall n phi,
      Provable (Impl (Box n phi) (Box (S n) phi))
  | Ax_NextCon : forall n,
      Provable (Box (S n) (Neg (Box n Bot)))
  (* Inference rules. *)
  | MP : forall phi psi,
      Provable (Impl phi psi) -> Provable phi -> Provable psi
  | Nec : forall n phi,
      Provable phi -> Provable (Box n phi).

Notation "|- f" := (Provable f) (at level 75, no associativity).

(** A small library of derived propositional facts.  We proceed in
    Hilbert style: every theorem is a chain of axioms and modus
    ponens.  These lemmas are reused throughout the development. *)

(** ** [phi -> phi] (reflexivity of implication) *)
Lemma prov_id : forall phi, |- Impl phi phi.
Proof.
  intro phi.
  (* Standard Hilbert proof: K, S, K, MP, MP. *)
  pose proof (Ax_S phi (Impl phi phi) phi) as Hs.
  pose proof (Ax_K phi (Impl phi phi)) as Hk1.
  pose proof (Ax_K phi phi) as Hk2.
  exact (MP _ _ (MP _ _ Hs Hk1) Hk2).
Qed.

(** ** Weakening: from [phi] derive [psi -> phi]. *)
Lemma prov_weaken : forall phi psi, |- phi -> |- Impl psi phi.
Proof.
  intros phi psi Hphi.
  exact (MP _ _ (Ax_K phi psi) Hphi).
Qed.

(** ** Composition / syllogism: from [phi -> psi] and [psi -> chi]
    derive [phi -> chi]. *)
Lemma prov_compose : forall phi psi chi,
  |- Impl phi psi -> |- Impl psi chi -> |- Impl phi chi.
Proof.
  intros phi psi chi Hpq Hqr.
  (* Use S applied to (Ax_K (psi -> chi) phi) to get
     (phi -> psi -> chi) -> (phi -> psi) -> (phi -> chi). *)
  pose proof (Ax_S phi psi chi) as Hs.
  pose proof (prov_weaken _ phi Hqr) as Hpqr.
  exact (MP _ _ (MP _ _ Hs Hpqr) Hpq).
Qed.

(** ** Permutation of antecedents. *)
Lemma prov_perm : forall phi psi chi,
  |- Impl phi (Impl psi chi) -> |- Impl psi (Impl phi chi).
Proof.
  intros phi psi chi H.
  pose proof (Ax_S phi psi chi) as Hs.
  pose proof (MP _ _ Hs H) as H1. (* (phi -> psi) -> (phi -> chi) *)
  pose proof (Ax_K psi phi) as Hk.   (* psi -> (phi -> psi) *)
  pose proof (prov_compose _ _ _ Hk H1) as H2. (* psi -> (phi -> chi) *)
  exact H2.
Qed.

(** ** Three-place modus ponens / chained MP. *)
Lemma prov_mp2 : forall phi psi chi,
  |- Impl phi (Impl psi chi) -> |- phi -> |- psi -> |- chi.
Proof.
  intros phi psi chi H Hphi Hpsi.
  exact (MP _ _ (MP _ _ H Hphi) Hpsi).
Qed.

(** ** Double negation introduction: [phi -> ~~phi]. *)
Lemma prov_DN_intro : forall phi, |- Impl phi (Neg (Neg phi)).
Proof.
  intro phi.
  unfold Neg.
  (* Goal: |- Impl phi (Impl (Impl phi Bot) Bot). *)
  (* First derive: |- Impl (Impl phi Bot) (Impl phi Bot)  (= prov_id). *)
  pose proof (prov_id (Impl phi Bot)) as Hid.
  (* Permute antecedents: (phi -> Bot) -> (phi -> Bot)  =>  phi -> ((phi -> Bot) -> Bot). *)
  exact (prov_perm _ _ _ Hid).
Qed.

(** ** Ex falso: [Bot -> phi]. *)
Lemma prov_explosion : forall phi, |- Impl Bot phi.
Proof.
  intro phi.
  (* Bot -> Bot is just prov_id. *)
  pose proof (prov_id Bot) as HBB.
  (* Bot -> ((phi -> Bot) -> Bot)  by Ax_K applied to HBB twice: actually
     we want Bot -> phi, not via DN.  Use Ax_DN: ~~phi -> phi.
     We need: Bot -> ~~phi -> phi via Ax_K then composition. *)
  pose proof (Ax_K Bot (Neg phi)) as Hk. (* Bot -> ((phi -> Bot) -> Bot) *)
  (* Goal: Bot -> phi.
     We have Bot -> ~~phi (= Bot -> ((phi -> Bot) -> Bot)) since (Neg phi = phi -> Bot)
     and Ax_DN: ~~phi -> phi. *)
  pose proof (Ax_DN phi) as HDN.
  exact (prov_compose _ _ _ Hk HDN).
Qed.

(** ** Internal composition: [(psi -> chi) -> (phi -> psi) -> (phi -> chi)]. *)
Lemma prov_compose_internal : forall phi psi chi,
  |- Impl (Impl psi chi) (Impl (Impl phi psi) (Impl phi chi)).
Proof.
  intros phi psi chi.
  pose proof (Ax_K (Impl psi chi) phi) as Hk.
  pose proof (Ax_S phi psi chi) as Hs.
  exact (prov_compose _ _ _ Hk Hs).
Qed.

(** ** Internal permutation: [(a -> b -> c) -> (b -> a -> c)] as a
    single provable formula.

    The metatheorem [prov_perm] swaps antecedents at the proof level;
    this lemma is its internal Hilbert form, derivable from the
    propositional axioms K and S without any modal axioms. *)

Lemma prov_perm_internal : forall a b c,
  |- Impl (Impl a (Impl b c)) (Impl b (Impl a c)).
Proof.
  intros a b c.
  (* Step 1: Ax_S a b c = (a -> b -> c) -> ((a -> b) -> (a -> c)). *)
  pose proof (Ax_S a b c) as H_S.
  (* Step 2: Ax_S over (a -> b -> c) -> ((a -> b) -> (a -> c)) feeding
     the result through. *)
  pose proof (Ax_S (Impl a (Impl b c)) (Impl a b) (Impl a c)) as H_S2.
  (* H1 : ((a -> b -> c) -> (a -> b)) -> ((a -> b -> c) -> (a -> c)). *)
  pose proof (MP _ _ H_S2 H_S) as H1.
  (* Step 3: from b derive (a -> b) (Ax_K), and weaken to "(a -> b -> c) -> (a -> b)". *)
  pose proof (Ax_K b a) as H_K1.
  pose proof (Ax_K (Impl a b) (Impl a (Impl b c))) as H_K2.
  pose proof (prov_compose _ _ _ H_K1 H_K2) as H2.
  (* H2 : b -> ((a -> b -> c) -> (a -> b)). *)
  (* H3 : b -> ((a -> b -> c) -> (a -> c)) by composing H2 and H1. *)
  pose proof (prov_compose _ _ _ H2 H1) as H3.
  (* Goal: (a -> b -> c) -> (b -> (a -> c)).  Permute H3. *)
  exact (prov_perm _ _ _ H3).
Qed.

(** ** And-introduction: [|- phi -> psi -> phi /\ psi].

    Unfolds via [And phi psi := Neg (Impl phi (Neg psi))] to
    [|- phi -> psi -> (phi -> psi -> Bot) -> Bot].  The proof is a
    chain: start with [prov_id (phi -> psi -> Bot)], permute the
    outermost antecedent into position 3 using [prov_perm] then
    [prov_perm_internal] under one layer. *)

Lemma prov_and_intro : forall phi psi,
  |- Impl phi (Impl psi (And phi psi)).
Proof.
  intros phi psi.
  unfold And, Neg.
  (* Goal: |- Impl phi (Impl psi (Impl (Impl phi (Impl psi Bot)) Bot)). *)
  pose proof (prov_id (Impl phi (Impl psi Bot))) as Hid.
  pose proof (prov_perm _ _ _ Hid) as Hperm.
  pose proof (prov_perm_internal (Impl phi (Impl psi Bot)) psi Bot) as Hpi.
  exact (prov_compose _ _ _ Hperm Hpi).
Qed.

(** ** And-introduction in metatheorem form: from [|- phi] and [|- psi]
    derive [|- And phi psi].  Two MPs against [prov_and_intro]. *)

Lemma prov_and_intro_meta : forall phi psi,
  |- phi -> |- psi -> |- And phi psi.
Proof.
  intros phi psi Hphi Hpsi.
  exact (MP _ _ (MP _ _ (prov_and_intro phi psi) Hphi) Hpsi).
Qed.

(** ** From a negation derive any implication landing in a negation:
    [Neg phi -> (phi -> Neg psi)].

    Internal form of "if [phi] is impossible, then any consequence
    landing in a negation also follows."  Used in [prov_and_elim_l]. *)

Lemma prov_neg_imp_ng : forall phi psi,
  |- Impl (Neg phi) (Impl phi (Neg psi)).
Proof.
  intros phi psi.
  unfold Neg.
  pose proof (prov_compose_internal phi Bot (Impl psi Bot)) as Hci.
  pose proof (prov_explosion (Impl psi Bot)) as Hex.
  exact (MP _ _ Hci Hex).
Qed.

(** ** And-elimination (left): [|- (phi /\ psi) -> phi].

    Unfolded: [|- ((phi -> Neg psi) -> Bot) -> phi].
    Proof via classical double-negation: from [(phi -> Neg psi) -> Bot]
    derive [Neg phi -> Bot] (i.e. [Neg (Neg phi)]) by feeding a [Neg phi]
    through [prov_neg_imp_ng], then apply [Ax_DN]. *)

Lemma prov_and_elim_l : forall phi psi,
  |- Impl (And phi psi) phi.
Proof.
  intros phi psi.
  unfold And, Neg.
  (* Goal: |- Impl (Impl (Impl phi (Impl psi Bot)) Bot) phi. *)
  pose proof (prov_neg_imp_ng phi psi) as H1.
  (* H1 : |- Impl (Impl phi Bot) (Impl phi (Impl psi Bot)). *)
  pose proof (prov_compose_internal
                (Impl phi Bot)
                (Impl phi (Impl psi Bot))
                Bot) as H2.
  (* H2 : |- Impl (Impl (Impl phi (Impl psi Bot)) Bot)
                  (Impl (Impl (Impl phi Bot) (Impl phi (Impl psi Bot)))
                        (Impl (Impl phi Bot) Bot)). *)
  pose proof (prov_perm _ _ _ H2) as H2_perm.
  pose proof (MP _ _ H2_perm H1) as Hstep1.
  (* Hstep1 : |- Impl (Impl (Impl phi (Impl psi Bot)) Bot)
                      (Impl (Impl phi Bot) Bot). *)
  pose proof (Ax_DN phi) as HDN.
  (* HDN: |- Impl (Impl (Impl phi Bot) Bot) phi. *)
  exact (prov_compose _ _ _ Hstep1 HDN).
Qed.

(** ** And-elimination (right): [|- (phi /\ psi) -> psi].

    Symmetric to [prov_and_elim_l] but extracts the right component.
    From [psi -> (phi -> psi)] (Ax_K) and the [(phi -> Neg psi) -> Bot]
    hypothesis, double-negation elimination delivers [psi]. *)

Lemma prov_and_elim_r : forall phi psi,
  |- Impl (And phi psi) psi.
Proof.
  intros phi psi.
  unfold And, Neg.
  pose proof (Ax_K (Impl psi Bot) phi) as H1.
  pose proof (prov_compose_internal
                (Impl psi Bot)
                (Impl phi (Impl psi Bot))
                Bot) as H2.
  pose proof (prov_perm _ _ _ H2) as H2_perm.
  pose proof (MP _ _ H2_perm H1) as Hstep1.
  pose proof (Ax_DN psi) as HDN.
  exact (prov_compose _ _ _ Hstep1 HDN).
Qed.

(** ** And-elimination metatheorem (left): from [|- And phi psi]
    derive [|- phi]. *)

Lemma prov_and_elim_l_meta : forall phi psi,
  |- And phi psi -> |- phi.
Proof.
  intros phi psi Hand.
  exact (MP _ _ (prov_and_elim_l phi psi) Hand).
Qed.

(** ** And-elimination metatheorem (right). *)

Lemma prov_and_elim_r_meta : forall phi psi,
  |- And phi psi -> |- psi.
Proof.
  intros phi psi Hand.
  exact (MP _ _ (prov_and_elim_r phi psi) Hand).
Qed.

(** ** Box-And-elimination (left): [|- Box n (phi /\ psi) -> Box n phi].

    Pure K-distribution: necessitate [prov_and_elim_l] and feed
    through [Ax_BoxK]. *)

Lemma prov_box_and_elim_l : forall n phi psi,
  |- Impl (Box n (And phi psi)) (Box n phi).
Proof.
  intros n phi psi.
  pose proof (prov_and_elim_l phi psi) as Hand.
  pose proof (Nec n _ Hand) as Hnec.
  pose proof (Ax_BoxK n (And phi psi) phi) as HBK.
  exact (MP _ _ HBK Hnec).
Qed.

(** ** Box-And-elimination (right): [|- Box n (phi /\ psi) -> Box n psi].

    Symmetric counterpart of [prov_box_and_elim_l]. *)

Lemma prov_box_and_elim_r : forall n phi psi,
  |- Impl (Box n (And phi psi)) (Box n psi).
Proof.
  intros n phi psi.
  pose proof (prov_and_elim_r phi psi) as Hand.
  pose proof (Nec n _ Hand) as Hnec.
  pose proof (Ax_BoxK n (And phi psi) psi) as HBK.
  exact (MP _ _ HBK Hnec).
Qed.

(** ** Box-And introduction.

    If level [n] proves [phi] and proves [psi], then level [n] proves
    their conjunction.  The "easy" direction of K-distribution over And. *)

Lemma prov_box_and_intro : forall n phi psi,
  |- Impl (Box n phi) (Impl (Box n psi) (Box n (And phi psi))).
Proof.
  intros n phi psi.
  pose proof (prov_and_intro phi psi) as Hand.
  pose proof (Nec n _ Hand) as Hnec.
  pose proof (Ax_BoxK n phi (Impl psi (And phi psi))) as HBK1.
  pose proof (MP _ _ HBK1 Hnec) as Hstep1.
  pose proof (Ax_BoxK n psi (And phi psi)) as HBK2.
  exact (prov_compose _ _ _ Hstep1 HBK2).
Qed.

(** ** Box-And full distribution.

    The converse of [prov_box_and_intro]:
    [|- Box n (And phi psi) -> And (Box n phi) (Box n psi)].
    Combined with [prov_box_and_intro] (in metatheorem MP-form) this
    gives the full K-distribution-over-And biconditional. *)

Lemma prov_box_and_distrib_fwd : forall n phi psi,
  |- Impl (Box n (And phi psi)) (And (Box n phi) (Box n psi)).
Proof.
  intros n phi psi.
  pose proof (prov_box_and_elim_l n phi psi) as HL.
  pose proof (prov_box_and_elim_r n phi psi) as HR.
  pose proof (prov_and_intro (Box n phi) (Box n psi)) as Hand.
  (* Hand : |- Box n phi -> Box n psi -> And (Box n phi) (Box n psi). *)
  pose proof (prov_compose_internal
                (Box n (And phi psi))
                (Box n phi)
                (Impl (Box n psi) (And (Box n phi) (Box n psi)))) as Hci.
  pose proof (MP _ _ Hci Hand) as Hstep1.
  pose proof (MP _ _ Hstep1 HL) as Hstep2.
  (* Hstep2 : |- Box n (And phi psi) ->
                  (Box n psi -> And (Box n phi) (Box n psi)). *)
  pose proof (Ax_S
                (Box n (And phi psi))
                (Box n psi)
                (And (Box n phi) (Box n psi))) as Hs.
  pose proof (MP _ _ Hs Hstep2) as Hstep3.
  (* Hstep3 : |- (Box n (And phi psi) -> Box n psi) ->
                 (Box n (And phi psi) -> And (Box n phi) (Box n psi)). *)
  exact (MP _ _ Hstep3 HR).
Qed.

(** ** Contraposition (one direction): [(phi -> psi) -> (~psi -> ~phi)]. *)
Lemma prov_contrapos : forall phi psi,
  |- Impl (Impl phi psi) (Impl (Neg psi) (Neg phi)).
Proof.
  intros phi psi.
  unfold Neg.
  (* prov_compose_internal phi psi Bot gives
     (psi -> Bot) -> ((phi -> psi) -> (phi -> Bot)),
     and we need the perm of that. *)
  exact (prov_perm _ _ _ (prov_compose_internal phi psi Bot)).
Qed.

(** ** Contraposition (converse direction): [(~psi -> ~phi) -> (phi -> psi)].

    Together with [prov_contrapos] this gives the full classical
    contrapositive equivalence.  The proof uses double-negation
    elimination: from [(psi -> Bot) -> (phi -> Bot)] and [phi],
    derive [(psi -> Bot) -> Bot] (i.e., [Neg (Neg psi)]), then apply
    [Ax_DN]. *)

Lemma prov_contrapos_converse : forall phi psi,
  |- Impl (Impl (Neg psi) (Neg phi)) (Impl phi psi).
Proof.
  intros phi psi.
  unfold Neg.
  (* H_perm : ((psi -> Bot) -> (phi -> Bot)) -> (phi -> ((psi -> Bot) -> Bot)). *)
  pose proof (prov_perm_internal (Impl psi Bot) phi Bot) as H_perm.
  (* HDN : ((psi -> Bot) -> Bot) -> psi. *)
  pose proof (Ax_DN psi) as HDN.
  (* Hci : (((psi -> Bot) -> Bot) -> psi) ->
           ((phi -> ((psi -> Bot) -> Bot)) -> (phi -> psi)). *)
  pose proof (prov_compose_internal phi
                (Impl (Impl psi Bot) Bot) psi) as Hci.
  pose proof (MP _ _ Hci HDN) as Hstep.
  exact (prov_compose _ _ _ H_perm Hstep).
Qed.

(** ** Consequentia mirabilis: [(Neg chi -> chi) -> chi].

    A classical principle equivalent to double-negation elimination
    in the presence of [Ax_DN].  Used in the Or-elimination proof
    below. *)

Lemma prov_consequentia_mirabilis : forall chi,
  |- Impl (Impl (Neg chi) chi) chi.
Proof.
  intro chi.
  unfold Neg.
  (* From prov_id (Impl chi Bot) and Ax_S, derive
     (Impl (Impl chi Bot) chi) -> (Impl (Impl chi Bot) Bot),
     i.e., (Neg chi -> chi) -> Neg (Neg chi).  Then apply Ax_DN. *)
  pose proof (prov_id (Impl chi Bot)) as Hid.
  pose proof (Ax_S (Impl chi Bot) chi Bot) as Hs.
  pose proof (MP _ _ Hs Hid) as Hstep1.
  pose proof (Ax_DN chi) as HDN.
  exact (prov_compose _ _ _ Hstep1 HDN).
Qed.

(** ** Or-introduction (left): [|- phi -> Or phi psi].

    Unfolds to [|- phi -> (Neg phi -> psi)].  Classical: from [phi]
    and [Neg phi] derive [Bot] then anything. *)

Lemma prov_or_intro_l : forall phi psi,
  |- Impl phi (Or phi psi).
Proof.
  intros phi psi.
  unfold Or.
  pose proof (prov_explosion psi) as Hexp.
  pose proof (prov_compose_internal (Neg phi) Bot psi) as Hci.
  pose proof (MP _ _ Hci Hexp) as HX.
  (* HX : |- (Neg phi -> Bot) -> (Neg phi -> psi). *)
  pose proof (prov_DN_intro phi) as HDN.
  (* HDN : |- phi -> (Neg phi -> Bot). *)
  exact (prov_compose _ _ _ HDN HX).
Qed.

(** ** Or-introduction (right): [|- psi -> Or phi psi].

    Trivial via [Ax_K]: [psi] implies [Neg phi -> psi]. *)

Lemma prov_or_intro_r : forall phi psi,
  |- Impl psi (Or phi psi).
Proof.
  intros phi psi.
  unfold Or.
  exact (Ax_K psi (Neg phi)).
Qed.

(** ** Apply-two-under-outer-impl.

    From [|- A -> (B -> (C -> R))], [|- B], and [|- C], derive
    [|- A -> R].  Used to plug constant arguments into a multi-arg
    Hilbert formula while leaving an outer antecedent open. *)

Lemma prov_apply2 : forall A B C R,
  |- Impl A (Impl B (Impl C R)) -> |- B -> |- C -> |- Impl A R.
Proof.
  intros A B C R Hf Hb Hc.
  pose proof (Ax_S A B (Impl C R)) as Hs1.
  pose proof (MP _ _ Hs1 Hf) as Hstep1.
  pose proof (Ax_K B A) as HK_b.
  pose proof (MP _ _ HK_b Hb) as HAB.
  pose proof (MP _ _ Hstep1 HAB) as Hstep2.
  pose proof (Ax_S A C R) as Hs2.
  pose proof (MP _ _ Hs2 Hstep2) as Hstep3.
  pose proof (Ax_K C A) as HK_c.
  pose proof (MP _ _ HK_c Hc) as HAC.
  exact (MP _ _ Hstep3 HAC).
Qed.

(** ** Compose-under-shared-antecedent.

    From [|- A -> (B -> C)] and [|- D -> B] derive [|- A -> (D -> C)].
    Pre-composes with [g] under a shared outer antecedent [A]. *)

Lemma prov_compose_under : forall A B C D,
  |- Impl A (Impl B C) -> |- Impl D B -> |- Impl A (Impl D C).
Proof.
  intros A B C D Hf Hg.
  pose proof (prov_compose_internal D B C) as HCI.
  pose proof (prov_perm _ _ _ HCI) as HCI_perm.
  (* HCI_perm : |- (D -> B) -> ((B -> C) -> (D -> C)). *)
  pose proof (MP _ _ HCI_perm Hg) as HX.
  (* HX : |- (B -> C) -> (D -> C). *)
  exact (prov_compose _ _ _ Hf HX).
Qed.

(** ** Two-place forward chaining combinator.

    From [A -> B -> C] and [C -> D], derive [A -> B -> D].
    Equivalently as a single Hilbert formula:
    [(A -> B -> C) -> (C -> D) -> (A -> B -> D)]. *)

Lemma prov_chain_2 : forall A B C D,
  |- Impl (Impl A (Impl B C))
          (Impl (Impl C D) (Impl A (Impl B D))).
Proof.
  intros A B C D.
  pose proof (prov_compose_internal B C D) as H1.
  pose proof (prov_compose_internal A (Impl B C) (Impl B D)) as H2.
  pose proof (prov_compose _ _ _ H1 H2) as H3.
  exact (prov_perm _ _ _ H3).
Qed.

(** ** Or-elimination.

    Classical disjunction elimination: from [Or phi psi], [phi -> chi],
    and [psi -> chi], derive [chi].  In our system, [Or phi psi]
    unfolds to [Neg phi -> psi], so the goal is

      |- (Neg phi -> psi) -> (phi -> chi) -> (psi -> chi) -> chi.

    Proof chain: from [phi -> chi] derive [Neg chi -> Neg phi] by
    contrapos; compose with [Neg phi -> psi] to get [Neg chi -> psi];
    compose with [psi -> chi] to get [Neg chi -> chi]; apply
    consequentia mirabilis to get [chi]. *)

Lemma prov_or_elim : forall phi psi chi,
  |- Impl (Or phi psi)
       (Impl (Impl phi chi) (Impl (Impl psi chi) chi)).
Proof.
  intros phi psi chi.
  unfold Or.
  pose proof (prov_contrapos phi chi) as HCP.
  pose proof (prov_compose_internal (Neg chi) (Neg phi) psi) as HCI1.
  pose proof (prov_compose_internal (Neg chi) psi chi) as HCI2.
  pose proof (prov_consequentia_mirabilis chi) as HCM.
  (* HA : (Neg phi -> psi) -> ((phi -> chi) -> (Neg chi -> psi)). *)
  pose proof (prov_compose_under
                (Impl (Neg phi) psi)
                (Impl (Neg chi) (Neg phi))
                (Impl (Neg chi) psi)
                (Impl phi chi)
                HCI1 HCP) as HA.
  (* HCH : combine HCI2 and HCM via prov_chain_2 to derive
     (psi -> chi) -> ((Neg chi -> psi) -> chi). *)
  pose proof (prov_chain_2
                (Impl psi chi)
                (Impl (Neg chi) psi)
                (Impl (Neg chi) chi)
                chi) as HCH.
  pose proof (MP _ _ HCH HCI2) as HCH1.
  pose proof (MP _ _ HCH1 HCM) as HB.
  (* HB : (psi -> chi) -> ((Neg chi -> psi) -> chi). *)
  pose proof (prov_perm _ _ _ HB) as HB_perm.
  (* HB_perm : (Neg chi -> psi) -> ((psi -> chi) -> chi). *)
  pose proof (prov_chain_2
                (Impl (Neg phi) psi)
                (Impl phi chi)
                (Impl (Neg chi) psi)
                (Impl (Impl psi chi) chi)) as HCH2.
  pose proof (MP _ _ HCH2 HA) as HCH2_1.
  exact (MP _ _ HCH2_1 HB_perm).
Qed.

(** ** K-distribution over Or: [|- Or (Box n phi) (Box n psi) -> Box n (Or phi psi)].

    Standard K-modal-logic theorem: from a (classical) disjunction
    of boxed claims at level n, derive a box of the disjunction.
    Proof by classical Or-elim with the two Box-friendly directions. *)

Lemma prov_box_or_intro : forall n phi psi,
  |- Impl (Or (Box n phi) (Box n psi)) (Box n (Or phi psi)).
Proof.
  intros n phi psi.
  pose proof (prov_or_intro_l phi psi) as Holil.
  pose proof (Nec n _ Holil) as HNl.
  pose proof (Ax_BoxK n phi (Or phi psi)) as HBKl.
  pose proof (MP _ _ HBKl HNl) as Hbol.
  pose proof (prov_or_intro_r phi psi) as Holir.
  pose proof (Nec n _ Holir) as HNr.
  pose proof (Ax_BoxK n psi (Or phi psi)) as HBKr.
  pose proof (MP _ _ HBKr HNr) as Hbor.
  pose proof (prov_or_elim (Box n phi) (Box n psi) (Box n (Or phi psi))) as Hoe.
  exact (prov_apply2 _ _ _ _ Hoe Hbol Hbor).
Qed.

(** ** Modus tollens (derived form): [phi -> psi] and [~psi] yield [~phi]. *)
Lemma prov_mt : forall phi psi,
  |- Impl phi psi -> |- Neg psi -> |- Neg phi.
Proof.
  intros phi psi Himp Hnpsi.
  exact (MP _ _ (MP _ _ (prov_contrapos phi psi) Himp) Hnpsi).
Qed.

(** ** From [phi] and [~phi] derive [psi] (ex contradictione quodlibet). *)
Lemma prov_explode : forall phi psi,
  |- phi -> |- Neg phi -> |- psi.
Proof.
  intros phi psi Hphi Hnp.
  (* Apply Hnp (= phi -> Bot) to Hphi to get Bot, then apply prov_explosion. *)
  pose proof (MP _ _ Hnp Hphi) as Hbot.
  exact (MP _ _ (prov_explosion psi) Hbot).
Qed.

(** All [Box n] satisfy axiom K and the necessitation rule.  We derive
    their working forms here. *)

(** ** Internal modus ponens at level n. *)
Lemma prov_box_mp : forall n phi psi,
  |- Box n (Impl phi psi) -> |- Box n phi -> |- Box n psi.
Proof.
  intros n phi psi Himp Hphi.
  exact (MP _ _ (MP _ _ (Ax_BoxK n phi psi) Himp) Hphi).
Qed.

(** ** Necessitation lifts an implication. *)
Lemma prov_box_imp : forall n phi psi,
  |- Impl phi psi -> |- Impl (Box n phi) (Box n psi).
Proof.
  intros n phi psi H.
  exact (MP _ _ (Ax_BoxK n phi psi) (Nec n _ H)).
Qed.

(** ** Composition through Box. *)
Lemma prov_box_compose : forall n phi psi chi,
  |- Impl phi psi -> |- Impl psi chi ->
  |- Impl (Box n phi) (Box n chi).
Proof.
  intros n phi psi chi H1 H2.
  exact (prov_box_imp n _ _ (prov_compose _ _ _ H1 H2)).
Qed.

(** ** Two-step internal MP at level n. *)
Lemma prov_box_mp2 : forall n phi psi chi,
  |- Box n (Impl phi (Impl psi chi)) ->
  |- Box n phi -> |- Box n psi -> |- Box n chi.
Proof.
  intros n phi psi chi Himp Hphi Hpsi.
  exact (prov_box_mp n _ _ (prov_box_mp n _ _ Himp Hphi) Hpsi).
Qed.

(** ** [Box n] of an axiom is provable.  Just Nec + the axiom. *)
Lemma prov_box_K_inst : forall n phi psi,
  |- Box n (Impl phi (Impl psi phi)).
Proof.
  intros n phi psi; exact (Nec n _ (Ax_K phi psi)).
Qed.

(** ** Box-modus-tollens.

    If [Box n] proves [phi -> psi] and [Box n] proves [Neg psi], then
    [Box n] proves [Neg phi].  Internalized contraposition at level
    [n], useful for forward proofs about consistency. *)

Lemma prov_box_mt : forall n phi psi,
  |- Impl (Box n (Impl phi psi))
          (Impl (Box n (Neg psi)) (Box n (Neg phi))).
Proof.
  intros n phi psi.
  pose proof (prov_contrapos phi psi) as Hcp.
  pose proof (Nec n _ Hcp) as Hnec.
  pose proof (Ax_BoxK n (Impl phi psi) (Impl (Neg psi) (Neg phi))) as HBK1.
  pose proof (MP _ _ HBK1 Hnec) as Hstep1.
  pose proof (Ax_BoxK n (Neg psi) (Neg phi)) as HBK2.
  exact (prov_compose _ _ _ Hstep1 HBK2).
Qed.

(** ** Box-Diamond duality (definitional).

    By the very definition of [Diamond n phi := Neg (Box n (Neg phi))],
    the iff holds by [prov_id] in both directions. *)

Lemma prov_diamond_def : forall n phi,
  |- Iff (Diamond n phi) (Neg (Box n (Neg phi))).
Proof.
  intros n phi.
  unfold Iff, Diamond.
  apply prov_and_intro_meta.
  - exact (prov_id (Neg (Box n (Neg phi)))).
  - exact (prov_id (Neg (Box n (Neg phi)))).
Qed.

(** ** Box-Diamond duality (DN form): [|- Iff (Box n phi) (Neg (Diamond n (Neg phi)))].

    Standard classical-modal duality.  Both directions go through
    classical double-negation lifted under [Box] via [prov_box_imp]. *)

Lemma prov_box_neg_diamond : forall n phi,
  |- Iff (Box n phi) (Neg (Diamond n (Neg phi))).
Proof.
  intros n phi.
  unfold Iff, Diamond.
  (* Direction 1: Box n phi -> Neg (Neg (Box n (Neg (Neg phi)))). *)
  pose proof (prov_DN_intro phi) as Hdn1.
  pose proof (prov_box_imp n _ _ Hdn1) as Hb1.
  pose proof (prov_DN_intro (Box n (Neg (Neg phi)))) as Hdn2.
  pose proof (prov_compose _ _ _ Hb1 Hdn2) as HD1.
  (* Direction 2: Neg (Neg (Box n (Neg (Neg phi)))) -> Box n phi. *)
  pose proof (Ax_DN (Box n (Neg (Neg phi)))) as Hdn3.
  pose proof (Ax_DN phi) as Hdn4.
  pose proof (prov_box_imp n _ _ Hdn4) as Hb2.
  pose proof (prov_compose _ _ _ Hdn3 Hb2) as HD2.
  exact (prov_and_intro_meta _ _ HD1 HD2).
Qed.

(** Loeb's metatheorem.  This is the central derived rule of GL: if
    [Box n phi -> phi] is provable, so is [phi].  In Goedel-Loeb's
    arithmetic interpretation (where [Box] is the formal provability
    predicate of PA), this corresponds to: from [PA proves "Bew(phi)
    -> phi"], conclude [PA proves phi].

    The proof uses only the Loeb axiom, necessitation, and modus
    ponens; in particular it does not need axiom 4. *)

Theorem loeb_metatheorem : forall n phi,
  |- Impl (Box n phi) phi -> |- phi.
Proof.
  intros n phi Hsound.
  (* Nec gives: |- Box n (Box n phi -> phi). *)
  pose proof (Nec n _ Hsound) as Hnec.
  (* Loeb axiom: |- Box n (Box n phi -> phi) -> Box n phi. *)
  pose proof (Ax_Loeb n phi) as HLoeb.
  (* MP gives: |- Box n phi. *)
  pose proof (MP _ _ HLoeb Hnec) as Hbox.
  (* Combined with Hsound by MP: |- phi. *)
  exact (MP _ _ Hsound Hbox).
Qed.


(** The Loebian obstacle in Yudkowsky-Herreshoff 2013 is the assertion
    that a single fixed theory cannot prove its own soundness without
    becoming inconsistent.  In Goedel-Loeb form: any [Box]-modality
    that satisfies [Box phi -> phi] uniformly over [phi] is the
    modality of an inconsistent theory.

    The proof is a one-line corollary of the Loeb metatheorem,
    instantiated at [phi := Bot].  This is the obstacle that the
    parametric [T_kappa] construction in Section 9 will bypass. *)

Theorem loebian_obstacle : forall n,
  (forall phi, |- Impl (Box n phi) phi) -> |- Bot.
Proof.
  intros n Hsound.
  exact (loeb_metatheorem n Bot (Hsound Bot)).
Qed.

(** At a single level [n], if both [phi] and its negation are
    internally provable, then so is [Bot] — i.e., level [n] is
    inconsistent.  This is the K-internalization of the propositional
    fact that [phi] and [Neg phi] together imply [Bot]. *)

Lemma prov_box_n_contradiction : forall n phi,
  |- Impl (Box n phi) (Impl (Box n (Neg phi)) (Box n Bot)).
Proof.
  intros n phi.
  (* Step 1: |- Impl phi (Impl (Neg phi) Bot)  is just prov_DN_intro. *)
  pose proof (prov_DN_intro phi) as Hpnnp.
  (* Step 2: Necessitate at level n. *)
  pose proof (Nec n _ Hpnnp) as Hnec.
  (* Step 3: Ax_BoxK to peel off the outer Box. *)
  pose proof (Ax_BoxK n phi (Impl (Neg phi) Bot)) as HBK1.
  pose proof (MP _ _ HBK1 Hnec) as Hstep1.
  (* Hstep1 : |- Impl (Box n phi) (Box n (Impl (Neg phi) Bot)). *)
  (* Step 4: Ax_BoxK to peel off the inner Box from (Neg phi -> Bot). *)
  pose proof (Ax_BoxK n (Neg phi) Bot) as HBK2.
  (* HBK2 : |- Impl (Box n (Impl (Neg phi) Bot))
                    (Impl (Box n (Neg phi)) (Box n Bot)). *)
  (* Compose Hstep1 and HBK2. *)
  exact (prov_compose _ _ _ Hstep1 HBK2).
Qed.

(** The central positive result: at level [S n], the modality proves
    that level-[n] provability of [phi] excludes level-[n] provability
    of [Neg phi].

    This is the "consistency tiling" property of YH 2013 in modal
    abstraction: the theory at the strictly higher level [S n] verifies
    the consistency-of-phi-at-level-n property internally.  It is
    provable from the tower axioms (NextCon and Ax_BoxK) alone, no
    arithmetisation required.

    The Loebian obstacle (Section 6) ruled out the same statement at
    level n inside [Box n] itself; the tiling theorem here recovers
    the property by promoting it one level up. *)

Theorem tiling_consistency : forall n phi,
  |- Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi)))).
Proof.
  intros n phi.
  (* H1 : |- Impl (Box n phi) (Impl (Box n (Neg phi)) (Box n Bot)). *)
  pose proof (prov_box_n_contradiction n phi) as H1.
  (* H1n : |- Box (S n) (Impl (Box n phi) (Impl (Box n (Neg phi)) (Box n Bot))). *)
  pose proof (Nec (S n) _ H1) as H1n.
  (* H2 : |- Box (S n) (Neg (Box n Bot))
         = |- Box (S n) (Impl (Box n Bot) Bot). *)
  pose proof (Ax_NextCon n) as H2.
  (* H3 : the propositional chain combinator at A,B,C,D := Box n phi,
     Box n (Neg phi), Box n Bot, Bot. *)
  pose proof (prov_chain_2 (Box n phi) (Box n (Neg phi)) (Box n Bot) Bot) as H3.
  (* H3n : the chain combinator necessitated at level (S n). *)
  pose proof (Nec (S n) _ H3) as H3n.
  (* Apply prov_box_mp twice: first feed H1n into H3n, then feed H2. *)
  pose proof (prov_box_mp (S n) _ _ H3n H1n) as H4.
  pose proof (prov_box_mp (S n) _ _ H4 H2) as H5.
  exact H5.
Qed.

(** YH 2013 indexes a sequence of theories [T_0, T_1, T_2, ...] where
    each [T_{k+1}] strictly extends [T_k] with the consistency of
    [T_k].  Our polymodal axioms encode exactly this:

    - [Ax_Mon n phi] = [T_n |- phi] implies [T_{n+1} |- phi]:
      higher-indexed theories prove at least everything lower ones do.
    - [Ax_NextCon n] = [T_{n+1}] proves [Con(T_n)]:
      the strictly higher theory verifies consistency of the strictly
      lower one.

    Applying these axioms at multiple levels yields the chain
    [T_k |- Con(T_n)] for every [k > n], which we prove formally below. *)

(** ** Iterated monotonicity.

    The single-step monotonicity axiom [Box n phi -> Box (S n) phi]
    extends to an arbitrary jump [Box n phi -> Box m phi] whenever
    [n <= m].  Proof is by induction on the order proof. *)

Lemma prov_box_mon_le : forall n m phi,
  n <= m -> |- Impl (Box n phi) (Box m phi).
Proof.
  intros n m phi Hle.
  induction Hle as [| m' Hle' IH].
  - exact (prov_id (Box n phi)).
  - exact (prov_compose _ _ _ IH (Ax_Mon m' phi)).
Qed.

(** ** The consistency chain.

    For any two levels [n < k], the level-[k] theory proves the
    consistency of the level-[n] theory.  This is the FS2014-style
    "all levels above n agree on n's consistency" claim.

    Proof: NextCon gives the immediate-successor case [Box (S n)
    (Neg (Box n Bot))]; iterated monotonicity lifts it to any [Box k]
    for [k >= S n], i.e., for [k > n]. *)

Theorem consistency_chain : forall n k,
  n < k -> |- Box k (Neg (Box n Bot)).
Proof.
  intros n k Hlt.
  pose proof (Ax_NextCon n) as Hnext.
  pose proof (prov_box_mon_le (S n) k (Neg (Box n Bot)) Hlt) as Hmon.
  exact (MP _ _ Hmon Hnext).
Qed.

(** ** Tiling at any strictly higher level.

    The single-step tiling theorem ([tiling_consistency]) is lifted to
    arbitrary higher levels by monotonicity: if level [S n] verifies
    the consistency tiling at level [n], so does any level [k >= S n]
    (i.e., any [k > n]).

    Read in agent terms: every supervising agent strictly above the
    licensing level can verify that the licensor's claims do not
    contradict each other, regardless of the supervisory gap. *)

Theorem tiling_chain : forall n k phi,
  n < k -> |- Box k (Impl (Box n phi) (Neg (Box n (Neg phi)))).
Proof.
  intros n k phi Hlt.
  pose proof (tiling_consistency n phi) as Htil.
  pose proof (prov_box_mon_le (S n) k
                (Impl (Box n phi) (Neg (Box n (Neg phi)))) Hlt) as Hmon.
  exact (MP _ _ Hmon Htil).
Qed.

(** Following YH 2013, we identify "the level-n agent licenses claim
    [phi]" with the modal statement [Box n phi].  This is a
    semantically transparent abstraction layer: the agent's licensing
    decisions are exactly the theorems of its theory.

    An agent's licensure at level [n] is read as a Form (so that other
    agents may reason about it), and licensure-of-licensure stacks
    via nested boxes. *)

Definition licenses (n : nat) (phi : Form) : Form := Box n phi.

(** ** YH-style tiling in agent form.

    At any level [n], the strictly higher agent at level [S n]
    verifies that the level-[n] agent's licensing is internally
    consistent: the lower agent cannot license both [phi] and its
    negation.  This is exactly the YH tiling property as it appears
    in the paper, restated in our modal abstraction.

    The proof is a definitional unfolding of [tiling_consistency]. *)

Corollary licensing_consistency_yh : forall n phi,
  |- Box (S n) (Impl (licenses n phi) (Neg (licenses n (Neg phi)))).
Proof.
  intros n phi.
  unfold licenses.
  exact (tiling_consistency n phi).
Qed.

(** ** Licensure substitution congruence.

    If two formulas are provably equivalent, then their licensures
    at any level are also provably equivalent.  Internalises the
    congruence rule that justifies treating the [licenses] layer as a
    transparent abstraction over the modal calculus. *)

Lemma licenses_subst : forall n phi psi,
  |- Iff phi psi -> |- Iff (licenses n phi) (licenses n psi).
Proof.
  intros n phi psi Hiff.
  unfold licenses, Iff in *.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
  pose proof (prov_and_elim_r_meta _ _ Hiff) as Hbwd.
  pose proof (prov_box_imp n _ _ Hfwd) as Hbf.
  pose proof (prov_box_imp n _ _ Hbwd) as Hbb.
  exact (prov_and_intro_meta _ _ Hbf Hbb).
Qed.

(** ** Nested licensing transitivity (under reflection).

    Two-level supervised licensure can collapse to one-level licensure
    under a reflection hypothesis at the supervisor level.  This is
    the conditional form: given an internal reflection axiom at level
    [S (S n)] for level [S n], two-level nesting reduces.

    Pure GLP* does not prove the reflection hypothesis (it would
    collide with the Loebian obstacle).  But when explicitly assumed,
    the collapse follows by [prov_box_mp]. *)

Lemma nested_licensing_transitive : forall n phi,
  |- Box (S (S n)) (Impl (Box (S n) (Box n phi)) (Box n phi)) ->
  |- Box (S (S n)) (licenses (S n) (licenses n phi)) ->
  |- Box (S (S n)) (licenses n phi).
Proof.
  intros n phi Href Hnested.
  unfold licenses in *.
  exact (prov_box_mp (S (S n)) _ _ Href Hnested).
Qed.

(** ** And-list: conjunction over a finite list of formulas. *)

Fixpoint And_list (l : list Form) : Form :=
  match l with
  | nil => Top
  | phi :: rest => And phi (And_list rest)
  end.

(** ** [|- Box n Top]. *)

Lemma prov_box_top : forall n, |- Box n Top.
Proof.
  intro n.
  unfold Top.
  exact (Nec n _ (prov_id Bot)).
Qed.

(** ** Box-And-list intro: each entry boxed implies the conjunction boxed. *)

Lemma prov_box_and_list_intro : forall n l,
  Forall (fun phi => |- Box n phi) l ->
  |- Box n (And_list l).
Proof.
  intros n l. induction l as [|phi rest IH]; intro H.
  - simpl. exact (prov_box_top n).
  - simpl.
    pose proof (Forall_inv H) as Hphi.
    pose proof (Forall_inv_tail H) as Hrest.
    pose proof (IH Hrest) as IHrest.
    pose proof (prov_box_and_intro n phi (And_list rest)) as Hbai.
    exact (MP _ _ (MP _ _ Hbai Hphi) IHrest).
Qed.


(** ** Concrete licensing: if level n actually licenses [phi], then
    level (S n) proves licensing consistency for [phi].

    This is the "external" agent statement: when the lower agent has
    in fact verified its claim (Coq-provable [Box n phi]), the
    supervisory agent at level (S n) verifies consistency of that
    license — i.e., proves that the lower agent has not also
    licensed the negation. *)

Theorem licensing_consistency_concrete : forall n phi,
  |- Box n phi ->
  |- Box (S n) (Neg (Box n (Neg phi))).
Proof.
  intros n phi Hlic.
  pose proof (tiling_consistency n phi) as Htil.
  (* Htil : |- Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi)))). *)
  pose proof (Nec (S n) _ Hlic) as Hlic_box.
  (* Hlic_box : |- Box (S n) (Box n phi). *)
  exact (prov_box_mp (S n) _ _ Htil Hlic_box).
Qed.

(** ** Joint licensing consistency.

    If level [n] licenses both [phi] and [psi] (concretely, via two
    Coq-derivations of [Box n]), then level [S n] verifies that level
    [n] is consistent on their conjunction.  Combines [prov_box_and_intro]
    with [licensing_consistency_concrete]. *)

Theorem joint_licensing_consistency : forall n phi psi,
  |- Box n phi ->
  |- Box n psi ->
  |- Box (S n) (Neg (Box n (Neg (And phi psi)))).
Proof.
  intros n phi psi Hphi Hpsi.
  pose proof (prov_box_and_intro n phi psi) as Hai.
  pose proof (MP _ _ Hai Hphi) as Hstep.
  pose proof (MP _ _ Hstep Hpsi) as Hand.
  exact (licensing_consistency_concrete n (And phi psi) Hand).
Qed.

(** ** Joint licensing consistency lifted to any higher level.

    Combines [joint_licensing_consistency] with [prov_box_mon_le].
    Any supervisor strictly above [n] verifies the joint consistency
    of [phi] and [psi] when [n] has licensed both. *)

Theorem joint_licensing_consistency_chain : forall n phi psi k,
  n < k ->
  |- Box n phi ->
  |- Box n psi ->
  |- Box k (Neg (Box n (Neg (And phi psi)))).
Proof.
  intros n phi psi k Hlt Hphi Hpsi.
  pose proof (joint_licensing_consistency n phi psi Hphi Hpsi) as Hjlc.
  pose proof (prov_box_mon_le (S n) k
                (Neg (Box n (Neg (And phi psi)))) Hlt) as Hmon.
  exact (MP _ _ Hmon Hjlc).
Qed.

(** ** Finitary joint licensing consistency.

    If level [n] licenses every formula in a finite list, then level
    [S n] verifies that level [n]'s licensing is consistent on the
    conjunction.  An n-fold generalisation of [joint_licensing_consistency]. *)

Theorem joint_licensing_consistency_list : forall n l,
  Forall (fun phi => |- Box n phi) l ->
  |- Box (S n) (Neg (Box n (Neg (And_list l)))).
Proof.
  intros n l Hall.
  pose proof (prov_box_and_list_intro n l Hall) as Hbox.
  exact (licensing_consistency_concrete n (And_list l) Hbox).
Qed.

(** ** Two-level supervision.

    At level [S (S n)], the system verifies that the level-[(S n)]
    supervisor verifies the level-[n] tiling property.  This is the
    YH-style "every level acknowledges every level below it" claim
    in nested form.  Used to chain supervision across many levels
    of the tower. *)

Theorem nested_tiling : forall n phi,
  |- Box (S (S n)) (Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi))))).
Proof.
  intros n phi.
  exact (Nec (S (S n)) _ (tiling_consistency n phi)).
Qed.

(** ** Meta-level consistency translation.

    If level [n] is meta-consistent (i.e., we cannot Coq-derive
    [|- Box n Bot]), then no formula and its negation are both
    licensed at that level.

    The assumption [~(|- Box n Bot)] is the meta-consistency of
    level [n]'s theory.  We do not prove it for any specific [n] —
    that requires either semantic methods (Kripke models for GL) or
    a cut-elimination argument (Gore et al.).  But conditional on
    that assumption, level-internal contradiction collapses to
    inconsistency by [prov_box_n_contradiction]. *)

Theorem meta_consistency_no_contradiction : forall n,
  ~ (|- Box n Bot) ->
  forall phi, ~ (|- Box n phi /\ |- Box n (Neg phi)).
Proof.
  intros n Hcons phi [Hphi Hnphi].
  pose proof (prov_box_n_contradiction n phi) as Hcontra.
  pose proof (MP _ _ Hcontra Hphi) as Hstep.
  pose proof (MP _ _ Hstep Hnphi) as Hbot.
  exact (Hcons Hbot).
Qed.

(** The companion result to the Loebian obstacle: if level [n] proves
    its own consistency, then level [n] is inconsistent.

    [Box n (Neg (Box n Bot))] reads as "level n proves: level n
    doesn't prove Bot."  Goedel's second incompleteness theorem says
    this implies [Box n Bot] (level n is inconsistent).

    Concretely the proof is a one-step instance of the Loeb axiom at
    [phi := Bot]: [Box n (Box n Bot -> Bot) -> Box n Bot] under the
    notation unfolding [Neg X = Impl X Bot]. *)

Theorem godel_second : forall n,
  |- Impl (Box n (Neg (Box n Bot))) (Box n Bot).
Proof.
  intro n.
  exact (Ax_Loeb n Bot).
Qed.

(** ** Self-licensed consistency collapses.

    If level [n] internally licenses its own consistency
    ([|- Box n (Neg (Box n Bot))]), then level [n] is inconsistent
    ([|- Box n Bot]).  Read in YH terms: an agent that internally
    asserts its own consistency triggers the Loebian collapse and
    becomes inconsistent.  This is the agent-level reason a tower
    must reach for the next level up rather than self-trusting. *)

Theorem self_consistency_inconsistent : forall n,
  |- Box n (Neg (Box n Bot)) ->
  |- Box n Bot.
Proof.
  intros n Hself.
  exact (MP _ _ (godel_second n) Hself).
Qed.

(** ** Inconsistency propagates upward in the tower.

    If a lower level proves [Bot], every higher level does too, by
    monotonicity.  An inconsistent agent at any rung of the YH ladder
    therefore taints every supervisor above it. *)

Theorem inconsistency_propagates : forall n m,
  n <= m -> |- Box n Bot -> |- Box m Bot.
Proof.
  intros n m Hle Hbot.
  pose proof (prov_box_mon_le n m Bot Hle) as Hmon.
  exact (MP _ _ Hmon Hbot).
Qed.

(** ** Consistency propagates downward in the tower.

    Contrapositive of [inconsistency_propagates]: if a higher level
    is meta-consistent, then every lower level is too.  In tower
    terms, the consistency of any single supervisor at a level [m]
    certifies the consistency of every agent below it in the chain. *)

Theorem consistency_propagates_down : forall n m,
  n <= m -> ~ (|- Box m Bot) -> ~ (|- Box n Bot).
Proof.
  intros n m Hle Hcons_m Hbot_n.
  exact (Hcons_m (inconsistency_propagates n m Hle Hbot_n)).
Qed.

(** [Diamond n phi] is by definition [Neg (Box n (Neg phi))], i.e., the
    consistency of [phi] in the level-[n] theory.  The tiling theorem
    therefore reads, at level [S n], "if level n proves [phi], then
    [phi] is consistent in level n." *)

Corollary tiling_diamond : forall n phi,
  |- Box (S n) (Impl (Box n phi) (Diamond n phi)).
Proof.
  intros n phi.
  unfold Diamond.
  exact (tiling_consistency n phi).
Qed.

(** ** Diamond tiling at any strictly higher level.

    Same lift as [tiling_chain] for the [Neg-Box-Neg] form, restated
    using [Diamond] for symmetry with classical modal-logic notation. *)

Corollary tiling_diamond_chain : forall n k phi,
  n < k -> |- Box k (Impl (Box n phi) (Diamond n phi)).
Proof.
  intros n k phi Hlt.
  unfold Diamond.
  exact (tiling_chain n k phi Hlt).
Qed.

(** The Yudkowsky-Herreshoff bypass packages three facts:

    1. The single-level soundness schema is incompatible with
       consistency: any [Box n] satisfying [Box n phi -> phi]
       uniformly is the modality of an inconsistent theory.
       (Loebian obstacle.)

    2. At the strictly higher level [S n], the consistency tiling
       is provable: [Box (S n)] verifies that [Box n] cannot
       license both [phi] and [Neg phi].
       (Tiling theorem.)

    3. Higher levels provably acknowledge consistency of strictly
       lower levels: every [Box k] with [k > n] proves [Neg (Box n Bot)].
       (Consistency chain.)

    Together, these three facts isolate exactly the YH 2013
    construction: the parametric tower [T_0 subseteq T_1 subseteq ...]
    achieves cross-level consistency verification at every step,
    even though no single level can verify its own soundness. *)

Theorem yh_bypass_summary : forall n : nat,
  ((forall phi, |- Impl (Box n phi) phi) -> |- Bot) /\
  (forall phi, |- Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi))))) /\
  (forall k, n < k -> |- Box k (Neg (Box n Bot))).
Proof.
  intro n.
  split; [|split].
  - exact (loebian_obstacle n).
  - exact (tiling_consistency n).
  - exact (consistency_chain n).
Qed.

(** ** Internal YH bypass.

    A single Form witnessing the bypass content at a single level:
    the conjunction of consistency tiling for [phi] and consistency
    of level [n] itself.  Provable at level [S n] inside the calculus,
    not just at the meta-level. *)

Definition yh_bypass_summary_internal (n : nat) (phi : Form) : Form :=
  And (Impl (Box n phi) (Neg (Box n (Neg phi)))) (Neg (Box n Bot)).

Theorem yh_bypass_internal : forall n phi,
  |- Box (S n) (yh_bypass_summary_internal n phi).
Proof.
  intros n phi.
  unfold yh_bypass_summary_internal.
  pose proof (tiling_consistency n phi) as Htil.
  pose proof (Ax_NextCon n) as Hncon.
  pose proof (prov_box_and_intro (S n)
                (Impl (Box n phi) (Neg (Box n (Neg phi))))
                (Neg (Box n Bot))) as Hbai.
  exact (MP _ _ (MP _ _ Hbai Htil) Hncon).
Qed.

(** ** Uniform bypass schema.

    [tiling_consistency] as a uniform derivation, exposed as a single
    proof term parameterised by [n] and [phi].  The Coq type itself
    encodes the schematic nature: a single dependent term inhabits
    [forall n phi, |- ...], so each [tiling_consistency n phi]
    instance is obtained by parameter substitution into a fixed
    derivation tree. *)

Definition tiling_schema : forall n phi,
  |- Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi))))
  := tiling_consistency.

(** ** Agent-theoretic properties of [licenses].

    The licensure layer satisfies three agent-flavoured properties:

    - Modus ponens for licensure: composing implication-licensure
      with antecedent-licensure yields consequent-licensure.
    - Nested licensure intro: licensure entails licensure-of-licensure
      (axiom 4 in agent dress).
    - Conservativity over the modal calculus: licensure is
      definitionally equal to [Box n], so no theorem becomes provable
      that wasn't already. *)

Theorem licenses_mp : forall n phi psi,
  |- licenses n (Impl phi psi) -> |- licenses n phi -> |- licenses n psi.
Proof.
  intros n phi psi Himp Hphi.
  unfold licenses in *.
  exact (prov_box_mp n _ _ Himp Hphi).
Qed.

Theorem licenses_nested_intro : forall n phi,
  |- Impl (licenses n phi) (licenses n (licenses n phi)).
Proof.
  intros n phi.
  unfold licenses.
  exact (Ax_Box4 n phi).
Qed.

Theorem licenses_conservative : forall n phi,
  |- licenses n phi <-> |- Box n phi.
Proof.
  intros n phi. unfold licenses. split; intro H; exact H.
Qed.

(** ** Cross-level licensure composition.

    If a lower-level agent licenses an implication and a (possibly
    higher) agent licenses the antecedent, then the higher agent
    licenses the consequent.  The implication is lifted across
    levels by monotonicity, then chained with [licenses_mp]. *)

Theorem licenses_compose_cross : forall n m phi psi,
  n <= m ->
  |- licenses n (Impl phi psi) ->
  |- licenses m phi ->
  |- licenses m psi.
Proof.
  intros n m phi psi Hle Himp Hphi.
  unfold licenses in *.
  pose proof (prov_box_mon_le n m (Impl phi psi) Hle) as Hmon.
  pose proof (MP _ _ Hmon Himp) as Himp'.
  exact (prov_box_mp m _ _ Himp' Hphi).
Qed.

(** ** First de Morgan duality: [|- Iff (Neg (And phi psi)) (Or (Neg phi) (Neg psi))].

    After unfolding, the iff reduces to
    [Neg (Neg (Impl phi (Neg psi))) <-> (Neg (Neg phi) -> Neg psi)],
    which holds by repeated [Ax_DN] and [prov_DN_intro] manipulations
    on the antecedent and consequent of the inner implication. *)

Lemma de_morgan_and : forall phi psi,
  |- Iff (Neg (And phi psi)) (Or (Neg phi) (Neg psi)).
Proof.
  intros phi psi.
  unfold Iff, And, Or.
  (* Goal: Iff is And (...) (...).  We prove both implications. *)
  (* Direction 1: Neg (Neg (Impl phi (Neg psi)))
                     -> (Neg (Neg phi) -> Neg psi). *)
  pose proof (Ax_DN (Impl phi (Neg psi))) as HDN1.
  (* HDN1 : Neg (Neg (Impl phi (Neg psi))) -> (Impl phi (Neg psi)). *)
  pose proof (prov_compose_internal (Neg (Neg phi)) phi (Neg psi)) as HCI1.
  pose proof (prov_perm _ _ _ HCI1) as HCI1_perm.
  (* HCI1_perm : (Neg (Neg phi) -> phi)
                   -> ((phi -> Neg psi) -> (Neg (Neg phi) -> Neg psi)). *)
  pose proof (Ax_DN phi) as HDN_phi.
  pose proof (MP _ _ HCI1_perm HDN_phi) as Hbridge.
  (* Hbridge : (phi -> Neg psi) -> (Neg (Neg phi) -> Neg psi). *)
  pose proof (prov_compose _ _ _ HDN1 Hbridge) as Hd1.
  (* Hd1 : Neg (Neg (Impl phi (Neg psi))) -> (Neg (Neg phi) -> Neg psi). *)
  (* Direction 2: (Neg (Neg phi) -> Neg psi)
                     -> Neg (Neg (Impl phi (Neg psi))). *)
  pose proof (prov_compose_internal phi (Neg (Neg phi)) (Neg psi)) as HCI2.
  pose proof (prov_perm _ _ _ HCI2) as HCI2_perm.
  (* HCI2_perm : (phi -> Neg (Neg phi))
                   -> ((Neg (Neg phi) -> Neg psi) -> (phi -> Neg psi)). *)
  pose proof (prov_DN_intro phi) as HDN_intro_phi.
  pose proof (MP _ _ HCI2_perm HDN_intro_phi) as Hbridge2.
  (* Hbridge2 : (Neg (Neg phi) -> Neg psi) -> (phi -> Neg psi). *)
  pose proof (prov_DN_intro (Impl phi (Neg psi))) as HDNI.
  (* HDNI : (Impl phi (Neg psi)) -> Neg (Neg (Impl phi (Neg psi))). *)
  pose proof (prov_compose _ _ _ Hbridge2 HDNI) as Hd2.
  (* Hd2 : (Neg (Neg phi) -> Neg psi) -> Neg (Neg (Impl phi (Neg psi))). *)
  exact (prov_and_intro_meta _ _ Hd1 Hd2).
Qed.

(** ** Second de Morgan duality: [|- Iff (Neg (Or phi psi)) (And (Neg phi) (Neg psi))]. *)

Lemma de_morgan_or : forall phi psi,
  |- Iff (Neg (Or phi psi)) (And (Neg phi) (Neg psi)).
Proof.
  intros phi psi.
  unfold Iff, And, Or.
  (* Direction 1: ((Neg phi -> psi) -> Bot) -> ((Neg phi -> Neg (Neg psi)) -> Bot). *)
  pose proof (prov_compose_internal (Neg phi) (Neg (Neg psi)) psi) as HC1.
  pose proof (Ax_DN psi) as HDN_psi.
  pose proof (MP _ _ HC1 HDN_psi) as HX1.
  (* HX1 : (Neg phi -> Neg (Neg psi)) -> (Neg phi -> psi). *)
  pose proof (prov_compose_internal
                (Impl (Neg phi) (Neg (Neg psi)))
                (Impl (Neg phi) psi)
                Bot) as HC2.
  pose proof (prov_perm _ _ _ HC2) as HC2_perm.
  pose proof (MP _ _ HC2_perm HX1) as Hd1.
  (* Direction 2: ((Neg phi -> Neg (Neg psi)) -> Bot) -> ((Neg phi -> psi) -> Bot). *)
  pose proof (prov_compose_internal (Neg phi) psi (Neg (Neg psi))) as HC3.
  pose proof (prov_DN_intro psi) as HDNI_psi.
  pose proof (MP _ _ HC3 HDNI_psi) as HX2.
  (* HX2 : (Neg phi -> psi) -> (Neg phi -> Neg (Neg psi)). *)
  pose proof (prov_compose_internal
                (Impl (Neg phi) psi)
                (Impl (Neg phi) (Neg (Neg psi)))
                Bot) as HC4.
  pose proof (prov_perm _ _ _ HC4) as HC4_perm.
  pose proof (MP _ _ HC4_perm HX2) as Hd2.
  exact (prov_and_intro_meta _ _ Hd1 Hd2).
Qed.

(** ** Third de Morgan duality:
    [|- Iff (And phi psi) (Neg (Or (Neg phi) (Neg psi)))]. *)

Lemma de_morgan_and_neg : forall phi psi,
  |- Iff (And phi psi) (Neg (Or (Neg phi) (Neg psi))).
Proof.
  intros phi psi.
  unfold Iff, And, Or.
  (* Direction 1: ((phi -> Neg psi) -> Bot) -> ((Neg (Neg phi) -> Neg psi) -> Bot). *)
  pose proof (prov_compose_internal phi (Neg (Neg phi)) (Neg psi)) as HC1.
  pose proof (prov_perm _ _ _ HC1) as HC1_perm.
  pose proof (prov_DN_intro phi) as HDNI_phi.
  pose proof (MP _ _ HC1_perm HDNI_phi) as HX1.
  pose proof (prov_compose_internal
                (Impl (Neg (Neg phi)) (Neg psi))
                (Impl phi (Neg psi))
                Bot) as HC2.
  pose proof (prov_perm _ _ _ HC2) as HC2_perm.
  pose proof (MP _ _ HC2_perm HX1) as Hd1.
  (* Direction 2: ((Neg (Neg phi) -> Neg psi) -> Bot) -> ((phi -> Neg psi) -> Bot). *)
  pose proof (prov_compose_internal (Neg (Neg phi)) phi (Neg psi)) as HC3.
  pose proof (prov_perm _ _ _ HC3) as HC3_perm.
  pose proof (Ax_DN phi) as HDN_phi.
  pose proof (MP _ _ HC3_perm HDN_phi) as HX2.
  pose proof (prov_compose_internal
                (Impl phi (Neg psi))
                (Impl (Neg (Neg phi)) (Neg psi))
                Bot) as HC4.
  pose proof (prov_perm _ _ _ HC4) as HC4_perm.
  pose proof (MP _ _ HC4_perm HX2) as Hd2.
  exact (prov_and_intro_meta _ _ Hd1 Hd2).
Qed.

(** ** Fourth de Morgan duality:
    [|- Iff (Or phi psi) (Neg (And (Neg phi) (Neg psi)))]. *)

Lemma de_morgan_or_neg : forall phi psi,
  |- Iff (Or phi psi) (Neg (And (Neg phi) (Neg psi))).
Proof.
  intros phi psi.
  unfold Iff, And, Or.
  (* Direction 1: (Neg phi -> psi) -> Neg (Neg (Impl (Neg phi) (Neg (Neg psi)))). *)
  pose proof (prov_DN_intro psi) as HDNI_psi.
  pose proof (prov_compose_internal (Neg phi) psi (Neg (Neg psi))) as HC1.
  pose proof (MP _ _ HC1 HDNI_psi) as HX1.
  pose proof (prov_DN_intro (Impl (Neg phi) (Neg (Neg psi)))) as HDNI.
  pose proof (prov_compose _ _ _ HX1 HDNI) as Hd1.
  (* Direction 2: Neg (Neg (Impl (Neg phi) (Neg (Neg psi)))) -> (Neg phi -> psi). *)
  pose proof (Ax_DN (Impl (Neg phi) (Neg (Neg psi)))) as HDN1.
  pose proof (Ax_DN psi) as HDN2.
  pose proof (prov_compose_internal (Neg phi) (Neg (Neg psi)) psi) as HC2.
  pose proof (MP _ _ HC2 HDN2) as HX2.
  pose proof (prov_compose _ _ _ HDN1 HX2) as Hd2.
  exact (prov_and_intro_meta _ _ Hd1 Hd2).
Qed.

(** ** Cross-level reflection succeeds.

    [Ax_Mon] internalised as a positive theorem: monotonicity of [Box]
    across levels.  This is the "legitimate replacement" for the
    same-level reflection schema [Box n phi -> phi] that fails by the
    Loebian obstacle. *)

Theorem parametric_reflection_succeeds : forall n phi,
  |- Impl (Box n phi) (Box (S n) phi).
Proof.
  exact Ax_Mon.
Qed.

(** ** Same-level reflection collapses, cross-level does not.

    A side-by-side packaging of the two scenarios.  The Loeb axiom
    triggers a collapse when the reflection schema [Box n phi -> phi]
    is universal at the same level; cross-level reflection
    [Box n phi -> Box (S n) phi] survives because the conclusion
    has strictly larger level than the hypothesis, breaking the
    pattern that activates [Ax_Loeb]. *)

Theorem same_level_vs_cross_level_reflection : forall n,
  ((forall phi, |- Impl (Box n phi) phi) -> |- Bot) /\
  (forall phi, |- Impl (Box n phi) (Box (S n) phi)).
Proof.
  intro n. split.
  - exact (loebian_obstacle n).
  - exact (Ax_Mon n).
Qed.

(** ** Reflection schema unprovability (conditional).

    Strengthening of [loebian_obstacle]: assuming meta-consistency
    of the system ([~ |- Bot]), the same-level reflection schema is
    not even uniformly provable.  The unconditional version (without
    the consistency hypothesis) requires a syntactic or semantic
    consistency argument, addressed in todo items 23-25. *)

Theorem reflection_schema_unprovable_conditional : forall n,
  ~ (|- Bot) -> ~ (forall phi, |- Impl (Box n phi) phi).
Proof.
  intros n Hcons Hsch.
  exact (Hcons (loebian_obstacle n Hsch)).
Qed.

(** ** Boolean evaluation that maps every box-formula to [true].

    A simple semantic argument for system-level meta-consistency:
    define [eval] mapping every [Box _ _] to [true] and propositional
    structure to its classical truth-table.  Every axiom of GLP*
    evaluates to [true] under this assignment, hence so does every
    Provable formula.  Since [Bot] evaluates to [false], [Bot] is
    not Provable. *)

Fixpoint eval (val : nat -> bool) (phi : Form) : bool :=
  match phi with
  | Var p => val p
  | Bot => false
  | Impl X Y => orb (negb (eval val X)) (eval val Y)
  | Box _ _ => true
  end.

Lemma eval_provable_true : forall val phi, |- phi -> eval val phi = true.
Proof.
  intros val phi H.
  induction H; simpl in *.
  - destruct (eval val phi); destruct (eval val psi); reflexivity.
  - destruct (eval val phi); destruct (eval val psi); destruct (eval val chi);
      reflexivity.
  - destruct (eval val phi); reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (eval val phi); simpl in IHProvable1.
    + exact IHProvable1.
    + discriminate IHProvable2.
  - reflexivity.
Qed.

Theorem meta_consistency_system : ~ (|- Bot).
Proof.
  intro H.
  pose proof (eval_provable_true (fun _ => true) Bot H) as Heval.
  simpl in Heval.
  discriminate.
Qed.

(** With system-level meta-consistency in hand, the conditional
    [reflection_schema_unprovable_conditional] becomes unconditional. *)

Theorem reflection_schema_unprovable : forall n,
  ~ (forall phi, |- Impl (Box n phi) phi).
Proof.
  intros n.
  exact (reflection_schema_unprovable_conditional n meta_consistency_system).
Qed.

(** A Kripke frame for GLP* consists of a type of worlds, a family of
    accessibility relations indexed by level, and four structural
    conditions:

    - Each [R n] is transitive.
    - Each [R n] is converse-well-founded (Noetherian, validating Loeb).
    - [R (S n)] is contained in [R n] (validating monotonicity).
    - Every [R (S n)] successor has an [R n] successor (validating
      [NextCon]).

    Forcing is defined classically with [bool]-valued valuations. *)

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

(** ** Soundness of GLP* with respect to Kripke semantics.

    Every Provable formula is valid in every GLP*-frame.  The Loeb
    axiom uses well-founded induction on the converse of [fR n] to
    extract a witness; cross-level axioms use [fR_mon] and
    [fR_nextcon] respectively. *)

Theorem soundness : forall phi, |- phi -> Valid phi.
Proof.
  intros phi H. induction H.
  - (* Ax_K *)
    unfold Valid. intros F V w. simpl. intros Hphi _. exact Hphi.
  - (* Ax_S *)
    unfold Valid. intros F V w. simpl. intros Hf Hg Hphi.
    apply Hf; [exact Hphi | apply Hg; exact Hphi].
  - (* Ax_DN *)
    unfold Valid. intros F V w. simpl. intro Hnnp.
    apply NNPP. exact Hnnp.
  - (* Ax_BoxK *)
    unfold Valid. intros F V w. simpl. intros Himp Hphi v Hwv.
    apply (Himp v Hwv). apply (Hphi v Hwv).
  - (* Ax_Loeb *)
    unfold Valid. intros F V w. simpl. intros Hbox v Hwv.
    pose proof (fR_wf F n) as Hwf.
    set (P := fun u => fR F n w u -> forces F V u phi).
    cut (P v); [intro Hpv; exact (Hpv Hwv) |].
    apply (well_founded_ind Hwf P).
    intros u IH. unfold P. intro Hwu.
    apply (Hbox u Hwu).
    intros u' Huu'.
    apply (IH u' Huu' (fR_trans F n w u u' Hwu Huu')).
  - (* Ax_Box4 *)
    unfold Valid. intros F V w. simpl. intros Hphi v Hwv u Hvu.
    apply Hphi. apply (fR_trans F n w v u Hwv Hvu).
  - (* Ax_Mon *)
    unfold Valid. intros F V w. simpl. intros Hphi v Hwv.
    apply Hphi. apply (fR_mon F n w v Hwv).
  - (* Ax_NextCon *)
    unfold Valid. intros F V w. simpl. intros v Hwv Hbox.
    destruct (fR_nextcon F n w v Hwv) as [u Hvu].
    exact (Hbox u Hvu).
  - (* MP *)
    unfold Valid. intros F V w.
    apply (IHProvable1 F V w). apply (IHProvable2 F V w).
  - (* Nec *)
    unfold Valid. intros F V w. simpl.
    intros v _. apply (IHProvable F V v).
Qed.

(** ** A two-world frame refuting [Box 0 Bot].

    [F0] has [W := bool] (with [true] interpreted as the root and
    [false] as a single [R 0]-successor), [R 0] = {(true, false)},
    and all other [R n] empty.  All four frame conditions hold
    vacuously or trivially, so [F0] is a GLP*-frame.  At the root
    [true], [Box 0 Bot] forces to [False] because the successor
    [false] forces [Bot] to [False]. *)

Definition F0_R (n : nat) (w v : bool) : Prop :=
  match n with O => w = true /\ v = false | _ => False end.

Lemma F0_R_trans : forall n w v u,
  F0_R n w v -> F0_R n v u -> F0_R n w u.
Proof.
  intros [|n] w v u; simpl; intros H1 H2; try contradiction.
  destruct H1 as [_ Hvf]. destruct H2 as [Hvt _]. subst v. discriminate.
Qed.

Lemma F0_R_wf : forall n, well_founded (fun u v => F0_R n v u).
Proof.
  intros n w.
  destruct n; destruct w; apply Acc_intro; intros y Hy; simpl in Hy.
  - destruct Hy as [_ Hyf]. subst y.
    apply Acc_intro. intros z Hz. simpl in Hz.
    destruct Hz as [Heq _]. discriminate.
  - destruct Hy as [Heq _]. discriminate.
  - destruct Hy.
  - destruct Hy.
Qed.

Lemma F0_R_mon : forall n w v, F0_R (S n) w v -> F0_R n w v.
Proof. intros n w v H. simpl in H. destruct H. Qed.

Lemma F0_R_nextcon : forall n w v,
  F0_R (S n) w v -> exists u, F0_R n v u.
Proof. intros n w v H. simpl in H. destruct H. Qed.

Definition F0 : Frame :=
  mkFrame bool F0_R F0_R_trans F0_R_wf F0_R_mon F0_R_nextcon.

Theorem meta_consistency_box_0 : ~ (|- Box 0 Bot).
Proof.
  intro H.
  pose proof (soundness _ H F0 (fun _ _ => true) true) as Hf.
  simpl in Hf.
  apply (Hf false).
  split; reflexivity.
Qed.

(** ** A nat-indexed frame refuting [Box n Bot] uniformly.

    [Fnat] takes [W := nat] and [R k w v := w > v /\ v >= k].  At
    world [n+1], the world [n] witnesses an [R n]-successor with
    [Bot] forced false.  All four frame conditions are direct
    consequences of basic arithmetic. *)

Definition Fnat_R (k : nat) (w v : nat) : Prop := w > v /\ v >= k.

Lemma Fnat_R_trans : forall k w v u,
  Fnat_R k w v -> Fnat_R k v u -> Fnat_R k w u.
Proof.
  intros k w v u [Hwv _] [Hvu Hun]. split; lia.
Qed.

Lemma Fnat_R_wf : forall k, well_founded (fun u v => Fnat_R k v u).
Proof.
  intros k x.
  induction x as [x IH] using (well_founded_induction lt_wf).
  apply Acc_intro. intros y Hy.
  destruct Hy as [Hgt _].
  apply IH. exact Hgt.
Qed.

Lemma Fnat_R_mon : forall k w v, Fnat_R (S k) w v -> Fnat_R k w v.
Proof.
  intros k w v [H1 H2]. split; lia.
Qed.

Lemma Fnat_R_nextcon : forall k w v,
  Fnat_R (S k) w v -> exists u, Fnat_R k v u.
Proof.
  intros k w v [Hwv Hvk]. exists k.
  unfold Fnat_R. split; lia.
Qed.

Definition Fnat : Frame :=
  mkFrame nat Fnat_R Fnat_R_trans Fnat_R_wf Fnat_R_mon Fnat_R_nextcon.

(** ** Meta-consistency at every level.

    For any [n], evaluating in [Fnat] at world [S n] refutes [Box n
    Bot], since the witness [n] satisfies [S n > n /\ n >= n]. *)

Theorem meta_consistency_every_level : forall n, ~ (|- Box n Bot).
Proof.
  intros n H.
  pose proof (soundness _ H Fnat (fun _ _ => true) (S n)) as Hf.
  simpl in Hf.
  apply (Hf n).
  unfold Fnat_R. split; lia.
Qed.

(** ** Meta_consistency_no_contradiction unconditional. *)

Theorem meta_no_contradiction : forall n phi,
  ~ (|- Box n phi /\ |- Box n (Neg phi)).
Proof.
  intros n phi.
  apply meta_consistency_no_contradiction.
  exact (meta_consistency_every_level n).
Qed.

(** ** Monotonicity converse fails.

    [|- Impl (Box (S n) phi) (Box n phi)] is not a theorem of GLP*
    for [phi] a propositional variable.  Witnessed by [Fnat] at world
    [S n] with valuation [V w 0 := S n <=? w]: in [Fnat], every
    [R (S n)]-successor of [S n] is empty, so [Box (S n) (Var 0)]
    holds vacuously, while [n] is an [R n]-successor of [S n] but
    fails [Var 0]'s valuation.  Hence the implication fails at [S n]
    in [Fnat], and by soundness it is not Provable. *)

Theorem mon_converse_fails : forall n,
  ~ (|- Impl (Box (S n) (Var 0)) (Box n (Var 0))).
Proof.
  intros n H.
  pose (V := fun (w : nat) (p : nat) =>
    match p with 0 => Nat.leb (S n) w | _ => false end).
  pose proof (soundness _ H Fnat V (S n)) as Hf.
  simpl in Hf.
  assert (Hbox_Sn : forall v, Fnat_R (S n) (S n) v -> V v 0 = true).
  { intros v [Hlt Hge]. exfalso. lia. }
  pose proof (Hf Hbox_Sn n) as HboxN.
  assert (Hrn : Fnat_R n (S n) n).
  { unfold Fnat_R. split; lia. }
  specialize (HboxN Hrn).
  change (V n 0 = true) in HboxN.
  unfold V in HboxN.
  change (Nat.leb (S n) n = true) in HboxN.
  apply Nat.leb_le in HboxN. lia.
Qed.

(** ** Strict extension at every level.

    For each [n], the formula [Neg (Box n Bot)] (the consistency
    sentence for level [n]) is provable at level [S n] but not at
    level [n] itself.  This witnesses genuine ascent: each level of
    the tower proves something its predecessor cannot. *)

Theorem strict_extension_at_each_level : forall n,
  exists phi, (|- Box (S n) phi) /\ ~ (|- Box n phi).
Proof.
  intro n.
  exists (Neg (Box n Bot)).
  split.
  - exact (Ax_NextCon n).
  - intro H.
    apply (meta_consistency_every_level n).
    exact (MP _ _ (godel_second n) H).
Qed.

(** ** Same-level boxed reflection schema is unprovable uniformly.

    A "level-[S n] internalisation" of [loebian_obstacle]: if level
    [S n] uniformly proves [Box (S n) phi -> phi] (its own-level
    reflection schema), then by [Ax_Loeb] specialised at [Bot],
    [|- Box (S n) Bot] follows, contradicting
    [meta_consistency_every_level]. *)

Theorem reflection_at_same_level_unprovable_uniformly : forall n,
  ~ (forall phi, |- Box (S n) (Impl (Box (S n) phi) phi)).
Proof.
  intros n Hsch.
  pose proof (Hsch Bot) as Hbot.
  pose proof (Ax_Loeb (S n) Bot) as HLoeb.
  pose proof (MP _ _ HLoeb Hbot) as HboxBot.
  exact (meta_consistency_every_level (S n) HboxBot).
Qed.

(** ** GLP* without NextCon.

    [Provable_no_NC] is the calculus with every GLP* axiom except
    [Ax_NextCon].  Used below to show that consistency_chain at the
    level-0/1 boundary is unprovable without [NextCon], exhibiting
    the relative-consistency content of [NextCon]. *)

Inductive Provable_no_NC : Form -> Prop :=
  | NC_Ax_K : forall phi psi,
      Provable_no_NC (Impl phi (Impl psi phi))
  | NC_Ax_S : forall phi psi chi,
      Provable_no_NC (Impl (Impl phi (Impl psi chi))
                           (Impl (Impl phi psi) (Impl phi chi)))
  | NC_Ax_DN : forall phi,
      Provable_no_NC (Impl (Neg (Neg phi)) phi)
  | NC_Ax_BoxK : forall n phi psi,
      Provable_no_NC (Impl (Box n (Impl phi psi))
                           (Impl (Box n phi) (Box n psi)))
  | NC_Ax_Loeb : forall n phi,
      Provable_no_NC (Impl (Box n (Impl (Box n phi) phi)) (Box n phi))
  | NC_Ax_Box4 : forall n phi,
      Provable_no_NC (Impl (Box n phi) (Box n (Box n phi)))
  | NC_Ax_Mon : forall n phi,
      Provable_no_NC (Impl (Box n phi) (Box (S n) phi))
  | NC_MP : forall phi psi,
      Provable_no_NC (Impl phi psi) -> Provable_no_NC phi -> Provable_no_NC psi
  | NC_Nec : forall n phi,
      Provable_no_NC phi -> Provable_no_NC (Box n phi).

Notation "|-no_nc f" := (Provable_no_NC f) (at level 75, no associativity).

Record Frame_no_NC : Type := mkFrame_no_NC {
  fW_nc : Type;
  fR_nc : nat -> fW_nc -> fW_nc -> Prop;
  fR_nc_trans : forall n w v u, fR_nc n w v -> fR_nc n v u -> fR_nc n w u;
  fR_nc_wf : forall n, well_founded (fun u v => fR_nc n v u);
  fR_nc_mon : forall n w v, fR_nc (S n) w v -> fR_nc n w v
}.

Fixpoint forces_nc (F : Frame_no_NC) (V : fW_nc F -> nat -> bool)
                   (w : fW_nc F) (phi : Form) : Prop :=
  match phi with
  | Var p => V w p = true
  | Bot => False
  | Impl X Y => forces_nc F V w X -> forces_nc F V w Y
  | Box n psi => forall v, fR_nc F n w v -> forces_nc F V v psi
  end.

Theorem soundness_no_NC : forall phi, |-no_nc phi ->
  forall F V w, forces_nc F V w phi.
Proof.
  intros phi H. induction H.
  - intros F V w. simpl. intros Hphi _. exact Hphi.
  - intros F V w. simpl. intros Hf Hg Hphi.
    apply Hf; [exact Hphi | apply Hg; exact Hphi].
  - intros F V w. simpl. intro Hnnp. apply NNPP. exact Hnnp.
  - intros F V w. simpl. intros Himp Hphi v Hwv.
    apply (Himp v Hwv). apply (Hphi v Hwv).
  - intros F V w. simpl. intros Hbox v Hwv.
    pose proof (fR_nc_wf F n) as Hwf.
    set (P := fun u => fR_nc F n w u -> forces_nc F V u phi).
    cut (P v); [intro Hpv; exact (Hpv Hwv) |].
    apply (well_founded_ind Hwf P).
    intros u IH. unfold P. intro Hwu.
    apply (Hbox u Hwu).
    intros u' Huu'.
    apply (IH u' Huu' (fR_nc_trans F n w u u' Hwu Huu')).
  - intros F V w. simpl. intros Hphi v Hwv u Hvu.
    apply Hphi. apply (fR_nc_trans F n w v u Hwv Hvu).
  - intros F V w. simpl. intros Hphi v Hwv.
    apply Hphi. apply (fR_nc_mon F n w v Hwv).
  - intros F V w. apply (IHProvable_no_NC1 F V w).
    apply (IHProvable_no_NC2 F V w).
  - intros F V w. simpl. intros v _.
    apply (IHProvable_no_NC F V v).
Qed.

(** ** A frame violating NextCon at the 0/1 boundary.

    Two worlds, with [R 0 = R 1 = {(true, false)}] and higher [R n]
    empty.  Transitivity, well-foundedness, and monotonicity all hold
    trivially.  [NextCon] fails: [false] has no [R 0]-successor while
    being [R 1]-reachable from [true]. *)

Definition F_no_NC_R (n : nat) (w v : bool) : Prop :=
  match n with
  | 0 => w = true /\ v = false
  | 1 => w = true /\ v = false
  | _ => False
  end.

Lemma F_no_NC_R_trans : forall n w v u,
  F_no_NC_R n w v -> F_no_NC_R n v u -> F_no_NC_R n w u.
Proof.
  intros n w v u H1 H2.
  destruct n as [|[|n']]; simpl in *.
  - destruct H1 as [_ Hvf]. destruct H2 as [Hvt _]. subst v. discriminate.
  - destruct H1 as [_ Hvf]. destruct H2 as [Hvt _]. subst v. discriminate.
  - destruct H1.
Qed.

Lemma F_no_NC_R_wf : forall n, well_founded (fun u v => F_no_NC_R n v u).
Proof.
  intros n.
  destruct n as [|[|n']]; intros w; destruct w; apply Acc_intro;
    intros y Hy; simpl in Hy.
  - destruct Hy as [_ Hyf]. subst y.
    apply Acc_intro. intros z [Heq _]. discriminate.
  - destruct Hy as [Heq _]. discriminate.
  - destruct Hy as [_ Hyf]. subst y.
    apply Acc_intro. intros z [Heq _]. discriminate.
  - destruct Hy as [Heq _]. discriminate.
  - destruct Hy.
  - destruct Hy.
Qed.

Lemma F_no_NC_R_mon : forall n w v,
  F_no_NC_R (S n) w v -> F_no_NC_R n w v.
Proof.
  intros [|n] w v H; simpl in *.
  - exact H.
  - destruct n; simpl; auto. destruct H.
Qed.

Definition F_no_NC : Frame_no_NC :=
  mkFrame_no_NC bool F_no_NC_R F_no_NC_R_trans F_no_NC_R_wf F_no_NC_R_mon.

(** ** Consistency-chain at level 0 requires NextCon.

    [|- Box 1 (Neg (Box 0 Bot))] (which holds in full GLP* via
    [Ax_NextCon]) is not derivable in [Provable_no_NC]: in [F_no_NC],
    [false] has no [R 0]-successor, so [Box 0 Bot] is vacuously
    forced at [false], making [Neg (Box 0 Bot)] fail there, and the
    [Box 1] at [true] reaches [false]. *)

Theorem consistency_chain_needs_NC :
  ~ (|-no_nc Box 1 (Neg (Box 0 Bot))).
Proof.
  intro H.
  pose proof (soundness_no_NC _ H F_no_NC (fun _ _ => true) true) as Hf.
  simpl in Hf.
  specialize (Hf false).
  assert (HR : F_no_NC_R 1 true false) by (simpl; split; reflexivity).
  specialize (Hf HR).
  apply Hf.
  intros u Hfu. simpl in Hfu.
  destruct Hfu as [Heq _]. discriminate.
Qed.

(** ** [Top] is a fixed point of [phi(p) := Box n p].

    A trivial concrete fixed point: [|- Iff Top (Box n Top)].  Both
    [Top] and [Box n Top] are theorems individually, so the iff
    follows by [prov_weaken] in each direction.  The full de Jongh-
    Sambin theorem (todo items 36-38) handles arbitrary modalized
    [phi]; this is one of its simplest instances. *)

Theorem fixedpoint_top_box : forall n,
  |- Iff Top (Box n Top).
Proof.
  intro n.
  unfold Iff.
  apply prov_and_intro_meta.
  - exact (prov_weaken _ Top (prov_box_top n)).
  - unfold Top.
    exact (prov_weaken _ (Box n (Impl Bot Bot)) (prov_id Bot)).
Qed.

(** ** Loeb metatheorem in the no-NextCon calculus.

    The Loeb metatheorem and Loebian obstacle do not depend on
    [Ax_NextCon]: they are preserved under dropping NextCon.  This
    is one concrete instance of the YH bypass's robustness under
    axiomatization perturbations (todo item 56). *)

Theorem loeb_metatheorem_no_NC : forall n phi,
  (|-no_nc Impl (Box n phi) phi) -> |-no_nc phi.
Proof.
  intros n phi Hsound.
  pose proof (NC_Nec n _ Hsound) as Hnec.
  pose proof (NC_Ax_Loeb n phi) as HLoeb.
  pose proof (NC_MP _ _ HLoeb Hnec) as Hbox.
  exact (NC_MP _ _ Hsound Hbox).
Qed.

Theorem loebian_obstacle_no_NC : forall n,
  (forall phi, |-no_nc Impl (Box n phi) phi) -> |-no_nc Bot.
Proof.
  intros n Hsound.
  exact (loeb_metatheorem_no_NC n Bot (Hsound Bot)).
Qed.

(** ** Cross-level monotonicity is preserved.

    [Ax_Mon] is a constructor of [Provable_no_NC], so monotonicity
    survives the perturbation. *)

Theorem parametric_reflection_succeeds_no_NC : forall n phi,
  |-no_nc Impl (Box n phi) (Box (S n) phi).
Proof.
  intros n phi.
  exact (NC_Ax_Mon n phi).
Qed.

(** ** Reverse direction of [licensing_consistency_concrete].

    If level [S n] verifies that level [n] doesn't license [Neg phi]
    ([|- Box (S n) (Neg (Box n (Neg phi)))]), then level [n] really
    doesn't license [Neg phi] meta-level ([~ |- Box n (Neg phi)]).

    Proof: from the hypothesis [|- Box n (Neg phi)] for contradiction,
    Nec at level [S n] gives [|- Box (S n) (Box n (Neg phi))], which
    combined with the hypothesis via [prov_box_mp] yields
    [|- Box (S n) Bot], contradicting [meta_consistency_every_level].

    This is the meta-level converse of [licensing_consistency_concrete]:
    the cross-level consistency verification at level [S n] is sound
    with respect to actual licensing decisions at level [n].  This
    addresses todo item 12 in a precise form. *)

Theorem licensing_consistency_concrete_converse : forall n phi,
  |- Box (S n) (Neg (Box n (Neg phi))) ->
  ~ |- Box n (Neg phi).
Proof.
  intros n phi HSn Hn.
  pose proof (Nec (S n) _ Hn) as HnBox.
  pose proof (prov_box_mp (S n) _ _ HSn HnBox) as HBoxBot.
  exact (meta_consistency_every_level (S n) HBoxBot).
Qed.

(** ** Finite tower (FS2014).

    For any natural [n], the family [T_0, T_1, ..., T_n] in our
    polymodal abstraction is a sequence of progressively stronger
    theories where each [T_(k+1)] verifies the consistency of [T_k]
    over the [Bot]-class of sentences.  This is the modal analog of
    the FS2014 finite tower result. *)

Theorem fs2014_finite_tower : forall n,
  forall k, k < n -> |- Box (S k) (Neg (Box k Bot)).
Proof.
  intros n k _.
  exact (Ax_NextCon k).
Qed.

(** ** Infinite consistency chain (FS2014).

    The chain extends without limit: every [T_(S n)] proves the
    consistency of its immediate predecessor [T_n], and every level
    strictly above [n] inherits this verification by monotonicity.
    Formalised via [consistency_chain] from earlier. *)

Theorem fs2014_infinite_chain : forall n,
  |- Box (S n) (Neg (Box n Bot)).
Proof.
  exact Ax_NextCon.
Qed.

(** ** Successor-licensing safety (FS2014 self-modification).

    An agent at level [n] proves that the level-[(S n)] agent has
    consistently verified the level-[n] consistency.  In FS2014's
    "agent using T_n proves it is safe to self-modify into an agent
    using T_(S n)" reading, this is the modal core of the
    safety-of-self-modification claim, restricted to the consistency
    sentence-class. *)

Theorem fs2014_safe_self_modification : forall n,
  |- Box n (Box (S n) (Neg (Box n Bot))).
Proof.
  intro n.
  exact (Nec n _ (Ax_NextCon n)).
Qed.

(** ** Provability with hypotheses.

    [Provable_with_hyp Gamma phi] holds when [phi] is derivable from
    the hypotheses in [Gamma] using axioms, theorems, and modus
    ponens.  Necessitation is deliberately omitted: in modal logic,
    [Nec] only applies to closed proofs, not to derivations under
    open assumptions, since [phi] in the modal-K sense is
    [|- phi -> |- Box n phi] — a metatheorem, not a Hilbert rule on
    hypotheses.  This restriction is what makes the deduction
    theorem hold. *)

Inductive Provable_with_hyp : list Form -> Form -> Prop :=
  | DT_hyp : forall Gamma alpha,
      In alpha Gamma -> Provable_with_hyp Gamma alpha
  | DT_thm : forall Gamma alpha,
      |- alpha -> Provable_with_hyp Gamma alpha
  | DT_MP : forall Gamma alpha beta,
      Provable_with_hyp Gamma (Impl alpha beta) ->
      Provable_with_hyp Gamma alpha ->
      Provable_with_hyp Gamma beta.

(** ** The deduction theorem.

    If [phi] discharges to [psi] under hypotheses [Gamma], then
    [phi -> psi] is derivable from [Gamma] alone.  Standard Hilbert-
    calculus result, valid here because [Provable_with_hyp] omits
    [Nec]. *)

Theorem deduction_theorem : forall Gamma phi psi,
  Provable_with_hyp (phi :: Gamma) psi ->
  Provable_with_hyp Gamma (Impl phi psi).
Proof.
  intros Gamma phi psi H.
  remember (phi :: Gamma) as G eqn:HG.
  generalize dependent Gamma. generalize dependent phi.
  induction H as [G' alpha Hin | G' alpha Hthm
                   | G' alpha beta Himp IHimp Halpha IHalpha];
    intros phi Gamma HG.
  - (* DT_hyp: alpha is in G = phi :: Gamma. *)
    subst G'. simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst alpha. apply DT_thm. apply prov_id.
    + apply DT_MP with (alpha := alpha).
      * apply DT_thm. apply Ax_K.
      * apply DT_hyp. exact Hin'.
  - (* DT_thm: alpha is a closed theorem; weaken via Ax_K. *)
    apply DT_thm. exact (MP _ _ (Ax_K alpha phi) Hthm).
  - (* DT_MP: chain via Ax_S. *)
    subst G'.
    pose proof (IHimp phi Gamma eq_refl) as HI1.
    pose proof (IHalpha phi Gamma eq_refl) as HI2.
    apply DT_MP with (alpha := Impl phi alpha).
    + apply DT_MP with (alpha := Impl phi (Impl alpha beta)).
      * apply DT_thm. exact (Ax_S phi alpha beta).
      * exact HI1.
    + exact HI2.
Qed.

(** ** Reflexivity, intro, symmetry for Iff. *)

Lemma prov_iff_refl : forall phi, |- Iff phi phi.
Proof.
  intro phi. unfold Iff.
  exact (prov_and_intro_meta _ _ (prov_id phi) (prov_id phi)).
Qed.

Lemma prov_iff_intro : forall phi psi,
  |- Impl phi psi -> |- Impl psi phi -> |- Iff phi psi.
Proof.
  intros phi psi H1 H2. unfold Iff.
  exact (prov_and_intro_meta _ _ H1 H2).
Qed.

Lemma prov_iff_sym : forall phi psi,
  |- Iff phi psi -> |- Iff psi phi.
Proof.
  intros phi psi H. unfold Iff in *.
  pose proof (prov_and_elim_l_meta _ _ H) as H1.
  pose proof (prov_and_elim_r_meta _ _ H) as H2.
  exact (prov_and_intro_meta _ _ H2 H1).
Qed.

(** ** Diamond elimination.

    [Diamond n phi := Neg (Box n (Neg phi))] is a definition, not a
    constructor.  Every Diamond-involving formula is already Box-only
    by definitional unfolding; the provability relation is unaffected
    by whether one writes [Diamond] or its unfolding. *)

Theorem diamond_elimination : forall n phi,
  |- Diamond n phi <-> |- Neg (Box n (Neg phi)).
Proof.
  intros n phi. unfold Diamond. split; intro H; exact H.
Qed.

(** ** Diamond cross-level monotonicity.

    [Diamond (S n) phi -> Diamond n phi] by contraposition of
    [Ax_Mon] applied to [Neg phi]. *)

Lemma prov_diamond_mon : forall n phi,
  |- Impl (Diamond (S n) phi) (Diamond n phi).
Proof.
  intros n phi. unfold Diamond.
  pose proof (Ax_Mon n (Neg phi)) as Hmon.
  pose proof (prov_contrapos (Box n (Neg phi)) (Box (S n) (Neg phi))) as Hcon.
  exact (MP _ _ Hcon Hmon).
Qed.

(** ** Diamond modus ponens.

    From [|- Box n (phi -> psi)] and [|- Diamond n phi] derive
    [|- Diamond n psi]. *)

Lemma prov_diamond_mp : forall n phi psi,
  |- Box n (Impl phi psi) -> |- Diamond n phi -> |- Diamond n psi.
Proof.
  intros n phi psi Himp Hdia. unfold Diamond in *.
  pose proof (prov_contrapos phi psi) as Hcon.
  pose proof (Nec n _ Hcon) as Hncon.
  pose proof (Ax_BoxK n (Impl phi psi)
                       (Impl (Neg psi) (Neg phi))) as HBK1.
  pose proof (MP _ _ HBK1 Hncon) as Hstep1.
  pose proof (MP _ _ Hstep1 Himp) as Hbcontra.
  pose proof (Ax_BoxK n (Neg psi) (Neg phi)) as HBK2.
  pose proof (MP _ _ HBK2 Hbcontra) as Himpneg.
  exact (prov_compose _ _ _ Himpneg Hdia).
Qed.

(** ** Substitution and finite axiom carriers.

    The schemata [Ax_K], [Ax_S], [Ax_DN], [Ax_BoxK n], [Ax_Loeb n],
    [Ax_Box4 n], [Ax_Mon n], [Ax_NextCon n] in [Provable] are
    presented in Coq with universal quantification over their formula
    arguments.  Each schema is generated by a single fixed
    "axiom carrier" formula in the propositional variables [Var 0],
    [Var 1], [Var 2], closed under uniform substitution of arbitrary
    formulas for variables.  The level index [n] remains a metalevel
    nat parameter.

    The result: [Provable] is equivalent to the closure of eight
    carrier formulas under uniform substitution, modus ponens, and
    necessitation. *)

Fixpoint subst_form (sigma : nat -> Form) (phi : Form) : Form :=
  match phi with
  | Var p => sigma p
  | Bot => Bot
  | Impl X Y => Impl (subst_form sigma X) (subst_form sigma Y)
  | Box n psi => Box n (subst_form sigma psi)
  end.

Definition AxK_carrier : Form :=
  Impl (Var 0) (Impl (Var 1) (Var 0)).
Definition AxS_carrier : Form :=
  Impl (Impl (Var 0) (Impl (Var 1) (Var 2)))
       (Impl (Impl (Var 0) (Var 1)) (Impl (Var 0) (Var 2))).
Definition AxDN_carrier : Form :=
  Impl (Neg (Neg (Var 0))) (Var 0).
Definition AxBoxK_carrier (n : nat) : Form :=
  Impl (Box n (Impl (Var 0) (Var 1)))
       (Impl (Box n (Var 0)) (Box n (Var 1))).
Definition AxLoeb_carrier (n : nat) : Form :=
  Impl (Box n (Impl (Box n (Var 0)) (Var 0))) (Box n (Var 0)).
Definition AxBox4_carrier (n : nat) : Form :=
  Impl (Box n (Var 0)) (Box n (Box n (Var 0))).
Definition AxMon_carrier (n : nat) : Form :=
  Impl (Box n (Var 0)) (Box (S n) (Var 0)).
Definition AxNextCon_carrier (n : nat) : Form :=
  Box (S n) (Neg (Box n Bot)).

Inductive FAxProvable : Form -> Prop :=
  | FAx_K_inst : forall sigma,
      FAxProvable (subst_form sigma AxK_carrier)
  | FAx_S_inst : forall sigma,
      FAxProvable (subst_form sigma AxS_carrier)
  | FAx_DN_inst : forall sigma,
      FAxProvable (subst_form sigma AxDN_carrier)
  | FAx_BoxK_inst : forall n sigma,
      FAxProvable (subst_form sigma (AxBoxK_carrier n))
  | FAx_Loeb_inst : forall n sigma,
      FAxProvable (subst_form sigma (AxLoeb_carrier n))
  | FAx_Box4_inst : forall n sigma,
      FAxProvable (subst_form sigma (AxBox4_carrier n))
  | FAx_Mon_inst : forall n sigma,
      FAxProvable (subst_form sigma (AxMon_carrier n))
  | FAx_NextCon_inst : forall n,
      FAxProvable (AxNextCon_carrier n)
  | FMP : forall phi psi,
      FAxProvable (Impl phi psi) -> FAxProvable phi -> FAxProvable psi
  | FNec : forall n phi,
      FAxProvable phi -> FAxProvable (Box n phi).

Definition sub1 (phi : Form) : nat -> Form := fun _ => phi.
Definition sub2 (phi psi : Form) : nat -> Form :=
  fun k => match k with 0 => phi | _ => psi end.
Definition sub3 (phi psi chi : Form) : nat -> Form :=
  fun k => match k with 0 => phi | 1 => psi | _ => chi end.

Theorem fax_provable_sound : forall phi, FAxProvable phi -> |- phi.
Proof.
  intros phi H. induction H; cbn.
  - apply Ax_K.
  - apply Ax_S.
  - apply Ax_DN.
  - apply Ax_BoxK.
  - apply Ax_Loeb.
  - apply Ax_Box4.
  - apply Ax_Mon.
  - apply Ax_NextCon.
  - exact (MP _ _ IHFAxProvable1 IHFAxProvable2).
  - exact (Nec _ _ IHFAxProvable).
Qed.

Theorem fax_provable_complete : forall phi, |- phi -> FAxProvable phi.
Proof.
  intros phi H. induction H.
  - exact (FAx_K_inst (sub2 phi psi)).
  - exact (FAx_S_inst (sub3 phi psi chi)).
  - exact (FAx_DN_inst (sub1 phi)).
  - exact (FAx_BoxK_inst n (sub2 phi psi)).
  - exact (FAx_Loeb_inst n (sub1 phi)).
  - exact (FAx_Box4_inst n (sub1 phi)).
  - exact (FAx_Mon_inst n (sub1 phi)).
  - exact (FAx_NextCon_inst n).
  - exact (FMP _ _ IHProvable1 IHProvable2).
  - exact (FNec _ _ IHProvable).
Qed.

Theorem finite_axiomatisation : forall phi, FAxProvable phi <-> |- phi.
Proof.
  intro phi. split.
  - apply fax_provable_sound.
  - apply fax_provable_complete.
Qed.

Fixpoint level_lift (k : nat) (phi : Form) : Form :=
  match phi with
  | Var p => Var p
  | Bot => Bot
  | Impl X Y => Impl (level_lift k X) (level_lift k Y)
  | Box n psi => Box (n + k) (level_lift k psi)
  end.

Definition AxBoxK_carrier_base : Form :=
  Impl (Box 0 (Impl (Var 0) (Var 1)))
       (Impl (Box 0 (Var 0)) (Box 0 (Var 1))).
Definition AxLoeb_carrier_base : Form :=
  Impl (Box 0 (Impl (Box 0 (Var 0)) (Var 0))) (Box 0 (Var 0)).
Definition AxBox4_carrier_base : Form :=
  Impl (Box 0 (Var 0)) (Box 0 (Box 0 (Var 0))).
Definition AxMon_carrier_base : Form :=
  Impl (Box 0 (Var 0)) (Box 1 (Var 0)).
Definition AxNextCon_carrier_base : Form :=
  Box 1 (Neg (Box 0 Bot)).

Inductive FAx2Provable : Form -> Prop :=
  | F2_AxK_inst : forall sigma k,
      FAx2Provable (subst_form sigma (level_lift k AxK_carrier))
  | F2_AxS_inst : forall sigma k,
      FAx2Provable (subst_form sigma (level_lift k AxS_carrier))
  | F2_AxDN_inst : forall sigma k,
      FAx2Provable (subst_form sigma (level_lift k AxDN_carrier))
  | F2_AxBoxK_inst : forall sigma k,
      FAx2Provable (subst_form sigma (level_lift k AxBoxK_carrier_base))
  | F2_AxLoeb_inst : forall sigma k,
      FAx2Provable (subst_form sigma (level_lift k AxLoeb_carrier_base))
  | F2_AxBox4_inst : forall sigma k,
      FAx2Provable (subst_form sigma (level_lift k AxBox4_carrier_base))
  | F2_AxMon_inst : forall sigma k,
      FAx2Provable (subst_form sigma (level_lift k AxMon_carrier_base))
  | F2_AxNextCon_inst : forall k,
      FAx2Provable (level_lift k AxNextCon_carrier_base)
  | F2_MP : forall phi psi,
      FAx2Provable (Impl phi psi) -> FAx2Provable phi -> FAx2Provable psi
  | F2_Nec : forall n phi,
      FAx2Provable phi -> FAx2Provable (Box n phi).

Theorem fax2_to_provable : forall phi, FAx2Provable phi -> |- phi.
Proof.
  intros phi H. induction H; cbn in *.
  - apply Ax_K.
  - apply Ax_S.
  - apply Ax_DN.
  - apply Ax_BoxK.
  - apply Ax_Loeb.
  - apply Ax_Box4.
  - apply Ax_Mon.
  - apply Ax_NextCon.
  - exact (MP _ _ IHFAx2Provable1 IHFAx2Provable2).
  - exact (Nec _ _ IHFAx2Provable).
Qed.

Theorem provable_to_fax2 : forall phi, |- phi -> FAx2Provable phi.
Proof.
  intros phi H. induction H.
  - exact (F2_AxK_inst (sub2 phi psi) 0).
  - exact (F2_AxS_inst (sub3 phi psi chi) 0).
  - exact (F2_AxDN_inst (sub1 phi) 0).
  - exact (F2_AxBoxK_inst (sub2 phi psi) n).
  - exact (F2_AxLoeb_inst (sub1 phi) n).
  - exact (F2_AxBox4_inst (sub1 phi) n).
  - exact (F2_AxMon_inst (sub1 phi) n).
  - exact (F2_AxNextCon_inst n).
  - exact (F2_MP _ _ IHProvable1 IHProvable2).
  - exact (F2_Nec _ _ IHProvable).
Qed.

Theorem finite_axiomatisation_levelsubst : forall phi, FAx2Provable phi <-> |- phi.
Proof.
  intro phi. split; [apply fax2_to_provable | apply provable_to_fax2].
Qed.

(** ** Lindenbaum-Tarski algebra of GLP*.

    The provable-equivalence relation [prov_equiv] partitions [Form]
    into equivalence classes; the quotient is the Lindenbaum-Tarski
    algebra of the calculus.  We establish the algebra's structural
    properties directly: [prov_equiv] is reflexive, symmetric, and
    transitive; it is a congruence for [Impl] and [Box n]; and the
    algebra is non-degenerate ([Top] and [Bot] are not in the same
    class).  The non-degeneracy proof routes through Kripke soundness
    against the [F0] frame, giving an independent witness of
    [~(|- Bot)] that does not invoke the trivial-truth-assignment
    used in [meta_consistency_system]. *)

Definition prov_equiv (phi psi : Form) : Prop := |- Iff phi psi.

Lemma prov_equiv_refl : forall phi, prov_equiv phi phi.
Proof. intro phi. unfold prov_equiv. apply prov_iff_refl. Qed.

Lemma prov_equiv_sym : forall phi psi,
  prov_equiv phi psi -> prov_equiv psi phi.
Proof.
  intros phi psi H. unfold prov_equiv in *.
  apply prov_iff_sym. exact H.
Qed.

Lemma prov_equiv_trans : forall phi psi chi,
  prov_equiv phi psi -> prov_equiv psi chi -> prov_equiv phi chi.
Proof.
  intros phi psi chi Hpq Hqr.
  unfold prov_equiv, Iff in *.
  pose proof (prov_and_elim_l_meta _ _ Hpq) as Hpq_f.
  pose proof (prov_and_elim_r_meta _ _ Hpq) as Hpq_b.
  pose proof (prov_and_elim_l_meta _ _ Hqr) as Hqr_f.
  pose proof (prov_and_elim_r_meta _ _ Hqr) as Hqr_b.
  apply prov_and_intro_meta.
  - exact (prov_compose _ _ _ Hpq_f Hqr_f).
  - exact (prov_compose _ _ _ Hqr_b Hpq_b).
Qed.

Lemma prov_equiv_impl_cong : forall phi1 phi2 psi1 psi2,
  prov_equiv phi1 phi2 -> prov_equiv psi1 psi2 ->
  prov_equiv (Impl phi1 psi1) (Impl phi2 psi2).
Proof.
  intros phi1 phi2 psi1 psi2 H1 H2.
  unfold prov_equiv, Iff in *.
  pose proof (prov_and_elim_l_meta _ _ H1) as H1f.
  pose proof (prov_and_elim_r_meta _ _ H1) as H1b.
  pose proof (prov_and_elim_l_meta _ _ H2) as H2f.
  pose proof (prov_and_elim_r_meta _ _ H2) as H2b.
  apply prov_and_intro_meta.
  - pose proof (prov_compose_internal phi2 phi1 psi1) as Hci1.
    pose proof (MP _ _ (prov_perm _ _ _ Hci1) H1b) as Hstep1.
    pose proof (prov_compose_internal phi2 psi1 psi2) as Hci2.
    pose proof (MP _ _ Hci2 H2f) as Hstep2.
    exact (prov_compose _ _ _ Hstep1 Hstep2).
  - pose proof (prov_compose_internal phi1 phi2 psi2) as Hci1.
    pose proof (MP _ _ (prov_perm _ _ _ Hci1) H1f) as Hstep1.
    pose proof (prov_compose_internal phi1 psi2 psi1) as Hci2.
    pose proof (MP _ _ Hci2 H2b) as Hstep2.
    exact (prov_compose _ _ _ Hstep1 Hstep2).
Qed.

Lemma prov_equiv_box_cong : forall n phi psi,
  prov_equiv phi psi -> prov_equiv (Box n phi) (Box n psi).
Proof.
  intros n phi psi H. unfold prov_equiv, Iff in *.
  pose proof (prov_and_elim_l_meta _ _ H) as Hf.
  pose proof (prov_and_elim_r_meta _ _ H) as Hb.
  apply prov_and_intro_meta.
  - exact (prov_box_imp n _ _ Hf).
  - exact (prov_box_imp n _ _ Hb).
Qed.

Theorem meta_consistency_via_kripke : ~ (|- Bot).
Proof.
  intro Hbot.
  pose proof (soundness Bot Hbot) as Hval.
  exact (Hval F0 (fun _ _ => false) true).
Qed.

Theorem lindenbaum_tarski_non_degenerate :
  ~ prov_equiv Top Bot.
Proof.
  intro Hequiv. unfold prov_equiv, Iff in Hequiv.
  pose proof (prov_and_elim_l_meta _ _ Hequiv) as Himp.
  pose proof (prov_id Bot) as Htop.
  pose proof (MP _ _ Himp Htop) as Hbot.
  exact (meta_consistency_via_kripke Hbot).
Qed.

(** ** Level-indexed Gödel-Rosser theorem.

    For every [n], [Var 0] is independent at level [n]: neither
    [Box n (Var 0)] nor [Box n (Neg (Var 0))] is provable.  Both
    unprovabilities follow from Kripke soundness against [Fnat] at
    world [S n], with [Var 0] valued uniformly false (resp. true).
    Establishes that level-[n] provability is genuinely incomplete in
    the Gödel sense at every level. *)

Theorem godel_rosser_every_level : forall n,
  exists phi, ~ (|- Box n phi) /\ ~ (|- Box n (Neg phi)).
Proof.
  intro n. exists (Var 0). split.
  - intro H.
    pose proof (soundness _ H Fnat (fun _ _ => false) (S n)) as Hf.
    simpl in Hf.
    assert (Hsucc : Fnat_R n (S n) n) by (unfold Fnat_R; split; lia).
    pose proof (Hf n Hsucc) as Hcontra. discriminate.
  - intro H.
    pose proof (soundness _ H Fnat (fun _ _ => true) (S n)) as Hf.
    simpl in Hf.
    assert (Hsucc : Fnat_R n (S n) n) by (unfold Fnat_R; split; lia).
    exact (Hf n Hsucc eq_refl).
Qed.

(** ** Frame-condition independence.

    Each of the four [Frame] conditions is independent of the other
    three: for each condition there is a [(W, R)] satisfying the other
    three but violating that one.  Each counter-frame is exhibited by
    a relation on a small finite or natural-numbered carrier. *)

(** *** Counter-frame violating transitivity. *)

Definition R_break_trans (n : nat) (w v : nat) : Prop :=
  match n with
  | 0 => (w = 0 /\ v = 1) \/ (w = 1 /\ v = 2)
  | _ => False
  end.

Lemma R_break_trans_NOT_trans :
  ~ (forall n w v u,
        R_break_trans n w v -> R_break_trans n v u -> R_break_trans n w u).
Proof.
  intro Htr.
  specialize (Htr 0 0 1 2).
  assert (H01 : R_break_trans 0 0 1) by (left; split; reflexivity).
  assert (H12 : R_break_trans 0 1 2) by (right; split; reflexivity).
  pose proof (Htr H01 H12) as H02. simpl in H02.
  destruct H02 as [[_ H]|[H _]]; discriminate.
Qed.

Lemma R_break_trans_wf :
  forall n, well_founded (fun u v => R_break_trans n v u).
Proof.
  intros n x.
  destruct n as [|n'].
  2: { apply Acc_intro. intros y Hy. simpl in Hy. contradiction. }
  destruct x as [|[|x']].
  - apply Acc_intro. intros y Hy. simpl in Hy.
    destruct Hy as [[_ Hy]|[H _]]; [|discriminate].
    subst y. apply Acc_intro. intros z Hz. simpl in Hz.
    destruct Hz as [[H _]|[_ Hz]]; [discriminate|].
    subst z. apply Acc_intro. intros w Hw. simpl in Hw.
    destruct Hw as [[H _]|[H _]]; discriminate.
  - apply Acc_intro. intros z Hz. simpl in Hz.
    destruct Hz as [[H _]|[_ Hz]]; [discriminate|].
    subst z. apply Acc_intro. intros w Hw. simpl in Hw.
    destruct Hw as [[H _]|[H _]]; discriminate.
  - apply Acc_intro. intros y Hy. simpl in Hy.
    destruct Hy as [[H _]|[H _]]; discriminate.
Qed.

Lemma R_break_trans_mon : forall n w v,
  R_break_trans (S n) w v -> R_break_trans n w v.
Proof. intros n w v H. simpl in H. contradiction. Qed.

Lemma R_break_trans_nextcon : forall n w v,
  R_break_trans (S n) w v -> exists u, R_break_trans n v u.
Proof. intros n w v H. simpl in H. contradiction. Qed.

(** *** Counter-frame violating converse-well-foundedness.
    [W := nat], [R n w v := w < v] at every level. *)

Definition R_break_wf (n : nat) (w v : nat) : Prop := w < v.

Lemma R_break_wf_trans : forall n w v u,
  R_break_wf n w v -> R_break_wf n v u -> R_break_wf n w u.
Proof. intros n w v u H1 H2. unfold R_break_wf in *. lia. Qed.

Lemma R_break_wf_NOT_wf :
  ~ (forall n, well_founded (fun u v => R_break_wf n v u)).
Proof.
  intro Hwf. pose proof (Hwf 0) as Hwf0.
  assert (Hloop : forall a,
    Acc (fun u v => R_break_wf 0 v u) a ->
    forall (t : nat -> nat),
      t 0 = a ->
      (forall n, R_break_wf 0 (t n) (t (S n))) ->
      False).
  { intros a Hacc. induction Hacc as [a _ IH].
    intros t Heq Hch.
    assert (Hpf : R_break_wf 0 a (t 1)).
    { rewrite <- Heq. exact (Hch 0). }
    exact (IH (t 1) Hpf (fun n => t (S n)) eq_refl
              (fun n => Hch (S n))). }
  apply (Hloop 0 (Hwf0 0) (fun n => n) eq_refl).
  intro n. unfold R_break_wf. lia.
Qed.

Lemma R_break_wf_mon : forall n w v,
  R_break_wf (S n) w v -> R_break_wf n w v.
Proof. intros n w v H. exact H. Qed.

Lemma R_break_wf_nextcon : forall n w v,
  R_break_wf (S n) w v -> exists u, R_break_wf n v u.
Proof.
  intros n w v H. exists (S v). unfold R_break_wf. lia.
Qed.

(** *** Counter-frame violating monotone inclusion.
    [W := nat] with [R 0 := {(1,2)}], [R 1 := {(0,1)}], [R n] empty
    for [n>=2].  [R 1] not a subset of [R 0] because [(0,1)] in [R 1]
    but not in [R 0]. *)

Definition R_break_mon (n : nat) (w v : nat) : Prop :=
  match n with
  | 0 => w = 1 /\ v = 2
  | 1 => w = 0 /\ v = 1
  | _ => False
  end.

Lemma R_break_mon_trans : forall n w v u,
  R_break_mon n w v -> R_break_mon n v u -> R_break_mon n w u.
Proof.
  intros [|[|n]] w v u H1 H2; simpl in *; try contradiction.
  - destruct H1 as [_ Hv]. destruct H2 as [Hv' _]. subst. discriminate.
  - destruct H1 as [_ Hv]. destruct H2 as [Hv' _]. subst. discriminate.
Qed.

Lemma R_break_mon_wf :
  forall n, well_founded (fun u v => R_break_mon n v u).
Proof.
  intros n x.
  destruct n as [|[|n']].
  - (* n=0: predecessors of x are y with x=1 /\ y=2 *)
    apply Acc_intro. intros y Hy. simpl in Hy.
    destruct Hy as [Hx Hy]. subst.
    apply Acc_intro. intros z Hz. simpl in Hz.
    destruct Hz as [Hz _]. discriminate.
  - (* n=1 *)
    apply Acc_intro. intros y Hy. simpl in Hy.
    destruct Hy as [Hx Hy]. subst.
    apply Acc_intro. intros z Hz. simpl in Hz.
    destruct Hz as [Hz _]. discriminate.
  - (* n>=2: empty *)
    apply Acc_intro. intros y Hy. simpl in Hy. contradiction.
Qed.

Lemma R_break_mon_NOT_mon :
  ~ (forall n w v, R_break_mon (S n) w v -> R_break_mon n w v).
Proof.
  intro Hm. specialize (Hm 0 0 1).
  assert (H : R_break_mon 1 0 1) by (simpl; split; reflexivity).
  pose proof (Hm H) as Hbad. simpl in Hbad.
  destruct Hbad as [Hbad _]. discriminate.
Qed.

Lemma R_break_mon_nextcon : forall n w v,
  R_break_mon (S n) w v -> exists u, R_break_mon n v u.
Proof.
  intros [|[|n]] w v H; simpl in H; try contradiction.
  - destruct H as [Hw Hv]. subst. exists 2. simpl. split; reflexivity.
Qed.

(** *** Counter-frame violating NextCon successor.
    [W := nat] with [R 0 := {(0,1)}], [R 1 := {(0,1)}], higher empty.
    NextCon at level 0 fails: [R 1 (0,1)] holds but [R 0 1 _] is
    empty. *)

Definition R_break_nc (n : nat) (w v : nat) : Prop :=
  match n with
  | 0 => w = 0 /\ v = 1
  | 1 => w = 0 /\ v = 1
  | _ => False
  end.

Lemma R_break_nc_trans : forall n w v u,
  R_break_nc n w v -> R_break_nc n v u -> R_break_nc n w u.
Proof.
  intros [|[|n']] w v u H1 H2; simpl in *; try contradiction;
    destruct H1 as [_ Hv]; destruct H2 as [Hv' _]; subst; discriminate.
Qed.

Lemma R_break_nc_wf :
  forall n, well_founded (fun u v => R_break_nc n v u).
Proof.
  intros n x.
  destruct n as [|[|n']].
  - apply Acc_intro. intros y Hy. simpl in Hy.
    destruct Hy as [Hx Hy]. subst.
    apply Acc_intro. intros z Hz. simpl in Hz.
    destruct Hz as [Hz _]. discriminate.
  - apply Acc_intro. intros y Hy. simpl in Hy.
    destruct Hy as [Hx Hy]. subst.
    apply Acc_intro. intros z Hz. simpl in Hz.
    destruct Hz as [Hz _]. discriminate.
  - apply Acc_intro. intros y Hy. simpl in Hy. contradiction.
Qed.

Lemma R_break_nc_mon : forall n w v,
  R_break_nc (S n) w v -> R_break_nc n w v.
Proof.
  intros [|[|n]] w v H; simpl in *; try contradiction.
  exact H.
Qed.

Lemma R_break_nc_NOT_nc :
  ~ (forall n w v, R_break_nc (S n) w v -> exists u, R_break_nc n v u).
Proof.
  intro Hnc. specialize (Hnc 0 0 1).
  assert (H : R_break_nc 1 0 1) by (simpl; split; reflexivity).
  pose proof (Hnc H) as [u Hu]. simpl in Hu.
  destruct Hu as [Hu _]. discriminate.
Qed.

Theorem frame_indep_trans :
  exists Rt : nat -> nat -> nat -> Prop,
    (forall n, well_founded (fun u v => Rt n v u)) /\
    (forall n w v, Rt (S n) w v -> Rt n w v) /\
    (forall n w v, Rt (S n) w v -> exists u, Rt n v u) /\
    ~ (forall n w v u, Rt n w v -> Rt n v u -> Rt n w u).
Proof.
  exists R_break_trans.
  refine (conj _ (conj _ (conj _ _))).
  - exact R_break_trans_wf.
  - exact R_break_trans_mon.
  - exact R_break_trans_nextcon.
  - exact R_break_trans_NOT_trans.
Qed.

Theorem frame_indep_wf :
  exists Rt : nat -> nat -> nat -> Prop,
    (forall n w v u, Rt n w v -> Rt n v u -> Rt n w u) /\
    (forall n w v, Rt (S n) w v -> Rt n w v) /\
    (forall n w v, Rt (S n) w v -> exists u, Rt n v u) /\
    ~ (forall n, well_founded (fun u v => Rt n v u)).
Proof.
  exists R_break_wf.
  refine (conj _ (conj _ (conj _ _))).
  - exact R_break_wf_trans.
  - exact R_break_wf_mon.
  - exact R_break_wf_nextcon.
  - exact R_break_wf_NOT_wf.
Qed.

Theorem frame_indep_mon :
  exists Rt : nat -> nat -> nat -> Prop,
    (forall n w v u, Rt n w v -> Rt n v u -> Rt n w u) /\
    (forall n, well_founded (fun u v => Rt n v u)) /\
    (forall n w v, Rt (S n) w v -> exists u, Rt n v u) /\
    ~ (forall n w v, Rt (S n) w v -> Rt n w v).
Proof.
  exists R_break_mon.
  refine (conj _ (conj _ (conj _ _))).
  - exact R_break_mon_trans.
  - exact R_break_mon_wf.
  - exact R_break_mon_nextcon.
  - exact R_break_mon_NOT_mon.
Qed.

Theorem frame_indep_nc :
  exists Rt : nat -> nat -> nat -> Prop,
    (forall n w v u, Rt n w v -> Rt n v u -> Rt n w u) /\
    (forall n, well_founded (fun u v => Rt n v u)) /\
    (forall n w v, Rt (S n) w v -> Rt n w v) /\
    ~ (forall n w v, Rt (S n) w v -> exists u, Rt n v u).
Proof.
  exists R_break_nc.
  refine (conj _ (conj _ (conj _ _))).
  - exact R_break_nc_trans.
  - exact R_break_nc_wf.
  - exact R_break_nc_mon.
  - exact R_break_nc_NOT_nc.
Qed.

(** ** Substitution theorem.

    Define [Subst p psi phi] as the result of substituting [psi] for
    [Var p] in [phi].  The general schematic substitution theorem
    [subst_provable] says: for any [sigma : nat -> Form] and any
    theorem [|- phi], the substituted formula is also a theorem.
    [Subst] is the single-variable instance.  Establishes that the
    schematic axioms of GLP* really are uniform schemas in the
    object calculus, not artifacts of Coq's parametric polymorphism. *)

Theorem subst_provable : forall sigma phi, |- phi -> |- subst_form sigma phi.
Proof.
  intros sigma phi H. induction H; cbn.
  - apply Ax_K.
  - apply Ax_S.
  - apply Ax_DN.
  - apply Ax_BoxK.
  - apply Ax_Loeb.
  - apply Ax_Box4.
  - apply Ax_Mon.
  - apply Ax_NextCon.
  - exact (MP _ _ IHProvable1 IHProvable2).
  - exact (Nec _ _ IHProvable).
Qed.

Definition Subst (p : nat) (psi phi : Form) : Form :=
  subst_form (fun k => if Nat.eqb k p then psi else Var k) phi.

Theorem prov_Subst : forall p psi phi, |- phi -> |- Subst p psi phi.
Proof.
  intros p psi phi H. unfold Subst. apply subst_provable. exact H.
Qed.

(** ** Replacement congruence.

    [|- Iff phi psi] implies [|- Iff (Subst p phi chi) (Subst p psi chi)].
    Substituting provably-equivalent formulas for the same variable in
    any context [chi] gives provably-equivalent results.  Proof by
    structural induction on [chi] using [prov_equiv_impl_cong] and
    [prov_equiv_box_cong]. *)

Theorem prov_replacement : forall p phi psi chi,
  |- Iff phi psi -> prov_equiv (Subst p phi chi) (Subst p psi chi).
Proof.
  intros p phi psi chi Hequiv.
  induction chi as [k | | X IHX Y IHY | n psi' IHpsi'].
  - unfold Subst, prov_equiv. cbn.
    destruct (Nat.eqb k p) eqn:Heq.
    + exact Hequiv.
    + apply prov_iff_refl.
  - unfold Subst, prov_equiv. cbn. apply prov_iff_refl.
  - unfold Subst in *. cbn. apply prov_equiv_impl_cong; assumption.
  - unfold Subst in *. cbn. apply prov_equiv_box_cong; assumption.
Qed.

(** ** Iff form of Löb.

    [|- Iff (Box n phi) (Box n (Impl (Box n phi) phi))].  Forward
    direction is K applied to [Ax_K phi (Box n phi)] necessitated and
    distributed; backward direction is exactly [Ax_Loeb]. *)

Theorem loeb_iff : forall n phi,
  |- Iff (Box n phi) (Box n (Impl (Box n phi) phi)).
Proof.
  intros n phi.
  apply prov_iff_intro.
  - pose proof (Ax_K phi (Box n phi)) as Hk.
    pose proof (Nec n _ Hk) as Hnec.
    pose proof (Ax_BoxK n phi (Impl (Box n phi) phi)) as HBK.
    exact (MP _ _ HBK Hnec).
  - exact (Ax_Loeb n phi).
Qed.

(** ** Trivial fragment.

    [ProvableProp] is the sub-calculus of [Provable] that uses only
    the classical propositional axioms [K], [S], [DN] and modus
    ponens, with no modal axioms or necessitation rule.  By
    construction this is the standard Hilbert axiomatisation of
    classical propositional logic (cf. Hilbert-Bernays 1934).

    Below: structural embedding into [Provable]; soundness with
    respect to the classical truth-table semantics; modus ponens for
    [eval] confirming the rule is sound; and the lemma that
    [ProvableProp] proofs cannot escape into modal-formula territory
    via their conclusion. *)

Inductive ProvableProp : Form -> Prop :=
  | PAx_K : forall phi psi,
      ProvableProp (Impl phi (Impl psi phi))
  | PAx_S : forall phi psi chi,
      ProvableProp (Impl (Impl phi (Impl psi chi))
                         (Impl (Impl phi psi) (Impl phi chi)))
  | PAx_DN : forall phi,
      ProvableProp (Impl (Neg (Neg phi)) phi)
  | PMP : forall phi psi,
      ProvableProp (Impl phi psi) -> ProvableProp phi -> ProvableProp psi.

Theorem trivial_in_provable : forall phi, ProvableProp phi -> |- phi.
Proof.
  intros phi H. induction H.
  - apply Ax_K.
  - apply Ax_S.
  - apply Ax_DN.
  - exact (MP _ _ IHProvableProp1 IHProvableProp2).
Qed.

Theorem trivial_classically_sound : forall val phi,
  ProvableProp phi -> eval val phi = true.
Proof.
  intros val phi H. induction H; simpl in *.
  - destruct (eval val phi); destruct (eval val psi); reflexivity.
  - destruct (eval val phi); destruct (eval val psi);
      destruct (eval val chi); reflexivity.
  - destruct (eval val phi); reflexivity.
  - destruct (eval val phi); simpl in IHProvableProp1.
    + exact IHProvableProp1.
    + discriminate IHProvableProp2.
Qed.

Lemma PP_id : forall phi, ProvableProp (Impl phi phi).
Proof.
  intro phi.
  exact (PMP _ _
          (PMP _ _ (PAx_S phi (Impl phi phi) phi)
                       (PAx_K phi (Impl phi phi)))
          (PAx_K phi phi)).
Qed.

Lemma PP_weaken : forall phi psi,
  ProvableProp phi -> ProvableProp (Impl psi phi).
Proof. intros phi psi Hphi. exact (PMP _ _ (PAx_K phi psi) Hphi). Qed.

Lemma PP_compose : forall phi psi chi,
  ProvableProp (Impl phi psi) ->
  ProvableProp (Impl psi chi) ->
  ProvableProp (Impl phi chi).
Proof.
  intros phi psi chi Hpq Hqr.
  pose proof (PAx_S phi psi chi) as Hs.
  pose proof (PP_weaken _ phi Hqr) as Hpqr.
  exact (PMP _ _ (PMP _ _ Hs Hpqr) Hpq).
Qed.

Lemma PP_perm : forall phi psi chi,
  ProvableProp (Impl phi (Impl psi chi)) ->
  ProvableProp (Impl psi (Impl phi chi)).
Proof.
  intros phi psi chi H.
  pose proof (PAx_S phi psi chi) as Hs.
  pose proof (PMP _ _ Hs H) as H1.
  pose proof (PAx_K psi phi) as Hk.
  exact (PP_compose _ _ _ Hk H1).
Qed.

Lemma PP_DN_intro : forall phi, ProvableProp (Impl phi (Neg (Neg phi))).
Proof.
  intro phi. unfold Neg.
  pose proof (PP_id (Impl phi Bot)) as Hid.
  exact (PP_perm _ _ _ Hid).
Qed.

Lemma PP_explosion : forall phi, ProvableProp (Impl Bot phi).
Proof.
  intro phi.
  pose proof (PAx_K Bot (Neg phi)) as Hk.
  pose proof (PAx_DN phi) as HDN.
  exact (PP_compose _ _ _ Hk HDN).
Qed.

Lemma PP_compose_internal : forall phi psi chi,
  ProvableProp (Impl (Impl psi chi) (Impl (Impl phi psi) (Impl phi chi))).
Proof.
  intros phi psi chi.
  pose proof (PAx_K (Impl psi chi) phi) as Hk.
  pose proof (PAx_S phi psi chi) as Hs.
  exact (PP_compose _ _ _ Hk Hs).
Qed.

Lemma PP_perm_internal : forall a b c,
  ProvableProp (Impl (Impl a (Impl b c)) (Impl b (Impl a c))).
Proof.
  intros a b c.
  pose proof (PAx_S a b c) as H_S.
  pose proof (PAx_S (Impl a (Impl b c)) (Impl a b) (Impl a c)) as H_S2.
  pose proof (PMP _ _ H_S2 H_S) as H1.
  pose proof (PAx_K b a) as H_K1.
  pose proof (PAx_K (Impl a b) (Impl a (Impl b c))) as H_K2.
  pose proof (PP_compose _ _ _ H_K1 H_K2) as H2.
  pose proof (PP_compose _ _ _ H2 H1) as H3.
  exact (PP_perm _ _ _ H3).
Qed.

Lemma PP_contrapos : forall phi psi,
  ProvableProp (Impl (Impl phi psi) (Impl (Neg psi) (Neg phi))).
Proof.
  intros phi psi. unfold Neg.
  exact (PP_perm _ _ _ (PP_compose_internal phi psi Bot)).
Qed.

Lemma PP_neg_to_anything : forall phi psi,
  ProvableProp (Impl (Neg phi) (Impl phi psi)).
Proof.
  intros phi psi. unfold Neg.
  pose proof (PP_compose_internal phi Bot psi) as Hci.
  pose proof (PP_explosion psi) as Hex.
  exact (PMP _ _ Hci Hex).
Qed.

Lemma PP_X_negY_to_neg_impl : forall X Y,
  ProvableProp (Impl X (Impl (Neg Y) (Neg (Impl X Y)))).
Proof.
  intros X Y.
  pose proof (PP_perm (Impl X Y) X Y (PP_id (Impl X Y))) as f1.
  pose proof (PP_DN_intro Y) as f2.
  pose proof (PP_compose_internal (Impl X Y) Y (Neg (Neg Y))) as Hci.
  pose proof (PMP _ _ Hci f2) as f3.
  pose proof (PP_compose _ _ _ f1 f3) as f4.
  pose proof (PP_perm_internal (Impl X Y) (Neg Y) Bot) as f5.
  exact (PP_compose _ _ _ f4 f5).
Qed.

Inductive ProvablePropH : list Form -> Form -> Prop :=
  | PHhyp : forall G phi, In phi G -> ProvablePropH G phi
  | PHthm : forall G phi, ProvableProp phi -> ProvablePropH G phi
  | PHMP : forall G phi psi,
      ProvablePropH G (Impl phi psi) -> ProvablePropH G phi -> ProvablePropH G psi.

Lemma PHweaken : forall G G' phi,
  (forall psi, In psi G -> In psi G') ->
  ProvablePropH G phi -> ProvablePropH G' phi.
Proof.
  intros G G' phi Hsub H. revert G' Hsub.
  induction H; intros G' Hsub.
  - apply PHhyp. apply Hsub. exact H.
  - apply PHthm. exact H.
  - exact (PHMP _ _ _ (IHProvablePropH1 _ Hsub) (IHProvablePropH2 _ Hsub)).
Qed.

Theorem PHdeduction : forall G phi psi,
  ProvablePropH (phi :: G) psi -> ProvablePropH G (Impl phi psi).
Proof.
  intros G phi psi H.
  remember (phi :: G) as G' eqn:HG.
  revert G phi HG.
  induction H; intros G' phi' HG'.
  - subst G. simpl in H. destruct H as [Heq | Hin].
    + subst phi. apply PHthm. apply PP_id.
    + apply PHMP with phi.
      * apply PHthm. apply PAx_K.
      * apply PHhyp. exact Hin.
  - apply PHthm. exact (PMP _ _ (PAx_K phi phi') H).
  - subst G.
    pose proof (IHProvablePropH1 G' phi' eq_refl) as H1.
    pose proof (IHProvablePropH2 G' phi' eq_refl) as H2.
    apply PHMP with (Impl phi' phi).
    + apply PHMP with (Impl phi' (Impl phi psi)).
      * apply PHthm. exact (PAx_S phi' phi psi).
      * exact H1.
    + exact H2.
Qed.

Fixpoint box_free (phi : Form) : Prop :=
  match phi with
  | Var _ => True
  | Bot => True
  | Impl X Y => box_free X /\ box_free Y
  | Box _ _ => False
  end.

Definition classical_valid (phi : Form) : Prop :=
  forall val, eval val phi = true.

Fixpoint free_vars (phi : Form) : list nat :=
  match phi with
  | Var p => [p]
  | Bot => []
  | Impl X Y => free_vars X ++ free_vars Y
  | Box _ psi => free_vars psi
  end.

Definition gamma (val : nat -> bool) (phi : Form) : Form :=
  if eval val phi then phi else Neg phi.

Fixpoint gamma_list (val : nat -> bool) (vars : list nat) : list Form :=
  match vars with
  | [] => []
  | p :: rest => gamma val (Var p) :: gamma_list val rest
  end.

Lemma gamma_list_in : forall val vars p,
  In p vars -> In (gamma val (Var p)) (gamma_list val vars).
Proof.
  intros val vars p Hin. induction vars as [|q rest IH].
  - destruct Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst q. simpl. left. reflexivity.
    + simpl. right. apply IH. exact Hin'.
Qed.

Lemma in_app_or : forall A (l1 l2 : list A) (x : A),
  In x (l1 ++ l2) -> In x l1 \/ In x l2.
Proof.
  intros A l1 l2 x. induction l1 as [|y l1 IH]; simpl.
  - intro H. right. exact H.
  - intros [Heq | Hin].
    + left. left. exact Heq.
    + destruct (IH Hin) as [Hl | Hr].
      * left. right. exact Hl.
      * right. exact Hr.
Qed.

Lemma gamma_list_app : forall val l1 l2 phi,
  In phi (gamma_list val l1) -> In phi (gamma_list val (l1 ++ l2)).
Proof.
  intros val l1 l2 phi. induction l1 as [|q rest IH]; simpl.
  - intro H. destruct H.
  - intros [Heq | Hin].
    + left. exact Heq.
    + right. apply IH. exact Hin.
Qed.

Lemma gamma_list_app_r : forall val l1 l2 phi,
  In phi (gamma_list val l2) -> In phi (gamma_list val (l1 ++ l2)).
Proof.
  intros val l1 l2 phi. induction l1 as [|q rest IH]; simpl.
  - intro H. exact H.
  - intro H. right. apply IH. exact H.
Qed.

Theorem kalmar : forall val phi,
  box_free phi -> ProvablePropH (gamma_list val (free_vars phi)) (gamma val phi).
Proof.
  intros val phi Hbf. induction phi as [p | | X IHX Y IHY | n psi IHpsi].
  - simpl. unfold gamma. simpl. apply PHhyp.
    destruct (val p); simpl; left; reflexivity.
  - simpl. unfold gamma. simpl. apply PHthm.
    pose proof (PP_id Bot) as Hid.
    exact Hid.
  - simpl in Hbf. destruct Hbf as [HbfX HbfY].
    pose proof (IHX HbfX) as IHX'.
    pose proof (IHY HbfY) as IHY'.
    pose proof (PHweaken _ (gamma_list val (free_vars X ++ free_vars Y)) _
                  (gamma_list_app val (free_vars X) (free_vars Y)) IHX') as IHX''.
    pose proof (PHweaken _ (gamma_list val (free_vars X ++ free_vars Y)) _
                  (gamma_list_app_r val (free_vars X) (free_vars Y)) IHY') as IHY''.
    simpl. unfold gamma at 1.
    destruct (eval val (Impl X Y)) eqn:HevImp.
    + simpl in HevImp.
      destruct (eval val X) eqn:HevX; destruct (eval val Y) eqn:HevY;
        simpl in HevImp; try discriminate.
      * apply PHMP with Y.
        -- apply PHthm. exact (PAx_K Y X).
        -- unfold gamma in IHY''. rewrite HevY in IHY''. exact IHY''.
      * apply PHMP with Y.
        -- apply PHthm. exact (PAx_K Y X).
        -- unfold gamma in IHY''. rewrite HevY in IHY''. exact IHY''.
      * apply PHMP with (Neg X).
        -- apply PHthm. exact (PP_neg_to_anything X Y).
        -- unfold gamma in IHX''. rewrite HevX in IHX''. exact IHX''.
    + simpl in HevImp.
      destruct (eval val X) eqn:HevX; destruct (eval val Y) eqn:HevY;
        simpl in HevImp; try discriminate.
      apply PHMP with (Neg Y).
      * apply PHMP with X.
        -- apply PHthm. exact (PP_X_negY_to_neg_impl X Y).
        -- unfold gamma in IHX''. rewrite HevX in IHX''. exact IHX''.
      * unfold gamma in IHY''. rewrite HevY in IHY''. exact IHY''.
  - simpl in Hbf. contradiction.
Qed.

Lemma PP_consequentia_mirabilis : forall chi,
  ProvableProp (Impl (Impl (Neg chi) chi) chi).
Proof.
  intro chi.
  pose proof (PP_id (Impl chi Bot)) as Hid.
  pose proof (PAx_S (Impl chi Bot) chi Bot) as Hs.
  pose proof (PMP _ _ Hs Hid) as Hstep1.
  pose proof (PAx_DN chi) as HDN.
  exact (PP_compose _ _ _ Hstep1 HDN).
Qed.

Lemma PHelim_var : forall G p Q,
  ProvablePropH (Var p :: G) Q ->
  ProvablePropH (Neg (Var p) :: G) Q ->
  ProvablePropH G Q.
Proof.
  intros G p Q Hpos Hneg.
  pose proof (PHdeduction _ _ _ Hpos) as Hpd.
  pose proof (PHdeduction _ _ _ Hneg) as Hnd.
  pose proof (PHMP _ _ _ (PHthm _ _ (PP_contrapos (Var p) Q)) Hpd) as Hcontrap.
  pose proof (PHthm G _ (PP_compose_internal (Neg Q) (Neg (Var p)) Q)) as Hcc.
  pose proof (PHMP _ _ _ Hcc Hnd) as Hcc'.
  pose proof (PHMP _ _ _ Hcc' Hcontrap) as Hnegq.
  apply PHMP with (Impl (Neg Q) Q).
  - apply PHthm. apply PP_consequentia_mirabilis.
  - exact Hnegq.
Qed.

Lemma gamma_list_ext_on : forall val val' L,
  (forall q, In q L -> val q = val' q) ->
  gamma_list val L = gamma_list val' L.
Proof.
  intros val val' L Hext. induction L as [|p rest IH]; simpl.
  - reflexivity.
  - f_equal.
    + unfold gamma. simpl. rewrite (Hext p).
      * reflexivity.
      * left. reflexivity.
    + apply IH. intros q Hq. apply Hext. right. exact Hq.
Qed.

Lemma elim_nodup : forall vars G phi,
  NoDup vars ->
  (forall val, ProvablePropH (gamma_list val vars ++ G) phi) ->
  ProvablePropH G phi.
Proof.
  intro vars. induction vars as [|p rest IH]; intros G phi Hnd Hhyp.
  - simpl in Hhyp. apply (Hhyp (fun _ => false)).
  - inversion Hnd as [|p' rest' Hnp Hndr Heq]. subst p' rest'.
    apply (IH G phi Hndr).
    intro val.
    set (val_pos := fun q : nat => if Nat.eqb q p then true else val q).
    set (val_neg := fun q : nat => if Nat.eqb q p then false else val q).
    assert (Hag_pos : forall q, In q rest -> val_pos q = val q).
    { intros q Hin. unfold val_pos. destruct (Nat.eqb_spec q p).
      - subst q. contradiction.
      - reflexivity. }
    assert (Hag_neg : forall q, In q rest -> val_neg q = val q).
    { intros q Hin. unfold val_neg. destruct (Nat.eqb_spec q p).
      - subst q. contradiction.
      - reflexivity. }
    pose proof (Hhyp val_pos) as Hp.
    pose proof (Hhyp val_neg) as Hn.
    simpl in Hp. simpl in Hn.
    unfold gamma in Hp at 1. unfold gamma in Hn at 1.
    simpl in Hp. simpl in Hn.
    assert (Hpos_p : val_pos p = true).
    { unfold val_pos. rewrite Nat.eqb_refl. reflexivity. }
    assert (Hneg_p : val_neg p = false).
    { unfold val_neg. rewrite Nat.eqb_refl. reflexivity. }
    rewrite Hpos_p in Hp. rewrite Hneg_p in Hn.
    rewrite (gamma_list_ext_on val_pos val rest Hag_pos) in Hp.
    rewrite (gamma_list_ext_on val_neg val rest Hag_neg) in Hn.
    apply (PHelim_var _ p _ Hp Hn).
Qed.

Lemma PHnohyp_to_PP : forall phi, ProvablePropH [] phi -> ProvableProp phi.
Proof.
  intros phi H. remember (@nil Form) as G eqn:HG.
  induction H as [G' phi Hin | G' phi Hphi | G' phi psi H1 IH1 H2 IH2].
  - subst G'. simpl in Hin. destruct Hin.
  - exact Hphi.
  - exact (PMP _ _ (IH1 HG) (IH2 HG)).
Qed.

Lemma gamma_list_in_nodup : forall val L psi,
  In psi (gamma_list val L) -> In psi (gamma_list val (nodup Nat.eq_dec L)).
Proof.
  intros val L psi Hin. induction L as [|p rest IH]; simpl in *.
  - destruct Hin.
  - destruct (in_dec Nat.eq_dec p rest) as [Hin_p | Hnin_p].
    + destruct Hin as [Heq | Hin'].
      * subst psi. apply gamma_list_in. apply (nodup_In Nat.eq_dec). exact Hin_p.
      * apply IH. exact Hin'.
    + simpl. destruct Hin as [Heq | Hin'].
      * left. exact Heq.
      * right. apply IH. exact Hin'.
Qed.

Theorem prop_completeness : forall phi,
  box_free phi -> classical_valid phi -> ProvableProp phi.
Proof.
  intros phi Hbf Hval.
  pose (vars := nodup Nat.eq_dec (free_vars phi)).
  assert (Hnd : NoDup vars) by apply NoDup_nodup.
  apply PHnohyp_to_PP.
  apply (elim_nodup vars [] phi Hnd).
  intro val.
  rewrite app_nil_r.
  pose proof (kalmar val phi Hbf) as Hk.
  unfold classical_valid in Hval.
  unfold gamma in Hk. rewrite (Hval val) in Hk.
  apply (PHweaken (gamma_list val (free_vars phi)) (gamma_list val vars)).
  - intros psi Hin. apply gamma_list_in_nodup. exact Hin.
  - exact Hk.
Qed.

Fixpoint all_bool_lists (n : nat) : list (list bool) :=
  match n with
  | O => [[]]
  | S n' => let rest := all_bool_lists n' in
            map (cons true) rest ++ map (cons false) rest
  end.

Fixpoint mk_assignment (vars : list nat) (bs : list bool) (p : nat) : bool :=
  match vars, bs with
  | [], _ => false
  | v :: vs', b :: bs' => if Nat.eqb v p then b else mk_assignment vs' bs' p
  | _, [] => false
  end.

Definition decide_tautology (phi : Form) : bool :=
  let vars := nodup Nat.eq_dec (free_vars phi) in
  forallb (fun bs => eval (mk_assignment vars bs) phi)
          (all_bool_lists (length vars)).

Lemma all_bool_lists_length : forall n bs,
  In bs (all_bool_lists n) -> length bs = n.
Proof.
  intro n. induction n as [|n IH]; intros bs Hin.
  - simpl in Hin. destruct Hin as [Heq|[]]. subst bs. reflexivity.
  - simpl in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + apply in_map_iff in Hin. destruct Hin as [bs' [Heq Hin']].
      subst bs. simpl. f_equal. apply IH. exact Hin'.
    + apply in_map_iff in Hin. destruct Hin as [bs' [Heq Hin']].
      subst bs. simpl. f_equal. apply IH. exact Hin'.
Qed.

Lemma all_bool_lists_complete : forall (vars : list nat) (val : nat -> bool),
  exists bs, length bs = length vars /\
             In bs (all_bool_lists (length vars)) /\
             forall p, In p vars -> mk_assignment vars bs p = val p.
Proof.
  intros vars val. induction vars as [|v rest IH].
  - exists []. split; [reflexivity|]. split.
    + simpl. left. reflexivity.
    + intros p Hin. destruct Hin.
  - destruct IH as [bs [Hlen [Hin Hagree]]].
    exists (val v :: bs). split; [simpl; f_equal; exact Hlen|]. split.
    + simpl. apply in_or_app.
      destruct (val v) eqn:Heq.
      * left. apply in_map_iff. exists bs. split; [reflexivity|exact Hin].
      * right. apply in_map_iff. exists bs. split; [reflexivity|exact Hin].
    + intros p Hin'. simpl in Hin'.
      simpl. destruct (Nat.eqb_spec v p).
      * subst p. reflexivity.
      * destruct Hin' as [Heq|Hin''].
        -- subst v. exfalso. apply n. reflexivity.
        -- apply Hagree. exact Hin''.
Qed.

Lemma free_vars_in_nodup : forall phi p,
  In p (free_vars phi) -> In p (nodup Nat.eq_dec (free_vars phi)).
Proof.
  intros phi p Hin. apply nodup_In. exact Hin.
Qed.

Lemma forallb_forall : forall A (f : A -> bool) (l : list A),
  forallb f l = true <-> forall x, In x l -> f x = true.
Proof.
  intros A f l. induction l as [|y l IH]; simpl.
  - split; intros _; [intros x H; destruct H | reflexivity].
  - rewrite Bool.andb_true_iff. split.
    + intros [Hf Hr] x [Heq|Hin].
      * subst y. exact Hf.
      * apply IH; assumption.
    + intro Hall. split.
      * apply Hall. left. reflexivity.
      * apply IH. intros x Hin. apply Hall. right. exact Hin.
Qed.

Lemma eval_ext_on_free_vars : forall phi val1 val2,
  (forall p, In p (free_vars phi) -> val1 p = val2 p) ->
  eval val1 phi = eval val2 phi.
Proof.
  intro phi. induction phi as [k | | X IHX Y IHY | n psi IHpsi];
    intros val1 val2 Hext; simpl.
  - apply Hext. simpl. left. reflexivity.
  - reflexivity.
  - rewrite (IHX val1 val2), (IHY val1 val2).
    + reflexivity.
    + intros p Hin. apply Hext. simpl. apply in_or_app. right. exact Hin.
    + intros p Hin. apply Hext. simpl. apply in_or_app. left. exact Hin.
  - reflexivity.
Qed.

Theorem decide_tautology_correct : forall phi,
  decide_tautology phi = true -> classical_valid phi.
Proof.
  intros phi Hdec val.
  unfold decide_tautology in Hdec.
  set (vars := nodup Nat.eq_dec (free_vars phi)) in *.
  rewrite forallb_forall in Hdec.
  destruct (all_bool_lists_complete vars val) as [bs [Hlen [Hin Hagree]]].
  pose proof (Hdec bs Hin) as Hf.
  rewrite <- Hf.
  apply eval_ext_on_free_vars.
  intros p Hpin.
  assert (Hin'' : In p vars).
  { unfold vars. apply free_vars_in_nodup. exact Hpin. }
  symmetry. apply Hagree. exact Hin''.
Qed.

Theorem decide_tautology_complete : forall phi,
  classical_valid phi -> decide_tautology phi = true.
Proof.
  intros phi Hval.
  unfold decide_tautology.
  apply forallb_forall.
  intros bs _.
  apply Hval.
Qed.

Theorem prop_decide_correct : forall phi,
  box_free phi -> decide_tautology phi = true -> ProvableProp phi.
Proof.
  intros phi Hbf Hdec.
  apply prop_completeness; [exact Hbf|].
  apply decide_tautology_correct. exact Hdec.
Qed.

Ltac prop_decide :=
  apply prop_decide_correct;
  [ cbn; repeat split; exact I
  | cbv; reflexivity ].

(** ** Uniform-witness theorem for tiling_consistency.

    [tiling_consistency] in Coq is already a single dependent term of
    type [forall n phi, |- Box (S n) (Impl (Box n phi) (Neg (Box n
    (Neg phi))))], i.e., a uniform witness whose body does not
    case-split on [n] or [phi].  We package this fact: the schematic
    instances [tiling_consistency n phi] are obtained by parameter
    substitution into a single derivation, not a family of unrelated
    proofs. *)

Definition tiling_witness :
  forall n phi, |- Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi))))
  := tiling_consistency.

Theorem tiling_uniform_witness :
  forall n phi, tiling_witness n phi = tiling_consistency n phi.
Proof. intros n phi. reflexivity. Qed.

Theorem tiling_witness_pointed :
  exists f : (forall n phi,
    |- Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi))))),
    forall n phi, f n phi = tiling_consistency n phi.
Proof.
  exists tiling_consistency. intros. reflexivity.
Qed.

(** ** Independence of Ax_Mon.

    [Provable_no_Mon] is GLP* with [Ax_Mon] removed.  A frame
    satisfying transitivity, converse-well-foundedness, and NextCon-
    successor (but not the monotone-inclusion condition) gives a
    counter-model.  Specifically [|- Impl (Box 0 (Var 0)) (Box 1
    (Var 0))], a direct instance of [Ax_Mon], is not derivable in
    [Provable_no_Mon].  Parallels [consistency_chain_needs_NC]. *)

Inductive Provable_no_Mon : Form -> Prop :=
  | NM_Ax_K : forall phi psi,
      Provable_no_Mon (Impl phi (Impl psi phi))
  | NM_Ax_S : forall phi psi chi,
      Provable_no_Mon (Impl (Impl phi (Impl psi chi))
                            (Impl (Impl phi psi) (Impl phi chi)))
  | NM_Ax_DN : forall phi,
      Provable_no_Mon (Impl (Neg (Neg phi)) phi)
  | NM_Ax_BoxK : forall n phi psi,
      Provable_no_Mon (Impl (Box n (Impl phi psi))
                            (Impl (Box n phi) (Box n psi)))
  | NM_Ax_Loeb : forall n phi,
      Provable_no_Mon (Impl (Box n (Impl (Box n phi) phi)) (Box n phi))
  | NM_Ax_Box4 : forall n phi,
      Provable_no_Mon (Impl (Box n phi) (Box n (Box n phi)))
  | NM_Ax_NextCon : forall n,
      Provable_no_Mon (Box (S n) (Neg (Box n Bot)))
  | NM_MP : forall phi psi,
      Provable_no_Mon (Impl phi psi) -> Provable_no_Mon phi -> Provable_no_Mon psi
  | NM_Nec : forall n phi,
      Provable_no_Mon phi -> Provable_no_Mon (Box n phi).

Notation "|-no_mon f" := (Provable_no_Mon f) (at level 75, no associativity).

Record Frame_no_Mon : Type := mkFrame_no_Mon {
  fW_nm : Type;
  fR_nm : nat -> fW_nm -> fW_nm -> Prop;
  fR_nm_trans : forall n w v u, fR_nm n w v -> fR_nm n v u -> fR_nm n w u;
  fR_nm_wf : forall n, well_founded (fun u v => fR_nm n v u);
  fR_nm_nextcon : forall n w v, fR_nm (S n) w v -> exists u, fR_nm n v u
}.

Fixpoint forces_nm (F : Frame_no_Mon) (V : fW_nm F -> nat -> bool)
                   (w : fW_nm F) (phi : Form) : Prop :=
  match phi with
  | Var p => V w p = true
  | Bot => False
  | Impl X Y => forces_nm F V w X -> forces_nm F V w Y
  | Box n psi => forall v, fR_nm F n w v -> forces_nm F V v psi
  end.

Theorem soundness_no_Mon : forall phi, |-no_mon phi ->
  forall F V w, forces_nm F V w phi.
Proof.
  intros phi H. induction H.
  - intros F V w. simpl. intros Hphi _. exact Hphi.
  - intros F V w. simpl. intros Hf Hg Hphi.
    apply Hf; [exact Hphi | apply Hg; exact Hphi].
  - intros F V w. simpl. intro Hnnp. apply NNPP. exact Hnnp.
  - intros F V w. simpl. intros Himp Hphi v Hwv.
    apply (Himp v Hwv). apply (Hphi v Hwv).
  - intros F V w. simpl. intros Hbox v Hwv.
    pose proof (fR_nm_wf F n) as Hwf.
    set (P := fun u => fR_nm F n w u -> forces_nm F V u phi).
    cut (P v); [intro Hpv; exact (Hpv Hwv) |].
    apply (well_founded_ind Hwf P).
    intros u IH. unfold P. intro Hwu.
    apply (Hbox u Hwu).
    intros u' Huu'.
    apply (IH u' Huu' (fR_nm_trans F n w u u' Hwu Huu')).
  - intros F V w. simpl. intros Hphi v Hwv u Hvu.
    apply Hphi. apply (fR_nm_trans F n w v u Hwv Hvu).
  - intros F V w. simpl. intros v Hwv Hbox.
    destruct (fR_nm_nextcon F n w v Hwv) as [u Hvu].
    exact (Hbox u Hvu).
  - intros F V w. apply (IHProvable_no_Mon1 F V w).
    apply (IHProvable_no_Mon2 F V w).
  - intros F V w. simpl. intros v _.
    apply (IHProvable_no_Mon F V v).
Qed.

Definition F_no_Mon : Frame_no_Mon :=
  mkFrame_no_Mon nat R_break_mon
    R_break_mon_trans R_break_mon_wf R_break_mon_nextcon.

Theorem mon_axiom_needs_Mon :
  ~ (|-no_mon Impl (Box 0 (Var 0)) (Box 1 (Var 0))).
Proof.
  intro H.
  pose proof (soundness_no_Mon _ H F_no_Mon (fun w _ => negb (Nat.eqb w 1)) 0)
    as Hf.
  simpl in Hf.
  assert (HBox0 : forall v : nat, R_break_mon 0 0 v -> negb (Nat.eqb v 1) = true).
  { intros v Hv. simpl in Hv. destruct Hv as [Hv _]. discriminate. }
  pose proof (Hf HBox0) as HBox1.
  assert (HR : R_break_mon 1 0 1) by (simpl; split; reflexivity).
  pose proof (HBox1 1 HR) as Hcontra.
  simpl in Hcontra. discriminate.
Qed.

(** ** Independence of Ax_Box4 (semantic and syntactic).

    Two complementary results.

    Semantically: in any transitive frame, [Box n (Box n phi)] is
    equivalent to "for all R-paths of length 2, [phi] holds at the
    end".  This is just a restatement of forcing under transitivity.

    Syntactically: axiom 4 is a derived theorem of [Provable_no_B4]
    (the calculus with [Ax_Box4] removed), so [Ax_Box4] is in fact
    redundant.  See [nb4_axiom4] for the derivation, which uses
    Löb's axiom applied at the formula [A ∧ Box n A] together with
    K and propositional reasoning. *)

Theorem box4_sound_in_transitive : forall (F : Frame) V w n phi,
  forces F V w (Box n (Box n phi)) <->
  (forall v u, fR F n w v -> fR F n v u -> forces F V u phi).
Proof.
  intros F V w n phi. split; intros H.
  - intros v u Hwv Hvu. apply (H v Hwv u Hvu).
  - intros v Hwv u Hvu. exact (H v u Hwv Hvu).
Qed.

(** ** Sambin's fixed-point theorem (build-up).

    We work toward Sambin's theorem: every formula [phi(p)] in which
    every occurrence of [Var p] is in the scope of some [Box] admits
    a fixed point [psi] with [|- Iff psi (Subst p psi phi)].
    Boolos's derivation of axiom 4 from K + Löb (Logic of Provability,
    Theorem 11) routes through this theorem.  We build up the
    machinery piece by piece. *)

(** *** [modalized p phi]: every [Var p] in [phi] is under a [Box]. *)

Fixpoint modalized (p : nat) (phi : Form) : Prop :=
  match phi with
  | Var k => k <> p
  | Bot => True
  | Impl X Y => modalized p X /\ modalized p Y
  | Box _ _ => True
  end.

(** *** Modal depth: maximum nesting of [Box]. *)

Fixpoint modal_depth (phi : Form) : nat :=
  match phi with
  | Var _ => 0
  | Bot => 0
  | Impl X Y => Nat.max (modal_depth X) (modal_depth Y)
  | Box _ psi => S (modal_depth psi)
  end.

Lemma modal_depth_neg : forall phi,
  modal_depth (Neg phi) = modal_depth phi.
Proof.
  intro phi. unfold Neg. simpl. rewrite Nat.max_0_r. reflexivity.
Qed.

(** *** Substitution composition.

    [subst_form sigma2 (subst_form sigma1 phi) =
     subst_form (sigma1 ; sigma2) phi]
    where [(sigma1 ; sigma2) k = subst_form sigma2 (sigma1 k)]. *)

Lemma subst_form_compose : forall sigma1 sigma2 phi,
  subst_form sigma2 (subst_form sigma1 phi) =
  subst_form (fun k => subst_form sigma2 (sigma1 k)) phi.
Proof.
  intros sigma1 sigma2 phi. induction phi as [k | | X IHX Y IHY | n psi IHpsi].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IHX, IHY. reflexivity.
  - simpl. rewrite IHpsi. reflexivity.
Qed.

(** ** Box4 as a derived theorem of K + Löb (without Ax_Box4).

    The standard derivation (folklore, attributed to substitution
    [A ∧ □A] for the variable in Löb's axiom): apply Löb's axiom at
    the formula [A ∧ □A], derive the antecedent [□(□(A ∧ □A) → A ∧ □A)]
    from [□A] using K + propositional reasoning, and conclude
    [□(A ∧ □A)], from which K + and-elim yields [□□A].  No fixed-point
    machinery beyond Löb's axiom itself is needed.

    [Provable_no_B4] is GLP* with [Ax_Box4] removed.  Showing axiom 4
    is derivable in [Provable_no_B4] establishes it as redundant. *)

Inductive Provable_no_B4 : Form -> Prop :=
  | NB4_Ax_K : forall phi psi,
      Provable_no_B4 (Impl phi (Impl psi phi))
  | NB4_Ax_S : forall phi psi chi,
      Provable_no_B4 (Impl (Impl phi (Impl psi chi))
                           (Impl (Impl phi psi) (Impl phi chi)))
  | NB4_Ax_DN : forall phi,
      Provable_no_B4 (Impl (Neg (Neg phi)) phi)
  | NB4_Ax_BoxK : forall n phi psi,
      Provable_no_B4 (Impl (Box n (Impl phi psi))
                           (Impl (Box n phi) (Box n psi)))
  | NB4_Ax_Loeb : forall n phi,
      Provable_no_B4 (Impl (Box n (Impl (Box n phi) phi)) (Box n phi))
  | NB4_Ax_Mon : forall n phi,
      Provable_no_B4 (Impl (Box n phi) (Box (S n) phi))
  | NB4_Ax_NextCon : forall n,
      Provable_no_B4 (Box (S n) (Neg (Box n Bot)))
  | NB4_MP : forall phi psi,
      Provable_no_B4 (Impl phi psi) -> Provable_no_B4 phi -> Provable_no_B4 psi
  | NB4_Nec : forall n phi,
      Provable_no_B4 phi -> Provable_no_B4 (Box n phi).

Notation "|-no_b4 f" := (Provable_no_B4 f) (at level 75, no associativity).

(** Basic propositional helpers in [Provable_no_B4]. *)

Lemma nb4_prov_id : forall phi, |-no_b4 Impl phi phi.
Proof.
  intro phi.
  exact (NB4_MP _ _
          (NB4_MP _ _ (NB4_Ax_S phi (Impl phi phi) phi)
                       (NB4_Ax_K phi (Impl phi phi)))
          (NB4_Ax_K phi phi)).
Qed.

Lemma nb4_prov_weaken : forall phi psi, |-no_b4 phi -> |-no_b4 Impl psi phi.
Proof. intros phi psi Hphi. exact (NB4_MP _ _ (NB4_Ax_K phi psi) Hphi). Qed.

Lemma nb4_prov_compose : forall phi psi chi,
  |-no_b4 Impl phi psi -> |-no_b4 Impl psi chi -> |-no_b4 Impl phi chi.
Proof.
  intros phi psi chi Hpq Hqr.
  pose proof (NB4_Ax_S phi psi chi) as Hs.
  pose proof (nb4_prov_weaken _ phi Hqr) as Hpqr.
  exact (NB4_MP _ _ (NB4_MP _ _ Hs Hpqr) Hpq).
Qed.

Lemma nb4_prov_box_imp : forall n phi psi,
  |-no_b4 Impl phi psi -> |-no_b4 Impl (Box n phi) (Box n psi).
Proof.
  intros n phi psi Himp.
  pose proof (NB4_Nec n _ Himp) as Hnec.
  pose proof (NB4_Ax_BoxK n phi psi) as HBK.
  exact (NB4_MP _ _ HBK Hnec).
Qed.

Lemma nb4_prov_perm : forall phi psi chi,
  |-no_b4 Impl phi (Impl psi chi) -> |-no_b4 Impl psi (Impl phi chi).
Proof.
  intros phi psi chi H.
  pose proof (NB4_Ax_S phi psi chi) as Hs.
  pose proof (NB4_MP _ _ Hs H) as H1.
  pose proof (NB4_Ax_K psi phi) as Hk.
  exact (nb4_prov_compose _ _ _ Hk H1).
Qed.

Lemma nb4_prov_DN_intro : forall phi, |-no_b4 Impl phi (Neg (Neg phi)).
Proof.
  intro phi. unfold Neg.
  pose proof (nb4_prov_id (Impl phi Bot)) as Hid.
  exact (nb4_prov_perm _ _ _ Hid).
Qed.

Lemma nb4_prov_explosion : forall phi, |-no_b4 Impl Bot phi.
Proof.
  intro phi.
  pose proof (NB4_Ax_K Bot (Neg phi)) as Hk.
  pose proof (NB4_Ax_DN phi) as HDN.
  exact (nb4_prov_compose _ _ _ Hk HDN).
Qed.

Lemma nb4_prov_compose_internal : forall phi psi chi,
  |-no_b4 Impl (Impl psi chi) (Impl (Impl phi psi) (Impl phi chi)).
Proof.
  intros phi psi chi.
  pose proof (NB4_Ax_K (Impl psi chi) phi) as Hk.
  pose proof (NB4_Ax_S phi psi chi) as Hs.
  exact (nb4_prov_compose _ _ _ Hk Hs).
Qed.

Lemma nb4_prov_perm_internal : forall a b c,
  |-no_b4 Impl (Impl a (Impl b c)) (Impl b (Impl a c)).
Proof.
  intros a b c.
  pose proof (NB4_Ax_S a b c) as H_S.
  pose proof (NB4_Ax_S (Impl a (Impl b c)) (Impl a b) (Impl a c)) as H_S2.
  pose proof (NB4_MP _ _ H_S2 H_S) as H1.
  pose proof (NB4_Ax_K b a) as H_K1.
  pose proof (NB4_Ax_K (Impl a b) (Impl a (Impl b c))) as H_K2.
  pose proof (nb4_prov_compose _ _ _ H_K1 H_K2) as H2.
  pose proof (nb4_prov_compose _ _ _ H2 H1) as H3.
  exact (nb4_prov_perm _ _ _ H3).
Qed.

Lemma nb4_prov_and_intro : forall phi psi,
  |-no_b4 Impl phi (Impl psi (And phi psi)).
Proof.
  intros phi psi.
  unfold And, Neg.
  pose proof (nb4_prov_id (Impl phi (Impl psi Bot))) as Hid.
  pose proof (nb4_prov_perm _ _ _ Hid) as Hperm.
  pose proof (nb4_prov_perm_internal (Impl phi (Impl psi Bot)) psi Bot) as Hpi.
  exact (nb4_prov_compose _ _ _ Hperm Hpi).
Qed.

Lemma nb4_prov_and_intro_meta : forall phi psi,
  |-no_b4 phi -> |-no_b4 psi -> |-no_b4 And phi psi.
Proof.
  intros phi psi Hphi Hpsi.
  exact (NB4_MP _ _ (NB4_MP _ _ (nb4_prov_and_intro phi psi) Hphi) Hpsi).
Qed.

Lemma nb4_prov_neg_imp_ng : forall phi psi,
  |-no_b4 Impl (Neg phi) (Impl phi (Neg psi)).
Proof.
  intros phi psi. unfold Neg.
  pose proof (nb4_prov_compose_internal phi Bot (Impl psi Bot)) as Hci.
  pose proof (nb4_prov_explosion (Impl psi Bot)) as Hex.
  exact (NB4_MP _ _ Hci Hex).
Qed.

Lemma nb4_prov_and_elim_l : forall phi psi,
  |-no_b4 Impl (And phi psi) phi.
Proof.
  intros phi psi. unfold And, Neg.
  pose proof (nb4_prov_neg_imp_ng phi psi) as H1.
  pose proof (nb4_prov_compose_internal
                (Impl phi Bot)
                (Impl phi (Impl psi Bot))
                Bot) as H2.
  pose proof (nb4_prov_perm _ _ _ H2) as H2_perm.
  pose proof (NB4_MP _ _ H2_perm H1) as Hstep1.
  pose proof (NB4_Ax_DN phi) as HDN.
  exact (nb4_prov_compose _ _ _ Hstep1 HDN).
Qed.

Lemma nb4_prov_and_elim_r : forall phi psi,
  |-no_b4 Impl (And phi psi) psi.
Proof.
  intros phi psi. unfold And, Neg.
  pose proof (NB4_Ax_K (Impl psi Bot) phi) as H1.
  pose proof (nb4_prov_compose_internal
                (Impl psi Bot)
                (Impl phi (Impl psi Bot))
                Bot) as H2.
  pose proof (nb4_prov_perm _ _ _ H2) as H2_perm.
  pose proof (NB4_MP _ _ H2_perm H1) as Hstep1.
  pose proof (NB4_Ax_DN psi) as HDN.
  exact (nb4_prov_compose _ _ _ Hstep1 HDN).
Qed.

Lemma nb4_prov_and_elim_l_meta : forall phi psi,
  |-no_b4 And phi psi -> |-no_b4 phi.
Proof.
  intros phi psi Hand.
  exact (NB4_MP _ _ (nb4_prov_and_elim_l phi psi) Hand).
Qed.

Lemma nb4_prov_and_elim_r_meta : forall phi psi,
  |-no_b4 And phi psi -> |-no_b4 psi.
Proof.
  intros phi psi Hand.
  exact (NB4_MP _ _ (nb4_prov_and_elim_r phi psi) Hand).
Qed.

(** Uncurry [And] into chained implication. *)

Lemma nb4_prov_uncurry : forall A B C,
  |-no_b4 Impl (And A B) C -> |-no_b4 Impl A (Impl B C).
Proof.
  intros A B C Hf.
  pose proof (nb4_prov_and_intro A B) as Handi.
  pose proof (nb4_prov_compose_internal B (And A B) C) as Hci.
  pose proof (NB4_MP _ _ Hci Hf) as Hstep1.
  exact (nb4_prov_compose _ _ _ Handi Hstep1).
Qed.

(** Axiom 4 as a derived theorem of Provable_no_B4 (i.e., GLP* without
    primitive [Ax_Box4]).  The standard substitution argument: apply
    Löb's axiom at the formula [A ∧ Box n A], derive the Löb-axiom
    antecedent from [Box n A] using K and propositional reasoning, and
    conclude [Box n (A ∧ Box n A)]; from this, K + and-elim yields
    [Box n (Box n A)]. *)

Theorem nb4_axiom4 : forall n A,
  |-no_b4 Impl (Box n A) (Box n (Box n A)).
Proof.
  intros n A.
  set (B := Box n A).
  set (X := And A (Box n (And A B))).
  pose proof (nb4_prov_and_elim_l A B) as H1.
  pose proof (nb4_prov_box_imp n _ _ H1) as H2.
  pose proof (nb4_prov_and_elim_l A (Box n (And A B))) as H3.
  pose proof (nb4_prov_and_elim_r A (Box n (And A B))) as H4pre.
  pose proof (nb4_prov_compose _ _ _ H4pre H2) as H4.
  pose proof (nb4_prov_and_intro A B) as Handi.
  pose proof (nb4_prov_compose _ _ _ H3 Handi) as Hcomp1.
  pose proof (NB4_Ax_S X B (And A B)) as Hs.
  pose proof (NB4_MP _ _ Hs Hcomp1) as Hstep1.
  pose proof (NB4_MP _ _ Hstep1 H4) as H5.
  pose proof (nb4_prov_uncurry _ _ _ H5) as H6.
  pose proof (nb4_prov_box_imp n _ _ H6) as H7.
  pose proof (NB4_Ax_Loeb n (And A B)) as H8.
  pose proof (nb4_prov_compose _ _ _ H7 H8) as H9.
  pose proof (nb4_prov_and_elim_r A B) as H10pre.
  pose proof (nb4_prov_box_imp n _ _ H10pre) as H11.
  exact (nb4_prov_compose _ _ _ H9 H11).
Qed.

Theorem provable_to_no_b4 : forall phi, |- phi -> |-no_b4 phi.
Proof.
  intros phi H. induction H.
  - apply NB4_Ax_K.
  - apply NB4_Ax_S.
  - apply NB4_Ax_DN.
  - apply NB4_Ax_BoxK.
  - apply NB4_Ax_Loeb.
  - apply nb4_axiom4.
  - apply NB4_Ax_Mon.
  - apply NB4_Ax_NextCon.
  - exact (NB4_MP _ _ IHProvable1 IHProvable2).
  - exact (NB4_Nec _ _ IHProvable).
Qed.

Theorem no_b4_to_provable : forall phi, |-no_b4 phi -> |- phi.
Proof.
  intros phi H. induction H as [| | | | | | | phi psi _ IH1 _ IH2 | n phi _ IH].
  - apply Ax_K.
  - apply Ax_S.
  - apply Ax_DN.
  - apply Ax_BoxK.
  - apply Ax_Loeb.
  - apply Ax_Mon.
  - apply Ax_NextCon.
  - exact (MP _ _ IH1 IH2).
  - exact (Nec _ _ IH).
Qed.

Theorem provable_iff_no_b4 : forall phi, |- phi <-> |-no_b4 phi.
Proof.
  intro phi. split; [apply provable_to_no_b4 | apply no_b4_to_provable].
Qed.

Definition F_no_NC_m_R (m : nat) (k : nat) (w v : bool) : Prop :=
  k <= m /\ w = true /\ v = false.

Lemma F_no_NC_m_R_trans : forall m k w v u,
  F_no_NC_m_R m k w v -> F_no_NC_m_R m k v u -> F_no_NC_m_R m k w u.
Proof.
  intros m k w v u [_ [_ Hvf]] [_ [Hvt _]]. subst v. discriminate.
Qed.

Lemma F_no_NC_m_R_wf : forall m k,
  well_founded (fun u v => F_no_NC_m_R m k v u).
Proof.
  intros m k x.
  apply Acc_intro. intros y [_ [_ Hyf]]. subst y.
  apply Acc_intro. intros z [_ [Hzt _]]. discriminate.
Qed.

Lemma F_no_NC_m_R_mon : forall m k w v,
  F_no_NC_m_R m (S k) w v -> F_no_NC_m_R m k w v.
Proof.
  intros m k w v [Hle [Hw Hv]]. split; [lia | split; assumption].
Qed.

Definition F_no_NC_m (m : nat) : Frame_no_NC :=
  mkFrame_no_NC bool (F_no_NC_m_R m)
    (F_no_NC_m_R_trans m) (F_no_NC_m_R_wf m) (F_no_NC_m_R_mon m).

Lemma provable_higher_NC : forall n,
  1 <= n -> |- Box n (Neg (Box 0 Bot)).
Proof.
  intros n Hn.
  destruct n as [|n']; [lia|].
  pose proof (Ax_NextCon 0) as H1.
  pose proof (prov_box_mon_le 1 (S n') (Neg (Box 0 Bot)) Hn) as Hmon.
  exact (MP _ _ Hmon H1).
Qed.

Theorem separation_NC_at : forall n, 1 <= n ->
  (|- Box n (Neg (Box 0 Bot))) /\
  ~ (|-no_nc Box n (Neg (Box 0 Bot))).
Proof.
  intros n Hn.
  split.
  - apply provable_higher_NC. exact Hn.
  - intro Habs.
    pose proof (soundness_no_NC _ Habs (F_no_NC_m n) (fun _ _ => true) true) as Hf.
    simpl in Hf.
    assert (Hwit : F_no_NC_m_R n n true false).
    { unfold F_no_NC_m_R. split; [lia | split; reflexivity]. }
    pose proof (Hf false Hwit) as Hnegbox.
    apply Hnegbox.
    intros u Hu.
    unfold F_no_NC_m_R in Hu.
    destruct Hu as [_ [Hbad _]]. discriminate.
Qed.

Definition F_no_Mon_n_R (k : nat) (w v : nat) : Prop :=
  w = k + 1 /\ v = k.

Lemma F_no_Mon_n_R_trans : forall k w v u,
  F_no_Mon_n_R k w v -> F_no_Mon_n_R k v u -> F_no_Mon_n_R k w u.
Proof.
  intros k w v u [_ Hv] [Hv' _]. subst v. lia.
Qed.

Lemma F_no_Mon_n_R_wf : forall k,
  well_founded (fun u v => F_no_Mon_n_R k v u).
Proof.
  intros k x.
  apply Acc_intro. intros y [_ Hy]. subst y.
  apply Acc_intro. intros z [Hz _]. lia.
Qed.

Lemma F_no_Mon_n_R_nextcon : forall k w v,
  F_no_Mon_n_R (S k) w v -> exists u, F_no_Mon_n_R k v u.
Proof.
  intros k w v [Hw Hv]. exists k.
  unfold F_no_Mon_n_R. split; lia.
Qed.

Definition F_no_Mon_n : Frame_no_Mon :=
  mkFrame_no_Mon nat F_no_Mon_n_R
    F_no_Mon_n_R_trans F_no_Mon_n_R_wf F_no_Mon_n_R_nextcon.

Theorem separation_Mon_at : forall n,
  (|- Impl (Box n (Var 0)) (Box (S n) (Var 0))) /\
  ~ (|-no_mon Impl (Box n (Var 0)) (Box (S n) (Var 0))).
Proof.
  intro n.
  split.
  - exact (Ax_Mon n (Var 0)).
  - intro Habs.
    pose proof (soundness_no_Mon _ Habs F_no_Mon_n
      (fun w _ => negb (Nat.eqb w (S n))) (n + 2)) as Hf.
    simpl in Hf.
    assert (HBoxN : forall v, F_no_Mon_n_R n (n+2) v -> negb (Nat.eqb v (S n)) = true).
    { intros v [Hw _]. exfalso. lia. }
    pose proof (Hf HBoxN) as HBoxSn.
    assert (HR : F_no_Mon_n_R (S n) (n+2) (S n)).
    { unfold F_no_Mon_n_R. split; lia. }
    pose proof (HBoxSn (S n) HR) as Hcontra.
    rewrite Nat.eqb_refl in Hcontra. simpl in Hcontra. discriminate.
Qed.

Theorem yh_bypass_robust_no_b4 : forall n,
  ((forall phi, |-no_b4 Impl (Box n phi) phi) -> |-no_b4 Bot) /\
  (forall phi, |-no_b4 Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi))))) /\
  (forall k, n < k -> |-no_b4 Box k (Neg (Box n Bot))).
Proof.
  intro n. split; [|split].
  - intros Hsch.
    apply provable_to_no_b4.
    apply (loebian_obstacle n).
    intro phi.
    apply no_b4_to_provable. apply Hsch.
  - intro phi.
    apply provable_to_no_b4. exact (tiling_consistency n phi).
  - intros k Hlt.
    apply provable_to_no_b4. exact (consistency_chain n k Hlt).
Qed.

Theorem yh_bypass_robust_summary :
  forall n, (forall phi, |- Box n phi <-> |-no_b4 Box n phi).
Proof.
  intros n phi. exact (provable_iff_no_b4 (Box n phi)).
Qed.

Theorem tiling_strongest : forall n,
  ~ (forall phi, |- Box (S n) (Box n phi)).
Proof.
  intros n Hsch.
  apply (meta_no_contradiction (S n) (Box n Bot)).
  split.
  - exact (Hsch Bot).
  - exact (Ax_NextCon n).
Qed.

Theorem tiling_strengthening_collapses : forall n psi,
  (forall phi, |- Impl (psi n phi) (Box n phi)) ->
  (forall phi, |- Box (S n) (psi n phi)) ->
  |- Bot.
Proof.
  intros n psi Himp Hbox.
  exfalso.
  apply (meta_consistency_every_level (S n)).
  pose proof (prov_box_imp (S n) _ _ (Himp Bot)) as Hlift.
  pose proof (MP _ _ Hlift (Hbox Bot)) as HboxBoxNBot.
  pose proof (Ax_NextCon n) as Hnc.
  pose proof (prov_box_n_contradiction (S n) (Box n Bot)) as Hcon.
  pose proof (MP _ _ Hcon HboxBoxNBot) as Hstep.
  exact (MP _ _ Hstep Hnc).
Qed.

Inductive Provable_plus (Sax : Form -> Prop) : Form -> Prop :=
  | PP_lift : forall phi, |- phi -> Provable_plus Sax phi
  | PP_extra : forall phi, Sax phi -> Provable_plus Sax phi
  | PP_MP_pp : forall phi psi,
      Provable_plus Sax (Impl phi psi) ->
      Provable_plus Sax phi ->
      Provable_plus Sax psi
  | PP_Nec_pp : forall n phi,
      Provable_plus Sax phi -> Provable_plus Sax (Box n phi).

Theorem no_go_reflection : forall Sax n,
  (forall phi, Provable_plus Sax (Impl (Box n phi) phi)) ->
  Provable_plus Sax Bot.
Proof.
  intros Sax n Hsch.
  pose proof (Hsch Bot) as Hbot.
  pose proof (PP_lift Sax _ (Ax_Loeb n Bot)) as HLoeb.
  pose proof (PP_Nec_pp Sax n _ Hbot) as HnecBot.
  pose proof (PP_MP_pp Sax _ _ HLoeb HnecBot) as HboxBot.
  exact (PP_MP_pp Sax _ _ Hbot HboxBot).
Qed.

Theorem minimal_viable_bypass_mon : forall n,
  ~ (forall phi, |-no_mon Impl (Box n phi) (Box (S n) phi)).
Proof.
  intros n Hsch.
  pose proof (separation_Mon_at n) as [_ Hsep].
  apply Hsep. apply (Hsch (Var 0)).
Qed.

Theorem minimal_viable_bypass_nc : forall n, 1 <= n ->
  ~ (|-no_nc Box n (Neg (Box 0 Bot))).
Proof.
  intros n Hn.
  pose proof (separation_NC_at n Hn) as [_ Hsep]. exact Hsep.
Qed.

(** ** Independence of Ax_Loeb.

    [Provable_no_Loeb] is GLP* with [Ax_Loeb] removed.  Loeb is sound
    in any converse-well-founded frame; in [R_break_wf] (the strict
    [<] relation on nat, which is transitive, monotone, and NextCon-
    successor closed but not converse-WF) Löb fails.  A specific
    instance of Löb at [Bot] is unprovable in [Provable_no_Loeb]. *)

Inductive Provable_no_Loeb : Form -> Prop :=
  | NL_Ax_K : forall phi psi,
      Provable_no_Loeb (Impl phi (Impl psi phi))
  | NL_Ax_S : forall phi psi chi,
      Provable_no_Loeb (Impl (Impl phi (Impl psi chi))
                             (Impl (Impl phi psi) (Impl phi chi)))
  | NL_Ax_DN : forall phi,
      Provable_no_Loeb (Impl (Neg (Neg phi)) phi)
  | NL_Ax_BoxK : forall n phi psi,
      Provable_no_Loeb (Impl (Box n (Impl phi psi))
                             (Impl (Box n phi) (Box n psi)))
  | NL_Ax_Box4 : forall n phi,
      Provable_no_Loeb (Impl (Box n phi) (Box n (Box n phi)))
  | NL_Ax_Mon : forall n phi,
      Provable_no_Loeb (Impl (Box n phi) (Box (S n) phi))
  | NL_Ax_NextCon : forall n,
      Provable_no_Loeb (Box (S n) (Neg (Box n Bot)))
  | NL_MP : forall phi psi,
      Provable_no_Loeb (Impl phi psi) -> Provable_no_Loeb phi -> Provable_no_Loeb psi
  | NL_Nec : forall n phi,
      Provable_no_Loeb phi -> Provable_no_Loeb (Box n phi).

Notation "|-no_loeb f" := (Provable_no_Loeb f) (at level 75, no associativity).

Record Frame_no_Loeb : Type := mkFrame_no_Loeb {
  fW_nl : Type;
  fR_nl : nat -> fW_nl -> fW_nl -> Prop;
  fR_nl_trans : forall n w v u, fR_nl n w v -> fR_nl n v u -> fR_nl n w u;
  fR_nl_mon : forall n w v, fR_nl (S n) w v -> fR_nl n w v;
  fR_nl_nextcon : forall n w v, fR_nl (S n) w v -> exists u, fR_nl n v u
}.

Fixpoint forces_nl (F : Frame_no_Loeb) (V : fW_nl F -> nat -> bool)
                   (w : fW_nl F) (phi : Form) : Prop :=
  match phi with
  | Var p => V w p = true
  | Bot => False
  | Impl X Y => forces_nl F V w X -> forces_nl F V w Y
  | Box n psi => forall v, fR_nl F n w v -> forces_nl F V v psi
  end.

Theorem soundness_no_Loeb : forall phi, |-no_loeb phi ->
  forall F V w, forces_nl F V w phi.
Proof.
  intros phi H. induction H.
  - intros F V w. simpl. intros Hphi _. exact Hphi.
  - intros F V w. simpl. intros Hf Hg Hphi.
    apply Hf; [exact Hphi | apply Hg; exact Hphi].
  - intros F V w. simpl. intro Hnnp. apply NNPP. exact Hnnp.
  - intros F V w. simpl. intros Himp Hphi v Hwv.
    apply (Himp v Hwv). apply (Hphi v Hwv).
  - intros F V w. simpl. intros Hphi v Hwv u Hvu.
    apply Hphi. apply (fR_nl_trans F n w v u Hwv Hvu).
  - intros F V w. simpl. intros Hphi v Hwv.
    apply Hphi. apply (fR_nl_mon F n w v Hwv).
  - intros F V w. simpl. intros v Hwv Hbox.
    destruct (fR_nl_nextcon F n w v Hwv) as [u Hvu].
    exact (Hbox u Hvu).
  - intros F V w. apply (IHProvable_no_Loeb1 F V w).
    apply (IHProvable_no_Loeb2 F V w).
  - intros F V w. simpl. intros v _.
    apply (IHProvable_no_Loeb F V v).
Qed.

Definition F_no_Loeb : Frame_no_Loeb :=
  mkFrame_no_Loeb nat R_break_wf
    R_break_wf_trans R_break_wf_mon R_break_wf_nextcon.

Theorem loeb_axiom_needs_Loeb :
  ~ (|-no_loeb Impl (Box 0 (Impl (Box 0 Bot) Bot)) (Box 0 Bot)).
Proof.
  intro H.
  pose proof (soundness_no_Loeb _ H F_no_Loeb (fun _ _ => true) 0) as Hf.
  simpl in Hf.
  assert (HantBox : forall v, R_break_wf 0 0 v ->
                    (forall u, R_break_wf 0 v u -> False) -> False).
  { intros v _ Habs. apply (Habs (S v)). unfold R_break_wf. lia. }
  pose proof (Hf HantBox) as HboxBot.
  apply (HboxBot 1). unfold R_break_wf. lia.
Qed.

(** ** Mutual independence theorem.

    Of the modal axioms {Ax_Loeb, Ax_Mon, Ax_NextCon, Ax_Box4}, the
    first three are mutually independent: removing any one of them
    leaves a strictly weaker calculus.  Ax_Box4 is in fact derivable
    from K + Löb (see [nb4_axiom4]) and so is *not* independent.
    The propositional [Ax_K] axiom is universal under Kripke
    semantics and cannot be refuted by a frame, so its independence
    requires non-Kripke (e.g. neighborhood) semantics not developed
    here. *)

Theorem minimal_viable_bypass_loeb :
  ~ (|-no_loeb Impl (Box 0 (Impl (Box 0 Bot) Bot)) (Box 0 Bot)).
Proof. exact loeb_axiom_needs_Loeb. Qed.

Definition Agent : Type := nat -> Form -> Prop.

Definition agent_equiv (A B : Agent) : Prop :=
  forall n phi, A n phi <-> B n phi.

Definition agent_tiling_consistency (A : Agent) (n : nat) (phi : Form) : Prop :=
  A (S n) (Impl (Box n phi) (Neg (Box n (Neg phi)))).

Theorem agent_tiling_invariant : forall A B,
  agent_equiv A B ->
  forall n phi,
    agent_tiling_consistency A n phi <-> agent_tiling_consistency B n phi.
Proof.
  intros A B Hequiv n phi.
  unfold agent_tiling_consistency. apply Hequiv.
Qed.

Definition Provable_agent : Agent := fun n phi => |- Box n phi.

Theorem provable_agent_tiling : forall n phi,
  agent_tiling_consistency Provable_agent n phi.
Proof.
  intros n phi. unfold agent_tiling_consistency, Provable_agent.
  exact (tiling_consistency n phi).
Qed.

Definition prov_preserving (f : Form -> Form) : Prop :=
  forall phi, |- phi -> |- f phi.

Theorem licensure_recursion : forall f,
  prov_preserving f ->
  forall n phi, |- f (Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi))))).
Proof.
  intros f Hf n phi. apply Hf. exact (tiling_consistency n phi).
Qed.

Inductive Provable_sensor (Sensor : Form -> Prop) : Form -> Prop :=
  | PSlift : forall phi, |- phi -> Provable_sensor Sensor phi
  | PSsensor : forall phi, Sensor phi -> Provable_sensor Sensor phi
  | PSMP : forall phi psi,
      Provable_sensor Sensor (Impl phi psi) ->
      Provable_sensor Sensor phi ->
      Provable_sensor Sensor psi
  | PSNec : forall n phi,
      Provable_sensor Sensor phi -> Provable_sensor Sensor (Box n phi).

Theorem sensor_tiling_consistency : forall Sensor n phi,
  Provable_sensor Sensor (Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi))))).
Proof.
  intros Sensor n phi.
  apply PSlift. exact (tiling_consistency n phi).
Qed.

Theorem sensor_consistency_chain : forall Sensor n k, n < k ->
  Provable_sensor Sensor (Box k (Neg (Box n Bot))).
Proof.
  intros Sensor n k Hlt.
  apply PSlift. exact (consistency_chain n k Hlt).
Qed.

Theorem sensor_joint_licensing : forall Sensor n phi psi,
  |- Box n phi -> |- Box n psi ->
  Provable_sensor Sensor (Box (S n) (Neg (Box n (Neg (And phi psi))))).
Proof.
  intros Sensor n phi psi Hphi Hpsi.
  apply PSlift. exact (joint_licensing_consistency n phi psi Hphi Hpsi).
Qed.

Lemma prov_neg_top_anything : forall G, |- Impl (Neg Top) G.
Proof.
  intro G.
  pose proof (prov_perm (Impl Top Bot) Top Bot (prov_id (Impl Top Bot))) as H1.
  pose proof (prov_id Bot) as Htop.
  pose proof (MP _ _ H1 Htop) as H2.
  pose proof (prov_explosion G) as Hexp.
  exact (prov_compose _ _ _ H2 Hexp).
Qed.

Definition default_action : Form := Top.

Theorem goal_preservation_tiling : forall n succ G,
  |- Box n (Impl succ (Or default_action G)).
Proof.
  intros n succ G.
  apply Nec. unfold Or, default_action.
  apply prov_weaken. apply prov_neg_top_anything.
Qed.

Theorem goal_preservation_lifts : forall n m succ G,
  n <= m ->
  |- Box n (Impl succ (Or default_action G)) ->
  |- Box m (Impl succ (Or default_action G)).
Proof.
  intros n m succ G Hle Hbox.
  pose proof (prov_box_mon_le n m (Impl succ (Or default_action G)) Hle) as Hmon.
  exact (MP _ _ Hmon Hbox).
Qed.

Theorem no_panic_reflective_trust : forall n,
  (|- Impl (Box n (Neg (Box n Bot))) (Box n Bot)) /\
  ~ (|- Box n Bot).
Proof.
  intro n. split.
  - exact (godel_second n).
  - exact (meta_consistency_every_level n).
Qed.

Theorem vingean_principle :
  exists pf : (forall n phi, |- Box (S n)
                  (Impl (Box n phi) (Neg (Box n (Neg phi))))),
    forall n phi, pf n phi = tiling_consistency n phi.
Proof. exact tiling_witness_pointed. Qed.

Definition LevelBisim (k : nat) (F1 F2 : Frame)
                       (V1 : fW F1 -> nat -> bool)
                       (V2 : fW F2 -> nat -> bool)
                       (Z : fW F1 -> fW F2 -> Prop) : Prop :=
  forall w1 w2, Z w1 w2 ->
    (forall p, V1 w1 p = V2 w2 p) /\
    (forall v1, fR F1 k w1 v1 -> exists v2, fR F2 k w2 v2 /\ Z v1 v2) /\
    (forall v2, fR F2 k w2 v2 -> exists v1, fR F1 k w1 v1 /\ Z v1 v2).

Fixpoint level_k_only (k : nat) (phi : Form) : Prop :=
  match phi with
  | Var _ => True
  | Bot => True
  | Impl X Y => level_k_only k X /\ level_k_only k Y
  | Box n psi => n = k /\ level_k_only k psi
  end.

Theorem level_bisim_invariance : forall k F1 F2 V1 V2 Z,
  LevelBisim k F1 F2 V1 V2 Z ->
  forall phi w1 w2, level_k_only k phi -> Z w1 w2 ->
    (forces F1 V1 w1 phi <-> forces F2 V2 w2 phi).
Proof.
  intros k F1 F2 V1 V2 Z HBisim phi.
  induction phi as [p | | X IHX Y IHY | n psi IHpsi];
    intros w1 w2 Hlk HZ; simpl.
  - destruct (HBisim w1 w2 HZ) as [Hval _].
    rewrite (Hval p). reflexivity.
  - reflexivity.
  - simpl in Hlk. destruct Hlk as [HlX HlY].
    rewrite (IHX w1 w2 HlX HZ), (IHY w1 w2 HlY HZ). reflexivity.
  - simpl in Hlk. destruct Hlk as [Hnk Hlpsi]. subst n.
    split.
    + intros HBox v2 Hv2.
      destruct (HBisim w1 w2 HZ) as [_ [_ Hback]].
      destruct (Hback v2 Hv2) as [v1 [Hv1 HZ12]].
      rewrite <- (IHpsi v1 v2 Hlpsi HZ12).
      apply HBox. exact Hv1.
    + intros HBox v1 Hv1.
      destruct (HBisim w1 w2 HZ) as [_ [Hforth _]].
      destruct (Hforth v1 Hv1) as [v2 [Hv2 HZ12]].
      rewrite (IHpsi v1 v2 Hlpsi HZ12).
      apply HBox. exact Hv2.
Qed.

Theorem level_bisim_id : forall k F V, LevelBisim k F F V V (@eq (fW F)).
Proof.
  intros k F V w1 w2 Heq. subst w2.
  split; [reflexivity|]. split.
  - intros v1 Hv1. exists v1. split; [exact Hv1|reflexivity].
  - intros v2 Hv2. exists v2. split; [exact Hv2|reflexivity].
Qed.

Definition de_re_licensure (n m : nat) : Prop :=
  exists phi, |- Box n (Box m phi).

Definition de_dicto_licensure (n m : nat) : Prop :=
  forall phi, |- Box n (Box m phi).

Theorem de_re_holds : forall n m, de_re_licensure n m.
Proof.
  intros n m. unfold de_re_licensure. exists Top.
  apply Nec. apply Nec. exact (prov_id Bot).
Qed.

Theorem de_dicto_collapses : forall n m, S m <= n ->
  ~ de_dicto_licensure n m.
Proof.
  intros n m Hle Hsch.
  apply (meta_no_contradiction n (Box m Bot)).
  split.
  - exact (Hsch Bot).
  - pose proof (Ax_NextCon m) as Hnc.
    pose proof (prov_box_mon_le (S m) n (Neg (Box m Bot)) Hle) as Hmon.
    exact (MP _ _ Hmon Hnc).
Qed.

Theorem de_re_de_dicto_distinct : forall n m, S m <= n ->
  de_re_licensure n m /\ ~ de_dicto_licensure n m.
Proof.
  intros n m Hle. split.
  - apply de_re_holds.
  - apply de_dicto_collapses. exact Hle.
Qed.

Theorem licensure_functor_identity : forall n phi,
  |- Impl (Box n phi) (Box n phi).
Proof. intros n phi. exact (prov_id (Box n phi)). Qed.

Theorem licensure_functor_composition : forall n m k phi,
  n <= m -> m <= k ->
  |- Impl (Box n phi) (Box k phi).
Proof.
  intros n m k phi Hnm Hmk.
  apply (prov_box_mon_le n k phi).
  exact (Nat.le_trans n m k Hnm Hmk).
Qed.

Theorem licensure_functor_compose_via : forall n m k phi (Hnm : n <= m) (Hmk : m <= k),
  let f := prov_box_mon_le n m phi Hnm in
  let g := prov_box_mon_le m k phi Hmk in
  |- Impl (Box n phi) (Box k phi).
Proof.
  intros n m k phi Hnm Hmk.
  exact (prov_compose _ _ _
          (prov_box_mon_le n m phi Hnm)
          (prov_box_mon_le m k phi Hmk)).
Qed.

Definition build_finite_frame
  (W : Type)
  (R : nat -> W -> W -> Prop)
  (Htrans : forall n w v u, R n w v -> R n v u -> R n w u)
  (Hwf : forall n, well_founded (fun u v => R n v u))
  (Hmon : forall n w v, R (S n) w v -> R n w v)
  (Hnextcon : forall n w v, R (S n) w v -> exists u, R n v u)
  : Frame :=
  mkFrame W R Htrans Hwf Hmon Hnextcon.

Theorem build_finite_frame_correct : forall W R Htrans Hwf Hmon Hnextcon,
  fW (build_finite_frame W R Htrans Hwf Hmon Hnextcon) = W /\
  (forall n w v, fR (build_finite_frame W R Htrans Hwf Hmon Hnextcon) n w v <-> R n w v).
Proof.
  intros W R Htrans Hwf Hmon Hnextcon.
  split.
  - reflexivity.
  - intros n w v. simpl. reflexivity.
Qed.

Definition F0_via_builder : Frame :=
  build_finite_frame bool F0_R F0_R_trans F0_R_wf F0_R_mon F0_R_nextcon.

Theorem F0_via_builder_eq_F0 : F0_via_builder = F0.
Proof. unfold F0_via_builder, build_finite_frame, F0. reflexivity. Qed.

Definition Fnat_via_builder : Frame :=
  build_finite_frame nat Fnat_R
    Fnat_R_trans Fnat_R_wf Fnat_R_mon Fnat_R_nextcon.

Theorem Fnat_via_builder_eq_Fnat : Fnat_via_builder = Fnat.
Proof. unfold Fnat_via_builder, build_finite_frame, Fnat. reflexivity. Qed.

Theorem fixed_point_uniqueness_lifts : forall psi1 psi2 n,
  |- Iff psi1 psi2 -> |- Box n (Iff psi1 psi2).
Proof.
  intros psi1 psi2 n Hiff. apply Nec. exact Hiff.
Qed.

Record NeighFrame : Type := mkNeighFrame {
  fW_neigh : Type;
  fN : nat -> fW_neigh -> (fW_neigh -> Prop) -> Prop
}.

Fixpoint forces_neigh (F : NeighFrame) (V : fW_neigh F -> nat -> bool)
                      (w : fW_neigh F) (phi : Form) : Prop :=
  match phi with
  | Var p => V w p = true
  | Bot => False
  | Impl X Y => forces_neigh F V w X -> forces_neigh F V w Y
  | Box k psi => fN F k w (fun v => forces_neigh F V v psi)
  end.

Definition F_K_refuter_N (_ : nat) (_ : bool) (P : bool -> Prop) : Prop :=
  (P true /\ ~ P false) \/ (~ P true /\ P false) \/ (P true /\ P false).

Definition F_K_refuter : NeighFrame :=
  mkNeighFrame bool F_K_refuter_N.

Theorem K_refuted_in_neighborhood :
  ~ forces_neigh F_K_refuter
      (fun w (_ : nat) => if w then true else false) true
      (Impl (Box 0 (Impl (Var 0) Bot))
            (Impl (Box 0 (Var 0)) (Box 0 Bot))).
Proof.
  intro Habs.
  assert (HboxImp : F_K_refuter_N 0 true
            (fun v => forces_neigh F_K_refuter
                        (fun w (_ : nat) => if w then true else false) v
                        (Impl (Var 0) Bot))).
  { unfold F_K_refuter_N. right. left. split.
    - simpl. intro H. apply H. reflexivity.
    - simpl. intro H. discriminate. }
  pose proof (Habs HboxImp) as Habs2.
  assert (HboxA : F_K_refuter_N 0 true
            (fun v => forces_neigh F_K_refuter
                        (fun w (_ : nat) => if w then true else false) v
                        (Var 0))).
  { unfold F_K_refuter_N. left. split.
    - simpl. reflexivity.
    - simpl. intro H. discriminate. }
  pose proof (Habs2 HboxA) as HboxB.
  unfold F_K_refuter_N in HboxB.
  destruct HboxB as [[H _]|[[_ H]|[H _]]]; exact H.
Qed.


Theorem axioms_mutually_independent :
  (~ (|-no_loeb Impl (Box 0 (Impl (Box 0 Bot) Bot)) (Box 0 Bot))) /\
  (~ (|-no_mon Impl (Box 0 (Var 0)) (Box 1 (Var 0)))) /\
  (~ (|-no_nc Box 1 (Neg (Box 0 Bot)))) /\
  (forall n A, |-no_b4 Impl (Box n A) (Box n (Box n A))).
Proof.
  split; [|split; [|split]].
  - exact loeb_axiom_needs_Loeb.
  - exact mon_axiom_needs_Mon.
  - exact consistency_chain_needs_NC.
  - exact nb4_axiom4.
Qed.

(** ** Failure catalog.

    Packages the principal negative results of the calculus into a
    single theorem: monotonicity converse fails, same-level
    reflection schema fails uniformly, each level strictly extends
    its predecessor, and the reflection schema fails at every level.
    Each clause carries its own refuting frame inside the proof; the
    catalog is the meta-level summary. *)

Theorem failure_catalog :
  (forall n, ~ (|- Impl (Box (S n) (Var 0)) (Box n (Var 0)))) /\
  (forall n, ~ (forall phi, |- Box (S n) (Impl (Box (S n) phi) phi))) /\
  (forall n, exists phi, (|- Box (S n) phi) /\ ~ (|- Box n phi)) /\
  (forall n, ~ (forall phi, |- Impl (Box n phi) phi)).
Proof.
  split; [|split; [|split]].
  - exact mon_converse_fails.
  - exact reflection_at_same_level_unprovable_uniformly.
  - exact strict_extension_at_each_level.
  - exact reflection_schema_unprovable.
Qed.

(** ** Polymodal bisimulation and forces-invariance.

    A bisimulation between [(F1, V1)] and [(F2, V2)] is a relation
    [Z] over [fW F1 × fW F2] satisfying atomic agreement plus the
    forth-and-back conditions for [fR] at every level.  [forces] is
    invariant under bisimulation: bisimilar worlds satisfy the same
    formulas. *)

Definition Bisim (F1 F2 : Frame)
                 (V1 : fW F1 -> nat -> bool)
                 (V2 : fW F2 -> nat -> bool)
                 (Z : fW F1 -> fW F2 -> Prop) : Prop :=
  forall w1 w2, Z w1 w2 ->
    (forall p, V1 w1 p = V2 w2 p) /\
    (forall n v1, fR F1 n w1 v1 -> exists v2, fR F2 n w2 v2 /\ Z v1 v2) /\
    (forall n v2, fR F2 n w2 v2 -> exists v1, fR F1 n w1 v1 /\ Z v1 v2).

Theorem bisim_invariance : forall F1 F2 V1 V2 Z,
  Bisim F1 F2 V1 V2 Z ->
  forall phi w1 w2, Z w1 w2 ->
    (forces F1 V1 w1 phi <-> forces F2 V2 w2 phi).
Proof.
  intros F1 F2 V1 V2 Z HBisim phi.
  induction phi as [p | | X IHX Y IHY | n psi IHpsi];
    intros w1 w2 HZ; simpl.
  - destruct (HBisim w1 w2 HZ) as [Hval _].
    rewrite (Hval p). reflexivity.
  - reflexivity.
  - rewrite (IHX w1 w2 HZ), (IHY w1 w2 HZ). reflexivity.
  - split.
    + intros HBox v2 Hv2.
      destruct (HBisim w1 w2 HZ) as [_ [_ Hback]].
      destruct (Hback n v2 Hv2) as [v1 [Hv1 HZ12]].
      rewrite <- (IHpsi v1 v2 HZ12).
      apply HBox. exact Hv1.
    + intros HBox v1 Hv1.
      destruct (HBisim w1 w2 HZ) as [_ [Hforth _]].
      destruct (Hforth n v1 Hv1) as [v2 [Hv2 HZ12]].
      rewrite (IHpsi v1 v2 HZ12).
      apply HBox. exact Hv2.
Qed.

(** Identity bisimulation: every model is bisimilar to itself by [eq]. *)

Theorem bisim_id : forall F V, Bisim F F V V (@eq (fW F)).
Proof.
  intros F V w1 w2 Heq. subst w2.
  split; [reflexivity|]. split.
  - intros n v1 Hv1. exists v1. split; [exact Hv1|reflexivity].
  - intros n v2 Hv2. exists v2. split; [exact Hv2|reflexivity].
Qed.

(** ** Propositional fragment: box-freeness predicate and decidability
    via truth-table evaluation.

    For [box_free] formulas, [eval val phi] is a complete classical
    truth-functional evaluator.  Soundness gives the easy direction:
    every [|- phi] is true under every valuation.  Hence a non-tautology
    is unprovable, decidable by computing [eval] on the [2^k]
    assignments to the [k] free variables.  The converse direction
    (every classical tautology is in [ProvableProp]) is the Kalmár
    completeness theorem [prop_completeness] above. *)


Theorem provable_classically_valid : forall phi,
  |- phi -> classical_valid phi.
Proof.
  intros phi H val. exact (eval_provable_true val phi H).
Qed.

(** Refutation procedure: a single valuation producing [false]
    suffices to refute provability. *)

Theorem refute_via_valuation : forall phi val,
  eval val phi = false -> ~ (|- phi).
Proof.
  intros phi val Hval Hprov.
  pose proof (provable_classically_valid phi Hprov val) as Hclaim.
  rewrite Hclaim in Hval. discriminate.
Qed.

(** Box-free formulas have no [Box] sub-formula. *)

Lemma box_free_eval_independent : forall phi,
  box_free phi -> forall val1 val2,
    (forall p, val1 p = val2 p) -> eval val1 phi = eval val2 phi.
Proof.
  intros phi Hbf val1 val2 Hext.
  induction phi as [k | | X IHX Y IHY | n psi IHpsi]; simpl.
  - apply Hext.
  - reflexivity.
  - simpl in Hbf. destruct Hbf as [HX HY].
    rewrite (IHX HX), (IHY HY). reflexivity.
  - simpl in Hbf. contradiction.
Qed.

(** Reflective refutation tactic.  Apply with a witness valuation:
    [prop_refute val] closes a goal [~ (|- phi)] when [eval val phi]
    reduces to [false]. *)

Ltac prop_refute val :=
  apply (refute_via_valuation _ val); cbn; try reflexivity.

(** Demonstration: [Var 0] is not a theorem (refuted by the constant
    [false] valuation). *)

Example var_not_provable : ~ (|- Var 0).
Proof. prop_refute (fun _ : nat => false). Qed.

(** ** Compactness for Provable_with_hyp.

    Lift hypotheses from finite lists to arbitrary predicates [Gamma]
    on [Form], with [Provable_set Gamma phi] meaning "[phi] is
    derivable from some finite [G] all of whose members lie in
    [Gamma]".  Compactness is the equivalence between [Consistent
    Gamma] and "every finite [G] in [Gamma] is consistent", which is
    immediate from the definition since derivability uses only finitely
    many hypotheses. *)

Definition Provable_set (Gamma : Form -> Prop) (phi : Form) : Prop :=
  exists G : list Form,
    (forall psi, In psi G -> Gamma psi) /\ Provable_with_hyp G phi.

Definition Consistent (Gamma : Form -> Prop) : Prop :=
  ~ Provable_set Gamma Bot.

Definition FinitelyConsistent (Gamma : Form -> Prop) : Prop :=
  forall G : list Form,
    (forall psi, In psi G -> Gamma psi) -> ~ Provable_with_hyp G Bot.

Theorem compactness_forward : forall Gamma,
  FinitelyConsistent Gamma -> Consistent Gamma.
Proof.
  intros Gamma Hfin Hcontra.
  destruct Hcontra as [G [HG HBot]].
  apply (Hfin G HG HBot).
Qed.

Theorem compactness_backward : forall Gamma,
  Consistent Gamma -> FinitelyConsistent Gamma.
Proof.
  intros Gamma HCon G HG Hbot.
  apply HCon. exists G. split; assumption.
Qed.

Theorem compactness : forall Gamma,
  Consistent Gamma <-> FinitelyConsistent Gamma.
Proof.
  intro Gamma. split.
  - apply compactness_backward.
  - apply compactness_forward.
Qed.

(** ** Japaridze axiom and Provable_GLP.

    The Japaridze axiom of standard polymodal provability logic GLP:
    [Diamond n phi -> Box (S n) (Diamond n phi)].  Stated and shown
    to fail under suitable Kripke counter-models (so it is not
    derivable in [Provable]).  The full conservativity-into-GLP
    embedding is a separate theorem that requires the Box4-derivability
    transfer (item 12) and remains for the GLP-style calculus
    [Provable_GLP], not built here. *)

Definition Japaridze (n : nat) (phi : Form) : Form :=
  Impl (Diamond n phi) (Box (S n) (Diamond n phi)).

Theorem japaridze_unprovable_at_0 :
  ~ (|- Japaridze 0 (Var 0)).
Proof.
  intro H.
  pose (V := fun (w : nat) (p : nat) =>
    match p with O => Nat.eqb w 4 | _ => false end).
  pose proof (soundness _ H Fnat V 5) as Hf.
  unfold Japaridze, Diamond in Hf. simpl in Hf.
  assert (Hdia0 : (forall v : nat, Fnat_R 0 5 v -> V v 0 = true -> False) -> False).
  { intro Habs.
    apply (Habs 4).
    - unfold Fnat_R. split; lia.
    - unfold V. simpl. reflexivity. }
  pose proof (Hf Hdia0) as HBox1.
  apply (HBox1 1).
  - unfold Fnat_R. split; lia.
  - intros v Hv Hval. unfold Fnat_R in Hv. destruct Hv as [Hv1 Hv2].
    assert (v = 0) by lia. subst v.
    unfold V in Hval. simpl in Hval. discriminate.
Qed.

Theorem japaridze_unprovable_family : forall n, ~ (|- Japaridze n (Var 0)).
Proof.
  intro n. intro H.
  pose (V := fun (w : nat) (p : nat) =>
    match p with O => Nat.eqb w (n+4) | _ => false end).
  pose proof (soundness _ H Fnat V (n+5)) as Hf.
  unfold Japaridze, Diamond in Hf. simpl in Hf.
  assert (Hdia : (forall v : nat, Fnat_R n (n+5) v -> V v 0 = true -> False) -> False).
  { intro Habs.
    apply (Habs (n+4)).
    - unfold Fnat_R. split; lia.
    - unfold V. simpl. rewrite Nat.eqb_refl. reflexivity. }
  pose proof (Hf Hdia) as HBoxSn.
  specialize (HBoxSn (n+1) ltac:(unfold Fnat_R; split; lia)) as HD.
  apply HD.
  intros v Hv Hval.
  unfold Fnat_R in Hv. destruct Hv as [Hv1 Hv2].
  assert (Hve : v = n) by lia. subst v.
  unfold V in Hval. simpl in Hval.
  apply Nat.eqb_eq in Hval. lia.
Qed.

Definition Sum_R (F1 F2 : Frame) (n : nat) (w v : fW F1 + fW F2) : Prop :=
  match w, v with
  | inl a, inl b => fR F1 n a b
  | inr a, inr b => fR F2 n a b
  | _, _ => False
  end.

Lemma Sum_R_trans : forall F1 F2 n w v u,
  Sum_R F1 F2 n w v -> Sum_R F1 F2 n v u -> Sum_R F1 F2 n w u.
Proof.
  intros F1 F2 n [a|a] [b|b] [c|c] H1 H2; simpl in *; try contradiction.
  - exact (fR_trans F1 n a b c H1 H2).
  - exact (fR_trans F2 n a b c H1 H2).
Qed.

Lemma Sum_R_wf : forall F1 F2 n,
  well_founded (fun u v => Sum_R F1 F2 n v u).
Proof.
  intros F1 F2 n [a|a].
  - induction a as [a IHa] using (well_founded_induction (fR_wf F1 n)).
    apply Acc_intro. intros [b|b] H; simpl in H.
    + apply IHa. exact H.
    + contradiction.
  - induction a as [a IHa] using (well_founded_induction (fR_wf F2 n)).
    apply Acc_intro. intros [b|b] H; simpl in H.
    + contradiction.
    + apply IHa. exact H.
Qed.

Lemma Sum_R_mon : forall F1 F2 n w v,
  Sum_R F1 F2 (S n) w v -> Sum_R F1 F2 n w v.
Proof.
  intros F1 F2 n [a|a] [b|b] H; simpl in *; try contradiction.
  - exact (fR_mon F1 n a b H).
  - exact (fR_mon F2 n a b H).
Qed.

Lemma Sum_R_nextcon : forall F1 F2 n w v,
  Sum_R F1 F2 (S n) w v -> exists u, Sum_R F1 F2 n v u.
Proof.
  intros F1 F2 n [a|a] [b|b] H; simpl in *; try contradiction.
  - destruct (fR_nextcon F1 n a b H) as [u Hu]. exists (inl u). exact Hu.
  - destruct (fR_nextcon F2 n a b H) as [u Hu]. exists (inr u). exact Hu.
Qed.

Definition Frame_Sum (F1 F2 : Frame) : Frame :=
  mkFrame (fW F1 + fW F2) (Sum_R F1 F2)
    (Sum_R_trans F1 F2) (Sum_R_wf F1 F2)
    (Sum_R_mon F1 F2) (Sum_R_nextcon F1 F2).

Lemma forces_sum_left : forall F1 F2 V phi w,
  forces (Frame_Sum F1 F2) V (inl w) phi <->
  forces F1 (fun v p => V (inl v) p) w phi.
Proof.
  intros F1 F2 V phi.
  induction phi as [p | | X IHX Y IHY | n psi IHpsi]; intro w; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (IHX w), (IHY w). reflexivity.
  - split.
    + intros HBox v1 Hv1.
      pose proof (HBox (inl v1) Hv1) as Hf.
      rewrite IHpsi in Hf. exact Hf.
    + intros HBox v Hv.
      destruct v as [v1|v2].
      * simpl in Hv. rewrite IHpsi. apply HBox. exact Hv.
      * simpl in Hv. contradiction.
Qed.

Lemma forces_sum_right : forall F1 F2 V phi w,
  forces (Frame_Sum F1 F2) V (inr w) phi <->
  forces F2 (fun v p => V (inr v) p) w phi.
Proof.
  intros F1 F2 V phi.
  induction phi as [p | | X IHX Y IHY | n psi IHpsi]; intro w; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (IHX w), (IHY w). reflexivity.
  - split.
    + intros HBox v2 Hv2.
      pose proof (HBox (inr v2) Hv2) as Hf.
      rewrite IHpsi in Hf. exact Hf.
    + intros HBox v Hv.
      destruct v as [v1|v2].
      * simpl in Hv. contradiction.
      * simpl in Hv. rewrite IHpsi. apply HBox. exact Hv.
Qed.

Theorem sum_preserves_validity : forall F1 F2 phi,
  Valid phi ->
  forall V w, forces (Frame_Sum F1 F2) V w phi.
Proof.
  intros F1 F2 phi Hval V w.
  apply Hval.
Qed.

Fixpoint level_le_k (k : nat) (phi : Form) : Prop :=
  match phi with
  | Var _ => True
  | Bot => True
  | Impl X Y => level_le_k k X /\ level_le_k k Y
  | Box n psi => n <= k /\ level_le_k k psi
  end.

Definition Provable_k (k : nat) (phi : Form) : Prop :=
  level_le_k k phi /\ |- phi.

Theorem provable_k_subset : forall k phi,
  Provable_k k phi -> |- phi.
Proof. intros k phi [_ H]. exact H. Qed.

Theorem provable_k_box_lift : forall k n phi,
  n <= k -> level_le_k k phi -> |- phi -> Provable_k k (Box n phi).
Proof.
  intros k n phi Hn Hbf Hp.
  split.
  - simpl. split. exact Hn. exact Hbf.
  - apply Nec. exact Hp.
Qed.

Theorem provable_k_monotone : forall k k' phi,
  k <= k' -> level_le_k k phi -> level_le_k k' phi.
Proof.
  intros k k' phi Hle. revert phi.
  induction phi as [p | | X IHX Y IHY | n psi IHpsi]; simpl; intro H; trivial.
  - destruct H as [HX HY]. split; auto.
  - destruct H as [Hn Hpsi]. split; [lia | auto].
Qed.

Theorem naturalistic_trust : forall n phi psi,
  |- Iff phi psi -> |- Iff (Box n phi) (Box n psi).
Proof.
  intros n phi psi Hiff.
  unfold Iff in Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hf.
  pose proof (prov_and_elim_r_meta _ _ Hiff) as Hb.
  pose proof (prov_box_imp n _ _ Hf) as HBf.
  pose proof (prov_box_imp n _ _ Hb) as HBb.
  apply prov_iff_intro; assumption.
Qed.

Definition action_criterion (n : nat) (b G : Form) : Form :=
  Impl b (Box n (Impl b G)).

Theorem updateless_agent_tiling : forall n b G,
  |- action_criterion n b G ->
  |- Box (S n) (action_criterion n b G).
Proof.
  intros n b G Hcrit. apply Nec. exact Hcrit.
Qed.

Theorem updateless_agent_lifts : forall n m b G,
  n <= m -> |- action_criterion n b G ->
  |- Impl b (Box m (Impl b G)).
Proof.
  intros n m b G Hle Hcrit.
  unfold action_criterion in Hcrit.
  pose proof (prov_compose_internal b (Box n (Impl b G)) (Box m (Impl b G))) as Hci.
  pose proof (prov_box_mon_le n m (Impl b G) Hle) as Hmon.
  pose proof (MP _ _ Hci Hmon) as Hstep.
  exact (MP _ _ Hstep Hcrit).
Qed.

Theorem updateless_agent_uniform : forall n m b G,
  n <= m ->
  |- Impl (Box n (Impl b G)) (Box m (Impl b G)).
Proof.
  intros n m b G Hle.
  exact (prov_box_mon_le n m (Impl b G) Hle).
Qed.

Inductive Provable_with_hyp_Nec : list Form -> Form -> Prop :=
  | DTN_hyp : forall G phi, In phi G -> Provable_with_hyp_Nec G phi
  | DTN_thm : forall G phi, |- phi -> Provable_with_hyp_Nec G phi
  | DTN_MP : forall G phi psi,
      Provable_with_hyp_Nec G (Impl phi psi) ->
      Provable_with_hyp_Nec G phi ->
      Provable_with_hyp_Nec G psi
  | DTN_Nec : forall G n phi,
      Provable_with_hyp_Nec [] phi ->
      Provable_with_hyp_Nec G (Box n phi).

Lemma dtn_nohyp_provable : forall phi,
  Provable_with_hyp_Nec [] phi -> |- phi.
Proof.
  intros phi H. remember (@nil Form) as G eqn:HG.
  induction H as [G phi Hin | G phi Hp | G phi psi H1 IH1 H2 IH2 | G n phi Hsub IH].
  - subst G. simpl in Hin. destruct Hin.
  - exact Hp.
  - exact (MP _ _ (IH1 HG) (IH2 HG)).
  - apply Nec. apply IH. reflexivity.
Qed.

Lemma dtn_provable_nohyp : forall phi,
  |- phi -> Provable_with_hyp_Nec [] phi.
Proof.
  intros phi H. apply DTN_thm. exact H.
Qed.

Theorem deduction_theorem_with_Nec : forall G phi psi,
  Provable_with_hyp_Nec (phi :: G) psi ->
  Provable_with_hyp_Nec G (Impl phi psi).
Proof.
  intros G phi psi H.
  remember (phi :: G) as G' eqn:HG.
  revert G phi HG.
  induction H as [G' alpha Hin | G' alpha Hthm
                  | G' alpha beta Himp IHimp Halpha IHalpha
                  | G' n alpha Hsub _];
    intros G phi' HG'.
  - subst G'. simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst alpha. apply DTN_thm. apply prov_id.
    + apply DTN_MP with alpha.
      * apply DTN_thm. apply Ax_K.
      * apply DTN_hyp. exact Hin'.
  - apply DTN_thm. exact (MP _ _ (Ax_K alpha phi') Hthm).
  - subst G'.
    pose proof (IHimp G phi' eq_refl) as HI1.
    pose proof (IHalpha G phi' eq_refl) as HI2.
    apply DTN_MP with (Impl phi' alpha).
    + apply DTN_MP with (Impl phi' (Impl alpha beta)).
      * apply DTN_thm. exact (Ax_S phi' alpha beta).
      * exact HI1.
    + exact HI2.
  - apply DTN_MP with (Box n alpha).
    + apply DTN_thm. apply Ax_K.
    + apply DTN_Nec. exact Hsub.
Qed.

Inductive Provable_GLP : Form -> Prop :=
  | GLP_Ax_K : forall phi psi,
      Provable_GLP (Impl phi (Impl psi phi))
  | GLP_Ax_S : forall phi psi chi,
      Provable_GLP (Impl (Impl phi (Impl psi chi))
                         (Impl (Impl phi psi) (Impl phi chi)))
  | GLP_Ax_DN : forall phi,
      Provable_GLP (Impl (Neg (Neg phi)) phi)
  | GLP_Ax_BoxK : forall n phi psi,
      Provable_GLP (Impl (Box n (Impl phi psi))
                         (Impl (Box n phi) (Box n psi)))
  | GLP_Ax_Loeb : forall n phi,
      Provable_GLP (Impl (Box n (Impl (Box n phi) phi)) (Box n phi))
  | GLP_Ax_Box4 : forall n phi,
      Provable_GLP (Impl (Box n phi) (Box n (Box n phi)))
  | GLP_Ax_Mon : forall n phi,
      Provable_GLP (Impl (Box n phi) (Box (S n) phi))
  | GLP_Ax_Japaridze : forall n phi, Provable_GLP (Japaridze n phi)
  | GLP_MP : forall phi psi,
      Provable_GLP (Impl phi psi) -> Provable_GLP phi -> Provable_GLP psi
  | GLP_Nec : forall n phi,
      Provable_GLP phi -> Provable_GLP (Box n phi).

Theorem provable_GLP_proves_japaridze : forall n phi,
  Provable_GLP (Japaridze n phi).
Proof. intros. apply GLP_Ax_Japaridze. Qed.

Theorem provable_does_not_prove_japaridze :
  ~ |- Japaridze 0 (Var 0).
Proof. exact japaridze_unprovable_at_0. Qed.

Theorem provable_GLP_incomparable_with_provable :
  Provable_GLP (Japaridze 0 (Var 0)) /\ ~ |- Japaridze 0 (Var 0).
Proof.
  split.
  - apply provable_GLP_proves_japaridze.
  - exact provable_does_not_prove_japaridze.
Qed.

Inductive Provable_GL : Form -> Prop :=
  | GL_Ax_K : forall phi psi,
      Provable_GL (Impl phi (Impl psi phi))
  | GL_Ax_S : forall phi psi chi,
      Provable_GL (Impl (Impl phi (Impl psi chi))
                        (Impl (Impl phi psi) (Impl phi chi)))
  | GL_Ax_DN : forall phi,
      Provable_GL (Impl (Neg (Neg phi)) phi)
  | GL_Ax_BoxK : forall phi psi,
      Provable_GL (Impl (Box 0 (Impl phi psi))
                        (Impl (Box 0 phi) (Box 0 psi)))
  | GL_Ax_Loeb : forall phi,
      Provable_GL (Impl (Box 0 (Impl (Box 0 phi) phi)) (Box 0 phi))
  | GL_Ax_Box4 : forall phi,
      Provable_GL (Impl (Box 0 phi) (Box 0 (Box 0 phi)))
  | GL_MP : forall phi psi,
      Provable_GL (Impl phi psi) -> Provable_GL phi -> Provable_GL psi
  | GL_Nec : forall phi,
      Provable_GL phi -> Provable_GL (Box 0 phi).

Fixpoint level_0_only (phi : Form) : Prop :=
  match phi with
  | Var _ => True
  | Bot => True
  | Impl X Y => level_0_only X /\ level_0_only Y
  | Box n psi => n = 0 /\ level_0_only psi
  end.

Theorem GL_in_provable : forall phi, Provable_GL phi -> |- phi.
Proof.
  intros phi H. induction H as [| | | | | | phi psi _ IH1 _ IH2 | phi _ IH].
  - apply Ax_K.
  - apply Ax_S.
  - apply Ax_DN.
  - apply Ax_BoxK.
  - apply Ax_Loeb.
  - apply Ax_Box4.
  - exact (MP _ _ IH1 IH2).
  - exact (Nec _ _ IH).
Qed.

Theorem frame_conditions_independent :
  (exists Rt : nat -> nat -> nat -> Prop,
    (forall n, well_founded (fun u v => Rt n v u)) /\
    (forall n w v, Rt (S n) w v -> Rt n w v) /\
    (forall n w v, Rt (S n) w v -> exists u, Rt n v u) /\
    ~ (forall n w v u, Rt n w v -> Rt n v u -> Rt n w u)) /\
  (exists Rt : nat -> nat -> nat -> Prop,
    (forall n w v u, Rt n w v -> Rt n v u -> Rt n w u) /\
    (forall n w v, Rt (S n) w v -> Rt n w v) /\
    (forall n w v, Rt (S n) w v -> exists u, Rt n v u) /\
    ~ (forall n, well_founded (fun u v => Rt n v u))) /\
  (exists Rt : nat -> nat -> nat -> Prop,
    (forall n w v u, Rt n w v -> Rt n v u -> Rt n w u) /\
    (forall n, well_founded (fun u v => Rt n v u)) /\
    (forall n w v, Rt (S n) w v -> exists u, Rt n v u) /\
    ~ (forall n w v, Rt (S n) w v -> Rt n w v)) /\
  (exists Rt : nat -> nat -> nat -> Prop,
    (forall n w v u, Rt n w v -> Rt n v u -> Rt n w u) /\
    (forall n, well_founded (fun u v => Rt n v u)) /\
    (forall n w v, Rt (S n) w v -> Rt n w v) /\
    ~ (forall n w v, Rt (S n) w v -> exists u, Rt n v u)).
Proof.
  exact (conj frame_indep_trans
        (conj frame_indep_wf
        (conj frame_indep_mon frame_indep_nc))).
Qed.

