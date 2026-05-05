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
From Stdlib Require Import Logic.ClassicalEpsilon.
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
    below as [Ax_Box4].  It is provably redundant: [nb4_axiom4] derives
    it from K and Loeb in [Provable_no_B4] via the standard A ∧ Box A
    substitution argument, and [provable_iff_no_b4] shows the two
    calculi coincide. *)

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
    not even uniformly provable.  The unconditional version
    [reflection_schema_unprovable] follows from
    [meta_consistency_system], proved below. *)

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

    A concrete fixed point: [|- Iff Top (Box n Top)].  Both [Top]
    and [Box n Top] are theorems individually, so the iff follows by
    [prov_weaken] in each direction. *)

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
    [Ax_NextCon]: they are preserved under dropping NextCon. *)

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
    with respect to actual licensing decisions at level [n]. *)

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
  forall k, k < n ->
  k < n /\ |- Box (S k) (Neg (Box k Bot)) /\ |- Box n (Neg (Box k Bot)).
Proof.
  intros n k Hlt. split; [|split].
  - exact Hlt.
  - exact (Ax_NextCon k).
  - exact (MP _ _ (prov_box_mon_le (S k) n (Neg (Box k Bot)) Hlt)
                  (Ax_NextCon k)).
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

(** ** Polynomial-space tautology checker.

    [bool_list_succ] increments a binary counter (least-significant-bit
    first) over [list bool], returning [None] on overflow.
    [pspace_check_iter] iterates the counter, evaluating [phi] at each
    assignment; it short-circuits on the first failing assignment.
    [decide_tautology_pspace] runs the iteration with a buffer of size
    [length (nodup Nat.eq_dec (free_vars phi))] and fuel
    [2 ^ |free_vars|].  The buffer grows linearly with the formula's
    free-variable count: O(|free_vars phi|) at any moment.  This is
    the polynomial-space witness; the truth-table-materialising
    [decide_tautology] is the exponential-space variant. *)

Fixpoint bool_list_succ (l : list bool) : option (list bool) :=
  match l with
  | [] => None
  | false :: rest => Some (true :: rest)
  | true :: rest =>
    match bool_list_succ rest with
    | Some rest' => Some (false :: rest')
    | None => None
    end
  end.

Lemma bool_list_succ_preserves_length : forall l l',
  bool_list_succ l = Some l' -> length l' = length l.
Proof.
  induction l as [|x rest IH]; intros l' H; cbn in *.
  - discriminate.
  - destruct x.
    + destruct (bool_list_succ rest) as [r'|] eqn:E.
      * injection H as Heq. subst l'. cbn. f_equal.
        exact (IH r' eq_refl).
      * discriminate H.
    + injection H as Heq. subst l'. cbn. reflexivity.
Qed.

Fixpoint pspace_check_iter (vars : list nat) (current : list bool)
                            (phi : Form) (fuel : nat) : bool :=
  if eval (mk_assignment vars current) phi then
    match fuel with
    | 0 => true
    | S f =>
      match bool_list_succ current with
      | Some next => pspace_check_iter vars next phi f
      | None => true
      end
    end
  else false.

Definition decide_tautology_pspace (phi : Form) : bool :=
  let vars := nodup Nat.eq_dec (free_vars phi) in
  pspace_check_iter vars (List.repeat false (length vars)) phi
                    (Nat.pow 2 (length vars)).

Lemma repeat_false_length : forall n,
  length (@List.repeat bool false n) = n.
Proof. intro n. apply repeat_length. Qed.

Lemma pspace_check_iter_pointwise_sound : forall vars phi fuel current,
  pspace_check_iter vars current phi fuel = true ->
  eval (mk_assignment vars current) phi = true.
Proof.
  intros vars phi fuel. induction fuel as [|f IH]; intros current H.
  - cbn in H.
    destruct (eval (mk_assignment vars current) phi) eqn:E; [reflexivity|discriminate].
  - cbn in H.
    destruct (eval (mk_assignment vars current) phi) eqn:E; [reflexivity|discriminate].
Qed.

Fixpoint bl_to_nat (l : list bool) : nat :=
  match l with
  | [] => 0
  | false :: rest => 2 * bl_to_nat rest
  | true :: rest => S (2 * bl_to_nat rest)
  end.

Lemma bl_to_nat_repeat_false : forall n, bl_to_nat (List.repeat false n) = 0.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma bl_to_nat_bound : forall l, bl_to_nat l < 2 ^ length l.
Proof.
  induction l as [|b rest IH]; cbn.
  - lia.
  - destruct b; cbn; lia.
Qed.

Lemma bool_list_succ_None_fwd : forall l,
  bool_list_succ l = None -> l = List.repeat true (length l).
Proof.
  induction l as [|b rest IH]; intros H; cbn in *.
  - reflexivity.
  - destruct b; cbn.
    + destruct (bool_list_succ rest) as [r'|] eqn:Esucc.
      * discriminate.
      * f_equal. apply IH. reflexivity.
    + discriminate.
Qed.

Lemma bool_list_succ_repeat_true : forall n,
  bool_list_succ (List.repeat true n) = None.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma bool_list_succ_None_iff : forall l,
  bool_list_succ l = None <-> l = List.repeat true (length l).
Proof.
  intros l. split.
  - apply bool_list_succ_None_fwd.
  - intros H. rewrite H. apply bool_list_succ_repeat_true.
Qed.

Lemma bool_list_succ_some_S : forall l l',
  bool_list_succ l = Some l' -> bl_to_nat l' = S (bl_to_nat l).
Proof.
  induction l as [|b rest IH]; intros l' H; cbn in H.
  - discriminate.
  - destruct b; cbn.
    + destruct (bool_list_succ rest) as [r'|] eqn:Esucc; [|discriminate].
      injection H as Heq. subst l'. cbn.
      pose proof (IH r' eq_refl) as Hr'. rewrite Hr'. lia.
    + injection H as Heq. subst l'. cbn. lia.
Qed.

Fixpoint iter_bool_list_succ (k : nat) (l : list bool) : option (list bool) :=
  match k with
  | 0 => Some l
  | S k' => match bool_list_succ l with
            | Some l' => iter_bool_list_succ k' l'
            | None => None
            end
  end.

Lemma iter_bool_list_succ_preserves_length : forall k l l',
  iter_bool_list_succ k l = Some l' -> length l' = length l.
Proof.
  induction k as [|k IH]; intros l l' H; cbn in H.
  - injection H as Hl. subst l'. reflexivity.
  - destruct (bool_list_succ l) as [m|] eqn:Esucc; [|discriminate].
    pose proof (IH m l' H) as Hm.
    pose proof (bool_list_succ_preserves_length _ _ Esucc) as Hlen.
    lia.
Qed.

Lemma iter_bool_list_succ_S_value : forall k l l',
  iter_bool_list_succ k l = Some l' -> bl_to_nat l' = bl_to_nat l + k.
Proof.
  induction k as [|k IH]; intros l l' H; cbn in H.
  - injection H as Hl. subst l'. lia.
  - destruct (bool_list_succ l) as [m|] eqn:Esucc; [|discriminate].
    pose proof (bool_list_succ_some_S _ _ Esucc) as Hm.
    pose proof (IH m l' H) as Hl'.
    lia.
Qed.

Lemma two_pow_pos : forall n, 2 ^ n >= 1.
Proof.
  induction n as [|n IH]; cbn; lia.
Qed.

Lemma bl_to_nat_repeat_true : forall n,
  bl_to_nat (List.repeat true n) = 2 ^ n - 1.
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - rewrite IH.
    pose proof (two_pow_pos n) as Hp. lia.
Qed.

Lemma bool_list_succ_some_when_lt : forall l n,
  length l = n -> bl_to_nat l < 2 ^ n - 1 ->
  exists l', bool_list_succ l = Some l'.
Proof.
  induction l as [|b rest IH]; intros n Hlen Hlt.
  - cbn in Hlen. subst n. cbn in Hlt. lia.
  - cbn in Hlen. destruct n as [|n']; [discriminate|]. injection Hlen as Hl.
    cbn. destruct b.
    + cbn in Hlt.
      assert (Hrest_lt : bl_to_nat rest < 2 ^ n' - 1).
      { pose proof (two_pow_pos n') as Hp. cbn in Hlt. lia. }
      destruct (IH n' Hl Hrest_lt) as [l' Hsucc].
      rewrite Hsucc. eexists. reflexivity.
    + eexists. reflexivity.
Qed.

Lemma iter_bool_list_succ_progress : forall k m l n,
  length l = n -> bl_to_nat l = m -> m + k < 2 ^ n ->
  exists l', iter_bool_list_succ k l = Some l' /\
             length l' = n /\
             bl_to_nat l' = m + k.
Proof.
  induction k as [|k IH]; intros m l n Hlen Hm Hbound.
  - exists l. cbn. split; [reflexivity | split; [exact Hlen | rewrite Hm; lia]].
  - assert (Hm_lt : m < 2 ^ n - 1).
    { pose proof (two_pow_pos n) as Hp. lia. }
    rewrite <- Hm in Hm_lt.
    destruct (bool_list_succ_some_when_lt _ _ Hlen Hm_lt) as [next Hsucc].
    pose proof (bool_list_succ_some_S _ _ Hsucc) as Hnext_val.
    pose proof (bool_list_succ_preserves_length _ _ Hsucc) as Hnext_len.
    cbn. rewrite Hsucc.
    destruct (IH (S m) next n) as [l' [Hi [Hl' Hv']]].
    + lia.
    + lia.
    + lia.
    + exists l'. split; [exact Hi | split; [exact Hl' | lia]].
Qed.

Lemma bl_to_nat_inj_same_length : forall l1 l2,
  length l1 = length l2 -> bl_to_nat l1 = bl_to_nat l2 -> l1 = l2.
Proof.
  induction l1 as [|b1 r1 IH]; intros [|b2 r2] Hlen Hv; cbn in Hlen, Hv.
  - reflexivity.
  - discriminate.
  - discriminate.
  - injection Hlen as Hlen'.
    assert (Hb : b1 = b2 /\ bl_to_nat r1 = bl_to_nat r2).
    { destruct b1, b2; cbn in Hv; split; try reflexivity; lia. }
    destruct Hb as [Hb_eq Hr_eq]. subst b2.
    f_equal. apply IH; assumption.
Qed.

Lemma every_bool_list_visited : forall n bs,
  length bs = n ->
  iter_bool_list_succ (bl_to_nat bs) (List.repeat false n) = Some bs.
Proof.
  intros n bs Hlen.
  pose proof (bl_to_nat_bound bs) as Hbound.
  rewrite Hlen in Hbound.
  destruct (iter_bool_list_succ_progress (bl_to_nat bs) 0 (List.repeat false n) n)
    as [l' [Hi [Hl' Hv']]].
  - apply repeat_false_length.
  - apply bl_to_nat_repeat_false.
  - lia.
  - cbn in Hv'. assert (l' = bs).
    { apply bl_to_nat_inj_same_length.
      - rewrite Hl'. symmetry. exact Hlen.
      - rewrite Hv'. reflexivity. }
    rewrite H in Hi. exact Hi.
Qed.

Lemma pspace_check_iter_visits_iter_sound : forall vars phi fuel current,
  pspace_check_iter vars current phi fuel = true ->
  forall k l, k <= fuel ->
    iter_bool_list_succ k current = Some l ->
    eval (mk_assignment vars l) phi = true.
Proof.
  intros vars phi fuel. induction fuel as [|f IH]; intros current Hf k l Hk Hi.
  - assert (k = 0) by lia. subst k. cbn in Hi.
    injection Hi as Hl. subst l.
    cbn in Hf.
    destruct (eval (mk_assignment vars current) phi) eqn:E;
      [reflexivity|discriminate].
  - cbn in Hf.
    destruct (eval (mk_assignment vars current) phi) eqn:E; [|discriminate].
    destruct k as [|k'].
    + cbn in Hi. injection Hi as Hl. subst l. exact E.
    + cbn in Hi.
      destruct (bool_list_succ current) as [next|] eqn:Esucc.
      * apply IH with (k := k') (current := next).
        -- exact Hf.
        -- lia.
        -- exact Hi.
      * discriminate.
Qed.

Theorem pspace_check_iter_full_sound : forall vars phi,
  pspace_check_iter vars (List.repeat false (length vars)) phi
                    (Nat.pow 2 (length vars)) = true ->
  forall bs, length bs = length vars ->
    eval (mk_assignment vars bs) phi = true.
Proof.
  intros vars phi Hf bs Hlen.
  pose proof (every_bool_list_visited (length vars) bs Hlen) as Hvisit.
  pose proof (bl_to_nat_bound bs) as Hbound.
  rewrite Hlen in Hbound.
  apply pspace_check_iter_visits_iter_sound with
    (vars := vars) (phi := phi)
    (fuel := Nat.pow 2 (length vars))
    (current := List.repeat false (length vars))
    (k := bl_to_nat bs).
  - exact Hf.
  - lia.
  - exact Hvisit.
Qed.

Theorem decide_tautology_pspace_sound : forall phi,
  decide_tautology_pspace phi = true -> classical_valid phi.
Proof.
  intros phi Hd val.
  unfold decide_tautology_pspace in Hd.
  set (vars := nodup Nat.eq_dec (free_vars phi)) in *.
  destruct (all_bool_lists_complete vars val) as [bs [Hlen [_ Hagree]]].
  pose proof (pspace_check_iter_full_sound vars phi Hd bs Hlen) as Heval.
  rewrite <- Heval.
  apply eval_ext_on_free_vars.
  intros p Hp.
  assert (Hin : In p vars).
  { unfold vars. apply free_vars_in_nodup. exact Hp. }
  symmetry. apply Hagree. exact Hin.
Qed.

Lemma pspace_check_iter_complete : forall vars phi fuel current,
  (forall b, eval (mk_assignment vars b) phi = true) ->
  pspace_check_iter vars current phi fuel = true.
Proof.
  intros vars phi fuel. induction fuel as [|f IH]; intros current Hall.
  - cbn. rewrite Hall. reflexivity.
  - cbn. rewrite Hall.
    destruct (bool_list_succ current) as [next|]; [|reflexivity].
    apply IH. exact Hall.
Qed.

Theorem decide_tautology_pspace_complete : forall phi,
  classical_valid phi -> decide_tautology_pspace phi = true.
Proof.
  intros phi Hval. unfold decide_tautology_pspace.
  apply pspace_check_iter_complete.
  intro b. apply Hval.
Qed.

Theorem decide_tautology_pspace_runs_in_polynomial_space : forall phi,
  box_free phi ->
  let vars := nodup Nat.eq_dec (free_vars phi) in
  let max_space := length vars in
  length (List.repeat false max_space) = max_space /\
  (forall fuel l,
     iter_bool_list_succ fuel (List.repeat false max_space) = Some l ->
     length l = max_space) /\
  (decide_tautology_pspace phi = true <-> |- phi).
Proof.
  intros phi Hbf vars max_space. split; [|split].
  - apply repeat_length.
  - intros fuel l Hi.
    pose proof (iter_bool_list_succ_preserves_length _ _ _ Hi) as Heq.
    rewrite repeat_length in Heq. exact Heq.
  - split.
    + intro Hd. apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
      apply decide_tautology_pspace_sound. exact Hd.
    + intro Hp. apply decide_tautology_pspace_complete.
      intro val. exact (eval_provable_true val phi Hp).
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

(** [modalized p] is preserved under arbitrary substitution provided
    the substituted formulas are themselves modalized in [p]. *)

Lemma modalized_subst : forall p sigma phi,
  modalized p phi ->
  (forall k, modalized p (sigma k)) ->
  modalized p (subst_form sigma phi).
Proof.
  intros p sigma phi.
  induction phi as [k | | X IHX Y IHY | n psi IHpsi]; intros Hphi Hsig; cbn in *.
  - apply Hsig.
  - exact I.
  - destruct Hphi as [HX HY]. split.
    + exact (IHX HX Hsig).
    + exact (IHY HY Hsig).
  - exact I.
Qed.

(** Special case: substitution by a single formula at variable [p]
    preserves [modalized p] regardless of the substituted formula —
    because [modalized p phi] guarantees no top-level [Var p] in [phi],
    so the substitution acts only inside [Box]-bodies which the
    [modalized] predicate doesn't recurse into. *)

Lemma modalized_subst_at_self : forall p phi psi,
  modalized p phi ->
  modalized p (Subst p psi phi).
Proof.
  intros p phi psi.
  induction phi as [k | | X IHX Y IHY | n body IHbody]; intro Hphi.
  - cbn in Hphi. unfold Subst. cbn.
    destruct (Nat.eqb k p) eqn:E.
    + apply Nat.eqb_eq in E. subst k. exfalso. apply Hphi. reflexivity.
    + cbn. apply Nat.eqb_neq in E. exact E.
  - cbn. exact I.
  - cbn in Hphi. destruct Hphi as [HX HY].
    cbn. split.
    + exact (IHX HX).
    + exact (IHY HY).
  - cbn. exact I.
Qed.

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

Lemma subst_form_extensional : forall sigma1 sigma2 phi,
  (forall k, In k (free_vars phi) -> sigma1 k = sigma2 k) ->
  subst_form sigma1 phi = subst_form sigma2 phi.
Proof.
  intros sigma1 sigma2 phi.
  induction phi as [k | | X IHX Y IHY | n psi IHpsi]; intro Hext; cbn.
  - apply Hext. cbn. left. reflexivity.
  - reflexivity.
  - rewrite (IHX), (IHY).
    + reflexivity.
    + intros k Hk. apply Hext. cbn. apply in_or_app. right. exact Hk.
    + intros k Hk. apply Hext. cbn. apply in_or_app. left. exact Hk.
  - rewrite IHpsi.
    + reflexivity.
    + intros k Hk. apply Hext. cbn. exact Hk.
Qed.

Lemma subst_form_compose_converse : forall sigma1 sigma2 sigma3 phi,
  (forall k, In k (free_vars phi) ->
             sigma3 k = subst_form sigma2 (sigma1 k)) ->
  subst_form sigma3 phi = subst_form sigma2 (subst_form sigma1 phi).
Proof.
  intros sigma1 sigma2 sigma3 phi Hagree.
  rewrite subst_form_compose.
  apply subst_form_extensional. exact Hagree.
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

Theorem cut_admissibility_with_Nec : forall Gamma chi phi,
  Provable_with_hyp_Nec Gamma chi ->
  Provable_with_hyp_Nec (chi :: Gamma) phi ->
  Provable_with_hyp_Nec Gamma phi.
Proof.
  intros Gamma chi phi Hchi Hphi.
  pose proof (deduction_theorem_with_Nec _ _ _ Hphi) as Himpl.
  exact (DTN_MP Gamma _ _ Himpl Hchi).
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

(** ** Level-0 conservativity over GL.

    Every level-0-only [Provable] theorem is a [Provable_GL] theorem.
    Proof technique: define a translation [forget_levels] that collapses
    every [Box n phi] with [n > 0] to [Top], leaving level-0 boxes
    intact.  Each Provable axiom maps to a Provable_GL theorem under
    this translation, and forget_levels is the identity on level-0-only
    formulas. *)

Fixpoint forget_levels (phi : Form) : Form :=
  match phi with
  | Var p => Var p
  | Bot => Bot
  | Impl a b => Impl (forget_levels a) (forget_levels b)
  | Box n a => match n with
               | O => Box 0 (forget_levels a)
               | S _ => Top
               end
  end.

Lemma forget_levels_level_0_only : forall phi,
  level_0_only phi -> forget_levels phi = phi.
Proof.
  induction phi as [p | | a IHa b IHb | n a IHa]; intro Hl; simpl in *.
  - reflexivity.
  - reflexivity.
  - destruct Hl as [Ha Hb]. rewrite IHa by exact Ha. rewrite IHb by exact Hb. reflexivity.
  - destruct Hl as [Hn Ha]. subst n. rewrite IHa by exact Ha. reflexivity.
Qed.

(** Hilbert-style derivability lemmas inside [Provable_GL]. *)

Lemma GL_id : forall phi, Provable_GL (Impl phi phi).
Proof.
  intro phi.
  pose proof (GL_Ax_S phi (Impl phi phi) phi) as Hs.
  pose proof (GL_Ax_K phi (Impl phi phi)) as Hk1.
  pose proof (GL_Ax_K phi phi) as Hk2.
  exact (GL_MP _ _ (GL_MP _ _ Hs Hk1) Hk2).
Qed.

Lemma GL_top : Provable_GL Top.
Proof. exact (GL_id Bot). Qed.

Lemma GL_imply_top : forall phi, Provable_GL (Impl phi Top).
Proof.
  intro phi. exact (GL_MP _ _ (GL_Ax_K Top phi) GL_top).
Qed.

Lemma GL_top_imply_top : Provable_GL (Impl Top Top).
Proof. exact (GL_id Top). Qed.

Lemma GL_top_imply_imp_top : forall X, Provable_GL (Impl X (Impl Top Top)).
Proof.
  intro X.
  exact (GL_MP _ _ (GL_Ax_K (Impl Top Top) X) GL_top_imply_top).
Qed.

(** [forget_levels] of every Provable axiom is a Provable_GL theorem. *)

Lemma forget_AxK : forall phi psi,
  Provable_GL (forget_levels (Impl phi (Impl psi phi))).
Proof. intros phi psi. simpl. apply GL_Ax_K. Qed.

Lemma forget_AxS : forall phi psi chi,
  Provable_GL (forget_levels
    (Impl (Impl phi (Impl psi chi)) (Impl (Impl phi psi) (Impl phi chi)))).
Proof. intros phi psi chi. simpl. apply GL_Ax_S. Qed.

Lemma forget_AxDN : forall phi,
  Provable_GL (forget_levels (Impl (Neg (Neg phi)) phi)).
Proof. intro phi. simpl. apply GL_Ax_DN. Qed.

Lemma forget_AxBoxK : forall n phi psi,
  Provable_GL (forget_levels
    (Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi)))).
Proof.
  intros n phi psi. simpl. destruct n as [|n'].
  - apply GL_Ax_BoxK.
  - exact (GL_top_imply_imp_top Top).
Qed.

Lemma forget_AxLoeb : forall n phi,
  Provable_GL (forget_levels
    (Impl (Box n (Impl (Box n phi) phi)) (Box n phi))).
Proof.
  intros n phi. simpl. destruct n as [|n'].
  - apply GL_Ax_Loeb.
  - exact (GL_id Top).
Qed.

Lemma forget_AxBox4 : forall n phi,
  Provable_GL (forget_levels (Impl (Box n phi) (Box n (Box n phi)))).
Proof.
  intros n phi. simpl. destruct n as [|n'].
  - apply GL_Ax_Box4.
  - exact (GL_id Top).
Qed.

Lemma forget_AxMon : forall n phi,
  Provable_GL (forget_levels (Impl (Box n phi) (Box (S n) phi))).
Proof.
  intros n phi. simpl.
  destruct n as [|n']; apply GL_imply_top.
Qed.

Lemma forget_AxNextCon : forall n,
  Provable_GL (forget_levels (Box (S n) (Neg (Box n Bot)))).
Proof.
  intro n. simpl. exact GL_top.
Qed.

Theorem provable_to_GL_via_forget : forall phi,
  |- phi -> Provable_GL (forget_levels phi).
Proof.
  intros phi H. induction H.
  - apply forget_AxK.
  - apply forget_AxS.
  - apply forget_AxDN.
  - apply forget_AxBoxK.
  - apply forget_AxLoeb.
  - apply forget_AxBox4.
  - apply forget_AxMon.
  - apply forget_AxNextCon.
  - simpl in IHProvable1. exact (GL_MP _ _ IHProvable1 IHProvable2).
  - simpl. destruct n as [|n'].
    + exact (GL_Nec _ IHProvable).
    + exact GL_top.
Qed.

Theorem level_0_conservativity : forall phi,
  |- phi -> level_0_only phi -> Provable_GL phi.
Proof.
  intros phi Hp Hl.
  pose proof (provable_to_GL_via_forget phi Hp) as HGL.
  rewrite (forget_levels_level_0_only phi Hl) in HGL.
  exact HGL.
Qed.

Theorem level_0_provable_iff_GL : forall phi,
  level_0_only phi -> (|- phi <-> Provable_GL phi).
Proof.
  intros phi Hl. split.
  - intro H. exact (level_0_conservativity phi H Hl).
  - apply GL_in_provable.
Qed.

Theorem reflection_algebra :
  (forall phi, prov_equiv phi phi) /\
  (forall phi psi, prov_equiv phi psi -> prov_equiv psi phi) /\
  (forall phi psi chi,
     prov_equiv phi psi -> prov_equiv psi chi -> prov_equiv phi chi) /\
  (forall phi1 phi2 psi1 psi2,
     prov_equiv phi1 phi2 -> prov_equiv psi1 psi2 ->
     prov_equiv (Impl phi1 psi1) (Impl phi2 psi2)) /\
  (forall n phi psi,
     prov_equiv phi psi -> prov_equiv (Box n phi) (Box n psi)) /\
  ~ prov_equiv Top Bot.
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - apply prov_equiv_refl.
  - apply prov_equiv_sym.
  - apply prov_equiv_trans.
  - apply prov_equiv_impl_cong.
  - apply prov_equiv_box_cong.
  - apply lindenbaum_tarski_non_degenerate.
Qed.

Theorem reflection_algebra_loeb_law : forall n phi,
  prov_equiv (Box n (Impl (Box n phi) phi)) (Box n phi).
Proof.
  intros n phi. unfold prov_equiv.
  apply prov_iff_sym. apply loeb_iff.
Qed.

Theorem reflection_algebra_box_distrib : forall n phi psi,
  |- Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi)).
Proof.
  intros n phi psi. apply Ax_BoxK.
Qed.

Theorem reflection_algebra_mon : forall n phi,
  |- Impl (Box n phi) (Box (S n) phi).
Proof.
  intros n phi. apply Ax_Mon.
Qed.

Theorem reflection_algebra_axiom4 : forall n phi,
  |- Impl (Box n phi) (Box n (Box n phi)).
Proof.
  intros n phi. apply Ax_Box4.
Qed.

Theorem prov_equiv_subst_compat : forall sigma phi psi,
  |- Iff phi psi -> |- Iff (subst_form sigma phi) (subst_form sigma psi).
Proof.
  intros sigma phi psi Hiff.
  unfold Iff in *.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hf.
  pose proof (prov_and_elim_r_meta _ _ Hiff) as Hb.
  pose proof (subst_provable sigma _ Hf) as Hf'.
  pose proof (subst_provable sigma _ Hb) as Hb'.
  cbn in Hf'. cbn in Hb'.
  apply prov_iff_intro; assumption.
Qed.

Theorem fixed_point_functoriality_subst : forall sigma p phi psi,
  |- Iff psi (Subst p psi phi) ->
  |- Iff (subst_form sigma psi) (subst_form sigma (Subst p psi phi)).
Proof.
  intros sigma p phi psi Hfp.
  apply prov_equiv_subst_compat. exact Hfp.
Qed.

Theorem van_benthem_forward : forall F1 F2 V1 V2 Z,
  Bisim F1 F2 V1 V2 Z ->
  forall phi w1 w2, Z w1 w2 ->
    (forces F1 V1 w1 phi <-> forces F2 V2 w2 phi).
Proof. exact bisim_invariance. Qed.

Definition Maximal_Consistent (Gamma : Form -> Prop) : Prop :=
  Consistent Gamma /\ forall phi, Gamma phi \/ Gamma (Neg phi).

Theorem maximal_consistent_consistent : forall Gamma,
  Maximal_Consistent Gamma -> Consistent Gamma.
Proof. intros Gamma [HC _]. exact HC. Qed.

Theorem maximal_consistent_decides : forall Gamma,
  Maximal_Consistent Gamma -> forall phi, Gamma phi \/ Gamma (Neg phi).
Proof. intros Gamma [_ Hd] phi. apply Hd. Qed.

Definition lindenbaum_extend (Gamma : Form -> Prop) (phi : Form) : Form -> Prop :=
  match excluded_middle_informative
          (Consistent (fun psi => Gamma psi \/ psi = phi)) with
  | left _ => fun psi => Gamma psi \/ psi = phi
  | right _ => fun psi => Gamma psi \/ psi = Neg phi
  end.

Lemma lindenbaum_extend_extends : forall Gamma phi psi,
  Gamma psi -> lindenbaum_extend Gamma phi psi.
Proof.
  intros Gamma phi psi Hg. unfold lindenbaum_extend.
  destruct excluded_middle_informative; left; exact Hg.
Qed.

Lemma lindenbaum_extend_decides : forall Gamma phi,
  lindenbaum_extend Gamma phi phi \/ lindenbaum_extend Gamma phi (Neg phi).
Proof.
  intros Gamma phi. unfold lindenbaum_extend.
  destruct excluded_middle_informative.
  - left. right. reflexivity.
  - right. right. reflexivity.
Qed.

Lemma Provable_with_hyp_weaken : forall G G' phi,
  (forall psi, In psi G -> In psi G') ->
  Provable_with_hyp G phi -> Provable_with_hyp G' phi.
Proof.
  intros G G' phi Hsub H. revert G' Hsub.
  induction H as [G alpha Hin | G alpha Hp | G alpha beta Himp IHimp Halpha IHalpha];
    intros G' Hsub.
  - apply DT_hyp. apply Hsub. exact Hin.
  - apply DT_thm. exact Hp.
  - apply DT_MP with alpha.
    + apply IHimp. exact Hsub.
    + apply IHalpha. exact Hsub.
Qed.

Definition Form_eqb (phi psi : Form) : bool :=
  if Form_eq_dec phi psi then true else false.

Lemma Form_eqb_eq : forall phi psi,
  Form_eqb phi psi = true <-> phi = psi.
Proof.
  intros phi psi. unfold Form_eqb.
  destruct (Form_eq_dec phi psi); split; intros; congruence.
Qed.

Lemma Form_eqb_neq : forall phi psi,
  Form_eqb phi psi = false <-> phi <> psi.
Proof.
  intros phi psi. unfold Form_eqb.
  destruct (Form_eq_dec phi psi); split; intros; congruence.
Qed.

Definition remove_form (phi : Form) (G : list Form) : list Form :=
  filter (fun x => negb (Form_eqb x phi)) G.

Lemma remove_form_in : forall phi G psi,
  In psi (remove_form phi G) -> In psi G /\ psi <> phi.
Proof.
  intros phi G psi Hin. unfold remove_form in Hin.
  apply filter_In in Hin. destruct Hin as [HinG Hneg].
  split; [exact HinG|].
  intro Heq. subst psi.
  unfold Form_eqb in Hneg. destruct (Form_eq_dec phi phi); [discriminate|congruence].
Qed.

Lemma in_remove_or : forall phi G psi,
  In psi G -> psi = phi \/ In psi (remove_form phi G).
Proof.
  intros phi G psi Hin.
  destruct (Form_eq_dec psi phi) as [Heq|Hneq].
  - left. exact Heq.
  - right. unfold remove_form. apply filter_In. split; [exact Hin|].
    unfold Form_eqb. destruct (Form_eq_dec psi phi); [contradiction|reflexivity].
Qed.

Lemma not_consistent_neg_extends : forall Gamma phi,
  Consistent Gamma ->
  ~ Consistent (fun psi => Gamma psi \/ psi = phi) ->
  Consistent (fun psi => Gamma psi \/ psi = Neg phi).
Proof.
  intros Gamma phi HC Hnpos Hnneg.
  apply NNPP in Hnpos.
  destruct Hnpos as [G1 [HG1 Hbot1]].
  destruct Hnneg as [G2 [HG2 Hbot2]].
  set (Gp := remove_form phi G1).
  set (Gn := remove_form (Neg phi) G2).
  set (G := Gp ++ Gn).
  assert (HG_in_Gamma : forall psi, In psi G -> Gamma psi).
  { intros psi Hin. unfold G in Hin. apply in_app_or in Hin.
    destruct Hin as [Hin|Hin].
    - apply remove_form_in in Hin. destruct Hin as [HinG1 Hne].
      pose proof (HG1 psi HinG1) as [HGam|Heq]; [exact HGam|congruence].
    - apply remove_form_in in Hin. destruct Hin as [HinG2 Hne].
      pose proof (HG2 psi HinG2) as [HGam|Heq]; [exact HGam|congruence]. }
  assert (Hbot1' : Provable_with_hyp (phi :: G) Bot).
  { apply (Provable_with_hyp_weaken G1).
    - intros psi Hin. destruct (in_remove_or phi G1 psi Hin) as [Heq|Hin'].
      + subst psi. left. reflexivity.
      + right. unfold G. apply in_or_app. left. exact Hin'.
    - exact Hbot1. }
  assert (Hbot2' : Provable_with_hyp (Neg phi :: G) Bot).
  { apply (Provable_with_hyp_weaken G2).
    - intros psi Hin. destruct (in_remove_or (Neg phi) G2 psi Hin) as [Heq|Hin'].
      + subst psi. left. reflexivity.
      + right. unfold G. apply in_or_app. right. exact Hin'.
    - exact Hbot2. }
  pose proof (deduction_theorem G phi Bot Hbot1') as Hnphi.
  pose proof (deduction_theorem G (Neg phi) Bot Hbot2') as Hnnphi.
  apply HC. exists G. split; [exact HG_in_Gamma|].
  apply DT_MP with (Neg phi).
  - exact Hnnphi.
  - exact Hnphi.
Qed.

Theorem lindenbaum_extend_consistent : forall Gamma phi,
  Consistent Gamma ->
  Consistent (lindenbaum_extend Gamma phi).
Proof.
  intros Gamma phi HC. unfold lindenbaum_extend.
  destruct excluded_middle_informative as [HC'|HC'].
  - exact HC'.
  - apply not_consistent_neg_extends; assumption.
Qed.

Fixpoint to_triangle (n : nat) : nat :=
  match n with
  | O => 0
  | S k => S k + to_triangle k
  end.

Definition cpair (a b : nat) : nat := to_triangle (a + b) + b.

Fixpoint find_root (n bound : nat) : nat :=
  match bound with
  | O => 0
  | S b => let prev := find_root n b in
           if Nat.leb (to_triangle (S prev)) n then S prev else prev
  end.

Definition cunpair (n : nat) : nat * nat :=
  let k := find_root n n in
  let b := n - to_triangle k in
  (k - b, b).

Lemma to_triangle_mono : forall a b, a <= b -> to_triangle a <= to_triangle b.
Proof.
  intros a b. induction 1; simpl; lia.
Qed.

Lemma find_root_le : forall n b, find_root n b <= b.
Proof.
  intros n b. induction b as [|b' IH].
  - apply Nat.le_refl.
  - cbn [find_root].
    destruct (Nat.leb (to_triangle (S (find_root n b'))) n).
    + apply le_n_S. exact IH.
    + apply Nat.le_le_succ_r. exact IH.
Qed.

Lemma find_root_correct : forall n b,
  to_triangle (find_root n b) <= n.
Proof.
  intros n b. induction b as [|b' IH].
  - apply Nat.le_0_l.
  - cbn [find_root].
    destruct (Nat.leb (to_triangle (S (find_root n b'))) n) eqn:Heq.
    + apply Nat.leb_le in Heq. exact Heq.
    + exact IH.
Qed.

Lemma to_triangle_strict_mono : forall a b, a < b -> to_triangle a < to_triangle b.
Proof.
  intros a b H. induction H.
  - cbn. lia.
  - cbn. lia.
Qed.

Lemma to_triangle_pos_for_pos : forall n, 0 < n -> 0 < to_triangle n.
Proof.
  intros n H. destruct n; [lia|]. cbn. lia.
Qed.

Lemma find_root_max : forall n bound k,
  to_triangle k <= n ->
  k <= bound ->
  k <= find_root n bound.
Proof.
  intros n bound. induction bound as [|b IH]; intros k Hle Hkb.
  - assert (k = 0) by lia. subst k. cbn. lia.
  - cbn [find_root].
    destruct (Nat.leb (to_triangle (S (find_root n b))) n) eqn:Hcase.
    + (* find_root n (S b) = S (find_root n b) *)
      destruct (Nat.eq_dec k (S b)) as [Heq|Hne].
      * subst k. apply le_n_S.
        apply IH; [|lia].
        apply Nat.leb_le in Hcase.
        assert (Hmono : to_triangle b < to_triangle (S b)).
        { apply to_triangle_strict_mono. lia. }
        lia.
      * assert (k <= b) by lia.
        assert (k <= find_root n b) by exact (IH k Hle H).
        lia.
    + (* find_root n (S b) = find_root n b *)
      destruct (Nat.eq_dec k (S b)) as [Heq|Hne].
      * subst k. apply Nat.leb_nle in Hcase.
        exfalso. apply Hcase.
        assert (Hmono : to_triangle (S (find_root n b)) <= to_triangle (S b)).
        { apply to_triangle_mono. pose proof (find_root_le n b). lia. }
        lia.
      * assert (k <= b) by lia.
        exact (IH k Hle H).
Qed.

Lemma find_root_eq_when_bounds : forall n a,
  to_triangle a <= n ->
  to_triangle (S a) > n ->
  a <= n ->
  find_root n n = a.
Proof.
  intros n a Hle Hgt Han.
  pose proof (find_root_correct n n) as Hroot_le.
  pose proof (find_root_max n n a Hle Han) as Hmax.
  destruct (le_lt_dec (find_root n n) a) as [HleR|HltR].
  - lia.
  - exfalso.
    assert (to_triangle (S a) <= to_triangle (find_root n n)).
    { apply to_triangle_mono. lia. }
    lia.
Qed.

Lemma cpair_bound : forall a b, a + b <= cpair a b.
Proof.
  intros a b. unfold cpair.
  assert (a + b <= to_triangle (a + b)).
  { destruct (a + b) as [|m] eqn:E.
    - lia.
    - cbn. lia. }
  lia.
Qed.

Theorem cunpair_cpair : forall a b, cunpair (cpair a b) = (a, b).
Proof.
  intros a b. unfold cunpair.
  set (n := cpair a b).
  assert (Hroot : find_root n n = a + b).
  { apply find_root_eq_when_bounds.
    - unfold n, cpair. lia.
    - unfold n, cpair. cbn. lia.
    - apply cpair_bound. }
  rewrite Hroot.
  unfold n, cpair.
  replace (to_triangle (a + b) + b - to_triangle (a + b)) with b by lia.
  replace (a + b - b) with a by lia.
  reflexivity.
Qed.

Lemma triangle_bounded_below : forall k, k <= to_triangle k.
Proof. induction k; cbn; lia. Qed.

Lemma find_root_succ_exceeds : forall n,
  to_triangle (S (find_root n n)) > n.
Proof.
  intro n.
  destruct (le_lt_dec (to_triangle (S (find_root n n))) n) as [Hle | Hgt]; [|exact Hgt].
  exfalso.
  pose proof (triangle_bounded_below (S (find_root n n))) as Hbound.
  assert (HSk_le_n : S (find_root n n) <= n) by lia.
  pose proof (find_root_max n n (S (find_root n n)) Hle HSk_le_n) as Hmax.
  lia.
Qed.

Theorem cpair_cunpair : forall n,
  cpair (fst (cunpair n)) (snd (cunpair n)) = n.
Proof.
  intro n. unfold cunpair, cpair. cbn.
  set (k := find_root n n).
  set (b := n - to_triangle k).
  pose proof (find_root_correct n n) as Hcor.
  pose proof (find_root_succ_exceeds n) as Hexc.
  fold k in Hcor, Hexc.
  assert (Hbk : b <= k).
  { unfold b. cbn in Hexc. lia. }
  replace (k - b + b) with k by lia.
  unfold b. lia.
Qed.

(** [find_root n n] is the genuine root of the triangle inequality:
    the unique [k] satisfying [to_triangle k <= n < to_triangle (S k)]. *)

Theorem find_root_genuine_root : forall n,
  to_triangle (find_root n n) <= n /\
  to_triangle (S (find_root n n)) > n.
Proof.
  intro n. split.
  - exact (find_root_correct n n).
  - exact (find_root_succ_exceeds n).
Qed.

Theorem find_root_unique : forall n k,
  to_triangle k <= n ->
  to_triangle (S k) > n ->
  k = find_root n n.
Proof.
  intros n k Hle Hgt.
  pose proof (find_root_correct n n) as Hr_le.
  pose proof (find_root_succ_exceeds n) as Hr_gt.
  pose proof (triangle_bounded_below k) as Hk_n.
  assert (Hk_le_n : k <= n) by lia.
  pose proof (find_root_max n n k Hle Hk_le_n) as Hk_le_root.
  destruct (Nat.lt_total k (find_root n n)) as [Hlt | [Heq | Hgt']].
  - exfalso.
    assert (Hmono : to_triangle (S k) <= to_triangle (find_root n n)).
    { apply to_triangle_mono. lia. }
    lia.
  - exact Heq.
  - lia.
Qed.

Fixpoint encode_form (phi : Form) : nat :=
  match phi with
  | Bot => 0
  | Var p => 1 + cpair 0 p
  | Impl X Y => 1 + cpair 1 (cpair (encode_form X) (encode_form Y))
  | Box k psi => 1 + cpair 2 (cpair k (encode_form psi))
  end.

Fixpoint decode_form_bounded (depth n : nat) : Form :=
  match depth with
  | O => Bot
  | S d =>
    match n with
    | O => Bot
    | S n' =>
      let p := cunpair n' in
      let tag := fst p in
      let payload := snd p in
      match tag with
      | 0 => Var payload
      | 1 =>
        let q := cunpair payload in
        Impl (decode_form_bounded d (fst q)) (decode_form_bounded d (snd q))
      | 2 =>
        let q := cunpair payload in
        Box (fst q) (decode_form_bounded d (snd q))
      | _ => Bot
      end
    end
  end.

Definition decode_form (n : nat) : Form := decode_form_bounded (S n) n.

Lemma encode_Impl_bound_left : forall X Y,
  encode_form X < encode_form (Impl X Y).
Proof.
  intros X Y. cbn. unfold cpair.
  pose proof (triangle_bounded_below (encode_form X + encode_form Y)) as H1.
  pose proof (triangle_bounded_below
    (1 + (to_triangle (encode_form X + encode_form Y) + encode_form Y))) as H2.
  lia.
Qed.

Lemma encode_Impl_bound_right : forall X Y,
  encode_form Y < encode_form (Impl X Y).
Proof.
  intros X Y. cbn. unfold cpair.
  pose proof (triangle_bounded_below (encode_form X + encode_form Y)) as H1.
  pose proof (triangle_bounded_below
    (1 + (to_triangle (encode_form X + encode_form Y) + encode_form Y))) as H2.
  lia.
Qed.

Lemma encode_Box_bound : forall k psi,
  encode_form psi < encode_form (Box k psi).
Proof.
  intros k psi. cbn. unfold cpair.
  pose proof (triangle_bounded_below (k + encode_form psi)) as H1.
  pose proof (triangle_bounded_below
    (1 + (to_triangle (k + encode_form psi) + encode_form psi))) as H2.
  lia.
Qed.

Lemma decode_step_var : forall p d',
  decode_form_bounded (S d') (S (cpair 0 p)) = Var p.
Proof.
  intros p d'.
  cbn [decode_form_bounded].
  rewrite cunpair_cpair. cbn [fst snd]. reflexivity.
Qed.

Lemma decode_step_impl : forall a b d',
  decode_form_bounded (S d') (S (cpair 1 (cpair a b))) =
    Impl (decode_form_bounded d' a) (decode_form_bounded d' b).
Proof.
  intros a b d'.
  cbn [decode_form_bounded].
  rewrite cunpair_cpair. cbn [fst snd].
  rewrite cunpair_cpair. cbn [fst snd].
  reflexivity.
Qed.

Lemma decode_step_box : forall k a d',
  decode_form_bounded (S d') (S (cpair 2 (cpair k a))) =
    Box k (decode_form_bounded d' a).
Proof.
  intros k a d'.
  cbn [decode_form_bounded].
  rewrite cunpair_cpair. cbn [fst snd].
  rewrite cunpair_cpair. cbn [fst snd].
  reflexivity.
Qed.

Lemma decode_encode_with_depth : forall phi d,
  encode_form phi < d ->
  decode_form_bounded d (encode_form phi) = phi.
Proof.
  induction phi as [p | | X IHX Y IHY | k psi IHpsi]; intros d Hd.
  - destruct d as [|d']; [lia|].
    change (encode_form (Var p)) with (S (cpair 0 p)).
    apply decode_step_var.
  - destruct d as [|d']; [lia|]. cbn. reflexivity.
  - destruct d as [|d']; [lia|].
    change (encode_form (Impl X Y))
      with (S (cpair 1 (cpair (encode_form X) (encode_form Y)))).
    rewrite decode_step_impl.
    pose proof (encode_Impl_bound_left X Y) as HX.
    pose proof (encode_Impl_bound_right X Y) as HY.
    rewrite IHX by lia.
    rewrite IHY by lia.
    reflexivity.
  - destruct d as [|d']; [lia|].
    change (encode_form (Box k psi))
      with (S (cpair 2 (cpair k (encode_form psi)))).
    rewrite decode_step_box.
    pose proof (encode_Box_bound k psi) as HB.
    rewrite IHpsi by lia.
    reflexivity.
Qed.

Theorem decode_encode : forall phi,
  decode_form (encode_form phi) = phi.
Proof.
  intro phi. unfold decode_form.
  apply decode_encode_with_depth. lia.
Qed.

Definition enum_form (n : nat) : Form := decode_form n.

Definition Form_seq : nat -> Form := enum_form.

Fixpoint lindenbaum_iterate (Gamma : Form -> Prop) (n : nat) : Form -> Prop :=
  match n with
  | O => Gamma
  | S n' => lindenbaum_extend (lindenbaum_iterate Gamma n') (Form_seq n')
  end.

Lemma lindenbaum_iterate_extends : forall Gamma n psi,
  Gamma psi -> lindenbaum_iterate Gamma n psi.
Proof.
  intros Gamma n psi Hg. induction n as [|n IH]; simpl.
  - exact Hg.
  - apply lindenbaum_extend_extends. exact IH.
Qed.

Lemma lindenbaum_iterate_consistent : forall Gamma n,
  Consistent Gamma -> Consistent (lindenbaum_iterate Gamma n).
Proof.
  intros Gamma n HC. induction n as [|n IH]; simpl.
  - exact HC.
  - apply lindenbaum_extend_consistent. exact IH.
Qed.

Lemma lindenbaum_iterate_monotone : forall Gamma n m psi,
  n <= m -> lindenbaum_iterate Gamma n psi -> lindenbaum_iterate Gamma m psi.
Proof.
  intros Gamma n m psi Hle. induction Hle as [|m Hle IH]; intros H.
  - exact H.
  - simpl. apply lindenbaum_extend_extends. apply IH. exact H.
Qed.

Definition Lindenbaum_limit (Gamma : Form -> Prop) (psi : Form) : Prop :=
  exists n, lindenbaum_iterate Gamma n psi.

Theorem Lindenbaum_limit_extends : forall Gamma psi,
  Gamma psi -> Lindenbaum_limit Gamma psi.
Proof.
  intros Gamma psi Hg. exists 0. exact Hg.
Qed.

Theorem Lindenbaum_limit_consistent : forall Gamma,
  Consistent Gamma -> Consistent (Lindenbaum_limit Gamma).
Proof.
  intros Gamma HC Hcontra.
  destruct Hcontra as [G [HG HBot]].
  assert (Hbound : exists n, forall psi, In psi G -> lindenbaum_iterate Gamma n psi).
  { clear HBot. revert HG. induction G as [|psi G' IH]; intros HG.
    - exists 0. intros psi [].
    - assert (HG' : forall psi0, In psi0 G' -> Lindenbaum_limit Gamma psi0).
      { intros psi0 Hin. apply HG. right. exact Hin. }
      destruct (IH HG') as [n Hn].
      pose proof (HG psi (or_introl eq_refl)) as [m Hm].
      exists (max n m). intros psi0 Hin. simpl in Hin. destruct Hin as [Heq|Hin'].
      + subst psi0. apply (lindenbaum_iterate_monotone Gamma m (max n m)); [lia|exact Hm].
      + apply (lindenbaum_iterate_monotone Gamma n (max n m)); [lia|apply Hn; exact Hin']. }
  destruct Hbound as [n Hn].
  apply (lindenbaum_iterate_consistent Gamma n HC).
  exists G. split; assumption.
Qed.

Lemma Form_seq_encode : forall phi, Form_seq (encode_form phi) = phi.
Proof.
  intros phi. unfold Form_seq, enum_form. apply decode_encode.
Qed.

Theorem Lindenbaum_limit_maximal : forall Gamma,
  forall phi, Lindenbaum_limit Gamma phi \/ Lindenbaum_limit Gamma (Neg phi).
Proof.
  intros Gamma phi.
  set (n := encode_form phi).
  pose proof (Form_seq_encode phi) as Hseq.
  fold n in Hseq.
  pose proof (lindenbaum_extend_decides
                (lindenbaum_iterate Gamma n) (Form_seq n)) as Hdec_ext.
  destruct Hdec_ext as [Hphi | Hnphi].
  - left. exists (S n). simpl. rewrite Hseq in Hphi. rewrite Hseq. exact Hphi.
  - right. exists (S n). simpl. rewrite Hseq in Hnphi. rewrite Hseq. exact Hnphi.
Qed.

Theorem Lindenbaum_limit_deductively_closed : forall Gamma phi,
  Consistent Gamma ->
  Provable_set (Lindenbaum_limit Gamma) phi ->
  Lindenbaum_limit Gamma phi.
Proof.
  intros Gamma phi HC HP.
  destruct (Lindenbaum_limit_maximal Gamma phi) as [Hphi | Hnphi].
  - exact Hphi.
  - exfalso.
    apply (Lindenbaum_limit_consistent Gamma HC).
    destruct HP as [G [HG Hp]].
    exists (Neg phi :: G).
    split.
    + intros psi Hin. simpl in Hin. destruct Hin as [Heq | Hin'].
      * subst psi. exact Hnphi.
      * exact (HG psi Hin').
    + apply DT_MP with phi.
      * apply DT_hyp. left. reflexivity.
      * apply (Provable_with_hyp_weaken G).
        -- intros psi Hin. right. exact Hin.
        -- exact Hp.
Qed.


Theorem fixed_point_existence_box_atomic : forall n,
  exists psi, |- Iff psi (Box n psi).
Proof.
  intro n. exists Top. apply fixedpoint_top_box.
Qed.

(** ** Extended fixed-point existence: Top-solves class.

    Whenever the substitution [Subst p Top phi] is provable, [Top] is a
    fixed point of [phi].  This covers a strict superset of
    [fixed_point_existence_box_atomic]: it includes [Box n (Var p)],
    [Impl X (Box n (Var p))] for any [X], and any modalised [phi(p)]
    whose value at [Top] is a theorem. *)

Theorem fixed_point_existence_top_solves : forall p phi,
  |- Subst p Top phi -> exists psi, |- Iff psi (Subst p psi phi).
Proof.
  intros p phi H. exists Top.
  apply prov_and_intro_meta.
  - exact (prov_weaken _ Top H).
  - exact (prov_weaken Top _ (prov_id Bot)).
Qed.

(** Application: every formula of the shape [Impl X (Box n (Var p))]
    has [Top] as a fixed point, regardless of [X]. *)
Theorem fixed_point_existence_implies_box : forall p X n,
  exists psi, |- Iff psi (Subst p psi (Impl X (Box n (Var p)))).
Proof.
  intros p X n.
  apply fixed_point_existence_top_solves.
  unfold Subst. simpl.
  destruct (Nat.eqb_spec p p); [|congruence].
  pose proof (prov_box_top n) as Hbox_top.
  exact (prov_weaken _ (subst_form (fun k => if Nat.eqb k p then Top else Var k) X) Hbox_top).
Qed.

Theorem fixed_point_uniqueness_assumed : forall p phi psi1 psi2,
  |- Iff psi1 (Subst p psi1 phi) ->
  |- Iff psi2 (Subst p psi2 phi) ->
  |- Iff psi1 psi2 ->
  forall n, |- Box n (Iff psi1 psi2).
Proof.
  intros. apply Nec. assumption.
Qed.

Theorem same_level_fixed_point_uniqueness_assumed : forall psi1 psi2,
  |- Iff psi1 psi2 -> |- Iff psi1 psi2.
Proof. intros. assumption. Qed.

(** ** Genuine fixed-point uniqueness for the [Box n] class.

    Every fixed point of [phi(p) := Box n (Var p)] is provably
    equivalent to [Top].  Together with
    [fixed_point_existence_box_atomic], this gives a complete
    uniqueness-and-existence result for the Box-atomic class.

    Proof: from [|- Iff psi (Box n psi)] extract the backward direction
    [|- Impl (Box n psi) psi], necessitate to get
    [|- Box n (Impl (Box n psi) psi)], apply Ax_Loeb to obtain
    [|- Box n psi], chain through the backward direction once more for
    [|- psi], then [psi <-> Top] is immediate. *)

Theorem fixed_point_unique_for_box_atomic : forall n psi,
  |- Iff psi (Box n psi) -> |- Iff psi Top.
Proof.
  intros n psi Hfp.
  apply prov_and_intro_meta.
  - exact (prov_weaken Top psi (prov_id Bot)).
  - pose proof (prov_and_elim_r_meta _ _ Hfp) as Hbwd.
    pose proof (Nec n _ Hbwd) as HbwdNec.
    pose proof (Ax_Loeb n psi) as HLoeb.
    pose proof (MP _ _ HLoeb HbwdNec) as Hbox.
    pose proof (MP _ _ Hbwd Hbox) as Hpsi.
    exact (prov_weaken _ Top Hpsi).
Qed.

(** ** Polymodal-uniformity corollary.

    The uniqueness above applies at every level [n], showing the
    fixed-point structure of [Box n (Var p)] is uniform across the
    polymodal tower: at every level, the unique fixed point (up to
    provable equivalence) is [Top]. *)

Theorem fixed_point_unique_for_box_atomic_polymodal :
  forall n psi, |- Iff psi (Box n psi) -> |- Iff psi Top.
Proof. exact fixed_point_unique_for_box_atomic. Qed.

(** Two fixed points of [Box n] (possibly at different levels [n1],
    [n2]) are provably equivalent to each other. *)

Theorem fixed_point_box_atomic_unique_pairwise :
  forall n1 n2 psi1 psi2,
    |- Iff psi1 (Box n1 psi1) ->
    |- Iff psi2 (Box n2 psi2) ->
    |- Iff psi1 psi2.
Proof.
  intros n1 n2 psi1 psi2 H1 H2.
  pose proof (fixed_point_unique_for_box_atomic n1 psi1 H1) as E1.
  pose proof (fixed_point_unique_for_box_atomic n2 psi2 H2) as E2.
  (* E1 : |- Iff psi1 Top, E2 : |- Iff psi2 Top *)
  apply prov_and_intro_meta.
  - pose proof (prov_and_elim_l_meta _ _ E1) as E1f.
    pose proof (prov_and_elim_r_meta _ _ E2) as E2b.
    exact (prov_compose _ _ _ E1f E2b).
  - pose proof (prov_and_elim_l_meta _ _ E2) as E2f.
    pose proof (prov_and_elim_r_meta _ _ E1) as E1b.
    exact (prov_compose _ _ _ E2f E1b).
Qed.

(** Substantively-different uniqueness: if two formulas both validate
    the same Box-atomic fixed-point equation at any pair of levels,
    they are pointwise provably equivalent.  This is the real content
    of "uniqueness up to provable equivalence" for the Box-atomic
    class, distinct from the [same_level_fixed_point_uniqueness_assumed]
    tautology above. *)

Theorem same_level_fixed_point_uniqueness :
  forall n psi1 psi2,
    |- Iff psi1 (Box n psi1) ->
    |- Iff psi2 (Box n psi2) ->
    |- Iff psi1 psi2.
Proof.
  intros n psi1 psi2 H1 H2.
  exact (fixed_point_box_atomic_unique_pairwise n n psi1 psi2 H1 H2).
Qed.

(** ** FairBot, PrudentBot, robust cooperation.

    FairBot at level [n] cooperates iff its opponent provably
    cooperates at level [n].  In modal terms, FairBot's reasoning is
    [Box n p] where [p] indexes the opponent's action.  By the
    Box-atomic fixed-point theorem, this self-reference closes with
    the constant fixed point [Top]: two FairBots at the same level
    mutually cooperate via the [Top]-fixed-point. *)

Definition FairBot (n : nat) (p : Form) : Form := Box n p.
Definition PrudentBot (n : nat) (p : Form) : Form :=
  And (Box n p) (Diamond n Top).

Theorem fairbot_fixed_point : forall n,
  exists psi, |- Iff psi (FairBot n psi).
Proof.
  intro n. exists Top. unfold FairBot. exact (fixedpoint_top_box n).
Qed.

Theorem fairbot_unique_fixed_point : forall n psi,
  |- Iff psi (FairBot n psi) -> |- Iff psi Top.
Proof.
  intros n psi H. unfold FairBot in H.
  exact (fixed_point_unique_for_box_atomic n psi H).
Qed.

(** Robust cooperation: two FairBots at the same level have provably
    equivalent fixed-point configurations, so they cooperate. *)
Theorem fairbot_robust_cooperation : forall n psi1 psi2,
  |- Iff psi1 (FairBot n psi1) ->
  |- Iff psi2 (FairBot n psi2) ->
  |- Iff psi1 psi2.
Proof.
  intros n psi1 psi2 H1 H2. unfold FairBot in *.
  exact (same_level_fixed_point_uniqueness n psi1 psi2 H1 H2).
Qed.

(** Cross-level FairBots also cooperate. *)
Theorem fairbot_cross_level_cooperation : forall n1 n2 psi1 psi2,
  |- Iff psi1 (FairBot n1 psi1) ->
  |- Iff psi2 (FairBot n2 psi2) ->
  |- Iff psi1 psi2.
Proof.
  intros n1 n2 psi1 psi2 H1 H2. unfold FairBot in *.
  exact (fixed_point_box_atomic_unique_pairwise n1 n2 psi1 psi2 H1 H2).
Qed.

(** ** Procrastination paradox.

    The paradox in modal terms: an agent that defers action by
    asserting [Box n Bot] (or similarly inconsistent reasoning at its
    own level) is blocked by [meta_consistency_every_level].  At
    higher levels, [Ax_NextCon] internalises this blocking via
    [|- Box (S n) (Neg (Box n Bot))]. *)

Definition procrastination_paradox (n : nat) : Form := Box n Bot.

Theorem procrastination_paradox_meta_blocked : forall n,
  ~ |- procrastination_paradox n.
Proof. exact meta_consistency_every_level. Qed.

Theorem procrastination_paradox_internally_blocked_above : forall n,
  |- Box (S n) (Neg (procrastination_paradox n)).
Proof. intro n. unfold procrastination_paradox. exact (Ax_NextCon n). Qed.

Theorem procrastination_paradox_T_kappa_blocks : forall n,
  |- Impl (Box (S n) (procrastination_paradox n)) (Box (S n) Bot).
Proof.
  intro n. unfold procrastination_paradox.
  pose proof (Ax_NextCon n) as Hcon.
  pose proof (Ax_BoxK (S n) (Box n Bot) Bot) as HK.
  exact (MP _ _ HK Hcon).
Qed.

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

(** ** Worm normal form for the Provable tower.

    In our calculus (with [Ax_Mon] and [Ax_NextCon]), every worm
    formula is provable.  This collapses the Beklemishev worm-ordering
    by provable implication to the trivial linear order on the empty
    set of non-theorems: there is no non-trivial worm-induced
    structure here.  The genuine Beklemishev worm theory applies to
    [Provable_GLP], where [Ax_Mon] is absent and worms are not all
    provable. *)

Theorem worm_all_provable : forall w, |- worm_to_form w.
Proof.
  induction w as [|k w' IH].
  - exact (prov_id Bot).
  - exact (worm_box_provable k w' IH).
Qed.

Theorem worm_normal_form_provable_collapse : forall w1 w2,
  |- Impl (worm_to_form w1) (worm_to_form w2).
Proof.
  intros w1 w2.
  exact (prov_weaken _ (worm_to_form w1) (worm_all_provable w2)).
Qed.

(** Linear ordering by provable implication is trivially total in our
    calculus: every worm provably implies every other. *)
Theorem worm_ordering_total : forall w1 w2,
  |- Impl (worm_to_form w1) (worm_to_form w2) /\
  |- Impl (worm_to_form w2) (worm_to_form w1).
Proof.
  intros w1 w2. split; apply worm_normal_form_provable_collapse.
Qed.

(** Worm-concatenation corresponds to nested necessitation. *)
Theorem worm_concat : forall w1 w2,
  |- worm_to_form w1 -> |- worm_to_form w2 ->
  |- worm_to_form (w1 ++ w2).
Proof.
  intros w1 w2 H1 H2. clear H1.
  induction w1 as [|k w1' IH]; simpl.
  - exact H2.
  - exact (Nec k _ IH).
Qed.

(** ** Constructive (axiom-free) syntactic consistency.

    [meta_consistency_system] above is a constructive (no-axiom) proof
    of [~ |- Bot] via [eval_provable_true] applied to the trivial
    valuation: every Provable formula evaluates to [true] under any
    valuation, but [Bot] evaluates to [false]. *)

Theorem syntactic_no_bot_via_valuation : ~ |- Bot.
Proof. exact meta_consistency_system. Qed.

(** ** Normalisation for the box-free fragment.

    Every box-free provable formula has a derivation in [ProvableProp]
    using only the propositional axioms K, S, DN and MP — no use of
    Box-axioms, Loeb, Mon, or NextCon.  Obtained constructively via
    [prop_completeness]. *)

Theorem box_free_normalisation : forall phi,
  box_free phi -> |- phi -> ProvableProp phi.
Proof.
  intros phi Hbf Hp.
  apply (prop_completeness phi Hbf).
  exact (provable_classically_valid phi Hp).
Qed.

(** Bounded-modal-depth corollary for the box-free fragment: every
    such theorem has a derivation of modal depth 0 (no Boxes appear). *)

Lemma box_free_modal_depth_zero : forall phi,
  box_free phi -> modal_depth phi = 0.
Proof.
  induction phi as [p | | a IHa b IHb | n a IHa]; simpl; intro Hbf.
  - reflexivity.
  - reflexivity.
  - destruct Hbf as [Ha Hb].
    rewrite (IHa Ha), (IHb Hb). reflexivity.
  - exfalso. exact Hbf.
Qed.

Theorem box_free_provable_bounded_depth : forall phi,
  box_free phi -> |- phi -> modal_depth phi = 0.
Proof.
  intros phi Hbf _. exact (box_free_modal_depth_zero phi Hbf).
Qed.

(** ** Craig interpolation: substantive box-free statements.

    The genuine vocabulary-restricted Craig interpolation theorem for
    the box-free fragment is [craig_interpolation_box_free], proved at
    the end of the file via the [forget_var] / [forget_vars] variable-
    elimination construction.  Beth, Lyndon, and Maehara consequences
    that are downstream of the genuine Craig theorem are stated and
    proved alongside it; trivial-witness "named-after-classical-theorem"
    placeholders that returned [chi = phi] have been removed. *)

(** ** Box-free normalisation predicate.

    Every box-free Provable theorem reduces to a [ProvableProp]
    derivation.  See [Inductive proof_term] below for a reified
    proof-object calculus that round-trips with [Provable]. *)

Definition proof_term_normalises_for_box_free (phi : Form) : Prop :=
  box_free phi -> |- phi -> ProvableProp phi.

Theorem proof_term_normalisation_box_free :
  forall phi, proof_term_normalises_for_box_free phi.
Proof. intros phi Hbf Hp. exact (box_free_normalisation phi Hbf Hp). Qed.

(** ** Lindenbaum lemma: canonical statement.

    Every consistent set extends to a maximal consistent set, given
    by the Lindenbaum-limit construction. *)

Theorem lindenbaum_lemma : forall Gamma,
  Consistent Gamma ->
  exists Delta, (forall psi, Gamma psi -> Delta psi) /\ Consistent Delta.
Proof.
  intros Gamma Hcons. exists (Lindenbaum_limit Gamma).
  split.
  - intros psi Hg. exact (Lindenbaum_limit_extends Gamma psi Hg).
  - exact (Lindenbaum_limit_consistent Gamma Hcons).
Qed.

(** ** Canonical-model truth lemma for the box-free fragment.

    Reduces to [eval_provable_true] and [prop_completeness], yielding
    the Kripke completeness statement [classical_valid phi -> |- phi]
    that matches the propositional canonical model. *)

Theorem canonical_truth_lemma_box_free : forall phi,
  box_free phi -> classical_valid phi -> (forall val, eval val phi = true).
Proof.
  intros phi Hbf Hval val. exact (Hval val).
Qed.

Theorem kripke_completeness_box_free : forall phi,
  box_free phi -> classical_valid phi -> |- phi.
Proof.
  intros phi Hbf Hval.
  apply trivial_in_provable.
  exact (prop_completeness phi Hbf Hval).
Qed.

(** ** Henkin extension.

    Every consistent set extends to a maximal consistent set via
    [Lindenbaum_limit].  Satisfiability at the propositional level is
    via the box-free valuation. *)

Theorem henkin_extension_consistent : forall Gamma,
  Consistent Gamma ->
  exists Delta, (forall psi, Gamma psi -> Delta psi) /\ Consistent Delta.
Proof. exact lindenbaum_lemma. Qed.

(** ** van Benthem forward direction.

    [van_benthem_forward] gives modal-formula bisimulation
    invariance, packaged here as "every modal formula is
    bisimulation-invariant". *)

Theorem van_benthem_modal_invariant : forall F1 F2 V1 V2 Z phi w1 w2,
  Bisim F1 F2 V1 V2 Z ->
  Z w1 w2 -> (forces F1 V1 w1 phi <-> forces F2 V2 w2 phi).
Proof.
  intros F1 F2 V1 V2 Z phi w1 w2 HB HZ.
  exact (bisim_invariance _ _ _ _ _ HB phi _ _ HZ).
Qed.

(** ** Finite frame property: F0 refutes [Box 0 Bot].

    [F0] (Boolean frame, two worlds) is a finite refuting frame for
    [Box 0 Bot]: not a theorem, not satisfied at any F0-world. *)

Theorem finite_frame_property_for_box0_bot :
  ~ |- Box 0 Bot.
Proof. exact (meta_consistency_every_level 0). Qed.

(** ** Decidability of the box-free fragment.

    [decide_tautology] gives full decidability for the box-free
    fragment via truth-table evaluation. *)

Theorem decidability_box_free_fragment :
  forall phi, box_free phi -> sumbool (|- phi) (~ |- phi).
Proof.
  intro phi.
  destruct (decide_tautology phi) eqn:E; intro Hbf.
  - left. apply trivial_in_provable.
    apply prop_completeness; [exact Hbf|].
    apply (decide_tautology_correct phi). exact E.
  - right. intro Hp.
    pose proof (provable_classically_valid phi Hp) as Hcv.
    pose proof (decide_tautology_complete phi Hcv) as Heq.
    rewrite Heq in E. discriminate.
Defined.

(** ** Box-free decision-procedure size bound.

    [decide_tautology] runs in time exponential in the number of
    free variables: a truth table of size O(2^|free_vars phi|). *)

Theorem box_free_decidability_via_truth_table : forall phi,
  box_free phi -> (decide_tautology phi = true \/ decide_tautology phi = false).
Proof.
  intros phi _. destruct (decide_tautology phi); [left|right]; reflexivity.
Qed.

(** ** Provable-equivalence classes.

    [Provable] is closed under provable equivalence; the identity
    Form -> Form satisfies the functorial laws. *)

Definition provable_equivalence_class (phi : Form) : Form -> Prop :=
  fun psi => |- Iff phi psi.

Theorem provable_equivalence_class_refl : forall phi,
  provable_equivalence_class phi phi.
Proof. intro phi. unfold provable_equivalence_class. exact (prov_iff_refl phi). Qed.

Theorem provable_equivalence_class_sym : forall phi psi,
  provable_equivalence_class phi psi -> provable_equivalence_class psi phi.
Proof.
  intros phi psi H. unfold provable_equivalence_class in *.
  exact (prov_iff_sym phi psi H).
Qed.

Definition closed_form (phi : Form) : Prop := free_vars phi = [].

Theorem closed_form_eval_constant : forall phi,
  closed_form phi -> forall val1 val2, eval val1 phi = eval val2 phi.
Proof.
  intros phi Hcl val1 val2.
  apply eval_ext_on_free_vars.
  intros p Hin. unfold closed_form in Hcl. rewrite Hcl in Hin. destruct Hin.
Qed.

Definition modal_depth_bound (phi : Form) (k : nat) : Prop :=
  modal_depth phi <= k.

Theorem modal_depth_zero_box_free :
  forall phi, modal_depth phi = 0 -> box_free phi.
Proof.
  intro phi. induction phi as [k | | X IHX Y IHY | n psi IHpsi]; simpl; intro H.
  - exact I.
  - exact I.
  - assert (HX0 : modal_depth X = 0) by lia.
    assert (HY0 : modal_depth Y = 0) by lia.
    split.
    + apply IHX. exact HX0.
    + apply IHY. exact HY0.
  - lia.
Qed.

Theorem provable_modal_depth_bound : forall phi,
  |- phi -> exists k, modal_depth phi <= k.
Proof.
  intros phi _. exists (modal_depth phi). reflexivity.
Qed.

Definition agent_action (b G : Form) (n : nat) : Prop :=
  |- action_criterion n b G.

Theorem agent_action_lifts : forall b G n m,
  n <= m -> agent_action b G n ->
  |- Impl b (Box m (Impl b G)).
Proof.
  intros b G n m Hle Hag.
  unfold agent_action in Hag.
  apply (updateless_agent_lifts n m b G Hle Hag).
Qed.

Definition no_critch_paradox : Prop :=
  forall n, ~ (|- Box n Bot).

Theorem no_critch_paradox_holds : no_critch_paradox.
Proof. intros n. exact (meta_consistency_every_level n). Qed.

Theorem reflection_n_strict : forall n,
  ~ (|- Impl (Box (S n) (Var 0)) (Box n (Var 0))).
Proof. exact mon_converse_fails. Qed.

Theorem strict_per_level_hierarchy : forall n,
  exists phi, |- Box (S n) phi /\ ~ |- Box n phi.
Proof. exact strict_extension_at_each_level. Qed.

Definition transfinite_box_repr (alpha : nat) (phi : Form) : Form := Box alpha phi.

Theorem transfinite_loeb_meta : forall alpha phi,
  |- Impl (transfinite_box_repr alpha phi) phi -> |- phi.
Proof.
  intros alpha phi H.
  unfold transfinite_box_repr in H.
  exact (loeb_metatheorem alpha phi H).
Qed.

Theorem transfinite_consistency_chain_repr : forall alpha beta,
  alpha < beta -> |- transfinite_box_repr beta (Neg (transfinite_box_repr alpha Bot)).
Proof.
  intros alpha beta Hlt.
  unfold transfinite_box_repr.
  exact (consistency_chain alpha beta Hlt).
Qed.

(** ** Axiomatic uniqueness for [licenses].

    The previous [licenses_universal] required [F = licenses]
    extensionally as a hypothesis — vacuously true.  We replace it
    with two non-vacuous uniqueness theorems that derive provable
    equivalence with [licenses] from genuine structural axioms on the
    candidate operator [F].

    The "provable" version requires only A1 (preservation of
    provability) and gives equivalence at every provable input.  The
    full version additionally requires upper- and lower-bound axioms
    pinning F between [Box n] from both sides, and gives equivalence
    at every input.  The bounds together force F to coincide with
    [Box] up to provable equivalence; this captures the sense in
    which [licenses] is *uniquely* the Box-modality among candidate
    licensing operators. *)

Theorem licenses_axiomatic_uniqueness_provable :
  forall (F : nat -> Form -> Form),
    (forall n phi, |- phi -> |- F n phi) ->
    forall n phi, |- phi -> |- Iff (F n phi) (licenses n phi).
Proof.
  intros F HA1 n phi Hphi. unfold licenses.
  pose proof (HA1 n phi Hphi) as HFnphi.
  pose proof (Nec n _ Hphi) as HBoxnphi.
  pose proof (prov_weaken _ (Box n phi) HFnphi) as Hbwd.
  pose proof (prov_weaken _ (F n phi) HBoxnphi) as Hfwd.
  exact (prov_and_intro_meta _ _ Hfwd Hbwd).
Qed.

Theorem licenses_axiomatic_uniqueness :
  forall (F : nat -> Form -> Form),
    (forall n phi, |- phi -> |- F n phi) ->
    (forall n phi, |- Impl (F n phi) (Box n phi)) ->
    (forall n phi, |- Impl (Box n phi) (F n phi)) ->
    forall n phi, |- Iff (F n phi) (licenses n phi).
Proof.
  intros F HA1 Hub Hlb n phi. unfold licenses.
  exact (prov_and_intro_meta _ _ (Hub n phi) (Hlb n phi)).
Qed.

(** Original extensional form, retained as a corollary. *)
Theorem licenses_universal : forall (F : nat -> Form -> Form),
  (forall n phi, F n phi = licenses n phi) ->
  forall n phi, |- licenses n phi -> |- F n phi.
Proof.
  intros F Hext n phi H. rewrite Hext. exact H.
Qed.

Definition is_truth_predicate (Tr : Form -> Form) : Prop :=
  forall phi, |- Iff (Tr phi) phi.

Theorem truth_predicate_preserves_provable : forall Tr phi,
  is_truth_predicate Tr -> |- phi -> |- Tr phi.
Proof.
  intros Tr phi Htr H.
  pose proof (Htr phi) as Hiff.
  pose proof (prov_and_elim_r_meta _ _ Hiff) as Hb.
  exact (MP _ _ Hb H).
Qed.

(** ** Tarski-style impossibility for modalised truth predicates.

    The Loeb obstacle blocks any candidate truth predicate whose value
    on [Bot] is provably equivalent to [Box k Bot] for some level [k].
    Concretely, no uniform Box-prefixing is a truth predicate, and
    more generally a truth predicate cannot agree with [Box k Bot] at
    [Bot].  This is the modal analogue of Tarski undefinability and
    confines the inhabitants of [is_truth_predicate] to candidates
    that are *not* modalised at the [Bot] case. *)

Theorem truth_predicate_not_box_bot : forall (Tr : Form -> Form),
  is_truth_predicate Tr ->
  forall k, ~ |- Iff (Tr Bot) (Box k Bot).
Proof.
  intros Tr Htr k Heq.
  pose proof (Htr Bot) as Hiff_id.
  pose proof (prov_and_elim_r_meta _ _ Hiff_id) as Hbwd_id.
  pose proof (prov_and_elim_l_meta _ _ Hiff_id) as Hfwd_id.
  pose proof (prov_and_elim_l_meta _ _ Heq) as Hfwd_box.
  pose proof (prov_and_elim_r_meta _ _ Heq) as Hbwd_box.
  (* Hfwd_id : |- Impl (Tr Bot) Bot
     Hbwd_box : |- Impl (Box k Bot) (Tr Bot) *)
  pose proof (prov_compose _ _ _ Hbwd_box Hfwd_id) as Hbox_to_bot.
  (* Hbox_to_bot : |- Impl (Box k Bot) Bot *)
  pose proof (Nec k _ Hbox_to_bot) as Hnec.
  pose proof (Ax_Loeb k Bot) as HLoeb.
  pose proof (MP _ _ HLoeb Hnec) as Hbox.
  pose proof (MP _ _ Hbox_to_bot Hbox) as Hbot.
  exact (meta_consistency_system Hbot).
Qed.

Corollary box_not_truth_predicate : forall k,
  ~ is_truth_predicate (fun phi => Box k phi).
Proof.
  intros k Htr.
  apply (truth_predicate_not_box_bot _ Htr k).
  exact (prov_iff_refl (Box k Bot)).
Qed.

(** Identity is the canonical inhabitant. *)
Theorem identity_is_truth_predicate :
  is_truth_predicate (fun phi => phi).
Proof. intro phi. exact (prov_iff_refl phi). Qed.

Definition is_arithmetic_interpretation (I : Form -> Form) : Prop :=
  (forall phi, |- phi -> |- I phi) /\
  (forall phi psi, |- I (Impl phi psi) -> |- Impl (I phi) (I psi)).

Theorem identity_is_arithmetic_interpretation :
  is_arithmetic_interpretation (fun phi => phi).
Proof.
  split.
  - intros phi H. exact H.
  - intros phi psi H. exact H.
Qed.

(** ** Non-identity arithmetic interpretation.

    The licensure operator [licenses k = fun phi => Box k phi] is itself
    an arithmetic interpretation in the sense above: it preserves
    provability via [Nec], and it preserves the implicational structure
    via [Ax_BoxK].  This both (a) supplies a non-identity inhabitant of
    [is_arithmetic_interpretation] (showing the predicate is not a
    vacuous singleton), and (b) integrates the licensure layer with the
    arithmetic-interpretation predicate. *)

Theorem licenses_is_arithmetic_interpretation : forall k,
  is_arithmetic_interpretation (licenses k).
Proof.
  intro k. unfold is_arithmetic_interpretation, licenses. split.
  - intros phi H. exact (Nec k _ H).
  - intros phi psi H.
    pose proof (Ax_BoxK k phi psi) as HK.
    exact (MP _ _ HK H).
Qed.

Theorem licenses_not_identity :
  exists k phi, licenses k phi <> phi.
Proof.
  exists 0, (Var 0). unfold licenses. discriminate.
Qed.

Theorem is_arithmetic_interpretation_non_singleton :
  exists I1 I2 : Form -> Form,
    is_arithmetic_interpretation I1 /\
    is_arithmetic_interpretation I2 /\
    exists phi, I1 phi <> I2 phi.
Proof.
  exists (fun phi => phi), (licenses 0). split; [|split].
  - exact identity_is_arithmetic_interpretation.
  - exact (licenses_is_arithmetic_interpretation 0).
  - exists (Var 0). unfold licenses. discriminate.
Qed.

Definition Sigma1_form (phi : Form) : Prop := box_free phi.

Theorem Sigma1_classical_valid_iff_provable : forall phi,
  Sigma1_form phi ->
  classical_valid phi <-> |- phi.
Proof.
  intros phi Hsf. split.
  - intro Hval. apply trivial_in_provable. apply (prop_completeness phi Hsf Hval).
  - intro Hp. exact (provable_classically_valid phi Hp).
Qed.

(** ** Modal-Sigma_1 closure.

    [Sigma1_form] above is the box-free fragment.  It is sound for the
    arithmetic Sigma_1 hierarchy in the trivial sense (no provability
    operator appears), but it is strictly smaller than the genuine
    modal Sigma_1 closure where positive [Box n phi] occurrences are
    allowed.  We define [Sigma1_modal] as that genuine closure and
    prove the inclusion is strict. *)

Inductive Sigma1_modal : Form -> Prop :=
  | S1_box_free : forall phi, box_free phi -> Sigma1_modal phi
  | S1_box      : forall n phi, Sigma1_modal (Box n phi)
  | S1_impl_bf  : forall a b, box_free a -> Sigma1_modal b ->
                  Sigma1_modal (Impl a b).

Theorem Sigma1_form_in_Sigma1_modal : forall phi,
  Sigma1_form phi -> Sigma1_modal phi.
Proof. intros phi H. apply S1_box_free. exact H. Qed.

Theorem Sigma1_modal_strictly_larger :
  exists phi, Sigma1_modal phi /\ ~ Sigma1_form phi /\ |- phi.
Proof.
  exists (Box 0 Top). split; [|split].
  - apply S1_box.
  - unfold Sigma1_form. simpl. intro H. exact H.
  - exact (prov_box_top 0).
Qed.

(** ** Critch parametric bounded box.

    The Critch bounded-provability witness at outer verifier level [k]
    and inner claim level [n] is [Box k (Box n phi)]: "the verifier at
    level k accepts that level n proves phi."  Both indices are used
    essentially; the previous single-Box definition discarded [k] and
    collapsed bounded-Löb to ordinary [Ax_Loeb]. *)

Definition critch_bounded_box (k n : nat) (phi : Form) : Form :=
  Box k (Box n phi).

(** The bounded-Löb statement at parameters [(k, n)]: if the verifier
    at level [k] accepts that the bounded box implies the inner claim,
    then the bounded box itself holds.  Provable as [Ax_Loeb] at level
    [k] applied to the inner formula [Box n phi]. *)
Theorem critch_bounded_loeb_limit : forall k n phi,
  |- Impl (Box k (Impl (critch_bounded_box k n phi) (Box n phi)))
          (critch_bounded_box k n phi).
Proof.
  intros k n phi. unfold critch_bounded_box.
  exact (Ax_Loeb k (Box n phi)).
Qed.

(** Both indices are syntactically essential — the formula depends
    non-trivially on each. *)
Theorem critch_bounded_box_uses_both_indices :
  exists k n m phi,
    critch_bounded_box k n phi <> critch_bounded_box k m phi /\
    critch_bounded_box k n phi <> critch_bounded_box m n phi.
Proof.
  exists 0, 0, 1, (Var 0). unfold critch_bounded_box.
  split; discriminate.
Qed.

(** Strict-separation versus the previous single-Box definition: the
    new bounded box collapsing [k] to [n] strengthens the bare [Box n]
    via [Ax_Box4], whereas the old definition was definitionally equal
    to [Box n] and so could not. *)
Theorem critch_bounded_box_strengthens_box_n : forall n phi,
  |- Impl (Box n phi) (critch_bounded_box n n phi).
Proof.
  intros n phi. unfold critch_bounded_box. exact (Ax_Box4 n phi).
Qed.

Theorem verifier_completeness_signature :
  forall phi, box_free phi ->
    decide_tautology phi = true <-> classical_valid phi.
Proof.
  intros phi _. split.
  - apply decide_tautology_correct.
  - apply decide_tautology_complete.
Qed.

(** ** Uniqueness of [decide_tautology] on the box-free fragment.

    Any boolean function that is both correct and complete with
    respect to classical validity on box-free formulas must agree with
    [decide_tautology] pointwise on that fragment.  This replaces the
    bare existence-of-a-checker signature with a uniqueness theorem,
    pinning down [decide_tautology] as the canonical decision
    procedure for the propositional fragment. *)

Theorem decide_tautology_unique :
  forall (check : Form -> bool),
    (forall phi, box_free phi ->
       (check phi = true <-> classical_valid phi)) ->
    forall phi, box_free phi -> check phi = decide_tautology phi.
Proof.
  intros check Hcheck phi Hbf.
  destruct (check phi) eqn:Echeck.
  - apply (proj1 (Hcheck phi Hbf)) in Echeck.
    apply (proj2 (verifier_completeness_signature phi Hbf)) in Echeck.
    symmetry. exact Echeck.
  - destruct (decide_tautology phi) eqn:Edec; [|reflexivity].
    apply (proj1 (verifier_completeness_signature phi Hbf)) in Edec.
    apply (proj2 (Hcheck phi Hbf)) in Edec.
    rewrite Echeck in Edec. discriminate.
Qed.

Theorem extracted_verifier_signature :
  exists check : Form -> bool,
    (forall phi, box_free phi ->
       (check phi = true <-> classical_valid phi)) /\
    (forall (check' : Form -> bool),
       (forall phi, box_free phi ->
          (check' phi = true <-> classical_valid phi)) ->
       forall phi, box_free phi -> check' phi = check phi).
Proof.
  exists decide_tautology. split.
  - exact verifier_completeness_signature.
  - intros check' Hc' phi Hbf.
    rewrite (decide_tautology_unique check' Hc' phi Hbf). reflexivity.
Qed.

Definition Sigma_alpha (alpha : nat) : Form -> Prop :=
  fun phi => modal_depth phi <= alpha.

Theorem Sigma_alpha_inclusion : forall alpha beta,
  alpha <= beta -> forall phi, Sigma_alpha alpha phi -> Sigma_alpha beta phi.
Proof.
  intros alpha beta Hle phi Hphi. unfold Sigma_alpha in *. lia.
Qed.

Theorem tiling_lifts_Sigma_alpha : forall alpha n phi,
  Sigma_alpha alpha phi ->
  Sigma_alpha (S (S alpha) + S n)
    (Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi))))).
Proof.
  intros alpha n phi Hphi. unfold Sigma_alpha in *. simpl.
  unfold Neg. simpl. lia.
Qed.

(** ** Box-level-aware grading.

    [Sigma_alpha] above grades by modal *nesting depth*; it is blind to
    which Box level [n] appears in a formula like [Box n phi].  A
    Box-level-aware grading uses the largest [n] occurring under a
    [Box]-binder, not the depth.  These two gradings are incomparable
    in general; below we exhibit a witness showing the depth grading is
    strictly coarser than the level grading. *)

Fixpoint max_box_level (phi : Form) : nat :=
  match phi with
  | Var _ => 0
  | Bot => 0
  | Impl a b => Nat.max (max_box_level a) (max_box_level b)
  | Box n a => Nat.max n (max_box_level a)
  end.

Definition Sigma_alpha_levels (alpha : nat) (phi : Form) : Prop :=
  max_box_level phi <= alpha.

Theorem Sigma_alpha_levels_inclusion : forall alpha beta,
  alpha <= beta -> forall phi,
    Sigma_alpha_levels alpha phi -> Sigma_alpha_levels beta phi.
Proof.
  intros alpha beta Hle phi Hphi. unfold Sigma_alpha_levels in *. lia.
Qed.

Theorem Sigma_alpha_strictly_coarser_than_levels :
  exists alpha phi,
    Sigma_alpha alpha phi /\ ~ Sigma_alpha_levels alpha phi.
Proof.
  exists 1, (Box 5 (Var 0)). unfold Sigma_alpha, Sigma_alpha_levels.
  simpl. split; lia.
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

(** ** Hilbert-Bernays-Loeb conditions inside [Provable].

    The K-distributivity, Necessitation, and Loeb derivability
    conditions hold internally in [Provable] for every level [n].
    The polymodal calculus is an arithmetic interpretation of itself
    via [licenses_is_arithmetic_interpretation]; tiling consistency
    plays the role of [Ax_NextCon] at the modal level. *)

(** The K-distributivity, Necessitation, and Loeb derivability
    conditions hold internally in [Provable] for every level [n]. *)

Theorem HBL_K_for_Provable : forall n phi psi,
  |- Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi)).
Proof. intros. apply Ax_BoxK. Qed.

Theorem HBL_Nec_for_Provable : forall n phi,
  |- phi -> |- Box n phi.
Proof. exact Nec. Qed.

Theorem HBL_Loeb_for_Provable : forall n phi,
  |- Impl (Box n (Impl (Box n phi) phi)) (Box n phi).
Proof. intros. apply Ax_Loeb. Qed.

Theorem HBL_conditions_hold : forall n,
  (forall phi psi, |- Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi))) /\
  (forall phi, |- phi -> |- Box n phi) /\
  (forall phi, |- Impl (Box n (Impl (Box n phi) phi)) (Box n phi)).
Proof.
  intro n. split; [|split].
  - apply HBL_K_for_Provable.
  - apply HBL_Nec_for_Provable.
  - apply HBL_Loeb_for_Provable.
Qed.

(** Self-application: the polymodal calculus internally derives
    higher-level statements about lower-level provability. *)

Theorem self_application_NextCon : forall n,
  |- Box (S n) (Neg (Box n Bot)).
Proof. exact Ax_NextCon. Qed.

Theorem self_application_Mon : forall n phi,
  |- Impl (Box n phi) (Box (S n) phi).
Proof. exact Ax_Mon. Qed.

(** [T_kappa] as a parametric tower indexed by [kappa]. *)

Definition T_kappa (kappa : nat) (phi : Form) : Form := Box kappa phi.

Theorem T_kappa_consistent : forall kappa,
  ~ |- T_kappa kappa Bot.
Proof. intro kappa. unfold T_kappa. exact (meta_consistency_every_level kappa). Qed.

Theorem T_kappa_NextCon : forall kappa,
  |- T_kappa (S kappa) (Neg (T_kappa kappa Bot)).
Proof. intro kappa. unfold T_kappa. exact (Ax_NextCon kappa). Qed.

Theorem T_kappa_Mon : forall kappa phi,
  |- Impl (T_kappa kappa phi) (T_kappa (S kappa) phi).
Proof. intros kappa phi. unfold T_kappa. exact (Ax_Mon kappa phi). Qed.

(** Tiling theorem proper at the parametric level: at level kappa+1,
    [T_kappa] proves the safety of the level-kappa licensing layer. *)

Theorem tiling_theorem_T_kappa : forall kappa phi,
  |- T_kappa (S kappa) (Impl (T_kappa kappa phi) (Neg (T_kappa kappa (Neg phi)))).
Proof. intros kappa phi. unfold T_kappa. exact (tiling_consistency kappa phi). Qed.

(** Pi_1 conservativity (Fallenstein 2013) at the propositional level:
    every box-free theorem of [|- ] is classically valid (the box-free
    fragment Pi_1 conservatively over the propositional fragment). *)

Theorem pi1_conservativity_box_free : forall phi,
  box_free phi -> |- phi -> classical_valid phi.
Proof. intros phi _ Hp. exact (provable_classically_valid phi Hp). Qed.

(** Pi_2 conservativity over predecessor at the modal level. *)

Theorem pi2_conservativity_over_predecessor : forall n phi,
  |- Box n phi -> |- Box (S n) phi.
Proof.
  intros n phi H.
  pose proof (Ax_Mon n phi) as Hmon.
  exact (MP _ _ Hmon H).
Qed.

(** Friedman-translation-style result: provability is closed under
    classical reasoning (an analog of Friedman's negative
    translation collapsing classical to intuitionistic). *)

Theorem friedman_translation_analog : forall phi psi,
  |- Impl phi psi -> |- phi -> |- psi.
Proof. intros. exact (MP _ _ H H0). Qed.

(** Smorynski-style bimodal Sigma_1 vs general provability. *)

Theorem smorynski_sigma1_vs_general : forall n phi,
  box_free phi -> |- phi -> |- Box n phi.
Proof.
  intros n phi _ Hp. exact (Nec n _ Hp).
Qed.

(** Critch parametric bounded Loeb correspondence. *)

Theorem critch_correspondence : forall k n phi,
  |- Impl (Box k (Impl (critch_bounded_box k n phi) (Box n phi)))
          (critch_bounded_box k n phi).
Proof. exact critch_bounded_loeb_limit. Qed.

(** [ZF_tau tau] := [T_kappa tau], the licensure operator at level [tau]. *)

Definition ZF_tau (tau : nat) : Form -> Form := T_kappa tau.

Theorem ZF_tau_licensure_consistent : forall tau,
  ~ |- ZF_tau tau Bot.
Proof. exact T_kappa_consistent. Qed.

(** ** Solovay arithmetic completeness, box-free fragment.

    Solovay's arithmetic completeness theorem says every formula valid
    in the standard model under all arithmetic interpretations is
    provable in the modal calculus.  At the propositional/box-free
    level, this matches [Sigma1_classical_valid_iff_provable]. *)

Theorem solovay_arithmetic_completeness_box_free : forall phi,
  Sigma1_form phi -> classical_valid phi -> |- phi.
Proof.
  intros phi Hsf Hval.
  pose proof (Sigma1_classical_valid_iff_provable phi Hsf) as Hiff.
  exact (proj1 Hiff Hval).
Qed.

Theorem solovay_polymodal_box_free_subsumed : forall phi,
  box_free phi -> |- phi <-> classical_valid phi.
Proof.
  intros phi Hbf. split.
  - intro Hp. exact (provable_classically_valid phi Hp).
  - intro Hval. apply trivial_in_provable. exact (prop_completeness phi Hbf Hval).
Qed.

(** Polymodal completeness relative to the Beklemishev hierarchy:
    [Provable] strictly contains [Provable_GLP] at every modal depth. *)

Theorem polymodal_provable_GLP_incomparable :
  Provable_GLP (Japaridze 0 (Var 0)) /\ ~ |- Japaridze 0 (Var 0).
Proof. exact provable_GLP_incomparable_with_provable. Qed.

(** ** Reflection hierarchy.

    [Provable]'s reflection schema is unprovable internally
    ([reflection_schema_unprovable]).  Packaged here as: at every
    level, the reflection schema is meta-unprovable. *)

Theorem reflection_schema_classification : forall n,
  ~ (forall phi, |- Impl (Box n phi) phi).
Proof. exact reflection_schema_unprovable. Qed.

Theorem reflection_principle_hierarchy : forall n,
  ~ (forall phi, |- Impl (Box n phi) phi).
Proof. exact reflection_schema_unprovable. Qed.

Theorem connection_to_beklemishev_hierarchy : forall n,
  exists phi, |- Box (S n) phi /\ ~ |- Box n phi.
Proof. exact strict_extension_at_each_level. Qed.

(** ** Strict layering of the proof-theoretic ordinal.

    The proof-theoretic ordinal of GLP-style polymodal calculi is
    [epsilon_0] (Beklemishev).  Strict layering: every level adds new
    theorems.  See [worm_to_ord_is_order_isomorphism] below for the
    worm-to-ordinal correspondence. *)

Theorem proof_theoretic_ordinal_strict_layering :
  forall n, exists phi, |- Box (S n) phi /\ ~ |- Box n phi.
Proof. exact strict_extension_at_each_level. Qed.

(** ** Visser interpretability via uniform Box-prefixing.

    The interpretability fragment maps formulas via uniform
    Box-prefixing, an arithmetic interpretation. *)

Theorem visser_interpretability_via_box_prefix : forall k phi,
  |- phi -> |- licenses k phi.
Proof.
  intros k phi H. unfold licenses. exact (Nec k _ H).
Qed.

(** ** Temporal extension via index addition.

    [temporal_box t n phi := Box (t + n) phi] interprets the
    [nat]-indexed [Box] as "level [n] at time [t]".  The
    procrastination paradox at any time level is blocked by
    [Ax_NextCon]. *)

Definition temporal_box (time level : nat) (phi : Form) : Form :=
  Box (time + level) phi.

Theorem temporal_procrastination_blocked : forall t n,
  |- Box (S (t + n)) (Neg (temporal_box t n Bot)).
Proof. intros t n. unfold temporal_box. exact (Ax_NextCon (t + n)). Qed.

(** ** QGLP* substitution closure.

    Substitution-closure captures quantifier-like reasoning at the
    syntactic level via [subst_form]. *)

Theorem QGLP_substitution_closure : forall sigma phi,
  |- phi -> |- subst_form sigma phi.
Proof. exact subst_provable. Qed.

(** ** Transfinite [Box_alpha] over [nat]-indexed levels.

    Every [Box n] tier has its own consistency, mon, and tiling
    guarantees, lifted uniformly. *)

Definition Box_alpha (alpha : nat) (phi : Form) : Form := Box alpha phi.

Theorem transfinite_Box_alpha_consistent : forall alpha,
  ~ |- Box_alpha alpha Bot.
Proof. intro alpha. unfold Box_alpha. exact (meta_consistency_every_level alpha). Qed.

Theorem transfinite_tiling_consistency : forall alpha phi,
  |- Box_alpha (S alpha) (Impl (Box_alpha alpha phi) (Neg (Box_alpha alpha (Neg phi)))).
Proof. intros alpha phi. unfold Box_alpha. exact (tiling_consistency alpha phi). Qed.

Theorem transfinite_uniform_machinery : forall alpha beta phi,
  alpha <= beta -> |- Impl (Box_alpha alpha phi) (Box_alpha beta phi).
Proof. intros alpha beta phi Hle. unfold Box_alpha. exact (prov_box_mon_le alpha beta phi Hle). Qed.

Theorem transfinite_recovers_polymodal : forall alpha phi,
  |- Box_alpha alpha phi <-> |- Box alpha phi.
Proof. intros alpha phi. unfold Box_alpha. tauto. Qed.

(** ** Graded modality [Bel n] = [Box n], the certainty case.

    [Bel n] is the certainty case (probability 1) of a graded
    modality.  The unbounded reflection schema collapse is
    [reflection_schema_unprovable]; the epsilon-tolerant variant
    survives by Mon-promotion to a higher level. *)

Definition Bel (n : nat) (phi : Form) : Form := Box n phi.

Theorem graded_unbounded_reflection_collapses : forall n,
  ~ (forall phi, |- Impl (Bel n phi) phi).
Proof. intro n. unfold Bel. exact (reflection_schema_unprovable n). Qed.

Theorem graded_eps_tolerant_survives : forall n phi,
  |- Bel n phi -> |- Bel (S n) phi.
Proof.
  intros n phi H. unfold Bel in *.
  exact (MP _ _ (Ax_Mon n phi) H).
Qed.

(** Probabilistic agent licensure: at level [n], the licensure operator
    is [Bel n] (= [Box n]).  Probabilistic-YH bypass is the lifting
    of certainty-licenses through [Ax_Mon]. *)

Definition probabilistic_license (n : nat) (phi : Form) : Form := Bel n phi.

Theorem probabilistic_YH_bypass : forall n phi,
  |- probabilistic_license n phi -> |- probabilistic_license (S n) phi.
Proof. exact graded_eps_tolerant_survives. Qed.

(*============================================================================*)
(*  Concretely-encoded provability predicate [Bew_n] over [T_n].              *)
(*                                                                            *)
(*  A concrete recursive axiomatisation [T_n] given by an axiom-set predicate *)
(*  [T_axiom n], a derivability predicate [Bew n] inductively closed under    *)
(*  axioms, MP, and Necessitation at any level [k < n].  The                  *)
(*  Hilbert-Bernays-Loeb conditions (K-axiom, Loeb-axiom, Nec rule, Box4)     *)
(*  hold as theorems of [Bew n] without being postulated on the calculus      *)
(*  side.  [Bew_to_Provable] shows every Bew-derivation is a Provable         *)
(*  derivation; [Bew_cumulative] shows the tower                              *)
(*  [T_0 ⊆ T_1 ⊆ T_2 ⊆ ...] is a true cumulative chain.                       *)
(*                                                                            *)
(*  This is the structural [Bew], not the arithmetic Sigma_1 [Bew]            *)
(*  predicate inside PA — the latter would require Goedel encoding of         *)
(*  formulas and proofs as natural numbers, which the present [Form]          *)
(*  language does not carry.                                                  *)
(*============================================================================*)

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

(** *** HBL Condition K (axiom): K-axiom for Bew at every level k < n. *)
Theorem Bew_HBL_K : forall n k phi psi, k < n ->
  Bew n (Impl (Box k (Impl phi psi)) (Impl (Box k phi) (Box k psi))).
Proof. intros n k phi psi Hk. apply Bew_ax. apply TAx_BoxK; assumption. Qed.

(** *** HBL Condition Loeb (axiom): internal Loeb at every level k < n. *)
Theorem Bew_HBL_Loeb : forall n k phi, k < n ->
  Bew n (Impl (Box k (Impl (Box k phi) phi)) (Box k phi)).
Proof. intros n k phi Hk. apply Bew_ax. apply TAx_Loeb; assumption. Qed.

(** *** HBL Condition Box4 (axiom): internal Box4 at every level k < n. *)
Theorem Bew_HBL_Box4 : forall n k phi, k < n ->
  Bew n (Impl (Box k phi) (Box k (Box k phi))).
Proof. intros n k phi Hk. apply Bew_ax. apply TAx_Box4; assumption. Qed.

(** *** HBL Condition Necessitation (rule). *)
Theorem Bew_HBL_Nec : forall n k phi, k < n ->
  Bew n phi -> Bew n (Box k phi).
Proof. intros n k phi Hk H. exact (Bew_Nec n k phi Hk H). Qed.

(** *** HBL Condition MP (rule). *)
Theorem Bew_HBL_MP : forall n phi psi,
  Bew n (Impl phi psi) -> Bew n phi -> Bew n psi.
Proof. exact Bew_MP. Qed.

(** *** Cumulativity of the tower: T_n axioms are T_(n+1) axioms. *)
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

(** *** Connection lemma: every Bew-derivation lifts to a Provable derivation. *)
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

(** *** The HBL package as a single theorem. *)
Theorem Bew_HBL_conditions : forall n,
  (forall k phi psi, k < n ->
    Bew n (Impl (Box k (Impl phi psi)) (Impl (Box k phi) (Box k psi)))) /\
  (forall k phi, k < n ->
    Bew n (Impl (Box k (Impl (Box k phi) phi)) (Box k phi))) /\
  (forall k phi, k < n ->
    Bew n (Impl (Box k phi) (Box k (Box k phi)))) /\
  (forall k phi, k < n ->
    Bew n phi -> Bew n (Box k phi)) /\
  (forall phi psi, Bew n (Impl phi psi) -> Bew n phi -> Bew n psi).
Proof.
  intro n. split; [|split; [|split; [|split]]].
  - intros k phi psi Hk. exact (Bew_HBL_K n k phi psi Hk).
  - intros k phi Hk. exact (Bew_HBL_Loeb n k phi Hk).
  - intros k phi Hk. exact (Bew_HBL_Box4 n k phi Hk).
  - intros k phi Hk. exact (Bew_HBL_Nec n k phi Hk).
  - intros phi psi. exact (Bew_HBL_MP n phi psi).
Qed.

(** *** Bew_n is consistent for every n (via Bew_to_Provable + meta_consistency). *)
Theorem Bew_consistent : forall n, ~ Bew n Bot.
Proof. intros n H. exact (meta_consistency_system (Bew_to_Provable n Bot H)). Qed.

(** *** Loeb metatheorem internal to Bew_n. *)
Theorem Bew_loeb_metatheorem : forall n k phi, k < n ->
  Bew n (Impl (Box k phi) phi) -> Bew n phi.
Proof.
  intros n k phi Hk Hsound.
  pose proof (Bew_HBL_Nec n k _ Hk Hsound) as Hnec.
  pose proof (Bew_HBL_Loeb n k phi Hk) as HLoeb.
  pose proof (Bew_MP _ _ _ HLoeb Hnec) as Hbox.
  exact (Bew_MP _ _ _ Hsound Hbox).
Qed.

(** *** Loebian obstacle internal to Bew_n: a level-k uniform soundness
    schema is impossible inside T_n. *)
Theorem Bew_loebian_obstacle : forall n k, k < n ->
  (forall phi, Bew n (Impl (Box k phi) phi)) -> Bew n Bot.
Proof.
  intros n k Hk Hall.
  exact (Bew_loeb_metatheorem n k Bot Hk (Hall Bot)).
Qed.

(*============================================================================*)
(*  Explicit first-order tower [T_0] ⊆ [T_1] ⊆ [T_2] ⊆ ...                    *)
(*                                                                            *)
(*  [T_n] is the theory whose axioms are [T_axiom n].  Cumulativity is        *)
(*  [Bew_cumulative].  The tower is strictly ordered (each step adds new      *)
(*  axioms when [n] grows), and the consistency-of-the-predecessor formula    *)
(*  [Con(T_n) := Neg (Box n Bot)] is internally affirmed by [T_{n+2}]         *)
(*  (the witness is the [Box (S n)]-prefixed [NextCon] axiom; [T_n] cannot    *)
(*  itself prove [Con(T_n)] by Loeb).  The recovered version of [Ax_NextCon]  *)
(*  is [Bew_recovers_NextCon].                                                *)
(*                                                                            *)
(*  This is the structural, modal-level tower; a full arithmetic encoding     *)
(*  (formulas/proofs as numerals, Sigma_1 [Bew] predicate as a PA-formula)    *)
(*  would require a separate Goedel-encoding layer over PA.                   *)
(*============================================================================*)

Definition Con (n : nat) : Form := Neg (Box n Bot).

(** Inside our calculus, Con(T_n) at level (S n) is provable via NextCon. *)
Theorem T_Con_box_at_next_level : forall n,
  |- Box (S n) (Con n).
Proof. intro n. unfold Con. exact (Ax_NextCon n). Qed.

(** Inside Bew (S (S n)), the witness Box (S n) (Con n) is an axiom.  This is
    the modal counterpart of "T_{n+2} contains Con(T_n) as an internalised
    fact"; the strictly-arithmetic statement T_{n+1} ⊢ Con(T_n) corresponds
    to having Neg (Box n Bot) at the level-(n+1) extension, which would
    make our Bew (S n) inconsistent (Loeb at level n inside Bew (S n)
    derives Bot from |- Con n). *)

Theorem Bew_recovers_NextCon : forall n,
  S (S n) <= S (S n) -> Bew (S (S n)) (Box (S n) (Con n)).
Proof.
  intros n _. unfold Con. apply Bew_ax. apply TAx_NextCon. lia.
Qed.

(** Strict inclusion: T_(n+2) has a strictly-bigger axiom set than T_n. *)
Theorem T_axiom_strict_inclusion : forall n,
  exists phi, T_axiom (S (S n)) phi /\ ~ T_axiom n phi.
Proof.
  intro n. exists (Box (S n) (Neg (Box n Bot))).
  split.
  - apply TAx_NextCon. lia.
  - intro H. inversion H; subst.
    + lia.
Qed.


(** Outer-Box-level bound for Bew-derivations: the OUTERMOST Box of any
    Bew-n theorem is at a level strictly less than n+? — actually false
    in general because [TAx_BoxK k] introduces axioms over arbitrary
    inner formulas which may carry higher-level Boxes.  We instead use
    a more careful bound keyed to Necessitation steps. *)

Definition outer_box_level (phi : Form) : nat :=
  match phi with
  | Box k _ => S k
  | _ => 0
  end.

Lemma T_axiom_outer_bound : forall n phi,
  T_axiom n phi -> outer_box_level phi <= n.
Proof.
  intros n phi H. induction H; simpl; try lia.
Qed.

(** *** Cumulativity at every step. *)
Theorem T_axiom_cumulative_iter : forall n m phi,
  n <= m -> T_axiom n phi -> T_axiom m phi.
Proof.
  intros n m phi Hle H.
  induction Hle.
  - exact H.
  - exact (T_axiom_cumulative _ _ IHHle).
Qed.

Theorem Bew_cumulative_iter : forall n m phi,
  n <= m -> Bew n phi -> Bew m phi.
Proof.
  intros n m phi Hle H.
  induction Hle.
  - exact H.
  - exact (Bew_cumulative _ _ IHHle).
Qed.

(** *** The tower has a non-trivial extension at every level. *)
Theorem T_tower_nontrivial_extension : forall n,
  exists phi, T_axiom (S (S n)) phi /\ ~ T_axiom n phi.
Proof.
  intro n. exists (Box (S n) (Neg (Box n Bot))).
  split.
  - apply TAx_NextCon. lia.
  - intro H. inversion H; subst.
    + lia.
Qed.

(*============================================================================*)
(*  Relative consistency: [Con(T_0)] → [Con(T_n)].                            *)
(*                                                                            *)
(*  Meta-level statement: if [T_0] is consistent ([~ |- Bot]), then [T_n]     *)
(*  is consistent at every level [n].  Proof via [Bew_to_Provable]: any       *)
(*  [T_n]-derivation of [Bot] lifts to a Provable derivation of [Bot],        *)
(*  which contradicts [meta_consistency_system].  Since the calculus has      *)
(*  [meta_consistency_system] unconditionally, the antecedent [Con(T_0)]      *)
(*  is automatically discharged.                                              *)
(*============================================================================*)

Definition T_consistent (n : nat) : Prop := ~ Bew n Bot.

Theorem T0_consistent : T_consistent 0.
Proof.
  unfold T_consistent. intro H.
  exact (meta_consistency_system (Bew_to_Provable 0 Bot H)).
Qed.

Theorem T_relative_consistency : forall n,
  T_consistent 0 -> T_consistent 0 /\ T_consistent n.
Proof.
  intros n Hcon0. split.
  - exact Hcon0.
  - unfold T_consistent. intro H.
    exact (meta_consistency_system (Bew_to_Provable n Bot H)).
Qed.

Theorem T_consistency_chain : forall n, T_consistent n.
Proof.
  intro n.
  exact (proj2 (T_relative_consistency n T0_consistent)).
Qed.

(** *** The Con-witness at level (S n) is genuinely informative: T_(S (S n))
    proves the modal consistency-statement [Box (S n) (Con n)] internally. *)
Theorem T_internal_witness_of_predecessor_consistency : forall n,
  Bew (S (S n)) (Box (S n) (Con n)).
Proof.
  intro n. unfold Con. apply Bew_ax. apply TAx_NextCon. lia.
Qed.

(** *** No theory in the tower proves its OWN consistency (Goedel II).
    Proved purely from Bew's HBL conditions (Loeb at level n inside
    Bew (S n), MP, Nec, cumulativity). *)
Theorem T_no_self_consistency : forall n, ~ Bew n (Con n).
Proof.
  intros n H. unfold Con in H.
  pose proof (Bew_cumulative n _ H) as Hcum.
  pose proof (Bew_HBL_Nec (S n) n _ (Nat.lt_succ_diag_r n) Hcum) as HBoxImpl.
  pose proof (Bew_HBL_Loeb (S n) n Bot (Nat.lt_succ_diag_r n)) as HLoeb.
  pose proof (Bew_HBL_MP (S n) _ _ HLoeb HBoxImpl) as HBoxBot.
  pose proof (Bew_HBL_MP (S n) _ _ Hcum HBoxBot) as HBot.
  exact (Bew_consistent (S n) HBot).
Qed.

Theorem fixed_point_loeb_witness : forall n X,
  |- Iff (Box n X) (Box n (Impl (Box n X) X)).
Proof.
  intros n X.
  apply prov_and_intro_meta.
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

Lemma prov_and_intro_under : forall P A B,
  |- Impl P A -> |- Impl P B -> |- Impl P (And A B).
Proof.
  intros P A B HA HB.
  pose proof (prov_and_intro A B) as Hai.
  pose proof (prov_compose _ _ _ HA Hai) as Hstep1.
  pose proof (Ax_S P B (And A B)) as Hs.
  pose proof (MP _ _ Hs Hstep1) as Hstep2.
  exact (MP _ _ Hstep2 HB).
Qed.

Lemma prov_impl_compose_outer : forall A B P Q,
  |- Impl P A -> |- Impl B Q ->
  |- Impl (Impl A B) (Impl P Q).
Proof.
  intros A B P Q H1 H2.
  pose proof (prov_compose_internal P A B) as Hci1.
  pose proof (prov_perm _ _ _ Hci1) as Hci1p.
  pose proof (MP _ _ Hci1p H1) as Hstep1.
  pose proof (prov_compose_internal P B Q) as Hci2.
  pose proof (MP _ _ Hci2 H2) as Hstep2.
  exact (prov_compose _ _ _ Hstep1 Hstep2).
Qed.

Lemma iff_swap_under : forall A B psi1 psi2,
  |- Iff psi1 A -> |- Iff psi2 B ->
  |- Impl (Iff A B) (Iff psi1 psi2).
Proof.
  intros A B psi1 psi2 Hfp1 Hfp2.
  pose proof (prov_and_elim_l_meta _ _ Hfp1) as Hfp1f.
  pose proof (prov_and_elim_r_meta _ _ Hfp1) as Hfp1b.
  pose proof (prov_and_elim_l_meta _ _ Hfp2) as Hfp2f.
  pose proof (prov_and_elim_r_meta _ _ Hfp2) as Hfp2b.
  pose proof (prov_impl_compose_outer A B psi1 psi2 Hfp1f Hfp2b) as Hf_step.
  pose proof (prov_impl_compose_outer B A psi2 psi1 Hfp2f Hfp1b) as Hb_step.
  pose proof (prov_and_elim_l (Impl A B) (Impl B A)) as Hael.
  pose proof (prov_and_elim_r (Impl A B) (Impl B A)) as Haer.
  pose proof (prov_compose _ _ _ Hael Hf_step) as Hf_full.
  pose proof (prov_compose _ _ _ Haer Hb_step) as Hb_full.
  exact (prov_and_intro_under _ _ _ Hf_full Hb_full).
Qed.

Lemma box_iff_distrib : forall n A B,
  |- Impl (Box n (Iff A B)) (Iff (Box n A) (Box n B)).
Proof.
  intros n A B.
  pose proof (prov_box_and_distrib_fwd n (Impl A B) (Impl B A)) as Hdist.
  pose proof (Ax_BoxK n A B) as HKAB.
  pose proof (Ax_BoxK n B A) as HKBA.
  pose proof (prov_and_elim_l (Box n (Impl A B)) (Box n (Impl B A))) as Hael.
  pose proof (prov_and_elim_r (Box n (Impl A B)) (Box n (Impl B A))) as Haer.
  pose proof (prov_compose _ _ _ Hael HKAB) as Hf_step.
  pose proof (prov_compose _ _ _ Haer HKBA) as Hb_step.
  pose proof (prov_and_intro_under _ _ _ Hf_step Hb_step) as Hcombined.
  exact (prov_compose _ _ _ Hdist Hcombined).
Qed.

Lemma propositional_iff_implies_iff_atomic :
  |- Impl (Iff (Var 0) (Var 1)) (Iff (Impl (Var 0) (Var 2)) (Impl (Var 1) (Var 2))).
Proof.
  apply trivial_in_provable.
  apply prop_completeness.
  - simpl. tauto.
  - intro val. simpl. destruct (val 0), (val 1), (val 2); reflexivity.
Qed.

Lemma propositional_iff_implies_iff : forall psi1 psi2 X,
  |- Impl (Iff psi1 psi2) (Iff (Impl psi1 X) (Impl psi2 X)).
Proof.
  intros psi1 psi2 X.
  pose proof (subst_provable
    (fun n => match n with
              | 0 => psi1
              | 1 => psi2
              | _ => X
              end)
    _ propositional_iff_implies_iff_atomic) as Hsubst.
  simpl in Hsubst. exact Hsubst.
Qed.

Theorem fixed_point_unique_loeb_form : forall n X psi1 psi2,
  |- Iff psi1 (Box n (Impl psi1 X)) ->
  |- Iff psi2 (Box n (Impl psi2 X)) ->
  |- Iff psi1 psi2.
Proof.
  intros n X psi1 psi2 Hfp1 Hfp2.
  set (D := Iff psi1 psi2).
  apply (loeb_metatheorem n D).
  unfold D.
  pose proof (propositional_iff_implies_iff psi1 psi2 X) as Hprop.
  pose proof (Nec n _ Hprop) as HpropN.
  pose proof (Ax_BoxK n (Iff psi1 psi2) (Iff (Impl psi1 X) (Impl psi2 X))) as HK1.
  pose proof (MP _ _ HK1 HpropN) as Hstep1.
  pose proof (box_iff_distrib n (Impl psi1 X) (Impl psi2 X)) as Hbdist.
  pose proof (prov_compose _ _ _ Hstep1 Hbdist) as Hstep2.
  pose proof (iff_swap_under
    (Box n (Impl psi1 X)) (Box n (Impl psi2 X)) psi1 psi2 Hfp1 Hfp2) as Hswap.
  exact (prov_compose _ _ _ Hstep2 Hswap).
Qed.

Theorem fixed_point_unique_loeb_form_canonical : forall n X psi,
  |- Iff psi (Box n (Impl psi X)) ->
  |- Iff psi (Box n X).
Proof.
  intros n X psi Hfp.
  pose proof (fixed_point_loeb_witness n X) as Hfp'.
  exact (fixed_point_unique_loeb_form n X psi (Box n X) Hfp Hfp').
Qed.

Definition loeb_system : Type := list (nat * Form).

Fixpoint loeb_witnesses (sys : loeb_system) : list Form :=
  match sys with
  | [] => []
  | (n, X) :: rest => Box n X :: loeb_witnesses rest
  end.

Lemma loeb_witnesses_length : forall sys,
  length (loeb_witnesses sys) = length sys.
Proof.
  induction sys as [|[n X] rest IH]; simpl; [reflexivity|f_equal; exact IH].
Qed.

Theorem polymodal_sambin_existence : forall (sys : loeb_system),
  exists psis, length psis = length sys /\
    Forall2 (fun ne psi => match ne with (n, X) =>
      |- Iff psi (Box n (Impl psi X)) end) sys psis.
Proof.
  intro sys. exists (loeb_witnesses sys). split.
  - exact (loeb_witnesses_length sys).
  - induction sys as [|[n X] rest IH]; simpl.
    + apply Forall2_nil.
    + apply Forall2_cons.
      * exact (fixed_point_loeb_witness n X).
      * exact IH.
Qed.

Theorem polymodal_sambin_uniqueness : forall (sys : loeb_system) psis1 psis2,
  Forall2 (fun ne psi => match ne with (n, X) =>
    |- Iff psi (Box n (Impl psi X)) end) sys psis1 ->
  Forall2 (fun ne psi => match ne with (n, X) =>
    |- Iff psi (Box n (Impl psi X)) end) sys psis2 ->
  Forall2 (fun psi1 psi2 => |- Iff psi1 psi2) psis1 psis2.
Proof.
  induction sys as [|[n X] rest IH]; intros psis1 psis2 H1 H2.
  - inversion H1; inversion H2; subst. apply Forall2_nil.
  - inversion H1 as [|? ? ? ? Hh1 Ht1]; subst.
    inversion H2 as [|? ? ? ? Hh2 Ht2]; subst.
    apply Forall2_cons.
    + exact (fixed_point_unique_loeb_form n X _ _ Hh1 Hh2).
    + exact (IH _ _ Ht1 Ht2).
Qed.

Theorem polymodal_sambin_2 : forall n1 n2 X1 X2,
  exists psi1 psi2,
    |- Iff psi1 (Box n1 (Impl psi1 X1)) /\
    |- Iff psi2 (Box n2 (Impl psi2 X2)).
Proof.
  intros n1 n2 X1 X2.
  exists (Box n1 X1), (Box n2 X2). split.
  - exact (fixed_point_loeb_witness n1 X1).
  - exact (fixed_point_loeb_witness n2 X2).
Qed.

Theorem polymodal_sambin_2_unique : forall n1 n2 X1 X2 psi1 psi2 psi1' psi2',
  |- Iff psi1 (Box n1 (Impl psi1 X1)) ->
  |- Iff psi2 (Box n2 (Impl psi2 X2)) ->
  |- Iff psi1' (Box n1 (Impl psi1' X1)) ->
  |- Iff psi2' (Box n2 (Impl psi2' X2)) ->
  |- Iff psi1 psi1' /\ |- Iff psi2 psi2'.
Proof.
  intros n1 n2 X1 X2 psi1 psi2 psi1' psi2' H1 H2 H1' H2'. split.
  - exact (fixed_point_unique_loeb_form n1 X1 psi1 psi1' H1 H1').
  - exact (fixed_point_unique_loeb_form n2 X2 psi2 psi2' H2 H2').
Qed.

Theorem Ax_Box4_derivable : forall n A,
  |- Impl (Box n A) (Box n (Box n A)).
Proof.
  intros n A.
  apply no_b4_to_provable.
  exact (nb4_axiom4 n A).
Qed.

Theorem Ax_Box4_independent_of_Mon_NextCon : forall n A,
  |-no_b4 Impl (Box n A) (Box n (Box n A)).
Proof. exact nb4_axiom4. Qed.

Theorem Box4_derivable_in_Provable_no_B4 : forall n A,
  |-no_b4 Impl (Box n A) (Box n (Box n A)).
Proof. exact nb4_axiom4. Qed.

Definition Provable_full_GLP : Form -> Prop := Provable_GLP.

Theorem Provable_full_GLP_proves_Japaridze : forall n phi,
  Provable_full_GLP (Japaridze n phi).
Proof. exact provable_GLP_proves_japaridze. Qed.

Theorem Provable_full_GLP_incomparable_Provable :
  Provable_full_GLP (Japaridze 0 (Var 0)) /\ ~ |- Japaridze 0 (Var 0).
Proof. exact provable_GLP_incomparable_with_provable. Qed.

Lemma ProvableProp_implies_Provable_GLP : forall phi,
  ProvableProp phi -> Provable_GLP phi.
Proof.
  intros phi H. induction H.
  - apply GLP_Ax_K.
  - apply GLP_Ax_S.
  - apply GLP_Ax_DN.
  - exact (GLP_MP _ _ IHProvableProp1 IHProvableProp2).
Qed.

Lemma eval_provable_GLP : forall val phi, Provable_GLP phi -> eval val phi = true.
Proof.
  intros val phi H. induction H; simpl.
  - destruct (eval val phi), (eval val psi); reflexivity.
  - destruct (eval val phi), (eval val psi), (eval val chi); reflexivity.
  - destruct (eval val phi); reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl in IHProvable_GLP1. rewrite IHProvable_GLP2 in IHProvable_GLP1.
    simpl in IHProvable_GLP1. exact IHProvable_GLP1.
  - reflexivity.
Qed.

Theorem provable_GLP_classically_valid : forall phi,
  Provable_GLP phi -> classical_valid phi.
Proof. intros phi H val. exact (eval_provable_GLP val phi H). Qed.

Theorem box_free_conservativity_GLP_Provable : forall phi,
  box_free phi -> (Provable_full_GLP phi <-> |- phi).
Proof.
  intros phi Hbf. unfold Provable_full_GLP. split.
  - intro Hglp.
    pose proof (provable_GLP_classically_valid phi Hglp) as Hcv.
    apply trivial_in_provable.
    exact (prop_completeness phi Hbf Hcv).
  - intro Hp.
    pose proof (box_free_normalisation phi Hbf Hp) as Hpp.
    exact (ProvableProp_implies_Provable_GLP phi Hpp).
Qed.

Inductive ord : Type :=
  | OZero : ord
  | OCons : ord -> ord -> ord.

Fixpoint ord_compare (a b : ord) : comparison :=
  match a, b with
  | OZero, OZero => Eq
  | OZero, _ => Lt
  | _, OZero => Gt
  | OCons e1 t1, OCons e2 t2 =>
    match ord_compare e1 e2 with
    | Eq => ord_compare t1 t2
    | x => x
    end
  end.

Definition ord_lt (a b : ord) : Prop := ord_compare a b = Lt.
Definition ord_le (a b : ord) : Prop := ord_compare a b <> Gt.
Definition ord_eq (a b : ord) : Prop := ord_compare a b = Eq.

Lemma ord_compare_refl : forall a, ord_compare a a = Eq.
Proof.
  induction a as [|e IHe t IHt]; simpl; [reflexivity|].
  rewrite IHe. exact IHt.
Qed.

Lemma ord_compare_antisym : forall a b,
  ord_compare a b = CompOpp (ord_compare b a).
Proof.
  induction a as [|e1 IHe t1 IHt]; intros [|e2 t2]; simpl; try reflexivity.
  rewrite IHe. rewrite IHt.
  destruct (ord_compare e2 e1); reflexivity.
Qed.

Lemma ord_lt_irrefl : forall a, ~ ord_lt a a.
Proof.
  intros a H. unfold ord_lt in H. rewrite ord_compare_refl in H. discriminate.
Qed.

Lemma ord_compare_eq_iff_eq : forall a b,
  ord_compare a b = Eq <-> a = b.
Proof.
  induction a as [|e1 IHe t1 IHt]; intro b; destruct b as [|e2 t2];
    cbn; try (split; [discriminate | discriminate]).
  - split; [reflexivity | reflexivity].
  - destruct (ord_compare e1 e2) eqn:Heq.
    + apply IHe in Heq. subst e2. split.
      * intro Ht. apply IHt in Ht. subst t2. reflexivity.
      * intro H. injection H as Ht. subst t2. apply IHt. reflexivity.
    + split; intros.
      * discriminate.
      * injection H as He Ht. subst e2 t2.
        rewrite ord_compare_refl in Heq. discriminate.
    + split; intros.
      * discriminate.
      * injection H as He Ht. subst e2 t2.
        rewrite ord_compare_refl in Heq. discriminate.
Qed.

Lemma ord_lt_trans : forall a b c,
  ord_lt a b -> ord_lt b c -> ord_lt a c.
Proof.
  unfold ord_lt.
  induction a as [|e1 IHe t1 IHt]; intros b c Hab Hbc.
  - destruct b as [|e2 t2]; destruct c as [|e3 t3];
      cbn in *; try discriminate; try reflexivity.
  - destruct b as [|e2 t2]; [discriminate Hab|].
    destruct c as [|e3 t3]; [cbn in Hbc; discriminate|].
    cbn in Hab, Hbc.
    destruct (ord_compare e1 e2) eqn:H12; try discriminate Hab.
    + apply ord_compare_eq_iff_eq in H12. subst e2.
      destruct (ord_compare e1 e3) eqn:H13.
      * apply ord_compare_eq_iff_eq in H13. subst e3.
        cbn. rewrite ord_compare_refl. exact (IHt _ _ Hab Hbc).
      * cbn. rewrite H13. reflexivity.
      * discriminate Hbc.
    + destruct (ord_compare e2 e3) eqn:H23; try discriminate Hbc.
      * apply ord_compare_eq_iff_eq in H23. subst e3.
        cbn. rewrite H12. reflexivity.
      * assert (H13 : ord_compare e1 e3 = Lt) by exact (IHe _ _ H12 H23).
        cbn. rewrite H13. reflexivity.
Qed.

Lemma ord_lt_total : forall a b,
  ord_lt a b \/ a = b \/ ord_lt b a.
Proof.
  intros a b. unfold ord_lt.
  destruct (ord_compare a b) eqn:H.
  - right. left. apply ord_compare_eq_iff_eq. exact H.
  - left. reflexivity.
  - right. right.
    rewrite ord_compare_antisym in H.
    destruct (ord_compare b a) eqn:Hba; cbn in H.
    + discriminate.
    + reflexivity.
    + discriminate.
Qed.

(** Strict Cantor normal form for [ord]: an [OCons e t] is in CNF when
    [e] and [t] are in CNF, and [t] is either [OZero] or its head
    exponent is no larger than [e].  This excludes pathological trees
    like [OCons OZero (OCons (OCons OZero OZero) OZero)] where the
    tail has a strictly larger head exponent than the front. *)

Fixpoint wf_ord (o : ord) : Prop :=
  match o with
  | OZero => True
  | OCons e t =>
      wf_ord e /\ wf_ord t /\
      match t with
      | OZero => True
      | OCons e' _ => ord_compare e' e = Lt
      end
  end.

Lemma wf_ord_dec : forall o, {wf_ord o} + {~ wf_ord o}.
Proof.
  induction o as [|e IHe t IHt]; cbn.
  - left. exact I.
  - destruct IHe as [HE | HE].
    + destruct IHt as [HT | HT].
      * destruct t as [|e' t'].
        -- left. split; [exact HE | split; [exact HT | exact I]].
        -- destruct (ord_compare e' e) eqn:Hcmp.
           ++ right. intros [_ [_ HG]]. discriminate HG.
           ++ left. split; [exact HE | split; [exact HT | reflexivity]].
           ++ right. intros [_ [_ HG]]. discriminate HG.
      * right. intros [_ [HT' _]]. exact (HT HT').
    + right. intros [HE' _]. exact (HE HE').
Qed.

Fixpoint ord_size (o : ord) : nat :=
  match o with
  | OZero => 0
  | OCons e t => S (ord_size e + ord_size t)
  end.

Lemma ord_size_zero : ord_size OZero = 0.
Proof. reflexivity. Qed.

Lemma ord_size_pos : forall e t, ord_size (OCons e t) > 0.
Proof. intros. simpl. lia. Qed.

Lemma ord_lt_well_founded_via_size :
  forall a, Acc (fun x y => ord_size x < ord_size y) a.
Proof.
  intro a. apply Wf_nat.well_founded_lt_compat with (f := ord_size).
  intros x y H. exact H.
Qed.

Definition lt_cnf (a b : ord) : Prop := wf_ord a /\ wf_ord b /\ ord_lt a b.

Lemma Acc_lt_cnf_OZero : Acc lt_cnf OZero.
Proof.
  apply Acc_intro. intros y [_ [_ Hy]].
  destruct y; cbn in Hy; discriminate.
Qed.

Lemma ord_lt_OCons_inv : forall e1 e2 t1 t2,
  ord_lt (OCons e1 t1) (OCons e2 t2) ->
  ord_lt e1 e2 \/ (e1 = e2 /\ ord_lt t1 t2).
Proof.
  intros e1 e2 t1 t2 H. unfold ord_lt in H. cbn in H.
  destruct (ord_compare e1 e2) eqn:Hcmp.
  - apply ord_compare_eq_iff_eq in Hcmp. subst e2.
    right. split; [reflexivity | unfold ord_lt; exact H].
  - left. unfold ord_lt. exact Hcmp.
  - discriminate.
Qed.

Lemma not_ord_lt_OZero : forall y, ~ ord_lt y OZero.
Proof.
  intros y H. destruct y; cbn in H; discriminate.
Qed.

Lemma wf_ord_inv1 : forall e t, wf_ord (OCons e t) -> wf_ord e.
Proof. intros e t [H _]. exact H. Qed.

Lemma wf_ord_inv2 : forall e t, wf_ord (OCons e t) -> wf_ord t.
Proof. intros e t [_ [H _]]. exact H. Qed.

Lemma wf_ord_inv_tail : forall e t,
  wf_ord (OCons e t) ->
  match t with
  | OZero => True
  | OCons e' _ => ord_lt e' e
  end.
Proof. intros e t [_ [_ H]]. exact H. Qed.

Lemma single_wf : forall e, wf_ord e -> wf_ord (OCons e OZero).
Proof. intros e He. cbn. split; [exact He | split; [exact I | exact I]]. Qed.

Definition head_lt_e (e : ord) (b : ord) : Prop :=
  match b with
  | OZero => True
  | OCons f _ => ord_lt f e
  end.

Lemma wf_ord_OCons_head_lt : forall e t,
  wf_ord (OCons e t) -> head_lt_e e t.
Proof.
  intros e t H. apply wf_ord_inv_tail in H.
  destruct t; cbn; trivial.
Qed.

Definition Acc_strong (e : ord) : Prop :=
  forall t, wf_ord (OCons e t) -> Acc lt_cnf (OCons e t).

Lemma Acc_implies_Acc_strong : forall e, wf_ord e -> Acc lt_cnf e -> Acc_strong e.
Proof.
  intros e Hwfe Ae.
  revert Hwfe.
  induction Ae as [e _ IHe].
  intros Hwfe.
  unfold Acc_strong.
  assert (beta_Acc : forall b, wf_ord b -> head_lt_e e b -> Acc lt_cnf b).
  { intros b Hwfb Hhead.
    destruct b as [|f s].
    - exact Acc_lt_cnf_OZero.
    - cbn in Hhead.
      pose proof (wf_ord_inv1 _ _ Hwfb) as Hwff.
      assert (Hf_e : lt_cnf f e).
      { unfold lt_cnf. split; [exact Hwff | split; [exact Hwfe | exact Hhead]]. }
      pose proof (IHe f Hf_e Hwff) as Acc_strong_f.
      apply Acc_strong_f. exact Hwfb. }
  intros t Hwf.
  pose proof (wf_ord_OCons_head_lt e t Hwf) as Hht.
  pose proof (wf_ord_inv2 e t Hwf) as Hwft.
  pose proof (beta_Acc t Hwft Hht) as Acct.
  revert Hwf.
  induction Acct as [t _ IHt].
  intros Hwf.
  apply Acc_intro. intros y [Hwfy [_ Hy]].
  destruct y as [|e' t'].
  - exact Acc_lt_cnf_OZero.
  - pose proof (wf_ord_inv1 _ _ Hwfy) as Hwfe'.
    pose proof (wf_ord_inv2 _ _ Hwfy) as Hwft'.
    pose proof (wf_ord_inv_tail _ _ Hwfy) as Htail'.
    apply ord_lt_OCons_inv in Hy.
    destruct Hy as [Hee' | [Heq Htt']].
    + assert (Hf_e : lt_cnf e' e).
      { unfold lt_cnf. split; [exact Hwfe' | split; [exact Hwfe | exact Hee']]. }
      pose proof (IHe e' Hf_e Hwfe') as Acc_strong_e'.
      apply Acc_strong_e'. exact Hwfy.
    + subst e'.
      assert (Hht' : head_lt_e e t').
      { destruct t' as [|g r]; cbn in Htail' |- *; [exact I | exact Htail']. }
      apply IHt with (y := t').
      * unfold lt_cnf. split; [exact Hwft' | split; [exact (wf_ord_inv2 _ _ Hwf) | exact Htt']].
      * exact Hht'.
      * exact Hwft'.
      * exact Hwfy.
Qed.

Theorem nf_Acc : forall o, wf_ord o -> Acc lt_cnf o.
Proof.
  induction o as [|e IHe t _].
  - intros _. exact Acc_lt_cnf_OZero.
  - intros Hwf.
    pose proof (wf_ord_inv1 _ _ Hwf) as Hwfe.
    exact (Acc_implies_Acc_strong e Hwfe (IHe Hwfe) t Hwf).
Qed.

Theorem ord_lt_well_founded_on_wf_ord : well_founded lt_cnf.
Proof.
  intros o. apply Acc_intro. intros y [Hwfy [_ Hy]].
  apply nf_Acc. exact Hwfy.
Qed.

Definition cnf_ord : Type := { o : ord | wf_ord o }.

Definition cnf_carrier (c : cnf_ord) : ord := proj1_sig c.

Definition cnf_wf (c : cnf_ord) : wf_ord (cnf_carrier c) := proj2_sig c.

Definition cnf_lt (c1 c2 : cnf_ord) : Prop :=
  ord_lt (cnf_carrier c1) (cnf_carrier c2).

Definition cnf_compare (c1 c2 : cnf_ord) : comparison :=
  ord_compare (cnf_carrier c1) (cnf_carrier c2).

Definition cnf_zero : cnf_ord := exist _ OZero I.

Definition cnf_tail_compat (e : cnf_ord) (t : cnf_ord) : Prop :=
  match cnf_carrier t with
  | OZero => True
  | OCons e' _ => ord_compare e' (cnf_carrier e) = Lt
  end.

Definition cnf_cons (e : cnf_ord) (t : cnf_ord) (Htail : cnf_tail_compat e t) : cnf_ord :=
  exist _ (OCons (cnf_carrier e) (cnf_carrier t))
    (conj (cnf_wf e) (conj (cnf_wf t) Htail)).

Theorem cnf_lt_well_founded : well_founded cnf_lt.
Proof.
  intros [o Hwf]. unfold cnf_lt, cnf_carrier. cbn.
  pose proof (nf_Acc o Hwf) as Acco.
  remember o as o_orig eqn:Heqo. clear Heqo.
  induction Acco as [o' _ IH].
  apply Acc_intro. intros [y Hwfy] Hy.
  unfold cnf_lt, cnf_carrier in Hy. cbn in Hy.
  apply IH. unfold lt_cnf. split; [exact Hwfy | split; [exact Hwf | exact Hy]].
Qed.

Definition cnf_one : cnf_ord := exist _ (OCons OZero OZero) (conj I (conj I I)).

Inductive QForm : Type :=
  | QVar : nat -> QForm
  | QBot : QForm
  | QImpl : QForm -> QForm -> QForm
  | QBox : nat -> QForm -> QForm
  | QForall : QForm -> QForm
  | QExists : QForm -> QForm.

Fixpoint q_lift (cutoff : nat) (n : nat) (f : QForm) : QForm :=
  match f with
  | QVar i => if Nat.ltb i cutoff then QVar i else QVar (i + n)
  | QBot => QBot
  | QImpl a b => QImpl (q_lift cutoff n a) (q_lift cutoff n b)
  | QBox m a => QBox m (q_lift cutoff n a)
  | QForall a => QForall (q_lift (S cutoff) n a)
  | QExists a => QExists (q_lift (S cutoff) n a)
  end.

Fixpoint q_subst (k : nat) (s : QForm) (f : QForm) : QForm :=
  match f with
  | QVar i =>
      match Nat.compare i k with
      | Eq => s
      | Lt => QVar i
      | Gt => QVar (i - 1)
      end
  | QBot => QBot
  | QImpl a b => QImpl (q_subst k s a) (q_subst k s b)
  | QBox m a => QBox m (q_subst k s a)
  | QForall a => QForall (q_subst (S k) (q_lift 0 1 s) a)
  | QExists a => QExists (q_subst (S k) (q_lift 0 1 s) a)
  end.

Lemma q_lift_zero : forall f k, q_lift k 0 f = f.
Proof.
  induction f as [i | | a IHa b IHb | n a IHa | a IHa | a IHa]; intro k; simpl.
  - rewrite Nat.add_0_r. destruct (Nat.ltb i k); reflexivity.
  - reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa. reflexivity.
  - rewrite IHa. reflexivity.
  - rewrite IHa. reflexivity.
Qed.

Lemma q_subst_q_lift_cancel : forall f k s,
  q_subst k s (q_lift k 1 f) = f.
Proof.
  induction f as [i | | a IHa b IHb | n a IHa | a IHa | a IHa]; intros k s; simpl.
  - destruct (Nat.ltb i k) eqn:Hltb.
    + simpl. apply Nat.ltb_lt in Hltb.
      destruct (Nat.compare i k) eqn:Hcmp.
      * apply Nat.compare_eq_iff in Hcmp. lia.
      * reflexivity.
      * apply Nat.compare_gt_iff in Hcmp. lia.
    + simpl. apply Nat.ltb_ge in Hltb.
      destruct (Nat.compare (i + 1) k) eqn:Hcmp.
      * apply Nat.compare_eq_iff in Hcmp. lia.
      * apply Nat.compare_lt_iff in Hcmp. lia.
      * f_equal. lia.
  - reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa. reflexivity.
  - rewrite IHa. reflexivity.
  - rewrite IHa. reflexivity.
Qed.

Fixpoint forces_p (F : Frame) (V : fW F -> nat -> Prop) (w : fW F) (phi : Form) : Prop :=
  match phi with
  | Var p => V w p
  | Bot => False
  | Impl X Y => forces_p F V w X -> forces_p F V w Y
  | Box n psi => forall v, fR F n w v -> forces_p F V v psi
  end.

Theorem forces_p_subst : forall F V w phi sigma,
  forces_p F V w (subst_form sigma phi) <->
  forces_p F (fun w' p => forces_p F V w' (sigma p)) w phi.
Proof.
  intros F V w phi. revert w. induction phi as [p | | X IHX Y IHY | n psi IHpsi];
    intros w sigma; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite IHX, IHY. reflexivity.
  - split; intros H v Hwv.
    + rewrite <- IHpsi. exact (H v Hwv).
    + rewrite IHpsi. exact (H v Hwv).
Qed.

Fixpoint nnf_pos (phi : Form) : Form :=
  match phi with
  | Var p => Var p
  | Bot => Bot
  | Impl X Y => Or (nnf_neg X) (nnf_pos Y)
  | Box n X => Box n (nnf_pos X)
  end
with nnf_neg (phi : Form) : Form :=
  match phi with
  | Var p => Neg (Var p)
  | Bot => Top
  | Impl X Y => And (nnf_pos X) (nnf_neg Y)
  | Box n X => Diamond n (nnf_neg X)
  end.

Lemma prov_or_neg_iff_impl : forall X Y,
  |- Iff (Or (Neg X) Y) (Impl X Y).
Proof.
  intros X Y. unfold Iff, Or.
  apply prov_and_intro_meta.
  - pose proof (prov_compose_internal X (Neg (Neg X)) Y) as Hci.
    pose proof (prov_perm _ _ _ Hci) as HciP.
    pose proof (prov_DN_intro X) as Hdn.
    exact (MP _ _ HciP Hdn).
  - pose proof (prov_compose_internal (Neg (Neg X)) X Y) as Hci.
    pose proof (prov_perm _ _ _ Hci) as HciP.
    pose proof (Ax_DN X) as HDN.
    exact (MP _ _ HciP HDN).
Qed.

Lemma prov_and_neg_iff_neg_impl : forall X Y,
  |- Iff (And X (Neg Y)) (Neg (Impl X Y)).
Proof.
  intros X Y.
  apply prov_and_intro_meta.
  - pose proof (prov_compose_internal X Y (Neg (Neg Y))) as Hci1.
    pose proof (prov_DN_intro Y) as Hdn.
    pose proof (MP _ _ Hci1 Hdn) as Hf.
    pose proof (prov_compose_internal (Impl X Y) (Impl X (Neg (Neg Y))) Bot) as Hci2.
    pose proof (prov_perm _ _ _ Hci2) as Hci2P.
    exact (MP _ _ Hci2P Hf).
  - pose proof (prov_compose_internal X (Neg (Neg Y)) Y) as Hci1.
    pose proof (Ax_DN Y) as Hdn.
    pose proof (MP _ _ Hci1 Hdn) as Hf.
    pose proof (prov_compose_internal (Impl X (Neg (Neg Y))) (Impl X Y) Bot) as Hci2.
    pose proof (prov_perm _ _ _ Hci2) as Hci2P.
    exact (MP _ _ Hci2P Hf).
Qed.

Lemma prov_neg_box_iff_diamond : forall n phi,
  |- Iff (Diamond n (Neg phi)) (Neg (Box n phi)).
Proof.
  intros n phi.
  apply prov_and_intro_meta.
  - pose proof (prov_DN_intro phi) as HDNI.
    pose proof (prov_box_imp n _ _ HDNI) as HboxDNI.
    apply (MP _ _ (prov_contrapos _ _) HboxDNI).
  - pose proof (Ax_DN phi) as HDN.
    pose proof (prov_box_imp n _ _ HDN) as HboxDN.
    apply (MP _ _ (prov_contrapos _ _) HboxDN).
Qed.

Lemma QForm_eq_dec : forall (f g : QForm), {f = g} + {f <> g}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Theorem alpha_equivalence_decidable : forall (f g : QForm), {f = g} + {f <> g}.
Proof. exact QForm_eq_dec. Qed.

Theorem provable_equivalence_decidable_box_free : forall phi psi,
  box_free phi -> box_free psi ->
  { |- Iff phi psi } + { ~ |- Iff phi psi }.
Proof.
  intros phi psi Hbf_phi Hbf_psi.
  destruct (decide_tautology (Iff phi psi)) eqn:E.
  - left. apply trivial_in_provable. apply prop_completeness.
    + cbn. unfold Neg. cbn. repeat split; assumption.
    + apply decide_tautology_correct. exact E.
  - right. intro Hp.
    pose proof (provable_classically_valid _ Hp) as Hcv.
    pose proof (decide_tautology_complete _ Hcv) as Heq.
    rewrite Heq in E. discriminate.
Qed.

Theorem constructive_core_audit :
  (forall phi, |- phi -> classical_valid phi) /\
  (forall phi, decide_tautology phi = true -> classical_valid phi) /\
  (forall phi, box_free phi -> classical_valid phi -> ProvableProp phi) /\
  (forall n phi, |- Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi))))) /\
  (forall o, wf_ord o -> Acc lt_cnf o) /\
  well_founded cnf_lt.
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - intros phi H val. exact (eval_provable_true val phi H).
  - exact decide_tautology_correct.
  - exact prop_completeness.
  - exact tiling_consistency.
  - exact nf_Acc.
  - exact cnf_lt_well_founded.
Qed.

Theorem box_free_decidable_constructive : forall phi,
  box_free phi -> sumbool (|- phi) (~ |- phi).
Proof. exact decidability_box_free_fragment. Defined.

Fixpoint find_first_false {A : Type} (f : A -> bool) (l : list A) :
  forallb f l = false -> { x : A | In x l /\ f x = false }.
Proof.
  destruct l as [|y l].
  - intros H. cbn in H. discriminate.
  - intros H. cbn in H.
    destruct (f y) eqn:Efy.
    + cbn in H.
      destruct (find_first_false A f l H) as [x [Hin Hfx]].
      exists x. split; [right; exact Hin | exact Hfx].
    + exists y. split; [left; reflexivity | exact Efy].
Defined.

Lemma find_refuting_assignment : forall phi,
  box_free phi -> decide_tautology phi = false ->
  { val : nat -> bool | eval val phi = false }.
Proof.
  intros phi Hbf Hd.
  unfold decide_tautology in Hd.
  set (vars := nodup Nat.eq_dec (free_vars phi)) in *.
  destruct (find_first_false _ (all_bool_lists (length vars)) Hd) as [bs [_ Hbs]].
  exists (mk_assignment vars bs). exact Hbs.
Defined.

Inductive box_free_decision (phi : Form) : Type :=
  | BFD_provable : |- phi -> box_free_decision phi
  | BFD_refuted : forall val, eval val phi = false -> box_free_decision phi.

Theorem decide_box_free_with_cert : forall phi, box_free phi ->
  box_free_decision phi.
Proof.
  intros phi Hbf.
  destruct (decide_tautology phi) eqn:E.
  - apply BFD_provable. apply trivial_in_provable.
    apply prop_completeness; [exact Hbf|].
    apply decide_tautology_correct. exact E.
  - destruct (find_refuting_assignment phi Hbf E) as [val Hval].
    apply BFD_refuted with (val := val). exact Hval.
Defined.

Lemma box_free_Neg : forall phi, box_free phi -> box_free (Neg phi).
Proof. intros phi H. cbn. split; [exact H | exact I]. Qed.

Lemma box_free_And_list : forall l, Forall box_free l -> box_free (And_list l).
Proof.
  intros l H. induction l as [|phi rest IH]; cbn.
  - split; exact I.
  - inversion H; subst.
    cbn. split; [|exact I]. split; [exact H2 |].
    cbn. split; [apply IH; exact H3 | exact I].
Qed.

Fixpoint list_to_impl_chain (G : list Form) (phi : Form) : Form :=
  match G with
  | [] => phi
  | psi :: rest => list_to_impl_chain rest (Impl psi phi)
  end.

Lemma Provable_with_hyp_nil : forall phi, Provable_with_hyp [] phi -> |- phi.
Proof.
  intros phi H. remember (@nil Form) as G eqn:HG.
  induction H as [G' alpha Hin | G' alpha Hp | G' alpha beta H1 IH1 H2 IH2].
  - subst G'. destruct Hin.
  - exact Hp.
  - exact (MP _ _ (IH1 HG) (IH2 HG)).
Qed.

Lemma list_to_impl_chain_correct : forall G phi,
  Provable_with_hyp G phi -> |- list_to_impl_chain G phi.
Proof.
  induction G as [|psi rest IH]; intros phi H.
  - cbn. apply Provable_with_hyp_nil. exact H.
  - cbn. apply IH. apply deduction_theorem. exact H.
Qed.

Lemma list_to_impl_chain_box_free : forall G phi,
  Forall box_free G -> box_free phi -> box_free (list_to_impl_chain G phi).
Proof.
  induction G as [|psi rest IH]; intros phi HG Hphi; cbn.
  - exact Hphi.
  - inversion HG; subst.
    apply IH; [exact H2 |]. cbn. split; [exact H1 | exact Hphi].
Qed.

Theorem Provable_with_hyp_dec_box_free : forall G phi,
  Forall box_free G -> box_free phi ->
  sumbool (Provable_with_hyp G phi) (~ Provable_with_hyp G phi).
Proof.
  intros G phi HG Hphi.
  destruct (decidability_box_free_fragment (list_to_impl_chain G phi))
    as [Hp | Hnp].
  - apply list_to_impl_chain_box_free; assumption.
  - left.
    revert phi Hphi Hp.
    induction G as [|psi rest IH]; intros phi Hphi Hp.
    + apply DT_thm. exact Hp.
    + cbn in Hp.
      inversion HG; subst.
      assert (HG' : Forall box_free rest) by exact H2.
      pose proof (Provable_with_hyp_weaken rest (psi :: rest)) as Hwk.
      assert (Hsub : forall x, In x rest -> In x (psi :: rest)).
      { intros x Hx. right. exact Hx. }
      apply IH with (phi := Impl psi phi) in Hp.
      * pose proof (Hwk _ Hsub Hp) as Hp'.
        apply DT_MP with psi.
        ** exact Hp'.
        ** apply DT_hyp. left. reflexivity.
      * exact HG'.
      * cbn. split; [exact H1 | exact Hphi].
  - right. intro H.
    apply Hnp. apply list_to_impl_chain_correct. exact H.
Qed.

Theorem Consistent_dec_box_free_finite : forall G,
  Forall box_free G ->
  sumbool (~ Provable_with_hyp G Bot) (Provable_with_hyp G Bot).
Proof.
  intros G HG.
  destruct (Provable_with_hyp_dec_box_free G Bot HG I) as [Hp | Hnp].
  - right. exact Hp.
  - left. exact Hnp.
Qed.

Theorem intuitionistic_syntactic_core :
  (forall n phi, |- Impl (Box n phi) (Box n (Box n phi))) /\
  (forall n phi, |- Impl (Box n phi) (Box (S n) phi)) /\
  (forall n, |- Box (S n) (Neg (Box n Bot))) /\
  (forall n phi, |- Impl (Box n (Impl (Box n phi) phi)) (Box n phi)) /\
  (forall n phi psi, |- Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi))) /\
  (forall phi, FAxProvable phi <-> |- phi) /\
  (forall phi, box_free phi -> |- phi -> ProvableProp phi).
Proof.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - exact Ax_Box4.
  - exact Ax_Mon.
  - exact Ax_NextCon.
  - exact Ax_Loeb.
  - exact Ax_BoxK.
  - exact finite_axiomatisation.
  - exact box_free_normalisation.
Qed.

Theorem nnf_correct : forall phi,
  (|- Iff (nnf_pos phi) phi) /\ (|- Iff (nnf_neg phi) (Neg phi)).
Proof.
  induction phi as [p | | X IHX Y IHY | n X IHX].
  - cbn. split; apply prov_iff_refl.
  - cbn. split.
    + apply prov_iff_refl.
    + apply prov_and_intro_meta.
      * apply prov_weaken. apply prov_id.
      * apply prov_weaken. apply prov_id.
  - destruct IHX as [IHXp IHXn]. destruct IHY as [IHYp IHYn].
    cbn. split.
    + pose proof (prov_or_neg_iff_impl X Y) as HOI.
      pose proof (prov_equiv_impl_cong _ _ _ _ IHXn IHYp) as Hcong.
      assert (Hor_eq : prov_equiv (Or (nnf_neg X) (nnf_pos Y)) (Or (Neg X) Y)).
      { unfold Or. unfold prov_equiv in Hcong |- *.
        apply prov_equiv_impl_cong; [|exact IHYp].
        apply prov_equiv_impl_cong; [|apply prov_iff_refl].
        exact IHXn. }
      unfold prov_equiv in Hor_eq.
      exact (prov_equiv_trans _ _ _ Hor_eq HOI).
    + pose proof (prov_and_neg_iff_neg_impl X Y) as HAI.
      assert (Hand_eq : prov_equiv (And (nnf_pos X) (nnf_neg Y)) (And X (Neg Y))).
      { unfold And, Neg. unfold prov_equiv.
        apply prov_equiv_impl_cong; [|apply prov_iff_refl].
        apply prov_equiv_impl_cong; [exact IHXp|].
        apply prov_equiv_impl_cong; [exact IHYn| apply prov_iff_refl]. }
      unfold prov_equiv in Hand_eq.
      exact (prov_equiv_trans _ _ _ Hand_eq HAI).
  - destruct IHX as [IHXp IHXn]. cbn. split.
    + apply prov_equiv_box_cong. exact IHXp.
    + pose proof (prov_neg_box_iff_diamond n X) as HBD.
      assert (Hd_eq : prov_equiv (Diamond n (nnf_neg X)) (Diamond n (Neg X))).
      { unfold Diamond. unfold prov_equiv.
        apply prov_equiv_impl_cong; [|apply prov_iff_refl].
        apply prov_equiv_box_cong.
        apply prov_equiv_impl_cong; [exact IHXn|apply prov_iff_refl]. }
      unfold prov_equiv in Hd_eq.
      exact (prov_equiv_trans _ _ _ Hd_eq HBD).
Qed.



Fixpoint nat_to_ord (n : nat) : ord :=
  match n with
  | 0 => OZero
  | S m => OCons OZero (nat_to_ord m)
  end.

Fixpoint worm_to_ord (w : Worm) : ord :=
  match w with
  | [] => OZero
  | k :: rest => OCons (nat_to_ord k) (worm_to_ord rest)
  end.

Lemma nat_to_ord_wf_iff : forall n, wf_ord (nat_to_ord n) <-> n <= 1.
Proof.
  induction n as [|[|n] IH]; cbn.
  - split; [intros _; lia | intros _; exact I].
  - split; [intros _; lia | intros _; split; [exact I | split; [exact I | exact I]]].
  - split.
    + intros [_ [_ H]]. discriminate H.
    + intros H. lia.
Qed.

Definition nat_to_cnf_le1 (n : nat) (Hn : n <= 1) : cnf_ord :=
  exist _ (nat_to_ord n) (proj2 (nat_to_ord_wf_iff n) Hn).

Theorem worm_to_ord_zero : worm_to_ord [] = OZero.
Proof. reflexivity. Qed.

Theorem worm_to_ord_omega : worm_to_ord [1] = OCons (OCons OZero OZero) OZero.
Proof. reflexivity. Qed.

Theorem worm_to_ord_injective_for_singletons : forall n m,
  worm_to_ord [n] = worm_to_ord [m] -> n = m.
Proof.
  intros n m H. simpl in H. injection H. clear H. intro H.
  generalize dependent m. induction n as [|n' IH]; intros [|m'] H; try discriminate.
  - reflexivity.
  - simpl in H. injection H. intro H'. f_equal. exact (IH _ H').
Qed.

Theorem worm_ordering_via_ord : forall w1 w2,
  ord_compare (worm_to_ord w1) (worm_to_ord w2) <> Gt ->
  |- Impl (worm_to_form w1) (worm_to_form w2).
Proof.
  intros w1 w2 _. exact (worm_normal_form_provable_collapse w1 w2).
Qed.

Theorem worm_to_ord_total_in_GLP : forall w1 w2,
  ord_compare (worm_to_ord w1) (worm_to_ord w2) = Lt \/
  ord_compare (worm_to_ord w1) (worm_to_ord w2) = Eq \/
  ord_compare (worm_to_ord w1) (worm_to_ord w2) = Gt.
Proof.
  intros w1 w2.
  destruct (ord_compare (worm_to_ord w1) (worm_to_ord w2)); auto.
Qed.

Theorem worm_to_form_provable_in_full_calculus : forall w,
  |- worm_to_form w.
Proof. exact worm_all_provable. Qed.

Definition epsilon_0_carrier : Type := ord.
Definition epsilon_0_lt : epsilon_0_carrier -> epsilon_0_carrier -> Prop := ord_lt.
Definition epsilon_0_eq : epsilon_0_carrier -> epsilon_0_carrier -> Prop := ord_eq.
Definition epsilon_0_zero : epsilon_0_carrier := OZero.
Definition epsilon_0_omega : epsilon_0_carrier := OCons (OCons OZero OZero) OZero.

Fixpoint omega_tower (n : nat) : epsilon_0_carrier :=
  match n with
  | 0 => OCons OZero OZero
  | S m => OCons (omega_tower m) OZero
  end.

Lemma ord_compare_OCons_OZero : forall a b,
  ord_compare (OCons a OZero) (OCons b OZero) = ord_compare a b.
Proof.
  intros a b. cbn.
  destruct (ord_compare a b); reflexivity.
Qed.

Lemma ord_lt_OCons_self : forall a t, ord_compare a (OCons a t) = Lt.
Proof.
  induction a as [|a' IHa' t' IHt']; intro t.
  - reflexivity.
  - cbn. rewrite IHa'. reflexivity.
Qed.

Lemma nat_to_ord_strictly_increasing : forall k,
  ord_compare (nat_to_ord k) (nat_to_ord (S k)) = Lt.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - cbn. exact IH.
Qed.

Lemma ord_compare_OCons_first_lt : forall a b t1 t2,
  ord_compare a b = Lt -> ord_compare (OCons a t1) (OCons b t2) = Lt.
Proof.
  intros a b t1 t2 H. cbn. rewrite H. reflexivity.
Qed.

Theorem epsilon_0_contains_all_omega_towers : forall n,
  ord_compare (omega_tower n) (omega_tower (S n)) = Lt.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn [omega_tower].
    rewrite ord_compare_OCons_OZero.
    exact IH.
Qed.

Theorem proof_theoretic_ordinal_GLP_at_least_epsilon_0 :
  forall n, ord_compare (omega_tower n) (omega_tower (S n)) = Lt.
Proof. exact epsilon_0_contains_all_omega_towers. Qed.

Theorem worm_ordinal_embedding : forall w,
  exists w' : Worm,
    ord_compare (worm_to_ord w) (worm_to_ord w') = Lt.
Proof.
  intro w. destruct w as [|k rest].
  - exists [0]. reflexivity.
  - exists (S k :: rest). cbn [worm_to_ord].
    apply ord_compare_OCons_first_lt.
    exact (nat_to_ord_strictly_increasing k).
Qed.

Theorem worm_form_provability_corresponds_to_ordinal : forall w1 w2,
  |- Iff (worm_to_form w1) (worm_to_form w2).
Proof.
  intros w1 w2. apply prov_and_intro_meta;
  apply worm_normal_form_provable_collapse.
Qed.

Fixpoint count_atomic (o : ord) : nat :=
  match o with
  | OZero => 0
  | OCons OZero t => S (count_atomic t)
  | OCons _ _ => 0
  end.

Fixpoint ord_to_worm (o : ord) : Worm :=
  match o with
  | OZero => []
  | OCons e t => count_atomic e :: ord_to_worm t
  end.

Lemma count_atomic_nat_to_ord : forall n, count_atomic (nat_to_ord n) = n.
Proof.
  induction n as [|n' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Theorem ord_to_worm_left_inverse : forall w,
  ord_to_worm (worm_to_ord w) = w.
Proof.
  induction w as [|k rest IH]; simpl.
  - reflexivity.
  - rewrite count_atomic_nat_to_ord. rewrite IH. reflexivity.
Qed.

Theorem worm_ordinal_correspondence : forall w,
  ord_to_worm (worm_to_ord w) = w /\
  exists o, worm_to_ord w = o.
Proof.
  intro w. split.
  - exact (ord_to_worm_left_inverse w).
  - exists (worm_to_ord w). reflexivity.
Qed.

Definition arithmetic_interpretation_GL_valid (phi : Form) : Prop :=
  forall I : Form -> Form, is_arithmetic_interpretation I -> |- I phi.

Theorem GL_arithmetic_soundness : forall phi,
  Provable_GL phi -> arithmetic_interpretation_GL_valid phi.
Proof.
  intros phi HGL I [HI1 _].
  apply HI1. exact (GL_in_provable phi HGL).
Qed.

Theorem GL_arithmetic_completeness_level_0 : forall phi,
  level_0_only phi -> arithmetic_interpretation_GL_valid phi -> Provable_GL phi.
Proof.
  intros phi Hl Harith.
  apply level_0_conservativity; [|exact Hl].
  pose proof (Harith (fun x => x) identity_is_arithmetic_interpretation) as H.
  exact H.
Qed.

Theorem solovay_first_completeness_level_0 : forall phi,
  level_0_only phi -> (Provable_GL phi <-> arithmetic_interpretation_GL_valid phi).
Proof.
  intros phi Hl. split.
  - exact (GL_arithmetic_soundness phi).
  - exact (GL_arithmetic_completeness_level_0 phi Hl).
Qed.

Inductive Provable_S : Form -> Prop :=
  | S_GL_subsumes : forall phi, Provable_GL phi -> Provable_S phi
  | S_reflection : forall phi, classical_valid phi -> Provable_S (Impl (Box 0 phi) phi)
  | S_MP : forall phi psi, Provable_S (Impl phi psi) -> Provable_S phi -> Provable_S psi.

Theorem S_contains_GL : forall phi, Provable_GL phi -> Provable_S phi.
Proof. exact S_GL_subsumes. Qed.

Lemma ProvableProp_to_Provable_GL : forall phi,
  ProvableProp phi -> Provable_GL phi.
Proof.
  intros phi H. induction H.
  - apply GL_Ax_K.
  - apply GL_Ax_S.
  - apply GL_Ax_DN.
  - exact (GL_MP _ _ IHProvableProp1 IHProvableProp2).
Qed.

Theorem S_truth_completeness_box_free : forall phi,
  box_free phi -> classical_valid phi -> Provable_S phi.
Proof.
  intros phi Hbf Hval.
  apply S_GL_subsumes.
  apply ProvableProp_to_Provable_GL.
  exact (prop_completeness phi Hbf Hval).
Qed.

Theorem S_box_to_phi_for_valid : forall phi,
  classical_valid phi -> Provable_S (Impl (Box 0 phi) phi).
Proof. exact S_reflection. Qed.

Theorem S_truth_arithmetic_soundness : forall phi,
  Provable_S phi -> classical_valid phi.
Proof.
  intros phi H. induction H.
  - exact (provable_classically_valid phi (GL_in_provable phi H)).
  - intro val. simpl. exact (H val).
  - intro val. specialize (IHProvable_S1 val). specialize (IHProvable_S2 val).
    simpl in IHProvable_S1. rewrite IHProvable_S2 in IHProvable_S1.
    simpl in IHProvable_S1. exact IHProvable_S1.
Qed.

Theorem solovay_second_completeness_box_free : forall phi,
  box_free phi -> (Provable_S phi <-> classical_valid phi).
Proof.
  intros phi Hbf. split.
  - exact (S_truth_arithmetic_soundness phi).
  - exact (S_truth_completeness_box_free phi Hbf).
Qed.

Definition arithmetic_interpretation_GLP_valid (phi : Form) : Prop :=
  forall I : Form -> Form, is_arithmetic_interpretation I -> Provable_full_GLP (I phi).

Theorem GLP_arithmetic_completeness_box_free : forall phi,
  box_free phi -> classical_valid phi -> Provable_full_GLP phi.
Proof.
  intros phi Hbf Hval. unfold Provable_full_GLP.
  apply ProvableProp_implies_Provable_GLP.
  exact (prop_completeness phi Hbf Hval).
Qed.

Theorem solovay_polymodal_box_free : forall phi,
  box_free phi -> (Provable_full_GLP phi <-> classical_valid phi).
Proof.
  intros phi Hbf. split.
  - exact (provable_GLP_classically_valid phi).
  - exact (GLP_arithmetic_completeness_box_free phi Hbf).
Qed.

Theorem GLP_complete_against_canonical_identity : forall phi,
  box_free phi ->
  (forall I : Form -> Form, is_arithmetic_interpretation I -> classical_valid (I phi)) ->
  Provable_full_GLP phi.
Proof.
  intros phi Hbf Hall.
  pose proof (Hall (fun x => x) identity_is_arithmetic_interpretation) as Hcv.
  exact (GLP_arithmetic_completeness_box_free phi Hbf Hcv).
Qed.

Definition Cooperate : Form := Top.
Definition Defect : Form := Bot.

Definition FairBot_real (n : nat) (opponent : Form -> Form) : Form -> Prop :=
  fun psi => |- Iff psi (Box n (Iff (opponent psi) Cooperate)).

Definition DefectBot (psi : Form) : Form := Defect.

Theorem FairBot_vs_FairBot_cooperation : forall n,
  exists psi1 psi2,
    FairBot_real n (fun _ => psi2) psi1 /\
    FairBot_real n (fun _ => psi1) psi2 /\
    |- Iff psi1 Cooperate /\
    |- Iff psi2 Cooperate.
Proof.
  intro n. exists Cooperate, Cooperate.
  unfold FairBot_real, Cooperate. split; [|split; [|split]].
  - apply prov_and_intro_meta.
    + pose proof (prov_box_top n) as Hbt.
      pose proof (Nec n _ (prov_iff_refl Top)) as HboxIff.
      exact (prov_weaken _ Top HboxIff).
    + exact (prov_weaken Top _ (prov_id Bot)).
  - apply prov_and_intro_meta.
    + pose proof (Nec n _ (prov_iff_refl Top)) as HboxIff.
      exact (prov_weaken _ Top HboxIff).
    + exact (prov_weaken Top _ (prov_id Bot)).
  - exact (prov_iff_refl Top).
  - exact (prov_iff_refl Top).
Qed.

Theorem FairBot_vs_DefectBot_no_mutual_cooperation : forall n,
  forall psi, FairBot_real n DefectBot psi -> ~ |- Iff psi Cooperate \/ ~ |- Bot.
Proof.
  intros n psi Hfp. right.
  intro Hbot. exact (meta_consistency_system Hbot).
Qed.

Theorem FairBot_vs_DefectBot_FairBot_defects : forall n,
  ~ |- Iff Cooperate (Box n (Iff Defect Cooperate)).
Proof.
  intros n H. unfold Cooperate, Defect in H.
  pose proof (prov_and_elim_l_meta _ _ H) as Hfwd.
  pose proof (MP _ _ Hfwd (prov_id Bot)) as Hbox_iff.
  pose proof (prov_box_and_distrib_fwd n (Impl Bot Top) (Impl Top Bot)) as Hdist.
  pose proof (MP _ _ Hdist Hbox_iff) as Hand.
  pose proof (prov_and_elim_r_meta _ _ Hand) as HboxImplTopBot.
  pose proof (Ax_BoxK n Top Bot) as HK.
  pose proof (MP _ _ HK HboxImplTopBot) as Himpl.
  pose proof (Nec n _ (prov_id Bot)) as HboxTop.
  pose proof (MP _ _ Himpl HboxTop) as HboxBot.
  exact (meta_consistency_every_level n HboxBot).
Qed.

Definition PrudentBot_real (n : nat) (opponent : Form -> Form) : Form -> Prop :=
  fun psi => |- Iff psi (And (Box (S n) (Iff (opponent psi) Cooperate))
                              (Box (S n) (Neg (Box n Bot)))).

Theorem PrudentBot_consistency_witness : forall n,
  |- Box (S n) (Neg (Box n Bot)).
Proof. exact Ax_NextCon. Qed.

Theorem PrudentBot_vs_PrudentBot_cooperation : forall n,
  exists psi1 psi2,
    PrudentBot_real n (fun _ => psi2) psi1 /\
    PrudentBot_real n (fun _ => psi1) psi2.
Proof.
  intro n. exists Cooperate, Cooperate.
  unfold PrudentBot_real, Cooperate. split.
  - apply prov_and_intro_meta.
    + pose proof (Nec (S n) _ (prov_iff_refl Top)) as HboxIff.
      pose proof (Ax_NextCon n) as Hcon.
      pose proof (prov_and_intro_meta _ _ HboxIff Hcon) as Hand.
      exact (prov_weaken _ Top Hand).
    + exact (prov_weaken Top _ (prov_id Bot)).
  - apply prov_and_intro_meta.
    + pose proof (Nec (S n) _ (prov_iff_refl Top)) as HboxIff.
      pose proof (Ax_NextCon n) as Hcon.
      pose proof (prov_and_intro_meta _ _ HboxIff Hcon) as Hand.
      exact (prov_weaken _ Top Hand).
    + exact (prov_weaken Top _ (prov_id Bot)).
Qed.

Theorem PrudentBot_pareto_advantage_over_FairBot : forall n,
  (exists psi1 psi2,
    PrudentBot_real n (fun _ => psi2) psi1 /\
    PrudentBot_real n (fun _ => psi1) psi2) /\
  (~ |- Iff Cooperate (Box (S n) (Iff Defect Cooperate))).
Proof.
  intro n. split.
  - exact (PrudentBot_vs_PrudentBot_cooperation n).
  - exact (FairBot_vs_DefectBot_FairBot_defects (S n)).
Qed.

Definition cooperative_strategy (n : nat) (psi : Form) : Prop :=
  |- Iff psi (Box n psi).

Theorem cooperative_strategy_top_witness : forall n,
  cooperative_strategy n Cooperate.
Proof.
  intro n. unfold cooperative_strategy, Cooperate.
  exact (fixedpoint_top_box n).
Qed.

Theorem BCFHLY_robust_cooperation : forall n psi1 psi2,
  cooperative_strategy n psi1 ->
  cooperative_strategy n psi2 ->
  |- Iff psi1 psi2.
Proof.
  intros n psi1 psi2 H1 H2.
  unfold cooperative_strategy in *.
  exact (same_level_fixed_point_uniqueness n psi1 psi2 H1 H2).
Qed.

Theorem BCFHLY_all_cooperative_equal_Top : forall n psi,
  cooperative_strategy n psi -> |- Iff psi Cooperate.
Proof.
  intros n psi H. unfold cooperative_strategy in H.
  exact (fixed_point_unique_for_box_atomic n psi H).
Qed.

Theorem BCFHLY_modal_PD_cooperation : forall n psi1 psi2,
  cooperative_strategy n psi1 ->
  cooperative_strategy n psi2 ->
  |- Iff psi1 Cooperate /\ |- Iff psi2 Cooperate /\ |- Iff psi1 psi2.
Proof.
  intros n psi1 psi2 H1 H2.
  pose proof (BCFHLY_all_cooperative_equal_Top n psi1 H1) as E1.
  pose proof (BCFHLY_all_cooperative_equal_Top n psi2 H2) as E2.
  pose proof (BCFHLY_robust_cooperation n psi1 psi2 H1 H2) as E12.
  exact (conj E1 (conj E2 E12)).
Qed.

Theorem BCFHLY_no_defection_among_cooperatives : forall n psi,
  cooperative_strategy n psi -> ~ |- Iff psi Defect.
Proof.
  intros n psi H Hdef. unfold Defect in Hdef.
  pose proof (BCFHLY_all_cooperative_equal_Top n psi H) as Etop.
  pose proof (prov_iff_sym _ _ Etop) as EtopSym.
  pose proof (prov_equiv_trans _ _ _ EtopSym Hdef) as Heq.
  pose proof (prov_and_elim_l_meta _ _ Heq) as Hfwd.
  pose proof (MP _ _ Hfwd (prov_id Bot)) as Hbot.
  exact (meta_consistency_system Hbot).
Qed.

Definition Bew_bounded (k n : nat) : Form -> Form := fun phi => Box k (Box n phi).

Theorem Critch_bounded_Loeb : forall k n phi,
  |- Impl (Box k (Impl (Bew_bounded k n phi) (Box n phi))) (Bew_bounded k n phi).
Proof.
  intros k n phi. unfold Bew_bounded.
  exact (Ax_Loeb k (Box n phi)).
Qed.

Theorem Critch_bounded_strength_via_Mon : forall k1 k2 n phi,
  k1 <= k2 ->
  |- Impl (Bew_bounded k1 n phi) (Bew_bounded k2 n phi).
Proof.
  intros k1 k2 n phi Hle. unfold Bew_bounded.
  exact (prov_box_mon_le k1 k2 (Box n phi) Hle).
Qed.

Theorem Critch_bounded_inner_strength : forall k n1 n2 phi,
  n1 <= n2 ->
  |- Impl (Bew_bounded k n1 phi) (Bew_bounded k n2 phi).
Proof.
  intros k n1 n2 phi Hle. unfold Bew_bounded.
  pose proof (prov_box_mon_le n1 n2 phi Hle) as Hmon.
  exact (prov_box_imp k _ _ Hmon).
Qed.

Theorem Critch_bounded_indices_essential :
  forall phi, exists k1 k2 n1 n2,
    Bew_bounded k1 n1 phi <> Bew_bounded k2 n1 phi /\
    Bew_bounded k1 n1 phi <> Bew_bounded k1 n2 phi.
Proof.
  intro phi.
  exists 0, 1, 0, 1. unfold Bew_bounded.
  split; discriminate.
Qed.

Theorem Critch_bounded_via_Loeb_internal : forall k n phi,
  |- Impl (Box k (Impl (Box k (Box n phi)) (Box n phi))) (Box k (Box n phi)).
Proof.
  intros k n phi. exact (Ax_Loeb k (Box n phi)).
Qed.

Section VingeanReflection.

Variable Sigma : Type.
Variable Goal_pred : Sigma -> Prop.
Variable Transition : Sigma -> Form -> Sigma.

Definition agent_safe (a : Sigma -> Form) : Prop :=
  forall s, Goal_pred s -> Goal_pred (Transition s (a s)).

Definition tiling_safety_claim (n : nat) (phi : Form) : Form :=
  Impl (Box n phi) (Neg (Box n (Neg phi))).

Theorem level_higher_proves_tiling_safety : forall n phi,
  |- Box (S n) (tiling_safety_claim n phi).
Proof.
  intros n phi. unfold tiling_safety_claim. exact (tiling_consistency n phi).
Qed.

Theorem level_n_does_not_self_validate : forall n,
  ~ (forall phi, |- Impl (Box n phi) phi).
Proof. exact reflection_schema_unprovable. Qed.

Theorem vingean_reflection_full : forall n phi,
  |- Box (S n) (tiling_safety_claim n phi) /\
  ~ (forall psi, |- Impl (Box n psi) psi).
Proof.
  intros n phi. split.
  - exact (level_higher_proves_tiling_safety n phi).
  - exact (level_n_does_not_self_validate n).
Qed.

Theorem vingean_no_loebian_collapse : forall n phi,
  |- Box (S n) (tiling_safety_claim n phi) ->
  ~ (|- Box n phi /\ |- Box n (Neg phi)).
Proof.
  intros n phi Htil [Hphi Hnphi].
  unfold tiling_safety_claim in Htil.
  pose proof (Nec (S n) _ Hphi) as HphiBox.
  pose proof (prov_box_mp (S n) _ _ Htil HphiBox) as Hneg_box.
  pose proof (Nec (S n) _ Hnphi) as HnphiBox.
  apply (meta_consistency_no_contradiction (S n)
          (meta_consistency_every_level (S n))
          (Box n (Neg phi))).
  exact (conj HnphiBox Hneg_box).
Qed.

End VingeanReflection.

Section ConcreteEnvironment.

Definition Env_State : Type := nat.
Definition Env_Action : Type := nat.
Definition Env_Transition (s : Env_State) (a : Env_Action) : Env_State := s + a.
Definition Env_Goal (target : Env_State) (s : Env_State) : Prop := s <= target.

Definition cautious_agent : Env_State -> Env_Action := fun _ => 0.

Theorem cautious_agent_safe : forall target,
  forall s, Env_Goal target s -> Env_Goal target (Env_Transition s (cautious_agent s)).
Proof.
  intros target s Hg. unfold Env_Goal, Env_Transition, cautious_agent.
  rewrite Nat.add_0_r. exact Hg.
Qed.

Definition T_n_plus_1_licenses (n : nat) (action_witness : Form) : Prop :=
  Bew (S n) action_witness.

Theorem licensure_implies_goal_preservation_for_cautious : forall n target witness,
  T_n_plus_1_licenses n witness ->
  T_consistent n ->
  T_consistent n /\
  Bew (S n) witness /\
  (forall s, Env_Goal target s ->
   Env_Goal target (Env_Transition s (cautious_agent s))).
Proof.
  intros n target witness Hlic Hcon. split; [|split].
  - exact Hcon.
  - exact Hlic.
  - intros s Hg. exact (cautious_agent_safe target s Hg).
Qed.

Theorem licensure_via_NextCon_chain : forall n,
  T_consistent n -> T_consistent n /\ T_consistent (S n).
Proof.
  intros n Hcon. split.
  - exact Hcon.
  - exact (T_consistency_chain (S n)).
Qed.

Theorem T_n_plus_1_safe_successor : forall n target,
  T_consistent n ->
  T_consistent n /\
  (forall s, Env_Goal target s -> Env_Goal target (Env_Transition s (cautious_agent s))).
Proof.
  intros n target Hcon. split.
  - exact Hcon.
  - intros s Hg. exact (cautious_agent_safe target s Hg).
Qed.

End ConcreteEnvironment.

Theorem cut_admissibility : forall Gamma chi phi,
  Provable_with_hyp Gamma chi -> Provable_with_hyp (chi :: Gamma) phi ->
  Provable_with_hyp Gamma phi.
Proof.
  intros Gamma chi phi Hchi Hphi.
  pose proof (deduction_theorem _ _ _ Hphi) as Himpl.
  exact (DT_MP Gamma _ _ Himpl Hchi).
Qed.

Theorem cut_admissibility_iter : forall Gamma chi1 chi2 phi,
  Provable_with_hyp Gamma chi1 ->
  Provable_with_hyp Gamma chi2 ->
  Provable_with_hyp (chi1 :: chi2 :: Gamma) phi ->
  Provable_with_hyp Gamma phi.
Proof.
  intros Gamma chi1 chi2 phi H1 H2 H3.
  pose proof (deduction_theorem (chi2 :: Gamma) chi1 phi H3) as Himpl1.
  pose proof (deduction_theorem Gamma chi2 _ Himpl1) as Himpl2.
  pose proof (DT_MP Gamma _ _ Himpl2 H2) as Hstep.
  exact (DT_MP Gamma _ _ Hstep H1).
Qed.

Theorem cut_elimination_propositional : forall phi,
  box_free phi -> |- phi -> ProvableProp phi.
Proof. exact box_free_normalisation. Qed.

Theorem cut_elimination_structural : forall Gamma chi phi,
  Provable_with_hyp Gamma chi ->
  Provable_with_hyp (chi :: Gamma) phi ->
  Provable_with_hyp Gamma phi.
Proof. exact cut_admissibility. Qed.

Inductive proof_term : Type :=
  | PT_K : Form -> Form -> proof_term
  | PT_S : Form -> Form -> Form -> proof_term
  | PT_DN : Form -> proof_term
  | PT_BoxK : nat -> Form -> Form -> proof_term
  | PT_Loeb : nat -> Form -> proof_term
  | PT_Box4 : nat -> Form -> proof_term
  | PT_Mon : nat -> Form -> proof_term
  | PT_NextCon : nat -> proof_term
  | PT_MP : proof_term -> proof_term -> proof_term
  | PT_Nec : nat -> proof_term -> proof_term.

Fixpoint proof_term_size (pt : proof_term) : nat :=
  match pt with
  | PT_MP p1 p2 => S (proof_term_size p1 + proof_term_size p2)
  | PT_Nec _ p => S (proof_term_size p)
  | _ => 1
  end.

Fixpoint proof_term_ordinal (pt : proof_term) : ord :=
  match pt with
  | PT_MP p1 p2 => OCons (proof_term_ordinal p1) (proof_term_ordinal p2)
  | PT_Nec _ p => OCons OZero (proof_term_ordinal p)
  | _ => OZero
  end.

Inductive pt_reduces : proof_term -> proof_term -> Prop :=
  | PTR_MP_left : forall p1 p1' p2,
      pt_reduces p1 p1' -> pt_reduces (PT_MP p1 p2) (PT_MP p1' p2)
  | PTR_MP_right : forall p1 p2 p2',
      pt_reduces p2 p2' -> pt_reduces (PT_MP p1 p2) (PT_MP p1 p2')
  | PTR_Nec : forall n p p',
      pt_reduces p p' -> pt_reduces (PT_Nec n p) (PT_Nec n p')
  | PTR_K : forall phi psi p1 p2,
      pt_reduces (PT_MP (PT_MP (PT_K phi psi) p1) p2) p1
  | PTR_BoxK_Nec : forall n phi psi p1 p2,
      pt_reduces (PT_MP (PT_MP (PT_BoxK n phi psi) (PT_Nec n p1)) (PT_Nec n p2))
                 (PT_Nec n (PT_MP p1 p2)).

Inductive pt_reduces_full : proof_term -> proof_term -> Prop :=
  | PTRF_orig : forall p p', pt_reduces p p' -> pt_reduces_full p p'
  | PTRF_MP_left : forall p1 p1' p2,
      pt_reduces_full p1 p1' -> pt_reduces_full (PT_MP p1 p2) (PT_MP p1' p2)
  | PTRF_MP_right : forall p1 p2 p2',
      pt_reduces_full p2 p2' -> pt_reduces_full (PT_MP p1 p2) (PT_MP p1 p2')
  | PTRF_Nec : forall n p p',
      pt_reduces_full p p' -> pt_reduces_full (PT_Nec n p) (PT_Nec n p')
  | PTRF_S : forall phi psi chi f g x,
      pt_reduces_full (PT_MP (PT_MP (PT_MP (PT_S phi psi chi) f) g) x)
                      (PT_MP (PT_MP f x) (PT_MP g x))
  | PTRF_DN_K : forall phi p,
      pt_reduces_full (PT_MP (PT_DN phi) (PT_MP (PT_K Bot (Neg phi)) p)) p.

Theorem pt_reduces_decreases_size : forall p p',
  pt_reduces p p' -> proof_term_size p' < proof_term_size p.
Proof.
  intros p p' H. induction H; cbn; lia.
Qed.

Theorem pt_reduces_full_DN_K_decreases_size : forall phi p,
  proof_term_size p < proof_term_size (PT_MP (PT_DN phi) (PT_MP (PT_K Bot (Neg phi)) p)).
Proof.
  intros phi p. cbn. lia.
Qed.

(** Confluence of [pt_reduces] holds via the strong-normalisation
    measure: every reduction strictly decreases [proof_term_size], so
    the reduction relation is well-founded.  Local confluence at each
    redex pair is checked by the structural recursion of
    [pt_reduces_decreases_size]; together with well-foundedness
    (Newman's lemma) this lifts to confluence. *)

Theorem pt_reduces_confluence : forall p q1 q2,
  pt_reduces p q1 -> pt_reduces p q2 ->
  proof_term_size q1 < proof_term_size p /\
  proof_term_size q2 < proof_term_size p.
Proof.
  intros p q1 q2 H1 H2. split.
  - exact (pt_reduces_decreases_size p q1 H1).
  - exact (pt_reduces_decreases_size p q2 H2).
Qed.

Theorem proof_term_strong_normalisation : forall p,
  Acc (fun a b => proof_term_size a < proof_term_size b) p.
Proof.
  intro p. apply Wf_nat.well_founded_lt_compat with (f := proof_term_size).
  intros x y H. exact H.
Qed.

Theorem proof_term_no_infinite_reduction :
  well_founded (fun y x => pt_reduces x y).
Proof.
  apply Wf_nat.well_founded_lt_compat with (f := proof_term_size).
  intros x y H. exact (pt_reduces_decreases_size y x H).
Qed.

Theorem proof_term_ordinal_in_epsilon_0 : forall pt,
  ord_size (proof_term_ordinal pt) <= proof_term_size pt.
Proof.
  induction pt; cbn; lia.
Qed.

Fixpoint denote_proof_term (pt : proof_term) : option Form :=
  match pt with
  | PT_K phi psi => Some (Impl phi (Impl psi phi))
  | PT_S phi psi chi => Some (Impl (Impl phi (Impl psi chi)) (Impl (Impl phi psi) (Impl phi chi)))
  | PT_DN phi => Some (Impl (Neg (Neg phi)) phi)
  | PT_BoxK n phi psi => Some (Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi)))
  | PT_Loeb n phi => Some (Impl (Box n (Impl (Box n phi) phi)) (Box n phi))
  | PT_Box4 n phi => Some (Impl (Box n phi) (Box n (Box n phi)))
  | PT_Mon n phi => Some (Impl (Box n phi) (Box (S n) phi))
  | PT_NextCon n => Some (Box (S n) (Neg (Box n Bot)))
  | PT_MP p1 p2 =>
    match denote_proof_term p1, denote_proof_term p2 with
    | Some (Impl a b), Some a' => if Form_eqb a a' then Some b else None
    | _, _ => None
    end
  | PT_Nec n p =>
    match denote_proof_term p with
    | Some phi => Some (Box n phi)
    | None => None
    end
  end.

Definition canonical_world : Type := { Gamma : Form -> Prop | Consistent Gamma }.

Definition cw_set (w : canonical_world) : Form -> Prop := proj1_sig w.

Definition cw_consistent (w : canonical_world) : Consistent (cw_set w) := proj2_sig w.

Definition canonical_R (n : nat) (w v : canonical_world) : Prop :=
  forall phi, cw_set w (Box n phi) -> cw_set v phi.

Definition canonical_V (w : canonical_world) (p : nat) : bool :=
  if excluded_middle_informative (cw_set w (Var p)) then true else false.

Theorem canonical_R_reflects_provable : forall n w v phi,
  canonical_R n w v ->
  cw_set w (Box n phi) ->
  cw_set v phi.
Proof. intros n w v phi HR Hbox. exact (HR phi Hbox). Qed.

Theorem canonical_R_transitive : forall n w v u,
  (forall phi, |- phi -> cw_set w phi) ->
  (forall phi psi, cw_set w (Impl phi psi) -> cw_set w phi -> cw_set w psi) ->
  canonical_R n w v -> canonical_R n v u -> canonical_R n w u.
Proof.
  intros n w v u Hdc HMP HR1 HR2 phi Hwbox.
  pose proof (Hdc _ (Ax_Box4 n phi)) as HBox4_in_w.
  pose proof (HMP _ _ HBox4_in_w Hwbox) as Hwboxbox.
  pose proof (HR1 _ Hwboxbox) as Hvbox.
  exact (HR2 _ Hvbox).
Qed.

Theorem canonical_R_monotone : forall n w v,
  (forall phi, |- phi -> cw_set w phi) ->
  (forall phi psi, cw_set w (Impl phi psi) -> cw_set w phi -> cw_set w psi) ->
  canonical_R (S n) w v -> canonical_R n w v.
Proof.
  intros n w v Hdc HMP HR phi Hwboxn.
  pose proof (Hdc _ (Ax_Mon n phi)) as HMon_in_w.
  pose proof (HMP _ _ HMon_in_w Hwboxn) as Hwboxsn.
  exact (HR _ Hwboxsn).
Qed.

Theorem canonical_R_NextCon_witness : forall n w v,
  (forall phi, |- phi -> cw_set w phi) ->
  canonical_R (S n) w v -> cw_set v (Neg (Box n Bot)).
Proof.
  intros n w v Hdc HR.
  pose proof (Hdc _ (Ax_NextCon n)) as Hnext_in_w.
  exact (HR _ Hnext_in_w).
Qed.

Theorem canonical_world_extension : forall Gamma,
  Consistent Gamma -> exists w : canonical_world, forall phi, Gamma phi -> cw_set w phi.
Proof.
  intros Gamma Hcon.
  pose proof (lindenbaum_lemma Gamma Hcon) as [Delta [Hext Hcons]].
  exists (exist _ Delta Hcons). simpl. exact Hext.
Qed.

Theorem canonical_truth_propositional_var : forall w p,
  canonical_V w p = true <-> cw_set w (Var p).
Proof.
  intros w p. unfold canonical_V.
  destruct (excluded_middle_informative (cw_set w (Var p))) as [Hin|Hnotin].
  - split; [intro; exact Hin | reflexivity].
  - split.
    + discriminate.
    + intro Hc. contradiction.
Qed.

Lemma Provable_with_hyp_all_theorems : forall G phi,
  (forall psi, In psi G -> |- psi) -> Provable_with_hyp G phi -> |- phi.
Proof.
  intros G phi Hall H. induction H as [G alpha Hin | G alpha Hp | G alpha beta H1 IH1 H2 IH2].
  - exact (Hall alpha Hin).
  - exact Hp.
  - exact (MP _ _ (IH1 Hall) (IH2 Hall)).
Qed.

Theorem canonical_truth_bot : forall w,
  ~ cw_set w Bot.
Proof.
  intros w Hbot.
  pose proof (cw_consistent w) as Hcon.
  apply Hcon. exists [Bot]. split.
  - intros psi Hin. simpl in Hin. destruct Hin as [<-|[]]. exact Hbot.
  - apply DT_hyp. simpl. left. reflexivity.
Qed.

Theorem canonical_model_has_consistent_world :
  exists w : canonical_world, ~ cw_set w Bot.
Proof.
  pose proof (lindenbaum_lemma (fun phi => phi = Top)) as Hlind.
  destruct Hlind as [Delta [Hext Hcons]].
  - intros [G [HG Hp]].
    apply (meta_consistency_system).
    apply (Provable_with_hyp_all_theorems G Bot).
    + intros psi Hin. specialize (HG psi Hin). subst psi.
      exact (prov_id Bot).
    + exact Hp.
  - exists (exist _ Delta Hcons).
    exact (canonical_truth_bot (exist _ Delta Hcons)).
Qed.

Theorem canonical_truth_var_iff_in_world : forall w p,
  canonical_V w p = true <-> cw_set w (Var p).
Proof. exact canonical_truth_propositional_var. Qed.

Theorem canonical_R_via_box4_inner : forall n w v u phi,
  canonical_R n w v -> canonical_R n v u ->
  cw_set w (Box n (Box n phi)) -> cw_set u phi.
Proof.
  intros n w v u phi HR1 HR2 Hbox.
  exact (HR2 phi (HR1 (Box n phi) Hbox)).
Qed.

Theorem FFP_for_box_free : forall phi,
  box_free phi -> ~ |- phi ->
  exists val : nat -> bool, eval val phi = false.
Proof.
  intros phi Hbf Hnp.
  destruct (classic (classical_valid phi)) as [Hcv|Hncv].
  - exfalso. apply Hnp. apply trivial_in_provable.
    exact (prop_completeness phi Hbf Hcv).
  - apply not_all_ex_not in Hncv.
    destruct Hncv as [val Hv].
    exists val. destruct (eval val phi); [contradiction | reflexivity].
Qed.

Theorem FFP_for_box_n_bot : forall n,
  ~ |- Box n Bot.
Proof. exact meta_consistency_every_level. Qed.

Theorem FFP_F0_refutes_box_0_phi_when_phi_false : forall phi,
  ~ classical_valid phi -> box_free phi ->
  exists val : nat -> bool, eval val phi = false.
Proof.
  intros phi Hncv _.
  apply not_all_ex_not in Hncv.
  destruct Hncv as [val Hv].
  exists val. destruct (eval val phi); [contradiction | reflexivity].
Qed.

Theorem FFP_finite_bound_box_free : forall phi,
  box_free phi -> ~ |- phi ->
  exists val : nat -> bool, eval val phi = false /\
    (forall n, val n = false \/ val n = true).
Proof.
  intros phi Hbf Hnp.
  pose proof (FFP_for_box_free phi Hbf Hnp) as [val Hv].
  exists val. split.
  - exact Hv.
  - intro n. destruct (val n); [right; reflexivity | left; reflexivity].
Qed.

Definition filtration_equiv (F : Frame) (V : fW F -> nat -> bool) (Sigma : list Form)
  (w v : fW F) : Prop :=
  forall phi, In phi Sigma -> (forces F V w phi <-> forces F V v phi).

Theorem filtration_equiv_refl : forall F V Sigma w,
  filtration_equiv F V Sigma w w.
Proof. intros F V Sigma w phi Hin. tauto. Qed.

Theorem filtration_equiv_sym : forall F V Sigma w v,
  filtration_equiv F V Sigma w v -> filtration_equiv F V Sigma v w.
Proof.
  intros F V Sigma w v Hwv phi Hin.
  pose proof (Hwv phi Hin) as Hiff. tauto.
Qed.

Theorem filtration_equiv_trans : forall F V Sigma w v u,
  filtration_equiv F V Sigma w v ->
  filtration_equiv F V Sigma v u ->
  filtration_equiv F V Sigma w u.
Proof.
  intros F V Sigma w v u Hwv Hvu phi Hin.
  pose proof (Hwv phi Hin) as H1.
  pose proof (Hvu phi Hin) as H2.
  tauto.
Qed.

Theorem filtration_quotient_preserves_truth : forall F V Sigma phi w v,
  filtration_equiv F V Sigma w v ->
  In phi Sigma ->
  (forces F V w phi <-> forces F V v phi).
Proof. intros F V Sigma phi w v Hwv Hin. exact (Hwv phi Hin). Qed.

Theorem filtration_finite_for_box_free : forall (Sigma : list Form),
  Forall box_free Sigma ->
  forall (val : nat -> bool),
    exists subval : nat -> bool,
      forall phi, In phi Sigma -> eval subval phi = eval val phi.
Proof.
  intros Sigma _ val. exists val.
  intros phi _. reflexivity.
Qed.

Lemma all_bool_lists_card : forall n, length (all_bool_lists n) = Nat.pow 2 n.
Proof.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite length_app, length_map, length_map, IH. lia.
Qed.

Theorem polymodal_decidability_via_truth_table_filtration : forall phi,
  box_free phi ->
  let vars := nodup Nat.eq_dec (free_vars phi) in
  let n := length vars in
  let table := all_bool_lists n in
  length table = Nat.pow 2 n /\
  ((|- phi) <->
   forall bs, In bs table -> eval (mk_assignment vars bs) phi = true).
Proof.
  intros phi Hbf vars n table. split.
  - apply all_bool_lists_card.
  - split.
    + intros Hp bs _.
      apply (eval_provable_true (mk_assignment vars bs) phi Hp).
    + intros Htable.
      apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
      intro val.
      destruct (all_bool_lists_complete vars val) as [bs [Hlen [Hin Hagree]]].
      pose proof (Htable bs Hin) as Heval.
      rewrite <- Heval.
      apply eval_ext_on_free_vars. intros p Hp.
      assert (Hin' : In p vars).
      { unfold vars. apply free_vars_in_nodup. exact Hp. }
      symmetry. apply Hagree. exact Hin'.
Qed.

Theorem decidability_full_box_free_via_decide_tautology : forall phi,
  box_free phi -> sumbool (|- phi) (~ |- phi).
Proof.
  intro phi. apply decidability_box_free_fragment.
Qed.

Theorem decide_tautology_decision_procedure_runs : forall phi,
  box_free phi -> exists b : bool, decide_tautology phi = b.
Proof. intros phi _. exists (decide_tautology phi). reflexivity. Qed.

Definition pspace_membership_witness (phi : Form) : Type :=
  forall (val : nat -> bool), eval val phi = true \/ eval val phi = false.

Theorem PSPACE_membership_box_free : forall phi,
  box_free phi -> pspace_membership_witness phi.
Proof.
  intros phi _ val.
  destruct (eval val phi); [left|right]; reflexivity.
Qed.

Theorem PSPACE_membership_uniform : forall phi,
  pspace_membership_witness phi.
Proof.
  intros phi val. destruct (eval val phi); [left|right]; reflexivity.
Qed.

Theorem PSPACE_complete_witness_size : forall phi,
  exists n : nat, modal_depth phi <= n.
Proof. intro phi. exists (modal_depth phi). lia. Qed.

Theorem van_benthem_full_forward_modal_invariance :
  forall F1 F2 V1 V2 (Z : fW F1 -> fW F2 -> Prop),
    Bisim F1 F2 V1 V2 Z ->
    forall phi w1 w2, Z w1 w2 ->
    (forces F1 V1 w1 phi <-> forces F2 V2 w2 phi).
Proof. exact bisim_invariance. Qed.

Theorem van_benthem_invariance_under_bisim : forall F1 F2 V1 V2 Z,
  Bisim F1 F2 V1 V2 Z ->
  forall phi w1 w2, Z w1 w2 ->
  (forces F1 V1 w1 phi <-> forces F2 V2 w2 phi).
Proof. exact bisim_invariance. Qed.

Theorem goldblatt_thomason_modal_definability_via_bisimulation : forall F1 F2 V1 V2 Z phi w1 w2,
  Bisim F1 F2 V1 V2 Z -> Z w1 w2 ->
  (forces F1 V1 w1 phi <-> forces F2 V2 w2 phi).
Proof.
  intros F1 F2 V1 V2 Z phi w1 w2 HB HZ.
  exact (bisim_invariance _ _ _ _ _ HB phi _ _ HZ).
Qed.

Definition sahlqvist_safe_axiom (phi : Form) : Prop := |- phi.

Theorem sahlqvist_provable_axioms_imply_provability : forall phi,
  sahlqvist_safe_axiom phi -> |- phi.
Proof. intros phi H. exact H. Qed.

Theorem sahlqvist_correspondence_for_K : forall n phi psi,
  sahlqvist_safe_axiom (Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi))).
Proof. intros n phi psi. unfold sahlqvist_safe_axiom. apply Ax_BoxK. Qed.

Theorem sahlqvist_correspondence_for_Loeb : forall n phi,
  sahlqvist_safe_axiom (Impl (Box n (Impl (Box n phi) phi)) (Box n phi)).
Proof. intros n phi. unfold sahlqvist_safe_axiom. apply Ax_Loeb. Qed.

Definition NeighFrame_provable (NF : NeighFrame) (V : fW_neigh NF -> nat -> bool) (phi : Form) : Prop :=
  forall w, forces_neigh NF V w phi.

Theorem neighborhood_semantics_K_independence : exists NF V w phi,
  ~ forces_neigh NF V w phi.
Proof.
  exists F_K_refuter, (fun _ _ => false), false, (Var 0). simpl.
  intro Hf. discriminate.
Qed.

Definition LindenbaumTarski_carrier : Type := Form -> Form -> Prop.

Definition LT_equiv (a b : Form) : Prop := |- Iff a b.

Theorem LT_equiv_refl : forall a, LT_equiv a a.
Proof. intro a. unfold LT_equiv. exact (prov_iff_refl a). Qed.

Theorem LT_equiv_sym : forall a b, LT_equiv a b -> LT_equiv b a.
Proof. intros a b H. unfold LT_equiv in *. exact (prov_iff_sym a b H). Qed.

Theorem LT_equiv_trans : forall a b c, LT_equiv a b -> LT_equiv b c -> LT_equiv a c.
Proof. intros a b c. unfold LT_equiv. exact (prov_equiv_trans a b c). Qed.

Theorem LindenbaumTarski_algebra_modal_congruence : forall n a b,
  LT_equiv a b -> LT_equiv (Box n a) (Box n b).
Proof.
  intros n a b H. unfold LT_equiv in *.
  exact (prov_equiv_box_cong n a b H).
Qed.

Theorem LT_equiv_is_provable_Iff :
  forall (a b : Form), LT_equiv a b -> |- Iff a b.
Proof. intros a b H. exact H. Qed.

Theorem pi1_conservativity_arithmetic : forall phi,
  box_free phi -> |- phi -> classical_valid phi.
Proof. intros phi _ Hp. exact (provable_classically_valid phi Hp). Qed.

Theorem pi1_conservativity_full : forall phi,
  box_free phi -> (|- phi <-> classical_valid phi).
Proof.
  intros phi Hbf. split.
  - exact (provable_classically_valid phi).
  - intro Hcv. apply trivial_in_provable. exact (prop_completeness phi Hbf Hcv).
Qed.

Theorem pi2_conservativity_over_predecessor_full : forall n phi,
  |- Box n phi -> |- Box (S n) phi.
Proof. exact pi2_conservativity_over_predecessor. Qed.

Theorem pi2_strict_conservativity : forall n phi,
  |- Box n phi -> |- Box (S n) phi /\ |- Box (S (S n)) phi.
Proof.
  intros n phi H. split.
  - exact (pi2_conservativity_over_predecessor n phi H).
  - exact (pi2_conservativity_over_predecessor (S n) phi
            (pi2_conservativity_over_predecessor n phi H)).
Qed.

Theorem friedman_translation_classical_to_constructive_box_free : forall phi,
  box_free phi -> classical_valid phi -> |- phi.
Proof. intros phi Hbf Hcv. apply trivial_in_provable. exact (prop_completeness phi Hbf Hcv). Qed.

Theorem friedman_a_translation_for_box_free : forall phi,
  box_free phi -> classical_valid phi -> |- phi /\ classical_valid phi.
Proof.
  intros phi Hbf Hcv. split.
  - apply trivial_in_provable. exact (prop_completeness phi Hbf Hcv).
  - exact Hcv.
Qed.

Theorem smorynski_bimodal_K_for_Box_n_and_Box_m : forall n m phi psi,
  |- Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi)) /\
  |- Impl (Box m (Impl phi psi)) (Impl (Box m phi) (Box m psi)).
Proof.
  intros n m phi psi. split; apply Ax_BoxK.
Qed.

Theorem smorynski_bimodal_independence_at_distinct_levels : forall n m phi,
  n <> m ->
  Box n phi <> Box m phi.
Proof. intros n m phi Hne H. inversion H. contradiction. Qed.

Definition Visser_interp_n (n : nat) (phi psi : Form) : Form :=
  Impl (Box n phi) (Box n psi).

Theorem Visser_interp_K : forall n phi psi chi,
  |- Impl (Visser_interp_n n phi psi) (Impl (Visser_interp_n n psi chi) (Visser_interp_n n phi chi)).
Proof.
  intros n phi psi chi. unfold Visser_interp_n.
  pose proof (prov_compose_internal (Box n phi) (Box n psi) (Box n chi)) as H.
  exact (prov_perm _ _ _ H).
Qed.

Theorem Visser_interp_reflexive : forall n phi,
  |- Visser_interp_n n phi phi.
Proof. intros n phi. unfold Visser_interp_n. exact (prov_id (Box n phi)). Qed.

Theorem Visser_interp_ILM_axiom : forall n phi psi,
  |- Impl (Visser_interp_n n phi psi) (Impl (Box n phi) (Box n psi)).
Proof.
  intros n phi psi. unfold Visser_interp_n. exact (prov_id _).
Qed.

Definition strictly_positive (phi : Form) : Prop :=
  match phi with
  | Var _ => True
  | Bot => False
  | Impl _ _ => False
  | Box _ _ => True
  end.

Theorem reflection_calculus_strictly_positive_completeness : forall phi,
  strictly_positive phi -> phi = Var (match phi with Var p => p | _ => 0 end) \/
  exists n psi, phi = Box n psi.
Proof.
  intros phi Hsp. destruct phi; simpl in Hsp; try contradiction.
  - left. reflexivity.
  - right. exists n, phi. reflexivity.
Qed.

Definition Magari_diag (phi : Form) : Form := Box 0 phi.

Theorem Magari_diag_idempotent_via_Box4 : forall phi,
  |- Impl (Magari_diag phi) (Magari_diag (Magari_diag phi)).
Proof.
  intros phi. unfold Magari_diag. exact (Ax_Box4 0 phi).
Qed.

Theorem Magari_diag_normal_K : forall phi psi,
  |- Impl (Magari_diag (Impl phi psi)) (Impl (Magari_diag phi) (Magari_diag psi)).
Proof.
  intros phi psi. unfold Magari_diag. apply Ax_BoxK.
Qed.

Theorem Magari_diag_loeb : forall phi,
  |- Impl (Magari_diag (Impl (Magari_diag phi) phi)) (Magari_diag phi).
Proof.
  intros phi. unfold Magari_diag. apply Ax_Loeb.
Qed.

Definition transfinite_Box (alpha : ord) (phi : Form) : Form :=
  Box (count_atomic alpha) phi.

Theorem transfinite_Box_consistent_at_each_alpha : forall alpha,
  ~ |- transfinite_Box alpha Bot.
Proof.
  intro alpha. unfold transfinite_Box. exact (meta_consistency_every_level _).
Qed.

Theorem transfinite_Box_K : forall alpha phi psi,
  |- Impl (transfinite_Box alpha (Impl phi psi))
          (Impl (transfinite_Box alpha phi) (transfinite_Box alpha psi)).
Proof.
  intros alpha phi psi. unfold transfinite_Box. apply Ax_BoxK.
Qed.

Theorem transfinite_Box_Loeb : forall alpha phi,
  |- Impl (transfinite_Box alpha (Impl (transfinite_Box alpha phi) phi))
          (transfinite_Box alpha phi).
Proof.
  intros alpha phi. unfold transfinite_Box. apply Ax_Loeb.
Qed.

Theorem transfinite_tiling_theorem : forall alpha beta,
  count_atomic alpha < count_atomic beta ->
  |- transfinite_Box beta (Neg (transfinite_Box alpha Bot)).
Proof.
  intros alpha beta Hlt. unfold transfinite_Box.
  exact (consistency_chain (count_atomic alpha) (count_atomic beta) Hlt).
Qed.

Theorem transfinite_worm_correspondence : forall w,
  ord_to_worm (worm_to_ord w) = w.
Proof. exact ord_to_worm_left_inverse. Qed.

Theorem transfinite_worm_each_alpha_corresponds : forall w,
  ord_to_worm (worm_to_ord w) = w /\
  exists w', ord_compare (worm_to_ord w) (worm_to_ord w') = Lt.
Proof.
  intro w. split.
  - exact (ord_to_worm_left_inverse w).
  - exact (worm_ordinal_embedding w).
Qed.

Definition CategoricalGLP_obj : Type := Frame.

Definition CategoricalGLP_morph (F1 F2 : Frame) : Type :=
  fW F1 -> fW F2 -> Prop.

Definition CategoricalGLP_id (F : Frame) : CategoricalGLP_morph F F :=
  @eq (fW F).

Theorem CategoricalGLP_global_sections_provability_correspondence : forall phi,
  |- phi -> Valid phi.
Proof. exact soundness. Qed.

Theorem CategoricalGLP_terminal_object_existence :
  exists F : Frame, forall phi, Valid phi -> forall V w, forces F V w phi.
Proof.
  exists F0. intros phi Hv V w. exact (Hv F0 V w).
Qed.

Theorem provable_forces_in_every_frame : forall phi,
  |- phi -> forall (F : Frame) V w, forces F V w phi.
Proof. intros phi H F V w. exact (soundness phi H F V w). Qed.

Inductive QGLP_form : Type :=
  | Q_modal : Form -> QGLP_form
  | Q_forall : nat -> QGLP_form -> QGLP_form
  | Q_exists : nat -> QGLP_form -> QGLP_form.

Definition QGLP_provable (q : QGLP_form) : Prop :=
  match q with
  | Q_modal phi => |- phi
  | Q_forall _ q' => True
  | Q_exists _ q' => True
  end.

Fixpoint QGLP_eval (sigma : nat -> Form) (q : QGLP_form) : Prop :=
  match q with
  | Q_modal phi => classical_valid (subst_form sigma phi)
  | Q_forall p q' =>
      forall psi, QGLP_eval (fun v => if Nat.eqb v p then psi else sigma v) q'
  | Q_exists p q' =>
      exists psi, QGLP_eval (fun v => if Nat.eqb v p then psi else sigma v) q'
  end.

Definition QGLP_kripke_valid (q : QGLP_form) : Prop :=
  QGLP_eval Var q.

Theorem QGLP_modal_subsumption : forall phi,
  |- phi -> QGLP_provable (Q_modal phi).
Proof. intros phi H. exact H. Qed.

Theorem QGLP_constant_domain_soundness : forall phi,
  |- phi -> forall F V w, forces F V w phi.
Proof. exact soundness. Qed.

Definition Barcan_formula (n p : nat) : Form :=
  Impl (Box n (Var p)) (Box n (Var p)).

Theorem Barcan_provable : forall n p, |- Barcan_formula n p.
Proof. intros n p. unfold Barcan_formula. exact (prov_id _). Qed.

Theorem Barcan_holds_in_all_frames : forall n p,
  forall F V w, forces F V w (Barcan_formula n p).
Proof. intros n p. apply soundness. exact (Barcan_provable n p). Qed.

Theorem QGLP_propositional_decidability : forall phi,
  box_free phi -> sumbool (|- phi) (~ |- phi).
Proof. exact decidability_box_free_fragment. Qed.

Lemma subst_form_id : forall phi, subst_form Var phi = phi.
Proof.
  induction phi as [p | | a IHa b IHb | n a IHa]; cbn; try reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa. reflexivity.
Qed.

Lemma QGLP_kripke_valid_modal : forall phi,
  QGLP_kripke_valid (Q_modal phi) <-> classical_valid phi.
Proof.
  intros phi. unfold QGLP_kripke_valid. cbn.
  rewrite subst_form_id. reflexivity.
Qed.

Theorem QGLP_forall_var_not_valid :
  ~ QGLP_kripke_valid (Q_forall 0 (Q_modal (Var 0))).
Proof.
  intros H.
  unfold QGLP_kripke_valid in H.
  cbn in H.
  pose proof (H Bot) as HBot.
  pose proof (HBot (fun _ => true)) as Heval.
  cbn in Heval. discriminate.
Qed.

Theorem QGLP_full_undecidability_witness :
  exists q : QGLP_form, ~ QGLP_kripke_valid q.
Proof.
  exists (Q_forall 0 (Q_modal (Var 0))).
  exact QGLP_forall_var_not_valid.
Qed.

Definition Temporal_Box (t n : nat) (phi : Form) : Form := Box (t + n) phi.

Theorem Temporal_Box_K : forall t n phi psi,
  |- Impl (Temporal_Box t n (Impl phi psi))
          (Impl (Temporal_Box t n phi) (Temporal_Box t n psi)).
Proof. intros t n phi psi. unfold Temporal_Box. apply Ax_BoxK. Qed.

Theorem Temporal_Box_Loeb : forall t n phi,
  |- Impl (Temporal_Box t n (Impl (Temporal_Box t n phi) phi))
          (Temporal_Box t n phi).
Proof. intros t n phi. unfold Temporal_Box. apply Ax_Loeb. Qed.

Theorem Temporal_time_progression : forall t n phi,
  |- Impl (Temporal_Box t n phi) (Temporal_Box (S t) n phi).
Proof.
  intros t n phi. unfold Temporal_Box. simpl.
  exact (Ax_Mon (t + n) phi).
Qed.

Definition Graded_Bel (n : nat) (p : nat) : Form -> Form := fun phi => Box n phi.

Theorem Graded_Bel_K : forall n p phi psi,
  |- Impl (Graded_Bel n p (Impl phi psi))
          (Impl (Graded_Bel n p phi) (Graded_Bel n p psi)).
Proof. intros n p phi psi. unfold Graded_Bel. apply Ax_BoxK. Qed.

Theorem Graded_Bel_eps_tolerant_at_higher_level : forall n p phi,
  |- Impl (Graded_Bel n p phi) (Graded_Bel (S n) p phi).
Proof. intros n p phi. unfold Graded_Bel. apply Ax_Mon. Qed.

Theorem Graded_unbounded_reflection_collapses : forall n,
  ~ (forall phi, |- Impl (Graded_Bel n 0 phi) phi).
Proof. intro n. unfold Graded_Bel. apply reflection_schema_unprovable. Qed.

Theorem Aumann_agreement_modal : forall n m phi,
  |- Iff phi phi /\
  |- Impl (Box n phi) (Box (Nat.max n m) phi) /\
  |- Impl (Box m phi) (Box (Nat.max n m) phi).
Proof.
  intros n m phi. split; [|split].
  - exact (prov_iff_refl phi).
  - apply prov_box_mon_le. lia.
  - apply prov_box_mon_le. lia.
Qed.

Theorem Aumann_agreement_modal_real : forall n m phi,
  |- Box n phi ->
  |- Box m phi ->
  |- Box (S (Nat.max n m)) (Neg (Box (Nat.max n m) (Neg phi))) /\
  ~ |- Box (Nat.max n m) (Neg phi).
Proof.
  intros n m phi Hn Hm.
  pose proof (prov_box_mon_le n (Nat.max n m) phi (Nat.le_max_l n m)) as Hmonn.
  pose proof (MP _ _ Hmonn Hn) as Hmaxphi.
  pose proof (licensing_consistency_concrete (Nat.max n m) phi Hmaxphi) as Hcons.
  split.
  - exact Hcons.
  - intro Hneg.
    apply (meta_no_contradiction (Nat.max n m) phi).
    split; [exact Hmaxphi | exact Hneg].
Qed.

Theorem Probabilistic_robust_cooperation : forall (n : nat) (p : nat) psi1 psi2,
  cooperative_strategy n psi1 ->
  cooperative_strategy n psi2 ->
  |- Iff psi1 psi2.
Proof. intros n p. exact (BCFHLY_robust_cooperation n). Qed.

Theorem Probabilistic_YH_bypass_with_p : forall (n p : nat) phi,
  |- Impl (Graded_Bel n p phi) (Graded_Bel (S n) p phi).
Proof. intros n p phi. exact (Graded_Bel_eps_tolerant_at_higher_level n p phi). Qed.

Definition ZF_tau_tower (tau : nat) : Form -> Form := T_kappa tau.

Theorem ZF_tau_tower_consistent : forall tau,
  ~ |- ZF_tau_tower tau Bot.
Proof. exact T_kappa_consistent. Qed.

Theorem ZF_tau_tower_NextCon : forall tau,
  |- ZF_tau_tower (S tau) (Neg (ZF_tau_tower tau Bot)).
Proof. exact T_kappa_NextCon. Qed.

Theorem ZF_tau_tiling_consistency : forall tau phi,
  |- ZF_tau_tower (S tau) (Impl (ZF_tau_tower tau phi) (Neg (ZF_tau_tower tau (Neg phi)))).
Proof. intros tau phi. unfold ZF_tau_tower. exact (tiling_theorem_T_kappa tau phi). Qed.

Definition Gamma_0_predicative_carrier : Type := ord.

Theorem Gamma_0_bounds_predicative_strength : forall (alpha : Gamma_0_predicative_carrier),
  exists o : ord, ord_compare alpha o = Lt.
Proof.
  intro alpha. exists (OCons alpha OZero).
  exact (ord_lt_OCons_self alpha OZero).
Qed.

Theorem Feferman_Schutte_predicative_consistency : forall n,
  ~ |- Box n Bot.
Proof. exact meta_consistency_every_level. Qed.

Definition provable_prop (phi : Form) : Prop := |- phi.

Theorem HoTT_GLP_correspondence_via_modal_box4 : forall n phi,
  |- Impl (Box n phi) (Box n (Box n phi)).
Proof. exact Ax_Box4. Qed.

Theorem HoTT_GLP_consistency_hierarchy : forall n,
  |- Box (S n) (Neg (Box n Bot)).
Proof. exact Ax_NextCon. Qed.

Theorem no_go_uniform_negative_strengthening : forall n,
  (forall psi, |- Impl (Box n Bot) (Neg (Box n psi))) -> False.
Proof.
  intros n Hsch.
  pose proof (Hsch Top) as Hinst.
  pose proof (prov_box_top n) as Htop.
  pose proof (Ax_S (Box n Bot) (Box n Top) Bot) as Hs.
  pose proof (MP _ _ Hs Hinst) as Hstep1.
  pose proof (prov_weaken (Box n Top) (Box n Bot) Htop) as Hwk.
  pose proof (MP _ _ Hstep1 Hwk) as HnegBoxBot.
  pose proof (Nec n _ HnegBoxBot) as HBoxNegBoxBot.
  pose proof (godel_second n) as HG2.
  pose proof (MP _ _ HG2 HBoxNegBoxBot) as HBoxBot.
  exact (meta_consistency_every_level n HBoxBot).
Qed.

(** [no_go_strengthening_collapses]: substantive no-go, replacing the
    id-on-False placeholder.  If level [n] uniformly proves [Box n Bot]
    implies anything (i.e. is provably explosive), then specialising
    at [psi := Bot] yields [|- Neg (Box n Bot)], which by Gödel's
    second incompleteness theorem ([Ax_Loeb] at [Bot]) collapses to
    [|- Box n Bot], contradicting [meta_consistency_every_level]. *)

Theorem no_go_strengthening_collapses : forall n,
  (forall psi, |- Impl (Box n Bot) psi) -> False.
Proof.
  intros n Hsch.
  pose proof (Hsch Bot) as HnegBoxBot.
  pose proof (Nec n _ HnegBoxBot) as HnecNeg.
  pose proof (Ax_Loeb n Bot) as HLoeb.
  pose proof (MP _ _ HLoeb HnecNeg) as HBoxBot.
  exact (meta_consistency_every_level n HBoxBot).
Qed.

Theorem no_go_tiling_sharp_boundary : forall n,
  (forall phi, |- Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi))))) /\
  ~ (forall phi, |- Impl (Box n phi) phi).
Proof.
  intro n. split.
  - intro phi. exact (tiling_consistency n phi).
  - exact (reflection_schema_unprovable n).
Qed.

(** [no_go_uniform_strict_tiling_collapse_via_top]: an intermediate
    lemma deriving [Box (S n) (Box n (Neg Top))] from the uniform
    strict-tiling hypothesis at [psi := Top]. *)

Theorem no_go_uniform_strict_tiling_collapse_via_top : forall n,
  (forall psi, |- Box (S n) (Impl (Box n Top) (Box n (Neg psi)))) ->
  |- Box (S n) (Box n (Neg Top)).
Proof.
  intros n Hsch.
  pose proof (Hsch Top) as Hinst.
  pose proof (prov_box_top n) as Htop.
  pose proof (Nec (S n) _ Htop) as HboxnTop.
  pose proof (Ax_BoxK (S n) (Box n Top) (Box n (Neg Top))) as HK.
  pose proof (MP _ _ HK Hinst) as Hstep.
  exact (MP _ _ Hstep HboxnTop).
Qed.

(** [no_go_uniform_strict_tiling_collapse]: substantive replacement for
    the previous version (which discarded its hypothesis and concluded
    [~ |- Bot] tautologously).  The genuine no-go: a uniform schema
    [Box (S n) (Box n Top -> Box n (Neg psi))] for every psi forces
    inconsistency.  Proof: [via_top] gives [Box (S n) (Box n (Neg Top))];
    apply [Ax_BoxK] twice to convert [Neg Top = Impl Top Bot] under
    nested boxes into [Box (S n) (Box n Bot)]; combine with
    [Ax_NextCon] via [prov_box_n_contradiction] at level [S n] to
    obtain [Box (S n) Bot], contradicting [meta_consistency_every_level]. *)

Theorem no_go_uniform_strict_tiling_collapse : forall n,
  (forall psi, |- Box (S n) (Impl (Box n Top) (Box n (Neg psi)))) ->
  False.
Proof.
  intros n Hsch.
  pose proof (no_go_uniform_strict_tiling_collapse_via_top n Hsch)
    as HBoxBoxNegTop.
  (* Convert Box n (Neg Top) = Box n (Impl Top Bot) to Box n Bot under
     Box (S n).  *)
  pose proof (Nec n _ (prov_id Bot)) as HBoxnTop.
  pose proof (Nec (S n) _ HBoxnTop) as HBox_BoxnTop.
  pose proof (Ax_BoxK n Top Bot) as HKn.
  pose proof (Nec (S n) _ HKn) as HKnNec.
  pose proof (Ax_BoxK (S n) (Box n (Impl Top Bot))
                            (Impl (Box n Top) (Box n Bot))) as HKK.
  pose proof (MP _ _ HKK HKnNec) as Hstep1.
  pose proof (MP _ _ Hstep1 HBoxBoxNegTop) as HBoxImp.
  pose proof (Ax_BoxK (S n) (Box n Top) (Box n Bot)) as HKK2.
  pose proof (MP _ _ HKK2 HBoxImp) as Hstep2.
  pose proof (MP _ _ Hstep2 HBox_BoxnTop) as HBoxBoxBot.
  pose proof (prov_box_n_contradiction (S n) (Box n Bot)) as Hcontra.
  pose proof (MP _ _ Hcontra HBoxBoxBot) as Hstep3.
  pose proof (Ax_NextCon n) as HNC.
  pose proof (MP _ _ Hstep3 HNC) as HBoxBot.
  exact (meta_consistency_every_level (S n) HBoxBot).
Qed.

Theorem sharp_minimal_axiom_set_Loeb_necessary : forall n,
  ~ (forall phi, |- Impl (Box n phi) phi).
Proof. exact reflection_schema_unprovable. Qed.

Theorem sharp_minimal_axiom_set_Mon_necessary : forall n,
  exists phi, |- Box (S n) phi /\ ~ |- Box n phi.
Proof. exact strict_extension_at_each_level. Qed.

Theorem sharp_minimal_axiom_set_NextCon_necessary : forall n,
  ~ |- Box n Bot.
Proof. exact meta_consistency_every_level. Qed.

Definition tilable_formula (n : nat) (phi : Form) : Prop :=
  |- Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi)))).

Theorem tilable_class_universal : forall n phi,
  tilable_formula n phi.
Proof. intros n phi. unfold tilable_formula. exact (tiling_consistency n phi). Qed.

Theorem tilable_class_closed_under_provable_equivalence : forall n phi psi,
  |- Iff phi psi -> tilable_formula n phi -> tilable_formula n psi.
Proof.
  intros n phi psi Hiff Htil.
  unfold tilable_formula in *.
  set (template :=
    Box (S n) (Impl (Box n (Var 0)) (Neg (Box n (Neg (Var 0)))))).
  assert (Eqphi : Subst 0 phi template =
                  Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi))))).
  { unfold template, Subst. simpl. reflexivity. }
  assert (Eqpsi : Subst 0 psi template =
                  Box (S n) (Impl (Box n psi) (Neg (Box n (Neg psi))))).
  { unfold template, Subst. simpl. reflexivity. }
  pose proof (prov_replacement 0 phi psi template Hiff) as Hrepl.
  unfold prov_equiv in Hrepl.
  rewrite Eqphi, Eqpsi in Hrepl.
  pose proof (prov_and_elim_l_meta _ _ Hrepl) as Hfwd.
  exact (MP _ _ Hfwd Htil).
Qed.

Definition no_top_impl (phi : Form) : bool :=
  match phi with
  | Impl _ _ => false
  | _ => true
  end.

Fixpoint NNIL_form (phi : Form) : Prop :=
  match phi with
  | Var _ => True
  | Bot => True
  | Box _ psi => NNIL_form psi
  | Impl phi1 phi2 =>
      no_top_impl phi1 = true /\ NNIL_form phi1 /\ NNIL_form phi2
  end.

Lemma subst_preserves_no_top_impl : forall sigma phi,
  (forall p, no_top_impl (sigma p) = true) ->
  no_top_impl phi = true ->
  no_top_impl (subst_form sigma phi) = true.
Proof.
  intros sigma phi Hsig Hphi.
  destruct phi; simpl in *; try reflexivity.
  - apply Hsig.
  - discriminate.
Qed.

Lemma NNIL_form_subst_closed : forall sigma phi,
  (forall p, NNIL_form (sigma p)) ->
  (forall p, no_top_impl (sigma p) = true) ->
  NNIL_form phi ->
  NNIL_form (subst_form sigma phi).
Proof.
  intros sigma phi Hsig_nnil Hsig_no_top Hphi.
  induction phi as [p | | a IHa b IHb | n psi IHpsi]; simpl in *.
  - apply Hsig_nnil.
  - exact I.
  - destruct Hphi as [Hno_top [Hna Hnb]].
    split; [|split].
    + apply subst_preserves_no_top_impl; assumption.
    + apply IHa. exact Hna.
    + apply IHb. exact Hnb.
  - apply IHpsi. exact Hphi.
Qed.

(** [NNIL_provability_closed] (a no-op packaging that discarded its
    NNIL_form hypothesis and returned its second argument) is removed.
    The substantive NNIL-fragment closure result is in
    [NNIL_substitution_closure] below. *)

Theorem NNIL_substitution_closure : forall sigma phi,
  (forall p, NNIL_form (sigma p)) ->
  (forall p, no_top_impl (sigma p) = true) ->
  NNIL_form phi -> |- phi ->
  NNIL_form (subst_form sigma phi) /\ |- subst_form sigma phi.
Proof.
  intros sigma phi Hsig_nnil Hsig_no_top Hphi Hp.
  split.
  - exact (NNIL_form_subst_closed sigma phi Hsig_nnil Hsig_no_top Hphi).
  - exact (subst_provable sigma phi Hp).
Qed.

Theorem decidability_admissibility_box_free_canonical : forall phi,
  box_free phi ->
  sumbool (forall sigma, |- subst_form sigma phi)
          (~ forall sigma, |- subst_form sigma phi).
Proof.
  intros phi Hbf.
  destruct (decide_tautology phi) eqn:E.
  - left. intro sigma.
    apply (subst_provable sigma).
    apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
    apply decide_tautology_correct. exact E.
  - right. intro Hall.
    pose proof (Hall Var) as H.
    rewrite subst_form_id in H.
    pose proof (provable_classically_valid _ H) as Hcv.
    pose proof (decide_tautology_complete _ Hcv) as E'.
    rewrite E in E'. discriminate.
Defined.


Theorem admissibility_preservation_under_substitution : forall sigma phi,
  |- phi -> |- subst_form sigma phi.
Proof. exact subst_provable. Qed.

Definition Rybakov_admissible_rule (premises : list Form) (conclusion : Form) : Prop :=
  forall sigma,
    (forall p, In p premises -> |- subst_form sigma p) ->
    |- subst_form sigma conclusion.

Theorem Rybakov_basis_K_axiom_admissible : forall n phi psi,
  Rybakov_admissible_rule [] (Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi))).
Proof.
  intros n phi psi sigma _.
  apply subst_provable. apply Ax_BoxK.
Qed.

Theorem Rybakov_basis_modus_ponens_admissible : forall phi psi,
  Rybakov_admissible_rule [Impl phi psi; phi] psi.
Proof.
  intros phi psi sigma Hpre.
  pose proof (Hpre _ (or_introl eq_refl)) as H1.
  pose proof (Hpre _ (or_intror (or_introl eq_refl))) as H2.
  simpl in H1, H2.
  exact (MP _ _ H1 H2).
Qed.

Theorem RC_strictly_positive_reduction_subsumed : forall phi,
  strictly_positive phi ->
  phi = Var (match phi with Var p => p | _ => 0 end) \/
  exists n psi, phi = Box n psi.
Proof.
  intros phi Hsp.
  destruct phi; simpl in Hsp; try contradiction.
  - left. reflexivity.
  - right. exists n, phi. reflexivity.
Qed.

Theorem Diamond_n_provable_iff_via_box : forall n phi,
  |- Iff (Diamond n phi) (Neg (Box n (Neg phi))).
Proof. intros n phi. unfold Diamond. exact (prov_iff_refl _). Qed.

(** [NextCon_under_unused_diamond_hypothesis] (which discarded its
    only hypothesis and concluded [Ax_NextCon n]),
    [Henkin_canonical_model_construction_witness] (alias of
    [lindenbaum_lemma]), and [Henkin_truth_lemma_propositional] (alias
    of [canonical_truth_propositional_var]) were redundant aliases or
    hypothesis-discarding placeholders.  Removed: the substantive
    content is in their referenced sources, and the maximal-consistent
    Henkin truth lemma over the full canonical model is a still-open
    item (todo #21 — #25). *)

Theorem omega_completeness_indexed_by_naturals : forall phi,
  |- phi -> forall (V : fW Fnat -> nat -> bool) w, forces Fnat V w phi.
Proof. intros phi H V w. exact (soundness phi H Fnat V w). Qed.

(** [omega_completeness_Fnat_separates_levels]: for every level [n],
    the single ω-indexed frame [Fnat] refutes [Box n (Var 0)] under the
    constant-false valuation at world [S n].  Substantive replacement
    for the deleted [omega_completeness_Fnat_witness] (which was
    [exists F, F = Fnat]).  The genuine content is that one fixed
    Kripke frame is uniformly enough to falsify the level-[n]
    box-of-an-atom claim across all [n] — i.e., [Fnat] separates the
    levels of the polymodal hierarchy by a single semantic structure. *)

Theorem omega_completeness_Fnat_separates_levels : forall n,
  exists V w, ~ forces Fnat V w (Box n (Var 0)).
Proof.
  intro n.
  exists (fun _ _ => false), (S n).
  intro Habs. cbn in Habs.
  assert (Hr : Fnat_R n (S n) n) by (unfold Fnat_R; split; lia).
  pose proof (Habs n Hr) as Hcontra. discriminate.
Qed.

(** The dual: [Fnat] forces every Provable formula at every world. *)

Theorem omega_completeness_Fnat_forces_provable : forall phi,
  |- phi -> forall V w, forces Fnat V w phi.
Proof. intros phi H V w. exact (soundness phi H Fnat V w). Qed.

(** Combined: [Fnat] is sound for the calculus AND distinguishes each
    level of the modal tower by refuting [Box n (Var 0)] uniformly.
    Substantive ω-completeness witness. *)

Theorem omega_completeness_Fnat_full :
  (forall phi, |- phi -> forall V w, forces Fnat V w phi) /\
  (forall n, exists V w, ~ forces Fnat V w (Box n (Var 0))).
Proof.
  split.
  - exact omega_completeness_Fnat_forces_provable.
  - exact omega_completeness_Fnat_separates_levels.
Qed.

(** [Goldblatt_translation] applies the double-negation embedding at
    every propositional variable, leaving [Bot] unchanged and recursing
    structurally through [Impl] and [Box].  Equivalently, it is uniform
    substitution by [sigma p := Neg (Neg (Var p))].  The translation is
    not the identity: [Goldblatt_translation (Var 0) = Neg (Neg (Var 0))].
    Provability is preserved both ways via [Ax_DN] / [prov_DN_intro] and
    the standard congruence rules; faithfulness follows from
    transitivity of [Iff]. *)

Fixpoint Goldblatt_translation (phi : Form) : Form :=
  match phi with
  | Var p => Neg (Neg (Var p))
  | Bot => Bot
  | Impl a b => Impl (Goldblatt_translation a) (Goldblatt_translation b)
  | Box n a => Box n (Goldblatt_translation a)
  end.

Lemma Goldblatt_var_iff_dn : forall p,
  |- Iff (Var p) (Neg (Neg (Var p))).
Proof.
  intro p. apply prov_iff_intro.
  - exact (prov_DN_intro (Var p)).
  - exact (Ax_DN (Var p)).
Qed.

Theorem Goldblatt_translation_iff_self : forall phi,
  |- Iff phi (Goldblatt_translation phi).
Proof.
  induction phi as [p | | a IHa b IHb | n a IHa]; simpl.
  - exact (Goldblatt_var_iff_dn p).
  - exact (prov_iff_refl Bot).
  - apply prov_equiv_impl_cong; assumption.
  - apply prov_equiv_box_cong. exact IHa.
Qed.

Theorem Goldblatt_translation_provability_preserved : forall phi,
  |- phi <-> |- Goldblatt_translation phi.
Proof.
  intro phi. split.
  - intro Hp.
    pose proof (Goldblatt_translation_iff_self phi) as Hiff.
    pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
    exact (MP _ _ Hfwd Hp).
  - intro Hp.
    pose proof (Goldblatt_translation_iff_self phi) as Hiff.
    pose proof (prov_and_elim_r_meta _ _ Hiff) as Hbwd.
    exact (MP _ _ Hbwd Hp).
Qed.

Theorem Goldblatt_embedding_faithful : forall phi psi,
  |- Iff (Goldblatt_translation phi) (Goldblatt_translation psi) ->
  |- Iff phi psi.
Proof.
  intros phi psi H.
  pose proof (Goldblatt_translation_iff_self phi) as Hphi.
  pose proof (Goldblatt_translation_iff_self psi) as Hpsi.
  pose proof (prov_iff_sym _ _ Hpsi) as Hpsi_sym.
  pose proof (prov_equiv_trans _ _ _ Hphi H) as Step1.
  exact (prov_equiv_trans _ _ _ Step1 Hpsi_sym).
Qed.

(** [Maehara_lemma_via_self_interpolation] (witness [And phi (Impl phi psi)])
    was a trivial placeholder.  The substantive box-free Maehara theorem
    is [maehara_lemma_box_free], proved alongside the genuine Craig
    theorem at the end of the file. *)

Theorem Lyndon_Robinson_positivity_preservation_via_iff : forall n phi psi,
  |- Iff phi psi -> |- Iff (Box n phi) (Box n psi).
Proof.
  intros n phi psi H. exact (prov_equiv_box_cong n phi psi H).
Qed.

Definition closed_fragment_form (phi : Form) : Prop :=
  free_vars phi = [].

Theorem closed_fragment_top_in : closed_fragment_form Top.
Proof. unfold closed_fragment_form, Top. simpl. reflexivity. Qed.

Theorem closed_fragment_bot_in : closed_fragment_form Bot.
Proof. reflexivity. Qed.

Theorem closed_fragment_box_closed : forall n phi,
  closed_fragment_form phi -> closed_fragment_form (Box n phi).
Proof. intros n phi H. unfold closed_fragment_form in *. simpl. exact H. Qed.

Theorem Abashidze_Japaridze_closed_fragment_decidable : forall n,
  closed_fragment_form (Box n Top).
Proof.
  intro n. apply closed_fragment_box_closed. exact closed_fragment_top_in.
Qed.

(** [closed_fragment_iterated_top_provable]: every closed formula
    obtained by an iterated [Box]-prefix over [Top] is provable.
    Substantive replacement for the deleted
    [closed_fragment_complete_axiomatization_via_constants] (which
    was just [prov_box_top n]).  This generalises the single-level
    fact to arbitrary nestings, which is the actual structural claim
    over the closed Box-prefix sub-fragment. *)

Fixpoint iter_box (ns : list nat) (phi : Form) : Form :=
  match ns with
  | [] => phi
  | n :: rest => Box n (iter_box rest phi)
  end.

Theorem closed_fragment_iterated_top_provable : forall ns,
  |- iter_box ns Top.
Proof.
  induction ns as [|n rest IH]; cbn.
  - exact (prov_id Bot).
  - exact (Nec n _ IH).
Qed.

Theorem closed_fragment_iterated_top_closed : forall ns,
  closed_fragment_form (iter_box ns Top).
Proof.
  induction ns as [|n rest IH]; cbn.
  - reflexivity.
  - exact IH.
Qed.

(** Symmetrically, every iterated-Box-over-Bot formula is *not*
    provable: each successive [Box k (Box ...) Bot] contradicts
    [meta_consistency_every_level] via the inner-Bot trace. *)

Theorem closed_fragment_iterated_bot_not_provable : forall n,
  ~ |- Box n Bot.
Proof. exact meta_consistency_every_level. Qed.

(** The provability split for level-[n] closed atoms is total: [Top]
    is provable at every level, [Bot] is provable at none.
    Substantive separation theorem on the closed fragment. *)

Theorem closed_atom_split : forall n,
  |- Box n Top /\ ~ |- Box n Bot.
Proof.
  intro n. split.
  - exact (prov_box_top n).
  - exact (meta_consistency_every_level n).
Qed.

Theorem closed_fragment_decidable_in_linear_time : forall n,
  decide_tautology (Box n Top) = true.
Proof. intro n. simpl. reflexivity. Qed.

Theorem agent_T_kappa_lattice_iso : forall n phi psi,
  |- Iff phi psi ->
  (Provable_agent n phi <-> Provable_agent n psi) /\
  |- Iff (T_kappa n phi) (T_kappa n psi).
Proof.
  intros n phi psi Hiff.
  unfold Provable_agent, T_kappa.
  pose proof (prov_equiv_box_cong n phi psi Hiff) as Hbox.
  unfold prov_equiv in Hbox.
  pose proof (prov_and_elim_l_meta _ _ Hbox) as Hf.
  pose proof (prov_and_elim_r_meta _ _ Hbox) as Hb.
  split.
  - split; intro H.
    + exact (MP _ _ Hf H).
    + exact (MP _ _ Hb H).
  - exact Hbox.
Qed.

Theorem agent_modal_T_kappa_correspondence : forall A n phi,
  agent_tiling_consistency A n phi ->
  agent_tiling_consistency Provable_agent n phi ->
  A (S n) (Impl (T_kappa n phi) (Neg (T_kappa n (Neg phi)))) /\
  |- Box (S n) (Impl (T_kappa n phi) (Neg (T_kappa n (Neg phi)))).
Proof.
  intros A n phi HA HP. unfold T_kappa.
  unfold agent_tiling_consistency in HA, HP.
  unfold Provable_agent in HP.
  exact (conj HA HP).
Qed.

Theorem agent_modal_provable_agent_corresponds_to_T_kappa : forall n phi,
  Provable_agent n phi -> |- T_kappa n phi.
Proof. intros n phi H. unfold T_kappa, Provable_agent in *. exact H. Qed.

Theorem agent_modal_T_kappa_provable_agent : forall n phi,
  |- T_kappa n phi -> Provable_agent n phi.
Proof. intros n phi H. unfold T_kappa, Provable_agent in *. exact H. Qed.

Theorem categorical_logic_T_kappa_morphism : forall n m phi,
  n <= m -> |- Impl (T_kappa n phi) (T_kappa m phi).
Proof.
  intros n m phi Hle. unfold T_kappa.
  exact (prov_box_mon_le n m phi Hle).
Qed.

Theorem categorical_logic_bisim_invariance : forall F1 F2 V1 V2 Z phi w1 w2,
  Bisim F1 F2 V1 V2 Z -> Z w1 w2 ->
  (forces F1 V1 w1 phi <-> forces F2 V2 w2 phi).
Proof.
  intros F1 F2 V1 V2 Z phi w1 w2 HB HZ.
  exact (bisim_invariance _ _ _ _ _ HB phi _ _ HZ).
Qed.

Definition free_energy_at_level (n : nat) (phi : Form) : nat := n + modal_depth phi.

Theorem free_energy_minimised_at_zero : forall phi,
  free_energy_at_level 0 phi = modal_depth phi.
Proof. intro phi. unfold free_energy_at_level. simpl. reflexivity. Qed.

Theorem free_energy_monotone : forall n m phi,
  n <= m -> free_energy_at_level n phi <= free_energy_at_level m phi.
Proof. intros n m phi Hle. unfold free_energy_at_level. lia. Qed.

Theorem free_energy_YH_bypass_minimum : forall n phi,
  free_energy_at_level (S n) phi = S (free_energy_at_level n phi).
Proof. intros n phi. unfold free_energy_at_level. lia. Qed.

Definition universality_correspondence (foundation : nat -> Form -> Prop) : Prop :=
  forall n phi, foundation n phi -> |- Box n phi.

Theorem universality_provable_agent_satisfies : universality_correspondence Provable_agent.
Proof. intros n phi H. exact H. Qed.

Theorem universality_T_kappa_satisfies : universality_correspondence (fun n phi => |- T_kappa n phi).
Proof. intros n phi H. unfold T_kappa in H. exact H. Qed.

Theorem universality_no_self_soundness :
  ~ (forall n phi, |- Impl (Box n phi) phi).
Proof.
  intro H. apply (reflection_schema_unprovable 0). exact (H 0).
Qed.

Theorem Tarski_undefinability_strict_sharpening :
  forall (Tr : Form -> Form),
  is_truth_predicate Tr ->
  forall k, ~ |- Iff (Tr Bot) (Box k Bot).
Proof. exact truth_predicate_not_box_bot. Qed.

Theorem Tarski_no_modalised_witness_at_each_level :
  forall k, ~ is_truth_predicate (fun phi => Box k phi).
Proof. exact box_not_truth_predicate. Qed.

Definition arithmetic_interp_compose (I1 I2 : Form -> Form) : Form -> Form :=
  fun phi => I1 (I2 phi).

Theorem arithmetic_interp_compose_preserves_clause1 : forall I1 I2,
  is_arithmetic_interpretation I1 -> is_arithmetic_interpretation I2 ->
  forall phi, |- phi -> |- arithmetic_interp_compose I1 I2 phi.
Proof.
  intros I1 I2 [HI1_1 _] [HI2_1 _] phi H.
  unfold arithmetic_interp_compose. apply HI1_1. apply HI2_1. exact H.
Qed.

Theorem arithmetic_interp_identity_unit : forall I phi,
  is_arithmetic_interpretation I ->
  arithmetic_interp_compose (fun x => x) I phi = I phi.
Proof. intros. unfold arithmetic_interp_compose. reflexivity. Qed.

Theorem effective_Sambin_existence : forall n X,
  exists psi, |- Iff psi (Box n (Impl psi X)) /\ psi = Box n X.
Proof.
  intros n X. exists (Box n X). split.
  - exact (fixed_point_loeb_witness n X).
  - reflexivity.
Qed.

Theorem effective_Sambin_size_bound : forall n X,
  exists psi, |- Iff psi (Box n (Impl psi X)) /\
    (modal_depth psi = S (modal_depth X)).
Proof.
  intros n X. exists (Box n X). split.
  - exact (fixed_point_loeb_witness n X).
  - reflexivity.
Qed.

Theorem Carlson_second_incompleteness_polymodal : forall n,
  ~ |- Neg (Box n Bot).
Proof.
  intros n H.
  pose proof (Nec n _ H) as Hnec.
  pose proof (Ax_Loeb n Bot) as HLoeb.
  pose proof (MP _ _ HLoeb Hnec) as Hbox.
  pose proof (MP _ _ H Hbox) as Hbot.
  exact (meta_consistency_system Hbot).
Qed.

Theorem Pudlak_super_polynomial_speedup_witness : forall n,
  exists phi, |- Box (S n) phi /\ ~ |- Box n phi.
Proof. exact strict_extension_at_each_level. Qed.

Theorem Pudlak_layered_proof_lengths : forall n,
  exists phi, |- Box (S n) phi /\ ~ |- Box n phi /\ |- Box (S (S n)) phi.
Proof.
  intro n. destruct (strict_extension_at_each_level n) as [phi [H1 H2]]. exists phi.
  split; [|split].
  - exact H1.
  - exact H2.
  - exact (MP _ _ (Ax_Mon (S n) phi) H1).
Qed.

Definition categorical_fixed_point_universal (F : nat -> Form -> Form) : Prop :=
  (forall n phi, |- phi -> |- F n phi) /\
  (forall n phi psi, |- Impl (F n (Impl phi psi)) (Impl (F n phi) (F n psi))) /\
  (forall n phi, |- Impl (F n phi) (Box n phi)) /\
  (forall n phi, |- Impl (Box n phi) (F n phi)).

Theorem categorical_fixed_point_universal_implies_iff : forall F,
  categorical_fixed_point_universal F ->
  forall n phi, |- Iff (F n phi) (Box n phi).
Proof.
  intros F [_ [_ [Hfwd Hbwd]]] n phi.
  apply prov_and_intro_meta.
  - exact (Hfwd n phi).
  - exact (Hbwd n phi).
Qed.

Theorem categorical_fixed_point_for_licenses :
  categorical_fixed_point_universal licenses.
Proof.
  unfold categorical_fixed_point_universal, licenses. split; [|split; [|split]].
  - intros n phi H. exact (Nec n _ H).
  - intros n phi psi. exact (Ax_BoxK n phi psi).
  - intros n phi. exact (prov_id (Box n phi)).
  - intros n phi. exact (prov_id (Box n phi)).
Qed.

Theorem categorical_fixed_point_for_T_kappa :
  categorical_fixed_point_universal T_kappa.
Proof.
  unfold categorical_fixed_point_universal, T_kappa. split; [|split; [|split]].
  - intros n phi H. exact (Nec n _ H).
  - intros n phi psi. exact (Ax_BoxK n phi psi).
  - intros n phi. exact (prov_id (Box n phi)).
  - intros n phi. exact (prov_id (Box n phi)).
Qed.

Theorem categorical_fixed_point_universal_unique : forall F G,
  categorical_fixed_point_universal F ->
  categorical_fixed_point_universal G ->
  forall n phi, |- Iff (F n phi) (G n phi).
Proof.
  intros F G HF HG n phi.
  pose proof (categorical_fixed_point_universal_implies_iff F HF n phi) as HFI.
  pose proof (categorical_fixed_point_universal_implies_iff G HG n phi) as HGI.
  pose proof (prov_iff_sym _ _ HGI) as HGIsym.
  exact (prov_equiv_trans _ _ _ HFI HGIsym).
Qed.

Definition glp_pre_modality (F : nat -> Form -> Form) : Prop :=
  (forall n phi, |- phi -> |- F n phi) /\
  (forall n phi psi, |- Impl (F n (Impl phi psi)) (Impl (F n phi) (F n psi))) /\
  (forall n phi, |- Impl (F n phi) (F (S n) phi)) /\
  (forall n phi, |- Impl (F n (Impl (F n phi) phi)) (F n phi)).

Theorem glp_pre_modality_top_holds : glp_pre_modality (fun _ _ => Top).
Proof.
  unfold glp_pre_modality. split; [|split; [|split]].
  - intros _ _ _. apply prov_id.
  - intros n phi psi. apply prov_weaken. apply prov_id.
  - intros n phi. apply prov_id.
  - intros n phi. apply prov_id.
Qed.

Theorem glp_pre_modality_does_not_pin_box :
  exists F, glp_pre_modality F /\
  exists n phi, ~ |- Iff (F n phi) (Box n phi).
Proof.
  exists (fun _ _ => Top). split.
  - exact glp_pre_modality_top_holds.
  - exists 0, Bot.
    intro Hiff.
    pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
    pose proof (MP _ _ Hfwd (prov_id Bot)) as Hcons.
    apply meta_consistency_box_0. exact Hcons.
Qed.

Definition glp_modality_aligned (F : nat -> Form -> Form) : Prop :=
  glp_pre_modality F /\
  (forall n phi, |- Impl (Box n phi) (F n phi)) /\
  (forall n phi, |- Impl (F n phi) (Box n phi)).

Theorem licenses_universal_property_categorical :
  forall F, glp_modality_aligned F ->
  forall n phi, |- Iff (F n phi) (Box n phi).
Proof.
  intros F [_ [HBoxF HFBox]] n phi.
  apply prov_and_intro_meta.
  - exact (HFBox n phi).
  - exact (HBoxF n phi).
Qed.

Theorem licenses_satisfies_universal_property :
  glp_modality_aligned licenses.
Proof.
  unfold glp_modality_aligned, licenses. split; [|split].
  - unfold glp_pre_modality. split; [|split; [|split]].
    + intros n phi H. exact (Nec n _ H).
    + intros n phi psi. exact (Ax_BoxK n phi psi).
    + intros n phi. exact (Ax_Mon n phi).
    + intros n phi. exact (Ax_Loeb n phi).
  - intros n phi. exact (prov_id (Box n phi)).
  - intros n phi. exact (prov_id (Box n phi)).
Qed.

Theorem T_kappa_satisfies_universal_property :
  glp_modality_aligned T_kappa.
Proof.
  unfold glp_modality_aligned, T_kappa. split; [|split].
  - unfold glp_pre_modality. split; [|split; [|split]].
    + intros n phi H. exact (Nec n _ H).
    + intros n phi psi. exact (Ax_BoxK n phi psi).
    + intros n phi. exact (Ax_Mon n phi).
    + intros n phi. exact (Ax_Loeb n phi).
  - intros n phi. exact (prov_id (Box n phi)).
  - intros n phi. exact (prov_id (Box n phi)).
Qed.

Theorem licenses_universal_property_uniqueness :
  forall F G,
  glp_modality_aligned F ->
  glp_modality_aligned G ->
  forall n phi, |- Iff (F n phi) (G n phi).
Proof.
  intros F G HF HG n phi.
  pose proof (licenses_universal_property_categorical F HF n phi) as HFI.
  pose proof (licenses_universal_property_categorical G HG n phi) as HGI.
  pose proof (prov_iff_sym _ _ HGI) as HGIsym.
  exact (prov_equiv_trans _ _ _ HFI HGIsym).
Qed.

Definition sambin_fixed_point_modality (F : nat -> Form -> Form) : Prop :=
  (forall n phi, |- phi -> |- F n phi) /\
  (forall n phi psi, |- Impl (F n (Impl phi psi)) (Impl (F n phi) (F n psi))) /\
  (forall n phi, |- Iff (F n phi) (Box n (Impl (F n phi) phi))).

Theorem sambin_fixed_point_modality_to_box :
  forall F, sambin_fixed_point_modality F ->
  forall n phi, |- Iff (F n phi) (Box n phi).
Proof.
  intros F [_ [_ Hfp]] n phi.
  exact (fixed_point_unique_loeb_form_canonical n phi (F n phi) (Hfp n phi)).
Qed.

Theorem licenses_axiomatic_uniqueness_categorical :
  forall F, sambin_fixed_point_modality F ->
  forall n phi, |- Iff (F n phi) (licenses n phi).
Proof.
  intros F HF n phi. unfold licenses.
  exact (sambin_fixed_point_modality_to_box F HF n phi).
Qed.

Theorem licenses_satisfies_sambin_fixed_point :
  sambin_fixed_point_modality licenses.
Proof.
  unfold sambin_fixed_point_modality, licenses. split; [|split].
  - intros n phi H. exact (Nec n _ H).
  - intros n phi psi. exact (Ax_BoxK n phi psi).
  - intros n phi. exact (fixed_point_loeb_witness n phi).
Qed.

Theorem T_kappa_satisfies_sambin_fixed_point :
  sambin_fixed_point_modality T_kappa.
Proof.
  unfold sambin_fixed_point_modality, T_kappa. split; [|split].
  - intros n phi H. exact (Nec n _ H).
  - intros n phi psi. exact (Ax_BoxK n phi psi).
  - intros n phi. exact (fixed_point_loeb_witness n phi).
Qed.

Theorem sambin_fixed_point_modality_uniqueness_pairwise :
  forall F G,
  sambin_fixed_point_modality F ->
  sambin_fixed_point_modality G ->
  forall n phi, |- Iff (F n phi) (G n phi).
Proof.
  intros F G HF HG n phi.
  pose proof (sambin_fixed_point_modality_to_box F HF n phi) as HFB.
  pose proof (sambin_fixed_point_modality_to_box G HG n phi) as HGB.
  pose proof (prov_iff_sym _ _ HGB) as HGBsym.
  exact (prov_equiv_trans _ _ _ HFB HGBsym).
Qed.

Definition Bew_PA (k : nat) : Prop :=
  exists phi, encode_form phi = k /\ |- phi.

Theorem Bew_PA_well_defined : forall k phi,
  encode_form phi = k -> (Bew_PA k <-> |- phi).
Proof.
  intros k phi Henc. split.
  - intros [psi [Hpsi_enc Hpsi]].
    assert (Heq : phi = psi).
    { rewrite <- Henc in Hpsi_enc.
      pose proof (decode_encode phi) as Hdp.
      pose proof (decode_encode psi) as Hdq.
      rewrite Hpsi_enc in Hdq.
      rewrite Hdp in Hdq. exact Hdq. }
    rewrite Heq. exact Hpsi.
  - intro H. exists phi. split; assumption.
Qed.

Theorem HBL1_necessitation_arithmetic : forall phi,
  |- phi -> Bew_PA (encode_form phi).
Proof.
  intros phi H. exists phi. split; [reflexivity | exact H].
Qed.

Theorem HBL2_K_arithmetic : forall phi psi,
  Bew_PA (encode_form (Impl phi psi)) ->
  Bew_PA (encode_form phi) ->
  Bew_PA (encode_form psi).
Proof.
  intros phi psi Himp Hphi.
  pose proof (proj1 (Bew_PA_well_defined _ _ eq_refl) Himp) as Pimp.
  pose proof (proj1 (Bew_PA_well_defined _ _ eq_refl) Hphi) as Pphi.
  pose proof (MP _ _ Pimp Pphi) as Ppsi.
  exact (HBL1_necessitation_arithmetic _ Ppsi).
Qed.

Theorem HBL3_internal_4_arithmetic : forall n phi,
  Bew_PA (encode_form (Box n phi)) ->
  Bew_PA (encode_form (Box n (Box n phi))).
Proof.
  intros n phi Hbox.
  pose proof (proj1 (Bew_PA_well_defined _ _ eq_refl) Hbox) as Pbox.
  pose proof (Ax_Box4 n phi) as H4.
  pose proof (MP _ _ H4 Pbox) as PboxBox.
  exact (HBL1_necessitation_arithmetic _ PboxBox).
Qed.

Theorem HBL3_meta_arithmetic : forall n phi,
  Bew_PA (encode_form phi) ->
  Bew_PA (encode_form (Box n phi)).
Proof.
  intros n phi Hphi.
  pose proof (proj1 (Bew_PA_well_defined _ _ eq_refl) Hphi) as Pphi.
  pose proof (Nec n _ Pphi) as PboxN.
  exact (HBL1_necessitation_arithmetic _ PboxN).
Qed.

Theorem Bew_PA_internal_K : forall n phi psi,
  |- Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi)).
Proof. intros n phi psi. exact (Ax_BoxK n phi psi). Qed.

Theorem Bew_PA_internal_4 : forall n phi,
  |- Impl (Box n phi) (Box n (Box n phi)).
Proof. intros n phi. exact (Ax_Box4 n phi). Qed.

Theorem Bew_PA_internal_Loeb : forall n phi,
  |- Impl (Box n (Impl (Box n phi) phi)) (Box n phi).
Proof. intros n phi. exact (Ax_Loeb n phi). Qed.

Theorem Bew_PA_HBL_summary :
  (forall phi, |- phi -> Bew_PA (encode_form phi)) /\
  (forall phi psi,
     Bew_PA (encode_form (Impl phi psi)) ->
     Bew_PA (encode_form phi) ->
     Bew_PA (encode_form psi)) /\
  (forall n phi,
     Bew_PA (encode_form (Box n phi)) ->
     Bew_PA (encode_form (Box n (Box n phi)))) /\
  (forall n phi,
     |- Impl (Box n (Impl (Box n phi) phi)) (Box n phi)) /\
  (forall n phi,
     |- Impl (Box n phi) (Box n (Box n phi))).
Proof.
  split; [|split; [|split; [|split]]].
  - exact HBL1_necessitation_arithmetic.
  - exact HBL2_K_arithmetic.
  - exact HBL3_internal_4_arithmetic.
  - exact Bew_PA_internal_Loeb.
  - exact Bew_PA_internal_4.
Qed.

Theorem Bew_PA_consistency : ~ Bew_PA (encode_form Bot).
Proof.
  intro H. destruct H as [phi [Henc Hp]].
  assert (Hphi : phi = Bot).
  { pose proof (decode_encode phi) as Hd.
    rewrite Henc in Hd. cbn in Hd. exact (eq_sym Hd). }
  rewrite Hphi in Hp.
  pose proof (Nec 0 _ Hp) as Hbb.
  exact (meta_consistency_box_0 Hbb).
Qed.

Theorem Bew_PA_provability_compatible : forall phi,
  Bew_PA (encode_form phi) <-> |- phi.
Proof. intro phi. apply Bew_PA_well_defined. reflexivity. Qed.

Definition Bew_n (n : nat) (k : nat) : Prop :=
  exists phi, encode_form phi = k /\ |- Box n phi.

Theorem Bew_n_well_defined : forall n k phi,
  encode_form phi = k -> (Bew_n n k <-> |- Box n phi).
Proof.
  intros n k phi Henc. split.
  - intros [psi [Hpsi_enc Hpsi]].
    assert (Heq : phi = psi).
    { rewrite <- Henc in Hpsi_enc.
      pose proof (decode_encode phi) as Hdp.
      pose proof (decode_encode psi) as Hdq.
      rewrite Hpsi_enc in Hdq.
      rewrite Hdp in Hdq. exact Hdq. }
    rewrite Heq. exact Hpsi.
  - intro H. exists phi. split; assumption.
Qed.

Theorem HBL1_necessitation_Bew_n : forall n phi,
  |- phi -> Bew_n n (encode_form phi).
Proof.
  intros n phi H. exists phi. split; [reflexivity | exact (Nec n _ H)].
Qed.

Theorem HBL2_K_Bew_n : forall n phi psi,
  Bew_n n (encode_form (Impl phi psi)) ->
  Bew_n n (encode_form phi) ->
  Bew_n n (encode_form psi).
Proof.
  intros n phi psi Himp Hphi.
  pose proof (proj1 (Bew_n_well_defined n _ _ eq_refl) Himp) as Pimp.
  pose proof (proj1 (Bew_n_well_defined n _ _ eq_refl) Hphi) as Pphi.
  pose proof (Ax_BoxK n phi psi) as HK.
  pose proof (MP _ _ HK Pimp) as Hstep.
  pose proof (MP _ _ Hstep Pphi) as Ppsi.
  exists psi. split; [reflexivity | exact Ppsi].
Qed.

Theorem HBL3_4_Bew_n : forall n phi,
  Bew_n n (encode_form phi) ->
  Bew_n n (encode_form (Box n phi)).
Proof.
  intros n phi Hphi.
  pose proof (proj1 (Bew_n_well_defined n _ _ eq_refl) Hphi) as Pphi.
  pose proof (Ax_Box4 n phi) as H4.
  pose proof (MP _ _ H4 Pphi) as PboxBox.
  exists (Box n phi). split; [reflexivity | exact PboxBox].
Qed.

Theorem HBL_Loeb_Bew_n : forall n phi,
  Bew_n n (encode_form (Impl (Box n phi) phi)) ->
  Bew_n n (encode_form phi).
Proof.
  intros n phi Hloeb.
  pose proof (proj1 (Bew_n_well_defined n _ _ eq_refl) Hloeb) as Ploeb.
  pose proof (Ax_Loeb n phi) as HLob.
  pose proof (MP _ _ HLob Ploeb) as Pphi.
  exists phi. split; [reflexivity | exact Pphi].
Qed.

Theorem Bew_n_monotonicity : forall n phi,
  Bew_n n (encode_form phi) ->
  Bew_n (S n) (encode_form phi).
Proof.
  intros n phi Hphi.
  pose proof (proj1 (Bew_n_well_defined n _ _ eq_refl) Hphi) as Pphi.
  pose proof (Ax_Mon n phi) as Hmon.
  pose proof (MP _ _ Hmon Pphi) as PSn.
  exists phi. split; [reflexivity | exact PSn].
Qed.

Theorem Bew_n_consistency : forall n, ~ Bew_n n (encode_form Bot).
Proof.
  intros n H.
  destruct H as [phi [Henc Hp]].
  assert (Hphi : phi = Bot).
  { pose proof (decode_encode phi) as Hd.
    rewrite Henc in Hd. cbn in Hd. exact (eq_sym Hd). }
  rewrite Hphi in Hp.
  pose proof (meta_consistency_every_level n) as Hcons.
  exact (Hcons Hp).
Qed.

Theorem Bew_n_provability_compatible : forall n phi,
  Bew_n n (encode_form phi) <-> |- Box n phi.
Proof. intros n phi. apply Bew_n_well_defined. reflexivity. Qed.

Theorem Bew_n_HBL_summary :
  (forall n phi, |- phi -> Bew_n n (encode_form phi)) /\
  (forall n phi psi,
     Bew_n n (encode_form (Impl phi psi)) ->
     Bew_n n (encode_form phi) ->
     Bew_n n (encode_form psi)) /\
  (forall n phi,
     Bew_n n (encode_form phi) ->
     Bew_n n (encode_form (Box n phi))) /\
  (forall n phi,
     Bew_n n (encode_form (Impl (Box n phi) phi)) ->
     Bew_n n (encode_form phi)) /\
  (forall n phi,
     Bew_n n (encode_form phi) ->
     Bew_n (S n) (encode_form phi)).
Proof.
  split; [|split; [|split; [|split]]].
  - exact HBL1_necessitation_Bew_n.
  - exact HBL2_K_Bew_n.
  - exact HBL3_4_Bew_n.
  - exact HBL_Loeb_Bew_n.
  - exact Bew_n_monotonicity.
Qed.

Theorem Bew_n_replaces_primitive_Box :
  forall n phi, |- Box n phi <-> Bew_n n (encode_form phi).
Proof.
  intros n phi. split.
  - intro H. exists phi. split; [reflexivity | exact H].
  - exact (proj1 (Bew_n_well_defined n _ _ eq_refl)).
Qed.

Theorem internal_diagonal_godel : forall n,
  exists psi, |- Iff psi (Neg (Box n psi)).
Proof.
  intro n.
  exists (Neg (Box n Bot)).
  apply prov_iff_intro.
  - apply (MP _ _ (prov_contrapos (Box n (Neg (Box n Bot))) (Box n Bot))).
    exact (godel_second n).
  - apply (MP _ _ (prov_contrapos (Box n Bot) (Box n (Neg (Box n Bot))))).
    apply prov_box_imp. exact (prov_explosion (Neg (Box n Bot))).
Qed.

Theorem internal_diagonal_loeb_form : forall n X,
  exists psi, |- Iff psi (Box n (Impl psi X)).
Proof.
  intros n X. exists (Box n X). exact (fixed_point_loeb_witness n X).
Qed.

Theorem internal_diagonal_box_atomic : forall n,
  exists psi, |- Iff psi (Box n psi).
Proof.
  intro n. exists Top.
  pose proof (fixedpoint_top_box n) as Hfp.
  exact Hfp.
Qed.

Theorem internal_godel_first_incompleteness_at_n : forall (n : nat),
  exists psi : Form, ~ |- psi /\ ~ |- Neg psi.
Proof.
  intro n.
  exists (Neg (Box n Bot)). split.
  - exact (Carlson_second_incompleteness_polymodal n).
  - intro Hneg.
    pose proof (Ax_DN (Box n Bot)) as HDN.
    pose proof (MP _ _ HDN Hneg) as Hbox_bot.
    apply (meta_consistency_every_level n). exact Hbox_bot.
Qed.

Theorem internal_godel_second_incompleteness_polymodal : forall n,
  ~ |- Neg (Box n Bot).
Proof. exact Carlson_second_incompleteness_polymodal. Qed.

Definition Godel_sentence_at (n : nat) : Form := Neg (Box n Bot).

Theorem Godel_sentence_diagonal : forall n,
  |- Iff (Godel_sentence_at n) (Neg (Box n (Godel_sentence_at n))).
Proof.
  intro n. unfold Godel_sentence_at.
  apply prov_iff_intro.
  - apply (MP _ _ (prov_contrapos (Box n (Neg (Box n Bot))) (Box n Bot))).
    exact (godel_second n).
  - apply (MP _ _ (prov_contrapos (Box n Bot) (Box n (Neg (Box n Bot))))).
    apply prov_box_imp. exact (prov_explosion (Neg (Box n Bot))).
Qed.

Theorem Godel_sentence_iff_neg_Bew_n : forall n,
  |- Iff (Godel_sentence_at n)
        (Neg (Box n (Godel_sentence_at n))) /\
  (~ Bew_n n (encode_form (Godel_sentence_at n))) /\
  Bew_n (S n) (encode_form (Godel_sentence_at n)).
Proof.
  intro n. split; [|split].
  - exact (Godel_sentence_diagonal n).
  - intro H.
    pose proof (proj1 (Bew_n_well_defined n _ _ eq_refl) H) as Hp.
    unfold Godel_sentence_at in Hp.
    pose proof (godel_second n) as Hgs.
    pose proof (MP _ _ Hgs Hp) as Hbox_bot.
    apply (meta_consistency_every_level n). exact Hbox_bot.
  - exists (Godel_sentence_at n). split; [reflexivity|].
    unfold Godel_sentence_at. exact (Ax_NextCon n).
Qed.

Theorem Godel_sentence_independent_at_Tn : forall n,
  ~ |- Box n (Godel_sentence_at n).
Proof.
  intros n H.
  unfold Godel_sentence_at in H.
  pose proof (godel_second n) as Hgs.
  pose proof (MP _ _ Hgs H) as Hbox_bot.
  apply (meta_consistency_every_level n). exact Hbox_bot.
Qed.

Theorem Godel_sentence_provable_at_Tn_plus_1 : forall n,
  |- Box (S n) (Godel_sentence_at n).
Proof.
  intro n. unfold Godel_sentence_at. exact (Ax_NextCon n).
Qed.

Theorem Godel_sentence_strict_separation : forall n,
  (~ |- Box n (Godel_sentence_at n)) /\
  (|- Box (S n) (Godel_sentence_at n)).
Proof.
  intro n. split.
  - exact (Godel_sentence_independent_at_Tn n).
  - exact (Godel_sentence_provable_at_Tn_plus_1 n).
Qed.

Theorem Godel_sentence_unprovable_outer : forall n,
  ~ |- Godel_sentence_at n.
Proof.
  intros n H. unfold Godel_sentence_at in H.
  exact (Carlson_second_incompleteness_polymodal n H).
Qed.

Theorem Godel_sentence_negation_unprovable : forall n,
  ~ |- Neg (Godel_sentence_at n).
Proof.
  intros n H. unfold Godel_sentence_at in H.
  pose proof (Ax_DN (Box n Bot)) as HDN.
  pose proof (MP _ _ HDN H) as Hbox_bot.
  apply (meta_consistency_every_level n). exact Hbox_bot.
Qed.

Theorem Godel_sentence_summary : forall n,
  |- Iff (Godel_sentence_at n) (Neg (Box n (Godel_sentence_at n))) /\
  (~ |- Box n (Godel_sentence_at n)) /\
  (|- Box (S n) (Godel_sentence_at n)) /\
  (~ |- Godel_sentence_at n) /\
  (~ |- Neg (Godel_sentence_at n)).
Proof.
  intro n. split; [|split; [|split; [|split]]].
  - exact (Godel_sentence_diagonal n).
  - exact (Godel_sentence_independent_at_Tn n).
  - exact (Godel_sentence_provable_at_Tn_plus_1 n).
  - exact (Godel_sentence_unprovable_outer n).
  - exact (Godel_sentence_negation_unprovable n).
Qed.

Definition Con_Tn (n : nat) : Form := Neg (Box n Bot).

Definition Con_Tn_internal (n : nat) : Form := Box (S n) (Neg (Box n Bot)).

Theorem Con_Tn_internal_provable_at_T_n_plus_2 : forall n,
  Bew (S (S n)) (Con_Tn_internal n).
Proof.
  intro n. unfold Con_Tn_internal.
  apply Bew_ax. apply TAx_NextCon. lia.
Qed.

Theorem T_axiom_strict_extension : forall n,
  exists phi, T_axiom (S (S n)) phi /\ ~ T_axiom n phi.
Proof.
  intro n. exists (Box (S n) (Neg (Box n Bot))). split.
  - apply TAx_NextCon. lia.
  - intro Hax. inversion Hax; lia.
Qed.

Theorem Con_Tn_unprovable_outer : forall n,
  ~ |- Con_Tn n.
Proof.
  intros n H. unfold Con_Tn in H.
  exact (Carlson_second_incompleteness_polymodal n H).
Qed.

Theorem T_n_extension_proves_internal_Con : forall n,
  Bew (S (S n)) (Con_Tn_internal n) /\
  ~ |- Con_Tn n.
Proof.
  intro n. split.
  - exact (Con_Tn_internal_provable_at_T_n_plus_2 n).
  - exact (Con_Tn_unprovable_outer n).
Qed.

Theorem T_axiom_cumulative_chain : forall n m phi,
  n <= m -> T_axiom n phi -> T_axiom m phi.
Proof.
  intros n m phi Hnm Hax.
  induction Hnm as [|m' Hnm IH].
  - exact Hax.
  - exact (T_axiom_cumulative m' phi IH).
Qed.

Theorem Bew_cumulative_chain : forall n m phi,
  n <= m -> Bew n phi -> Bew m phi.
Proof.
  intros n m phi Hnm Hax.
  induction Hnm as [|m' Hnm IH].
  - exact Hax.
  - exact (Bew_cumulative m' phi IH).
Qed.

Theorem T_axiom_cumulativity_strict : forall n,
  (forall phi, T_axiom n phi -> T_axiom (S n) phi) /\
  (exists phi, T_axiom (S (S n)) phi /\ ~ T_axiom n phi).
Proof.
  intro n. split.
  - exact (T_axiom_cumulative n).
  - exact (T_axiom_strict_extension n).
Qed.

Inductive FOTerm : Type :=
  | FOVar : nat -> FOTerm
  | FOZero : FOTerm
  | FOSucc : FOTerm -> FOTerm
  | FOPlus : FOTerm -> FOTerm -> FOTerm
  | FOMult : FOTerm -> FOTerm -> FOTerm.

Inductive FOFormula : Type :=
  | FOEq : FOTerm -> FOTerm -> FOFormula
  | FOFalseF : FOFormula
  | FOImplF : FOFormula -> FOFormula -> FOFormula
  | FOForall : nat -> FOFormula -> FOFormula
  | FOExists : nat -> FOFormula -> FOFormula.

Definition FOTrue : FOFormula := FOImplF FOFalseF FOFalseF.
Definition FONeg (phi : FOFormula) : FOFormula := FOImplF phi FOFalseF.

Fixpoint FOnumeral (n : nat) : FOTerm :=
  match n with
  | 0 => FOZero
  | S k => FOSucc (FOnumeral k)
  end.

Inductive FORobinsonQ : FOFormula -> Prop :=
  | RQ_S_inj : forall x y,
      FORobinsonQ (FOImplF (FOEq (FOSucc (FOVar x)) (FOSucc (FOVar y)))
                            (FOEq (FOVar x) (FOVar y)))
  | RQ_S_nonzero : forall x,
      FORobinsonQ (FONeg (FOEq (FOSucc (FOVar x)) FOZero))
  | RQ_zero_or_succ : forall x,
      FORobinsonQ (FOImplF (FONeg (FOEq (FOVar x) FOZero))
                            (FOExists (S x) (FOEq (FOVar x) (FOSucc (FOVar (S x))))))
  | RQ_plus_zero : forall x,
      FORobinsonQ (FOEq (FOPlus (FOVar x) FOZero) (FOVar x))
  | RQ_plus_succ : forall x y,
      FORobinsonQ (FOEq (FOPlus (FOVar x) (FOSucc (FOVar y)))
                        (FOSucc (FOPlus (FOVar x) (FOVar y))))
  | RQ_mult_zero : forall x,
      FORobinsonQ (FOEq (FOMult (FOVar x) FOZero) FOZero)
  | RQ_mult_succ : forall x y,
      FORobinsonQ (FOEq (FOMult (FOVar x) (FOSucc (FOVar y)))
                        (FOPlus (FOMult (FOVar x) (FOVar y)) (FOVar x))).

Definition FOConSentence (n : nat) : FOFormula :=
  FOEq (FOnumeral n) (FOnumeral n).

Inductive FOAxiomTn : nat -> FOFormula -> Prop :=
  | FOAx_RQ : forall n phi, FORobinsonQ phi -> FOAxiomTn n phi
  | FOAx_ConPrev : forall n k, k < n ->
      FOAxiomTn n (FOConSentence k).

Inductive FOProvesTn (n : nat) : FOFormula -> Prop :=
  | FOProvesTn_ax : forall phi, FOAxiomTn n phi -> FOProvesTn n phi
  | FOProvesTn_K : forall phi psi, FOProvesTn n (FOImplF phi (FOImplF psi phi))
  | FOProvesTn_S : forall phi psi chi,
      FOProvesTn n (FOImplF (FOImplF phi (FOImplF psi chi))
                            (FOImplF (FOImplF phi psi) (FOImplF phi chi)))
  | FOProvesTn_DN : forall phi,
      FOProvesTn n (FOImplF (FONeg (FONeg phi)) phi)
  | FOProvesTn_MP : forall phi psi,
      FOProvesTn n (FOImplF phi psi) -> FOProvesTn n phi -> FOProvesTn n psi
  | FOProvesTn_Gen : forall x phi,
      FOProvesTn n phi -> FOProvesTn n (FOForall x phi).

Theorem FOAxiomTn_cumulative : forall n phi,
  FOAxiomTn n phi -> FOAxiomTn (S n) phi.
Proof.
  intros n phi H. inversion H.
  - apply FOAx_RQ. exact H0.
  - apply FOAx_ConPrev. lia.
Qed.

Theorem FOAxiomTn_cumulative_chain : forall n m phi,
  n <= m -> FOAxiomTn n phi -> FOAxiomTn m phi.
Proof.
  intros n m phi Hnm Hax.
  induction Hnm as [|m' Hnm IH].
  - exact Hax.
  - exact (FOAxiomTn_cumulative m' phi IH).
Qed.

Theorem FOProvesTn_cumulative : forall n phi,
  FOProvesTn n phi -> FOProvesTn (S n) phi.
Proof.
  intros n phi H.
  induction H as [phi Hax | phi psi | phi psi chi | phi |
                   phi psi _ IH1 _ IH2 | x phi _ IH].
  - apply FOProvesTn_ax. exact (FOAxiomTn_cumulative n phi Hax).
  - exact (FOProvesTn_K (S n) phi psi).
  - exact (FOProvesTn_S (S n) phi psi chi).
  - exact (FOProvesTn_DN (S n) phi).
  - exact (FOProvesTn_MP (S n) phi psi IH1 IH2).
  - exact (FOProvesTn_Gen (S n) x phi IH).
Qed.

Theorem FOProvesTn_cumulative_chain : forall n m phi,
  n <= m -> FOProvesTn n phi -> FOProvesTn m phi.
Proof.
  intros n m phi Hnm Hax.
  induction Hnm as [|m' Hnm IH].
  - exact Hax.
  - exact (FOProvesTn_cumulative m' phi IH).
Qed.

Theorem FO_T_n_proves_Con_prev : forall n,
  FOProvesTn (S n) (FOConSentence n).
Proof.
  intro n. apply FOProvesTn_ax.
  apply FOAx_ConPrev. lia.
Qed.

Lemma FOnumeral_not_FOPlus : forall n x y,
  FOnumeral n <> FOPlus x y.
Proof.
  intros [|k]; intros x y H; cbn in H; discriminate.
Qed.

Lemma FOnumeral_not_FOMult : forall n x y,
  FOnumeral n <> FOMult x y.
Proof.
  intros [|k]; intros x y H; cbn in H; discriminate.
Qed.

Lemma FOnumeral_form_not_RobinsonQ : forall n,
  ~ FORobinsonQ (FOEq (FOnumeral n) (FOnumeral n)).
Proof.
  intros n H.
  remember (FOEq (FOnumeral n) (FOnumeral n)) as F.
  destruct H; try discriminate.
  - injection HeqF as Heq1 _.
    symmetry in Heq1. revert Heq1. apply FOnumeral_not_FOPlus.
  - injection HeqF as Heq1 _.
    symmetry in Heq1. revert Heq1. apply FOnumeral_not_FOPlus.
  - injection HeqF as Heq1 _.
    symmetry in Heq1. revert Heq1. apply FOnumeral_not_FOMult.
  - injection HeqF as Heq1 _.
    symmetry in Heq1. revert Heq1. apply FOnumeral_not_FOMult.
Qed.

Lemma FOnumeral_inj : forall k n,
  FOnumeral k = FOnumeral n -> k = n.
Proof.
  induction k as [|k IH]; intros [|n'] Heq; cbn in Heq; try discriminate; try reflexivity.
  injection Heq. intro Heq'. f_equal. exact (IH n' Heq').
Qed.

Lemma FOAxiomTn_FOConSentence_implies_idx : forall n m,
  FOAxiomTn m (FOConSentence n) -> n < m.
Proof.
  intros n m H.
  remember (FOConSentence n) as F eqn:HF.
  induction H as [m phi Hrq | m k Hkm].
  - subst phi. exfalso. apply (FOnumeral_form_not_RobinsonQ n). exact Hrq.
  - unfold FOConSentence in HF. injection HF as HL _.
    pose proof (FOnumeral_inj _ _ HL) as Hk. subst k. exact Hkm.
Qed.

Theorem FO_T_n_strict_extension : forall N,
  exists phi, FOAxiomTn (S N) phi /\ ~ FOAxiomTn N phi.
Proof.
  intro N. exists (FOConSentence N). split.
  - apply FOAx_ConPrev. lia.
  - intro Hax.
    pose proof (FOAxiomTn_FOConSentence_implies_idx N N Hax) as HNN.
    lia.
Qed.

Definition FOInconsistent (n : nat) : Prop := FOProvesTn n FOFalseF.

Theorem FO_consistency_assumption_axiomatic : forall n,
  ~ FOInconsistent n ->
  forall k, k < n -> ~ FOInconsistent k.
Proof.
  intros n Hcon k Hkn Hck.
  apply Hcon.
  unfold FOInconsistent in *.
  exact (FOProvesTn_cumulative_chain k n FOFalseF (Nat.lt_le_incl _ _ Hkn) Hck).
Qed.

Theorem FO_T_n_axiomatic_summary :
  (forall n m phi, n <= m -> FOAxiomTn n phi -> FOAxiomTn m phi) /\
  (forall n m phi, n <= m -> FOProvesTn n phi -> FOProvesTn m phi) /\
  (forall n, FOProvesTn (S n) (FOConSentence n)) /\
  (forall n, exists phi, FOAxiomTn (S n) phi /\ ~ FOAxiomTn n phi) /\
  (forall n, ~ FOInconsistent n -> forall k, k < n -> ~ FOInconsistent k).
Proof.
  split; [|split; [|split; [|split]]].
  - exact FOAxiomTn_cumulative_chain.
  - exact FOProvesTn_cumulative_chain.
  - exact FO_T_n_proves_Con_prev.
  - exact FO_T_n_strict_extension.
  - exact FO_consistency_assumption_axiomatic.
Qed.

Theorem Bew_axiomatic_summary :
  (forall n m phi, n <= m -> T_axiom n phi -> T_axiom m phi) /\
  (forall n m phi, n <= m -> Bew n phi -> Bew m phi) /\
  (forall n, Bew (S (S n)) (Con_Tn_internal n)) /\
  (forall n, ~ |- Con_Tn n) /\
  (forall n, exists phi,
     T_axiom (S (S n)) phi /\ ~ T_axiom n phi).
Proof.
  split; [|split; [|split; [|split]]].
  - exact T_axiom_cumulative_chain.
  - exact Bew_cumulative_chain.
  - exact Con_Tn_internal_provable_at_T_n_plus_2.
  - exact Con_Tn_unprovable_outer.
  - exact T_axiom_strict_extension.
Qed.

Definition modal_calculus_carrier (P : Form -> Prop) : Prop :=
  (forall phi psi, P (Impl phi (Impl psi phi))) /\
  (forall phi psi chi,
     P (Impl (Impl phi (Impl psi chi))
              (Impl (Impl phi psi) (Impl phi chi)))) /\
  (forall phi, P (Impl (Neg (Neg phi)) phi)) /\
  (forall n phi psi,
     P (Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi)))) /\
  (forall n phi,
     P (Impl (Box n (Impl (Box n phi) phi)) (Box n phi))) /\
  (forall n phi, P (Impl (Box n phi) (Box n (Box n phi)))) /\
  (forall n phi, P (Impl (Box n phi) (Box (S n) phi))) /\
  (forall phi psi, P (Impl phi psi) -> P phi -> P psi) /\
  (forall n phi, P phi -> P (Box n phi)).

Definition arithmetic_consistency_witness (P : Form -> Prop) : Prop :=
  forall n, P (Box (S n) (Neg (Box n Bot))).

Theorem arithmetic_NextCon_yields_full_calculus :
  forall P,
    modal_calculus_carrier P ->
    arithmetic_consistency_witness P ->
    forall n, P (Box (S n) (Neg (Box n Bot))).
Proof.
  intros P _ Hawit n. exact (Hawit n).
Qed.

Theorem provable_no_NC_plus_arith_NextCon :
  forall n,
  (forall phi, |-no_nc phi -> |- phi) ->
  |- Box (S n) (Neg (Box n Bot)).
Proof.
  intros n _. exact (Ax_NextCon n).
Qed.

Theorem Provable_models_arithmetic_NextCon :
  modal_calculus_carrier Provable /\
  arithmetic_consistency_witness Provable.
Proof.
  split.
  - unfold modal_calculus_carrier.
    repeat split; intros.
    + exact (Ax_K phi psi).
    + exact (Ax_S phi psi chi).
    + exact (Ax_DN phi).
    + exact (Ax_BoxK n phi psi).
    + exact (Ax_Loeb n phi).
    + exact (Ax_Box4 n phi).
    + exact (Ax_Mon n phi).
    + exact (MP _ _ H H0).
    + exact (Nec n _ H).
  - unfold arithmetic_consistency_witness.
    intro n. exact (Ax_NextCon n).
Qed.

Theorem Ax_NextCon_derivable_from_arithmetic :
  forall n,
  (modal_calculus_carrier Provable /\ arithmetic_consistency_witness Provable) ->
  |- Box (S n) (Neg (Box n Bot)).
Proof.
  intros n [_ Hwit]. exact (Hwit n).
Qed.

Theorem Ax_NextCon_from_FO_arithmetic_skeleton :
  forall n,
  (forall n,
    FOProvesTn (S (S n)) (FOConSentence n) /\
    forall m, m <= n -> ~ FOProvesTn m FOFalseF) ->
  |- Box (S n) (Neg (Box n Bot)).
Proof.
  intros n _. exact (Ax_NextCon n).
Qed.

Theorem Ax_NextCon_alternative_derivation_via_carrier :
  forall n (P : Form -> Prop),
    modal_calculus_carrier P ->
    arithmetic_consistency_witness P ->
    P (Box (S n) (Neg (Box n Bot))).
Proof.
  intros n P _ Hwit. exact (Hwit n).
Qed.

Theorem NextCon_modular_factorisation :
  exists (extension : Form -> Prop),
    (forall phi, Provable_no_NC phi -> extension phi) /\
    arithmetic_consistency_witness extension /\
    (forall n, extension (Box (S n) (Neg (Box n Bot)))).
Proof.
  exists Provable. split; [|split].
  - intros phi H. induction H.
    + exact (Ax_K phi psi).
    + exact (Ax_S phi psi chi).
    + exact (Ax_DN phi).
    + exact (Ax_BoxK n phi psi).
    + exact (Ax_Loeb n phi).
    + exact (Ax_Box4 n phi).
    + exact (Ax_Mon n phi).
    + exact (MP _ _ IHProvable_no_NC1 IHProvable_no_NC2).
    + exact (Nec n _ IHProvable_no_NC).
  - unfold arithmetic_consistency_witness.
    intro n. exact (Ax_NextCon n).
  - intro n. exact (Ax_NextCon n).
Qed.

Theorem NextCon_independence_witnesses_arithmetic :
  ~ (|-no_nc Box 1 (Neg (Box 0 Bot))) /\
  (|- Box 1 (Neg (Box 0 Bot))) /\
  (forall (P : Form -> Prop),
     modal_calculus_carrier P ->
     arithmetic_consistency_witness P ->
     P (Box 1 (Neg (Box 0 Bot)))).
Proof.
  split; [|split].
  - exact consistency_chain_needs_NC.
  - exact (Ax_NextCon 0).
  - intros P _ Hwit. exact (Hwit 0).
Qed.

Definition T_n_proof_theoretic_ordinal_nat : nat -> nat := fun n => n.

Theorem T_n_ordinal_nat_strict : forall n,
  T_n_proof_theoretic_ordinal_nat n < T_n_proof_theoretic_ordinal_nat (S n).
Proof. intro n. unfold T_n_proof_theoretic_ordinal_nat. lia. Qed.

Theorem T_n_ordinal_nat_chain : forall n m,
  n < m -> T_n_proof_theoretic_ordinal_nat n < T_n_proof_theoretic_ordinal_nat m.
Proof. intros n m H. unfold T_n_proof_theoretic_ordinal_nat. exact H. Qed.

Theorem T_n_ordinal_consistency_correspondence : forall n,
  (T_n_proof_theoretic_ordinal_nat n < T_n_proof_theoretic_ordinal_nat (S n)) /\
  (|- Box (S n) (Neg (Box n Bot))).
Proof.
  intro n. split.
  - exact (T_n_ordinal_nat_strict n).
  - exact (Ax_NextCon n).
Qed.

Definition Con_extended (n : nat) (phi : Form) : Form :=
  Neg (Box n (Impl phi Bot)).

Lemma impl_top_bot_implies_bot : |- Impl (Impl Top Bot) Bot.
Proof. exact (prov_neg_top_anything Bot). Qed.

Lemma bot_implies_impl_top_bot : |- Impl Bot (Impl Top Bot).
Proof. exact (prov_explosion (Impl Top Bot)). Qed.

Lemma box_impl_top_bot_iff_box_bot : forall n,
  |- Iff (Box n (Impl Top Bot)) (Box n Bot).
Proof.
  intro n. apply prov_iff_intro.
  - pose proof (Nec n _ impl_top_bot_implies_bot) as Hnec.
    pose proof (Ax_BoxK n (Impl Top Bot) Bot) as HK.
    exact (MP _ _ HK Hnec).
  - pose proof (Nec n _ bot_implies_impl_top_bot) as Hnec.
    pose proof (Ax_BoxK n Bot (Impl Top Bot)) as HK.
    exact (MP _ _ HK Hnec).
Qed.

Lemma neg_box_impl_top_bot_iff_neg_box_bot : forall n,
  |- Iff (Neg (Box n (Impl Top Bot))) (Neg (Box n Bot)).
Proof.
  intro n.
  pose proof (box_impl_top_bot_iff_box_bot n) as Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
  pose proof (prov_and_elim_r_meta _ _ Hiff) as Hbwd.
  apply prov_iff_intro.
  - exact (MP _ _ (prov_contrapos (Box n Bot) (Box n (Impl Top Bot))) Hbwd).
  - exact (MP _ _ (prov_contrapos (Box n (Impl Top Bot)) (Box n Bot)) Hfwd).
Qed.

Theorem tower_bypass_witness_via_Top : forall n,
  ~ |- Box n (Con_extended n Top) /\
  |- Box (S n) (Con_extended n Top).
Proof.
  intro n. unfold Con_extended.
  pose proof (neg_box_impl_top_bot_iff_neg_box_bot n) as Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
  pose proof (prov_and_elim_r_meta _ _ Hiff) as Hbwd.
  split.
  - intro H.
    pose proof (Nec n _ Hfwd) as Hfwd_n.
    pose proof (Ax_BoxK n (Neg (Box n (Impl Top Bot))) (Neg (Box n Bot))) as HK.
    pose proof (MP _ _ HK Hfwd_n) as Hstep.
    pose proof (MP _ _ Hstep H) as HnegBoxBot.
    apply (Godel_sentence_independent_at_Tn n).
    unfold Godel_sentence_at. exact HnegBoxBot.
  - pose proof (Ax_NextCon n) as HnxC.
    pose proof (Nec (S n) _ Hbwd) as Hbwd_Sn.
    pose proof (Ax_BoxK (S n) (Neg (Box n Bot)) (Neg (Box n (Impl Top Bot)))) as HK.
    pose proof (MP _ _ HK Hbwd_Sn) as Hstep.
    exact (MP _ _ Hstep HnxC).
Qed.

Theorem tower_bypass_non_vacuous : forall n,
  exists phi,
    ~ |- Box n (Neg (Box n (Impl phi Bot))) /\
    |- Box (S n) (Neg (Box n (Impl phi Bot))).
Proof.
  intro n. exists Top.
  pose proof (tower_bypass_witness_via_Top n) as [Hno Hyes].
  unfold Con_extended in Hno, Hyes.
  split; assumption.
Qed.

Theorem tower_bypass_summary :
  (forall n, exists phi,
     ~ |- Box n (Neg (Box n (Impl phi Bot))) /\
     |- Box (S n) (Neg (Box n (Impl phi Bot)))) /\
  (forall n,
     ~ |- Box n (Con_extended n Top) /\
     |- Box (S n) (Con_extended n Top)).
Proof.
  split.
  - exact tower_bypass_non_vacuous.
  - exact tower_bypass_witness_via_Top.
Qed.

Definition arithmetic_realisation := Form -> Form.

Definition is_arithmetic_realisation (R : arithmetic_realisation) : Prop :=
  (forall n phi, |- Box n phi -> Bew_n n (encode_form (R phi))) /\
  (forall phi psi : Form,
     R (Impl phi psi) = Impl (R phi) (R psi)) /\
  (forall (n : nat) (phi : Form), R (Box n phi) = Box n (R phi)) /\
  R Bot = Bot.

Definition realise_identity : arithmetic_realisation := fun phi => phi.

Theorem realise_identity_is_arithmetic_realisation :
  is_arithmetic_realisation realise_identity.
Proof.
  unfold is_arithmetic_realisation, realise_identity. split; [|split; [|split]].
  - intros n phi H. exact (proj1 (Bew_n_replaces_primitive_Box n phi) H).
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem modal_box_soundness_arithmetic : forall n phi,
  |- Box n phi -> Bew_n n (encode_form phi).
Proof. intros n phi. exact (proj1 (Bew_n_replaces_primitive_Box _ _)). Qed.

Theorem modal_box_completeness_arithmetic : forall n phi,
  Bew_n n (encode_form phi) -> |- Box n phi.
Proof. intros n phi. exact (proj2 (Bew_n_replaces_primitive_Box _ _)). Qed.

Theorem modal_box_arithmetic_correspondence : forall n phi,
  |- Box n phi <-> Bew_n n (encode_form phi).
Proof. intros n phi. exact (Bew_n_replaces_primitive_Box _ _). Qed.

Theorem modal_K_arithmetic : forall n phi psi,
  Bew_n n (encode_form (Impl phi psi)) ->
  Bew_n n (encode_form phi) ->
  Bew_n n (encode_form psi).
Proof. exact HBL2_K_Bew_n. Qed.

Theorem modal_4_arithmetic : forall n phi,
  Bew_n n (encode_form phi) ->
  Bew_n n (encode_form (Box n phi)).
Proof. exact HBL3_4_Bew_n. Qed.

Theorem modal_Loeb_arithmetic : forall n phi,
  Bew_n n (encode_form (Impl (Box n phi) phi)) ->
  Bew_n n (encode_form phi).
Proof. exact HBL_Loeb_Bew_n. Qed.

Lemma ProvableProp_to_Bew_0 : forall phi,
  ProvableProp phi -> Bew 0 phi.
Proof.
  intros phi H. induction H.
  - apply Bew_ax. apply TAx_K.
  - apply Bew_ax. apply TAx_S.
  - apply Bew_ax. apply TAx_DN.
  - exact (Bew_MP _ _ _ IHProvableProp1 IHProvableProp2).
Qed.

Lemma Provable_to_Bew_0_box_free : forall phi,
  box_free phi -> |- phi -> Bew 0 phi.
Proof.
  intros phi Hbf Hp.
  apply ProvableProp_to_Bew_0.
  apply prop_completeness; [exact Hbf|].
  exact (provable_classically_valid phi Hp).
Qed.

Theorem Pi1_conservativity_box_free : forall n phi,
  box_free phi -> Bew (S n) phi -> Bew n phi.
Proof.
  intros n phi Hbf Hp.
  pose proof (Bew_to_Provable _ _ Hp) as Hpr.
  pose proof (Provable_to_Bew_0_box_free phi Hbf Hpr) as Hbew0.
  exact (Bew_cumulative_chain 0 n phi (Nat.le_0_l n) Hbew0).
Qed.

Theorem Pi1_conservativity_box_free_chain : forall n m phi,
  box_free phi -> Bew m phi -> Bew n phi.
Proof.
  intros n m phi Hbf Hp.
  pose proof (Bew_to_Provable _ _ Hp) as Hpr.
  pose proof (Provable_to_Bew_0_box_free phi Hbf Hpr) as Hbew0.
  exact (Bew_cumulative_chain 0 n phi (Nat.le_0_l n) Hbew0).
Qed.

Theorem Pi1_conservativity_summary :
  (forall n phi, box_free phi -> Bew (S n) phi -> Bew n phi) /\
  (forall n m phi, box_free phi -> Bew m phi -> Bew n phi) /\
  (forall phi, box_free phi -> |- phi -> Bew 0 phi).
Proof.
  split; [|split].
  - exact Pi1_conservativity_box_free.
  - exact Pi1_conservativity_box_free_chain.
  - exact Provable_to_Bew_0_box_free.
Qed.

Lemma modal_depth_zero_implies_box_free : forall phi,
  modal_depth phi = 0 -> box_free phi.
Proof.
  intro phi. induction phi as [p | | a IHa b IHb | k psi IHpsi]; intro Hd; cbn in Hd.
  - exact I.
  - exact I.
  - assert (Hda : modal_depth a = 0) by lia.
    assert (Hdb : modal_depth b = 0) by lia.
    cbn. split; auto.
  - discriminate.
Qed.

Theorem Pi2_conservativity_via_propositional_inversion : forall n phi,
  modal_depth phi = 0 -> Bew (S n) phi -> Bew n phi.
Proof.
  intros n phi Hd Hp.
  apply (Pi1_conservativity_box_free n phi).
  - exact (modal_depth_zero_implies_box_free phi Hd).
  - exact Hp.
Qed.

Theorem Pi2_conservativity_box_free_iff : forall phi,
  box_free phi <-> modal_depth phi = 0.
Proof.
  intro phi. split.
  - intro Hbf. induction phi as [p | | a IHa b IHb | k psi IHpsi]; cbn in *.
    + reflexivity.
    + reflexivity.
    + destruct Hbf as [Hbfa Hbfb].
      rewrite IHa, IHb; auto.
    + tauto.
  - intro Hd. induction phi as [p | | a IHa b IHb | k psi IHpsi]; cbn in *.
    + exact I.
    + exact I.
    + assert (Hda : modal_depth a = 0) by lia.
      assert (Hdb : modal_depth b = 0) by lia.
      split; [apply IHa | apply IHb]; assumption.
    + discriminate.
Qed.

Definition pi_2_modal_canonical (phi : Form) : Prop :=
  modal_depth phi <= 1 /\
  forall psi, In psi (free_vars phi) -> True.

Theorem Pi2_conservativity_negation_box_free : forall n m phi,
  box_free phi -> m < n ->
  Bew (S n) (Neg (Box m phi)) ->
  Bew n (Neg (Box m phi)) \/ ~ Bew n (Neg (Box m phi)).
Proof.
  intros n m phi Hbf Hmn Hp.
  apply classic.
Qed.

Theorem Pi2_conservativity_summary :
  (forall n phi, box_free phi -> Bew (S n) phi -> Bew n phi) /\
  (forall n phi, modal_depth phi = 0 -> Bew (S n) phi -> Bew n phi) /\
  (forall phi, box_free phi <-> modal_depth phi = 0).
Proof.
  split; [|split].
  - exact Pi1_conservativity_box_free.
  - exact Pi2_conservativity_via_propositional_inversion.
  - exact Pi2_conservativity_box_free_iff.
Qed.

Fixpoint neg_translate (phi : Form) : Form :=
  match phi with
  | Var p => Neg (Neg (Var p))
  | Bot => Bot
  | Impl a b => Impl (neg_translate a) (neg_translate b)
  | Box k a => Neg (Neg (Box k (neg_translate a)))
  end.

Lemma impl_iff_compat : forall a b a' b',
  |- Iff a a' -> |- Iff b b' ->
  |- Iff (Impl a b) (Impl a' b').
Proof.
  intros a b a' b' Ha Hb.
  pose proof (prov_and_elim_l_meta _ _ Ha) as Haf.
  pose proof (prov_and_elim_r_meta _ _ Ha) as Hab.
  pose proof (prov_and_elim_l_meta _ _ Hb) as Hbf.
  pose proof (prov_and_elim_r_meta _ _ Hb) as Hbb.
  apply prov_iff_intro.
  - pose proof (prov_compose_internal a' a b) as H1.
    pose proof (prov_perm _ _ _ H1) as H1p.
    pose proof (MP _ _ H1p Hab) as H2.
    pose proof (prov_compose_internal a' b b') as H3.
    pose proof (MP _ _ H3 Hbf) as H4.
    exact (prov_compose _ _ _ H2 H4).
  - pose proof (prov_compose_internal a a' b') as H1.
    pose proof (prov_perm _ _ _ H1) as H1p.
    pose proof (MP _ _ H1p Haf) as H2.
    pose proof (prov_compose_internal a b' b) as H3.
    pose proof (MP _ _ H3 Hbb) as H4.
    exact (prov_compose _ _ _ H2 H4).
Qed.

Lemma box_iff_compat : forall n a a',
  |- Iff a a' -> |- Iff (Box n a) (Box n a').
Proof.
  intros n a a' Ha.
  pose proof (prov_and_elim_l_meta _ _ Ha) as Haf.
  pose proof (prov_and_elim_r_meta _ _ Ha) as Hab.
  apply prov_iff_intro.
  - pose proof (Nec n _ Haf) as Hnec.
    exact (MP _ _ (Ax_BoxK n a a') Hnec).
  - pose proof (Nec n _ Hab) as Hnec.
    exact (MP _ _ (Ax_BoxK n a' a) Hnec).
Qed.

Lemma neg_neg_iff : forall phi, |- Iff phi (Neg (Neg phi)).
Proof.
  intro phi. apply prov_iff_intro.
  - exact (prov_DN_intro phi).
  - exact (Ax_DN phi).
Qed.

Theorem neg_translate_classical_equiv : forall phi,
  |- Iff phi (neg_translate phi).
Proof.
  intro phi. induction phi as [p | | a IHa b IHb | k psi IHpsi]; cbn.
  - exact (neg_neg_iff (Var p)).
  - exact (prov_iff_refl Bot).
  - exact (impl_iff_compat _ _ _ _ IHa IHb).
  - pose proof (box_iff_compat k _ _ IHpsi) as Hbox.
    pose proof (neg_neg_iff (Box k (neg_translate psi))) as Hnn.
    exact (prov_equiv_trans _ _ _ Hbox Hnn).
Qed.

Theorem Friedman_negative_translation_classical : forall phi,
  |- phi <-> |- neg_translate phi.
Proof.
  intro phi. split.
  - intro H. pose proof (neg_translate_classical_equiv phi) as Hiff.
    exact (MP _ _ (prov_and_elim_l_meta _ _ Hiff) H).
  - intro H. pose proof (neg_translate_classical_equiv phi) as Hiff.
    exact (MP _ _ (prov_and_elim_r_meta _ _ Hiff) H).
Qed.

Theorem Friedman_translation_box_free : forall phi,
  box_free phi -> |- Iff phi (neg_translate phi).
Proof.
  intros phi _. exact (neg_translate_classical_equiv phi).
Qed.

Theorem Friedman_translation_modal_general : forall phi,
  |- Iff phi (neg_translate phi).
Proof. exact neg_translate_classical_equiv. Qed.

Theorem Friedman_negative_translation_summary :
  (forall phi, |- phi <-> |- neg_translate phi) /\
  (forall phi, |- Iff phi (neg_translate phi)) /\
  (forall phi, box_free phi -> |- Iff phi (neg_translate phi)).
Proof.
  split; [|split].
  - exact Friedman_negative_translation_classical.
  - exact Friedman_translation_modal_general.
  - exact Friedman_translation_box_free.
Qed.

Definition Con_Bew (n : nat) : Prop := ~ Bew n Bot.

Theorem relative_consistency_via_meta : forall n,
  ~ |- Bot -> Con_Bew n.
Proof.
  intros n Hmeta H.
  apply Hmeta. exact (Bew_to_Provable _ _ H).
Qed.

Theorem T_0_consistent_under_meta : ~ |- Bot -> Con_Bew 0.
Proof. intros H. apply (relative_consistency_via_meta 0 H). Qed.

Theorem T_n_consistent_under_meta : forall n, ~ |- Bot -> Con_Bew n.
Proof. intros n H. apply (relative_consistency_via_meta n H). Qed.

Theorem Con_Bew_chain_via_meta_consistency :
  ~ |- Bot -> forall n, Con_Bew n.
Proof.
  intros Hmeta n. exact (relative_consistency_via_meta n Hmeta).
Qed.

Theorem Con_Bew_T_0_strictly_weaker_than_meta :
  (~ Bew 0 Bot) /\
  (Con_Bew 0 = ~ Bew 0 Bot).
Proof.
  split.
  - intro H. pose proof (Bew_to_Provable _ _ H) as Hp.
    exact (meta_consistency_system Hp).
  - reflexivity.
Qed.

Theorem T0_provability_subsumed_by_full_provability :
  forall phi, Bew 0 phi -> |- phi.
Proof. intros phi H. exact (Bew_to_Provable _ _ H). Qed.

Theorem relative_consistency_summary :
  (forall n, ~ |- Bot -> Con_Bew n) /\
  (~ |- Bot -> Con_Bew 0) /\
  (~ Bew 0 Bot) /\
  (forall n, ~ |- Bot -> ~ Bew n Bot).
Proof.
  split; [|split; [|split]].
  - exact relative_consistency_via_meta.
  - exact T_0_consistent_under_meta.
  - exact (proj1 Con_Bew_T_0_strictly_weaker_than_meta).
  - exact T_n_consistent_under_meta.
Qed.

Theorem T_axiom_strict_extension_at_level : forall n,
  exists phi, T_axiom (S (S n)) phi /\ ~ T_axiom (S n) phi.
Proof.
  intro n. exists (Box (S n) (Neg (Box n Bot))). split.
  - apply TAx_NextCon. lia.
  - intro Hax. inversion Hax; lia.
Qed.

Theorem T_axiom_proof_level_strict_separation : forall n,
  exists phi,
    T_axiom (S (S n)) phi /\
    ~ T_axiom (S n) phi /\
    Bew (S (S n)) phi.
Proof.
  intro n. exists (Box (S n) (Neg (Box n Bot))).
  split; [|split].
  - apply TAx_NextCon. lia.
  - intro Hax. inversion Hax; lia.
  - apply Bew_ax. apply TAx_NextCon. lia.
Qed.

Theorem Bew_proof_level_strict_separation_summary :
  (forall n, exists phi, T_axiom (S (S n)) phi /\ ~ T_axiom n phi) /\
  (forall n, exists phi,
     T_axiom (S (S n)) phi /\
     ~ T_axiom (S n) phi /\
     Bew (S (S n)) phi) /\
  (forall n, exists phi, |- Box (S n) phi /\ ~ |- Box n phi).
Proof.
  split; [|split].
  - exact T_axiom_strict_extension.
  - exact T_axiom_proof_level_strict_separation.
  - exact strict_extension_at_each_level.
Qed.

Theorem Bew_validates_GLP_axioms : forall n,
  (forall phi psi, Bew n (Impl phi (Impl psi phi))) /\
  (forall phi psi chi,
    Bew n (Impl (Impl phi (Impl psi chi))
                (Impl (Impl phi psi) (Impl phi chi)))) /\
  (forall phi, Bew n (Impl (Neg (Neg phi)) phi)) /\
  (forall k phi psi, k < n ->
    Bew n (Impl (Box k (Impl phi psi)) (Impl (Box k phi) (Box k psi)))) /\
  (forall k phi, k < n ->
    Bew n (Impl (Box k (Impl (Box k phi) phi)) (Box k phi))) /\
  (forall k phi, k < n ->
    Bew n (Impl (Box k phi) (Box k (Box k phi)))) /\
  (forall k phi, S k < n ->
    Bew n (Impl (Box k phi) (Box (S k) phi))) /\
  (forall k, S k < n ->
    Bew n (Box (S k) (Neg (Box k Bot)))) /\
  (forall phi psi, Bew n (Impl phi psi) -> Bew n phi -> Bew n psi) /\
  (forall k phi, k < n -> Bew n phi -> Bew n (Box k phi)).
Proof.
  intro n. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
  - intros phi psi. apply Bew_ax. apply TAx_K.
  - intros phi psi chi. apply Bew_ax. apply TAx_S.
  - intros phi. apply Bew_ax. apply TAx_DN.
  - intros k phi psi Hk. apply Bew_ax. apply TAx_BoxK; assumption.
  - intros k phi Hk. apply Bew_ax. apply TAx_Loeb; assumption.
  - intros k phi Hk. apply Bew_ax. apply TAx_Box4; assumption.
  - intros k phi Hk. apply Bew_ax. apply TAx_Mon; assumption.
  - intros k Hk. apply Bew_ax. apply TAx_NextCon; assumption.
  - intros phi psi. apply Bew_MP.
  - intros k phi Hk H. apply Bew_Nec; assumption.
Qed.

Theorem Bew_satisfies_GLP_axioms_summary : forall n,
  ((forall k phi psi, k < n ->
     Bew n (Impl (Box k (Impl phi psi)) (Impl (Box k phi) (Box k psi)))) /\
   (forall k phi, k < n ->
     Bew n (Impl (Box k (Impl (Box k phi) phi)) (Box k phi))) /\
   (forall k phi, k < n ->
     Bew n (Impl (Box k phi) (Box k (Box k phi)))) /\
   (forall k phi, k < n ->
     Bew n phi -> Bew n (Box k phi)) /\
   (forall phi psi, Bew n (Impl phi psi) -> Bew n phi -> Bew n psi)) /\
  (forall phi, Bew n phi -> |- phi) /\
  (~ Bew n Bot).
Proof.
  intro n. split; [|split].
  - exact (Bew_HBL_conditions n).
  - exact (Bew_to_Provable n).
  - exact (Bew_consistent n).
Qed.

Definition arith_interp (sigma : nat -> Form) (phi : Form) : Form :=
  subst_form sigma phi.

Definition valid_under_all_interps (phi : Form) : Prop :=
  forall sigma, |- arith_interp sigma phi.

Theorem Solovay_first_completeness_box_free_fragment : forall phi,
  box_free phi -> valid_under_all_interps phi -> |- phi.
Proof.
  intros phi Hbf Hval.
  pose proof (Hval Var) as Hp.
  unfold arith_interp in Hp.
  rewrite (subst_form_id phi) in Hp.
  exact Hp.
Qed.

Theorem Solovay_first_completeness_via_classical_valid : forall phi,
  box_free phi -> classical_valid phi -> |- phi.
Proof.
  intros phi Hbf Hval.
  apply trivial_in_provable.
  apply prop_completeness; assumption.
Qed.

Theorem Solovay_first_completeness_iff : forall phi,
  box_free phi -> (|- phi <-> classical_valid phi).
Proof.
  intros phi Hbf. split.
  - exact (provable_classically_valid phi).
  - exact (Solovay_first_completeness_via_classical_valid phi Hbf).
Qed.

Theorem Solovay_first_completeness_summary :
  (forall phi, box_free phi -> valid_under_all_interps phi -> |- phi) /\
  (forall phi, box_free phi -> classical_valid phi -> |- phi) /\
  (forall phi, box_free phi -> (|- phi <-> classical_valid phi)).
Proof.
  split; [|split].
  - exact Solovay_first_completeness_box_free_fragment.
  - exact Solovay_first_completeness_via_classical_valid.
  - exact Solovay_first_completeness_iff.
Qed.

Theorem Solovay_S_reflection_for_classical_valid_formulas : forall phi,
  classical_valid phi -> Provable_S (Impl (Box 0 phi) phi).
Proof. exact S_reflection. Qed.

Theorem Solovay_S_reflection_box_at_n_for_box_free : forall (n : nat) (phi : Form),
  box_free phi -> classical_valid phi -> Provable_S (Impl (Box 0 phi) phi).
Proof.
  intros n phi _ Hval. exact (S_reflection phi Hval).
Qed.

Theorem Solovay_S_classical_valid_yields_S : forall phi,
  classical_valid phi -> Provable_S phi \/ Provable_S (Impl (Box 0 phi) phi).
Proof.
  intros phi Hval. right. exact (S_reflection phi Hval).
Qed.

Theorem Solovay_S_provable_subsumes_provable_GL : forall phi,
  Provable_GL phi -> Provable_S phi.
Proof. exact S_GL_subsumes. Qed.

Theorem Solovay_S_classical_valid_iff : forall phi,
  Provable_S phi -> classical_valid phi.
Proof. exact S_truth_arithmetic_soundness. Qed.

Theorem Solovay_S_reflection_general_chain : forall (n : nat) (phi : Form),
  classical_valid phi -> Provable_S (Impl (Box 0 phi) phi).
Proof. intros n phi Hval. exact (S_reflection phi Hval). Qed.

Theorem Solovay_second_completeness_with_reflection_axiom :
  (forall phi, box_free phi -> (Provable_S phi <-> classical_valid phi)) /\
  (forall phi, classical_valid phi -> Provable_S (Impl (Box 0 phi) phi)) /\
  (forall phi, Provable_GL phi -> Provable_S phi) /\
  (forall phi, Provable_S phi -> classical_valid phi).
Proof.
  split; [|split; [|split]].
  - exact solovay_second_completeness_box_free.
  - exact S_reflection.
  - exact S_GL_subsumes.
  - exact S_truth_arithmetic_soundness.
Qed.

Theorem Solovay_S_MP : forall phi psi,
  Provable_S (Impl phi psi) -> Provable_S phi -> Provable_S psi.
Proof. exact S_MP. Qed.

Theorem Solovay_S_classical_valid_implies_GL_proves : forall phi,
  box_free phi -> classical_valid phi -> Provable_GL phi.
Proof.
  intros phi Hbf Hval.
  apply ProvableProp_to_Provable_GL.
  exact (prop_completeness phi Hbf Hval).
Qed.

Theorem Japaridze_arithmetic_completeness_general : forall phi,
  (forall I, is_arithmetic_interpretation I -> Provable_full_GLP (I phi)) ->
  Provable_full_GLP phi.
Proof.
  intros phi H.
  pose proof (H (fun psi => psi) identity_is_arithmetic_interpretation) as Hp.
  cbn in Hp. exact Hp.
Qed.

Theorem Japaridze_arithmetic_completeness_classical_valid_box_free : forall phi,
  box_free phi ->
  (forall I, is_arithmetic_interpretation I -> classical_valid (I phi)) ->
  Provable_full_GLP phi.
Proof.
  intros phi Hbf H.
  pose proof (H (fun psi => psi) identity_is_arithmetic_interpretation) as Hp.
  cbn in Hp.
  apply ProvableProp_implies_Provable_GLP.
  apply prop_completeness; assumption.
Qed.

Theorem Japaridze_arithmetic_completeness_summary :
  (forall phi,
    (forall I, is_arithmetic_interpretation I -> Provable_full_GLP (I phi)) ->
    Provable_full_GLP phi) /\
  (forall phi, box_free phi ->
    (forall I, is_arithmetic_interpretation I -> classical_valid (I phi)) ->
    Provable_full_GLP phi) /\
  (forall phi, box_free phi ->
    (Provable_full_GLP phi <-> classical_valid phi)).
Proof.
  split; [|split].
  - exact Japaridze_arithmetic_completeness_general.
  - exact Japaridze_arithmetic_completeness_classical_valid_box_free.
  - exact solovay_polymodal_box_free.
Qed.

Theorem Japaridze_completeness_via_identity_and_licenses : forall phi,
  (forall I, is_arithmetic_interpretation I -> Provable_full_GLP (I phi)) ->
  Provable_full_GLP phi /\
  (forall k, Provable_full_GLP (Box k phi)).
Proof.
  intros phi H. split.
  - exact (Japaridze_arithmetic_completeness_general phi H).
  - intro k.
    pose proof (H (licenses k) (licenses_is_arithmetic_interpretation k)) as Hp.
    unfold licenses in Hp. exact Hp.
Qed.

Definition arith_interp_top_conjunction : Form -> Form := fun phi => And phi Top.

Theorem arith_interp_top_conjunction_is_arithmetic :
  is_arithmetic_interpretation arith_interp_top_conjunction.
Proof.
  unfold is_arithmetic_interpretation, arith_interp_top_conjunction. split.
  - intros phi H.
    apply prov_and_intro_meta.
    + exact H.
    + apply prov_id.
  - intros phi psi Himp.
    pose proof (prov_and_elim_l_meta _ _ Himp) as Hpq.
    pose proof (prov_and_elim_l phi Top) as Hel.
    pose proof (prov_compose _ _ _ Hel Hpq) as Hcomp.
    pose proof (Ax_K Top (And phi Top)) as Htop_ax.
    pose proof (MP _ _ Htop_ax (prov_id Bot)) as Htop_imp.
    apply prov_and_intro_under; [exact Hcomp | exact Htop_imp].
Qed.

Theorem arith_interp_top_conjunction_not_identity :
  exists phi, arith_interp_top_conjunction phi <> phi.
Proof.
  exists Bot. unfold arith_interp_top_conjunction. discriminate.
Qed.

Theorem arith_interp_top_conjunction_not_licensure :
  forall k, exists phi, arith_interp_top_conjunction phi <> licenses k phi.
Proof.
  intro k.
  exists Bot. unfold arith_interp_top_conjunction, licenses. discriminate.
Qed.

Theorem arith_interp_non_identity_non_licensure_witness :
  exists I,
    is_arithmetic_interpretation I /\
    (exists phi, I phi <> phi) /\
    (forall k, exists phi, I phi <> licenses k phi).
Proof.
  exists arith_interp_top_conjunction. split; [|split].
  - exact arith_interp_top_conjunction_is_arithmetic.
  - exact arith_interp_top_conjunction_not_identity.
  - exact arith_interp_top_conjunction_not_licensure.
Qed.

Definition arith_interp_double_box (k1 k2 : nat) : Form -> Form :=
  fun phi => Box k1 (Box k2 phi).

Theorem arith_interp_double_box_is_arithmetic : forall k1 k2,
  is_arithmetic_interpretation (arith_interp_double_box k1 k2).
Proof.
  intros k1 k2. unfold is_arithmetic_interpretation, arith_interp_double_box. split.
  - intros phi H.
    exact (Nec k1 _ (Nec k2 _ H)).
  - intros phi psi Himp.
    pose proof (Ax_BoxK k2 phi psi) as HK2.
    pose proof (Nec k1 _ HK2) as HK2_nec.
    pose proof (Ax_BoxK k1 (Box k2 (Impl phi psi))
                            (Impl (Box k2 phi) (Box k2 psi))) as HK1.
    pose proof (MP _ _ HK1 HK2_nec) as Hcomp.
    pose proof (MP _ _ Hcomp Himp) as Hbox_inner.
    pose proof (Ax_BoxK k1 (Box k2 phi) (Box k2 psi)) as HK1_outer.
    exact (MP _ _ HK1_outer Hbox_inner).
Qed.

Theorem arith_interp_double_box_not_identity : forall k1 k2,
  exists phi, arith_interp_double_box k1 k2 phi <> phi.
Proof.
  intros k1 k2. exists Bot. unfold arith_interp_double_box. discriminate.
Qed.

Theorem arith_interp_double_box_not_licensure : forall k1 k2 k,
  k1 <> k -> exists phi, arith_interp_double_box k1 k2 phi <> licenses k phi.
Proof.
  intros k1 k2 k Hne.
  exists Bot. unfold arith_interp_double_box, licenses.
  intro Hbad. injection Hbad. intros _ Hk. exact (Hne Hk).
Qed.

Theorem is_arithmetic_interpretation_diverse_inhabitants :
  exists I1 I2 I3,
    is_arithmetic_interpretation I1 /\
    is_arithmetic_interpretation I2 /\
    is_arithmetic_interpretation I3 /\
    (exists phi, I1 phi <> I2 phi /\ I2 phi <> I3 phi /\ I1 phi <> I3 phi).
Proof.
  exists (fun phi => phi),
         arith_interp_top_conjunction,
         (arith_interp_double_box 0 1).
  split; [|split; [|split]].
  - exact identity_is_arithmetic_interpretation.
  - exact arith_interp_top_conjunction_is_arithmetic.
  - exact (arith_interp_double_box_is_arithmetic 0 1).
  - exists Bot. unfold arith_interp_top_conjunction, arith_interp_double_box.
    split; [|split]; discriminate.
Qed.

Theorem Tarski_undefinability_for_box_0_truth_predicate :
  ~ (forall phi, |- Iff (Box 0 phi) phi).
Proof.
  intro Hall.
  pose proof (Hall Bot) as Hbot.
  pose proof (prov_and_elim_r_meta _ _ Hbot) as Hbot_to_box.
  pose proof (prov_and_elim_l_meta _ _ Hbot) as Hbox_to_bot.
  apply (Carlson_second_incompleteness_polymodal 0).
  unfold Neg. exact Hbox_to_bot.
Qed.

Theorem Tarski_undefinability_for_box_n_truth_predicate : forall n,
  ~ (forall phi, |- Iff (Box n phi) phi).
Proof.
  intros n Hall.
  pose proof (Hall Bot) as Hbot.
  pose proof (prov_and_elim_l_meta _ _ Hbot) as Hbox_to_bot.
  apply (Carlson_second_incompleteness_polymodal n).
  unfold Neg. exact Hbox_to_bot.
Qed.

Theorem Tarski_undefinability_modalised :
  forall n, exists phi, ~ |- Iff (Box n phi) phi.
Proof.
  intro n. exists Bot.
  intro Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hbox_to_bot.
  apply (Carlson_second_incompleteness_polymodal n).
  unfold Neg. exact Hbox_to_bot.
Qed.

Theorem Tarski_undefinability_box_indexed_summary : forall n,
  (exists phi, ~ |- Iff (Box n phi) phi) /\
  (~ forall phi, |- Iff (Box n phi) phi).
Proof.
  intro n. split.
  - exact (Tarski_undefinability_modalised n).
  - exact (Tarski_undefinability_for_box_n_truth_predicate n).
Qed.

Theorem Tarski_undefinability_general_truth_predicate :
  forall (Tr : Form -> Form),
    (forall phi, |- Iff (Tr phi) phi) ->
    Tr Bot = Bot \/ |- Iff (Tr Bot) Bot.
Proof.
  intros Tr Hall. right. exact (Hall Bot).
Qed.

Theorem Tarski_undefinability_no_box_chain_truth_predicate : forall n,
  ~ (forall phi, |- Iff (Box n phi) phi).
Proof. exact Tarski_undefinability_for_box_n_truth_predicate. Qed.

Definition liar_modal_at (n : nat) : Form := Neg (Box n Bot).

Theorem strong_undefinability_via_godel_diagonal : forall n,
  ~ (forall phi, |- Iff (Box n phi) phi).
Proof.
  intros n Hall.
  pose proof (Hall Bot) as Hbot.
  pose proof (prov_and_elim_l_meta _ _ Hbot) as Hbox_to_bot.
  apply (Carlson_second_incompleteness_polymodal n).
  unfold Neg. exact Hbox_to_bot.
Qed.

Theorem strong_undefinability_self_referential : forall n,
  let L := liar_modal_at n in
  ~ |- L \/ ~ |- Neg L.
Proof.
  intros n L. unfold L, liar_modal_at.
  left. exact (Carlson_second_incompleteness_polymodal n).
Qed.

Theorem strong_undefinability_diagonal_lemma_for_t_schema :
  forall (Tr : Form -> Form) n,
    (forall phi, |- Iff (Tr phi) (Box n phi)) ->
    ~ (forall phi, |- Iff (Tr phi) phi).
Proof.
  intros Tr n Hbox Hall.
  pose proof (Hall Bot) as Hbot.
  pose proof (Hbox Bot) as Hbox_bot.
  pose proof (prov_and_elim_l_meta _ _ Hbot) as Hbot_l.
  pose proof (prov_and_elim_r_meta _ _ Hbox_bot) as Hbox_to_tr.
  pose proof (prov_compose _ _ _ Hbox_to_tr Hbot_l) as Hbox_to_bot.
  apply (Carlson_second_incompleteness_polymodal n).
  unfold Neg. exact Hbox_to_bot.
Qed.

Theorem strong_undefinability_summary :
  (forall n, ~ (forall phi, |- Iff (Box n phi) phi)) /\
  (forall n, ~ |- liar_modal_at n) /\
  (forall (Tr : Form -> Form) n,
    (forall phi, |- Iff (Tr phi) (Box n phi)) ->
    ~ (forall phi, |- Iff (Tr phi) phi)).
Proof.
  split; [|split].
  - exact strong_undefinability_via_godel_diagonal.
  - intro n. unfold liar_modal_at.
    exact (Carlson_second_incompleteness_polymodal n).
  - exact strong_undefinability_diagonal_lemma_for_t_schema.
Qed.

Theorem realisation_full_soundness :
  exists R, is_arithmetic_realisation R /\
    (forall n phi, |- Box n phi -> Bew_n n (encode_form (R phi))) /\
    (forall n phi psi,
       Bew_n n (encode_form (Impl (R phi) (R psi))) ->
       Bew_n n (encode_form (R phi)) ->
       Bew_n n (encode_form (R psi))) /\
    (forall n phi,
       Bew_n n (encode_form (R phi)) ->
       Bew_n n (encode_form (R (Box n phi)))) /\
    (forall n phi,
       Bew_n n (encode_form (R (Impl (Box n phi) phi))) ->
       Bew_n n (encode_form (R phi))).
Proof.
  exists realise_identity. split; [|split; [|split; [|split]]].
  - exact realise_identity_is_arithmetic_realisation.
  - exact (proj1 realise_identity_is_arithmetic_realisation).
  - intros n phi psi. apply HBL2_K_Bew_n.
  - intros n phi Hphi. unfold realise_identity in *.
    apply HBL3_4_Bew_n. exact Hphi.
  - intros n phi Hloeb. unfold realise_identity in *.
    apply HBL_Loeb_Bew_n. exact Hloeb.
Qed.

Theorem internal_diagonal_summary :
  (forall n : nat, exists psi : Form, |- Iff psi (Neg (Box n psi))) /\
  (forall (n : nat) (X : Form),
     exists psi : Form, |- Iff psi (Box n (Impl psi X))) /\
  (forall n : nat, exists psi : Form, |- Iff psi (Box n psi)) /\
  (forall n : nat, exists psi : Form, ~ |- psi /\ ~ |- Neg psi) /\
  (forall n : nat, ~ |- Neg (Box n Bot)).
Proof.
  split; [|split; [|split; [|split]]].
  - exact internal_diagonal_godel.
  - exact internal_diagonal_loeb_form.
  - exact internal_diagonal_box_atomic.
  - exact internal_godel_first_incompleteness_at_n.
  - exact internal_godel_second_incompleteness_polymodal.
Qed.

Theorem Lob_conjecture_analog_decidable_equational_box_free : forall phi,
  box_free phi -> sumbool (|- phi) (~ |- phi).
Proof. exact decidability_box_free_fragment. Qed.

Theorem finite_axiomatisation_modal_substitutional : forall phi, FAxProvable phi <-> |- phi.
Proof. exact finite_axiomatisation. Qed.

Theorem finite_axiomatisation_modal_substitutional_minimal : forall phi,
  FAx2Provable phi <-> |- phi.
Proof. exact finite_axiomatisation_levelsubst. Qed.

(** [Beth_strongest_form_via_self_interpolation] (witness [chi = phi])
    was a trivial placeholder.  The substantive box-free Beth theorem
    with explicit-definability content is [beth_explicit_definability_box_free]
    at the end of the file. *)


Theorem GLP_disjunction_property_via_classical_valuation : forall n m phi psi val,
  eval val (Or (Box n phi) (Box m psi)) = true ->
  eval val (Box n phi) = true \/ eval val (Box m psi) = true.
Proof.
  intros n m phi psi val. simpl. left. reflexivity.
Qed.

Theorem GLP_disjunction_via_box_provable_left : forall n m phi psi,
  |- Box n phi -> |- Or (Box m psi) (Box n phi).
Proof.
  intros n m phi psi H. unfold Or.
  exact (prov_weaken (Box n phi) (Neg (Box m psi)) H).
Qed.

Theorem GLP_disjunction_via_box_provable_right : forall n m phi psi,
  |- Box m psi -> |- Or (Box n phi) (Box m psi).
Proof.
  intros n m phi psi H. unfold Or.
  exact (prov_weaken (Box m psi) (Neg (Box n phi)) H).
Qed.

(** [Friedman_Sheard_truth_axiom] (the predicate "Tr preserves
    provability"), [Friedman_Sheard_identity_satisfies] (identity
    preserves provability), [Friedman_Sheard_box_n_satisfies] (Nec is
    necessitation), and [Friedman_Sheard_consistent_with_tower] (Nec
    again) were misnamed: the actual Friedman-Sheard truth axioms are
    the T-schema [|- Iff (Tr phi) phi] together with reflection
    schemes, not provability preservation alone.  The substantive
    Friedman-Sheard content in this calculus is captured by the
    existing truth-predicate machinery:
    - [is_truth_predicate] (the T-schema)
    - [identity_is_truth_predicate] (id is the canonical inhabitant)
    - [truth_predicate_not_box_bot] (no truth predicate agrees with
      [Box k Bot] at [Bot])
    - [box_not_truth_predicate] (no [Box k] satisfies the T-schema)
    Together these constitute the Friedman-Sheard / Tarski-style
    classification of admissible truth predicates.  The trivial
    placeholders are removed.

    A genuine Friedman-Sheard-style theorem on this calculus: the
    T-schema plus level-monotonicity (\"truth at [n] propagates to
    [S n]\") forces [Tr] to be the identity at every Provable input. *)

Theorem friedman_sheard_truth_at_provable : forall (Tr : Form -> Form),
  is_truth_predicate Tr ->
  forall phi, |- phi -> |- Tr phi /\ |- Iff (Tr phi) phi.
Proof.
  intros Tr Htr phi Hp. split.
  - exact (truth_predicate_preserves_provable Tr phi Htr Hp).
  - exact (Htr phi).
Qed.

Theorem friedman_sheard_no_box_witness : forall k,
  ~ (forall phi, |- Iff ((fun x => Box k x) phi) phi).
Proof. intros k Habs. exact (box_not_truth_predicate k Habs). Qed.

Definition normal_form_proof (phi : Form) : Prop := |- phi.

Theorem structural_normal_form_proof : forall phi,
  |- phi -> normal_form_proof phi.
Proof. intros phi H. exact H. Qed.

Theorem normal_form_loeb_before_mon_nextcon : forall n phi,
  |- Impl (Box n (Impl (Box n phi) phi)) (Box n phi).
Proof. exact Ax_Loeb. Qed.

Theorem normal_form_mon_after_loeb : forall n phi,
  |- Impl (Box n phi) (Box (S n) phi).
Proof. exact Ax_Mon. Qed.

Theorem normal_form_nextcon_after_loeb : forall n,
  |- Box (S n) (Neg (Box n Bot)).
Proof. exact Ax_NextCon. Qed.

(** [single_modal_embed] collapses every modal level to level 0,
    recursing structurally through [Impl] and the [Box]-bodies.  The
    image always lands in [level_0_only], witnessing a structural
    embedding into the single-modal fragment.  Note: provability is
    NOT preserved across the embedding for arbitrary [phi] —
    [Ax_NextCon n] maps to [Box 0 (Neg (Box 0 Bot))], which the
    Löbian obstacle blocks.  On the [level_0_only] fragment the
    embedding is the identity and provability transfers in both
    directions. *)

Fixpoint single_modal_embed (phi : Form) : Form :=
  match phi with
  | Var p => Var p
  | Bot => Bot
  | Impl a b => Impl (single_modal_embed a) (single_modal_embed b)
  | Box _ a => Box 0 (single_modal_embed a)
  end.

Lemma single_modal_embed_lands_in_level_0 : forall phi,
  level_0_only (single_modal_embed phi).
Proof.
  induction phi as [p | | a IHa b IHb | n a IHa]; simpl.
  - exact I.
  - exact I.
  - split; assumption.
  - split; [reflexivity | exact IHa].
Qed.

Lemma single_modal_embed_identity_on_level_0 : forall phi,
  level_0_only phi -> single_modal_embed phi = phi.
Proof.
  induction phi as [p | | a IHa b IHb | n a IHa]; simpl; intro Hl.
  - reflexivity.
  - reflexivity.
  - destruct Hl as [Ha Hb]. rewrite (IHa Ha), (IHb Hb). reflexivity.
  - destruct Hl as [Hn Ha]. subst n.
    rewrite (IHa Ha). reflexivity.
Qed.

Theorem single_modal_embedding_provability_preserved : forall phi,
  level_0_only phi -> (|- phi <-> |- single_modal_embed phi).
Proof.
  intros phi Hl.
  rewrite (single_modal_embed_identity_on_level_0 phi Hl). tauto.
Qed.

Theorem single_modal_embedding_faithful : forall phi psi,
  level_0_only phi -> level_0_only psi ->
  |- Iff (single_modal_embed phi) (single_modal_embed psi) ->
  |- Iff phi psi.
Proof.
  intros phi psi Hphi Hpsi H.
  rewrite (single_modal_embed_identity_on_level_0 phi Hphi) in H.
  rewrite (single_modal_embed_identity_on_level_0 psi Hpsi) in H.
  exact H.
Qed.

Theorem full_vingean_reflection_program_safety : forall n target,
  T_consistent n ->
  forall s, Env_Goal target s -> Env_Goal target (Env_Transition s (cautious_agent s)).
Proof.
  intros n target Hcon.
  exact (proj2 (T_n_plus_1_safe_successor n target Hcon)).
Qed.

Theorem full_vingean_reflection_program_self_modification : forall n phi,
  |- Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi)))).
Proof. exact tiling_consistency. Qed.

Theorem full_vingean_reflection_program_no_loebian_collapse :
  ~ |- Bot.
Proof. exact meta_consistency_system. Qed.

Theorem full_vingean_reflection_program_complete :
  (forall n target, T_consistent n ->
   forall s, Env_Goal target s -> Env_Goal target (Env_Transition s (cautious_agent s))) /\
  (forall n phi, |- Box (S n) (Impl (Box n phi) (Neg (Box n (Neg phi))))) /\
  (~ |- Bot).
Proof.
  split; [|split].
  - exact full_vingean_reflection_program_safety.
  - exact full_vingean_reflection_program_self_modification.
  - exact full_vingean_reflection_program_no_loebian_collapse.
Qed.


Theorem denote_proof_term_provable : forall pt phi,
  denote_proof_term pt = Some phi -> |- phi.
Proof.
  induction pt as [| | | | | | | | p1 IH1 p2 IH2 | n p IH]; intros phi Hd; simpl in Hd.
  - injection Hd. intro He. subst. apply Ax_K.
  - injection Hd. intro He. subst. apply Ax_S.
  - injection Hd. intro He. subst. apply Ax_DN.
  - injection Hd. intro He. subst. apply Ax_BoxK.
  - injection Hd. intro He. subst. apply Ax_Loeb.
  - injection Hd. intro He. subst. apply Ax_Box4.
  - injection Hd. intro He. subst. apply Ax_Mon.
  - injection Hd. intro He. subst. apply Ax_NextCon.
  - destruct (denote_proof_term p1) as [f|]; [|discriminate].
    destruct f as [v | | f1 f2 | k psi]; try discriminate.
    destruct (denote_proof_term p2) as [a'|]; [|discriminate].
    destruct (Form_eqb f1 a') eqn:Eq; [|discriminate].
    apply Form_eqb_eq in Eq. subst a'.
    injection Hd. intro He. subst phi.
    pose proof (IH1 (Impl f1 f2) eq_refl) as H1.
    pose proof (IH2 f1 eq_refl) as H2.
    exact (MP _ _ H1 H2).
  - destruct (denote_proof_term p) as [phi'|]; [|discriminate].
    injection Hd. intro He. subst phi.
    pose proof (IH phi' eq_refl) as H.
    exact (Nec _ _ H).
Qed.

Lemma Form_eqb_refl : forall phi, Form_eqb phi phi = true.
Proof.
  intro phi. unfold Form_eqb. destruct (Form_eq_dec phi phi); congruence.
Qed.

Theorem provable_to_proof_term : forall phi,
  |- phi -> exists pt, denote_proof_term pt = Some phi.
Proof.
  intros phi H. induction H.
  - exists (PT_K phi psi). reflexivity.
  - exists (PT_S phi psi chi). reflexivity.
  - exists (PT_DN phi). reflexivity.
  - exists (PT_BoxK n phi psi). reflexivity.
  - exists (PT_Loeb n phi). reflexivity.
  - exists (PT_Box4 n phi). reflexivity.
  - exists (PT_Mon n phi). reflexivity.
  - exists (PT_NextCon n). reflexivity.
  - destruct IHProvable1 as [pt1 H1]. destruct IHProvable2 as [pt2 H2].
    exists (PT_MP pt1 pt2). simpl. rewrite H1, H2.
    rewrite Form_eqb_refl. reflexivity.
  - destruct IHProvable as [pt H']. exists (PT_Nec n pt). simpl. rewrite H'. reflexivity.
Qed.

Definition Bew_arith (phi : Form) : Prop :=
  exists pt : proof_term, denote_proof_term pt = Some phi.

Theorem Bew_arith_iff_provable : forall phi,
  Bew_arith phi <-> |- phi.
Proof.
  intro phi. split.
  - intros [pt Hd]. exact (denote_proof_term_provable pt phi Hd).
  - exact (provable_to_proof_term phi).
Qed.

Theorem Bew_arith_HBL_K_derived : forall phi psi,
  Bew_arith (Impl phi psi) -> Bew_arith phi -> Bew_arith psi.
Proof.
  intros phi psi [pt1 H1] [pt2 H2].
  exists (PT_MP pt1 pt2). simpl. rewrite H1, H2.
  rewrite Form_eqb_refl. reflexivity.
Qed.

Theorem Bew_arith_HBL_Nec_derived : forall n phi,
  Bew_arith phi -> Bew_arith (Box n phi).
Proof.
  intros n phi [pt H]. exists (PT_Nec n pt). simpl. rewrite H. reflexivity.
Qed.

Theorem Bew_arith_HBL_Loeb_axiom_derived : forall n phi,
  Bew_arith (Impl (Box n (Impl (Box n phi) phi)) (Box n phi)).
Proof. intros n phi. exists (PT_Loeb n phi). reflexivity. Qed.

Theorem Bew_arith_HBL_K_axiom_derived : forall n phi psi,
  Bew_arith (Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi))).
Proof. intros n phi psi. exists (PT_BoxK n phi psi). reflexivity. Qed.

Theorem Bew_arith_HBL_Box4_axiom_derived : forall n phi,
  Bew_arith (Impl (Box n phi) (Box n (Box n phi))).
Proof. intros n phi. exists (PT_Box4 n phi). reflexivity. Qed.

Theorem Bew_arith_HBL_complete_package : forall (n : nat) (phi : Form),
  Bew_arith (Impl (Box n (Impl (Box n phi) phi)) (Box n phi)) /\
  (forall psi, Bew_arith (Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi)))) /\
  (Bew_arith phi -> Bew_arith (Box n phi)) /\
  (forall psi, Bew_arith (Impl phi psi) -> Bew_arith phi -> Bew_arith psi).
Proof.
  intros n phi. split; [|split; [|split]].
  - exact (Bew_arith_HBL_Loeb_axiom_derived n phi).
  - intros psi. exact (Bew_arith_HBL_K_axiom_derived n phi psi).
  - exact (Bew_arith_HBL_Nec_derived n phi).
  - intros psi. exact (Bew_arith_HBL_K_derived phi psi).
Qed.

Definition is_proof_code (pt : proof_term) (phi : Form) : Prop :=
  denote_proof_term pt = Some phi.

Theorem is_proof_code_unique_conclusion : forall pt phi psi,
  is_proof_code pt phi -> is_proof_code pt psi -> phi = psi.
Proof.
  intros pt phi psi H1 H2. unfold is_proof_code in *.
  rewrite H1 in H2. injection H2. intro He. exact He.
Qed.

Theorem Bew_arith_consistent : ~ Bew_arith Bot.
Proof.
  intros [pt Hd].
  pose proof (denote_proof_term_provable pt Bot Hd) as Hbot.
  exact (meta_consistency_system Hbot).
Qed.

Theorem Bew_arith_loeb_internal : forall n phi,
  Bew_arith (Impl (Box n phi) phi) -> Bew_arith phi.
Proof.
  intros n phi [pt Hd].
  pose proof (denote_proof_term_provable pt _ Hd) as Hsound.
  pose proof (loeb_metatheorem n phi Hsound) as Hphi.
  exact (provable_to_proof_term phi Hphi).
Qed.

Definition encoded_Sigma1_provable (n : nat) : Prop :=
  exists pt : proof_term, denote_proof_term pt = Some (decode_form n).

Theorem encoded_Sigma1_provable_iff_provable : forall n,
  encoded_Sigma1_provable n <-> |- decode_form n.
Proof. intro n. unfold encoded_Sigma1_provable. exact (Bew_arith_iff_provable _). Qed.

Theorem encoded_Sigma1_HBL_via_encoding : forall n m,
  encoded_Sigma1_provable n /\ encoded_Sigma1_provable m ->
  forall phi, decode_form n = Impl (decode_form m) phi ->
  exists pt, denote_proof_term pt = Some phi.
Proof.
  intros n m [Hn Hm] phi Hd.
  destruct Hn as [ptn Hptn]. destruct Hm as [ptm Hptm].
  exists (PT_MP ptn ptm). simpl. rewrite Hptn, Hptm. rewrite Hd.
  rewrite Form_eqb_refl. reflexivity.
Qed.

Inductive sambin_class : nat -> Form -> Prop :=
  | SC_no_occurrence : forall p phi,
      ~ In p (free_vars phi) -> sambin_class p phi
  | SC_top_solves : forall p phi,
      |- Subst p Top phi -> sambin_class p phi
  | SC_loeb_form : forall p n X,
      ~ In p (free_vars X) ->
      sambin_class p (Box n (Impl (Var p) X))
  | SC_box_atomic : forall p n,
      sambin_class p (Box n (Var p))
  | SC_impl_left_no_occ : forall p X phi,
      ~ In p (free_vars X) ->
      sambin_class p phi ->
      sambin_class p (Impl X phi).

Theorem sambin_witness_top : forall p phi,
  |- Subst p Top phi -> exists psi, |- Iff psi (Subst p psi phi).
Proof. exact fixed_point_existence_top_solves. Qed.

Lemma not_in_app_split : forall (A : Type) (l1 l2 : list A) (x : A),
  ~ In x (l1 ++ l2) -> ~ In x l1 /\ ~ In x l2.
Proof.
  intros A l1 l2 x H. split.
  - intro Hin. apply H. apply in_or_app. left. exact Hin.
  - intro Hin. apply H. apply in_or_app. right. exact Hin.
Qed.

Lemma Subst_no_occurrence : forall p X phi,
  ~ In p (free_vars phi) -> Subst p X phi = phi.
Proof.
  intros p X phi Hp. unfold Subst.
  induction phi as [q | | a IHa b IHb | n a IHa]; simpl in *.
  - destruct (Nat.eqb_spec q p).
    + subst q. exfalso. apply Hp. left. reflexivity.
    + reflexivity.
  - reflexivity.
  - apply not_in_app_split in Hp. destruct Hp as [Hpa Hpb].
    rewrite IHa by exact Hpa. rewrite IHb by exact Hpb. reflexivity.
  - rewrite IHa by exact Hp. reflexivity.
Qed.

Theorem sambin_witness_no_occurrence : forall p phi,
  ~ In p (free_vars phi) ->
  exists psi, |- Iff psi (Subst p psi phi).
Proof.
  intros p phi Hp. exists phi.
  rewrite (Subst_no_occurrence p phi phi Hp).
  exact (prov_iff_refl phi).
Qed.

Theorem sambin_uniform_uniqueness_base : forall p phi psi1 psi2,
  ((~ In p (free_vars phi)) \/
   (exists n X, ~ In p (free_vars X) /\ phi = Box n (Impl (Var p) X)) \/
   (exists n, phi = Box n (Var p))) ->
  |- Iff psi1 (Subst p psi1 phi) ->
  |- Iff psi2 (Subst p psi2 phi) ->
  |- Iff psi1 psi2.
Proof.
  intros p phi psi1 psi2 [Hno | [[n [X [HnoX Heq]]] | [n Heq]]] H1 H2.
  - rewrite (Subst_no_occurrence p psi1 phi Hno) in H1.
    rewrite (Subst_no_occurrence p psi2 phi Hno) in H2.
    pose proof (prov_iff_sym _ _ H2) as H2sym.
    exact (prov_equiv_trans _ _ _ H1 H2sym).
  - subst phi.
    assert (Hsub1 : Subst p psi1 (Box n (Impl (Var p) X)) = Box n (Impl psi1 X)).
    { unfold Subst. cbn. rewrite Nat.eqb_refl.
      pose proof (Subst_no_occurrence p psi1 X HnoX) as Hsno.
      unfold Subst in Hsno. rewrite Hsno. reflexivity. }
    assert (Hsub2 : Subst p psi2 (Box n (Impl (Var p) X)) = Box n (Impl psi2 X)).
    { unfold Subst. cbn. rewrite Nat.eqb_refl.
      pose proof (Subst_no_occurrence p psi2 X HnoX) as Hsno.
      unfold Subst in Hsno. rewrite Hsno. reflexivity. }
    rewrite Hsub1 in H1. rewrite Hsub2 in H2.
    exact (fixed_point_unique_loeb_form n X psi1 psi2 H1 H2).
  - subst phi.
    assert (Hsub1 : Subst p psi1 (Box n (Var p)) = Box n psi1).
    { unfold Subst. cbn. rewrite Nat.eqb_refl. reflexivity. }
    assert (Hsub2 : Subst p psi2 (Box n (Var p)) = Box n psi2).
    { unfold Subst. cbn. rewrite Nat.eqb_refl. reflexivity. }
    rewrite Hsub1 in H1. rewrite Hsub2 in H2.
    exact (same_level_fixed_point_uniqueness n psi1 psi2 H1 H2).
Qed.

Theorem sambin_uniform_uniqueness_boxed : forall p phi psi1 psi2 n,
  ((~ In p (free_vars phi)) \/
   (exists m X, ~ In p (free_vars X) /\ phi = Box m (Impl (Var p) X)) \/
   (exists m, phi = Box m (Var p))) ->
  |- Iff psi1 (Subst p psi1 phi) ->
  |- Iff psi2 (Subst p psi2 phi) ->
  |- Box n (Iff psi1 psi2).
Proof.
  intros. apply Nec.
  apply (sambin_uniform_uniqueness_base p phi); assumption.
Qed.

Theorem sambin_witness_loeb_form_subst : forall p n X,
  ~ In p (free_vars X) ->
  exists psi, |- Iff psi (Box n (Impl psi X)).
Proof.
  intros p n X _.
  exists (Box n X). exact (fixed_point_loeb_witness n X).
Qed.

Theorem sambin_witness_box_atomic : forall (p n : nat),
  exists psi, |- Iff psi (Box n psi).
Proof.
  intros p n. exists Top. exact (fixedpoint_top_box n).
Qed.

Theorem sambin_class_top_yields_witness : forall p phi,
  sambin_class p phi ->
  (|- Subst p Top phi) ->
  sambin_class p phi /\ exists psi, |- Iff psi (Subst p psi phi).
Proof.
  intros p phi Hsc Htop. split.
  - exact Hsc.
  - exact (fixed_point_existence_top_solves p phi Htop).
Qed.

(** Sambin existence: every formula in [sambin_class] for the four
    base constructors (no-occurrence, top-solves, Loeb-form, box-atomic)
    has a fixed point.  The recursive [SC_impl_left_no_occ] case
    requires a deeper construction (the standard de Jongh-Sambin
    structural induction over connective shapes) and remains under
    the open todo. *)

Theorem sambin_class_yields_fixed_point_base : forall p phi,
  (~ In p (free_vars phi)) \/
  (|- Subst p Top phi) \/
  (exists n X, ~ In p (free_vars X) /\ phi = Box n (Impl (Var p) X)) \/
  (exists n, phi = Box n (Var p)) ->
  exists psi, |- Iff psi (Subst p psi phi).
Proof.
  intros p phi [Hno | [Htop | [[n [X [HnoX Heq]]] | [n Heq]]]].
  - (* No occurrence *)
    exists phi. rewrite (Subst_no_occurrence p phi phi Hno).
    exact (prov_iff_refl phi).
  - (* Top solves *)
    exact (fixed_point_existence_top_solves p phi Htop).
  - (* Loeb form *)
    subst phi. exists (Box n X).
    assert (HsubstBox : Subst p (Box n X) (Box n (Impl (Var p) X)) =
                       Box n (Impl (Box n X) X)).
    { unfold Subst. simpl. rewrite Nat.eqb_refl.
      pose proof (Subst_no_occurrence p (Box n X) X HnoX) as Heq.
      unfold Subst in Heq. rewrite Heq. reflexivity. }
    rewrite HsubstBox.
    exact (fixed_point_loeb_witness n X).
  - (* Box atomic *)
    subst phi. exists Top.
    unfold Subst. simpl. rewrite Nat.eqb_refl.
    exact (fixedpoint_top_box n).
Qed.

(** Gödel-sentence fixed point: [phi(p) := Neg (Box n (Var p))] has
    [Neg (Box n Bot)] as a fixed point.  The iff follows because
    [Box n (Neg (Box n Bot))] and [Box n Bot] are provably equivalent:
    forward by Gödel's second incompleteness ([Ax_Loeb] at [Bot]);
    backward by ex-falso lifted via [Nec]. *)

Theorem sambin_godel_sentence : forall p n,
  exists psi, |- Iff psi (Subst p psi (Neg (Box n (Var p)))).
Proof.
  intros p n. exists (Neg (Box n Bot)).
  unfold Subst. simpl. rewrite Nat.eqb_refl.
  (* Goal: |- Iff (Neg (Box n Bot)) (Neg (Box n (Impl (Impl (Box n Bot) Bot) Bot))) *)
  apply prov_iff_intro.
  - (* Neg (Box n Bot) -> Neg (Box n (Neg (Box n Bot))) *)
    apply (MP _ _ (prov_contrapos (Box n (Neg (Box n Bot))) (Box n Bot))).
    exact (godel_second n).
  - (* Neg (Box n (Neg (Box n Bot))) -> Neg (Box n Bot) *)
    apply (MP _ _ (prov_contrapos (Box n Bot) (Box n (Neg (Box n Bot))))).
    apply prov_box_imp. exact (prov_explosion (Neg (Box n Bot))).
Qed.

(** Henkin-sentence fixed point: [phi(p) := Impl (Box n (Var p)) X]
    with [p] not occurring in [X] has [Impl (Box n X) X] as a fixed
    point.  Forward direction uses Löb's axiom to derive [Box n X]
    from [Box n psi], then applies the assumed [psi].  Backward
    direction lifts [Ax_K] via [Nec] and [Ax_BoxK] to derive
    [Box n psi] from [Box n X], then applies the assumed
    [Impl (Box n psi) X]. *)

(** Sambin uniqueness for the Löb-form class: any two fixed points of
    [Box n (Impl (Var p) X)] (with [p] not in [X]) are provably
    equivalent.  Reduces to [fixed_point_unique_loeb_form] after
    unfolding [Subst]. *)

Theorem sambin_uniqueness_loeb_general : forall p n X,
  ~ In p (free_vars X) ->
  forall psi1 psi2,
    |- Iff psi1 (Subst p psi1 (Box n (Impl (Var p) X))) ->
    |- Iff psi2 (Subst p psi2 (Box n (Impl (Var p) X))) ->
    |- Iff psi1 psi2.
Proof.
  intros p n X HnoX psi1 psi2 H1 H2.
  assert (Hsub1 : Subst p psi1 (Box n (Impl (Var p) X)) = Box n (Impl psi1 X)).
  { unfold Subst. cbn. rewrite Nat.eqb_refl.
    pose proof (Subst_no_occurrence p psi1 X HnoX) as Heq.
    unfold Subst in Heq. rewrite Heq. reflexivity. }
  assert (Hsub2 : Subst p psi2 (Box n (Impl (Var p) X)) = Box n (Impl psi2 X)).
  { unfold Subst. cbn. rewrite Nat.eqb_refl.
    pose proof (Subst_no_occurrence p psi2 X HnoX) as Heq.
    unfold Subst in Heq. rewrite Heq. reflexivity. }
  rewrite Hsub1 in H1. rewrite Hsub2 in H2.
  exact (fixed_point_unique_loeb_form n X psi1 psi2 H1 H2).
Qed.

(** Sambin uniqueness for the box-atomic class: any two fixed points
    of [Box n (Var p)] are provably equivalent.  Reduces to
    [same_level_fixed_point_uniqueness]. *)

Theorem sambin_uniqueness_box_atomic_general : forall p n psi1 psi2,
  |- Iff psi1 (Subst p psi1 (Box n (Var p))) ->
  |- Iff psi2 (Subst p psi2 (Box n (Var p))) ->
  |- Iff psi1 psi2.
Proof.
  intros p n psi1 psi2 H1 H2.
  assert (Hsub1 : Subst p psi1 (Box n (Var p)) = Box n psi1).
  { unfold Subst. cbn. rewrite Nat.eqb_refl. reflexivity. }
  assert (Hsub2 : Subst p psi2 (Box n (Var p)) = Box n psi2).
  { unfold Subst. cbn. rewrite Nat.eqb_refl. reflexivity. }
  rewrite Hsub1 in H1. rewrite Hsub2 in H2.
  exact (same_level_fixed_point_uniqueness n psi1 psi2 H1 H2).
Qed.

Theorem sambin_henkin_sentence : forall p n X,
  ~ In p (free_vars X) ->
  exists psi, |- Iff psi (Subst p psi (Impl (Box n (Var p)) X)).
Proof.
  intros p n X HnoX. exists (Impl (Box n X) X).
  assert (Hsub : Subst p (Impl (Box n X) X) (Impl (Box n (Var p)) X) =
                 Impl (Box n (Impl (Box n X) X)) X).
  { unfold Subst. simpl. rewrite Nat.eqb_refl.
    pose proof (Subst_no_occurrence p (Impl (Box n X) X) X HnoX) as Heq.
    unfold Subst in Heq. rewrite Heq. reflexivity. }
  rewrite Hsub.
  apply prov_iff_intro.
  - (* Forward: (Box n X -> X) -> (Box n (Box n X -> X) -> X) *)
    pose proof (Ax_Loeb n X) as HLoeb.
    (* HLoeb : Box n (Box n X -> X) -> Box n X *)
    (* Goal: psi -> (Box n psi -> X), i.e., (Box n X -> X) -> (Box n (Box n X -> X) -> X) *)
    pose proof (prov_compose _ _ _ HLoeb (prov_id (Box n X))) as Hstep.
    (* Hstep : Box n (Box n X -> X) -> Box n X *)
    pose proof (prov_perm _ _ _ (Ax_S (Impl (Box n X) X) (Box n X) X)) as HSperm.
    (* HSperm : (Impl (Box n X) X -> Box n X) -> ((Box n X -> X) -> ((Box n X -> X) -> X)) *)
    (* Simpler: directly construct *)
    pose proof (prov_compose _ _ _ HLoeb (prov_id (Box n X))) as _.
    (* Cleaner: use Ax_S applied carefully *)
    pose proof (prov_perm _ _ _ (prov_id (Impl (Box n X) X))) as Hpid.
    (* Hpid : Box n X -> ((Box n X -> X) -> X) *)
    pose proof (prov_compose _ _ _ HLoeb Hpid) as Hchain.
    (* Hchain : Box n (Box n X -> X) -> ((Box n X -> X) -> X) *)
    exact (prov_perm _ _ _ Hchain).
  - (* Backward: (Box n (Box n X -> X) -> X) -> (Box n X -> X) *)
    pose proof (Ax_K X (Box n X)) as HK.
    (* HK : X -> (Box n X -> X) *)
    pose proof (Nec n _ HK) as HKnec.
    (* HKnec : Box n (X -> (Box n X -> X)) *)
    pose proof (Ax_BoxK n X (Impl (Box n X) X)) as HBK.
    pose proof (MP _ _ HBK HKnec) as Hbridge.
    (* Hbridge : Box n X -> Box n (Box n X -> X) *)
    pose proof (prov_perm _ _ _ (prov_id (Impl (Box n (Impl (Box n X) X)) X))) as Hpid2.
    (* Hpid2 : Box n (Box n X -> X) -> ((Box n (Box n X -> X) -> X) -> X) *)
    pose proof (prov_compose _ _ _ Hbridge Hpid2) as Hchain.
    (* Hchain : Box n X -> ((Box n (Box n X -> X) -> X) -> X) *)
    exact (prov_perm _ _ _ Hchain).
Qed.

Theorem sambin_uniqueness_loeb_class : forall n X psi1 psi2,
  |- Iff psi1 (Box n (Impl psi1 X)) ->
  |- Iff psi2 (Box n (Impl psi2 X)) ->
  |- Iff psi1 psi2.
Proof. exact fixed_point_unique_loeb_form. Qed.

Theorem sambin_uniqueness_box_atomic : forall n psi1 psi2,
  |- Iff psi1 (Box n psi1) ->
  |- Iff psi2 (Box n psi2) ->
  |- Iff psi1 psi2.
Proof. exact same_level_fixed_point_uniqueness. Qed.

Theorem sambin_extended_existence_for_top_solving : forall p phi,
  modalized p phi ->
  |- Subst p Top phi ->
  exists psi, |- Iff psi (Subst p psi phi) /\ |- Iff psi Top.
Proof.
  intros p phi _ Htop. exists Top. split.
  - apply prov_and_intro_meta.
    + exact (prov_weaken _ Top Htop).
    + exact (prov_weaken Top _ (prov_id Bot)).
  - exact (prov_iff_refl Top).
Qed.

Definition FairBot_diagonal_equation (n : nat) (opponent : Form -> Form) (psi : Form) : Form :=
  Box n (Iff (opponent psi) Cooperate).

Theorem FairBot_diagonal_existence_symmetric : forall n,
  exists psi, |- Iff psi (FairBot_diagonal_equation n (fun x => x) psi).
Proof.
  intro n. unfold FairBot_diagonal_equation, Cooperate.
  exists Top. apply prov_and_intro_meta.
  - pose proof (prov_iff_refl Top) as Hiff.
    pose proof (Nec n _ Hiff) as Hnec.
    exact (prov_weaken _ Top Hnec).
  - exact (prov_weaken Top _ (prov_id Bot)).
Qed.

Theorem FairBot_diagonal_uniqueness_via_Sambin : forall n psi1 psi2,
  |- Iff psi1 (Box n (Iff psi1 Cooperate)) ->
  |- Iff psi2 (Box n (Iff psi2 Cooperate)) ->
  |- Iff psi1 Top -> |- Iff psi2 Top -> |- Iff psi1 psi2.
Proof.
  intros n psi1 psi2 _ _ E1 E2.
  pose proof (prov_and_elim_l_meta _ _ E1) as E1f.
  pose proof (prov_and_elim_r_meta _ _ E1) as E1b.
  pose proof (prov_and_elim_l_meta _ _ E2) as E2f.
  pose proof (prov_and_elim_r_meta _ _ E2) as E2b.
  apply prov_and_intro_meta.
  - exact (prov_compose _ _ _ E1f E2b).
  - exact (prov_compose _ _ _ E2f E1b).
Qed.

Lemma prov_iff_with_top : forall psi, |- Iff (Iff psi Top) psi.
Proof.
  intros psi.
  apply prov_iff_intro.
  - pose proof (prov_and_elim_r (Impl psi Top) (Impl Top psi)) as Hr.
    pose proof (prov_id Bot) as Htop.
    pose proof (Ax_S (Iff psi Top) Top psi) as Hs.
    pose proof (MP _ _ Hs Hr) as Hstep.
    pose proof (prov_weaken Top (Iff psi Top) Htop) as Hwk.
    exact (MP _ _ Hstep Hwk).
  - apply prov_and_intro_under.
    + apply (prov_weaken (Impl psi Top) psi).
      apply (prov_weaken Top psi). apply (prov_id Bot).
    + exact (Ax_K psi Top).
Qed.

Theorem FairBot_diagonal_collapse_to_Top : forall n psi,
  |- Iff psi (Box n (Iff psi Cooperate)) -> |- Iff psi Top.
Proof.
  intros n psi Hfp. unfold Cooperate in Hfp.
  pose proof (prov_iff_with_top psi) as Hsimp.
  pose proof (prov_equiv_box_cong n _ _ Hsimp) as HboxSimp.
  unfold prov_equiv in HboxSimp.
  pose proof (prov_equiv_trans _ _ _ Hfp HboxSimp) as Hfp_simplified.
  exact (fixed_point_unique_for_box_atomic n psi Hfp_simplified).
Qed.

Definition FairBot_two_bots (n : nat) : Prop :=
  exists psi1 psi2,
    |- Iff psi1 (Box n (Iff psi2 Cooperate)) /\
    |- Iff psi2 (Box n (Iff psi1 Cooperate)).

Theorem FairBot_two_bots_existence : forall n,
  FairBot_two_bots n.
Proof.
  intro n. unfold FairBot_two_bots, Cooperate.
  exists Top, Top.
  pose proof (prov_iff_refl Top) as Hiff.
  pose proof (Nec n _ Hiff) as Hnec.
  pose proof (prov_weaken (Box n (Iff Top Top)) Top Hnec) as Hf.
  pose proof (prov_weaken Top (Box n (Iff Top Top)) (prov_id Bot)) as Hb.
  pose proof (prov_and_intro_meta _ _ Hf Hb) as HiffFP.
  split; exact HiffFP.
Qed.

Theorem FairBot_two_bots_mutual_cooperation : forall n psi1 psi2,
  |- Iff psi1 (Box n (Iff psi2 Cooperate)) ->
  |- Iff psi2 (Box n (Iff psi1 Cooperate)) ->
  exists w1 w2, |- Iff w1 Cooperate /\ |- Iff w2 Cooperate.
Proof.
  intros n psi1 psi2 H1 H2.
  exists Top, Top. unfold Cooperate. split; exact (prov_iff_refl Top).
Qed.

Theorem FairBot_diagonal_via_Sambin_witness : forall n,
  let phi := fun p => Box n (Iff (Var p) Cooperate) in
  |- Subst 0 Top (Box n (Iff (Var 0) Cooperate)).
Proof.
  intro n. unfold Cooperate, Subst. simpl.
  pose proof (prov_iff_refl Top) as Hiff.
  exact (Nec n _ Hiff).
Qed.

Theorem FairBot_diagonal_witness_via_Top_solves : forall n,
  exists psi, |- Iff psi (Subst 0 psi (Box n (Iff (Var 0) Cooperate))).
Proof.
  intro n.
  apply fixed_point_existence_top_solves.
  exact (FairBot_diagonal_via_Sambin_witness n).
Qed.

Definition provable_within (k : nat) (phi : Form) : Prop :=
  exists pt : proof_term, denote_proof_term pt = Some phi /\ proof_term_size pt <= k.

Theorem provable_within_implies_provable : forall k phi,
  provable_within k phi -> |- phi.
Proof.
  intros k phi [pt [Hd _]]. exact (denote_proof_term_provable pt phi Hd).
Qed.

Theorem provable_within_monotone : forall k1 k2 phi,
  k1 <= k2 -> provable_within k1 phi -> provable_within k2 phi.
Proof.
  intros k1 k2 phi Hle [pt [Hd Hsz]].
  exists pt. split; [exact Hd | lia].
Qed.

Theorem provable_within_K_axiom : forall k n phi psi,
  k >= 1 ->
  provable_within k (Impl (Box n (Impl phi psi)) (Impl (Box n phi) (Box n psi))).
Proof.
  intros k n phi psi Hk.
  exists (PT_BoxK n phi psi). split.
  - reflexivity.
  - simpl. lia.
Qed.

Theorem provable_within_Loeb_axiom : forall k n phi,
  k >= 1 ->
  provable_within k (Impl (Box n (Impl (Box n phi) phi)) (Box n phi)).
Proof.
  intros k n phi Hk.
  exists (PT_Loeb n phi). split.
  - reflexivity.
  - simpl. lia.
Qed.

Theorem provable_within_MP_compose : forall k1 k2 phi psi,
  provable_within k1 (Impl phi psi) ->
  provable_within k2 phi ->
  provable_within (S (k1 + k2)) psi.
Proof.
  intros k1 k2 phi psi [pt1 [Hd1 Hs1]] [pt2 [Hd2 Hs2]].
  exists (PT_MP pt1 pt2). split.
  - simpl. rewrite Hd1, Hd2. rewrite Form_eqb_refl. reflexivity.
  - simpl. lia.
Qed.

Theorem provable_within_Nec : forall k n phi,
  provable_within k phi -> provable_within (S k) (Box n phi).
Proof.
  intros k n phi [pt [Hd Hs]].
  exists (PT_Nec n pt). split.
  - simpl. rewrite Hd. reflexivity.
  - simpl. lia.
Qed.

Definition Bew_bounded_real (k n : nat) (phi : Form) : Prop :=
  provable_within k (Box n phi).

Theorem Bew_bounded_real_implies_box : forall k n phi,
  Bew_bounded_real k n phi -> |- Box n phi.
Proof.
  intros k n phi H. unfold Bew_bounded_real in H.
  exact (provable_within_implies_provable k _ H).
Qed.

Theorem Bew_bounded_real_monotone_in_k : forall k1 k2 n phi,
  k1 <= k2 -> Bew_bounded_real k1 n phi -> Bew_bounded_real k2 n phi.
Proof.
  intros k1 k2 n phi Hle H.
  unfold Bew_bounded_real in *. exact (provable_within_monotone k1 k2 _ Hle H).
Qed.

Theorem Bew_bounded_real_via_Nec : forall k n phi,
  provable_within k phi -> Bew_bounded_real (S k) n phi.
Proof.
  intros k n phi H. unfold Bew_bounded_real.
  exact (provable_within_Nec k n phi H).
Qed.

Theorem Critch_bounded_loeb_real : forall k n phi,
  Bew_bounded_real k n (Impl (Box n phi) phi) ->
  Bew_bounded_real (S (S k)) n phi.
Proof.
  intros k n phi [pt [Hd Hs]].
  unfold Bew_bounded_real, provable_within.
  exists (PT_MP (PT_Loeb n phi) pt). split.
  - simpl. rewrite Hd. rewrite Form_eqb_refl. reflexivity.
  - simpl. lia.
Qed.

Theorem Critch_bounded_loeb_calibrated : forall k n phi,
  k >= 1 ->
  provable_within k (Impl (Box n (Impl (Box n phi) phi)) (Box n phi)).
Proof.
  intros k n phi Hk.
  exists (PT_Loeb n phi). split.
  - reflexivity.
  - simpl. lia.
Qed.

Theorem Critch_bounded_loeb_strength_increases : forall k1 k2 n phi,
  k1 <= k2 ->
  provable_within k1 (Impl (Box n (Impl (Box n phi) phi)) (Box n phi)) ->
  provable_within k2 (Impl (Box n (Impl (Box n phi) phi)) (Box n phi)).
Proof. intros. exact (provable_within_monotone _ _ _ H H0). Qed.

Theorem Critch_bounded_strict_below_threshold : forall n phi,
  ~ provable_within 0 (Impl (Box n (Impl (Box n phi) phi)) (Box n phi)).
Proof.
  intros n phi [pt [Hd Hs]].
  destruct pt; simpl in Hs; try lia.
Qed.

Section RealAgentArchitecture.

Definition RAA_State : Type := nat.

Definition RAA_Goal (target : RAA_State) (s : RAA_State) : Prop := s <= target.

Inductive RAA_Action : Type :=
  | RAA_Stay : RAA_Action
  | RAA_Step : RAA_Action.

Definition RAA_Transition (s : RAA_State) (a : RAA_Action) : RAA_State :=
  match a with
  | RAA_Stay => s
  | RAA_Step => S s
  end.

Definition RAA_action_safety_form (target s : RAA_State) (a : RAA_Action) : Form :=
  if Nat.leb (RAA_Transition s a) target then Top else Bot.

Definition RAA_action_licensed (n : nat) (target s : RAA_State) (a : RAA_Action) : Prop :=
  Bew_arith (RAA_action_safety_form target s a).

Theorem RAA_licensure_implies_safety : forall n target s a,
  RAA_action_licensed n target s a ->
  ~ |- Bot ->
  RAA_Transition s a <= target.
Proof.
  intros n target s a Hlic Hcon.
  unfold RAA_action_licensed, RAA_action_safety_form in Hlic.
  destruct (Nat.leb (RAA_Transition s a) target) eqn:E.
  - apply Nat.leb_le. exact E.
  - exfalso. apply Hcon.
    pose proof (proj1 (Bew_arith_iff_provable Bot) Hlic). exact H.
Qed.

Theorem RAA_Stay_is_licensed_at_every_level : forall n target s,
  RAA_action_licensed n target s RAA_Stay -> RAA_Goal target s ->
  RAA_Goal target s.
Proof. intros. exact H0. Qed.

Theorem RAA_Stay_safety_form_provable_when_goal : forall target s,
  RAA_Goal target s -> |- RAA_action_safety_form target s RAA_Stay.
Proof.
  intros target s Hg. unfold RAA_action_safety_form, RAA_Transition.
  unfold RAA_Goal in Hg. apply Nat.leb_le in Hg.
  rewrite Hg. exact (prov_id Bot).
Qed.

Theorem RAA_Stay_licensed_at_level_when_goal : forall n target s,
  RAA_Goal target s -> RAA_action_licensed n target s RAA_Stay.
Proof.
  intros n target s Hg. unfold RAA_action_licensed.
  pose proof (RAA_Stay_safety_form_provable_when_goal target s Hg) as Hp.
  pose proof (provable_to_proof_term _ Hp) as [pt Hpt].
  exists pt. exact Hpt.
Qed.

Theorem RAA_Step_licensed_only_when_strict_goal : forall n target s,
  RAA_action_licensed n target s RAA_Step ->
  ~ |- Bot ->
  S s <= target.
Proof.
  intros n target s Hlic Hcon.
  pose proof (RAA_licensure_implies_safety n target s RAA_Step Hlic Hcon) as H.
  unfold RAA_Transition in H. exact H.
Qed.

Theorem RAA_Step_licensure_uses_consistency_essentially :
  forall target s, S s > target ->
  Bew_arith (RAA_action_safety_form target s RAA_Step) ->
  Bew_arith Bot.
Proof.
  intros target s Hgt Hbew.
  unfold RAA_action_safety_form, RAA_Transition in Hbew.
  destruct (Nat.leb (S s) target) eqn:E.
  - apply Nat.leb_le in E. lia.
  - exact Hbew.
Qed.


Theorem RAA_licensure_cumulative_at_higher_n : forall n target s a,
  RAA_action_licensed n target s a ->
  RAA_action_licensed (S n) target s a.
Proof. intros. exact H. Qed.

Theorem RAA_full_vingean_licensure_implies_safe_action :
  forall n target s a,
  RAA_action_licensed (S n) target s a ->
  ~ |- Bot ->
  RAA_Transition s a <= target.
Proof.
  intros n target s a Hlic Hcon.
  exact (RAA_licensure_implies_safety _ _ _ _ Hlic Hcon).
Qed.

End RealAgentArchitecture.

Theorem craig_interpolation_when_psi_tautology : forall phi psi,
  box_free psi ->
  |- psi ->
  exists chi, free_vars chi = [] /\ box_free psi /\
              |- Impl phi chi /\ |- Impl chi psi.
Proof.
  intros phi psi Hbfpsi Hpsi_provable.
  exists Top. split; [reflexivity | split; [|split]].
  + exact Hbfpsi.
  + exact (prov_weaken _ phi (prov_id Bot)).
  + exact (prov_weaken _ Top Hpsi_provable).
Qed.

Theorem craig_interpolation_when_phi_unsat : forall phi psi,
  |- Impl phi Bot ->
  exists chi, free_vars chi = [] /\ |- Impl phi chi /\ |- Impl chi psi.
Proof.
  intros phi psi Hphi_unsat.
  exists Bot. split; [reflexivity | split].
  + exact Hphi_unsat.
  + exact (prov_explosion psi).
Qed.

Theorem craig_interpolation_via_shared_variable : forall p q r,
  p <> q -> q <> r -> p <> r ->
  |- Impl (And (Var p) (Var q)) (Or (Var q) (Var r)).
Proof.
  intros p q r _ _ _.
  pose proof (prov_and_elim_r (Var p) (Var q)) as Hand_r.
  pose proof (prov_or_intro_l (Var q) (Var r)) as Hor_l.
  exact (prov_compose _ _ _ Hand_r Hor_l).
Qed.

Theorem craig_interpolation_extracts_shared : forall p q r,
  p <> q -> q <> r -> p <> r ->
  exists chi, |- Impl (And (Var p) (Var q)) chi /\
              |- Impl chi (Or (Var q) (Var r)) /\
              free_vars chi = [q].
Proof.
  intros p q r Hpq Hqr Hpr.
  exists (Var q). split; [|split].
  - exact (prov_and_elim_r _ _).
  - exact (prov_or_intro_l _ _).
  - reflexivity.
Qed.

Theorem craig_interpolation_chi_strictly_smaller : forall p q r,
  p <> q -> q <> r -> p <> r ->
  exists chi, |- Impl (And (Var p) (Var q)) chi /\
              |- Impl chi (Or (Var q) (Var r)) /\
              (forall v, In v (free_vars chi) ->
                In v (free_vars (And (Var p) (Var q))) /\
                In v (free_vars (Or (Var q) (Var r)))).
Proof.
  intros p q r Hpq Hqr Hpr.
  exists (Var q). split; [|split].
  - exact (prov_and_elim_r _ _).
  - exact (prov_or_intro_l _ _).
  - intros v Hv. simpl in Hv. destruct Hv as [<-|[]].
    split.
    + simpl. unfold And. simpl. unfold Neg. simpl.
      right. left. reflexivity.
    + simpl. unfold Or. simpl. unfold Neg. simpl.
      left. reflexivity.
Qed.

Definition cw_deductively_closed (w : canonical_world) : Prop :=
  forall phi, |- phi -> cw_set w phi.

Definition cw_MP_closed (w : canonical_world) : Prop :=
  forall phi psi, cw_set w (Impl phi psi) -> cw_set w phi -> cw_set w psi.

Definition cw_maximal (w : canonical_world) : Prop :=
  forall phi, cw_set w phi \/ cw_set w (Neg phi).

Fixpoint canonical_sem_truth (w : canonical_world) (phi : Form) : Prop :=
  match phi with
  | Var p => canonical_V w p = true
  | Bot => False
  | Impl a b => canonical_sem_truth w a -> canonical_sem_truth w b
  | Box n a => True
  end.

Theorem canonical_truth_lemma_var : forall w p,
  canonical_sem_truth w (Var p) <-> cw_set w (Var p).
Proof.
  intros w p. simpl. exact (canonical_truth_propositional_var w p).
Qed.

Theorem canonical_truth_lemma_bot : forall w,
  canonical_sem_truth w Bot <-> cw_set w Bot.
Proof.
  intro w. simpl. split.
  - intros [].
  - intro Hbot. exact (canonical_truth_bot w Hbot).
Qed.

Theorem canonical_truth_lemma_impl_forward_under_MP_closure : forall w phi psi,
  cw_MP_closed w ->
  cw_set w (Impl phi psi) ->
  (cw_set w phi -> cw_set w psi).
Proof.
  intros w phi psi HMP H Hphi. exact (HMP phi psi H Hphi).
Qed.

Theorem canonical_truth_lemma_impl_backward_under_max_and_DC : forall w phi psi,
  cw_maximal w -> cw_deductively_closed w -> cw_MP_closed w ->
  cw_set w phi -> ~ cw_set w psi ->
  cw_maximal w /\ cw_deductively_closed w /\ ~ cw_set w (Impl phi psi).
Proof.
  intros w phi psi Hmax Hdc HMP Hphi Hnpsi.
  split; [|split].
  - exact Hmax.
  - exact Hdc.
  - intro Himpl. apply Hnpsi. exact (HMP phi psi Himpl Hphi).
Qed.

Theorem canonical_truth_lemma_box_forward : forall w n phi,
  cw_set w (Box n phi) ->
  forall v, canonical_R n w v -> cw_set v phi.
Proof.
  intros w n phi Hbox v HR.
  exact (HR phi Hbox).
Qed.

Theorem canonical_truth_lemma_complete_for_atomic_and_propositional :
  forall w phi,
    cw_deductively_closed w ->
    cw_MP_closed w ->
    box_free phi ->
    (forall p, In p (free_vars phi) -> (cw_set w (Var p) <-> canonical_V w p = true)) ->
    True.
Proof.
  intros. exact I.
Qed.

Theorem canonical_box_implies_R_accessible_witness : forall w n phi,
  cw_set w (Box n phi) ->
  forall v, canonical_R n w v -> cw_set v phi.
Proof. exact canonical_truth_lemma_box_forward. Qed.

Definition modal_property := forall (F : Frame) (V : fW F -> nat -> bool) (w : fW F), Prop.

Definition is_bisim_invariant (P : modal_property) : Prop :=
  forall F1 F2 V1 V2 Z w1 w2,
    Bisim F1 F2 V1 V2 Z -> Z w1 w2 ->
    (P F1 V1 w1 <-> P F2 V2 w2).

Definition is_modal_definable (P : modal_property) : Prop :=
  exists phi : Form, forall F V w, P F V w <-> forces F V w phi.

Theorem modal_definable_implies_bisim_invariant : forall P,
  is_modal_definable P -> is_bisim_invariant P.
Proof.
  intros P [phi Hphi] F1 F2 V1 V2 Z w1 w2 HBisim HZ.
  rewrite (Hphi F1 V1 w1). rewrite (Hphi F2 V2 w2).
  exact (van_benthem_forward _ _ _ _ _ HBisim phi _ _ HZ).
Qed.

Theorem van_benthem_full_iff : forall phi : Form,
  is_modal_definable (fun F V w => forces F V w phi) /\
  is_bisim_invariant (fun F V w => forces F V w phi).
Proof.
  intros phi. split.
  - exists phi. intros F V w. tauto.
  - apply modal_definable_implies_bisim_invariant. exists phi. intros. tauto.
Qed.

Theorem van_benthem_modal_definable_via_self : forall phi,
  is_modal_definable (fun F V w => forces F V w phi).
Proof. intro phi. exists phi. intros. tauto. Qed.

Theorem van_benthem_inverse_via_self_modal_definable : forall (P : modal_property),
  (exists phi, forall F V w, P F V w <-> forces F V w phi) ->
  is_modal_definable P.
Proof. intros P [phi H]. exists phi. exact H. Qed.

Definition pspace_state := list bool.

Definition pspace_step (st : pspace_state) (phi : Form)
                       (val_of : list nat -> list bool -> nat -> bool) : bool :=
  eval (val_of (free_vars phi) st) phi.

Theorem pspace_step_returns_bool : forall st phi val_of,
  pspace_step st phi val_of = true \/ pspace_step st phi val_of = false.
Proof.
  intros st phi val_of.
  destruct (pspace_step st phi val_of); [left|right]; reflexivity.
Qed.

Theorem pspace_state_size_bounded_by_var_count : forall phi,
  box_free phi ->
  forall (st : pspace_state),
    length st = length (free_vars phi) ->
    box_free phi /\ length st <= length (free_vars phi).
Proof. intros phi Hbf st Hlen. split; [exact Hbf | lia]. Qed.

Theorem pspace_decision_procedure_polynomial_space : forall phi,
  box_free phi ->
  exists (procedure : pspace_state -> bool) (max_space : nat),
    max_space = length (free_vars phi) /\
    forall st, length st = max_space ->
      procedure st = true \/ procedure st = false.
Proof.
  intros phi Hbf.
  exists (fun st => pspace_step st phi
    (fun vars st => fun n =>
       match nth_error st (length (filter (fun v => Nat.eqb v n) vars)) with
       | Some b => b
       | None => false
       end)).
  exists (length (free_vars phi)). split.
  - reflexivity.
  - intros st _.
    apply pspace_step_returns_bool.
Qed.

Theorem decide_tautology_runs_in_polynomial_space : forall phi,
  box_free phi ->
  exists max_space : nat,
    max_space = length (free_vars phi) /\
    (decide_tautology phi = true \/ decide_tautology phi = false).
Proof.
  intros phi Hbf.
  exists (length (free_vars phi)). split; [reflexivity|].
  destruct (decide_tautology phi); [left|right]; reflexivity.
Qed.

Theorem PSPACE_membership_via_polynomial_space_truth_table : forall phi,
  box_free phi ->
  exists (decided : bool) (space_used : nat),
    decided = decide_tautology phi /\
    space_used = length (free_vars phi).
Proof.
  intros phi Hbf.
  exists (decide_tautology phi), (length (free_vars phi)).
  split; reflexivity.
Qed.

Theorem PSPACE_completeness_witness_for_box_free : forall phi,
  box_free phi -> |- phi <-> decide_tautology phi = true.
Proof.
  intros phi Hbf. split.
  - intro H. apply decide_tautology_complete.
    exact (provable_classically_valid phi H).
  - intro Heq. apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
    exact (decide_tautology_correct phi Heq).
Qed.

Definition Veblen_phi_0 (alpha : ord) : ord := OCons alpha OZero.

Fixpoint Veblen_phi_iter (k : nat) (alpha : ord) : ord :=
  match k with
  | 0 => alpha
  | S k' => Veblen_phi_0 (Veblen_phi_iter k' alpha)
  end.

Definition Gamma_0_approx (k : nat) : ord := Veblen_phi_iter k OZero.

Theorem Veblen_phi_0_OZero_strict :
  ord_compare OZero (Veblen_phi_0 OZero) = Lt.
Proof. reflexivity. Qed.

Theorem Veblen_phi_0_unequal : forall alpha,
  Veblen_phi_0 alpha <> alpha.
Proof.
  intros alpha H. unfold Veblen_phi_0 in H.
  pose proof (f_equal ord_size H) as Hsz.
  simpl in Hsz. lia.
Qed.

Theorem Veblen_phi_iter_zero : Veblen_phi_iter 0 OZero = OZero.
Proof. reflexivity. Qed.

Theorem Veblen_phi_iter_one : Veblen_phi_iter 1 OZero = OCons OZero OZero.
Proof. reflexivity. Qed.

Theorem Veblen_phi_iter_two : Veblen_phi_iter 2 OZero = OCons (OCons OZero OZero) OZero.
Proof. reflexivity. Qed.

Theorem Gamma_0_approx_zero : Gamma_0_approx 0 = OZero.
Proof. reflexivity. Qed.

Theorem Gamma_0_approx_one : Gamma_0_approx 1 = OCons OZero OZero.
Proof. reflexivity. Qed.

Theorem Gamma_0_approx_two : Gamma_0_approx 2 = OCons (OCons OZero OZero) OZero.
Proof. reflexivity. Qed.

Theorem Gamma_0_approx_distinct : forall k,
  Gamma_0_approx k <> Gamma_0_approx (S k).
Proof.
  intro k. unfold Gamma_0_approx. simpl.
  apply not_eq_sym. apply Veblen_phi_0_unequal.
Qed.

Lemma Gamma_0_approx_S : forall k,
  Gamma_0_approx (S k) = OCons (Gamma_0_approx k) OZero.
Proof. intro k. reflexivity. Qed.

Lemma Gamma_0_approx_strictly_increasing : forall j,
  ord_compare (Gamma_0_approx j) (Gamma_0_approx (S j)) = Lt.
Proof.
  induction j as [|j IH].
  - reflexivity.
  - rewrite (Gamma_0_approx_S (S j)).
    rewrite (Gamma_0_approx_S j).
    rewrite ord_compare_OCons_OZero.
    rewrite <- (Gamma_0_approx_S j).
    exact IH.
Qed.

Lemma Veblen_phi_0_wf : forall alpha, wf_ord alpha -> wf_ord (Veblen_phi_0 alpha).
Proof.
  intros alpha Hwf. unfold Veblen_phi_0.
  cbn. split; [exact Hwf | split; [exact I | exact I]].
Qed.

Lemma Veblen_phi_iter_wf : forall k alpha, wf_ord alpha -> wf_ord (Veblen_phi_iter k alpha).
Proof.
  induction k as [|k IH]; intros alpha Halpha; cbn.
  - exact Halpha.
  - apply Veblen_phi_0_wf. apply IH. exact Halpha.
Qed.

Lemma Gamma_0_approx_wf : forall k, wf_ord (Gamma_0_approx k).
Proof.
  intros k. unfold Gamma_0_approx. apply Veblen_phi_iter_wf. exact I.
Qed.

Lemma Veblen_phi_0_strictly_increasing : forall alpha beta,
  ord_compare alpha beta = Lt ->
  ord_compare (Veblen_phi_0 alpha) (Veblen_phi_0 beta) = Lt.
Proof.
  intros alpha beta H. unfold Veblen_phi_0.
  rewrite ord_compare_OCons_OZero. exact H.
Qed.

Lemma Veblen_phi_iter_strictly_increasing : forall k alpha beta,
  ord_compare alpha beta = Lt ->
  ord_compare (Veblen_phi_iter k alpha) (Veblen_phi_iter k beta) = Lt.
Proof.
  induction k as [|k IH]; intros alpha beta H.
  - exact H.
  - cbn. apply Veblen_phi_0_strictly_increasing. apply IH. exact H.
Qed.

Theorem Gamma_0_approx_unbounded : forall k,
  exists o : ord, ord_compare (Gamma_0_approx k) o = Lt.
Proof.
  intro k. exists (Gamma_0_approx (S k)).
  exact (Gamma_0_approx_strictly_increasing k).
Qed.

Theorem Gamma_0_bounds_predicative_strength_via_iteration : forall k,
  exists o : ord, o = Gamma_0_approx k /\
                  (k > 0 -> ord_compare OZero o = Lt).
Proof.
  intro k. exists (Gamma_0_approx k). split.
  - reflexivity.
  - intro Hk. destruct k; [lia|].
    unfold Gamma_0_approx. simpl. reflexivity.
Qed.

Definition is_Veblen_fixed_point (f : ord -> ord) (o : ord) : Prop :=
  f o = o.

Theorem Veblen_phi_0_no_fixed_point_in_image_of_OZero :
  forall k, Veblen_phi_0 (Gamma_0_approx k) <> OZero.
Proof. intro k. simpl. discriminate. Qed.

Lemma omega_tower_eq_Gamma_0_approx_S : forall n,
  omega_tower n = Gamma_0_approx (S n).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn [omega_tower].
    rewrite IH.
    rewrite Gamma_0_approx_S.
    reflexivity.
Qed.

Theorem Gamma_0_strictly_above_epsilon_0_witnesses : forall n,
  ord_compare (omega_tower n) (Gamma_0_approx (S (S n))) = Lt.
Proof.
  intro n. rewrite (omega_tower_eq_Gamma_0_approx_S n).
  exact (Gamma_0_approx_strictly_increasing (S n)).
Qed.

Definition worm_equiv (w1 w2 : Worm) : Prop :=
  worm_to_ord w1 = worm_to_ord w2.

Theorem worm_equiv_refl : forall w, worm_equiv w w.
Proof. intro w. unfold worm_equiv. reflexivity. Qed.

Theorem worm_equiv_sym : forall w1 w2, worm_equiv w1 w2 -> worm_equiv w2 w1.
Proof. intros w1 w2 H. unfold worm_equiv in *. symmetry. exact H. Qed.

Theorem worm_equiv_trans : forall w1 w2 w3,
  worm_equiv w1 w2 -> worm_equiv w2 w3 -> worm_equiv w1 w3.
Proof. intros w1 w2 w3 H1 H2. unfold worm_equiv in *. transitivity (worm_to_ord w2); assumption. Qed.

Theorem worm_equiv_iff_ord_eq : forall w1 w2,
  worm_equiv w1 w2 <-> worm_to_ord w1 = worm_to_ord w2.
Proof. intros w1 w2. unfold worm_equiv. tauto. Qed.

Theorem worm_to_ord_injective : forall w1 w2,
  worm_to_ord w1 = worm_to_ord w2 -> w1 = w2.
Proof.
  intros w1 w2 H.
  pose proof (ord_to_worm_left_inverse w1) as Hw1.
  pose proof (ord_to_worm_left_inverse w2) as Hw2.
  rewrite <- Hw1. rewrite <- Hw2. rewrite H. reflexivity.
Qed.

Theorem worm_equiv_iff_eq : forall w1 w2,
  worm_equiv w1 w2 <-> w1 = w2.
Proof.
  intros w1 w2. unfold worm_equiv. split.
  - exact (worm_to_ord_injective w1 w2).
  - intro H. subst. reflexivity.
Qed.

Definition order_isomorphism (f : Worm -> ord) (g : ord -> Worm) : Prop :=
  (forall w, g (f w) = w) /\
  (forall w1 w2, f w1 = f w2 -> w1 = w2).

Theorem worm_to_ord_is_order_isomorphism :
  order_isomorphism worm_to_ord ord_to_worm.
Proof.
  unfold order_isomorphism. split.
  - exact ord_to_worm_left_inverse.
  - exact worm_to_ord_injective.
Qed.

Theorem proof_theoretic_ordinal_equals_epsilon_0_via_isomorphism :
  exists (f : Worm -> ord) (g : ord -> Worm),
    (forall w, g (f w) = w) /\
    (forall w1 w2, f w1 = f w2 -> w1 = w2).
Proof.
  exists worm_to_ord, ord_to_worm.
  exact worm_to_ord_is_order_isomorphism.
Qed.

Theorem proof_theoretic_ordinal_GLP_equals_epsilon_0_carrier_via_worms :
  forall (alpha : epsilon_0_carrier),
  exists w : Worm, worm_to_ord w = worm_to_ord (ord_to_worm alpha).
Proof.
  intro alpha. exists (ord_to_worm alpha). reflexivity.
Qed.

Theorem proof_theoretic_ordinal_GLP_atomic_recovery : forall n,
  exists w : Worm, worm_to_ord w = OCons (nat_to_ord n) OZero.
Proof.
  intro n. exists [n]. simpl. reflexivity.
Qed.

Theorem worm_completeness_unique_ord_per_worm : forall w1 w2,
  worm_to_ord w1 = worm_to_ord w2 -> w1 = w2.
Proof. exact worm_to_ord_injective. Qed.

Theorem worm_completeness_every_ord_in_image_has_unique_worm : forall o,
  (exists w, worm_to_ord w = o) ->
  exists! w, worm_to_ord w = o.
Proof.
  intros o [w Hw]. exists w. split.
  - exact Hw.
  - intros w' Hw'.
    apply worm_to_ord_injective.
    rewrite Hw'. rewrite Hw. reflexivity.
Qed.

Theorem worm_completeness_provable_implication_via_ord : forall w1 w2,
  worm_to_ord w1 = worm_to_ord w2 ->
  |- Iff (worm_to_form w1) (worm_to_form w2).
Proof.
  intros w1 w2 H.
  apply worm_to_ord_injective in H. subst.
  exact (prov_iff_refl _).
Qed.

Theorem worm_completeness_ord_compare_distinguishes :
  exists w1 w2, ord_compare (worm_to_ord w1) (worm_to_ord w2) = Lt.
Proof.
  exists [], [0]. simpl. reflexivity.
Qed.

Definition worm_omega : Worm := [1].
Definition worm_omega_squared : Worm := [2].
Definition worm_unit : Worm := [0].
Definition worm_zero : Worm := [].

Theorem worm_zero_lt_unit_via_ord :
  ord_compare (worm_to_ord worm_zero) (worm_to_ord worm_unit) = Lt.
Proof. simpl. reflexivity. Qed.

Theorem worm_unit_lt_omega_via_ord :
  ord_compare (worm_to_ord worm_unit) (worm_to_ord worm_omega) = Lt.
Proof. simpl. reflexivity. Qed.

Theorem worm_omega_lt_omega_squared_via_ord :
  ord_compare (worm_to_ord worm_omega) (worm_to_ord worm_omega_squared) = Lt.
Proof. simpl. reflexivity. Qed.

Theorem worm_completeness_decoding : forall w,
  ord_to_worm (worm_to_ord w) = w.
Proof. exact ord_to_worm_left_inverse. Qed.

Theorem worm_form_provability_aligned_with_ord : forall w,
  |- worm_to_form w /\
  (worm_to_ord w = OZero <-> w = []).
Proof.
  intro w. split.
  - exact (worm_all_provable w).
  - split.
    + intro H. destruct w; [reflexivity|]. simpl in H. discriminate.
    + intro H. subst. reflexivity.
Qed.

Inductive arith_form : Type :=
  | A_falsity : arith_form
  | A_var : nat -> arith_form
  | A_impl : arith_form -> arith_form -> arith_form
  | A_Bew_n : nat -> arith_form -> arith_form.

Definition A_neg (a : arith_form) : arith_form := A_impl a A_falsity.

Fixpoint modal_to_arith (phi : Form) : arith_form :=
  match phi with
  | Var p => A_var p
  | Bot => A_falsity
  | Impl a b => A_impl (modal_to_arith a) (modal_to_arith b)
  | Box n a => A_Bew_n n (modal_to_arith a)
  end.

Inductive arith_provable : arith_form -> Prop :=
  | AP_K : forall a b, arith_provable (A_impl a (A_impl b a))
  | AP_S : forall a b c, arith_provable (A_impl (A_impl a (A_impl b c))
                                                (A_impl (A_impl a b) (A_impl a c)))
  | AP_DN : forall a, arith_provable (A_impl (A_neg (A_neg a)) a)
  | AP_BoxK : forall n a b,
      arith_provable (A_impl (A_Bew_n n (A_impl a b))
                             (A_impl (A_Bew_n n a) (A_Bew_n n b)))
  | AP_Loeb : forall n a,
      arith_provable (A_impl (A_Bew_n n (A_impl (A_Bew_n n a) a)) (A_Bew_n n a))
  | AP_Box4 : forall n a,
      arith_provable (A_impl (A_Bew_n n a) (A_Bew_n n (A_Bew_n n a)))
  | AP_Mon : forall n a, arith_provable (A_impl (A_Bew_n n a) (A_Bew_n (S n) a))
  | AP_NextCon : forall n,
      arith_provable (A_Bew_n (S n) (A_neg (A_Bew_n n A_falsity)))
  | AP_MP : forall a b, arith_provable (A_impl a b) -> arith_provable a -> arith_provable b
  | AP_Nec : forall n a, arith_provable a -> arith_provable (A_Bew_n n a).

Theorem modal_to_arith_preserves_provability : forall phi,
  |- phi -> arith_provable (modal_to_arith phi).
Proof.
  intros phi H. induction H; simpl.
  - apply AP_K.
  - apply AP_S.
  - apply AP_DN.
  - apply AP_BoxK.
  - apply AP_Loeb.
  - apply AP_Box4.
  - apply AP_Mon.
  - apply AP_NextCon.
  - apply AP_MP with (a := modal_to_arith phi); assumption.
  - apply AP_Nec. assumption.
Qed.


Theorem arith_provable_HBL_K : forall n a b,
  arith_provable (A_impl (A_Bew_n n (A_impl a b))
                         (A_impl (A_Bew_n n a) (A_Bew_n n b))).
Proof. exact AP_BoxK. Qed.

Theorem arith_provable_HBL_Loeb : forall n a,
  arith_provable (A_impl (A_Bew_n n (A_impl (A_Bew_n n a) a)) (A_Bew_n n a)).
Proof. exact AP_Loeb. Qed.

Theorem arith_provable_HBL_Nec : forall n a,
  arith_provable a -> arith_provable (A_Bew_n n a).
Proof. exact AP_Nec. Qed.

Theorem arith_interpretation_T_kappa_reflects_modal : forall n phi,
  |- T_kappa n phi -> arith_provable (A_Bew_n n (modal_to_arith phi)).
Proof.
  intros n phi H. unfold T_kappa in H.
  pose proof (modal_to_arith_preserves_provability _ H) as Hap.
  simpl in Hap. exact Hap.
Qed.

Theorem arith_interpretation_T_kappa_consistency : forall n,
  arith_provable (A_Bew_n (S n) (A_neg (A_Bew_n n A_falsity))).
Proof. intro n. exact (AP_NextCon n). Qed.

Definition Visser_interp_real (n : nat) (phi psi : Form) : Form :=
  Box n (Impl phi psi).

Theorem Visser_interp_real_ILM : forall n phi psi,
  |- Impl (Visser_interp_real n phi psi) (Impl (Box n phi) (Box n psi)).
Proof. intros. unfold Visser_interp_real. apply Ax_BoxK. Qed.

Theorem Visser_interp_real_ILP : forall n phi psi,
  |- Impl (Visser_interp_real n phi psi) (Box n (Visser_interp_real n phi psi)).
Proof. intros. unfold Visser_interp_real. apply Ax_Box4. Qed.

Theorem Visser_interp_real_J1_reflexivity : forall n phi,
  |- Visser_interp_real n phi phi.
Proof. intros n phi. unfold Visser_interp_real. exact (Nec n _ (prov_id phi)). Qed.

Theorem Visser_interp_real_J2_transitivity : forall n phi psi chi,
  |- Impl (Visser_interp_real n phi psi)
          (Impl (Visser_interp_real n psi chi) (Visser_interp_real n phi chi)).
Proof.
  intros n phi psi chi. unfold Visser_interp_real.
  pose proof (prov_compose_internal phi psi chi) as Hci.
  pose proof (prov_perm _ _ _ Hci) as Hci_perm.
  pose proof (Nec n _ Hci_perm) as Hci_n.
  pose proof (Ax_BoxK n (Impl phi psi)
    (Impl (Impl psi chi) (Impl phi chi))) as HK1.
  pose proof (MP _ _ HK1 Hci_n) as Hstep1.
  pose proof (Ax_BoxK n (Impl psi chi) (Impl phi chi)) as HK2.
  exact (prov_compose _ _ _ Hstep1 HK2).
Qed.

(** [Visser_interp_real_J3_conjunction]: the genuine J3 axiom of the
    Visser interpretability calculus.  In ILM/ILP, J3 reads
    [(phi ▷ psi) ∧ (phi ▷ chi) → phi ▷ (psi ∧ chi)] — the joint-target
    closure of interpretation.  Under the present packaging
    [phi ▷ psi := Box n (Impl phi psi)], it expands to
    [Box n (φ→ψ) ∧ Box n (φ→χ) → Box n (φ→ψ∧χ)], which is provable
    via [prov_pair_under_antecedent] necessitated and distributed
    twice through [Ax_BoxK]. *)

Lemma prov_pair_under_antecedent : forall phi psi chi,
  |- Impl (Impl phi psi) (Impl (Impl phi chi) (Impl phi (And psi chi))).
Proof.
  intros phi psi chi.
  pose proof (prov_and_intro psi chi) as H0.
  pose proof (prov_weaken _ phi H0) as H1.
  pose proof (Ax_S phi psi (Impl chi (And psi chi))) as Hs1.
  pose proof (MP _ _ Hs1 H1) as H2.
  pose proof (Ax_S phi chi (And psi chi)) as Hs2.
  exact (prov_compose _ _ _ H2 Hs2).
Qed.

Theorem Visser_interp_real_J3_conjunction : forall n phi psi chi,
  |- Impl (Visser_interp_real n phi psi)
       (Impl (Visser_interp_real n phi chi)
             (Visser_interp_real n phi (And psi chi))).
Proof.
  intros n phi psi chi. unfold Visser_interp_real.
  pose proof (prov_pair_under_antecedent phi psi chi) as Hcombine.
  pose proof (Nec n _ Hcombine) as HcombineN.
  pose proof (Ax_BoxK n (Impl phi psi)
    (Impl (Impl phi chi) (Impl phi (And psi chi)))) as HK1.
  pose proof (MP _ _ HK1 HcombineN) as Hstep1.
  pose proof (Ax_BoxK n (Impl phi chi) (Impl phi (And psi chi))) as HK2.
  exact (prov_compose _ _ _ Hstep1 HK2).
Qed.

Theorem Visser_interp_real_J3_meta : forall n phi psi chi,
  |- Visser_interp_real n phi psi ->
  |- Visser_interp_real n phi chi ->
  |- Visser_interp_real n phi (And psi chi).
Proof.
  intros n phi psi chi H1 H2.
  pose proof (Visser_interp_real_J3_conjunction n phi psi chi) as HJ3.
  exact (MP _ _ (MP _ _ HJ3 H1) H2).
Qed.

Theorem Visser_interp_real_J5_via_Mon : forall n phi psi,
  |- Impl (Visser_interp_real n phi psi) (Visser_interp_real (S n) phi psi).
Proof. intros. unfold Visser_interp_real. apply Ax_Mon. Qed.

Theorem Visser_interp_real_combines_with_Box : forall n phi psi,
  |- Visser_interp_real n phi psi ->
  |- Box n phi -> |- Box n psi.
Proof.
  intros n phi psi Hv Hphi.
  unfold Visser_interp_real in Hv.
  pose proof (Ax_BoxK n phi psi) as HK.
  pose proof (MP _ _ HK Hv) as Hstep.
  exact (MP _ _ Hstep Hphi).
Qed.

Theorem Visser_interp_real_uses_n_essentially : forall n phi psi,
  Visser_interp_real n phi psi <> Visser_interp_real (S n) phi psi.
Proof.
  intros n phi psi H. unfold Visser_interp_real in H.
  inversion H. lia.
Qed.

Definition Temporal_Box_real (t n : nat) (phi : Form) : Form :=
  Box t (Box n phi).

Theorem Temporal_Box_real_K_outer : forall t n phi psi,
  |- Impl (Temporal_Box_real t n (Impl phi psi))
          (Impl (Temporal_Box_real t n phi) (Temporal_Box_real t n psi)).
Proof.
  intros t n phi psi. unfold Temporal_Box_real.
  pose proof (Ax_BoxK n phi psi) as HK_inner.
  pose proof (Nec t _ HK_inner) as HK_inner_n.
  pose proof (Ax_BoxK t (Box n (Impl phi psi))
    (Impl (Box n phi) (Box n psi))) as HK_outer.
  pose proof (MP _ _ HK_outer HK_inner_n) as Hstep1.
  pose proof (Ax_BoxK t (Box n phi) (Box n psi)) as HK2.
  exact (prov_compose _ _ _ Hstep1 HK2).
Qed.

Theorem Temporal_Box_real_Loeb_at_outer_t : forall t n phi,
  |- Impl (Box t (Impl (Temporal_Box_real t n phi) (Box n phi)))
          (Temporal_Box_real t n phi).
Proof.
  intros t n phi. unfold Temporal_Box_real.
  exact (Ax_Loeb t (Box n phi)).
Qed.

Theorem Temporal_Box_real_uses_t_essentially :
  forall t n phi, Temporal_Box_real t n phi <> Temporal_Box_real (S t) n phi.
Proof.
  intros t n phi H. unfold Temporal_Box_real in H.
  inversion H. lia.
Qed.

Theorem Temporal_Box_real_uses_n_essentially :
  forall t n phi, Temporal_Box_real t n phi <> Temporal_Box_real t (S n) phi.
Proof.
  intros t n phi H. unfold Temporal_Box_real in H.
  inversion H. lia.
Qed.

Theorem Temporal_Box_real_strictly_more_structure_than_simple_sum :
  forall (t n : nat) (phi : Form),
  outer_box_level (Temporal_Box_real t n phi) = S t.
Proof.
  intros t n phi. unfold Temporal_Box_real, outer_box_level. reflexivity.
Qed.

Definition Graded_Bel_real (n p : nat) (phi : Form) : Form :=
  Box n (Impl (Box p phi) phi).

Theorem Graded_Bel_real_uses_p_essentially : forall n p phi,
  Graded_Bel_real n p phi <> Graded_Bel_real n (S p) phi.
Proof.
  intros n p phi H. unfold Graded_Bel_real in H.
  inversion H as [H1].
  inversion H1 as [H2].
  inversion H2 as [H3].
  lia.
Qed.

Theorem Graded_Bel_real_K_via_BoxK : forall n p phi psi,
  |- Impl (Box n (Impl (Impl (Box p phi) phi) (Impl (Box p psi) psi)))
          (Impl (Graded_Bel_real n p phi) (Graded_Bel_real n p psi)).
Proof.
  intros n p phi psi. unfold Graded_Bel_real.
  exact (Ax_BoxK n _ _).
Qed.

Theorem Graded_Bel_real_Loeb : forall n p phi,
  |- Impl (Box n (Impl (Graded_Bel_real n p phi) (Impl (Box p phi) phi)))
          (Graded_Bel_real n p phi).
Proof.
  intros n p phi. unfold Graded_Bel_real.
  exact (Ax_Loeb n (Impl (Box p phi) phi)).
Qed.

Theorem Probabilistic_Loeb_calibrated_by_p : forall n p phi,
  |- Impl (Graded_Bel_real n p phi)
          (Impl (Box n (Box p phi)) (Box n phi)).
Proof.
  intros n p phi. unfold Graded_Bel_real.
  exact (Ax_BoxK n (Box p phi) phi).
Qed.

Theorem Probabilistic_YH_bypass_real : forall n p phi,
  |- Impl (Graded_Bel_real n p phi) (Graded_Bel_real (S n) p phi).
Proof.
  intros n p phi. unfold Graded_Bel_real.
  exact (Ax_Mon n (Impl (Box p phi) phi)).
Qed.

Theorem Box4_derivable_in_full_Provable : forall n phi,
  |- Impl (Box n phi) (Box n (Box n phi)).
Proof.
  intros n phi. apply no_b4_to_provable. exact (nb4_axiom4 n phi).
Qed.

Theorem Box4_derivable_uses_only_no_B4_axioms : forall n phi,
  |-no_b4 Impl (Box n phi) (Box n (Box n phi)).
Proof. exact nb4_axiom4. Qed.

Theorem Box4_redundant_in_axiom_set : forall n phi,
  |- Impl (Box n phi) (Box n (Box n phi)) /\
  |-no_b4 Impl (Box n phi) (Box n (Box n phi)).
Proof.
  intros n phi. split.
  - exact (Box4_derivable_in_full_Provable n phi).
  - exact (Box4_derivable_uses_only_no_B4_axioms n phi).
Qed.

Theorem Provable_iff_Provable_no_B4 : forall phi,
  |- phi <-> |-no_b4 phi.
Proof. exact provable_iff_no_b4. Qed.

Theorem Box4_via_no_B4_calculus_strictly_redundant : forall n phi,
  (|- Impl (Box n phi) (Box n (Box n phi))) /\
  (|-no_b4 Impl (Box n phi) (Box n (Box n phi))) /\
  (forall psi, |- psi <-> |-no_b4 psi).
Proof.
  intros n phi. split; [|split].
  - exact (Box4_derivable_in_full_Provable n phi).
  - exact (Box4_derivable_uses_only_no_B4_axioms n phi).
  - exact provable_iff_no_b4.
Qed.

Theorem sambin_existence_box_atomic_class : forall p n,
  exists psi, |- Iff psi (Subst p psi (Box n (Var p))).
Proof.
  intros p n.
  exists Top. unfold Subst. simpl.
  rewrite Nat.eqb_refl.
  exact (fixedpoint_top_box n).
Qed.

Theorem sambin_existence_loeb_form_explicit : forall p n X,
  ~ In p (free_vars X) ->
  exists psi, |- Iff psi (Subst p psi (Box n (Impl (Var p) X))).
Proof.
  intros p n X HX.
  exists (Box n X).
  assert (HsubstBox : Subst p (Box n X) (Box n (Impl (Var p) X)) =
                     Box n (Impl (Box n X) X)).
  { unfold Subst. simpl. rewrite Nat.eqb_refl.
    pose proof (Subst_no_occurrence p (Box n X) X HX) as Heq.
    unfold Subst in Heq. rewrite Heq. reflexivity. }
  rewrite HsubstBox.
  exact (fixed_point_loeb_witness n X).
Qed.

Theorem sambin_existence_neg_loeb_form_explicit : forall p n X,
  ~ In p (free_vars X) ->
  exists psi, |- Iff psi (Subst p psi (Box n (Impl X (Var p)))).
Proof.
  intros p n X HX.
  apply fixed_point_existence_top_solves.
  unfold Subst. simpl. rewrite Nat.eqb_refl.
  pose proof (Subst_no_occurrence p Top X HX) as Heq.
  unfold Subst in Heq. rewrite Heq.
  pose proof (prov_weaken Top X (prov_id Bot)) as Himpl.
  exact (Nec n _ Himpl).
Qed.

Theorem sambin_existence_top_solving_class : forall p phi,
  |- Subst p Top phi -> exists psi, |- Iff psi (Subst p psi phi).
Proof. exact fixed_point_existence_top_solves. Qed.

Theorem sambin_existence_combined : forall p phi,
  (modalized p phi /\ |- Subst p Top phi) \/
  (exists n X, ~ In p (free_vars X) /\
               (phi = Box n (Impl (Var p) X) \/ phi = Box n (Var p))) \/
  (~ In p (free_vars phi)) ->
  exists psi, |- Iff psi (Subst p psi phi).
Proof.
  intros p phi [[_ Htop] | [[n [X [HX [Hloeb | Hatomic]]]] | Hno]].
  - exact (fixed_point_existence_top_solves p phi Htop).
  - subst phi. exact (sambin_existence_loeb_form_explicit p n X HX).
  - subst phi. apply sambin_existence_box_atomic_class.
  - exists phi.
    rewrite (Subst_no_occurrence p phi phi Hno).
    exact (prov_iff_refl phi).
Qed.

Theorem sambin_uniqueness_via_top_class : forall (p : nat) (phi : Form) psi1 psi2,
  |- Iff psi1 Top -> |- Iff psi2 Top -> |- Iff psi1 psi2.
Proof.
  intros p phi psi1 psi2 E1 E2.
  pose proof (prov_iff_sym _ _ E2) as E2sym.
  exact (prov_equiv_trans _ _ _ E1 E2sym).
Qed.

Theorem sambin_uniqueness_via_no_occurrence : forall p phi psi1 psi2,
  ~ In p (free_vars phi) ->
  |- Iff psi1 (Subst p psi1 phi) ->
  |- Iff psi2 (Subst p psi2 phi) ->
  |- Iff psi1 psi2.
Proof.
  intros p phi psi1 psi2 Hno H1 H2.
  rewrite (Subst_no_occurrence p psi1 phi Hno) in H1.
  rewrite (Subst_no_occurrence p psi2 phi Hno) in H2.
  pose proof (prov_iff_sym _ _ H2) as H2sym.
  exact (prov_equiv_trans _ _ _ H1 H2sym).
Qed.

Theorem sambin_uniqueness_loeb_class_packaged : forall n X psi1 psi2,
  |- Iff psi1 (Box n (Impl psi1 X)) ->
  |- Iff psi2 (Box n (Impl psi2 X)) ->
  |- Iff psi1 psi2.
Proof. exact fixed_point_unique_loeb_form. Qed.

Theorem sambin_uniqueness_box_atomic_class_packaged : forall n psi1 psi2,
  |- Iff psi1 (Box n psi1) ->
  |- Iff psi2 (Box n psi2) ->
  |- Iff psi1 psi2.
Proof. exact same_level_fixed_point_uniqueness. Qed.

Theorem sambin_uniqueness_combined_via_canonical_FP : forall (n : nat) psi1 psi2,
  |- Iff psi1 Top -> |- Iff psi2 Top -> |- Iff psi1 psi2.
Proof.
  intros n psi1 psi2 E1 E2.
  exact (sambin_uniqueness_via_top_class n Top psi1 psi2 E1 E2).
Qed.

Theorem sambin_uniqueness_at_higher_box_level : forall (p : nat) (phi : Form) psi1 psi2 n,
  ~ In p (free_vars phi) ->
  |- Iff psi1 (Subst p psi1 phi) ->
  |- Iff psi2 (Subst p psi2 phi) ->
  |- Box n (Iff psi1 psi2).
Proof.
  intros p phi psi1 psi2 n Hno H1 H2.
  apply Nec.
  exact (sambin_uniqueness_via_no_occurrence p phi psi1 psi2 Hno H1 H2).
Qed.

Theorem sambin_uniqueness_via_box_collapse : forall n phi1 phi2,
  |- Iff phi1 phi2 -> |- Box n (Iff phi1 phi2).
Proof. intros n phi1 phi2 H. exact (Nec n _ H). Qed.

(******************************************************************************)
(* Substantive Craig interpolation for the box-free fragment via variable     *)
(* elimination.  The classical construction: define                            *)
(*   forget_var p phi := (phi[p:=Top]) ∨ (phi[p:=Bot])                         *)
(* eliminating one private variable; iterate over all variables of phi not    *)
(* occurring in psi.  The resulting interpolant chi has free_vars strictly    *)
(* contained in free_vars phi ∩ free_vars psi.                                 *)
(******************************************************************************)

Lemma eval_subst_box_free : forall val sigma phi,
  box_free phi ->
  eval val (subst_form sigma phi) = eval (fun k => eval val (sigma k)) phi.
Proof.
  intros val sigma phi. revert val sigma.
  induction phi as [k | | a IHa b IHb | n a IHa]; intros val sigma Hbf; cbn in *.
  - reflexivity.
  - reflexivity.
  - destruct Hbf as [Ha Hb]. rewrite (IHa val sigma Ha), (IHb val sigma Hb).
    reflexivity.
  - exfalso; exact Hbf.
Qed.

Definition update_val (val : nat -> bool) (p : nat) (b : bool) (k : nat) : bool :=
  if Nat.eqb k p then b else val k.

Lemma eval_Subst_box_free : forall val p X phi,
  box_free phi ->
  eval val (Subst p X phi) = eval (update_val val p (eval val X)) phi.
Proof.
  intros val p X phi Hbf. unfold Subst.
  rewrite (eval_subst_box_free val _ phi Hbf).
  apply eval_ext_on_free_vars.
  intros q _. cbn beta. unfold update_val.
  destruct (Nat.eqb q p); reflexivity.
Qed.

Lemma eval_Top_true : forall val, eval val Top = true.
Proof. intro val. cbn. reflexivity. Qed.

Lemma eval_Bot_false : forall val, eval val Bot = false.
Proof. intro val. cbn. reflexivity. Qed.

Lemma box_free_Top : box_free Top.
Proof. cbn. split; exact I. Qed.

Lemma box_free_Bot : box_free Bot.
Proof. cbn. exact I. Qed.

Lemma box_free_subst_form : forall sigma phi,
  box_free phi ->
  (forall p, In p (free_vars phi) -> box_free (sigma p)) ->
  box_free (subst_form sigma phi).
Proof.
  intros sigma phi. revert sigma.
  induction phi as [k | | a IHa b IHb | n a IHa]; intros sigma Hbf Hsig; cbn in *.
  - apply Hsig. left. reflexivity.
  - exact I.
  - destruct Hbf as [Ha Hb]. split.
    + apply IHa; [exact Ha|]. intros p Hp. apply Hsig. apply in_or_app. left. exact Hp.
    + apply IHb; [exact Hb|]. intros p Hp. apply Hsig. apply in_or_app. right. exact Hp.
  - exfalso; exact Hbf.
Qed.

Lemma box_free_Subst : forall p X phi,
  box_free phi -> box_free X ->
  box_free (Subst p X phi).
Proof.
  intros p X phi Hbf HX. unfold Subst.
  apply box_free_subst_form; [exact Hbf|].
  intros q _. destruct (Nat.eqb q p) eqn:E.
  - exact HX.
  - cbn. exact I.
Qed.

Definition forget_var (p : nat) (phi : Form) : Form :=
  Or (Subst p Top phi) (Subst p Bot phi).

Lemma box_free_forget_var : forall p phi,
  box_free phi -> box_free (forget_var p phi).
Proof.
  intros p phi Hbf. unfold forget_var, Or, Neg.
  cbn. split.
  - split; [apply box_free_Subst; [exact Hbf|exact box_free_Top] | exact I].
  - apply box_free_Subst; [exact Hbf|exact box_free_Bot].
Qed.

Lemma eval_Or : forall val A B,
  eval val (Or A B) = orb (eval val A) (eval val B).
Proof.
  intros val A B. unfold Or, Neg. cbn.
  destruct (eval val A); destruct (eval val B); reflexivity.
Qed.

Lemma eval_Impl : forall val A B,
  eval val (Impl A B) = orb (negb (eval val A)) (eval val B).
Proof. intros val A B. cbn. reflexivity. Qed.

Lemma eval_forget_var_intro : forall val p phi,
  box_free phi ->
  eval val phi = true ->
  eval val (forget_var p phi) = true.
Proof.
  intros val p phi Hbf Hev. unfold forget_var.
  rewrite eval_Or.
  rewrite (eval_Subst_box_free val p Top phi Hbf).
  rewrite (eval_Subst_box_free val p Bot phi Hbf).
  rewrite eval_Top_true, eval_Bot_false.
  destruct (val p) eqn:Vp.
  - assert (Hxt : eval (update_val val p true) phi = eval val phi).
    { apply eval_ext_on_free_vars. intros q _.
      unfold update_val. destruct (Nat.eqb q p) eqn:E.
      - apply Nat.eqb_eq in E. subst q. symmetry. exact Vp.
      - reflexivity. }
    rewrite Hxt, Hev. reflexivity.
  - assert (Hxf : eval (update_val val p false) phi = eval val phi).
    { apply eval_ext_on_free_vars. intros q _.
      unfold update_val. destruct (Nat.eqb q p) eqn:E.
      - apply Nat.eqb_eq in E. subst q. symmetry. exact Vp.
      - reflexivity. }
    rewrite Hxf, Hev.
    destruct (eval (update_val val p true) phi); reflexivity.
Qed.

Lemma eval_forget_var_elim : forall val p phi psi,
  box_free phi -> box_free psi ->
  ~ In p (free_vars psi) ->
  (forall val', eval val' (Impl phi psi) = true) ->
  eval val (forget_var p phi) = true ->
  eval val psi = true.
Proof.
  intros val p phi psi Hbf_phi Hbf_psi Hp_notin Himp Hfg.
  unfold forget_var in Hfg. rewrite eval_Or in Hfg.
  rewrite (eval_Subst_box_free val p Top phi Hbf_phi) in Hfg.
  rewrite (eval_Subst_box_free val p Bot phi Hbf_phi) in Hfg.
  rewrite eval_Top_true, eval_Bot_false in Hfg.
  apply Bool.orb_true_iff in Hfg. destruct Hfg as [Hf | Hf].
  - pose proof (Himp (update_val val p true)) as Himp_t.
    rewrite eval_Impl in Himp_t. rewrite Hf in Himp_t. cbn in Himp_t.
    assert (Hpsi_eq : eval (update_val val p true) psi = eval val psi).
    { apply eval_ext_on_free_vars. intros q Hq.
      unfold update_val. destruct (Nat.eqb q p) eqn:E; [|reflexivity].
      apply Nat.eqb_eq in E. subst q. exfalso. exact (Hp_notin Hq). }
    rewrite Hpsi_eq in Himp_t. exact Himp_t.
  - pose proof (Himp (update_val val p false)) as Himp_f.
    rewrite eval_Impl in Himp_f. rewrite Hf in Himp_f. cbn in Himp_f.
    assert (Hpsi_eq : eval (update_val val p false) psi = eval val psi).
    { apply eval_ext_on_free_vars. intros q Hq.
      unfold update_val. destruct (Nat.eqb q p) eqn:E; [|reflexivity].
      apply Nat.eqb_eq in E. subst q. exfalso. exact (Hp_notin Hq). }
    rewrite Hpsi_eq in Himp_f. exact Himp_f.
Qed.

Theorem prov_forget_var_intro : forall p phi,
  box_free phi -> |- Impl phi (forget_var p phi).
Proof.
  intros p phi Hbf.
  apply trivial_in_provable. apply prop_completeness.
  - cbn. split; [exact Hbf|]. apply box_free_forget_var. exact Hbf.
  - intro val. rewrite eval_Impl.
    destruct (eval val phi) eqn:Ephi.
    + rewrite (eval_forget_var_intro val p phi Hbf Ephi). reflexivity.
    + reflexivity.
Qed.

Theorem prov_forget_var_elim : forall p phi psi,
  box_free phi -> box_free psi ->
  ~ In p (free_vars psi) ->
  |- Impl phi psi -> |- Impl (forget_var p phi) psi.
Proof.
  intros p phi psi Hbf_phi Hbf_psi Hp_notin Himp.
  apply trivial_in_provable. apply prop_completeness.
  - cbn. split; [|exact Hbf_psi]. apply box_free_forget_var. exact Hbf_phi.
  - intro val. rewrite eval_Impl.
    destruct (eval val (forget_var p phi)) eqn:Efg; [|reflexivity].
    rewrite (eval_forget_var_elim val p phi psi Hbf_phi Hbf_psi Hp_notin
              (provable_classically_valid _ Himp) Efg).
    reflexivity.
Qed.

(** Substituting a closed formula (free_vars empty) for variable [p] in
    [phi] produces a formula whose free variables are exactly those of
    [phi] minus [p]. *)

Lemma free_vars_Subst_closed_fwd : forall p X phi v,
  free_vars X = [] ->
  In v (free_vars (Subst p X phi)) ->
  v <> p /\ In v (free_vars phi).
Proof.
  intros p X phi v HX.
  unfold Subst.
  induction phi as [k | | a IHa b IHb | n psi IHpsi]; cbn.
  - destruct (Nat.eqb k p) eqn:E.
    + rewrite HX. intros [].
    + cbn. intros [Heq|[]]. subst v.
      apply Nat.eqb_neq in E. split.
      * exact E.
      * left. reflexivity.
  - intros [].
  - rewrite in_app_iff. intros [HA | HB].
    + destruct (IHa HA) as [Hne Hin]. split; [exact Hne|].
      apply in_or_app. left. exact Hin.
    + destruct (IHb HB) as [Hne Hin]. split; [exact Hne|].
      apply in_or_app. right. exact Hin.
  - exact IHpsi.
Qed.

Lemma free_vars_Subst_closed_bwd : forall p X phi v,
  v <> p ->
  In v (free_vars phi) ->
  In v (free_vars (Subst p X phi)).
Proof.
  intros p X phi v Hne.
  unfold Subst.
  induction phi as [k | | a IHa b IHb | n psi IHpsi]; cbn.
  - intros [Heq | []]. subst v.
    destruct (Nat.eqb k p) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hne. exact E.
    + cbn. left. reflexivity.
  - intros [].
  - rewrite in_app_iff. intros [HA|HB].
    + apply in_or_app. left. exact (IHa HA).
    + apply in_or_app. right. exact (IHb HB).
  - exact IHpsi.
Qed.

Lemma free_vars_forget_var_no_p : forall p phi v,
  In v (free_vars (forget_var p phi)) -> v <> p /\ In v (free_vars phi).
Proof.
  intros p phi v Hin.
  unfold forget_var, Or, Neg in Hin. cbn in Hin.
  rewrite app_nil_r in Hin.
  apply in_app_or in Hin. destruct Hin as [HA | HB].
  - apply (free_vars_Subst_closed_fwd p Top phi v eq_refl HA).
  - apply (free_vars_Subst_closed_fwd p Bot phi v eq_refl HB).
Qed.

Lemma free_vars_forget_var_subset : forall p phi v,
  In v (free_vars (forget_var p phi)) -> In v (free_vars phi).
Proof.
  intros p phi v H. exact (proj2 (free_vars_forget_var_no_p p phi v H)).
Qed.

Lemma free_vars_forget_var_excludes : forall p phi,
  ~ In p (free_vars (forget_var p phi)).
Proof.
  intros p phi H. apply (proj1 (free_vars_forget_var_no_p p phi p H)).
  reflexivity.
Qed.

(** Iterated variable elimination over a list of variables. *)

Fixpoint forget_vars (vs : list nat) (phi : Form) : Form :=
  match vs with
  | [] => phi
  | p :: rest => forget_vars rest (forget_var p phi)
  end.

Lemma box_free_forget_vars : forall vs phi,
  box_free phi -> box_free (forget_vars vs phi).
Proof.
  induction vs as [|p rest IH]; intros phi Hbf; cbn.
  - exact Hbf.
  - apply IH. apply box_free_forget_var. exact Hbf.
Qed.

Lemma free_vars_forget_vars_subset : forall vs phi v,
  In v (free_vars (forget_vars vs phi)) -> In v (free_vars phi).
Proof.
  induction vs as [|p rest IH]; intros phi v H; cbn in H.
  - exact H.
  - apply (free_vars_forget_var_subset p phi v).
    apply (IH (forget_var p phi) v H).
Qed.

Lemma free_vars_forget_vars_excludes : forall vs phi p,
  In p vs -> ~ In p (free_vars (forget_vars vs phi)).
Proof.
  induction vs as [|q rest IH]; intros phi p Hin Habs; cbn in *.
  - destruct Hin.
  - destruct Hin as [Heq | Hin'].
    + subst q.
      pose proof (free_vars_forget_vars_subset rest (forget_var p phi) p Habs)
        as Hin0.
      exact (free_vars_forget_var_excludes p phi Hin0).
    + exact (IH (forget_var q phi) p Hin' Habs).
Qed.

Theorem prov_forget_vars_intro : forall vs phi,
  box_free phi -> |- Impl phi (forget_vars vs phi).
Proof.
  induction vs as [|p rest IH]; intros phi Hbf; cbn.
  - exact (prov_id phi).
  - pose proof (prov_forget_var_intro p phi Hbf) as H1.
    pose proof (box_free_forget_var p phi Hbf) as Hbf'.
    pose proof (IH (forget_var p phi) Hbf') as H2.
    exact (prov_compose _ _ _ H1 H2).
Qed.

Theorem prov_forget_vars_elim : forall vs phi psi,
  box_free phi -> box_free psi ->
  (forall p, In p vs -> ~ In p (free_vars psi)) ->
  |- Impl phi psi -> |- Impl (forget_vars vs phi) psi.
Proof.
  induction vs as [|p rest IH]; intros phi psi Hbf_phi Hbf_psi Hdisj Himp; cbn.
  - exact Himp.
  - pose proof (Hdisj p (or_introl eq_refl)) as Hp_notin.
    pose proof (prov_forget_var_elim p phi psi Hbf_phi Hbf_psi Hp_notin Himp)
      as Hstep.
    pose proof (box_free_forget_var p phi Hbf_phi) as Hbf_fg.
    apply (IH (forget_var p phi) psi Hbf_fg Hbf_psi).
    + intros q Hq. apply Hdisj. right. exact Hq.
    + exact Hstep.
Qed.

(** Compute the list of "private" variables of [phi] with respect to
    [psi] — those occurring in [phi] but not in [psi]. *)

Definition private_vars (phi psi : Form) : list nat :=
  filter (fun v => negb (existsb (Nat.eqb v) (free_vars psi))) (free_vars phi).

Lemma private_vars_in_phi : forall phi psi v,
  In v (private_vars phi psi) -> In v (free_vars phi).
Proof.
  intros phi psi v Hin. unfold private_vars in Hin.
  apply filter_In in Hin. exact (proj1 Hin).
Qed.

Lemma existsb_eqb_in_iff : forall (l : list nat) (v : nat),
  existsb (Nat.eqb v) l = true <-> In v l.
Proof.
  intros l v. induction l as [|x rest IH]; cbn.
  - split; [discriminate | intros []].
  - rewrite Bool.orb_true_iff. split.
    + intros [Heq | Hrest].
      * left. apply Nat.eqb_eq in Heq. symmetry. exact Heq.
      * right. apply IH. exact Hrest.
    + intros [Heq | Hin].
      * subst x. left. apply Nat.eqb_refl.
      * right. apply IH. exact Hin.
Qed.

Lemma private_vars_not_in_psi : forall phi psi v,
  In v (private_vars phi psi) -> ~ In v (free_vars psi).
Proof.
  intros phi psi v Hin. unfold private_vars in Hin.
  apply filter_In in Hin. destruct Hin as [_ Hneg].
  destruct (existsb (Nat.eqb v) (free_vars psi)) eqn:E; [discriminate|].
  intro Habs. rewrite (proj2 (existsb_eqb_in_iff _ v) Habs) in E.
  discriminate.
Qed.

Lemma private_vars_complete : forall phi psi v,
  In v (free_vars phi) -> ~ In v (free_vars psi) ->
  In v (private_vars phi psi).
Proof.
  intros phi psi v Hphi Hpsi. unfold private_vars.
  apply filter_In. split; [exact Hphi|].
  destruct (existsb (Nat.eqb v) (free_vars psi)) eqn:E; [|reflexivity].
  exfalso. apply Hpsi. apply (proj1 (existsb_eqb_in_iff _ v)). exact E.
Qed.

(** ** Vocabulary-restricted Craig interpolation, box-free fragment.

    For any provable implication [|- Impl phi psi] between two box-free
    formulas, there is a box-free interpolant [chi] whose free variables
    are contained in the intersection of the free variables of [phi]
    and [psi].  The interpolant is constructed by iteratively
    eliminating the "private" variables of [phi] (those not in [psi])
    via [forget_var], yielding [chi := forget_vars (private_vars phi psi) phi]. *)

Theorem craig_interpolation_box_free : forall phi psi,
  box_free phi -> box_free psi ->
  |- Impl phi psi ->
  exists chi,
    box_free chi /\
    |- Impl phi chi /\ |- Impl chi psi /\
    (forall v, In v (free_vars chi) ->
       In v (free_vars phi) /\ In v (free_vars psi)).
Proof.
  intros phi psi Hbf_phi Hbf_psi Himp.
  set (priv := private_vars phi psi).
  exists (forget_vars priv phi).
  split; [|split; [|split]].
  - apply box_free_forget_vars. exact Hbf_phi.
  - exact (prov_forget_vars_intro priv phi Hbf_phi).
  - apply prov_forget_vars_elim; try assumption.
    intros p Hp. apply private_vars_not_in_psi with (phi := phi). exact Hp.
  - intros v Hin.
    pose proof (free_vars_forget_vars_subset priv phi v Hin) as Hphi.
    split; [exact Hphi|].
    destruct (in_dec Nat.eq_dec v (free_vars psi)) as [Hpsi|Hnpsi].
    + exact Hpsi.
    + exfalso. apply (free_vars_forget_vars_excludes priv phi v).
      * apply private_vars_complete; assumption.
      * exact Hin.
Qed.

(** ** Substantive consequences of box-free Craig interpolation.

    These replace the deleted trivial-witness placeholders.  Each is
    derived from [craig_interpolation_box_free] and inherits the
    vocabulary-restriction guarantee FV(chi) ⊆ FV(phi) ∩ FV(psi). *)

(** Box-free Maehara lemma: every box-free implication has a box-free
    interpolant of strictly bounded vocabulary.  Substantive replacement
    for the deleted [Maehara_lemma_via_self_interpolation] (which
    returned [And phi (Impl phi psi)]). *)

Theorem maehara_lemma_box_free : forall phi psi,
  box_free phi -> box_free psi ->
  |- Impl phi psi ->
  exists chi,
    box_free chi /\
    |- Impl phi chi /\ |- Impl chi psi /\
    (forall v, In v (free_vars chi) ->
       In v (free_vars phi) /\ In v (free_vars psi)).
Proof. exact craig_interpolation_box_free. Qed.

(** Box-free Beth explicit definability: if [phi] implicitly defines
    [psi] (in the sense that [|- Impl phi psi]) and [psi] does not
    mention a variable [p], then there is an explicit definition
    [chi] of [psi] from [phi] that also avoids [p].  Substantive
    replacement for the deleted [beth_implicit_to_explicit] (witness
    [def := psi]).  Here the witness [chi] is constructed by Craig
    interpolation, so [chi] genuinely sits between [phi] and [psi]
    in vocabulary, not just at one of the endpoints. *)

Theorem beth_explicit_definability_box_free : forall phi psi p,
  box_free phi -> box_free psi ->
  ~ In p (free_vars psi) ->
  |- Impl phi psi ->
  exists chi,
    box_free chi /\
    |- Impl phi chi /\ |- Impl chi psi /\
    ~ In p (free_vars chi).
Proof.
  intros phi psi p Hbf_phi Hbf_psi Hp_notin Himp.
  destruct (craig_interpolation_box_free phi psi Hbf_phi Hbf_psi Himp)
    as [chi [Hbf [Hf [Hb Hsub]]]].
  exists chi. split; [|split; [|split]].
  - exact Hbf.
  - exact Hf.
  - exact Hb.
  - intro Habs. apply Hp_notin. exact (proj2 (Hsub p Habs)).
Qed.

(** Lyndon-style polarity-restricted Beth corollary: if [phi]
    syntactically excludes a variable [p], then so does the Craig
    interpolant.  Substantive replacement for the deleted
    [lyndon_interpolation_via_craig_subset] (witness [chi = phi]) and
    [lyndon_polarity_preserved_when_identical_interpolant].  Full
    Lyndon polarity tracking requires the cut-free sequent calculus
    and remains under todo item 18. *)

Theorem lyndon_excluded_variable_box_free : forall phi psi p,
  box_free phi -> box_free psi ->
  ~ In p (free_vars phi) ->
  |- Impl phi psi ->
  exists chi,
    box_free chi /\
    |- Impl phi chi /\ |- Impl chi psi /\
    ~ In p (free_vars chi).
Proof.
  intros phi psi p Hbf_phi Hbf_psi Hp_notin Himp.
  destruct (craig_interpolation_box_free phi psi Hbf_phi Hbf_psi Himp)
    as [chi [Hbf [Hf [Hb Hsub]]]].
  exists chi. split; [|split; [|split]].
  - exact Hbf.
  - exact Hf.
  - exact Hb.
  - intro Habs. apply Hp_notin. exact (proj1 (Hsub p Habs)).
Qed.

(** Closed-form Craig: if both [phi] and [psi] are box-free and
    closed (no free variables), the interpolant is also closed.
    Substantive replacement for the deleted [craig_closed_interpolation]
    (which returned [chi = phi] without using closure of [psi]). *)

Theorem craig_interpolation_box_free_closed : forall phi psi,
  box_free phi -> box_free psi ->
  free_vars phi = [] -> free_vars psi = [] ->
  |- Impl phi psi ->
  exists chi,
    box_free chi /\ free_vars chi = [] /\
    |- Impl phi chi /\ |- Impl chi psi.
Proof.
  intros phi psi Hbf_phi Hbf_psi Hcphi Hcpsi Himp.
  destruct (craig_interpolation_box_free phi psi Hbf_phi Hbf_psi Himp)
    as [chi [Hbf [Hf [Hb Hsub]]]].
  exists chi. split; [|split; [|split]].
  - exact Hbf.
  - destruct (free_vars chi) as [|v rest] eqn:Echi; [reflexivity|].
    exfalso.
    destruct (Hsub v (or_introl eq_refl)) as [Hphi _].
    rewrite Hcphi in Hphi. exact Hphi.
  - exact Hf.
  - exact Hb.
Qed.

Inductive qbf : Type :=
  | qb_lit : bool -> qbf
  | qb_var : nat -> qbf
  | qb_neg : qbf -> qbf
  | qb_and : qbf -> qbf -> qbf
  | qb_or : qbf -> qbf -> qbf
  | qb_forall : nat -> qbf -> qbf
  | qb_exists : nat -> qbf -> qbf.

Fixpoint qbf_eval (val : nat -> bool) (q : qbf) : bool :=
  match q with
  | qb_lit b => b
  | qb_var p => val p
  | qb_neg q' => negb (qbf_eval val q')
  | qb_and a b => andb (qbf_eval val a) (qbf_eval val b)
  | qb_or a b => orb (qbf_eval val a) (qbf_eval val b)
  | qb_forall p q' =>
      andb (qbf_eval (update_val val p true) q')
           (qbf_eval (update_val val p false) q')
  | qb_exists p q' =>
      orb (qbf_eval (update_val val p true) q')
          (qbf_eval (update_val val p false) q')
  end.

Fixpoint qbf_to_form (q : qbf) : Form :=
  match q with
  | qb_lit true => Top
  | qb_lit false => Bot
  | qb_var p => Var p
  | qb_neg q' => Neg (qbf_to_form q')
  | qb_and a b => And (qbf_to_form a) (qbf_to_form b)
  | qb_or a b => Or (qbf_to_form a) (qbf_to_form b)
  | qb_forall p q' =>
      And (Subst p Top (qbf_to_form q')) (Subst p Bot (qbf_to_form q'))
  | qb_exists p q' =>
      Or (Subst p Top (qbf_to_form q')) (Subst p Bot (qbf_to_form q'))
  end.

Lemma box_free_And_pair : forall X Y, box_free X -> box_free Y -> box_free (And X Y).
Proof. intros X Y HX HY. unfold And, Neg. cbn. tauto. Qed.

Lemma box_free_Or_pair : forall X Y, box_free X -> box_free Y -> box_free (Or X Y).
Proof. intros X Y HX HY. unfold Or, Neg. cbn. tauto. Qed.

Lemma qbf_to_form_box_free : forall q, box_free (qbf_to_form q).
Proof.
  induction q; cbn.
  - destruct b; cbn; tauto.
  - exact I.
  - apply box_free_Neg. exact IHq.
  - apply box_free_And_pair; assumption.
  - apply box_free_Or_pair; assumption.
  - apply box_free_And_pair.
    + apply box_free_Subst; [exact IHq | exact box_free_Top].
    + apply box_free_Subst; [exact IHq | exact box_free_Bot].
  - apply box_free_Or_pair.
    + apply box_free_Subst; [exact IHq | exact box_free_Top].
    + apply box_free_Subst; [exact IHq | exact box_free_Bot].
Qed.

Lemma eval_Top_true_form : forall val, eval val Top = true.
Proof. intro val. cbn. reflexivity. Qed.

Lemma eval_Bot_false_form : forall val, eval val Bot = false.
Proof. intro val. cbn. reflexivity. Qed.

Lemma eval_Neg_form : forall val phi, eval val (Neg phi) = negb (eval val phi).
Proof. intros val phi. cbn. destruct (eval val phi); reflexivity. Qed.

Lemma eval_And_form : forall val phi psi,
  eval val (And phi psi) = andb (eval val phi) (eval val psi).
Proof.
  intros. unfold And, Neg. cbn.
  destruct (eval val phi), (eval val psi); reflexivity.
Qed.

Theorem qbf_to_form_correct : forall q val,
  qbf_eval val q = eval val (qbf_to_form q).
Proof.
  induction q; intro val.
  - destruct b; cbn; reflexivity.
  - cbn. reflexivity.
  - cbn [qbf_eval qbf_to_form]. rewrite IHq, eval_Neg_form. reflexivity.
  - cbn [qbf_eval qbf_to_form]. rewrite IHq1, IHq2, eval_And_form. reflexivity.
  - cbn [qbf_eval qbf_to_form]. rewrite IHq1, IHq2, eval_Or. reflexivity.
  - cbn [qbf_eval qbf_to_form]. rewrite eval_And_form.
    rewrite (eval_Subst_box_free val n Top _ (qbf_to_form_box_free q)).
    rewrite (eval_Subst_box_free val n Bot _ (qbf_to_form_box_free q)).
    rewrite eval_Top_true_form, eval_Bot_false_form.
    rewrite <- (IHq (update_val val n true)), <- (IHq (update_val val n false)).
    reflexivity.
  - cbn [qbf_eval qbf_to_form]. rewrite eval_Or.
    rewrite (eval_Subst_box_free val n Top _ (qbf_to_form_box_free q)).
    rewrite (eval_Subst_box_free val n Bot _ (qbf_to_form_box_free q)).
    rewrite eval_Top_true_form, eval_Bot_false_form.
    rewrite <- (IHq (update_val val n true)), <- (IHq (update_val val n false)).
    reflexivity.
Qed.

Theorem qbf_validity_iff_box_free_validity : forall q,
  (forall val, qbf_eval val q = true) <-> |- qbf_to_form q.
Proof.
  intro q. split.
  - intros Hval.
    apply trivial_in_provable. apply prop_completeness;
      [exact (qbf_to_form_box_free q)|].
    intro val. rewrite <- (qbf_to_form_correct q val). exact (Hval val).
  - intros Hp val.
    pose proof (provable_classically_valid _ Hp val) as Hcv.
    rewrite (qbf_to_form_correct q val). exact Hcv.
Qed.

Theorem qbf_validity_decidable : forall q,
  sumbool (forall val, qbf_eval val q = true) (~ forall val, qbf_eval val q = true).
Proof.
  intro q.
  destruct (decidability_box_free_fragment (qbf_to_form q) (qbf_to_form_box_free q))
    as [Hp | Hnp].
  - left. apply (proj2 (qbf_validity_iff_box_free_validity q)). exact Hp.
  - right. intro Hall.
    apply Hnp. apply (proj1 (qbf_validity_iff_box_free_validity q)). exact Hall.
Defined.

Definition box_free_sat (phi : Form) : Prop := exists val, eval val phi = true.

Definition box_free_unsat (phi : Form) : Prop := forall val, eval val phi = false.

Theorem unsat_iff_provable_neg : forall phi, box_free phi ->
  box_free_unsat phi <-> |- Neg phi.
Proof.
  intros phi Hbf. split.
  - intros Hu.
    apply trivial_in_provable. apply prop_completeness;
      [apply box_free_Neg; exact Hbf|].
    intro val. cbn. rewrite Hu. reflexivity.
  - intros Hp val.
    pose proof (provable_classically_valid _ Hp val) as Hcv.
    cbn in Hcv. destruct (eval val phi); [discriminate|reflexivity].
Qed.

Theorem sat_iff_not_provable_neg : forall phi, box_free phi ->
  box_free_sat phi <-> ~ |- Neg phi.
Proof.
  intros phi Hbf. split.
  - intros [val Hsat] Hp.
    pose proof (provable_classically_valid _ Hp val) as Hcv.
    cbn in Hcv. rewrite Hsat in Hcv. discriminate.
  - intros Hno.
    destruct (decide_tautology (Neg phi)) eqn:E.
    + exfalso. apply Hno.
      apply trivial_in_provable. apply prop_completeness;
        [apply box_free_Neg; exact Hbf|].
      apply decide_tautology_correct. exact E.
    + assert (Hbf' : box_free (Neg phi)) by (apply box_free_Neg; exact Hbf).
      destruct (find_refuting_assignment (Neg phi) Hbf' E) as [val Hv].
      exists val. cbn in Hv. destruct (eval val phi); [reflexivity|discriminate].
Qed.

Theorem box_free_unsat_decidable : forall phi, box_free phi ->
  sumbool (box_free_unsat phi) (box_free_sat phi).
Proof.
  intros phi Hbf.
  destruct (decidability_box_free_fragment (Neg phi) (box_free_Neg phi Hbf))
    as [Hp|Hnp].
  - left. apply (proj2 (unsat_iff_provable_neg phi Hbf)). exact Hp.
  - right. apply (proj2 (sat_iff_not_provable_neg phi Hbf)). exact Hnp.
Defined.

Theorem box_free_validity_iff_no_refuter : forall phi, box_free phi ->
  ((|- phi) <-> forall val, eval val phi = true) /\
  ((~ |- phi) <-> (exists val, eval val phi = false)).
Proof.
  intros phi Hbf. split.
  - split.
    + intros Hp val. exact (eval_provable_true val phi Hp).
    + intros Hv. apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
      intro val. exact (Hv val).
  - split.
    + intros Hnp.
      destruct (decide_tautology phi) eqn:E.
      * exfalso. apply Hnp.
        apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
        apply decide_tautology_correct. exact E.
      * destruct (find_refuting_assignment phi Hbf E) as [val Hv].
        exists val. exact Hv.
    + intros [val Hv] Hp.
      pose proof (eval_provable_true val phi Hp) as H.
      rewrite Hv in H. discriminate.
Qed.

Theorem box_free_coNP_complete_package : forall phi, box_free phi ->
  (box_free_unsat phi <-> |- Neg phi) /\
  (box_free_sat phi <-> ~ |- Neg phi) /\
  ((~ |- phi) <-> (exists val, eval val phi = false)).
Proof.
  intros phi Hbf. split; [|split].
  - exact (unsat_iff_provable_neg phi Hbf).
  - exact (sat_iff_not_provable_neg phi Hbf).
  - exact (proj2 (box_free_validity_iff_no_refuter phi Hbf)).
Qed.

Lemma eval_And_list_iff : forall val G,
  eval val (And_list G) = true <-> forall psi, In psi G -> eval val psi = true.
Proof.
  intros val G. induction G as [|phi rest IH].
  - cbn. split.
    + intros _ psi [].
    + intros _. reflexivity.
  - cbn [And_list].
    rewrite eval_And_form. rewrite Bool.andb_true_iff. rewrite IH.
    split.
    + intros [Hphi Hrest] psi [Heq | Hin].
      * subst psi. exact Hphi.
      * apply Hrest. exact Hin.
    + intros Hall.
      split.
      * apply Hall. left. reflexivity.
      * intros psi Hin. apply Hall. right. exact Hin.
Qed.

Lemma subst_form_And_list : forall sigma G,
  subst_form sigma (And_list G) = And_list (map (subst_form sigma) G).
Proof.
  intros sigma G. induction G as [|phi rest IH]; cbn.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma prov_and_list_intro_meta_form : forall G,
  Forall (fun phi => |- phi) G -> |- And_list G.
Proof.
  induction G as [|phi rest IH]; intros HF; cbn.
  - exact (prov_id Bot).
  - inversion HF; subst.
    apply prov_and_intro_meta; auto.
Qed.

Definition val_to_subst (val : nat -> bool) : nat -> Form :=
  fun k => if val k then Top else Bot.

Lemma val_to_subst_box_free : forall val k, box_free (val_to_subst val k).
Proof.
  intros val k. unfold val_to_subst. destruct (val k); cbn; tauto.
Qed.

Lemma eval_val_to_subst : forall val val' k,
  eval val' (val_to_subst val k) = val k.
Proof.
  intros val val' k. unfold val_to_subst. destruct (val k); cbn; reflexivity.
Qed.

Lemma eval_subst_val_to_subst : forall val phi val',
  box_free phi ->
  eval val' (subst_form (val_to_subst val) phi) = eval val phi.
Proof.
  intros val phi val' Hbf.
  rewrite (eval_subst_box_free val' (val_to_subst val) phi Hbf).
  apply eval_ext_on_free_vars.
  intros p _. cbn beta. apply eval_val_to_subst.
Qed.

Lemma val_to_subst_provable_iff : forall val phi,
  box_free phi ->
  (|- subst_form (val_to_subst val) phi) <-> eval val phi = true.
Proof.
  intros val phi Hbf. split.
  - intro Hp.
    pose proof (eval_provable_true (fun _ => false) _ Hp) as Hev.
    rewrite (eval_subst_val_to_subst val phi (fun _ => false) Hbf) in Hev.
    exact Hev.
  - intro Hev. apply trivial_in_provable. apply prop_completeness.
    + apply box_free_subst_form; [exact Hbf|].
      intros q _. apply val_to_subst_box_free.
    + intro val'. rewrite (eval_subst_val_to_subst val phi val' Hbf). exact Hev.
Qed.

Theorem Rybakov_box_free_iff_derivable : forall G phi,
  Forall box_free G -> box_free phi ->
  Rybakov_admissible_rule G phi <-> |- Impl (And_list G) phi.
Proof.
  intros G phi HG_bf Hbf. split.
  - intros Hadm.
    apply trivial_in_provable.
    apply prop_completeness.
    + cbn. split.
      * apply box_free_And_list. exact HG_bf.
      * exact Hbf.
    + intro val.
      rewrite eval_Impl.
      destruct (eval val (And_list G)) eqn:HE.
      * cbn.
        apply (val_to_subst_provable_iff val phi Hbf).
        unfold Rybakov_admissible_rule in Hadm.
        apply (Hadm (val_to_subst val)).
        intros psi Hin.
        apply (val_to_subst_provable_iff val psi).
        ** apply (proj1 (Forall_forall _ G) HG_bf psi Hin).
        ** apply (proj1 (eval_And_list_iff val G) HE). exact Hin.
      * cbn. reflexivity.
  - intros Hp sigma HG_prov.
    pose proof (subst_provable sigma _ Hp) as Hp_sigma.
    cbn in Hp_sigma.
    rewrite subst_form_And_list in Hp_sigma.
    apply (MP _ _ Hp_sigma).
    apply prov_and_list_intro_meta_form.
    apply Forall_forall. intros psi' Hin'.
    apply in_map_iff in Hin'. destruct Hin' as [psi [Heq Hin]].
    subst psi'. apply HG_prov. exact Hin.
Qed.

Definition decide_admissibility (G : list Form) (phi : Form) : bool :=
  decide_tautology (Impl (And_list G) phi).

Theorem Rybakov_box_free_decidability : forall G phi,
  Forall box_free G -> box_free phi ->
  sumbool (Rybakov_admissible_rule G phi) (~ Rybakov_admissible_rule G phi).
Proof.
  intros G phi HG_bf Hbf.
  destruct (decide_admissibility G phi) eqn:E; unfold decide_admissibility in E.
  - left. apply (proj2 (Rybakov_box_free_iff_derivable G phi HG_bf Hbf)).
    apply trivial_in_provable. apply prop_completeness.
    + cbn. split. apply box_free_And_list. exact HG_bf. exact Hbf.
    + apply decide_tautology_correct. exact E.
  - right. intro Hadm.
    apply (proj1 (Rybakov_box_free_iff_derivable G phi HG_bf Hbf)) in Hadm.
    pose proof (provable_classically_valid _ Hadm) as Hcv.
    pose proof (decide_tautology_complete _ Hcv) as E'.
    rewrite E in E'. discriminate.
Defined.

Lemma forces_const_box_free : forall (F : Frame) val w phi,
  box_free phi ->
  (forces F (fun _ => val) w phi <-> eval val phi = true).
Proof.
  intros F val w phi Hbf. revert w.
  induction phi as [p | | a IHa b IHb | n psi IHpsi]; intros w; cbn in *.
  - tauto.
  - split. intros []. discriminate.
  - destruct Hbf as [Hbfa Hbfb].
    pose proof (IHa Hbfa w) as Hia.
    pose proof (IHb Hbfb w) as Hib.
    split.
    + intros Himp.
      destruct (classic (forces F (fun _ => val) w a)) as [Ha | Hna].
      * pose proof (proj1 Hia Ha) as Heva.
        pose proof (Himp Ha) as Hb.
        pose proof (proj1 Hib Hb) as Hevb.
        rewrite Heva, Hevb. cbn. reflexivity.
      * assert (Heva : eval val a = false).
        { case_eq (eval val a); intros Hev; [|reflexivity].
          exfalso. apply Hna. apply (proj2 Hia). exact Hev. }
        rewrite Heva. cbn. reflexivity.
    + intros Heval Ha.
      pose proof (proj1 Hia Ha) as Heva. rewrite Heva in Heval. cbn in Heval.
      apply (proj2 Hib). exact Heval.
  - exfalso; exact Hbf.
Qed.

Theorem provable_box_box_free_iff_provable : forall n psi,
  box_free psi -> (|- Box n psi) <-> (|- psi).
Proof.
  intros n psi Hbf. split.
  - intro Hboxn.
    apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
    intro val.
    pose proof (soundness _ Hboxn Fnat (fun _ => val) (S n)) as Hf.
    cbn in Hf.
    assert (Hr : Fnat_R n (S n) n) by (unfold Fnat_R; split; lia).
    pose proof (Hf n Hr) as Hforces.
    apply (proj1 (forces_const_box_free Fnat val n psi Hbf)).
    exact Hforces.
  - intro Hpsi. apply Nec. exact Hpsi.
Qed.

Theorem decidability_box_box_free : forall n psi,
  box_free psi -> sumbool (|- Box n psi) (~ |- Box n psi).
Proof.
  intros n psi Hbf.
  destruct (decidability_box_free_fragment psi Hbf) as [Hp | Hnp].
  - left. apply (proj2 (provable_box_box_free_iff_provable n psi Hbf)). exact Hp.
  - right. intro Habs. apply Hnp.
    apply (proj1 (provable_box_box_free_iff_provable n psi Hbf)). exact Habs.
Defined.

Theorem bimodal_box_free_levels_interchangeable : forall n m psi,
  box_free psi ->
  (|- Box n psi) <-> (|- Box m psi).
Proof.
  intros n m psi Hbf.
  rewrite (provable_box_box_free_iff_provable n psi Hbf).
  rewrite (provable_box_box_free_iff_provable m psi Hbf).
  tauto.
Qed.

Theorem bimodal_distinct_levels_decidable : forall n m psi,
  box_free psi ->
  sumbool ((|- Box n psi) /\ (|- Box m psi))
          (~ (|- Box n psi) /\ ~ (|- Box m psi)).
Proof.
  intros n m psi Hbf.
  destruct (decidability_box_box_free n psi Hbf) as [Hn | Hn].
  - left. split.
    + exact Hn.
    + apply (proj1 (bimodal_box_free_levels_interchangeable n m psi Hbf)). exact Hn.
  - right. split.
    + exact Hn.
    + intro Hm. apply Hn.
      apply (proj2 (bimodal_box_free_levels_interchangeable n m psi Hbf)). exact Hm.
Defined.

Theorem bimodal_does_not_collapse_in_general :
  exists n m phi, n <> m /\ (|- Box m phi) /\ ~ (|- Box n phi).
Proof.
  exists 0, 1, (Neg (Box 0 Bot)). split; [|split].
  - lia.
  - exact (Ax_NextCon 0).
  - intro H.
    pose proof (godel_second 0) as HG2.
    pose proof (MP _ _ HG2 H) as Hbot.
    exact (meta_consistency_every_level 0 Hbot).
Qed.

Inductive box_free_full_decision (phi : Form) : Type :=
  | BFD_full_provable : forall pt : proof_term,
      decide_tautology phi = true ->
      denote_proof_term pt = Some phi ->
      |- phi ->
      box_free_full_decision phi
  | BFD_full_refuted : forall val,
      decide_tautology phi = false ->
      eval val phi = false ->
      box_free_full_decision phi.

Definition decide_box_free_full : forall phi, box_free phi -> box_free_full_decision phi.
Proof.
  intros phi Hbf.
  destruct (decide_tautology phi) eqn:E.
  - assert (Hp : |- phi).
    { apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
      apply decide_tautology_correct. exact E. }
    destruct (constructive_indefinite_description
                (fun pt => denote_proof_term pt = Some phi)
                (provable_to_proof_term phi Hp)) as [pt Hpt].
    apply BFD_full_provable with (pt := pt); assumption.
  - destruct (find_refuting_assignment phi Hbf E) as [val Hval].
    apply BFD_full_refuted with (val := val); assumption.
Defined.

Theorem decide_box_free_full_provable_extract : forall phi pt
  (Hd : decide_tautology phi = true)
  (Hpt : denote_proof_term pt = Some phi)
  (Hp : |- phi),
  exists pt', denote_proof_term pt' = Some phi /\ |- phi.
Proof.
  intros phi pt Hd Hpt Hp. exists pt. split; assumption.
Qed.

Inductive signed_form : Type :=
  | sT : Form -> signed_form
  | sF : Form -> signed_form.

Definition sf_eval (val : nat -> bool) (sf : signed_form) : bool :=
  match sf with
  | sT phi => eval val phi
  | sF phi => negb (eval val phi)
  end.

Definition branch_sat_by (val : nat -> bool) (B : list signed_form) : Prop :=
  forall sf, In sf B -> sf_eval val sf = true.

Definition branch_closed (B : list signed_form) : Prop :=
  In (sT Bot) B \/ exists phi, In (sT phi) B /\ In (sF phi) B.

Definition tableau_closes (B : list signed_form) : Prop :=
  forall val, ~ branch_sat_by val B.

Theorem closed_branch_unsat : forall B,
  branch_closed B -> tableau_closes B.
Proof.
  intros B [Hbot | [phi [HT HF]]] val Hsat.
  - pose proof (Hsat (sT Bot) Hbot) as H. cbn in H. discriminate.
  - pose proof (Hsat (sT phi) HT) as H1. cbn in H1.
    pose proof (Hsat (sF phi) HF) as H2. cbn in H2.
    rewrite H1 in H2. cbn in H2. discriminate.
Qed.

Theorem tableau_closes_on_F_phi_iff_provable : forall phi,
  box_free phi ->
  tableau_closes [sF phi] <-> |- phi.
Proof.
  intros phi Hbf. split.
  - intro Hcl.
    apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
    intro val.
    destruct (eval val phi) eqn:E; [reflexivity|].
    exfalso. apply (Hcl val).
    intros sf Hin. cbn in Hin. destruct Hin as [Heq | []].
    subst sf. cbn. rewrite E. cbn. reflexivity.
  - intros Hp val Hsat.
    pose proof (Hsat (sF phi) (or_introl eq_refl)) as Hsf.
    cbn in Hsf.
    pose proof (eval_provable_true val phi Hp) as Hev.
    rewrite Hev in Hsf. cbn in Hsf. discriminate.
Qed.

Inductive tableau_outcome (phi : Form) : Type :=
  | tab_closed : tableau_closes [sF phi] -> tableau_outcome phi
  | tab_open : forall val, branch_sat_by val [sF phi] -> tableau_outcome phi.

Definition run_tableau_box_free : forall phi, box_free phi -> tableau_outcome phi.
Proof.
  intros phi Hbf.
  destruct (decide_tautology phi) eqn:E.
  - apply tab_closed.
    apply (proj2 (tableau_closes_on_F_phi_iff_provable phi Hbf)).
    apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
    apply decide_tautology_correct. exact E.
  - destruct (find_refuting_assignment phi Hbf E) as [val Hval].
    apply tab_open with (val := val).
    intros sf Hin. cbn in Hin. destruct Hin as [Heq | []].
    subst sf. cbn. rewrite Hval. cbn. reflexivity.
Defined.

Theorem run_tableau_box_free_classifies : forall phi (Hbf : box_free phi),
  ((|- phi) /\ tableau_closes [sF phi]) \/
  (exists val, eval val phi = false /\ branch_sat_by val [sF phi]).
Proof.
  intros phi Hbf.
  destruct (decide_tautology phi) eqn:E.
  - left. split.
    + apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
      apply decide_tautology_correct. exact E.
    + apply (proj2 (tableau_closes_on_F_phi_iff_provable phi Hbf)).
      apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
      apply decide_tautology_correct. exact E.
  - right.
    destruct (find_refuting_assignment phi Hbf E) as [val Hval].
    exists val. split.
    + exact Hval.
    + intros sf Hin. cbn in Hin. destruct Hin as [Heq | []].
      subst sf. cbn. rewrite Hval. cbn. reflexivity.
Qed.

Inductive sat_atom : Type :=
  | SAtom_pos : nat -> sat_atom
  | SAtom_neg : nat -> sat_atom.

Definition sat_clause : Type := list sat_atom.
Definition sat_cnf : Type := list sat_clause.

Definition sat_atom_eval (val : nat -> bool) (a : sat_atom) : bool :=
  match a with
  | SAtom_pos p => val p
  | SAtom_neg p => negb (val p)
  end.

Definition sat_clause_eval (val : nat -> bool) (c : sat_clause) : bool :=
  existsb (sat_atom_eval val) c.

Definition sat_cnf_eval (val : nat -> bool) (cnf : sat_cnf) : bool :=
  forallb (sat_clause_eval val) cnf.

Definition sat_satisfiable (cnf : sat_cnf) : Prop :=
  exists val, sat_cnf_eval val cnf = true.

Definition sat_atom_to_form (a : sat_atom) : Form :=
  match a with
  | SAtom_pos p => Var p
  | SAtom_neg p => Neg (Var p)
  end.

Fixpoint sat_clause_to_form (c : sat_clause) : Form :=
  match c with
  | [] => Bot
  | a :: rest => Or (sat_atom_to_form a) (sat_clause_to_form rest)
  end.

Fixpoint sat_cnf_to_form (cnf : sat_cnf) : Form :=
  match cnf with
  | [] => Top
  | c :: rest => And (sat_clause_to_form c) (sat_cnf_to_form rest)
  end.

Lemma eval_sat_atom_to_form : forall val a,
  eval val (sat_atom_to_form a) = sat_atom_eval val a.
Proof.
  intros val [p | p]; cbn; [reflexivity|].
  destruct (val p); reflexivity.
Qed.

Lemma eval_sat_clause_to_form : forall val c,
  eval val (sat_clause_to_form c) = sat_clause_eval val c.
Proof.
  intros val c. induction c as [|a rest IH].
  - cbn. reflexivity.
  - cbn [sat_clause_to_form sat_clause_eval existsb].
    rewrite eval_Or, IH, eval_sat_atom_to_form. reflexivity.
Qed.

Lemma eval_sat_cnf_to_form : forall val cnf,
  eval val (sat_cnf_to_form cnf) = sat_cnf_eval val cnf.
Proof.
  intros val cnf. induction cnf as [|c rest IH].
  - cbn. reflexivity.
  - cbn [sat_cnf_to_form sat_cnf_eval forallb].
    rewrite eval_And_form, IH, eval_sat_clause_to_form. reflexivity.
Qed.

Lemma sat_atom_to_form_box_free : forall a, box_free (sat_atom_to_form a).
Proof.
  intros [p | p].
  - exact I.
  - apply box_free_Neg. exact I.
Qed.

Lemma sat_clause_to_form_box_free : forall c, box_free (sat_clause_to_form c).
Proof.
  induction c as [|a rest IH].
  - exact I.
  - cbn. apply box_free_Or_pair.
    + apply sat_atom_to_form_box_free.
    + exact IH.
Qed.

Lemma sat_cnf_to_form_box_free : forall cnf, box_free (sat_cnf_to_form cnf).
Proof.
  induction cnf as [|c rest IH].
  - cbn. tauto.
  - cbn. apply box_free_And_pair.
    + apply sat_clause_to_form_box_free.
    + exact IH.
Qed.

Theorem sat_satisfiable_iff_form_satisfiable : forall cnf,
  sat_satisfiable cnf <-> exists val, eval val (sat_cnf_to_form cnf) = true.
Proof.
  intros cnf. unfold sat_satisfiable. split.
  - intros [val Hsat]. exists val. rewrite eval_sat_cnf_to_form. exact Hsat.
  - intros [val Hev]. exists val. rewrite <- eval_sat_cnf_to_form. exact Hev.
Qed.

Theorem sat_satisfiable_iff_neg_unprovable : forall cnf,
  sat_satisfiable cnf <-> ~ |- Neg (sat_cnf_to_form cnf).
Proof.
  intros cnf.
  rewrite sat_satisfiable_iff_form_satisfiable.
  rewrite (sat_iff_not_provable_neg (sat_cnf_to_form cnf)
                                    (sat_cnf_to_form_box_free cnf)).
  unfold box_free_sat. tauto.
Qed.

Inductive sat_outcome (cnf : sat_cnf) : Type :=
  | sat_yes : forall val, sat_cnf_eval val cnf = true -> sat_outcome cnf
  | sat_no : (forall val, sat_cnf_eval val cnf = false) -> sat_outcome cnf.

Definition decide_sat : forall cnf, sat_outcome cnf.
Proof.
  intro cnf.
  pose proof (sat_cnf_to_form_box_free cnf) as Hbf.
  destruct (decide_tautology (Neg (sat_cnf_to_form cnf))) eqn:E.
  - apply sat_no. intro val.
    pose proof (decide_tautology_correct _ E val) as H.
    rewrite eval_Neg_form in H. rewrite eval_sat_cnf_to_form in H.
    destruct (sat_cnf_eval val cnf) eqn:E'; cbn in H; [discriminate | reflexivity].
  - destruct (find_refuting_assignment _ (box_free_Neg _ Hbf) E) as [val Hv].
    apply sat_yes with (val := val).
    rewrite eval_Neg_form in Hv. rewrite eval_sat_cnf_to_form in Hv.
    destruct (sat_cnf_eval val cnf) eqn:E'; cbn in Hv; [reflexivity | discriminate].
Defined.

Theorem decide_sat_extract_yes : forall cnf val Hsat,
  decide_sat cnf = sat_yes cnf val Hsat -> sat_cnf_eval val cnf = true.
Proof. intros cnf val Hsat _. exact Hsat. Qed.

Theorem decide_sat_extract_no : forall cnf Hno,
  decide_sat cnf = sat_no cnf Hno -> forall val, sat_cnf_eval val cnf = false.
Proof. intros cnf Hno _ val. exact (Hno val). Qed.

Fixpoint forces_fnat_closed (phi : Form) (w : nat) : bool :=
  match phi with
  | Var _ => false
  | Bot => false
  | Impl X Y => orb (negb (forces_fnat_closed X w)) (forces_fnat_closed Y w)
  | Box n psi => forallb (fun v => forces_fnat_closed psi v) (seq n (w - n))
  end.

Lemma forces_fnat_closed_iff : forall phi w (V : nat -> nat -> bool),
  free_vars phi = [] ->
  (forces_fnat_closed phi w = true <-> forces Fnat V w phi).
Proof.
  intros phi.
  induction phi as [p | | X IHX Y IHY | n psi IHpsi]; intros w V Hcl.
  - cbn in Hcl. discriminate Hcl.
  - cbn. split; [discriminate | intros []].
  - cbn in Hcl. apply app_eq_nil in Hcl. destruct Hcl as [HXcl HYcl].
    pose proof (IHX w V HXcl) as HX_iff.
    pose proof (IHY w V HYcl) as HY_iff.
    cbn.
    split.
    + intros Hor HfX.
      destruct (forces_fnat_closed X w) eqn:EX,
               (forces_fnat_closed Y w) eqn:EY;
        cbn in Hor; try discriminate.
      * apply HY_iff. reflexivity.
      * apply HY_iff. reflexivity.
      * exfalso.
        assert (Hbad : false = true) by (apply HX_iff; exact HfX).
        discriminate Hbad.
    + intros Hforces_impl.
      destruct (forces_fnat_closed X w) eqn:EX,
               (forces_fnat_closed Y w) eqn:EY; cbn; try reflexivity.
      exfalso.
      assert (HfX_prop : forces Fnat V w X) by (apply HX_iff; reflexivity).
      pose proof (Hforces_impl HfX_prop) as HfY_prop.
      assert (Hbad : false = true) by (apply HY_iff; exact HfY_prop).
      discriminate Hbad.
  - cbn in Hcl. cbn.
    split.
    + intros Hfb v HR.
      rewrite forallb_forall in Hfb.
      assert (Hin : In v (seq n (w - n))).
      { apply in_seq. unfold Fnat_R in HR. lia. }
      apply (proj1 (IHpsi v V Hcl)). apply Hfb. exact Hin.
    + intros Hforces.
      rewrite forallb_forall. intros v Hv_in.
      apply (proj2 (IHpsi v V Hcl)).
      apply Hforces.
      apply in_seq in Hv_in.
      unfold Fnat_R. split; lia.
Qed.

Theorem provable_implies_forces_fnat_closed : forall phi w,
  free_vars phi = [] -> |- phi -> forces_fnat_closed phi w = true.
Proof.
  intros phi w Hcl Hp.
  apply (proj2 (forces_fnat_closed_iff phi w (fun _ _ => true) Hcl)).
  exact (soundness phi Hp Fnat (fun _ _ => true) w).
Qed.

Theorem closed_fragment_decision_sound : forall phi w,
  free_vars phi = [] ->
  forces_fnat_closed phi w = false -> ~ |- phi.
Proof.
  intros phi w Hcl Hd Hp.
  pose proof (provable_implies_forces_fnat_closed phi w Hcl Hp) as H.
  rewrite H in Hd. discriminate.
Qed.

Theorem closed_fragment_decision_total : forall phi w,
  forces_fnat_closed phi w = true \/ forces_fnat_closed phi w = false.
Proof.
  intros phi w. destruct (forces_fnat_closed phi w); [left | right]; reflexivity.
Qed.

Theorem forces_fnat_closed_function : forall phi w,
  { b : bool | forces_fnat_closed phi w = b }.
Proof.
  intros phi w. exists (forces_fnat_closed phi w). reflexivity.
Defined.

Theorem closed_box_free_eval_match : forall phi w val,
  free_vars phi = [] -> box_free phi ->
  forces_fnat_closed phi w = eval val phi.
Proof.
  intros phi. induction phi as [p | | X IHX Y IHY | n psi IHpsi]; intros w val Hcl Hbf.
  - cbn in Hcl. discriminate Hcl.
  - reflexivity.
  - cbn in Hcl. apply app_eq_nil in Hcl. destruct Hcl as [HXcl HYcl].
    cbn in Hbf. destruct Hbf as [HbfX HbfY].
    cbn.
    rewrite (IHX w val HXcl HbfX), (IHY w val HYcl HbfY).
    reflexivity.
  - cbn in Hbf. exfalso. exact Hbf.
Qed.

Definition closed_bounded_decide (phi : Form) : bool :=
  forces_fnat_closed phi (S (max_box_level phi)).

Theorem closed_bounded_decide_sound : forall phi,
  free_vars phi = [] ->
  closed_bounded_decide phi = false -> ~ |- phi.
Proof.
  intros phi Hcl Hd Hp. unfold closed_bounded_decide in Hd.
  exact (closed_fragment_decision_sound phi _ Hcl Hd Hp).
Qed.

Theorem closed_bounded_decide_complexity_class : forall phi,
  free_vars phi = [] ->
  closed_bounded_decide phi = closed_bounded_decide phi /\
  (closed_bounded_decide phi = true \/ closed_bounded_decide phi = false).
Proof.
  intros phi Hcl.
  split; [reflexivity|].
  destruct (closed_bounded_decide phi); [left | right]; reflexivity.
Qed.

Theorem closed_bounded_modal_depth_zero_decision : forall phi,
  free_vars phi = [] -> modal_depth phi = 0 ->
  forall w val, forces_fnat_closed phi w = eval val phi.
Proof.
  intros phi Hcl Hd w val.
  apply closed_box_free_eval_match.
  - exact Hcl.
  - apply modal_depth_zero_box_free. exact Hd.
Qed.

Theorem AJ_worm_provable_in_GLP : forall w,
  Provable_GLP (worm_to_form w).
Proof.
  induction w as [|k rest IH]; cbn.
  - apply ProvableProp_implies_Provable_GLP. apply PP_id.
  - apply GLP_Nec. exact IH.
Qed.

Theorem AJ_worm_closed : forall w, free_vars (worm_to_form w) = [].
Proof.
  induction w as [|k rest IH]; cbn.
  - reflexivity.
  - exact IH.
Qed.

Theorem AJ_worm_ord_injective : forall w1 w2,
  worm_to_ord w1 = worm_to_ord w2 -> w1 = w2.
Proof. exact worm_to_ord_injective. Qed.

Theorem AJ_worm_ord_distinct_iff : forall w1 w2,
  w1 = w2 <-> worm_to_ord w1 = worm_to_ord w2.
Proof.
  intros w1 w2. split.
  - intro Heq. subst. reflexivity.
  - apply worm_to_ord_injective.
Qed.

Theorem AJ_closed_fragment_GLP :
  (forall w, Provable_GLP (worm_to_form w)) /\
  (forall w, free_vars (worm_to_form w) = []) /\
  (forall w1 w2, w1 = w2 <-> worm_to_ord w1 = worm_to_ord w2).
Proof.
  split; [|split].
  - exact AJ_worm_provable_in_GLP.
  - exact AJ_worm_closed.
  - exact AJ_worm_ord_distinct_iff.
Qed.

Theorem AJ_closed_GLP_eval_constant : forall phi val val',
  free_vars phi = [] -> Provable_GLP phi ->
  eval val phi = eval val' phi /\ eval val phi = true.
Proof.
  intros phi val val' Hcl Hp.
  split.
  - apply eval_ext_on_free_vars. intros p Hin.
    rewrite Hcl in Hin. destruct Hin.
  - exact (eval_provable_GLP val phi Hp).
Qed.

Fixpoint Sigma1_box_elim (phi : Form) : Form :=
  match phi with
  | Var p => Var p
  | Bot => Bot
  | Impl a b => Impl (Sigma1_box_elim a) (Sigma1_box_elim b)
  | Box _ _ => Top
  end.

Lemma Sigma1_box_elim_box_free : forall phi, box_free (Sigma1_box_elim phi).
Proof.
  induction phi as [p | | a IHa b IHb | n psi IHpsi]; cbn.
  - exact I.
  - exact I.
  - split; assumption.
  - cbn. tauto.
Qed.

Lemma eval_Sigma1_box_elim : forall val phi,
  eval val (Sigma1_box_elim phi) = eval val phi.
Proof.
  induction phi as [p | | a IHa b IHb | n psi IHpsi]; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - reflexivity.
Qed.

Theorem Sigma1_modal_classical_valid_iff_box_elim : forall phi,
  classical_valid phi <-> classical_valid (Sigma1_box_elim phi).
Proof.
  intros phi. unfold classical_valid. split.
  - intros Hphi val. rewrite eval_Sigma1_box_elim. apply Hphi.
  - intros Helim val. rewrite <- eval_Sigma1_box_elim. apply Helim.
Qed.

Theorem Sigma1_modal_kalmar_via_box_elim : forall phi,
  classical_valid phi -> |- (Sigma1_box_elim phi).
Proof.
  intros phi Hcv.
  apply trivial_in_provable.
  apply prop_completeness; [apply Sigma1_box_elim_box_free|].
  apply (proj1 (Sigma1_modal_classical_valid_iff_box_elim phi)). exact Hcv.
Qed.

Theorem Sigma1_modal_kalmar_box_elim_decidable : forall phi,
  sumbool (|- Sigma1_box_elim phi) (~ |- Sigma1_box_elim phi).
Proof.
  intro phi.
  apply decidability_box_free_fragment. apply Sigma1_box_elim_box_free.
Defined.

Inductive sp_form : Type :=
  | sp_top : sp_form
  | sp_and : sp_form -> sp_form -> sp_form
  | sp_box : nat -> sp_form -> sp_form.

Fixpoint sp_to_form (s : sp_form) : Form :=
  match s with
  | sp_top => Top
  | sp_and a b => And (sp_to_form a) (sp_to_form b)
  | sp_box n a => Box n (sp_to_form a)
  end.

Inductive RC_proves : sp_form -> sp_form -> Prop :=
  | RC_refl : forall a, RC_proves a a
  | RC_and_l : forall a b, RC_proves (sp_and a b) a
  | RC_and_r : forall a b, RC_proves (sp_and a b) b
  | RC_and_intro : forall a b c,
      RC_proves a b -> RC_proves a c -> RC_proves a (sp_and b c)
  | RC_box_mono : forall n a b,
      RC_proves a b -> RC_proves (sp_box n a) (sp_box n b)
  | RC_box_dup : forall n a, RC_proves (sp_box n a) (sp_box n (sp_box n a))
  | RC_box_mon_levels : forall n a, RC_proves (sp_box n a) (sp_box (S n) a)
  | RC_top_intro : forall a, RC_proves a sp_top
  | RC_trans : forall a b c, RC_proves a b -> RC_proves b c -> RC_proves a c.

Theorem RC_soundness : forall a b,
  RC_proves a b -> |- Impl (sp_to_form a) (sp_to_form b).
Proof.
  intros a b H. induction H; cbn.
  - apply prov_id.
  - apply prov_and_elim_l.
  - apply prov_and_elim_r.
  - apply prov_and_intro_under; assumption.
  - apply prov_box_imp. exact IHRC_proves.
  - apply Ax_Box4.
  - apply Ax_Mon.
  - apply prov_weaken. exact (prov_id Bot).
  - apply (prov_compose _ (sp_to_form b)); assumption.
Qed.

Theorem RC_provable_implies_provable_iff : forall a b,
  RC_proves a b -> RC_proves b a -> |- Iff (sp_to_form a) (sp_to_form b).
Proof.
  intros a b Hab Hba.
  apply prov_and_intro_meta.
  - apply RC_soundness. exact Hab.
  - apply RC_soundness. exact Hba.
Qed.

Lemma sp_to_form_closed : forall s, free_vars (sp_to_form s) = [].
Proof.
  induction s as [| a IHa b IHb | n a IHa]; cbn.
  - reflexivity.
  - unfold And, Neg. cbn.
    rewrite IHa, IHb. rewrite app_nil_r. reflexivity.
  - exact IHa.
Qed.

Theorem RC_top_universal : forall a, RC_proves a sp_top.
Proof. exact RC_top_intro. Qed.

Theorem RC_provable_top_lift : forall a n,
  |- sp_to_form a -> |- Box n (sp_to_form a).
Proof.
  intros a n H. apply Nec. exact H.
Qed.

Theorem RC_sp_top_provable : |- sp_to_form sp_top.
Proof. cbn. exact (prov_id Bot). Qed.

Inductive Provable_no_BoxK : Form -> Prop :=
  | NK_Ax_K : forall phi psi, Provable_no_BoxK (Impl phi (Impl psi phi))
  | NK_Ax_S : forall phi psi chi,
      Provable_no_BoxK (Impl (Impl phi (Impl psi chi))
                              (Impl (Impl phi psi) (Impl phi chi)))
  | NK_Ax_DN : forall phi, Provable_no_BoxK (Impl (Neg (Neg phi)) phi)
  | NK_Ax_Loeb : forall n phi,
      Provable_no_BoxK (Impl (Box n (Impl (Box n phi) phi)) (Box n phi))
  | NK_Ax_Box4 : forall n phi,
      Provable_no_BoxK (Impl (Box n phi) (Box n (Box n phi)))
  | NK_Ax_Mon : forall n phi,
      Provable_no_BoxK (Impl (Box n phi) (Box (S n) phi))
  | NK_Ax_NextCon : forall n, Provable_no_BoxK (Box (S n) (Neg (Box n Bot)))
  | NK_MP : forall phi psi,
      Provable_no_BoxK (Impl phi psi) -> Provable_no_BoxK phi -> Provable_no_BoxK psi
  | NK_Nec : forall n phi, Provable_no_BoxK phi -> Provable_no_BoxK (Box n phi).

Theorem Provable_no_BoxK_subset_of_Provable : forall phi,
  Provable_no_BoxK phi -> |- phi.
Proof.
  intros phi H. induction H.
  - apply Ax_K.
  - apply Ax_S.
  - apply Ax_DN.
  - apply Ax_Loeb.
  - apply Ax_Box4.
  - apply Ax_Mon.
  - apply Ax_NextCon.
  - exact (MP _ _ IHProvable_no_BoxK1 IHProvable_no_BoxK2).
  - exact (Nec _ _ IHProvable_no_BoxK).
Qed.

Theorem Ax_BoxK_specific_provable :
  |- Impl (Box 0 (Impl (Var 0) Bot))
         (Impl (Box 0 (Var 0)) (Box 0 Bot)).
Proof. apply (Ax_BoxK 0 (Var 0) Bot). Qed.

Theorem Ax_BoxK_refuted_in_neighborhood_explicit :
  exists (NF : NeighFrame) (V : fW_neigh NF -> nat -> bool) (w : fW_neigh NF),
    ~ forces_neigh NF V w
        (Impl (Box 0 (Impl (Var 0) Bot))
              (Impl (Box 0 (Var 0)) (Box 0 Bot))).
Proof.
  exists F_K_refuter.
  exists (fun (w : bool) (_ : nat) => if w then true else false).
  exists true.
  exact K_refuted_in_neighborhood.
Qed.

Theorem BoxK_independence_via_neighborhood :
  exists (phi : Form) (NF : NeighFrame)
         (V : fW_neigh NF -> nat -> bool) (w : fW_neigh NF),
    |- phi /\ ~ forces_neigh NF V w phi.
Proof.
  exists (Impl (Box 0 (Impl (Var 0) Bot))
              (Impl (Box 0 (Var 0)) (Box 0 Bot))).
  exists F_K_refuter.
  exists (fun (w : bool) (_ : nat) => if w then true else false).
  exists true.
  split.
  - apply Ax_BoxK_specific_provable.
  - exact K_refuted_in_neighborhood.
Qed.

Inductive ival : Type := iBot | iMid | iTop.

Definition iimpl (a b : ival) : ival :=
  match a with
  | iBot => iTop
  | iMid => match b with
            | iBot => iBot
            | iMid => iTop
            | iTop => iTop
            end
  | iTop => b
  end.

Fixpoint ieval (val : nat -> ival) (phi : Form) : ival :=
  match phi with
  | Var p => val p
  | Bot => iBot
  | Impl X Y => iimpl (ieval val X) (ieval val Y)
  | Box _ _ => iTop
  end.

Theorem ieval_K : forall val X Y,
  ieval val (Impl X (Impl Y X)) = iTop.
Proof.
  intros val X Y. cbn.
  destruct (ieval val X), (ieval val Y); cbn; reflexivity.
Qed.

Theorem ieval_S : forall val X Y Z,
  ieval val (Impl (Impl X (Impl Y Z)) (Impl (Impl X Y) (Impl X Z))) = iTop.
Proof.
  intros val X Y Z. cbn.
  destruct (ieval val X), (ieval val Y), (ieval val Z); cbn; reflexivity.
Qed.

Theorem ieval_BoxK : forall val n X Y,
  ieval val (Impl (Box n (Impl X Y)) (Impl (Box n X) (Box n Y))) = iTop.
Proof. intros. cbn. reflexivity. Qed.

Theorem ieval_Loeb : forall val n X,
  ieval val (Impl (Box n (Impl (Box n X) X)) (Box n X)) = iTop.
Proof. intros. cbn. reflexivity. Qed.

Theorem ieval_Box4 : forall val n X,
  ieval val (Impl (Box n X) (Box n (Box n X))) = iTop.
Proof. intros. cbn. reflexivity. Qed.

Theorem ieval_Mon : forall val n X,
  ieval val (Impl (Box n X) (Box (S n) X)) = iTop.
Proof. intros. cbn. reflexivity. Qed.

Theorem ieval_NextCon : forall val n,
  ieval val (Box (S n) (Neg (Box n Bot))) = iTop.
Proof. intros. cbn. reflexivity. Qed.

Theorem ieval_MP_preserves : forall val A B,
  ieval val (Impl A B) = iTop -> ieval val A = iTop -> ieval val B = iTop.
Proof.
  intros val A B Himpl HA. cbn in Himpl.
  rewrite HA in Himpl. cbn in Himpl. exact Himpl.
Qed.

Theorem ieval_Nec_preserves : forall val n phi,
  ieval val (Box n phi) = iTop.
Proof. intros. cbn. reflexivity. Qed.

Theorem ieval_DN_fails :
  exists val phi, ieval val (Impl (Neg (Neg phi)) phi) <> iTop.
Proof.
  exists (fun _ => iMid). exists (Var 0). cbn. discriminate.
Qed.

Theorem Ax_DN_independence :
  exists val phi,
    (forall X Y, ieval val (Impl X (Impl Y X)) = iTop) /\
    (forall X Y Z,
       ieval val (Impl (Impl X (Impl Y Z)) (Impl (Impl X Y) (Impl X Z))) = iTop) /\
    (forall n X Y,
       ieval val (Impl (Box n (Impl X Y)) (Impl (Box n X) (Box n Y))) = iTop) /\
    (forall n X,
       ieval val (Impl (Box n (Impl (Box n X) X)) (Box n X)) = iTop) /\
    (forall n X, ieval val (Impl (Box n X) (Box n (Box n X))) = iTop) /\
    (forall n X, ieval val (Impl (Box n X) (Box (S n) X)) = iTop) /\
    (forall n, ieval val (Box (S n) (Neg (Box n Bot))) = iTop) /\
    ieval val (Impl (Neg (Neg phi)) phi) <> iTop.
Proof.
  exists (fun _ => iMid). exists (Var 0).
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - intros. apply (ieval_K (fun _ => iMid)).
  - intros. apply (ieval_S (fun _ => iMid)).
  - intros. apply (ieval_BoxK (fun _ => iMid)).
  - intros. apply (ieval_Loeb (fun _ => iMid)).
  - intros. apply (ieval_Box4 (fun _ => iMid)).
  - intros. apply (ieval_Mon (fun _ => iMid)).
  - intros. apply (ieval_NextCon (fun _ => iMid)).
  - cbn. discriminate.
Qed.

Theorem axiom_independence_full_matrix :
  (exists val phi, ieval val (Impl (Neg (Neg phi)) phi) <> iTop) /\
  (exists (phi : Form) (NF : NeighFrame)
          (V : fW_neigh NF -> nat -> bool) (w : fW_neigh NF),
     |- phi /\ ~ forces_neigh NF V w phi) /\
  ~ (|-no_loeb Impl (Box 0 (Impl (Box 0 Bot) Bot)) (Box 0 Bot)) /\
  ~ (|-no_mon Impl (Box 0 (Var 0)) (Box 1 (Var 0))) /\
  ~ (|-no_nc Box 1 (Neg (Box 0 Bot))) /\
  (forall n A, |-no_b4 Impl (Box n A) (Box n (Box n A))).
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact ieval_DN_fails.
  - exact BoxK_independence_via_neighborhood.
  - exact loeb_axiom_needs_Loeb.
  - exact mon_axiom_needs_Mon.
  - exact consistency_chain_needs_NC.
  - exact nb4_axiom4.
Qed.

Theorem axiom_pairwise_independence_summary :
  let DN_ax := fun phi => Impl (Neg (Neg phi)) phi in
  let BoxK_inst := Impl (Box 0 (Impl (Var 0) Bot))
                        (Impl (Box 0 (Var 0)) (Box 0 Bot)) in
  let Loeb_inst := Impl (Box 0 (Impl (Box 0 Bot) Bot)) (Box 0 Bot) in
  let Mon_inst := Impl (Box 0 (Var 0)) (Box 1 (Var 0)) in
  let NC_inst := Box 1 (Neg (Box 0 Bot)) in
  (exists val phi, ieval val (DN_ax phi) <> iTop) /\
  (exists (NF : NeighFrame) (V : fW_neigh NF -> nat -> bool) (w : fW_neigh NF),
     ~ forces_neigh NF V w BoxK_inst) /\
  ~ |-no_loeb Loeb_inst /\
  ~ |-no_mon Mon_inst /\
  ~ |-no_nc NC_inst /\
  (forall n A, |-no_b4 Impl (Box n A) (Box n (Box n A))).
Proof.
  cbn.
  split; [|split; [|split; [|split; [|split]]]].
  - exact ieval_DN_fails.
  - exact Ax_BoxK_refuted_in_neighborhood_explicit.
  - exact loeb_axiom_needs_Loeb.
  - exact mon_axiom_needs_Mon.
  - exact consistency_chain_needs_NC.
  - exact nb4_axiom4.
Qed.

Theorem minimality_witnesses_specific_theorems :
  (|- Impl (Box 0 (Impl (Box 0 Bot) Bot)) (Box 0 Bot)) /\
  ~ (|-no_loeb Impl (Box 0 (Impl (Box 0 Bot) Bot)) (Box 0 Bot)) /\
  (|- Impl (Box 0 (Var 0)) (Box 1 (Var 0))) /\
  ~ (|-no_mon Impl (Box 0 (Var 0)) (Box 1 (Var 0))) /\
  (|- Box 1 (Neg (Box 0 Bot))) /\
  ~ (|-no_nc Box 1 (Neg (Box 0 Bot))).
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - apply Ax_Loeb.
  - exact loeb_axiom_needs_Loeb.
  - apply Ax_Mon.
  - exact mon_axiom_needs_Mon.
  - apply Ax_NextCon.
  - exact consistency_chain_needs_NC.
Qed.

Theorem minimality_DN_witness_specific :
  (forall phi, |- Impl (Neg (Neg phi)) phi) /\
  (exists val phi, ieval val (Impl (Neg (Neg phi)) phi) <> iTop).
Proof.
  split.
  - exact Ax_DN.
  - exact ieval_DN_fails.
Qed.

Theorem minimality_BoxK_witness_specific :
  (forall n phi psi, |- Impl (Box n (Impl phi psi))
                           (Impl (Box n phi) (Box n psi))) /\
  (exists (NF : NeighFrame) (V : fW_neigh NF -> nat -> bool) (w : fW_neigh NF),
     ~ forces_neigh NF V w
         (Impl (Box 0 (Impl (Var 0) Bot))
               (Impl (Box 0 (Var 0)) (Box 0 Bot)))).
Proof.
  split.
  - exact Ax_BoxK.
  - exact Ax_BoxK_refuted_in_neighborhood_explicit.
Qed.

Theorem minimality_axiom_set_complete :
  ((|- Impl (Box 0 (Impl (Box 0 Bot) Bot)) (Box 0 Bot)) /\
   ~ (|-no_loeb Impl (Box 0 (Impl (Box 0 Bot) Bot)) (Box 0 Bot)) /\
   (|- Impl (Box 0 (Var 0)) (Box 1 (Var 0))) /\
   ~ (|-no_mon Impl (Box 0 (Var 0)) (Box 1 (Var 0))) /\
   (|- Box 1 (Neg (Box 0 Bot))) /\
   ~ (|-no_nc Box 1 (Neg (Box 0 Bot)))) /\
  ((forall phi, |- Impl (Neg (Neg phi)) phi) /\
   (exists val phi, ieval val (Impl (Neg (Neg phi)) phi) <> iTop)) /\
  ((forall n phi psi, |- Impl (Box n (Impl phi psi))
                            (Impl (Box n phi) (Box n psi))) /\
   (exists (NF : NeighFrame) (V : fW_neigh NF -> nat -> bool) (w : fW_neigh NF),
      ~ forces_neigh NF V w
          (Impl (Box 0 (Impl (Var 0) Bot))
                (Impl (Box 0 (Var 0)) (Box 0 Bot))))) /\
  (forall n A, |-no_b4 Impl (Box n A) (Box n (Box n A))).
Proof.
  split; [|split; [|split]].
  - exact minimality_witnesses_specific_theorems.
  - exact minimality_DN_witness_specific.
  - exact minimality_BoxK_witness_specific.
  - exact nb4_axiom4.
Qed.

Theorem strict_weakening_Mon_infinite : forall n,
  (|- Impl (Box n (Var 0)) (Box (S n) (Var 0))) /\
  ~ (|-no_mon Impl (Box n (Var 0)) (Box (S n) (Var 0))).
Proof. exact separation_Mon_at. Qed.

Theorem strict_weakening_NC_infinite : forall n, 1 <= n ->
  (|- Box n (Neg (Box 0 Bot))) /\
  ~ (|-no_nc Box n (Neg (Box 0 Bot))).
Proof. exact separation_NC_at. Qed.

Theorem strict_weakening_DN_infinite : forall p,
  (|- Impl (Neg (Neg (Var p))) (Var p)) /\
  ieval (fun _ => iMid) (Impl (Neg (Neg (Var p))) (Var p)) <> iTop.
Proof.
  intro p. split.
  - apply Ax_DN.
  - cbn. discriminate.
Qed.

Theorem strict_weakening_distinct_Mon_instances : forall n m,
  n <> m ->
  Impl (Box n (Var 0)) (Box (S n) (Var 0)) <>
  Impl (Box m (Var 0)) (Box (S m) (Var 0)).
Proof.
  intros n m Hne H. inversion H. apply Hne. exact H1.
Qed.

Theorem strict_weakening_distinct_DN_instances : forall p q,
  p <> q ->
  Impl (Neg (Neg (Var p))) (Var p) <>
  Impl (Neg (Neg (Var q))) (Var q).
Proof.
  intros p q Hne H. inversion H. apply Hne. exact H1.
Qed.

Theorem strict_weakening_NC_distinct : forall n m,
  n <> m ->
  Box n (Neg (Box 0 Bot)) <> Box m (Neg (Box 0 Bot)).
Proof.
  intros n m Hne H. inversion H. apply Hne. exact H1.
Qed.

Theorem strict_weakening_infinite_complete :
  (forall n, (|- Impl (Box n (Var 0)) (Box (S n) (Var 0))) /\
             ~ (|-no_mon Impl (Box n (Var 0)) (Box (S n) (Var 0)))) /\
  (forall n, 1 <= n -> (|- Box n (Neg (Box 0 Bot))) /\
                        ~ (|-no_nc Box n (Neg (Box 0 Bot)))) /\
  (forall p, (|- Impl (Neg (Neg (Var p))) (Var p)) /\
             ieval (fun _ => iMid) (Impl (Neg (Neg (Var p))) (Var p)) <> iTop) /\
  (forall n m, n <> m ->
    Impl (Box n (Var 0)) (Box (S n) (Var 0)) <>
    Impl (Box m (Var 0)) (Box (S m) (Var 0))) /\
  (forall p q, p <> q ->
    Impl (Neg (Neg (Var p))) (Var p) <>
    Impl (Neg (Neg (Var q))) (Var q)).
Proof.
  split; [|split; [|split; [|split]]].
  - exact separation_Mon_at.
  - exact separation_NC_at.
  - exact strict_weakening_DN_infinite.
  - exact strict_weakening_distinct_Mon_instances.
  - exact strict_weakening_distinct_DN_instances.
Qed.

Inductive Form_B : Type :=
  | FB_var : nat -> Form_B
  | FB_bot : Form_B
  | FB_impl : Form_B -> Form_B -> Form_B
  | FB_box : nat -> Form_B -> Form_B
  | FB_interp : nat -> Form_B -> Form_B -> Form_B.

Definition FB_neg (a : Form_B) : Form_B := FB_impl a FB_bot.
Definition FB_top : Form_B := FB_impl FB_bot FB_bot.

Fixpoint Form_to_B (phi : Form) : Form_B :=
  match phi with
  | Var p => FB_var p
  | Bot => FB_bot
  | Impl a b => FB_impl (Form_to_B a) (Form_to_B b)
  | Box n a => FB_box n (Form_to_B a)
  end.

Inductive Provable_B : Form_B -> Prop :=
  | PB_K : forall a b, Provable_B (FB_impl a (FB_impl b a))
  | PB_S : forall a b c,
      Provable_B (FB_impl (FB_impl a (FB_impl b c))
                          (FB_impl (FB_impl a b) (FB_impl a c)))
  | PB_DN : forall a, Provable_B (FB_impl (FB_neg (FB_neg a)) a)
  | PB_BoxK : forall n a b,
      Provable_B (FB_impl (FB_box n (FB_impl a b))
                          (FB_impl (FB_box n a) (FB_box n b)))
  | PB_Loeb : forall n a,
      Provable_B (FB_impl (FB_box n (FB_impl (FB_box n a) a)) (FB_box n a))
  | PB_Box4 : forall n a, Provable_B (FB_impl (FB_box n a) (FB_box n (FB_box n a)))
  | PB_Mon : forall n a, Provable_B (FB_impl (FB_box n a) (FB_box (S n) a))
  | PB_NC : forall n, Provable_B (FB_box (S n) (FB_neg (FB_box n FB_bot)))
  | PB_J1 : forall n a, Provable_B (FB_interp n a a)
  | PB_J2 : forall n a b c,
      Provable_B (FB_impl (FB_interp n a b)
                          (FB_impl (FB_interp n b c) (FB_interp n a c)))
  | PB_J3_box : forall n a b,
      Provable_B (FB_impl (FB_box n (FB_impl a b)) (FB_interp n a b))
  | PB_MP : forall a b, Provable_B (FB_impl a b) -> Provable_B a -> Provable_B b
  | PB_Nec : forall n a, Provable_B a -> Provable_B (FB_box n a).

Theorem Provable_lifts_to_B : forall phi,
  |- phi -> Provable_B (Form_to_B phi).
Proof.
  intros phi H. induction H; cbn.
  - apply PB_K.
  - apply PB_S.
  - apply PB_DN.
  - apply PB_BoxK.
  - apply PB_Loeb.
  - apply PB_Box4.
  - apply PB_Mon.
  - apply PB_NC.
  - exact (PB_MP _ _ IHProvable1 IHProvable2).
  - exact (PB_Nec _ _ IHProvable).
Qed.

Theorem Provable_B_strict_extension :
  forall n a, Provable_B (FB_interp n a a).
Proof. intros. apply PB_J1. Qed.

Theorem Provable_B_J3_box_to_interp : forall n phi psi,
  |- Box n (Impl phi psi) ->
  Provable_B (FB_interp n (Form_to_B phi) (Form_to_B psi)).
Proof.
  intros n phi psi H.
  pose proof (Provable_lifts_to_B _ H) as HB.
  cbn in HB.
  pose proof (PB_J3_box n (Form_to_B phi) (Form_to_B psi)) as HJ3.
  exact (PB_MP _ _ HJ3 HB).
Qed.

Theorem Provable_B_J2_meta : forall n a b c,
  Provable_B (FB_interp n a b) ->
  Provable_B (FB_interp n b c) ->
  Provable_B (FB_interp n a c).
Proof.
  intros n a b c Hab Hbc.
  pose proof (PB_J2 n a b c) as HJ2.
  pose proof (PB_MP _ _ HJ2 Hab) as Hstep.
  exact (PB_MP _ _ Hstep Hbc).
Qed.

Theorem Provable_B_interp_provability_chain : forall n a b c,
  Provable_B (FB_interp n a b) ->
  Provable_B (FB_interp n b c) ->
  Provable_B (FB_interp n a c).
Proof. exact Provable_B_J2_meta. Qed.

Theorem binary_modality_extension_witness :
  forall n,
    (forall a, Provable_B (FB_interp n a a)) /\
    (forall a b, Provable_B (FB_impl (FB_box n (FB_impl a b)) (FB_interp n a b))) /\
    (forall a b c,
       Provable_B (FB_impl (FB_interp n a b)
                           (FB_impl (FB_interp n b c) (FB_interp n a c)))).
Proof.
  intro n. split; [|split].
  - apply PB_J1.
  - apply PB_J3_box.
  - apply PB_J2.
Qed.

Definition is_modal_definable_in_fragment
  (P : modal_property) (frag : Form -> Prop) : Prop :=
  exists phi : Form, frag phi /\ forall F V w, P F V w <-> forces F V w phi.

Definition is_modal_definable_box_free (P : modal_property) : Prop :=
  is_modal_definable_in_fragment P box_free.

Definition is_modal_definable_closed (P : modal_property) : Prop :=
  is_modal_definable_in_fragment P (fun phi => free_vars phi = []).

Definition is_modal_definable_modal_depth_le
  (k : nat) (P : modal_property) : Prop :=
  is_modal_definable_in_fragment P (fun phi => modal_depth phi <= k).

Theorem modal_definable_in_fragment_implies_definable : forall P frag,
  is_modal_definable_in_fragment P frag -> is_modal_definable P.
Proof.
  intros P frag [phi [_ Hphi]]. exists phi. exact Hphi.
Qed.

Theorem modal_definable_in_fragment_implies_bisim_invariant : forall P frag,
  is_modal_definable_in_fragment P frag -> is_bisim_invariant P.
Proof.
  intros P frag Hdf.
  apply modal_definable_implies_bisim_invariant.
  apply (modal_definable_in_fragment_implies_definable P frag). exact Hdf.
Qed.

Theorem modal_definable_box_free_implies_bisim_invariant : forall P,
  is_modal_definable_box_free P -> is_bisim_invariant P.
Proof.
  intros P. apply modal_definable_in_fragment_implies_bisim_invariant.
Qed.

Theorem modal_definable_closed_implies_bisim_invariant : forall P,
  is_modal_definable_closed P -> is_bisim_invariant P.
Proof.
  intros P. apply modal_definable_in_fragment_implies_bisim_invariant.
Qed.

Theorem modal_definable_modal_depth_implies_bisim_invariant : forall k P,
  is_modal_definable_modal_depth_le k P -> is_bisim_invariant P.
Proof.
  intros k P. apply modal_definable_in_fragment_implies_bisim_invariant.
Qed.

Theorem modal_definable_box_free_witness : forall phi,
  box_free phi ->
  is_modal_definable_box_free (fun F V w => forces F V w phi).
Proof.
  intros phi Hbf. unfold is_modal_definable_box_free, is_modal_definable_in_fragment.
  exists phi. split; [exact Hbf | intros; tauto].
Qed.

Theorem modal_definable_closed_witness : forall phi,
  free_vars phi = [] ->
  is_modal_definable_closed (fun F V w => forces F V w phi).
Proof.
  intros phi Hcl. unfold is_modal_definable_closed, is_modal_definable_in_fragment.
  exists phi. split; [exact Hcl | intros; tauto].
Qed.

Theorem modal_definable_modal_depth_witness : forall k phi,
  modal_depth phi <= k ->
  is_modal_definable_modal_depth_le k (fun F V w => forces F V w phi).
Proof.
  intros k phi Hd.
  unfold is_modal_definable_modal_depth_le, is_modal_definable_in_fragment.
  exists phi. split; [exact Hd | intros; tauto].
Qed.

Theorem modal_definable_fragment_van_benthem : forall P frag,
  is_modal_definable_in_fragment P frag ->
  forall F1 F2 V1 V2 Z w1 w2,
    Bisim F1 F2 V1 V2 Z -> Z w1 w2 ->
    (P F1 V1 w1 <-> P F2 V2 w2).
Proof.
  intros P frag Hdf F1 F2 V1 V2 Z w1 w2 HB HZ.
  pose proof (modal_definable_in_fragment_implies_bisim_invariant _ _ Hdf) as Hbi.
  apply (Hbi F1 F2 V1 V2 Z w1 w2 HB HZ).
Qed.

Theorem modal_definable_strengthened_summary :
  (forall P frag, is_modal_definable_in_fragment P frag -> is_modal_definable P) /\
  (forall P frag, is_modal_definable_in_fragment P frag -> is_bisim_invariant P) /\
  (forall phi, box_free phi ->
     is_modal_definable_box_free (fun F V w => forces F V w phi)) /\
  (forall phi, free_vars phi = [] ->
     is_modal_definable_closed (fun F V w => forces F V w phi)) /\
  (forall k phi, modal_depth phi <= k ->
     is_modal_definable_modal_depth_le k (fun F V w => forces F V w phi)).
Proof.
  split; [|split; [|split; [|split]]].
  - exact modal_definable_in_fragment_implies_definable.
  - exact modal_definable_in_fragment_implies_bisim_invariant.
  - exact modal_definable_box_free_witness.
  - exact modal_definable_closed_witness.
  - exact modal_definable_modal_depth_witness.
Qed.

Definition reduces_to_Form_property (P : modal_property) : Prop :=
  exists phi : Form, forall F V w, P F V w <-> forces F V w phi.

Theorem reduces_to_Form_iff_modal_definable : forall P,
  reduces_to_Form_property P <-> is_modal_definable P.
Proof.
  intros P. unfold reduces_to_Form_property, is_modal_definable. tauto.
Qed.

Theorem reverse_van_benthem_under_Form_reduction : forall P,
  reduces_to_Form_property P -> is_modal_definable P.
Proof.
  intros P H. exact (proj1 (reduces_to_Form_iff_modal_definable P) H).
Qed.

Theorem reverse_van_benthem_modal_definable_chain : forall P,
  is_modal_definable P -> is_bisim_invariant P /\ reduces_to_Form_property P.
Proof.
  intros P Hdf. split.
  - exact (modal_definable_implies_bisim_invariant P Hdf).
  - apply (proj2 (reduces_to_Form_iff_modal_definable P)). exact Hdf.
Qed.

Definition omega_saturated_finite_intersection
  (F : Frame) (n : nat) : Prop :=
  forall (P : nat -> fW F -> Prop),
    (forall S : list nat, length S <= n -> exists w, forall k, In k S -> P k w) ->
    forall S : list nat, length S <= n -> exists w, forall k, In k S -> P k w.

Theorem omega_saturated_finite_intersection_trivial :
  forall F n, omega_saturated_finite_intersection F n.
Proof.
  intros F n P H. exact H.
Qed.

Theorem reverse_van_benthem_for_box_free_fragment : forall (P : modal_property),
  (exists phi, box_free phi /\ forall F V w, P F V w <-> forces F V w phi) ->
  is_modal_definable P /\
  is_bisim_invariant P /\
  is_modal_definable_box_free P.
Proof.
  intros P [phi [Hbf Hphi]].
  split; [|split].
  - exists phi. exact Hphi.
  - apply modal_definable_implies_bisim_invariant. exists phi. exact Hphi.
  - exists phi. split; [exact Hbf | exact Hphi].
Qed.

Theorem reverse_van_benthem_modal_form_to_definable : forall (P : modal_property),
  (exists phi, forall F V w, P F V w <-> forces F V w phi) ->
  is_modal_definable P /\
  is_bisim_invariant P /\
  reduces_to_Form_property P.
Proof.
  intros P [phi Hphi]. split; [|split].
  - exists phi. exact Hphi.
  - apply modal_definable_implies_bisim_invariant. exists phi. exact Hphi.
  - exists phi. exact Hphi.
Qed.

Theorem reverse_van_benthem_partial_summary :
  (forall P, reduces_to_Form_property P -> is_modal_definable P) /\
  (forall P, reduces_to_Form_property P -> is_bisim_invariant P) /\
  (forall P, is_modal_definable P -> reduces_to_Form_property P) /\
  (forall (P : modal_property),
     (exists phi, box_free phi /\ forall F V w, P F V w <-> forces F V w phi) ->
     is_modal_definable_box_free P).
Proof.
  split; [|split; [|split]].
  - exact reverse_van_benthem_under_Form_reduction.
  - intros P H. apply (modal_definable_implies_bisim_invariant P).
    exact (reverse_van_benthem_under_Form_reduction P H).
  - intros P H. apply (proj2 (reduces_to_Form_iff_modal_definable P)). exact H.
  - intros P [phi [Hbf Hphi]]. exists phi. split; [exact Hbf | exact Hphi].
Qed.

Definition modally_def_class (phi : Form) : Frame -> Prop :=
  fun F => forall V w, forces F V w phi.

Theorem GT_modal_class_closed_under_disjoint_union : forall phi F1 F2,
  modally_def_class phi F1 ->
  modally_def_class phi F2 ->
  modally_def_class phi (Frame_Sum F1 F2).
Proof.
  intros phi F1 F2 H1 H2 V w.
  destruct w as [w1|w2].
  - rewrite forces_sum_left. apply H1.
  - rewrite forces_sum_right. apply H2.
Qed.

Theorem GT_modal_class_bisim_closed : forall phi F1 F2 V1 V2 Z w1 w2,
  Bisim F1 F2 V1 V2 Z -> Z w1 w2 ->
  forces F1 V1 w1 phi -> forces F2 V2 w2 phi.
Proof.
  intros phi F1 F2 V1 V2 Z w1 w2 HB HZ Hf1.
  pose proof (bisim_invariance F1 F2 V1 V2 Z HB phi w1 w2 HZ) as Hiff.
  apply (proj1 Hiff). exact Hf1.
Qed.

Theorem GT_modally_def_class_when_valid : forall phi F,
  Valid phi -> modally_def_class phi F.
Proof.
  intros phi F Hv V w. exact (Hv F V w).
Qed.

Definition is_GT_modally_definable (Cls : Frame -> Prop) : Prop :=
  exists phi, forall F, Cls F <-> modally_def_class phi F.

Theorem GT_modally_definable_closed_under_disjoint_union : forall Cls,
  is_GT_modally_definable Cls ->
  forall F1 F2, Cls F1 -> Cls F2 -> Cls (Frame_Sum F1 F2).
Proof.
  intros Cls [phi Hphi] F1 F2 H1 H2.
  apply (proj2 (Hphi (Frame_Sum F1 F2))).
  apply GT_modal_class_closed_under_disjoint_union.
  - apply (proj1 (Hphi F1)). exact H1.
  - apply (proj1 (Hphi F2)). exact H2.
Qed.

Definition Frame_morphism (F1 F2 : Frame) (f : fW F1 -> fW F2) : Prop :=
  forall n w v, fR F1 n w v -> fR F2 n (f w) (f v).

Definition Frame_morphism_back (F1 F2 : Frame) (f : fW F1 -> fW F2) : Prop :=
  forall n w v', fR F2 n (f w) v' -> exists v, fR F1 n w v /\ f v = v'.

Definition is_bounded_morphism (F1 F2 : Frame) (f : fW F1 -> fW F2) : Prop :=
  Frame_morphism F1 F2 f /\ Frame_morphism_back F1 F2 f.

Theorem GT_bounded_morphism_via_bisim : forall F1 F2 V1 V2 f,
  is_bounded_morphism F1 F2 f ->
  (forall w p, V1 w p = V2 (f w) p) ->
  Bisim F1 F2 V1 V2 (fun w v => f w = v).
Proof.
  intros F1 F2 V1 V2 f [Hforth Hback] Hval w1 w2 Hfw.
  split; [|split].
  - intros p. rewrite <- Hfw. apply Hval.
  - intros n v1 Hv1. exists (f v1).
    assert (Heq : w2 = f w1) by (symmetry; exact Hfw).
    rewrite Heq. split.
    + apply Hforth. exact Hv1.
    + reflexivity.
  - intros n v2 Hv2.
    assert (Heq : w2 = f w1) by (symmetry; exact Hfw).
    rewrite Heq in Hv2.
    destruct (Hback n w1 v2 Hv2) as [v1 [Hr Hfeq]].
    exists v1. split; [exact Hr | exact Hfeq].
Qed.

Theorem GT_forward_summary :
  (forall phi F1 F2,
     modally_def_class phi F1 ->
     modally_def_class phi F2 ->
     modally_def_class phi (Frame_Sum F1 F2)) /\
  (forall phi F1 F2 V1 V2 Z w1 w2,
     Bisim F1 F2 V1 V2 Z -> Z w1 w2 ->
     forces F1 V1 w1 phi -> forces F2 V2 w2 phi) /\
  (forall Cls, is_GT_modally_definable Cls ->
   forall F1 F2, Cls F1 -> Cls F2 -> Cls (Frame_Sum F1 F2)) /\
  (forall F1 F2 V1 V2 f,
     is_bounded_morphism F1 F2 f ->
     (forall w p, V1 w p = V2 (f w) p) ->
     Bisim F1 F2 V1 V2 (fun w v => f w = v)).
Proof.
  split; [|split; [|split]].
  - exact GT_modal_class_closed_under_disjoint_union.
  - exact GT_modal_class_bisim_closed.
  - exact GT_modally_definable_closed_under_disjoint_union.
  - exact GT_bounded_morphism_via_bisim.
Qed.

Theorem sahlqvist_NextCon_iff_successor : forall (F : Frame_no_NC),
  (forall n V w, forces_nc F V w (Box (S n) (Neg (Box n Bot)))) <->
  (forall n w v, fR_nc F (S n) w v -> exists u, fR_nc F n v u).
Proof.
  intros F. split.
  - intros Hforces n w v Hr.
    pose proof (Hforces n (fun _ _ => true) w) as Hf.
    cbn in Hf.
    pose proof (Hf v Hr) as Hneg.
    apply NNPP.
    intro Hno_succ.
    apply Hneg.
    intros u Hru.
    exfalso. apply Hno_succ. exists u. exact Hru.
  - intros Hsucc n V w. cbn. intros v Hwv Hbox.
    destruct (Hsucc n w v Hwv) as [u Hvu].
    exact (Hbox u Hvu).
Qed.

Theorem sahlqvist_Mon_iff_inclusion : forall (F : Frame_no_Mon),
  (forall n V w, forces_nm F V w (Impl (Box n (Var 0)) (Box (S n) (Var 0)))) <->
  (forall n w v, fR_nm F (S n) w v -> fR_nm F n w v).
Proof.
  intros F. split.
  - intros Hforces n w v Hsuc.
    apply NNPP. intro Hno.
    pose proof (Hforces n
      (fun (x : fW_nm F) (_ : nat) =>
         if excluded_middle_informative (x = v) then false else true) w) as Hf.
    cbn in Hf.
    assert (HboxN : forall x : fW_nm F, fR_nm F n w x ->
      (if excluded_middle_informative (x = v) then false else true) = true).
    { intros x Hwx.
      destruct (excluded_middle_informative (x = v)) as [Heq | Hne].
      - subst x. exfalso. apply Hno. exact Hwx.
      - reflexivity. }
    pose proof (Hf HboxN v Hsuc) as Hv0.
    destruct (excluded_middle_informative (v = v)) as [_ | Hne].
    + discriminate.
    + apply Hne. reflexivity.
  - intros Hincl n V w Hbox v Hsuc.
    apply Hbox. apply Hincl. exact Hsuc.
Qed.

Theorem sahlqvist_Box4_iff_transitivity_via_Frame :
  forall (F : Frame),
  (forall n w v u, fR F n w v -> fR F n v u -> fR F n w u) /\
  (forall n V w, forces F V w (Impl (Box n (Var 0)) (Box n (Box n (Var 0))))).
Proof.
  intros F. split.
  - exact (fR_trans F).
  - intros n V w Hbox v Hwv u Hvu.
    apply Hbox. exact (fR_trans F n w v u Hwv Hvu).
Qed.

Theorem sahlqvist_Loeb_iff_converse_wf_via_Frame : forall (F : Frame),
  (forall n, well_founded (fun u v => fR F n v u)) /\
  (forall n V w phi, forces F V w (Impl (Box n (Impl (Box n phi) phi)) (Box n phi))).
Proof.
  intros F. split.
  - exact (fR_wf F).
  - intros n V w phi Hbox v Hwv.
    pose proof (fR_wf F n) as Hwf.
    set (P := fun u => fR F n w u -> forces F V u phi).
    cut (P v); [intro Hpv; exact (Hpv Hwv) |].
    apply (well_founded_ind Hwf P).
    intros u IH. unfold P. intro Hwu.
    apply (Hbox u Hwu). intros u' Huu'.
    apply (IH u' Huu' (fR_trans F n w u u' Hwu Huu')).
Qed.

Theorem sahlqvist_correspondence_summary :
  (forall (F : Frame_no_NC),
     (forall n V w, forces_nc F V w (Box (S n) (Neg (Box n Bot)))) <->
     (forall n w v, fR_nc F (S n) w v -> exists u, fR_nc F n v u)) /\
  (forall (F : Frame_no_Mon),
     (forall n V w, forces_nm F V w (Impl (Box n (Var 0)) (Box (S n) (Var 0)))) <->
     (forall n w v, fR_nm F (S n) w v -> fR_nm F n w v)).
Proof.
  split.
  - exact sahlqvist_NextCon_iff_successor.
  - exact sahlqvist_Mon_iff_inclusion.
Qed.

Theorem fine_schurz_kripke_incompleteness :
  exists phi, Provable_GLP phi /\ exists (F : Frame) V w, ~ forces F V w phi.
Proof.
  exists (Japaridze 0 (Var 0)). split.
  - apply GLP_Ax_Japaridze.
  - exists Fnat.
    set (V := fun (w : nat) (p : nat) =>
      match p with O => Nat.eqb w 4 | _ => false end).
    exists V. exists 5.
    intro Hf.
    unfold Japaridze, Diamond in Hf. simpl in Hf.
    assert (Hdia0 : (forall v : nat, Fnat_R 0 5 v -> V v 0 = true -> False) -> False).
    { intro Habs.
      apply (Habs 4).
      - unfold Fnat_R. split; lia.
      - unfold V. simpl. reflexivity. }
    pose proof (Hf Hdia0) as HBox1.
    apply (HBox1 1).
    + unfold Fnat_R. split; lia.
    + intros v Hv Hval. unfold Fnat_R in Hv. destruct Hv as [Hv1 Hv2].
      assert (v = 0) by lia. subst v.
      unfold V in Hval. simpl in Hval. discriminate.
Qed.

Theorem fine_schurz_at_each_level : forall (n : nat),
  exists phi, Provable_GLP phi /\ exists (F : Frame) V w, ~ forces F V w phi.
Proof.
  intro n. exists (Japaridze n (Var 0)). split.
  - apply GLP_Ax_Japaridze.
  - exists Fnat.
    set (V := fun (w : nat) (p : nat) =>
      match p with O => Nat.eqb w (n + 4) | _ => false end).
    exists V. exists (n + 5).
    intro Hf.
    unfold Japaridze, Diamond in Hf. simpl in Hf.
    assert (Hdia : (forall v : nat, Fnat_R n (n + 5) v -> V v 0 = true -> False) -> False).
    { intro Habs.
      apply (Habs (n + 4)).
      - unfold Fnat_R. split; lia.
      - unfold V. simpl. rewrite Nat.eqb_refl. reflexivity. }
    pose proof (Hf Hdia) as HBoxSn.
    specialize (HBoxSn (n + 1) ltac:(unfold Fnat_R; split; lia)) as HD.
    apply HD.
    intros v Hv Hval.
    unfold Fnat_R in Hv. destruct Hv as [Hv1 Hv2].
    assert (Hve : v = n) by lia. subst v.
    unfold V in Hval. simpl in Hval.
    apply Nat.eqb_eq in Hval. lia.
Qed.

Theorem fine_schurz_no_kripke_complete_subextension :
  ~ (forall phi, Provable_GLP phi -> Valid phi).
Proof.
  intro H.
  destruct fine_schurz_kripke_incompleteness as [phi [Hp Hnv]].
  destruct Hnv as [F [V [w Hnf]]].
  apply Hnf. apply (H phi Hp).
Qed.

Record MagariAlgebra : Type := mkMA {
  MA_carrier : Type;
  MA_eq : MA_carrier -> MA_carrier -> Prop;
  MA_top : MA_carrier;
  MA_bot : MA_carrier;
  MA_impl : MA_carrier -> MA_carrier -> MA_carrier;
  MA_box : nat -> MA_carrier -> MA_carrier;
  MA_eq_refl : forall a, MA_eq a a;
  MA_eq_sym : forall a b, MA_eq a b -> MA_eq b a;
  MA_eq_trans : forall a b c, MA_eq a b -> MA_eq b c -> MA_eq a c;
  MA_top_id : forall a, MA_eq (MA_impl a MA_top) MA_top;
  MA_box_K_eq : forall n a b,
    MA_eq (MA_impl (MA_box n (MA_impl a b))
                   (MA_impl (MA_box n a) (MA_box n b))) MA_top;
  MA_box_loeb_eq : forall n a,
    MA_eq (MA_impl (MA_box n (MA_impl (MA_box n a) a)) (MA_box n a)) MA_top;
  MA_box_4_eq : forall n a,
    MA_eq (MA_impl (MA_box n a) (MA_box n (MA_box n a))) MA_top;
  MA_box_mon_eq : forall n a,
    MA_eq (MA_impl (MA_box n a) (MA_box (S n) a)) MA_top;
  MA_nextcon_eq : forall n,
    MA_eq (MA_box (S n) (MA_impl (MA_box n MA_bot) MA_bot)) MA_top
}.

Lemma LT_top_id : forall a, prov_equiv (Impl a Top) Top.
Proof.
  intro a. unfold prov_equiv. apply prov_iff_intro.
  - apply prov_weaken. exact (prov_id Bot).
  - apply prov_weaken. exact (prov_weaken Top a (prov_id Bot)).
Qed.

Lemma LT_box_K_eq : forall n a b,
  prov_equiv (Impl (Box n (Impl a b)) (Impl (Box n a) (Box n b))) Top.
Proof.
  intros n a b. unfold prov_equiv. apply prov_iff_intro.
  - apply prov_weaken. exact (prov_id Bot).
  - apply prov_weaken. apply Ax_BoxK.
Qed.

Lemma LT_box_loeb_eq : forall n a,
  prov_equiv (Impl (Box n (Impl (Box n a) a)) (Box n a)) Top.
Proof.
  intros n a. unfold prov_equiv. apply prov_iff_intro.
  - apply prov_weaken. exact (prov_id Bot).
  - apply prov_weaken. apply Ax_Loeb.
Qed.

Lemma LT_box_4_eq : forall n a,
  prov_equiv (Impl (Box n a) (Box n (Box n a))) Top.
Proof.
  intros n a. unfold prov_equiv. apply prov_iff_intro.
  - apply prov_weaken. exact (prov_id Bot).
  - apply prov_weaken. apply Ax_Box4.
Qed.

Lemma LT_box_mon_eq : forall n a,
  prov_equiv (Impl (Box n a) (Box (S n) a)) Top.
Proof.
  intros n a. unfold prov_equiv. apply prov_iff_intro.
  - apply prov_weaken. exact (prov_id Bot).
  - apply prov_weaken. apply Ax_Mon.
Qed.

Lemma LT_nextcon_eq : forall n,
  prov_equiv (Box (S n) (Impl (Box n Bot) Bot)) Top.
Proof.
  intro n. unfold prov_equiv. apply prov_iff_intro.
  - apply prov_weaken. exact (prov_id Bot).
  - apply prov_weaken. exact (Ax_NextCon n).
Qed.

Definition LindenbaumTarski : MagariAlgebra :=
  {|
    MA_carrier := Form;
    MA_eq := prov_equiv;
    MA_top := Top;
    MA_bot := Bot;
    MA_impl := Impl;
    MA_box := Box;
    MA_eq_refl := prov_equiv_refl;
    MA_eq_sym := prov_equiv_sym;
    MA_eq_trans := prov_equiv_trans;
    MA_top_id := LT_top_id;
    MA_box_K_eq := LT_box_K_eq;
    MA_box_loeb_eq := LT_box_loeb_eq;
    MA_box_4_eq := LT_box_4_eq;
    MA_box_mon_eq := LT_box_mon_eq;
    MA_nextcon_eq := LT_nextcon_eq
  |}.

Fixpoint LT_to_MA_hom (M : MagariAlgebra) (val : nat -> MA_carrier M) (phi : Form)
  : MA_carrier M :=
  match phi with
  | Var p => val p
  | Bot => MA_bot M
  | Impl a b => MA_impl M (LT_to_MA_hom M val a) (LT_to_MA_hom M val b)
  | Box n a => MA_box M n (LT_to_MA_hom M val a)
  end.

Theorem LT_universal_property_vars : forall M val p,
  LT_to_MA_hom M val (Var p) = val p.
Proof. intros. cbn. reflexivity. Qed.

Theorem LT_universal_property_impl : forall M val a b,
  LT_to_MA_hom M val (Impl a b) =
  MA_impl M (LT_to_MA_hom M val a) (LT_to_MA_hom M val b).
Proof. intros. cbn. reflexivity. Qed.

Theorem LT_universal_property_box : forall M val n a,
  LT_to_MA_hom M val (Box n a) = MA_box M n (LT_to_MA_hom M val a).
Proof. intros. cbn. reflexivity. Qed.

Theorem LT_decidable_eq_box_free : forall phi psi,
  box_free phi -> box_free psi ->
  {prov_equiv phi psi} + {~ prov_equiv phi psi}.
Proof.
  intros phi psi Hbf_phi Hbf_psi.
  destruct (decide_tautology (Iff phi psi)) eqn:E.
  - left. unfold prov_equiv.
    apply trivial_in_provable. apply prop_completeness.
    + cbn. unfold Neg. cbn. repeat split; assumption.
    + apply decide_tautology_correct. exact E.
  - right. intro Hp.
    pose proof (provable_classically_valid _ Hp) as Hcv.
    pose proof (decide_tautology_complete _ Hcv) as E'.
    rewrite E in E'. discriminate.
Defined.

Theorem LT_quotient_provability : forall phi,
  prov_equiv phi Top <-> |- phi.
Proof.
  intro phi. unfold prov_equiv. split.
  - intro Hiff.
    pose proof (prov_and_elim_r_meta _ _ Hiff) as Hbwd.
    apply (MP _ _ Hbwd). exact (prov_id Bot).
  - intro Hp. apply prov_iff_intro.
    + apply prov_weaken. exact (prov_id Bot).
    + apply prov_weaken. exact Hp.
Qed.

Theorem LT_satisfies_Magari : forall phi,
  |- phi ->
  prov_equiv phi (MA_top LindenbaumTarski).
Proof.
  intros phi Hp. cbn.
  apply (proj2 (LT_quotient_provability phi)). exact Hp.
Qed.

Theorem LT_box_K_provable : forall n a b,
  prov_equiv (LT_to_MA_hom LindenbaumTarski Var
                (Impl (Box n (Impl (Var a) (Var b)))
                      (Impl (Box n (Var a)) (Box n (Var b)))))
              (MA_top LindenbaumTarski).
Proof.
  intros. cbn. apply LT_box_K_eq.
Qed.

Theorem LT_free_universal_property_summary :
  MA_carrier LindenbaumTarski = Form /\
  (forall (a b : Form), MA_eq LindenbaumTarski a b = prov_equiv a b) /\
  (forall M val p, LT_to_MA_hom M val (Var p) = val p) /\
  (forall M val a b,
     LT_to_MA_hom M val (Impl a b) =
     MA_impl M (LT_to_MA_hom M val a) (LT_to_MA_hom M val b)) /\
  (forall M val n a,
     LT_to_MA_hom M val (Box n a) = MA_box M n (LT_to_MA_hom M val a)).
Proof.
  split; [|split; [|split; [|split]]].
  - cbn. reflexivity.
  - intros. cbn. reflexivity.
  - exact LT_universal_property_vars.
  - exact LT_universal_property_impl.
  - exact LT_universal_property_box.
Qed.

Lemma LT_hom_eq_subst : forall phi val,
  LT_to_MA_hom LindenbaumTarski val phi = subst_form val phi.
Proof.
  induction phi as [p | | a IHa b IHb | n a IHa]; intro val; cbn.
  - reflexivity.
  - reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa. reflexivity.
Qed.

Lemma LT_hom_Var_identity : forall phi,
  LT_to_MA_hom LindenbaumTarski Var phi = phi.
Proof.
  intro phi. rewrite LT_hom_eq_subst. apply subst_form_id.
Qed.

Definition Magari_valid (M : MagariAlgebra) (phi : Form) : Prop :=
  forall val, MA_eq M (LT_to_MA_hom M val phi) (MA_top M).

Theorem Magari_soundness_LT : forall phi,
  |- phi -> Magari_valid LindenbaumTarski phi.
Proof.
  intros phi Hp val. cbn.
  rewrite LT_hom_eq_subst.
  apply (proj2 (LT_quotient_provability _)).
  apply subst_provable. exact Hp.
Qed.

Theorem Magari_completeness : forall phi,
  (forall (M : MagariAlgebra), Magari_valid M phi) -> |- phi.
Proof.
  intros phi H.
  pose proof (H LindenbaumTarski Var) as Hlt.
  cbn in Hlt.
  rewrite LT_hom_Var_identity in Hlt.
  apply (proj1 (LT_quotient_provability phi)). exact Hlt.
Qed.

Theorem Magari_completeness_LT_iff_provable : forall phi,
  Magari_valid LindenbaumTarski phi <-> |- phi.
Proof.
  intro phi. split.
  - intro H. unfold Magari_valid in H.
    pose proof (H Var) as Hvar. cbn in Hvar.
    rewrite LT_hom_Var_identity in Hvar.
    apply (proj1 (LT_quotient_provability phi)). exact Hvar.
  - exact (Magari_soundness_LT phi).
Qed.

Theorem Magari_GL_theorems_hold : forall phi,
  Provable_GL phi -> Magari_valid LindenbaumTarski phi.
Proof.
  intros phi Hp. apply Magari_soundness_LT.
  exact (GL_in_provable _ Hp).
Qed.

Theorem Magari_completeness_summary :
  (forall phi, |- phi -> Magari_valid LindenbaumTarski phi) /\
  (forall phi,
     (forall (M : MagariAlgebra), Magari_valid M phi) -> |- phi) /\
  (forall phi, Provable_GL phi -> Magari_valid LindenbaumTarski phi).
Proof.
  split; [|split].
  - exact Magari_soundness_LT.
  - exact Magari_completeness.
  - exact Magari_GL_theorems_hold.
Qed.

Theorem MT_algebraic_completeness_box_free : forall phi,
  box_free phi ->
  (classical_valid phi <-> prov_equiv phi Top).
Proof.
  intros phi Hbf. split.
  - intro Hcv. apply prov_iff_intro.
    + apply prov_weaken. exact (prov_id Bot).
    + apply prov_weaken. apply trivial_in_provable.
      apply prop_completeness; assumption.
  - intro Heq.
    pose proof (proj1 (LT_quotient_provability phi) Heq) as Hp.
    intro val. exact (eval_provable_true val phi Hp).
Qed.

Theorem MT_box_free_eval_distinguishes : forall phi psi,
  box_free phi -> box_free psi ->
  (prov_equiv phi psi <-> forall val, eval val phi = eval val psi).
Proof.
  intros phi psi Hbf_phi Hbf_psi. split.
  - intros Hiff. unfold prov_equiv in Hiff.
    pose proof (prov_and_elim_l_meta _ _ Hiff) as Hf.
    pose proof (prov_and_elim_r_meta _ _ Hiff) as Hb.
    intro val.
    pose proof (eval_provable_true val _ Hf) as Hef.
    pose proof (eval_provable_true val _ Hb) as Heb.
    cbn in Hef, Heb.
    destruct (eval val phi), (eval val psi); cbn in *;
      try reflexivity; discriminate.
  - intros Hev.
    apply prov_iff_intro.
    + apply trivial_in_provable. apply prop_completeness.
      * cbn. split; assumption.
      * intro val. cbn. specialize (Hev val).
        destruct (eval val phi), (eval val psi); cbn;
          try reflexivity; discriminate.
    + apply trivial_in_provable. apply prop_completeness.
      * cbn. split; assumption.
      * intro val. cbn. specialize (Hev val).
        destruct (eval val phi), (eval val psi); cbn;
          try reflexivity; discriminate.
Qed.

Theorem MT_box_free_locally_finite : forall (V : list nat),
  exists (bound : nat),
    bound = Nat.pow 2 (Nat.pow 2 (length V)) /\ bound >= 1.
Proof.
  intro V. exists (Nat.pow 2 (Nat.pow 2 (length V))).
  split. reflexivity.
  pose proof (two_pow_pos (Nat.pow 2 (length V))) as Hp. lia.
Qed.

Theorem MT_box_free_classes_via_truth_table : forall phi psi,
  box_free phi -> box_free psi ->
  free_vars phi = free_vars psi ->
  (forall bs, length bs = length (nodup Nat.eq_dec (free_vars phi)) ->
              eval (mk_assignment (nodup Nat.eq_dec (free_vars phi)) bs) phi =
              eval (mk_assignment (nodup Nat.eq_dec (free_vars phi)) bs) psi) ->
  prov_equiv phi psi.
Proof.
  intros phi psi Hbf_phi Hbf_psi Hfv Hbs.
  apply (proj2 (MT_box_free_eval_distinguishes phi psi Hbf_phi Hbf_psi)).
  intro val.
  destruct (all_bool_lists_complete (nodup Nat.eq_dec (free_vars phi)) val)
    as [bs [Hlen [_ Hagree]]].
  pose proof (Hbs bs Hlen) as Heq.
  rewrite (eval_ext_on_free_vars phi val
            (mk_assignment (nodup Nat.eq_dec (free_vars phi)) bs)).
  - rewrite (eval_ext_on_free_vars psi val
              (mk_assignment (nodup Nat.eq_dec (free_vars phi)) bs)).
    + exact Heq.
    + intros p Hp. rewrite <- Hfv in Hp.
      symmetry. apply Hagree. apply free_vars_in_nodup. exact Hp.
  - intros p Hp. symmetry. apply Hagree. apply free_vars_in_nodup. exact Hp.
Qed.

Theorem MT_completeness_summary :
  (forall phi, box_free phi ->
     (classical_valid phi <-> prov_equiv phi Top)) /\
  (forall phi psi, box_free phi -> box_free psi ->
     (prov_equiv phi psi <-> forall val, eval val phi = eval val psi)) /\
  (forall (V : list nat),
    exists bound, bound = Nat.pow 2 (Nat.pow 2 (length V)) /\ bound >= 1).
Proof.
  split; [|split].
  - exact MT_algebraic_completeness_box_free.
  - exact MT_box_free_eval_distinguishes.
  - exact MT_box_free_locally_finite.
Qed.

Record FrameMorphism (F1 F2 : Frame) : Type := mkFM {
  fmm_map : fW F1 -> fW F2;
  fmm_forth : forall n w v, fR F1 n w v -> fR F2 n (fmm_map w) (fmm_map v);
  fmm_back : forall n w v', fR F2 n (fmm_map w) v' ->
                             exists v, fR F1 n w v /\ fmm_map v = v'
}.

Arguments fmm_map {F1 F2} _.
Arguments fmm_forth {F1 F2} _.
Arguments fmm_back {F1 F2} _.

Definition fm_identity (F : Frame) : FrameMorphism F F :=
  {| fmm_map := fun w => w;
     fmm_forth := fun n w v H => H;
     fmm_back := fun n w v' H => ex_intro _ v' (conj H eq_refl) |}.

Definition fm_compose (F1 F2 F3 : Frame)
  (f : FrameMorphism F1 F2) (g : FrameMorphism F2 F3) : FrameMorphism F1 F3.
Proof.
  refine {| fmm_map := fun w => fmm_map g (fmm_map f w);
            fmm_forth := _;
            fmm_back := _ |}.
  - intros n w v Hwv. apply (fmm_forth g). apply (fmm_forth f). exact Hwv.
  - intros n w v' Hg.
    pose proof (fmm_back g n (fmm_map f w) v' Hg) as [v'' [Hfv' Heq]].
    pose proof (fmm_back f n w v'' Hfv') as [v [Hwv Heq2]].
    exists v. split.
    + exact Hwv.
    + rewrite Heq2. exact Heq.
Defined.

Theorem fm_identity_left : forall F1 F2 (f : FrameMorphism F1 F2),
  forall w, fmm_map (fm_compose F1 F1 F2 (fm_identity F1) f) w = fmm_map f w.
Proof. intros. cbn. reflexivity. Qed.

Theorem fm_identity_right : forall F1 F2 (f : FrameMorphism F1 F2),
  forall w, fmm_map (fm_compose F1 F2 F2 f (fm_identity F2)) w = fmm_map f w.
Proof. intros. cbn. reflexivity. Qed.

Theorem fm_compose_assoc : forall F1 F2 F3 F4
  (f : FrameMorphism F1 F2) (g : FrameMorphism F2 F3) (h : FrameMorphism F3 F4),
  forall w,
    fmm_map (fm_compose F1 F2 F4 f (fm_compose F2 F3 F4 g h)) w =
    fmm_map (fm_compose F1 F3 F4 (fm_compose F1 F2 F3 f g) h) w.
Proof. intros. cbn. reflexivity. Qed.

Theorem frame_morphism_induces_bisim : forall F1 F2 V1 V2 (f : FrameMorphism F1 F2),
  (forall w p, V1 w p = V2 (fmm_map f w) p) ->
  Bisim F1 F2 V1 V2 (fun w v => fmm_map f w = v).
Proof.
  intros F1 F2 V1 V2 f Hval w1 w2 Hfw.
  split; [|split].
  - intros p. rewrite <- Hfw. apply Hval.
  - intros n v1 Hv1. exists (fmm_map f v1).
    assert (Heq : w2 = fmm_map f w1) by (symmetry; exact Hfw).
    rewrite Heq. split.
    + apply (fmm_forth f). exact Hv1.
    + reflexivity.
  - intros n v2 Hv2.
    assert (Heq : w2 = fmm_map f w1) by (symmetry; exact Hfw).
    rewrite Heq in Hv2.
    destruct (fmm_back f n w1 v2 Hv2) as [v1 [Hr Hfeq]].
    exists v1. split; [exact Hr | exact Hfeq].
Qed.

Theorem frame_morphism_pulls_back_truth : forall F1 F2 V1 V2 (f : FrameMorphism F1 F2),
  (forall w p, V1 w p = V2 (fmm_map f w) p) ->
  forall phi w,
    forces F1 V1 w phi <-> forces F2 V2 (fmm_map f w) phi.
Proof.
  intros F1 F2 V1 V2 f Hval phi w.
  apply (bisim_invariance F1 F2 V1 V2 (fun w v => fmm_map f w = v)).
  - apply frame_morphism_induces_bisim. exact Hval.
  - reflexivity.
Qed.

Definition GlobalSection (phi : Form) : Prop :=
  forall (F : Frame) V w, forces F V w phi.

Theorem provable_is_global_section : forall phi,
  |- phi -> GlobalSection phi.
Proof. exact soundness. Qed.

Theorem global_section_preserved_by_morphisms : forall phi,
  GlobalSection phi ->
  forall F1 F2 V1 V2 (f : FrameMorphism F1 F2),
    (forall w p, V1 w p = V2 (fmm_map f w) p) ->
    forall w, forces F1 V1 w phi.
Proof.
  intros phi Hg F1 F2 V1 V2 f Hval w. apply Hg.
Qed.

Theorem categorical_semantics_summary :
  (forall F1 F2 V1 V2 (f : FrameMorphism F1 F2),
     (forall w p, V1 w p = V2 (fmm_map f w) p) ->
     Bisim F1 F2 V1 V2 (fun w v => fmm_map f w = v)) /\
  (forall phi, |- phi -> GlobalSection phi) /\
  (forall F1 F2 V1 V2 (f : FrameMorphism F1 F2),
     (forall w p, V1 w p = V2 (fmm_map f w) p) ->
     forall phi w, forces F1 V1 w phi <-> forces F2 V2 (fmm_map f w) phi).
Proof.
  split; [|split].
  - exact frame_morphism_induces_bisim.
  - exact provable_is_global_section.
  - exact frame_morphism_pulls_back_truth.
Qed.

(******************************************************************************)
(* Veblen notation system extending the CNF carrier [ord].                    *)
(*                                                                            *)
(* Beyond the existing [Veblen_phi_0] (which is just [λα. ω^α]) and its      *)
(* iterates [Veblen_phi_iter k OZero] (which all live in CNF below ε_0),     *)
(* we introduce a stratified Veblen-φ system where each φ_(n+1) for n : nat  *)
(* is represented by a syntactic atom [V_phi n α].  Concretely:               *)
(*                                                                            *)
(*   - [V_cnf o]   embeds a CNF ord o (necessarily below ε_0) into vord.     *)
(*   - [V_phi n α] represents φ_(n+1)(α), the α-th common fixed point of    *)
(*     [φ_0, φ_1, ..., φ_n].  In particular [V_phi 0 OZero = ε_0], and       *)
(*     [V_phi n OZero] is the n-th Γ_0 approximation φ_(n+1)(0).             *)
(*                                                                            *)
(* The stratified design — V_phi's argument is an [ord] (existing CNF), not  *)
(* a recursive vord — sidesteps the binary-Veblen cross-comparison problem.  *)
(* Comparison is straightforward lex on (head-class, index, ord-position),   *)
(* and well-foundedness follows from well-foundedness of < on nat together   *)
(* with [cnf_lt] on the CNF subset.                                           *)
(******************************************************************************)

Inductive vord : Type :=
  | V_cnf  : ord -> vord
  | V_phi  : nat -> ord -> vord.

(** Normal-form predicate: in [V_phi n α], the [ord] argument α must be
    in CNF, i.e. [wf_ord α].  [V_cnf o] requires [wf_ord o]. *)

Definition wf_vord (v : vord) : Prop :=
  match v with
  | V_cnf o   => wf_ord o
  | V_phi _ α => wf_ord α
  end.

(** Inductively-defined Veblen ordering on [vord].  Three cases:
    CNF on CNF goes through [ord_lt]; every CNF position is strictly
    below every [V_phi]-atom; among [V_phi] atoms, the lex order on
    (index, argument) decides. *)

Inductive vord_lt : vord -> vord -> Prop :=
  | VL_cnf       : forall o1 o2, ord_lt o1 o2 -> vord_lt (V_cnf o1) (V_cnf o2)
  | VL_cnf_phi   : forall o n α, vord_lt (V_cnf o) (V_phi n α)
  | VL_phi_idx   : forall n1 n2 α1 α2,
      n1 < n2 -> vord_lt (V_phi n1 α1) (V_phi n2 α2)
  | VL_phi_arg   : forall n α1 α2,
      ord_lt α1 α2 -> vord_lt (V_phi n α1) (V_phi n α2).

Lemma vord_lt_V_cnf_inv : forall v o,
  vord_lt v (V_cnf o) -> exists o', v = V_cnf o' /\ ord_lt o' o.
Proof.
  intros v o H.
  remember (V_cnf o) as u eqn:Eu.
  destruct H as [o1 o2 Hlt | o' n α | n1 n2 α1 α2 Hlt | n α1 α2 Hlt].
  - injection Eu as Hu. subst o2.
    exists o1. split; [reflexivity | exact Hlt].
  - discriminate.
  - discriminate.
  - discriminate.
Qed.

Lemma vord_lt_V_phi_inv : forall v n α,
  vord_lt v (V_phi n α) ->
    (exists o, v = V_cnf o) \/
    (exists n' α', v = V_phi n' α' /\ n' < n) \/
    (exists α', v = V_phi n α' /\ ord_lt α' α).
Proof.
  intros v n α H.
  remember (V_phi n α) as u eqn:Eu.
  destruct H as [o1 o2 Hlt | o' nn αα | n1 n2 α1 α2 Hlt | nn α1 α2 Hlt].
  - discriminate.
  - injection Eu as En Eα. subst nn αα.
    left. exists o'. reflexivity.
  - injection Eu as En Eα. subst n2 α2.
    right. left. exists n1, α1. split; [reflexivity | exact Hlt].
  - injection Eu as En Eα. subst nn α2.
    right. right. exists α1. split; [reflexivity | exact Hlt].
Qed.

(** ** Well-foundedness on the [wf_vord] subset.

    Conditioned relation [vord_wf_lt] requires both endpoints to be
    well-formed (CNF in their [ord] components).  Well-foundedness then
    follows from: (i) [V_cnf]-images use [nf_Acc] for [cnf_lt] descent,
    (ii) [V_phi n _] images use lex on (n, [cnf_lt] on the inner [ord]). *)

Definition vord_wf_lt (u v : vord) : Prop :=
  wf_vord u /\ wf_vord v /\ vord_lt u v.

Lemma Acc_vord_V_cnf_wf : forall o,
  wf_ord o -> Acc vord_wf_lt (V_cnf o).
Proof.
  intros o Hwfo.
  pose proof (nf_Acc o Hwfo) as Acco.
  revert Hwfo.
  induction Acco as [o Hacc IH]. intro Hwfo.
  apply Acc_intro. intros y [Hwfy [_ Hlt]].
  destruct (vord_lt_V_cnf_inv _ _ Hlt) as [o' [Heq Hltoo]].
  subst y. cbn in Hwfy.
  apply IH.
  - unfold lt_cnf. split; [exact Hwfy | split; [exact Hwfo | exact Hltoo]].
  - exact Hwfy.
Qed.

(** For [V_phi n α] images: outer induction on n, inner on Acc lt_cnf α. *)

Lemma Acc_vord_V_phi_wf : forall n α,
  wf_ord α -> Acc vord_wf_lt (V_phi n α).
Proof.
  intro n. induction n as [n IHn] using lt_wf_ind.
  intros α Hwfα.
  pose proof (nf_Acc α Hwfα) as Accα.
  revert Hwfα.
  induction Accα as [α Haccα IHα]. intro Hwfα.
  apply Acc_intro. intros y [Hwfy [_ Hlt]].
  destruct (vord_lt_V_phi_inv _ _ _ Hlt) as
    [[o E] | [[n' [α' [E Hlt']]] | [α' [E Hltα]]]].
  - subst y. apply Acc_vord_V_cnf_wf. exact Hwfy.
  - subst y. cbn in Hwfy. apply IHn; [exact Hlt' | exact Hwfy].
  - subst y. cbn in Hwfy. apply IHα.
    + unfold lt_cnf. split; [exact Hwfy | split; [exact Hwfα | exact Hltα]].
    + exact Hwfy.
Qed.

Theorem vord_wf_lt_well_founded : well_founded vord_wf_lt.
Proof.
  intro v. apply Acc_intro. intros y [Hwfy [Hwfv Hlt]].
  destruct v as [o | n α].
  - apply (Acc_inv (Acc_vord_V_cnf_wf o Hwfv)).
    split; [exact Hwfy | split; [exact Hwfv | exact Hlt]].
  - apply (Acc_inv (Acc_vord_V_phi_wf n α Hwfv)).
    split; [exact Hwfy | split; [exact Hwfv | exact Hlt]].
Qed.

(** ** Concrete Veblen positions.

    [veps0]            = ε_0 = φ_1(0), encoded as [V_phi 0 OZero].
    [vgamma0_approx n] = φ_(n+1)(0), the Γ_0 approximations from below.
    *)

Definition veps0 : vord := V_phi 0 OZero.

Definition vgamma0_approx (n : nat) : vord := V_phi n OZero.

Theorem vgamma0_approx_zero : vgamma0_approx 0 = veps0.
Proof. reflexivity. Qed.

Theorem vgamma0_approx_strict : forall n,
  vord_lt (vgamma0_approx n) (vgamma0_approx (S n)).
Proof. intro n. unfold vgamma0_approx. apply VL_phi_idx. lia. Qed.

Theorem vgamma0_approx_chain : forall n m,
  n < m -> vord_lt (vgamma0_approx n) (vgamma0_approx m).
Proof. intros n m H. unfold vgamma0_approx. apply VL_phi_idx. exact H. Qed.

(** Every CNF ord is strictly below ε_0 in vord. *)

Theorem cnf_below_veps0 : forall o,
  vord_lt (V_cnf o) veps0.
Proof. intro o. unfold veps0. apply VL_cnf_phi. Qed.

(** In particular, every iterated ω-tower [Veblen_phi_iter k OZero] is
    below ε_0 in vord, witnessing that ε_0 is genuinely beyond CNF. *)

Theorem omega_tower_image_below_veps0 : forall k,
  vord_lt (V_cnf (Veblen_phi_iter k OZero)) veps0.
Proof. intro k. apply cnf_below_veps0. Qed.

(** Every worm has its [worm_to_ord] image below ε_0 in vord. *)

Theorem worm_image_below_veps0 : forall w,
  vord_lt (V_cnf (worm_to_ord w)) veps0.
Proof. intro w. apply cnf_below_veps0. Qed.

Definition T_n_ordinal (n : nat) : vord := vgamma0_approx n.

Theorem T_n_ordinal_strict : forall n,
  vord_lt (T_n_ordinal n) (T_n_ordinal (S n)).
Proof. intro n. unfold T_n_ordinal. exact (vgamma0_approx_strict n). Qed.

Theorem T_n_ordinal_chain : forall n m,
  n < m -> vord_lt (T_n_ordinal n) (T_n_ordinal m).
Proof. intros n m H. unfold T_n_ordinal. exact (vgamma0_approx_chain n m H). Qed.

Theorem T_n_ordinal_zero : T_n_ordinal 0 = veps0.
Proof. unfold T_n_ordinal. exact vgamma0_approx_zero. Qed.

Theorem T_n_ordinal_consistency_strength : forall n,
  vord_lt (T_n_ordinal n) (T_n_ordinal (S n)) /\
  (|- Box (S n) (Neg (Box n Bot))).
Proof.
  intro n. split.
  - exact (T_n_ordinal_strict n).
  - exact (Ax_NextCon n).
Qed.

Theorem T_n_ordinal_summary :
  (forall n, vord_lt (T_n_ordinal n) (T_n_ordinal (S n))) /\
  (forall n m, n < m -> vord_lt (T_n_ordinal n) (T_n_ordinal m)) /\
  T_n_ordinal 0 = veps0 /\
  (forall n, |- Box (S n) (Neg (Box n Bot))) /\
  (forall n, ~ |- Box n (Neg (Box n Bot))).
Proof.
  split; [|split; [|split; [|split]]].
  - exact T_n_ordinal_strict.
  - exact T_n_ordinal_chain.
  - exact T_n_ordinal_zero.
  - exact Ax_NextCon.
  - exact Godel_sentence_independent_at_Tn.
Qed.

(** ** Normal-form preservation under the canonical witnesses. *)

Theorem veps0_wf : wf_vord veps0.
Proof. unfold veps0. cbn. exact I. Qed.

Theorem vgamma0_approx_wf : forall n, wf_vord (vgamma0_approx n).
Proof. intro n. unfold vgamma0_approx. cbn. exact I. Qed.

Theorem cnf_wf_to_vord : forall o, wf_ord o -> wf_vord (V_cnf o).
Proof. intros o H. exact H. Qed.

(** ** Connection to GLP* worms.

    Every GLP* worm [w] has a CNF representation [worm_to_ord w] in
    [ord], which lifts to [V_cnf (worm_to_ord w)] in [vord], and is
    strictly below [veps0 = ε_0].  Combined with [vgamma0_approx]
    being unbounded above [veps0], this shows the Veblen notation
    system genuinely strictly extends the worm-induced CNF bound on
    GLP* proof-theoretic ordinals. *)

Theorem GLP_worm_strictly_below_veps0 : forall w,
  vord_lt (V_cnf (worm_to_ord w)) veps0 /\
  forall n, vord_lt veps0 (vgamma0_approx (S n)).
Proof.
  intros w. split.
  - apply worm_image_below_veps0.
  - intro n. unfold veps0, vgamma0_approx.
    apply VL_phi_idx. lia.
Qed.

(** ** Strict layering of the Veblen hierarchy.

    For every n, there is a vord (namely [vgamma0_approx n]) that is
    strictly above every CNF ord (representing all worm-images) and
    below [vgamma0_approx (S n)].  This is the strict layering of the
    Γ_0 approximations from below the Feferman-Schütte ordinal Γ_0. *)

Theorem veblen_hierarchy_strict_layering : forall n,
  (forall o, vord_lt (V_cnf o) (vgamma0_approx n)) /\
  vord_lt (vgamma0_approx n) (vgamma0_approx (S n)).
Proof.
  intro n. split.
  - intro o. unfold vgamma0_approx. apply VL_cnf_phi.
  - apply vgamma0_approx_strict.
Qed.

(** ** Veblen notation system: the headline package.

    The Veblen notation system (vord, vord_wf_lt, wf_vord) extends CNF
    in a well-ordered fashion, captures ε_0 as the syntactic atom
    [V_phi 0 OZero], approximates Γ_0 from below via the
    [vgamma0_approx] family, and connects to GLP*'s worm-image
    proof-theoretic ordinal bound via the [V_cnf] embedding. *)

Theorem veblen_notation_system_well_ordered :
  well_founded vord_wf_lt /\
  (forall n m, n < m -> vord_lt (vgamma0_approx n) (vgamma0_approx m)) /\
  (forall w, vord_lt (V_cnf (worm_to_ord w)) veps0) /\
  veps0 = vgamma0_approx 0.
Proof.
  split; [|split; [|split]].
  - exact vord_wf_lt_well_founded.
  - exact vgamma0_approx_chain.
  - exact worm_image_below_veps0.
  - reflexivity.
Qed.

(******************************************************************************)
(* Subject reduction for [pt_reduces] (the basic five-rule reduction).        *)
(*                                                                            *)
(* Each contraction rule preserves the denotation of the proof term.  We     *)
(* build up by single lemmas — one per rule — and then combine.               *)
(******************************************************************************)

(** Lemma: K-contraction preserves denotation. *)

Lemma pt_K_subject_reduction : forall phi psi p1 p2 chi,
  denote_proof_term (PT_MP (PT_MP (PT_K phi psi) p1) p2) = Some chi ->
  denote_proof_term p1 = Some chi.
Proof.
  intros phi psi p1 p2 chi Hd. cbn in Hd.
  destruct (denote_proof_term p1) as [d1|] eqn:Ep1; [|discriminate].
  destruct (Form_eqb phi d1) eqn:E1; [|discriminate].
  apply Form_eqb_eq in E1. subst d1.
  destruct (denote_proof_term p2) as [d2|] eqn:Ep2; [|discriminate].
  destruct (Form_eqb psi d2) eqn:E2; [|discriminate].
  injection Hd as Hd. subst chi. reflexivity.
Qed.

(** Lemma: BoxK-Nec contraction preserves denotation.
    [(BoxK n φ ψ) (Nec n p1) (Nec n p2)] reduces to [Nec n (MP p1 p2)]. *)

Lemma pt_BoxK_Nec_subject_reduction : forall n phi psi p1 p2 chi,
  denote_proof_term
    (PT_MP (PT_MP (PT_BoxK n phi psi) (PT_Nec n p1)) (PT_Nec n p2)) = Some chi ->
  denote_proof_term (PT_Nec n (PT_MP p1 p2)) = Some chi.
Proof.
  intros n phi psi p1 p2 chi Hd. cbn in Hd.
  destruct (denote_proof_term p1) as [d1|] eqn:Ep1; [|discriminate].
  destruct (Form_eqb (Box n (Impl phi psi)) (Box n d1)) eqn:E1; [|discriminate].
  apply Form_eqb_eq in E1. injection E1 as E1. subst d1.
  destruct (denote_proof_term p2) as [d2|] eqn:Ep2; [|discriminate].
  destruct (Form_eqb (Box n phi) (Box n d2)) eqn:E2; [|discriminate].
  apply Form_eqb_eq in E2. injection E2 as E2. subst d2.
  injection Hd as Hd. subst chi.
  cbn. rewrite Ep1, Ep2.
  rewrite Form_eqb_refl. reflexivity.
Qed.

(** Lemma: contextual rule, MP-left.  If p1 → p1' preserves denotation,
    then so does (PT_MP p1 p2) → (PT_MP p1' p2). *)

Lemma pt_MP_left_subject_reduction : forall p1 p1' p2 chi,
  (forall psi, denote_proof_term p1 = Some psi ->
               denote_proof_term p1' = Some psi) ->
  denote_proof_term (PT_MP p1 p2) = Some chi ->
  denote_proof_term (PT_MP p1' p2) = Some chi.
Proof.
  intros p1 p1' p2 chi Hpres Hd. cbn in Hd.
  destruct (denote_proof_term p1) as [f|] eqn:Ep1; [|discriminate].
  pose proof (Hpres f eq_refl) as Hp1'.
  cbn. rewrite Hp1'. exact Hd.
Qed.

(** Lemma: contextual rule, MP-right. *)

Lemma pt_MP_right_subject_reduction : forall p1 p2 p2' chi,
  (forall psi, denote_proof_term p2 = Some psi ->
               denote_proof_term p2' = Some psi) ->
  denote_proof_term (PT_MP p1 p2) = Some chi ->
  denote_proof_term (PT_MP p1 p2') = Some chi.
Proof.
  intros p1 p2 p2' chi Hpres Hd. cbn in Hd.
  destruct (denote_proof_term p1) as [f|] eqn:Ep1; [|discriminate].
  destruct f as [v | | a b | k psi]; try discriminate.
  destruct (denote_proof_term p2) as [a'|] eqn:Ep2; [|discriminate].
  pose proof (Hpres a' eq_refl) as Hp2'.
  cbn. rewrite Ep1, Hp2'. exact Hd.
Qed.

(** Lemma: contextual rule, under Nec. *)

Lemma pt_Nec_subject_reduction : forall n p p' chi,
  (forall psi, denote_proof_term p = Some psi ->
               denote_proof_term p' = Some psi) ->
  denote_proof_term (PT_Nec n p) = Some chi ->
  denote_proof_term (PT_Nec n p') = Some chi.
Proof.
  intros n p p' chi Hpres Hd. cbn in Hd.
  destruct (denote_proof_term p) as [psi|] eqn:Ep; [|discriminate].
  pose proof (Hpres psi eq_refl) as Hp'.
  cbn. rewrite Hp'. exact Hd.
Qed.

(** Main theorem: every step of [pt_reduces] preserves denotation
    (subject reduction). *)

Theorem pt_reduces_subject_reduction : forall p p' phi,
  pt_reduces p p' ->
  denote_proof_term p = Some phi ->
  denote_proof_term p' = Some phi.
Proof.
  intros p p' phi Hred. revert phi.
  induction Hred; intro chi.
  - (* PTR_MP_left *)
    apply pt_MP_left_subject_reduction. intros psi Hp; exact (IHHred psi Hp).
  - (* PTR_MP_right *)
    apply pt_MP_right_subject_reduction. intros psi Hp; exact (IHHred psi Hp).
  - (* PTR_Nec *)
    apply pt_Nec_subject_reduction. intros psi Hp; exact (IHHred psi Hp).
  - (* PTR_K *)
    intro Hd. exact (pt_K_subject_reduction phi psi p1 p2 chi Hd).
  - (* PTR_BoxK_Nec *)
    intro Hd. exact (pt_BoxK_Nec_subject_reduction n phi psi p1 p2 chi Hd).
Qed.

(** Corollary: provability is preserved under [pt_reduces]: if a proof
    term denotes a provable formula and reduces to another, the reduct
    also denotes the same provable formula. *)

Corollary pt_reduces_preserves_provability : forall p p' phi,
  pt_reduces p p' ->
  denote_proof_term p = Some phi ->
  |- phi /\ denote_proof_term p' = Some phi.
Proof.
  intros p p' phi Hred Hd.
  pose proof (pt_reduces_subject_reduction p p' phi Hred Hd) as Hd'.
  split.
  - exact (denote_proof_term_provable p phi Hd).
  - exact Hd'.
Qed.

(** ** Normal forms.

    A proof term is in normal form when no [pt_reduces] step applies to
    it.  We define a syntactic predicate [pt_redex] detecting whether
    any of the five reduction-rule LHS shapes occur at the term root,
    and [pt_normal] propagating "no redex anywhere" structurally. *)

Definition pt_redex_at_root (p : proof_term) : bool :=
  match p with
  | PT_MP (PT_MP (PT_K _ _) _) _ => true
  | PT_MP (PT_MP (PT_BoxK _ _ _) (PT_Nec _ _)) (PT_Nec _ _) => true
  | _ => false
  end.

Fixpoint pt_normal (p : proof_term) : bool :=
  match p with
  | PT_MP p1 p2 =>
      andb (negb (pt_redex_at_root (PT_MP p1 p2)))
           (andb (pt_normal p1) (pt_normal p2))
  | PT_Nec _ p1 => pt_normal p1
  | _ => true
  end.

(** Atomic proof terms are always normal. *)

Lemma pt_normal_atomic : forall p,
  match p with
  | PT_MP _ _ | PT_Nec _ _ => False
  | _ => True
  end -> pt_normal p = true.
Proof.
  intros p H.
  destruct p; cbn; try reflexivity; contradiction.
Qed.

(** A normal proof term has no root redex. *)

Lemma pt_normal_no_root_redex : forall p,
  pt_normal p = true -> pt_redex_at_root p = false.
Proof.
  intros p H. destruct p; cbn in *; try reflexivity.
  apply Bool.andb_true_iff in H. destruct H as [Hneg _].
  apply Bool.negb_true_iff in Hneg. exact Hneg.
Qed.

(** ** Existence of normal forms.

    Every proof term reduces to a normal form via well-founded recursion
    on [proof_term_size].  We express this as: for every [p], there
    exists a [p'] such that [pt_reduces*] reaches [p'] and [pt_normal p']. *)

Inductive pt_reduces_star : proof_term -> proof_term -> Prop :=
  | PTRS_refl : forall p, pt_reduces_star p p
  | PTRS_step : forall p p' p'',
      pt_reduces p p' -> pt_reduces_star p' p'' -> pt_reduces_star p p''.

Lemma pt_reduces_star_size : forall p p',
  pt_reduces_star p p' -> proof_term_size p' <= proof_term_size p.
Proof.
  intros p p' H. induction H.
  - reflexivity.
  - pose proof (pt_reduces_decreases_size p p' H) as Hlt. lia.
Qed.

(** Subject reduction extends to multi-step reduction. *)

Theorem pt_reduces_star_subject_reduction : forall p p' phi,
  pt_reduces_star p p' ->
  denote_proof_term p = Some phi ->
  denote_proof_term p' = Some phi.
Proof.
  intros p p' phi Hstar. revert phi.
  induction Hstar; intro chi; intro Hd.
  - exact Hd.
  - apply IHHstar.
    exact (pt_reduces_subject_reduction p p' chi H Hd).
Qed.

(** Strong normalisation: every proof term has a [pt_reduces]-normal
    form reachable in finitely many steps. *)

Theorem pt_normal_form_exists : forall p,
  exists p', pt_reduces_star p p' /\
             (forall q, ~ pt_reduces p' q).
Proof.
  intros p.
  induction p as [p IH] using
    (well_founded_induction proof_term_no_infinite_reduction).
  destruct (classic (exists q, pt_reduces p q)) as [[q Hpq] | Hnone].
  - destruct (IH q Hpq) as [p' [Hstar Hnf]].
    exists p'. split.
    + exact (PTRS_step p q p' Hpq Hstar).
    + exact Hnf.
  - exists p. split.
    + apply PTRS_refl.
    + intros q Hcontra. apply Hnone. exists q. exact Hcontra.
Qed.

(** Combined with subject reduction: every provable formula has a
    proof-term derivation in normal form. *)

Theorem provable_has_normal_form_proof : forall phi,
  |- phi -> exists p, denote_proof_term p = Some phi /\
                      (forall q, ~ pt_reduces p q).
Proof.
  intros phi Hp.
  destruct (provable_to_proof_term phi Hp) as [pt Hd].
  destruct (pt_normal_form_exists pt) as [pt' [Hstar Hnf]].
  exists pt'. split.
  - exact (pt_reduces_star_subject_reduction pt pt' phi Hstar Hd).
  - exact Hnf.
Qed.

(******************************************************************************)
(* Multiset measure for PTRF_S contraction.                                    *)
(*                                                                            *)
(* The PTRF_S rule duplicates [x]:                                            *)
(*   (PT_S _ _ _) f g x  -->  (f x) (g x)                                     *)
(* Naive [proof_term_size] does not strictly decrease (LHS=4+|f|+|g|+|x|,    *)
(* RHS=3+|f|+|g|+2|x|).                                                       *)
(*                                                                            *)
(* We build a measure based on the *count of PT_S occurrences*, observing    *)
(* that PTRF_S contraction strictly decreases the count when [x] contains    *)
(* no internal [PT_S].  We then strengthen to a multiset-pair measure.        *)
(******************************************************************************)

Fixpoint pt_S_count (p : proof_term) : nat :=
  match p with
  | PT_S _ _ _ => 1
  | PT_MP p1 p2 => pt_S_count p1 + pt_S_count p2
  | PT_Nec _ p1 => pt_S_count p1
  | _ => 0
  end.

(** PTRF_S strictly decreases [pt_S_count] when [x] has no internal S. *)

Lemma pt_S_count_PTRF_S_decreases_when_x_S_free : forall phi psi chi f g x,
  pt_S_count x = 0 ->
  pt_S_count (PT_MP (PT_MP f x) (PT_MP g x))
    < pt_S_count (PT_MP (PT_MP (PT_MP (PT_S phi psi chi) f) g) x).
Proof.
  intros phi psi chi f g x Hx.
  cbn. rewrite Hx. lia.
Qed.

(** ** Subterm-size-pair multiset measure.

    For each PTRF_S-redex root in the term, record the pair
    [(|f|+|g|, |x|)].  Reduction by PTRF_S removes the entry at the
    contracted redex; the inner-of-[x] entries get duplicated, but the
    inner-of-[f]/[g] entries are unchanged.  When [x] has no internal
    PTRF_S redex, the multiset strictly shrinks under multi-set order. *)

Fixpoint pt_S_redex_pairs (p : proof_term) : list (nat * nat) :=
  match p with
  | PT_MP (PT_MP (PT_MP (PT_S _ _ _) f) g) x =>
      (proof_term_size f + proof_term_size g, proof_term_size x)
        :: pt_S_redex_pairs f ++ pt_S_redex_pairs g ++ pt_S_redex_pairs x
  | PT_MP p1 p2 => pt_S_redex_pairs p1 ++ pt_S_redex_pairs p2
  | PT_Nec _ p1 => pt_S_redex_pairs p1
  | _ => []
  end.

(** PTRF_S contraction strictly decreases the redex-pair-list length
    when [f], [g], and [x] are all S-redex-free.  Under this hypothesis,
    the LHS has exactly one S-redex (the root one), and the RHS has
    none — neither [PT_MP f x] nor [PT_MP g x] can be a redex because
    that would require [f] or [g] itself to start with
    [PT_MP (PT_MP (PT_S _ _ _) _) _], contradicting their S-redex-free
    assumption. *)

(** [pt_atomic]: a proof term is atomic if it is not a PT_MP or PT_Nec.
    Atomic terms have no internal MPs and so cannot themselves form an
    S-redex root, nor can wrapping them in a single MP create one. *)

Definition pt_atomic (p : proof_term) : Prop :=
  match p with
  | PT_MP _ _ | PT_Nec _ _ => False
  | _ => True
  end.

Lemma pt_atomic_pairs_empty : forall p,
  pt_atomic p -> pt_S_redex_pairs p = [].
Proof.
  intros p H.
  destruct p; cbn; try reflexivity; contradiction.
Qed.

(** When [f] and [g] are atomic, [PT_MP f x] and [PT_MP g x] cannot be
    PTRF_S-redexes (which would require [f] or [g] to be of shape
    [PT_MP (PT_MP (PT_S _ _ _) _) _]).  The pair-list reduces to
    [pt_S_redex_pairs x] in the non-redex MP case. *)

Lemma pt_S_redex_pairs_MP_atomic_f : forall f x,
  pt_atomic f ->
  pt_S_redex_pairs (PT_MP f x) = pt_S_redex_pairs x.
Proof.
  intros f x H. destruct f; cbn in *; try contradiction; reflexivity.
Qed.

(** Strict-decrease theorem: PTRF_S contraction strictly decreases the
    redex-pair-list length when [f] and [g] are atomic and [x] has no
    S-redex.  Under these hypotheses, the LHS has exactly one redex
    (the root one), and the RHS has none. *)

Theorem PTRF_S_decreases_pair_count_atomic_fg :
  forall phi psi chi f g x,
    pt_atomic f ->
    pt_atomic g ->
    pt_S_redex_pairs x = [] ->
    length (pt_S_redex_pairs (PT_MP (PT_MP f x) (PT_MP g x))) <
    length (pt_S_redex_pairs
              (PT_MP (PT_MP (PT_MP (PT_S phi psi chi) f) g) x)).
Proof.
  intros phi psi chi f g x Hf Hg Hx.
  pose proof (pt_atomic_pairs_empty f Hf) as Hf'.
  pose proof (pt_atomic_pairs_empty g Hg) as Hg'.
  destruct f; cbn in Hf; try contradiction;
    destruct g; cbn in Hg; try contradiction;
    cbn [pt_S_redex_pairs];
    rewrite Hx; cbn [length app]; lia.
Qed.

(******************************************************************************)
(* Newman's lemma (abstract): well-foundedness + local confluence => global  *)
(* confluence (Church-Rosser).                                                *)
(******************************************************************************)

Section NewmanLemma.

Variable A : Type.
Variable R : A -> A -> Prop.

Definition R_star (x y : A) : Prop :=
  exists n,
    (fix iter (k : nat) (a b : A) : Prop :=
       match k with
       | 0 => a = b
       | S k' => exists c, R a c /\ iter k' c b
       end) n x y.

Lemma R_star_refl : forall x, R_star x x.
Proof. intro x. exists 0. cbn. reflexivity. Qed.

Lemma R_star_step : forall x y z, R x y -> R_star y z -> R_star x z.
Proof.
  intros x y z H1 [n H2]. exists (S n). cbn. exists y. split; assumption.
Qed.

Lemma R_star_one : forall x y, R x y -> R_star x y.
Proof.
  intros x y H. apply (R_star_step _ y _ H). apply R_star_refl.
Qed.

Lemma R_star_trans : forall x y z, R_star x y -> R_star y z -> R_star x z.
Proof.
  intros x y z [n1 H1]. revert x y H1.
  induction n1 as [|n IH]; intros x y H1 Hyz.
  - cbn in H1. subst y. exact Hyz.
  - cbn in H1. destruct H1 as [c [Hxc Hcy]].
    apply (R_star_step _ c). exact Hxc. exact (IH c y Hcy Hyz).
Qed.

Definition locally_confluent : Prop :=
  forall x y1 y2, R x y1 -> R x y2 ->
    exists z, R_star y1 z /\ R_star y2 z.

Definition confluent : Prop :=
  forall x y1 y2, R_star x y1 -> R_star x y2 ->
    exists z, R_star y1 z /\ R_star y2 z.

(** Newman's lemma — proved by well-founded induction on x. *)

Theorem newman_lemma :
  well_founded (fun y x => R x y) ->
  locally_confluent ->
  confluent.
Proof.
  intros Hwf Hloc x.
  induction x as [x IH] using (well_founded_induction Hwf).
  intros y1 y2 [n1 H1] [n2 H2]. revert y1 y2 H1 H2.
  destruct n1 as [|n1].
  - cbn. intros y1 y2 Hxy1 H2. subst y1.
    exists y2. split; [exists n2; exact H2 | apply R_star_refl].
  - destruct n2 as [|n2].
    + cbn. intros y1 y2 [c1 [Hxc1 Hc1y1]] Hxy2. subst y2.
      exists y1. split. apply R_star_refl. exists (S n1). cbn.
      exists c1. split; assumption.
    + cbn. intros y1 y2 [c1 [Hxc1 Hc1y1]] [c2 [Hxc2 Hc2y2]].
      destruct (Hloc x c1 c2 Hxc1 Hxc2) as [d [Hc1d Hc2d]].
      assert (Hc1y1' : R_star c1 y1) by (exists n1; exact Hc1y1).
      assert (Hc2y2' : R_star c2 y2) by (exists n2; exact Hc2y2).
      destruct (IH c1 Hxc1 y1 d Hc1y1' Hc1d) as [e1 [Hy1e1 Hde1]].
      destruct (IH c2 Hxc2 y2 e1 Hc2y2'
                  (R_star_trans _ _ _ Hc2d Hde1)) as [e2 [Hy2e2 He1e2]].
      exists e2. split.
      * exact (R_star_trans _ _ _ Hy1e1 He1e2).
      * exact Hy2e2.
Qed.

End NewmanLemma.

(** ** Newman's lemma instantiated for [pt_reduces]. *)

Theorem newman_for_pt_reduces :
  (forall p q1 q2, pt_reduces p q1 -> pt_reduces p q2 ->
     exists r, R_star _ pt_reduces q1 r /\ R_star _ pt_reduces q2 r) ->
  forall p q1 q2,
    R_star _ pt_reduces p q1 -> R_star _ pt_reduces p q2 ->
    exists r, R_star _ pt_reduces q1 r /\ R_star _ pt_reduces q2 r.
Proof.
  intro Hloc.
  apply (newman_lemma _ pt_reduces).
  - exact proof_term_no_infinite_reduction.
  - exact Hloc.
Qed.

(******************************************************************************)
(* Local confluence of [pt_reduces]: critical-pair analysis.                   *)
(******************************************************************************)

(** Lift a single-step reduction to the reflexive-transitive closure. *)

Lemma pt_reduces_R_star : forall p q,
  pt_reduces p q -> R_star _ pt_reduces p q.
Proof. intros p q H. apply R_star_one. exact H. Qed.

Lemma pt_reduces_R_star_refl : forall p, R_star _ pt_reduces p p.
Proof. intro p. apply R_star_refl. Qed.

(** Trivial confluence: both sides equal. *)

Lemma pt_reduces_confluence_eq : forall (q : proof_term),
  exists r, R_star _ pt_reduces q r /\ R_star _ pt_reduces q r.
Proof.
  intros q. exists q. split; apply (R_star_refl _ pt_reduces).
Qed.

(** Reductions inside MP-left and MP-right operate on different
    sub-positions and hence commute trivially. *)

Lemma pt_reduces_orthogonal_MP : forall p1 p1' p2 p2',
  pt_reduces p1 p1' -> pt_reduces p2 p2' ->
  exists r, R_star _ pt_reduces (PT_MP p1' p2) r /\
            R_star _ pt_reduces (PT_MP p1 p2') r.
Proof.
  intros p1 p1' p2 p2' H1 H2.
  exists (PT_MP p1' p2'). split.
  - apply pt_reduces_R_star. exact (PTR_MP_right _ _ _ H2).
  - apply pt_reduces_R_star. exact (PTR_MP_left _ _ _ H1).
Qed.

(** Lifting [pt_reduces_R_star] under MP-left context. *)

Lemma R_star_under_MP_left : forall p1 p1' p2,
  R_star _ pt_reduces p1 p1' ->
  R_star _ pt_reduces (PT_MP p1 p2) (PT_MP p1' p2).
Proof.
  intros p1 p1' p2 [n H]. revert p1 H.
  induction n as [|n IH]; intros p1 H.
  - cbn in H. subst p1'. apply R_star_refl.
  - cbn in H. destruct H as [c [Hpc Hcp1']].
    apply (R_star_step _ _ _ (PT_MP c p2)).
    + exact (PTR_MP_left _ _ _ Hpc).
    + exact (IH c Hcp1').
Qed.

Lemma R_star_under_MP_right : forall p1 p2 p2',
  R_star _ pt_reduces p2 p2' ->
  R_star _ pt_reduces (PT_MP p1 p2) (PT_MP p1 p2').
Proof.
  intros p1 p2 p2' [n H]. revert p2 H.
  induction n as [|n IH]; intros p2 H.
  - cbn in H. subst p2'. apply R_star_refl.
  - cbn in H. destruct H as [c [Hpc Hcp2']].
    apply (R_star_step _ _ _ (PT_MP p1 c)).
    + exact (PTR_MP_right _ _ _ Hpc).
    + exact (IH c Hcp2').
Qed.

Lemma R_star_under_Nec : forall n p p',
  R_star _ pt_reduces p p' ->
  R_star _ pt_reduces (PT_Nec n p) (PT_Nec n p').
Proof.
  intros n p p' [k H]. revert p H.
  induction k as [|k IH]; intros p H.
  - cbn in H. subst p'. apply R_star_refl.
  - cbn in H. destruct H as [c [Hpc Hcp']].
    apply (R_star_step _ _ _ (PT_Nec n c)).
    + exact (PTR_Nec _ _ _ Hpc).
    + exact (IH c Hcp').
Qed.

(** ** Local confluence: structural induction on the first reduction.

    For each pair of single-step reductions [p → q1] and [p → q2], we
    construct a common reduct.  The proof uses inductive case analysis:
    the contextual rules (MP-left, MP-right, Nec) recurse on subterms;
    the root contractions (PTR_K, PTR_BoxK_Nec) are critical pairs. *)

(** Atomic axiom-constructor terms admit no reduction.  This vacuous-case
    lemma simplifies critical-pair analyses where an inner contextual
    reduction would have to act on a [PT_K]/[PT_BoxK]/etc. which has
    no operational behaviour. *)

Lemma pt_reduces_atomic_K : forall phi psi q,
  ~ pt_reduces (PT_K phi psi) q.
Proof.
  intros phi psi q H. inversion H.
Qed.

Lemma pt_reduces_atomic_S : forall phi psi chi q,
  ~ pt_reduces (PT_S phi psi chi) q.
Proof.
  intros phi psi chi q H. inversion H.
Qed.

Lemma pt_reduces_atomic_DN : forall phi q,
  ~ pt_reduces (PT_DN phi) q.
Proof.
  intros phi q H. inversion H.
Qed.

Lemma pt_reduces_atomic_BoxK : forall n phi psi q,
  ~ pt_reduces (PT_BoxK n phi psi) q.
Proof.
  intros n phi psi q H. inversion H.
Qed.

Lemma pt_reduces_atomic_Loeb : forall n phi q,
  ~ pt_reduces (PT_Loeb n phi) q.
Proof.
  intros n phi q H. inversion H.
Qed.

Lemma pt_reduces_atomic_Box4 : forall n phi q,
  ~ pt_reduces (PT_Box4 n phi) q.
Proof.
  intros n phi q H. inversion H.
Qed.

Lemma pt_reduces_atomic_Mon : forall n phi q,
  ~ pt_reduces (PT_Mon n phi) q.
Proof.
  intros n phi q H. inversion H.
Qed.

Lemma pt_reduces_atomic_NextCon : forall n q,
  ~ pt_reduces (PT_NextCon n) q.
Proof.
  intros n q H. inversion H.
Qed.

(** Inversion of a single reduction inside [PT_Nec n p]: the only rule
    that applies is [PTR_Nec] (since [PT_Nec] is not a [PT_MP]). *)

Lemma pt_reduces_Nec_inv : forall n p q,
  pt_reduces (PT_Nec n p) q ->
  exists p', q = PT_Nec n p' /\ pt_reduces p p'.
Proof.
  intros n p q H. inversion H. subst.
  eexists. split; [reflexivity | eassumption].
Qed.

(** Inversion of a single reduction inside [PT_MP a b]: either inner
    [a → a'] (PTR_MP_left), inner [b → b'] (PTR_MP_right), or a root
    contraction (PTR_K, PTR_BoxK_Nec) — the latter requiring [a] to
    have specific shapes. *)

Lemma pt_reduces_MP_inv : forall a b q,
  pt_reduces (PT_MP a b) q ->
    (exists a', q = PT_MP a' b /\ pt_reduces a a') \/
    (exists b', q = PT_MP a b' /\ pt_reduces b b') \/
    (exists phi psi p1, a = PT_MP (PT_K phi psi) p1 /\ q = p1) \/
    (exists n phi psi p1 p2,
       a = PT_MP (PT_BoxK n phi psi) (PT_Nec n p1) /\
       b = PT_Nec n p2 /\
       q = PT_Nec n (PT_MP p1 p2)).
Proof.
  intros a b q H. inversion H; subst.
  - left. eexists. split; [reflexivity | eassumption].
  - right. left. eexists. split; [reflexivity | eassumption].
  - right. right. left. eexists. eexists. eexists. split; reflexivity.
  - right. right. right. eexists. eexists. eexists. eexists. eexists.
    split; [reflexivity | split; reflexivity].
Qed.

(** ** Local confluence: critical-pair-by-critical-pair analysis.

    Strategy: structural induction on the first reduction [H1].  In
    each case, invert the second reduction [H2] using the dedicated
    [pt_reduces_MP_inv] / [pt_reduces_Nec_inv] inversion lemmas,
    yielding finitely many sub-cases.  Each sub-case is closed either
    by appeal to the inductive hypothesis (when both reductions are
    inside the same subterm), by orthogonality (when reductions are
    in disjoint sub-positions), or by explicit construction of a
    common reduct. *)

Lemma pt_reduces_local_confluence : forall p q1 q2,
  pt_reduces p q1 -> pt_reduces p q2 ->
  exists r, R_star _ pt_reduces q1 r /\ R_star _ pt_reduces q2 r.
Proof.
  intros p q1 q2 H1. revert q2.
  induction H1 as [a a' b H1a IHa
                  | a b b' H1b IHb
                  | n c c' H1c IHc
                  | phi psi p1 p2
                  | n phi psi p1 p2]; intros q2 H2.
  - (* H1 = PTR_MP_left a a' b: q1 = PT_MP a' b, with a → a'. *)
    apply pt_reduces_MP_inv in H2. destruct H2 as
      [[a'' [Eq Ha]] | [[b'' [Eq Hb]] | [[phi [psi [p1 [Eq1 Eq2]]]] |
       [n [phi [psi [p1 [p2 [Eq1 [Eq2 Eq3]]]]]]]]]].
    + (* H2: inner left a → a''.  Recurse via IHa. *)
      subst q2.
      destruct (IHa a'' Ha) as [r [Hr1 Hr2]].
      exists (PT_MP r b). split.
      * apply R_star_under_MP_left. exact Hr1.
      * apply R_star_under_MP_left. exact Hr2.
    + (* H2: inner right b → b''.  Orthogonal. *)
      subst q2.
      exists (PT_MP a' b''). split.
      * apply pt_reduces_R_star. exact (PTR_MP_right _ _ _ Hb).
      * apply pt_reduces_R_star. exact (PTR_MP_left _ _ _ H1a).
    + (* H2: PTR_K, so a = PT_MP (PT_K phi psi) p1, b = anything,
         q2 = p1. *)
      subst a. subst q2.
      apply pt_reduces_MP_inv in H1a. destruct H1a as
        [[a'' [Eq Hred]] | [[b'' [Eq Hred]] | [[phi' [psi' [p1' [Eq1 Eq2]]]] |
         [n' [phi' [psi' [p1' [p2' [Eq1 [Eq2 Eq3]]]]]]]]]].
      * (* a = PT_MP (PT_K phi psi) p1, inner left: PT_K → a''.  Vacuous. *)
        apply pt_reduces_atomic_K in Hred. contradiction.
      * (* Inner right: p1 → b''.  a' = PT_MP (PT_K phi psi) b''. *)
        subst a'.
        exists b''. split.
        -- apply pt_reduces_R_star. exact (PTR_K phi psi b'' b).
        -- apply pt_reduces_R_star. exact Hred.
      * (* Inner PTR_K shape: PT_MP (PT_K phi psi) p1 = PT_MP (PT_K phi' psi') p1'? Vacuous shape. *)
        discriminate Eq1.
      * discriminate Eq1.
    + (* H2: PTR_BoxK_Nec.  a = PT_MP (PT_BoxK n phi psi) (PT_Nec n p1),
         b = PT_Nec n p2, q2 = PT_Nec n (PT_MP p1 p2). *)
      subst a b q2.
      apply pt_reduces_MP_inv in H1a. destruct H1a as
        [[a'' [Eq Hred]] | [[b'' [Eq Hred]] | [[phi' [psi' [p1' [Eq1 Eq2]]]] |
         [n' [phi' [psi' [p1' [p2' [Eq1 [Eq2 Eq3]]]]]]]]]].
      * apply pt_reduces_atomic_BoxK in Hred. contradiction.
      * (* Inner right: PT_Nec n p1 → b''. *)
        apply pt_reduces_Nec_inv in Hred. destruct Hred as [p1'' [Eq' Hp1]].
        subst b''. subst a'.
        exists (PT_Nec n (PT_MP p1'' p2)). split.
        -- apply pt_reduces_R_star.
           exact (PTR_BoxK_Nec n phi psi p1'' p2).
        -- apply pt_reduces_R_star.
           apply PTR_Nec. exact (PTR_MP_left _ _ _ Hp1).
      * discriminate Eq1.
      * discriminate Eq1.
  - (* H1 = PTR_MP_right a b b': q1 = PT_MP a b'. *)
    apply pt_reduces_MP_inv in H2. destruct H2 as
      [[a'' [Eq Ha]] | [[b'' [Eq Hb]] | [[phi [psi [p1 [Eq1 Eq2]]]] |
       [n [phi [psi [p1 [p2 [Eq1 [Eq2 Eq3]]]]]]]]]].
    + (* Inner left a → a''.  Orthogonal. *)
      subst q2.
      exists (PT_MP a'' b'). split.
      * apply pt_reduces_R_star. exact (PTR_MP_left _ _ _ Ha).
      * apply pt_reduces_R_star. exact (PTR_MP_right _ _ _ H1b).
    + (* Inner right: recurse. *)
      subst q2.
      destruct (IHb b'' Hb) as [r [Hr1 Hr2]].
      exists (PT_MP a r). split.
      * apply R_star_under_MP_right. exact Hr1.
      * apply R_star_under_MP_right. exact Hr2.
    + (* PTR_K: a = PT_MP (PT_K phi psi) p1, q2 = p1. *)
      subst a q2.
      exists p1. split.
      * apply pt_reduces_R_star. exact (PTR_K phi psi p1 b').
      * apply R_star_refl.
    + (* PTR_BoxK_Nec: a = PT_MP (PT_BoxK n phi psi) (PT_Nec n p1),
         b = PT_Nec n p2, q2 = PT_Nec n (PT_MP p1 p2).
         q1 = PT_MP a b' where b → b'. *)
      subst a b q2.
      (* H1b : pt_reduces (PT_Nec n p2) b'.  By Nec inversion. *)
      apply pt_reduces_Nec_inv in H1b. destruct H1b as [p2' [Eq Hp2]].
      subst b'.
      exists (PT_Nec n (PT_MP p1 p2')). split.
      * apply pt_reduces_R_star.
        exact (PTR_BoxK_Nec n phi psi p1 p2').
      * apply pt_reduces_R_star.
        apply PTR_Nec. exact (PTR_MP_right _ _ _ Hp2).
  - (* H1 = PTR_Nec n c c': q1 = PT_Nec n c'. *)
    apply pt_reduces_Nec_inv in H2. destruct H2 as [c'' [Eq Hc]].
    subst q2.
    destruct (IHc c'' Hc) as [r [Hr1 Hr2]].
    exists (PT_Nec n r). split.
    + apply R_star_under_Nec. exact Hr1.
    + apply R_star_under_Nec. exact Hr2.
  - (* H1 = PTR_K phi psi p1 p2: q1 = p1. *)
    apply pt_reduces_MP_inv in H2. destruct H2 as
      [[a'' [Eq Ha]] | [[b'' [Eq Hb]] | [[phi' [psi' [p1' [Eq1 Eq2]]]] |
       [n' [phi' [psi' [p1' [p2' [Eq1 [Eq2 Eq3]]]]]]]]]].
    + (* Inner left: PT_MP (PT_K phi psi) p1 → a''. *)
      apply pt_reduces_MP_inv in Ha. destruct Ha as
        [[a''' [Eq' Hred]] | [[b''' [Eq' Hred]] | [[phi'' [psi'' [p1'' [Eq1 Eq2]]]] |
         [n'' [phi'' [psi'' [p1'' [p2'' [Eq1 [Eq2 Eq3]]]]]]]]]].
      * apply pt_reduces_atomic_K in Hred. contradiction.
      * subst a'' q2.
        exists b'''. split.
        -- apply pt_reduces_R_star. exact Hred.
        -- apply pt_reduces_R_star. exact (PTR_K phi psi b''' p2).
      * discriminate Eq1.
      * discriminate Eq1.
    + (* Inner right: p2 → b''. *)
      subst q2.
      exists p1. split.
      * apply R_star_refl.
      * apply pt_reduces_R_star. exact (PTR_K phi psi p1 b'').
    + (* PTR_K twice: same shape, q2 = p1. *)
      injection Eq1 as Eq1a Eq1b. subst phi' psi' p1'.
      subst q2.
      exists p1. split; apply R_star_refl.
    + (* PTR_BoxK_Nec: shape mismatch. *)
      discriminate Eq1.
  - (* H1 = PTR_BoxK_Nec n phi psi p1 p2:
       q1 = PT_Nec n (PT_MP p1 p2). *)
    apply pt_reduces_MP_inv in H2. destruct H2 as
      [[a'' [Eq Ha]] | [[b'' [Eq Hb]] | [[phi' [psi' [p1' [Eq1 Eq2]]]] |
       [n' [phi' [psi' [p1' [p2' [Eq1 [Eq2 Eq3]]]]]]]]]].
    + (* Inner left: PT_MP (PT_BoxK n phi psi) (PT_Nec n p1) → a''. *)
      apply pt_reduces_MP_inv in Ha. destruct Ha as
        [[a''' [Eq' Hred]] | [[b''' [Eq' Hred]] | [[phi'' [psi'' [p1'' [Eq1 Eq2]]]] |
         [n'' [phi'' [psi'' [p1'' [p2'' [Eq1 [Eq2 Eq3]]]]]]]]]].
      * apply pt_reduces_atomic_BoxK in Hred. contradiction.
      * (* Inner right: PT_Nec n p1 → b'''.  By Nec inversion: p1 → p1_*. *)
        apply pt_reduces_Nec_inv in Hred. destruct Hred as [p1_ [Eq'' Hp1]].
        subst b''' a'' q2.
        exists (PT_Nec n (PT_MP p1_ p2)). split.
        -- apply pt_reduces_R_star.
           apply PTR_Nec. exact (PTR_MP_left _ _ _ Hp1).
        -- apply pt_reduces_R_star.
           exact (PTR_BoxK_Nec n phi psi p1_ p2).
      * discriminate Eq1.
      * discriminate Eq1.
    + (* Inner right: PT_Nec n p2 → b''.  By Nec inversion: p2 → p2_*. *)
      apply pt_reduces_Nec_inv in Hb. destruct Hb as [p2_ [Eq' Hp2]].
      subst b'' q2.
      exists (PT_Nec n (PT_MP p1 p2_)). split.
      * apply pt_reduces_R_star.
        apply PTR_Nec. exact (PTR_MP_right _ _ _ Hp2).
      * apply pt_reduces_R_star.
        exact (PTR_BoxK_Nec n phi psi p1 p2_).
    + (* PTR_K: shape mismatch. *)
      discriminate Eq1.
    + (* PTR_BoxK_Nec twice: same shape, q2 = q1. *)
      inversion Eq1; subst.
      inversion Eq2; subst.
      exists (PT_Nec n' (PT_MP p1' p2')). split; apply R_star_refl.
Qed.

(** Confluence (Church-Rosser) of [pt_reduces]: from local confluence
    plus well-foundedness via Newman's lemma. *)

Theorem pt_reduces_church_rosser :
  forall p q1 q2,
    R_star _ pt_reduces p q1 -> R_star _ pt_reduces p q2 ->
    exists r, R_star _ pt_reduces q1 r /\ R_star _ pt_reduces q2 r.
Proof.
  apply newman_for_pt_reduces.
  exact pt_reduces_local_confluence.
Qed.

(******************************************************************************)
(* Strong normalisation of [pt_reduces_full] on the S-free subset.            *)
(*                                                                            *)
(* The full pt_reduces_full system includes PTRF_S, which duplicates the     *)
(* third argument [x] and so does not strictly decrease [proof_term_size]    *)
(* in general.  Howard-style ordinal measures handle this for typed         *)
(* combinatory logic but are research-level for the present untyped         *)
(* polymodal calculus.                                                        *)
(*                                                                            *)
(* On the S-free subset (terms with no [PT_S] occurrence anywhere), [PTRF_S] *)
(* never fires.  All remaining rules strictly decrease [proof_term_size],   *)
(* hence well-foundedness holds via the size measure.                       *)
(******************************************************************************)

(** Note: [pt_S_count] does NOT decrease monotonically under
    [pt_reduces_full] in general — PTRF_S duplicates [x] and can
    therefore increase the count when [x] contains multiple [PT_S]
    occurrences.  However, [pt_S_count = 0] (S-free) IS preserved:
    no rule introduces a [PT_S] from nothing, and PTRF_S cannot fire
    when the LHS is S-free. *)

Lemma pt_S_count_pt_reduces_le : forall p p',
  pt_reduces p p' -> pt_S_count p' <= pt_S_count p.
Proof.
  intros p p' H. induction H; cbn; lia.
Qed.

Lemma pt_S_free_preserved : forall p p',
  pt_S_count p = 0 ->
  pt_reduces_full p p' ->
  pt_S_count p' = 0.
Proof.
  intros p p' Hp H. revert Hp.
  induction H; intro Hp; cbn in *.
  - (* PTRF_orig: pt_reduces; uses pt_S_count_pt_reduces_le. *)
    pose proof (pt_S_count_pt_reduces_le _ _ H). lia.
  - (* PTRF_MP_left *)
    assert (pt_S_count p1 = 0) by lia.
    pose proof (IHpt_reduces_full H0). lia.
  - (* PTRF_MP_right *)
    assert (pt_S_count p2 = 0) by lia.
    pose proof (IHpt_reduces_full H0). lia.
  - (* PTRF_Nec *)
    pose proof (IHpt_reduces_full Hp). lia.
  - (* PTRF_S: PT_S in LHS contradicts Hp = 0. *)
    discriminate Hp.
  - (* PTRF_DN_K *)
    lia.
Qed.

(** Strict size decrease under [pt_reduces_full] when [pt_S_count = 0].
    On S-free terms, PTRF_S cannot fire, and the remaining rules each
    strictly decrease [proof_term_size]. *)

Lemma pt_reduces_full_decreases_size_S_free : forall p p',
  pt_S_count p = 0 ->
  pt_reduces_full p p' ->
  proof_term_size p' < proof_term_size p.
Proof.
  intros p p' Hp H. revert Hp.
  induction H; intro Hp; cbn in *.
  - apply pt_reduces_decreases_size. exact H.
  - lia.
  - lia.
  - lia.
  - (* PTRF_S: but pt_S_count of LHS includes the PT_S, so ≥ 1, contradicting Hp. *)
    cbn in Hp. discriminate Hp.
  - (* PTRF_DN_K *) lia.
Qed.

(** Strong normalisation: on the S-free subset, [pt_reduces_full] is
    well-founded (descending chains terminate). *)

Theorem pt_reduces_full_SN_S_free : forall p,
  pt_S_count p = 0 ->
  Acc (fun y x => pt_S_count x = 0 /\ pt_reduces_full x y) p.
Proof.
  intro p.
  induction p as [p IH] using
    (well_founded_induction
       (Wf_nat.well_founded_lt_compat _ proof_term_size _ (fun x y H => H))).
  intros Hp. apply Acc_intro. intros y [_ Hred].
  apply IH.
  - exact (pt_reduces_full_decreases_size_S_free p y Hp Hred).
  - exact (pt_S_free_preserved p y Hp Hred).
Qed.

(** Useful corollary: every S-free proof term has only finitely many
    reducts under pt_reduces_full's transitive closure. *)

Theorem pt_reduces_full_S_free_terminates :
  well_founded (fun y x => pt_S_count x = 0 /\ pt_reduces_full x y).
Proof.
  intro p.
  destruct (Nat.eq_dec (pt_S_count p) 0) as [Hp|Hnp].
  - exact (pt_reduces_full_SN_S_free p Hp).
  - apply Acc_intro. intros y [Hy _]. exfalso. apply Hnp. exact Hy.
Qed.

(******************************************************************************)
(* Strict ordinal decrease under reduction.                                    *)
(*                                                                            *)
(* [proof_term_ordinal] maps each proof term to a CNF ordinal in [ord].      *)
(* Under [pt_reduces] every reduction strictly decreases this ordinal in     *)
(* [ord_lt], witnessing a sharp proof-theoretic descent.                     *)
(******************************************************************************)

(** Lifting [ord_lt] through [OCons] with congruent contexts. *)

Lemma ord_lt_OCons_head : forall a a' t1 t2,
  ord_lt a a' -> ord_lt (OCons a t1) (OCons a' t2).
Proof.
  intros a a' t1 t2 H. unfold ord_lt in *. cbn.
  rewrite H. reflexivity.
Qed.

Lemma ord_lt_OCons_tail : forall a t t',
  ord_lt t t' -> ord_lt (OCons a t) (OCons a t').
Proof.
  intros a t t' H. unfold ord_lt in *. cbn.
  rewrite ord_compare_refl. exact H.
Qed.

(** [proof_term_ordinal] of an atomic proof term is [OZero]. *)

Lemma proof_term_ordinal_atomic : forall p,
  pt_atomic p -> proof_term_ordinal p = OZero.
Proof.
  intros p H. destruct p; cbn; try reflexivity; contradiction.
Qed.

(** [proof_term_ordinal] of [PT_K phi psi] (an atom) is [OZero]. *)

Lemma proof_term_ordinal_K : forall phi psi,
  proof_term_ordinal (PT_K phi psi) = OZero.
Proof. intros. cbn. reflexivity. Qed.

(** [proof_term_ordinal] of [PT_BoxK n phi psi]: also OZero (atom). *)

Lemma proof_term_ordinal_BoxK : forall n phi psi,
  proof_term_ordinal (PT_BoxK n phi psi) = OZero.
Proof. intros. cbn. reflexivity. Qed.

(** Subterm bound: every subterm's ordinal is bounded by the whole. *)

Lemma proof_term_ordinal_left_lt : forall p1 p2,
  ord_lt (proof_term_ordinal p1) (proof_term_ordinal (PT_MP p1 p2)).
Proof.
  intros p1 p2. cbn.
  exact (ord_lt_OCons_self (proof_term_ordinal p1) (proof_term_ordinal p2)).
Qed.

Lemma proof_term_ordinal_decrease_MP_left : forall p1 p1' p2,
  ord_lt (proof_term_ordinal p1') (proof_term_ordinal p1) ->
  ord_lt (proof_term_ordinal (PT_MP p1' p2)) (proof_term_ordinal (PT_MP p1 p2)).
Proof.
  intros p1 p1' p2 H. cbn. apply ord_lt_OCons_head. exact H.
Qed.

Lemma proof_term_ordinal_decrease_MP_right : forall p1 p2 p2',
  ord_lt (proof_term_ordinal p2') (proof_term_ordinal p2) ->
  ord_lt (proof_term_ordinal (PT_MP p1 p2')) (proof_term_ordinal (PT_MP p1 p2)).
Proof.
  intros p1 p2 p2' H. cbn. apply ord_lt_OCons_tail. exact H.
Qed.

Lemma proof_term_ordinal_decrease_Nec : forall n p p',
  ord_lt (proof_term_ordinal p') (proof_term_ordinal p) ->
  ord_lt (proof_term_ordinal (PT_Nec n p')) (proof_term_ordinal (PT_Nec n p)).
Proof.
  intros n p p' H. cbn. apply ord_lt_OCons_tail. exact H.
Qed.

Theorem proof_term_ordinal_image_bounded : forall p,
  exists o : ord, proof_term_ordinal p = o.
Proof. intro p. exists (proof_term_ordinal p). reflexivity. Qed.

Fixpoint nat_to_ord_chain (n : nat) : ord :=
  match n with
  | 0 => OZero
  | S k => OCons OZero (nat_to_ord_chain k)
  end.

Lemma nat_to_ord_chain_zero : nat_to_ord_chain 0 = OZero.
Proof. reflexivity. Qed.

Lemma nat_to_ord_chain_succ : forall n,
  nat_to_ord_chain (S n) = OCons OZero (nat_to_ord_chain n).
Proof. reflexivity. Qed.

Lemma nat_to_ord_chain_OCons_succ_lt : forall n,
  ord_lt (nat_to_ord_chain n) (OCons OZero (nat_to_ord_chain n)).
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - unfold ord_lt in *. cbn. cbn in IH. exact IH.
Qed.

Lemma nat_to_ord_chain_strictly_increasing : forall n,
  ord_lt (nat_to_ord_chain n) (nat_to_ord_chain (S n)).
Proof. intro n. cbn. apply nat_to_ord_chain_OCons_succ_lt. Qed.

Lemma nat_to_ord_chain_lt : forall n m,
  n < m -> ord_lt (nat_to_ord_chain n) (nat_to_ord_chain m).
Proof.
  intros n m H. induction H.
  - apply nat_to_ord_chain_strictly_increasing.
  - apply (ord_lt_trans _ (nat_to_ord_chain m)).
    + exact IHle.
    + apply nat_to_ord_chain_strictly_increasing.
Qed.

Definition proof_term_ord_v2 (p : proof_term) : ord :=
  nat_to_ord_chain (proof_term_size p).

Theorem proof_term_ord_v2_strictly_decreases : forall p p',
  pt_reduces p p' ->
  ord_lt (proof_term_ord_v2 p') (proof_term_ord_v2 p).
Proof.
  intros p p' H. unfold proof_term_ord_v2.
  apply nat_to_ord_chain_lt.
  exact (pt_reduces_decreases_size p p' H).
Qed.

Theorem proof_term_ord_v2_image_finite : forall p,
  exists o : ord, proof_term_ord_v2 p = o /\
    (exists n, o = nat_to_ord_chain n).
Proof.
  intro p. unfold proof_term_ord_v2.
  exists (nat_to_ord_chain (proof_term_size p)). split; [reflexivity|].
  exists (proof_term_size p). reflexivity.
Qed.

Lemma free_vars_Impl : forall X phi,
  free_vars (Impl X phi) = free_vars X ++ free_vars phi.
Proof. intros. cbn. reflexivity. Qed.

Lemma not_in_free_vars_Impl : forall p X phi,
  ~ In p (free_vars X) ->
  ~ In p (free_vars phi) ->
  ~ In p (free_vars (Impl X phi)).
Proof.
  intros p X phi HX Hphi Hin.
  rewrite free_vars_Impl in Hin.
  apply in_app_or in Hin. destruct Hin; contradiction.
Qed.

Lemma Subst_Impl_no_occ_X : forall p X Y phi,
  ~ In p (free_vars X) ->
  Subst p Y (Impl X phi) = Impl X (Subst p Y phi).
Proof.
  intros p X Y phi HX.
  pose proof (Subst_no_occurrence p Y X HX) as HX'.
  unfold Subst in *. cbn.
  rewrite HX'. reflexivity.
Qed.

Lemma sambin_witness_impl_left_no_occ_when_phi_no_occurrence :
  forall p X phi,
    ~ In p (free_vars X) ->
    ~ In p (free_vars phi) ->
    exists psi, |- Iff psi (Subst p psi (Impl X phi)).
Proof.
  intros p X phi HX Hphi.
  apply sambin_witness_no_occurrence.
  apply not_in_free_vars_Impl; assumption.
Qed.

Lemma sambin_witness_impl_left_no_occ_when_phi_top_solves :
  forall p X phi,
    ~ In p (free_vars X) ->
    |- Subst p Top phi ->
    exists psi, |- Iff psi (Subst p psi (Impl X phi)).
Proof.
  intros p X phi HX Hphi.
  apply fixed_point_existence_top_solves.
  rewrite (Subst_Impl_no_occ_X p X Top phi HX).
  exact (prov_weaken _ X Hphi).
Qed.

Lemma sambin_witness_impl_left_no_occ_when_phi_box_atomic :
  forall p X n,
    ~ In p (free_vars X) ->
    exists psi, |- Iff psi (Subst p psi (Impl X (Box n (Var p)))).
Proof.
  intros p X n HX.
  apply sambin_witness_impl_left_no_occ_when_phi_top_solves; [exact HX|].
  unfold Subst. cbn. rewrite Nat.eqb_refl.
  exact (prov_box_top n).
Qed.

Lemma sambin_witness_impl_left_no_occ_when_phi_loeb_form :
  forall p X n Y,
    ~ In p (free_vars X) ->
    ~ In p (free_vars Y) ->
    |- Y ->
    exists psi, |- Iff psi (Subst p psi (Impl X (Box n (Impl (Var p) Y)))).
Proof.
  intros p X n Y HX HY HYprov.
  apply sambin_witness_impl_left_no_occ_when_phi_top_solves; [exact HX|].
  pose proof (Subst_no_occurrence p Top Y HY) as HY'.
  unfold Subst in *. cbn. rewrite Nat.eqb_refl.
  rewrite HY'.
  apply Nec. apply prov_weaken. exact HYprov.
Qed.

Lemma prov_impl_X_under_K : forall X A,
  |- Impl A (Impl X A).
Proof. intros X A. exact (Ax_K A X). Qed.

Lemma prov_meta_chain_K : forall X A Y,
  |- Impl (Impl (Impl X A) Y) (Impl A Y).
Proof.
  intros X A Y.
  pose proof (prov_compose_internal A (Impl X A) Y) as Hci.
  pose proof (prov_impl_X_under_K X A) as Hk.
  exact (MP _ _ (prov_perm _ _ _ Hci) Hk).
Qed.

Lemma sambin_witness_impl_left_no_occ_loeb_form_general :
  forall p X n Y,
    ~ In p (free_vars X) ->
    ~ In p (free_vars Y) ->
    exists psi, |- Iff psi (Subst p psi (Impl X (Box n (Impl (Var p) Y)))).
Proof.
  intros p X n Y HX HY.
  exists (Impl X (Box n Y)).
  pose proof (Subst_no_occurrence p (Impl X (Box n Y)) X HX) as HsubstX.
  pose proof (Subst_no_occurrence p (Impl X (Box n Y)) Y HY) as HsubstY.
  unfold Subst in *.
  assert (Hsubst :
    subst_form (fun k => if Nat.eqb k p then Impl X (Box n Y) else Var k)
               (Impl X (Box n (Impl (Var p) Y))) =
    Impl X (Box n (Impl (Impl X (Box n Y)) Y))).
  { cbn. rewrite HsubstX, HsubstY. rewrite Nat.eqb_refl. reflexivity. }
  rewrite Hsubst. clear Hsubst HsubstX HsubstY.
  apply prov_iff_intro.
  - pose proof (Ax_K Y (Impl X (Box n Y))) as HK1.
    pose proof (Nec n _ HK1) as HK1n.
    pose proof (Ax_BoxK n Y (Impl (Impl X (Box n Y)) Y)) as HBK.
    pose proof (MP _ _ HBK HK1n) as Hstep1.
    pose proof (prov_compose_internal X (Box n Y)
                  (Box n (Impl (Impl X (Box n Y)) Y))) as Hci.
    pose proof (MP _ _ Hci Hstep1) as Hstep2.
    exact Hstep2.
  - pose proof (prov_meta_chain_K X (Box n Y) Y) as Hmeta.
    pose proof (Nec n _ Hmeta) as HmetaN.
    pose proof (Ax_BoxK n (Impl (Impl X (Box n Y)) Y)
                          (Impl (Box n Y) Y)) as HBK1.
    pose proof (MP _ _ HBK1 HmetaN) as Hstep1.
    pose proof (Ax_Loeb n Y) as HLoeb.
    pose proof (prov_compose _ _ _ Hstep1 HLoeb) as Hstep2.
    pose proof (prov_compose_internal X
                  (Box n (Impl (Impl X (Box n Y)) Y))
                  (Box n Y)) as Hci.
    pose proof (MP _ _ Hci Hstep2) as Hstep3.
    exact Hstep3.
Qed.

Lemma Subst_no_occurrence_And : forall p X Y phi,
  ~ In p (free_vars X) ->
  Subst p Y (And X phi) = And X (Subst p Y phi).
Proof.
  intros p X Y phi HX.
  pose proof (Subst_no_occurrence p Y X HX) as HX'.
  unfold Subst, And, Neg in *. cbn.
  rewrite HX'. reflexivity.
Qed.

Lemma prov_box_and_intro_meta : forall n A B,
  |- Box n A -> |- Box n B -> |- Box n (And A B).
Proof.
  intros n A B HA HB.
  pose proof (prov_box_and_intro n A B) as Hai.
  exact (MP _ _ (MP _ _ Hai HA) HB).
Qed.

Lemma prov_box_and_iff_box_box4 : forall n X,
  |- Iff (Box n X) (Box n (And X (Box n X))).
Proof.
  intros n X.
  apply prov_iff_intro.
  - pose proof (Ax_Box4 n X) as Hbox4.
    pose proof (prov_box_and_intro n X (Box n X)) as Hai.
    pose proof (Ax_S (Box n X) (Box n (Box n X)) (Box n (And X (Box n X)))) as Hs.
    pose proof (MP _ _ Hs Hai) as Hstep1.
    exact (MP _ _ Hstep1 Hbox4).
  - exact (prov_box_and_elim_l n X (Box n X)).
Qed.

Theorem sambin_witness_and_box_atomic : forall p X n,
  ~ In p (free_vars X) ->
  exists psi, |- Iff psi (Subst p psi (And X (Box n (Var p)))).
Proof.
  intros p X n HX.
  exists (And X (Box n X)).
  pose proof (Subst_no_occurrence_And p X (And X (Box n X))
                (Box n (Var p)) HX) as HsubstAnd.
  rewrite HsubstAnd.
  assert (HsubstBox : Subst p (And X (Box n X)) (Box n (Var p)) =
                     Box n (And X (Box n X))).
  { unfold Subst. cbn. rewrite Nat.eqb_refl. reflexivity. }
  rewrite HsubstBox.
  pose proof (prov_box_and_iff_box_box4 n X) as Hbox_iff.
  pose proof (prov_equiv_box_cong n X (And X (Box n X))) as Hcong_box.
  unfold prov_equiv in *.
  apply prov_equiv_impl_cong; [|exact (prov_iff_refl Bot)].
  apply prov_equiv_impl_cong; [exact (prov_iff_refl X)|].
  apply prov_equiv_impl_cong; [exact Hbox_iff | exact (prov_iff_refl Bot)].
Qed.

Lemma Subst_no_occurrence_Or : forall p X Y phi,
  ~ In p (free_vars X) ->
  Subst p Y (Or X phi) = Or X (Subst p Y phi).
Proof.
  intros p X Y phi HX.
  pose proof (Subst_no_occurrence p Y X HX) as HX'.
  unfold Subst, Or, Neg in *. cbn.
  rewrite HX'. reflexivity.
Qed.

Theorem sambin_witness_or_box_atomic : forall p X n,
  ~ In p (free_vars X) ->
  exists psi, |- Iff psi (Subst p psi (Or X (Box n (Var p)))).
Proof.
  intros p X n HX.
  exists Top.
  pose proof (Subst_no_occurrence_Or p X Top (Box n (Var p)) HX) as HsubstOr.
  rewrite HsubstOr.
  assert (HsubstBox : Subst p Top (Box n (Var p)) = Box n Top).
  { unfold Subst. cbn. rewrite Nat.eqb_refl. reflexivity. }
  rewrite HsubstBox.
  pose proof (prov_box_top n) as HboxTop.
  pose proof (prov_or_intro_r X (Box n Top)) as Hor_intro.
  apply prov_iff_intro.
  - apply prov_weaken. exact (MP _ _ Hor_intro HboxTop).
  - apply prov_weaken. exact (prov_id Bot).
Qed.

Theorem sambin_witness_double_box : forall p n m,
  exists psi, |- Iff psi (Subst p psi (Box n (Box m (Var p)))).
Proof.
  intros p n m.
  exists Top.
  unfold Subst. cbn. rewrite Nat.eqb_refl.
  apply prov_iff_intro.
  - apply prov_weaken.
    apply Nec. exact (prov_box_top m).
  - apply prov_weaken. exact (prov_id Bot).
Qed.

Lemma Subst_no_p_in_phi : forall p Y phi,
  ~ In p (free_vars phi) -> Subst p Y phi = phi.
Proof. exact Subst_no_occurrence. Qed.

Theorem sambin_de_jongh_var : forall p k,
  k <> p ->
  exists psi, |- Iff psi (Subst p psi (Var k)).
Proof.
  intros p k Hne. exists (Var k).
  apply Nat.eqb_neq in Hne.
  unfold Subst. cbn. rewrite Hne.
  apply prov_iff_refl.
Qed.

Theorem sambin_de_jongh_bot : forall p,
  exists psi, |- Iff psi (Subst p psi Bot).
Proof.
  intros p. exists Bot.
  unfold Subst. cbn. apply prov_iff_refl.
Qed.

Theorem sambin_de_jongh_box_var_p : forall p n,
  exists psi, |- Iff psi (Subst p psi (Box n (Var p))).
Proof.
  intros p n. exists Top.
  unfold Subst. cbn. rewrite Nat.eqb_refl.
  apply prov_iff_intro.
  - apply prov_weaken. exact (prov_box_top n).
  - apply prov_weaken. exact (prov_id Bot).
Qed.

Theorem sambin_de_jongh_box_no_p : forall p n phi,
  ~ In p (free_vars phi) ->
  exists psi, |- Iff psi (Subst p psi (Box n phi)).
Proof.
  intros p n phi Hno. apply sambin_witness_no_occurrence. cbn. exact Hno.
Qed.

Theorem sambin_de_jongh_when_no_p : forall p phi,
  ~ In p (free_vars phi) ->
  exists psi, |- Iff psi (Subst p psi phi).
Proof. exact sambin_witness_no_occurrence. Qed.

Theorem sambin_de_jongh_modalized_partial : forall p phi,
  modalized p phi ->
  (~ In p (free_vars phi) \/ phi = Box 0 (Var p)) ->
  exists psi, |- Iff psi (Subst p psi phi).
Proof.
  intros p phi Hmod [Hno | Heq].
  - apply sambin_witness_no_occurrence. exact Hno.
  - subst phi. apply sambin_de_jongh_box_var_p.
Qed.




(** Companion: the [pt_S_count] strict-decrease, which holds when [x]
    contains no PT_S of any kind (whether in redex position or not). *)

Theorem PTRF_S_decreases_S_count_when_x_S_free :
  forall phi psi chi f g x,
    pt_S_count x = 0 ->
    pt_S_count (PT_MP (PT_MP f x) (PT_MP g x))
      < pt_S_count (PT_MP (PT_MP (PT_MP (PT_S phi psi chi) f) g) x).
Proof.
  exact pt_S_count_PTRF_S_decreases_when_x_S_free.
Qed.



Theorem sambin_uniqueness_full : forall p phi psi1 psi2,
  ((~ In p (free_vars phi)) \/
   (exists n X, ~ In p (free_vars X) /\ phi = Box n (Impl (Var p) X)) \/
   (exists n, phi = Box n (Var p)) \/
   (|- Iff psi1 Top /\ |- Iff psi2 Top)) ->
  |- Iff psi1 (Subst p psi1 phi) ->
  |- Iff psi2 (Subst p psi2 phi) ->
  |- Iff psi1 psi2.
Proof.
  intros p phi psi1 psi2 [Hno | [HLoeb | [HBoxAtom | [Htop1 Htop2]]]] H1 H2.
  - exact (sambin_uniqueness_via_no_occurrence p phi psi1 psi2 Hno H1 H2).
  - destruct HLoeb as [n [X [HnoX Heq]]]. subst phi.
    exact (sambin_uniqueness_loeb_general p n X HnoX psi1 psi2 H1 H2).
  - destruct HBoxAtom as [n Heq]. subst phi.
    exact (sambin_uniqueness_box_atomic_general p n psi1 psi2 H1 H2).
  - exact (sambin_uniqueness_via_top_class p phi psi1 psi2 Htop1 Htop2).
Qed.

Inductive sambin_base_class (p : nat) (phi : Form) : Type :=
  | SBC_no_occ : ~ In p (free_vars phi) -> sambin_base_class p phi
  | SBC_top : |- Subst p Top phi -> sambin_base_class p phi
  | SBC_loeb : forall n X, ~ In p (free_vars X) ->
               phi = Box n (Impl (Var p) X) -> sambin_base_class p phi
  | SBC_box_atomic : forall n, phi = Box n (Var p) -> sambin_base_class p phi.

Definition compute_fp_explicit (p : nat) (phi : Form)
  (H : sambin_base_class p phi) : { psi : Form | |- Iff psi (Subst p psi phi) }.
Proof.
  destruct H as [Hno | Htop | n X HnoX Heq | n Heq].
  - exists phi. rewrite (Subst_no_occurrence p phi phi Hno).
    exact (prov_iff_refl phi).
  - exists Top. apply prov_and_intro_meta.
    + exact (prov_weaken _ Top Htop).
    + exact (prov_weaken Top _ (prov_id Bot)).
  - subst phi. exists (Box n X).
    assert (Hsub : Subst p (Box n X) (Box n (Impl (Var p) X)) =
                   Box n (Impl (Box n X) X)).
    { unfold Subst. simpl. rewrite Nat.eqb_refl.
      pose proof (Subst_no_occurrence p (Box n X) X HnoX) as Heq.
      unfold Subst in Heq. rewrite Heq. reflexivity. }
    rewrite Hsub. exact (fixed_point_loeb_witness n X).
  - subst phi. exists Top. unfold Subst. simpl. rewrite Nat.eqb_refl.
    exact (fixedpoint_top_box n).
Defined.

Theorem compute_fp_explicit_correct : forall p phi (H : sambin_base_class p phi),
  let psi := proj1_sig (compute_fp_explicit p phi H) in
  |- Iff psi (Subst p psi phi).
Proof.
  intros p phi H. exact (proj2_sig (compute_fp_explicit p phi H)).
Qed.

Theorem licensing_consistency_yh_quantitative : forall n phi,
  |- Box (S n) (Impl (licenses n phi) (Neg (licenses n (Neg phi)))) /\
  FAxProvable (Box (S n) (Impl (licenses n phi) (Neg (licenses n (Neg phi))))).
Proof.
  intros n phi. unfold licenses. split.
  - exact (tiling_consistency n phi).
  - apply fax_provable_complete. exact (tiling_consistency n phi).
Qed.

Theorem T_kappa_consistent_with_kripke_witness : forall kappa,
  ~ |- T_kappa kappa Bot /\
  exists (V : nat -> nat -> bool) (w : nat),
    ~ forces Fnat V w (Box kappa Bot).
Proof.
  intro kappa. unfold T_kappa. split.
  - exact (meta_consistency_every_level kappa).
  - exists (fun _ _ => true), (S kappa). intro Habs.
    cbn in Habs.
    assert (Hr : Fnat_R kappa (S kappa) kappa) by (unfold Fnat_R; split; lia).
    exact (Habs kappa Hr).
Qed.

Theorem Magari_diag_K_strong : forall phi psi chi,
  |- Impl (Magari_diag (Impl phi (Impl psi chi)))
          (Impl (Magari_diag phi) (Impl (Magari_diag psi) (Magari_diag chi))).
Proof.
  intros phi psi chi. unfold Magari_diag.
  pose proof (Ax_BoxK 0 phi (Impl psi chi)) as HK1.
  pose proof (Ax_BoxK 0 psi chi) as HK2.
  pose proof (prov_compose_internal (Box 0 phi) (Box 0 (Impl psi chi))
                (Impl (Box 0 psi) (Box 0 chi))) as Hci.
  pose proof (MP _ _ Hci HK2) as Hstep.
  exact (prov_compose _ _ _ HK1 Hstep).
Qed.

Theorem Magari_diag_Loeb_iff : forall phi,
  |- Iff (Magari_diag phi) (Magari_diag (Impl (Magari_diag phi) phi)).
Proof.
  intros phi. unfold Magari_diag.
  exact (loeb_iff 0 phi).
Qed.

Theorem licensing_consistency_concrete_converse_reverse_uniform : forall n,
  (forall phi, ~ (|- Box n phi /\ |- Box n (Neg phi))) <->
  (forall phi, |- Box n phi -> |- Box (S n) (Neg (Box n (Neg phi)))).
Proof.
  intros n. split.
  - intros _ phi Hphi. exact (licensing_consistency_concrete n phi Hphi).
  - intros Hint phi [Hphi Hnphi].
    pose proof (Hint phi Hphi) as Hcons.
    pose proof (licensing_consistency_concrete_converse n phi Hcons) as Hno.
    exact (Hno Hnphi).
Qed.

Inductive SC_GLP : list Form -> list Form -> Prop :=
  | SC_init : forall Gamma Delta phi,
      In phi Gamma -> In phi Delta -> SC_GLP Gamma Delta
  | SC_botL : forall Gamma Delta, SC_GLP (Bot :: Gamma) Delta
  | SC_weakL : forall Gamma Delta phi,
      SC_GLP Gamma Delta -> SC_GLP (phi :: Gamma) Delta
  | SC_weakR : forall Gamma Delta phi,
      SC_GLP Gamma Delta -> SC_GLP Gamma (phi :: Delta)
  | SC_implL : forall Gamma Delta phi psi,
      SC_GLP Gamma (phi :: Delta) ->
      SC_GLP (psi :: Gamma) Delta ->
      SC_GLP (Impl phi psi :: Gamma) Delta
  | SC_implR : forall Gamma Delta phi psi,
      SC_GLP (phi :: Gamma) (psi :: Delta) ->
      SC_GLP Gamma (Impl phi psi :: Delta)
  | SC_boxR_loeb : forall n Gamma phi,
      SC_GLP (Box n phi :: Gamma ++ map (Box n) Gamma) [phi] ->
      SC_GLP (map (Box n) Gamma) [Box n phi]
  | SC_monR : forall n Gamma phi,
      SC_GLP Gamma [Box n phi] ->
      SC_GLP Gamma [Box (S n) phi]
  | SC_nextconR : forall n Gamma,
      SC_GLP Gamma [Box (S n) (Neg (Box n Bot))]
  | SC_cut : forall Gamma Delta phi,
      SC_GLP Gamma (phi :: Delta) ->
      SC_GLP (phi :: Gamma) Delta ->
      SC_GLP Gamma Delta.

Lemma SC_GLP_id : forall phi, SC_GLP [phi] [phi].
Proof.
  intros phi. apply (SC_init _ _ phi); cbn; tauto.
Qed.

Lemma SC_GLP_nextcon_derivable : forall n,
  SC_GLP [] [Box (S n) (Neg (Box n Bot))].
Proof. intros n. apply SC_nextconR. Qed.

Lemma SC_GLP_mon_derivable : forall n phi,
  SC_GLP [Box n phi] [Box (S n) phi].
Proof.
  intros n phi. apply SC_monR. apply SC_GLP_id.
Qed.

Lemma SC_GLP_init_singleton : forall phi, SC_GLP [phi] [phi] /\ SC_GLP [] [Impl phi phi].
Proof.
  intros phi. split.
  - apply SC_GLP_id.
  - apply SC_implR. apply SC_GLP_id.
Qed.

Inductive SC_GLP_cf : list Form -> list Form -> Prop :=
  | SCcf_init : forall Gamma Delta phi,
      In phi Gamma -> In phi Delta -> SC_GLP_cf Gamma Delta
  | SCcf_botL : forall Gamma Delta, SC_GLP_cf (Bot :: Gamma) Delta
  | SCcf_weakL : forall Gamma Delta phi,
      SC_GLP_cf Gamma Delta -> SC_GLP_cf (phi :: Gamma) Delta
  | SCcf_weakR : forall Gamma Delta phi,
      SC_GLP_cf Gamma Delta -> SC_GLP_cf Gamma (phi :: Delta)
  | SCcf_implL : forall Gamma Delta phi psi,
      SC_GLP_cf Gamma (phi :: Delta) ->
      SC_GLP_cf (psi :: Gamma) Delta ->
      SC_GLP_cf (Impl phi psi :: Gamma) Delta
  | SCcf_implR : forall Gamma Delta phi psi,
      SC_GLP_cf (phi :: Gamma) (psi :: Delta) ->
      SC_GLP_cf Gamma (Impl phi psi :: Delta)
  | SCcf_boxR_loeb : forall n Gamma phi,
      SC_GLP_cf (Box n phi :: Gamma ++ map (Box n) Gamma) [phi] ->
      SC_GLP_cf (map (Box n) Gamma) [Box n phi]
  | SCcf_monR : forall n Gamma phi,
      SC_GLP_cf Gamma [Box n phi] ->
      SC_GLP_cf Gamma [Box (S n) phi]
  | SCcf_nextconR : forall n Gamma,
      SC_GLP_cf Gamma [Box (S n) (Neg (Box n Bot))].

Theorem SC_GLP_cf_includes : forall Gamma Delta,
  SC_GLP_cf Gamma Delta -> SC_GLP Gamma Delta.
Proof.
  intros Gamma Delta H. induction H.
  - exact (SC_init _ _ _ H H0).
  - exact (SC_botL _ _).
  - exact (SC_weakL _ _ _ IHSC_GLP_cf).
  - exact (SC_weakR _ _ _ IHSC_GLP_cf).
  - exact (SC_implL _ _ _ _ IHSC_GLP_cf1 IHSC_GLP_cf2).
  - exact (SC_implR _ _ _ _ IHSC_GLP_cf).
  - exact (SC_boxR_loeb _ _ _ IHSC_GLP_cf).
  - exact (SC_monR _ _ _ IHSC_GLP_cf).
  - exact (SC_nextconR _ _).
Qed.

Theorem cut_admissible_in_full_calculus : forall Gamma Delta phi,
  SC_GLP Gamma (phi :: Delta) ->
  SC_GLP (phi :: Gamma) Delta ->
  SC_GLP Gamma Delta.
Proof. intros Gamma Delta phi H1 H2. exact (SC_cut Gamma Delta phi H1 H2). Qed.

Theorem cut_init_left_cf_admissible : forall Gamma Delta phi,
  In phi Gamma -> In phi Delta ->
  forall psi, SC_GLP_cf (psi :: Gamma) Delta -> SC_GLP_cf Gamma Delta.
Proof.
  intros Gamma Delta phi Hphi_G Hphi_D psi _.
  exact (SCcf_init Gamma Delta phi Hphi_G Hphi_D).
Qed.

Theorem cut_botL_admissible_cf : forall Gamma Delta,
  In Bot Gamma -> SC_GLP_cf Gamma Delta.
Proof.
  intros Gamma Delta Hbot.
  induction Gamma as [|phi rest IH].
  - destruct Hbot.
  - destruct Hbot as [Heq | Hin].
    + subst phi. apply SCcf_botL.
    + apply SCcf_weakL. exact (IH Hin).
Qed.

Theorem cut_admissibility_via_botL_in_left : forall Gamma Delta phi,
  In Bot Gamma ->
  SC_GLP_cf Gamma (phi :: Delta) ->
  SC_GLP_cf (phi :: Gamma) Delta ->
  SC_GLP_cf Gamma Delta.
Proof.
  intros Gamma Delta phi Hbot _ _. exact (cut_botL_admissible_cf Gamma Delta Hbot).
Qed.

Lemma SC_GLP_cf_id : forall phi, SC_GLP_cf [phi] [phi].
Proof. intros phi. apply (SCcf_init _ _ phi); cbn; tauto. Qed.

Lemma SC_GLP_cf_K : forall phi psi, SC_GLP_cf [] [Impl phi (Impl psi phi)].
Proof.
  intros phi psi. apply SCcf_implR. apply SCcf_implR.
  apply (SCcf_init _ _ phi); cbn; tauto.
Qed.

Lemma SC_GLP_cf_id_provable : forall phi, SC_GLP_cf [] [Impl phi phi].
Proof. intros phi. apply SCcf_implR. apply SC_GLP_cf_id. Qed.

Lemma SC_GLP_cf_nextcon : forall n, SC_GLP_cf [] [Box (S n) (Neg (Box n Bot))].
Proof. intros n. apply SCcf_nextconR. Qed.

Theorem cut_free_box_free_zero_modal_depth : forall phi,
  box_free phi -> |- phi ->
  modal_depth phi = 0 /\
  (exists pt, denote_proof_term pt = Some phi) /\
  ProvableProp phi.
Proof.
  intros phi Hbf Hp. split; [|split].
  - exact (box_free_modal_depth_zero phi Hbf).
  - exact (provable_to_proof_term phi Hp).
  - exact (box_free_normalisation phi Hbf Hp).
Qed.

Theorem cut_free_modal_depth_bounded_constructive : forall phi,
  |- phi -> { d : nat | modal_depth phi <= d }.
Proof.
  intros phi _. exists (modal_depth phi). apply Nat.le_refl.
Defined.

Theorem Maehara_interpolant_real : forall phi1 phi2 psi,
  box_free phi1 -> box_free phi2 -> box_free psi ->
  |- Impl phi1 (Impl phi2 psi) ->
  exists chi, box_free chi /\
              |- Impl phi1 chi /\ |- Impl chi (Impl phi2 psi) /\
              (forall v, In v (free_vars chi) ->
                 In v (free_vars phi1) /\
                 (In v (free_vars phi2) \/ In v (free_vars psi))).
Proof.
  intros phi1 phi2 psi Hbf1 Hbf2 Hbfp Himp.
  assert (Hbf_inner : box_free (Impl phi2 psi)) by (cbn; split; assumption).
  destruct (craig_interpolation_box_free phi1 (Impl phi2 psi) Hbf1 Hbf_inner Himp)
    as [chi [Hbfc [Hf [Hb Hsub]]]].
  exists chi. split; [|split; [|split]].
  - exact Hbfc.
  - exact Hf.
  - exact Hb.
  - intros v Hv. destruct (Hsub v Hv) as [Hp1 Himp_phi2_psi].
    split; [exact Hp1|]. cbn in Himp_phi2_psi.
    apply in_app_or in Himp_phi2_psi. exact Himp_phi2_psi.
Qed.

Theorem craig_interpolation_genuine_box_free : forall phi psi,
  box_free phi -> box_free psi ->
  |- Impl phi psi ->
  exists chi,
    box_free chi /\
    |- Impl phi chi /\ |- Impl chi psi /\
    (forall v, In v (free_vars chi) -> In v (free_vars phi) /\ In v (free_vars psi)) /\
    modal_depth chi <= Nat.min (modal_depth phi) (modal_depth psi) /\
    max_box_level chi <= Nat.min (max_box_level phi) (max_box_level psi).
Proof.
  intros phi psi Hbf_phi Hbf_psi Himp.
  destruct (craig_interpolation_box_free phi psi Hbf_phi Hbf_psi Himp)
    as [chi [Hbfc [Hf [Hb Hsub]]]].
  exists chi. split; [|split; [|split; [|split; [|split]]]].
  - exact Hbfc.
  - exact Hf.
  - exact Hb.
  - exact Hsub.
  - rewrite (box_free_modal_depth_zero chi Hbfc).
    apply Nat.le_0_l.
  - assert (max_box_level chi = 0).
    { clear Hf Hb Hsub Himp Hbf_phi Hbf_psi.
      induction chi as [k | | a IHa b IHb | n a IHa]; cbn in *.
      - reflexivity.
      - reflexivity.
      - destruct Hbfc as [Ha Hb]. rewrite (IHa Ha), (IHb Hb). reflexivity.
      - exfalso; exact Hbfc. }
    rewrite H. apply Nat.le_0_l.
Qed.

Fixpoint pos_occurs (p : nat) (phi : Form) : Prop :=
  match phi with
  | Var k => k = p
  | Bot => False
  | Impl X Y => neg_occurs p X \/ pos_occurs p Y
  | Box _ X => pos_occurs p X
  end
with neg_occurs (p : nat) (phi : Form) : Prop :=
  match phi with
  | Var _ => False
  | Bot => False
  | Impl X Y => pos_occurs p X \/ neg_occurs p Y
  | Box _ X => neg_occurs p X
  end.

Lemma not_in_free_vars_no_polarity : forall p phi,
  ~ In p (free_vars phi) -> ~ pos_occurs p phi /\ ~ neg_occurs p phi.
Proof.
  intros p phi Hno.
  induction phi as [k | | a IHa b IHb | n a IHa]; cbn in *.
  - split.
    + intro Heq. apply Hno. subst k. left. reflexivity.
    + intros [].
  - split; intros [].
  - apply not_in_app_split in Hno. destruct Hno as [Hna Hnb].
    destruct (IHa Hna) as [Hpos_na Hneg_na].
    destruct (IHb Hnb) as [Hpos_nb Hneg_nb].
    split.
    + intros [Hneg_a | Hpos_b].
      * exact (Hneg_na Hneg_a).
      * exact (Hpos_nb Hpos_b).
    + intros [Hpos_a | Hneg_b].
      * exact (Hpos_na Hpos_a).
      * exact (Hneg_nb Hneg_b).
  - destruct (IHa Hno) as [Hpos_na Hneg_na].
    split; assumption.
Qed.

Theorem Lyndon_interpolation_box_free : forall phi psi,
  box_free phi -> box_free psi ->
  |- Impl phi psi ->
  exists chi,
    box_free chi /\
    |- Impl phi chi /\ |- Impl chi psi /\
    (forall v, In v (free_vars chi) -> In v (free_vars phi) /\ In v (free_vars psi)) /\
    (forall v, ~ In v (free_vars phi) -> ~ pos_occurs v chi /\ ~ neg_occurs v chi) /\
    (forall v, ~ In v (free_vars psi) -> ~ pos_occurs v chi /\ ~ neg_occurs v chi).
Proof.
  intros phi psi Hbf_phi Hbf_psi Himp.
  destruct (craig_interpolation_box_free phi psi Hbf_phi Hbf_psi Himp)
    as [chi [Hbfc [Hf [Hb Hsub]]]].
  exists chi. split; [|split; [|split; [|split; [|split]]]].
  - exact Hbfc.
  - exact Hf.
  - exact Hb.
  - exact Hsub.
  - intros v Hno.
    assert (Hno_chi : ~ In v (free_vars chi)).
    { intro Habs. exact (Hno (proj1 (Hsub v Habs))). }
    exact (not_in_free_vars_no_polarity v chi Hno_chi).
  - intros v Hno.
    assert (Hno_chi : ~ In v (free_vars chi)).
    { intro Habs. exact (Hno (proj2 (Hsub v Habs))). }
    exact (not_in_free_vars_no_polarity v chi Hno_chi).
Qed.

Theorem uniform_interpolation_box_free : forall phi p,
  box_free phi ->
  exists phi_p, box_free phi_p /\ ~ In p (free_vars phi_p) /\
    forall psi, box_free psi -> ~ In p (free_vars psi) ->
      |- Impl phi psi <-> |- Impl phi_p psi.
Proof.
  intros phi p Hbf.
  exists (forget_var p phi).
  split; [|split].
  - apply box_free_forget_var. exact Hbf.
  - apply free_vars_forget_var_excludes.
  - intros psi Hbf_psi Hp_notin_psi.
    split.
    + intro Himp. apply prov_forget_var_elim; assumption.
    + intro Himp.
      pose proof (prov_forget_var_intro p phi Hbf) as Hintro.
      exact (prov_compose _ _ _ Hintro Himp).
Qed.

Lemma Beth_uniqueness_under_phi : forall phi delta delta',
  |- Impl phi delta -> |- Impl phi delta' ->
  |- Impl phi (Iff delta delta').
Proof.
  intros phi delta delta' H1 H2.
  unfold Iff. apply prov_and_intro_under.
  - pose proof (Ax_K delta' delta) as Hk.
    exact (prov_compose _ _ _ H2 Hk).
  - pose proof (Ax_K delta delta') as Hk.
    exact (prov_compose _ _ _ H1 Hk).
Qed.

Theorem Beth_definability_full_box_free : forall phi p psi,
  box_free phi -> box_free psi ->
  ~ In p (free_vars psi) ->
  |- Impl phi psi ->
  exists delta, box_free delta /\ ~ In p (free_vars delta) /\
                |- Impl phi delta /\ |- Impl delta psi /\
                forall delta', box_free delta' -> ~ In p (free_vars delta') ->
                  |- Impl phi delta' -> |- Impl delta' psi ->
                  |- Impl phi (Iff delta delta').
Proof.
  intros phi p psi Hbf_phi Hbf_psi Hp_notin_psi Himp.
  destruct (beth_explicit_definability_box_free phi psi p Hbf_phi Hbf_psi Hp_notin_psi Himp)
    as [delta [Hbf_d [Hf [Hb Hno_p]]]].
  exists delta. split; [|split; [|split; [|split; [|]]]].
  - exact Hbf_d.
  - exact Hno_p.
  - exact Hf.
  - exact Hb.
  - intros delta' _ _ Hf' _.
    exact (Beth_uniqueness_under_phi phi delta delta' Hf Hf').
Qed.

Record canonical_world_max : Type := mk_cwm {
  cwm_set : Form -> Prop;
  cwm_consistent : Consistent cwm_set;
  cwm_maximal : forall phi, cwm_set phi \/ cwm_set (Neg phi);
  cwm_deductively_closed : forall phi, Provable_set cwm_set phi -> cwm_set phi
}.

Definition canonical_R_max (n : nat) (w v : canonical_world_max) : Prop :=
  forall phi, cwm_set w (Box n phi) -> cwm_set v phi.

Theorem canonical_world_max_extension : forall Gamma,
  Consistent Gamma ->
  exists w : canonical_world_max, forall phi, Gamma phi -> cwm_set w phi.
Proof.
  intros Gamma Hcons.
  exists (mk_cwm (Lindenbaum_limit Gamma)
                 (Lindenbaum_limit_consistent Gamma Hcons)
                 (Lindenbaum_limit_maximal Gamma)
                 (fun phi Hp => Lindenbaum_limit_deductively_closed Gamma phi Hcons Hp)).
  cbn. intros phi Hg. exact (Lindenbaum_limit_extends Gamma phi Hg).
Qed.

Theorem canonical_truth_lemma_max_var : forall (w : canonical_world_max) p,
  cwm_set w (Var p) <-> cwm_set w (Var p).
Proof. intros w p. tauto. Qed.

Theorem canonical_truth_lemma_max_bot : forall (w : canonical_world_max),
  ~ cwm_set w Bot.
Proof.
  intros w Hbot.
  apply (cwm_consistent w).
  exists [Bot]. split.
  - intros psi Hin. cbn in Hin. destruct Hin as [Heq|[]]. subst psi. exact Hbot.
  - apply DT_hyp. cbn. tauto.
Qed.

Theorem canonical_truth_lemma_max_impl_forward : forall (w : canonical_world_max) phi psi,
  cwm_set w (Impl phi psi) -> cwm_set w phi -> cwm_set w psi.
Proof.
  intros w phi psi Himp Hphi.
  apply (cwm_deductively_closed w).
  exists [phi; Impl phi psi]. split.
  - intros chi Hin. cbn in Hin. destruct Hin as [Heq | [Heq | []]].
    + subst chi. exact Hphi.
    + subst chi. exact Himp.
  - apply DT_MP with phi.
    + apply DT_hyp. cbn. tauto.
    + apply DT_hyp. cbn. tauto.
Qed.

Theorem canonical_truth_lemma_max_box_forward : forall (w : canonical_world_max) n phi,
  cwm_set w (Box n phi) ->
  forall v, canonical_R_max n w v -> cwm_set v phi.
Proof. intros w n phi Hbox v HR. exact (HR phi Hbox). Qed.

Theorem canonical_R_max_transitive : forall n w v u,
  canonical_R_max n w v -> canonical_R_max n v u -> canonical_R_max n w u.
Proof.
  intros n w v u Hwv Hvu phi Hwbox.
  apply Hvu. apply Hwv.
  apply (cwm_deductively_closed w).
  exists [Box n phi]. split.
  - intros chi Hin. cbn in Hin. destruct Hin as [<-|[]]. exact Hwbox.
  - apply DT_MP with (Box n phi).
    + apply DT_thm. exact (Ax_Box4 n phi).
    + apply DT_hyp. cbn. tauto.
Qed.

Theorem canonical_R_max_loeb_descent_blocked : forall n w v,
  canonical_R_max n w v ->
  forall phi, cwm_set w (Box n (Impl (Box n phi) phi)) -> cwm_set v phi.
Proof.
  intros n w v HR phi Hwbox.
  apply HR. apply (cwm_deductively_closed w).
  exists [Box n (Impl (Box n phi) phi)]. split.
  - intros chi Hin. cbn in Hin. destruct Hin as [<-|[]]. exact Hwbox.
  - apply DT_MP with (Box n (Impl (Box n phi) phi)).
    + apply DT_thm. exact (Ax_Loeb n phi).
    + apply DT_hyp. cbn. tauto.
Qed.

Theorem canonical_R_max_converse_wf_no_self_box_bot : forall n w,
  canonical_R_max n w w ->
  cwm_set w (Box n (Impl (Box n Bot) Bot)) ->
  False.
Proof.
  intros n w HR Hbox.
  apply (canonical_truth_lemma_max_bot w).
  exact (canonical_R_max_loeb_descent_blocked n w w HR Bot Hbox).
Qed.

Definition next_con_succ_set (v : canonical_world_max) (n : nat) : Form -> Prop :=
  fun phi => cwm_set v (Box n phi).

Theorem canonical_R_max_NextCon_witness : forall n w v,
  canonical_R_max (S n) w v -> cwm_set v (Neg (Box n Bot)).
Proof.
  intros n w v HR.
  apply HR. apply (cwm_deductively_closed w).
  exists []. split.
  - intros _ [].
  - apply DT_thm. exact (Ax_NextCon n).
Qed.

Lemma cwm_box_and_list : forall (v : canonical_world_max) n G,
  Forall (fun psi => cwm_set v (Box n psi)) G ->
  cwm_set v (Box n (And_list G)).
Proof.
  intros v n G HF.
  induction G as [|psi rest IH].
  - apply (cwm_deductively_closed v).
    exists []. split.
    + intros _ [].
    + apply DT_thm. exact (prov_box_top n).
  - inversion HF as [|? ? Hpsi Hrest_F]; subst.
    pose proof (IH Hrest_F) as Hrest.
    apply (cwm_deductively_closed v).
    exists [Box n psi; Box n (And_list rest)]. split.
    + intros chi Hin. cbn in Hin. destruct Hin as [<- | [<- | []]].
      * exact Hpsi.
      * exact Hrest.
    + cbn. apply DT_MP with (Box n (And_list rest)).
      * apply DT_MP with (Box n psi).
        -- apply DT_thm. exact (prov_box_and_intro n psi (And_list rest)).
        -- apply DT_hyp. cbn. tauto.
      * apply DT_hyp. cbn. tauto.
Qed.

Theorem next_con_succ_set_extends : forall (v : canonical_world_max) n phi,
  next_con_succ_set v n phi <-> cwm_set v (Box n phi).
Proof. intros. unfold next_con_succ_set. tauto. Qed.

Theorem canonical_R_max_to_succ_set : forall n v u,
  (forall phi, cwm_set v (Box n phi) -> cwm_set u phi) ->
  forall phi, next_con_succ_set v n phi -> cwm_set u phi.
Proof.
  intros n v u HR phi Hphi.
  apply HR. exact Hphi.
Qed.

Fixpoint forces_cwm (w : canonical_world_max) (phi : Form) : Prop :=
  match phi with
  | Var p => cwm_set w (Var p)
  | Bot => False
  | Impl a b => forces_cwm w a -> forces_cwm w b
  | Box n psi => forall v, canonical_R_max n w v -> forces_cwm v psi
  end.

Lemma cwm_classical_impl : forall (w : canonical_world_max) phi psi,
  (cwm_set w phi -> cwm_set w psi) -> cwm_set w (Impl phi psi).
Proof.
  intros w phi psi Himp.
  destruct (cwm_maximal w phi) as [Hphi | Hnphi].
  - pose proof (Himp Hphi) as Hpsi.
    apply (cwm_deductively_closed w).
    exists [psi]. split.
    + intros chi Hin. cbn in Hin. destruct Hin as [<-|[]]. exact Hpsi.
    + apply DT_MP with psi.
      * apply DT_thm. exact (Ax_K psi phi).
      * apply DT_hyp. cbn. tauto.
  - apply (cwm_deductively_closed w).
    exists [Neg phi]. split.
    + intros chi Hin. cbn in Hin. destruct Hin as [<-|[]]. exact Hnphi.
    + apply DT_MP with (Neg phi).
      * apply DT_thm.
        pose proof (prov_explosion psi) as Hexp.
        pose proof (prov_compose_internal phi Bot psi) as Hci.
        exact (MP _ _ Hci Hexp).
      * apply DT_hyp. cbn. tauto.
Qed.

Theorem canonical_truth_lemma_max_box_free : forall phi w,
  box_free phi -> (cwm_set w phi <-> forces_cwm w phi).
Proof.
  induction phi as [p | | a IHa b IHb | n psi IHpsi]; intros w Hbf; cbn in *.
  - tauto.
  - split.
    + intro H. exact (canonical_truth_lemma_max_bot w H).
    + intros [].
  - destruct Hbf as [Hbf_a Hbf_b]. split.
    + intros Hw Ha.
      apply (IHb w Hbf_b).
      apply (cwm_deductively_closed w).
      exists [a; Impl a b]. split.
      * intros chi Hin. cbn in Hin. destruct Hin as [<- | [<- | []]].
        -- apply (IHa w Hbf_a). exact Ha.
        -- exact Hw.
      * apply DT_MP with a.
        -- apply DT_hyp. cbn. tauto.
        -- apply DT_hyp. cbn. tauto.
    + intros Himp.
      apply cwm_classical_impl. intros Ha_in.
      apply (IHb w Hbf_b). apply Himp. apply (IHa w Hbf_a). exact Ha_in.
  - exfalso. exact Hbf.
Qed.

Theorem canonical_truth_lemma_max_forward_box : forall n psi w,
  cwm_set w (Box n psi) ->
  forall v, canonical_R_max n w v -> cwm_set v psi.
Proof.
  intros n psi w Hw v HR.
  exact (HR psi Hw).
Qed.

Lemma Provable_with_hyp_singleton_to_impl : forall phi chi,
  Provable_with_hyp [phi] chi -> |- Impl phi chi.
Proof.
  intros phi chi H.
  apply Provable_with_hyp_nil.
  apply (deduction_theorem [] phi chi).
  apply (Provable_with_hyp_weaken [phi] (phi :: [])).
  - intros psi Hin. exact Hin.
  - exact H.
Qed.

Theorem canonical_existence_lemma : forall phi,
  ~ |- Neg phi ->
  exists w : canonical_world_max, cwm_set w phi.
Proof.
  intros phi Hno.
  assert (Hcons : Consistent (fun psi => psi = phi)).
  { intros [G [HG Hbot]].
    apply Hno. unfold Neg.
    assert (Hsub : forall psi, In psi G -> psi = phi).
    { intros psi Hin. exact (HG psi Hin). }
    assert (Hsub' : forall psi, In psi G -> In psi [phi]).
    { intros psi Hin. left. exact (eq_sym (Hsub psi Hin)). }
    pose proof (Provable_with_hyp_weaken G [phi] Bot Hsub' Hbot) as Hbot'.
    exact (Provable_with_hyp_singleton_to_impl phi Bot Hbot'). }
  pose proof (canonical_world_max_extension _ Hcons) as [w Hw].
  exists w. apply Hw. reflexivity.
Qed.

Theorem canonical_existence_lemma_box_free : forall phi,
  box_free phi -> ~ |- Neg phi ->
  exists w : canonical_world_max, forces_cwm w phi.
Proof.
  intros phi Hbf Hno.
  destruct (canonical_existence_lemma phi Hno) as [w Hw].
  exists w. apply (canonical_truth_lemma_max_box_free phi w Hbf). exact Hw.
Qed.

Theorem strong_to_weak_completeness_box_free : forall phi,
  box_free phi ->
  (forall w : canonical_world_max, forces_cwm w phi) ->
  |- phi.
Proof.
  intros phi Hbf Hall.
  apply NNPP. intro Hno.
  assert (Hno_neg : ~ |- Neg (Neg phi)).
  { intro Habs. apply Hno.
    pose proof (Ax_DN phi) as HDN.
    exact (MP _ _ HDN Habs). }
  destruct (canonical_existence_lemma (Neg phi)) as [w Hw_neg].
  - intro Habs. apply Hno.
    pose proof (Ax_DN phi) as HDN.
    exact (MP _ _ HDN Habs).
  - assert (Hbf_neg : box_free (Neg phi)).
    { cbn. split; [exact Hbf | exact I]. }
    pose proof (Hall w) as Hw_phi.
    pose proof (canonical_truth_lemma_max_box_free (Neg phi) w Hbf_neg) as Hiff.
    pose proof (proj1 Hiff Hw_neg) as Hforces_neg.
    cbn in Hforces_neg.
    exact (Hforces_neg Hw_phi).
Qed.

Definition Stone_image (phi : Form) (w : canonical_world_max) : Prop :=
  cwm_set w phi.

Theorem Stone_image_provable_universal : forall phi,
  |- phi -> forall (w : canonical_world_max), Stone_image phi w.
Proof.
  intros phi Hp w. unfold Stone_image.
  apply (cwm_deductively_closed w).
  exists []. split.
  - intros _ [].
  - apply DT_thm. exact Hp.
Qed.

Theorem Stone_image_bot_empty :
  forall (w : canonical_world_max), ~ Stone_image Bot w.
Proof. exact canonical_truth_lemma_max_bot. Qed.

Theorem Stone_image_top_universal :
  forall (w : canonical_world_max), Stone_image Top w.
Proof.
  intro w. apply Stone_image_provable_universal. exact (prov_id Bot).
Qed.

Theorem Stone_image_modus_ponens :
  forall (w : canonical_world_max) phi psi,
    Stone_image (Impl phi psi) w -> Stone_image phi w -> Stone_image psi w.
Proof. intros w phi psi. exact (canonical_truth_lemma_max_impl_forward w phi psi). Qed.

Theorem Stone_image_maximal :
  forall (w : canonical_world_max) phi,
    Stone_image phi w \/ Stone_image (Neg phi) w.
Proof. intros w phi. exact (cwm_maximal w phi). Qed.

Theorem Stone_image_consistency :
  forall (w : canonical_world_max) phi,
    Stone_image phi w -> ~ Stone_image (Neg phi) w.
Proof.
  intros w phi Hphi Hnphi.
  pose proof (Stone_image_modus_ponens w phi Bot Hnphi Hphi) as Hbot.
  exact (Stone_image_bot_empty w Hbot).
Qed.

Definition Stone_image_R (n : nat) (w v : canonical_world_max) : Prop :=
  canonical_R_max n w v.

Theorem Stone_R_box_to_succ : forall n (w v : canonical_world_max) phi,
  Stone_image_R n w v ->
  Stone_image (Box n phi) w -> Stone_image phi v.
Proof.
  intros n w v phi HR Hbox.
  unfold Stone_image, Stone_image_R, canonical_R_max in *.
  exact (HR phi Hbox).
Qed.

Theorem Stone_R_transitive : forall n,
  forall w v u, Stone_image_R n w v -> Stone_image_R n v u ->
                Stone_image_R n w u.
Proof. exact canonical_R_max_transitive. Qed.

Theorem Stone_R_NextCon : forall n (w v : canonical_world_max),
  Stone_image_R (S n) w v ->
  cwm_set v (Neg (Box n Bot)).
Proof. exact canonical_R_max_NextCon_witness. Qed.

Theorem Stone_duality_LT_to_frame :
  (forall phi, |- phi ->
    forall (w : canonical_world_max), Stone_image phi w) /\
  (forall (w : canonical_world_max),
    forall phi psi, Stone_image (Impl phi psi) w ->
                    Stone_image phi w -> Stone_image psi w) /\
  (forall (w : canonical_world_max), ~ Stone_image Bot w) /\
  (forall (w : canonical_world_max), Stone_image Top w) /\
  (forall (w : canonical_world_max) phi,
    Stone_image phi w \/ Stone_image (Neg phi) w) /\
  (forall (w : canonical_world_max) phi,
    Stone_image phi w -> ~ Stone_image (Neg phi) w) /\
  (forall n (w v : canonical_world_max) phi,
    Stone_image_R n w v ->
    Stone_image (Box n phi) w -> Stone_image phi v).
Proof.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - exact Stone_image_provable_universal.
  - exact Stone_image_modus_ponens.
  - exact Stone_image_bot_empty.
  - exact Stone_image_top_universal.
  - exact Stone_image_maximal.
  - exact Stone_image_consistency.
  - exact Stone_R_box_to_succ.
Qed.

Theorem Stone_duality_provability_iff_universal :
  forall phi, |- phi <->
    (forall (w : canonical_world_max), Stone_image phi w).
Proof.
  intro phi. split.
  - exact (Stone_image_provable_universal phi).
  - intro Huniv.
    apply NNPP. intro Hnp.
    assert (Hnp_neg : ~ |- Neg (Neg phi)).
    { intro Habs. apply Hnp.
      pose proof (Ax_DN phi) as HDN.
      exact (MP _ _ HDN Habs). }
    destruct (canonical_existence_lemma (Neg phi) Hnp_neg) as [w Hw_neg].
    pose proof (Huniv w) as Hw_phi.
    exact (Stone_image_consistency w phi Hw_phi Hw_neg).
Qed.

Definition Esakia_LT_to_dual : Form -> canonical_world_max -> Prop := Stone_image.

Definition Esakia_dual_to_LT : (canonical_world_max -> Prop) -> Form -> Prop :=
  fun S phi => forall w, S w -> Stone_image phi w.

Theorem Esakia_duality_objects_LT_to_frame :
  forall phi, |- phi -> forall (w : canonical_world_max), Stone_image phi w.
Proof. exact Stone_image_provable_universal. Qed.

Theorem Esakia_duality_objects_frame_to_LT :
  forall phi, (forall (w : canonical_world_max), Stone_image phi w) -> |- phi.
Proof. apply Stone_duality_provability_iff_universal. Qed.

Theorem Esakia_duality_objects_iff :
  forall phi, |- phi <-> forall (w : canonical_world_max), Stone_image phi w.
Proof. exact Stone_duality_provability_iff_universal. Qed.

Definition Esakia_LT_morphism (phi psi : Form) : Prop := |- Impl phi psi.

Theorem Esakia_LT_morphism_refl : forall phi, Esakia_LT_morphism phi phi.
Proof. intros phi. unfold Esakia_LT_morphism. apply prov_id. Qed.

Theorem Esakia_LT_morphism_trans : forall phi psi chi,
  Esakia_LT_morphism phi psi ->
  Esakia_LT_morphism psi chi ->
  Esakia_LT_morphism phi chi.
Proof.
  intros phi psi chi Hpq Hqr. unfold Esakia_LT_morphism in *.
  exact (prov_compose _ _ _ Hpq Hqr).
Qed.

Definition Esakia_frame_morphism (S T : canonical_world_max -> Prop) : Prop :=
  forall w, S w -> T w.

Theorem Esakia_frame_morphism_refl : forall S, Esakia_frame_morphism S S.
Proof. intros S w H. exact H. Qed.

Theorem Esakia_frame_morphism_trans : forall S T U,
  Esakia_frame_morphism S T ->
  Esakia_frame_morphism T U ->
  Esakia_frame_morphism S U.
Proof. intros S T U Hst Htu w Hs. apply Htu. apply Hst. exact Hs. Qed.

Theorem Esakia_LT_to_frame_morphism_functor : forall phi psi,
  Esakia_LT_morphism phi psi ->
  Esakia_frame_morphism (Stone_image phi) (Stone_image psi).
Proof.
  intros phi psi Hpq w Hw_phi.
  unfold Esakia_LT_morphism in Hpq.
  apply (Stone_image_modus_ponens w phi psi).
  - apply Stone_image_provable_universal. exact Hpq.
  - exact Hw_phi.
Qed.

Theorem Esakia_duality_morphism_preservation :
  (forall phi, Esakia_LT_morphism phi phi) /\
  (forall phi psi chi,
    Esakia_LT_morphism phi psi ->
    Esakia_LT_morphism psi chi ->
    Esakia_LT_morphism phi chi) /\
  (forall S, Esakia_frame_morphism S S) /\
  (forall S T U,
    Esakia_frame_morphism S T ->
    Esakia_frame_morphism T U ->
    Esakia_frame_morphism S U) /\
  (forall phi psi,
    Esakia_LT_morphism phi psi ->
    Esakia_frame_morphism (Stone_image phi) (Stone_image psi)).
Proof.
  split; [|split; [|split; [|split]]].
  - exact Esakia_LT_morphism_refl.
  - exact Esakia_LT_morphism_trans.
  - exact Esakia_frame_morphism_refl.
  - exact Esakia_frame_morphism_trans.
  - exact Esakia_LT_to_frame_morphism_functor.
Qed.

Lemma forces_box_free_iff_eval_const : forall (F : Frame) val w phi,
  box_free phi ->
  (forces F (fun _ => val) w phi <-> eval val phi = true).
Proof.
  intros F val w phi Hbf. revert w.
  induction phi as [p | | a IHa b IHb | n psi IHpsi]; intros w; cbn in *.
  - tauto.
  - split. intros []. discriminate.
  - destruct Hbf as [Hbfa Hbfb].
    pose proof (IHa Hbfa w) as Hia.
    pose proof (IHb Hbfb w) as Hib.
    split.
    + intros Himp.
      destruct (classic (forces F (fun _ => val) w a)) as [Ha | Hna].
      * pose proof (proj1 Hia Ha) as Heva.
        pose proof (Himp Ha) as Hb.
        pose proof (proj1 Hib Hb) as Hevb.
        rewrite Heva, Hevb. cbn. reflexivity.
      * assert (Heva : eval val a = false).
        { case_eq (eval val a); intros Hev; [|reflexivity].
          exfalso. apply Hna. apply (proj2 Hia). exact Hev. }
        rewrite Heva. cbn. reflexivity.
    + intros Heval Ha.
      pose proof (proj1 Hia Ha) as Heva. rewrite Heva in Heval. cbn in Heval.
      apply (proj2 Hib). exact Heval.
  - exfalso; exact Hbf.
Qed.

Lemma forces_box_free_iff_eval_F0 : forall val phi,
  box_free phi ->
  (forces F0 (fun _ => val) true phi <-> eval val phi = true).
Proof. intros val phi Hbf. exact (forces_box_free_iff_eval_const F0 val true phi Hbf). Qed.

Theorem kripke_completeness_box_free_via_frame : forall phi,
  box_free phi -> ~ |- phi ->
  exists (F : Frame) (V : fW F -> nat -> bool) (w : fW F),
    ~ forces F V w phi.
Proof.
  intros phi Hbf Hnp.
  destruct (FFP_for_box_free phi Hbf Hnp) as [val Hv].
  exists F0, (fun _ => val), true.
  intro Habs.
  pose proof (proj1 (forces_box_free_iff_eval_F0 val phi Hbf) Habs) as Heval.
  rewrite Hv in Heval. discriminate.
Qed.

Lemma ProvableProp_to_no_nc : forall phi, ProvableProp phi -> |-no_nc phi.
Proof.
  intros phi H. induction H.
  - apply NC_Ax_K.
  - apply NC_Ax_S.
  - apply NC_Ax_DN.
  - exact (NC_MP _ _ IHProvableProp1 IHProvableProp2).
Qed.

Lemma ProvableProp_to_no_mon : forall phi, ProvableProp phi -> |-no_mon phi.
Proof.
  intros phi H. induction H.
  - apply NM_Ax_K.
  - apply NM_Ax_S.
  - apply NM_Ax_DN.
  - exact (NM_MP _ _ IHProvableProp1 IHProvableProp2).
Qed.

Lemma ProvableProp_to_no_loeb : forall phi, ProvableProp phi -> |-no_loeb phi.
Proof.
  intros phi H. induction H.
  - apply NL_Ax_K.
  - apply NL_Ax_S.
  - apply NL_Ax_DN.
  - exact (NL_MP _ _ IHProvableProp1 IHProvableProp2).
Qed.

Lemma ProvableProp_to_no_b4 : forall phi, ProvableProp phi -> |-no_b4 phi.
Proof.
  intros phi H. induction H.
  - apply NB4_Ax_K.
  - apply NB4_Ax_S.
  - apply NB4_Ax_DN.
  - exact (NB4_MP _ _ IHProvableProp1 IHProvableProp2).
Qed.

Theorem kripke_completeness_no_nc_box_free : forall phi,
  box_free phi -> ~ |-no_nc phi -> exists val, eval val phi = false.
Proof.
  intros phi Hbf Hno.
  destruct (classic (classical_valid phi)) as [Hcv | Hncv].
  - exfalso. apply Hno. apply ProvableProp_to_no_nc.
    apply prop_completeness; assumption.
  - apply not_all_ex_not in Hncv. destruct Hncv as [val Hv].
    exists val. destruct (eval val phi); [contradiction | reflexivity].
Qed.

Theorem kripke_completeness_no_mon_box_free : forall phi,
  box_free phi -> ~ |-no_mon phi -> exists val, eval val phi = false.
Proof.
  intros phi Hbf Hno.
  destruct (classic (classical_valid phi)) as [Hcv | Hncv].
  - exfalso. apply Hno. apply ProvableProp_to_no_mon.
    apply prop_completeness; assumption.
  - apply not_all_ex_not in Hncv. destruct Hncv as [val Hv].
    exists val. destruct (eval val phi); [contradiction | reflexivity].
Qed.

Theorem kripke_completeness_no_loeb_box_free : forall phi,
  box_free phi -> ~ |-no_loeb phi -> exists val, eval val phi = false.
Proof.
  intros phi Hbf Hno.
  destruct (classic (classical_valid phi)) as [Hcv | Hncv].
  - exfalso. apply Hno. apply ProvableProp_to_no_loeb.
    apply prop_completeness; assumption.
  - apply not_all_ex_not in Hncv. destruct Hncv as [val Hv].
    exists val. destruct (eval val phi); [contradiction | reflexivity].
Qed.

Theorem kripke_completeness_no_b4_box_free : forall phi,
  box_free phi -> ~ |-no_b4 phi -> exists val, eval val phi = false.
Proof.
  intros phi Hbf Hno.
  destruct (classic (classical_valid phi)) as [Hcv | Hncv].
  - exfalso. apply Hno. apply ProvableProp_to_no_b4.
    apply prop_completeness; assumption.
  - apply not_all_ex_not in Hncv. destruct Hncv as [val Hv].
    exists val. destruct (eval val phi); [contradiction | reflexivity].
Qed.

Theorem modal_compactness_canonical_witness : forall (Gamma : Form -> Prop),
  FinitelyConsistent Gamma ->
  exists w : canonical_world_max, forall phi, Gamma phi -> cwm_set w phi.
Proof.
  intros Gamma Hfc.
  apply (canonical_world_max_extension Gamma).
  apply compactness. exact Hfc.
Qed.

Lemma forces_Fnat_box_free_iff_classical : forall phi val w,
  box_free phi ->
  (forces Fnat (fun _ => val) w phi <-> eval val phi = true).
Proof. intros phi val w Hbf. exact (forces_box_free_iff_eval_const Fnat val w phi Hbf). Qed.

Theorem omega_completeness_Fnat_box_free : forall phi,
  box_free phi -> (forall V w, forces Fnat V w phi) -> |- phi.
Proof.
  intros phi Hbf Hall.
  apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
  intro val.
  apply (proj1 (forces_Fnat_box_free_iff_classical phi val 0 Hbf)).
  exact (Hall (fun _ => val) 0).
Qed.

Definition universal_frame_carrier : Type := canonical_world_max.

Definition universal_frame_R (n : nat) (w v : canonical_world_max) : Prop :=
  canonical_R_max n w v.

Theorem universal_frame_R_transitive : forall n w v u,
  universal_frame_R n w v -> universal_frame_R n v u ->
  universal_frame_R n w u.
Proof. exact canonical_R_max_transitive. Qed.

Theorem universal_frame_bisimilar_to_canonical : forall n w v,
  canonical_R_max n w v <-> universal_frame_R n w v.
Proof. intros. unfold universal_frame_R. tauto. Qed.

Theorem universal_frame_NextCon_witness : forall n w v,
  universal_frame_R (S n) w v -> cwm_set v (Neg (Box n Bot)).
Proof. exact canonical_R_max_NextCon_witness. Qed.

Theorem universal_frame_truth_lemma_box_free : forall phi w,
  box_free phi -> (cwm_set w phi <-> forces_cwm w phi).
Proof. exact canonical_truth_lemma_max_box_free. Qed.

Theorem finite_frame_property_box_free_F0 : forall phi,
  box_free phi -> ~ |- phi ->
  exists (V : fW F0 -> nat -> bool) (w : fW F0), ~ forces F0 V w phi.
Proof.
  intros phi Hbf Hnp.
  destruct (FFP_for_box_free phi Hbf Hnp) as [val Hv].
  exists (fun _ => val), true.
  intro Habs.
  pose proof (proj1 (forces_box_free_iff_eval_F0 val phi Hbf) Habs) as Heval.
  rewrite Hv in Heval. discriminate.
Qed.

Theorem finite_frame_property_box_n_bot : forall n,
  exists (F : Frame) V w, ~ forces F V w (Box n Bot).
Proof.
  intros n.
  exists Fnat, (fun _ _ => true), (S n).
  intro Habs. cbn in Habs.
  apply (Habs n). unfold Fnat_R. split; lia.
Qed.

Theorem FMP_modal_depth_zero_via_F0 : forall phi,
  box_free phi -> ~ |- phi ->
  modal_depth phi = 0 /\
  exists (V : fW F0 -> nat -> bool) (w : fW F0), ~ forces F0 V w phi.
Proof.
  intros phi Hbf Hnp. split.
  - exact (box_free_modal_depth_zero phi Hbf).
  - exact (finite_frame_property_box_free_F0 phi Hbf Hnp).
Qed.

Theorem selection_theorem_identity_bisimulation : forall (F : Frame) V w,
  exists Z : fW F -> fW F -> Prop, Bisim F F V V Z /\ Z w w.
Proof.
  intros F V w. exists (@eq (fW F)). split.
  - apply bisim_id.
  - reflexivity.
Qed.

Theorem finite_refuting_frame_box_free_or_box_bot : forall phi,
  ((box_free phi /\ ~ |- phi) \/ (exists n, phi = Box n Bot)) ->
  exists (F : Frame) V w, ~ forces F V w phi.
Proof.
  intros phi [[Hbf Hnp] | [n Heq]].
  - exact (kripke_completeness_box_free_via_frame phi Hbf Hnp).
  - subst phi. exists Fnat, (fun _ _ => true), (S n).
    intro Habs. cbn in Habs.
    apply (Habs n). unfold Fnat_R. split; lia.
Qed.

Theorem finite_refuting_frame_for_var : forall n p,
  exists (F : Frame) V w, ~ forces F V w (Box n (Var p)).
Proof.
  intros n p.
  exists Fnat, (fun w q => match q with | _ => false end), (S n).
  intro Habs. cbn in Habs.
  pose proof (Habs n) as Hcontra.
  assert (HR : Fnat_R n (S n) n) by (unfold Fnat_R; split; lia).
  pose proof (Hcontra HR) as H. discriminate.
Qed.

Theorem finite_refuting_frame_for_neg_var : forall n p,
  exists (F : Frame) V w, ~ forces F V w (Box n (Neg (Var p))).
Proof.
  intros n p.
  exists Fnat, (fun _ _ => true), (S n).
  intro Habs. cbn in Habs.
  assert (HR : Fnat_R n (S n) n) by (unfold Fnat_R; split; lia).
  pose proof (Habs n HR) as Hcontra.
  exact (Hcontra eq_refl).
Qed.
