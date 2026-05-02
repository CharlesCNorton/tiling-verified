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
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

(** * Section 1: Modal Formulas *)

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

(** * Section 2: The Polymodal Goedel-Loeb System GLP* *)

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

(** * Section 3: Basic Propositional Theorems *)

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

(** * Section 4: Modal-K Theorems *)

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

(** * Section 5: The Loeb Metatheorem *)

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


(** * Section 6: The Loebian Obstacle *)

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

(** * Section 7: Toward the Tiling Theorem *)

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

(** * Section 8: The Tiling Theorem (Modal Form) *)

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

(** * Section 9: The T_kappa Tower *)

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

(** * Section 10: Agent Licensure Layer *)

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

(** * Section 11: Modal Goedel's Second Incompleteness *)

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

(** * Section 12: Tiling Restated with the Diamond Modality *)

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

(** * Section 13: The YH Bypass Summary *)

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

(** * Section 14: Classical Equivalences *)

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

