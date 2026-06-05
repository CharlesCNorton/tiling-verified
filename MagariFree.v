(******************************************************************************)
(*                                                                            *)
(*  The Lindenbaum-Tarski algebra of GLP* is the FREE polymodal Magari        *)
(*  algebra (todo item #5).                                                   *)
(*                                                                            *)
(*  [polymodal_Magari_algebra] is a setoid-carried record: a Boolean          *)
(*  implication algebra (impl/bot presentation, with the K/S/DN laws,         *)
(*  MP-closure, necessitation closure, and internal-iff-to-equality —         *)
(*  enough to derive every classical Boolean law via the generic              *)
(*  theorem-replay below) together with a family of box operators            *)
(*  validating K, Loeb, Box4, Mon and NextCon at every index.                 *)
(*                                                                            *)
(*  [LT_GLP] is the Lindenbaum-Tarski instance: carrier Form, equality        *)
(*  provable-iff.  [pma_hom A val] is the unique interpretation               *)
(*  homomorphism determined by a valuation of the variables; freeness         *)
(*  ([LT_GLP_free]) gives existence plus uniqueness-up-to-algebra-equality,   *)
(*  where the uniqueness proof is a pure structural-induction CALCULATION     *)
(*  (no proof_irrelevance, no functional_extensionality — which is also       *)
(*  why the uniqueness is stated setoid-pointwise rather than with Coq's      *)
(*  intensional eq on morphism records; the latter is unprovable without      *)
(*  funext and was forbidden anyway).                                         *)
(*                                                                            *)
(*  Non-degeneracy: the freeness theorem is instantiated at the genuinely     *)
(*  different two-element Boolean algebra [PMA_bool] (so the statement is     *)
(*  not collapsed at A := LT_GLP), and the morphism laws are carried as       *)
(*  record fields and CHECKED for both instances.                             *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.
Import ListNotations.
From Tiling Require Import Tiling.

(** ** The algebra signature with its laws. *)

Record polymodal_Magari_algebra : Type := mkPMA {
  pma_carrier : Type;
  pma_eq : pma_carrier -> pma_carrier -> Prop;
  pma_bot : pma_carrier;
  pma_top : pma_carrier;
  pma_impl : pma_carrier -> pma_carrier -> pma_carrier;
  pma_box : nat -> pma_carrier -> pma_carrier;

  pma_eq_refl : forall a, pma_eq a a;
  pma_eq_sym : forall a b, pma_eq a b -> pma_eq b a;
  pma_eq_trans : forall a b c, pma_eq a b -> pma_eq b c -> pma_eq a c;
  pma_impl_cong : forall a a' b b',
      pma_eq a a' -> pma_eq b b' ->
      pma_eq (pma_impl a b) (pma_impl a' b');
  pma_box_cong : forall n a a',
      pma_eq a a' -> pma_eq (pma_box n a) (pma_box n a');

  pma_top_def : pma_eq pma_top (pma_impl pma_bot pma_bot);

  pma_K : forall a b,
      pma_eq (pma_impl a (pma_impl b a)) pma_top;
  pma_S : forall a b c,
      pma_eq (pma_impl (pma_impl a (pma_impl b c))
                       (pma_impl (pma_impl a b) (pma_impl a c))) pma_top;
  pma_DN : forall a,
      pma_eq (pma_impl (pma_impl (pma_impl a pma_bot) pma_bot) a) pma_top;
  pma_BoxK : forall n a b,
      pma_eq (pma_impl (pma_box n (pma_impl a b))
                       (pma_impl (pma_box n a) (pma_box n b))) pma_top;
  pma_Loeb : forall n a,
      pma_eq (pma_impl (pma_box n (pma_impl (pma_box n a) a))
                       (pma_box n a)) pma_top;
  pma_Box4 : forall n a,
      pma_eq (pma_impl (pma_box n a) (pma_box n (pma_box n a))) pma_top;
  pma_Mon : forall n a,
      pma_eq (pma_impl (pma_box n a) (pma_box (S n) a)) pma_top;
  pma_NextCon : forall n,
      pma_eq (pma_box (S n) (pma_impl (pma_box n pma_bot) pma_bot)) pma_top;

  pma_MP : forall a b,
      pma_eq (pma_impl a b) pma_top -> pma_eq a pma_top -> pma_eq b pma_top;
  pma_Nec : forall n a,
      pma_eq a pma_top -> pma_eq (pma_box n a) pma_top;
  pma_iff_eq : forall a b,
      pma_eq (pma_impl a b) pma_top ->
      pma_eq (pma_impl b a) pma_top ->
      pma_eq a b
}.

Arguments pma_eq {p}.
Arguments pma_bot {p}.
Arguments pma_top {p}.
Arguments pma_impl {p}.
Arguments pma_box {p}.
Arguments pma_eq_refl {p}.
Arguments pma_eq_sym {p}.
Arguments pma_eq_trans {p}.
Arguments pma_impl_cong {p}.
Arguments pma_box_cong {p}.
Arguments pma_MP {p}.
Arguments pma_Nec {p}.
Arguments pma_iff_eq {p}.

(** ** The interpretation homomorphism determined by a valuation. *)

Fixpoint pma_hom (A : polymodal_Magari_algebra)
  (val : nat -> pma_carrier A) (phi : Form) : pma_carrier A :=
  match phi with
  | Var p => val p
  | Bot => pma_bot
  | Impl a b => pma_impl (pma_hom A val a) (pma_hom A val b)
  | Box n a => pma_box n (pma_hom A val a)
  end.

(** Generic theorem replay: every GLP*-theorem's image is the top of
    any polymodal Magari algebra, under any valuation.  This is the
    sense in which the record's laws present "validity of the
    calculus" — and it manufactures arbitrary internal Boolean laws,
    quantified over arbitrary carrier elements, from propositional
    tautologies (see the demonstrations below). *)

Lemma pma_hom_theorem : forall (A : polymodal_Magari_algebra) val phi,
  |- phi -> pma_eq (pma_hom A val phi) (pma_top (p:=A)).
Proof.
  intros A val phi H.
  induction H as [phi psi | phi psi chi | phi | n phi psi | n phi | n phi
                 | n phi | n | phi psi H1 IH1 H2 IH2 | n phi H IH]; cbn [pma_hom].
  - exact (pma_K A _ _).
  - exact (pma_S A _ _ _).
  - exact (pma_DN A _).
  - exact (pma_BoxK A n _ _).
  - exact (pma_Loeb A n _).
  - exact (pma_Box4 A n _).
  - exact (pma_Mon A n _).
  - exact (pma_NextCon A n).
  - exact (pma_MP _ _ IH1 IH2).
  - exact (pma_Nec n _ IH).
Qed.

(** The hom respects provable equivalence — well-definedness on the
    Lindenbaum-Tarski classes. *)

Lemma pma_hom_respects : forall (A : polymodal_Magari_algebra) val phi psi,
  |- Iff phi psi ->
  pma_eq (pma_hom A val phi) (pma_hom A val psi).
Proof.
  intros A val phi psi Hiff.
  apply pma_iff_eq.
  - exact (pma_hom_theorem A val _ (prov_and_elim_l_meta _ _ Hiff)).
  - exact (pma_hom_theorem A val _ (prov_and_elim_r_meta _ _ Hiff)).
Qed.

(** ** The Lindenbaum-Tarski instance. *)

Lemma LT_law_top : forall phi, |- phi -> prov_equiv phi Top.
Proof.
  intros phi H. exact (proj2 (LT_quotient_provability phi) H).
Qed.

Lemma LT_law_from_top : forall phi, prov_equiv phi Top -> |- phi.
Proof.
  intros phi H. exact (proj1 (LT_quotient_provability phi) H).
Qed.

Definition LT_GLP : polymodal_Magari_algebra.
Proof.
  refine (mkPMA Form prov_equiv Bot Top Impl Box
            prov_equiv_refl prov_equiv_sym prov_equiv_trans
            prov_equiv_impl_cong prov_equiv_box_cong
            (prov_equiv_refl Top)
            _ _ _ _ _ _ _ _ _ _ _).
  - intros a b. apply LT_law_top. exact (Ax_K a b).
  - intros a b c. apply LT_law_top. exact (Ax_S a b c).
  - intros a. apply LT_law_top. exact (Ax_DN a).
  - intros n a b. apply LT_law_top. exact (Ax_BoxK n a b).
  - intros n a. apply LT_law_top. exact (Ax_Loeb n a).
  - intros n a. apply LT_law_top. exact (Ax_Box4 n a).
  - intros n a. apply LT_law_top. exact (Ax_Mon n a).
  - intros n. apply LT_law_top. exact (Ax_NextCon n).
  - intros a b H1 H2.
    apply LT_law_top.
    exact (MP _ _ (LT_law_from_top _ H1) (LT_law_from_top _ H2)).
  - intros n a H. apply LT_law_top.
    exact (Nec n _ (LT_law_from_top _ H)).
  - intros a b H1 H2.
    exact (prov_iff_intro a b (LT_law_from_top _ H1) (LT_law_from_top _ H2)).
Defined.

(** The Lindenbaum class map (setoid-style quotient: an element of the
    carrier is a representative, equality is provable-iff). *)

Definition LT_class (phi : Form) : pma_carrier LT_GLP := phi.

(** ** Morphisms of polymodal Magari algebras. *)

Record PMA_morphism (A B : polymodal_Magari_algebra) : Type := mkPMAm {
  pmam_map : pma_carrier A -> pma_carrier B;
  pmam_respects : forall a a',
      pma_eq a a' -> pma_eq (pmam_map a) (pmam_map a');
  pmam_bot : pma_eq (pmam_map (pma_bot (p:=A))) (pma_bot (p:=B));
  pmam_impl : forall a b,
      pma_eq (pmam_map (pma_impl a b)) (pma_impl (pmam_map a) (pmam_map b));
  pmam_box : forall n a,
      pma_eq (pmam_map (pma_box n a)) (pma_box n (pmam_map a))
}.

Arguments pmam_map {A B}.
Arguments pmam_respects {A B}.
Arguments pmam_bot {A B}.
Arguments pmam_impl {A B}.
Arguments pmam_box {A B}.

Definition LT_GLP_morphism (A : polymodal_Magari_algebra) : Type :=
  PMA_morphism LT_GLP A.

(** ** Existence: the free morphism extending a valuation. *)

Definition LT_free_hom (A : polymodal_Magari_algebra)
  (val : nat -> pma_carrier A) : LT_GLP_morphism A.
Proof.
  refine (mkPMAm LT_GLP A (pma_hom A val) _ _ _ _).
  - intros a a' Hiff. exact (pma_hom_respects A val a a' Hiff).
  - exact (pma_eq_refl _).
  - intros a b. exact (pma_eq_refl _).
  - intros n a. exact (pma_eq_refl _).
Defined.

(** ** Uniqueness, by calculation: structural induction on the carrier
    element, using only the morphism laws and the congruences.  No
    proof irrelevance, no functional extensionality. *)

Theorem LT_free_hom_unique : forall (A : polymodal_Magari_algebra)
  (val : nat -> pma_carrier A) (k : LT_GLP_morphism A),
  (forall p, pma_eq (pmam_map k (LT_class (Var p))) (val p)) ->
  forall x, pma_eq (pmam_map k x) (pma_hom A val x).
Proof.
  intros A val k Hvar x.
  induction x as [p | | a IHa b IHb | n a IHa]; cbn [pma_hom].
  - exact (Hvar p).
  - exact (pmam_bot k).
  - eapply pma_eq_trans.
    + exact (pmam_impl k a b).
    + exact (pma_impl_cong _ _ _ _ IHa IHb).
  - eapply pma_eq_trans.
    + exact (pmam_box k n a).
    + exact (pma_box_cong n _ _ IHa).
Qed.

(** ** Freeness: existence and uniqueness-up-to-algebra-equality of the
    morphism extending any valuation of the variables. *)

Theorem LT_GLP_free : forall (A : polymodal_Magari_algebra)
  (val : nat -> pma_carrier A),
  exists h : LT_GLP_morphism A,
    (forall p, pma_eq (pmam_map h (LT_class (Var p))) (val p)) /\
    (forall k : LT_GLP_morphism A,
       (forall p, pma_eq (pmam_map k (LT_class (Var p))) (val p)) ->
       forall x, pma_eq (pmam_map k x) (pmam_map h x)).
Proof.
  intros A val.
  exists (LT_free_hom A val). split.
  - intro p. exact (pma_eq_refl _).
  - intros k Hk x. exact (LT_free_hom_unique A val k Hk x).
Qed.

(** Two morphisms extending the same valuation are pointwise equal —
    the uniqueness half restated symmetrically. *)

Theorem LT_GLP_free_unique_pairwise : forall (A : polymodal_Magari_algebra)
  (val : nat -> pma_carrier A) (h k : LT_GLP_morphism A),
  (forall p, pma_eq (pmam_map h (LT_class (Var p))) (val p)) ->
  (forall p, pma_eq (pmam_map k (LT_class (Var p))) (val p)) ->
  forall x, pma_eq (pmam_map h x) (pmam_map k x).
Proof.
  intros A val h k Hh Hk x.
  eapply pma_eq_trans.
  - exact (LT_free_hom_unique A val h Hh x).
  - apply pma_eq_sym. exact (LT_free_hom_unique A val k Hk x).
Qed.

(** ** Internal Boolean structure, manufactured by theorem replay:
    arbitrary-element Boolean laws hold in EVERY polymodal Magari
    algebra.  Demonstrations: commutativity of the derived meet, and
    the converse double-negation law. *)

Definition pma_neg {A : polymodal_Magari_algebra}
  (a : pma_carrier A) : pma_carrier A := pma_impl a pma_bot.

Definition pma_and {A : polymodal_Magari_algebra}
  (a b : pma_carrier A) : pma_carrier A := pma_neg (pma_impl a (pma_neg b)).

Lemma pma_hom_two : forall (A : polymodal_Magari_algebra) (a b : pma_carrier A),
  pma_hom A (fun n => match n with 0 => a | _ => b end) (And (Var 0) (Var 1))
  = pma_and a b.
Proof. reflexivity. Qed.

Theorem pma_and_comm : forall (A : polymodal_Magari_algebra)
  (a b : pma_carrier A),
  pma_eq (pma_and a b) (pma_and b a).
Proof.
  intros A a b.
  rewrite <- (pma_hom_two A a b).
  assert (Hba : pma_hom A (fun n => match n with 0 => a | _ => b end)
                  (And (Var 1) (Var 0)) = pma_and b a)
    by reflexivity.
  rewrite <- Hba.
  apply pma_hom_respects.
  apply trivial_in_provable.
  apply prop_decide_correct.
  - cbn. unfold And, Neg. cbn. repeat split; exact I.
  - cbv. reflexivity.
Qed.

Theorem pma_dn_converse : forall (A : polymodal_Magari_algebra)
  (a : pma_carrier A),
  pma_eq (pma_impl a (pma_neg (pma_neg a))) (pma_top (p:=A)).
Proof.
  intros A a.
  assert (H : pma_hom A (fun _ => a) (Impl (Var 0) (Neg (Neg (Var 0))))
              = pma_impl a (pma_neg (pma_neg a)))
    by reflexivity.
  rewrite <- H.
  apply pma_hom_theorem.
  exact (prov_DN_intro (Var 0)).
Qed.

(******************************************************************************)
(* Non-degeneracy: the two-element Boolean algebra with trivial boxes is a    *)
(* polymodal Magari algebra genuinely different from LT_GLP, and freeness     *)
(* instantiates at it.                                                        *)
(******************************************************************************)

Definition bool_impl (a b : bool) : bool := orb (negb a) b.

Definition PMA_bool : polymodal_Magari_algebra.
Proof.
  refine (mkPMA bool (@eq bool) false true bool_impl (fun _ _ => true)
            (fun a => eq_refl)
            (fun a b H => eq_sym H)
            (fun a b c H1 H2 => eq_trans H1 H2)
            _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - intros a a' b b' H1 H2. subst a' b'. reflexivity.
  - intros n a a' H. reflexivity.
  - reflexivity.
  - intros a b. destruct a; destruct b; reflexivity.
  - intros a b c. destruct a; destruct b; destruct c; reflexivity.
  - intros a. destruct a; reflexivity.
  - intros n a b. reflexivity.
  - intros n a. reflexivity.
  - intros n a. reflexivity.
  - intros n a. reflexivity.
  - intros n. reflexivity.
  - intros a b H1 H2. subst a. destruct b; cbn in H1; congruence.
  - intros n a H. reflexivity.
  - intros a b H1 H2. destruct a; destruct b; cbn in *; congruence.
Defined.

Theorem PMA_bool_differs_from_LT :
  pma_carrier PMA_bool = bool /\ pma_carrier LT_GLP = Form.
Proof. split; reflexivity. Qed.

(** Freeness instantiated at the Boolean algebra: the evaluation
    morphism exists and agrees with classical evaluation on box-free
    formulas. *)

Theorem LT_GLP_free_at_bool : forall (val : nat -> bool),
  exists h : LT_GLP_morphism PMA_bool,
    forall p, pmam_map h (LT_class (Var p)) = val p.
Proof.
  intro val.
  destruct (LT_GLP_free PMA_bool val) as [h [Hvar _]].
  exists h. exact Hvar.
Qed.

Theorem pma_hom_bool_is_eval : forall (val : nat -> bool) phi,
  box_free phi ->
  pma_hom PMA_bool val phi = eval val phi.
Proof.
  intros val phi Hbf.
  induction phi as [p | | a IHa b IHb | n a IHa]; cbn in *.
  - reflexivity.
  - reflexivity.
  - destruct Hbf as [Ha Hb].
    rewrite (IHa Ha), (IHb Hb). reflexivity.
  - destruct Hbf.
Qed.

(** ** Headline summary for todo #5. *)

Theorem LT_GLP_free_summary :
  (forall (A : polymodal_Magari_algebra) (val : nat -> pma_carrier A),
     exists h : LT_GLP_morphism A,
       (forall p, pma_eq (pmam_map h (LT_class (Var p))) (val p)) /\
       (forall k : LT_GLP_morphism A,
          (forall p, pma_eq (pmam_map k (LT_class (Var p))) (val p)) ->
          forall x, pma_eq (pmam_map k x) (pmam_map h x))) /\
  (forall (A : polymodal_Magari_algebra) val phi,
     |- phi -> pma_eq (pma_hom A val phi) (pma_top (p:=A))) /\
  (forall (A : polymodal_Magari_algebra) (a b : pma_carrier A),
     pma_eq (pma_and a b) (pma_and b a)) /\
  (forall val : nat -> bool,
     exists h : LT_GLP_morphism PMA_bool,
       forall p, pmam_map h (LT_class (Var p)) = val p).
Proof.
  split; [|split; [|split]].
  - exact LT_GLP_free.
  - exact pma_hom_theorem.
  - exact pma_and_comm.
  - exact LT_GLP_free_at_bool.
Qed.
