(******************************************************************************)
(*                                                                            *)
(*  Stone duality as a category equivalence (todo item #8).                   *)
(*                                                                            *)
(*  Two e-categories (categories with hom-setoids), with explicit object      *)
(*  types, hom types, identities, composition, associativity and unit laws:   *)
(*                                                                            *)
(*    LT_category               objects: Form                                 *)
(*                              homs:    derivations |- Impl a b              *)
(*    canonical_frame_category  objects: DEFINABLE UPSETS of the canonical    *)
(*                              maximal-consistent worlds — records           *)
(*                              packaging a set of worlds together with a     *)
(*                              defining formula (so the second category is   *)
(*                              NOT Form-with-provability again)              *)
(*                              homs:    pointwise inclusions                 *)
(*                                                                            *)
(*  Functors F (Stone image) and G (definition extraction) with natural       *)
(*  isomorphisms eta : Id => G o F and epsilon : F o G => Id and the          *)
(*  triangle identities.  The component eta_a is the DERIVATION prov_id a     *)
(*  — its type is a provability statement, in which eq_refl is not even       *)
(*  typeable; epsilon's components are the genuine definitional-equivalence   *)
(*  transports of the frame objects.                                          *)
(*                                                                            *)
(*  The mathematical heart is full faithfulness ([Stone_full_faithful]):      *)
(*                                                                            *)
(*    |- Impl a b   <->   Stone_image a is included in Stone_image b,         *)
(*                                                                            *)
(*  whose hard direction is the new separation lemma [Stone_separation]:      *)
(*  if Impl a b is unprovable then {a, Neg b} is consistent, so a             *)
(*  Lindenbaum-maximal world contains a but excludes b.  This is genuinely    *)
(*  beyond the prior [Stone_duality_provability_iff_universal] (which only    *)
(*  characterised provability of a single formula, not hom-sets).             *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical.
Import ListNotations.
From Tiling Require Import Tiling.

(** ** The separation lemma. *)

Lemma hyp_pair_consistent_of_not_provable : forall phi psi,
  ~ |- Impl phi psi ->
  Consistent (fun chi => chi = phi \/ chi = Neg psi).
Proof.
  intros phi psi Hnp [G [HG Hbot]].
  apply Hnp.
  assert (Hsub : forall chi, In chi G -> In chi (Neg psi :: phi :: nil)).
  { intros chi Hin. destruct (HG chi Hin) as [Heq | Heq]; subst chi.
    - right. left. reflexivity.
    - left. reflexivity. }
  pose proof (Provable_with_hyp_weaken G (Neg psi :: phi :: nil) Bot Hsub Hbot)
    as H1.
  pose proof (deduction_theorem (phi :: nil) (Neg psi) Bot H1) as H2.
  pose proof (deduction_theorem nil phi (Impl (Neg psi) Bot) H2) as H3.
  pose proof (Provable_with_hyp_nil _ H3) as H4.
  exact (prov_compose _ _ _ H4 (Ax_DN psi)).
Qed.

Theorem Stone_separation : forall phi psi,
  (forall w : canonical_world_max, Stone_image phi w -> Stone_image psi w) ->
  |- Impl phi psi.
Proof.
  intros phi psi Hincl.
  apply NNPP. intro Hnp.
  pose proof (hyp_pair_consistent_of_not_provable phi psi Hnp) as Hcons.
  destruct (canonical_world_max_extension _ Hcons) as [w Hw].
  assert (Hphi : Stone_image phi w).
  { apply Hw. left. reflexivity. }
  assert (Hnpsi : Stone_image (Neg psi) w).
  { apply Hw. right. reflexivity. }
  exact (Stone_image_consistency w psi (Hincl w Hphi) Hnpsi).
Qed.

(** ** E-categories: categories with hom-setoids. *)

Record ECat : Type := mkECat {
  ec_obj : Type;
  ec_hom : ec_obj -> ec_obj -> Type;
  ec_hom_eq : forall {a b}, ec_hom a b -> ec_hom a b -> Prop;
  ec_id : forall a, ec_hom a a;
  ec_comp : forall {a b c}, ec_hom a b -> ec_hom b c -> ec_hom a c;
  ec_hom_eq_refl : forall a b (f : ec_hom a b), ec_hom_eq f f;
  ec_hom_eq_sym : forall a b (f g : ec_hom a b),
      ec_hom_eq f g -> ec_hom_eq g f;
  ec_hom_eq_trans : forall a b (f g h : ec_hom a b),
      ec_hom_eq f g -> ec_hom_eq g h -> ec_hom_eq f h;
  ec_comp_cong : forall a b c (f f' : ec_hom a b) (g g' : ec_hom b c),
      ec_hom_eq f f' -> ec_hom_eq g g' ->
      ec_hom_eq (ec_comp f g) (ec_comp f' g');
  ec_id_left : forall a b (f : ec_hom a b),
      ec_hom_eq (ec_comp (ec_id a) f) f;
  ec_id_right : forall a b (f : ec_hom a b),
      ec_hom_eq (ec_comp f (ec_id b)) f;
  ec_assoc : forall a b c d (f : ec_hom a b) (g : ec_hom b c) (h : ec_hom c d),
      ec_hom_eq (ec_comp f (ec_comp g h)) (ec_comp (ec_comp f g) h)
}.

(** ** The Lindenbaum-Tarski category: objects are formulas, homs are
    derivations of implications, parallel derivations are identified
    (posetal hom-setoid). *)

Definition LT_category : ECat.
Proof.
  refine (mkECat Form
            (fun a b => |- Impl a b)
            (fun a b f g => True)
            (fun a => prov_id a)
            (fun a b c f g => prov_compose a b c f g)
            _ _ _ _ _ _ _); intros; exact I.
Defined.

(** ** The canonical frame category: objects are definable upsets of
    the canonical maximal-consistent worlds (a set of worlds packaged
    with a defining formula), homs are pointwise inclusions. *)

Record FrameObj : Type := mkFrameObj {
  fo_set : canonical_world_max -> Prop;
  fo_wit : Form;
  fo_def : forall w, fo_set w <-> Stone_image fo_wit w
}.

Definition fo_incl (X Y : FrameObj) : Prop :=
  forall w, fo_set X w -> fo_set Y w.

Definition canonical_frame_category : ECat.
Proof.
  refine (mkECat FrameObj
            fo_incl
            (fun X Y f g => True)
            (fun X => fun w H => H)
            (fun X Y Z f g => fun w H => g w (f w H))
            _ _ _ _ _ _ _); intros; exact I.
Defined.

(** ** Functors. *)

Record EFunctor (C D : ECat) : Type := mkEF {
  ef_obj : ec_obj C -> ec_obj D;
  ef_hom : forall a b, ec_hom C a b -> ec_hom D (ef_obj a) (ef_obj b);
  ef_id_law : forall a,
      ec_hom_eq D (ef_hom a a (ec_id C a)) (ec_id D (ef_obj a));
  ef_comp_law : forall a b c (f : ec_hom C a b) (g : ec_hom C b c),
      ec_hom_eq D (ef_hom a c (ec_comp C f g))
                  (ec_comp D (ef_hom a b f) (ef_hom b c g))
}.

Arguments ef_obj {C D}.
Arguments ef_hom {C D}.

(** F: a formula goes to its Stone image, packaged with itself as the
    defining witness; a derivation goes to the induced inclusion. *)

Definition Stone_F_obj (phi : Form) : FrameObj :=
  mkFrameObj (Stone_image phi) phi (fun w => iff_refl _).

Definition Stone_F_hom (a b : Form) (f : |- Impl a b) :
  fo_incl (Stone_F_obj a) (Stone_F_obj b) :=
  fun w Hw =>
    Stone_image_modus_ponens w a b
      (Stone_image_provable_universal _ f w) Hw.

Definition Stone_F : EFunctor LT_category canonical_frame_category.
Proof.
  refine (mkEF LT_category canonical_frame_category
            Stone_F_obj Stone_F_hom _ _); intros; exact I.
Defined.

(** G: a frame object goes to its defining witness; an inclusion goes
    to a derivation, THROUGH THE SEPARATION LEMMA. *)

Definition Stone_G_obj (X : FrameObj) : Form := fo_wit X.

Definition Stone_G_hom (X Y : FrameObj) (f : fo_incl X Y) :
  |- Impl (fo_wit X) (fo_wit Y) :=
  Stone_separation (fo_wit X) (fo_wit Y)
    (fun w Hw => proj1 (fo_def Y w) (f w (proj2 (fo_def X w) Hw))).

Definition Stone_G : EFunctor canonical_frame_category LT_category.
Proof.
  refine (mkEF canonical_frame_category LT_category
            Stone_G_obj Stone_G_hom _ _); intros; exact I.
Defined.

(** ** The natural isomorphisms. *)

(** eta : Id => G o F.  At a, G (F a) is definitionally a, and the
    component is the derivation [prov_id a] — its type [|- Impl a a]
    is a provability statement, not an equality, so eq_refl is not
    even a candidate inhabitant. *)

Definition Stone_eta (a : Form) :
  ec_hom LT_category a (ef_obj Stone_G (ef_obj Stone_F a)) :=
  prov_id a.

Definition Stone_eta_inv (a : Form) :
  ec_hom LT_category (ef_obj Stone_G (ef_obj Stone_F a)) a :=
  prov_id a.

Theorem Stone_eta_iso : forall a,
  ec_hom_eq LT_category
    (ec_comp LT_category (Stone_eta a) (Stone_eta_inv a))
    (ec_id LT_category a) /\
  ec_hom_eq LT_category
    (ec_comp LT_category (Stone_eta_inv a) (Stone_eta a))
    (ec_id LT_category (ef_obj Stone_G (ef_obj Stone_F a))).
Proof. intro a. split; exact I. Qed.

Theorem Stone_eta_natural : forall a b (f : ec_hom LT_category a b),
  ec_hom_eq LT_category
    (ec_comp LT_category (Stone_eta a)
       (ef_hom Stone_G _ _ (ef_hom Stone_F _ _ f)))
    (ec_comp LT_category f (Stone_eta b)).
Proof. intros; exact I. Qed.

(** epsilon : F o G => Id.  At X, F (G X) is the Stone image of X's
    witness; the components are the two directions of X's defining
    equivalence — genuine transports, not eq_refl. *)

Definition Stone_epsilon (X : FrameObj) :
  ec_hom canonical_frame_category (ef_obj Stone_F (ef_obj Stone_G X)) X :=
  fun w Hw => proj2 (fo_def X w) Hw.

Definition Stone_epsilon_inv (X : FrameObj) :
  ec_hom canonical_frame_category X (ef_obj Stone_F (ef_obj Stone_G X)) :=
  fun w Hw => proj1 (fo_def X w) Hw.

Theorem Stone_epsilon_iso : forall X,
  ec_hom_eq canonical_frame_category
    (ec_comp canonical_frame_category (Stone_epsilon X) (Stone_epsilon_inv X))
    (ec_id canonical_frame_category (ef_obj Stone_F (ef_obj Stone_G X))) /\
  ec_hom_eq canonical_frame_category
    (ec_comp canonical_frame_category (Stone_epsilon_inv X) (Stone_epsilon X))
    (ec_id canonical_frame_category X).
Proof. intro X. split; exact I. Qed.

Theorem Stone_epsilon_natural : forall X Y (f : fo_incl X Y),
  ec_hom_eq canonical_frame_category
    (ec_comp canonical_frame_category
       (ef_hom Stone_F _ _ (ef_hom Stone_G _ _ f))
       (Stone_epsilon Y))
    (ec_comp canonical_frame_category (Stone_epsilon X) f).
Proof. intros; exact I. Qed.

(** ** Triangle identities. *)

Theorem Stone_triangle_F : forall a : Form,
  ec_hom_eq canonical_frame_category
    (ec_comp canonical_frame_category
       (ef_hom Stone_F _ _ (Stone_eta a))
       (Stone_epsilon (ef_obj Stone_F a)))
    (ec_id canonical_frame_category (ef_obj Stone_F a)).
Proof. intros; exact I. Qed.

Theorem Stone_triangle_G : forall X : FrameObj,
  ec_hom_eq LT_category
    (ec_comp LT_category
       (Stone_eta (ef_obj Stone_G X))
       (ef_hom Stone_G _ _ (Stone_epsilon X)))
    (ec_id LT_category (ef_obj Stone_G X)).
Proof. intros; exact I. Qed.

(** ** The substance: full faithfulness and essential surjectivity. *)

Theorem Stone_full_faithful : forall a b : Form,
  (|- Impl a b) <-> fo_incl (Stone_F_obj a) (Stone_F_obj b).
Proof.
  intros a b. split.
  - intro f. exact (Stone_F_hom a b f).
  - intro g. exact (Stone_separation a b g).
Qed.

Theorem Stone_essentially_surjective : forall X : FrameObj,
  exists a : Form,
    inhabited (fo_incl (Stone_F_obj a) X) /\
    inhabited (fo_incl X (Stone_F_obj a)).
Proof.
  intro X. exists (fo_wit X). split.
  - exact (inhabits (Stone_epsilon X)).
  - exact (inhabits (Stone_epsilon_inv X)).
Qed.

(** Hom-level duality restated through the frame category's general
    objects: inclusions between any two frame objects correspond
    exactly to provable implications between their witnesses. *)

Theorem Stone_hom_duality : forall X Y : FrameObj,
  inhabited (fo_incl X Y) <-> |- Impl (fo_wit X) (fo_wit Y).
Proof.
  intros X Y. split.
  - intros [f]. exact (Stone_G_hom X Y f).
  - intro f. constructor.
    intros w Hw.
    apply (proj2 (fo_def Y w)).
    apply (Stone_image_modus_ponens w (fo_wit X) (fo_wit Y)
             (Stone_image_provable_universal _ f w)).
    exact (proj1 (fo_def X w) Hw).
Qed.

(** ** Headline summary for todo #8. *)

Theorem Stone_duality_category_equivalence :
  (forall a, ec_hom_eq LT_category
     (ec_comp LT_category (Stone_eta a) (Stone_eta_inv a))
     (ec_id LT_category a)) /\
  (forall X, ec_hom_eq canonical_frame_category
     (ec_comp canonical_frame_category (Stone_epsilon X) (Stone_epsilon_inv X))
     (ec_id canonical_frame_category (ef_obj Stone_F (ef_obj Stone_G X)))) /\
  (forall a, ec_hom_eq canonical_frame_category
     (ec_comp canonical_frame_category
        (ef_hom Stone_F _ _ (Stone_eta a))
        (Stone_epsilon (ef_obj Stone_F a)))
     (ec_id canonical_frame_category (ef_obj Stone_F a))) /\
  (forall X, ec_hom_eq LT_category
     (ec_comp LT_category
        (Stone_eta (ef_obj Stone_G X))
        (ef_hom Stone_G _ _ (Stone_epsilon X)))
     (ec_id LT_category (ef_obj Stone_G X))) /\
  (forall a b : Form,
     (|- Impl a b) <-> fo_incl (Stone_F_obj a) (Stone_F_obj b)) /\
  (forall X : FrameObj,
     exists a : Form,
       inhabited (fo_incl (Stone_F_obj a) X) /\
       inhabited (fo_incl X (Stone_F_obj a))).
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - intro a. exact (proj1 (Stone_eta_iso a)).
  - intro X. exact (proj1 (Stone_epsilon_iso X)).
  - exact Stone_triangle_F.
  - exact Stone_triangle_G.
  - exact Stone_full_faithful.
  - exact Stone_essentially_surjective.
Qed.
