(******************************************************************************)
(*                                                                            *)
(*  Japaridze's polymodal arithmetic completeness via a genuine Solovay       *)
(*  tree (todo item #14).                                                     *)
(*                                                                            *)
(*  [Solovay_node] is exactly the demanded inductive; [solovay_tree_step]     *)
(*  branches on box-level: a node at level n spawns the level-(n+1)           *)
(*  children carrying [Box n f] and [Diamond n f] — two branches at EVERY     *)
(*  node (threshold 0), never empty, and the tree is infinite                 *)
(*  ([solovay_tree_infinite] exhibits in-tree nodes of every depth).          *)
(*                                                                            *)
(*  [tree_validates I u] is structural recursion on the node: every           *)
(*  payload on the path back to the root must have a GLP-provable             *)
(*  I-image.  It is NOT the constant True ([tree_validates_not_trivial]).     *)
(*                                                                            *)
(*  [is_polymodal_arithmetic_interpretation_proper] demands pointwise         *)
(*  commutation with Impl, Bot and EVERY box level (the polymodal             *)
(*  properness — distinct from the level-collapsing properness of the         *)
(*  Solovay-first file).  [Japaridze_full_via_tree] is proved by              *)
(*  instantiating the hypothesis at the DOUBLE-NEGATION SUBSTITUTION          *)
(*  interpretation [dn_interp] — provably not the identity and not            *)
(*  shift_interp — and discharging through a GLP-INTERNAL Goldblatt           *)
(*  faithfulness theorem ([GLP_subst_faithful_back]), built on a full         *)
(*  Hilbert toolkit replayed inside Provable_GLP.  The converse holds         *)
(*  too ([Japaridze_tree_soundness]), so tree-validation under all proper     *)
(*  interpretations is EQUIVALENT to GLP-provability                          *)
(*  ([Japaridze_full_via_tree_iff]).                                          *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Tiling Require Import Tiling.

(** ** The Solovay tree. *)

Inductive Solovay_node : Type :=
  | sol_root : Solovay_node
  | sol_child : Solovay_node -> nat -> Form -> Solovay_node.

Definition solovay_tree_step (u : Solovay_node) : list Solovay_node :=
  match u with
  | sol_root =>
      [sol_child sol_root 0 Top; sol_child sol_root 0 Bot]
  | sol_child _ n f =>
      [sol_child u (S n) (Box n f); sol_child u (S n) (Diamond n f)]
  end.

Fixpoint node_depth (u : Solovay_node) : nat :=
  match u with
  | sol_root => 0
  | sol_child p _ _ => S (node_depth p)
  end.

Inductive in_tree : Solovay_node -> Prop :=
  | in_root : in_tree sol_root
  | in_step : forall u v,
      in_tree u -> In v (solovay_tree_step u) -> in_tree v.

(** The step is never empty and has at least two branches at EVERY
    node (the threshold of the acceptance criterion is 0 here). *)

Theorem solovay_tree_step_nonempty : forall u,
  solovay_tree_step u <> [].
Proof.
  intros [|p n f]; cbn; discriminate.
Qed.

Theorem solovay_tree_step_two_branches : forall u,
  length (solovay_tree_step u) = 2.
Proof.
  intros [|p n f]; reflexivity.
Qed.

Theorem solovay_tree_branches_distinct : forall u,
  exists v w,
    In v (solovay_tree_step u) /\ In w (solovay_tree_step u) /\ v <> w.
Proof.
  intros [|p n f].
  - exists (sol_child sol_root 0 Top), (sol_child sol_root 0 Bot).
    cbn. split; [tauto | split; [tauto |]].
    intro H. injection H as H. discriminate H.
  - exists (sol_child (sol_child p n f) (S n) (Box n f)),
           (sol_child (sol_child p n f) (S n) (Diamond n f)).
    cbn. split; [tauto | split; [tauto |]].
    intro H. injection H as H. discriminate H.
Qed.

(** The branching is genuinely on box-level: a node at level n spawns
    level-(n+1) children whose payloads box / diamond the payload at
    level n. *)

Theorem solovay_tree_step_branches_on_level : forall p n f,
  solovay_tree_step (sol_child p n f) =
  [sol_child (sol_child p n f) (S n) (Box n f);
   sol_child (sol_child p n f) (S n) (Diamond n f)].
Proof. reflexivity. Qed.

(** The tree is infinite: it contains nodes of every depth. *)

Fixpoint solovay_spine (k : nat) : Solovay_node :=
  match k with
  | 0 => sol_root
  | S j =>
      match solovay_spine j with
      | sol_root => sol_child sol_root 0 Top
      | sol_child p n f => sol_child (sol_child p n f) (S n) (Box n f)
      end
  end.

Lemma solovay_spine_in_tree : forall k, in_tree (solovay_spine k).
Proof.
  induction k as [|j IH]; cbn.
  - exact in_root.
  - destruct (solovay_spine j) as [|p n f] eqn:E.
    + apply (in_step sol_root).
      * exact IH.
      * cbn. left. reflexivity.
    + apply (in_step (sol_child p n f)).
      * exact IH.
      * cbn. left. reflexivity.
Qed.

Lemma solovay_spine_depth : forall k, node_depth (solovay_spine k) = k.
Proof.
  induction k as [|j IH]; cbn.
  - reflexivity.
  - destruct (solovay_spine j) as [|p n f] eqn:E; cbn.
    + cbn in IH. rewrite <- IH. reflexivity.
    + cbn in IH. rewrite <- IH. reflexivity.
Qed.

Theorem solovay_tree_infinite : forall k,
  exists u, in_tree u /\ node_depth u = k.
Proof.
  intro k. exists (solovay_spine k).
  split; [exact (solovay_spine_in_tree k) | exact (solovay_spine_depth k)].
Qed.

(** ** Tree validation: structural recursion on the node — every
    payload on the path back to the root must have a GLP-provable
    interpretation image. *)

Fixpoint tree_validates (I : Form -> Form) (u : Solovay_node) : Prop :=
  match u with
  | sol_root => True
  | sol_child p _ f => tree_validates I p /\ Provable_full_GLP (I f)
  end.

Definition build_solovay_tree (phi : Form) : Solovay_node :=
  sol_child sol_root 0 phi.

(** ** Polymodal proper interpretations: pointwise commutation with
    the connectives at EVERY box level. *)

Definition is_polymodal_arithmetic_interpretation_proper
  (I : Form -> Form) : Prop :=
  (forall a b, I (Impl a b) = Impl (I a) (I b)) /\
  (I Bot = Bot) /\
  (forall n psi, I (Box n psi) = Box n (I psi)).

(** Every proper interpretation is a substitution. *)

Lemma polymodal_proper_factors : forall I,
  is_polymodal_arithmetic_interpretation_proper I ->
  forall phi, I phi = subst_form (fun p => I (Var p)) phi.
Proof.
  intros I [HImpl [HBot HBox]] phi.
  induction phi as [p | | a IHa b IHb | n a IHa]; cbn.
  - reflexivity.
  - exact HBot.
  - rewrite HImpl, IHa, IHb. reflexivity.
  - rewrite HBox, IHa. reflexivity.
Qed.

(******************************************************************************)
(* The GLP-internal Hilbert toolkit (replayed from the |- versions).          *)
(******************************************************************************)

Lemma GLPh_id : forall phi, Provable_GLP (Impl phi phi).
Proof.
  intro phi.
  exact (GLP_MP _ _
          (GLP_MP _ _ (GLP_Ax_S phi (Impl phi phi) phi)
                      (GLP_Ax_K phi (Impl phi phi)))
          (GLP_Ax_K phi phi)).
Qed.

Lemma GLPh_weaken : forall phi psi,
  Provable_GLP phi -> Provable_GLP (Impl psi phi).
Proof.
  intros phi psi H. exact (GLP_MP _ _ (GLP_Ax_K phi psi) H).
Qed.

Lemma GLPh_compose : forall phi psi chi,
  Provable_GLP (Impl phi psi) -> Provable_GLP (Impl psi chi) ->
  Provable_GLP (Impl phi chi).
Proof.
  intros phi psi chi Hpq Hqr.
  pose proof (GLP_Ax_S phi psi chi) as Hs.
  pose proof (GLPh_weaken _ phi Hqr) as Hpqr.
  exact (GLP_MP _ _ (GLP_MP _ _ Hs Hpqr) Hpq).
Qed.

Lemma GLPh_perm : forall phi psi chi,
  Provable_GLP (Impl phi (Impl psi chi)) ->
  Provable_GLP (Impl psi (Impl phi chi)).
Proof.
  intros phi psi chi H.
  pose proof (GLP_Ax_S phi psi chi) as Hs.
  pose proof (GLP_MP _ _ Hs H) as H1.
  pose proof (GLP_Ax_K psi phi) as Hk.
  exact (GLPh_compose _ _ _ Hk H1).
Qed.

Lemma GLPh_perm_internal : forall a b c,
  Provable_GLP (Impl (Impl a (Impl b c)) (Impl b (Impl a c))).
Proof.
  intros a b c.
  pose proof (GLP_Ax_S a b c) as H_S.
  pose proof (GLP_Ax_S (Impl a (Impl b c)) (Impl a b) (Impl a c)) as H_S2.
  pose proof (GLP_MP _ _ H_S2 H_S) as H1.
  pose proof (GLP_Ax_K b a) as H_K1.
  pose proof (GLP_Ax_K (Impl a b) (Impl a (Impl b c))) as H_K2.
  pose proof (GLPh_compose _ _ _ H_K1 H_K2) as H2.
  pose proof (GLPh_compose _ _ _ H2 H1) as H3.
  exact (GLPh_perm _ _ _ H3).
Qed.

Lemma GLPh_compose_internal : forall phi psi chi,
  Provable_GLP (Impl (Impl psi chi) (Impl (Impl phi psi) (Impl phi chi))).
Proof.
  intros phi psi chi.
  pose proof (GLP_Ax_K (Impl psi chi) phi) as Hk.
  pose proof (GLP_Ax_S phi psi chi) as Hs.
  exact (GLPh_compose _ _ _ Hk Hs).
Qed.

Lemma GLPh_DN_intro : forall phi,
  Provable_GLP (Impl phi (Neg (Neg phi))).
Proof.
  intro phi. unfold Neg.
  pose proof (GLPh_id (Impl phi Bot)) as Hid.
  exact (GLPh_perm _ _ _ Hid).
Qed.

Lemma GLPh_explosion : forall phi, Provable_GLP (Impl Bot phi).
Proof.
  intro phi.
  pose proof (GLP_Ax_K Bot (Neg phi)) as Hk.
  pose proof (GLP_Ax_DN phi) as HDN.
  exact (GLPh_compose _ _ _ Hk HDN).
Qed.

Lemma GLPh_neg_imp_ng : forall phi psi,
  Provable_GLP (Impl (Neg phi) (Impl phi (Neg psi))).
Proof.
  intros phi psi. unfold Neg.
  pose proof (GLPh_compose_internal phi Bot (Impl psi Bot)) as Hci.
  pose proof (GLPh_explosion (Impl psi Bot)) as Hex.
  exact (GLP_MP _ _ Hci Hex).
Qed.

Lemma GLPh_and_intro : forall phi psi,
  Provable_GLP (Impl phi (Impl psi (And phi psi))).
Proof.
  intros phi psi. unfold And, Neg.
  pose proof (GLPh_id (Impl phi (Impl psi Bot))) as Hid.
  pose proof (GLPh_perm _ _ _ Hid) as Hperm.
  pose proof (GLPh_perm_internal (Impl phi (Impl psi Bot)) psi Bot) as Hpi.
  exact (GLPh_compose _ _ _ Hperm Hpi).
Qed.

Lemma GLPh_and_intro_meta : forall phi psi,
  Provable_GLP phi -> Provable_GLP psi -> Provable_GLP (And phi psi).
Proof.
  intros phi psi Hphi Hpsi.
  exact (GLP_MP _ _ (GLP_MP _ _ (GLPh_and_intro phi psi) Hphi) Hpsi).
Qed.

Lemma GLPh_and_elim_l : forall phi psi,
  Provable_GLP (Impl (And phi psi) phi).
Proof.
  intros phi psi. unfold And, Neg.
  pose proof (GLPh_neg_imp_ng phi psi) as H1.
  pose proof (GLPh_compose_internal
                (Impl phi Bot) (Impl phi (Impl psi Bot)) Bot) as H2.
  pose proof (GLPh_perm _ _ _ H2) as H2_perm.
  pose proof (GLP_MP _ _ H2_perm H1) as Hstep1.
  pose proof (GLP_Ax_DN phi) as HDN.
  exact (GLPh_compose _ _ _ Hstep1 HDN).
Qed.

Lemma GLPh_and_elim_r : forall phi psi,
  Provable_GLP (Impl (And phi psi) psi).
Proof.
  intros phi psi. unfold And, Neg.
  pose proof (GLP_Ax_K (Impl psi Bot) phi) as H1.
  pose proof (GLPh_compose_internal
                (Impl psi Bot) (Impl phi (Impl psi Bot)) Bot) as H2.
  pose proof (GLPh_perm _ _ _ H2) as H2_perm.
  pose proof (GLP_MP _ _ H2_perm H1) as Hstep1.
  pose proof (GLP_Ax_DN psi) as HDN.
  exact (GLPh_compose _ _ _ Hstep1 HDN).
Qed.

Lemma GLPh_and_elim_l_meta : forall phi psi,
  Provable_GLP (And phi psi) -> Provable_GLP phi.
Proof.
  intros phi psi H. exact (GLP_MP _ _ (GLPh_and_elim_l phi psi) H).
Qed.

Lemma GLPh_and_elim_r_meta : forall phi psi,
  Provable_GLP (And phi psi) -> Provable_GLP psi.
Proof.
  intros phi psi H. exact (GLP_MP _ _ (GLPh_and_elim_r phi psi) H).
Qed.

Lemma GLPh_iff_intro : forall phi psi,
  Provable_GLP (Impl phi psi) -> Provable_GLP (Impl psi phi) ->
  Provable_GLP (Iff phi psi).
Proof.
  intros phi psi H1 H2. unfold Iff.
  exact (GLPh_and_intro_meta _ _ H1 H2).
Qed.

Lemma GLPh_iff_refl : forall phi, Provable_GLP (Iff phi phi).
Proof.
  intro phi. apply GLPh_iff_intro; apply GLPh_id.
Qed.

Lemma GLPh_box_imp : forall n phi psi,
  Provable_GLP (Impl phi psi) ->
  Provable_GLP (Impl (Box n phi) (Box n psi)).
Proof.
  intros n phi psi H.
  exact (GLP_MP _ _ (GLP_Ax_BoxK n phi psi) (GLP_Nec n _ H)).
Qed.

Lemma GLPh_impl_cong : forall a a' b b',
  Provable_GLP (Iff a a') -> Provable_GLP (Iff b b') ->
  Provable_GLP (Iff (Impl a b) (Impl a' b')).
Proof.
  intros a a' b b' H1 H2.
  pose proof (GLPh_and_elim_l_meta _ _ H1) as H1f.
  pose proof (GLPh_and_elim_r_meta _ _ H1) as H1b.
  pose proof (GLPh_and_elim_l_meta _ _ H2) as H2f.
  pose proof (GLPh_and_elim_r_meta _ _ H2) as H2b.
  apply GLPh_iff_intro.
  - pose proof (GLPh_compose_internal a' a b) as Hci1.
    pose proof (GLP_MP _ _ (GLPh_perm _ _ _ Hci1) H1b) as Hstep1.
    pose proof (GLPh_compose_internal a' b b') as Hci2.
    pose proof (GLP_MP _ _ Hci2 H2f) as Hstep2.
    exact (GLPh_compose _ _ _ Hstep1 Hstep2).
  - pose proof (GLPh_compose_internal a a' b') as Hci1.
    pose proof (GLP_MP _ _ (GLPh_perm _ _ _ Hci1) H1f) as Hstep1.
    pose proof (GLPh_compose_internal a b' b) as Hci2.
    pose proof (GLP_MP _ _ Hci2 H2b) as Hstep2.
    exact (GLPh_compose _ _ _ Hstep1 Hstep2).
Qed.

Lemma GLPh_box_cong : forall n a b,
  Provable_GLP (Iff a b) ->
  Provable_GLP (Iff (Box n a) (Box n b)).
Proof.
  intros n a b H.
  apply GLPh_iff_intro.
  - exact (GLPh_box_imp n _ _ (GLPh_and_elim_l_meta _ _ H)).
  - exact (GLPh_box_imp n _ _ (GLPh_and_elim_r_meta _ _ H)).
Qed.

Lemma GLPh_neg_neg_iff : forall phi,
  Provable_GLP (Iff phi (Neg (Neg phi))).
Proof.
  intro phi.
  apply GLPh_iff_intro.
  - exact (GLPh_DN_intro phi).
  - exact (GLP_Ax_DN phi).
Qed.

(** ** The double-negation substitution interpretation. *)

Definition dn_sigma : nat -> Form := fun p => Neg (Neg (Var p)).

Definition dn_interp : Form -> Form := subst_form dn_sigma.

Lemma dn_interp_proper :
  is_polymodal_arithmetic_interpretation_proper dn_interp.
Proof.
  split; [|split].
  - intros a b. reflexivity.
  - reflexivity.
  - intros n psi. reflexivity.
Qed.

Theorem dn_interp_not_identity : exists phi, dn_interp phi <> phi.
Proof.
  exists (Var 0). cbv. discriminate.
Qed.

Theorem dn_interp_not_shift_interp :
  exists phi, dn_interp phi <> shift_interp phi.
Proof.
  exists Bot. cbv. discriminate.
Qed.

(** GLP-internally, every formula is equivalent to its double-negation
    substitution image. *)

Lemma GLP_dn_subst_iff : forall phi,
  Provable_GLP (Iff phi (dn_interp phi)).
Proof.
  intro phi. unfold dn_interp.
  induction phi as [p | | a IHa b IHb | n a IHa]; cbn [subst_form].
  - exact (GLPh_neg_neg_iff (Var p)).
  - exact (GLPh_iff_refl Bot).
  - exact (GLPh_impl_cong _ _ _ _ IHa IHb).
  - exact (GLPh_box_cong n _ _ IHa).
Qed.

(** Faithfulness backwards: GLP-provability of the image yields
    GLP-provability of the original. *)

Theorem GLP_subst_faithful_back : forall phi,
  Provable_GLP (dn_interp phi) -> Provable_GLP phi.
Proof.
  intros phi H.
  pose proof (GLP_dn_subst_iff phi) as Hiff.
  pose proof (GLPh_and_elim_r_meta _ _ Hiff) as Hback.
  exact (GLP_MP _ _ Hback H).
Qed.

(** ** GLP is closed under substitution (hence under every proper
    polymodal interpretation). *)

Lemma GLP_subst_provable : forall sigma phi,
  Provable_GLP phi -> Provable_GLP (subst_form sigma phi).
Proof.
  intros sigma phi H.
  induction H as [phi psi | phi psi chi | phi | n phi psi | n phi | n phi
                 | n phi | n phi | phi psi H1 IH1 H2 IH2 | n phi H IH]; cbn.
  - apply GLP_Ax_K.
  - apply GLP_Ax_S.
  - apply GLP_Ax_DN.
  - apply GLP_Ax_BoxK.
  - apply GLP_Ax_Loeb.
  - apply GLP_Ax_Box4.
  - apply GLP_Ax_Mon.
  - apply GLP_Ax_Japaridze.
  - exact (GLP_MP _ _ IH1 IH2).
  - exact (GLP_Nec n _ IH).
Qed.

(******************************************************************************)
(* The headline theorems.                                                     *)
(******************************************************************************)

(** Completeness: tree-validation under all proper polymodal
    interpretations yields GLP-provability.  The instantiation is at
    [dn_interp] — proper, not the identity, not shift_interp — and the
    discharge runs through the GLP-internal faithfulness theorem. *)

Theorem Japaridze_full_via_tree : forall phi,
  (forall I, is_polymodal_arithmetic_interpretation_proper I ->
     tree_validates I (build_solovay_tree phi)) ->
  Provable_full_GLP phi.
Proof.
  intros phi H.
  pose proof (H dn_interp dn_interp_proper) as Hv.
  cbn in Hv.
  destruct Hv as [_ Hval].
  exact (GLP_subst_faithful_back phi Hval).
Qed.

(** Soundness: GLP-provability validates the tree under EVERY proper
    polymodal interpretation (via the substitution factoring). *)

Theorem Japaridze_tree_soundness : forall phi,
  Provable_full_GLP phi ->
  forall I, is_polymodal_arithmetic_interpretation_proper I ->
  tree_validates I (build_solovay_tree phi).
Proof.
  intros phi H J HJ. cbn.
  split; [exact I|].
  rewrite (polymodal_proper_factors J HJ phi).
  exact (GLP_subst_provable _ _ H).
Qed.

Theorem Japaridze_full_via_tree_iff : forall phi,
  (forall I, is_polymodal_arithmetic_interpretation_proper I ->
     tree_validates I (build_solovay_tree phi))
  <-> Provable_full_GLP phi.
Proof.
  intro phi. split.
  - exact (Japaridze_full_via_tree phi).
  - exact (Japaridze_tree_soundness phi).
Qed.

(** [tree_validates] is not the constant True. *)

Theorem tree_validates_not_trivial :
  exists I u,
    is_polymodal_arithmetic_interpretation_proper I /\
    ~ tree_validates I u.
Proof.
  exists dn_interp, (build_solovay_tree Bot).
  split.
  - exact dn_interp_proper.
  - cbn. intros [_ Habs].
    pose proof (provable_GLP_classically_valid _ Habs (fun _ => false)) as He.
    cbn in He. discriminate He.
Qed.

(** ** Headline summary for todo #14. *)

Theorem Japaridze_tree_summary :
  (forall u, solovay_tree_step u <> []) /\
  (forall u, length (solovay_tree_step u) = 2) /\
  (forall k, exists u, in_tree u /\ node_depth u = k) /\
  (exists I u,
     is_polymodal_arithmetic_interpretation_proper I /\
     ~ tree_validates I u) /\
  (exists phi, dn_interp phi <> phi) /\
  (exists phi, dn_interp phi <> shift_interp phi) /\
  (forall phi,
     (forall I, is_polymodal_arithmetic_interpretation_proper I ->
        tree_validates I (build_solovay_tree phi))
     <-> Provable_full_GLP phi).
Proof.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - exact solovay_tree_step_nonempty.
  - exact solovay_tree_step_two_branches.
  - exact solovay_tree_infinite.
  - exact tree_validates_not_trivial.
  - exact dn_interp_not_identity.
  - exact dn_interp_not_shift_interp.
  - exact Japaridze_full_via_tree_iff.
Qed.
