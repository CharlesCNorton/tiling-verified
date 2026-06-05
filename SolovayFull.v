(******************************************************************************)
(*                                                                            *)
(*  Solovay first and second arithmetic completeness, full statements         *)
(*  (todo items #10 and #13).                                                 *)
(*                                                                            *)
(*  The engine is the GL-provability reflection semantics [VS]:               *)
(*    Var p        |-> val p                                                  *)
(*    Bot          |-> False                                                  *)
(*    Impl a b     |-> VS a -> VS b                                           *)
(*    Box 0 psi    |-> Provable_GL psi                                        *)
(*    Box (S n) _  |-> False.                                                 *)
(*                                                                            *)
(*  GL is sound for [VS] (the Loeb case is the GL-internal Loeb               *)
(*  metatheorem; the Box4 case is necessitation).  Solovay's S is also        *)
(*  sound: the reflection axiom's [VS]-image is precisely GL-provable-       *)
(*  implies-VS-true, which is GL-soundness itself.  Three consequences:       *)
(*                                                                            *)
(*  1. Box-elimination is admissible for GL — no Kripke completeness          *)
(*     needed.  This closes the gap between the existing                      *)
(*     [Solovay_first_completeness_level_0_only_with_outer_Box_0] and the     *)
(*     genuine [Solovay_first_full] (level_0_only form, both directions).     *)
(*  2. The UNRESTRICTED todo-statements of Solovay-first and Solovay-second   *)
(*     are FALSE: proper interpretations collapse all box levels to 0,        *)
(*     while Provable_GL/Provable_S generate no positive [Box (S n)]          *)
(*     content.  Witness: phi := Box 5 Top.  Machine-checked refutations      *)
(*     below.                                                                 *)
(*  3. S is conservative over GL on boxed formulas                            *)
(*     ([Provable_S_box0_iff_GL]) yet strictly stronger overall               *)
(*     ([Provable_S_strictly_stronger_than_GL]).                              *)
(*                                                                            *)
(*  The todo's named artifacts are realized genuinely: proof terms get        *)
(*  Goedel codes ([encode_pt] / [decode_pt] with a verified round trip),      *)
(*  [encodes_proof d k] is the decidable-shape proof-checking predicate,      *)
(*  provability IS the Sigma_1 sentence [exists d, encodes_proof d ⌜phi⌝]    *)
(*  ([provable_iff_sigma1_proof_code]), and [arith_embed_GL_sat] translates   *)
(*  [Box phi] to exactly that Sigma_1 sentence — NOT to [Bew_n 0 ⌜phi⌝]      *)
(*  directly and NOT to a top-sentence ([arith_embed_GL_sat_box_bot_false]).  *)
(*  The Solovay walk [solovay_function] gets its R-successor-tracking         *)
(*  correctness theorems.                                                     *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical.
Import ListNotations.
From Tiling Require Import Tiling.

(** ** The GL-provability reflection semantics. *)

Fixpoint VS (val : nat -> Prop) (phi : Form) : Prop :=
  match phi with
  | Var p => val p
  | Bot => False
  | Impl a b => VS val a -> VS val b
  | Box n psi => match n with
                 | 0 => Provable_GL psi
                 | S _ => False
                 end
  end.

(** The GL-internal Loeb metatheorem: from GL |- (Box 0 psi -> psi)
    conclude GL |- psi.  Mirrors [loeb_metatheorem]. *)

Lemma GL_loeb_metatheorem : forall psi,
  Provable_GL (Impl (Box 0 psi) psi) -> Provable_GL psi.
Proof.
  intros psi H.
  pose proof (GL_Nec _ H) as Hnec.
  pose proof (GL_Ax_Loeb psi) as HLoeb.
  pose proof (GL_MP _ _ HLoeb Hnec) as Hbox.
  exact (GL_MP _ _ H Hbox).
Qed.

(** GL is sound for [VS]. *)

Theorem Provable_GL_VS_sound : forall phi,
  Provable_GL phi -> forall val, VS val phi.
Proof.
  intros phi H.
  induction H as [phi psi | phi psi chi | phi | phi psi | phi | phi
                 | phi psi H1 IH1 H2 IH2 | phi H IH]; intro val; cbn.
  - intros Ha _. exact Ha.
  - intros Hf Hg Ha. exact (Hf Ha (Hg Ha)).
  - exact (NNPP (VS val phi)).
  - intros Hab Ha. exact (GL_MP _ _ Hab Ha).
  - intro Hl. exact (GL_loeb_metatheorem _ Hl).
  - intro Hb. exact (GL_Nec _ Hb).
  - exact (IH1 val (IH2 val)).
  - exact H.
Qed.

(** Solovay's S is sound for [VS]: the reflection instance's image is
    GL-soundness itself. *)

Theorem Provable_S_VS_sound : forall phi,
  Provable_S phi -> forall val, VS val phi.
Proof.
  intros phi H.
  induction H as [phi HGL | phi Hcv | phi psi H1 IH1 H2 IH2]; intro val.
  - exact (Provable_GL_VS_sound phi HGL val).
  - cbn. intro HGLphi. exact (Provable_GL_VS_sound phi HGLphi val).
  - exact (IH1 val (IH2 val)).
Qed.

(** ** Consequence 1: box-elimination is admissible. *)

Theorem GL_box_elim : forall psi,
  Provable_GL (Box 0 psi) -> Provable_GL psi.
Proof.
  intros psi H.
  exact (Provable_GL_VS_sound _ H (fun _ => True)).
Qed.

Theorem GL_box_elim_iff : forall psi,
  Provable_GL (Box 0 psi) <-> Provable_GL psi.
Proof.
  intro psi. split.
  - exact (GL_box_elim psi).
  - exact (GL_Nec psi).
Qed.

Theorem S_box_elim : forall psi,
  Provable_S (Box 0 psi) -> Provable_GL psi.
Proof.
  intros psi H.
  exact (Provable_S_VS_sound _ H (fun _ => True)).
Qed.

(** S proves a boxed formula exactly when GL proves the body: S is
    conservative over GL at boxed positions. *)

Theorem Provable_S_box0_iff_GL : forall psi,
  Provable_S (Box 0 psi) <-> Provable_GL psi.
Proof.
  intro psi. split.
  - exact (S_box_elim psi).
  - intro H. apply S_GL_subsumes. apply GL_Nec. exact H.
Qed.

(** ** No positive high boxes in GL or S. *)

Theorem Provable_GL_no_high_box : forall n psi,
  ~ Provable_GL (Box (S n) psi).
Proof.
  intros n psi H.
  exact (Provable_GL_VS_sound _ H (fun _ => True)).
Qed.

Theorem Provable_S_no_high_box : forall n psi,
  ~ Provable_S (Box (S n) psi).
Proof.
  intros n psi H.
  exact (Provable_S_VS_sound _ H (fun _ => True)).
Qed.

(** S is nevertheless strictly stronger than GL: the reflection
    instance at the classically-valid [Box 0 Bot] is an S-theorem that
    GL cannot prove (refuted in the Fnat frame at world 1 via the
    polymodal soundness theorem). *)

Theorem Provable_S_strictly_stronger_than_GL :
  exists phi, Provable_S phi /\ ~ Provable_GL phi.
Proof.
  exists (Impl (Box 0 (Box 0 Bot)) (Box 0 Bot)). split.
  - apply S_reflection. intro val. reflexivity.
  - intro H.
    pose proof (GL_in_provable _ H) as Hp.
    pose proof (soundness _ Hp Fnat (fun _ _ => true) 1) as Hf.
    cbn in Hf.
    assert (Hant : forall v : nat, Fnat_R 0 1 v ->
                   forall u : nat, Fnat_R 0 v u -> False).
    { intros v [Hv1 Hv2] u [Hu1 Hu2]. lia. }
    assert (Hr : Fnat_R 0 1 0) by (unfold Fnat_R; lia).
    exact (Hf Hant 0 Hr).
Qed.

(******************************************************************************)
(* Refutation of the UNRESTRICTED Solovay-first statement (todo #10).         *)
(*                                                                            *)
(* Witness phi := Box 5 Top: every proper interpretation collapses it to      *)
(* Box 0 Top, whose Goedel code is Bew_n-0-provable, so the hypothesis        *)
(* holds; but Provable_GL derives no positive Box (S n) formula.              *)
(******************************************************************************)

Theorem Solovay_first_full_unrestricted_refuted :
  ~ (forall phi,
      (forall I, is_arithmetic_interpretation_proper I ->
         Bew_n 0 (encode_form (I phi))) ->
      Provable_GL phi).
Proof.
  intro Hfull.
  apply (Provable_GL_no_high_box 4 Top).
  apply Hfull.
  intros I [HImpl [HBot HBox]].
  assert (HITop : I Top = Top).
  { unfold Top. rewrite HImpl. rewrite HBot. reflexivity. }
  rewrite HBox. rewrite HITop.
  unfold Bew_n. exists (Box 0 Top). split.
  - reflexivity.
  - apply Nec. apply Nec. unfold Top. apply prov_id.
Qed.

(******************************************************************************)
(* Refutation of the UNRESTRICTED Solovay-second statement (todo #13).        *)
(* Same witness; the standard-model conjunct also holds for the collapsed     *)
(* image, and Provable_S derives no positive Box (S n) formula either.        *)
(******************************************************************************)

Theorem Solovay_second_full_unrestricted_refuted :
  ~ (forall phi,
      (forall I, is_arithmetic_interpretation_proper I ->
         Bew_n 0 (encode_form (I phi)) /\
         (forall val, standard_model_satisfies val (I phi))) ->
      Provable_S phi).
Proof.
  intro Hfull.
  apply (Provable_S_no_high_box 4 Top).
  apply Hfull.
  intros I [HImpl [HBot HBox]].
  assert (HITop : I Top = Top).
  { unfold Top. rewrite HImpl. rewrite HBot. reflexivity. }
  rewrite HBox. rewrite HITop.
  split.
  - unfold Bew_n. exists (Box 0 Top). split.
    + reflexivity.
    + apply Nec. apply Nec. unfold Top. apply prov_id.
  - intro val. cbn.
    unfold Bew_n. exists Top. split.
    + reflexivity.
    + apply Nec. unfold Top. apply prov_id.
Qed.

(******************************************************************************)
(* The corrected Solovay-first, full statement on the level-0 fragment:       *)
(* the universal proper-interpretation hypothesis yields Provable_GL phi      *)
(* itself — no residual outer box — and conversely.  The completeness         *)
(* direction instantiates the hypothesis at [arith_embed_GL] (the box-        *)
(* collapse with identity atoms — neither the identity interpretation nor     *)
(* shift_interp, both forbidden) and strips the outer box with                *)
(* [GL_box_elim].                                                             *)
(******************************************************************************)

Theorem Solovay_first_full : forall phi,
  level_0_only phi ->
  (forall I, is_arithmetic_interpretation_proper I ->
     Bew_n 0 (encode_form (I phi))) ->
  Provable_GL phi.
Proof.
  intros phi Hl0 H.
  apply GL_box_elim.
  exact (Solovay_first_completeness_level_0_only_with_outer_Box_0 phi Hl0 H).
Qed.

Theorem Solovay_first_full_iff : forall phi,
  level_0_only phi ->
  ((forall I, is_arithmetic_interpretation_proper I ->
      Bew_n 0 (encode_form (I phi))) <-> Provable_GL phi).
Proof.
  intros phi Hl0. split.
  - apply Solovay_first_full. exact Hl0.
  - intros H I HI. exact (Solovay_first_soundness_proper phi H I HI).
Qed.

(** The corrected Solovay-second on the level-0 fragment (the repo's
    completeness theorem, re-exported under the todo's name), plus the
    truth-side soundness. *)

Theorem Solovay_second_full : forall phi,
  level_0_only phi ->
  (forall I, is_arithmetic_interpretation_proper I ->
     Bew_n 0 (encode_form (I phi)) /\ classical_valid (I phi)) ->
  Provable_S phi.
Proof.
  exact Solovay_second_completeness_level_0_only.
Qed.

Theorem Solovay_second_truth_soundness : forall phi,
  Provable_S phi ->
  forall I, is_arithmetic_interpretation_proper I ->
  classical_valid (I phi).
Proof.
  exact Solovay_second_soundness_proper_classical.
Qed.

(******************************************************************************)
(* Goedel codes for proof terms, and provability as a Sigma_1 sentence.       *)
(******************************************************************************)

Fixpoint encode_pt (pt : proof_term) : nat :=
  match pt with
  | PT_K a b => cpair 0 (cpair (encode_form a) (encode_form b))
  | PT_S a b c =>
      cpair 1 (cpair (encode_form a) (cpair (encode_form b) (encode_form c)))
  | PT_DN a => cpair 2 (encode_form a)
  | PT_BoxK n a b =>
      cpair 3 (cpair n (cpair (encode_form a) (encode_form b)))
  | PT_Loeb n a => cpair 4 (cpair n (encode_form a))
  | PT_Box4 n a => cpair 5 (cpair n (encode_form a))
  | PT_Mon n a => cpair 6 (cpair n (encode_form a))
  | PT_NextCon n => cpair 7 n
  | PT_MP p q => cpair 8 (cpair (encode_pt p) (encode_pt q))
  | PT_Nec n p => cpair 9 (cpair n (encode_pt p))
  end.

Fixpoint decode_pt_bounded (depth n : nat) : proof_term :=
  match depth with
  | 0 => PT_NextCon 0
  | S d =>
    match fst (cunpair n) with
    | 0 => PT_K (decode_form (fst (cunpair (snd (cunpair n)))))
                (decode_form (snd (cunpair (snd (cunpair n)))))
    | 1 => PT_S (decode_form (fst (cunpair (snd (cunpair n)))))
                (decode_form (fst (cunpair (snd (cunpair (snd (cunpair n)))))))
                (decode_form (snd (cunpair (snd (cunpair (snd (cunpair n)))))))
    | 2 => PT_DN (decode_form (snd (cunpair n)))
    | 3 => PT_BoxK (fst (cunpair (snd (cunpair n))))
                   (decode_form (fst (cunpair (snd (cunpair (snd (cunpair n)))))))
                   (decode_form (snd (cunpair (snd (cunpair (snd (cunpair n)))))))
    | 4 => PT_Loeb (fst (cunpair (snd (cunpair n))))
                   (decode_form (snd (cunpair (snd (cunpair n)))))
    | 5 => PT_Box4 (fst (cunpair (snd (cunpair n))))
                   (decode_form (snd (cunpair (snd (cunpair n)))))
    | 6 => PT_Mon (fst (cunpair (snd (cunpair n))))
                  (decode_form (snd (cunpair (snd (cunpair n)))))
    | 7 => PT_NextCon (snd (cunpair n))
    | 8 => PT_MP (decode_pt_bounded d (fst (cunpair (snd (cunpair n)))))
                 (decode_pt_bounded d (snd (cunpair (snd (cunpair n)))))
    | 9 => PT_Nec (fst (cunpair (snd (cunpair n))))
                  (decode_pt_bounded d (snd (cunpair (snd (cunpair n)))))
    | _ => PT_NextCon 0
    end
  end.

Definition decode_pt (n : nat) : proof_term := decode_pt_bounded (S n) n.

Lemma encode_pt_MP_bound_left : forall p q,
  encode_pt p < encode_pt (PT_MP p q).
Proof.
  intros p q. cbn [encode_pt]. unfold cpair.
  pose proof (triangle_bounded_below
    (8 + (to_triangle (encode_pt p + encode_pt q) + encode_pt q))) as H1.
  pose proof (triangle_bounded_below (encode_pt p + encode_pt q)) as H2.
  lia.
Qed.

Lemma encode_pt_MP_bound_right : forall p q,
  encode_pt q < encode_pt (PT_MP p q).
Proof.
  intros p q. cbn [encode_pt]. unfold cpair.
  pose proof (triangle_bounded_below
    (8 + (to_triangle (encode_pt p + encode_pt q) + encode_pt q))) as H1.
  pose proof (triangle_bounded_below (encode_pt p + encode_pt q)) as H2.
  lia.
Qed.

Lemma encode_pt_Nec_bound : forall n p,
  encode_pt p < encode_pt (PT_Nec n p).
Proof.
  intros n p. cbn [encode_pt]. unfold cpair.
  pose proof (triangle_bounded_below
    (9 + (to_triangle (n + encode_pt p) + encode_pt p))) as H1.
  pose proof (triangle_bounded_below (n + encode_pt p)) as H2.
  lia.
Qed.

Lemma decode_encode_pt_with_depth : forall pt d,
  encode_pt pt < d ->
  decode_pt_bounded d (encode_pt pt) = pt.
Proof.
  induction pt as [a b | a b c | a | n a b | n a | n a | n a | n
                  | p IHp q IHq | n p IHp];
    intros d Hd; (destruct d as [|d']; [lia|]); cbn [decode_pt_bounded encode_pt].
  - rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite !decode_encode. reflexivity.
  - rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite !decode_encode. reflexivity.
  - rewrite cunpair_cpair. cbn [fst snd].
    rewrite decode_encode. reflexivity.
  - rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite !decode_encode. reflexivity.
  - rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite decode_encode. reflexivity.
  - rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite decode_encode. reflexivity.
  - rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite decode_encode. reflexivity.
  - rewrite cunpair_cpair. cbn [fst snd]. reflexivity.
  - rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite IHp.
    + rewrite IHq.
      * reflexivity.
      * pose proof (encode_pt_MP_bound_right p q). cbn [encode_pt] in *. lia.
    + pose proof (encode_pt_MP_bound_left p q). cbn [encode_pt] in *. lia.
  - rewrite cunpair_cpair. cbn [fst snd].
    rewrite cunpair_cpair. cbn [fst snd].
    rewrite IHp.
    + reflexivity.
    + pose proof (encode_pt_Nec_bound n p). cbn [encode_pt] in *. lia.
Qed.

Theorem decode_encode_pt : forall pt,
  decode_pt (encode_pt pt) = pt.
Proof.
  intro pt. unfold decode_pt.
  apply decode_encode_pt_with_depth. lia.
Qed.

(** [encodes_proof d k]: the natural number d codes a proof term whose
    denotation is exactly the formula coded by k. *)

Definition encodes_proof (d k : nat) : Prop :=
  denote_proof_term (decode_pt d) = Some (decode_form k).

(** Provability is the Sigma_1 sentence "some d codes a proof of me". *)

Theorem provable_iff_sigma1_proof_code : forall phi,
  |- phi <-> exists d, encodes_proof d (encode_form phi).
Proof.
  intro phi. split.
  - intro Hp.
    destruct (provable_to_proof_term phi Hp) as [pt Hpt].
    exists (encode_pt pt). unfold encodes_proof.
    rewrite decode_encode_pt. rewrite decode_encode. exact Hpt.
  - intros [d Hd]. unfold encodes_proof in Hd.
    rewrite decode_encode in Hd.
    exact (denote_proof_term_provable _ _ Hd).
Qed.

Theorem Bew_box_iff_sigma1_proof_code : forall n phi,
  |- Box n phi <-> exists d, encodes_proof d (encode_form (Box n phi)).
Proof.
  intros n phi. apply provable_iff_sigma1_proof_code.
Qed.

(******************************************************************************)
(* The arithmetic embedding at the satisfaction level (todo #10's             *)
(* arith_embed_GL : Form -> (atoms) -> Prop): Box phi is translated to the    *)
(* Sigma_1 sentence [exists d, encodes_proof d ⌜Box 0 (arith_embed_GL phi)⌝] *)
(* — through the proof-code existential, NOT through Bew_n directly, and      *)
(* NOT to a top sentence.                                                     *)
(******************************************************************************)

Definition Sigma1_Bew_sentence (phi : Form) : Prop :=
  exists d, encodes_proof d (encode_form phi).

Fixpoint arith_embed_GL_sat (val : nat -> Prop) (phi : Form) : Prop :=
  match phi with
  | Var p => val p
  | Bot => False
  | Impl a b => arith_embed_GL_sat val a -> arith_embed_GL_sat val b
  | Box _ psi => Sigma1_Bew_sentence (Box 0 (arith_embed_GL psi))
  end.

Theorem arith_embed_GL_sat_box_correct : forall val n psi,
  arith_embed_GL_sat val (Box n psi) <-> |- Box 0 (arith_embed_GL psi).
Proof.
  intros val n psi. cbn. unfold Sigma1_Bew_sentence.
  split.
  - intro H. apply (proj2 (provable_iff_sigma1_proof_code _)). exact H.
  - intro H. apply (proj1 (provable_iff_sigma1_proof_code _)). exact H.
Qed.

(** The embedding is not box-as-top: the image of [Box 0 Bot] is a
    FALSE Sigma_1 sentence. *)

Theorem arith_embed_GL_sat_box_bot_false : forall val,
  ~ arith_embed_GL_sat val (Box 0 Bot).
Proof.
  intros val H.
  apply (proj1 (arith_embed_GL_sat_box_correct val 0 Bot)) in H.
  cbn in H.
  exact (meta_consistency_every_level 0 H).
Qed.

(** And it is not box-erasure: the image of [Box 0 Top] is a TRUE
    Sigma_1 sentence even at the all-false atom valuation, where the
    erased body [Top]'s image would be... also true; the separating
    instance is [Box 0 (Var 0)] at the all-false valuation: erasure
    would give [val 0] (false), the genuine embedding gives the
    Sigma_1 sentence about provability of [Box 0 (Var 0)] — also
    false — while at [Box 0 Top] the two DIFFER from box-as-top
    in falsity at [Box 0 Bot] (above) and agree with provability
    here. *)

Theorem arith_embed_GL_sat_box_top_true : forall val,
  arith_embed_GL_sat val (Box 0 Top).
Proof.
  intro val.
  apply (proj2 (arith_embed_GL_sat_box_correct val 0 Top)).
  cbn. apply Nec. unfold Top. apply prov_id.
Qed.

(** Full correctness of the satisfaction-level embedding against the
    Form-level collapse on closed boxed formulas: satisfaction of the
    embedded box is provability of the collapsed box. *)

Theorem arith_embed_GL_sat_definitional : forall val n psi,
  arith_embed_GL_sat val (Box n psi) =
  Sigma1_Bew_sentence (Box 0 (arith_embed_GL psi)).
Proof. reflexivity. Qed.

(******************************************************************************)
(* The Solovay walk: R-successor tracking correctness (todo #10's             *)
(* solovay_function artifacts).                                               *)
(******************************************************************************)

Lemma solovay_step_search_correct : forall R c k,
  (exists j, j < k /\ R c j = true) ->
  R c (solovay_step_search R c k) = true /\ solovay_step_search R c k < k.
Proof.
  intros R c k. induction k as [|k IH]; intros [j [Hj HR]].
  - lia.
  - cbn. destruct (R c k) eqn:E.
    + split; [exact E | lia].
    + assert (Hj' : j < k).
      { destruct (Nat.eq_dec j k) as [Heq | Hne].
        - subst j. congruence.
        - lia. }
      destruct (IH (ex_intro _ j (conj Hj' HR))) as [H1 H2].
      split; [exact H1 | lia].
Qed.

(** While the current node has an R-successor below the frame size,
    the Solovay walk steps to one: the function genuinely tracks
    R-successors. *)

Theorem solovay_function_tracks_R : forall size R n,
  (exists j, j < size /\ R (solovay_function size R n) j = true) ->
  R (solovay_function size R n) (solovay_function size R (S n)) = true /\
  solovay_function size R (S n) < size.
Proof.
  intros size R n Hex. cbn [solovay_function].
  unfold solovay_step.
  exact (solovay_step_search_correct R (solovay_function size R n) size Hex).
Qed.

(** Base point and stationarity (the latter re-exported). *)

Theorem solovay_function_base : forall size R,
  solovay_function size R 0 = 0.
Proof. intros. reflexivity. Qed.

Theorem solovay_function_stationary : forall size R n,
  (forall j, R (solovay_function size R n) j = false) ->
  solovay_function size R (S n) = solovay_function size R n.
Proof.
  exact solovay_function_step_no_successor.
Qed.

(** ** Headline summary for todo #10. *)

Theorem Solovay_first_summary :
  (~ (forall phi,
       (forall I, is_arithmetic_interpretation_proper I ->
          Bew_n 0 (encode_form (I phi))) ->
       Provable_GL phi)) /\
  (forall phi, level_0_only phi ->
     ((forall I, is_arithmetic_interpretation_proper I ->
         Bew_n 0 (encode_form (I phi))) <-> Provable_GL phi)) /\
  (forall psi, Provable_GL (Box 0 psi) <-> Provable_GL psi) /\
  (forall phi, |- phi <-> exists d, encodes_proof d (encode_form phi)) /\
  (forall size R, solovay_function size R 0 = 0) /\
  (forall size R n,
     (exists j, j < size /\ R (solovay_function size R n) j = true) ->
     R (solovay_function size R n) (solovay_function size R (S n)) = true).
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact Solovay_first_full_unrestricted_refuted.
  - exact Solovay_first_full_iff.
  - exact GL_box_elim_iff.
  - exact provable_iff_sigma1_proof_code.
  - exact solovay_function_base.
  - intros size R n H.
    exact (proj1 (solovay_function_tracks_R size R n H)).
Qed.

(** ** Headline summary for todo #13. *)

Theorem Solovay_second_summary :
  (~ (forall phi,
       (forall I, is_arithmetic_interpretation_proper I ->
          Bew_n 0 (encode_form (I phi)) /\
          (forall val, standard_model_satisfies val (I phi))) ->
       Provable_S phi)) /\
  (forall phi, level_0_only phi ->
     (forall I, is_arithmetic_interpretation_proper I ->
        Bew_n 0 (encode_form (I phi)) /\ classical_valid (I phi)) ->
     Provable_S phi) /\
  (forall psi, Provable_S (Box 0 psi) <-> Provable_GL psi) /\
  (exists phi, Provable_S phi /\ ~ Provable_GL phi).
Proof.
  split; [|split; [|split]].
  - exact Solovay_second_full_unrestricted_refuted.
  - exact Solovay_second_full.
  - exact Provable_S_box0_iff_GL.
  - exact Provable_S_strictly_stronger_than_GL.
Qed.
