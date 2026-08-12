(******************************************************************************)
(*                                                                            *)
(*           Parametric Provability: Bypassing the Loebian Obstacle           *)
(*                                                                            *)
(*     Part 5 of 5. Decision procedures, algebra, duality, term rewriting.    *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Arith.Factorial.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Logic.Classical.
From Stdlib Require Import Logic.ClassicalEpsilon.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics Completeness.

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

(** ** The free polymodal Magari algebra.

    [polymodal_Magari_algebra] is a setoid-carried Boolean implication
    algebra with a box family validating K, Loeb, Box4, Mon, NextCon at
    every index.  [LT_GLP] is the Lindenbaum-Tarski instance (carrier
    Form, equality provable-iff); [pma_hom A val] interprets a valuation;
    [LT_GLP_free] gives the extending morphism and its uniqueness up to
    algebra-equality.  [PMA_bool] instantiates freeness at the
    two-element algebra. *)

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

Fixpoint pma_hom (A : polymodal_Magari_algebra)
  (val : nat -> pma_carrier A) (phi : Form) : pma_carrier A :=
  match phi with
  | Var p => val p
  | Bot => pma_bot
  | Impl a b => pma_impl (pma_hom A val a) (pma_hom A val b)
  | Box n a => pma_box n (pma_hom A val a)
  end.

(** Every GLP*-theorem maps to top in any polymodal Magari algebra,
    under any valuation. *)

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

Lemma pma_hom_respects : forall (A : polymodal_Magari_algebra) val phi psi,
  |- Iff phi psi ->
  pma_eq (pma_hom A val phi) (pma_hom A val psi).
Proof.
  intros A val phi psi Hiff.
  apply pma_iff_eq.
  - exact (pma_hom_theorem A val _ (prov_and_elim_l_meta _ _ Hiff)).
  - exact (pma_hom_theorem A val _ (prov_and_elim_r_meta _ _ Hiff)).
Qed.

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

Definition LT_class (phi : Form) : pma_carrier LT_GLP := phi.

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

Definition LT_free_hom (A : polymodal_Magari_algebra)
  (val : nat -> pma_carrier A) : LT_GLP_morphism A.
Proof.
  refine (mkPMAm LT_GLP A (pma_hom A val) _ _ _ _).
  - intros a a' Hiff. exact (pma_hom_respects A val a a' Hiff).
  - exact (pma_eq_refl _).
  - intros a b. exact (pma_eq_refl _).
  - intros n a. exact (pma_eq_refl _).
Defined.

(** Uniqueness by structural induction on the carrier element, using the
    morphism laws and the congruences. *)

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

(** The two-element Boolean algebra with trivial boxes, a polymodal
    Magari algebra different from LT_GLP at which freeness instantiates. *)

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

Theorem categorical_semantics_with_morphism_soundness :
  (forall F1 F2 V1 V2 (f : FrameMorphism F1 F2),
     (forall w p, V1 w p = V2 (fmm_map f w) p) ->
     Bisim F1 F2 V1 V2 (fun w v => fmm_map f w = v)) /\
  (forall phi, |- phi -> GlobalSection phi) /\
  (forall F1 F2 V1 V2 (f : FrameMorphism F1 F2),
     (forall w p, V1 w p = V2 (fmm_map f w) p) ->
     forall phi w, forces F1 V1 w phi <-> forces F2 V2 (fmm_map f w) phi) /\
  (forall F1 F2 V1 V2 (f : FrameMorphism F1 F2),
     (forall w p, V1 w p = V2 (fmm_map f w) p) ->
     forall phi, (|- phi -> forall w, forces F1 V1 w phi) /\
                 (|- phi -> forall w, forces F2 V2 (fmm_map f w) phi)).
Proof.
  split; [|split; [|split]].
  - exact frame_morphism_induces_bisim.
  - exact provable_is_global_section.
  - exact frame_morphism_pulls_back_truth.
  - intros F1 F2 V1 V2 f Hcompat phi.
    pose proof (frame_morphism_pulls_back_truth F1 F2 V1 V2 f Hcompat phi) as Hpb.
    split.
    + intros Hp w. exact (soundness phi Hp F1 V1 w).
    + intros Hp w. exact (soundness phi Hp F2 V2 (fmm_map f w)).
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
  | V_phi  : nat -> ord -> vord
  | V_gamma0 : vord.

(** Normal-form predicate: in [V_phi n α], the [ord] argument α must be
    in CNF, i.e. [wf_ord α].  [V_cnf o] requires [wf_ord o].  The
    [V_gamma0] atom — the Feferman-Schütte point Γ_0, i.e. the first
    common fixed point of the whole φ-tower, sitting strictly above
    every [V_phi n α] — is always well-formed. *)

Definition wf_vord (v : vord) : Prop :=
  match v with
  | V_cnf o   => wf_ord o
  | V_phi _ α => wf_ord α
  | V_gamma0  => True
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
      ord_lt α1 α2 -> vord_lt (V_phi n α1) (V_phi n α2)
  | VL_cnf_g0    : forall o, vord_lt (V_cnf o) V_gamma0
  | VL_phi_g0    : forall n α, vord_lt (V_phi n α) V_gamma0.

Lemma vord_lt_V_cnf_inv : forall v o,
  vord_lt v (V_cnf o) -> exists o', v = V_cnf o' /\ ord_lt o' o.
Proof.
  intros v o H.
  remember (V_cnf o) as u eqn:Eu.
  destruct H as [o1 o2 Hlt | o' n α | n1 n2 α1 α2 Hlt | n α1 α2 Hlt | o' | n α].
  - injection Eu as Hu. subst o2.
    exists o1. split; [reflexivity | exact Hlt].
  - discriminate.
  - discriminate.
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
  destruct H as [o1 o2 Hlt | o' nn αα | n1 n2 α1 α2 Hlt | nn α1 α2 Hlt | o' | nn αα].
  - discriminate.
  - injection Eu as En Eα. subst nn αα.
    left. exists o'. reflexivity.
  - injection Eu as En Eα. subst n2 α2.
    right. left. exists n1, α1. split; [reflexivity | exact Hlt].
  - injection Eu as En Eα. subst nn α2.
    right. right. exists α1. split; [reflexivity | exact Hlt].
  - discriminate.
  - discriminate.
Qed.

(** Inversion at the [V_gamma0] top atom: its strict predecessors are
    exactly the [V_cnf] and [V_phi] atoms. *)

Lemma vord_lt_V_gamma0_inv : forall v,
  vord_lt v V_gamma0 ->
  (exists o, v = V_cnf o) \/ (exists n α, v = V_phi n α).
Proof.
  intros v H.
  remember V_gamma0 as u eqn:Eu.
  destruct H as [o1 o2 Hlt | o' nn αα | n1 n2 α1 α2 Hlt | nn α1 α2 Hlt | o' | nn αα].
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - left. exists o'. reflexivity.
  - right. exists nn, αα. reflexivity.
Qed.

(** Nothing lies strictly above [V_gamma0] within the carrier; in
    particular [V_gamma0] is not below itself. *)

Lemma vord_lt_from_V_gamma0_absurd : forall v,
  ~ vord_lt V_gamma0 v.
Proof.
  intros v H.
  remember V_gamma0 as u eqn:Eu.
  destruct H as [o1 o2 Hlt | o' nn αα | n1 n2 α1 α2 Hlt | nn α1 α2 Hlt | o' | nn αα];
    discriminate.
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

(** Accessibility of the top atom: every [vord_wf_lt]-predecessor of
    [V_gamma0] is a well-formed [V_cnf] or [V_phi] atom, each already
    accessible by the two lemmas above. *)

Lemma Acc_vord_V_gamma0 : Acc vord_wf_lt V_gamma0.
Proof.
  apply Acc_intro. intros y [Hwfy [_ Hlt]].
  destruct (vord_lt_V_gamma0_inv _ Hlt) as [[o E] | [n [α E]]]; subst y.
  - apply Acc_vord_V_cnf_wf. exact Hwfy.
  - apply Acc_vord_V_phi_wf. exact Hwfy.
Qed.

Theorem vord_wf_lt_well_founded : well_founded vord_wf_lt.
Proof.
  intro v. apply Acc_intro. intros y [Hwfy [Hwfv Hlt]].
  destruct v as [o | n α |].
  - apply (Acc_inv (Acc_vord_V_cnf_wf o Hwfv)).
    split; [exact Hwfy | split; [exact Hwfv | exact Hlt]].
  - apply (Acc_inv (Acc_vord_V_phi_wf n α Hwfv)).
    split; [exact Hwfy | split; [exact Hwfv | exact Hlt]].
  - apply (Acc_inv Acc_vord_V_gamma0).
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

Theorem worm_normalisation_strict_decrease_vord : forall w,
  w <> normalise_worm w ->
  vord_lt (V_cnf (worm_to_ord (normalise_worm w))) (V_cnf (worm_to_ord w)).
Proof.
  intros w Hne. apply VL_cnf.
  unfold ord_lt. exact (worm_normalisation_strict_decrease w Hne).
Qed.

Theorem worm_normalisation_complete : forall w,
  (vord_lt (V_cnf (worm_to_ord (normalise_worm w))) (V_cnf (worm_to_ord w)) \/
   normalise_worm w = w) /\
  is_sorted_asc (normalise_worm w) /\
  normalise_worm (normalise_worm w) = normalise_worm w.
Proof.
  intro w. split; [|split].
  - destruct (list_eq_dec Nat.eq_dec w (normalise_worm w)) as [Heq | Hne].
    + right. exact (eq_sym Heq).
    + left. exact (worm_normalisation_strict_decrease_vord w Hne).
  - exact (normalise_worm_sorted w).
  - exact (normalise_worm_idempotent w).
Qed.

(** ** Beklemishev worm reduction (todo item 1).

    The Beklemishev step splits a worm at the head and recursively
    reduces the tail.  When the reduced tail is non-empty, the head is
    re-prepended unchanged ([bek_step a (b :: rest) := a :: b :: rest]).
    When the reduced tail is empty, the head is decremented by one
    (giving [[a-1]] when [a > 0], or [[]] when [a = 0]).  This is
    genuinely different from [normalise_worm] (which sorts via
    insertion); the recursion structure here is "split at the head,
    recurse on the tail, head-substitute on the result".  Each call
    strictly decreases [worm_to_ord]. *)

Definition bek_step (a : nat) (rest : Worm) : Worm :=
  match rest with
  | [] =>
      match a with
      | 0 => []
      | S k => k :: nil
      end
  | _ => a :: rest
  end.

Fixpoint beklemishev_reduce (w : Worm) : Worm :=
  match w with
  | [] => []
  | a :: rest => bek_step a (beklemishev_reduce rest)
  end.

Fixpoint iterate {A : Type} (f : A -> A) (n : nat) (x : A) : A :=
  match n with
  | 0 => x
  | S n' => f (iterate f n' x)
  end.

(** Forbidden-shortcut sanity check: the reduction is NOT
    [normalise_worm] and NOT the immediate-empty constant. *)

Example beklemishev_reduce_not_normalise :
  beklemishev_reduce (1 :: 2 :: nil) <> normalise_worm (1 :: 2 :: nil).
Proof. cbn. discriminate. Qed.

Example beklemishev_reduce_nontrivial :
  beklemishev_reduce (3 :: 2 :: 1 :: nil) = 3 :: 2 :: 0 :: nil.
Proof. reflexivity. Qed.

Example beklemishev_reduce_pop_zero_tail :
  beklemishev_reduce (5 :: 0 :: nil) = 4 :: nil.
Proof. reflexivity. Qed.

(** Helper: [nat_to_ord] is strictly increasing in [ord_lt]. *)

Lemma nat_to_ord_lt : forall a b, a < b ->
  ord_lt (nat_to_ord a) (nat_to_ord b).
Proof. exact nat_to_ord_strict_lt. Qed.

(** [bek_step] applied to an empty tail strictly decreases the
    [worm_to_ord] image of the singleton [a :: nil]. *)

Lemma bek_step_empty_decreases : forall a,
  ord_lt (worm_to_ord (bek_step a nil)) (worm_to_ord (a :: nil)).
Proof.
  intro a. destruct a as [|k].
  - cbn [bek_step worm_to_ord]. unfold ord_lt. cbn. reflexivity.
  - cbn [bek_step worm_to_ord].
    apply ord_compare_OCons_first_lt.
    apply nat_to_ord_strict_lt. lia.
Qed.

(** [bek_step] applied to a non-empty reduced tail [r'] (where [r' < r]
    in [ord_lt]) preserves the strict-decrease via the head. *)

Lemma bek_step_nonempty_decreases : forall a rest r',
  rest <> [] ->
  r' <> [] ->
  ord_lt (worm_to_ord r') (worm_to_ord rest) ->
  ord_lt (worm_to_ord (bek_step a r')) (worm_to_ord (a :: rest)).
Proof.
  intros a rest r' Hrest Hr' Hlt.
  destruct r' as [|b r'']; [contradiction|].
  cbn [bek_step worm_to_ord].
  unfold ord_lt. cbn [ord_compare].
  rewrite ord_compare_refl. exact Hlt.
Qed.

(** When the reduced tail collapses to [], decrementing/popping the head
    still produces a strictly smaller worm (relative to the original
    [a :: rest]). *)

Lemma bek_step_collapse_decreases : forall a rest,
  rest <> [] ->
  ord_lt (worm_to_ord (bek_step a nil)) (worm_to_ord (a :: rest)).
Proof.
  intros a rest Hrest.
  cbn [bek_step].
  destruct a as [|k].
  - cbn [worm_to_ord]. unfold ord_lt. cbn. reflexivity.
  - cbn [worm_to_ord].
    apply ord_compare_OCons_first_lt.
    apply nat_to_ord_strict_lt. lia.
Qed.

(** Main strict-descent theorem: every Beklemishev step strictly
    decreases [worm_to_ord] in [ord_lt]. *)

Theorem beklemishev_reduce_strictly_decreases : forall w,
  w <> [] ->
  ord_lt (worm_to_ord (beklemishev_reduce w)) (worm_to_ord w).
Proof.
  intro w. induction w as [|a rest IH]; intro Hne.
  - exfalso. apply Hne. reflexivity.
  - cbn [beklemishev_reduce].
    destruct rest as [|b rest'].
    + apply bek_step_empty_decreases.
    + assert (Hrest_ne : (b :: rest') <> []) by discriminate.
      pose proof (IH Hrest_ne) as IHrest.
      destruct (beklemishev_reduce (b :: rest')) as [|c r''] eqn:Ered.
      * apply bek_step_collapse_decreases. exact Hrest_ne.
      * apply bek_step_nonempty_decreases.
        -- exact Hrest_ne.
        -- discriminate.
        -- exact IHrest.
Qed.

(** Termination: a single application of [beklemishev_reduce] strictly
    decreases the natural-number measure [length w + sum of w].  This
    is a coarser termination measure than the ord-descent above, but
    is easy to formalize and gives finite-step termination. *)

Fixpoint worm_size (w : Worm) : nat :=
  match w with
  | [] => 0
  | a :: rest => S (a + worm_size rest)
  end.

Lemma worm_size_zero_iff : forall w, worm_size w = 0 <-> w = [].
Proof.
  intro w. destruct w; cbn; split; intros H; congruence.
Qed.

Theorem beklemishev_reduce_size_decreases : forall w,
  w <> [] ->
  worm_size (beklemishev_reduce w) < worm_size w.
Proof.
  intro w. induction w as [|a rest IH]; intro Hne.
  - exfalso. apply Hne. reflexivity.
  - cbn [beklemishev_reduce].
    destruct rest as [|b rest'].
    + cbn [beklemishev_reduce].
      destruct a as [|k]; cbn [bek_step worm_size]; lia.
    + assert (Hrne : (b :: rest') <> []) by discriminate.
      pose proof (IH Hrne) as Hsz.
      destruct (beklemishev_reduce (b :: rest')) as [|c r''] eqn:Ered.
      * destruct a as [|k]; cbn [bek_step worm_size]; cbn [worm_size] in Hsz; lia.
      * cbn [bek_step worm_size]. cbn [worm_size] in Hsz. lia.
Qed.

(** [iterate] commutes via [f] in the standard way. *)

Lemma iterate_S_shift : forall {A : Type} (f : A -> A) n x,
  iterate f (S n) x = iterate f n (f x).
Proof.
  intros A f n. induction n as [|n IH]; intro x.
  - reflexivity.
  - cbn [iterate]. f_equal. apply IH.
Qed.

(** Iteration eventually reaches []. *)

Theorem beklemishev_reduce_terminates : forall w,
  exists n, iterate beklemishev_reduce n w = [].
Proof.
  intro w.
  remember (worm_size w) as sz eqn:Hsz.
  revert w Hsz.
  induction sz as [sz IH] using (well_founded_induction lt_wf).
  intros w Hsz.
  destruct w as [|a rest].
  - exists 0. reflexivity.
  - assert (Hne : (a :: rest) <> []) by discriminate.
    pose proof (beklemishev_reduce_size_decreases (a :: rest) Hne) as Hdec.
    pose proof (IH (worm_size (beklemishev_reduce (a :: rest)))
                   ltac:(subst sz; exact Hdec)
                   (beklemishev_reduce (a :: rest)) eq_refl) as [n Hn].
    exists (S n). rewrite iterate_S_shift. exact Hn.
Qed.

(** Restated termination using the [V_cnf] embedding into [vord]: the
    ord-image of the final iterate is at or below [V_cnf OZero], which
    is the smallest [vord]. *)

Theorem beklemishev_reduce_terminates_at_eps0 : forall w,
  exists n, V_cnf (worm_to_ord (iterate beklemishev_reduce n w)) = V_cnf OZero.
Proof.
  intro w.
  destruct (beklemishev_reduce_terminates w) as [n Hn].
  exists n. rewrite Hn. reflexivity.
Qed.

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

Theorem T_n_ordinal_with_NextCon_Godel_pair :
  (forall n, vord_lt (T_n_ordinal n) (T_n_ordinal (S n))) /\
  (forall n m, n < m -> vord_lt (T_n_ordinal n) (T_n_ordinal m)) /\
  T_n_ordinal 0 = veps0 /\
  (forall n, |- Box (S n) (Neg (Box n Bot))) /\
  (forall n, ~ |- Box n (Neg (Box n Bot))) /\
  (forall n, |- Box (S n) (Neg (Box n Bot)) /\
             ~ |- Box n (Neg (Box n Bot))).
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact T_n_ordinal_strict.
  - exact T_n_ordinal_chain.
  - exact T_n_ordinal_zero.
  - exact Ax_NextCon.
  - exact Godel_sentence_independent_at_Tn.
  - intro n. split.
    + exact (Ax_NextCon n).
    + exact (Godel_sentence_independent_at_Tn n).
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

(** ** Stone duality as a category equivalence.

    [LT_category]: objects Form, homs derivations |- Impl a b.
    [canonical_frame_category]: objects [FrameObj] (definable upsets of
    [canonical_world_max] packaged with a defining formula), homs
    pointwise inclusions.  Functors [Stone_F]/[Stone_G] with natural
    isomorphisms [Stone_eta], [Stone_epsilon] and the triangle
    identities.  Full faithfulness ([Stone_full_faithful]) rests on the
    separation lemma [Stone_separation]: an unprovable [Impl a b] yields
    a maximal-consistent world containing a but excluding b. *)

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

(** E-categories: categories with hom-setoids. *)

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

(** Objects are formulas, homs are derivations of implications, parallel
    derivations identified (posetal hom-setoid). *)

Definition LT_category : ECat.
Proof.
  refine (mkECat Form
            (fun a b => |- Impl a b)
            (fun a b f g => True)
            (fun a => prov_id a)
            (fun a b c f g => prov_compose a b c f g)
            _ _ _ _ _ _ _); intros; exact I.
Defined.

(** Objects are definable upsets of the canonical maximal-consistent
    worlds (a set of worlds packaged with a defining formula), homs are
    pointwise inclusions. *)

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

(** G: a frame object goes to its defining witness; an inclusion goes to
    a derivation via the separation lemma. *)

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

(** eta : Id => G o F.  At a, G (F a) is definitionally a; the component
    is the derivation [prov_id a]. *)

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
    equivalence. *)

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

(** ** What the duality asserts.

    Both categories are posetal.  Their homs are the Prop-valued
    [|- Impl a b] and [fo_incl X Y], so parallel arrows carry no
    distinguishing data and the hom-setoid of each is the total
    relation; the naturality squares and the triangle identities above
    follow from that thinness.  The content of the equivalence is the
    package below: [Stone_G] inverts [Stone_F] on objects, [Stone_F]
    inverts [Stone_G] pointwise, the correspondence is full and faithful
    on the order (through [Stone_separation]), and every frame object is
    isomorphic to one in the image.

    A proof-relevant hom-setoid would need the categorical laws to hold
    up to a conversion on derivations.  [pt_reduces] supplies no such
    conversion: it has no S-contraction, so the identity and
    associativity laws fail on the combinator terms that realise
    [ec_id] and [ec_comp].  [pt_reduces_full] does contract S, but has
    no Church-Rosser theorem here, so joinability under it is not
    transitive and does not form a setoid. *)

Theorem Stone_categories_posetal :
  (forall (a b : Form) (f g : ec_hom LT_category a b),
     ec_hom_eq LT_category f g) /\
  (forall (X Y : FrameObj) (f g : ec_hom canonical_frame_category X Y),
     ec_hom_eq canonical_frame_category f g).
Proof. split; intros; exact I. Qed.

Theorem Stone_G_inverts_Stone_F_on_objects : forall a : Form,
  ef_obj Stone_G (ef_obj Stone_F a) = a.
Proof. intro a. reflexivity. Qed.

Theorem Stone_F_inverts_Stone_G_pointwise : forall (X : FrameObj) w,
  fo_set (ef_obj Stone_F (ef_obj Stone_G X)) w <-> fo_set X w.
Proof. intros X w. exact (iff_sym (fo_def X w)). Qed.

Theorem Stone_duality_posetal_equivalence :
  (forall a : Form, ef_obj Stone_G (ef_obj Stone_F a) = a) /\
  (forall (X : FrameObj) w,
     fo_set (ef_obj Stone_F (ef_obj Stone_G X)) w <-> fo_set X w) /\
  (forall a b : Form,
     (|- Impl a b) <-> fo_incl (Stone_F_obj a) (Stone_F_obj b)) /\
  (forall X : FrameObj, exists a : Form,
     inhabited (fo_incl (Stone_F_obj a) X) /\
     inhabited (fo_incl X (Stone_F_obj a))).
Proof.
  split; [|split; [|split]].
  - exact Stone_G_inverts_Stone_F_on_objects.
  - exact Stone_F_inverts_Stone_G_pointwise.
  - exact Stone_full_faithful.
  - exact Stone_essentially_surjective.
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

(** [Gamma_0_ordinal] is the genuine Feferman-Schütte atom [V_gamma0]:
    the point of the notation system sitting strictly above EVERY
    [V_phi n α] — i.e., above the whole stratified Veblen tower — and
    proved below ([Gamma_0_least_above_phi_tower]) to be the LEAST such
    point of the carrier.  It is NOT the ε_0 atom [veps0 = V_phi 0 OZero]
    (see [Gamma_0_not_eps0]) and NOT a CNF tree such as
    [Veblen_eps0_ordinal] (see [Gamma_0_not_cnf_shape]). *)

Definition Gamma_0_ordinal : vord := V_gamma0.

Definition omega_cnf : ord := OCons (OCons OZero OZero) OZero.

Fixpoint succ_cnf (o : ord) : ord :=
  match o with
  | OZero => OCons OZero OZero
  | OCons a t => OCons a (succ_cnf t)
  end.

Definition ord_max (o1 o2 : ord) : ord :=
  match ord_compare o1 o2 with
  | Lt => o2
  | _ => o1
  end.

Fixpoint ord_add (a b : ord) : ord :=
  match a with
  | OZero => b
  | OCons ae at_a =>
      match b with
      | OZero => OCons ae at_a
      | OCons be _ =>
          match ord_compare ae be with
          | Lt => b
          | _  => OCons ae (ord_add at_a b)
          end
      end
  end.

Definition omega_pow (e : ord) : ord := OCons e OZero.

Fixpoint proof_height_ord (phi : Form) (pt : Provable_term phi) : ord :=
  match pt with
  | pt_K _ _      => omega_cnf
  | pt_S _ _ _    => omega_cnf
  | pt_DN _       => omega_cnf
  | pt_BoxK _ _ _ => omega_cnf
  | pt_Loeb _ _   => omega_cnf
  | pt_Box4 _ _   => omega_cnf
  | pt_Mon _ _    => omega_cnf
  | pt_NextCon _  => omega_cnf
  | pt_MP _ _ p1 p2 => ord_add (proof_height_ord _ p1) (proof_height_ord _ p2)
  | pt_Nec _ _ p    => omega_pow (proof_height_ord _ p)
  end.

Definition proof_height (phi : Form) (pt : Provable_term phi) : vord :=
  V_cnf (proof_height_ord phi pt).

(* Every proof's height is a V_cnf-shaped vord, hence strictly below
   the Gamma_0 atom [V_gamma0]: VL_cnf_g0 places every CNF strictly
   below the Feferman-Schütte point.  This is the (#9) upper bound.
   The bound is genuine but NOT tight — see [Gamma_0_bound_not_tight]
   below: heights are already strictly below the ε_0 atom [veps0],
   which is itself strictly below [Gamma_0_ordinal]. *)
Theorem GLP_proof_height_below_Gamma_0 :
  forall phi (pt : Provable_term phi),
  vord_lt (proof_height phi pt) Gamma_0_ordinal.
Proof.
  intros phi pt.
  unfold proof_height, Gamma_0_ordinal.
  apply VL_cnf_g0.
Qed.

(* Concrete proof-term for Top := Impl Bot Bot, via the standard
   Hilbert id-derivation S(K(B->B->B))(K(B->B)). *)
Definition pt_id_Top : Provable_term Top :=
  pt_MP _ _
    (pt_MP _ _
       (pt_S Bot (Impl Bot Bot) Bot)
       (pt_K Bot (Impl Bot Bot)))
    (pt_K Bot Bot).

Lemma proof_height_id_Top_compute :
  proof_height_ord Top pt_id_Top
  = OCons (OCons OZero OZero) (OCons (OCons OZero OZero) (OCons (OCons OZero OZero) OZero)).
Proof. reflexivity. Qed.

Lemma proof_height_id_Top_gt_omega :
  ord_lt omega_cnf (proof_height_ord Top pt_id_Top).
Proof.
  rewrite proof_height_id_Top_compute.
  unfold ord_lt, omega_cnf. cbn. reflexivity.
Qed.

Fixpoint nat_witness_form (n : nat) : Form :=
  match n with
  | 0 => Top
  | S k => Box 0 (nat_witness_form k)
  end.

Fixpoint nat_witness_proof (n : nat) : Provable_term (nat_witness_form n) :=
  match n return Provable_term (nat_witness_form n) with
  | 0 => pt_id_Top
  | S k => pt_Nec 0 (nat_witness_form k) (nat_witness_proof k)
  end.

Definition vord_le (u v : vord) : Prop := u = v \/ vord_lt u v.

(* Every nat n is strictly below omega_cnf in ord (nat_to_ord n is
   the standard CNF embedding of finite ordinals). *)
Lemma nat_to_ord_lt_omega_cnf : forall n,
  ord_lt (nat_to_ord n) omega_cnf.
Proof.
  intro n. unfold ord_lt, omega_cnf.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - reflexivity.
Qed.

(* The proof-height of nat_witness_proof n always exceeds omega_cnf:
   the base case pt_id_Top uses pt_S and pt_K (each rank omega_cnf)
   plus two MPs (each succ_cnf), so the base height is succ_cnf
   (succ_cnf omega_cnf) = omega_cnf + 2.  Each Nec adds a succ_cnf.
   So the height grows with n, never falling below omega_cnf. *)
(* succ_cnf strictly increases ords (used for the original cure
   spec; kept available even though Nec now uses omega_pow). *)
Lemma succ_cnf_gt : forall o, ord_lt o (succ_cnf o).
Proof.
  intro o. unfold ord_lt. induction o as [|a IHa t IHt]; cbn.
  - reflexivity.
  - rewrite ord_compare_refl. exact IHt.
Qed.

(* omega_pow is strictly monotone in its argument. *)
Lemma omega_pow_monotone : forall a b,
  ord_lt a b -> ord_lt (omega_pow a) (omega_pow b).
Proof.
  intros a b H. unfold ord_lt, omega_pow in *.
  cbn. rewrite H. reflexivity.
Qed.

(* For e > OZero, omega_pow e is strictly above any e (since
   omega^e > e for e > 0).  In particular omega_pow OZero =
   OCons OZero OZero = 1 > OZero. *)
Lemma omega_pow_OZero_gt_OZero : ord_lt OZero (omega_pow OZero).
Proof. unfold ord_lt, omega_pow. cbn. reflexivity. Qed.


(* Any Provable_term with omega_pow as the outermost rank-step is
   bounded below by omega_cnf, since omega_pow X >= omega_cnf
   whenever X >= omega_cnf >= 1. *)
Lemma omega_pow_geq_omega_when_arg_geq_one : forall x,
  ord_lt OZero x ->
  ord_le omega_cnf (omega_pow x).
Proof.
  intros x Hx.
  unfold omega_pow, omega_cnf, ord_le.
  destruct x as [|xe xt].
  - unfold ord_lt in Hx. cbn in Hx. discriminate.
  - cbn.
    destruct xe as [|xee xet].
    + cbn. destruct xt as [|xte xtt]; cbn; congruence.
    + cbn. destruct xee as [|xeee xeet]; cbn; congruence.
Qed.

Lemma proof_height_nat_witness_geq_omega : forall n,
  ord_le omega_cnf (proof_height_ord (nat_witness_form n) (nat_witness_proof n)).
Proof.
  induction n as [|n IH].
  - unfold ord_le. cbn.
    unfold ord_add. cbn. congruence.
  - cbn.
    apply omega_pow_geq_omega_when_arg_geq_one.
    unfold ord_le in IH.
    destruct (proof_height_ord (nat_witness_form n) (nat_witness_proof n))
      as [|he ht] eqn:Heq.
    + exfalso. apply IH. cbn. reflexivity.
    + unfold ord_lt. cbn. reflexivity.
Qed.

Lemma ord_compare_eq_iff : forall a b,
  ord_compare a b = Eq <-> a = b.
Proof.
  induction a as [|ae IHae at_a IHat]; intros [|be bt]; cbn.
  - split; intro; reflexivity.
  - split; intro H; discriminate.
  - split; intro H; discriminate.
  - destruct (ord_compare ae be) eqn:Eae; split.
    + intro Ht. f_equal.
      * apply IHae. exact Eae.
      * apply IHat. exact Ht.
    + intro Heq. injection Heq as Hae Hat. subst.
      rewrite ord_compare_refl in Eae. discriminate Eae || idtac.
      apply IHat. reflexivity.
    + intro H. discriminate H.
    + intro Heq. injection Heq as Hae Hat. subst.
      rewrite ord_compare_refl in Eae. discriminate Eae.
    + intro H. discriminate H.
    + intro Heq. injection Heq as Hae Hat. subst.
      rewrite ord_compare_refl in Eae. discriminate Eae.
Qed.

Lemma proof_height_nat_witness_gt_nat : forall n,
  ord_lt (nat_to_ord n) (proof_height_ord (nat_witness_form n) (nat_witness_proof n)).
Proof.
  intro n.
  pose proof (nat_to_ord_lt_omega_cnf n) as H1.
  pose proof (proof_height_nat_witness_geq_omega n) as H2.
  unfold ord_le in H2.
  destruct (ord_compare omega_cnf (proof_height_ord (nat_witness_form n) (nat_witness_proof n)))
    eqn:Hcmp.
  - apply (proj1 (ord_compare_eq_iff _ _)) in Hcmp.
    rewrite <- Hcmp. exact H1.
  - exact (ord_lt_trans _ _ _ H1 Hcmp).
  - exfalso. apply H2. reflexivity.
Qed.

(* The lower-bound theorem: for every nat n, there is a Provable_term
   phi whose height is strictly above V_cnf (nat_to_ord n).  The phi
   is nat_witness_form n (= n levels of Box 0 around Top), and the
   proof is nat_witness_proof n (= n Nec applications on pt_id_Top).
   Both vary with n -- the construction is primitive-recursive on n
   with one Nec increment per step. *)
Theorem witness_at_for_finite_alpha : forall n,
  { phi : Form &
    { pt : Provable_term phi &
        vord_le (V_cnf (nat_to_ord n)) (proof_height phi pt) } }.
Proof.
  intro n.
  exists (nat_witness_form n).
  exists (nat_witness_proof n).
  right.
  unfold proof_height. apply VL_cnf.
  exact (proof_height_nat_witness_gt_nat n).
Qed.

Theorem witness_at_finite_lower_bound : forall n,
  exists phi (pt : Provable_term phi),
    vord_le (V_cnf (nat_to_ord n)) (proof_height phi pt).
Proof.
  intro n.
  destruct (witness_at_for_finite_alpha n) as [phi [pt Hle]].
  exists phi, pt. exact Hle.
Qed.

(* Recursive witness construction over arbitrary CNF ords.
   Given o : ord, builds a Form phi and a Provable_term proof pt
   such that the proof's rank ord_le-dominates o.
   Recursion structure: for OCons a t, recurse on a (giving a
   proof of rank >= a, then Nec'd to give rank >= ω^a) and on t
   (giving a proof of rank >= t), then combine via MP-then-K to
   get a proof of rank >= ord_add (ω^a) t = OCons a t (when t's
   leading exp < a, i.e. o is in CNF). *)
Fixpoint witness_at_for_ord_form (o : ord) : Form :=
  match o with
  | OZero => Top
  | OCons a _ => Box 0 (witness_at_for_ord_form a)
  end.

Fixpoint witness_at_for_ord_proof (o : ord) :
  Provable_term (witness_at_for_ord_form o) :=
  match o return Provable_term (witness_at_for_ord_form o) with
  | OZero => pt_id_Top
  | OCons a t =>
      let p_a := witness_at_for_ord_proof a in
      let p_a_box : Provable_term (Box 0 (witness_at_for_ord_form a))
        := pt_Nec 0 (witness_at_for_ord_form a) p_a in
      let p_t := witness_at_for_ord_proof t in
      let pK := pt_K (Box 0 (witness_at_for_ord_form a))
                     (witness_at_for_ord_form t) in
      let p1 := pt_MP _ _ pK p_a_box in
      pt_MP _ _ p1 p_t
  end.

(* The transitivity of ord_lt for arbitrary CNF (the codebase's
   [ord_lt_trans] is for the wf_ord/cnf-restricted version; here
   we use the unrestricted ord_compare-based one). *)
Lemma ord_lt_trans_unrestricted : forall a b c,
  ord_lt a b -> ord_lt b c -> ord_lt a c.
Proof. intros a b c. exact (ord_lt_trans a b c). Qed.

(* OCons _ _ is strictly greater than OZero. *)
Lemma OZero_lt_OCons : forall e t, ord_lt OZero (OCons e t).
Proof. intros e t. unfold ord_lt. cbn. reflexivity. Qed.

(* Reflexivity of ord_le. *)
Lemma ord_le_refl : forall o, ord_le o o.
Proof.
  intro o. unfold ord_le. rewrite ord_compare_refl. discriminate.
Qed.

(* Strict-implies-le. *)
Lemma ord_lt_le : forall a b, ord_lt a b -> ord_le a b.
Proof.
  intros a b H. unfold ord_le, ord_lt in *. rewrite H. discriminate.
Qed.

(* ord_add of two OCons-shaped ords is OCons-shaped. *)
Lemma ord_add_OCons_OCons_OCons : forall ae at_a be bt,
  exists e t, ord_add (OCons ae at_a) (OCons be bt) = OCons e t.
Proof.
  intros ae at_a be bt. cbn.
  destruct (ord_compare ae be); eauto.
Qed.

(* Every Provable_term has positive proof_height_ord (= OCons-shaped). *)
Lemma proof_height_ord_OCons_shape :
  forall (phi : Form) (pt : Provable_term phi),
  exists e t, proof_height_ord phi pt = OCons e t.
Proof.
  intros phi pt. induction pt; try (cbn; eauto; fail).
  - cbn. unfold omega_cnf. eauto.
  - cbn. unfold omega_cnf. eauto.
  - cbn. unfold omega_cnf. eauto.
  - cbn. unfold omega_cnf. eauto.
  - cbn. unfold omega_cnf. eauto.
  - cbn. unfold omega_cnf. eauto.
  - cbn. unfold omega_cnf. eauto.
  - cbn. unfold omega_cnf. eauto.
  - cbn.
    destruct IHpt1 as [e1 [t1 H1]].
    destruct IHpt2 as [e2 [t2 H2]].
    rewrite H1, H2.
    apply ord_add_OCons_OCons_OCons.
  - cbn. unfold omega_pow. eauto.
Qed.

(* The proof_height of witness_at_for_ord_proof always exceeds OZero. *)
Lemma proof_height_witness_at_for_ord_proof_pos : forall o,
  ord_lt OZero (proof_height_ord (witness_at_for_ord_form o)
                                  (witness_at_for_ord_proof o)).
Proof.
  intro o.
  destruct (proof_height_ord_OCons_shape (witness_at_for_ord_form o)
                                          (witness_at_for_ord_proof o))
    as [e [t Heq]].
  rewrite Heq. unfold ord_lt. cbn. reflexivity.
Qed.

(* Basic ord_le/ord_lt arithmetic. *)
Lemma ord_le_lt_trans : forall a b c,
  ord_le a b -> ord_lt b c -> ord_lt a c.
Proof.
  intros a b c Hab Hbc. unfold ord_le, ord_lt in *.
  destruct (ord_compare a b) eqn:Eab.
  - apply ord_compare_eq_iff in Eab. rewrite Eab. exact Hbc.
  - exact (ord_lt_trans _ _ _ Eab Hbc).
  - exfalso. apply Hab. reflexivity.
Qed.

Lemma ord_lt_le_trans : forall a b c,
  ord_lt a b -> ord_le b c -> ord_lt a c.
Proof.
  intros a b c Hab Hbc. unfold ord_le, ord_lt in *.
  destruct (ord_compare b c) eqn:Ebc.
  - apply ord_compare_eq_iff in Ebc. rewrite <- Ebc. exact Hab.
  - exact (ord_lt_trans _ _ _ Hab Ebc).
  - exfalso. apply Hbc. reflexivity.
Qed.

Lemma ord_le_trans : forall a b c,
  ord_le a b -> ord_le b c -> ord_le a c.
Proof.
  intros a b c Hab Hbc. unfold ord_le in *.
  destruct (ord_compare a c) eqn:Eac.
  - congruence.
  - congruence.
  - destruct (ord_compare a b) eqn:Eab.
    + apply ord_compare_eq_iff in Eab. rewrite Eab in Eac.
      exfalso. apply Hbc. exact Eac.
    + assert (Hab2 : ord_lt a b) by exact Eab.
      destruct (ord_compare b c) eqn:Ebc.
      * apply ord_compare_eq_iff in Ebc.
        rewrite Ebc in Hab2. unfold ord_lt in Hab2.
        rewrite Eac in Hab2. discriminate.
      * pose proof (ord_lt_trans _ _ _ Hab2 Ebc) as H.
        unfold ord_lt in H. rewrite Eac in H. discriminate.
      * exfalso. apply Hbc. reflexivity.
    + exfalso. apply Hab. reflexivity.
Qed.

(* The CNF condition: t's leading exp < a => ord_add (omega_pow a) t = OCons a t. *)
Lemma ord_add_omega_pow_t_when_t_is_OZero : forall a,
  ord_add (omega_pow a) OZero = OCons a OZero.
Proof. intro a. cbn. reflexivity. Qed.

Lemma ord_add_omega_pow_OCons_when_lt :
  forall a be bt,
  ord_compare a be = Gt ->
  ord_add (omega_pow a) (OCons be bt) = OCons a (OCons be bt).
Proof.
  intros a be bt H. unfold omega_pow. cbn. rewrite H. reflexivity.
Qed.

Lemma ord_add_omega_pow_OCons_when_eq :
  forall a bt,
  ord_add (omega_pow a) (OCons a bt) = OCons a (OCons a bt).
Proof.
  intros a bt. unfold omega_pow. cbn. rewrite ord_compare_refl. reflexivity.
Qed.

(* For wf_ord (OCons a t): t's leading exp is strictly less than a,
   or t is OZero.  In both cases, ord_add (omega_pow a) t = OCons a t. *)
Lemma ord_add_omega_pow_wf : forall a t,
  wf_ord (OCons a t) ->
  ord_add (omega_pow a) t = OCons a t.
Proof.
  intros a t Hwf. cbn in Hwf.
  destruct Hwf as [_ [_ Hcond]].
  destruct t as [|te tt].
  - apply ord_add_omega_pow_t_when_t_is_OZero.
  - apply ord_add_omega_pow_OCons_when_lt.
    pose proof (ord_compare_antisym te a) as Hsym.
    rewrite Hcond in Hsym.
    destruct (ord_compare a te); cbn in Hsym; congruence.
Qed.

(* ord_compare on omega_pow distributes through the argument. *)
Lemma ord_compare_omega_pow : forall a b,
  ord_compare (omega_pow a) (omega_pow b) = ord_compare a b.
Proof.
  intros a b. unfold omega_pow. cbn.
  destruct (ord_compare a b) eqn:E; reflexivity.
Qed.

Lemma omega_pow_monotone_le : forall a b,
  ord_le a b -> ord_le (omega_pow a) (omega_pow b).
Proof.
  intros a b Hab. unfold ord_le in *.
  rewrite ord_compare_omega_pow. exact Hab.
Qed.

Lemma omega_pow_monotone_lt : forall a b,
  ord_lt a b -> ord_lt (omega_pow a) (omega_pow b).
Proof.
  intros a b Hab. unfold ord_lt in *.
  rewrite ord_compare_omega_pow. exact Hab.
Qed.

(* Strict ord_lt-through-leading: when a < a', OCons a t < OCons a' t' *)
Lemma ord_lt_OCons_leading : forall a t a' t',
  ord_lt a a' -> ord_lt (OCons a t) (OCons a' t').
Proof.
  intros a t a' t' H. apply ord_lt_OCons_head. exact H.
Qed.

(* When the leading is equal and tails compare ord_le, OCons-form ord_le. *)
Lemma ord_le_OCons_when_eq_leading : forall a t1 t2,
  ord_le t1 t2 -> ord_le (OCons a t1) (OCons a t2).
Proof.
  intros a t1 t2 H. unfold ord_le, ord_lt in *.
  cbn. rewrite ord_compare_refl. exact H.
Qed.

(* Generalisation: when leadings compare Eq (need not be syntactically
   identical), the OCons-form ord_le follows from the tail's ord_le. *)
Lemma ord_le_OCons_when_compare_eq_leading : forall a a' t1 t2,
  ord_compare a a' = Eq -> ord_le t1 t2 -> ord_le (OCons a t1) (OCons a' t2).
Proof.
  intros a a' t1 t2 Hcmp Ht. unfold ord_le, ord_lt in *.
  cbn. rewrite Hcmp. exact Ht.
Qed.

(* OCons a t1 ≤ OCons a' t2 when a < a' (purely from leading exp). *)
Lemma ord_le_OCons_leading_lt : forall a t1 a' t2,
  ord_lt a a' -> ord_le (OCons a t1) (OCons a' t2).
Proof.
  intros a t1 a' t2 H. apply ord_lt_le. apply ord_lt_OCons_head. exact H.
Qed.

(* Helper: omega_cnf is positive. *)
Lemma omega_cnf_pos : ord_lt OZero omega_cnf.
Proof. unfold ord_lt, omega_cnf. cbn. reflexivity. Qed.

Lemma omega_cnf_gt_one : ord_lt (OCons OZero OZero) omega_cnf.
Proof. unfold ord_lt, omega_cnf. cbn. reflexivity. Qed.

(* Every proof_height_ord is at least omega_cnf, since the base axiom
   ranks ARE omega_cnf and ord_add / omega_pow only grow heights. *)
(* Helper: ord_compare X (OCons (OCons OZero OZero) Y) is determined
   by the leading exp of X compared to OCons OZero OZero, with the
   tail comparing only when leading is exactly OCons OZero OZero. *)
Lemma omega_cnf_le_OCons_OCons_OZero_OZero_anything : forall t,
  ord_le omega_cnf (OCons (OCons OZero OZero) t).
Proof.
  intro t. unfold ord_le, omega_cnf. cbn.
  destruct t; cbn; discriminate.
Qed.

(* If e is OCons (OCons OZero OZero) _ or has leading >= OCons OZero OZero,
   then ord_le omega_cnf (OCons e _). *)
Lemma omega_cnf_le_OCons_when_lead_ge : forall e t,
  ord_le (OCons OZero OZero) e ->
  ord_le omega_cnf (OCons e t).
Proof.
  intros e t H.
  destruct e as [|ee et].
  - exfalso. apply H. unfold ord_le. cbn. reflexivity.
  - destruct ee as [|eee eet].
    + (* e = OCons OZero et: leading exp OZero, equal to OCons OZero OZero's
         leading exp OZero. Compare tails. *)
      destruct et as [|ete ett].
      * (* e = OCons OZero OZero = 1 = leading of omega_cnf. *)
        unfold ord_le, omega_cnf. cbn.
        destruct t; cbn; discriminate.
      * (* e = OCons OZero (OCons _ _) *)
        unfold ord_le, omega_cnf. cbn.
        discriminate.
    + (* e = OCons (OCons _ _) _: leading > OZero. *)
      unfold ord_le, omega_cnf. cbn.
      discriminate.
Qed.

Lemma omega_cnf_le_implies_gt_one : forall x,
  ord_le omega_cnf x -> ord_lt (OCons OZero OZero) x.
Proof.
  intros x H. exact (ord_lt_le_trans _ _ _ omega_cnf_gt_one H).
Qed.

(* When H_a > 1, ord_add omega_cnf (omega_pow H_a) absorbs to omega_pow H_a. *)
Lemma ord_add_omega_cnf_absorbed : forall H_a,
  ord_lt (OCons OZero OZero) H_a ->
  ord_add omega_cnf (omega_pow H_a) = omega_pow H_a.
Proof.
  intros H_a Hlt.
  destruct H_a as [|e t].
  - exfalso. unfold ord_lt in Hlt. cbn in Hlt. discriminate.
  - destruct e as [|ee et].
    + destruct t as [|te tt].
      * exfalso. unfold ord_lt in Hlt. cbn in Hlt. discriminate.
      * unfold omega_cnf, omega_pow. cbn. reflexivity.
    + unfold omega_cnf, omega_pow. cbn. reflexivity.
Qed.

Lemma proof_height_ord_ge_omega_cnf :
  forall (phi : Form) (pt : Provable_term phi),
  ord_le omega_cnf (proof_height_ord phi pt).
Proof.
  intros phi pt. induction pt.
  - cbn. apply ord_le_refl.
  - cbn. apply ord_le_refl.
  - cbn. apply ord_le_refl.
  - cbn. apply ord_le_refl.
  - cbn. apply ord_le_refl.
  - cbn. apply ord_le_refl.
  - cbn. apply ord_le_refl.
  - cbn. apply ord_le_refl.
  - cbn.
    destruct (proof_height_ord_OCons_shape _ pt1) as [e1 [t1 H1]].
    destruct (proof_height_ord_OCons_shape _ pt2) as [e2 [t2 H2]].
    rewrite H1 in IHpt1 |- *.
    rewrite H2 in IHpt2 |- *.
    cbn.
    (* IHpt1: ord_le omega_cnf (OCons e1 t1).  This means ord_compare
       (OCons OZero OZero) e1 is Eq or Lt, i.e., e1 >= OCons OZero OZero. *)
    assert (HE1 : ord_le (OCons OZero OZero) e1).
    { destruct e1 as [|e1e e1t].
      - exfalso. apply IHpt1. unfold omega_cnf. cbn. reflexivity.
      - destruct e1e as [|e1ee e1et].
        + destruct e1t as [|e1te e1tt].
          * unfold ord_le. cbn. discriminate.
          * unfold ord_le. cbn. discriminate.
        + unfold ord_le. cbn. discriminate. }
    destruct (ord_compare e1 e2) eqn:Hee.
    + apply ord_compare_eq_iff in Hee. subst e2.
      apply omega_cnf_le_OCons_when_lead_ge. exact HE1.
    + exact IHpt2.
    + apply omega_cnf_le_OCons_when_lead_ge. exact HE1.
  - cbn.
    unfold omega_pow.
    destruct (proof_height_ord_OCons_shape _ pt) as [e [t Heq]].
    rewrite Heq.
    apply omega_cnf_le_OCons_when_lead_ge.
    unfold ord_le. destruct e as [|ee et]; cbn.
    + destruct t as [|te tt]; cbn; discriminate.
    + discriminate.
Qed.

(* Helper: if omega_pow X has leading exp X, the result of ord_add ω
   (omega_pow X) has leading exp X (when X >= 1, which it is for positive X). *)

(* Tail-lt-leading for wf_ord: when wf_ord (OCons e t), ord_lt t (OCons e t). *)
Lemma wf_ord_OCons_tail_lt : forall e t,
  wf_ord (OCons e t) -> ord_lt t (OCons e t).
Proof.
  intros e t Hwf. unfold ord_lt.
  destruct t as [|te tt]; cbn.
  - reflexivity.
  - cbn in Hwf. destruct Hwf as [_ [_ Hcond]].
    rewrite Hcond. reflexivity.
Qed.

(* The proof_height of witness_at_for_ord_proof (OCons a t) is the explicit
   nested ord_add expression in terms of the heights of the sub-proofs. *)
Lemma proof_height_ord_witness_OCons : forall a t,
  proof_height_ord (witness_at_for_ord_form (OCons a t))
                   (witness_at_for_ord_proof (OCons a t))
  = ord_add (ord_add omega_cnf
               (omega_pow (proof_height_ord (witness_at_for_ord_form a)
                                            (witness_at_for_ord_proof a))))
            (proof_height_ord (witness_at_for_ord_form t)
                              (witness_at_for_ord_proof t)).
Proof. intros a t. reflexivity. Qed.

(* The main theorem: for every CNF ord o, the witness construction
   yields a proof whose height ord_le-dominates o.  The construction
   is primitive-recursive on the structure of o, and the height bound
   is achieved without any classical-existence appeal. *)
Theorem witness_at_for_ord_bound : forall o,
  wf_ord o ->
  ord_le o (proof_height_ord (witness_at_for_ord_form o)
                              (witness_at_for_ord_proof o)).
Proof.
  induction o as [|a IHa t IHt]; intro Hwf.
  - (* o = OZero: ord_le OZero anything. *)
    apply ord_compare_OZero_le.
  - cbn in Hwf. destruct Hwf as [Hwf_a [Hwf_t _]].
    pose proof (IHa Hwf_a) as IH_a.
    pose proof (IHt Hwf_t) as IH_t.
    rewrite proof_height_ord_witness_OCons.
    pose proof (proof_height_ord_ge_omega_cnf _
                  (witness_at_for_ord_proof a)) as Ha_ge.
    pose proof (omega_cnf_le_implies_gt_one _ Ha_ge) as Ha_gt1.
    rewrite (ord_add_omega_cnf_absorbed _ Ha_gt1).
    pose proof (proof_height_ord_OCons_shape _
                  (witness_at_for_ord_proof t)) as [hte [htt Hht_eq]].
    rewrite Hht_eq.
    rewrite Hht_eq in IH_t.
    unfold omega_pow.
    cbn [ord_add].
    destruct (ord_compare (proof_height_ord (witness_at_for_ord_form a)
                                            (witness_at_for_ord_proof a))
                          hte) eqn:Hcmp_a_hte.
    + (* H_a = hte *)
      apply ord_compare_eq_iff in Hcmp_a_hte.
      subst hte.
      cbn [ord_add].
      destruct (ord_compare a (proof_height_ord (witness_at_for_ord_form a)
                                                (witness_at_for_ord_proof a)))
        eqn:Ha_cmp.
      * (* a = H_a *)
        apply ord_le_OCons_when_compare_eq_leading; [exact Ha_cmp|].
        exact IH_t.
      * (* a < H_a *)
        apply ord_le_OCons_leading_lt. exact Ha_cmp.
      * (* a > H_a — contradicts IH_a *)
        exfalso. apply IH_a. exact Ha_cmp.
    + (* H_a < hte *)
      apply ord_le_OCons_leading_lt.
      exact (ord_le_lt_trans _ _ _ IH_a Hcmp_a_hte).
    + (* H_a > hte *)
      cbn [ord_add].
      destruct (ord_compare a (proof_height_ord (witness_at_for_ord_form a)
                                                (witness_at_for_ord_proof a)))
        eqn:Ha_cmp.
      * apply ord_le_OCons_when_compare_eq_leading; [exact Ha_cmp|].
        exact IH_t.
      * apply ord_le_OCons_leading_lt. exact Ha_cmp.
      * exfalso. apply IH_a. exact Ha_cmp.
Qed.

(* Every vord strictly below the ε_0 atom [veps0 = V_phi 0 OZero] is a
   V_cnf-image: VL_cnf_phi places every CNF strictly below V_phi-atoms,
   while no V_phi atom is below V_phi 0 OZero (the index 0 has no
   smaller nat, and the argument OZero has no smaller ord).  Note this
   is FALSE for the genuine [Gamma_0_ordinal = V_gamma0]: the V_phi
   atoms all sit strictly between ε_0-and-friends and Γ_0. *)
Lemma vord_lt_veps0_iff_V_cnf : forall v,
  vord_lt v veps0 ->
  exists o, v = V_cnf o.
Proof.
  intros v Hlt. unfold veps0 in Hlt.
  apply vord_lt_V_phi_inv in Hlt.
  destruct Hlt as [[o Heq] | [[n' [α' [_ Hlt_n]]] | [α' [_ Hlt_α]]]].
  - exists o. exact Heq.
  - lia.
  - destruct α' as [|αe αt]; unfold ord_lt in Hlt_α; cbn in Hlt_α; discriminate.
Qed.

(* The vord-level lower bound: for every vord v strictly below the
   ε_0 atom [veps0], there is a Provable_term whose proof_height
   vord_le-dominates v.  Combined with [proof_height_below_eps0]
   below, this gives EXACTNESS at ε_0 for the omega_pow height
   measure — the heights are all strictly below the ε_0 atom, and
   every threshold strictly below it is attained.  The lower-bound
   construction is primitive-recursive on the underlying CNF ord and
   produces strictly larger proof_heights for strictly larger ords. *)
Theorem witness_at_below_eps0 : forall v,
  wf_vord v ->
  vord_lt v veps0 ->
  { phi : Form &
    { pt : Provable_term phi & vord_le v (proof_height phi pt) } }.
Proof.
  intros v Hwf Hlt.
  destruct v as [o | n α |].
  - cbn in Hwf.
    exists (witness_at_for_ord_form o).
    exists (witness_at_for_ord_proof o).
    pose proof (witness_at_for_ord_bound o Hwf) as Hbound.
    unfold ord_le in Hbound. unfold proof_height, vord_le.
    destruct (ord_compare o (proof_height_ord (witness_at_for_ord_form o)
                                              (witness_at_for_ord_proof o)))
      eqn:Hcmp.
    + left. f_equal. apply ord_compare_eq_iff. exact Hcmp.
    + right. apply VL_cnf. exact Hcmp.
    + exfalso. apply Hbound. reflexivity.
  - exfalso. unfold veps0 in Hlt.
    apply vord_lt_V_phi_inv in Hlt.
    destruct Hlt as [[o Heq] | [[n' [α' [Heq Hlt_n]]] | [α' [Heq Hlt_α]]]].
    + discriminate.
    + injection Heq as En _. subst n'. lia.
    + injection Heq as En _. subst n.
      destruct α' as [|αe αt]; unfold ord_lt in Hlt_α; cbn in Hlt_α; discriminate.
  - exfalso. unfold veps0 in Hlt.
    apply vord_lt_V_phi_inv in Hlt.
    destruct Hlt as [[o Heq] | [[n' [α' [Heq Hlt_n]]] | [α' [Heq Hlt_α]]]];
      discriminate.
Qed.


(******************************************************************************)
(* Genuine Gamma_0 (todo #9).                                                  *)
(*                                                                            *)
(* [Gamma_0_ordinal = V_gamma0] is the new top atom of the Veblen carrier:    *)
(* strictly above every [V_phi n alpha] (in particular above the whole        *)
(* phi-tower of Gamma_0-approximations [vgamma0_approx n]) and the LEAST      *)
(* such point of the carrier.  It is provably distinct from the eps_0 atom    *)
(* and from every CNF tree, discharging the forbidden-alias clauses.          *)
(******************************************************************************)

Theorem Gamma_0_is_V_gamma0 : Gamma_0_ordinal = V_gamma0.
Proof. reflexivity. Qed.

Theorem Gamma_0_not_eps0 : Gamma_0_ordinal <> veps0.
Proof. discriminate. Qed.

Theorem Gamma_0_not_cnf_shape : forall o, Gamma_0_ordinal <> V_cnf o.
Proof. intros o H. discriminate H. Qed.

Theorem Gamma_0_not_Veblen_eps0_alias :
  Gamma_0_ordinal <> V_cnf Veblen_eps0_ordinal.
Proof. apply Gamma_0_not_cnf_shape. Qed.

Theorem Gamma_0_wf : wf_vord Gamma_0_ordinal.
Proof. exact I. Qed.

Theorem Gamma_0_above_phi_tower : forall n alpha,
  vord_lt (V_phi n alpha) Gamma_0_ordinal.
Proof. intros n alpha. apply VL_phi_g0. Qed.

Theorem Gamma_0_above_eps0 : vord_lt veps0 Gamma_0_ordinal.
Proof. apply VL_phi_g0. Qed.

Theorem Gamma_0_above_gamma0_approx : forall n,
  vord_lt (vgamma0_approx n) Gamma_0_ordinal.
Proof. intro n. apply VL_phi_g0. Qed.

(** Leastness: any vord lying strictly above EVERY phi-tower stage
    [vgamma0_approx n] is at least [Gamma_0_ordinal].  This is the
    "first (common) fixed point above the phi-tower" characterisation
    inside the notation system: Gamma_0 is the least upper bound of
    the family phi_(n+1)(0). *)

Theorem Gamma_0_least_above_phi_tower : forall v,
  (forall n, vord_lt (vgamma0_approx n) v) ->
  vord_le Gamma_0_ordinal v.
Proof.
  intros v H.
  destruct v as [o | m alpha |].
  - exfalso. pose proof (H 0) as H0.
    apply vord_lt_V_cnf_inv in H0.
    destruct H0 as [o' [Heq _]]. discriminate.
  - exfalso. pose proof (H (S m)) as HSm.
    unfold vgamma0_approx in HSm.
    apply vord_lt_V_phi_inv in HSm.
    destruct HSm as [[o Heq] | [[n' [a' [Heq Hlt]]] | [a' [Heq Hlt]]]].
    + discriminate.
    + injection Heq as E1 E2. lia.
    + injection Heq as E1 E2. lia.
  - left. reflexivity.
Qed.

(** The omega_pow proof-height measure is strictly below the eps_0 atom
    — so the Gamma_0 upper bound [GLP_proof_height_below_Gamma_0] is
    genuine but NOT tight, with [veps0] witnessing the gap. *)

Theorem proof_height_below_eps0 : forall phi (pt : Provable_term phi),
  vord_lt (proof_height phi pt) veps0.
Proof.
  intros phi pt. unfold proof_height, veps0. apply VL_cnf_phi.
Qed.

Theorem Gamma_0_bound_not_tight :
  (forall phi (pt : Provable_term phi), vord_lt (proof_height phi pt) veps0) /\
  vord_lt veps0 Gamma_0_ordinal.
Proof.
  split.
  - exact proof_height_below_eps0.
  - exact Gamma_0_above_eps0.
Qed.

(** Exactness of the omega_pow measure at eps_0: heights are bounded by
    the eps_0 atom, and every well-formed CNF threshold strictly below
    it is attained by an explicit primitive-recursive witness. *)

Theorem proof_height_eps0_exact :
  (forall phi (pt : Provable_term phi), vord_lt (proof_height phi pt) veps0) /\
  (forall o, wf_ord o ->
     exists phi (pt : Provable_term phi),
       vord_le (V_cnf o) (proof_height phi pt)).
Proof.
  split.
  - exact proof_height_below_eps0.
  - intros o Hwf.
    destruct (witness_at_below_eps0 (V_cnf o) Hwf (cnf_below_veps0 o))
      as [phi [pt Hle]].
    exists phi, pt. exact Hle.
Qed.

(******************************************************************************)
(* Acceptance-literal height measure (todo #9): Loeb leaves at rank omega,    *)
(* all other axiom leaves at rank 1, MP = successor of the sup (ord_max) of   *)
(* the children, Nec = successor of the child.  Its exact supremum is         *)
(* omega * 2, computed below: every height is strictly below omega_two and    *)
(* every omega + n is attained by the explicit Nec-tower over a Loeb leaf.    *)
(******************************************************************************)

Definition ord_one : ord := OCons OZero OZero.

Definition omega_plus (n : nat) : ord := OCons ord_one (nat_to_ord n).

Definition omega_two : ord := OCons ord_one (OCons ord_one OZero).

Fixpoint proof_height_lit (phi : Form) (pt : Provable_term phi) : ord :=
  match pt with
  | pt_K _ _      => ord_one
  | pt_S _ _ _    => ord_one
  | pt_DN _       => ord_one
  | pt_BoxK _ _ _ => ord_one
  | pt_Loeb _ _   => omega_cnf
  | pt_Box4 _ _   => ord_one
  | pt_Mon _ _    => ord_one
  | pt_NextCon _  => ord_one
  | pt_MP _ _ p1 p2 =>
      succ_cnf (ord_max (proof_height_lit _ p1) (proof_height_lit _ p2))
  | pt_Nec _ _ p => succ_cnf (proof_height_lit _ p)
  end.

Lemma succ_cnf_shape : forall t, exists e t', succ_cnf t = OCons e t'.
Proof. intros [|e t]; cbn; eauto. Qed.

Lemma succ_cnf_nat_to_ord : forall n,
  succ_cnf (nat_to_ord n) = nat_to_ord (S n).
Proof.
  induction n as [|n IH]; cbn.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma succ_omega_plus : forall n,
  succ_cnf (omega_plus n) = omega_plus (S n).
Proof.
  intro n. unfold omega_plus. cbn.
  rewrite succ_cnf_nat_to_ord. reflexivity.
Qed.

Lemma nat_to_ord_le : forall a b,
  a <= b -> ord_le (nat_to_ord a) (nat_to_ord b).
Proof.
  intros a b Hle.
  destruct (Nat.eq_dec a b) as [Heq | Hne].
  - subst b. apply ord_le_refl.
  - apply ord_lt_le. apply nat_to_ord_strict_lt. lia.
Qed.

Lemma omega_plus_le_mono : forall a b,
  a <= b -> ord_le (omega_plus a) (omega_plus b).
Proof.
  intros a b Hle. unfold omega_plus.
  apply ord_le_OCons_when_eq_leading.
  apply nat_to_ord_le. exact Hle.
Qed.

Lemma ord_one_le_omega_plus : forall n, ord_le ord_one (omega_plus n).
Proof.
  intro n. apply ord_lt_le.
  unfold ord_lt, ord_one, omega_plus. cbn. reflexivity.
Qed.

Lemma omega_cnf_le_omega_plus : forall n, ord_le omega_cnf (omega_plus n).
Proof.
  intro n. unfold omega_cnf, omega_plus, ord_one.
  apply ord_le_OCons_when_eq_leading.
  unfold ord_le. apply ord_compare_OZero_le.
Qed.

Lemma ord_max_le_combine : forall x y a b,
  ord_le x (omega_plus a) ->
  ord_le y (omega_plus b) ->
  ord_le (ord_max x y) (omega_plus (Nat.max a b)).
Proof.
  intros x y a b Hx Hy. unfold ord_max.
  destruct (ord_compare x y).
  - eapply ord_le_trans; [exact Hx | apply omega_plus_le_mono; lia].
  - eapply ord_le_trans; [exact Hy | apply omega_plus_le_mono; lia].
  - eapply ord_le_trans; [exact Hx | apply omega_plus_le_mono; lia].
Qed.

Lemma succ_cnf_compare : forall a b,
  ord_compare (succ_cnf a) (succ_cnf b) = ord_compare a b.
Proof.
  induction a as [|ae IHae at_ IHat]; intros b; destruct b as [|be bt]; cbn.
  - reflexivity.
  - destruct be; cbn.
    + destruct (succ_cnf_shape bt) as [e [t' E]]. rewrite E. reflexivity.
    + reflexivity.
  - destruct ae; cbn.
    + destruct (succ_cnf_shape at_) as [e [t' E]]. rewrite E. reflexivity.
    + reflexivity.
  - rewrite IHat. destruct (ord_compare ae be); reflexivity.
Qed.

Lemma succ_cnf_le_mono : forall a b,
  ord_le a b -> ord_le (succ_cnf a) (succ_cnf b).
Proof.
  intros a b H. unfold ord_le in *.
  rewrite succ_cnf_compare. exact H.
Qed.

(** Heights of the literal measure are bounded by omega + proof length. *)

Lemma proof_height_lit_le_length : forall phi (pt : Provable_term phi),
  ord_le (proof_height_lit phi pt) (omega_plus (Provable_term_length phi pt)).
Proof.
  intros phi pt.
  induction pt; cbn [proof_height_lit Provable_term_length].
  - exact (ord_one_le_omega_plus 1).
  - exact (ord_one_le_omega_plus 1).
  - exact (ord_one_le_omega_plus 1).
  - exact (ord_one_le_omega_plus 1).
  - exact (omega_cnf_le_omega_plus 1).
  - exact (ord_one_le_omega_plus 1).
  - exact (ord_one_le_omega_plus 1).
  - exact (ord_one_le_omega_plus 1).
  - eapply ord_le_trans.
    + apply succ_cnf_le_mono.
      eapply ord_max_le_combine; eassumption.
    + rewrite succ_omega_plus. apply omega_plus_le_mono. lia.
  - eapply ord_le_trans.
    + apply succ_cnf_le_mono. eassumption.
    + rewrite succ_omega_plus. apply ord_le_refl.
Qed.

Lemma omega_plus_lt_omega_two : forall n,
  ord_lt (omega_plus n) omega_two.
Proof.
  intro n. unfold ord_lt, omega_plus, omega_two, ord_one. cbn.
  destruct n as [|m]; cbn; reflexivity.
Qed.

Theorem proof_height_lit_below_omega_two :
  forall phi (pt : Provable_term phi),
  ord_lt (proof_height_lit phi pt) omega_two.
Proof.
  intros phi pt.
  eapply ord_le_lt_trans.
  - apply proof_height_lit_le_length.
  - apply omega_plus_lt_omega_two.
Qed.

(** The explicit Nec-tower over a Loeb leaf attains omega + n exactly. *)

Fixpoint loeb_tower_form (n : nat) : Form :=
  match n with
  | 0 => Impl (Box 0 (Impl (Box 0 Bot) Bot)) (Box 0 Bot)
  | S k => Box 0 (loeb_tower_form k)
  end.

Fixpoint loeb_tower (n : nat) : Provable_term (loeb_tower_form n) :=
  match n return Provable_term (loeb_tower_form n) with
  | 0 => pt_Loeb 0 Bot
  | S k => pt_Nec 0 (loeb_tower_form k) (loeb_tower k)
  end.

Lemma loeb_tower_height : forall n,
  proof_height_lit (loeb_tower_form n) (loeb_tower n) = omega_plus n.
Proof.
  induction n as [|n IH]; cbn [loeb_tower proof_height_lit].
  - unfold omega_cnf, omega_plus, ord_one. reflexivity.
  - rewrite IH. apply succ_omega_plus.
Qed.

(** Exactness package: the literal measure's supremum is omega * 2 —
    bounded strictly below omega_two, with every omega + n attained. *)

Theorem proof_height_lit_sup_omega_two :
  (forall phi (pt : Provable_term phi),
     ord_lt (proof_height_lit phi pt) omega_two) /\
  (forall n, exists phi (pt : Provable_term phi),
     proof_height_lit phi pt = omega_plus n).
Proof.
  split.
  - exact proof_height_lit_below_omega_two.
  - intro n. exists (loeb_tower_form n), (loeb_tower n).
    apply loeb_tower_height.
Qed.

(** Non-degeneracy: the literal measure never returns OZero and is not
    a constant function of the derivation — discharging the forbidden
    trivialisations of todo #9. *)

Lemma proof_height_lit_shape : forall phi (pt : Provable_term phi),
  exists e t, proof_height_lit phi pt = OCons e t.
Proof.
  intros phi pt. destruct pt; cbn.
  - unfold ord_one. eauto.
  - unfold ord_one. eauto.
  - unfold ord_one. eauto.
  - unfold ord_one. eauto.
  - unfold omega_cnf. eauto.
  - unfold ord_one. eauto.
  - unfold ord_one. eauto.
  - unfold ord_one. eauto.
  - apply succ_cnf_shape.
  - apply succ_cnf_shape.
Qed.

Theorem proof_height_lit_never_zero : forall phi (pt : Provable_term phi),
  proof_height_lit phi pt <> OZero.
Proof.
  intros phi pt H.
  destruct (proof_height_lit_shape phi pt) as [e [t E]].
  rewrite E in H. discriminate.
Qed.

Theorem proof_height_lit_not_constant :
  proof_height_lit _ (loeb_tower 0) <> proof_height_lit _ (loeb_tower 1).
Proof.
  rewrite (loeb_tower_height 0), (loeb_tower_height 1).
  unfold omega_plus. cbn.
  intro H. injection H as H1. discriminate H1.
Qed.

(** The literal measure also sits strictly below the genuine Gamma_0
    atom (the todo #9 headline restated for this measure), and the
    Gamma_0 bound is again not tight: heights are V_cnf images, hence
    already strictly below the eps_0 atom. *)

Theorem GLP_proof_height_lit_below_Gamma_0 :
  forall phi (pt : Provable_term phi),
  vord_lt (V_cnf (proof_height_lit phi pt)) Gamma_0_ordinal.
Proof.
  intros phi pt. apply VL_cnf_g0.
Qed.

Theorem proof_height_lit_below_eps0 :
  forall phi (pt : Provable_term phi),
  vord_lt (V_cnf (proof_height_lit phi pt)) veps0.
Proof.
  intros phi pt. apply VL_cnf_phi.
Qed.

(** Bridge for the Prop-level provability predicate: [proof_height]
    cannot be a function out of [|- phi] (large elimination from Prop
    into Type is impossible), but every Provable formula admits SOME
    derivation height, strictly below omega_two, hence below eps_0 and
    Gamma_0. *)

Theorem proof_height_lit_bound_for_provable : forall phi,
  |- phi ->
  exists o : ord,
    ord_lt o omega_two /\
    exists pt : Provable_term phi, proof_height_lit phi pt = o.
Proof.
  intros phi Hp.
  destruct (provable_to_inhabited_Provable_term phi Hp) as [pt].
  exists (proof_height_lit phi pt). split.
  - apply proof_height_lit_below_omega_two.
  - exists pt. reflexivity.
Qed.

(** ** Decidability infrastructure for full GLP*: fragment deciders,
    the Fnat-closed bounded semantics, worm implications, the I2 frame,
    and the measure-recursive decider for box-towers over box-free
    leaves. *)

Fixpoint form_length (phi : Form) : nat :=
  match phi with
  | Var _ => 1
  | Bot => 1
  | Impl X Y => S (form_length X + form_length Y)
  | Box _ psi => S (form_length psi)
  end.

Lemma form_length_pos : forall phi, form_length phi >= 1.
Proof. intro phi. destruct phi; cbn; lia. Qed.

(** ** Closed box-free [forces_fnat_closed] equals [eval]. *)

Lemma forces_fnat_closed_box_free_eq_eval : forall phi,
  free_vars phi = [] -> box_free phi ->
  forall w val, forces_fnat_closed phi w = eval val phi.
Proof.
  intro phi. induction phi as [k | | X IHX Y IHY | n psi IHpsi];
    intros Hcl Hbf w val; cbn in *.
  - discriminate Hcl.
  - reflexivity.
  - apply app_eq_nil in Hcl. destruct Hcl as [HclX HclY].
    destruct Hbf as [HbfX HbfY].
    rewrite (IHX HclX HbfX w val), (IHY HclY HbfY w val). reflexivity.
  - exfalso. exact Hbf.
Qed.

(** ** Closed box-free FMP. *)

Theorem closed_box_free_FMP : forall phi,
  free_vars phi = [] -> box_free phi ->
  ((forall w, forces_fnat_closed phi w = true) <-> |- phi).
Proof.
  intros phi Hcl Hbf. split.
  - intros Hall. apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
    intro val.
    rewrite <- (forces_fnat_closed_box_free_eq_eval phi Hcl Hbf 0 val).
    exact (Hall 0).
  - intros Hp w. exact (provable_implies_forces_fnat_closed phi w Hcl Hp).
Qed.

Definition glp_decide_closed_box_free (phi : Form)
  (Hcl : free_vars phi = []) (Hbf : box_free phi) :
  sumbool (|- phi) (~ |- phi).
Proof.
  destruct (decide_tautology phi) eqn:Eq.
  - left. apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
    apply decide_tautology_correct. exact Eq.
  - right. intro Hp.
    pose proof (provable_classically_valid phi Hp) as Hcv.
    pose proof (decide_tautology_complete phi Hcv) as Heq.
    rewrite Eq in Heq. discriminate.
Defined.

(** ** Iterated boxes. *)

Lemma iter_box_closed : forall ns psi,
  free_vars psi = [] -> free_vars (iter_box ns psi) = [].
Proof.
  intro ns. induction ns as [|n rest IH]; intros psi Hcl; cbn.
  - exact Hcl.
  - exact (IH psi Hcl).
Qed.

Lemma provable_iter_box_intro : forall ns psi,
  |- psi -> |- iter_box ns psi.
Proof.
  intro ns. induction ns as [|n rest IH]; intros psi Hp; cbn.
  - exact Hp.
  - exact (Nec n _ (IH psi Hp)).
Qed.

(** [forces_fnat_closed (iter_box ns psi) v = true] uniformly when [eval val psi = true]. *)

Lemma forces_iter_box_eval_true_uniform : forall ns psi val,
  free_vars psi = [] -> box_free psi -> eval val psi = true ->
  forall v, forces_fnat_closed (iter_box ns psi) v = true.
Proof.
  intro ns. induction ns as [|n rest IH]; intros psi val Hcl Hbf Heval v; cbn.
  - rewrite (forces_fnat_closed_box_free_eq_eval psi Hcl Hbf v val). exact Heval.
  - apply forallb_forall. intros u _.
    exact (IH psi val Hcl Hbf Heval u).
Qed.

Fixpoint bad_world (ns : list nat) : nat :=
  match ns with
  | [] => 0
  | n :: rest => S (Nat.max n (bad_world rest))
  end.

Lemma forces_iter_box_at_bad_world : forall ns psi val,
  free_vars psi = [] -> box_free psi ->
  forall v, v >= bad_world ns ->
  forces_fnat_closed (iter_box ns psi) v = eval val psi.
Proof.
  intro ns. induction ns as [|n rest IH]; intros psi val Hcl Hbf v Hv.
  - cbn. exact (forces_fnat_closed_box_free_eq_eval psi Hcl Hbf v val).
  - destruct (eval val psi) eqn:Eeval.
    + exact (forces_iter_box_eval_true_uniform (n :: rest) psi val Hcl Hbf Eeval v).
    + cbn [iter_box bad_world] in *. cbn [forces_fnat_closed].
      destruct (forallb _ _) eqn:Efb; [|reflexivity].
      exfalso. rewrite forallb_forall in Efb.
      assert (Hin : In (v - 1) (seq n (v - n))).
      { apply in_seq. lia. }
      pose proof (Efb (v - 1) Hin) as Hf.
      assert (Hbnd : v - 1 >= bad_world rest) by lia.
      pose proof (IH psi val Hcl Hbf (v - 1) Hbnd) as Hihv.
      rewrite Hihv in Hf. rewrite Eeval in Hf. discriminate.
Qed.

(** ** Iter-box closed-box-free FMP / decidability. *)

Theorem provable_iter_box_box_free_iff : forall ns psi,
  free_vars psi = [] -> box_free psi ->
  (|- iter_box ns psi) <-> (|- psi).
Proof.
  intros ns psi Hcl Hbf. split.
  - intros Hp.
    apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
    intro val.
    pose proof (provable_implies_forces_fnat_closed (iter_box ns psi)
                  (bad_world ns) (iter_box_closed ns psi Hcl) Hp) as Hf.
    rewrite (forces_iter_box_at_bad_world ns psi val Hcl Hbf
               (bad_world ns) (Nat.le_refl _)) in Hf.
    exact Hf.
  - exact (provable_iter_box_intro ns psi).
Qed.

Definition glp_decide_iter_box_closed_box_free (ns : list nat) (psi : Form)
  (Hcl : free_vars psi = []) (Hbf : box_free psi) :
  sumbool (|- iter_box ns psi) (~ |- iter_box ns psi).
Proof.
  destruct (glp_decide_closed_box_free psi Hcl Hbf) as [Hp | Hnp].
  - left. exact (provable_iter_box_intro ns psi Hp).
  - right. intro Habs. apply Hnp.
    exact (proj1 (provable_iter_box_box_free_iff ns psi Hcl Hbf) Habs).
Defined.

(** ** Carlson-generalised unprovability of [Neg (Box n X)] for any closed [X].
    Carlson's polymodal second-incompleteness corresponds to [X = Bot]; the
    same Fnat-at-world-0 argument refutes [|- Neg (Box n X)] for arbitrary
    closed [X], because [forces_fnat_closed (Box n X) 0] is vacuously [true]. *)

Theorem closed_neg_box_unprovable : forall n X,
  free_vars X = [] -> ~ |- Neg (Box n X).
Proof.
  intros n X Hcl Hp.
  assert (Hclneg : free_vars (Neg (Box n X)) = []).
  { unfold Neg. cbn. rewrite app_nil_r. exact Hcl. }
  pose proof (provable_implies_forces_fnat_closed (Neg (Box n X)) 0 Hclneg Hp) as Hf.
  cbn in Hf. discriminate.
Qed.

(** ** Decidability of [Neg (Box n X)] for closed [X]: always [right]. *)

Definition glp_decide_neg_box_closed (n : nat) (X : Form)
  (Hcl : free_vars X = []) :
  sumbool (|- Neg (Box n X)) (~ |- Neg (Box n X)).
Proof.
  right. exact (closed_neg_box_unprovable n X Hcl).
Defined.

(** ** Decidability composition for And: combine two decidability results. *)

Definition glp_decide_and (phi psi : Form)
  (Dphi : sumbool (|- phi) (~ |- phi))
  (Dpsi : sumbool (|- psi) (~ |- psi)) :
  sumbool (|- And phi psi) (~ |- And phi psi).
Proof.
  destruct Dphi as [Hphi | Hphi]; destruct Dpsi as [Hpsi | Hpsi].
  - left. exact (prov_and_intro_meta phi psi Hphi Hpsi).
  - right. intro Hand. apply Hpsi. exact (prov_and_elim_r_meta phi psi Hand).
  - right. intro Hand. apply Hphi. exact (prov_and_elim_l_meta phi psi Hand).
  - right. intro Hand. apply Hphi. exact (prov_and_elim_l_meta phi psi Hand).
Defined.

(** ** Decidability composition for Iff: both directions decidable. *)

Definition glp_decide_iff (phi psi : Form)
  (Dfwd : sumbool (|- Impl phi psi) (~ |- Impl phi psi))
  (Dbwd : sumbool (|- Impl psi phi) (~ |- Impl psi phi)) :
  sumbool (|- Iff phi psi) (~ |- Iff phi psi).
Proof.
  unfold Iff. exact (glp_decide_and (Impl phi psi) (Impl psi phi) Dfwd Dbwd).
Defined.

(** ** Decidability of [Impl phi psi] when the consequent is provable. *)

Definition glp_decide_impl_consequent_provable (phi psi : Form)
  (Hpsi : |- psi) :
  sumbool (|- Impl phi psi) (~ |- Impl phi psi).
Proof.
  left. exact (MP _ _ (Ax_K psi phi) Hpsi).
Defined.

(** ** Decidability of [Impl phi psi] when the antecedent is provable
    and the consequent's provability status is decidable. *)

Definition glp_decide_impl_antecedent_provable (phi psi : Form)
  (Hphi : |- phi)
  (Dpsi : sumbool (|- psi) (~ |- psi)) :
  sumbool (|- Impl phi psi) (~ |- Impl phi psi).
Proof.
  destruct Dpsi as [Hpsi | Hnpsi].
  - left. exact (MP _ _ (Ax_K psi phi) Hpsi).
  - right. intro Himp. apply Hnpsi. exact (MP _ _ Himp Hphi).
Defined.

(** ** Decidability for [Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2)]
    when [psi_2] is provable: the consequent is provable, so the implication
    is provable by [Ax_K]. *)

Definition glp_decide_impl_iter_box_via_consequent_provable
  (ns_1 ns_2 : list nat) (psi_1 psi_2 : Form)
  (Hp_2 : |- psi_2) :
  sumbool (|- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2))
          (~ |- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2)).
Proof.
  left.
  exact (MP _ _ (Ax_K _ (iter_box ns_1 psi_1))
                (provable_iter_box_intro ns_2 psi_2 Hp_2)).
Defined.

(** ** Decidability for [Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2)]
    when [psi_1] is provable but [psi_2] is not (with [psi_2] closed
    box-free): the antecedent is provable and consequent is not, so
    the implication cannot be provable (would yield [|- iter_box ns_2 psi_2]
    via MP, contradicting [~ |- psi_2] under [provable_iter_box_box_free_iff]). *)

Definition glp_decide_impl_iter_box_via_antecedent_provable_consequent_not
  (ns_1 ns_2 : list nat) (psi_1 psi_2 : Form)
  (Hcl_2 : free_vars psi_2 = []) (Hbf_2 : box_free psi_2)
  (Hp_1 : |- psi_1) (Hnp_2 : ~ |- psi_2) :
  sumbool (|- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2))
          (~ |- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2)).
Proof.
  right. intro Himp. apply Hnp_2.
  apply (proj1 (provable_iter_box_box_free_iff ns_2 psi_2 Hcl_2 Hbf_2)).
  apply (MP _ _ Himp).
  exact (provable_iter_box_intro ns_1 psi_1 Hp_1).
Defined.

(** ** [And] of two iterated-box closed-box-free formulas: provable iff both
    inner formulas are classically valid. *)

Definition glp_decide_and_iter_box_box_free
  (ns_1 ns_2 : list nat) (psi_1 psi_2 : Form)
  (Hcl_1 : free_vars psi_1 = []) (Hbf_1 : box_free psi_1)
  (Hcl_2 : free_vars psi_2 = []) (Hbf_2 : box_free psi_2) :
  sumbool (|- And (iter_box ns_1 psi_1) (iter_box ns_2 psi_2))
          (~ |- And (iter_box ns_1 psi_1) (iter_box ns_2 psi_2)).
Proof.
  apply glp_decide_and.
  - exact (glp_decide_iter_box_closed_box_free ns_1 psi_1 Hcl_1 Hbf_1).
  - exact (glp_decide_iter_box_closed_box_free ns_2 psi_2 Hcl_2 Hbf_2).
Defined.

(** ** [Iff] of two iterated-box closed-box-free formulas: each direction
    is decidable when one of the cases (valid consequent, or
    valid antecedent + invalid consequent) applies. *)

(** ** [forces_fnat_closed (Box k Bot)] reduces to [Nat.leb w k]. *)

Lemma forces_box_bot_eq_leb : forall k w,
  forces_fnat_closed (Box k Bot) w = Nat.leb w k.
Proof.
  intros k w. cbn.
  destruct (Nat.leb w k) eqn:Eq.
  - apply Nat.leb_le in Eq.
    assert (Hempty : seq k (w - k) = []).
    { assert (w - k = 0) by lia. rewrite H. reflexivity. }
    rewrite Hempty. reflexivity.
  - apply Nat.leb_nle in Eq.
    destruct (forallb _ _) eqn:Efb; [|reflexivity].
    rewrite forallb_forall in Efb.
    assert (Hin : In k (seq k (w - k))).
    { apply in_seq. lia. }
    pose proof (Efb k Hin) as H. cbn in H. discriminate.
Qed.

(** ** [Impl (Box k_1 Bot) (Box k_2 Bot)] decidable: provable iff [k_1 <= k_2]. *)

Lemma decide_impl_box_bot_box_bot_le : forall k_1 k_2,
  k_1 <= k_2 -> |- Impl (Box k_1 Bot) (Box k_2 Bot).
Proof.
  intros k_1 k_2 Hle. exact (prov_box_mon_le k_1 k_2 Bot Hle).
Qed.

Lemma decide_impl_box_bot_box_bot_gt : forall k_1 k_2,
  k_1 > k_2 -> ~ |- Impl (Box k_1 Bot) (Box k_2 Bot).
Proof.
  intros k_1 k_2 Hgt Hp.
  pose proof (soundness _ Hp Fnat (fun _ _ => true) (S k_2)) as Hf.
  cbn in Hf.
  assert (Hk1 : forall v, Fnat_R k_1 (S k_2) v -> False).
  { intros v Hr. unfold Fnat_R in Hr. lia. }
  apply (Hf (fun v Hr => False_ind _ (Hk1 v Hr)) k_2).
  unfold Fnat_R. split; lia.
Qed.

Definition glp_decide_impl_box_bot_box_bot (k_1 k_2 : nat) :
  sumbool (|- Impl (Box k_1 Bot) (Box k_2 Bot))
          (~ |- Impl (Box k_1 Bot) (Box k_2 Bot)).
Proof.
  destruct (le_gt_dec k_1 k_2) as [Hle | Hgt].
  - left. exact (decide_impl_box_bot_box_bot_le k_1 k_2 Hle).
  - right. exact (decide_impl_box_bot_box_bot_gt k_1 k_2 Hgt).
Defined.

(** ** Eval of closed box-free formulas is independent of the valuation. *)

Lemma eval_box_free_closed_const : forall phi val_1 val_2,
  free_vars phi = [] -> box_free phi ->
  eval val_1 phi = eval val_2 phi.
Proof.
  intros phi val_1 val_2 Hcl Hbf.
  rewrite <- (forces_fnat_closed_box_free_eq_eval phi Hcl Hbf 0 val_1).
  rewrite <- (forces_fnat_closed_box_free_eq_eval phi Hcl Hbf 0 val_2).
  reflexivity.
Qed.

(** ** For closed box-free [psi], unprovability implies provability of [Neg psi]. *)

Lemma not_provable_implies_provable_neg_closed_box_free : forall psi,
  free_vars psi = [] -> box_free psi -> ~ |- psi -> |- Neg psi.
Proof.
  intros psi Hcl Hbf Hnp.
  apply trivial_in_provable. apply prop_completeness.
  - cbn. split; [exact Hbf | exact I].
  - intro val. cbn.
    destruct (eval val psi) eqn:E.
    + exfalso. apply Hnp.
      apply trivial_in_provable.
      apply prop_completeness; [exact Hbf|].
      intro val'.
      pose proof (eval_box_free_closed_const psi val' val Hcl Hbf) as Heq.
      rewrite Heq. exact E.
    + reflexivity.
Qed.

(** ** When [|- Neg psi], [Box k psi] is provably equivalent to [Box k Bot]. *)

Lemma box_psi_iff_box_bot_when_neg_provable : forall k psi,
  |- Neg psi -> |- Iff (Box k psi) (Box k Bot).
Proof.
  intros k psi Hneg.
  apply prov_iff_intro.
  - exact (MP _ _ (Ax_BoxK k psi Bot) (Nec k _ Hneg)).
  - exact (MP _ _ (Ax_BoxK k Bot psi) (Nec k _ (prov_explosion psi))).
Qed.

(** ** Decidability of [Impl (Box k_1 psi) (Box k_2 psi)] for closed box-free
    [psi].  Provable iff [|- psi] OR [k_1 <= k_2]; refuted by Fnat-soundness
    when [psi] is unprovable and [k_1 > k_2]. *)

Definition glp_decide_impl_box_box_box_free_same_psi
  (k_1 k_2 : nat) (psi : Form)
  (Hcl : free_vars psi = []) (Hbf : box_free psi) :
  sumbool (|- Impl (Box k_1 psi) (Box k_2 psi))
          (~ |- Impl (Box k_1 psi) (Box k_2 psi)).
Proof.
  destruct (glp_decide_closed_box_free psi Hcl Hbf) as [Hp | Hnp].
  - left. exact (MP _ _ (Ax_K (Box k_2 psi) (Box k_1 psi)) (Nec k_2 psi Hp)).
  - destruct (le_gt_dec k_1 k_2) as [Hle | Hgt].
    + left. exact (prov_box_mon_le k_1 k_2 psi Hle).
    + right. intro Himp.
      pose proof (soundness _ Himp Fnat (fun _ _ => true) (S k_2)) as Hf.
      cbn in Hf.
      assert (Hbox1 : forall v, Fnat_R k_1 (S k_2) v ->
                       forces Fnat (fun _ _ => true) v psi).
      { intros v Hr. unfold Fnat_R in Hr. lia. }
      pose proof (Hf Hbox1) as Hbox2.
      assert (Hr : Fnat_R k_2 (S k_2) k_2) by (unfold Fnat_R; split; lia).
      pose proof (Hbox2 k_2 Hr) as Hpsi_at_k2.
      apply Hnp.
      apply trivial_in_provable.
      apply prop_completeness; [exact Hbf|].
      intro val.
      apply (proj1 (forces_const_box_free Fnat (fun _ : nat => true) k_2 psi Hbf))
        in Hpsi_at_k2.
      pose proof (eval_box_free_closed_const psi val (fun _ => true) Hcl Hbf) as Heq.
      rewrite Heq. exact Hpsi_at_k2.
Defined.

(** ** When [psi] is closed box-free and classically refutable, the iterated
    box [iter_box ns psi] forces in Fnat at exactly the worlds [v < bad_world ns]. *)

Lemma forces_iter_box_below_bad_world : forall ns psi val,
  free_vars psi = [] -> box_free psi -> eval val psi = false ->
  forall v, v < bad_world ns ->
  forces_fnat_closed (iter_box ns psi) v = true.
Proof.
  intro ns. induction ns as [|n rest IH]; intros psi val Hcl Hbf Heval v Hv.
  - cbn in Hv. lia.
  - cbn [iter_box bad_world] in *.
    cbn [forces_fnat_closed].
    apply forallb_forall. intros u Hu.
    apply in_seq in Hu. destruct Hu as [Hun Huv].
    apply (IH psi val Hcl Hbf Heval).
    lia.
Qed.

(** ** [forces_fnat_closed (iter_box ns Bot) v = true] iff [v < bad_world ns]. *)

Lemma forces_iter_box_bot_eq_ltb : forall ns v,
  forces_fnat_closed (iter_box ns Bot) v = Nat.ltb v (bad_world ns).
Proof.
  intros ns v.
  destruct (Nat.ltb v (bad_world ns)) eqn:Eq.
  - apply Nat.ltb_lt in Eq.
    apply (forces_iter_box_below_bad_world ns Bot (fun _ => false) eq_refl I eq_refl v Eq).
  - apply Nat.ltb_nlt in Eq.
    rewrite (forces_iter_box_at_bad_world ns Bot (fun _ => false) eq_refl I v); [|lia].
    reflexivity.
Qed.

(** ** Forward direction of the iter-box-Bot implication theorem:
    [|- (iter_box ns_1 Bot) -> (iter_box ns_2 Bot)] entails
    [bad_world ns_1 <= bad_world ns_2]. *)

Theorem provable_impl_iter_box_bot_forward : forall ns_1 ns_2,
  |- Impl (iter_box ns_1 Bot) (iter_box ns_2 Bot) ->
  bad_world ns_1 <= bad_world ns_2.
Proof.
  intros ns_1 ns_2 Hp.
  destruct (le_gt_dec (bad_world ns_1) (bad_world ns_2)) as [Hle | Hgt]; [exact Hle|].
  exfalso.
  assert (Hcl_impl : free_vars (Impl (iter_box ns_1 Bot) (iter_box ns_2 Bot)) = []).
  { cbn. rewrite (iter_box_closed ns_1 Bot eq_refl).
    exact (iter_box_closed ns_2 Bot eq_refl). }
  pose proof (provable_implies_forces_fnat_closed
                (Impl (iter_box ns_1 Bot) (iter_box ns_2 Bot))
                (bad_world ns_2) Hcl_impl Hp) as Hf.
  cbn [forces_fnat_closed] in Hf.
  rewrite forces_iter_box_bot_eq_ltb in Hf.
  rewrite forces_iter_box_bot_eq_ltb in Hf.
  assert (Hlt : Nat.ltb (bad_world ns_2) (bad_world ns_1) = true)
    by (apply Nat.ltb_lt; lia).
  assert (Hge : Nat.ltb (bad_world ns_2) (bad_world ns_2) = false)
    by (apply Nat.ltb_nlt; lia).
  rewrite Hlt, Hge in Hf. cbn in Hf. discriminate.
Qed.

(** ** Empty antecedent case is trivial via [Bot] explosion. *)

Lemma provable_impl_iter_box_bot_backward_empty : forall ns_2,
  |- Impl (iter_box [] Bot) (iter_box ns_2 Bot).
Proof.
  intros ns_2. cbn. exact (prov_explosion (iter_box ns_2 Bot)).
Qed.

(** ** Iterated [Mon] lift inside an iter-box wrapper. *)

Lemma provable_iter_box_mon_le : forall n m psi,
  n <= m -> |- Impl (iter_box [n] psi) (iter_box [m] psi).
Proof.
  intros n m psi Hle. cbn. exact (prov_box_mon_le n m psi Hle).
Qed.

(** ** Provable explosion under [Box]: if the inner antecedent is [Bot],
    the consequent of the box-implication can be anything at the same level. *)

Lemma prov_box_bot_to_box_anything : forall n psi,
  |- Impl (Box n Bot) (Box n psi).
Proof.
  intros n psi.
  pose proof (prov_explosion psi) as Hexp.
  pose proof (Nec n _ Hexp) as Hbox_exp.
  pose proof (Ax_BoxK n Bot psi) as HK.
  exact (MP _ _ HK Hbox_exp).
Qed.

(** ** Lifting [Box n Bot] to [Box m psi] when [n <= m]. *)

Lemma prov_box_bot_to_higher_box_anything : forall n m psi,
  n <= m -> |- Impl (Box n Bot) (Box m psi).
Proof.
  intros n m psi Hle.
  pose proof (prov_box_mon_le n m Bot Hle) as Hmon.
  pose proof (prov_box_bot_to_box_anything m psi) as Hexp.
  exact (prov_compose _ _ _ Hmon Hexp).
Qed.

(** ** Singleton-antecedent backward direction.  When the head of [ns_2]
    dominates [k], the entire iter-box-Bot implication is provable directly
    by [prov_box_bot_to_higher_box_anything].  This is a special case of the
    Beklemishev worm theorem, sufficient when the consequent worm absorbs
    the antecedent at its outermost layer. *)

Lemma provable_impl_box_bot_iter_box_bot_head_match :
  forall k m rest, k <= m ->
  |- Impl (Box k Bot) (iter_box (m :: rest) Bot).
Proof.
  intros k m rest Hle. cbn [iter_box].
  exact (prov_box_bot_to_higher_box_anything k m (iter_box rest Bot) Hle).
Qed.

(** ** Pointwise monotonicity for iter-box: if [ns_1] and [ns_2] have the
    same length and [ns_1[i] <= ns_2[i]] pointwise, the worm-implication
    follows from iterated [Mon] under [Nec]+[BoxK]. *)

Lemma prov_iter_box_pointwise_mon : forall ns_1 ns_2 psi,
  length ns_1 = length ns_2 ->
  (forall i, i < length ns_1 -> nth i ns_1 0 <= nth i ns_2 0) ->
  |- Impl (iter_box ns_1 psi) (iter_box ns_2 psi).
Proof.
  intro ns_1. induction ns_1 as [|n rest_1 IH]; intros ns_2 psi Hlen Hpt.
  - destruct ns_2 as [|m rest_2]; [|cbn in Hlen; discriminate Hlen].
    cbn. exact (prov_id psi).
  - destruct ns_2 as [|m rest_2]; [cbn in Hlen; discriminate Hlen|].
    cbn [length] in Hlen. injection Hlen as Hlen.
    assert (Hhead : n <= m).
    { apply (Hpt 0). cbn [length]. lia. }
    assert (Hrest_pt : forall i, i < length rest_1 -> nth i rest_1 0 <= nth i rest_2 0).
    { intros i Hi. apply (Hpt (S i)). cbn [length]. lia. }
    pose proof (IH rest_2 psi Hlen Hrest_pt) as Hinner.
    pose proof (Nec m _ Hinner) as Hboxed.
    pose proof (Ax_BoxK m (iter_box rest_1 psi) (iter_box rest_2 psi)) as HK.
    pose proof (MP _ _ HK Hboxed) as Hstep.
    pose proof (prov_box_mon_le n m (iter_box rest_1 psi) Hhead) as Hmon.
    cbn [iter_box].
    exact (prov_compose _ _ _ Hmon Hstep).
Qed.

(** ** Strengthening the inner formula under an iter-box wrapper.  Since
    [Bot] is the strongest closed antecedent, [|- iter_box ns Bot ->
    iter_box ns psi] for any [psi]: explosion at the leaf, lifted through
    the wrapper by [Nec] and [BoxK]. *)

Lemma prov_iter_box_inner_strengthen : forall ns psi,
  |- Impl (iter_box ns Bot) (iter_box ns psi).
Proof.
  intro ns. induction ns as [|n rest IH]; intro psi.
  - cbn. exact (prov_explosion psi).
  - cbn [iter_box].
    pose proof (IH psi) as Hinner.
    pose proof (Nec n _ Hinner) as Hboxed.
    pose proof (Ax_BoxK n (iter_box rest Bot) (iter_box rest psi)) as HK.
    exact (MP _ _ HK Hboxed).
Qed.

(** ** Worm-extension case.  Appending an extension to a worm preserves
    provability of the worm-implication: [|- iter_box ns Bot ->
    iter_box (ns ++ ext) Bot].  Follows from
    [iter_box (ns ++ ext) Bot = iter_box ns (iter_box ext Bot)] and
    [prov_iter_box_inner_strengthen]. *)

Lemma iter_box_app : forall ns_1 ns_2 psi,
  iter_box (ns_1 ++ ns_2) psi = iter_box ns_1 (iter_box ns_2 psi).
Proof.
  intro ns_1. induction ns_1 as [|n rest IH]; intros ns_2 psi.
  - cbn. reflexivity.
  - cbn [iter_box app]. rewrite IH. reflexivity.
Qed.

Lemma prov_iter_box_extension : forall ns ext,
  |- Impl (iter_box ns Bot) (iter_box (ns ++ ext) Bot).
Proof.
  intros ns ext. rewrite iter_box_app. exact (prov_iter_box_inner_strengthen ns (iter_box ext Bot)).
Qed.

(** ** Combined head-lift + worm-extension.  When [ns_1] is a "weakening"
    of a prefix of [ns_2] (both pointwise [<=] on the prefix and [ns_2] has
    additional boxes appended), the worm-implication is provable. *)

Lemma prov_iter_box_prefix_mon_extension : forall ns_1 prefix ext psi,
  length ns_1 = length prefix ->
  (forall i, i < length ns_1 -> nth i ns_1 0 <= nth i prefix 0) ->
  |- Impl (iter_box ns_1 Bot) (iter_box (prefix ++ ext) psi).
Proof.
  intros ns_1 prefix ext psi Hlen Hpt.
  pose proof (prov_iter_box_pointwise_mon ns_1 prefix Bot Hlen Hpt) as Hmon.
  rewrite iter_box_app.
  pose proof (prov_iter_box_inner_strengthen prefix (iter_box ext psi)) as Hstr.
  exact (prov_compose _ _ _ Hmon Hstr).
Qed.

(** ** Witness extraction from a [false] [forallb]. *)

Lemma forallb_false_witness : forall {A : Type} (f : A -> bool) (l : list A),
  forallb f l = false -> exists x, In x l /\ f x = false.
Proof.
  intros A f. induction l as [|x rest IH]; intro Hfb.
  - cbn in Hfb. discriminate Hfb.
  - cbn in Hfb. destruct (f x) eqn:Ef.
    + cbn in Hfb. destruct (IH Hfb) as [y [Hy_in Hy_f]].
      exists y. split; [right; exact Hy_in | exact Hy_f].
    + exists x. split; [left; reflexivity | exact Ef].
Qed.

(** ** Stabilization bound for closed [forces_fnat_closed].  Beyond [wbound
    phi], [forces_fnat_closed phi w] is constant (in [w]).  This gives a
    finite-window refutation: any closed Form refutable by [Fnat] is
    refutable by checking [w in [0, wbound phi]]. *)

Fixpoint wbound (phi : Form) : nat :=
  match phi with
  | Var _ => 0
  | Bot => 0
  | Impl X Y => Nat.max (wbound X) (wbound Y)
  | Box n psi => S (Nat.max n (wbound psi))
  end.

Lemma forces_fnat_closed_stabilizes : forall phi w_1 w_2,
  free_vars phi = [] ->
  w_1 >= wbound phi -> w_2 >= wbound phi ->
  forces_fnat_closed phi w_1 = forces_fnat_closed phi w_2.
Proof.
  intro phi.
  induction phi as [k | | X IHX Y IHY | n psi IHpsi];
    intros w_1 w_2 Hcl Hw1 Hw2.
  - cbn in Hcl. discriminate Hcl.
  - cbn. reflexivity.
  - cbn in Hcl. apply app_eq_nil in Hcl. destruct Hcl as [HclX HclY].
    cbn in Hw1, Hw2.
    assert (Hw1X : w_1 >= wbound X) by lia.
    assert (Hw1Y : w_1 >= wbound Y) by lia.
    assert (Hw2X : w_2 >= wbound X) by lia.
    assert (Hw2Y : w_2 >= wbound Y) by lia.
    cbn. rewrite (IHX w_1 w_2 HclX Hw1X Hw2X), (IHY w_1 w_2 HclY Hw1Y Hw2Y).
    reflexivity.
  - cbn in Hcl. cbn in Hw1, Hw2. cbn [forces_fnat_closed].
    destruct (forallb (fun v => forces_fnat_closed psi v) (seq n (w_1 - n))) eqn:Eb1;
      destruct (forallb (fun v => forces_fnat_closed psi v) (seq n (w_2 - n))) eqn:Eb2;
      try reflexivity; exfalso.
    + (* Eb1 = true, Eb2 = false: produce a witness in seq_w_2 violating, derive contradiction with Eb1. *)
      destruct (forallb_false_witness _ _ Eb2) as [v [Hin Hf]].
      apply in_seq in Hin. destruct Hin as [Hvn Hvw2].
      rewrite forallb_forall in Eb1.
      destruct (le_gt_dec (wbound psi) v) as [Hvge | Hvlt].
      * (* v >= wbound psi: stabilize via [max n (wbound psi)]. *)
        assert (Hin_max : In (Nat.max n (wbound psi)) (seq n (w_1 - n))) by (apply in_seq; lia).
        pose proof (Eb1 _ Hin_max) as Hf_max.
        assert (Hbnd_max : Nat.max n (wbound psi) >= wbound psi) by lia.
        pose proof (IHpsi (Nat.max n (wbound psi)) v Hcl Hbnd_max Hvge) as Heq.
        rewrite Heq in Hf_max. rewrite Hf in Hf_max. discriminate.
      * (* v < wbound psi: then v < w_1, so [v ∈ seq n (w_1 - n)]. *)
        assert (Hv_in_w1 : In v (seq n (w_1 - n))) by (apply in_seq; lia).
        pose proof (Eb1 _ Hv_in_w1) as Hf_at_v. rewrite Hf in Hf_at_v. discriminate.
    + (* Eb1 = false, Eb2 = true: symmetric. *)
      destruct (forallb_false_witness _ _ Eb1) as [v [Hin Hf]].
      apply in_seq in Hin. destruct Hin as [Hvn Hvw1].
      rewrite forallb_forall in Eb2.
      destruct (le_gt_dec (wbound psi) v) as [Hvge | Hvlt].
      * assert (Hin_max : In (Nat.max n (wbound psi)) (seq n (w_2 - n))) by (apply in_seq; lia).
        pose proof (Eb2 _ Hin_max) as Hf_max.
        assert (Hbnd_max : Nat.max n (wbound psi) >= wbound psi) by lia.
        pose proof (IHpsi (Nat.max n (wbound psi)) v Hcl Hbnd_max Hvge) as Heq.
        rewrite Heq in Hf_max. rewrite Hf in Hf_max. discriminate.
      * assert (Hv_in_w2 : In v (seq n (w_2 - n))) by (apply in_seq; lia).
        pose proof (Eb2 _ Hv_in_w2) as Hf_at_v. rewrite Hf in Hf_at_v. discriminate.
Qed.

(** ** Bounded-window characterization of universal [Fnat] validity. *)

Theorem forces_fnat_closed_universal_iff_bounded : forall phi,
  free_vars phi = [] ->
  ((forall w, forces_fnat_closed phi w = true) <->
   (forall w, w <= wbound phi -> forces_fnat_closed phi w = true)).
Proof.
  intros phi Hcl. split.
  - intros Hall w _. exact (Hall w).
  - intros Hbnd w. destruct (le_gt_dec w (wbound phi)) as [Hle | Hgt].
    + exact (Hbnd w Hle).
    + assert (Hwbnd : wbound phi >= wbound phi) by lia.
      assert (Hwgt : w >= wbound phi) by lia.
      rewrite (forces_fnat_closed_stabilizes phi w (wbound phi) Hcl Hwgt Hwbnd).
      exact (Hbnd (wbound phi) (Nat.le_refl _)).
Qed.

(** ** Bounded refutation: a closed [phi] with [forces_fnat_closed phi w =
    false] for some [w in [0, wbound phi]] is unprovable.  Sound but not
    complete: not every Fnat-valid closed [phi] is provable in GLP*. *)

Theorem closed_refutation_via_fnat : forall phi w,
  free_vars phi = [] -> w <= wbound phi ->
  forces_fnat_closed phi w = false -> ~ |- phi.
Proof.
  intros phi w Hcl _ Hf Hp.
  pose proof (provable_implies_forces_fnat_closed phi w Hcl Hp) as Hf'.
  rewrite Hf in Hf'. discriminate Hf'.
Qed.

(** ** Decidability of [forall w in [0, wbound phi], forces phi w = true].
    Bounded boolean check: returns [sumbool] indicating whether [phi] is
    Fnat-valid up to its stabilization threshold. *)

Lemma forces_bounded_decidable : forall phi,
  free_vars phi = [] ->
  sumbool (forall w, w <= wbound phi -> forces_fnat_closed phi w = true)
          (exists w, w <= wbound phi /\ forces_fnat_closed phi w = false).
Proof.
  intros phi Hcl.
  destruct (forallb (fun w => forces_fnat_closed phi w) (seq 0 (S (wbound phi)))) eqn:Eb.
  - left. intros w Hw.
    rewrite forallb_forall in Eb.
    apply Eb. apply in_seq. lia.
  - right.
    destruct (forallb_false_witness _ _ Eb) as [w [Hin Hf]].
    apply in_seq in Hin. destruct Hin as [_ Hwlt].
    exists w. split; [lia | exact Hf].
Qed.

(** ** Full decidability for [Impl (Box k_1 psi_1) (Box k_2 psi_2)] with
    closed box-free [psi_1, psi_2].  Four cases by the validity of each:
    (a) both valid: provable via Nec on [psi_2] then [Ax_K];
    (b) [psi_1] valid, [psi_2] not: refuted, since MP would give [|- psi_2];
    (c) [psi_1] not, [psi_2] valid: provable via Nec on [psi_2];
    (d) both not valid: each [Box k psi_i] is provably equivalent to
        [Box k Bot] (via [box_psi_iff_box_bot_when_neg_provable]), so the
        implication reduces to [Impl (Box k_1 Bot) (Box k_2 Bot)],
        decidable via [glp_decide_impl_box_bot_box_bot]. *)

Definition glp_decide_impl_box_box_box_free_general
  (k_1 k_2 : nat) (psi_1 psi_2 : Form)
  (Hcl_1 : free_vars psi_1 = []) (Hbf_1 : box_free psi_1)
  (Hcl_2 : free_vars psi_2 = []) (Hbf_2 : box_free psi_2) :
  sumbool (|- Impl (Box k_1 psi_1) (Box k_2 psi_2))
          (~ |- Impl (Box k_1 psi_1) (Box k_2 psi_2)).
Proof.
  destruct (glp_decide_closed_box_free psi_2 Hcl_2 Hbf_2) as [Hp2 | Hnp2].
  - (* psi_2 valid: |- Box k_2 psi_2 then Ax_K. *)
    left. exact (MP _ _ (Ax_K (Box k_2 psi_2) (Box k_1 psi_1)) (Nec k_2 psi_2 Hp2)).
  - destruct (glp_decide_closed_box_free psi_1 Hcl_1 Hbf_1) as [Hp1 | Hnp1].
    + (* psi_1 valid, psi_2 not: refuted via MP. *)
      right. intro Himp. apply Hnp2.
      apply (proj1 (provable_box_box_free_iff_provable k_2 psi_2 Hbf_2)).
      exact (MP _ _ Himp (Nec k_1 psi_1 Hp1)).
    + (* both not valid: reduce to [Impl (Box k_1 Bot) (Box k_2 Bot)]. *)
      pose proof (not_provable_implies_provable_neg_closed_box_free psi_1 Hcl_1 Hbf_1 Hnp1) as Hneg1.
      pose proof (not_provable_implies_provable_neg_closed_box_free psi_2 Hcl_2 Hbf_2 Hnp2) as Hneg2.
      pose proof (box_psi_iff_box_bot_when_neg_provable k_1 psi_1 Hneg1) as Hiff1.
      pose proof (box_psi_iff_box_bot_when_neg_provable k_2 psi_2 Hneg2) as Hiff2.
      destruct (glp_decide_impl_box_bot_box_bot k_1 k_2) as [HBot | HnBot].
      * left.
        pose proof (prov_and_elim_l_meta _ _ Hiff1) as Hf1.
        pose proof (prov_and_elim_r_meta _ _ Hiff2) as Hb2.
        pose proof (prov_compose _ _ _ Hf1 HBot) as Hstep1.
        exact (prov_compose _ _ _ Hstep1 Hb2).
      * right. intro Himp. apply HnBot.
        pose proof (prov_and_elim_r_meta _ _ Hiff1) as Hb1.
        pose proof (prov_and_elim_l_meta _ _ Hiff2) as Hf2.
        pose proof (prov_compose _ _ _ Hb1 Himp) as Hstep1.
        exact (prov_compose _ _ _ Hstep1 Hf2).
Defined.

(** ** When [|- Neg psi], lifting through [iter_box ns] preserves Iff with
    [iter_box ns Bot].  This is the reduction-to-worm step: classically
    refutable [psi] makes [iter_box ns psi] provably equivalent to a
    worm. *)

Lemma iter_box_psi_iff_iter_box_bot_when_neg_provable : forall ns psi,
  |- Neg psi -> |- Iff (iter_box ns psi) (iter_box ns Bot).
Proof.
  intro ns. induction ns as [|n rest IH]; intros psi Hneg.
  - cbn. apply prov_iff_intro.
    + exact Hneg.
    + exact (prov_explosion psi).
  - cbn [iter_box].
    pose proof (IH psi Hneg) as Hiff_inner.
    pose proof (prov_and_elim_l_meta _ _ Hiff_inner) as Hfwd.
    pose proof (prov_and_elim_r_meta _ _ Hiff_inner) as Hback.
    apply prov_iff_intro.
    + exact (MP _ _ (Ax_BoxK n (iter_box rest psi) (iter_box rest Bot))
                  (Nec n _ Hfwd)).
    + exact (MP _ _ (Ax_BoxK n (iter_box rest Bot) (iter_box rest psi))
                  (Nec n _ Hback)).
Qed.

(** ** Reduction-to-worm: for closed box-free [psi_1, psi_2] both
    classically refutable, the iter-box implication is provably equivalent
    to the iter-box-Bot worm-implication. *)

Theorem iter_box_iter_box_iff_worm_implication_when_both_neg :
  forall ns_1 ns_2 psi_1 psi_2,
  |- Neg psi_1 -> |- Neg psi_2 ->
  |- Iff (Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2))
        (Impl (iter_box ns_1 Bot) (iter_box ns_2 Bot)).
Proof.
  intros ns_1 ns_2 psi_1 psi_2 Hneg1 Hneg2.
  pose proof (iter_box_psi_iff_iter_box_bot_when_neg_provable ns_1 psi_1 Hneg1) as Hiff1.
  pose proof (iter_box_psi_iff_iter_box_bot_when_neg_provable ns_2 psi_2 Hneg2) as Hiff2.
  exact (prov_equiv_impl_cong _ _ _ _ Hiff1 Hiff2).
Qed.

(** ** Refutation case for the both-invalid sub-case via Fnat soundness on
    bad_world.  When [bad_world ns_1 > bad_world ns_2] and both [psi_i]
    are closed box-free + classically refutable, the implication is
    unprovable. *)

Theorem refute_impl_iter_box_iter_box_box_free_via_bad_world :
  forall ns_1 ns_2 psi_1 psi_2,
  free_vars psi_1 = [] -> box_free psi_1 ->
  free_vars psi_2 = [] -> box_free psi_2 ->
  ~ |- psi_1 -> ~ |- psi_2 ->
  bad_world ns_1 > bad_world ns_2 ->
  ~ |- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2).
Proof.
  intros ns_1 ns_2 psi_1 psi_2 Hcl1 Hbf1 Hcl2 Hbf2 Hnp1 Hnp2 Hgt Himp.
  pose proof (not_provable_implies_provable_neg_closed_box_free psi_1 Hcl1 Hbf1 Hnp1) as Hneg1.
  pose proof (not_provable_implies_provable_neg_closed_box_free psi_2 Hcl2 Hbf2 Hnp2) as Hneg2.
  pose proof (iter_box_iter_box_iff_worm_implication_when_both_neg ns_1 ns_2 psi_1 psi_2 Hneg1 Hneg2) as Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
  pose proof (MP _ _ Hfwd Himp) as Hworm.
  pose proof (provable_impl_iter_box_bot_forward ns_1 ns_2 Hworm) as Hle.
  lia.
Qed.

(** ** Decider for the iter-box implication when [psi_2] is classically
    valid: the consequent is provable, hence the implication is provable
    via [Ax_K]. *)

Definition glp_decide_impl_iter_box_iter_box_box_free_psi_2_valid
  (ns_1 ns_2 : list nat) (psi_1 psi_2 : Form)
  (Hcl_2 : free_vars psi_2 = []) (Hbf_2 : box_free psi_2)
  (Hp2 : |- psi_2) :
  sumbool (|- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2))
          (~ |- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2)) :=
  glp_decide_impl_iter_box_via_consequent_provable ns_1 ns_2 psi_1 psi_2 Hp2.

(** ** Decider when [psi_1] is valid and [psi_2] is invalid: the implication
    cannot hold, since [MP] would yield the (refutable) consequent. *)

Definition glp_decide_impl_iter_box_iter_box_box_free_psi_1_valid_psi_2_invalid
  (ns_1 ns_2 : list nat) (psi_1 psi_2 : Form)
  (Hcl_2 : free_vars psi_2 = []) (Hbf_2 : box_free psi_2)
  (Hp1 : |- psi_1) (Hnp2 : ~ |- psi_2) :
  sumbool (|- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2))
          (~ |- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2)) :=
  glp_decide_impl_iter_box_via_antecedent_provable_consequent_not
    ns_1 ns_2 psi_1 psi_2 Hcl_2 Hbf_2 Hp1 Hnp2.

(** ** Refutation when both are invalid and the bad_world ordering favors
    refutation. *)

Definition glp_decide_impl_iter_box_iter_box_box_free_both_invalid_refute
  (ns_1 ns_2 : list nat) (psi_1 psi_2 : Form)
  (Hcl_1 : free_vars psi_1 = []) (Hbf_1 : box_free psi_1)
  (Hcl_2 : free_vars psi_2 = []) (Hbf_2 : box_free psi_2)
  (Hnp1 : ~ |- psi_1) (Hnp2 : ~ |- psi_2)
  (Hgt : bad_world ns_1 > bad_world ns_2) :
  ~ |- Impl (iter_box ns_1 psi_1) (iter_box ns_2 psi_2) :=
  refute_impl_iter_box_iter_box_box_free_via_bad_world
    ns_1 ns_2 psi_1 psi_2 Hcl_1 Hbf_1 Hcl_2 Hbf_2 Hnp1 Hnp2 Hgt.

(** ** Empty-antecedent case for both-invalid: trivially provable since
    [psi_1] is provably equivalent to [Bot] under [|- Neg psi_1], so
    [iter_box [] psi_1 = psi_1] is equivalent to [Bot], from which
    everything follows by explosion. *)

Lemma provable_impl_psi_iter_box_psi_2_when_neg_psi_provable :
  forall psi_1 ns_2 psi_2,
  |- Neg psi_1 ->
  |- Impl psi_1 (iter_box ns_2 psi_2).
Proof.
  intros psi_1 ns_2 psi_2 Hneg.
  exact (prov_compose _ _ _ Hneg (prov_explosion (iter_box ns_2 psi_2))).
Qed.

Definition glp_decide_impl_psi_iter_box_psi_2_box_free
  (ns_2 : list nat) (psi_1 psi_2 : Form)
  (Hcl_1 : free_vars psi_1 = []) (Hbf_1 : box_free psi_1)
  (Hcl_2 : free_vars psi_2 = []) (Hbf_2 : box_free psi_2) :
  sumbool (|- Impl psi_1 (iter_box ns_2 psi_2))
          (~ |- Impl psi_1 (iter_box ns_2 psi_2)).
Proof.
  destruct (glp_decide_closed_box_free psi_2 Hcl_2 Hbf_2) as [Hp2 | Hnp2].
  - left.
    exact (MP _ _ (Ax_K (iter_box ns_2 psi_2) psi_1)
                  (provable_iter_box_intro ns_2 psi_2 Hp2)).
  - destruct (glp_decide_closed_box_free psi_1 Hcl_1 Hbf_1) as [Hp1 | Hnp1].
    + right. intro Himp.
      apply Hnp2.
      apply (proj1 (provable_iter_box_box_free_iff ns_2 psi_2 Hcl_2 Hbf_2)).
      exact (MP _ _ Himp Hp1).
    + left.
      pose proof (not_provable_implies_provable_neg_closed_box_free
                    psi_1 Hcl_1 Hbf_1 Hnp1) as Hneg1.
      exact (provable_impl_psi_iter_box_psi_2_when_neg_psi_provable
               psi_1 ns_2 psi_2 Hneg1).
Defined.

(** ** Full decidability for the special case [ns_1 = []]: when the
    antecedent has no outer boxes, classical analysis on [psi_1, psi_2]
    completely determines provability. *)

Definition glp_decide_impl_iter_box_empty_iter_box_box_free
  (ns_2 : list nat) (psi_1 psi_2 : Form)
  (Hcl_1 : free_vars psi_1 = []) (Hbf_1 : box_free psi_1)
  (Hcl_2 : free_vars psi_2 = []) (Hbf_2 : box_free psi_2) :
  sumbool (|- Impl (iter_box [] psi_1) (iter_box ns_2 psi_2))
          (~ |- Impl (iter_box [] psi_1) (iter_box ns_2 psi_2)) :=
  glp_decide_impl_psi_iter_box_psi_2_box_free
    ns_2 psi_1 psi_2 Hcl_1 Hbf_1 Hcl_2 Hbf_2.

(** ** [NextCon]-explosion at the outer level.  When the inner level [n] is
    strictly less than the outer level [m], the [Box m] of [Box n Bot]
    collapses to [Box m Bot]: at level [m], the consistency of level [n]
    (via [Ax_NextCon] lifted by [Mon]) refutes [Box n Bot], so MP yields
    [Box m Bot]. *)

Lemma prov_box_higher_box_lower_bot_to_box_higher_bot : forall n m,
  n < m -> |- Impl (Box m (Box n Bot)) (Box m Bot).
Proof.
  intros n m Hlt.
  pose proof (Ax_NextCon n) as Hnext.
  pose proof (prov_box_mon_le (S n) m (Neg (Box n Bot)) Hlt) as Hmon.
  pose proof (MP _ _ Hmon Hnext) as Hboxm_neg.
  pose proof (Ax_BoxK m (Box n Bot) Bot) as HK.
  exact (MP _ _ HK Hboxm_neg).
Qed.

(** ** Worm collapse for two-element worms with inner < outer.  This is the
    simplest non-trivial case of Beklemishev's worm reduction: when the
    second box-level is strictly less than the first, the worm collapses
    to its single-box form. *)

Theorem worm_two_element_collapse_inner_lt_outer : forall outer inner,
  inner < outer ->
  |- Iff (iter_box [outer; inner] Bot) (Box outer Bot).
Proof.
  intros outer inner Hlt. cbn [iter_box].
  apply prov_iff_intro.
  - exact (prov_box_higher_box_lower_bot_to_box_higher_bot inner outer Hlt).
  - exact (prov_box_bot_to_box_anything outer (Box inner Bot)).
Qed.

(** ** Provable [Impl (iter_box [outer; inner] Bot) (Box m Bot)] when
    [inner < outer] and [outer <= m].  Combines worm collapse with [Mon]. *)

Theorem provable_impl_iter_box_two_element_to_box_bot :
  forall outer inner m,
  inner < outer -> outer <= m ->
  |- Impl (iter_box [outer; inner] Bot) (Box m Bot).
Proof.
  intros outer inner m Hlt Hle.
  pose proof (worm_two_element_collapse_inner_lt_outer outer inner Hlt) as Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
  pose proof (prov_box_mon_le outer m Bot Hle) as Hmon.
  exact (prov_compose _ _ _ Hfwd Hmon).
Qed.

(** ** Provable [Impl (iter_box [outer; inner] Bot) (iter_box (m :: rest) Bot)]
    when [inner < outer] and [outer <= m].  Combines worm collapse with the
    box-bot-explosion route. *)

Theorem provable_impl_iter_box_two_element_to_iter_box :
  forall outer inner m rest,
  inner < outer -> outer <= m ->
  |- Impl (iter_box [outer; inner] Bot) (iter_box (m :: rest) Bot).
Proof.
  intros outer inner m rest Hlt Hle.
  pose proof (worm_two_element_collapse_inner_lt_outer outer inner Hlt) as Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
  pose proof (provable_impl_box_bot_iter_box_bot_head_match outer m rest Hle) as Hhead.
  exact (prov_compose _ _ _ Hfwd Hhead).
Qed.

(** ** Two cleanly-handled sub-cases for the worm-implication with a
    2-element collapsed antecedent: empty consequent (refute via the
    Carlson generalisation) and head-match consequent (provable via the
    collapse + head-match chain).  The remaining cases (consequent with
    head [m < outer] but inner structure rich enough to dominate) are
    gaps in the bad_world-only characterisation, so we expose
    these positive cases as separate lemmas rather than forcing a
    [sumbool] over an indeterminate domain. *)

Lemma worm_implication_two_element_collapsed_to_empty_unprovable :
  forall outer inner,
  inner < outer ->
  ~ |- Impl (iter_box [outer; inner] Bot) (iter_box [] Bot).
Proof.
  intros outer inner Hlt Himp.
  pose proof (worm_two_element_collapse_inner_lt_outer outer inner Hlt) as Hiff.
  pose proof (prov_and_elim_r_meta _ _ Hiff) as Hback.
  pose proof (prov_compose _ _ _ Hback Himp) as Hbox_outer_to_bot.
  exact (closed_neg_box_unprovable outer Bot eq_refl Hbox_outer_to_bot).
Qed.

(** ** Boolean prefix-mon check: Boolean predicate that is [true] iff
    [ns_2] starts with a length-[length ns_1] prefix that pointwise
    dominates [ns_1].  Yields a syntactic sufficient condition for
    worm-implication provability. *)

Fixpoint prefix_mon_le_b (ns_1 ns_2 : list nat) : bool :=
  match ns_1, ns_2 with
  | [], _ => true
  | _ :: _, [] => false
  | n :: rest_1, m :: rest_2 => andb (Nat.leb n m) (prefix_mon_le_b rest_1 rest_2)
  end.

Lemma prefix_mon_le_b_implies_split : forall ns_1 ns_2,
  prefix_mon_le_b ns_1 ns_2 = true ->
  exists prefix ext,
    ns_2 = prefix ++ ext /\
    length ns_1 = length prefix /\
    (forall i, i < length ns_1 -> nth i ns_1 0 <= nth i prefix 0).
Proof.
  intro ns_1. induction ns_1 as [|n rest_1 IH]; intros ns_2 Hb.
  - exists [], ns_2. split; [reflexivity | split; [reflexivity|]].
    intros i Hi. cbn in Hi. lia.
  - destruct ns_2 as [|m rest_2]; [discriminate Hb|].
    cbn in Hb. apply Bool.andb_true_iff in Hb. destruct Hb as [Hle Hrec].
    apply Nat.leb_le in Hle.
    destruct (IH rest_2 Hrec) as [prefix [ext [Heq [Hlen Hpt]]]].
    exists (m :: prefix), ext. split; [|split].
    + cbn. rewrite Heq. reflexivity.
    + cbn. rewrite Hlen. reflexivity.
    + intros i Hi. destruct i as [|i].
      * cbn. exact Hle.
      * cbn. cbn in Hi. apply Hpt. lia.
Qed.

(** ** Provable worm-implication from the Boolean prefix-mon check. *)

Theorem prefix_mon_le_b_implies_worm_provable : forall ns_1 ns_2,
  prefix_mon_le_b ns_1 ns_2 = true ->
  |- Impl (iter_box ns_1 Bot) (iter_box ns_2 Bot).
Proof.
  intros ns_1 ns_2 Hb.
  destruct (prefix_mon_le_b_implies_split ns_1 ns_2 Hb) as [prefix [ext [Heq [Hlen Hpt]]]].
  rewrite Heq.
  exact (prov_iter_box_prefix_mon_extension ns_1 prefix ext Bot Hlen Hpt).
Qed.

(** ** Decidability of the boolean prefix-mon check yields a [sumbool] for
    a structurally identifiable subset of provable worm implications.
    When the check fails, we cannot conclude unprovability in general
    (the Beklemishev worm theorem provides additional positive cases
    not captured by pointwise prefix mon). *)

Definition glp_decide_worm_implication_via_prefix_mon
  (ns_1 ns_2 : list nat) :
  sumbool (prefix_mon_le_b ns_1 ns_2 = true)
          (prefix_mon_le_b ns_1 ns_2 = false).
Proof.
  destruct (prefix_mon_le_b ns_1 ns_2) eqn:Eb.
  - left. reflexivity.
  - right. reflexivity.
Defined.

(** ** Full decision when the bad_world ordering FAILS: refute via the
    forward direction of the worm-implication theorem. *)

Definition glp_decide_worm_implication_via_bad_world
  (ns_1 ns_2 : list nat)
  (Hgt : bad_world ns_1 > bad_world ns_2) :
  ~ |- Impl (iter_box ns_1 Bot) (iter_box ns_2 Bot).
Proof.
  intro Himp.
  pose proof (provable_impl_iter_box_bot_forward ns_1 ns_2 Himp) as Hle.
  lia.
Defined.

(** ** Combined decision principle for worm implications: the [sumbool]
    holds when at least one of the two structural conditions decides:
    (a) prefix-mon check passes (provable), or
    (b) bad_world ordering fails (unprovable).  When neither decides,
    we cannot conclude with the present tools. *)

Definition glp_decide_worm_implication_via_structural_principles
  (ns_1 ns_2 : list nat) :
  sumbool (|- Impl (iter_box ns_1 Bot) (iter_box ns_2 Bot))
          (~ |- Impl (iter_box ns_1 Bot) (iter_box ns_2 Bot)) +
  ((prefix_mon_le_b ns_1 ns_2 = false) /\
   (bad_world ns_1 <= bad_world ns_2)).
Proof.
  destruct (glp_decide_worm_implication_via_prefix_mon ns_1 ns_2) as [Hpref | Hpref].
  - left. left. exact (prefix_mon_le_b_implies_worm_provable ns_1 ns_2 Hpref).
  - destruct (le_gt_dec (bad_world ns_1) (bad_world ns_2)) as [Hle | Hgt].
    + right. split; assumption.
    + left. right. exact (glp_decide_worm_implication_via_bad_world ns_1 ns_2 Hgt).
Defined.

(** ** Free-variable extension for box-free [iter_box].  For arbitrary
    [psi] (closed or open) that is box-free, [|- iter_box ns psi] iff
    [psi] is classically valid (true under every Boolean valuation).
    This generalises [provable_iter_box_box_free_iff] to forms with free
    variables, leveraging [prop_completeness] (which works in the
    box-free fragment regardless of whether variables are present). *)

Lemma forces_iter_box_at_bad_world_const : forall ns psi val w,
  box_free psi ->
  w >= bad_world ns ->
  forces Fnat (fun _ => val) w (iter_box ns psi) ->
  eval val psi = true.
Proof.
  intro ns. induction ns as [|n rest IH]; intros psi val w Hbf Hw Hf.
  - cbn in Hf. apply (proj1 (forces_const_box_free Fnat val w psi Hbf)). exact Hf.
  - cbn in Hf. cbn in Hw.
    set (v := Nat.max n (bad_world rest)).
    assert (Hr : Fnat_R n w v).
    { unfold Fnat_R, v. lia. }
    pose proof (Hf v Hr) as Hinner.
    apply (IH psi val v Hbf).
    + unfold v. lia.
    + exact Hinner.
Qed.

Theorem provable_iter_box_box_free_iff_classical_valid : forall ns psi,
  box_free psi ->
  (|- iter_box ns psi <-> classical_valid psi).
Proof.
  intros ns psi Hbf. unfold classical_valid. split.
  - intros Hp val.
    pose proof (soundness _ Hp Fnat (fun _ => val) (bad_world ns)) as Hf.
    exact (forces_iter_box_at_bad_world_const ns psi val (bad_world ns)
             Hbf (Nat.le_refl _) Hf).
  - intros Hval.
    pose proof (prop_completeness psi Hbf Hval) as Hpp.
    pose proof (trivial_in_provable psi Hpp) as Hp.
    exact (provable_iter_box_intro ns psi Hp).
Qed.

(** ** Decision procedure for [iter_box ns psi] with general (open)
    box-free [psi].  Uses [decide_tautology] for the underlying classical
    decision. *)

Definition glp_decide_iter_box_box_free (ns : list nat) (psi : Form)
  (Hbf : box_free psi) :
  sumbool (|- iter_box ns psi) (~ |- iter_box ns psi).
Proof.
  destruct (decide_tautology psi) eqn:Edt.
  - left.
    apply (proj2 (provable_iter_box_box_free_iff_classical_valid ns psi Hbf)).
    apply decide_tautology_correct. exact Edt.
  - right.
    intro Hp.
    pose proof (proj1 (provable_iter_box_box_free_iff_classical_valid ns psi Hbf) Hp) as Hval.
    pose proof (decide_tautology_complete psi Hval) as Edt'.
    rewrite Edt in Edt'. discriminate.
Defined.

(** ** Full decision procedure for the entire box-free fragment, open or
    closed: [|- phi] iff [phi] is classically valid.  This is just
    [decide_tautology] wrapped as a [sumbool]. *)

Definition glp_decide_box_free (phi : Form) (Hbf : box_free phi) :
  sumbool (|- phi) (~ |- phi).
Proof.
  destruct (decide_tautology phi) eqn:Edt.
  - left. apply trivial_in_provable. apply prop_completeness; [exact Hbf|].
    apply decide_tautology_correct. exact Edt.
  - right. intro Hp.
    pose proof (eval_provable_true) as Heval.
    pose proof (decide_tautology_complete phi (fun val => Heval val phi Hp)) as Edt'.
    rewrite Edt in Edt'. discriminate.
Defined.

(** ** Boolean version of [box_free]. *)

Fixpoint box_free_b (phi : Form) : bool :=
  match phi with
  | Var _ => true
  | Bot => true
  | Impl X Y => andb (box_free_b X) (box_free_b Y)
  | Box _ _ => false
  end.

Lemma box_free_b_iff : forall phi,
  box_free_b phi = true <-> box_free phi.
Proof.
  intro phi. induction phi as [k | | X IHX Y IHY | n psi IHpsi]; cbn.
  - tauto.
  - tauto.
  - rewrite Bool.andb_true_iff. rewrite IHX, IHY. reflexivity.
  - split; [discriminate | intros []].
Qed.

(** ** Decomposition: every formula factors as [iter_box ns psi] where
    [psi] is the result of stripping all outermost [Box] layers and [ns]
    collects the box levels. *)

Fixpoint extract_box_levels (phi : Form) : list nat :=
  match phi with
  | Box n psi => n :: extract_box_levels psi
  | _ => []
  end.

Fixpoint extract_inner_form (phi : Form) : Form :=
  match phi with
  | Box _ psi => extract_inner_form psi
  | _ => phi
  end.

Lemma extract_decomposition : forall phi,
  phi = iter_box (extract_box_levels phi) (extract_inner_form phi).
Proof.
  intro phi. induction phi as [k | | X IHX Y IHY | n psi IHpsi]; cbn; try reflexivity.
  rewrite <- IHpsi at 1. reflexivity.
Qed.

Lemma extract_inner_form_no_outer_box : forall phi,
  match extract_inner_form phi with Box _ _ => False | _ => True end.
Proof.
  intro phi. induction phi as [k | | X IHX Y IHY | n psi IHpsi]; cbn; auto; exact I.
Qed.

(** ** Boolean predicate identifying the sub-fragment for which we provide
    full decidability: a formula whose innermost (after stripping outer
    boxes) is box-free.  These are exactly the formulas of shape
    [iter_box ns psi] with box-free [psi]. *)

Definition is_iter_box_of_box_free (phi : Form) : bool :=
  box_free_b (extract_inner_form phi).

Lemma extract_inner_box_free : forall phi,
  is_iter_box_of_box_free phi = true -> box_free (extract_inner_form phi).
Proof.
  intros phi Hb. unfold is_iter_box_of_box_free in Hb.
  apply box_free_b_iff. exact Hb.
Qed.

(** ** Headline decidability for the [is_iter_box_of_box_free] fragment.
    Combined with [glp_decide_box_free] for the box-free part of the
    fragment, this yields a decision procedure for every formula whose
    syntactic shape strips to a box-free leaf. *)

Definition glp_decide_iter_box_of_box_free (phi : Form)
  (Hb : is_iter_box_of_box_free phi = true) :
  sumbool (|- phi) (~ |- phi).
Proof.
  rewrite (extract_decomposition phi).
  exact (glp_decide_iter_box_box_free
           (extract_box_levels phi)
           (extract_inner_form phi)
           (extract_inner_box_free phi Hb)).
Defined.

(** ** Iff-congruence under [Box].  A directional [Iff] under a single
    [Box] follows from [Nec] + [BoxK] applied componentwise. *)

Lemma iff_under_box : forall n phi psi,
  |- Iff phi psi ->
  |- Iff (Box n phi) (Box n psi).
Proof.
  intros n phi psi Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hf.
  pose proof (prov_and_elim_r_meta _ _ Hiff) as Hb.
  apply prov_iff_intro.
  - exact (MP _ _ (Ax_BoxK n phi psi) (Nec n _ Hf)).
  - exact (MP _ _ (Ax_BoxK n psi phi) (Nec n _ Hb)).
Qed.

(** ** Boolean check for strictly descending lists. *)

Fixpoint is_strictly_descending (ns : list nat) : bool :=
  match ns with
  | [] => true
  | [_] => true
  | a :: ((b :: _) as rest) => andb (Nat.ltb b a) (is_strictly_descending rest)
  end.

(** ** Iterated worm collapse for strictly descending sequences.  Each
    successive [(a, b, ...)] with [b < a] collapses [Box a (Box b ...)]
    to [Box a Bot] via iterated application of the 2-element collapse and
    [iff_under_box]. *)

Lemma prov_iff_trans : forall phi psi chi,
  |- Iff phi psi -> |- Iff psi chi -> |- Iff phi chi.
Proof.
  intros phi psi chi H1 H2.
  pose proof (prov_and_elim_l_meta _ _ H1) as H1f.
  pose proof (prov_and_elim_r_meta _ _ H1) as H1b.
  pose proof (prov_and_elim_l_meta _ _ H2) as H2f.
  pose proof (prov_and_elim_r_meta _ _ H2) as H2b.
  apply prov_iff_intro.
  - exact (prov_compose _ _ _ H1f H2f).
  - exact (prov_compose _ _ _ H2b H1b).
Qed.

Theorem worm_descending_collapse_to_head : forall n rest,
  is_strictly_descending (n :: rest) = true ->
  |- Iff (iter_box (n :: rest) Bot) (Box n Bot).
Proof.
  intros n rest. revert n. induction rest as [|m rest' IH]; intros n Hd.
  - cbn [iter_box]. apply prov_iff_refl.
  - cbn in Hd. apply Bool.andb_true_iff in Hd. destruct Hd as [Hlt Hd_rest].
    apply Nat.ltb_lt in Hlt.
    pose proof (IH m Hd_rest) as Hiff_inner.
    pose proof (iff_under_box n _ _ Hiff_inner) as Hiff_outer.
    cbn [iter_box] in Hiff_outer.
    pose proof (worm_two_element_collapse_inner_lt_outer n m Hlt) as Hcollapse.
    cbn [iter_box] in Hcollapse.
    cbn [iter_box].
    exact (prov_iff_trans _ _ _ Hiff_outer Hcollapse).
Qed.

(** ** Worm-implication via descending-collapse + head-match.  When the
    antecedent is strictly descending, it collapses to its head; if the
    head is dominated by the consequent's head, the implication is
    provable. *)

Theorem provable_impl_descending_iter_box_to_iter_box_via_head :
  forall n rest m rest_2,
  is_strictly_descending (n :: rest) = true ->
  n <= m ->
  |- Impl (iter_box (n :: rest) Bot) (iter_box (m :: rest_2) Bot).
Proof.
  intros n rest m rest_2 Hd Hle.
  pose proof (worm_descending_collapse_to_head n rest Hd) as Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
  pose proof (provable_impl_box_bot_iter_box_bot_head_match n m rest_2 Hle) as Hhead.
  exact (prov_compose _ _ _ Hfwd Hhead).
Qed.

(** ** Beklemishev-style absorption: when an iter-box-Bot has a sub-pattern
    [Box outer (Box inner ...)] with [inner < outer], the inner box can
    be absorbed.  Specifically, [Box outer (Box inner phi)] entails
    [Box outer Bot] when [inner < outer] AND [phi = Bot] — extending to
    the case [phi = iter_box rest Bot] requires that [rest] doesn't
    introduce new structure stronger than [Bot].  We capture the simplest
    productive case: a worm where the second level is strictly less than
    the first AND the remaining suffix is empty. *)

Lemma worm_two_element_bot_provable_iff_outer_bot : forall outer inner,
  inner < outer ->
  (|- iter_box [outer; inner] Bot <-> |- Box outer Bot).
Proof.
  intros outer inner Hlt.
  pose proof (worm_two_element_collapse_inner_lt_outer outer inner Hlt) as Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
  pose proof (prov_and_elim_r_meta _ _ Hiff) as Hback.
  split.
  - intro Hp. exact (MP _ _ Hfwd Hp).
  - intro Hp. exact (MP _ _ Hback Hp).
Qed.

(** ** A complete decidability statement for [iter_box [outer; inner] Bot]
    when [inner < outer]: the worm is provable iff [Box outer Bot] is,
    which is iff false (by [closed_fragment_iterated_bot_not_provable]). *)

Theorem worm_two_element_descending_unprovable : forall outer inner,
  inner < outer ->
  ~ |- iter_box [outer; inner] Bot.
Proof.
  intros outer inner Hlt Hp.
  apply (proj1 (worm_two_element_bot_provable_iff_outer_bot outer inner Hlt)) in Hp.
  exact (closed_fragment_iterated_bot_not_provable outer Hp).
Qed.

(** ** Same conclusion via the iterated-descending generalization: an
    iter-box-Bot worm with strictly descending box-levels collapses to its
    head's [Box n Bot], which is unprovable. *)

Theorem worm_descending_unprovable : forall n rest,
  is_strictly_descending (n :: rest) = true ->
  ~ |- iter_box (n :: rest) Bot.
Proof.
  intros n rest Hd Hp.
  pose proof (worm_descending_collapse_to_head n rest Hd) as Hiff.
  pose proof (prov_and_elim_l_meta _ _ Hiff) as Hfwd.
  pose proof (MP _ _ Hfwd Hp) as Hbox_n_bot.
  exact (closed_fragment_iterated_bot_not_provable n Hbox_n_bot).
Qed.

(** ** Decidability of unprovability for descending worms (paired with
    the existing positive results). *)

Definition glp_decide_descending_worm
  (n : nat) (rest : list nat)
  (Hd : is_strictly_descending (n :: rest) = true) :
  sumbool (|- iter_box (n :: rest) Bot) (~ |- iter_box (n :: rest) Bot).
Proof.
  right. exact (worm_descending_unprovable n rest Hd).
Defined.

(** ** Beklemishev-gap refutation for [Impl (Box k Bot) (Box 0 (Box m Bot))]
    when [m < k].  This is a corner case where Fnat is not directly able
    to refute, but a syntactic argument via [Mon] + the unprovability of
    [Box 0 (Box m Bot)] does the job.

    Approach: assume the implication is provable.  Then by the contrapositive
    direction of NextCon-derived equivalences, we should be able to derive
    something contradictory.  However, the gap remains in our axioms:
    we have [|- Box 0 (Box m Bot) -> Box (S m) Bot] (via Mon + NextCon route),
    so [Box 0 (Box m Bot)] is provably stronger than [Box (S m) Bot], and
    [Box (S m) Bot] is in turn implied by [Box k Bot] when [k <= S m].

    But for [m < k], we have [k > m], so [Box (S m) Bot -> Box k Bot] by
    [Mon] iff [S m <= k], i.e., [m < k].  Thus [Box 0 (Box m Bot) -> Box k Bot]
    is provable, but the reverse [Box k Bot -> Box 0 (Box m Bot)] is not
    derivable in our axiom system (it would require the unprovable
    "T_k inconsistent therefore T_0 proves T_m inconsistent"). *)

Lemma prov_box_0_box_m_bot_to_box_S_m_bot : forall m,
  |- Impl (Box 0 (Box m Bot)) (Box (S m) Bot).
Proof.
  intro m.
  pose proof (prov_box_mon_le 0 (S m) (Box m Bot)
                (Nat.le_0_l (S m))) as Hmon.
  pose proof (prov_box_higher_box_lower_bot_to_box_higher_bot m (S m)
                (Nat.lt_succ_diag_r m)) as Hcol.
  exact (prov_compose _ _ _ Hmon Hcol).
Qed.

(** ** When [|- Box k Bot -> Box 0 (Box m Bot)] holds AND [m < k] holds,
    we can chain to derive [|- Box k Bot -> Box (S m) Bot], which is not
    a direct contradiction.  But we also have [|- Box (S m) Bot -> Box k Bot]
    by [Mon] (when [S m <= k]), so the two are provably equivalent.

    Thus [|- Box k Bot -> Box 0 (Box m Bot)] iff [|- Box (S m) Bot -> Box 0 (Box m Bot)]
    (by chasing the chain).  Since [Box (S m) Bot] is derivable from
    [Box 0 (Box m Bot)] AND vice versa (provable equivalence in this direction)
    is the missing ingredient — only one direction of equivalence holds. *)

Lemma prov_iff_box_S_m_bot_box_0_box_m_bot_partial : forall m,
  |- Impl (Box 0 (Box m Bot)) (Box (S m) Bot).
Proof.
  exact prov_box_0_box_m_bot_to_box_S_m_bot.
Qed.

(** ** An Ignatiev-style 2-dimensional Kripke frame [I2] that refutes
    Beklemishev-gap formulas.  Worlds are pairs of naturals; [R_0] is the
    lex order, while [R_n] for [n >= 1] depends only on the first
    coordinate with a level-threshold.  This frame distinguishes formulas
    that Fnat collapses, since the second coordinate provides extra
    "depth" at each first-coordinate level. *)

Definition I2_R (n : nat) (w v : nat * nat) : Prop :=
  match n with
  | 0 => fst w > fst v \/ (fst w = fst v /\ snd w > snd v)
  | S k => fst w > fst v /\ fst v >= S k
  end.

Lemma I2_R_trans : forall n w v u, I2_R n w v -> I2_R n v u -> I2_R n w u.
Proof.
  intros [|k] [a b] [c d] [e f]; cbn.
  - intros [Hac | [Hac Hbd]] [Hce | [Hce Hdf]].
    + left. lia.
    + left. lia.
    + left. lia.
    + right. split; [lia | lia].
  - intros [Hac Hcn] [Hce Hen]. split; lia.
Qed.

Lemma I2_R_wf_helper :
  forall a b,
    Acc (fun v u : nat * nat =>
           fst u > fst v \/ (fst u = fst v /\ snd u > snd v)) (a, b).
Proof.
  induction a as [a IHa] using (well_founded_induction Wf_nat.lt_wf).
  intro b.
  induction b as [b IHb] using (well_founded_induction Wf_nat.lt_wf).
  apply Acc_intro. intros [c d] H.
  destruct H as [Hac | [Hac Hbd]].
  - cbn in Hac. apply (IHa c Hac).
  - cbn in Hac, Hbd. subst c.
    apply (IHb d Hbd).
Qed.

Lemma I2_R_wf : forall n, well_founded (fun u v : nat * nat => I2_R n v u).
Proof.
  intros [|k] [a b].
  - apply I2_R_wf_helper.
  - revert b.
    induction a as [a IHa] using (well_founded_induction Wf_nat.lt_wf).
    intro b. apply Acc_intro. intros [c d] [Hac _].
    cbn in Hac. apply (IHa c Hac).
Qed.

Lemma I2_R_mon : forall n w v, I2_R (S n) w v -> I2_R n w v.
Proof.
  intros [|k] [a b] [c d]; cbn.
  - intros [Hac _]. left. exact Hac.
  - intros [Hac Hcn]. split; [lia|lia].
Qed.

Lemma I2_R_nextcon : forall n w v, I2_R (S n) w v -> exists u, I2_R n v u.
Proof.
  intros [|k] [a b] [c d]; cbn.
  - intros [Hac Hcn].
    exists (c - 1, 0). cbn.
    left. lia.
  - intros [Hac Hcn].
    exists (S k, 0). cbn. split; [lia|lia].
Qed.

Definition I2 : Frame :=
  mkFrame (nat * nat) I2_R I2_R_trans I2_R_wf I2_R_mon I2_R_nextcon.

(** ** Concrete refutation: [|- Box 4 Bot -> Box 0 (Box 3 Bot)] is FALSE
    in GLP*.  The witness is [I2] at world [(4, 5)]. *)

Theorem refute_box_4_bot_implies_box_0_box_3_bot :
  ~ |- Impl (Box 4 Bot) (Box 0 (Box 3 Bot)).
Proof.
  intro Hp.
  pose proof (soundness _ Hp I2 (fun _ _ => false) (4, 5)) as Hf.
  cbn in Hf.
  assert (Hbox4 : forall v : nat * nat, I2_R 4 (4, 5) v -> False).
  { intros [c d] [Hac Hcn]. cbn in *. lia. }
  pose proof (Hf Hbox4) as Hbox0.
  pose proof (Hbox0 (4, 0)) as Hbox0'.
  assert (Hr0 : I2_R 0 (4, 5) (4, 0))
    by (cbn; right; split; [reflexivity | lia]).
  pose proof (Hbox0' Hr0) as Hbox3.
  apply (Hbox3 (3, 0)).
  cbn. split; [lia | lia].
Qed.

(** ** Generalised Beklemishev-gap refutation: for any [m < k], the
    formula [Box k Bot -> Box 0 (Box m Bot)] is unprovable.  The witness
    is [I2] at world [(S m, 1)]. *)

Theorem refute_box_k_bot_implies_box_0_box_m_bot : forall k m,
  m < k -> ~ |- Impl (Box k Bot) (Box 0 (Box m Bot)).
Proof.
  intros k m Hmk Hp.
  pose proof (soundness _ Hp I2 (fun _ _ => false) (S m, 1)) as Hf.
  cbn in Hf.
  assert (Hboxk : forall v : nat * nat, I2_R k (S m, 1) v -> False).
  { intros [c d]. destruct k as [|k']; cbn.
    - intros _. lia.
    - intros [Hac Hcn]. cbn in Hac, Hcn. lia. }
  pose proof (Hf Hboxk) as Hbox0.
  pose proof (Hbox0 (S m, 0)) as Hbox0'.
  assert (Hr0 : I2_R 0 (S m, 1) (S m, 0))
    by (cbn; right; split; [reflexivity | lia]).
  pose proof (Hbox0' Hr0) as Hboxm.
  destruct m as [|m']; cbn in Hboxm.
  - apply (Hboxm (0, 0)). cbn. left. lia.
  - apply (Hboxm (S m', 0)). cbn. split; [lia|lia].
Qed.

(** ** Bidirectional Lindenbaum gap: [Box (S m) Bot] does NOT imply
    [Box 0 (Box m Bot)] (refuted via I2), but the reverse direction
    does (provable via Mon + NextCon collapse).  Hence the two formulas
    are NOT provably equivalent in GLP*, despite being Fnat-equivalent. *)

Theorem reverse_implication_box_S_m_bot_box_0_box_m_bot_unprovable :
  forall m, ~ |- Impl (Box (S m) Bot) (Box 0 (Box m Bot)).
Proof.
  intro m.
  exact (refute_box_k_bot_implies_box_0_box_m_bot (S m) m (Nat.lt_succ_diag_r m)).
Qed.

(** ** Refutation of [Box k Bot -> Box 0 (Box 0 (Box m Bot))] via I2.
    Witness at [(S m, 2)].  This shows the I2 frame extends to
    refute deeper Beklemishev-gap formulas with multiple Box-0 layers. *)

Theorem refute_box_k_bot_implies_box_0_box_0_box_m_bot : forall k m,
  m < k -> ~ |- Impl (Box k Bot) (Box 0 (Box 0 (Box m Bot))).
Proof.
  intros k m Hmk Hp.
  pose proof (soundness _ Hp I2 (fun _ _ => false) (S m, 2)) as Hf.
  cbn in Hf.
  assert (Hboxk : forall v : nat * nat, I2_R k (S m, 2) v -> False).
  { intros [c d]. destruct k as [|k']; cbn.
    - intros _. lia.
    - intros [Hac Hcn]. cbn in Hac, Hcn. lia. }
  pose proof (Hf Hboxk) as Hbox0_box0.
  pose proof (Hbox0_box0 (S m, 1)) as Hbox0_box0'.
  assert (Hr0 : I2_R 0 (S m, 2) (S m, 1))
    by (cbn; right; split; [reflexivity | lia]).
  pose proof (Hbox0_box0' Hr0) as Hbox0_boxm.
  pose proof (Hbox0_boxm (S m, 0)) as Hbox0_boxm'.
  assert (Hr0' : I2_R 0 (S m, 1) (S m, 0))
    by (cbn; right; split; [reflexivity | lia]).
  pose proof (Hbox0_boxm' Hr0') as Hboxm.
  destruct m as [|m']; cbn in Hboxm.
  - apply (Hboxm (0, 0)). cbn. left. lia.
  - apply (Hboxm (S m', 0)). cbn. split; [lia|lia].
Qed.

(** ** General refutation tool: for any iter-box-Bot consequent of the
    form [iter_box (zeros ++ [m]) Bot] where [zeros] is a list of [0]s and
    [m < k], the implication [Box k Bot -> ...] is unprovable.  Proof by
    induction on [zeros], stepping into the lex-below world at each [0]. *)

Lemma forces_iter_box_zeros_box_m_bot_at_drop : forall zeros,
  Forall (fun n => n = 0) zeros ->
  forall m a b,
  forces I2 (fun _ _ => false) (a, b)
         (iter_box zeros (Box m Bot)) ->
  b >= length zeros ->
  forces I2 (fun _ _ => false) (a, b - length zeros) (Box m Bot).
Proof.
  intro zeros. induction zeros as [|z rest IH]; intros Hall m a b Hf Hb.
  - cbn. rewrite Nat.sub_0_r. exact Hf.
  - inversion Hall as [|y ys Hz0 Hrest]. subst z.
    cbn [iter_box length] in *.
    pose proof (Hf (a, b - 1)) as Hf'.
    assert (Hr : I2_R 0 (a, b) (a, b - 1)).
    { cbn. right. split; [reflexivity | lia]. }
    pose proof (Hf' Hr) as Hf_inner.
    assert (Hsub : b - 1 - length rest = b - S (length rest)) by lia.
    rewrite <- Hsub.
    apply (IH Hrest m a (b - 1)); [exact Hf_inner | lia].
Qed.

Theorem refute_box_k_bot_implies_iter_box_zero_prefix_box_m_bot :
  forall k m zeros,
  m < k ->
  Forall (fun n => n = 0) zeros ->
  ~ |- Impl (Box k Bot) (iter_box zeros (Box m Bot)).
Proof.
  intros k m zeros Hmk Hall Hp.
  pose proof (soundness _ Hp I2 (fun _ _ => false) (S m, length zeros)) as Hf.
  cbn in Hf.
  assert (Hboxk : forall v : nat * nat, I2_R k (S m, length zeros) v -> False).
  { intros [c d]. destruct k as [|k']; cbn.
    - intros _. lia.
    - intros [Hac Hcn]. cbn in Hac, Hcn. lia. }
  pose proof (Hf Hboxk) as Hcons.
  pose proof (forces_iter_box_zeros_box_m_bot_at_drop
                zeros Hall m (S m) (length zeros)
                Hcons (Nat.le_refl _)) as Hboxm.
  rewrite Nat.sub_diag in Hboxm.
  cbn in Hboxm.
  destruct m as [|m']; cbn in Hboxm.
  - apply (Hboxm (0, 0)). cbn. left. lia.
  - apply (Hboxm (S m', 0)). cbn. split; [lia|lia].
Qed.

(** ** I2 refutation for [Box k_1 (Box k_2 Bot) -> Box 0 (Box m Bot)]
    when [k_1 >= 1], [k_1 <= k_2], and [k_2 = m] (i.e., the
    bad_world-equal Beklemishev-gap configuration). *)

Theorem refute_box_box_bot_implies_box_0_box_m_bot :
  forall k_1 k_2 m,
  1 <= k_1 -> k_1 <= k_2 -> k_2 = m ->
  ~ |- Impl (Box k_1 (Box k_2 Bot)) (Box 0 (Box m Bot)).
Proof.
  intros k_1 k_2 m Hk1 Hk1k2 Hk2m Hp. subst k_2.
  pose proof (soundness _ Hp I2 (fun _ _ => false) (S m, 1)) as Hf.
  cbn in Hf.
  assert (Hbox12 : forall v : nat * nat,
            I2_R k_1 (S m, 1) v ->
            forall u, I2_R m v u -> False).
  { intros [c d]. destruct k_1 as [|k_1']; cbn.
    - lia.
    - intros [Hac Hcn]. cbn in Hac, Hcn.
      intros [e f]. destruct m as [|m']; cbn.
      + intros _. lia.
      + intros [Hce Hen]. cbn in Hce, Hen. lia. }
  pose proof (Hf Hbox12) as Hbox0.
  pose proof (Hbox0 (S m, 0)) as Hbox0'.
  assert (Hr0 : I2_R 0 (S m, 1) (S m, 0))
    by (cbn; right; split; [reflexivity | lia]).
  pose proof (Hbox0' Hr0) as Hboxm.
  destruct m as [|m']; cbn in Hboxm.
  - apply (Hboxm (0, 0)). cbn. left. lia.
  - apply (Hboxm (S m', 0)). cbn. split; [lia|lia].
Qed.

(** ** Concrete instance: [|- Box 1 (Box 3 Bot) -> Box 0 (Box 3 Bot)] is
    UNPROVABLE.  Together with [Box 0 (Box 3 Bot) -> Box 1 (Box 3 Bot)]
    (provable via Mon), this establishes another Fnat-incompleteness
    witness. *)

Corollary refute_box_1_box_3_bot_implies_box_0_box_3_bot :
  ~ |- Impl (Box 1 (Box 3 Bot)) (Box 0 (Box 3 Bot)).
Proof.
  apply refute_box_box_bot_implies_box_0_box_m_bot; [lia|lia|reflexivity].
Qed.

(** ** Hence, in our axiom system, the Lindenbaum classes of
    [Box 0 (Box m Bot)] and [Box (S m) Bot] are NOT provably equivalent.
    [I2] refutes the reverse direction, completing the Fnat-incompleteness
    witness for the closed fragment of GLP*. *)


(** ** The explicit measure-recursive decider.

    [glp_dec_b] recurses structurally through the outer [Box] layers --
    each step strictly decreases both [modal_depth] and [form_length] --
    and decides the box-free leaf by the classical tautology checker.
    [Some true] = provable, [Some false] = refuted, [None] = outside the
    decidable fragment. *)

Fixpoint glp_dec_b (phi : Form) : option bool :=
  match phi with
  | Box _ psi => glp_dec_b psi
  | _ => if box_free_b phi then Some (decide_tautology phi) else None
  end.

(** The decreasing measure is explicit and lexicographic: the [Box]
    recursion strictly drops the modal depth (first component) and the
    length (second component). *)

Lemma modal_depth_box_decreases : forall n psi,
  modal_depth psi < modal_depth (Box n psi).
Proof. intros n psi. cbn. lia. Qed.

Lemma form_length_box_decreases : forall n psi,
  form_length psi < form_length (Box n psi).
Proof. intros n psi. cbn. lia. Qed.

Theorem glp_dec_b_measure_decreases : forall n psi,
  modal_depth psi < modal_depth (Box n psi) /\
  form_length psi < form_length (Box n psi).
Proof.
  intros n psi. split;
    [apply modal_depth_box_decreases | apply form_length_box_decreases].
Qed.

(** [glp_dec_b] computes the tautology status of the box-free leaf
    reached by stripping the outer boxes. *)

Lemma glp_dec_b_extract : forall phi,
  glp_dec_b phi =
    (if box_free_b (extract_inner_form phi)
     then Some (decide_tautology (extract_inner_form phi))
     else None).
Proof.
  induction phi as [k | | X IHX Y IHY | n psi IHpsi]; cbn.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact IHpsi.
Qed.

(** Inside the fragment, the inner leaf is box-free. *)

Lemma fragment_inner_box_free_b : forall phi,
  is_iter_box_of_box_free phi = true ->
  box_free_b (extract_inner_form phi) = true.
Proof.
  intros phi H. unfold is_iter_box_of_box_free in H. exact H.
Qed.

(** ** Correctness of the explicit decider. *)

Theorem glp_decide_b_correct : forall phi,
  is_iter_box_of_box_free phi = true ->
  (glp_dec_b phi = Some true <-> |- phi).
Proof.
  intros phi H.
  pose proof (extract_inner_box_free phi H) as Hbf.
  pose proof (fragment_inner_box_free_b phi H) as Hbfb.
  rewrite glp_dec_b_extract, Hbfb.
  split.
  - intro Hs. injection Hs as Hs.
    rewrite (extract_decomposition phi).
    apply (proj2 (provable_iter_box_box_free_iff_classical_valid
                    (extract_box_levels phi) (extract_inner_form phi) Hbf)).
    apply decide_tautology_correct. exact Hs.
  - intro Hp. f_equal.
    apply decide_tautology_complete.
    apply (proj1 (provable_iter_box_box_free_iff_classical_valid
                    (extract_box_levels phi) (extract_inner_form phi) Hbf)).
    rewrite <- (extract_decomposition phi). exact Hp.
Qed.

Theorem glp_decide_b_refute : forall phi,
  is_iter_box_of_box_free phi = true ->
  (glp_dec_b phi = Some false <-> ~ |- phi).
Proof.
  intros phi H.
  pose proof (extract_inner_box_free phi H) as Hbf.
  pose proof (fragment_inner_box_free_b phi H) as Hbfb.
  rewrite glp_dec_b_extract, Hbfb.
  split.
  - intros Hs Hp.
    apply (proj2 (glp_decide_b_correct phi H)) in Hp.
    rewrite glp_dec_b_extract, Hbfb in Hp.
    rewrite Hs in Hp. discriminate Hp.
  - intro Hnp. f_equal.
    destruct (decide_tautology (extract_inner_form phi)) eqn:Edt.
    + exfalso. apply Hnp.
      rewrite (extract_decomposition phi).
      apply (proj2 (provable_iter_box_box_free_iff_classical_valid
                      (extract_box_levels phi) (extract_inner_form phi) Hbf)).
      apply decide_tautology_correct. exact Edt.
    + reflexivity.
Qed.

(** ** The sumbool decider over the decidable fragment. *)

Definition glp_decide (phi : Form)
  (H : is_iter_box_of_box_free phi = true) : { |- phi } + { ~ |- phi }.
Proof.
  destruct (glp_dec_b phi) as [b|] eqn:E.
  - destruct b.
    + left. apply (proj1 (glp_decide_b_correct phi H)). exact E.
    + right. apply (proj1 (glp_decide_b_refute phi H)). exact E.
  - exfalso.
    rewrite glp_dec_b_extract, (fragment_inner_box_free_b phi H) in E.
    discriminate E.
Defined.

Theorem glp_decide_correct : forall phi (H : is_iter_box_of_box_free phi = true),
  match glp_decide phi H with left _ => True | right _ => False end <-> |- phi.
Proof.
  intros phi H. destruct (glp_decide phi H) as [p | np].
  - split; [intros _; exact p | intros _; exact I].
  - split; [intros [] | intros Hp; exact (np Hp)].
Qed.

(** ** The decider covers modal formulas beyond the box-free fragment. *)

Example glp_decide_box_tower_provable :
  is_iter_box_of_box_free (Box 3 (Box 1 (Impl (Var 0) (Var 0)))) = true /\
  glp_dec_b (Box 3 (Box 1 (Impl (Var 0) (Var 0)))) = Some true.
Proof. split; reflexivity. Qed.

Example glp_decide_box_bot_refuted :
  is_iter_box_of_box_free (Box 0 Bot) = true /\
  glp_dec_b (Box 0 Bot) = Some false.
Proof. split; reflexivity. Qed.

(** ** Obstruction: provability is not compositional, so the demanded
    total naive structural recursion cannot be complete. *)

Lemma not_provable_neg_box0_bot : ~ |- Neg (Box 0 Bot).
Proof.
  intro H.
  pose proof (soundness _ H Fnat (fun _ _ => true) 0) as Hf.
  apply Hf. intros v Hv. unfold Fnat_R in Hv. destruct Hv as [Hgt _]. lia.
Qed.

Theorem box_provability_noncompositional :
  exists n psi, |- Box n psi /\ ~ |- psi.
Proof.
  exists 1, (Neg (Box 0 Bot)). split.
  - exact (Ax_NextCon 0).
  - exact not_provable_neg_box0_bot.
Qed.

Theorem impl_provability_noncompositional :
  exists a b, |- Impl a b /\ ~ |- a /\ ~ |- b.
Proof.
  exists (Var 0), (Var 0). split; [|split].
  - exact (prov_id (Var 0)).
  - exact var_not_provable.
  - exact var_not_provable.
Qed.

(** Decidability holds as a proposition, classically, via excluded
    middle. *)

Theorem glp_provability_decidable_classically : forall phi,
  (|- phi) \/ ~ |- phi.
Proof. intro phi. apply classic. Qed.

(** ** Decider summary. *)

Theorem glp_decide_summary :
  (* explicit lexicographic measure decreases through the Box recursion *)
  (forall n psi,
     modal_depth psi < modal_depth (Box n psi) /\
     form_length psi < form_length (Box n psi)) /\
  (* the constructive decider is correct on its fragment *)
  (forall phi (H : is_iter_box_of_box_free phi = true),
     match glp_decide phi H with left _ => True | right _ => False end <-> |- phi) /\
  (* it decides modal formulas beyond the box-free fragment *)
  (glp_dec_b (Box 3 (Box 1 (Impl (Var 0) (Var 0)))) = Some true) /\
  (glp_dec_b (Box 0 Bot) = Some false) /\
  (* provability is non-compositional: the naive total recursion fails *)
  (exists n psi, |- Box n psi /\ ~ |- psi) /\
  (exists a b, |- Impl a b /\ ~ |- a /\ ~ |- b).
Proof.
  split; [|split; [|split; [|split; [|split]]]].
  - exact glp_dec_b_measure_decreases.
  - exact glp_decide_correct.
  - reflexivity.
  - reflexivity.
  - exact box_provability_noncompositional.
  - exact impl_provability_noncompositional.
Qed.

(** ** Worked examples. *)

Example example_1_godel_second_at_level_zero :
  ~ |- Box 0 (Neg (Box 0 Bot)).
Proof. exact (Godel_sentence_independent_at_Tn 0). Qed.

Example example_1_consistency_provable_at_level_one :
  |- Box 1 (Neg (Box 0 Bot)).
Proof. exact (Ax_NextCon 0). Qed.

Example example_2_loeb_at_level_two :
  forall phi, |- Impl (Box 2 (Impl (Box 2 phi) phi)) (Box 2 phi).
Proof. intros phi. exact (Ax_Loeb 2 phi). Qed.

Example example_3_fairbot_provable :
  forall n, |- genuine_FairBot n Cooperate_action.
Proof. exact genuine_FairBot_provable_when_opp_eq_cooperate. Qed.

Example example_3_prudentbot_provable :
  forall n, |- genuine_PrudentBot n Cooperate_action.
Proof. exact genuine_PrudentBot_provable_when_opp_eq_cooperate. Qed.

Example example_4_strict_separation : forall n,
  exists phi,
    |- Box (S n) phi /\
    ~ |- Box n phi.
Proof. exact strict_extension_at_each_level. Qed.

Example example_5_meta_consistency : ~ |- Bot.
Proof. exact meta_consistency_system. Qed.

Example example_6_box_atomic_fixedpoint : forall n,
  |- Iff Top (Box n Top).
Proof. exact fixedpoint_top_box. Qed.

Example example_7_kalmar_completeness : forall phi,
  box_free phi -> classical_valid phi -> |- phi.
Proof. exact Solovay_first_completeness_via_classical_valid. Qed.
