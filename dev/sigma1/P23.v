From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22.
Open Scope fo_scope.

(** ** Code patterns of terms and formulas.

    [cpat_tm rho t], [cpat_f rho A]: the code of [t], [A] with every
    free variable [y] that [rho] maps to [Some i] left as slot [i];
    a binder hides its variable from [rho]. *)

Definition rho_hide (y : nat) (rho : nat -> option nat) : nat -> option nat :=
  fun z => if Nat.eqb z y then None else rho z.

Fixpoint cpat_tm (rho : nat -> option nat) (t : FOTerm) : CPat :=
  match t with
  | FOVar y => match rho y with Some i => CVarP i | None => tVarP (CLit y) end
  | FOZero => tZeroP
  | FOSucc a => tSuccP (cpat_tm rho a)
  | FOPlus a b => tPlusP (cpat_tm rho a) (cpat_tm rho b)
  | FOMult a b => tMultP (cpat_tm rho a) (cpat_tm rho b)
  end.

Fixpoint cpat_f (rho : nat -> option nat) (A : FOFormula) : CPat :=
  match A with
  | FOEq a b => pEqP (cpat_tm rho a) (cpat_tm rho b)
  | FOFalseF => pFlsP
  | FOImplF B C => pImpP (cpat_f rho B) (cpat_f rho C)
  | FOForall y B => pAllP (CLit y) (cpat_f (rho_hide y rho) B)
  | FOExists y B => pExP (CLit y) (cpat_f (rho_hide y rho) B)
  end.

Lemma cpat_tm_ext : forall t rho rho', (forall z, rho z = rho' z) ->
  cpat_tm rho t = cpat_tm rho' t.
Proof.
  induction t as [y| |a IH|a IHa b IHb|a IHa b IHb]; intros rho rho' H; cbn [cpat_tm].
  - rewrite H. reflexivity.
  - reflexivity.
  - rewrite (IH rho rho' H). reflexivity.
  - rewrite (IHa rho rho' H), (IHb rho rho' H). reflexivity.
  - rewrite (IHa rho rho' H), (IHb rho rho' H). reflexivity.
Qed.

Lemma rho_hide_ext : forall y rho rho', (forall z, rho z = rho' z) ->
  forall z, rho_hide y rho z = rho_hide y rho' z.
Proof. intros y rho rho' H z. unfold rho_hide. destruct (Nat.eqb z y); [reflexivity | apply H]. Qed.

Lemma cpat_f_ext : forall A rho rho', (forall z, rho z = rho' z) ->
  cpat_f rho A = cpat_f rho' A.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros rho rho' H; cbn [cpat_f].
  - rewrite (cpat_tm_ext a rho rho' H), (cpat_tm_ext b rho rho' H). reflexivity.
  - reflexivity.
  - rewrite (IHB rho rho' H), (IHC rho rho' H). reflexivity.
  - rewrite (IHB _ _ (rho_hide_ext y rho rho' H)). reflexivity.
  - rewrite (IHB _ _ (rho_hide_ext y rho rho' H)). reflexivity.
Qed.

Lemma cpat_tm_closed_sem : forall t rho sigma, (forall z, rho z = None) ->
  cpat_sem sigma (cpat_tm rho t) = FOcode_tm t.
Proof.
  induction t as [y| |a IH|a IHa b IHb|a IHa b IHb]; intros rho sigma H;
    cbn [cpat_tm cpat_sem FOcode_tm tVarP tZeroP tSuccP tPlusP tMultP].
  - rewrite H. reflexivity.
  - reflexivity.
  - rewrite IH by exact H. reflexivity.
  - rewrite IHa, IHb by exact H. reflexivity.
  - rewrite IHa, IHb by exact H. reflexivity.
Qed.

Lemma cpat_f_closed_sem : forall A rho sigma, (forall z, rho z = None) ->
  cpat_sem sigma (cpat_f rho A) = FOcode_f A.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros rho sigma H;
    cbn [cpat_f cpat_sem FOcode_f pEqP pFlsP pImpP pAllP pExP].
  - rewrite !cpat_tm_closed_sem by exact H. reflexivity.
  - reflexivity.
  - rewrite IHB, IHC by exact H. reflexivity.
  - rewrite IHB; [reflexivity|]. intros z. unfold rho_hide. destruct (Nat.eqb z y); auto.
  - rewrite IHB; [reflexivity|]. intros z. unfold rho_hide. destruct (Nat.eqb z y); auto.
Qed.

(** ** Pairing: congruence and functionality. *)

Lemma FOPrH_cpairF_cong : forall n G a b c a' b' c',
  FOPrH n G (FOEq a a') -> FOPrH n G (FOEq b b') -> FOPrH n G (FOEq c c') ->
  FOPrH n G (FOcpairF a b c) -> FOPrH n G (FOcpairF a' b' c').
Proof.
  intros n G a b c a' b' c' E1 E2 E3 H. unfold FOcpairF in *.
  pose proof (FOPrH_congPlus _ _ _ _ _ _ E1 E2) as Eab.
  pose proof (FOPrH_congMult _ _ _ _ _ _ Eab (FOPrH_congS _ _ _ _ Eab)) as Em.
  pose proof (FOPrH_congPlus _ _ _ _ _ _ Em (FOPrH_congPlus _ _ _ _ _ _ E2 E2)) as Er.
  pose proof (FOPrH_congPlus _ _ _ _ _ _ E3 E3) as Ec.
  exact (FOPrH_eq_trans _ _ _ _ _ (FOPrH_eq_sym _ _ _ _ Ec) (FOPrH_eq_trans _ _ _ _ _ H Er)).
Qed.

Lemma FOPrH_cpair_fun : forall n G a b c c',
  FOtms_avoid [c; c'] 440 442 ->
  FOPrH n G (FOcpairF a b c) -> FOPrH n G (FOcpairF a b c') -> FOPrH n G (FOEq c c').
Proof.
  intros n G a b c c' Hav H1 H2.
  assert (E : FOPrH n G (FOEq (FOPlus c c) (FOPlus c' c'))).
  { unfold FOcpairF in H1, H2. exact (FOPrH_eq_trans _ _ _ _ _ H1 (FOPrH_eq_sym _ _ _ _ H2)). }
  assert (Vc : FOtm_avoid c 440 442) by avoid_tm.
  assert (Vc' : FOtm_avoid c' 440 442) by avoid_tm.
  pose proof (FOPrH_thm n G _ (FOPr_double_inj n)) as D.
  apply (FOPrH_inst n G 440 c) in D;
    [| cbn [FOsubst_ok FOfree_in FOin_tm orb negb andb Nat.eqb];
       rewrite (Vc 441 ltac:(lia) ltac:(lia)); reflexivity].
  cbn [FOsubst_f FOsubst_t Nat.eqb] in D.
  apply (FOPrH_inst n G 441 c') in D; [|cbn [FOsubst_ok]; reflexivity].
  cbn [FOsubst_f FOsubst_t Nat.eqb] in D.
  rewrite (FOsubst_t_not_in c 441 c' (Vc 441 ltac:(lia) ltac:(lia))) in D.
  exact (FOPrH_mp _ _ _ _ D E).
Qed.

(** ** Pattern nodes decomposed at their own bound variables.

    The two witnesses of a pair node at base [B] are named by the
    variables [B] and [B + 2] that bind them; the sub-patterns sit at
    higher bases, so the names stay out of every region still to be
    decomposed. *)

Lemma FOPrH_patf_pair_elim_self : forall n G B env a b d C,
  FOPrH n G (FOPATF B env (CPair a b) d) ->
  500 <= B ->
  FOctx_avoid G B (B + cpat_span (CPair a b)) ->
  (forall w, B <= w -> w < B + cpat_span (CPair a b) -> FOfree_in w C = false) ->
  FOtms_avoid (d :: env) B (B + cpat_span (CPair a b)) ->
  FOPrH n (G ++ [FOAnd (FOcpairF (FOVar B) (FOVar (B + 2)) d)
                   (FOAnd (FOPATF (B + 4) env a (FOVar B))
                          (FOPATF (B + 4 + 4 * cpat_pairs a) env b (FOVar (B + 2))))]) C ->
  FOPrH n G C.
Proof.
  intros n G B env a b d C H HB HG HC Hav H0.
  pose proof (cpat_span_le a) as Ha. cbn [cpat_span] in HG, HC, Hav.
  assert (Hd : FOtm_avoid d B (B + (4 + 4 * cpat_pairs a + cpat_span b)))
    by (apply Hav; left; reflexivity).
  cbn [FOPATF] in H. rewrite FOBexC_ltv in H.
  refine (FOPrH_ex_elim n G B _ C (HG B ltac:(lia) ltac:(lia)) (HC B ltac:(lia) ltac:(lia))
            H _).
  lazymatch goal with |- FOPrH _ (_ ++ [?X]) _ =>
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G X)) as H1 end.
  rewrite FOBexC_ltv in H1.
  refine (FOPrH_ex_elim n _ (B + 2) _ C _ (HC (B + 2) ltac:(lia) ltac:(lia)) H1 _).
  { apply FOfree_ctx_app_inv; [apply HG; lia|].
    apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
    rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
    - apply FOfree_in_ltv; [lia|]. rewrite FOin_tm_succ_eq. apply Hd; lia.
    - try rewrite FOBexC_ltv. apply FOfree_in_ex_self. }
  refine (FOPrH_cut _ _ _ C (FOPrH_and_r _ _ _ _ (FOPrH_last _ _ _)) _).
  refine (FOPrH_weaken n _ _ C _ H0).
  intros X HX. apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
  - apply in_or_app. left. apply in_or_app. left. apply in_or_app. left. exact HX.
  - apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPrH_patf_succ_elim_self : forall n G B env q d C,
  FOPrH n G (FOPATF B env (CSuccP q) d) ->
  500 <= B ->
  FOctx_avoid G B (B + cpat_span (CSuccP q)) ->
  (forall w, B <= w -> w < B + cpat_span (CSuccP q) -> FOfree_in w C = false) ->
  FOtms_avoid (d :: env) B (B + cpat_span (CSuccP q)) ->
  FOPrH n (G ++ [FOAnd (FOEq d (FOSucc (FOVar B))) (FOPATF (B + 2) env q (FOVar B))]) C ->
  FOPrH n G C.
Proof.
  intros n G B env q d C H HB HG HC Hav H0.
  cbn [cpat_span] in HG, HC, Hav.
  cbn [FOPATF] in H. rewrite FOBexC_ltv in H.
  refine (FOPrH_ex_elim n G B _ C (HG B ltac:(lia) ltac:(lia)) (HC B ltac:(lia) ltac:(lia))
            H _).
  refine (FOPrH_cut _ _ _ C (FOPrH_and_r _ _ _ _ (FOPrH_last _ _ _)) _).
  refine (FOPrH_weaken n _ _ C _ H0).
  intros X HX. apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
  - apply in_or_app. left. apply in_or_app. left. exact HX.
  - apply in_or_app. right. left. reflexivity.
Qed.

(** A pair node whose left component is a literal. *)

Lemma FOPrH_patf_lit_elim : forall n G B env k q d C,
  FOPrH n G (FOPATF B env (CPair (CLit k) q) d) ->
  500 <= B ->
  FOctx_avoid G B (B + cpat_span (CPair (CLit k) q)) ->
  (forall w, B <= w -> w < B + cpat_span (CPair (CLit k) q) -> FOfree_in w C = false) ->
  FOtms_avoid (d :: env) B (B + cpat_span (CPair (CLit k) q)) ->
  FOPrH n (G ++ [FOcpairF (FOnumeral k) (FOVar (B + 2)) d;
                 FOPATF (B + 4) env q (FOVar (B + 2))]) C ->
  FOPrH n G C.
Proof.
  intros n G B env k q d C H HB HG HC Hav H0.
  apply (FOPrH_patf_pair_elim_self n G B env (CLit k) q d C H HB HG HC Hav).
  replace (B + 4 + 4 * cpat_pairs (CLit k)) with (B + 4) by (cbn [cpat_pairs]; lia).
  lazymatch goal with |- FOPrH _ (_ ++ [?X]) _ => pose proof (FOPrH_last n G X) as HX end.
  cbn [FOPATF] in HX.
  pose proof (FOPrH_and_l _ _ _ _ HX) as Hc.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ HX)) as Ek.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ HX)) as Hq.
  pose proof (FOPrH_cpairF_cong _ _ _ _ _ _ _ _ Ek (FOPrH_refl _ _ _) (FOPrH_refl _ _ _) Hc)
    as Hc'.
  refine (FOPrH_cut _ _ _ C Hc' _).
  refine (FOPrH_cut _ _ _ C (FOPrH_weak_app _ _ _ _ Hq) _).
  refine (FOPrH_weaken n _ _ C _ H0).
  intros Y HY. apply in_app_or in HY. destruct HY as [HY|[<-|[<-|[]]]].
  - apply in_or_app. left. apply in_or_app. left. apply in_or_app. left. exact HY.
  - apply in_or_app. left. apply in_or_app. right. left. reflexivity.
  - apply in_or_app. right. left. reflexivity.
Qed.

(** ** Avoidance for sublists. *)

Lemma FOtms_avoid_incl : forall L L' lo hi lo' hi',
  FOtms_avoid L' lo hi -> (forall t, In t L -> In t L') -> lo <= lo' -> hi' <= hi ->
  FOtms_avoid L lo' hi'.
Proof.
  intros L L' lo hi lo' hi' H Hinc H1 H2 t Ht.
  exact (FOtm_avoid_sub t lo hi lo' hi' (H t (Hinc t Ht)) H1 H2).
Qed.

Ltac avoid_tms ::=
  lazymatch goal with
  | |- FOtms_avoid (_ ++ _) _ _ => apply FOtms_avoid_app; avoid_tms
  | |- FOtms_avoid (_ :: _) _ _ => apply FOtms_avoid_cons; [avoid_tm | avoid_tms]
  | |- FOtms_avoid [] _ _ => apply FOtms_avoid_nil
  | |- FOtms_avoid (FOtab_terms ?T) ?lo ?hi =>
      match goal with
      | H : FOtms_avoid ?L ?lo' ?hi' |- _ =>
          apply (FOtms_avoid_sub _ lo' hi' lo hi); [|lia|lia];
          intros u Hu; apply H; simpl in Hu |- *; tauto
      end
  | |- FOtms_avoid ?L ?lo ?hi =>
      match goal with
      | H : FOtms_avoid ?L' ?lo' ?hi' |- _ =>
          apply (FOtms_avoid_incl L L' lo' hi' lo hi H);
          [ let t := fresh "t" in let Ht := fresh "Ht" in
            intros t Ht; clear -Ht; cbn [In] in *; repeat rewrite in_app_iff in *;
            cbn [In] in *; tauto
          | nat_fast | nat_fast]
      end
  end.

(** ** Introduction of a successor node. *)

Lemma FOPrH_patf_succ_intro : forall n G B env q d u,
  FOPrH n G (FOEq d (FOSucc u)) -> FOPrH n G (FOPATF (B + 2) env q u) ->
  500 <= B ->
  FOtms_avoid (d :: u :: env) B (B + cpat_span (CSuccP q)) ->
  FOtms_avoid [d; u] 420 500 ->
  FOPrH n G (FOPATF B env (CSuccP q) d).
Proof.
  intros n G B env q d u E Hq HB Hav Hav2.
  cbn [cpat_span] in Hav. cbn [FOPATF].
  apply (FOPrH_bex_intro_t _ _ B d u); [lia | lia | avoid_tm | avoid_tm | avoid_tm
    | avoid_tm | | | ].
  - apply (FOPrH_le_of_eq n G (FOSucc u) d FOZero); [|avoid_tms].
    exact (FOPrH_eq_trans _ _ _ _ _ (FOPrH_Q_plus_zero _ _ _) (FOPrH_eq_sym _ _ _ _ E)).
  - apply FOsubst_ok_and; [apply FOsubst_ok_eq|]. apply FOsubst_ok_PATF.
    apply (FOtm_avoid_sub u B (B + (2 + cpat_span q)));
      [apply Hav; right; left; reflexivity | lia | lia].
  - rewrite FOsubst_f_and, FOsubst_f_eq, FOsubst_t_succ, FOsubst_t_var_eq'.
    rewrite FOsubst_f_PATF by lia. rewrite FOsubst_t_var_eq'.
    rewrite (FOsubst_t_not_in d B _ (Hav d (or_introl eq_refl) B ltac:(lia) ltac:(lia))).
    rewrite (FOsubst_map_avoid B u env)
      by (intros t Ht; apply (Hav t); [right; right; exact Ht | lia | lia]).
    apply FOPrH_and_intro; [exact E | exact Hq].
Qed.

(** ** Codes matching a pattern are equal. *)

Lemma FOPrH_patf_unique : forall p n G B B' env d d',
  FOPrH n G (FOPATF B env p d) -> FOPrH n G (FOPATF B' env p d') ->
  500 <= B -> 500 <= B' -> B + cpat_span p <= B' \/ B' + cpat_span p <= B ->
  FOctx_avoid G B (B + cpat_span p) -> FOctx_avoid G B' (B' + cpat_span p) ->
  FOtms_avoid (d :: d' :: env) B (B + cpat_span p) ->
  FOtms_avoid (d :: d' :: env) B' (B' + cpat_span p) ->
  FOtms_avoid [d; d'] 440 442 ->
  FOPrH n G (FOEq d d').
Proof.
  induction p as [k|i|q IH|a IHa b IHb];
    intros n G B B' env d d' H H' HB HB' Hdis HG HG' Hav Hav' Hd.
  - cbn [FOPATF] in H, H'. exact (FOPrH_eq_trans _ _ _ _ _ H (FOPrH_eq_sym _ _ _ _ H')).
  - cbn [FOPATF] in H, H'. exact (FOPrH_eq_trans _ _ _ _ _ H (FOPrH_eq_sym _ _ _ _ H')).
  - cbn [cpat_span] in Hdis, HG, HG', Hav, Hav'.
    apply (FOPrH_patf_succ_elim_self n G B env q d _ H HB);
      [cbn [cpat_span]; exact HG | intros w H1 H2; cbn [cpat_span] in H2; free_fm
      | cbn [cpat_span]; avoid_tms |].
    apply (FOPrH_patf_succ_elim_self n _ B' env q d' _ (FOPrH_weak_app _ _ _ _ H') HB');
      [cbn [cpat_span]; ctx_list | intros w H1 H2; cbn [cpat_span] in H2; free_fm
      | cbn [cpat_span]; avoid_tms |].
    lazymatch goal with |- FOPrH _ ((?G0 ++ [?X]) ++ [?X']) _ =>
      pose proof (FOPrH_weak_app _ _ [X'] _ (FOPrH_last n G0 X)) as HX;
      pose proof (FOPrH_last n (G0 ++ [X]) X') as HX'
    end.
    pose proof (IH n _ (B + 2) (B' + 2) env (FOVar B) (FOVar B')
                  (FOPrH_and_r _ _ _ _ HX) (FOPrH_and_r _ _ _ _ HX')
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as E.
    exact (FOPrH_eq_trans _ _ _ _ _ (FOPrH_and_l _ _ _ _ HX)
             (FOPrH_eq_trans _ _ _ _ _ (FOPrH_congS _ _ _ _ E)
                (FOPrH_eq_sym _ _ _ _ (FOPrH_and_l _ _ _ _ HX')))).
  - pose proof (cpat_span_le a) as Hsa. cbn [cpat_span] in Hdis, HG, HG', Hav, Hav'.
    apply (FOPrH_patf_pair_elim_self n G B env a b d _ H HB);
      [cbn [cpat_span]; exact HG | intros w H1 H2; cbn [cpat_span] in H2; free_fm
      | cbn [cpat_span]; avoid_tms |].
    apply (FOPrH_patf_pair_elim_self n _ B' env a b d' _ (FOPrH_weak_app _ _ _ _ H') HB');
      [cbn [cpat_span]; ctx_list | intros w H1 H2; cbn [cpat_span] in H2; free_fm
      | cbn [cpat_span]; avoid_tms |].
    lazymatch goal with |- FOPrH _ ((?G0 ++ [?X]) ++ [?X']) _ =>
      pose proof (FOPrH_weak_app _ _ [X'] _ (FOPrH_last n G0 X)) as HX;
      pose proof (FOPrH_last n (G0 ++ [X]) X') as HX'
    end.
    pose proof (IHa n _ (B + 4) (B' + 4) env (FOVar B) (FOVar B')
                  (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ HX))
                  (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ HX'))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Ea.
    pose proof (IHb n _ (B + 4 + 4 * cpat_pairs a) (B' + 4 + 4 * cpat_pairs a) env
                  (FOVar (B + 2)) (FOVar (B' + 2))
                  (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ HX))
                  (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ HX'))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Eb.
    pose proof (FOPrH_cpairF_cong _ _ _ _ _ _ _ _ Ea Eb (FOPrH_refl _ _ _)
                  (FOPrH_and_l _ _ _ _ HX)) as Hc.
    exact (FOPrH_cpair_fun n _ (FOVar B') (FOVar (B' + 2)) d d' ltac:(avoid_tms) Hc
             (FOPrH_and_l _ _ _ _ HX')).
Qed.

(** ** A pattern fact moved to another base. *)

Lemma FOPrH_patf_rebase : forall p n G B B' env d,
  FOPrH n G (FOPATF B env p d) ->
  500 <= B -> 500 <= B' -> B + cpat_span p <= B' \/ B' + cpat_span p <= B ->
  FOctx_avoid G B (B + cpat_span p) ->
  FOtms_avoid (d :: env) B (B + cpat_span p) ->
  FOtms_avoid (d :: env) B' (B' + cpat_span p) ->
  FOtms_avoid (d :: env) 420 500 ->
  FOPrH n G (FOPATF B' env p d).
Proof.
  induction p as [k|i|q IH|a IHa b IHb]; intros n G B B' env d H HB HB' Hdis HG Hav Hav' Hav2.
  - exact H.
  - exact H.
  - cbn [cpat_span] in Hdis, HG, Hav, Hav'.
    apply (FOPrH_patf_succ_elim_self n G B env q d _ H HB);
      [cbn [cpat_span]; exact HG | intros w H1 H2; cbn [cpat_span] in H2; free_fm
      | cbn [cpat_span]; avoid_tms |].
    lazymatch goal with |- FOPrH _ (?G0 ++ [?X]) _ => pose proof (FOPrH_last n G0 X) as HX end.
    pose proof (IH n _ (B + 2) (B' + 2) env (FOVar B) (FOPrH_and_r _ _ _ _ HX)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Hq.
    apply (FOPrH_patf_succ_intro n _ B' env q d (FOVar B) (FOPrH_and_l _ _ _ _ HX) Hq HB');
      [cbn [cpat_span]; avoid_tms | avoid_tms].
  - pose proof (cpat_span_le a) as Hsa. cbn [cpat_span] in Hdis, HG, Hav, Hav'.
    apply (FOPrH_patf_pair_elim_self n G B env a b d _ H HB);
      [cbn [cpat_span]; exact HG | intros w H1 H2; cbn [cpat_span] in H2; free_fm
      | cbn [cpat_span]; avoid_tms |].
    lazymatch goal with |- FOPrH _ (?G0 ++ [?X]) _ => pose proof (FOPrH_last n G0 X) as HX end.
    pose proof (IHa n _ (B + 4) (B' + 4) env (FOVar B)
                  (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ HX))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Ha.
    pose proof (IHb n _ (B + 4 + 4 * cpat_pairs a) (B' + 4 + 4 * cpat_pairs a) env
                  (FOVar (B + 2)) (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ HX))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Hb.
    apply (FOPrH_patf_pair_intro n _ B' env a b d (FOVar B) (FOVar (B + 2))
             (FOPrH_and_l _ _ _ _ HX) Ha Hb ltac:(lia));
      [cbn [cpat_span]; avoid_tms | avoid_tms].
Qed.

(** ** Every pattern has a code.

    The code is named [z]; the recursion names the component codes
    [z + 1] and [z + 2], all below the pattern's base. *)

Lemma FOPrH_patf_total : forall p n G B env z,
  1000 <= z -> z + 3 <= B ->
  FOctx_avoid G z (z + 3) -> FOctx_avoid G 420 500 ->
  FOtms_avoid env B (B + cpat_span p) -> FOtms_avoid env z (z + 3) ->
  FOtms_avoid env 420 500 ->
  FOPrH n G (FOExists z (FOPATF B env p (FOVar z))).
Proof.
  induction p as [k|i|q IH|a IHa b IHb]; intros n G B env z Hz HzB HG HG2 Hav Havz Hav2.
  - apply (FOPrH_ex_intro _ _ z (FOnumeral k)); [cbn [FOPATF]; apply FOsubst_ok_eq|].
    cbn [FOPATF]. rewrite FOsubst_f_eq, FOsubst_t_var_eq', FOsubst_t_numeral.
    apply FOPrH_refl.
  - apply (FOPrH_ex_intro _ _ z (nth i env FOZero)); [cbn [FOPATF]; apply FOsubst_ok_eq|].
    cbn [FOPATF]. rewrite FOsubst_f_eq, FOsubst_t_var_eq'.
    rewrite FOsubst_t_not_in; [apply FOPrH_refl|].
    destruct (nth_in_or_default i env FOZero) as [Hin| ->]; [|reflexivity].
    apply (Havz _ Hin); lia.
  - cbn [cpat_span] in Hav.
    pose proof (IH n G (B + 2) env z Hz ltac:(lia) HG HG2 ltac:(avoid_tms) Havz Hav2) as Hq.
    refine (FOPrH_exe n G z (z + 1) _ _ Hq _ _ _ _ _);
      [apply HG; lia | free_fm | free_fm | apply FOsubst_ok_PATF; avoid_tm |].
    rewrite FOsubst_f_PATF by lia. rewrite FOsubst_t_var_eq'.
    rewrite (FOsubst_map_avoid z _ env) by (intros t Ht; apply (Havz t Ht); lia).
    apply (FOPrH_ex_intro _ _ z (FOSucc (FOVar (z + 1))));
      [apply FOsubst_ok_PATF; cbn [cpat_span]; avoid_tm|].
    rewrite FOsubst_f_PATF by lia. rewrite FOsubst_t_var_eq'.
    rewrite (FOsubst_map_avoid z _ env) by (intros t Ht; apply (Havz t Ht); lia).
    apply (FOPrH_patf_succ_intro n _ B env q (FOSucc (FOVar (z + 1))) (FOVar (z + 1)));
      [apply FOPrH_refl | apply FOPrH_last | lia | cbn [cpat_span]; avoid_tms | avoid_tms].
  - pose proof (cpat_span_le a) as Hsa. cbn [cpat_span] in Hav.
    pose proof (IHa n G (B + 4) env z Hz ltac:(lia) HG HG2 ltac:(avoid_tms) Havz Hav2) as Ha.
    pose proof (IHb n G (B + 4 + 4 * cpat_pairs a) env z Hz ltac:(lia) HG HG2 ltac:(avoid_tms)
                  Havz Hav2) as Hb.
    refine (FOPrH_exe n G z (z + 1) _ _ Ha _ _ _ _ _);
      [apply HG; lia | free_fm | free_fm | apply FOsubst_ok_PATF; avoid_tm |].
    rewrite FOsubst_f_PATF by lia. rewrite FOsubst_t_var_eq'.
    rewrite (FOsubst_map_avoid z _ env) by (intros t Ht; apply (Havz t Ht); lia).
    refine (FOPrH_exe n _ z (z + 2) _ _ (FOPrH_weak_app _ _ _ _ Hb) _ _ _ _ _);
      [free_ctx | free_fm | free_fm | apply FOsubst_ok_PATF; avoid_tm |].
    rewrite FOsubst_f_PATF by lia. rewrite FOsubst_t_var_eq'.
    rewrite (FOsubst_map_avoid z _ env) by (intros t Ht; apply (Havz t Ht); lia).
    apply (FOPrH_cpair_elim_hi n _ (FOVar (z + 1)) (FOVar (z + 2)) z);
      [ctx_list | avoid_tms | lia | free_ctx | free_fm | avoid_tms |].
    apply (FOPrH_ex_intro _ _ z (FOVar z)); [apply FOsubst_ok_var_self|].
    rewrite FOsubst_f_id.
    apply (FOPrH_patf_pair_intro n _ B env a b (FOVar z) (FOVar (z + 1)) (FOVar (z + 2)));
      [apply FOPrH_last | wk_in | wk_in | lia | cbn [cpat_span]; avoid_tms | avoid_tms].
Qed.

