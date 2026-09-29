(******************************************************************************)
(*                                                                            *)
(*           Parametric Provability: Bypassing the Loebian Obstacle           *)
(*                                                                            *)
(*     Part 4 of 9. Object-level arithmetic, beta sequences, Cantor pairing.  *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics.

(** ** Instantiating derivable open equations.

    An equation derived with free variables holds at every term: [Gen]
    followed by [FOProvesTn_AllElimT], whose capture condition is
    vacuous on an equation.  Simultaneous substitution [FOsim_t] is
    reduced to a sequence of single substitutions that first rename
    every variable of the equation to a fresh block and then replace
    the fresh block by the target terms. *)

Lemma FOPr_eq_inst : forall n x t a b,
  FOProvesTn n (FOEq a b) ->
  FOProvesTn n (FOEq (FOsubst_t x t a) (FOsubst_t x t b)).
Proof.
  intros n x t a b H.
  exact (FOProvesTn_MP n _ _
           (FOProvesTn_AllElimT n x t (FOEq a b) eq_refl)
           (FOProvesTn_Gen n x _ H)).
Qed.

Fixpoint FOsim_t (s : nat -> FOTerm) (t : FOTerm) : FOTerm :=
  match t with
  | FOVar y => s y
  | FOZero => FOZero
  | FOSucc a => FOSucc (FOsim_t s a)
  | FOPlus a b => FOPlus (FOsim_t s a) (FOsim_t s b)
  | FOMult a b => FOMult (FOsim_t s a) (FOsim_t s b)
  end.

Fixpoint FOseq_t (l : list (nat * FOTerm)) (t : FOTerm) : FOTerm :=
  match l with
  | [] => t
  | (x, u) :: l' => FOseq_t l' (FOsubst_t x u t)
  end.

Lemma FOPr_eq_seq : forall n l a b,
  FOProvesTn n (FOEq a b) ->
  FOProvesTn n (FOEq (FOseq_t l a) (FOseq_t l b)).
Proof.
  intros n l. induction l as [|[x u] l IH]; intros a b H; cbn.
  - exact H.
  - apply IH. apply FOPr_eq_inst. exact H.
Qed.

Lemma FOseq_t_app : forall l1 l2 t,
  FOseq_t (l1 ++ l2) t = FOseq_t l2 (FOseq_t l1 t).
Proof.
  induction l1 as [|[x u] l1 IH]; intros l2 t; cbn; [reflexivity|].
  apply IH.
Qed.

Lemma FOseq_t_Zero : forall l, FOseq_t l FOZero = FOZero.
Proof. induction l as [|[x u] l IH]; cbn; [reflexivity | exact IH]. Qed.

Lemma FOseq_t_Succ : forall l a,
  FOseq_t l (FOSucc a) = FOSucc (FOseq_t l a).
Proof.
  induction l as [|[x u] l IH]; intros a; cbn; [reflexivity | apply IH].
Qed.

Lemma FOseq_t_Plus : forall l a b,
  FOseq_t l (FOPlus a b) = FOPlus (FOseq_t l a) (FOseq_t l b).
Proof.
  induction l as [|[x u] l IH]; intros a b; cbn; [reflexivity | apply IH].
Qed.

Lemma FOseq_t_Mult : forall l a b,
  FOseq_t l (FOMult a b) = FOMult (FOseq_t l a) (FOseq_t l b).
Proof.
  induction l as [|[x u] l IH]; intros a b; cbn; [reflexivity | apply IH].
Qed.

(** A sequence whose substituted variables all lie above [t]'s
    variables leaves [t] unchanged. *)

Lemma FOseq_t_above : forall l t,
  (forall x u, In (x, u) l -> FOmax_var_tm t < x) ->
  FOseq_t l t = t.
Proof.
  induction l as [|[x u] l IH]; intros t Hl; cbn; [reflexivity|].
  rewrite FOsubst_t_not_in.
  - apply IH. intros x' u' Hin. apply (Hl x' u'). right. exact Hin.
  - apply FOin_tm_above. apply (Hl x u). left. reflexivity.
Qed.

Definition FOren_list (K lo len : nat) : list (nat * FOTerm) :=
  map (fun v => (v, FOVar (K + v))) (seq lo len).

Definition FOfill_list (s : nat -> FOTerm) (K lo len : nat)
  : list (nat * FOTerm) :=
  map (fun v => (K + v, s v)) (seq lo len).

Lemma FOseq_t_var_miss : forall l y,
  (forall x u, In (x, u) l -> x <> y) -> FOseq_t l (FOVar y) = FOVar y.
Proof.
  induction l as [|[x u] l IH]; intros y Hl; cbn; [reflexivity|].
  destruct (Nat.eqb_spec y x) as [E|E].
  - exfalso. apply (Hl x u); [left; reflexivity | symmetry; exact E].
  - apply IH. intros x' u' Hin. apply (Hl x' u'). right. exact Hin.
Qed.

Lemma FOren_list_var : forall K len lo y,
  lo + len <= K ->
  FOseq_t (FOren_list K lo len) (FOVar y) =
  if andb (lo <=? y) (y <? lo + len) then FOVar (K + y) else FOVar y.
Proof.
  intros K len. induction len as [|len IH]; intros lo y Hle.
  - cbn [FOren_list seq map FOseq_t].
    destruct (lo <=? y) eqn:E1; destruct (y <? lo + 0) eqn:E2;
      cbn; try reflexivity.
    exfalso. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2. lia.
  - unfold FOren_list. cbn [seq map FOseq_t FOsubst_t].
    destruct (Nat.eqb_spec y lo) as [E|E].
    + subst y.
      rewrite FOseq_t_var_miss.
      * rewrite Nat.leb_refl. replace (lo <? lo + S len) with true
          by (symmetry; apply Nat.ltb_lt; lia).
        reflexivity.
      * intros x u Hin. apply in_map_iff in Hin.
        destruct Hin as [v [Hv Hin]]. injection Hv as Hx _. subst x.
        apply in_seq in Hin. lia.
    + fold (FOren_list K (S lo) len).
      rewrite (IH (S lo) y ltac:(lia)).
      destruct (S lo <=? y) eqn:E1; destruct (y <? S lo + len) eqn:E2;
        destruct (lo <=? y) eqn:E3; destruct (y <? lo + S len) eqn:E4;
        cbn; try reflexivity; exfalso;
        repeat match goal with
               | H : (_ <=? _) = true |- _ => apply Nat.leb_le in H
               | H : (_ <=? _) = false |- _ => apply Nat.leb_gt in H
               | H : (_ <? _) = true |- _ => apply Nat.ltb_lt in H
               | H : (_ <? _) = false |- _ => apply Nat.ltb_ge in H
               end; lia.
Qed.

Lemma FOfill_list_var : forall s K len lo y,
  (forall v, lo <= v < lo + len -> FOmax_var_tm (s v) < K) ->
  lo <= y < lo + len ->
  FOseq_t (FOfill_list s K lo len) (FOVar (K + y)) = s y.
Proof.
  intros s K len. induction len as [|len IH]; intros lo y Hs Hy.
  - lia.
  - unfold FOfill_list. cbn [seq map FOseq_t FOsubst_t].
    destruct (Nat.eqb_spec (K + y) (K + lo)) as [E|E].
    + assert (y = lo) by lia. subst y.
      apply FOseq_t_above.
      intros x u Hin. apply in_map_iff in Hin.
      destruct Hin as [v [Hv Hin]]. injection Hv as Hx _. subst x.
      apply in_seq in Hin. pose proof (Hs lo ltac:(lia)). lia.
    + fold (FOfill_list s K (S lo) len).
      apply IH.
      * intros v Hv. apply Hs. lia.
      * lia.
Qed.

Fixpoint FOmaxs (s : nat -> FOTerm) (M : nat) : nat :=
  match M with
  | 0 => FOmax_var_tm (s 0)
  | S M' => Nat.max (FOmax_var_tm (s (S M'))) (FOmaxs s M')
  end.

Lemma FOmaxs_ge : forall s M v, v <= M -> FOmax_var_tm (s v) <= FOmaxs s M.
Proof.
  intros s M. induction M as [|M IH]; intros v Hv; cbn.
  - assert (v = 0) by lia. subst v. lia.
  - destruct (Nat.eq_dec v (S M)) as [->|Hne]; [lia|].
    pose proof (IH v ltac:(lia)). lia.
Qed.

Lemma FOsim_t_as_seq : forall s M t,
  FOmax_var_tm t <= M ->
  let K := S (M + FOmaxs s M) in
  FOseq_t (FOren_list K 0 (S M) ++ FOfill_list s K 0 (S M)) t = FOsim_t s t.
Proof.
  intros s M t Ht K.
  induction t as [y | | a IH | a IHa b IHb | a IHa b IHb]; cbn in Ht.
  - rewrite FOseq_t_app.
    rewrite (FOren_list_var K (S M) 0 y ltac:(unfold K; lia)).
    replace (andb (0 <=? y) (y <? 0 + S M)) with true
      by (symmetry; apply andb_true_intro; split;
          [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia]).
    apply FOfill_list_var; [|lia].
    intros v Hv. pose proof (FOmaxs_ge s M v ltac:(lia)). unfold K. lia.
  - rewrite FOseq_t_Zero. reflexivity.
  - rewrite FOseq_t_Succ. cbn. f_equal. apply IH. exact Ht.
  - rewrite FOseq_t_Plus. cbn. f_equal; [apply IHa | apply IHb]; lia.
  - rewrite FOseq_t_Mult. cbn. f_equal; [apply IHa | apply IHb]; lia.
Qed.

Lemma FOPr_eq_sim : forall n s a b,
  FOProvesTn n (FOEq a b) ->
  FOProvesTn n (FOEq (FOsim_t s a) (FOsim_t s b)).
Proof.
  intros n s a b H.
  set (M := Nat.max (FOmax_var_tm a) (FOmax_var_tm b)).
  rewrite <- (FOsim_t_as_seq s M a ltac:(unfold M; lia)).
  rewrite <- (FOsim_t_as_seq s M b ltac:(unfold M; lia)).
  apply FOPr_eq_seq. exact H.
Qed.

(** ** The semiring laws at arbitrary terms. *)

Lemma FOPr_all_open : forall n x A,
  FOProvesTn n (FOForall x A) -> FOProvesTn n A.
Proof.
  intros n x A H.
  pose proof (FOProvesTn_MP n _ _
    (FOProvesTn_AllElimT n x (FOVar x) A (FOsubst_ok_var_self A x)) H) as H'.
  rewrite FOsubst_f_id in H'. exact H'.
Qed.

Definition FOsg (a b c : FOTerm) : nat -> FOTerm :=
  fun v => match v with 0 => a | 1 => b | _ => c end.

Lemma FOPr_t_plus_zero_l : forall n a, FOProvesTn n (FOEq (FOPlus FOZero a) a).
Proof.
  intros n a.
  exact (FOPr_eq_sim n (FOsg a a a) _ _ (FOPr_all_open n 0 _ (FOPr_zero_plus n))).
Qed.

Lemma FOPr_t_plus_comm : forall n a b,
  FOProvesTn n (FOEq (FOPlus a b) (FOPlus b a)).
Proof.
  intros n a b.
  exact (FOPr_eq_sim n (FOsg a b b) _ _
           (FOPr_all_open n 0 _ (FOPr_all_open n 1 _ (FOPr_plus_comm n)))).
Qed.

Lemma FOPr_t_plus_assoc : forall n a b c,
  FOProvesTn n (FOEq (FOPlus a (FOPlus b c)) (FOPlus (FOPlus a b) c)).
Proof.
  intros n a b c. apply FOPr_eq_sym.
  exact (FOPr_eq_sim n (FOsg a b c) _ _
           (FOPr_all_open n 2 _ (FOPr_all_open n 1 _
              (FOPr_all_open n 0 _ (FOPr_plus_assoc n))))).
Qed.

Lemma FOPr_t_mult_zero_l : forall n a, FOProvesTn n (FOEq (FOMult FOZero a) FOZero).
Proof.
  intros n a.
  exact (FOPr_eq_sim n (FOsg a a a) _ _ (FOPr_all_open n 0 _ (FOPr_mult_zero_l n))).
Qed.

Lemma FOPr_t_mult_comm : forall n a b,
  FOProvesTn n (FOEq (FOMult a b) (FOMult b a)).
Proof.
  intros n a b.
  exact (FOPr_eq_sim n (FOsg a b b) _ _
           (FOPr_all_open n 0 _ (FOPr_all_open n 1 _ (FOPr_mult_comm n)))).
Qed.

Lemma FOPr_t_mult_assoc : forall n a b c,
  FOProvesTn n (FOEq (FOMult a (FOMult b c)) (FOMult (FOMult a b) c)).
Proof.
  intros n a b c. apply FOPr_eq_sym.
  exact (FOPr_eq_sim n (FOsg a b c) _ _
           (FOPr_all_open n 2 _ (FOPr_all_open n 1 _
              (FOPr_all_open n 0 _ (FOPr_mult_assoc n))))).
Qed.

Lemma FOPr_t_distr_r : forall n a b c,
  FOProvesTn n (FOEq (FOMult (FOPlus a b) c)
                     (FOPlus (FOMult a c) (FOMult b c))).
Proof.
  intros n a b c.
  exact (FOPr_eq_sim n (FOsg a b c) _ _
           (FOPr_all_open n 2 _ (FOPr_all_open n 1 _
              (FOPr_all_open n 0 _ (FOPr_mult_distrib_r n))))).
Qed.

Lemma FOPr_t_plus_one : forall n a,
  FOProvesTn n (FOEq (FOSucc a) (FOPlus a (FOSucc FOZero))).
Proof.
  intros n a.
  apply FOPr_eq_sym.
  exact (FOPr_eq_trans n _ (FOSucc (FOPlus a FOZero)) _
           (FOPr_q_plus_succ n a FOZero)
           (FOPr_eq_congS n _ _ (FOPr_q_plus_zero n a))).
Qed.

Lemma FOPr_t_mult_one_l : forall n a,
  FOProvesTn n (FOEq (FOMult (FOSucc FOZero) a) a).
Proof.
  intros n a.
  eapply FOPr_eq_trans.
  - apply FOPr_t_mult_comm.
  - eapply FOPr_eq_trans.
    + apply FOPr_q_mult_succ.
    + eapply FOPr_eq_trans.
      * apply FOPr_eq_congPlus; [apply FOPr_q_mult_zero | apply FOProvesTn_EqRefl].
      * apply FOPr_t_plus_zero_l.
Qed.

(** ** Object-level equality at every level as a semiring setoid. *)

Definition FOreq (a b : FOTerm) : Prop := forall n, FOProvesTn n (FOEq a b).

Lemma FOreq_setoid : Setoid_Theory FOTerm FOreq.
Proof.
  constructor.
  - intros a n. apply FOProvesTn_EqRefl.
  - intros a b H n. exact (FOPr_eq_sym n _ _ (H n)).
  - intros a b c H1 H2 n. exact (FOPr_eq_trans n _ _ _ (H1 n) (H2 n)).
Qed.

Lemma FOreq_ext : sring_eq_ext FOPlus FOMult FOreq.
Proof.
  constructor.
  - intros a b H c d H' n. exact (FOPr_eq_congPlus n _ _ _ _ (H n) (H' n)).
  - intros a b H c d H' n. exact (FOPr_eq_congMult n _ _ _ _ (H n) (H' n)).
Qed.

Lemma FOsrt : semi_ring_theory FOZero (FOSucc FOZero) FOPlus FOMult FOreq.
Proof.
  constructor; intros; intro k.
  - apply FOPr_t_plus_zero_l.
  - apply FOPr_t_plus_comm.
  - apply FOPr_t_plus_assoc.
  - apply FOPr_t_mult_one_l.
  - apply FOPr_t_mult_zero_l.
  - apply FOPr_t_mult_comm.
  - apply FOPr_t_mult_assoc.
  - apply FOPr_t_distr_r.
Qed.

Add Ring FOring : FOsrt (setoid FOreq_setoid FOreq_ext).

(** Successor as [+ 1], so [ring] sees it. *)

Fixpoint FOunS (t : FOTerm) : FOTerm :=
  match t with
  | FOSucc a => FOPlus (FOunS a) (FOSucc FOZero)
  | FOPlus a b => FOPlus (FOunS a) (FOunS b)
  | FOMult a b => FOMult (FOunS a) (FOunS b)
  | _ => t
  end.

Lemma FOunS_req : forall t, FOreq t (FOunS t).
Proof.
  induction t as [y | | a IH | a IHa b IHb | a IHa b IHb]; intro k; cbn.
  - apply FOProvesTn_EqRefl.
  - apply FOProvesTn_EqRefl.
  - exact (FOPr_eq_trans k _ _ _ (FOPr_t_plus_one k a)
             (FOPr_eq_congPlus k _ _ _ _ (IH k) (FOProvesTn_EqRefl k _))).
  - exact (FOPr_eq_congPlus k _ _ _ _ (IHa k) (IHb k)).
  - exact (FOPr_eq_congMult k _ _ _ _ (IHa k) (IHb k)).
Qed.

Lemma FOreq_via_unS : forall a b, FOreq (FOunS a) (FOunS b) -> FOreq a b.
Proof.
  intros a b H k.
  exact (FOPr_eq_trans k _ _ _ (FOunS_req a k)
           (FOPr_eq_trans k _ _ _ (H k) (FOPr_eq_sym k _ _ (FOunS_req b k)))).
Qed.

Ltac fo_ring :=
  match goal with
  | |- FOProvesTn ?k (FOEq ?a ?b) =>
      apply (FOreq_via_unS a b); cbn [FOunS]; ring
  | |- FOreq ?a ?b =>
      apply (FOreq_via_unS a b); cbn [FOunS]; ring
  end.


(** ** Derivations under hypotheses.

    A context [G] is read as the nested implication [FOimps G A]:
    [FOPrH n G A] is derivability of [A] from the hypotheses [G] at
    level [n].  The rules below are derived from the Hilbert calculus;
    the quantifier rules carry the usual freshness conditions on the
    context. *)

Fixpoint FOimps (G : list FOFormula) (A : FOFormula) : FOFormula :=
  match G with
  | [] => A
  | H :: G' => FOImplF H (FOimps G' A)
  end.

Definition FOPrH (n : nat) (G : list FOFormula) (A : FOFormula) : Prop :=
  FOProvesTn n (FOimps G A).

Arguments FOPrH : simpl never.

Definition FOfree_ctx (x : nat) (G : list FOFormula) : Prop :=
  forall H, In H G -> FOfree_in x H = false.

Lemma FOimps_app : forall G1 G2 A,
  FOimps (G1 ++ G2) A = FOimps G1 (FOimps G2 A).
Proof.
  induction G1 as [|H G1 IH]; intros G2 A; cbn; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma FOPr_imps_dist : forall n G A B,
  FOProvesTn n (FOImplF (FOimps G (FOImplF A B))
                        (FOImplF (FOimps G A) (FOimps G B))).
Proof.
  intros n G A B. induction G as [|H G IH]; cbn.
  - exact (FOPr_idf n (FOImplF A B)).
  - set (X := FOimps G (FOImplF A B)). set (Y := FOimps G A).
    set (Z := FOimps G B).
    assert (T : FOProvesTn n
      (FOImplF (FOImplF X (FOImplF Y Z))
         (FOImplF (FOImplF H X) (FOImplF (FOImplF H Y) (FOImplF H Z))))).
    { apply (FOPr_taut n (FOm4 X Y Z H)
        (Impl (Impl (Var 0) (Impl (Var 1) (Var 2)))
              (Impl (Impl (Var 3) (Var 0))
                    (Impl (Impl (Var 3) (Var 1)) (Impl (Var 3) (Var 2))))));
        [cbn; tauto | reflexivity]. }
    exact (FOProvesTn_MP n _ _ T IH).
Qed.

Lemma FOPrH_thm : forall n G A, FOProvesTn n A -> FOPrH n G A.
Proof.
  intros n G A H. unfold FOPrH.
  induction G as [|B G IH]; cbn; [exact H | exact (FOPr_weaken n _ _ IH)].
Qed.

Lemma FOPrH_mp : forall n G A B,
  FOPrH n G (FOImplF A B) -> FOPrH n G A -> FOPrH n G B.
Proof.
  intros n G A B H1 H2.
  exact (FOPr_mp2 n _ _ _ (FOPr_imps_dist n G A B) H1 H2).
Qed.

Lemma FOPrH_intro : forall n G A B,
  FOPrH n (G ++ [A]) B -> FOPrH n G (FOImplF A B).
Proof.
  intros n G A B H. unfold FOPrH in *. rewrite FOimps_app in H. exact H.
Qed.

Lemma FOPrH_revert : forall n G A B,
  FOPrH n G (FOImplF A B) -> FOPrH n (G ++ [A]) B.
Proof.
  intros n G A B H. unfold FOPrH in *. rewrite FOimps_app. exact H.
Qed.

Lemma FOPr_imps_self : forall n G H, FOProvesTn n (FOImplF H (FOimps G H)).
Proof.
  intros n G H. induction G as [|K G IH]; cbn.
  - exact (FOPr_idf n H).
  - exact (FOPr_compose n _ _ _ IH (FOProvesTn_K n _ K)).
Qed.

Lemma FOPrH_assum : forall n G A, In A G -> FOPrH n G A.
Proof.
  intros n G A. unfold FOPrH. induction G as [|H G IH]; intros Hin.
  - destruct Hin.
  - cbn. destruct Hin as [<-|Hin].
    + exact (FOPr_imps_self n G H).
    + exact (FOPr_weaken n _ _ (IH Hin)).
Qed.

(** Discharging a context: a derivation from [G] becomes one from [G']
    when every hypothesis of [G] is derivable from [G']. *)

Lemma FOPrH_cut_ctx : forall n G G' A,
  (forall H, In H G -> FOPrH n G' H) ->
  FOPrH n G A -> FOPrH n G' A.
Proof.
  intros n G G' A HG HA.
  assert (L : forall G0, (forall H, In H G0 -> FOPrH n G' H) ->
                forall B, FOPrH n G' (FOimps G0 B) -> FOPrH n G' B).
  { induction G0 as [|H G0 IH]; intros HG0 B HB; cbn in HB; [exact HB|].
    apply (IH (fun H' Hin => HG0 H' (or_intror Hin))).
    exact (FOPrH_mp n G' _ _ HB (HG0 H (or_introl eq_refl))). }
  exact (L G HG A (FOPrH_thm n G' _ HA)).
Qed.

Lemma FOPrH_weaken : forall n G G' A,
  (forall H, In H G -> In H G') -> FOPrH n G A -> FOPrH n G' A.
Proof.
  intros n G G' A Hinc HA.
  apply (FOPrH_cut_ctx n G G' A); [|exact HA].
  intros H Hin. apply FOPrH_assum. exact (Hinc H Hin).
Qed.

Lemma FOPrH_cut : forall n G A B,
  FOPrH n G A -> FOPrH n (G ++ [A]) B -> FOPrH n G B.
Proof.
  intros n G A B HA HB. exact (FOPrH_mp n G A B (FOPrH_intro n G A B HB) HA).
Qed.

(** Quantifier rules. *)

Lemma FOPr_imps_all : forall n x G A,
  FOfree_ctx x G ->
  FOProvesTn n (FOImplF (FOForall x (FOimps G A)) (FOimps G (FOForall x A))).
Proof.
  intros n x G A. induction G as [|H G IH]; intros HG; cbn.
  - exact (FOPr_idf n _).
  - pose proof (FOProvesTn_AllExport n x H (FOimps G A)
                  (HG H (or_introl eq_refl))) as E.
    pose proof (IH (fun H' Hin => HG H' (or_intror Hin))) as IH'.
    set (P := FOForall x (FOImplF H (FOimps G A))) in *.
    set (Q := FOForall x (FOimps G A)) in *.
    set (Y := FOimps G (FOForall x A)) in *.
    assert (T : FOProvesTn n
      (FOImplF (FOImplF P (FOImplF H Q))
         (FOImplF (FOImplF Q Y) (FOImplF P (FOImplF H Y))))).
    { apply (FOPr_taut n (FOm4 P H Q Y)
        (Impl (Impl (Var 0) (Impl (Var 1) (Var 2)))
              (Impl (Impl (Var 2) (Var 3)) (Impl (Var 0) (Impl (Var 1) (Var 3))))));
        [cbn; tauto | reflexivity]. }
    exact (FOPr_mp2 n _ _ _ T E IH').
Qed.

Lemma FOPrH_all_intro : forall n G x A,
  FOfree_ctx x G -> FOPrH n G A -> FOPrH n G (FOForall x A).
Proof.
  intros n G x A HG HA.
  exact (FOProvesTn_MP n _ _ (FOPr_imps_all n x G A HG)
           (FOProvesTn_Gen n x _ HA)).
Qed.

Lemma FOPrH_all_elim : forall n G x t A,
  FOsubst_ok x t A = true ->
  FOPrH n G (FOForall x A) -> FOPrH n G (FOsubst_f x t A).
Proof.
  intros n G x t A Hok H.
  exact (FOPrH_mp n G _ _ (FOPrH_thm n G _ (FOProvesTn_AllElimT n x t A Hok)) H).
Qed.

Lemma FOPrH_ex_intro : forall n G x t A,
  FOsubst_ok x t A = true ->
  FOPrH n G (FOsubst_f x t A) -> FOPrH n G (FOExists x A).
Proof.
  intros n G x t A Hok H.
  exact (FOPrH_mp n G _ _ (FOPrH_thm n G _ (FOProvesTn_ExIntroT n x t A Hok)) H).
Qed.

Lemma FOPrH_ex_elim : forall n G x A B,
  FOfree_ctx x G -> FOfree_in x B = false ->
  FOPrH n G (FOExists x A) -> FOPrH n (G ++ [A]) B -> FOPrH n G B.
Proof.
  intros n G x A B HG HB HE HAB.
  pose proof (FOPrH_all_intro n G x _ HG (FOPrH_intro n G A B HAB)) as HAll.
  exact (FOPrH_mp n G _ _
           (FOPrH_mp n G _ _ (FOPrH_thm n G _ (FOProvesTn_ExElim n x A B HB)) HAll)
           HE).
Qed.

(** Equality and induction. *)

Lemma FOPrH_leibniz : forall n G x s t A,
  FOsubst_ok x s A = true -> FOsubst_ok x t A = true ->
  FOPrH n G (FOEq s t) -> FOPrH n G (FOsubst_f x s A) ->
  FOPrH n G (FOsubst_f x t A).
Proof.
  intros n G x s t A Hs Ht Hst HA.
  exact (FOPrH_mp n G _ _
           (FOPrH_mp n G _ _ (FOPrH_thm n G _ (FOPr_f_leibniz A n x s t Hs Ht)) Hst)
           HA).
Qed.

Lemma FOPrH_ind : forall n G x A,
  FOfree_ctx x G ->
  FOPrH n G (FOsubst_f x FOZero A) ->
  FOPrH n (G ++ [A]) (FOsubst_f x (FOSucc (FOVar x)) A) ->
  FOPrH n G (FOForall x A).
Proof.
  intros n G x A HG H0 HS.
  pose proof (FOPrH_all_intro n G x _ HG (FOPrH_intro n G _ _ HS)) as HStep.
  pose proof (FOPrH_thm n G _ (FOProvesTn_ax n _ (FOAx_Ind n x A))) as HI.
  unfold FOInduction in HI.
  exact (FOPrH_mp n G _ _ (FOPrH_mp n G _ _ HI H0) HStep).
Qed.

Lemma FOPrH_req : forall n G a b, FOreq a b -> FOPrH n G (FOEq a b).
Proof. intros n G a b H. exact (FOPrH_thm n G _ (H n)). Qed.

Lemma FOPrH_eq_sym : forall n G a b,
  FOPrH n G (FOEq a b) -> FOPrH n G (FOEq b a).
Proof.
  intros n G a b H.
  exact (FOPrH_mp n G _ _ (FOPrH_thm n G _ (FOProvesTn_EqSym n a b)) H).
Qed.

Lemma FOPrH_eq_trans : forall n G a b c,
  FOPrH n G (FOEq a b) -> FOPrH n G (FOEq b c) -> FOPrH n G (FOEq a c).
Proof.
  intros n G a b c H1 H2.
  exact (FOPrH_mp n G _ _
           (FOPrH_mp n G _ _ (FOPrH_thm n G _ (FOProvesTn_EqTrans n a b c)) H1) H2).
Qed.

(** Propositional rules under a context. *)

Lemma FOPrH_or_intro_l : forall n G A B, FOPrH n G A -> FOPrH n G (FOOr A B).
Proof. intros n G A B H. exact (FOPrH_mp n G _ _ (FOPrH_thm n G _ (FOPr_or_intro_l n A B)) H). Qed.

Lemma FOPrH_or_intro_r : forall n G A B, FOPrH n G B -> FOPrH n G (FOOr A B).
Proof. intros n G A B H. exact (FOPrH_mp n G _ _ (FOPrH_thm n G _ (FOPr_or_intro_r n A B)) H). Qed.

Lemma FOPrH_or_elim : forall n G A B C,
  FOPrH n G (FOOr A B) -> FOPrH n (G ++ [A]) C -> FOPrH n (G ++ [B]) C ->
  FOPrH n G C.
Proof.
  intros n G A B C Hor HA HB.
  exact (FOPrH_mp n G _ _
           (FOPrH_mp n G _ _
              (FOPrH_mp n G _ _ (FOPrH_thm n G _ (FOPr_or_elim n A B C))
                 (FOPrH_intro n G A C HA))
              (FOPrH_intro n G B C HB))
           Hor).
Qed.

Lemma FOPrH_and_intro : forall n G A B,
  FOPrH n G A -> FOPrH n G B -> FOPrH n G (FOAnd A B).
Proof.
  intros n G A B HA HB.
  assert (T : FOProvesTn n (FOImplF A (FOImplF B (FOAnd A B)))).
  { apply (FOPr_taut n (FOm2 A B) (Impl (Var 0) (Impl (Var 1) (And (Var 0) (Var 1)))));
      [cbn; tauto | reflexivity]. }
  exact (FOPrH_mp n G _ _ (FOPrH_mp n G _ _ (FOPrH_thm n G _ T) HA) HB).
Qed.

Lemma FOPrH_and_l : forall n G A B, FOPrH n G (FOAnd A B) -> FOPrH n G A.
Proof. intros n G A B H. exact (FOPrH_mp n G _ _ (FOPrH_thm n G _ (FOPr_and_elim_l n A B)) H). Qed.

Lemma FOPrH_and_r : forall n G A B, FOPrH n G (FOAnd A B) -> FOPrH n G B.
Proof. intros n G A B H. exact (FOPrH_mp n G _ _ (FOPrH_thm n G _ (FOPr_and_elim_r n A B)) H). Qed.

Lemma FOPrH_efq : forall n G A, FOPrH n G FOFalseF -> FOPrH n G A.
Proof. intros n G A H. exact (FOPrH_mp n G _ _ (FOPrH_thm n G _ (FOPr_efq n A)) H). Qed.

(** Every number is zero or a successor, by induction in a context. *)

Lemma FOPr_zero_or_succ : forall n,
  FOProvesTn n (FOForall 0 (FOOr (FOEq (FOVar 0) FOZero)
                                 (FOExists 1 (FOEq (FOVar 0) (FOSucc (FOVar 1)))))).
Proof.
  intro n. change (FOPrH n [] (FOForall 0 (FOOr (FOEq (FOVar 0) FOZero)
                     (FOExists 1 (FOEq (FOVar 0) (FOSucc (FOVar 1))))))).
  apply FOPrH_ind; [intros H []| |]; cbn.
  - apply FOPrH_or_intro_l. apply FOPrH_thm. apply FOProvesTn_EqRefl.
  - apply FOPrH_or_intro_r.
    apply (FOPrH_ex_intro n _ 1 (FOVar 0)); [reflexivity|]. cbn.
    apply FOPrH_thm. apply FOProvesTn_EqRefl.
Qed.

(** ** Renaming a bound variable.

    Substituting a variable [w] that is not free in [A] for [z], and
    then [z] back for [w], returns [A] whenever the first substitution
    is capture-free.  With it an existential can be re-bound at any
    fresh variable, which is what existential elimination needs when
    the bound variable occurs in the context. *)

Lemma FOsubst_t_rename_back : forall a z w,
  FOin_tm w a = false ->
  FOsubst_t w (FOVar z) (FOsubst_t z (FOVar w) a) = a.
Proof.
  induction a as [y | | a IH | a IHa b IHb | a IHa b IHb];
    intros z w Hw; cbn in Hw |- *.
  - destruct (Nat.eqb y z) eqn:Eyz; cbn.
    + apply Nat.eqb_eq in Eyz. subst y. rewrite Nat.eqb_refl. reflexivity.
    + rewrite Hw. reflexivity.
  - reflexivity.
  - rewrite IH by exact Hw. reflexivity.
  - apply Bool.orb_false_iff in Hw as [H1 H2].
    rewrite IHa, IHb by assumption. reflexivity.
  - apply Bool.orb_false_iff in Hw as [H1 H2].
    rewrite IHa, IHb by assumption. reflexivity.
Qed.

Lemma FOin_tm_subst_away : forall a z w,
  z <> w -> FOin_tm z (FOsubst_t z (FOVar w) a) = false.
Proof.
  induction a as [y | | a IH | a IHa b IHb | a IHa b IHb]; intros z w Hzw; cbn.
  - destruct (Nat.eqb y z) eqn:Eyz; cbn.
    + apply Nat.eqb_neq. intro E. apply Hzw. symmetry. exact E.
    + exact Eyz.
  - reflexivity.
  - apply IH. exact Hzw.
  - rewrite IHa, IHb by exact Hzw. reflexivity.
  - rewrite IHa, IHb by exact Hzw. reflexivity.
Qed.

Lemma FOfree_in_subst_away : forall A z w,
  z <> w -> FOfree_in z (FOsubst_f z (FOVar w) A) = false.
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB]; intros z w Hzw; cbn.
  - rewrite !FOin_tm_subst_away by exact Hzw. reflexivity.
  - reflexivity.
  - rewrite IHB, IHC by exact Hzw. reflexivity.
  - destruct (Nat.eqb y z) eqn:Eyz; cbn; rewrite Eyz; [reflexivity|].
    apply IHB. exact Hzw.
  - destruct (Nat.eqb y z) eqn:Eyz; cbn; rewrite Eyz; [reflexivity|].
    apply IHB. exact Hzw.
Qed.

Lemma FOsubst_f_rename_back : forall A z w,
  FOfree_in w A = false -> FOsubst_ok z (FOVar w) A = true ->
  FOsubst_f w (FOVar z) (FOsubst_f z (FOVar w) A) = A.
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB];
    intros z w Hw Hok; cbn in Hw, Hok |- *.
  - apply Bool.orb_false_iff in Hw as [H1 H2].
    rewrite !FOsubst_t_rename_back by assumption. reflexivity.
  - reflexivity.
  - apply Bool.orb_false_iff in Hw as [H1 H2].
    apply Bool.andb_true_iff in Hok as [K1 K2].
    rewrite IHB, IHC by assumption. reflexivity.
  - destruct (Nat.eqb y z) eqn:Eyz.
    + apply Nat.eqb_eq in Eyz. subst y. cbn.
      destruct (Nat.eqb z w) eqn:Ezw; [reflexivity|].
      rewrite (FOsubst_f_not_free B w (FOVar z) Hw). reflexivity.
    + cbn. destruct (FOfree_in z B) eqn:Ez.
      * apply Bool.andb_true_iff in Hok as [K1 K2].
        apply Bool.negb_true_iff in K1.
        assert (Eyw : Nat.eqb y w = false).
        { apply Nat.eqb_neq. intro E. subst y. rewrite Nat.eqb_refl in K1.
          discriminate. }
        rewrite Eyw in Hw |- *. rewrite IHB by assumption. reflexivity.
      * rewrite (FOsubst_f_not_free B z (FOVar w) Ez).
        destruct (Nat.eqb y w) eqn:Eyw; [reflexivity|].
        rewrite (FOsubst_f_not_free B w (FOVar z) Hw). reflexivity.
  - destruct (Nat.eqb y z) eqn:Eyz.
    + apply Nat.eqb_eq in Eyz. subst y. cbn.
      destruct (Nat.eqb z w) eqn:Ezw; [reflexivity|].
      rewrite (FOsubst_f_not_free B w (FOVar z) Hw). reflexivity.
    + cbn. destruct (FOfree_in z B) eqn:Ez.
      * apply Bool.andb_true_iff in Hok as [K1 K2].
        apply Bool.negb_true_iff in K1.
        assert (Eyw : Nat.eqb y w = false).
        { apply Nat.eqb_neq. intro E. subst y. rewrite Nat.eqb_refl in K1.
          discriminate. }
        rewrite Eyw in Hw |- *. rewrite IHB by assumption. reflexivity.
      * rewrite (FOsubst_f_not_free B z (FOVar w) Ez).
        destruct (Nat.eqb y w) eqn:Eyw; [reflexivity|].
        rewrite (FOsubst_f_not_free B w (FOVar z) Hw). reflexivity.
Qed.

Lemma FOsubst_ok_back : forall A z w,
  FOfree_in w A = false -> FOsubst_ok z (FOVar w) A = true ->
  FOsubst_ok w (FOVar z) (FOsubst_f z (FOVar w) A) = true.
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB];
    intros z w Hw Hok; cbn in Hw, Hok |- *.
  - reflexivity.
  - reflexivity.
  - apply Bool.orb_false_iff in Hw as [H1 H2].
    apply Bool.andb_true_iff in Hok as [K1 K2].
    rewrite IHB, IHC by assumption. reflexivity.
  - destruct (Nat.eqb y z) eqn:Eyz.
    + apply Nat.eqb_eq in Eyz. subst y. cbn.
      destruct (Nat.eqb z w) eqn:Ezw; [reflexivity|].
      rewrite Hw. reflexivity.
    + cbn. destruct (FOfree_in z B) eqn:Ez.
      * apply Bool.andb_true_iff in Hok as [K1 K2].
        apply Bool.negb_true_iff in K1.
        assert (Eyw : Nat.eqb y w = false).
        { apply Nat.eqb_neq. intro E. subst y. rewrite Nat.eqb_refl in K1.
          discriminate. }
        rewrite Eyw in Hw |- *.
        destruct (FOfree_in w (FOsubst_f z (FOVar w) B)); [|reflexivity].
        rewrite (IHB z w Hw K2). cbn.
        replace (Nat.eqb z y) with false
          by (symmetry; apply Nat.eqb_neq; intro E; subst z;
              rewrite Nat.eqb_refl in Eyz; discriminate).
        reflexivity.
      * rewrite (FOsubst_f_not_free B z (FOVar w) Ez).
        destruct (Nat.eqb y w) eqn:Eyw; [reflexivity|].
        rewrite Hw. reflexivity.
  - destruct (Nat.eqb y z) eqn:Eyz.
    + apply Nat.eqb_eq in Eyz. subst y. cbn.
      destruct (Nat.eqb z w) eqn:Ezw; [reflexivity|].
      rewrite Hw. reflexivity.
    + cbn. destruct (FOfree_in z B) eqn:Ez.
      * apply Bool.andb_true_iff in Hok as [K1 K2].
        apply Bool.negb_true_iff in K1.
        assert (Eyw : Nat.eqb y w = false).
        { apply Nat.eqb_neq. intro E. subst y. rewrite Nat.eqb_refl in K1.
          discriminate. }
        rewrite Eyw in Hw |- *.
        destruct (FOfree_in w (FOsubst_f z (FOVar w) B)); [|reflexivity].
        rewrite (IHB z w Hw K2). cbn.
        replace (Nat.eqb z y) with false
          by (symmetry; apply Nat.eqb_neq; intro E; subst z;
              rewrite Nat.eqb_refl in Eyz; discriminate).
        reflexivity.
      * rewrite (FOsubst_f_not_free B z (FOVar w) Ez).
        destruct (Nat.eqb y w) eqn:Eyw; [reflexivity|].
        rewrite Hw. reflexivity.
Qed.

Lemma FOPr_ex_rename : forall n z w A,
  FOfree_in w A = false -> FOsubst_ok z (FOVar w) A = true ->
  FOProvesTn n (FOImplF (FOExists z A) (FOExists w (FOsubst_f z (FOVar w) A))).
Proof.
  intros n z w A Hw Hok.
  destruct (Nat.eq_dec z w) as [<-|Hzw].
  - rewrite FOsubst_f_id. apply FOPr_idf.
  - assert (Hfree : FOfree_in z (FOExists w (FOsubst_f z (FOVar w) A)) = false).
    { cbn. replace (Nat.eqb w z) with false
        by (symmetry; apply Nat.eqb_neq; intro E; apply Hzw; symmetry; exact E).
      apply FOfree_in_subst_away. exact Hzw. }
    apply (FOProvesTn_MP n _ _ (FOProvesTn_ExElim n z A _ Hfree)).
    apply FOProvesTn_Gen.
    pose proof (FOProvesTn_ExIntroT n w (FOVar z) (FOsubst_f z (FOVar w) A)
                  (FOsubst_ok_back A z w Hw Hok)) as H.
    rewrite (FOsubst_f_rename_back A z w Hw Hok) in H. exact H.
Qed.

Lemma FOPrH_ex_elim_fresh : forall n G z w A C,
  FOfree_ctx w G -> FOfree_in w C = false -> FOfree_in w A = false ->
  FOsubst_ok z (FOVar w) A = true ->
  FOPrH n G (FOExists z A) ->
  FOPrH n (G ++ [FOsubst_f z (FOVar w) A]) C -> FOPrH n G C.
Proof.
  intros n G z w A C HG HC HA Hok HE HB.
  apply (FOPrH_ex_elim n G w (FOsubst_f z (FOVar w) A) C HG HC); [|exact HB].
  exact (FOPrH_mp n G _ _ (FOPrH_thm n G _ (FOPr_ex_rename n z w A HA Hok)) HE).
Qed.

(** Variables above every variable of a formula are fresh for it. *)

Fixpoint FOvars_max (A : FOFormula) : nat :=
  match A with
  | FOEq a b => Nat.max (FOmax_var_tm a) (FOmax_var_tm b)
  | FOFalseF => 0
  | FOImplF B C => Nat.max (FOvars_max B) (FOvars_max C)
  | FOForall y B => Nat.max y (FOvars_max B)
  | FOExists y B => Nat.max y (FOvars_max B)
  end.

Fixpoint FOvars_ctx_max (G : list FOFormula) : nat :=
  match G with
  | [] => 0
  | H :: G' => Nat.max (FOvars_max H) (FOvars_ctx_max G')
  end.

Lemma FOfree_in_above : forall A v, FOvars_max A < v -> FOfree_in v A = false.
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB]; intros v Hv; cbn in *.
  - rewrite !FOin_tm_above by lia. reflexivity.
  - reflexivity.
  - rewrite IHB, IHC by lia. reflexivity.
  - destruct (Nat.eqb y v); [reflexivity|]. apply IHB. lia.
  - destruct (Nat.eqb y v); [reflexivity|]. apply IHB. lia.
Qed.

Lemma FOfree_ctx_above : forall G v, FOvars_ctx_max G < v -> FOfree_ctx v G.
Proof.
  induction G as [|H G IH]; intros v Hv K Hin; [destruct Hin|].
  cbn in Hv. destruct Hin as [<-|Hin].
  - apply FOfree_in_above. lia.
  - apply (IH v); [lia | exact Hin].
Qed.

Lemma FOsubst_ok_above : forall A z w,
  FOvars_max A < w -> FOsubst_ok z (FOVar w) A = true.
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB]; intros z w Hw; cbn in *.
  - reflexivity.
  - reflexivity.
  - rewrite IHB, IHC by lia. reflexivity.
  - destruct (Nat.eqb y z); [reflexivity|].
    destruct (FOfree_in z B); [|reflexivity].
    replace (Nat.eqb w y) with false by (symmetry; apply Nat.eqb_neq; lia).
    cbn. apply IHB. lia.
  - destruct (Nat.eqb y z); [reflexivity|].
    destruct (FOfree_in z B); [|reflexivity].
    replace (Nat.eqb w y) with false by (symmetry; apply Nat.eqb_neq; lia).
    cbn. apply IHB. lia.
Qed.

(** Existential elimination at a variable above everything in sight. *)

Lemma FOPrH_ex_elim_above : forall n G z A C w,
  FOvars_ctx_max G < w -> FOvars_max C < w -> FOvars_max A < w ->
  FOPrH n G (FOExists z A) ->
  FOPrH n (G ++ [FOsubst_f z (FOVar w) A]) C -> FOPrH n G C.
Proof.
  intros n G z A C w HG HC HA HE HB.
  exact (FOPrH_ex_elim_fresh n G z w A C (FOfree_ctx_above G w HG)
           (FOfree_in_above C w HC) (FOfree_in_above A w HA)
           (FOsubst_ok_above A z w HA) HE HB).
Qed.

(** ** Instantiating derivable quantifier-free formulas.

    The simultaneous instantiation of [FOPr_eq_sim] extends from
    equations to every quantifier-free formula: single substitutions
    are capture-free there, and the fresh-block construction is the
    same. *)

Fixpoint FOqf (A : FOFormula) : Prop :=
  match A with
  | FOEq _ _ => True
  | FOFalseF => True
  | FOImplF B C => FOqf B /\ FOqf C
  | FOForall _ _ => False
  | FOExists _ _ => False
  end.

Fixpoint FOsim_f (s : nat -> FOTerm) (A : FOFormula) : FOFormula :=
  match A with
  | FOEq a b => FOEq (FOsim_t s a) (FOsim_t s b)
  | FOFalseF => FOFalseF
  | FOImplF B C => FOImplF (FOsim_f s B) (FOsim_f s C)
  | FOForall y B => FOForall y B
  | FOExists y B => FOExists y B
  end.

Fixpoint FOseq_f (l : list (nat * FOTerm)) (A : FOFormula) : FOFormula :=
  match l with
  | [] => A
  | (x, u) :: l' => FOseq_f l' (FOsubst_f x u A)
  end.

Lemma FOsubst_ok_qf : forall A x u, FOqf A -> FOsubst_ok x u A = true.
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB]; intros x u H; cbn in *.
  - reflexivity.
  - reflexivity.
  - destruct H as [H1 H2]. rewrite IHB, IHC by assumption. reflexivity.
  - destruct H.
  - destruct H.
Qed.

Lemma FOqf_subst : forall A x u, FOqf A -> FOqf (FOsubst_f x u A).
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB]; intros x u H; cbn in *.
  - exact I.
  - exact I.
  - destruct H as [H1 H2]. split; [apply IHB | apply IHC]; assumption.
  - destruct H.
  - destruct H.
Qed.

Lemma FOPr_qf_inst : forall n x u A,
  FOqf A -> FOProvesTn n A -> FOProvesTn n (FOsubst_f x u A).
Proof.
  intros n x u A Hqf H.
  exact (FOProvesTn_MP n _ _
           (FOProvesTn_AllElimT n x u A (FOsubst_ok_qf A x u Hqf))
           (FOProvesTn_Gen n x _ H)).
Qed.

Lemma FOPr_qf_seq : forall n l A,
  FOqf A -> FOProvesTn n A -> FOProvesTn n (FOseq_f l A).
Proof.
  intros n l. induction l as [|[x u] l IH]; intros A Hqf H; cbn; [exact H|].
  apply IH; [apply FOqf_subst; exact Hqf | apply FOPr_qf_inst; assumption].
Qed.

Lemma FOseq_f_Eq : forall l a b,
  FOseq_f l (FOEq a b) = FOEq (FOseq_t l a) (FOseq_t l b).
Proof. induction l as [|[x u] l IH]; intros a b; cbn; [reflexivity | apply IH]. Qed.

Lemma FOseq_f_False : forall l, FOseq_f l FOFalseF = FOFalseF.
Proof. induction l as [|[x u] l IH]; cbn; [reflexivity | exact IH]. Qed.

Lemma FOseq_f_Impl : forall l B C,
  FOseq_f l (FOImplF B C) = FOImplF (FOseq_f l B) (FOseq_f l C).
Proof. induction l as [|[x u] l IH]; intros B C; cbn; [reflexivity | apply IH]. Qed.

Lemma FOsim_f_as_seq : forall s M A,
  FOqf A -> FOvars_max A <= M ->
  let K := S (M + FOmaxs s M) in
  FOseq_f (FOren_list K 0 (S M) ++ FOfill_list s K 0 (S M)) A = FOsim_f s A.
Proof.
  intros s M A Hqf HM K. subst K.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB]; cbn in Hqf, HM.
  - rewrite FOseq_f_Eq. cbn [FOsim_f].
    rewrite (FOsim_t_as_seq s M a ltac:(lia)).
    rewrite (FOsim_t_as_seq s M b ltac:(lia)). reflexivity.
  - apply FOseq_f_False.
  - destruct Hqf as [H1 H2]. rewrite FOseq_f_Impl. cbn [FOsim_f].
    rewrite IHB, IHC by (assumption || lia). reflexivity.
  - destruct Hqf.
  - destruct Hqf.
Qed.

Lemma FOPr_qf_sim : forall n s A,
  FOqf A -> FOProvesTn n A -> FOProvesTn n (FOsim_f s A).
Proof.
  intros n s A Hqf H.
  rewrite <- (FOsim_f_as_seq s (FOvars_max A) A Hqf (Nat.le_refl _)).
  apply FOPr_qf_seq; assumption.
Qed.

(** A universally closed quantifier-free lemma, instantiated. *)

Lemma FOPr_all_open_qf : forall n s xs A,
  FOqf A -> FOProvesTn n (fold_right FOForall A xs) ->
  FOProvesTn n (FOsim_f s A).
Proof.
  intros n s xs A Hqf H.
  apply FOPr_qf_sim; [exact Hqf|].
  induction xs as [|x xs IH]; cbn in H; [exact H|].
  apply IH. exact (FOPr_all_open n x _ H).
Qed.

Lemma FOPrH_qf_sim : forall n G s A,
  FOqf A -> FOProvesTn n (FOsim_f s A) -> FOPrH n G (FOsim_f s A).
Proof. intros n G s A _ H. exact (FOPrH_thm n G _ H). Qed.

(** ** Object-level number theory.

    Closed lemmas below quantify over variables of the band 400..449 and
    bind their existentials in 450..499; derivations inside them use
    eigenvariables from 500 up.  Instantiation at terms free of these
    bands is capture-free, and every substitution and freshness check
    reduces by computation. *)

Declare Scope fo_scope.
Delimit Scope fo_scope with fo.
Notation "# k" := (FOVar k) (at level 1, format "# k") : fo_scope.
Notation "x '.+' y" := (FOPlus x y) (at level 50, left associativity) : fo_scope.
Notation "x '.*' y" := (FOMult x y) (at level 40, left associativity) : fo_scope.
Notation "'.S' x" := (FOSucc x) (at level 35, right associativity) : fo_scope.
Notation "'.0'" := FOZero : fo_scope.
Notation "x '.=' y" := (FOEq x y) (at level 70, no associativity) : fo_scope.
Notation "A '.->' B" := (FOImplF A B) (at level 90, right associativity) : fo_scope.
Notation "'.A' x , A" := (FOForall x A)
  (at level 200, x at level 0, right associativity) : fo_scope.
Notation "'.E' x , A" := (FOExists x A)
  (at level 200, x at level 0, right associativity) : fo_scope.

Open Scope fo_scope.

(** Context lookup.  Formulas are normalized by [lazy], which unfolds
    the connectives, the beta and bounded quantifier builders and
    substitutions.  Membership in a context and freshness for a context
    are decided by boolean searches evaluated with [vm_compute]; the
    search compares formulas with [FOform_eqb], so a folded and an
    unfolded form of the same formula match.  The step-by-step searches
    remain for contexts that do not compute. *)

Ltac fo_normT T := eval lazy in T.

Ltac fo_norm_goal :=
  lazymatch goal with
  | |- FOPrH ?k ?G ?T => let T' := fo_normT T in change (FOPrH k G T')
  end.

Lemma FOPrH_assum_b : forall n G A,
  existsb (FOform_eqb A) G = true -> FOPrH n G A.
Proof.
  intros n G A H. apply FOPrH_assum.
  apply existsb_exists in H. destruct H as [B [HB HE]].
  apply FOform_eqb_eq in HE. subst B. exact HB.
Qed.

Lemma FOfree_ctx_b : forall w G,
  forallb (fun H => negb (FOfree_in w H)) G = true -> FOfree_ctx w G.
Proof.
  intros w G Hb H Hin. rewrite forallb_forall in Hb. specialize (Hb H Hin).
  destruct (FOfree_in w H); [discriminate | reflexivity].
Qed.

(** The most recently added existential over [z] in a context. *)

Fixpoint FOlast_ex (z : nat) (G : list FOFormula) : option FOFormula :=
  match G with
  | [] => None
  | A :: G' =>
      match FOlast_ex z G' with
      | Some B => Some B
      | None =>
          match A with
          | FOExists y _ => if Nat.eqb y z then Some A else None
          | _ => None
          end
      end
  end.

Ltac fo_hyp_b :=
  lazymatch goal with
  | |- FOPrH ?k ?G ?A => refine (FOPrH_assum_b k G A _); vm_compute; reflexivity
  end.

Ltac fo_in_syn :=
  lazymatch goal with
  | |- In ?x (?y :: _) => first [ constr_eq x y; left; exact eq_refl | right; fo_in_syn ]
  | |- In ?x (?l1 ++ ?l2) =>
      first [ apply in_or_app; right; fo_in_syn | apply in_or_app; left; fo_in_syn ]
  end.

Ltac fo_in_conv :=
  lazymatch goal with
  | |- In ?x (?y :: _) => first [ left; exact eq_refl | right; fo_in_conv ]
  | |- In ?x (?l1 ++ ?l2) =>
      first [ apply in_or_app; right; fo_in_conv | apply in_or_app; left; fo_in_conv ]
  end.

Ltac fo_in := first [ fo_in_syn | fo_in_conv ].

Ltac fo_hyp := first [ fo_hyp_b | fo_norm_goal; apply FOPrH_assum; fo_in ].

(** Substitution by an association list of variables and terms. *)

Fixpoint FOlk (l : list (nat * FOTerm)) (v : nat) : FOTerm :=
  match l with
  | [] => FOVar v
  | (x, t) :: l' => if Nat.eqb v x then t else FOlk l' v
  end.

Ltac fo_fresh := first [ solve [intros ? []]
                       | apply FOfree_ctx_b; vm_compute; reflexivity
                       | solve [let H := fresh in let Hin := fresh in
                                intros H Hin; cbn [In app] in Hin;
                                repeat (destruct Hin as [<-|Hin];
                                        [vm_compute; exact eq_refl|]);
                                destruct Hin]
                       | apply FOfree_ctx_above; apply Nat.ltb_lt;
                         vm_compute; reflexivity ].

Lemma FOPrH_Q_plus_zero : forall n G a, FOPrH n G (a .+ .0 .= a).
Proof. intros. apply FOPrH_thm, FOPr_q_plus_zero. Qed.

Lemma FOPrH_Q_plus_succ : forall n G a b, FOPrH n G (a .+ .S b .= .S (a .+ b)).
Proof. intros. apply FOPrH_thm, FOPr_q_plus_succ. Qed.

Lemma FOPrH_Q_succ_inj : forall n G a b,
  FOPrH n G (.S a .= .S b) -> FOPrH n G (a .= b).
Proof.
  intros n G a b H. exact (FOPrH_mp n G _ _ (FOPrH_thm n G _ (FOPr_q_succ_inj n a b)) H).
Qed.

Lemma FOPrH_Q_succ_nonzero : forall n G a,
  FOPrH n G (.S a .= .0) -> FOPrH n G FOFalseF.
Proof.
  intros n G a H. exact (FOPrH_mp n G _ _ (FOPrH_thm n G _ (FOPr_q_succ_nonzero n a)) H).
Qed.

(** Existential elimination with the existential first, so that its
    body is known when the side conditions are checked. *)

Lemma FOPrH_exe : forall n G z w A C,
  FOPrH n G (FOExists z A) ->
  FOfree_ctx w G -> FOfree_in w C = false -> FOfree_in w A = false ->
  FOsubst_ok z (FOVar w) A = true ->
  FOPrH n (G ++ [FOsubst_f z (FOVar w) A]) C -> FOPrH n G C.
Proof.
  intros n G z w A C HE HG HC HA Hok HB.
  exact (FOPrH_ex_elim_fresh n G z w A C HG HC HA Hok HE HB).
Qed.

Lemma FOPrH_ring : forall n G a b, FOreq a b -> FOPrH n G (a .= b).
Proof. intros n G a b H. exact (FOPrH_thm n G _ (H n)). Qed.

Lemma FOPrH_congS : forall n G a b, FOPrH n G (a .= b) -> FOPrH n G (.S a .= .S b).
Proof.
  intros n G a b H. exact (FOPrH_mp n G _ _ (FOPrH_thm n G _ (FOProvesTn_CongS n a b)) H).
Qed.

Lemma FOPrH_congPlus : forall n G a b c d,
  FOPrH n G (a .= b) -> FOPrH n G (c .= d) -> FOPrH n G (a .+ c .= b .+ d).
Proof.
  intros n G a b c d H1 H2.
  exact (FOPrH_mp n G _ _ (FOPrH_mp n G _ _
           (FOPrH_thm n G _ (FOProvesTn_CongPlus n a b c d)) H1) H2).
Qed.

Lemma FOPrH_congMult : forall n G a b c d,
  FOPrH n G (a .= b) -> FOPrH n G (c .= d) -> FOPrH n G (a .* c .= b .* d).
Proof.
  intros n G a b c d H1 H2.
  exact (FOPrH_mp n G _ _ (FOPrH_mp n G _ _
           (FOPrH_thm n G _ (FOProvesTn_CongMult n a b c d)) H1) H2).
Qed.

Lemma FOPrH_refl : forall n G a, FOPrH n G (a .= a).
Proof. intros. apply FOPrH_thm, FOProvesTn_EqRefl. Qed.

(** Universal instantiation with the derivation first, so that the
    capture check is stated after the formula is known. *)

Lemma FOPrH_inst : forall n G x t A,
  FOPrH n G (FOForall x A) -> FOsubst_ok x t A = true ->
  FOPrH n G (FOsubst_f x t A).
Proof. intros n G x t A H Hok. exact (FOPrH_all_elim n G x t A Hok H). Qed.

(** Additive cancellation, by induction on the cancelled summand. *)

Lemma FOPr_add_cancel : forall n,
  FOProvesTn n (.A 400, .A 401, .A 402,
    (#400 .+ #402 .= #401 .+ #402) .-> #400 .= #401).
Proof.
  intro n.
  change (FOPrH n [] (.A 400, .A 401, .A 402,
    (#400 .+ #402 .= #401 .+ #402) .-> #400 .= #401)).
  apply FOPrH_all_intro; [fo_fresh|].
  apply FOPrH_all_intro; [fo_fresh|].
  apply FOPrH_ind; [fo_fresh| |]; cbn.
  - apply FOPrH_intro. cbn [app].
    eapply FOPrH_eq_trans; [apply FOPrH_eq_sym, FOPrH_Q_plus_zero|].
    eapply FOPrH_eq_trans; [fo_hyp|]. apply FOPrH_Q_plus_zero.
  - apply FOPrH_intro. cbn [app].
    apply (FOPrH_mp n _ (#400 .+ #402 .= #401 .+ #402)); [fo_hyp|].
    apply FOPrH_Q_succ_inj.
    eapply FOPrH_eq_trans; [apply FOPrH_eq_sym, FOPrH_Q_plus_succ|].
    eapply FOPrH_eq_trans; [fo_hyp|]. apply FOPrH_Q_plus_succ.
Qed.

Lemma FOPrH_add_cancel : forall n G a b c,
  FOPrH n G (a .+ c .= b .+ c) -> FOPrH n G (a .= b).
Proof.
  intros n G a b c H.
  pose proof (FOPr_all_open_qf n (FOlk [(400, a); (401, b); (402, c)]) [400; 401; 402]
                ((#400 .+ #402 .= #401 .+ #402) .-> #400 .= #401)
                ltac:(cbn; tauto) (FOPr_add_cancel n)) as C.
  cbn in C. exact (FOPrH_mp n G _ _ (FOPrH_thm n G _ C) H).
Qed.

(** A sum is zero only when its second summand is. *)

Lemma FOPr_add_zero_r : forall n,
  FOProvesTn n (.A 400, .A 401, (#400 .+ #401 .= .0) .-> #401 .= .0).
Proof.
  intro n.
  change (FOPrH n [] (.A 400, .A 401, (#400 .+ #401 .= .0) .-> #401 .= .0)).
  apply FOPrH_all_intro; [fo_fresh|].
  apply FOPrH_all_intro; [fo_fresh|].
  apply FOPrH_intro. cbn [app].
  pose proof (FOPrH_thm n [#400 .+ #401 .= .0] _ (FOPr_zero_or_succ n)) as ZS.
  pose proof (FOPrH_inst n _ 0 (#401) _ ZS eq_refl) as ZS1. cbn in ZS1.
  apply (FOPrH_or_elim n _ _ _ _ ZS1); cbn [app].
  - fo_hyp.
  - apply (FOPrH_ex_elim_fresh n _ 1 500 (#401 .= .S #1));
      [fo_fresh | reflexivity | reflexivity | reflexivity | fo_hyp |].
    cbn [app FOsubst_f FOsubst_t Nat.eqb].
    apply FOPrH_efq.
    apply (FOPrH_Q_succ_nonzero n _ (#400 .+ #500)).
    eapply FOPrH_eq_trans; [apply FOPrH_eq_sym, FOPrH_Q_plus_succ|].
    eapply FOPrH_eq_trans; [|fo_hyp].
    apply FOPrH_congPlus; [apply FOPrH_refl|]. apply FOPrH_eq_sym. fo_hyp.
Qed.

Lemma FOPrH_add_zero_r : forall n G a b,
  FOPrH n G (a .+ b .= .0) -> FOPrH n G (b .= .0).
Proof.
  intros n G a b H.
  pose proof (FOPr_all_open_qf n (FOlk [(400, a); (401, b)]) [400; 401]
                ((#400 .+ #401 .= .0) .-> #401 .= .0)
                ltac:(cbn; tauto) (FOPr_add_zero_r n)) as C.
  cbn in C. exact (FOPrH_mp n G _ _ (FOPrH_thm n G _ C) H).
Qed.

Lemma FOPrH_add_zero_l : forall n G a b,
  FOPrH n G (a .+ b .= .0) -> FOPrH n G (a .= .0).
Proof.
  intros n G a b H. apply (FOPrH_add_zero_r n G b a).
  apply (FOPrH_eq_trans n G _ (a .+ b)); [apply FOPrH_ring; fo_ring | exact H].
Qed.

(** Linear combinations of hypotheses: [L = R] follows from equations
    [l_i = r_i] when [L + sum k_i l_i] and [R + sum k_i r_i] agree as
    polynomials. *)

Fixpoint FOlc_l (cs : list (FOTerm * FOTerm * FOTerm)) : FOTerm :=
  match cs with
  | [] => .0
  | (k, l, _) :: cs' => k .* l .+ FOlc_l cs'
  end.

Fixpoint FOlc_r (cs : list (FOTerm * FOTerm * FOTerm)) : FOTerm :=
  match cs with
  | [] => .0
  | (k, _, r) :: cs' => k .* r .+ FOlc_r cs'
  end.

Lemma FOPrH_lc_eq : forall n G cs,
  (forall k l r, In (k, l, r) cs -> FOPrH n G (l .= r)) ->
  FOPrH n G (FOlc_l cs .= FOlc_r cs).
Proof.
  intros n G cs. induction cs as [|[[k l] r] cs IH]; intros H; cbn.
  - apply FOPrH_refl.
  - apply FOPrH_congPlus.
    + apply FOPrH_congMult; [apply FOPrH_refl | apply (H k l r); left; reflexivity].
    + apply IH. intros k' l' r' Hin. apply (H k' l' r'). right. exact Hin.
Qed.

Lemma FOPrH_lincomb : forall n G L R cs,
  FOreq (L .+ FOlc_l cs) (R .+ FOlc_r cs) ->
  (forall k l r, In (k, l, r) cs -> FOPrH n G (l .= r)) ->
  FOPrH n G (L .= R).
Proof.
  intros n G L R cs Hr Hc.
  apply (FOPrH_add_cancel n G L R (FOlc_l cs)).
  apply (FOPrH_eq_trans n G _ (R .+ FOlc_r cs)); [apply FOPrH_ring; exact Hr|].
  apply FOPrH_congPlus; [apply FOPrH_refl|].
  apply FOPrH_eq_sym. apply FOPrH_lc_eq. exact Hc.
Qed.

(** The hypotheses of a linear combination, one conjunct per triple. *)

Fixpoint FOlc_ok (n : nat) (G : list FOFormula)
    (cs : list (FOTerm * FOTerm * FOTerm)) : Prop :=
  match cs with
  | [] => True
  | (_, l, r) :: cs' => FOPrH n G (l .= r) /\ FOlc_ok n G cs'
  end.

Lemma FOlc_ok_in : forall n G cs, FOlc_ok n G cs ->
  forall k l r, In (k, l, r) cs -> FOPrH n G (l .= r).
Proof.
  intros n G cs. induction cs as [|[[k0 l0] r0] cs IH]; cbn; [tauto|].
  intros [H0 H] k l r [E|Hin].
  - injection E; intros; subst. exact H0.
  - exact (IH H k l r Hin).
Qed.

Lemma FOPrH_lincomb_ok : forall n G L R cs,
  FOreq (L .+ FOlc_l cs) (R .+ FOlc_r cs) -> FOlc_ok n G cs ->
  FOPrH n G (L .= R).
Proof.
  intros n G L R cs Hr Hc. exact (FOPrH_lincomb n G L R cs Hr (FOlc_ok_in n G cs Hc)).
Qed.

Ltac fo_lc_one :=
  first [fo_hyp_b | apply FOPrH_eq_sym; fo_hyp_b
        | fo_hyp | apply FOPrH_eq_sym; fo_hyp | idtac].

Ltac fo_lc_goals := first [exact I | refine (conj _ _); [fo_lc_one | fo_lc_goals]].

Ltac fo_lc_hyps :=
  let k := fresh "k" in let l := fresh "l" in let r := fresh "r" in
  let Hin := fresh "Hin" in
  intros k l r Hin; cbn [In] in Hin;
  repeat match type of Hin with
         | False => destruct Hin
         | _ \/ _ =>
             let E1 := fresh "E" in let E2 := fresh "E" in let E3 := fresh "E" in
             destruct Hin as [Hin|Hin];
             [injection Hin as E1 E2 E3; subst k l r; fo_lc_one | ]
         end.

Ltac fo_lin cs :=
  lazymatch goal with
  | |- FOPrH ?k ?G (FOEq ?L ?R) =>
      refine (FOPrH_lincomb_ok k G L R cs _ _);
      [cbn [FOlc_l FOlc_r]; fo_ring | fo_lc_goals]
  | |- _ =>
      apply (FOPrH_lincomb_ok _ _ _ _ cs);
      [cbn [FOlc_l FOlc_r]; fo_ring | fo_lc_goals]
  end.

(** Case split on a term being zero or a successor, the successor case
    receiving the predecessor as the fresh variable [w]; [fo_cases t w]
    applies it and discharges the side conditions. *)

Lemma FOPrH_cases_zs : forall n G t w C,
  1 < w -> FOin_tm 1 t = false -> FOfree_ctx w G -> FOfree_in w C = false ->
  FOin_tm w t = false ->
  FOPrH n (G ++ [t .= .0]) C ->
  FOPrH n (G ++ [t .= .S #w]) C ->
  FOPrH n G C.
Proof.
  intros n G t w C Hw1 Ht1 HG HC Htw H0 HS.
  assert (ZS : FOPrH n G (FOOr (t .= .0) (.E 1, t .= .S #1))).
  { pose proof (FOPrH_thm n G _ (FOPr_zero_or_succ n)) as Z.
    assert (Hok : FOsubst_ok 0 t (FOOr (#0 .= .0) (.E 1, #0 .= .S #1)) = true).
    { cbn. rewrite Ht1. reflexivity. }
    exact (FOPrH_inst n G 0 t _ Z Hok). }
  apply (FOPrH_or_elim n G _ _ C ZS); [exact H0|].
  assert (Hw1' : Nat.eqb 1 w = false) by (apply Nat.eqb_neq; lia).
  apply (FOPrH_ex_elim_fresh n _ 1 w (t .= .S #1) C).
  - intros H Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + exact (HG H Hin).
    + destruct Hin as [<-|[]]. cbn [FOfree_in FOin_tm orb].
      rewrite Htw, Hw1'. reflexivity.
  - exact HC.
  - cbn [FOfree_in FOin_tm orb]. rewrite Htw, Hw1'. reflexivity.
  - reflexivity.
  - fo_hyp.
  - cbn [FOsubst_f FOsubst_t Nat.eqb].
    rewrite (FOsubst_t_not_in t 1 (#w)) by exact Ht1.
    apply (FOPrH_weaken n (G ++ [t .= .S #w])); [|exact HS].
    intros H Hin. apply in_app_or in Hin. apply in_or_app.
    destruct Hin as [Hin|Hin].
    + left. apply in_or_app. left. exact Hin.
    + right. exact Hin.
Qed.

Ltac fo_cases t w :=
  lazymatch goal with
  | |- FOPrH ?k ?G ?C =>
      refine (FOPrH_cases_zs k G t w C _ _ _ _ _ _ _);
      [lia | reflexivity | fo_fresh | vm_compute; reflexivity | reflexivity | |]
  end.

(** ** Rules with precomputed substitution results.

    Each rule takes the substituted formula as a separate argument,
    equated to the substitution by a computation, so tactics evaluate
    only that formula and never the whole context. *)

Lemma FOPrH_exe' : forall n G z w A A' C,
  FOPrH n G (FOExists z A) ->
  FOfree_ctx w G -> FOfree_in w C = false -> FOfree_in w A = false ->
  FOsubst_ok z (FOVar w) A = true -> FOsubst_f z (FOVar w) A = A' ->
  FOPrH n (G ++ [A']) C -> FOPrH n G C.
Proof.
  intros n G z w A A' C HE HG HC HA Hok HA' HB. subst A'.
  exact (FOPrH_exe n G z w A C HE HG HC HA Hok HB).
Qed.

Lemma FOPrH_exi' : forall n G x t A A',
  FOsubst_ok x t A = true -> FOsubst_f x t A = A' ->
  FOPrH n G A' -> FOPrH n G (FOExists x A).
Proof.
  intros n G x t A A' Hok HA' H. subst A'. exact (FOPrH_ex_intro n G x t A Hok H).
Qed.

Lemma FOPrH_inst' : forall n G x t A A',
  FOPrH n G (FOForall x A) -> FOsubst_ok x t A = true ->
  FOsubst_f x t A = A' -> FOPrH n G A'.
Proof.
  intros n G x t A A' H Hok HA'. subst A'. exact (FOPrH_all_elim n G x t A Hok H).
Qed.

Lemma FOPrH_ind' : forall n G x A A0 AS,
  FOfree_ctx x G ->
  FOsubst_f x FOZero A = A0 -> FOsubst_f x (FOSucc (FOVar x)) A = AS ->
  FOPrH n G A0 -> FOPrH n (G ++ [A]) AS -> FOPrH n G (FOForall x A).
Proof.
  intros n G x A A0 AS HG H0 HS HB HT. subst A0 AS.
  exact (FOPrH_ind n G x A HG HB HT).
Qed.

Ltac fo_exe_from H w :=
  lazymatch type of H with
  | FOPrH ?k ?G ?F =>
      let F' := eval lazy in F in
      lazymatch F' with
      | FOExists ?z ?A =>
          let A' := eval lazy in (FOsubst_f z (FOVar w) A) in
          lazymatch goal with
          | |- FOPrH _ _ ?C =>
              refine (FOPrH_exe' k G z w A A' C (H : FOPrH k G (FOExists z A))
                        _ _ _ _ _ _);
              [ fo_fresh | vm_compute; exact eq_refl | vm_compute; exact eq_refl
              | vm_compute; exact eq_refl | vm_compute; exact eq_refl | ]
          end
      end
  end.

(** [fo_exe z w] eliminates the most recently added existential over
    [z] in the context. *)

Ltac fo_exe z w :=
  lazymatch goal with
  | |- FOPrH ?k ?G _ =>
      let r := eval vm_compute in (FOlast_ex z G) in
      lazymatch r with
      | Some ?A =>
          let H := fresh "HE" in
          assert (H : FOPrH k G A) by fo_hyp_b;
          fo_exe_from H w; clear H
      end
  end.

Ltac fo_exi_core t :=
  lazymatch goal with
  | |- FOPrH ?k ?G (FOExists ?x ?A) =>
      let A' := eval lazy in (FOsubst_f x t A) in
      refine (FOPrH_exi' k G x t A A' _ _ _);
      [vm_compute; exact eq_refl | vm_compute; exact eq_refl | ]
  end.

Ltac fo_exi t := first [ fo_exi_core t | fo_norm_goal; fo_exi_core t ].

Ltac fo_inst H t :=
  lazymatch type of H with
  | FOPrH _ _ (FOForall ?x ?A) =>
      let A' := eval lazy in (FOsubst_f x t A) in
      let H' := fresh H in
      pose proof (FOPrH_inst' _ _ x t A A' H ltac:(vm_compute; exact eq_refl)
                    ltac:(vm_compute; exact eq_refl)) as H'
  end.

Ltac fo_ind :=
  lazymatch goal with
  | |- FOPrH ?k ?G (FOForall ?x ?A) =>
      let A0 := eval lazy in (FOsubst_f x FOZero A) in
      let AS := eval lazy in (FOsubst_f x (FOSucc (FOVar x)) A) in
      refine (FOPrH_ind' k G x A A0 AS _ _ _ _ _);
      [fo_fresh | vm_compute; exact eq_refl | vm_compute; exact eq_refl | | ]
  end.

Ltac fo_all :=
  lazymatch goal with
  | |- FOPrH ?k ?G (FOForall ?x ?A) => refine (FOPrH_all_intro k G x A _ _); [fo_fresh|]
  | |- _ => apply FOPrH_all_intro; [fo_fresh|]
  end.

(** Introducing a universal at another variable: [fo_all_as w] proves
    [forall z, A] through [forall w, A[z:=w]], so that derivations can
    keep their variables away from the binders of the lemmas they
    instantiate. *)

Lemma FOPrH_all_rename : forall n G z w A A',
  FOfree_ctx z G -> FOfree_in w A = false ->
  FOsubst_ok z (FOVar w) A = true -> FOsubst_f z (FOVar w) A = A' ->
  FOPrH n G (FOForall w A') -> FOPrH n G (FOForall z A).
Proof.
  intros n G z w A A' HG Hw Hok HA' H. subst A'.
  apply FOPrH_all_intro; [exact HG|].
  pose proof (FOPrH_all_elim n G w (FOVar z) _ (FOsubst_ok_back A z w Hw Hok) H) as H1.
  rewrite (FOsubst_f_rename_back A z w Hw Hok) in H1. exact H1.
Qed.

Ltac fo_all_as w :=
  lazymatch goal with
  | |- FOPrH ?k ?G (FOForall ?z ?A) =>
      let A' := eval lazy in (FOsubst_f z (FOVar w) A) in
      refine (FOPrH_all_rename k G z w A A' _ _ _ _ _);
      [fo_fresh | vm_compute; exact eq_refl | vm_compute; exact eq_refl
      | vm_compute; exact eq_refl | fo_all]
  end.

Ltac fo_intro :=
  lazymatch goal with
  | |- FOPrH ?k ?G (FOImplF ?A ?B) => refine (FOPrH_intro k G A B _)
  | |- _ => apply FOPrH_intro
  end.

Ltac fo_have H :=
  lazymatch type of H with
  | FOPrH ?k ?G ?A =>
      lazymatch goal with |- FOPrH _ _ ?B => refine (FOPrH_cut k G A B H _) end
  end.

(** [fo_split X Y] adds both halves of a context conjunction
    [FOAnd X Y], each derived in the current context. *)

Ltac fo_split X0 Y0 :=
  let X := fo_normT X0 in let Y := fo_normT Y0 in
  lazymatch goal with
  | |- FOPrH ?k ?G ?C =>
      refine (FOPrH_cut k G X C _ _);
      [refine (FOPrH_and_l k G X Y _); fo_hyp |];
      refine (FOPrH_cut k (G ++ [X]) Y C _ _);
      [refine (FOPrH_and_r k (G ++ [X]) X Y _); fo_hyp |]
  end.

Ltac fo_ctx_thm H T :=
  lazymatch goal with |- FOPrH ?k ?G _ => pose proof (FOPrH_thm k G _ T) as H end.

(** Additive absorption and its contradiction form. *)

Lemma FOPrH_add_eq_self : forall n G a t,
  FOPrH n G (a .+ t .= a) -> FOPrH n G (t .= .0).
Proof.
  intros n G a t H.
  apply (FOPrH_add_cancel n G t .0 a).
  apply (FOPrH_lincomb n G _ _ [(.S .0, a, a .+ t)]);
    [cbn [FOlc_l FOlc_r]; fo_ring|].
  intros k l r Hin. destruct Hin as [Hin|[]]. injection Hin; intros; subst.
  apply FOPrH_eq_sym. exact H.
Qed.

Lemma FOPrH_add_succ_absurd : forall n G a b,
  FOPrH n G (a .+ .S b .= a) -> FOPrH n G FOFalseF.
Proof.
  intros n G a b H.
  exact (FOPrH_Q_succ_nonzero n G b (FOPrH_add_eq_self n G a (.S b) H)).
Qed.

(** Totality of the order. *)

Lemma FOPr_total : forall n,
  FOProvesTn n (.A 400, .A 401,
    FOOr (.E 450, #400 .+ #450 .= #401) (.E 450, #401 .+ .S #450 .= #400)).
Proof.
  intro n.
  change (FOPrH n [] (.A 400, .A 401,
    FOOr (.E 450, #400 .+ #450 .= #401) (.E 450, #401 .+ .S #450 .= #400))).
  fo_norm_goal. fo_all. fo_ind.
  - apply (FOPrH_cases_zs n _ (#400) 500);
      [lia | reflexivity | fo_fresh | reflexivity | reflexivity | |]; cbn [app].
    + apply FOPrH_or_intro_l. fo_exi .0. fo_lin [(.S .0, .0, #400)].
    + apply FOPrH_or_intro_r. fo_exi (#500). fo_lin [(.S .0, #400, .S #500)].
  - cbn [app].
    eapply FOPrH_or_elim; [fo_hyp | |]; cbn [app].
    + fo_exe 450 500. apply FOPrH_or_intro_l. fo_exi (.S #500).
      fo_lin [(.S .0, #401, #400 .+ #500)].
    + fo_exe 450 500.
      apply (FOPrH_cases_zs n _ (#500) 501);
        [lia | reflexivity | fo_fresh | reflexivity | reflexivity | |]; cbn [app].
      * apply FOPrH_or_intro_l. fo_exi .0.
        fo_lin [(.S .0, #401 .+ .S #500, #400); (.S .0, .0, #500)].
      * apply FOPrH_or_intro_r. fo_exi (#501).
        fo_lin [(.S .0, #400, #401 .+ .S #500); (.S .0, #500, .S #501)].
Qed.

Ltac fo_exe_f T0 w :=
  let T := fo_normT T0 in
  lazymatch goal with
  | |- FOPrH ?k ?G _ =>
      let H := fresh "HE" in
      assert (H : FOPrH k G T) by fo_hyp;
      fo_exe_from H w; clear H
  end.

(** Uniqueness of the remainder. *)

Lemma FOPr_rem_unique : forall n,
  FOProvesTn n (.A 400, .A 401, .A 402, .A 403, .A 404, .A 405,
    (#400 .= #402 .* .S #401 .+ #403) .->
    (.E 450, #403 .+ .S #450 .= .S #401) .->
    (#400 .= #404 .* .S #401 .+ #405) .->
    (.E 450, #405 .+ .S #450 .= .S #401) .->
    #403 .= #405).
Proof.
  intro n.
  change (FOPrH n [] (.A 400, .A 401, .A 402, .A 403, .A 404, .A 405,
    (#400 .= #402 .* .S #401 .+ #403) .->
    (.E 450, #403 .+ .S #450 .= .S #401) .->
    (#400 .= #404 .* .S #401 .+ #405) .->
    (.E 450, #405 .+ .S #450 .= .S #401) .->
    #403 .= #405)).
  do 6 fo_all. do 4 fo_intro. cbn [app].
  fo_exe_f (.E 450, #403 .+ .S #450 .= .S #401) 500.
  fo_ctx_thm T (FOPr_total n).
  fo_inst T (#402). fo_inst T0 (#404).
  eapply (FOPrH_or_elim n _ _ _ _ T1); cbn [app].
  - fo_exe_f (.E 450, #402 .+ #450 .= #404) 501.
    apply (FOPrH_cases_zs n _ (#501) 502);
      [lia | reflexivity | fo_fresh | reflexivity | reflexivity | |]; cbn [app].
    + fo_lin [(.S .0, #400, #402 .* .S #401 .+ #403);
              (.S .0, #404 .* .S #401 .+ #405, #400);
              (.S #401, #402 .+ #501, #404); (.S #401, .0, #501)].
    + apply FOPrH_efq.
      apply (FOPrH_add_succ_absurd n _ (.S #401) (#502 .* .S #401 .+ #405 .+ #500)).
      fo_lin [(.S .0, .S #401, #403 .+ .S #500);
              (.S #401, #501, .S #502);
              (.S #401, #404, #402 .+ #501);
              (.S .0, #400, #404 .* .S #401 .+ #405);
              (.S .0, #402 .* .S #401 .+ #403, #400)].
  - fo_exe_f (.E 450, #404 .+ .S #450 .= #402) 501.
    fo_exe_f (.E 450, #405 .+ .S #450 .= .S #401) 502.
    apply FOPrH_efq.
    apply (FOPrH_add_succ_absurd n _ (.S #401) (#501 .* .S #401 .+ #403 .+ #502)).
    fo_lin [(.S .0, .S #401, #405 .+ .S #502);
            (.S #401, #402, #404 .+ .S #501);
            (.S .0, #400, #402 .* .S #401 .+ #403);
            (.S .0, #404 .* .S #401 .+ #405, #400)].
Qed.

(** ** Coprimality in Bezout form, and the Chinese remainder step.

    [FOCPR p q]: [p * u = q * v + 1] for some [u], [v]. *)

Notation FOCPR p q := (.E 456, .E 457, p .* #456 .= q .* #457 .+ .S .0).

Lemma FOPr_cpr_flip : forall n,
  FOProvesTn n (.A 400, .A 401, .A 402, .A 403,
    (#400 .= .S #402) .-> (#401 .= .S #403) .->
    FOCPR #400 #401 .-> FOCPR #401 #400).
Proof.
  intro n.
  change (FOPrH n [] (.A 400, .A 401, .A 402, .A 403,
    (#400 .= .S #402) .-> (#401 .= .S #403) .->
    FOCPR #400 #401 .-> FOCPR #401 #400)).
  do 4 fo_all. do 3 fo_intro. cbn [app].
  fo_exe 456 500. fo_exe 457 501.
  set (K := #500 .+ #501 .+ .S .0).
  fo_exi (K .* #402 .+ #500 .+ .S .0). fo_exi (K .* #403 .+ #501 .+ .S .0).
  apply (FOPrH_lincomb n _ _ _
    [(.S .0, #401 .* #501 .+ .S .0, #400 .* #500);
     (K .* #402 .+ #500 .+ .S .0 .+ #501, .S #403, #401);
     (K .* #403 .+ #501 .+ .S .0 .+ #500, #400, .S #402)]);
    [cbn [FOlc_l FOlc_r]; unfold K; fo_ring | fo_lc_hyps].
Qed.

Lemma FOPr_cpr_prod : forall n,
  FOProvesTn n (.A 400, .A 401, .A 402,
    FOCPR #400 #402 .-> FOCPR #401 #402 .-> FOCPR (#400 .* #401) #402).
Proof.
  intro n.
  change (FOPrH n [] (.A 400, .A 401, .A 402,
    FOCPR #400 #402 .-> FOCPR #401 #402 .-> FOCPR (#400 .* #401) #402)).
  do 3 fo_all. do 2 fo_intro. cbn [app].
  fo_exe_f (FOCPR #400 #402) 500. fo_exe 457 501.
  fo_exe_f (FOCPR #401 #402) 502. fo_exe 457 503.
  fo_exi (#500 .* #502). fo_exi (#402 .* #501 .* #503 .+ #501 .+ #503).
  fo_lin [(#401 .* #502, #402 .* #501 .+ .S .0, #400 .* #500);
          (#402 .* #501 .+ .S .0, #402 .* #503 .+ .S .0, #401 .* #502)].
Qed.

Lemma FOPr_crt_step : forall n,
  FOProvesTn n (.A 400, .A 401, .A 402, .A 403,
    FOCPR #400 #401 .-> FOCPR #401 #400 .->
    .E 463, .E 464, .E 465,
      FOAnd (#463 .= #402 .+ #400 .* #464) (#463 .= #403 .+ #401 .* #465)).
Proof.
  intro n.
  change (FOPrH n [] (.A 400, .A 401, .A 402, .A 403,
    FOCPR #400 #401 .-> FOCPR #401 #400 .->
    .E 463, .E 464, .E 465,
      FOAnd (#463 .= #402 .+ #400 .* #464) (#463 .= #403 .+ #401 .* #465))).
  do 4 fo_all. do 2 fo_intro. cbn [app].
  fo_exe_f (FOCPR #400 #401) 500. fo_exe 457 501.
  fo_exe_f (FOCPR #401 #400) 502. fo_exe 457 503.
  fo_exi (#402 .* #401 .* #502 .+ #403 .* #400 .* #500).
  fo_exi (#402 .* #503 .+ #403 .* #500).
  fo_exi (#402 .* #502 .+ #403 .* #501).
  apply FOPrH_and_intro.
  - fo_lin [(#402, #400 .* #503 .+ .S .0, #401 .* #502)].
  - fo_lin [(#403, #401 .* #501 .+ .S .0, #400 .* #500)].
Qed.

(** A common multiple of the positive numbers up to [M]. *)

Notation FOCMD M D :=
  (.A 460, .A 461, (.S #460 .+ #461 .= M) .-> .E 462, .S #460 .* #462 .= D).

Lemma FOPr_common_mult : forall n,
  FOProvesTn n (.A 400, .E 458, .E 459,
    FOAnd (#458 .= .S #459) (FOCMD #400 #458)).
Proof.
  intro n.
  change (FOPrH n [] (.A 400, .E 458, .E 459,
    FOAnd (#458 .= .S #459) (FOCMD #400 #458))).
  fo_norm_goal. fo_ind.
  - fo_exi (.S .0). fo_exi .0. apply FOPrH_and_intro; [apply FOPrH_refl|].
    do 2 fo_all. fo_intro. cbn [app]. apply FOPrH_efq.
    apply (FOPrH_Q_succ_nonzero n _ (#460)).
    apply (FOPrH_add_zero_l n _ _ (#461)). fo_hyp.
  - cbn [app].
    fo_exe 458 500. fo_exe 459 501.
    fo_split (#500 .= .S #501) (FOCMD #400 #500).
    fo_exi (#500 .* .S #400). fo_exi (#501 .* .S #400 .+ #400).
    apply FOPrH_and_intro; [fo_lin [(.S #400, .S #501, #500)]|].
    do 2 fo_all. fo_intro. cbn [app].
    apply (FOPrH_cases_zs n _ (#461) 502);
      [lia | reflexivity | fo_fresh | reflexivity | reflexivity | |]; cbn [app].
    + fo_exi (#500).
      fo_lin [(#500, .S #400, .S #460 .+ #461); (#500, #461, .0)].
    + match goal with |- FOPrH _ ?G _ =>
        assert (Dv : FOPrH n G (FOCMD #400 #500)) by fo_hyp end.
      fo_inst Dv (#460). fo_inst Dv0 (#502).
      match goal with |- FOPrH _ ?G _ =>
        assert (Hle : FOPrH n G (.S #460 .+ #502 .= #400)) end.
      { apply (FOPrH_add_cancel n _ _ _ (.S .0)).
        fo_lin [(.S .0, .S #400, .S #460 .+ #461); (.S .0, #461, .S #502)]. }
      pose proof (FOPrH_mp n _ _ _ Dv1 Hle) as Dw.
      fo_exe_from Dw 503.
      fo_exi (#503 .* .S #400).
      fo_lin [(.S #400, #500, .S #460 .* #503)].
Qed.

(** The beta function is total. *)

Lemma FOPr_beta_total : forall n,
  FOProvesTn n (.A 420, .A 421, .A 422, .E 470, FObetaF 480 #420 #421 #422 #470).
Proof.
  intro n.
  change (FOPrH n [] (.A 420, .A 421, .A 422, .E 470, FObetaF 480 #420 #421 #422 #470)).
  do 3 fo_all.
  fo_ctx_thm Dv (FOPr_div_exists n).
  fo_inst Dv (#421 .* .S #422). fo_inst Dv0 (#420).
  fo_exe_from Dv1 500. fo_exe 3 501.
  fo_split (#420 .= .S (#421 .* .S #422) .* #500 .+ #501)
           (.E 4, #501 .+ .S #4 .= .S (#421 .* .S #422)).
  fo_exe 4 502.
  unfold FObetaF, FOBexC.
  fo_exi (#501). fo_exi (#500).
  apply FOPrH_and_intro.
  - fo_exi (#500 .* (#421 .* .S #422) .+ #501).
    fo_lin [(.S .0, #420, .S (#421 .* .S #422) .* #500 .+ #501)].
  - apply FOPrH_and_intro.
    + fo_lin [(.S .0, .S (#421 .* .S #422) .* #500 .+ #501, #420)].
    + fo_exi (#502). apply FOPrH_and_intro.
      * fo_exi (#501). fo_lin [(.S .0, .S (#421 .* .S #422), #501 .+ .S #502)].
      * fo_hyp.
Qed.

Ltac fo_assert H T0 :=
  let T := fo_normT T0 in
  lazymatch goal with |- FOPrH ?k ?G _ => assert (H : FOPrH k G T) end.

(** The beta moduli [S (D * S i)] and [S (D * S j)] are coprime when
    [j - i] divides [D]. *)

Lemma FOPr_mod_cpr : forall n,
  FOProvesTn n (.A 400, .A 401, .A 402, .A 403, .A 404,
    (#400 .= .S #401) .-> (.S #403 .* #404 .= #400) .->
    FOCPR (.S (#400 .* .S #402)) (.S (#400 .* .S (#402 .+ .S #403)))).
Proof.
  intro n.
  change (FOPrH n [] (.A 400, .A 401, .A 402, .A 403, .A 404,
    (#400 .= .S #401) .-> (.S #403 .* #404 .= #400) .->
    FOCPR (.S (#400 .* .S #402)) (.S (#400 .* .S (#402 .+ .S #403))))).
  fo_all_as 600. fo_all_as 601. fo_all_as 602. fo_all_as 603. fo_all_as 604.
  do 2 fo_intro. cbn [app].
  fo_assert H1 (#600 .= .S #601). { fo_hyp. }
  fo_assert C1 (FOCPR (.S (#600 .* .S #602)) #600).
  { fo_exi (.S .0). fo_exi (.S #602). apply FOPrH_ring. fo_ring. }
  fo_ctx_thm F (FOPr_cpr_flip n).
  fo_inst F (.S (#600 .* .S #602)). fo_inst F0 (#600).
  fo_inst F1 (#600 .* .S #602). fo_inst F2 (#601).
  pose proof (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ F3
                (FOPrH_refl n _ _)) H1) C1) as C2.
  fo_assert C3 (FOCPR (.S (#600 .* .S #602)) (.S #603)).
  { fo_exi (.S .0). fo_exi (#604 .* .S #602).
    fo_lin [(.S #602, .S #603 .* #604, #600)]. }
  fo_inst F (.S (#600 .* .S #602)). rename F4 into G0.
  fo_inst G0 (.S #603). fo_inst G1 (#600 .* .S #602). fo_inst G2 (#603).
  pose proof (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ G3
                (FOPrH_refl n _ _)) (FOPrH_refl n _ _)) C3) as C4.
  fo_ctx_thm P (FOPr_cpr_prod n).
  fo_inst P (#600). fo_inst P0 (.S #603). fo_inst P1 (.S (#600 .* .S #602)).
  pose proof (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ P2 C2) C4) as C5.
  fo_assert E5 (#600 .* .S #603 .= .S (#601 .* .S #603 .+ #603)).
  { fo_lin [(.S #603, .S #601, #600)]. }
  fo_inst F (#600 .* .S #603). rename F4 into K0.
  fo_inst K0 (.S (#600 .* .S #602)). fo_inst K1 (#601 .* .S #603 .+ #603).
  fo_inst K2 (#600 .* .S #602).
  pose proof (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ K3 E5)
                (FOPrH_refl n _ _)) C5) as C6.
  fo_exe_from C6 700. fo_exe 457 701.
  fo_exi (#700 .+ #701). fo_exi (#701).
  fo_lin [(.S .0, #600 .* .S #603 .* #701 .+ .S .0, .S (#600 .* .S #602) .* #700)].
Qed.

(** The element relation of the extended sequence: position [i] holds
    [y] when [i < l] and [beta c d i = y], or [i = l] and [y = x]. *)

Notation FOYREL i y :=
  (FOOr (FOAnd (.E 475, i .+ .S #475 .= #422) (FObetaF 480 #420 #421 i y))
        (FOAnd (i .= #422) (y .= #423))).

Lemma FOPr_Y_unique : forall n,
  FOProvesTn n (.A 420, .A 421, .A 422, .A 423, .A 463, .A 465, .A 466,
    FOYREL #463 #465 .-> FOYREL #463 #466 .-> #465 .= #466).
Proof.
  intro n.
  change (FOPrH n [] (.A 420, .A 421, .A 422, .A 423, .A 463, .A 465, .A 466,
    FOYREL #463 #465 .-> FOYREL #463 #466 .-> #465 .= #466)).
  fo_norm_goal.
  do 7 fo_all. do 2 fo_intro. cbn [app].
  fo_assert Y1 (FOYREL #463 #465). { fo_hyp. }
  apply (FOPrH_or_elim n _ _ _ _ Y1); clear Y1.
  - fo_split (.E 475, #463 .+ .S #475 .= #422) (FObetaF 480 #420 #421 #463 #465).
    fo_assert Y2 (FOYREL #463 #466). { fo_hyp. }
    apply (FOPrH_or_elim n _ _ _ _ Y2); clear Y2.
    + fo_split (.E 475, #463 .+ .S #475 .= #422) (FObetaF 480 #420 #421 #463 #466).
      fo_assert B1 (FObetaF 480 #420 #421 #463 #465). { fo_hyp. }
      fo_exe_from B1 500. clear B1.
      fo_split (.E 481, #500 .+ .S #481 .= .S #420)
               (FOAnd (#420 .= #500 .* .S (#421 .* .S #463) .+ #465)
                      (.E 482, FOAnd (.E 483, #482 .+ .S #483 .= .S (#421 .* .S #463))
                                     (#465 .+ .S #482 .= .S (#421 .* .S #463)))).
      fo_split (#420 .= #500 .* .S (#421 .* .S #463) .+ #465)
               (.E 482, FOAnd (.E 483, #482 .+ .S #483 .= .S (#421 .* .S #463))
                              (#465 .+ .S #482 .= .S (#421 .* .S #463))).
      fo_exe 482 501.
      fo_split (.E 483, #501 .+ .S #483 .= .S (#421 .* .S #463))
               (#465 .+ .S #501 .= .S (#421 .* .S #463)).
      fo_assert B2 (FObetaF 480 #420 #421 #463 #466). { fo_hyp. }
      fo_exe_from B2 502. clear B2.
      fo_split (.E 481, #502 .+ .S #481 .= .S #420)
               (FOAnd (#420 .= #502 .* .S (#421 .* .S #463) .+ #466)
                      (.E 482, FOAnd (.E 483, #482 .+ .S #483 .= .S (#421 .* .S #463))
                                     (#466 .+ .S #482 .= .S (#421 .* .S #463)))).
      fo_split (#420 .= #502 .* .S (#421 .* .S #463) .+ #466)
               (.E 482, FOAnd (.E 483, #482 .+ .S #483 .= .S (#421 .* .S #463))
                              (#466 .+ .S #482 .= .S (#421 .* .S #463))).
      fo_exe 482 503.
      fo_split (.E 483, #503 .+ .S #483 .= .S (#421 .* .S #463))
               (#466 .+ .S #503 .= .S (#421 .* .S #463)).
      fo_ctx_thm R (FOPr_rem_unique n).
      fo_inst R (#420). fo_inst R0 (#421 .* .S #463). fo_inst R1 (#500).
      fo_inst R2 (#465). fo_inst R3 (#502). fo_inst R4 (#466).
      apply (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _
               (FOPrH_mp n _ _ _ R5 ltac:(fo_hyp)) ltac:(fo_exi (#501); fo_hyp))
               ltac:(fo_hyp)) ltac:(fo_exi (#503); fo_hyp)).
    + fo_split (#463 .= #422) (#466 .= #423).
      fo_exe_f (.E 475, #463 .+ .S #475 .= #422) 500.
      apply FOPrH_efq. apply (FOPrH_add_succ_absurd n _ (#422) (#500)).
      fo_lin [(.S .0, #422, #463 .+ .S #500); (.S .0, #463, #422)].
  - fo_split (#463 .= #422) (#465 .= #423).
    fo_assert Y2 (FOYREL #463 #466). { fo_hyp. }
    apply (FOPrH_or_elim n _ _ _ _ Y2); clear Y2.
    + fo_split (.E 475, #463 .+ .S #475 .= #422) (FObetaF 480 #420 #421 #463 #466).
      fo_exe_f (.E 475, #463 .+ .S #475 .= #422) 500.
      apply FOPrH_efq. apply (FOPrH_add_succ_absurd n _ (#422) (#500)).
      fo_lin [(.S .0, #422, #463 .+ .S #500); (.S .0, #463, #422)].
    + fo_split (#463 .= #422) (#466 .= #423).
      fo_lin [(.S .0, #423, #465); (.S .0, #466, #423)].
Qed.

(** ** The invariant of the iterated Chinese remainder construction.

    With moduli [NM D i = S (D * S i)], a product [P] and a code [c]:
    [FODIVALL D P k] says every modulus below [k] divides [P];
    [FOCONG D c k] says [c] meets every element of the extended
    sequence below [k] modulo its modulus; [FOCOPALL D P k] says [P] is
    coprime to every modulus from [k] up to [l]. *)

Notation FONM D i := (.S (D .* .S i)).

Notation FODIVALL D P k :=
  (.A 463, (.E 473, #463 .+ .S #473 .= k) .-> .E 464, FONM D #463 .* #464 .= P).

Notation FOCONG D c k :=
  (.A 463, (.E 473, #463 .+ .S #473 .= k) .->
     .A 465, FOYREL #463 #465 .-> .E 466, c .= #465 .+ FONM D #463 .* #466).

Notation FOCOPALL D P k :=
  (.A 463, (.E 473, k .+ #473 .= #463) .-> (.E 474, #463 .+ #474 .= #422) .->
     FOCPR P (FONM D #463)).

Lemma FOPr_divall_step : forall n,
  FOProvesTn n (.A 600, .A 601, .A 602,
    FODIVALL #600 #601 #602 .->
    FODIVALL #600 (#601 .* FONM #600 #602) (.S #602)).
Proof.
  intro n.
  change (FOPrH n [] (.A 600, .A 601, .A 602,
    FODIVALL #600 #601 #602 .->
    FODIVALL #600 (#601 .* FONM #600 #602) (.S #602))).
  fo_norm_goal.
  do 3 fo_all. fo_intro.
  fo_all. fo_intro.
  fo_exe 473 700.
  fo_cases (#700) 701.
  - fo_exi (#601).
    fo_lin [(#601 .* #600, .S #602, #463 .+ .S #700); (#601 .* #600, #700, .0)].
  - fo_assert DA (FODIVALL #600 #601 #602). { fo_hyp. }
    fo_inst DA (#463).
    fo_assert Hlt (.E 473, #463 .+ .S #473 .= #602).
    { fo_exi (#701). fo_lin [(.S .0, .S #602, #463 .+ .S #700); (.S .0, #700, .S #701)]. }
    pose proof (FOPrH_mp n _ _ _ DA0 Hlt) as DA1.
    fo_exe_from DA1 702.
    fo_exi (#702 .* FONM #600 #602).
    fo_lin [(FONM #600 #602, #601, FONM #600 #463 .* #702)].
Qed.

Lemma FOPr_cong_step : forall n,
  FOProvesTn n (.A 600, .A 601, .A 602, .A 603, .A 604, .A 605, .A 606, .A 607,
    FODIVALL #600 #601 #604 .-> FOCONG #600 #602 #604 .->
    FOYREL #604 #605 .->
    (#603 .= #602 .+ #601 .* #606) .->
    (#603 .= #605 .+ FONM #600 #604 .* #607) .->
    FOCONG #600 #603 (.S #604)).
Proof.
  intro n.
  change (FOPrH n [] (.A 600, .A 601, .A 602, .A 603, .A 604, .A 605, .A 606, .A 607,
    FODIVALL #600 #601 #604 .-> FOCONG #600 #602 #604 .->
    FOYREL #604 #605 .->
    (#603 .= #602 .+ #601 .* #606) .->
    (#603 .= #605 .+ FONM #600 #604 .* #607) .->
    FOCONG #600 #603 (.S #604))).
  fo_norm_goal.
  do 8 fo_all. do 5 fo_intro.
  fo_all. fo_intro. fo_all. fo_intro.
  fo_exe 473 700.
  fo_cases (#700) 701.
  - fo_assert Eik (#463 .= #604).
    { fo_lin [(.S .0, .S #604, #463 .+ .S #700); (.S .0, #700, .0)]. }
    fo_assert Yk (FOYREL #604 #465).
    { apply (FOPrH_leibniz n _ 699 (#463) (#604) (FOYREL #699 #465));
        [vm_compute; exact eq_refl | vm_compute; exact eq_refl | exact Eik |].
      fo_norm_goal. fo_hyp. }
    fo_ctx_thm U (FOPr_Y_unique n).
    fo_inst U (#420). fo_inst U0 (#421). fo_inst U1 (#422). fo_inst U2 (#423).
    fo_inst U3 (#604). fo_inst U4 (#465). fo_inst U5 (#605).
    pose proof (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ U6 Yk) ltac:(fo_hyp)) as E.
    fo_have E. clear U U0 U1 U2 U3 U4 U5 U6 Yk Eik.
    fo_exi (#607).
    fo_lin [(.S .0, #605 .+ FONM #600 #604 .* #607, #603);
            (.S .0, #465, #605);
            (#607 .* #600, #463 .+ .S #700, .S #604);
            (#607 .* #600, .0, #700)].
  - fo_assert CG (FOCONG #600 #602 #604). { fo_hyp. }
    fo_inst CG (#463).
    fo_assert Hlt (.E 473, #463 .+ .S #473 .= #604).
    { fo_exi (#701). fo_lin [(.S .0, .S #604, #463 .+ .S #700); (.S .0, #700, .S #701)]. }
    pose proof (FOPrH_mp n _ _ _ CG0 Hlt) as CG1.
    fo_inst CG1 (#465).
    pose proof (FOPrH_mp n _ _ _ CG2 ltac:(fo_hyp)) as CG3.
    fo_assert DA (FODIVALL #600 #601 #604). { fo_hyp. }
    fo_inst DA (#463).
    pose proof (FOPrH_mp n _ _ _ DA0 Hlt) as DA1.
    fo_exe_from CG3 702. clear CG CG0 CG1 CG2 CG3.
    match goal with |- FOPrH _ ?G _ =>
      pose proof (FOPrH_weaken n _ G _ ltac:(intros H Hin; apply in_or_app; left; exact Hin) DA1) as DA2 end.
    fo_exe_from DA2 703. clear DA DA0 DA1 DA2 Hlt.
    fo_exi (#702 .+ #703 .* #606).
    fo_lin [(.S .0, #602 .+ #601 .* #606, #603);
            (.S .0, #465 .+ FONM #600 #463 .* #702, #602);
            (#606, FONM #600 #463 .* #703, #601)].
Qed.

Lemma FOPr_copall_step : forall n,
  FOProvesTn n (.A 600, .A 601, .A 602, .A 603,
    (#600 .= .S #601) .-> FOCMD #422 #600 .->
    FOCOPALL #600 #602 #603 .->
    FOCOPALL #600 (#602 .* FONM #600 #603) (.S #603)).
Proof.
  intro n.
  change (FOPrH n [] (.A 600, .A 601, .A 602, .A 603,
    (#600 .= .S #601) .-> FOCMD #422 #600 .->
    FOCOPALL #600 #602 #603 .->
    FOCOPALL #600 (#602 .* FONM #600 #603) (.S #603))).
  fo_norm_goal.
  do 4 fo_all. do 3 fo_intro.
  fo_all. do 2 fo_intro.
  fo_exe 473 700. fo_exe 474 701.
  fo_assert CA (FOCOPALL #600 #602 #603). { fo_hyp. }
  fo_inst CA (#463).
  fo_assert Hle (.E 473, #603 .+ #473 .= #463).
  { fo_exi (.S #700). fo_lin [(.S .0, #463, .S #603 .+ #700)]. }
  pose proof (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ CA0 Hle) ltac:(fo_exi (#701); fo_hyp)) as C1.
  fo_assert CM (FOCMD #422 #600). { fo_hyp. }
  fo_inst CM (#700). fo_inst CM0 (#603 .+ #701).
  fo_assert Hs (.S #700 .+ (#603 .+ #701) .= #422).
  { fo_lin [(.S .0, #422, #463 .+ #701); (.S .0, #463, .S #603 .+ #700)]. }
  pose proof (FOPrH_mp n _ _ _ CM1 Hs) as CM2.
  fo_have C1. clear CA CA0 Hle CM CM0 CM1 Hs.
  match goal with |- FOPrH _ ?G _ =>
    pose proof (FOPrH_weaken n _ G _ ltac:(intros H Hin; apply in_or_app; left; exact Hin) CM2) as CM3 end.
  fo_exe_from CM3 702. clear CM2 CM3.
  fo_ctx_thm M (FOPr_mod_cpr n).
  fo_inst M (#600). fo_inst M0 (#601). fo_inst M1 (#603). fo_inst M2 (#700).
  fo_inst M3 (#702).
  pose proof (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ M4 ltac:(fo_hyp)) ltac:(fo_hyp)) as C2.
  fo_assert Ej (#603 .+ .S #700 .= #463). { fo_lin [(.S .0, #463, .S #603 .+ #700)]. }
  fo_assert C3 (FOCPR (FONM #600 #603) (FONM #600 #463)).
  { apply (FOPrH_leibniz n _ 698 (#603 .+ .S #700) (#463)
             (FOCPR (FONM #600 #603) (.S (#600 .* .S #698))));
      [vm_compute; exact eq_refl | vm_compute; exact eq_refl | exact Ej | exact C2]. }
  fo_ctx_thm P (FOPr_cpr_prod n).
  fo_inst P (#602). fo_inst P0 (FONM #600 #603). fo_inst P1 (FONM #600 #463).
  exact (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ P2 ltac:(fo_hyp)) C3).
Qed.


(** The iterated construction: for every [k <= S l] a code [c] and a
    positive product [P] satisfying the invariant below [k]. *)

Notation FOPSI D k :=
  ((.E 472, k .+ #472 .= .S #422) .->
   .E 460, .E 461, FOAnd (.E 462, #461 .= .S #462)
                     (FOAnd (FODIVALL D #461 k)
                            (FOAnd (FOCONG D #460 k) (FOCOPALL D #461 k)))).

Lemma FOPr_crt_iter : forall n,
  FOProvesTn n (.A 420, .A 421, .A 422, .A 423, .A 424, .A 425,
    (#424 .= .S #425) .-> FOCMD #422 #424 .-> .A 430, FOPSI #424 #430).
Proof.
  intro n.
  change (FOPrH n [] (.A 420, .A 421, .A 422, .A 423, .A 424, .A 425,
    (#424 .= .S #425) .-> FOCMD #422 #424 .-> .A 430, FOPSI #424 #430)).
  fo_norm_goal.
  do 6 fo_all. do 2 fo_intro.
  fo_ind.
  - fo_intro. fo_exi (.0). fo_exi (.S .0).
    apply FOPrH_and_intro; [fo_exi (.0); apply FOPrH_refl|].
    apply FOPrH_and_intro; [|apply FOPrH_and_intro].
    + fo_all. fo_intro. fo_exe 473 700. apply FOPrH_efq.
      apply (FOPrH_Q_succ_nonzero n _ (#463 .+ #700)).
      fo_lin [(.S .0, .0, #463 .+ .S #700)].
    + fo_all. fo_intro. fo_exe 473 700. apply FOPrH_efq.
      apply (FOPrH_Q_succ_nonzero n _ (#463 .+ #700)).
      fo_lin [(.S .0, .0, #463 .+ .S #700)].
    + fo_all. do 2 fo_intro. fo_exi (.S .0). fo_exi (.0). apply FOPrH_ring. fo_ring.
  - fo_intro. fo_exe 472 700.
    fo_assert Hk (.E 472, #430 .+ #472 .= .S #422).
    { fo_exi (.S #700). fo_lin [(.S .0, .S #422, .S #430 .+ #700)]. }
    fo_assert IH (FOPSI #424 #430). { fo_hyp. }
    pose proof (FOPrH_mp n _ _ _ IH Hk) as IH1. clear IH Hk.
    fo_exe_from IH1 701. clear IH1. fo_exe 461 702.
    fo_split (.E 462, #702 .= .S #462)
             (FOAnd (FODIVALL #424 #702 #430)
                    (FOAnd (FOCONG #424 #701 #430) (FOCOPALL #424 #702 #430))).
    fo_split (FODIVALL #424 #702 #430)
             (FOAnd (FOCONG #424 #701 #430) (FOCOPALL #424 #702 #430)).
    fo_split (FOCONG #424 #701 #430) (FOCOPALL #424 #702 #430).
    fo_exe_f (.E 462, #702 .= .S #462) 703.
    fo_assert Hkl (#430 .+ #700 .= #422).
    { fo_lin [(.S .0, .S #422, .S #430 .+ #700)]. }
    fo_have Hkl. clear Hkl.
    (* P is coprime to the k-th modulus, both ways *)
    fo_assert CA (FOCOPALL #424 #702 #430). { fo_hyp. }
    fo_inst CA (#430).
    fo_assert C0 (FOCPR #702 (FONM #424 #430)).
    { apply (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ CA0
               ltac:(fo_exi (.0); apply FOPrH_Q_plus_zero))).
      fo_exi (#700). fo_hyp. }
    fo_have C0. clear CA CA0 C0.
    fo_ctx_thm F (FOPr_cpr_flip n).
    fo_inst F (#702). fo_inst F0 (FONM #424 #430). fo_inst F1 (#703).
    fo_inst F2 (#424 .* .S #430).
    fo_assert C1 (FOCPR (FONM #424 #430) #702).
    { exact (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ F3 ltac:(fo_hyp))
               (FOPrH_refl n _ _)) ltac:(fo_hyp)). }
    fo_have C1. clear F F0 F1 F2 F3 C1.
    (* the k-th element of the extended sequence *)
    fo_assert Hy (.E 476, FOYREL #430 #476).
    { fo_cases (#700) 704.
      - fo_exi (#423). apply FOPrH_or_intro_r. apply FOPrH_and_intro.
        + fo_lin [(.S .0, #422, #430 .+ #700); (.S .0, #700, .0)].
        + apply FOPrH_refl.
      - fo_ctx_thm B (FOPr_beta_total n).
        fo_inst B (#420). fo_inst B0 (#421). fo_inst B1 (#430).
        fo_exe_from B2 705.
        fo_exi (#705). apply FOPrH_or_intro_l. apply FOPrH_and_intro.
        + fo_exi (#704). fo_lin [(.S .0, #422, #430 .+ #700); (.S .0, #700, .S #704)].
        + fo_hyp. }
    fo_exe_from Hy 706. clear Hy.
    (* one Chinese remainder step *)
    fo_ctx_thm R (FOPr_crt_step n).
    fo_inst R (#702). fo_inst R0 (FONM #424 #430). fo_inst R1 (#701). fo_inst R2 (#706).
    pose proof (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ R3 ltac:(fo_hyp)) ltac:(fo_hyp)) as Z.
    clear R R0 R1 R2 R3.
    fo_exe_from Z 707. clear Z. fo_exe 464 708. fo_exe 465 709.
    fo_split (#707 .= #701 .+ #702 .* #708) (#707 .= #706 .+ FONM #424 #430 .* #709).
    fo_exi (#707). fo_exi (#702 .* FONM #424 #430).
    apply FOPrH_and_intro; [|apply FOPrH_and_intro; [|apply FOPrH_and_intro]].
    + fo_exi (#703 .* FONM #424 #430 .+ #424 .* .S #430).
      fo_lin [(FONM #424 #430, .S #703, #702)].
    + fo_ctx_thm DS (FOPr_divall_step n).
      fo_inst DS (#424). fo_inst DS0 (#702). fo_inst DS1 (#430).
      exact (FOPrH_mp n _ _ _ DS2 ltac:(fo_hyp)).
    + fo_ctx_thm CS (FOPr_cong_step n).
      fo_inst CS (#424). fo_inst CS0 (#702). fo_inst CS1 (#701). fo_inst CS2 (#707).
      fo_inst CS3 (#430). fo_inst CS4 (#706). fo_inst CS5 (#708). fo_inst CS6 (#709).
      exact (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _
               (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ CS7 ltac:(fo_hyp)) ltac:(fo_hyp))
               ltac:(fo_hyp)) ltac:(fo_hyp)) ltac:(fo_hyp)).
    + fo_ctx_thm PS (FOPr_copall_step n).
      fo_inst PS (#424). fo_inst PS0 (#425). fo_inst PS1 (#702). fo_inst PS2 (#430).
      exact (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ PS3 ltac:(fo_hyp))
               ltac:(fo_hyp)) ltac:(fo_hyp)).
Qed.


(** ** Extending a beta-coded sequence.

    Inside the tower: for every code [c, d], length [l], new element
    [x] and bound [b] there is a code [c', d'] with [c' >= b] that
    agrees with [c, d] below [l] and holds [x] at [l]. *)

Notation FOBETAEXT :=
  (.A 420, .A 421, .A 422, .A 423, .A 426,
     .E 466, .E 467,
       FOAnd (.E 468, #426 .+ #468 .= #466)
         (FOAnd (.A 469, (.E 470, #469 .+ .S #470 .= #422) .->
                   .A 471, FObetaF 480 #420 #421 #469 #471 .->
                           FObetaF 484 #466 #467 #469 #471)
                (FObetaF 488 #466 #467 #422 #423))).

Local Notation FOMM := (#420 .+ #422 .+ #423 .+ .S .0).
Local Notation FOMM' := (#420 .+ #422 .+ #423).
Local Notation FOC1 := (#704 .+ #705 .* #426).
Local Notation FOQ1 := (#708 .+ #709 .* #426).
Local Notation FOE1 :=
  (#700 .* #469 .+ #710 .* .S (#421 .* .S #469) .+ #422 .+ #423 .+ .S .0
   .+ FOMM .* #703).
Local Notation FOQ2 := (#707 .+ #708 .* #426).
Local Notation FOE2 := (#700 .* #422 .+ #420 .+ #422 .+ .S .0 .+ FOMM .* #703).

Lemma FOPr_beta_extend : forall n, FOProvesTn n FOBETAEXT.
Proof.
  intro n. change (FOPrH n [] FOBETAEXT). fo_norm_goal.
  do 5 fo_all.
  (* a common multiple D of 1..M, with D = M * S t *)
  fo_ctx_thm CMt (FOPr_common_mult n).
  fo_inst CMt constr:(FOMM). fo_exe_from CMt0 700. clear CMt CMt0. fo_exe 459 701.
  fo_split (#700 .= .S #701) (FOCMD FOMM #700).
  fo_assert HM (FOCMD FOMM #700). { fo_hyp. }
  fo_inst HM constr:(FOMM'). fo_inst HM0 (.0).
  pose proof (FOPrH_mp n _ _ _ HM1 ltac:(apply FOPrH_ring; fo_ring)) as HM2.
  clear HM HM0 HM1.
  fo_exe_from HM2 702. clear HM2.
  fo_cases (#702) 703.
  { apply FOPrH_efq. apply (FOPrH_Q_succ_nonzero n _ (#701)).
    fo_lin [(.S .0, #700, .S #701); (.S .0, .S FOMM' .* #702, #700);
            (.S FOMM', .0, #702)]. }
  (* the common multiple covers every length up to l *)
  fo_assert HCl (FOCMD #422 #700).
  { fo_all. fo_all. fo_intro.
    fo_assert HM (FOCMD FOMM #700). { fo_hyp. }
    fo_inst HM (#460). fo_inst HM0 (#461 .+ #420 .+ #423 .+ .S .0).
    apply (FOPrH_mp n _ _ _ HM1).
    fo_lin [(.S .0, #422, .S #460 .+ #461)]. }
  fo_have HCl. clear HCl.
  (* the iterated construction up to S l *)
  fo_ctx_thm IT (FOPr_crt_iter n).
  fo_inst IT (#420). fo_inst IT0 (#421). fo_inst IT1 (#422). fo_inst IT2 (#423).
  fo_inst IT3 (#700). fo_inst IT4 (#701).
  pose proof (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ IT5 ltac:(fo_hyp)) ltac:(fo_hyp)) as IT6.
  fo_inst IT6 (.S #422).
  pose proof (FOPrH_mp n _ _ _ IT7 ltac:(fo_exi (.0); apply FOPrH_Q_plus_zero)) as IT8.
  clear IT IT0 IT1 IT2 IT3 IT4 IT5 IT6 IT7.
  fo_exe_from IT8 704. clear IT8. fo_exe 461 705.
  fo_split (.E 462, #705 .= .S #462)
           (FOAnd (FODIVALL #700 #705 (.S #422))
                  (FOAnd (FOCONG #700 #704 (.S #422)) (FOCOPALL #700 #705 (.S #422)))).
  fo_split (FODIVALL #700 #705 (.S #422))
           (FOAnd (FOCONG #700 #704 (.S #422)) (FOCOPALL #700 #705 (.S #422))).
  fo_split (FOCONG #700 #704 (.S #422)) (FOCOPALL #700 #705 (.S #422)).
  fo_exe_f (.E 462, #705 .= .S #462) 706.
  fo_exi constr:(FOC1). fo_exi (#700).
  apply FOPrH_and_intro; [|apply FOPrH_and_intro].
  - fo_exi (#704 .+ #706 .* #426).
    fo_lin [(#426, #705, .S #706)].
  - fo_all. fo_intro. fo_all. fo_intro.
    fo_exe_f (.E 470, #469 .+ .S #470 .= #422) 707.
    fo_assert Yi (FOYREL #469 #471).
    { apply FOPrH_or_intro_l. apply FOPrH_and_intro; [fo_exi (#707); fo_hyp | fo_hyp]. }
    fo_assert CG (FOCONG #700 #704 (.S #422)). { fo_hyp. }
    fo_inst CG (#469).
    pose proof (FOPrH_mp n _ _ _ CG0
                  ltac:(fo_exi (.S #707); fo_lin [(.S .0, #422, #469 .+ .S #707)])) as CG1.
    fo_inst CG1 (#471).
    pose proof (FOPrH_mp n _ _ _ CG2 Yi) as CG3. clear CG CG0 CG1 CG2 Yi.
    fo_exe_from CG3 708. clear CG3.
    fo_assert DV (FODIVALL #700 #705 (.S #422)). { fo_hyp. }
    fo_inst DV (#469).
    pose proof (FOPrH_mp n _ _ _ DV0
                  ltac:(fo_exi (.S #707); fo_lin [(.S .0, #422, #469 .+ .S #707)])) as DV1.
    clear DV DV0.
    fo_exe_from DV1 709. clear DV1.
    fo_exe_f (FObetaF 480 #420 #421 #469 #471) 710.
    fo_split (.E 481, #710 .+ .S #481 .= .S #420)
             (FOAnd (#420 .= #710 .* .S (#421 .* .S #469) .+ #471)
                    (.E 482, FOAnd (.E 483, #482 .+ .S #483 .= .S (#421 .* .S #469))
                                   (#471 .+ .S #482 .= .S (#421 .* .S #469)))).
    fo_split (#420 .= #710 .* .S (#421 .* .S #469) .+ #471)
             (.E 482, FOAnd (.E 483, #482 .+ .S #483 .= .S (#421 .* .S #469))
                            (#471 .+ .S #482 .= .S (#421 .* .S #469))).
    fo_exi constr:(FOQ1).
    apply FOPrH_and_intro; [|apply FOPrH_and_intro].
    + fo_exi (FOQ1 .* (#700 .* .S #469) .+ #471).
      fo_lin [(.S .0, #704, #471 .+ FONM #700 #469 .* #708);
              (#426, #705, FONM #700 #469 .* #709)].
    + fo_lin [(.S .0, #471 .+ FONM #700 #469 .* #708, #704);
              (#426, FONM #700 #469 .* #709, #705)].
    + fo_exi constr:(FOE1). apply FOPrH_and_intro.
      * fo_exi (#471).
        fo_lin [(.S .0, #420, #710 .* .S (#421 .* .S #469) .+ #471);
                (.S FOMM', #702, .S #703); (.S .0, #700, .S FOMM' .* #702)].
      * fo_lin [(.S .0, #420, #710 .* .S (#421 .* .S #469) .+ #471);
                (.S FOMM', #702, .S #703); (.S .0, #700, .S FOMM' .* #702)].
  - fo_assert CG (FOCONG #700 #704 (.S #422)). { fo_hyp. }
    fo_inst CG (#422).
    pose proof (FOPrH_mp n _ _ _ CG0
                  ltac:(fo_exi (.0); apply FOPrH_ring; fo_ring)) as CG1.
    fo_inst CG1 (#423).
    pose proof (FOPrH_mp n _ _ _ CG2
                  ltac:(apply FOPrH_or_intro_r; apply FOPrH_and_intro;
                        apply FOPrH_refl)) as CG3.
    clear CG CG0 CG1 CG2.
    fo_exe_from CG3 707. clear CG3.
    fo_assert DV (FODIVALL #700 #705 (.S #422)). { fo_hyp. }
    fo_inst DV (#422).
    pose proof (FOPrH_mp n _ _ _ DV0
                  ltac:(fo_exi (.0); apply FOPrH_ring; fo_ring)) as DV1.
    clear DV DV0.
    fo_exe_from DV1 708. clear DV1.
    fo_exi constr:(FOQ2).
    apply FOPrH_and_intro; [|apply FOPrH_and_intro].
    + fo_exi (FOQ2 .* (#700 .* .S #422) .+ #423).
      fo_lin [(.S .0, #704, #423 .+ FONM #700 #422 .* #707);
              (#426, #705, FONM #700 #422 .* #708)].
    + fo_lin [(.S .0, #423 .+ FONM #700 #422 .* #707, #704);
              (#426, FONM #700 #422 .* #708, #705)].
    + fo_exi constr:(FOE2). apply FOPrH_and_intro.
      * fo_exi (#423).
        fo_lin [(.S FOMM', #702, .S #703); (.S .0, #700, .S FOMM' .* #702)].
      * fo_lin [(.S FOMM', #702, .S #703); (.S .0, #700, .S FOMM' .* #702)].
Qed.

Ltac fo_last H :=
  lazymatch goal with
  | |- FOPrH ?k ?G _ =>
      let A := eval vm_compute in (List.last G FOFalseF) in
      assert (H : FOPrH k G A) by fo_hyp_b
  end.

(** ** The beta function is functional, and its binders can be moved. *)

Lemma FOPr_beta_fun : forall n,
  FOProvesTn n (.A 420, .A 421, .A 422, .A 423, .A 424,
    FObetaF 480 #420 #421 #422 #423 .-> FObetaF 480 #420 #421 #422 #424 .->
    #423 .= #424).
Proof.
  intro n.
  change (FOPrH n [] (.A 420, .A 421, .A 422, .A 423, .A 424,
    FObetaF 480 #420 #421 #422 #423 .-> FObetaF 480 #420 #421 #422 #424 .->
    #423 .= #424)).
  fo_norm_goal. do 5 fo_all. do 2 fo_intro.
  fo_exe_f (FObetaF 480 #420 #421 #422 #423) 500.
  fo_split (.E 481, #500 .+ .S #481 .= .S #420)
           (FOAnd (#420 .= #500 .* .S (#421 .* .S #422) .+ #423)
                  (.E 482, FOAnd (.E 483, #482 .+ .S #483 .= .S (#421 .* .S #422))
                                 (#423 .+ .S #482 .= .S (#421 .* .S #422)))).
  fo_split (#420 .= #500 .* .S (#421 .* .S #422) .+ #423)
           (.E 482, FOAnd (.E 483, #482 .+ .S #483 .= .S (#421 .* .S #422))
                          (#423 .+ .S #482 .= .S (#421 .* .S #422))).
  fo_exe 482 501.
  fo_split (.E 483, #501 .+ .S #483 .= .S (#421 .* .S #422))
           (#423 .+ .S #501 .= .S (#421 .* .S #422)).
  fo_exe_f (FObetaF 480 #420 #421 #422 #424) 502.
  fo_split (.E 481, #502 .+ .S #481 .= .S #420)
           (FOAnd (#420 .= #502 .* .S (#421 .* .S #422) .+ #424)
                  (.E 482, FOAnd (.E 483, #482 .+ .S #483 .= .S (#421 .* .S #422))
                                 (#424 .+ .S #482 .= .S (#421 .* .S #422)))).
  fo_split (#420 .= #502 .* .S (#421 .* .S #422) .+ #424)
           (.E 482, FOAnd (.E 483, #482 .+ .S #483 .= .S (#421 .* .S #422))
                          (#424 .+ .S #482 .= .S (#421 .* .S #422))).
  fo_exe 482 503.
  fo_split (.E 483, #503 .+ .S #483 .= .S (#421 .* .S #422))
           (#424 .+ .S #503 .= .S (#421 .* .S #422)).
  fo_ctx_thm R (FOPr_rem_unique n).
  fo_inst R (#420). fo_inst R0 (#421 .* .S #422). fo_inst R1 (#500).
  fo_inst R2 (#423). fo_inst R3 (#502). fo_inst R4 (#424).
  exact (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _
           (FOPrH_mp n _ _ _ R5 ltac:(fo_hyp)) ltac:(fo_exi (#501); fo_hyp))
           ltac:(fo_hyp)) ltac:(fo_exi (#503); fo_hyp)).
Qed.

Lemma FOPr_beta_484_480 : forall n,
  FOProvesTn n (.A 420, .A 421, .A 422, .A 423,
    FObetaF 484 #420 #421 #422 #423 .-> FObetaF 480 #420 #421 #422 #423).
Proof.
  intro n.
  change (FOPrH n [] (.A 420, .A 421, .A 422, .A 423,
    FObetaF 484 #420 #421 #422 #423 .-> FObetaF 480 #420 #421 #422 #423)).
  fo_norm_goal. do 4 fo_all. fo_intro.
  fo_exe 484 500.
  fo_split (.E 485, #500 .+ .S #485 .= .S #420)
           (FOAnd (#420 .= #500 .* .S (#421 .* .S #422) .+ #423)
                  (.E 486, FOAnd (.E 487, #486 .+ .S #487 .= .S (#421 .* .S #422))
                                 (#423 .+ .S #486 .= .S (#421 .* .S #422)))).
  fo_split (#420 .= #500 .* .S (#421 .* .S #422) .+ #423)
           (.E 486, FOAnd (.E 487, #486 .+ .S #487 .= .S (#421 .* .S #422))
                          (#423 .+ .S #486 .= .S (#421 .* .S #422))).
  fo_exe 486 501.
  fo_split (.E 487, #501 .+ .S #487 .= .S (#421 .* .S #422))
           (#423 .+ .S #501 .= .S (#421 .* .S #422)).
  fo_exe 485 502. fo_exe 487 503.
  fo_exi (#500).
  apply FOPrH_and_intro; [fo_exi (#502); fo_hyp | apply FOPrH_and_intro; [fo_hyp |]].
  fo_exi (#501). apply FOPrH_and_intro; [fo_exi (#503); fo_hyp | fo_hyp].
Qed.

Lemma FOPr_beta_488_484 : forall n,
  FOProvesTn n (.A 420, .A 421, .A 422, .A 423,
    FObetaF 488 #420 #421 #422 #423 .-> FObetaF 484 #420 #421 #422 #423).
Proof.
  intro n.
  change (FOPrH n [] (.A 420, .A 421, .A 422, .A 423,
    FObetaF 488 #420 #421 #422 #423 .-> FObetaF 484 #420 #421 #422 #423)).
  fo_norm_goal. do 4 fo_all. fo_intro.
  fo_exe 488 500.
  fo_split (.E 489, #500 .+ .S #489 .= .S #420)
           (FOAnd (#420 .= #500 .* .S (#421 .* .S #422) .+ #423)
                  (.E 490, FOAnd (.E 491, #490 .+ .S #491 .= .S (#421 .* .S #422))
                                 (#423 .+ .S #490 .= .S (#421 .* .S #422)))).
  fo_split (#420 .= #500 .* .S (#421 .* .S #422) .+ #423)
           (.E 490, FOAnd (.E 491, #490 .+ .S #491 .= .S (#421 .* .S #422))
                          (#423 .+ .S #490 .= .S (#421 .* .S #422))).
  fo_exe 490 501.
  fo_split (.E 491, #501 .+ .S #491 .= .S (#421 .* .S #422))
           (#423 .+ .S #501 .= .S (#421 .* .S #422)).
  fo_exe 489 502. fo_exe 491 503.
  fo_exi (#500).
  apply FOPrH_and_intro; [fo_exi (#502); fo_hyp | apply FOPrH_and_intro; [fo_hyp |]].
  fo_exi (#501). apply FOPrH_and_intro; [fo_exi (#503); fo_hyp | fo_hyp].
Qed.

(** ** Concatenating beta-coded sequences.

    For codes [c1, d1] of length [l1], [c2, d2] of length [l2] and a
    bound [b] there is a code [c, d] with [c >= b] that agrees with
    [c1, d1] below [l1] and holds the [i]-th element of [c2, d2] at
    [l1 + i] for every [i < l2]. *)

Notation FOBETACAT :=
  (.A 430, .A 431, .A 432, .A 433, .A 434, .A 435, .A 436,
     .E 466, .E 467,
       FOAnd (.E 468, #436 .+ #468 .= #466)
         (FOAnd (.A 469, (.E 470, #469 .+ .S #470 .= #432) .->
                   .A 471, FObetaF 480 #430 #431 #469 #471 .->
                           FObetaF 484 #466 #467 #469 #471)
                (.A 469, (.E 470, #469 .+ .S #470 .= #435) .->
                   .A 471, FObetaF 480 #433 #434 #469 #471 .->
                           FObetaF 484 #466 #467 (#432 .+ #469) #471))).

Local Notation FOAG1 c d :=
  (.A 469, (.E 470, #469 .+ .S #470 .= #432) .->
     .A 471, FObetaF 480 #430 #431 #469 #471 .-> FObetaF 484 c d #469 #471).
Local Notation FOAG2 c d k :=
  (.A 469, (.E 470, #469 .+ .S #470 .= k) .->
     .A 471, FObetaF 480 #433 #434 #469 #471 .->
             FObetaF 484 c d (#432 .+ #469) #471).
Local Notation FOAGX :=
  (.A 469, (.E 470, #469 .+ .S #470 .= #432 .+ #435) .->
     .A 471, FObetaF 480 #700 #701 #469 #471 .-> FObetaF 484 #703 #704 #469 #471).

Lemma FOPr_beta_concat : forall n, FOProvesTn n FOBETACAT.
Proof.
  intro n. change (FOPrH n [] FOBETACAT). fo_norm_goal.
  do 5 fo_all. fo_ind.
  - fo_all.
    fo_ctx_thm E (FOPr_beta_extend n).
    fo_inst E (#430). fo_inst E0 (#431). fo_inst E1 (#432). fo_inst E2 (.0).
    fo_inst E3 (#436).
    fo_exe_from E4 700. clear E E0 E1 E2 E3 E4. fo_exe 467 701.
    fo_split (.E 468, #436 .+ #468 .= #700)
             (FOAnd (FOAG1 #700 #701) (FObetaF 488 #700 #701 #432 .0)).
    fo_split (FOAG1 #700 #701) (FObetaF 488 #700 #701 #432 .0).
    fo_exi (#700). fo_exi (#701).
    apply FOPrH_and_intro; [fo_hyp | apply FOPrH_and_intro; [fo_hyp |]].
    fo_all. fo_intro. fo_exe 470 702. apply FOPrH_efq.
    apply (FOPrH_Q_succ_nonzero n _ (#469 .+ #702)).
    fo_lin [(.S .0, .0, #469 .+ .S #702)].
  - fo_last IH. fo_all. fo_inst IH (#436).
    fo_exe_from IH0 700. clear IH IH0. fo_exe 467 701.
    fo_split (.E 468, #436 .+ #468 .= #700)
             (FOAnd (FOAG1 #700 #701) (FOAG2 #700 #701 #435)).
    fo_split (FOAG1 #700 #701) (FOAG2 #700 #701 #435).
    (* the next element of the second sequence *)
    fo_ctx_thm BT (FOPr_beta_total n).
    fo_inst BT (#433). fo_inst BT0 (#434). fo_inst BT1 (#435).
    fo_exe_from BT2 702. clear BT BT0 BT1 BT2.
    (* extend the code by it *)
    fo_ctx_thm E (FOPr_beta_extend n).
    fo_inst E (#700). fo_inst E0 (#701). fo_inst E1 (#432 .+ #435). fo_inst E2 (#702).
    fo_inst E3 (#436).
    fo_exe_from E4 703. clear E E0 E1 E2 E3 E4. fo_exe 467 704.
    fo_split (.E 468, #436 .+ #468 .= #703)
             (FOAnd FOAGX (FObetaF 488 #703 #704 (#432 .+ #435) #702)).
    fo_split constr:(FOAGX) (FObetaF 488 #703 #704 (#432 .+ #435) #702).
    fo_exi (#703). fo_exi (#704).
    apply FOPrH_and_intro; [fo_hyp | apply FOPrH_and_intro].
    + (* the first sequence is kept *)
      fo_all. fo_intro. fo_all. fo_intro.
      fo_exe_f (.E 470, #469 .+ .S #470 .= #432) 705.
      fo_assert AG (FOAG1 #700 #701). { fo_hyp. }
      fo_inst AG (#469).
      pose proof (FOPrH_mp n _ _ _ AG0 ltac:(fo_exi (#705); fo_hyp)) as AG1.
      fo_inst AG1 (#471).
      pose proof (FOPrH_mp n _ _ _ AG2 ltac:(fo_hyp)) as AG3.
      fo_ctx_thm RB (FOPr_beta_484_480 n).
      fo_inst RB (#700). fo_inst RB0 (#701). fo_inst RB1 (#469). fo_inst RB2 (#471).
      pose proof (FOPrH_mp n _ _ _ RB3 AG3) as B1.
      fo_assert AX constr:(FOAGX). { fo_hyp. }
      fo_inst AX (#469).
      pose proof (FOPrH_mp n _ _ _ AX0
                    ltac:(fo_exi (#705 .+ #435);
                          fo_lin [(.S .0, #432, #469 .+ .S #705)])) as AX1.
      fo_inst AX1 (#471).
      exact (FOPrH_mp n _ _ _ AX2 B1).
    + (* the second sequence, one element longer *)
      fo_all. fo_intro. fo_all. fo_intro.
      fo_exe_f (.E 470, #469 .+ .S #470 .= .S #435) 705.
      fo_cases (#705) 706.
      * fo_assert Ei (#469 .= #435).
        { fo_lin [(.S .0, .S #435, #469 .+ .S #705); (.S .0, #705, .0)]. }
        fo_assert Bk (FObetaF 480 #433 #434 #435 #471).
        { apply (FOPrH_leibniz n _ 699 (#469) (#435) (FObetaF 480 #433 #434 #699 #471));
            [vm_compute; reflexivity | vm_compute; reflexivity | exact Ei |].
          fo_hyp. }
        fo_ctx_thm BF (FOPr_beta_fun n).
        fo_inst BF (#433). fo_inst BF0 (#434). fo_inst BF1 (#435). fo_inst BF2 (#471).
        fo_inst BF3 (#702).
        pose proof (FOPrH_mp n _ _ _ (FOPrH_mp n _ _ _ BF4 Bk) ltac:(fo_hyp)) as Ey.
        fo_ctx_thm RB (FOPr_beta_488_484 n).
        fo_inst RB (#703). fo_inst RB0 (#704). fo_inst RB1 (#432 .+ #435). fo_inst RB2 (#702).
        pose proof (FOPrH_mp n _ _ _ RB3 ltac:(fo_hyp)) as L1.
        fo_assert L2 (FObetaF 484 #703 #704 (#432 .+ #469) #702).
        { apply (FOPrH_leibniz n _ 699 (#435) (#469)
                   (FObetaF 484 #703 #704 (#432 .+ #699) #702));
            [vm_compute; reflexivity | vm_compute; reflexivity
            | apply FOPrH_eq_sym; exact Ei | exact L1]. }
        apply (FOPrH_leibniz n _ 699 (#702) (#471)
                 (FObetaF 484 #703 #704 (#432 .+ #469) #699));
          [vm_compute; reflexivity | vm_compute; reflexivity
          | apply FOPrH_eq_sym; exact Ey | exact L2].
      * fo_assert AG (FOAG2 #700 #701 #435). { fo_hyp. }
        fo_inst AG (#469).
        pose proof (FOPrH_mp n _ _ _ AG0
                      ltac:(fo_exi (#706);
                            fo_lin [(.S .0, .S #435, #469 .+ .S #705);
                                    (.S .0, #705, .S #706)])) as AG1.
        fo_inst AG1 (#471).
        pose proof (FOPrH_mp n _ _ _ AG2 ltac:(fo_hyp)) as AG3.
        fo_ctx_thm RB (FOPr_beta_484_480 n).
        fo_inst RB (#700). fo_inst RB0 (#701). fo_inst RB1 (#432 .+ #469).
        fo_inst RB2 (#471).
        pose proof (FOPrH_mp n _ _ _ RB3 AG3) as B1.
        fo_assert AX constr:(FOAGX). { fo_hyp. }
        fo_inst AX (#432 .+ #469).
        pose proof (FOPrH_mp n _ _ _ AX0
                      ltac:(fo_exi (#706);
                            fo_lin [(.S .0, .S #435, #469 .+ .S #705);
                                    (.S .0, #705, .S #706)])) as AX1.
        fo_inst AX1 (#471).
        exact (FOPrH_mp n _ _ _ AX2 B1).
Qed.

(** ** Cantor pairing inside the tower.

    [FOcpairF a b c] states [c + c = (a + b) * S (a + b) + (b + b)].
    Every pair has a code, every number decodes, both components are
    bounded by the code, and decoding is unique. *)

Lemma FOPr_double_inj : forall n,
  FOProvesTn n (.A 440, .A 441, (#440 .+ #440 .= #441 .+ #441) .-> #440 .= #441).
Proof.
  intro n.
  change (FOPrH n [] (.A 440, .A 441, (#440 .+ #440 .= #441 .+ #441) .-> #440 .= #441)).
  fo_norm_goal. fo_all_as 600. fo_all_as 601. fo_intro.
  fo_ctx_thm T (FOPr_total n). fo_inst T (#600). fo_inst T0 (#601).
  apply (FOPrH_or_elim n _ _ _ _ T1).
  - fo_exe_f (.E 450, #600 .+ #450 .= #601) 700.
    fo_cases (#700) 701.
    + fo_lin [(.S .0, #601, #600 .+ #700); (.S .0, #700, .0)].
    + apply FOPrH_efq.
      apply (FOPrH_add_succ_absurd n _ (#600 .+ #600) (#701 .+ #701 .+ .S .0)).
      fo_lin [(.S .0, #600 .+ #600, #601 .+ #601); (.S (.S .0), #601, #600 .+ #700);
              (.S (.S .0), #700, .S #701)].
  - fo_exe_f (.E 450, #601 .+ .S #450 .= #600) 700.
    apply FOPrH_efq.
    apply (FOPrH_add_succ_absurd n _ (#601 .+ #601) (#700 .+ #700 .+ .S .0)).
    fo_lin [(.S .0, #601 .+ #601, #600 .+ #600); (.S (.S .0), #600, #601 .+ .S #700)].
Qed.

Lemma FOPr_half_tri : forall n,
  FOProvesTn n (.A 440, .E 450, #450 .+ #450 .= #440 .* .S #440).
Proof.
  intro n.
  change (FOPrH n [] (.A 440, .E 450, #450 .+ #450 .= #440 .* .S #440)).
  fo_norm_goal. fo_ind.
  - fo_exi (.0). apply FOPrH_ring. fo_ring.
  - fo_exe 450 700. fo_exi (#700 .+ .S #440).
    fo_lin [(.S .0, #440 .* .S #440, #700 .+ #700)].
Qed.

Lemma FOPr_cpair_total : forall n,
  FOProvesTn n (.A 440, .A 441, .E 450, FOcpairF #440 #441 #450).
Proof.
  intro n.
  change (FOPrH n [] (.A 440, .A 441, .E 450, FOcpairF #440 #441 #450)).
  fo_norm_goal. fo_all_as 600. fo_all_as 601.
  fo_ctx_thm H (FOPr_half_tri n). fo_inst H (#600 .+ #601). fo_exe_from H0 700.
  fo_exi (#700 .+ #601).
  fo_lin [(.S .0, (#600 .+ #601) .* .S (#600 .+ #601), #700 .+ #700)].
Qed.

Lemma FOPr_cpair_surj : forall n,
  FOProvesTn n (.A 440, .E 450, .E 451, FOcpairF #450 #451 #440).
Proof.
  intro n.
  change (FOPrH n [] (.A 440, .E 450, .E 451, FOcpairF #450 #451 #440)).
  fo_norm_goal. fo_ind.
  - fo_exi (.0). fo_exi (.0). apply FOPrH_ring. fo_ring.
  - fo_exe 450 700. fo_exe 451 701.
    fo_cases (#700) 702.
    + fo_exi (.S #701). fo_exi (.0).
      fo_lin [(.S .0, (#700 .+ #701) .* .S (#700 .+ #701) .+ (#701 .+ #701), #440 .+ #440);
              (#700 .+ #701 .+ #701 .+ .S .0, .0, #700)].
    + fo_exi (#702). fo_exi (.S #701).
      fo_lin [(.S .0, (#700 .+ #701) .* .S (#700 .+ #701) .+ (#701 .+ #701), #440 .+ #440);
              (#700 .+ #702 .+ #701 .+ #701 .+ .S (.S .0), .S #702, #700)].
Qed.

Lemma FOPr_cpair_le_r : forall n,
  FOProvesTn n (.A 440, .A 441, .A 442,
    FOcpairF #440 #441 #442 .-> .E 450, #441 .+ #450 .= #442).
Proof.
  intro n.
  change (FOPrH n [] (.A 440, .A 441, .A 442,
    FOcpairF #440 #441 #442 .-> .E 450, #441 .+ #450 .= #442)).
  fo_norm_goal. fo_all_as 600. fo_all_as 601. fo_all_as 602. fo_intro.
  fo_ctx_thm H (FOPr_half_tri n). fo_inst H (#600 .+ #601). fo_exe_from H0 700.
  fo_exi (#700).
  fo_ctx_thm D (FOPr_double_inj n). fo_inst D (#601 .+ #700). fo_inst D0 (#602).
  apply (FOPrH_mp n _ _ _ D1).
  fo_lin [(.S .0, (#600 .+ #601) .* .S (#600 .+ #601), #700 .+ #700);
          (.S .0, #602 .+ #602, (#600 .+ #601) .* .S (#600 .+ #601) .+ (#601 .+ #601))].
Qed.

Lemma FOPr_cpair_le_l : forall n,
  FOProvesTn n (.A 440, .A 441, .A 442,
    FOcpairF #440 #441 #442 .-> .E 450, #440 .+ #450 .= #442).
Proof.
  intro n.
  change (FOPrH n [] (.A 440, .A 441, .A 442,
    FOcpairF #440 #441 #442 .-> .E 450, #440 .+ #450 .= #442)).
  fo_norm_goal. fo_all_as 600. fo_all_as 601. fo_all_as 602. fo_intro.
  fo_cases (#600 .+ #601) 700.
  - fo_assert Z (#600 .= .0). { apply (FOPrH_add_zero_l n _ _ (#601)). fo_hyp. }
    fo_have Z. fo_exi (#602). fo_lin [(.S .0, .0, #600)].
  - fo_ctx_thm H (FOPr_half_tri n). fo_inst H (#700). fo_exe_from H0 701.
    fo_exi (#701 .+ #601 .+ #601).
    fo_ctx_thm D (FOPr_double_inj n). fo_inst D (#600 .+ (#701 .+ #601 .+ #601)).
    fo_inst D0 (#602).
    apply (FOPrH_mp n _ _ _ D1).
    fo_lin [(.S .0, #602 .+ #602, (#600 .+ #601) .* .S (#600 .+ #601) .+ (#601 .+ #601));
            (.S .0, #700 .* .S #700, #701 .+ #701);
            (#600 .+ #601 .+ #700, #600 .+ #601, .S #700)].
Qed.

Local Notation FOH1 := ((#600 .+ #601) .* .S (#600 .+ #601) .+ (#601 .+ #601)).
Local Notation FOH2 := ((#602 .+ #603) .* .S (#602 .+ #603) .+ (#603 .+ #603)).

Lemma FOPr_cpair_inj : forall n,
  FOProvesTn n (.A 440, .A 441, .A 442, .A 443, .A 444,
    FOcpairF #440 #441 #444 .-> FOcpairF #442 #443 #444 .->
    FOAnd (#440 .= #442) (#441 .= #443)).
Proof.
  intro n.
  change (FOPrH n [] (.A 440, .A 441, .A 442, .A 443, .A 444,
    FOcpairF #440 #441 #444 .-> FOcpairF #442 #443 #444 .->
    FOAnd (#440 .= #442) (#441 .= #443))).
  fo_norm_goal.
  fo_all_as 600. fo_all_as 601. fo_all_as 602. fo_all_as 603. fo_all_as 604.
  do 2 fo_intro.
  fo_assert Ss (#600 .+ #601 .= #602 .+ #603).
  { fo_ctx_thm T (FOPr_total n). fo_inst T (#600 .+ #601). fo_inst T0 (#602 .+ #603).
    apply (FOPrH_or_elim n _ _ _ _ T1).
    - fo_exe_f (.E 450, #600 .+ #601 .+ #450 .= #602 .+ #603) 700.
      fo_cases (#700) 701.
      + fo_lin [(.S .0, #602 .+ #603, #600 .+ #601 .+ #700); (.S .0, #700, .0)].
      + apply FOPrH_efq.
        apply (FOPrH_add_succ_absurd n _ (#604 .+ #604)
                 (#600 .+ #600 .+ .S .0 .+ (#603 .+ #603)
                  .+ #701 .* (#600 .+ #600 .+ #601 .+ #601 .+ .S (.S (.S .0)))
                  .+ #701 .* #701)).
        fo_lin [(.S .0, #604 .+ #604, FOH2); (.S .0, FOH1, #604 .+ #604);
                (#600 .+ #601 .+ .S #701 .+ #602 .+ #603 .+ .S .0,
                 #602 .+ #603, #600 .+ #601 .+ #700);
                (#600 .+ #601 .+ .S #701 .+ #602 .+ #603 .+ .S .0, #700, .S #701)].
    - fo_exe_f (.E 450, #602 .+ #603 .+ .S #450 .= #600 .+ #601) 700.
      apply FOPrH_efq.
      apply (FOPrH_add_succ_absurd n _ (#604 .+ #604)
               (#602 .+ #602 .+ .S .0 .+ (#601 .+ #601)
                .+ #700 .* (#602 .+ #602 .+ #603 .+ #603 .+ .S (.S (.S .0)))
                .+ #700 .* #700)).
      fo_lin [(.S .0, #604 .+ #604, FOH1); (.S .0, FOH2, #604 .+ #604);
              (#602 .+ #603 .+ .S #700 .+ #600 .+ #601 .+ .S .0,
               #600 .+ #601, #602 .+ #603 .+ .S #700)]. }
  fo_have Ss.
  fo_ctx_thm D (FOPr_double_inj n). fo_inst D (#601). fo_inst D0 (#603).
  fo_assert Eb (#601 .= #603).
  { apply (FOPrH_mp n _ _ _ D1).
    fo_lin [(.S .0, #604 .+ #604, FOH1); (.S .0, FOH2, #604 .+ #604);
            (#600 .+ #601 .+ #602 .+ #603 .+ .S .0, #600 .+ #601, #602 .+ #603)]. }
  fo_have Eb.
  apply FOPrH_and_intro.
  - fo_lin [(.S .0, #602 .+ #603, #600 .+ #601); (.S .0, #601, #603)].
  - fo_hyp.
Qed.
