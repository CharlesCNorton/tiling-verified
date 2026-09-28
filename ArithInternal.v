(******************************************************************************)
(*                                                                            *)
(*           Parametric Provability: Bypassing the Loebian Obstacle           *)
(*                                                                            *)
(*     Part 4 of 6. Object-level arithmetic: instantiation, ring, contexts.   *)
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
