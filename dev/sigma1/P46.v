From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19
  P20 P21 P22 P23 P24 P25 P26 P27 P28 P29 P30 P31 P32 P33 P34 P35 P36 P37 P38 P39 P40 P41
  P42 P43 P44 P45.
Open Scope fo_scope.

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
      first
        [ match goal with
          | H : FOtms_avoid ?L' ?lo' ?hi' |- _ =>
              apply (FOtms_avoid_incl L L' lo' hi' lo hi H);
              [ let t := fresh "t" in let Ht := fresh "Ht" in
                intros t Ht; clear -Ht; cbn [In] in *; repeat rewrite in_app_iff in *;
                cbn [In] in *; tauto
              | nat_fast | nat_fast]
          end
        | match goal with
          | H : forall s, In s L -> forall w, ?V <= w -> FOin_tm w s = false |- _ =>
              let t := fresh "t" in let Ht := fresh "Ht" in let w := fresh "w" in
              let H1 := fresh "Hw" in let H2 := fresh "Hw" in
              intros t Ht w H1 H2; apply (H t Ht w); nat_fast
          end ]
  end.

Ltac above_tac ::=
  let t := fresh "t" in let Ht := fresh "Ht" in let w0 := fresh "w0" in
  let Hw0 := fresh "Hw0" in
  intros t Ht w0 Hw0;
  repeat match goal with
    | H : In t (_ ++ _) |- _ => apply in_app_or in H
    | H : In t (_ :: _) |- _ => cbn [In] in H
    | H : In t [] |- _ => destruct H
    | H : In t _ \/ _ |- _ => destruct H as [H|H]
    | H : _ = t \/ _ |- _ => destruct H as [H|H]
    | H : False |- _ => destruct H
    | H : _ = t |- _ => subst t
    end;
  first [ fr_tm
        | match goal with
          | H : forall s, In s ?L -> forall w, ?V <= w -> FOin_tm w s = false,
            H' : In t ?L |- _ => apply (H t H' w0); nat_fast
          end ].

(** ** Sums and products at arbitrary slots. *)

Lemma PRI_op_gen : forall n k V G f rho env z1 z2 z3 j1 j2 j3 x y,
  2000 <= V -> FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  EnvOK n V G env -> FOtms_avoid env 0 1100 -> FOtms_avoid [x; y] 0 1100 ->
  (forall t, In t [x; y] -> forall w, V <= w -> FOin_tm w t = false) ->
  rho z1 = Some j1 -> rho z2 = Some j2 -> rho z3 = Some j3 ->
  FOPrH n G (FONUMR x (nth j1 env FOZero)) -> FOPrH n G (FONUMR y (nth j2 env FOZero)) ->
  FOPrH n G (FONUMR (opT f x y) (nth j3 env FOZero)) ->
  PRI n (FOPrCores k) (FOu0 k) V G
    (cpat_f rho (FOEq (opT f (FOVar z1) (FOVar z2)) (FOVar z3))) env.
Proof.
  intros n k V G f rho env z1 z2 z3 j1 j2 j3 x y HV HG0 HGV HE Henv Hxy Hxyv Hz1 Hz2 Hz3
    H1 H2 H3.
  pose proof HE as [_ [_ [_ Henvv]]].
  destruct f.
  - pose proof (PRI_plus n k V G x y (nth j1 env FOZero) (nth j2 env FOZero)
                  (nth j3 env FOZero) HV HG0 HGV ltac:(avoid_tms) ltac:(above_tac) H1 H2 H3) as T.
    refine (PRI_conv n _ _ V G _ _ _ _ _ _ _ _ T); [| above_tac | avoid_tms | lia].
    intros G' Hinc. unfold fPlus3, rhoN. cbn [cpat_f cpat_tm opT Nat.ltb Nat.leb].
    rewrite Hz1, Hz2, Hz3. cprel_tac.
  - pose proof (PRI_times n k V G x y (nth j1 env FOZero) (nth j2 env FOZero)
                  (nth j3 env FOZero) HV HG0 HGV ltac:(avoid_tms) ltac:(above_tac) H1 H2 H3) as T.
    refine (PRI_conv n _ _ V G _ _ _ _ _ _ _ _ T); [| above_tac | avoid_tms | lia].
    intros G' Hinc. unfold fTimes3, rhoN. cbn [cpat_f cpat_tm opT Nat.ltb Nat.leb].
    rewrite Hz1, Hz2, Hz3. cprel_tac.
Qed.

Lemma FOin_tm_opT_eq : forall f w a b, FOin_tm w (opT f a b) = (FOin_tm w a || FOin_tm w b)%bool.
Proof. intros [|] w a b; reflexivity. Qed.

(** ** Holder facts. *)

Definition HOK (n : nat) (G : list FOFormula) (V : nat) (h : nat -> nat)
    (rho : nat -> option nat) (env : list FOTerm) (x : nat) : Prop :=
  exists i, rho x = Some i /\ i < length env /\
    FOPrH n G (FONUMR (FOVar (h x)) (nth i env FOZero)) /\ 1100 <= h x /\ h x < V.

Lemma HOK_ext : forall n G G' V V' h rho rho' env env' x,
  HOK n G V h rho env x -> (forall X, In X G -> In X G') -> V <= V' ->
  (forall i, rho x = Some i -> rho' x = Some i) -> length env <= length env' ->
  (forall i, i < length env -> nth i env' FOZero = nth i env FOZero) ->
  HOK n G' V' h rho' env' x.
Proof.
  intros n G G' V V' h rho rho' env env' x [i [Hr [Hi [HN [H1 H2]]]]] Hinc HV Hrr Hl Hn.
  exists i. split; [exact (Hrr i Hr)|]. split; [lia|]. split; [|lia].
  rewrite (Hn i Hi). exact (FOPrH_weaken n G G' _ Hinc HN).
Qed.

Lemma hsub_tm_range : forall t h lo hi, (forall x, FOin_tm x t = true -> lo <= h x < hi) ->
  forall w, FOin_tm w (hsub_tm h t) = true -> lo <= w < hi.
Proof.
  intros t h lo hi H w Hw. destruct (FOin_tm_hsub t h w Hw) as [x [Hx <-]]. exact (H x Hx).
Qed.

Lemma hsub_tm_avoid : forall t h lo hi, (forall x, FOin_tm x t = true -> lo <= h x) ->
  hi <= lo -> FOtm_avoid (hsub_tm h t) 0 hi.
Proof.
  intros t h lo hi H Hhi w Hw1 Hw2. destruct (FOin_tm w (hsub_tm h t)) eqn:E.
  - destruct (FOin_tm_hsub t h w E) as [x [Hx <-]]. specialize (H x Hx). lia.
  - reflexivity.
Qed.

Lemma hsub_tm_below : forall t h V, (forall x, FOin_tm x t = true -> h x < V) ->
  forall w, V <= w -> FOin_tm w (hsub_tm h t) = false.
Proof.
  intros t h V H w Hw. destruct (FOin_tm w (hsub_tm h t)) eqn:E; [|reflexivity].
  destruct (FOin_tm_hsub t h w E) as [x [Hx <-]]. specialize (H x Hx). lia.
Qed.

Lemma EnvOK_mono : forall n V V' G G' env, EnvOK n V G env ->
  (forall X, In X G -> In X G') -> FOctx_avoid G' 2 1000 -> V <= V' -> EnvOK n V' G' env.
Proof.
  intros n V V' G G' env [HS [H0 [HV Hab]]] Hinc HG' HVV.
  split; [exact (SlotCtx_mono n env G G' Hinc HG' HS)|]. split; [exact H0|]. split; [lia|].
  intros t Ht w Hw. apply (Hab t Ht). lia.
Qed.

Lemma nth_app_lt : forall (env l : list FOTerm) i, i < length env ->
  nth i (env ++ l) FOZero = nth i env FOZero.
Proof. intros env l i Hi. apply app_nth1. exact Hi. Qed.

Lemma nth_app_len : forall (env l : list FOTerm) i,
  nth (length env + i) (env ++ l) FOZero = nth i l FOZero.
Proof.
  intros env l i. rewrite app_nth2 by lia. f_equal. lia.
Qed.

(** ** Values of terms. *)

Lemma FOPr_succ_cong :  forall a z,
  FOProvesTn 0 (FOImplF (FOEq a (FOVar z)) (FOEq (FOSucc a) (FOSucc (FOVar z)))).
Proof.
  intros a z. change (FOPrH 0 [] (FOImplF (FOEq a (FOVar z)) (FOEq (FOSucc a) (FOSucc (FOVar z))))).
  apply FOPrH_intro. apply FOPrH_congS. apply FOPrH_assum. left. reflexivity.
Qed.

Lemma FOPr_op_cong : forall f a b z1 z2 z,
  FOProvesTn 0 (FOImplF (FOEq a (FOVar z1)) (FOImplF (FOEq b (FOVar z2))
    (FOImplF (FOEq (opT f (FOVar z1) (FOVar z2)) (FOVar z)) (FOEq (opT f a b) (FOVar z))))).
Proof.
  intros f a b z1 z2 z.
  change (FOPrH 0 [] (FOImplF (FOEq a (FOVar z1)) (FOImplF (FOEq b (FOVar z2))
    (FOImplF (FOEq (opT f (FOVar z1) (FOVar z2)) (FOVar z)) (FOEq (opT f a b) (FOVar z)))))).
  apply FOPrH_intro. apply FOPrH_intro. apply FOPrH_intro. cbn [app].
  apply (FOPrH_eq_trans _ _ _ (opT f (FOVar z1) (FOVar z2))).
  - destruct f; cbn [opT].
    + apply FOPrH_congPlus; apply FOPrH_assum; [left | right; left]; reflexivity.
    + apply FOPrH_congMult; apply FOPrH_assum; [left | right; left]; reflexivity.
  - apply FOPrH_assum. right. right. left. reflexivity.
Qed.

Lemma FOPr_var_refl : forall x, FOProvesTn 0 (FOEq (FOVar x) (FOVar x)).
Proof. intros x. change (FOPrH 0 [] (FOEq (FOVar x) (FOVar x))). apply FOPrH_refl. Qed.

Lemma FOPr_zero_refl : FOProvesTn 0 (FOEq FOZero FOZero).
Proof. change (FOPrH 0 [] (FOEq FOZero FOZero)). apply FOPrH_refl. Qed.

Ltac fv_cases H :=
  repeat match type of H with
  | FOfree_in _ (FOImplF _ _) = true => cbn [FOfree_in] in H
  | FOfree_in _ (FOEq _ _) = true => cbn [FOfree_in] in H
  | FOfree_in _ FOFalseF = true => discriminate H
  | (_ || _)%bool = true => apply Bool.orb_true_iff in H; destruct H as [H|H]
  | FOin_tm _ (FOSucc _) = true => cbn [FOin_tm] in H
  | FOin_tm _ (FOPlus _ _) = true => cbn [FOin_tm] in H
  | FOin_tm _ (FOMult _ _) = true => cbn [FOin_tm] in H
  | FOin_tm _ (opT _ _ _) = true => rewrite FOin_tm_opT_eq in H
  | FOin_tm _ FOZero = true => discriminate H
  | FOin_tm ?x (FOVar _) = true => cbn [FOin_tm] in H; apply Nat.eqb_eq in H; subst x
  | Nat.eqb _ ?x = true => apply Nat.eqb_eq in H; subst x
  end.

(** [TEV n k t]: a numeral code of the value of [t], at the holders,
    makes the equation of [t] with that code provable. *)

Definition TEV (n k : nat) (t : FOTerm) : Prop :=
  forall V G h rho env z j,
  2000 <= V -> FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  EnvOK n V G env -> FOtms_avoid env 0 1100 ->
  (forall z' i, rho z' = Some i -> i < length env) ->
  (forall x, FOin_tm x t = true -> HOK n G V h rho env x) ->
  FOin_tm z t = false -> rho z = Some j -> j < length env ->
  FOPrH n G (FONUMR (hsub_tm h t) (nth j env FOZero)) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho (FOEq t (FOVar z))) env.

Lemma TEV_var : forall n k x, TEV n k (FOVar x).
Proof.
  intros n k x V G h rho env z j HV HG0 HGV HE Henv Hr Hh Hz Hzj Hj HN.
  pose proof HE as [_ [_ [_ Henvv]]].
  destruct (Hh x ltac:(cbn [FOin_tm]; apply Nat.eqb_refl)) as [i [Hxi [Hi [HNx [H1 H2]]]]].
  cbn [hsub_tm] in HN.
  pose proof (FOPrH_numr_unique n G (FOVar (h x)) (nth i env FOZero) (nth j env FOZero) HNx HN
                ltac:(avoid_tms) ltac:(avoid_tms)) as E.
  assert (Hfv : forall x', FOfree_in x' (FOEq (FOVar x) (FOVar x)) = true ->
            exists j', rho x' = Some j' /\ j' < length env).
  { intros x' Hx'. cbn [FOfree_in FOin_tm] in Hx'. rewrite Bool.orb_diag in Hx'.
    apply Nat.eqb_eq in Hx'. subst x'. exists i. split; assumption. }
  pose proof (PRI_thm_open n k V G _ rho env (FOPr_var_refl x) HE Hfv) as T.
  refine (PRI_conv n _ _ V G _ _ _ _ _ _ _ _ T); [| above_tac | avoid_tms | lia].
  intros G' Hinc. pose proof (FOPrH_weaken n G G' _ Hinc E) as E'.
  cbn [cpat_f cpat_tm]. rewrite Hxi, Hzj. cprel_tac.
Qed.

Lemma TEV_zero : forall n k, TEV n k FOZero.
Proof.
  intros n k V G h rho env z j HV HG0 HGV HE Henv Hr Hh Hz Hzj Hj HN.
  pose proof HE as [_ [_ [_ Henvv]]].
  cbn [hsub_tm] in HN.
  pose proof (FOPrH_numr_inv0 n G (nth j env FOZero) ltac:(intros w ? ?; apply HG0; lia)
                ltac:(avoid_tms) HN) as C.
  pose proof (PRI_thm_open n k V G _ rho env FOPr_zero_refl HE
                ltac:(intros x' Hx'; discriminate Hx')) as T.
  refine (PRI_conv n _ _ V G _ _ _ _ _ _ _ _ T); [| above_tac | avoid_tms | lia].
  intros G' Hinc. pose proof (FOPrH_weaken n G G' _ Hinc C) as C'.
  cbn [cpat_f cpat_tm]. rewrite Hzj. cprel_tac.
Qed.

Lemma nth_snoc_len : forall (env : list FOTerm) x, nth (length env) (env ++ [x]) FOZero = x.
Proof. intros env x. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma TEV_succ : forall n k a, TEV n k a -> TEV n k (FOSucc a).
Proof.
  intros n k a IH V G h rho env z j HV HG0 HGV HE Henv Hr Hh Hz Hzj Hj HN.
  pose proof HE as [_ [_ [_ Henvv]]].
  cbn [hsub_tm] in HN. cbn [FOin_tm] in Hz.
  assert (Hha : forall x, FOin_tm x a = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; cbn [FOin_tm]; exact Hx).
  assert (Hhr : forall x, FOin_tm x a = true -> 1100 <= h x < V)
    by (intros x Hx; destruct (Hha x Hx) as [i [_ [_ [_ [H1 H2]]]]]; lia).
  assert (Hav_a : FOtms_avoid [hsub_tm h a] 0 1100).
  { intros s [<-|[]]. apply (hsub_tm_avoid a h 1100 1100); [|lia].
    intros x Hx. apply Hhr. exact Hx. }
  assert (Hab_a : forall s, In s [hsub_tm h a] -> forall w, V <= w -> FOin_tm w s = false).
  { intros s [<-|[]] w Hw. apply (hsub_tm_below a h V); [|exact Hw].
    intros x Hx. apply Hhr. exact Hx. }
  refine (PRI_numr_invS n _ _ V 0 G _ env (hsub_tm h a) (nth j env FOZero) HN _ _ _ _ _ _);
    [lia | avoid_tms | above_tac | avoid_tms | above_tac |].
  intros w Hw _.
  remember (S (Nat.max (FOmax_var_tm a) z)) as z' eqn:Ez'.
  assert (Hz'a : FOin_tm z' a = false) by (apply FOin_tm_above; lia).
  assert (Hr2 : rho_sub (Some z') (length env) rho z' = Some (length env))
    by (unfold rho_sub; rewrite Nat.eqb_refl; reflexivity).
  assert (Hrho2 : forall x, x <> z' -> rho_sub (Some z') (length env) rho x = rho x)
    by (intros x Hx; unfold rho_sub; rewrite (proj2 (Nat.eqb_neq x z') Hx); reflexivity).
  assert (Hxz' : forall x, FOin_tm x a = true -> x <> z').
  { intros x Hx E. subst x. congruence. }
  lazymatch goal with |- PRI _ _ _ _ ?G2 _ _ =>
    assert (HG2 : FOctx_avoid G2 0 1000) by (intros w' ? ?; free_ctx);
    assert (HG2V : forall w', S w <= w' -> FOfree_ctx w' G2) by (intros w' ?; free_ctx);
    assert (Hinc2 : forall X, In X G -> In X G2) by (intros X HX; apply in_or_app; left; exact HX);
    assert (Cw : FOPrH n G2 (FOcpairF (FOnumeral 2) (FOVar w) (nth j env FOZero))) by wk_in;
    assert (Nw : FOPrH n G2 (FONUMR (hsub_tm h a) (FOVar w))) by wk_in;
    assert (HE2 : EnvOK n (S w) G2 (env ++ [FOVar w]))
      by (apply (EnvOK_snoc n (S w) G2 env (FOVar w) (hsub_tm h a));
          [ apply (EnvOK_mono n V (S w) G);
            [exact HE | exact Hinc2 | intros w' ? ?; apply HG2; lia | lia]
          | exact Nw | avoid_tms | intros w' Hw'; apply FOin_tm_var_ne; lia ])
  end.
  assert (Hr2' : forall z0 i, rho_sub (Some z') (length env) rho z0 = Some i ->
            i < length (env ++ [FOVar w])).
  { intros z0 i Hz0. rewrite length_app. cbn [length]. unfold rho_sub in Hz0.
    destruct (Nat.eqb z0 z'); [injection Hz0 as <-; lia | specialize (Hr z0 i Hz0); lia]. }
  pose proof (IH (S w) _ h (rho_sub (Some z') (length env) rho) (env ++ [FOVar w]) z'
                (length env) ltac:(lia) HG2 HG2V HE2 ltac:(avoid_tms) Hr2'
                ltac:(intros x Hx;
                      refine (HOK_ext n G _ V (S w) h rho _ env (env ++ [FOVar w]) x (Hha x Hx)
                                Hinc2 _ _ _ _);
                      [ lia | intros i Hi; rewrite (Hrho2 x (Hxz' x Hx)); exact Hi
                      | rewrite length_app; lia | intros i Hi; apply nth_app_lt; exact Hi ])
                Hz'a Hr2 ltac:(rewrite length_app; cbn [length]; lia)
                ltac:(rewrite nth_snoc_len; exact Nw)) as IHa.
  pose proof (PRI_thm_open n k (S w) _ _ (rho_sub (Some z') (length env) rho) _
                (FOPr_succ_cong a z') HE2) as T.
  specialize (T ltac:(intros x Hx; fv_cases Hx;
                      first [ destruct (Hha x Hx) as [i [Hxi [Hi _]]]; exists i;
                              rewrite (Hrho2 x (Hxz' x Hx));
                              split; [exact Hxi | rewrite length_app; lia]
                            | exists (length env);
                              split; [exact Hr2 | rewrite length_app; cbn [length]; lia] ])).
  pose proof (PRI_mp n _ _ (S w) _ _ _ _ _ HE2 Hr2' T IHa) as T2.
  refine (PRI_conv n _ _ (S w) _ _ _ _ _ _ _ _ _ T2); [| above_tac | avoid_tms | lia].
  intros G' Hinc. pose proof (FOPrH_weaken n _ G' _ Hinc Cw) as Cw'.
  cbn [cpat_f cpat_tm]. rewrite Hr2, Hzj.
  apply cpr_pair; [apply cpr_lit|]. apply cpr_pair.
  - apply cpr_pair; [apply cpr_lit|]. apply CPrel_cpat_tm. intros x Hx. unfold SlotAgree.
    rewrite (Hrho2 x (Hxz' x Hx)). destruct (Hha x Hx) as [i [Hxi [Hi _]]]. rewrite Hxi.
    rewrite nth_app_lt by exact Hi. apply FOPrH_refl.
  - apply cpr_succ_r. rewrite nth_snoc_len. exact Cw'.
Qed.

Lemma hsub_tm_opT : forall f h a b, hsub_tm h (opT f a b) = opT f (hsub_tm h a) (hsub_tm h b).
Proof. intros [|] h a b; reflexivity. Qed.

Lemma TEV_op : forall n k f a b, TEV n k a -> TEV n k b -> TEV n k (opT f a b).
Proof.
  intros n k f a b IHa IHb V G h rho env z j HV HG0 HGV HE Henv Hr Hh Hz Hzj Hj HN.
  pose proof HE as [_ [_ [_ Henvv]]].
  rewrite hsub_tm_opT in HN. rewrite FOin_tm_opT_eq in Hz.
  apply Bool.orb_false_iff in Hz as [Hza Hzb].
  assert (Hha : forall x, FOin_tm x a = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; rewrite FOin_tm_opT_eq, Hx; reflexivity).
  assert (Hhb : forall x, FOin_tm x b = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; rewrite FOin_tm_opT_eq, Hx; apply Bool.orb_true_r).
  assert (Hhra : forall x, FOin_tm x a = true -> 1100 <= h x < V)
    by (intros x Hx; destruct (Hha x Hx) as [i [_ [_ [_ [H1 H2]]]]]; lia).
  assert (Hhrb : forall x, FOin_tm x b = true -> 1100 <= h x < V)
    by (intros x Hx; destruct (Hhb x Hx) as [i [_ [_ [_ [H1 H2]]]]]; lia).
  assert (Hav_ab : FOtms_avoid [hsub_tm h a; hsub_tm h b] 0 1100).
  { intros s [<-|[<-|[]]];
      [apply (hsub_tm_avoid a h 1100 1100) | apply (hsub_tm_avoid b h 1100 1100)];
      try lia; intros x Hx; [apply Hhra | apply Hhrb]; exact Hx. }
  assert (Hab_ab : forall s, In s [hsub_tm h a; hsub_tm h b] ->
            forall w, V <= w -> FOin_tm w s = false).
  { intros s [<-|[<-|[]]] w Hw; [apply (hsub_tm_below a h V) | apply (hsub_tm_below b h V)];
      try exact Hw; intros x Hx; [apply Hhra | apply Hhrb]; exact Hx. }
  refine (PRI_numr_ex n _ _ V 0 G _ env (hsub_tm h a) _ _ _ _ _ _);
    [lia | avoid_tms | intros w' ?; fr_tm | avoid_tms | above_tac |].
  intros w1 Hw1 _.
  refine (PRI_numr_ex n _ _ (S w1) 0 _ _ env (hsub_tm h b) _ _ _ _ _ _);
    [lia | avoid_tms | intros w' ?; fr_tm | avoid_tms | above_tac |].
  intros w2 Hw2 _.
  remember (S (Nat.max (Nat.max (FOmax_var_tm a) (FOmax_var_tm b)) z)) as z1 eqn:Ez1.
  assert (Hz1a : FOin_tm z1 a = false) by (apply FOin_tm_above; lia).
  assert (Hz1b : FOin_tm z1 b = false) by (apply FOin_tm_above; lia).
  assert (Hz2a : FOin_tm (S z1) a = false) by (apply FOin_tm_above; lia).
  assert (Hz2b : FOin_tm (S z1) b = false) by (apply FOin_tm_above; lia).
  remember (rho_sub (Some (S z1)) (S (length env)) (rho_sub (Some z1) (length env) rho))
    as rho3 eqn:Erho3.
  assert (H31 : rho3 z1 = Some (length env)).
  { subst rho3. unfold rho_sub. rewrite (proj2 (Nat.eqb_neq z1 (S z1)) ltac:(lia)).
    rewrite Nat.eqb_refl. reflexivity. }
  assert (H32 : rho3 (S z1) = Some (S (length env))).
  { subst rho3. unfold rho_sub. rewrite Nat.eqb_refl. reflexivity. }
  assert (H3x : forall x, x <> z1 -> x <> S z1 -> rho3 x = rho x).
  { intros x Hx1 Hx2. subst rho3. unfold rho_sub.
    rewrite (proj2 (Nat.eqb_neq x (S z1)) Hx2), (proj2 (Nat.eqb_neq x z1) Hx1). reflexivity. }
  assert (Hxa : forall x, FOin_tm x a = true -> x <> z1 /\ x <> S z1).
  { intros x Hx. split; intro E; subst x; congruence. }
  assert (Hxb : forall x, FOin_tm x b = true -> x <> z1 /\ x <> S z1).
  { intros x Hx. split; intro E; subst x; congruence. }
  assert (Hzz : z <> z1 /\ z <> S z1) by lia.
  assert (Hn1 : nth (length env) ((env ++ [FOVar w1]) ++ [FOVar w2]) FOZero = FOVar w1).
  { rewrite nth_app_lt by (rewrite length_app; cbn [length]; lia). apply nth_snoc_len. }
  assert (Hn2 : nth (S (length env)) ((env ++ [FOVar w1]) ++ [FOVar w2]) FOZero = FOVar w2).
  { replace (S (length env)) with (length (env ++ [FOVar w1]))
      by (rewrite length_app; cbn [length]; lia). apply nth_snoc_len. }
  assert (Hn0 : forall i, i < length env ->
            nth i ((env ++ [FOVar w1]) ++ [FOVar w2]) FOZero = nth i env FOZero).
  { intros i Hi. rewrite nth_app_lt by (rewrite length_app; cbn [length]; lia).
    apply nth_app_lt. exact Hi. }
  assert (Hl3 : length ((env ++ [FOVar w1]) ++ [FOVar w2]) = S (S (length env)))
    by (rewrite !length_app; cbn [length]; lia).
  assert (Hr3 : forall z0 i, rho3 z0 = Some i -> i < length ((env ++ [FOVar w1]) ++ [FOVar w2])).
  { intros z0 i Hz0. rewrite Hl3. subst rho3. unfold rho_sub in Hz0.
    destruct (Nat.eqb z0 (S z1)); [injection Hz0 as <-; lia|].
    destruct (Nat.eqb z0 z1); [injection Hz0 as <-; lia|]. specialize (Hr z0 i Hz0). lia. }
  lazymatch goal with |- PRI _ _ _ _ ?G3 _ _ =>
    assert (HG3 : FOctx_avoid G3 0 1000) by (intros w' ? ?; free_ctx);
    assert (HG3V : forall w', S w2 <= w' -> FOfree_ctx w' G3) by (intros w' ?; free_ctx);
    assert (Hinc3 : forall X, In X G -> In X G3)
      by (intros X HX; apply in_or_app; left; apply in_or_app; left; exact HX);
    assert (Na : FOPrH n G3 (FONUMR (hsub_tm h a) (FOVar w1))) by wk_in;
    assert (Nb : FOPrH n G3 (FONUMR (hsub_tm h b) (FOVar w2))) by wk_in;
    assert (HN3 : FOPrH n G3 (FONUMR (opT f (hsub_tm h a) (hsub_tm h b)) (nth j env FOZero)))
      by exact (FOPrH_weaken n G G3 _ Hinc3 HN);
    assert (HE3 : EnvOK n (S w2) G3 ((env ++ [FOVar w1]) ++ [FOVar w2]))
      by (apply (EnvOK_snoc n (S w2) G3 _ (FOVar w2) (hsub_tm h b));
          [ apply (EnvOK_snoc n (S w2) G3 env (FOVar w1) (hsub_tm h a));
            [ apply (EnvOK_mono n V (S w2) G);
              [exact HE | exact Hinc3 | intros w' ? ?; apply HG3; lia | lia]
            | exact Na | avoid_tms | intros w' Hw'; apply FOin_tm_var_ne; lia ]
          | exact Nb | avoid_tms | intros w' Hw'; apply FOin_tm_var_ne; lia ])
  end.
  lazymatch type of HG3 with FOctx_avoid ?G3 _ _ =>
    assert (HOKa : forall x, FOin_tm x a = true ->
              HOK n G3 (S w2) h rho3 ((env ++ [FOVar w1]) ++ [FOVar w2]) x)
      by (intros x Hx; destruct (Hxa x Hx) as [Hx1 Hx2];
          refine (HOK_ext n G _ V (S w2) h rho _ env _ x (Hha x Hx) Hinc3 _ _ _ _);
          [lia | intros i Hi; rewrite (H3x x Hx1 Hx2); exact Hi | rewrite Hl3; lia
          | exact Hn0]);
    assert (HOKb : forall x, FOin_tm x b = true ->
              HOK n G3 (S w2) h rho3 ((env ++ [FOVar w1]) ++ [FOVar w2]) x)
      by (intros x Hx; destruct (Hxb x Hx) as [Hx1 Hx2];
          refine (HOK_ext n G _ V (S w2) h rho _ env _ x (Hhb x Hx) Hinc3 _ _ _ _);
          [lia | intros i Hi; rewrite (H3x x Hx1 Hx2); exact Hi | rewrite Hl3; lia
          | exact Hn0])
  end.
  pose proof (IHa (S w2) _ h rho3 _ z1 (length env) ltac:(lia) HG3 HG3V HE3 ltac:(avoid_tms) Hr3
                HOKa Hz1a H31 ltac:(rewrite Hl3; lia) ltac:(rewrite Hn1; exact Na)) as Ta.
  pose proof (IHb (S w2) _ h rho3 _ (S z1) (S (length env)) ltac:(lia) HG3 HG3V HE3
                ltac:(avoid_tms) Hr3 HOKb Hz2b H32 ltac:(rewrite Hl3; lia)
                ltac:(rewrite Hn2; exact Nb)) as Tb.
  pose proof (PRI_op_gen n k (S w2) _ f rho3 _ z1 (S z1) z (length env) (S (length env)) j
                (hsub_tm h a) (hsub_tm h b) ltac:(lia) HG3 HG3V HE3 ltac:(avoid_tms)
                ltac:(avoid_tms) ltac:(above_tac) H31 H32
                ltac:(rewrite (H3x z (proj1 Hzz) (proj2 Hzz)); exact Hzj)
                ltac:(rewrite Hn1; exact Na) ltac:(rewrite Hn2; exact Nb)
                ltac:(rewrite (Hn0 j Hj); exact HN3)) as Top.
  pose proof (PRI_thm_open n k (S w2) _ _ rho3 _ (FOPr_op_cong f a b z1 (S z1) z) HE3) as T.
  specialize (T ltac:(intros x Hx; fv_cases Hx;
                      first [ destruct (HOKa x Hx) as [i [Hxi [Hi _]]]; exists i; split; assumption
                            | destruct (HOKb x Hx) as [i [Hxi [Hi _]]]; exists i; split; assumption
                            | exists (length env); split; [exact H31 | rewrite Hl3; lia]
                            | exists (S (length env)); split; [exact H32 | rewrite Hl3; lia]
                            | exists j; split;
                              [rewrite (H3x z (proj1 Hzz) (proj2 Hzz)); exact Hzj
                              | rewrite Hl3; lia] ])).
  pose proof (PRI_mp n _ _ (S w2) _ rho3 _ _ _ HE3 Hr3 T Ta) as T1.
  pose proof (PRI_mp n _ _ (S w2) _ rho3 _ _ _ HE3 Hr3 T1 Tb) as T2.
  pose proof (PRI_mp n _ _ (S w2) _ rho3 _ _ _ HE3 Hr3 T2 Top) as T3.
  refine (PRI_reslot n _ _ (S w2) _ _ rho3 rho _ env _ _ _ _ T3); [| above_tac | avoid_tms | lia].
  intros x Hx. unfold SlotAgree. fv_cases Hx.
  - destruct (Hxa x Hx) as [Hx1 Hx2]. rewrite (H3x x Hx1 Hx2).
    destruct (Hha x Hx) as [i [Hxi [Hi _]]]. rewrite Hxi, (Hn0 i Hi). apply FOPrH_refl.
  - destruct (Hxb x Hx) as [Hx1 Hx2]. rewrite (H3x x Hx1 Hx2).
    destruct (Hhb x Hx) as [i [Hxi [Hi _]]]. rewrite Hxi, (Hn0 i Hi). apply FOPrH_refl.
  - rewrite (H3x z (proj1 Hzz) (proj2 Hzz)), Hzj, (Hn0 j Hj). apply FOPrH_refl.
Qed.

Theorem PRI_teval : forall t n k, TEV n k t.
Proof.
  induction t as [x| |a IH|a IHa b IHb|a IHa b IHb]; intros n k.
  - apply TEV_var.
  - apply TEV_zero.
  - apply TEV_succ. apply IH.
  - exact (TEV_op n k true a b (IHa n k) (IHb n k)).
  - exact (TEV_op n k false a b (IHa n k) (IHb n k)).
Qed.
