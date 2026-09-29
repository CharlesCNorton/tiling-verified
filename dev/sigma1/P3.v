From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2.
Open Scope fo_scope.

(** ** The dispatch clause at one row.

    [FODISPCASES]: the case split of the dispatch at base [20] with the
    row's fields [(tg, a1, a2, a3, r)] in place of its witnesses. *)

Definition FODISPCASES (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (tg a1 a2 a3 r : FOTerm) : FOFormula :=
  FOOr (FOAnd (FOEq tg FOZero)
          (FOSTEP0 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 r))
  (FOOr (FOAnd (FOEq tg (FOnumeral 1))
          (FOSTEP1 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 r))
  (FOOr (FOAnd (FOEq tg (FOnumeral 2))
          (FOSTEP2 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 a3 r))
  (FOOr (FOAnd (FOEq tg (FOnumeral 3))
          (FOSTEP3 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 a3 r))
  (FOOr (FOAnd (FOEq tg (FOnumeral 4))
          (FOSTEP4 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 a3 r))
        (FOAnd (FOEq tg (FOnumeral 5))
          (FOSTEP5 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 r)))))).

Ltac ok_step :=
  lazymatch goal with
  | |- FOsubst_ok _ ?s _ = true =>
      let V := fresh "V" in assert (V : FOtm_avoid s 20 122) by avoid_tm;
      solve [auto 100 with fook]
  end.

Lemma FOPrH_dispatch_intro : forall n G ct dt c1 d1 c2 d2 c3 d3 cr dr len j tg a1 a2 a3 r,
  FOPrH n G (FObetaF 30 ct dt j tg) -> FOPrH n G (FObetaF 34 c1 d1 j a1) ->
  FOPrH n G (FObetaF 38 c2 d2 j a2) -> FOPrH n G (FObetaF 42 c3 d3 j a3) ->
  FOPrH n G (FObetaF 46 cr dr j r) ->
  FOPrH n G (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r) ->
  FOctx_avoid G 20 122 ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; j; tg; a1; a2; a3; r] 20 122 ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; j; tg; a1; a2; a3; r] 498 499 ->
  FOPrH n G (FOSTEPDISPATCH 20 ct dt c1 d1 c2 d2 c3 d3 cr dr len j).
Proof.
  intros n G ct dt c1 d1 c2 d2 c3 d3 cr dr len j tg a1 a2 a3 r Bt B1 B2 B3 Br HC HG Hav Hav2.
  assert (Le : forall v c d x, FOPrH n G (FObetaF v c d j x) -> v + 4 <= 122 -> 20 <= v ->
            FOtms_avoid [c; d; x] 20 122 -> FOtms_avoid [c; d; x] 498 499 ->
            FOPrH n G (FOle (FOSucc x) (FOSucc c))).
  { intros v c d x Hb Hv1 Hv2 Hc1 Hc2.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_beta_le n G v c d j x
                  ltac:(intros w ? ?; apply HG; lia) ltac:(lia) ltac:(avoid_tms)
                  ltac:(avoid_tms)) Hb) as H.
    unfold FOle in H |- *.
    refine (FOPrH_mp _ _ _ _ _ H). apply FOPrH_empty.
    apply FOPrH_intro.
    refine (FOPrH_ex_elim _ _ 498 (FOEq (FOPlus x (FOVar 498)) c) _ _ _ _ _);
      [free_ctx | free_fm | apply FOPrH_last |].
    apply (FOPrH_ex_intro _ _ 498 (FOVar 498)); [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_id.
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (E : FOPrH n Gc (FOEq c (FOPlus x (FOVar 498)))) by (apply FOPrH_eq_sym; wk_in)
    end.
    fo_lin [(.S .0, c, x .+ #498)]; exact E. }
  unfold FOSTEPDISPATCH.
  apply (FOPrH_bex_intro_t _ _ 20 (FOSucc ct) tg); [lia | lia | avoid_tm | avoid_tm
    | avoid_tm | avoid_tm | apply (Le 30 ct dt tg Bt); [lia | lia | avoid_tms | avoid_tms]
    | ok_step | ].
  autorewrite with fosubst. subst_avoid_h Hav.
  apply (FOPrH_bex_intro_t _ _ 22 (FOSucc c1) a1); [lia | lia | avoid_tm | avoid_tm
    | avoid_tm | avoid_tm | apply (Le 34 c1 d1 a1 B1); [lia | lia | avoid_tms | avoid_tms]
    | ok_step | ].
  autorewrite with fosubst. subst_avoid_h Hav.
  apply (FOPrH_bex_intro_t _ _ 24 (FOSucc c2) a2); [lia | lia | avoid_tm | avoid_tm
    | avoid_tm | avoid_tm | apply (Le 38 c2 d2 a2 B2); [lia | lia | avoid_tms | avoid_tms]
    | ok_step | ].
  autorewrite with fosubst. subst_avoid_h Hav.
  apply (FOPrH_bex_intro_t _ _ 26 (FOSucc c3) a3); [lia | lia | avoid_tm | avoid_tm
    | avoid_tm | avoid_tm | apply (Le 42 c3 d3 a3 B3); [lia | lia | avoid_tms | avoid_tms]
    | ok_step | ].
  autorewrite with fosubst. subst_avoid_h Hav.
  apply (FOPrH_bex_intro_t _ _ 28 (FOSucc cr) r); [lia | lia | avoid_tm | avoid_tm
    | avoid_tm | avoid_tm | apply (Le 46 cr dr r Br); [lia | lia | avoid_tms | avoid_tms]
    | ok_step | ].
  autorewrite with fosubst. subst_avoid_h Hav.
  repeat (apply FOPrH_and_intro; [assumption|]).
  exact HC.
Qed.

(** ** Adding a row to a table.

    [FOPrH_text_elim] names the columns of an extension of [T] by fresh
    variables [k] .. [k+9]; [FOPrH_row_add] turns the dispatch clause of
    the new row into validity of the extension, its inclusion of [T],
    and the lookup of the new row. *)

Definition FOtabx (k : nat) (len : FOTerm) : FOtab :=
  mkTab (FOVar k) (FOVar (k + 1)) (FOVar (k + 2)) (FOVar (k + 3)) (FOVar (k + 4))
    (FOVar (k + 5)) (FOVar (k + 6)) (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9)) len.

Lemma FOPrH_text_elim : forall n G T tg a1 a2 a3 r k C,
  FOctx_avoid G 420 500 -> FOctx_avoid G k (k + 10) ->
  2 <= k -> k + 10 <= 420 ->
  (forall w, k <= w -> w < k + 10 -> FOfree_in w C = false) ->
  FOtms_avoid (FOtab_terms T ++ [tg; a1; a2; a3; r]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ [tg; a1; a2; a3; r]) k (k + 10) ->
  FOPrH n (G ++ [FOTEXT T (FOtabx k (FOSucc (tlen T))) tg a1 a2 a3 r]) C ->
  FOPrH n G C.
Proof.
  intros n G T tg a1 a2 a3 r k C HG HGk Hk Hk' HC Hav Havk H0.
  apply (FOPrH_extend_elim n G (tct T) (tdt T) (tlen T) tg (tct T) k (k + 1) C);
    try (apply HGk; lia); try (apply HC; lia); try lia; try avoid_tms; try assumption.
  apply (FOPrH_extend_elim n _ (tc1 T) (td1 T) (tlen T) a1 (tc1 T) (k + 2) (k + 3) C);
    try (apply HC; lia); try lia; try avoid_tms; try ctx_list; try free_ctx.
  apply (FOPrH_extend_elim n _ (tc2 T) (td2 T) (tlen T) a2 (tc2 T) (k + 4) (k + 5) C);
    try (apply HC; lia); try lia; try avoid_tms; try ctx_list; try free_ctx.
  apply (FOPrH_extend_elim n _ (tc3 T) (td3 T) (tlen T) a3 (tc3 T) (k + 6) (k + 7) C);
    try (apply HC; lia); try lia; try avoid_tms; try ctx_list; try free_ctx.
  apply (FOPrH_extend_elim n _ (tcr T) (tdr T) (tlen T) r (tcr T) (k + 8) (k + 9) C);
    try (apply HC; lia); try lia; try avoid_tms; try ctx_list; try free_ctx.
  refine (FOPrH_cut _ _ (FOTEXT T (FOtabx k (FOSucc (tlen T))) tg a1 a2 a3 r) _ _ _).
  - unfold FOTEXT, FOtabx. cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen].
    do 4 (apply FOPrH_and_intro; [wk_in|]). wk_in.
  - refine (FOPrH_weaken n _ _ _ _ H0).
    intros X HX. apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
    + do 6 (apply in_or_app; left). exact HX.
    + apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPrH_row_add : forall n G T T' tg a1 a2 a3 r,
  FOPrH n G (FOTBLVALID 18 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T)) ->
  FOPrH n G (FOTEXT T T' tg a1 a2 a3 r) -> tlen T' = FOSucc (tlen T) ->
  FOPrH n G (FODISPCASES (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') tg a1 a2 a3 r) ->
  FOctx_avoid G 18 122 -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r]) 18 122 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r]) 400 500 ->
  FOPrH n G (FOTBLVALID 18 (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T')) /\
  FOTabMono n G T T'.
Proof.
  intros n G T T' tg a1 a2 a3 r HV HX Hlen HC HG HG2 Hav1 Hav2.
  assert (Hav : FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r])
                  420 500) by avoid_tms.
  split; [|exact (FOPrH_text_mono n G T T' tg a1 a2 a3 r HX Hlen HG2 Hav)].
  apply (FOPrH_tbl_extend n G T T' tg a1 a2 a3 r HV HX Hlen); try assumption.
  pose proof HX as HX'. text_split HX'.
  apply (FOPrH_dispatch_intro n G _ _ _ _ _ _ _ _ _ _ _ _ tg a1 a2 a3 r);
    [ refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
                (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ Xt))); [lia | avoid_tms | avoid_tms]
    | refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
                (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ X1))); [lia | avoid_tms | avoid_tms]
    | refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
                (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ X2))); [lia | avoid_tms | avoid_tms]
    | refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
                (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ X3))); [lia | avoid_tms | avoid_tms]
    | refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
                (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ Xr))); [lia | avoid_tms | avoid_tms]
    | exact HC | intros w ? ?; apply HG; lia | avoid_tms | avoid_tms ].
Qed.
