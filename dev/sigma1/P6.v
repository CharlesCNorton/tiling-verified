From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Tiling Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability.
From Dev2 Require Import P1 P2 P3 P4 P5.
Open Scope fo_scope.

(** ** Some valid table has a given row.

    [FOTBLEX tg a1 a2 a3 r]: the table sits at the variables [2]
    through [12], the row is looked up at base [28]. *)

Definition FOTBLEX (tg a1 a2 a3 r : FOTerm) : FOFormula :=
  FOExists 2 (FOExists 3 (FOExists 4 (FOExists 5 (FOExists 6 (FOExists 7
  (FOExists 8 (FOExists 9 (FOExists 10 (FOExists 11 (FOExists 12
    (FOAnd (FOTBLVALID 18 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
              (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12))
       (FOlookup 28 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
          (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
          tg a1 a2 a3 r)))))))))))).

Ltac tblex_intro_step t Hav :=
  lazymatch goal with
  | |- FOPrH _ _ (FOExists ?z ?A) =>
      apply (FOPrH_ex_intro _ _ z t);
      [ let V := fresh "V" in assert (V : FOtm_avoid t 2 122) by avoid_tm;
        solve [auto 100 with fook]
      | autorewrite with fosubst; rewrite ?FOsubst_t_var_eq'; subst_avoid_h Hav ]
  end.

Lemma FOPrH_tblex_intro : forall n G T tg a1 a2 a3 r,
  FOPrH n G (FOTBLVALID 18 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T)) ->
  FOPrH n G (FOlookup 28 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) tg a1 a2 a3 r) ->
  FOtms_avoid (FOtab_terms T ++ [tg; a1; a2; a3; r]) 2 122 ->
  FOPrH n G (FOTBLEX tg a1 a2 a3 r).
Proof.
  intros n G T tg a1 a2 a3 r HV HL Hav.
  destruct T as [ct dt c1 d1 c2 d2 c3 d3 cr dr len].
  unfold FOtab_terms in Hav. cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen app] in *.
  unfold FOTBLEX.
  tblex_intro_step ct Hav. tblex_intro_step dt Hav. tblex_intro_step c1 Hav.
  tblex_intro_step d1 Hav. tblex_intro_step c2 Hav. tblex_intro_step d2 Hav.
  tblex_intro_step c3 Hav. tblex_intro_step d3 Hav. tblex_intro_step cr Hav.
  tblex_intro_step dr Hav. tblex_intro_step len Hav.
  apply FOPrH_and_intro; assumption.
Qed.

Ltac tblex_rename_step Hr w :=
  lazymatch goal with
  | |- FOPrH _ _ (FOImplF (FOExists ?z ?A) _) =>
      apply (FOPrH_imp_exl_rename _ _ z w A);
      [ solve [match goal with HG : FOctx_avoid _ _ _ |- _ => apply HG; lia end]
      | solve [match goal with HC : forall w, _ -> _ -> FOfree_in w _ = false |- _ =>
                                     apply HC; lia end]
      | repeat rewrite FOfree_in_FOExists_neq by lia; free_fm
      | let V := fresh "V" in assert (V : FOtm_avoid (FOVar w) 2 122) by avoid_tm;
        solve [auto 100 with fook]
      | autorewrite with fosubst; rewrite ?FOsubst_t_var_eq'; subst_avoid_h Hr ]
  end.

Lemma FOPrH_tblex_elim : forall n G tg a1 a2 a3 r k C,
  122 <= k -> k + 11 <= 420 ->
  FOctx_avoid G k (k + 11) ->
  (forall w, k <= w -> w < k + 11 -> FOfree_in w C = false) ->
  FOtms_avoid [tg; a1; a2; a3; r] 2 122 -> FOtms_avoid [tg; a1; a2; a3; r] k (k + 11) ->
  FOPrH n (G ++ [FOAnd (FOTBLVALID 18 (FOVar k) (FOVar (k + 1)) (FOVar (k + 2))
                          (FOVar (k + 3)) (FOVar (k + 4)) (FOVar (k + 5)) (FOVar (k + 6))
                          (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9)) (FOVar (k + 10)))
                       (FOlookup 28 (FOVar k) (FOVar (k + 1)) (FOVar (k + 2))
                          (FOVar (k + 3)) (FOVar (k + 4)) (FOVar (k + 5)) (FOVar (k + 6))
                          (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9)) (FOVar (k + 10))
                          tg a1 a2 a3 r)]) C ->
  FOPrH n G (FOTBLEX tg a1 a2 a3 r .-> C).
Proof.
  intros n G tg a1 a2 a3 r k C Hk Hk' HG HC Hr Hrk H.
  unfold FOTBLEX.
  tblex_rename_step Hr k. tblex_rename_step Hr (k + 1). tblex_rename_step Hr (k + 2).
  tblex_rename_step Hr (k + 3). tblex_rename_step Hr (k + 4). tblex_rename_step Hr (k + 5).
  tblex_rename_step Hr (k + 6). tblex_rename_step Hr (k + 7). tblex_rename_step Hr (k + 8).
  tblex_rename_step Hr (k + 9). tblex_rename_step Hr (k + 10).
  apply FOPrH_intro. exact H.
Qed.
